;;; comphack-codegen.el --- C code generation for comphack -*- lexical-binding: t -*-

;; Author: mbrock
;; Package-Requires: ((emacs "28.1"))

;;; Commentary:

;; Generates C code by using c-mode editing commands like a human typist would.
;; Uses newline-and-indent, c-indent-line, etc. and ensures GNU C coding style.

;;; Code:

(require 'comp)
(require 'cl-lib)
(require 'cc-mode)
(require 'map)

(declare-function comp-mvar-const "comp")
(declare-function comphack-get-abi-hash "comphack")
(declare-function comphack--strip-positions "comphack")

(defvar compc--args-many-functions nil
  "Hash table mapping symbols → t for functions using ARGS_MANY calling convention.")

;;; Helper Functions

;;; Configuration

(defconst compc--pseudo-subr-map
  '(("add1" . "1+")
    ("sub1" . "1-")
    ("negate" . "-"))
  "Map of compiler-only pseudo-subrs to real primitive names.")

(defconst compc--helper-prototypes
  '((wrong_type_argument . ("Lisp_Object" "(Lisp_Object, Lisp_Object)"))
    (helper_PSEUDOVECTOR_TYPEP_XUNTAG . ("bool" "(Lisp_Object, int)"))
    (pure_write_error . ("void" "(Lisp_Object)"))
    (push_handler . ("void*" "(Lisp_Object, int)"))
    (record_unwind_protect_excursion . ("Lisp_Object" "(void)"))
    (helper_unbind_n . ("Lisp_Object" "(Lisp_Object)"))
    (helper_save_restriction . ("Lisp_Object" "(void)"))
    (helper_GET_SYMBOL_WITH_POSITION . ("Lisp_Object" "(Lisp_Object)"))
    (helper_sanitizer_assert . ("Lisp_Object" "(Lisp_Object, Lisp_Object)"))
    (record_unwind_current_buffer . ("Lisp_Object" "(void)"))
    (set_internal . ("Lisp_Object" "(Lisp_Object, Lisp_Object, Lisp_Object, Lisp_Object)"))
    (helper_unwind_protect . ("Lisp_Object" "(Lisp_Object)"))
    (specbind . ("Lisp_Object" "(Lisp_Object, Lisp_Object)"))
    (maybe_gc . ("void" "(void)"))
    (maybe_quit . ("void" "(void)")))
  "Alist describing helper prototypes keyed by helper symbol.")

(defvar compc--runtime-helper-symbols-cache nil
  "Cached list of helper symbols in runtime order.")

(defvar compc--runtime-helper-name-cache nil
  "Cached list of helper names as strings.")

(defvar compc--subr-arity-cache nil
  "Map primitive names to the arities represented by the freloc table.")

(defvar compc--c-name-map nil
  "Map original anonymous C names to compilation-unit-local names.")

(defun compc--mapped-c-name (name)
  "Return compilation-unit-local C name corresponding to NAME."
  (let ((name (cond
               ((stringp name) name)
               ((symbolp name) (symbol-name name))
               (t (format "%s" name)))))
    (or (and compc--c-name-map (gethash name compc--c-name-map))
        name)))

(defun compc--make-c-name-map (functions)
  "Build content-addressed anonymous C symbol map for FUNCTIONS.
TCC does not reliably keep identically named dynamic symbols local even when
linking with -Bsymbolic.  Anonymous functions occur in many separate ELNs, so
give differing functions differing names while preserving reproducible builds."
  (let ((map (make-hash-table :test #'equal)))
    (dolist (func functions map)
      (let ((name (plist-get func :c-name)))
        (when (and (stringp name)
                   (string-match-p "_anonymous_lambda_" name))
          (let ((function-c
                 (with-temp-buffer
                   (let ((compc--c-name-map nil)
                         (buffer-undo-list t)
                         (inhibit-modification-hooks t))
                     (compc-insert-func func))
                   (buffer-string))))
            (puthash name
                     (concat name "_u"
                             (substring (secure-hash 'sha1 function-c) 0 12))
                     map)))))))

(defun compc--replace-c-names (obj &optional seen)
  "Copy OBJ, replacing strings found in `compc--c-name-map'.
Preserve sharing and circular structure using SEEN."
  (let ((seen (or seen (make-hash-table :test #'eq))))
    (cond
     ((stringp obj) (compc--mapped-c-name obj))
     ((vectorp obj)
      (or (gethash obj seen)
          (let ((copy (make-vector (length obj) nil)))
            (puthash obj copy seen)
            (dotimes (i (length obj))
              (aset copy i (compc--replace-c-names (aref obj i) seen)))
            copy)))
     ((consp obj)
      (or (gethash obj seen)
          (let ((copy (cons nil nil)))
            (puthash obj copy seen)
            (setcar copy (compc--replace-c-names (car obj) seen))
            (setcdr copy (compc--replace-c-names (cdr obj) seen))
            copy)))
     (t obj))))

(defun compc--tree-memq (needle tree &optional seen)
  "Return non-nil when NEEDLE occurs in TREE, tolerating circular structure."
  (let ((seen (or seen (make-hash-table :test #'eq))))
    (cond
     ((eq needle tree) t)
     ((or (consp tree) (vectorp tree))
      (unless (gethash tree seen)
        (puthash tree t seen)
        (if (consp tree)
            (or (compc--tree-memq needle (car tree) seen)
                (compc--tree-memq needle (cdr tree) seen))
          (catch 'found
            (dotimes (i (length tree))
              (when (compc--tree-memq needle (aref tree i) seen)
                (throw 'found t)))))))
     (t nil))))

(defun compc--runtime-helper-symbols ()
  "Return helper symbols as provided by the runtime."
  (or compc--runtime-helper-symbols-cache
      (setq compc--runtime-helper-symbols-cache
            (comp-runtime-helper-names))))

(defun compc--runtime-helper-names ()
  "Return helper names as strings."
  (or compc--runtime-helper-name-cache
      (setq compc--runtime-helper-name-cache
            (mapcar #'symbol-name (compc--runtime-helper-symbols)))))

(defvar compc--header-constants-cache nil
  "Cached plist of constants returned by `comp--header-constants'.")

(defun compc--header-constants ()
  "Return plist of constants used to build the freloc header."
  (or compc--header-constants-cache
      (setq compc--header-constants-cache
            (comp--header-constants))))

(defun compc--const (plist key)
  "Fetch KEY from PLIST, signaling if it is missing."
  (let ((value (plist-get plist key)))
    (unless (or (integerp value) (memq key '(:use-lsb-tag)))
      (unless value
        (error "Missing header constant %s" key)))
    value))

(defun compc--const-int (plist key)
  "Like `compc--const' but ensure the value is an integer."
  (let ((value (plist-get plist key)))
    (unless (integerp value)
      (error "Expected integer for %s, got %S" key value))
    value))

(defun compc--canonicalize-func-name (func-name)
  "Return FUNC-NAME mapped to the underlying primitive, if needed."
  (or (alist-get func-name compc--pseudo-subr-map nil nil #'string=)
      func-name))

(defun compc--helper-name-p (func-name)
  "Return non-nil if FUNC-NAME (a string) names a runtime helper."
  (member func-name (compc--runtime-helper-names)))

(defun compc--name->symbol (name)
  "Return bare symbol from NAME, handling symbol-with-pos and singleton lists."
  (cond
   ((symbol-with-pos-p name) (bare-symbol name))
   ((symbolp name) name)
   ((consp name)
    (compc--name->symbol (car name)))
   (t nil)))

(defun compc--helper-prototype-line (helper-symbol)
  "Return struct field declaration string for HELPER-SYMBOL."
  (let ((spec (alist-get helper-symbol compc--helper-prototypes)))
    (unless spec
      (error "Missing helper prototype for %s" helper-symbol))
    (pcase-let ((`(,ret ,args) spec))
      (let ((c-name (symbol-name helper-symbol)))
        (format "%s (*%s) %s;  /* %s */"
                ret c-name args c-name)))))

(defvar compc-func-is-fixed-arity nil
  "Whether current function being generated has fixed arity.
Bound dynamically during function generation.")

(defvar compc--indent-level 0
  "Current indentation level for code generation.
Bound dynamically during code generation.")

;;; Typing Helpers

(defun compc-insert-line (text)
  "Insert TEXT and newline with proper indentation."
  (insert (make-string (* compc--indent-level 2) ?\s) text "\n"))

(defmacro compc-with-block (&rest body)
  "Insert opening brace, execute BODY with increased indentation, then closing brace."
  `(progn
     (compc-insert-line "{")
     (let ((compc--indent-level (1+ compc--indent-level)))
       ,@body)
     (compc-insert-line "}")))

;;; Instruction Translation (returns strings, insertion done by caller)

(defvar compc--d-default-idx nil
  "Hash table mapping constants to d_reloc indices.
Bound dynamically during code generation.")

(defvar compc--d-impure-idx nil
  "Hash table mapping constants to d_reloc_imp indices.
Bound dynamically during code generation.")

(defvar compc--d-ephemeral-idx nil
  "Hash table mapping constants to d_reloc_eph indices.
Bound dynamically during code generation.")

(defun compc-immediate-to-c (val)
  "Convert immediate VAL (literal/closure template) to C code.
Uses d_reloc when the value lives in the default data vector."
  (cond
    ((null val) "Qnil")
    ((eq val t) "Qt")
    ;; Direct call to create a closure: (direct-call "C-name" arg1 arg2 ...)
    ((and (consp val) (eq (car val) 'direct-call))
     (let ((c-name (compc--mapped-c-name (cadr val)))
           (args (cddr val)))
       (if args
           (let ((args-str (mapconcat #'compc-mvar-to-c args ", ")))
             (format "%s (%s)" c-name args-str))
         (format "%s ()" c-name))))
    (t
     ;; Recursively strip position info before lookup
     (let* ((bare-val (comphack--strip-positions val))
            (idx (and compc--d-default-idx
                      (gethash bare-val compc--d-default-idx))))
       (cond
        ;; Check reloc tables first (even for integers!)
        ;; This is crucial for closures where integers may be indices
        (idx
         (format "RELOC (%d)" idx))
        ((and compc--d-impure-idx
              (setq idx (gethash bare-val compc--d-impure-idx)))
         (format "RELOC_IMP (%d)" idx))
        ((and compc--d-ephemeral-idx
              (setq idx (gethash bare-val compc--d-ephemeral-idx)))
         (format "RELOC_EPH (%d)" idx))
        ;; Only treat as literal integer if not found in reloc tables
        ((integerp bare-val)
         (format "make_fixnum (%d)" bare-val))
        ;; For plain symbols not in any reloc array, intern them
        ((symbolp bare-val)
         (format "intern_c_string (\"%s\")" (symbol-name bare-val)))
        (t
         (error "Immediate not found in any reloc idx: %S" val)))))))

(defun compc-mvar-to-c (mvar)
  "Convert MVAR to C variable reference or constant."
  (pcase mvar
    ((pred integerp)
     (format "s%d" mvar))

    ;; Special case: 'scratch' symbol means use scratch variable
    ((pred (lambda (x) (eq x 'scratch)))
     "scratch")

    (`(mvar . ,plist)
     (let ((slot (plist-get plist :slot))
           (val (plist-get plist :val)))
       (cond
        ((eq slot 'scratch) "scratch")  ; Special scratch slot
        (slot (format "s%d" slot))
        (t (compc-immediate-to-c val)))))

    ((and mv (pred comp-mvar-p))
     (let ((slot (comp-mvar-slot mv)))
       (cond
        ((eq slot 'scratch) "scratch")  ; Special scratch slot
        (slot (format "s%d" slot))
        (t (compc-immediate-to-c (comp-mvar-const mv))))))

    (_ (compc-immediate-to-c mvar))))

(defun compc--infer-type-hints-from-value (val)
  "Return list of type symbols implied by literal VAL.
Only returns types that match comp.c's type hint system (fixnum, cons)."
  (cond
   ((fixnump val) '(fixnum))
   ((consp val) '(cons))
   (t nil)))

(defun compc--mvar-type-hints (mvar)
  "Return cached type hints stored on MVAR."
  (cond
   ((and (listp mvar) (eq (car mvar) 'mvar))
    (let ((plist (cdr mvar)))
      (or (plist-get plist :type-hints)
          (compc--infer-type-hints-from-value (plist-get plist :val)))))
   ((integerp mvar) nil)
   ((eq mvar 'scratch) nil)
   (t nil)))

(defun compc--mvar-has-type (mvar type)
  "Return non-nil if MVAR is proven to be of TYPE."
  (memq type (compc--mvar-type-hints mvar)))

(defun compc--mvar-has-any-type (mvar types)
  "Return non-nil if MVAR is proven to satisfy any type in TYPES."
  (let ((hints (compc--mvar-type-hints mvar)))
    (and hints
         (cl-some (lambda (ty) (memq ty hints))
                  types))))

(defun compc--maybe-assign (dst expr)
  "Return C assignment for DST with EXPR, or EXPR when DST is nil."
  (if dst
      (format "%s = %s;" dst expr)
    (format "%s;" expr)))

(defun compc--format-direct-callref (func args dst)
  "Return C snippet for calling FUNC with ARGS via direct-callref.
When DST is non-nil, assign the result there; otherwise, just emit
the call for its side effects."
  (let* ((func-name (cond
                     ((stringp func) func)
                     ((symbolp func) (symbol-name func))
                     (t (format "%s" func))))
         (nargs (length args))
         (func-name (compc--mapped-c-name func-name))
         (call-line (if dst
                        (format "%s = %s (%d, _args);"
                                dst func-name nargs)
                      (format "%s (%d, _args);" func-name nargs))))
    (if (zerop nargs)
        (if dst
            (format "%s = %s (0, NULL);" dst func-name)
          (format "%s (0, NULL);" func-name))
      (let* ((args-c (mapcar #'compc-mvar-to-c args))
             (init-lines (mapcar (lambda (idx-val)
                                   (pcase-let ((`(,idx . ,val) idx-val))
                                     (format "  _args[%d] = %s;" idx val)))
                                 (cl-mapcar #'cons
                                            (number-sequence 0 (1- nargs))
                                            args-c))))
        (format "{\n  Lisp_Object _args[%d];\n%s\n  %s\n}"
                nargs
                (mapconcat #'identity init-lines "\n")
                call-line)))))

(defun compc--emit-optimized-call (func args dst)
  "Emit inline lowering for FUNC when available.
ARGS is the raw argument list from the instruction, and DST is the
stringified destination or nil.  Returns a C snippet string or nil."
  (let* ((fname (if (symbolp func) (symbol-name func) (format "%s" func)))
         (args-c (mapcar #'compc-mvar-to-c args))
         (arg1 (car args))
         (arg2 (cadr args))
         (arg1-c (car args-c))
         (arg2-c (cadr args-c)))
    (cl-labels ((assign (expr &optional indent)
                        (let ((line (compc--maybe-assign dst expr)))
                          (if indent (concat indent line) line)))
                (sure-fixnum-p (mvar)
                  (compc--mvar-has-type mvar 'fixnum))
                (sure-cons-p (mvar)
                  (compc--mvar-has-type mvar 'cons))
                (inline-add (arg arg-str delta fallback limit)
                            (let* ((sign (if (> delta 0) "+" "-"))
                                   (condition (if (sure-fixnum-p arg)
                                                  (format "XFIXNUM (_tmp) != %s" limit)
                                                (format "FIXNUMP (_tmp) && XFIXNUM (_tmp) != %s" limit)))
                                   (body (format "make_fixnum (XFIXNUM (_tmp) %s %d)" sign 1)))
                              (format "{\n  Lisp_Object _tmp = %s;\n  if (%s)\n%s\n  else\n%s\n}"
                                      arg-str condition
                                      (assign body "    ")
                                      (assign (format "%s (_tmp)" fallback) "    "))))
                (inline-negate (arg arg-str)
                               (let ((condition (if (sure-fixnum-p arg)
                                                    "XFIXNUM (_tmp) != MOST_NEGATIVE_FIXNUM"
                                                  "FIXNUMP (_tmp) && XFIXNUM (_tmp) != MOST_NEGATIVE_FIXNUM")))
                                 (format "{\n  Lisp_Object _tmp = %s;\n  if (%s)\n%s\n  else\n%s\n}"
                                         arg-str condition
                                         (assign "make_fixnum (-XFIXNUM (_tmp))" "    ")
                                         (assign "fn->f__ (1, LIST (_tmp))" "    "))))
                (inline-cons-access (arg arg-str op fallback)
                                    (if (sure-cons-p arg)
                                        (format "{\n  Lisp_Object _tmp = %s;\n%s\n}"
                                                arg-str
                                                (assign (format "%s (_tmp)" op) "    "))
                                      (format "{\n  Lisp_Object _tmp = %s;\n  if (CONSP (_tmp))\n%s\n  else\n%s\n}"
                                              arg-str
                                              (assign (format "%s (_tmp)" op) "    ")
                                              (assign (format "%s (_tmp)" fallback) "    "))))
                (inline-set (cell cell-str value value-str fallback offset)
                            (let ((fast-line (when dst (assign "_new" "    "))))
                              (if (sure-cons-p cell)
                                  (format "{\n  Lisp_Object _cell = %s;\n  Lisp_Object _new = %s;\n  char *_ptr = compc_xcons_ptr (_cell);\n  CHECK_IMPURE (_cell, _ptr);\n  *(Lisp_Object *)(_ptr + %s) = _new;\n%s}\n"
                                          cell-str value-str offset
                                          (or fast-line ""))
                                (format "{\n  Lisp_Object _cell = %s;\n  Lisp_Object _new = %s;\n  if (CONSP (_cell)) {\n    char *_ptr = compc_xcons_ptr (_cell);\n    CHECK_IMPURE (_cell, _ptr);\n    *(Lisp_Object *)(_ptr + %s) = _new;\n%s  } else {\n%s\n  }\n}"
                                        cell-str value-str offset
                                        (or fast-line "")
                                        (assign (format "%s (_cell, _new)" fallback) "    ")))))
                (inline-boolean (expr)
                                 (assign (format "BOOL_TO_LISP (%s)" expr))))
      (pcase fname
        ("add1" (inline-add arg1 arg1-c 1 "fn->f_1_PLUS" "MOST_POSITIVE_FIXNUM"))
        ("sub1" (inline-add arg1 arg1-c -1 "fn->f_1_MINUS" "MOST_NEGATIVE_FIXNUM"))
        ("negate" (inline-negate arg1 arg1-c))
        ("consp"
         (if (sure-cons-p arg1)
             (assign "Qt")
           (inline-boolean (format "CONSP (%s)" arg1-c))))
        ("numberp"
         ;; If known to be fixnum, it's definitely a number
         (if (compc--mvar-has-type arg1 'fixnum)
             (assign "Qt")
           (inline-boolean
            (format "FIXNUMP (%1$s) || BIGNUMP (%1$s) || FLOATP (%1$s)" arg1-c))))
        ("integerp"
         ;; If known to be fixnum, it's definitely an integer
         (if (compc--mvar-has-type arg1 'fixnum)
             (assign "Qt")
           (inline-boolean
            (format "FIXNUMP (%1$s) || BIGNUMP (%1$s)" arg1-c))))
        ("car" (inline-cons-access arg1 arg1-c "XCAR" "fn->f_car"))
        ("cdr" (inline-cons-access arg1 arg1-c "XCDR" "fn->f_cdr"))
        ("setcar"
         (inline-set arg1 arg1-c arg2 arg2-c "fn->f_setcar" "CONS_CAR_OFFSET"))
        ("setcdr"
         (inline-set arg1 arg1-c arg2 arg2-c "fn->f_setcdr" "CONS_CDR_OFFSET"))
        ("comp-maybe-gc-or-quit"
         (format "{\n  compc_maybe_gc_or_quit (fn);\n%s\n}"
                 (if dst (assign "Qnil" "  ") "")))
        (_ nil)))))

(defun compc-get-subr-arity (func-name)
  "Get arity of built-in function FUNC-NAME.
Returns cons (min . max) or nil if not found."
  (unless compc--subr-arity-cache
    (setq compc--subr-arity-cache (make-hash-table :test #'equal))
    (dolist (subr comp-subr-list)
      (puthash (subr-name subr)
               (subr-arity subr)
               compc--subr-arity-cache)))
  (gethash func-name compc--subr-arity-cache))

(defun compc--add-default-args (func-name args)
  "Add default arguments for functions that need them.
Some runtime functions are called with fewer arguments in LIMPLE,
relying on default values for omitted arguments."
  (cond
   ;; set_internal (symbol, newval, where, bindflag)
   ;; When called with 2 args, defaults are: Qnil, SET_INTERNAL_SET
   ((and (equal func-name "set_internal") (= (length args) 2))
    (append args '("Qnil" "SET_INTERNAL_SET")))

   ;; Default: return args unchanged
   (t args)))

(defun compc-freloc-call (func-name args &optional dst)
  "Generate freloc function call for FUNC-NAME with ARGS.
If DST is non-nil, assigns result to DST."
  (let* ((canonical-name (compc--canonicalize-func-name func-name))
         ;; Add default arguments if needed
         (args (compc--add-default-args canonical-name args)))
    (if (compc--helper-name-p canonical-name)
        (compc--format-helper-call canonical-name args dst)
      (let* ((arity (compc-get-subr-arity canonical-name))
         (num-args (length args))
         (readable-name (replace-regexp-in-string
                         "[^a-zA-Z0-9_-]"
                         (lambda (c)
                           (pcase c
                             ("+" "_PLUS")
                             ("*" "_STAR")
                             ("/" "_SLASH")
                             ("<" "_LT")
                             (">" "_GT")
                             ("=" "_EQ")
                             ("?" "_P")
                             ("!" "_BANG")
                             ("%" "_PCT")
                             ("&" "_AND")
                             ("|" "_OR")
                             ("~" "_TILDE")
                             ("^" "_XOR")
                             (":" "_COLON")
                             ("." "_DOT")
                             ("," "_COMMA")
                             ("'" "_QUOTE")
                             ("\"" "_DQUOTE")
                             (_ "_")))
                        canonical-name))
         (readable-name (replace-regexp-in-string "-" "_" readable-name))
         (c-name (concat "f_" readable-name))
         (call-str
          (cond
           ;; Fixed arity - direct call (including optional args)
           ((and arity
                 (numberp (car arity))
                 (numberp (cdr arity))
                 (= num-args (cdr arity)))
            (let ((args-str (mapconcat #'identity args ", ")))
              (if (> (+ (length c-name) (length args-str)) 60)
                  (format "fn->%s\n  (%s)" c-name args-str)
                (format "fn->%s (%s)" c-name args-str))))

           ;; Variadic - array form
           (t
            (if (zerop num-args)
                (format "fn->%s (%d, NULL)" c-name num-args)
              (let ((args-str (mapconcat #'identity args ", ")))
                (if (> (+ (length c-name) (length args-str)) 50)
                    (format "fn->%s\n  (%d, LIST (%s))"
                            c-name num-args args-str)
                  (format "fn->%s (%d, LIST (%s))"
                          c-name num-args args-str))))))))

      (if dst
          (if (string-match-p "\n" call-str)
              (format "%s =\n  %s;" dst call-str)
            (format "%s = %s;" dst call-str))
        (format "%s;" call-str))))))

(defun compc--format-helper-call (func-name args dst)
  "Emit a helper call to FUNC-NAME with ARGS, optionally assigning to DST."
  (let* ((field (format "fn->%s"
                        (replace-regexp-in-string "-" "_" func-name)))
         (call (if args
                   (format "%s (%s)" field (mapconcat #'identity args ", "))
                 (format "%s ()" field))))
    (if dst
        (format "%s = %s;" dst call)
      (format "%s;" call))))

(defun compc-insn-to-c (insn)
  "Convert LIMPLE INSN to C code."
  (pcase insn
    (`(comment ,_text)
     nil)

    (`(setimm ,dst ,val)
     (format "%s = %s;"
             (compc-mvar-to-c dst)
             (compc-immediate-to-c val)))

    (`(set ,dst (callref ,func . ,args))
     (let* ((dst-c (compc-mvar-to-c dst))
            (func-name (symbol-name func))
            (optimized (compc--emit-optimized-call func args dst-c)))
       (cond
        (optimized optimized)
        ;; Fix ARGS_MANY function registration for callref pattern
        ((equal func-name "comp--register-subr")
         (let* ((fun-name-arg (nth 0 args))
                (fun-name (and (listp fun-name-arg)
                               (eq (car fun-name-arg) 'mvar)
                               (plist-get (cdr fun-name-arg) :val)))
                (min-arg (nth 2 args))
                (min-val (and (listp min-arg)
                              (eq (car min-arg) 'mvar)
                              (plist-get (cdr min-arg) :val)))
                (max-arg (nth 3 args))
                (max-val (and (listp max-arg)
                              (eq (car max-arg) 'mvar)
                              (plist-get (cdr max-arg) :val)))
                (fun-sym (compc--name->symbol fun-name))
                (needs-many (or (and fun-sym
                                     (gethash fun-sym compc--args-many-functions))
                                (and (integerp max-val) (> max-val 8))))
                (fixed-args (if (and needs-many (not (consp min-val)))
                                (let ((copy (copy-sequence args)))
                                  (setf (nth 3 copy) '(mvar :val nil))
                                  copy)
                              args))
                (args-c (mapcar #'compc-mvar-to-c fixed-args)))
           (compc-freloc-call func-name args-c (compc-mvar-to-c dst))))

        (t
         (compc-freloc-call
          func-name
          (mapcar #'compc-mvar-to-c args)
          dst-c)))))

    (`(set ,dst (call ,func . ,args))
     (let* ((dst-c (compc-mvar-to-c dst))
            (func-name (if (symbolp func) (symbol-name func) (format "%s" func)))
            (optimized (compc--emit-optimized-call func args dst-c)))
       (cond
        (optimized optimized)
        ((equal func-name "comp-maybe-gc-or-quit")
         (format "%s = comp_maybe_gc_or_quit (%d, %s);"
                 dst-c
                 (length args)
                 (if (zerop (length args)) "NULL"
                   (format "LIST (%s)" (mapconcat #'compc-mvar-to-c args ", ")))))

        ;; Fix ARGS_MANY function registration
        ((equal func-name "comp--register-subr")
         (let* ((fun-name-arg (nth 0 args))
                (fun-name (and (listp fun-name-arg)
                               (eq (car fun-name-arg) 'mvar)
                               (plist-get (cdr fun-name-arg) :val)))
                (min-arg (nth 2 args))
                (min-val (and (listp min-arg)
                              (eq (car min-arg) 'mvar)
                              (plist-get (cdr min-arg) :val)))
                (max-arg (nth 3 args))
                (max-val (and (listp max-arg)
                              (eq (car max-arg) 'mvar)
                              (plist-get (cdr max-arg) :val)))
                (fun-sym (compc--name->symbol fun-name))
                (needs-many (or (and fun-sym
                                     (gethash fun-sym compc--args-many-functions))
                                (and (integerp max-val) (> max-val 8))))
                (fixed-args (if (and needs-many (not (consp min-val)))
                                (let ((copy (copy-sequence args)))
                                  (setf (nth 3 copy) '(mvar :val nil))
                                  copy)
                              args))
                (args-c (mapcar #'compc-mvar-to-c fixed-args)))
           (compc-freloc-call func-name args-c (compc-mvar-to-c dst))))

        (t
         (compc-freloc-call func-name
                            (mapcar #'compc-mvar-to-c args)
                            dst-c)))))

    (`(set ,dst (direct-callref ,c-name . ,args))
     (compc--format-direct-callref c-name args (compc-mvar-to-c dst)))

    (`(set ,dst ,src)
     (format "%s = %s;"
             (compc-mvar-to-c dst)
             (compc-mvar-to-c src)))

    (`(callref ,func . ,args)
     (or (compc--emit-optimized-call func args nil)
         (compc-freloc-call
          (symbol-name func)
          (mapcar #'compc-mvar-to-c args)
          nil)))

    (`(call ,func . ,args)
     (let ((func-name (if (symbolp func) (symbol-name func) (format "%s" func))))
       (cond
        ((compc--emit-optimized-call func args nil))
        ((equal func-name "comp-maybe-gc-or-quit")
         (format "comp_maybe_gc_or_quit (%d, %s);"
                 (length args)
                 (if (zerop (length args)) "NULL"
                   (format "LIST (%s)" (mapconcat #'compc-mvar-to-c args ", ")))))

        ;; Fix ARGS_MANY function registration for standalone calls
        ((equal func-name "comp--register-subr")
         (let* ((fun-name-arg (nth 0 args))
                (fun-name (and (listp fun-name-arg)
                               (eq (car fun-name-arg) 'mvar)
                               (plist-get (cdr fun-name-arg) :val)))
                (min-arg (nth 2 args))
                (min-val (and (listp min-arg)
                              (eq (car min-arg) 'mvar)
                              (plist-get (cdr min-arg) :val)))
                (max-arg (nth 3 args))
                (max-val (and (listp max-arg)
                              (eq (car max-arg) 'mvar)
                              (plist-get (cdr max-arg) :val)))
                (fun-sym (compc--name->symbol fun-name))
                (needs-many (or (and fun-sym
                                     (gethash fun-sym compc--args-many-functions))
                                (and (integerp max-val) (> max-val 8))))
                (fixed-args (if (and needs-many (not (consp min-val)))
                                (let ((copy (copy-sequence args)))
                                  (setf (nth 3 copy) '(mvar :val nil))
                                  copy)
                              args))
                (args-c (mapcar #'compc-mvar-to-c fixed-args)))
           (compc-freloc-call func-name args-c nil)))

        (t
         (compc-freloc-call func-name
                            (mapcar #'compc-mvar-to-c args)
                            nil)))))

    (`(direct-callref ,c-name . ,args)
     (compc--format-direct-callref c-name args nil))

    (`(return ,val)
     (format "return %s;" (compc-mvar-to-c val)))

    (`(jump ,label)
     (format "goto %s;" label))

    (`(cond-jump ,test ,cmp ,true-bb ,false-bb)
     ;; cond-jump tests if test==cmp, goto true-bb if equal, else false-bb
     ;; When cmp is nil (the constant), test if test is nil/false
     (let ((cmp-val (cond
                     ((null cmp) nil)
                     ((comp-mvar-p cmp) (comp-mvar-const cmp))
                     ;; Extract value from (mvar :val VALUE) plist
                     ((and (listp cmp) (eq (car cmp) 'mvar))
                      (plist-get (cdr cmp) :val))
                     (t cmp))))
       (if (null cmp-val)
           ;; Comparing to nil requires Lisp_Object equality, not C truth.
           (format "if (%s == Qnil)\n  goto %s;\nelse\n  goto %s;"
                   (compc-mvar-to-c test)
                   true-bb
                   false-bb)
         ;; `cond-jump' has Lisp `eq' semantics.  In particular, Emacs 31
         ;; considers a symbol-with-position equal to its bare symbol when
         ;; `symbols_with_pos_enabled' is set.  Raw Lisp_Object comparison
         ;; would make compiler dispatch on positioned source forms miss.
         (format "if (fn->f_eq (%s, %s))\n  goto %s;\nelse\n  goto %s;"
                 (compc-mvar-to-c test)
                 (compc-immediate-to-c cmp-val)
                 true-bb
                 false-bb))))

    (`(set-par-to-local ,dst ,n)
     (if compc-func-is-fixed-arity
         (format "%s = arg%d;" (compc-mvar-to-c dst) n)
       ;; For ARGS_MANY, parameters are already extracted in entry block
       ;; so this instruction can be skipped
       nil))

    (`(set-args-to-local ,dst)
     (format "%s = *args++;" (compc-mvar-to-c dst)))

    (`(inc-args)
     "/* inc-args handled by set-args-to-local */")

    (`(set-rest-args-to-local ,dst)
     ;; From comp.c: local[slot] = list (nargs - slot, args);
     ;; In our case, args pointer has already been incremented by set-args-to-local
     ;; so we need to find the slot number to know how many args were consumed
     (let* ((slot (cond
                   ((comp-mvar-p dst) (comp-mvar-slot dst))
                   ((and (listp dst) (eq (car dst) 'mvar))
                    (plist-get (cdr dst) :slot))
                   ((integerp dst) dst)
                   (t nil))))
       (if slot
           (format "%s = fn->f_list (nargs - %d, args);"
                   (compc-mvar-to-c dst)
                   slot)
         (format "%s = Qnil; /* ERROR: no slot for rest args, dst=%S */"
                 (compc-mvar-to-c dst) dst))))

    (`(cond-jump-narg-leq ,n ,true-bb ,false-bb)
     ;; Jump based on number of arguments
     ;; if (nargs <= n) goto true-bb; else goto false-bb;
     (format "if (nargs <= %d)\n  goto %s;\nelse\n  goto %s;"
             n true-bb false-bb))

    (`(phi ,dst . ,_)
     ;; PHI nodes generate no code - handled by patching predecessor blocks
     nil)

    (`(assume . ,_)
     ;; Assume instructions generate no code - purely for type analysis
     nil)

    (`(unreachable)
     ;; Unreachable code marker - no code generation needed
     "/* unreachable */")

    (`(push-handler ,type ,handler-num ,handler-bb ,guarded-bb)
     ;; Push a new exception handler onto the stack
     ;; type: handler type (CATCHER=0, CONDITION_CASE=1)
     ;; handler-num: mvar containing the tag (condition or catch tag)
     ;; handler-bb: exception caught path (setjmp returned non-zero)
     ;; guarded-bb: normal execution path (setjmp returned 0)
     (format "{\n  comp_handler_ptr h = fn->push_handler(%s, %s);\n  if (setjmp(*GET_HANDLER_JMP(h)) == 0)\n    goto %s;\n  else\n    goto %s;\n}"
             (compc-mvar-to-c handler-num)
             (if (eq type 'condition-case) "CONDITION_CASE" "CATCHER")
             guarded-bb
             handler-bb))

    (`(pop-handler)
     ;; Remove the current handler from the stack
     ;; Move handlerlist to the next handler
     "SET_HANDLERLIST(GET_HANDLER_NEXT(GET_HANDLERLIST()));")

    (`(fetch-handler ,dst)
     ;; Get the value from the current handler AND pop it
     ;; This is what comp.c does: save handler, pop it, then get val
     (format "{\n  comp_handler_ptr h = GET_HANDLERLIST();\n  SET_HANDLERLIST(GET_HANDLER_NEXT(h));\n  %s = GET_HANDLER_VAL(h);\n}"
             (compc-mvar-to-c dst)))

    ;; Direct call without assignment - just call for side effects
    (`(direct-call ,c-name . ,args)
     (let ((c-name (compc--mapped-c-name c-name)))
       (if args
           (let ((args-str (mapconcat #'compc-mvar-to-c args ", ")))
             (format "%s (%s);" c-name args-str))
         (format "%s ();" c-name))))

    (_ (error "Unknown instruction: %S" insn))))

;;; Block and Function Generation

(defun compc-func-has-rest-args-p (func)
  "Return t if FUNC uses &rest args (has set-args-to-local instructions)."
  (let ((blocks (plist-get func :blocks)))
    (cl-some
     (lambda (b)
       (cl-some (lambda (insn)
                  (and (listp insn)
                       (memq (car insn) '(set-args-to-local set-rest-args-to-local))))
                (plist-get b :insns)))
     blocks)))

(defun compc--function-arity-info (func)
  "Return plist describing FUNC arity metadata."
  (pcase-let* (((map :name :args) func)
               (args-clean (cond
                            ((comp-args-p args)
                             (list (aref args 1) (aref args 2)))
                            ((consp args) args)
                            (t (list 0 0))))
               (min-args (car args-clean))
               (max-args (cadr args-clean))
               (has-rest-args (or (memq max-args '(many unevalled))
                                  (compc-func-has-rest-args-p func)))
               (fun-symbol (compc--name->symbol name))
               (lisp-name (and fun-symbol (symbol-name fun-symbol))))
    (list :symbol fun-symbol
          :lisp-name lisp-name
          :min min-args
          :max max-args
          :rest has-rest-args)))

(defun compc-insert-block (block)
  "Insert basic BLOCK using c-mode commands."
  (pcase-let (((map :name :insns) block))
    (compc-insert-line (format "%s:" name))
    (let ((compc--indent-level (1+ compc--indent-level)))
      (dolist (insn insns)
        (let ((code (compc-insn-to-c insn)))
          (when code
            (compc-insert-line code)))))))

(defun compc-extract-phi-assignments (blocks)
  "Extract PHI node assignments as a hash table.
Returns hash mapping (pred-block . target-block) -> list of assignments."
  (let ((phi-map (make-hash-table :test 'equal)))
    (prog1 phi-map
      (dolist (block blocks)
        (let ((block-name (plist-get block :name))
              (insns (plist-get block :insns)))
          (dolist (insn insns)
            (when (and (listp insn) (eq (car insn) 'phi))
              (let ((dst (nth 1 insn))
                    (phi-args (cddr insn)))
                ;; phi-args is like ((val1 pred1) (val2 pred2) ...)
                (dolist (phi-arg phi-args)
                  (let* ((val (car phi-arg))
                         (pred (cadr phi-arg))
                         (key (cons pred block-name))
                         (dst-c (compc-mvar-to-c dst))
                         (val-c (compc-mvar-to-c val)))
                    ;; Skip identity assignments
                    (unless (equal dst-c val-c)
                      (let ((assignment (format "%s = %s;" dst-c val-c)))
                        (push assignment (gethash key phi-map))))))))))))))

(defun compc-patch-phi-assignments (phi-map func-start)
  "Patch PHI assignments into predecessor blocks by searching backwards.
Uses narrow-to-region to stay within the function starting at FUNC-START."
  (save-restriction
    (narrow-to-region func-start (point-max))
    (maphash
     (lambda (key assignments)
       (let ((pred-block (car key)))
         ;; Search backwards for "goto target;" after "pred-block:"
         (goto-char (point-max))
         (when (re-search-backward (format "^\\s-*%s:" pred-block) nil t)
           ;; Move to end of block (just before the goto/return/jump)
           (forward-line 1)
           (when (re-search-forward "\\(goto\\|return\\|if\\)\\s-" nil t)
             (beginning-of-line)
             ;; Insert PHI assignments
             (dolist (assignment (reverse assignments))
               (insert "  " assignment)
               (insert "\n"))))))
     phi-map)))

(defun compc-insert-func (func)
  "Insert function FUNC using c-mode commands."
  (pcase-let* (((map :c-name :frame-size :blocks) func)
               (c-name (compc--mapped-c-name c-name))
               (arity-info (compc--function-arity-info func))
               (lisp-name (plist-get arity-info :lisp-name))
               (min-args (plist-get arity-info :min))
               (max-args (plist-get arity-info :max))
               (has-rest-args (plist-get arity-info :rest))
               (fixed-arity (and (numberp max-args)
                                 (<= max-args 8)
                                 (not has-rest-args)))
               (params (if fixed-arity
                           (if (zerop max-args)
                               "void"
                             (mapconcat (lambda (i)
                                          (format "Lisp_Object arg%d" i))
                                        (number-sequence 0 (1- max-args))
                                        ", "))
                         "ptrdiff_t nargs, Lisp_Object *args")))

    (let ((compc-func-is-fixed-arity fixed-arity)
          (func-start (point)))
      ;; Generate DEFUN signature
      (if fixed-arity
          (let ((args-macro (cond
                            ((zerop max-args) "ARGS_0")
                            ((<= max-args 3) (format "ARGS_%d" max-args))
                            (t nil))))
            (if args-macro
                (compc-insert-line (format "DEFUN (\"%s\", %s, %s)" lisp-name c-name args-macro))
              (compc-insert-line (format "Lisp_Object\n%s (%s)" c-name params))))
        (compc-insert-line (format "DEFUN (\"%s\", %s, ARGS_MANY)" lisp-name c-name)))

      (compc-with-block
       (compc-insert-line "struct freloc_link_table *fn = freloc_link_table;")

      ;; Check if function uses scratch variable
      (let ((uses-scratch (cl-some
                           (lambda (block)
                             (cl-some (lambda (insn)
                                        (and (listp insn)
                                             (compc--tree-memq 'scratch insn)))
                                      (plist-get block :insns)))
                           blocks)))
        (when uses-scratch
          (compc-insert-line "Lisp_Object scratch;")))

      (when (> frame-size 0)
        (insert "Lisp_Object ")
        (let ((slots (mapconcat (lambda (i) (format "s%d" i))
                                (number-sequence 0 (1- frame-size))
                                ", ")))
          (if (> (length slots) 60)
              (insert (mapconcat (lambda (i) (format "s%d" i))
                                 (number-sequence 0 (1- frame-size))
                                 ",\n    "))
            (insert slots)))
        (insert ";")
        (insert "\n")
        (insert "\n"))

      ;; For ARGS_MANY functions, extract all parameters from args array
      ;; This must happen before processing blocks to ensure all parameters
      ;; are initialized, even if they're unused (optimized away by compiler)
      (unless fixed-arity
        (when (and (numberp max-args) (> max-args 0))
          (dotimes (i max-args)
            (compc-insert-line
             (format "s%d = (nargs > %d) ? args[%d] : Qnil;" i i i)))))

      ;; First pass: extract PHI assignments
      (let ((phi-map (compc-extract-phi-assignments blocks)))

        ;; Second pass: insert blocks
        (dolist (block blocks)
          (compc-insert-block block))

        ;; Third pass: patch in PHI assignments by searching backwards (narrowed to function)
        (when (> (hash-table-count phi-map) 0)
          (save-excursion
            (compc-patch-phi-assignments phi-map func-start))))))))

;;; Data Serialization

(defun compc-escape-c-string (str)
  "Escape STR as a portable C string literal payload.
Encode non-ASCII and control characters as fixed-width octal escapes so the
generated C source itself contains no embedded control bytes.  In particular,
literal NUL bytes are accepted by GCC but prematurely terminate a string token
in TCC."
  (let ((bytes (encode-coding-string str 'utf-8 t)))
    (with-temp-buffer
      (dotimes (i (length bytes))
        (let ((byte (aref bytes i)))
          (cond
           ((eq byte ?\") (insert "\\\""))
           ((eq byte ?\\) (insert "\\\\"))
           ((eq byte ?\n) (insert "\\n"))
           ((and (>= byte #x20) (<= byte #x7e)) (insert byte))
           (t (insert (format "\\%03o" byte))))))
      (buffer-string))))

(defun compc--make-data-readable (obj)
  "Make OBJ readable by converting symbols-with-pos to plain symbols."
  (compc--replace-c-names (comphack--strip-positions obj)))

(defun compc-insert-blob (name obj)
  "Insert static blob declaration for NAME containing OBJ."
  (let* ((readable-obj (compc--make-data-readable obj))
         (serialized (let ((print-length nil)
                           (print-level nil)
                           (print-circle t)
                           (print-gensym t)
                           (print-escape-newlines t)
                           (print-escape-multibyte t))
                       (prin1-to-string readable-obj)))
         (escaped (compc-escape-c-string serialized)))
    (insert "\n")
    (compc-insert-line (format "DEFBLOB (%s,\n  \"%s\");" name escaped))))

(defun compc-insert-data-blobs (minimal)
  "Insert data blob declarations from MINIMAL context."
  (pcase-let* (((map :d-default :d-impure :d-ephemeral :speed :debug :function-docs) minimal)
               (speed (or speed 2))
               (debug (or debug 0)))

    (compc-insert-line "/* Static blobs */")

    (compc-insert-blob "freloc_hash" comp-abi-hash)
    (compc-insert-blob "text_data_reloc_eph" d-ephemeral)
    (compc-insert-blob "text_data_reloc_imp" d-impure)
    (compc-insert-blob "text_data_reloc" d-default)
    (compc-insert-blob "text_data_fdoc" function-docs)
    (compc-insert-blob "text_optim_qly"
                       (list (cons 'native-comp-speed speed)
                             (cons 'native-comp-debug debug)))))

(defun compc-insert-reloc-arrays (minimal)
  "Insert relocation array declarations from MINIMAL context."
  (pcase-let* (((map :d-default :d-impure :d-ephemeral) minimal)
               (default-len (length d-default))
               (impure-len (length d-impure))
               (ephemeral-len (length d-ephemeral)))

    (compc-insert-line "/* Relocation arrays */")
    (compc-insert-line (format "Lisp_Object d_reloc[%d];" (max 1 default-len)))
    (compc-insert-line (format "Lisp_Object d_reloc_imp[%d];" (max 1 impure-len)))
    (compc-insert-line (format "Lisp_Object d_reloc_eph[%d];" (max 1 ephemeral-len)))
    (insert "\n")))

(defun compc-insert-exports ()
  "Insert global export definitions."
  (compc-insert-line "/* Exports */")
  (compc-insert-line "Lisp_Object comp_unit;")
  (compc-insert-line "void **current_thread_reloc;")
  (compc-insert-line "bool **f_symbols_with_pos_enabled_reloc;")
  (compc-insert-line "void **pure_reloc;")
  (compc-insert-line "struct freloc_link_table *freloc_link_table;")
  (insert "\n"))

;;; Complete File Generation

;;;###autoload
(defun comphack-codegen-insert-complete-eln (minimal &optional freloc-filename)
  "Insert complete .eln C source from MINIMAL context into current buffer.
FRELOC-FILENAME specifies the ABI-versioned freloc header to include.
Uses c-mode for proper GNU C coding style indentation."
  (pcase-let* (((map :functions
                     :d-default-idx
                     :d-impure-idx
                     :d-ephemeral-idx) minimal)
               (freloc-h (or freloc-filename "freloc.h")))

    (let ((compc--d-default-idx d-default-idx)
          (compc--d-impure-idx d-impure-idx)
          (compc--d-ephemeral-idx d-ephemeral-idx)
          (compc--c-name-map nil)
          (compc--args-many-functions (make-hash-table :test 'eq))
          (buffer-undo-list t)
          (inhibit-modification-hooks t))
      (dolist (func functions)
        (let* ((info (compc--function-arity-info func))
               (sym (plist-get info :symbol))
               (max-args (plist-get info :max))
               (rest (plist-get info :rest))
               (fixed (and (numberp max-args)
                           (<= max-args 8)
                           (not rest))))
          (when (and sym (not fixed))
            (puthash sym t compc--args-many-functions))))
      (setq compc--c-name-map
            (compc--make-c-name-map functions))
     ; (c-mode)
      (font-lock-mode -1)
      (setq c-default-style "gnu")

      ;; Includes (comphack.h is now inlined in freloc header)
      (compc-insert-line (format "#include \"%s\"" freloc-h))
      (insert "\n")

      ;; Relocation arrays (needed by functions)
      (compc-insert-reloc-arrays minimal)
      (insert "\n")

      ;; Exports
      (compc-insert-exports)

      ;; Compile all functions (including top_level_run) from LIMPLE
      (let ((user-funcs functions))

        (when user-funcs
          (insert "\n")
          (dolist (func user-funcs)
            (pcase-let* (((map :c-name) func)
                         (c-name (compc--mapped-c-name c-name))
                         (info (compc--function-arity-info func))
                         (max-args (plist-get info :max))
                         (has-rest-args (plist-get info :rest))
                         (fixed-arity (and (numberp max-args)
                                           (<= max-args 8)
                                           (not has-rest-args)))
                         (params (if fixed-arity
                                     (if (zerop max-args)
                                         "void"
                                       (let ((args-list
                                              (mapconcat
                                               (lambda (i)
                                                 (format "Lisp_Object arg%d" i))
                                               (number-sequence 0 (1- max-args))
                                               ", ")))
                                         (if (> (length args-list) 50)
                                             (mapconcat
                                              (lambda (i)
                                                (format "Lisp_Object arg%d" i))
                                              (number-sequence 0 (1- max-args))
                                              ",\n    ")
                                           args-list)))
                                   "ptrdiff_t nargs, Lisp_Object *args")))
              (compc-insert-line
               (format "Lisp_Object %s (%s);" c-name params))))
          (insert "\n"))

        (when user-funcs
          (insert "\n")
          (dolist (func user-funcs)
            (compc-insert-func func)
            (insert "\n"))))

      ;; Static blobs at the end
      (insert "\n")
      (compc-insert-data-blobs minimal))))

;;; freloc.h Generation

(defun compc-generate-freloc-struct ()
  "Generate freloc.h struct definition with all Emacs primitives."
  (with-temp-buffer
                                        ;    (c-mode)
    (setq c-default-style "gnu")

    (compc-insert-line "/* Function relocation table structure */")
    (compc-insert-line "/* This must match Emacs's internal freloc table exactly */")
    (insert "\n")
    (compc-insert-line "struct freloc_link_table")
    (compc-with-block
     (dolist (helper (compc--runtime-helper-symbols))
       (compc-insert-line (compc--helper-prototype-line helper)))
     (dolist (subr comp-subr-list)
       (let* ((name (subr-name subr))
              (arity (subr-arity subr))
              (readable-name (replace-regexp-in-string
                              "[^a-zA-Z0-9_-]"
                              (lambda (c)
                                (pcase c
                                  ("+" "_PLUS")
                                  ("*" "_STAR")
                                  ("/" "_SLASH")
                                  ("<" "_LT")
                                  (">" "_GT")
                                  ("=" "_EQ")
                                  ("?" "_P")
                                  ("!" "_BANG")
                                  ("%" "_PCT")
                                  ("&" "_AND")
                                  ("|" "_OR")
                                  ("~" "_TILDE")
                                  ("^" "_XOR")
                                  (":" "_COLON")
                                  ("." "_DOT")
                                  ("," "_COMMA")
                                  ("'" "_QUOTE")
                                  ("\"" "_DQUOTE")
                                  (_ "_")))
                              name))
              (readable-name (replace-regexp-in-string "-" "_" readable-name))
              (c-name (concat "f_" readable-name))
              (max-arity (cdr arity)))

         (cond
          ((or (eq max-arity 'many) (eq max-arity 'unevalled))
           (compc-insert-line
            (format "Lisp_Object (*%s) (ptrdiff_t, Lisp_Object *);  /* %s */" c-name name)))

          ;; Fixed arity (including optional args - use max arity)
          ((numberp max-arity)
           (let ((params (if (zerop max-arity)
                             "void"
                           (mapconcat (lambda (_) "Lisp_Object")
                                      (number-sequence 1 max-arity)
                                      ", "))))
             (compc-insert-line
              (format "Lisp_Object (*%s) (%s);  /* %s */" c-name params name))))

          (t
           (compc-insert-line
            (format "Lisp_Object (*%s) (ptrdiff_t, Lisp_Object *);  /* %s */" c-name name)))))))


    (compc-insert-line ";")
    (buffer-string)))



(defun compc-insert-base-definitions ()
  "Insert minimal type and macro definitions for compiled code."
  (let* ((offsets (comp--handler-struct-offsets))
         (constants (compc--header-constants))
         (handler-val (nth 0 offsets))
         (handler-next (nth 1 offsets))
         (handler-jmp (nth 2 offsets))
         (thread-handler (nth 3 offsets))
         (use-lsb (if (plist-get constants :use-lsb-tag) 1 0))
         (gctypebits (compc--const-int constants :gctypebits))
         (valbits (compc--const-int constants :valbits))
         (inttypebits (compc--const-int constants :inttypebits))
         (lisp-int0 (compc--const-int constants :lisp-int0))
         (lisp-int1 (compc--const-int constants :lisp-int1))
         (lisp-cons (compc--const-int constants :lisp-cons))
         (lisp-float (compc--const-int constants :lisp-float))
         (lisp-vectorlike (compc--const-int constants :lisp-vectorlike))
         (pvec-bignum (compc--const-int constants :pvec-bignum))
         (mpf (compc--const-int constants :most-positive-fixnum))
         (mnf (compc--const-int constants :most-negative-fixnum))
         (pure-size (compc--const-int constants :pure-size))
         (cons-car (compc--const-int constants :cons-car-offset))
         (cons-cdr (compc--const-int constants :cons-cdr-offset))
         (qnil (compc--const-int constants :qnil))
         (qt (compc--const-int constants :qt))
         (qmany (compc--const-int constants :qmany)))
    (insert "#include <stddef.h>\n#include <stdint.h>\n#include <stdbool.h>\n#include <limits.h>\n#include <setjmp.h>\n\n")
    (insert "struct freloc_link_table;\n\n")
    (insert "/* Basic Lisp types */\ntypedef intptr_t Lisp_Object;\n")
    (insert "typedef intptr_t EMACS_INT;\ntypedef uintptr_t EMACS_UINT;\n\n")
    (insert "/* Constants derived from the running Emacs. */\n")
    (insert (format "#define USE_LSB_TAG %d\n" use-lsb))
    (insert (format "#define GCTYPEBITS %d\n" gctypebits))
    (insert (format "#define VALBITS %d\n" valbits))
    (insert (format "#define INTTYPEBITS %d\n" inttypebits))
    (insert (format "#define FIXNUM_BITS (VALBITS + 1)\n"))
    (insert (format "#define LISP_INT0 %d\n" lisp-int0))
    (insert (format "#define LISP_INT1 %d\n" lisp-int1))
    (insert (format "#define LISP_CONS_TAG %d\n" lisp-cons))
    (insert (format "#define LISP_FLOAT_TAG %d\n" lisp-float))
    (insert (format "#define LISP_VECTORLIKE_TAG %d\n" lisp-vectorlike))
    (insert (format "#define PVEC_BIGNUM %d\n" pvec-bignum))
    (insert (format "#define MOST_POSITIVE_FIXNUM %d\n" mpf))
    (insert (format "#define MOST_NEGATIVE_FIXNUM %d\n" mnf))
    (insert (format "#define PURESIZE %d\n" pure-size))
    (insert (format "#define CONS_CAR_OFFSET %d\n" cons-car))
    (insert (format "#define CONS_CDR_OFFSET %d\n" cons-cdr))
    (insert (format "#define Qnil ((Lisp_Object)%d)\n" qnil))
    (insert (format "#define Qt ((Lisp_Object)%d)\n" qt))
    (insert (format "#define Qmany ((Lisp_Object)%d)\n" qmany))
    (insert "#define CONST Qnil\n")
    (insert "#define TAG_SHIFT (USE_LSB_TAG ? 0 : VALBITS)\n")
    (insert "#define TAG_MASK (((uintptr_t)1 << GCTYPEBITS) - 1)\n")
    (insert "#define INTTYPE_MASK (((uintptr_t)1 << INTTYPEBITS) - 1)\n")
    (insert "#define LISP_WORD_TAG(tag) ((uintptr_t)(tag) << TAG_SHIFT)\n")
    (insert "#define INTMASK (INTPTR_MAX >> (INTTYPEBITS - 1))\n\n")
    (insert "/* Thread state relocation (filled by loader) */\nextern void **current_thread_reloc;\n\n")
    (insert (format "#define HANDLER_VAL_OFFSET %d\n" handler-val))
    (insert (format "#define HANDLER_NEXT_OFFSET %d\n" handler-next))
    (insert (format "#define HANDLER_JMP_OFFSET %d\n" handler-jmp))
    (insert (format "#define THREAD_HANDLERLIST_OFFSET %d\n\n" thread-handler))
    (insert "#define GET_HANDLER_VAL(h) \\\n    (*(Lisp_Object *)((char *)(h) + HANDLER_VAL_OFFSET))\n")
    (insert "#define GET_HANDLER_NEXT(h) \\\n    (*(comp_handler_ptr *)((char *)(h) + HANDLER_NEXT_OFFSET))\n")
    (insert "#define GET_HANDLER_JMP(h) \\\n    ((jmp_buf *)((char *)(h) + HANDLER_JMP_OFFSET))\n")
    (insert "#define GET_HANDLERLIST() \\\n    (*(comp_handler_ptr *)((char *)(*current_thread_reloc) + THREAD_HANDLERLIST_OFFSET))\n")
    (insert "#define SET_HANDLERLIST(val) \\\n    (*(comp_handler_ptr *)((char *)(*current_thread_reloc) + THREAD_HANDLERLIST_OFFSET) = (val))\n\n")
    (insert "/* Opaque handler pointer */\ntypedef void* comp_handler_ptr;\n\n")
    (insert (compc-generate-freloc-struct))
    (insert "\n/* Helper functions mirroring src/lisp.h. */\n")
    (insert "static inline uintptr_t compc_xli (Lisp_Object obj) { return (uintptr_t)obj; }\n")
    (insert "static inline bool compc_tagged_p (Lisp_Object obj, uintptr_t tag) {\n    uintptr_t value = compc_xli (obj);\n    if (!USE_LSB_TAG) value >>= VALBITS;\n    return ((value - tag) & TAG_MASK) == 0;\n}\n")
    (insert "static inline bool compc_consp (Lisp_Object obj) { return compc_tagged_p (obj, LISP_CONS_TAG); }\n")
    (insert "static inline bool compc_floatp (Lisp_Object obj) { return compc_tagged_p (obj, LISP_FLOAT_TAG); }\n")
    (insert "static inline bool compc_fixnump (Lisp_Object obj) {\n    uintptr_t value = compc_xli (obj);\n    if (!USE_LSB_TAG) value >>= FIXNUM_BITS;\n    uintptr_t tag = (uintptr_t)(LISP_INT0 >> (USE_LSB_TAG ? 0 : 1));\n    return ((value - tag) & INTTYPE_MASK) == 0;\n}\n")
    (insert "static inline EMACS_INT compc_xfixnum (Lisp_Object obj) {\n    EMACS_INT val = (EMACS_INT)compc_xli (obj);\n    if (!USE_LSB_TAG) { EMACS_UINT u = (EMACS_UINT)val; val = (EMACS_INT)(u << INTTYPEBITS); }\n    return val >> INTTYPEBITS;\n}\n")
    (insert "static inline Lisp_Object compc_make_fixnum (EMACS_INT n) {\n    EMACS_INT int0 = LISP_INT0;\n    if (USE_LSB_TAG) { EMACS_UINT u = (EMACS_UINT)n; n = (EMACS_INT)(u << INTTYPEBITS); n += int0; }\n    else { n &= INTMASK; n += (int0 << VALBITS); }\n    return (Lisp_Object)n;\n}\n")
    (insert "static inline char *compc_xcons_ptr (Lisp_Object obj) {\n    return (char *)(compc_xli (obj) - LISP_WORD_TAG (LISP_CONS_TAG));\n}\n")
    (insert "static inline Lisp_Object compc_xcar (Lisp_Object obj) {\n    return *(Lisp_Object *)(compc_xcons_ptr (obj) + CONS_CAR_OFFSET);\n}\n")
    (insert "static inline Lisp_Object compc_xcdr (Lisp_Object obj) {\n    return *(Lisp_Object *)(compc_xcons_ptr (obj) + CONS_CDR_OFFSET);\n}\n")
    (insert "static inline void compc_xsetcar (Lisp_Object obj, Lisp_Object val) {\n    *(Lisp_Object *)(compc_xcons_ptr (obj) + CONS_CAR_OFFSET) = val;\n}\n")
    (insert "static inline void compc_xsetcdr (Lisp_Object obj, Lisp_Object val) {\n
*(Lisp_Object *)(compc_xcons_ptr (obj) + CONS_CDR_OFFSET) = val;\n}\n")
    (insert "static inline Lisp_Object compc_bool_to_lisp (bool value) { return value ? Qt : Qnil; }\n")
    (insert "static inline bool compc_pure_p (void *ptr) {\n    extern void **pure_reloc;\n    if (!pure_reloc || !*pure_reloc) return false;\n    uintptr_t base = (uintptr_t)(*pure_reloc);\n    uintptr_t offset = (uintptr_t)((char *)ptr - (char *)base);\n    return offset <= (uintptr_t)PURESIZE;\n}\n")
    (insert "static inline void compc_check_impure (struct freloc_link_table *fn, Lisp_Object obj, void *ptr) {\n    if (compc_pure_p (ptr)) fn->pure_write_error (obj);\n}\n")
    (insert "static inline bool compc_bignump (struct freloc_link_table *fn, Lisp_Object obj) {\n    if (!compc_tagged_p (obj, LISP_VECTORLIKE_TAG))\n        return false;\n    return fn->helper_PSEUDOVECTOR_TYPEP_XUNTAG (obj, PVEC_BIGNUM);\n}\n")
    (insert "static inline void compc_maybe_gc_or_quit (struct freloc_link_table *fn) {\n    static unsigned int quitcounter;\n    quitcounter++;\n    if (quitcounter >> 9) { quitcounter = 0; fn->maybe_gc (); fn->maybe_quit (); }\n}\n")
    (insert "#define TAGGEDP(obj, tag) compc_tagged_p ((obj), (tag))\n")
    (insert "#define CONSP(obj) compc_consp (obj)\n")
    (insert "#define FLOATP(obj) compc_floatp (obj)\n")
    (insert "#define FIXNUMP(obj) compc_fixnump (obj)\n")
    (insert "#define XFIXNUM(obj) compc_xfixnum (obj)\n")
    (insert "#define make_fixnum(n) compc_make_fixnum (n)\n")
    (insert "#define XCAR(obj) compc_xcar (obj)\n")
    (insert "#define XCDR(obj) compc_xcdr (obj)\n")
    (insert "#define XSETCAR(obj, val) compc_xsetcar ((obj), (val))\n")
    (insert "#define XSETCDR(obj, val) compc_xsetcdr ((obj), (val))\n")
    (insert "#define BOOL_TO_LISP(val) compc_bool_to_lisp (val)\n")
    (insert "#define BIGNUMP(obj) compc_bignump (fn, (obj))\n")
    (insert "#define CHECK_IMPURE(obj, ptr) compc_check_impure (fn, (obj), (ptr))\n\n")
    (insert "/* Static object type */\ntypedef struct { ptrdiff_t len; char data[]; } static_obj_t;\n")
    (insert "/* Enums for runtime functions */\nenum Set_Internal_Bind { SET_INTERNAL_SET, SET_INTERNAL_BIND, SET_INTERNAL_UNBIND, SET_INTERNAL_THREAD_SWITCH };\n")
    (insert "/* Handler type enum (must match src/lisp.h) */\nenum handlertype { CATCHER = 0, CONDITION_CASE = 1 };\n\n")
    (insert "/* Stubs */\nstatic inline Lisp_Object build_string(const char *str) { (void)str; return Qnil; }\n")
    (insert "static inline Lisp_Object intern_c_string(const char *str) { (void)str; return Qnil; }\n")
    (insert "static inline Lisp_Object comp_maybe_gc_or_quit(ptrdiff_t n, Lisp_Object *args) { (void)n; (void)args; return Qnil; }\n")
    (insert "static inline Lisp_Object Fcons(Lisp_Object car, Lisp_Object cdr) { (void)car; (void)cdr; return Qnil; }\n")

    (insert "
/* Comp unit structure */
struct Lisp_Native_Comp_Unit {
    Lisp_Object header;
};

/* Defines */
#define config_h 1
#define lisp_h 1
#define comp_h 1

/* Macros */
#define CALL(f, ...) (fn->f (__VA_ARGS__))
#define RELOC(i) d_reloc[i]
#define RELOC_IMP(i) d_reloc_imp[i]
#define RELOC_EPH(i) d_reloc_eph[i]
#define LIST(...) (Lisp_Object[]){__VA_ARGS__}

#define DEFBLOB(name, str) \\
  struct { ptrdiff_t len; char data[sizeof(str)]; } name ## _blob = \\
    { .len = sizeof(str), .data = str }; \\
  static static_obj_t *name = (static_obj_t *)&name ## _blob

#define REGISTER_SUBR(name_idx, cname_idx, min, max, rest_idx) \\
  fn->f_comp__register_subr(RELOC_EPH(name_idx), RELOC_EPH(cname_idx), \\
                            make_fixnum(min), make_fixnum(max), \\
                            Qnil, RELOC_EPH(rest_idx), comp_u)

#define ARGS_0    (void)
#define ARGS_1    (Lisp_Object arg0)
#define ARGS_2    (Lisp_Object arg0, Lisp_Object arg1)
#define ARGS_3    (Lisp_Object arg0, Lisp_Object arg1, Lisp_Object arg2)
#define ARGS_MANY (ptrdiff_t nargs, Lisp_Object *args)

#define DEFUN(lisp_name, c_name, args) \\
  Lisp_Object c_name args
"
            )))

;;;###autoload
(defun comphack-codegen-ensure-freloc-h ()
  "Ensure ABI-versioned freloc.h exists, generating if necessary.
Returns the filename of the freloc header (e.g., \"generated/freloc-2b8d5670.h\")."
  (require 'comphack)
  (let* ((abi-hash (comphack-get-abi-hash))
         ;; `load-file-name' is dynamically bound and may name the Lisp file
         ;; whose loading happened to request compilation.  Keep generated
         ;; headers rooted at the Comphack installation instead.
         (base-dir (or (and (boundp 'comphack-base-dir) comphack-base-dir)
                       (and load-file-name (file-name-directory load-file-name))
                       default-directory))
         (gen-dir (expand-file-name "generated" base-dir))
         (freloc-filename (format "freloc-%s.h" abi-hash))
         (freloc-file (expand-file-name freloc-filename gen-dir))
         (tmp-file (expand-file-name (format ".%s.tmp.%d" freloc-filename (emacs-pid)) gen-dir))
         (guard-name (upcase (replace-regexp-in-string "[^A-Z0-9]" "_" freloc-filename))))

    (unless (file-directory-p gen-dir)
      (make-directory gen-dir t))

    (with-temp-file tmp-file
      (insert (format "#ifndef %s\n" guard-name))
      (insert (format "#define %s\n\n" guard-name))
      (insert (format "/* Generated for Emacs ABI hash: %s */\n\n" abi-hash))
      (compc-insert-base-definitions)
      (insert (format "\n#endif /* %s */\n" guard-name)))

    (rename-file tmp-file freloc-file t)
    (comp-log (format "Generated %s" (concat "generated/" freloc-filename)))
    (concat "generated/" freloc-filename)))

(provide 'comphack-codegen)
;;; comphack-codegen.el ends here
