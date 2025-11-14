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

;;; Configuration

(defconst compc--pseudo-subr-map
  '(("add1" . "1+")
    ("sub1" . "1-")
    ("negate" . "-"))
  "Map of compiler-only pseudo-subrs to real primitive names.")

(defconst compc--helper-prototypes
  '((wrong_type_argument . ("Lisp_Object" "(Lisp_Object, Lisp_Object)"))
    (helper_PSEUDOVECTOR_TYPEP_XUNTAG . ("Lisp_Object" "(Lisp_Object, Lisp_Object)"))
    (pure_write_error . ("Lisp_Object" "(Lisp_Object)"))
    (push_handler . ("Lisp_Object" "(Lisp_Object, Lisp_Object)"))
    (record_unwind_protect_excursion . ("Lisp_Object" "(void)"))
    (helper_unbind_n . ("Lisp_Object" "(Lisp_Object)"))
    (helper_save_restriction . ("Lisp_Object" "(void)"))
    (helper_GET_SYMBOL_WITH_POSITION . ("Lisp_Object" "(Lisp_Object)"))
    (helper_sanitizer_assert . ("Lisp_Object" "(Lisp_Object, Lisp_Object)"))
    (record_unwind_current_buffer . ("Lisp_Object" "(void)"))
    (set_internal . ("Lisp_Object" "(Lisp_Object, Lisp_Object, Lisp_Object, Lisp_Object)"))
    (helper_unwind_protect . ("Lisp_Object" "(Lisp_Object)"))
    (specbind . ("Lisp_Object" "(Lisp_Object, Lisp_Object)"))
    (maybe_gc . ("Lisp_Object" "(void)"))
    (maybe_quit . ("Lisp_Object" "(void)")))
  "Alist describing helper prototypes keyed by helper symbol.")

(defvar compc--runtime-helper-symbols-cache nil
  "Cached list of helper symbols in runtime order.")

(defvar compc--runtime-helper-name-cache nil
  "Cached list of helper names as strings.")

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

(defun compc--canonicalize-func-name (func-name)
  "Return FUNC-NAME mapped to the underlying primitive, if needed."
  (or (alist-get func-name compc--pseudo-subr-map nil nil #'string=)
      func-name))

(defun compc--helper-name-p (func-name)
  "Return non-nil if FUNC-NAME (a string) names a runtime helper."
  (member func-name (compc--runtime-helper-names)))

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
  (pcase val
    (`nil "Qnil")
    (`t "Qt")
    ((pred integerp)
     (format "make_fixnum (%d)" val))
    ;; Direct call to create a closure: (direct-call "C-name" slot1 slot2 ...)
    (`(direct-call ,c-name . ,closure-slots)
     (if closure-slots
         (let ((args-str (mapconcat (lambda (slot) (format "s%d" slot))
                                    closure-slots ", ")))
           (format "%s (%s)" c-name args-str))
       (format "%s ()" c-name)))
    (_
     (let ((idx (and compc--d-default-idx (gethash val compc--d-default-idx))))
       (cond
        (idx
         (format "RELOC (%d)" idx))
        ((and compc--d-impure-idx
              (setq idx (gethash val compc--d-impure-idx)))
         (format "RELOC_IMP (%d)" idx))
        ((and compc--d-ephemeral-idx
              (setq idx (gethash val compc--d-ephemeral-idx)))
         (format "RELOC_EPH (%d)" idx))
        (t
         (error "Immediate not found in any reloc idx: %S" val)))))))

(defun compc-mvar-to-c (mvar)
  "Convert MVAR to C variable reference or constant."
  (pcase mvar
    ((pred integerp)
     (format "s%d" mvar))

    (`(mvar . ,plist)
     (let ((slot (plist-get plist :slot))
           (val (plist-get plist :val)))
       (if slot
           (format "s%d" slot)
         (compc-immediate-to-c val))))

    ((and mv (pred comp-mvar-p))
     (if (comp-mvar-slot mv)
         (format "s%d" (comp-mvar-slot mv))
       (compc-immediate-to-c (comp-mvar-const mv))))

    (_ (compc-immediate-to-c mvar))))

(defun compc-get-subr-arity (func-name)
  "Get arity of built-in function FUNC-NAME.
Returns cons (min . max) or nil if not found."
  (condition-case nil
      (let ((sym (intern func-name)))
        (when (fboundp sym)
          (subr-arity (symbol-function sym))))
    (error nil)))

(defun compc-freloc-call (func-name args &optional dst)
  "Generate freloc function call for FUNC-NAME with ARGS.
If DST is non-nil, assigns result to DST."
  (let ((canonical-name (compc--canonicalize-func-name func-name)))
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
     (compc-freloc-call
      (symbol-name func)
      (mapcar #'compc-mvar-to-c args)
      (compc-mvar-to-c dst)))

    (`(set ,dst (call ,func . ,args))
     (let ((func-name (if (symbolp func) (symbol-name func) (format "%s" func))))
       (if (equal func-name "comp-maybe-gc-or-quit")
           (format "%s = comp_maybe_gc_or_quit (%d, %s);"
                   (compc-mvar-to-c dst)
                   (length args)
                   (if (zerop (length args)) "NULL"
                     (format "LIST (%s)" (mapconcat #'compc-mvar-to-c args ", "))))
         (compc-freloc-call func-name
                            (mapcar #'compc-mvar-to-c args)
                            (compc-mvar-to-c dst)))))

    (`(set ,dst ,src)
     (format "%s = %s;"
             (compc-mvar-to-c dst)
             (compc-mvar-to-c src)))

    (`(callref ,func . ,args)
     (compc-freloc-call
      (symbol-name func)
      (mapcar #'compc-mvar-to-c args)
      nil))

    (`(call ,func . ,args)
     (let ((func-name (if (symbolp func) (symbol-name func) (format "%s" func))))
       (if (equal func-name "comp-maybe-gc-or-quit")
           (format "comp_maybe_gc_or_quit (%d, %s);"
                   (length args)
                   (if (zerop (length args)) "NULL"
                     (format "LIST (%s)" (mapconcat #'compc-mvar-to-c args ", "))))
         (compc-freloc-call func-name
                            (mapcar #'compc-mvar-to-c args)
                            nil))))

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
                     (t cmp))))
       (if (null cmp-val)
           (format "if (!%s)\n  goto %s;\nelse\n  goto %s;"
                   (compc-mvar-to-c test)
                   true-bb
                   false-bb)
         (format "if (%s)\n  goto %s;\nelse\n  goto %s;"
                 (compc-mvar-to-c test)
                 true-bb
                 false-bb))))

    (`(set-par-to-local ,dst ,n)
     (if compc-func-is-fixed-arity
         (format "%s = arg%d;" (compc-mvar-to-c dst) n)
       (format "%s = args[%d];" (compc-mvar-to-c dst) n)))

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

    (`(phi ,dst . ,_)
     ;; PHI nodes generate no code - handled by patching predecessor blocks
     nil)

    (`(assume . ,_)
     ;; Assume instructions generate no code - purely for type analysis
     nil)

    (_ (format "/* TODO: %S */" insn))))

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
  (pcase-let* (((map :c-name :name :args :frame-size :blocks) func)
               (args-clean (cond
                            ((comp-args-p args)
                             (list (aref args 1) (aref args 2)))
                            ((listp args) args)
                            (t '(0 0))))
               (min-args (car args-clean))
               (max-args (cadr args-clean))
               (has-rest-args (compc-func-has-rest-args-p func))
               (fixed-arity (and (numberp min-args)
                                (numberp max-args)
                                (= min-args max-args)
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
          (func-start (point))
          (lisp-name (if (symbol-with-pos-p name)
                        (symbol-name (bare-symbol name))
                      (symbol-name name))))
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
  "Escape STR for use in C string literal."
  (with-temp-buffer
    (insert str)
    (goto-char (point-min))
    (while (re-search-forward "[\"\\]" nil t)
      (replace-match "\\\\\\&" nil nil))
    (goto-char (point-min))
    (while (re-search-forward "\n" nil t)
      (replace-match "\\\\n" nil nil))
    (buffer-string)))

(defun compc-insert-blob (name obj)
  "Insert static blob declaration for NAME containing OBJ.
Uses C raw string literals (GCC extension with -std=gnu99) with
unique delimiter to avoid conflicts."
  (let ((serialized (let ((print-length nil)
                          (print-level nil)
                          (print-circle t)
                          (print-escape-newlines t)
                          (print-escape-multibyte t))
                      (prin1-to-string obj))))
    (insert "\n")
    (compc-insert-line (format "DEFBLOB (%s,\n  R\"LISP(%s)LISP\");" name serialized))))

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
  (compc-insert-line "struct thread_state ***current_thread_reloc;")
  (compc-insert-line "bool **f_symbols_with_pos_enabled_reloc;")
  (compc-insert-line "void **pure_reloc;")
  (compc-insert-line "struct freloc_link_table *freloc_link_table;")
  (insert "\n"))

(defun compc-insert-top-level-run (minimal)
  "Insert top_level_run entry point from MINIMAL context."
  (let ((functions (plist-get minimal :functions))
        (d-ephemeral-idx (plist-get minimal :d-ephemeral-idx)))

    (compc-insert-line "/* Entry point */")
    (compc-insert-line "Lisp_Object top_level_run (Lisp_Object comp_u)")
    (compc-with-block
     (compc-insert-line "struct freloc_link_table *fn = freloc_link_table;")
     (compc-insert-line "comp_unit = comp_u;")

     (let ((user-funcs (cl-remove-if
                        (lambda (f)
                          (equal (plist-get f :c-name) "top_level_run"))
                        functions)))

       (dolist (func user-funcs)
         (let* ((name-raw (plist-get func :name))
                (c-name (plist-get func :c-name))
                (args (plist-get func :args))
                (name (if (symbol-with-pos-p name-raw)
                          (bare-symbol name-raw)
                        name-raw))
                (args-clean (cond
                             ((comp-args-p args)
                              (list (comp-args-min args) (comp-args-max args)))
                             ((comp-nargs-p args)
                              (list (comp-nargs-min args) (comp-nargs-nonrest args)))
                             ((listp args) args)
                             (t (error "Unknown args type for function %s: %S" name args))))
                (min-args (car args-clean))
                (max-args (cadr args-clean))
                (has-rest-args (compc-func-has-rest-args-p func))
                ;; If function has rest args, max-args should be MANY (-2)
                (effective-max-args (if has-rest-args -2 max-args))
                (name-idx (gethash name d-ephemeral-idx))
                (c-name-idx (gethash c-name d-ephemeral-idx)))

           (when (and name-idx c-name-idx)
             (compc-insert-line
              (format "REGISTER_SUBR (%d, %d, %d, %d, %d);  /* %s */"
                      name-idx c-name-idx
                      (or min-args 0) (or effective-max-args -1)
                      (1+ c-name-idx) name))))))

     (insert "\n")
     (compc-insert-line "return Qt;"))))

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
          (buffer-undo-list t)
          (inhibit-modification-hooks t))
     ; (c-mode)
      (font-lock-mode -1)
      (setq c-default-style "gnu")

      ;; Includes
      (compc-insert-line "#include \"comphack.h\"")
      (compc-insert-line (format "#include \"%s\"" freloc-h))
      (insert "\n")

      ;; Relocation arrays (needed by functions)
      (compc-insert-reloc-arrays minimal)
      (insert "\n")

      ;; Exports
      (compc-insert-exports)

      ;; top_level_run first
      (compc-insert-top-level-run minimal)
      (insert "\n")

      (let ((user-funcs (cl-remove-if
                         (lambda (f)
                           (equal (plist-get f :c-name) "top_level_run"))
                         functions)))

        (when user-funcs
          (insert "\n")
          (dolist (func user-funcs)
            (pcase-let* (((map :c-name :args) func)
                         (args-clean (cond
                                      ((comp-args-p args)
                                       (list (aref args 1) (aref args 2)))
                                      ((listp args) args)
                                      (t '(0 0))))
                         (min-args (car args-clean))
                         (max-args (cadr args-clean))
                         (has-rest-args (compc-func-has-rest-args-p func))
                         (fixed-arity (and (numberp min-args)
                                           (numberp max-args)
                                           (= min-args max-args)
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


;;;###autoload
(defun comphack-codegen-ensure-freloc-h ()
  "Ensure ABI-versioned freloc.h exists, generating if necessary.
Returns the filename of the freloc header (e.g., \"generated/freloc-2b8d5670.h\")."
  (require 'comphack)
  (let* ((abi-hash (comphack-get-abi-hash))
         (base-dir (or (and load-file-name (file-name-directory load-file-name))
                       (and (boundp 'comphack-base-dir) comphack-base-dir)
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
      (insert "#include \"../comphack.h\"\n\n")
      (insert (format "/* Generated for Emacs ABI hash: %s */\n\n" abi-hash))
      (insert (compc-generate-freloc-struct))
      (insert (format "\n#endif /* %s */\n" guard-name)))

    (rename-file tmp-file freloc-file t)
    (message "Generated %s" (concat "generated/" freloc-filename))
    (concat "generated/" freloc-filename)))

(provide 'comphack-codegen)
;;; comphack-codegen.el ends here
