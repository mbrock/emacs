;;; comphack.el --- Clean Elisp→C native compiler -*- lexical-binding: t -*-

;; Author: mbrock
;; Version: 2.0
;; Package-Requires: ((emacs "28.1"))

;;; Commentary:

;; A straightforward implementation of native Elisp compilation via C generation.
;; This bypasses libgccjit by generating C source code from LIMPLE IR.
;;
;; Main entry points:
;;   (comphack-compile-to-c "foo.el" "foo.c")
;;   (comphack-compile-to-eln "foo.el" "foo.eln")

;;; Code:

(require 'comp)
(require 'cl-lib)
(require 'comphack-codegen)

;;; Configuration

(defvar comphack-emacs-source-dir
  (or (getenv "EMACS_SRC")
      (and (boundp 'source-directory)
           (expand-file-name "src" source-directory))
      "/usr/include/emacs")
  "Directory containing Emacs C source headers.")

(defun comphack-get-abi-hash ()
  "Get the Emacs ABI hash (native compilation version identifier)."
  (or (and (boundp 'comp-abi-hash) comp-abi-hash)
      (and (boundp 'comp-native-version-dir)
           (file-name-nondirectory (directory-file-name comp-native-version-dir)))
      "unknown"))

(defvar comphack-compiler-flags
  '("-shared" "-fPIC" "-O0" "-w"
    "-fno-stack-protector" "-fno-toplevel-reorder")
  "Flags passed to the compiler when compiling C to .eln.
The -fno-toplevel-reorder flag is critical to preserve blob declaration order.")

(defvar comphack-linker-flags
  (when (memq system-type '(gnu gnu/linux gnu/kfreebsd berkeley-unix usg-unix-v))
    '("-Wl,-Bsymbolic"))
  "Platform linker flags used to bind references within each .eln.
Comphack's exported function and data names are intentionally discoverable by
the Emacs loader, but many recur in different compilation units.  ELF's normal
symbol interposition would otherwise let one loaded .eln capture another
.eln's internal references.")

(defvar comphack-base-dir
  (file-name-directory (or load-file-name buffer-file-name))
  "Base directory of comphack installation.")

;;; State

(defvar comphack--last-ctxt nil
  "Most recently compiled comp-ctxt, for debugging.")

(defvar comphack--last-minimal nil
  "Most recently extracted minimal context, for debugging.")

(defvar comphack--captured-ctxt nil
  "Temporary variable for capturing comp-ctxt during compilation.")

;;; LIMPLE IR Extraction

(defun comphack--capture-hook (_)
  "Hook function to capture comp-ctxt during compilation."
  (setq comphack--captured-ctxt comp-ctxt))

(defun comphack--extract-limple (source-file)
  "Compile SOURCE-FILE and extract LIMPLE IR as comp-ctxt.
Uses Emacs's native-compile in dry-run mode to capture the IR."
  (let ((comp-dry-run t)
        (native-comp-verbose 0)
        (native-comp-speed 2)
        (native-comp-eln-load-path (list (temporary-file-directory)))
        (comphack--captured-ctxt nil))
    (push '(comp--final comphack--capture-hook) comp-post-pass-hooks)

    (unwind-protect
        (progn
          (native-compile source-file)
          (unless comphack--captured-ctxt
            (error "Compilation did not produce comp-ctxt"))
          (setq comphack--last-ctxt comphack--captured-ctxt)
          comphack--captured-ctxt)

      ;; Always remove our hook
      (setq comp-post-pass-hooks
            (assoc-delete-all 'comp--final comp-post-pass-hooks)))))

;;; Minimal Context Extraction

(defconst comphack--type-hint-symbols '(fixnum cons)
  "Type hints accepted by `comp-mvar-type-hint-match-p'.
These are the only type hints that comp.c understands.")

(defun comphack--collect-type-hints (mvar)
  "Return list of type symbols proven for MVAR.
Only returns type hints that comp.c actually understands (fixnum, cons)."
  (when (and (comp-mvar-p mvar)
             (fboundp 'comp-mvar-type-hint-match-p))
    (let (hints)
      (dolist (sym comphack--type-hint-symbols)
        (when (comp-mvar-type-hint-match-p mvar sym)
          (cl-pushnew sym hints)))
      hints)))

(defun comphack--clean-insn (insn)
  "Remove unprintable objects from INSN for serialization.
Returns either a slot number, a constant value wrapper, or a plist representation."
  (cond
   ((comp-mvar-p insn)
    ;; If mvar has a slot, use the slot number or symbol (e.g., 'scratch')
    (let* ((slot (comp-mvar-slot insn))
           (const-val (comp-cstr-imm insn))
           (valset (comp-cstr-valset insn))
           (type-hints (comphack--collect-type-hints insn))
           (plist nil))
      (cond
       (slot
        (setq plist (plist-put plist :slot slot)))
       (const-val
        (setq plist (plist-put plist :val const-val)))
       ((and valset (= (length valset) 1))
        (let ((val (car valset)))
          ;; Only treat as constant if it's a known constant type
          (if (or (null val)        ; nil
                  (eq val t)        ; t
                  (numberp val)     ; numbers
                  (stringp val)     ; strings
                  (vectorp val)     ; vectors
                  (consp val))      ; conses
              (setq plist (plist-put plist :val val))
            ;; Symbol but not a known constant - keep as mvar representation
            (setq plist (plist-put plist :val val)))))
       ;; No clear constant value - keep placeholder
       (t
        (setq plist (plist-put plist :val nil))))
      (when type-hints
        (setq plist (plist-put plist :type-hints type-hints)))
      `(mvar ,@plist)))
   ((proper-list-p insn)
    (mapcar #'comphack--clean-insn insn))
   (t insn)))

(defun comphack--contains-positioned-symbol-p (obj &optional seen)
  "Return non-nil if OBJ contains a symbol-with-position."
  (let ((seen (or seen (make-hash-table :test #'eq)))
        (pending (list obj)))
    (catch 'found
      (while pending
        (let ((value (pop pending)))
          (cond
           ((symbol-with-pos-p value)
            (throw 'found t))
           ((and (consp value) (not (gethash value seen)))
            (puthash value t seen)
            (push (car value) pending)
            (push (cdr value) pending))
           ((and (vectorp value) (not (gethash value seen)))
            (puthash value t seen)
            (dotimes (i (length value))
              (push (aref value i) pending))))))
      nil)))

(defun comphack--copy-without-positions (obj seen)
  "Copy OBJ into graph SEEN while stripping symbol positions."
  (let (pending)
    (cl-labels
        ((copy-value
          (value)
          (cond
           ((symbol-with-pos-p value)
            (bare-symbol value))
           ((or (consp value) (vectorp value))
            (or (gethash value seen)
                (let ((copy (if (consp value)
                                (cons nil nil)
                              (make-vector (length value) nil))))
                  (puthash value copy seen)
                  (push (vector value copy) pending)
                  copy)))
           (t value))))
      (let ((result (copy-value obj)))
        (while pending
          (let* ((pair (pop pending))
                 (source (aref pair 0))
                 (copy (aref pair 1)))
            (if (consp source)
                (progn
                  (setcar copy (copy-value (car source)))
                  (setcdr copy (copy-value (cdr source))))
              (dotimes (i (length source))
                (aset copy i (copy-value (aref source i)))))))
        result))))

(defun comphack--strip-positions (obj)
  "Strip position info from OBJ recursively.
Handles symbols-with-pos, vectors, conses, sharing, and circular structure.
Objects without positioned symbols retain their identity."
  (if (comphack--contains-positioned-symbol-p obj)
      (comphack--copy-without-positions
       obj (make-hash-table :test #'eq))
    obj))

(defun comphack--extract-data-container (container)
  "Extract serialized data from CONTAINER.
Returns cons of (vector . index-hash) mapping objects to indices.
Preserves both the ordering and indexing computed by `comp--finalize-relocs'.
Strips position info from symbols-with-pos keys for proper lookup.
When multiple keys with different positions map to the same bare key,
keeps only the first one (smallest integer index)."
  (let* ((objects (vconcat (comp-data-container-l container)))
         (old-idx-map (comp-data-container-idx container))
         (idx-map (make-hash-table :test (hash-table-test old-idx-map)
                                    :size (hash-table-count old-idx-map))))
    ;; Rebuild index hash table with bare symbols as keys (recursively)
    ;; Keep only integer values and the first occurrence when there are duplicates
    (maphash
     (lambda (key value)
       (when (integerp value)  ; Only include integer indices
         (let ((bare-key (comphack--strip-positions key)))
           ;; Only add if not already present, or if this value is smaller
           (let ((existing (gethash bare-key idx-map)))
             (when (or (null existing)
                       (< value existing))
               (puthash bare-key value idx-map))))))
     old-idx-map)
    (cons objects idx-map)))

(defun comphack--simplify-ctxt (ctxt)
  "Extract minimal compilation context from COMP-CTXT.
Returns plist with only fields needed for C generation."
  ;; Finalize relocations first to populate data container lists
  (let ((comp-ctxt ctxt))
    (comp--finalize-relocs))

  ;; AFTER finalize-relocs, use lambda-fixups-h to get lambda → d-impure-idx mapping
  ;; lambda-fixups-h maps byte-func → reloc-mvar, we need c-name → reloc-idx (integer)
  (let ((lambda-impure-idx (make-hash-table :test 'equal)))
    (maphash
     (lambda (c-name func)
       (when-let ((byte-func (comp-func-byte-func func)))
         ;; Look up this byte-func in lambda-fixups-h
         (when-let ((reloc-mvar (gethash byte-func (comp-ctxt-lambda-fixups-h ctxt))))
           ;; Extract integer index from comp-mvar
           ;; Check slot first, then valset, then range
           (let ((idx (or (comp-mvar-slot reloc-mvar)
                          (and (comp-cstr-valset reloc-mvar)
                               (car (comp-cstr-valset reloc-mvar)))
                          (and (comp-cstr-range reloc-mvar)
                               (car (car (comp-cstr-range reloc-mvar)))))))
             (when idx
               (puthash c-name idx lambda-impure-idx))))))
     (comp-ctxt-funcs-h ctxt))

    (let ((funcs-list nil)
          (function-docs (comp-ctxt-function-docs ctxt))
          (doc-to-idx (make-hash-table :test 'equal)))

    ;; Build reverse mapping from doc-string to doc-idx
    ;; function-docs is a vector where index is doc-idx
    (dotimes (idx (length function-docs))
      (puthash (aref function-docs idx) idx doc-to-idx))

    ;; Extract all functions
    (maphash
     (lambda (c-name func)
       (let ((blocks-list nil))
         ;; Extract all basic blocks
         (maphash
          (lambda (bb-name bb)
            (push (list :name bb-name
                       :insns (mapcar #'comphack--clean-insn
                                     (comp-block-insns bb))
                       :in-edges (mapcar (lambda (e)
                                          (comp-block-name (comp-edge-src e)))
                                        (comp-block-in-edges bb))
                       :out-edges (mapcar (lambda (e)
                                           (comp-block-name (comp-edge-dst e)))
                                         (comp-block-out-edges bb)))
                  blocks-list))
          (comp-func-blocks func))

         (let ((doc (comp-func-doc func)))
           (push (list :c-name c-name
                      :name (comp-func-name func)
                      :args (if (comp-func-l-p func)
                                (comp-func-l-args func)
                              (comp-func-d-lambda-list func))
                      :frame-size (comp-func-frame-size func)
                      :speed (comp-func-speed func)
                      :pure (comp-func-pure func)
                      :doc-idx (gethash doc doc-to-idx)
                      :int-spec (comp-func-int-spec func)
                      :command-modes (comp-func-command-modes func)
                      :blocks (nreverse blocks-list))
                 funcs-list))))
     (comp-ctxt-funcs-h ctxt))

    ;; Extract data containers
    (let ((d-default (comphack--extract-data-container
                     (comp-ctxt-d-default ctxt)))
          (d-impure (comphack--extract-data-container
                    (comp-ctxt-d-impure ctxt)))
          (d-ephemeral (comphack--extract-data-container
                       (comp-ctxt-d-ephemeral ctxt))))

      (list :functions (nreverse funcs-list)
            :d-default (car d-default)
            :d-default-idx (cdr d-default)
            :d-impure (car d-impure)
            :d-impure-idx (cdr d-impure)
            :d-ephemeral (car d-ephemeral)
            :d-ephemeral-idx (cdr d-ephemeral)
            :lambda-impure-idx lambda-impure-idx
            :function-docs (comp-ctxt-function-docs ctxt)
            :speed (comp-ctxt-speed ctxt)
            :debug (comp-ctxt-debug ctxt)
            :compiler-options (comp-ctxt-compiler-options ctxt))))))

;;; Public API

;;;###autoload
(defun comphack-compile-to-c (input-file output-file)
  "Compile Elisp INPUT-FILE to C source OUTPUT-FILE.
Returns OUTPUT-FILE on success."
  (interactive "fInput .el file: \nFOutput .c file: ")

  (message "Compiling %s → %s"  (file-name-nondirectory input-file) (file-name-nondirectory output-file))

  ;; Extract LIMPLE IR
  (let ((t1 (current-time)))
    (let* ((ctxt (comphack--extract-limple input-file))
           (t2 (current-time))
           (minimal (comphack--simplify-ctxt ctxt))
           (t3 (current-time)))

      (message "  LIMPLE extraction: %.3fs" (float-time (time-subtract t2 t1)))
      (setq comphack--last-minimal minimal)

      ;; Ensure ABI-versioned freloc.h exists
      (let ((freloc-filename (comphack-codegen-ensure-freloc-h)))

        ;; Generate C source
        (with-temp-file output-file
          (comphack-codegen-insert-complete-eln minimal freloc-filename)))

      (let ((t4 (current-time)))
        (message "  C generation: %.3fs" (float-time (time-subtract t4 t3)))
        (message "Generated %s (%d bytes)"
                 output-file
                 (file-attribute-size (file-attributes output-file))))
      output-file)))

;;;###autoload
(defun comphack-compile-to-eln (input-file &optional output-file)
  "Compile Elisp INPUT-FILE to native .eln OUTPUT-FILE.
If OUTPUT-FILE is nil, uses INPUT-FILE base name with .eln extension.
Returns OUTPUT-FILE on success."
  (interactive "fInput .el file: ")

  (let* ((base (file-name-sans-extension input-file))
         (c-file (make-temp-file "comphack-" nil ".c"))
         (output-file (or output-file (concat base ".eln"))))

    (unwind-protect
        (progn
          ;; Step 1: Elisp → C
          (comphack-compile-to-c input-file c-file)

          ;; Step 2: C → .eln
          (comphack--compile-c-to-eln c-file output-file)

          output-file)
      ;; Always clean up temporary C file
      (ignore-errors (delete-file c-file)))))

(defun comphack-compile-comp-ctxt (ctxt output-file &optional keep-c-source)
  "Compile COMP-CTXT (a `comp-ctxt' struct) to OUTPUT-FILE using comphack.
When KEEP-C-SOURCE is non-nil, preserve the intermediate C translation."
  (unless output-file
    (error "Output file must be specified for comphack compilation"))
  (let* ((minimal (comphack--simplify-ctxt ctxt))
         (freloc-filename (comphack-codegen-ensure-freloc-h))
         (tmp-c-file (make-temp-file "emacs-comphack-" nil ".c")))
    (unwind-protect
        (progn
          (with-temp-file tmp-c-file
            (comphack-codegen-insert-complete-eln minimal freloc-filename))
          (comphack--compile-c-to-eln tmp-c-file output-file)
          output-file)
      (unless keep-c-source
        (ignore-errors (delete-file tmp-c-file))))))

(defun comphack--compile-c-to-eln (c-file eln-file)
  "Compile C-FILE to ELN-FILE using the configured C compiler.
Signals error if compilation fails."
  (let* ((eln-file (expand-file-name eln-file))
         (eln-directory (file-name-directory eln-file))
         (include-flags
          (list (concat "-I" comphack-emacs-source-dir)
                (concat "-I" comphack-emacs-source-dir "/lib")
                (concat "-I" comphack-base-dir))))
    (make-directory eln-directory t)
    (let* ((temporary-eln
            (make-temp-file
             (expand-file-name ".comphack-" eln-directory) nil ".eln"))
           (all-flags (append comphack-compiler-flags
                              (when (> native-comp-debug 0) '("-g"))
                              comphack-linker-flags
                              native-comp-comphack-extra-flags
                              include-flags
                              (list "-o" temporary-eln c-file))))
      (comp-log
       (format "Compiling C → ELN: %s" (file-name-nondirectory eln-file)))
      (unwind-protect
          (with-temp-buffer
            (let ((exit-code
                   (apply #'call-process
                          native-comp-comphack-cc nil t nil all-flags)))
              (unless (zerop exit-code)
                (error
                 "Comphack backend compiler failed with exit code %d:\n%s"
                 exit-code
                 (buffer-string))))
            ;; Publish only complete shared objects.  Native compilation can
            ;; have consumers waiting for this exact file in other processes.
            (rename-file temporary-eln eln-file t)
            (comp-log
             (format "Successfully compiled %s (%d bytes)"
                     eln-file
                     (file-attribute-size (file-attributes eln-file)))))
        (when (file-exists-p temporary-eln)
          (ignore-errors (delete-file temporary-eln)))))))


;;; Debugging Utilities

(defun comphack-show-last-minimal ()
  "Display the last extracted minimal context in a buffer."
  (interactive)
  (unless comphack--last-minimal
    (user-error "No minimal context available. Compile something first"))

  (with-current-buffer (get-buffer-create "*comphack-minimal*")
    (erase-buffer)
    (emacs-lisp-mode)
    (pp comphack--last-minimal (current-buffer))
    (goto-char (point-min))
    (pop-to-buffer (current-buffer))))

(defun comphack-show-last-c ()
  "Display the C code that would be generated from last minimal context."
  (interactive)
  (unless comphack--last-minimal
    (user-error "No minimal context available. Compile something first"))

  (with-current-buffer (get-buffer-create "*comphack-c*")
    (erase-buffer)
    (c-mode)
    (comphack-codegen-insert-complete-eln comphack--last-minimal)
    (goto-char (point-min))
    (pop-to-buffer (current-buffer))))

(provide 'comphack)
;;; comphack.el ends here
