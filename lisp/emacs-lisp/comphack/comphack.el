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
  '("-shared" "-fPIC" "-O2" "-w" "-fno-stack-protector" "-fno-toplevel-reorder")
  "Flags passed to the compiler when compiling C to .eln.
The -fno-toplevel-reorder flag is critical to preserve blob declaration order.")

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

(defun comphack--clean-insn (insn)
  "Remove unprintable objects from INSN for serialization."
  (cond
   ((comp-mvar-p insn) (comp-mvar-slot insn))
   ((proper-list-p insn)
    (mapcar #'comphack--clean-insn insn))
   (t insn)))

(defun comphack--extract-data-container (container)
  "Extract data from CONTAINER as vector.
Returns cons of (vector . index-hash) mapping objects to indices.
Uses comp-data-container-l which is populated by comp--finalize-relocs."
  (let* ((objects-list (comp-data-container-l container))
         (idx-map (make-hash-table :test 'equal))
         (objects nil)
         (seen (make-hash-table :test 'equal)))

    ;; Filter, normalize, and deduplicate objects from the list
    (dolist (obj objects-list)
      (unless (comp-cstr-p obj)
        ;; Convert symbol-with-pos to plain symbol for comparison
        (let ((normalized (if (symbol-with-pos-p obj)
                             (bare-symbol obj)
                           obj)))
          ;; Only add if we haven't seen this object before
          (unless (gethash normalized seen)
            (puthash normalized t seen)
            (push normalized objects)))))

    (setq objects (nreverse objects))

    ;; Build index map
    (let ((idx 0))
      (dolist (obj objects)
        (puthash obj idx idx-map)
        (setq idx (1+ idx))))

    (cons (vconcat objects) idx-map)))

(defun comphack--simplify-ctxt (comp-ctxt)
  "Extract minimal compilation context from COMP-CTXT.
Returns plist with only fields needed for C generation."
  ;; Finalize relocations to populate data container lists
  (let ((comp-ctxt comp-ctxt))
    (comp--finalize-relocs))

  (let ((funcs-list nil))

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

         (push (list :c-name c-name
                    :name (comp-func-name func)
                    :args (comp-func-l-args func)
                    :frame-size (comp-func-frame-size func)
                    :speed (comp-func-speed func)
                    :pure (comp-func-pure func)
                    :blocks (nreverse blocks-list))
               funcs-list)))
     (comp-ctxt-funcs-h comp-ctxt))

    ;; Extract data containers
    (let ((d-default (comphack--extract-data-container
                     (comp-ctxt-d-default comp-ctxt)))
          (d-impure (comphack--extract-data-container
                    (comp-ctxt-d-impure comp-ctxt)))
          (d-ephemeral (comphack--extract-data-container
                       (comp-ctxt-d-ephemeral comp-ctxt))))

      (list :functions (nreverse funcs-list)
            :d-default (car d-default)
            :d-default-idx (cdr d-default)
            :d-impure (car d-impure)
            :d-impure-idx (cdr d-impure)
            :d-ephemeral (car d-ephemeral)
            :d-ephemeral-idx (cdr d-ephemeral)
            :function-docs (comp-ctxt-function-docs comp-ctxt)
            :speed (comp-ctxt-speed comp-ctxt)
            :debug (comp-ctxt-debug comp-ctxt)
            :compiler-options (comp-ctxt-compiler-options comp-ctxt)))))

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
         (c-file (concat base ".c"))
         (output-file (or output-file (concat base ".eln"))))

    ;; Step 1: Elisp → C
    (comphack-compile-to-c input-file c-file)

    ;; Step 2: C → .eln
    (comphack--compile-c-to-eln c-file output-file)

    output-file))

(defun comphack-compile-comp-ctxt (comp-ctxt output-file &optional keep-c-source)
  "Compile COMP-CTXT (a `comp-ctxt' struct) to OUTPUT-FILE using comphack.
When KEEP-C-SOURCE is non-nil, preserve the intermediate C translation."
  (unless output-file
    (error "Output file must be specified for comphack compilation"))
  (let* ((minimal (comphack--simplify-ctxt comp-ctxt))
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
  "Compile C-FILE to ELN-FILE using GCC.
Signals error if compilation fails."
  (let* ((include-flags
          (list (concat "-I" comphack-emacs-source-dir)
                (concat "-I" comphack-emacs-source-dir "/lib")
                (concat "-I" comphack-base-dir)))
         (all-flags (append comphack-compiler-flags
                            native-comp-comphack-extra-flags
                            include-flags
                            (list "-o" eln-file c-file)))
         (command (mapconcat #'shell-quote-argument
                             (cons native-comp-comphack-cc all-flags)
                             " ")))

    (message "Compiling C → ELN: %s" (file-name-nondirectory eln-file))

    (with-temp-buffer
      (let ((exit-code (apply #'call-process native-comp-comphack-cc nil t nil all-flags)))
        (if (zerop exit-code)
            (message "Successfully compiled %s (%d bytes)"
                     eln-file
                     (file-attribute-size (file-attributes eln-file)))
          (error "Comphack backend compiler failed with exit code %d:\n%s"
                 exit-code
                 (buffer-string)))))))

(defun comphack-compile-comp-ctxt (comp-ctxt output-file &optional keep-c-source)
  "Compile COMP-CTXT to OUTPUT-FILE using the comphack pipeline.
When KEEP-C-SOURCE is non-nil, do not delete the temporary C translation."
  (unless output-file
    (error "Output file must be specified for comphack compilation"))
  (let* ((minimal (comphack--simplify-ctxt comp-ctxt))
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
