;;; differential-trace.el --- Find the first native miscompilation  -*- lexical-binding: t; -*-

;; This is a batch-mode helper for trace-selfhost.sh.  It records the calls
;; made through a family of compiler functions during a known-good compile,
;; then compares a candidate compiler against that trace.  Comparing entries
;; as well as returns catches the first bad intermediate value rather than the
;; much later error it eventually causes.

(require 'cl-lib)
(require 'seq)

(declare-function comphack-compile-to-c "comphack" (input-file output-file))

(defvar comphack-trace--mode
  (intern (or (getenv "COMPHACK_TRACE_MODE") "record")))
(defvar comphack-trace--events nil)
(defvar comphack-trace--expected nil)
(defvar comphack-trace--index 0)
(defvar comphack-trace--gensyms nil)
(defvar comphack-trace--next-gensym 0)

(define-error 'comphack-trace-divergence "Comphack trace divergence")

(defun comphack-trace--portable (object)
  "Return a position- and gensym-independent copy of OBJECT."
  (cond
   ((symbol-with-pos-p object) (bare-symbol object))
   ((and (symbolp object)
         (not (eq object (intern-soft (symbol-name object)))))
    (or (alist-get object comphack-trace--gensyms nil nil #'eq)
        (let ((replacement
               (make-symbol
                (format "comphack-gensym-%d"
                        (prog1 comphack-trace--next-gensym
                          (setq comphack-trace--next-gensym
                                (1+ comphack-trace--next-gensym)))))))
          (push (cons object replacement) comphack-trace--gensyms)
          replacement)))
   ((consp object)
    (cons (comphack-trace--portable (car object))
          (comphack-trace--portable (cdr object))))
   ((vectorp object)
    (vconcat (mapcar #'comphack-trace--portable object)))
   (t object)))

(defun comphack-trace--printed (object)
  "Return a stable printed representation of OBJECT."
  (let ((comphack-trace--gensyms nil)
        (comphack-trace--next-gensym 0)
        (print-circle t)
        (print-gensym t)
        (print-level nil)
        (print-length nil))
    (prin1-to-string (comphack-trace--portable object))))

(defun comphack-trace--digest (object)
  (secure-hash 'sha256 (comphack-trace--printed object)))

(defun comphack-trace--preview (object)
  (let ((text (comphack-trace--printed object)))
    (substring text 0 (min 500 (length text)))))

(defun comphack-trace--diverge (expected actual)
  (signal
   'comphack-trace-divergence
   (list
    (format
     (concat "first divergence at event %d\n"
             "Expected: %S\nActual:   %S")
     (1+ comphack-trace--index) expected actual))))

(defun comphack-trace--event (kind function value)
  (let ((event (list kind function (comphack-trace--digest value)
                     (comphack-trace--preview value))))
    (pcase comphack-trace--mode
      ('record (push event comphack-trace--events))
      ('compare
       (if (>= comphack-trace--index
               (length comphack-trace--expected))
           (comphack-trace--diverge :end-of-trace event)
         (let ((expected
                (aref comphack-trace--expected comphack-trace--index)))
           (unless (equal (seq-take expected 3)
                          (seq-take event 3))
             (comphack-trace--diverge expected event))
           (setq comphack-trace--index
                 (1+ comphack-trace--index))))))))

(defun comphack-trace--around (function original &rest args)
  (comphack-trace--event 'enter function args)
  (condition-case error-data
      (let ((result (apply original args)))
        (comphack-trace--event 'leave function result)
        result)
    (comphack-trace-divergence
     (signal (car error-data) (cdr error-data)))
    (error
     (comphack-trace--event 'error function error-data)
     (signal (car error-data) (cdr error-data)))))

(defun comphack-trace--prefix-p (symbol prefixes)
  (seq-some
   (lambda (prefix) (string-prefix-p prefix (symbol-name symbol)))
   prefixes))

(defun comphack-trace--instrument (prefixes)
  (mapatoms
   (lambda (symbol)
     (when (and (comphack-trace--prefix-p symbol prefixes)
                (fboundp symbol)
                (not (macrop symbol))
                (not (special-form-p symbol)))
       (advice-add
        symbol :around
        (apply-partially #'comphack-trace--around symbol))))))

(defun comphack-trace--read (file)
  (with-temp-buffer
    (insert-file-contents file)
    (read (current-buffer))))

(defun comphack-trace--write-report (text)
  (let ((report (getenv "COMPHACK_TRACE_REPORT")))
    (when report
      (with-temp-file report
        (insert text "\n")))))

(let* ((trace-file (getenv "COMPHACK_TRACE_FILE"))
       (source (getenv "COMPHACK_TRACE_SOURCE"))
       (output (getenv "COMPHACK_TRACE_OUTPUT"))
       (prefixes
        (split-string
         (or (getenv "COMPHACK_TRACE_PREFIXES") "cconv-") "[, \t]+" t)))
  (when (eq comphack-trace--mode 'compare)
    (setq comphack-trace--expected
          (vconcat (comphack-trace--read trace-file))))
  (comphack-trace--instrument prefixes)
  (condition-case error-data
      (progn
        (comphack-compile-to-c source output)
        (if (eq comphack-trace--mode 'record)
            (progn
              (setq comphack-trace--events
                    (nreverse comphack-trace--events))
              (with-temp-file trace-file
                (let ((print-level nil) (print-length nil))
                  (prin1 comphack-trace--events (current-buffer))
                  (insert "\n")))
              (message "Recorded %d compiler events"
                       (length comphack-trace--events)))
          (when (/= comphack-trace--index
                    (length comphack-trace--expected))
            (comphack-trace--diverge
             (aref comphack-trace--expected comphack-trace--index)
             :end-of-candidate))
          (message "All %d compiler events agree"
                   comphack-trace--index)))
    (comphack-trace-divergence
     (let ((text (error-message-string error-data)))
       (comphack-trace--write-report text)
       (message "%s" text)
       (kill-emacs 1)))
    (error
     (let ((text (format "Compile failed before a trace divergence: %S"
                         error-data)))
       (comphack-trace--write-report text)
       (message "%s" text)
       (kill-emacs 2)))))

;;; differential-trace.el ends here
