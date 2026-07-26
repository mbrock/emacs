;;; positioned-symbol.el --- Regression test for positioned dispatch  -*- lexical-binding: t; -*-

(defun comphack-test--positioned-dispatch (form)
  (pcase form
    (`(defvar ,name)
     (list :declaration name))
    (`(,(or 'defconst 'defvar) ,name ,value . ,_)
     (list :definition name value))
    (_ :other)))

(let* ((symbols-with-pos-enabled t)
       (result
        (comphack-test--positioned-dispatch
         (list (position-symbol 'defconst 17) 'answer 42 "doc"))))
  (unless (equal result '(:definition answer 42))
    (error "Positioned-symbol dispatch was miscompiled: %S" result)))

;;; positioned-symbol.el ends here
