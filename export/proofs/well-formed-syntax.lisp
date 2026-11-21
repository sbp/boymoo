(in-package "ACL2")

(include-book "system/legal-variablep" :dir :system)

(set-verify-guards-eagerness 0)

;;; Data and terms, as in spec/language.md, sections 1, 2 and 5.

(defun wf-datump (x)
  (if (consp x)
      (and (wf-datump (car x)) (wf-datump (cdr x)))
    (or (acl2-numberp x) (characterp x) (stringp x) (symbolp x))))

(defun wf-name-p (x)
  (and (symbolp x) (not (keywordp x))))

(defun wf-function-name-p (x)
  (and (wf-name-p x) (not (eq x 'quote))))

; PSEUDO-TERMP checks the list shapes, including the length of a quote
; and the arity of a lambda application. The following tests add the
; restrictions on names, data and variables. SCOPE is T for a term
; whose variables need not be bound, or the formals of its lambda.

(mutual-recursion
 (defun wf-term-details-p (x scope)
   (cond ((atom x)
          (and (legal-variablep x)
               (or (eq scope t) (member-eq x scope))))
         ((eq (car x) 'quote)
          (wf-datump (cadr x)))
         ((symbolp (car x))
          (and (wf-function-name-p (car x))
               (wf-term-list-details-p (cdr x) scope)))
         (t
          (and (consp (car x))
               (arglistp (cadar x))
               (wf-term-details-p (caddar x) (cadar x))
               (wf-term-list-details-p (cdr x) scope)))))

 (defun wf-term-list-details-p (xs scope)
   (or (atom xs)
       (and (wf-term-details-p (car xs) scope)
            (wf-term-list-details-p (cdr xs) scope)))))

(defun wf-term-p (x)
  (and (pseudo-termp x) (wf-term-details-p x t)))

(defun wf-term-list-p (xs)
  (and (pseudo-term-listp xs) (wf-term-list-details-p xs t)))

;;; Statement fields, as in spec/formats.md, section 4.

(defun wf-ruler-extenders-p (x)
  (or (eq x :all) (symbol-listp x)))

(defun wf-definition-p (x)
  (and (true-listp x)
       (equal (len x) 3)
       (wf-function-name-p (car x))
       (arglistp (cadr x))
       (wf-term-p (caddr x))))

(defun wf-definition-list-p (xs)
  (if (consp xs)
      (and (wf-definition-p (car xs)) (wf-definition-list-p (cdr xs)))
    (null xs)))

(defun wf-arity-list-p (xs)
  (if (consp xs)
      (let ((x (car xs)))
        (and (true-listp x)
             (equal (len x) 2)
             (wf-function-name-p (car x))
             (natp (cadr x))
             (wf-arity-list-p (cdr xs))))
    (null xs)))

(defun wf-named-formula-p (x)
  (and (true-listp x)
       (equal (len x) 2)
       (wf-name-p (car x))
       (wf-term-p (cadr x))))

(defun wf-named-formula-list-p (xs)
  (if (consp xs)
      (and (wf-named-formula-p (car xs)) (wf-named-formula-list-p (cdr xs)))
    (null xs)))

(defun wf-package-name-p (x)
  (and (stringp x) (not (equal x ""))))

(defun wf-define-args-p (args)
  (and (consp args)
       (wf-ruler-extenders-p (car args))
       (consp (cdr args))
       (wf-definition-list-p (cdr args))))

(defun wf-choice-args-p (args)
  (and (true-listp args)
       (equal (len args) 5)
       (wf-function-name-p (car args))
       (consp (cadr args))
       (arglistp (cadr args))
       (arglistp (caddr args))
       (wf-term-p (cadddr args))
       (let ((free2 (fifth args)))
         (or (null free2)
             (and (arglistp free2)
                  (equal (len free2) (len (caddr args))))))))

;;; A line is the word and the list of its data, as in spec/formats.md,
;;; sections 3 to 5. Each recognizer includes the shape of both lists.

(defun wf-statement-line-p (line)
  (and (true-listp line)
       (equal (len line) 2)
       (let ((word (car line)) (args (cadr line)))
         (cond ((or (equal word "package") (equal word "hidden-package"))
                (and (true-listp args)
                     (equal (len args) 2)
                     (wf-package-name-p (car args))
                     (symbol-listp (cadr args))))
               ((equal word "define") (wf-define-args-p args))
               ((equal word "constrain")
                (and (true-listp args)
                     (equal (len args) 2)
                     (consp (car args))
                     (wf-arity-list-p (car args))
                     (wf-named-formula-list-p (cadr args))
                     (not (member-eq nil (strip-cars (cadr args))))))
               ((equal word "choose") (wf-choice-args-p args))
               ((or (equal word "theorem") (equal word "axiom"))
                (wf-named-formula-p args))
               ((equal word "reserve")
                (and (true-listp args)
                     (equal (len args) 1)
                     (wf-name-p (car args))))
               (t nil)))))

(defun wf-program-line-p (line)
  (and (true-listp line)
       (equal (len line) 2)
       (let ((word (car line)) (args (cadr line)))
         (cond ((equal word "define") (wf-define-args-p args))
               ((equal word "attach")
                (and (true-listp args)
                     (equal (len args) 2)
                     (symbolp (car args))
                     (symbolp (cadr args))))
               (t nil)))))

(defun wf-statement-lines-p (lines)
  (if (consp lines)
      (and (wf-statement-line-p (car lines))
           (wf-statement-lines-p (cdr lines)))
    (null lines)))

(defun wf-program-lines-p (lines)
  (if (consp lines)
      (and (wf-program-line-p (car lines))
           (wf-program-lines-p (cdr lines)))
    (null lines)))
