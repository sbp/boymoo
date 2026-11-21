(in-package "ACL2")

(include-book "core")
(include-book "well-formed-syntax")

(set-verify-guards-eagerness 0)

;;; The term recognizer at each of the forms that an event can produce.

(defthm wf-term-list-p-of-cons
  (equal (wf-term-list-p (cons x xs))
         (and (wf-term-p x) (wf-term-list-p xs))))

(defthm wf-term-p-of-call
  (implies (and (symbolp fn) (not (eq fn 'quote)))
           (equal (wf-term-p (cons fn args))
                  (and (wf-function-name-p fn)
                       (wf-term-list-p args))))
  :hints (("Goal" :in-theory (enable pseudo-termp wf-term-details-p))))

(defthm wf-arglistp-implies-symbol-listp
  (implies (arglistp x) (symbol-listp x))
  :hints (("Goal" :in-theory (enable arglistp arglistp1))))

;;; Taking the executable half of an MBE preserves terms and the
;;; number of actuals. Induction changes scope when entering a lambda.

; An MBE encountered during the walk must have an executable half.
; The other actuals of that call are discarded.

(mutual-recursion
 (defun wf-exec-input-p (x)
   (cond ((or (atom x) (eq (car x) 'quote)) t)
         ((and (eq (car x) 'return-last) (equal (cadr x) ''mbe1-raw))
          (and (consp (cddr x)) (wf-exec-input-p (caddr x))))
         ((consp (car x))
          (and (wf-exec-input-p (caddar x))
               (wf-exec-input-list-p (cdr x))))
         (t (wf-exec-input-list-p (cdr x)))))

 (defun wf-exec-input-list-p (xs)
   (or (atom xs)
       (and (wf-exec-input-p (car xs)) (wf-exec-input-list-p (cdr xs))))))

(local
 (defthm wf-len-of-bx-exec-lst
   (equal (len (bx-exec-lst xs)) (len xs))
   :hints (("Goal" :induct (len xs)))))

(local
 (defun wf-exec-induction (listp x scope)
   (declare (xargs :measure (acl2-count x)))
   (cond (listp
          (and (consp x)
               (list (wf-exec-induction nil (car x) scope)
                     (wf-exec-induction t (cdr x) scope))))
         ((or (atom x) (eq (car x) 'quote)) scope)
         ((and (eq (car x) 'return-last)
               (equal (cadr x) ''mbe1-raw))
          (wf-exec-induction nil (caddr x) scope))
         ((consp (car x))
          (list (wf-exec-induction nil (caddar x) (cadar x))
                (wf-exec-induction t (cdr x) scope)))
         (t (wf-exec-induction t (cdr x) scope)))))

(local
 (defthm wf-exec-preserves-scoped-terms
   (if listp
       (implies (and (pseudo-term-listp x) (wf-term-list-details-p x scope)
                     (wf-exec-input-list-p x))
                (and (pseudo-term-listp (bx-exec-lst x))
                     (wf-term-list-details-p (bx-exec-lst x) scope)))
     (implies (and (pseudo-termp x) (wf-term-details-p x scope) (wf-exec-input-p x))
              (and (pseudo-termp (bx-exec x))
                   (wf-term-details-p (bx-exec x) scope))))
   :rule-classes nil
   :hints (("Goal" :induct (wf-exec-induction listp x scope)
            :in-theory (enable pseudo-termp pseudo-term-listp)))))

(defthm wf-term-p-of-bx-exec
  (implies (and (wf-term-p x) (wf-exec-input-p x)) (wf-term-p (bx-exec x)))
  :hints (("Goal" :use ((:instance wf-exec-preserves-scoped-terms
                                  (listp nil) (scope t))))))

;;; The variables read from a choice axiom are selected from the
;;; lambda's distinct formals. In the multiple-value case each selected
;;; formal corresponds to its own index.

(local
 (defthm wf-legal-variablep-when-member-of-arglist
   (implies (and (arglistp1 formals) (member-equal v formals))
            (legal-variablep v))
   :hints (("Goal" :in-theory (enable arglistp1)))))

(local
 (defthm wf-arglistp-of-bx-bound-one
   (implies (arglistp formals)
            (arglistp (bx-bound-one formals actuals call)))
   :hints (("Goal" :induct (bx-bound-one formals actuals call)
            :in-theory (enable arglistp arglistp1)))))

(local
 (defthm wf-bound-index-in-formals
   (implies (bx-bound-index formals actuals mv i)
            (member-equal (bx-bound-index formals actuals mv i) formals))))

(local
 (defun wf-formal-actual (v formals actuals)
   (cond ((atom formals) nil)
         ((equal v (car formals)) (car actuals))
         (t (wf-formal-actual v (cdr formals) (cdr actuals))))))

(local
 (defthm wf-actual-of-bx-bound-index
   (implies (and (no-duplicatesp-equal formals)
                 (bx-bound-index formals actuals mv i))
            (equal (wf-formal-actual (bx-bound-index formals actuals mv i)
                                     formals actuals)
                   (list 'mv-nth (kwote i) mv)))
   :hints (("Goal" :induct (bx-bound-index formals actuals mv i)))))

(local
 (defthm wf-index-of-member-of-bx-bound-many
   (implies (and (no-duplicatesp-equal formals)
                 (natp i)
                 (member-equal v (bx-bound-many formals actuals mv i fuel)))
            (<= i (cadadr (wf-formal-actual v formals actuals))))
   :rule-classes nil
   :hints (("Goal" :induct (bx-bound-many formals actuals mv i fuel)
            :in-theory (disable bx-bound-index wf-formal-actual)))))

(local
 (defthm wf-bx-bound-many-excludes-previous
   (implies (and (no-duplicatesp-equal formals)
                 (natp i)
                 (bx-bound-index formals actuals mv i))
            (not (member-equal (bx-bound-index formals actuals mv i)
                               (bx-bound-many formals actuals mv (+ 1 i) fuel))))
   :hints (("Goal" :use ((:instance wf-index-of-member-of-bx-bound-many
                                   (v (bx-bound-index formals actuals mv i))
                                   (i (+ 1 i))))
            :in-theory (disable bx-bound-index bx-bound-many wf-formal-actual)))))

(local
 (defthm wf-arglistp-of-bx-bound-many
   (implies (and (arglistp formals) (natp i))
            (arglistp (bx-bound-many formals actuals mv i fuel)))
   :hints (("Goal" :induct (bx-bound-many formals actuals mv i fuel)
            :in-theory (e/d (arglistp arglistp1) (bx-bound-index))))))

;;; Subterms of the stored choice axiom remain terms when inspected
;;; outside the scope of the lambda in which they occur.

(local
 (defun wf-scope-induction (listp x)
   (declare (xargs :measure (acl2-count x)))
   (cond (listp (and (consp x)
                     (list (wf-scope-induction nil (car x))
                           (wf-scope-induction t (cdr x)))))
         ((or (atom x) (eq (car x) 'quote)) nil)
         (t (wf-scope-induction t (cdr x))))))

(local
 (defthm wf-term-details-without-scope
   (if listp
       (implies (wf-term-list-details-p x scope) (wf-term-list-details-p x t))
     (implies (wf-term-details-p x scope) (wf-term-details-p x t)))
   :rule-classes nil
   :hints (("Goal" :induct (wf-scope-induction listp x))
           ("Subgoal *1/4" :expand ((wf-term-details-p x scope)
                                    (wf-term-details-p x t))))))

(local
 (defthm wf-subterms-of-wf-call
   (implies (and (wf-term-p x) (consp x) (not (eq (car x) 'quote)))
            (wf-term-list-p (cdr x)))
   :hints (("Goal" :in-theory (enable pseudo-termp wf-term-details-p)))))

(local
 (defthm wf-arglistp-of-wf-lambda
   (implies (and (wf-term-p x) (consp (car x)))
            (arglistp (cadar x)))
   :hints (("Goal" :in-theory (enable pseudo-termp wf-term-details-p)))))

(local
 (defthm wf-term-p-of-wf-lambda-body
   (implies (and (wf-term-p x) (consp (car x)))
            (wf-term-p (caddar x)))
   :hints (("Goal" :use ((:instance wf-term-details-without-scope
                                   (listp nil) (x (caddar x)) (scope (cadar x))))
            :in-theory (enable pseudo-termp wf-term-details-p)))))

(local
 (defthm wf-car-and-cdr-of-wf-term-list
   (implies (and (wf-term-list-p xs) (consp xs))
            (and (wf-term-p (car xs)) (wf-term-list-p (cdr xs))))))

(defthm wf-bx-choose-parts
  (implies (and (wf-term-p axiom) (car (bx-choose-parts axiom fn wrld)))
           (and (arglistp (car (bx-choose-parts axiom fn wrld)))
                (wf-term-p (mv-nth 1 (bx-choose-parts axiom fn wrld)))))
  :hints (("Goal" :in-theory (disable wf-term-p wf-term-list-p formals
                                      bx-bound-one bx-bound-many))))
