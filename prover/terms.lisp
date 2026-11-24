(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *terms-car* '("sym" "COMMON-LISP" "CAR"))
(defconst *terms-cdr* '("sym" "COMMON-LISP" "CDR"))

(defconst *terms-unproved* '(:failure "Unproved" ""))
(defconst *terms-missing-measure-ordinality* '(:failure "MissingMeasureOrdinality" ""))
(defconst *terms-invalid-proof-arity* '(:failure "InvalidProofArity" ""))
(defconst *terms-different-normal-forms* '(:failure "DifferentNormalForms" ""))

(defun terms-unproved-p (answer)
  (and (failure-p answer)
       (or (equal (cadr answer) "Unproved")
           (equal (cadr answer) "MissingMeasureOrdinality"))))

(defun terms-proof-fallback-p (answer)
  (or (terms-unproved-p answer)
      (and (failure-p answer)
           (if (member-equal (cadr answer) '("InvalidProofArity" "DifferentNormalForms" "value"))
               t
             nil))))

(mutual-recursion
 (defun terms-replace-calls (term names)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) term)
    ((endp term) '(:failure "failure" ""))
    (t
     (let* ((head (car term))
            (new-head
             (if (proof-compound head)
                 (if (consp (cddr head))
                     (let ((body (terms-replace-calls (caddr head) names)))
                       (if (failure-p body)
                           body
                         (list (car head) (cadr head) body)))
                   '(:failure "failure" ""))
               (table-get names head head))))
       (if (failure-p new-head)
           new-head
         (let ((args (terms-replace-calls-args (cdr term) names)))
           (if (failure-p args) args (cons new-head args))))))))
 (defun terms-replace-calls-args (args names)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (let ((first (terms-replace-calls (car args) names)))
       (if (failure-p first)
           first
         (let ((rest (terms-replace-calls-args (cdr args) names)))
           (if (failure-p rest) rest (cons first rest))))))))

(defun terms-selector-edges-loop (term base edges)
  (cond
   ((equal term base) edges)
   ((and (consp term)
         (or (proof-is-call term *terms-car*) (proof-is-call term *terms-cdr*)))
    (if (consp (cdr term))
        (terms-selector-edges-loop (cadr term) base (cons (list (car term) (cadr term)) edges))
      '(:failure "failure" "")))
   (t nil)))

(defun terms-selector-edges (term base)
  (terms-selector-edges-loop term base nil))
