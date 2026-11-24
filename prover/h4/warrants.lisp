(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-warrants-primitive* (proof-sym "APPLY$-PRIMP" "ACL2"))
(defconst *h4-warrants-tame* (proof-sym "TAMEP-FUNCTIONP" "ACL2"))
(defconst *h4-warrants-filter* (proof-sym "H4-WARRANT-NAMEP" "ACL2"))
(defconst *h4-warrants-primitive-absence* (proof-sym "H4-WARRANT-NAMES-NOT-PRIMITIVE" "ACL2"))
(defconst *h4-warrants-tame-example* (proof-sym "H4-TAME-EXAMPLE" "ACL2"))
(defconst *h4-warrants-key* (proof-sym "KEY" "ACL2"))
(defconst *h4-warrants-args* (proof-sym "ARGS" "ACL2"))
(defconst *h4-warrants-example*
  (list (proof-cl "LAMBDA") (list *library-x*) *proof-false*))
(defconst *h4-warrants-eq* (proof-cl "EQ"))
(defconst *h4-warrants-force* (proof-sym "FORCE" "ACL2"))
(defconst *h4-warrants-badge* (proof-sym "BADGE" "ACL2"))
(defconst *h4-warrants-apply* (proof-sym "APPLY$" "ACL2"))

(defconst *h4-warrants-tame-definitions*
  (list *h4-warrants-tame* (proof-sym "TAMEP" "ACL2")
        (proof-sym "LAMBDA-OBJECT-SHAPEP" "ACL2")
        (proof-sym "LAMBDA-OBJECT-FORMALS" "ACL2")
        (proof-sym "LAMBDA-OBJECT-BODY" "ACL2")
        (proof-sym "SYMBOL-LISTP" "ACL2")
        (proof-cl "ATOM") *proof-not* (proof-cl "NULL") *h4-warrants-eq*))

(defun h4-warrants-datum-length (datum)
  (cond ((stringp datum) (length datum))
        ((integerp datum) '(:failure "failure" ""))
        ((rationalp datum) '(:failure "failure" ""))
        ((eq datum t) '(:failure "failure" ""))
        (t (len datum))))

(defun h4-warrants-necessity (warrant)
  (proof-with-checked-results
      ((package-name (proof-term-at warrant 1))
       (label (proof-term-at warrant 2)))
    (proof-sym (concatenate 'string label "-NECC") package-name)))

(defun h4-warrants-warrant-parts-application (warrant datum application)
  (if (not (proof-is-call application *proof-equal*))
      nil
    (proof-with-checked-results ((call (proof-term-at application 1)))
      (if (not (proof-is-call call *h4-warrants-apply*))
          nil
        (proof-with-checked-results
            ((function (proof-term-at datum 1))
             (argument (proof-term-at call 1)))
          (if (and (equal argument datum) (true-listp function))
              (proof-with-checked-results ((tag (proof-term-at function 0)))
                (if (equal tag "sym")
                    (proof-with-checked-results ((value (proof-term-at application 2)))
                      (if (proof-is-call value function)
                          (proof-with-checked-results
                              ((warrant (proof-list-of-length warrant 3))
                               (necessity (h4-warrants-necessity warrant)))
                            (list function necessity))
                        nil))
                  nil))
            nil))))))

(defun h4-warrants-warrant-parts-badge (warrant badge application)
  (if (not (proof-is-call badge *proof-equal*))
      nil
    (proof-with-checked-results ((call (proof-term-at badge 1)))
      (if (not (proof-is-call call *h4-warrants-badge*))
          nil
        (proof-with-checked-results ((datum (proof-term-at call 1)))
          (if (proof-is-call datum *proof-quote*)
              (h4-warrants-warrant-parts-application warrant datum application)
            nil))))))

(defun h4-warrants-warrant-parts-calls (force badge application)
  (if (not (proof-is-call force *h4-warrants-force*))
      nil
    (proof-with-checked-results
        ((call (proof-term-at force 1))
         (size (h4-warrants-datum-length call)))
      (if (or (not (equal size 1)) (stringp call))
          nil
        (let ((warrant (car call)))
          (proof-with-checked-results ((tag (proof-term-at warrant 0)))
            (if (equal tag "sym")
                (h4-warrants-warrant-parts-badge warrant badge application)
              nil)))))))

(defun h4-warrants-warrant-parts-higher-order (formula)
  (proof-with-checked-results ((tail (proof-term-at formula 3)))
    (let ((badge-implication (cadr formula))
          (apply-implication (caddr formula)))
      (if (and (equal tail *proof-false*)
               (proof-is-call badge-implication *library-implies*)
               (proof-is-call apply-implication *library-implies*))
          (proof-with-checked-results
              ((badge-parts (proof-list-of-length badge-implication 3))
               (apply-parts (proof-list-of-length apply-implication 3)))
            (let ((force (cadr badge-parts))
                  (guard (cadr apply-parts)))
              (if (proof-is-call guard *proof-if*)
                  (proof-with-checked-results ((test (proof-term-at guard 1)))
                    (if (equal test force)
                        (proof-with-checked-results ((otherwise (proof-term-at guard 3)))
                          (if (equal otherwise *proof-false*)
                              (h4-warrants-warrant-parts-calls force (caddr badge-parts)
                                                              (caddr apply-parts))
                            nil))
                      nil))
                nil)))
        nil))))

(defun h4-warrants-warrant-parts (formula)
  (cond
   ((proof-is-call formula *library-implies*)
    (proof-with-checked-results ((guarded (proof-term-at formula 2)))
      (if (proof-is-call guarded *proof-if*)
          (proof-with-checked-results ((tail (proof-term-at guarded 3)))
            (if (equal tail *proof-false*)
                (proof-with-checked-results
                    ((parts (proof-list-of-length (cdr formula) 2))
                     (guarded-parts (proof-list-of-length guarded 4)))
                  (h4-warrants-warrant-parts-calls (car parts) (cadr guarded-parts)
                                                  (caddr guarded-parts)))
              nil))
        nil)))
   ((proof-is-call formula *proof-if*)
    (h4-warrants-warrant-parts-higher-order formula))
   (t nil)))

(defun h4-warrants-tame-example (p)
  (proof-with-checked-results
      ((equality (h4-tactics-tactics-evaluate-closed
                  p (list *h4-warrants-tame* (proof-quote *h4-warrants-example*))
                  *h4-warrants-tame-definitions*)))
    (h4-tactics-tactics-non-nil p equality)))

(defun h4-warrants-proved-warrant-at-argument (forced arguments p force necessity)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof force))
         (warranted (proof-proof-rewrite proof forced opened '(1)))
         (constraint (proof-proof-fact proof necessity
                                       (list (list *h4-warrants-args* arguments)))))
      (h4-tactics-tactics-from-contrapositive p constraint warranted))))

(defun h4-warrants-proved-warrant-dispatch (term p primitive-absence)
  (proof-with-checked-results
      ((head (proof-term-at term 0))
       (equality (h4-tactics-tactics-normalize
                  p term (list primitive-absence) (list head *h4-warrants-eq*) nil nil)))
    (proof-proof-symmetric (library-library-proof p) equality)))

(defun h4-warrants-example-arguments (arity)
  (declare (xargs :measure (nfix arity)))
  (if (zp arity)
      nil
    (cons *h4-warrants-example* (h4-warrants-example-arguments (1- arity)))))

(defun h4-warrants-proved-warrant-higher-order
    (p formula badge-implication apply-implication force premise apply-conclusion
       necessity badge application-equality witness)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof premise t))
         (parts (h4-tactics-tactics-conjunct p assumed))
         (argument (h4-warrants-proved-warrant-at-argument
                    (car parts) *h4-warrants-args* p force necessity))
         (dispatch-constraint (h4-tactics-tactics-modus-ponens p argument (cadr parts)))
         (dispatch-parts (h4-tactics-tactics-conjunct p dispatch-constraint))
         (application (proof-proof-rewrite proof (cadr dispatch-parts) application-equality '(1 1)))
         (call (proof-term-at apply-conclusion 2))
         (arity (h4-warrants-datum-length call))
         (forced (proof-proof-assume proof force t))
         (instance (h4-warrants-proved-warrant-at-argument
                    forced (proof-quote (h4-warrants-example-arguments (1- arity)))
                    p force necessity))
         (literal (proof-step-first instance))
         (test (proof-term-at literal 1))
         (tame-instance (h4-tactics-tactics-establish p test (list witness) nil nil nil))
         (specialized (h4-tactics-tactics-modus-ponens p instance tame-instance))
         (specialized-parts (h4-tactics-tactics-conjunct p specialized))
         (badge-test (proof-proof-rewrite proof (car specialized-parts) badge '(1 1)))
         (badge-step (h4-tactics-tactics-imply p badge-implication badge-test))
         (application-step (h4-tactics-tactics-imply p apply-implication application)))
      (h4-tactics-tactics-conjunction p formula badge-step application-step))))

(defun h4-warrants-proved-warrant-conclusions
    (p formula primitive-absence witness force badge-conclusion apply-conclusion
       higher-order badge-implication apply-implication premise)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((call (proof-term-at force 1))
         (warrant (proof-term-at call 0))
         (necessity (h4-warrants-necessity warrant))
         (badge-call (proof-term-at badge-conclusion 1))
         (badge (h4-warrants-proved-warrant-dispatch badge-call p primitive-absence))
         (application-call (proof-term-at apply-conclusion 1))
         (application (h4-warrants-proved-warrant-dispatch application-call p primitive-absence)))
      (if higher-order
          (h4-warrants-proved-warrant-higher-order
           p formula badge-implication apply-implication force premise apply-conclusion
           necessity badge application witness)
        (proof-with-checked-results
            ((assumed (proof-proof-assume proof force t))
             (both (h4-warrants-proved-warrant-at-argument
                    assumed *h4-warrants-args* p force necessity))
             (with-badge (proof-proof-rewrite proof both badge '(1 1 1)))
             (with-application (proof-proof-rewrite proof with-badge application '(1 2 1))))
          (h4-tactics-tactics-imply p formula with-application))))))

(defun h4-warrants-proved-warrant (p formula primitive-absence witness)
  (if (proof-is-call formula *library-implies*)
      (proof-with-checked-results
          ((parts (proof-list-of-length formula 3))
           (guarded (proof-list-of-length (caddr parts) 4)))
        (h4-warrants-proved-warrant-conclusions p formula primitive-absence witness
                                               (cadr parts) (cadr guarded) (caddr guarded)
                                               nil nil nil nil))
    (proof-with-checked-results
        ((implications (proof-list-of-length (seq-slice formula 1 3) 2))
         (badge (proof-list-of-length (car implications) 3))
         (application (proof-list-of-length (cadr implications) 3)))
      (h4-warrants-proved-warrant-conclusions
       p formula primitive-absence witness (cadr badge) (caddr badge) (caddr application)
       t (car implications) (cadr implications) (cadr application)))))

(defun h4-warrants-warrant-recipe (p formula warrant-filters)
  (let ((higher-order (not (proof-is-call formula *library-implies*))))
    (proof-with-checked-results
        ((p (if higher-order (h4-tactics-tactics-propositional-lemmas p) p))
         (implication (proof-term-at formula (if higher-order 1 2)))
         (badge (proof-term-at implication (if higher-order 2 1)))
         (badge-call (proof-term-at badge 1))
         (function (proof-term-at badge-call 1))
         (equality (h4-tactics-tactics-evaluate-closed
                    p (list *h4-warrants-filter* function) warrant-filters))
         (recognized (h4-tactics-tactics-non-nil p equality))
         (proof (library-library-proof p))
         (fact (proof-proof-fact proof *h4-warrants-primitive-absence*
                                 (list (list *h4-warrants-key* function))))
         (absent (h4-tactics-tactics-modus-ponens p fact recognized))
         (witness (proof-proof-fact proof *h4-warrants-tame-example* nil))
         (step (h4-warrants-proved-warrant p formula absent witness)))
      (cons step p))))
