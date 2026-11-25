(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-warrant-theorem-force* (proof-sym "FORCE" "ACL2"))
(defconst *l1-warrant-theorem-non-primitive* (proof-sym "L1-NON-PRIMITIVE" "ACL2"))
(defconst *l1-warrant-theorem-user-badge* (proof-sym "L1-USER-BADGE" "ACL2"))
(defconst *l1-warrant-theorem-user-apply* (proof-sym "L1-USER-APPLY" "ACL2"))
(defconst *l1-warrant-theorem-controls* (list (proof-cl "EQ") (proof-cl "EQL")))

(defun l1-warrant-theorem-unguarded-parts (formula)
  (and (proof-is-call formula *library-implies*)
       (proof-with-checked-results ((body (proof-term-at formula 2)))
         (and (proof-is-call body *proof-if*)
              (proof-with-checked-results ((otherwise-term (proof-term-at body 3)))
                (and (equal otherwise-term *proof-false*)
                     (proof-with-checked-results
                         ((parts (proof-list-of-length formula 3))
                          (badge (proof-term-at body 1))
                          (applied (proof-term-at body 2)))
                       (list (cadr parts) badge applied :none))))))))

(defun l1-warrant-theorem-guarded-parts (badge-clause application-clause)
  (proof-with-checked-results
      ((badge-parts (proof-list-of-length badge-clause 3))
       (application-parts (proof-list-of-length application-clause 3)))
    (let ((force (cadr badge-parts))
          (guard (cadr application-parts)))
      (and (proof-is-call guard *proof-if*)
           (proof-with-checked-results ((condition (proof-term-at guard 1)))
             (and (equal condition force)
                  (proof-with-checked-results ((otherwise-term (proof-term-at guard 3)))
                    (and (equal otherwise-term *proof-false*)
                         (proof-with-checked-results ((tame (proof-term-at guard 2)))
                           (list force (caddr badge-parts) (caddr application-parts) tame))))))))))

(defun l1-warrant-theorem-theorem-parts (formula)
  (proof-with-checked-results ((unguarded (l1-warrant-theorem-unguarded-parts formula)))
    (or unguarded
        (and (proof-is-call formula *proof-if*)
             (proof-with-checked-results ((otherwise-term (proof-term-at formula 3)))
               (and (equal otherwise-term *proof-false*)
                    (proof-with-checked-results ((badge-clause (proof-term-at formula 1)))
                      (and (proof-is-call badge-clause *library-implies*)
                           (proof-with-checked-results ((application-clause (proof-term-at formula 2)))
                             (and (proof-is-call application-clause *library-implies*)
                                  (l1-warrant-theorem-guarded-parts badge-clause
                                                                   application-clause)))))))))))

(defun l1-warrant-theorem-necessity-literal (proof name)
  (let ((fact (assoc-equal name (proof-proof-facts proof))))
    (if fact
        (proof-term-at (cdr fact) 0)
      '(:failure "missing-warrant-dependency" ""))))

(defun l1-warrant-theorem-match-tests (rule tests badge expected guard designator arguments)
  (let ((test (car tests))
        (tame (cadr tests))
        (bindings (list (cons (l1-witness-choice-rule-argument rule) arguments))))
    (proof-with-checked-results ((badge-value (l1-warrant-term-at-place test '(1 2))))
      (and (equal badge (proof-eq (list *l1-application-badge* designator) badge-value))
           (proof-with-checked-results
               ((application (proof-term-at test 2))
                (application (proof-subst application bindings)))
             (and (equal application expected)
                  (proof-with-checked-results ((condition (proof-subst tame bindings)))
                    (and (equal condition guard) (list rule test tame designator arguments)))))))))

(defun l1-warrant-theorem-match-rule (proof rule force badge expected guard designator arguments)
  (and (l1-witness-choice-rule-definition-name rule)
       (not (l1-witness-choice-rule-parameters rule))
       (proof-with-checked-results
           ((necessity (l1-warrant-theorem-necessity-literal proof
                                                             (l1-witness-choice-rule-necessity-name rule)))
            (conclusion (proof-term-at necessity 2))
            (warrant (proof-term-at force 1)))
         (and (equal conclusion (proof-neg warrant))
              (proof-with-checked-results ((tests (l1-warrant-warrant-tests rule)))
                (and tests (l1-warrant-theorem-match-tests rule tests badge expected
                                                           guard designator arguments)))))))

(defun l1-warrant-theorem-match-rules (proof choices force badge expected guard designator arguments)
  (if (endp choices)
      nil
    (proof-with-checked-results
        ((match (l1-warrant-theorem-match-rule proof (car choices) force badge expected
                                              guard designator arguments)))
      (or match (l1-warrant-theorem-match-rules proof (cdr choices) force badge expected
                                                guard designator arguments)))))

(defun l1-warrant-theorem-matching-warrant (proof choices parts)
  (proof-with-checked-results ((parts (proof-list-of-length parts 4)))
    (let ((force (car parts))
          (badge (cadr parts))
          (applied (caddr parts))
          (guard (cadddr parts)))
      (and (proof-is-call force *l1-warrant-theorem-force*)
           (proof-is-call applied *proof-equal*)
           (proof-with-checked-results ((application (proof-term-at applied 1)))
             (and (proof-is-call application *l1-application-apply*)
                  (proof-with-checked-results ((application (proof-list-of-length application 3)))
                    (let ((designator (cadr application))
                          (arguments (caddr application)))
                      (and (proof-is-call designator *proof-quote*)
                           (proof-with-checked-results
                               ((value (proof-term-at applied 2))
                                (expected (proof-eq (list *l1-warrant-apply-user-function*
                                                          designator arguments) value)))
                             (l1-warrant-theorem-match-rules proof choices force badge expected
                                                             guard designator arguments)))))))))))

(defun l1-warrant-theorem-contract (proof rule arguments warrant-holds)
  (proof-with-checked-results
      ((necessity (proof-proof-fact proof (l1-witness-choice-rule-necessity-name rule)
                                    (list (list (l1-witness-choice-rule-argument rule) arguments))))
       (test (l1-warrant-step-at-place necessity '(1 1)))
       (test-fails (proof-proof-assume proof test nil))
       (contradicts (proof-proof-modus-ponens proof necessity test-fails))
       (result (proof-proof-cut proof warrant-holds contradicts)))
    (proof-proof-front proof result test)))

(defun l1-warrant-theorem-prove-unguarded
    (proof rule arguments warrant-holds unfold-badge unfold-apply formula force)
  (proof-with-checked-results
      ((contract (l1-warrant-theorem-contract proof rule arguments warrant-holds))
       (pair (proof-proof-conjunct proof contract))
       (fold-badge (proof-proof-symmetric proof unfold-badge))
       (badge-proof (proof-proof-rewrite proof (car pair) fold-badge '(1 1)))
       (fold-apply (proof-proof-symmetric proof unfold-apply))
       (application (proof-proof-rewrite proof (cadr pair) fold-apply '(1 1)))
       (body (proof-term-at formula 2))
       (selected (proof-proof-select proof body badge-proof))
       (both (proof-proof-transport proof application selected)))
    (l1-recursive-introduce-implication proof force both)))

(defun l1-warrant-theorem-prove-guarded
    (proof rule test tame arguments warrant-holds unfold-force unfold-badge unfold-apply formula force)
  (proof-with-checked-results
      ((fixed (l1-warrant-fixed-failure proof rule test tame))
       (necessity (proof-proof-fact proof (l1-witness-choice-rule-necessity-name rule)
                                     (list (list (l1-witness-choice-rule-argument rule) (car fixed)))))
       (bad (proof-proof-modus-ponens proof necessity (cadr fixed)))
       (badge-cut (proof-proof-cut proof warrant-holds bad))
       (badge-test (proof-term-at test 1))
       (user-badge (proof-proof-front proof badge-cut badge-test))
       (fold-badge (proof-proof-symmetric proof unfold-badge))
       (badge-proof (proof-proof-rewrite proof user-badge fold-badge '(1 1)))
       (first (l1-recursive-introduce-implication proof force badge-proof))
       (assumption (l1-warrant-term-at-place formula '(2 1)))
       (assumed (proof-proof-assume proof assumption t))
       (part (proof-proof-conjunct proof assumed))
       (forced (proof-proof-rewrite proof (car part) unfold-force '(1)))
       (warranted (l1-warrant-theorem-contract proof rule arguments forced))
       (open-tame (proof-proof-modus-ponens proof warranted (cadr part)))
       (both (proof-proof-conjunct proof open-tame))
       (fold-apply (proof-proof-symmetric proof unfold-apply))
       (application (proof-proof-rewrite proof (cadr both) fold-apply '(1 1)))
       (second (l1-recursive-introduce-implication proof assumption application))
       (selected (proof-proof-select proof formula first)))
    (proof-proof-transport proof second selected)))

(defun l1-warrant-theorem-skip-special-cases (body expected proof step)
  (cond
   ((equal body expected) step)
   ((and (proof-is-call body *proof-if*) (consp (cdddr body)))
    (proof-with-checked-results
        ((otherwise (proof-proof-if-false proof body))
         (step (proof-proof-rewrite proof step otherwise '(1 2))))
      (l1-warrant-theorem-skip-special-cases (cadddr body) expected proof step)))
   (t nil)))

(defun l1-warrant-theorem-add-user-equation (certificates name call expected)
  (let ((proof (l1-primitive-certificates-proof certificates)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof call))
         (body (proof-rewritten-term opened))
         (equation (l1-warrant-theorem-skip-special-cases body expected proof opened)))
      (if equation
          (proof-with-checked-results ((added (l1-primitive-certificates-add certificates name equation)))
            (cdr added))
        certificates))))

(defun l1-warrant-theorem-discharge-special-cases (tests position proof step)
  (if (endp tests)
      (proof-proof-tidy proof step)
    (proof-with-checked-results
        ((test (l1-warrant-simplify proof (car tests) nil *l1-warrant-theorem-controls*)))
      (and test
           (proof-with-checked-results
               ((value (proof-rewritten-term test))
                (next (and (equal value *proof-false*)
                           (proof-proof-rewrite proof step test (list position)))))
             (and next
                  (l1-warrant-theorem-discharge-special-cases (cdr tests) (1+ position)
                                                            proof next)))))))

(defun l1-warrant-theorem-open-user-call (proof name formals call denied)
  (proof-with-checked-results
      ((equation (and (assoc-equal name (proof-proof-facts proof))
                      (proof-proof-fact proof name (seq-zip formals (cdr call)))))
       (equation (and equation (proof-proof-discharge proof equation denied)))
       (equation (and equation
                      (l1-warrant-theorem-discharge-special-cases
                       (cdr (proof-step-clause equation)) 2 proof equation))))
    (or equation
        (l1-warrant-simplify proof call (list denied)
                             (cons (car call) *l1-warrant-theorem-controls*)))))

(defun l1-warrant-theorem-prove-non-primitive (certificates denied name formula parts match unfold-force)
  (let ((force (car parts))
        (badge (cadr parts))
        (applied (caddr parts))
        (guard (cadddr parts))
        (rule (car match))
        (test (cadr match))
        (tame (caddr match))
        (arguments (car (cddddr match))))
    (proof-with-checked-results
        ((proof (l1-primitive-certificates-proof certificates))
         (badge-call (proof-term-at badge 1))
         (unfold-badge (l1-warrant-theorem-open-user-call
                        proof *l1-warrant-theorem-user-badge* (list *library-x*) badge-call denied))
         (application-call (proof-term-at applied 1))
         (unfold-apply (l1-warrant-theorem-open-user-call
                        proof *l1-warrant-theorem-user-apply* (list *library-x* *library-y*)
                        application-call denied))
         (assume-force (proof-proof-assume proof force t))
         (warrant-holds (proof-proof-rewrite proof assume-force unfold-force '(1)))
         (result (if (eq guard :none)
                     (l1-warrant-theorem-prove-unguarded proof rule arguments warrant-holds
                                                        unfold-badge unfold-apply formula force)
                   (l1-warrant-theorem-prove-guarded proof rule test tame arguments warrant-holds
                                                    unfold-force unfold-badge unfold-apply formula force)))
         (result (proof-proof-subsume proof result (list formula)))
         (entry (proof-proof-entry "theorem" name (list name) (list result))))
      (let* ((entries (l1-primitive-certificates-entries certificates))
             (count (+ (l1-warrant-counts-total (caddr entry)) (l1-warrant-entries-count entries))))
        (proof-with-checked-results
            ((closed (l1-primitive-certificates-close certificates)))
          (list count (append (l1-warrant-entries-sources entries) (list (cadddr entry)))))))))

(defun l1-warrant-theorem-add-tame-example (certificates)
  (let* ((proof (l1-primitive-certificates-proof certificates))
         (step (and (assoc-equal *l1-warrant-tame-function* (proof-proof-definitions proof))
                    (l1-warrant-warrant-proof-trivial-function-tame proof)))
         (term (list *l1-warrant-tame-function* (proof-quote *l1-warrant-trivial-function*))))
    (if (equal (proof-step-clause step) (list (proof-eq term *proof-true*)))
        (proof-with-checked-results
            ((added (l1-primitive-certificates-add
                     certificates *l1-application-warrant-tame-example* step)))
          (cdr added))
      certificates)))

(defun l1-warrant-theorem-prove-match (proof name formula parts match unfold-force)
  (proof-with-checked-results
      ((certificates (l1-warrant-warrant-logic (l1-primitive-certificates-init proof)))
       (certificates (l1-warrant-theorem-add-tame-example certificates))
       (badge (l1-warrant-theorem-add-user-equation
               certificates *l1-warrant-theorem-user-badge*
               (list *l1-application-badge* *library-x*) (list *l1-warrant-badge* *library-x*)))
       (certificates (l1-warrant-theorem-add-user-equation
                      badge *l1-warrant-theorem-user-apply*
                      (list *l1-application-apply* *library-x* *library-y*)
                      (list *l1-warrant-apply-user-function* *library-x* *library-y*)))
       (table (l1-primitive-badge-table-init certificates))
       (function (proof-term-at (cadddr match) 1))
       (witnesses (l1-primitive-badge-table-absence table function *l1-warrant-theorem-non-primitive*)))
    (and witnesses
         (l1-warrant-theorem-prove-non-primitive
          (l1-primitive-badge-table-certificates (cdr witnesses))
          (caar witnesses) name formula parts match unfold-force))))

(defun l1-warrant-theorem-prove-fragments (proof name formula choices)
  (proof-with-checked-results
      ((parts (l1-warrant-theorem-theorem-parts formula))
       (match (and parts (l1-warrant-theorem-matching-warrant proof choices parts))))
    (and match
         (let ((force (car parts)))
           (proof-with-checked-results
               ((unfold-force (proof-proof-unfold proof force))
                (unfolded (l1-warrant-step-at-place unfold-force '(2)))
                (warrant (proof-term-at force 1)))
             (and (equal unfolded warrant)
                  (l1-warrant-theorem-prove-match proof name formula parts match unfold-force)))))))

