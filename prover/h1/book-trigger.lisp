(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-book-trigger-trigger*
  (proof-sym "TRIGGERING-LIT-FOR-REWRITE-WITH-EQUALP" "ACL2"))
(defconst *h1-book-trigger-find*
  (proof-sym "FIND-TRIGGERING-LIT-FOR-REWRITE-WITH-EQUALP" "ACL2"))
(defconst *h1-book-trigger-rewrite*
  (proof-sym "REWRITE-CLAUSE-WITH-EQUAL" "ACL2"))
(defconst *h1-book-trigger-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *h1-book-trigger-conjoin-clauses* (proof-sym "CONJOIN-CLAUSES" "ACL2"))
(defconst *h1-book-trigger-disjoin-list* (proof-sym "DISJOIN-LST" "ACL2"))
(defconst *h1-book-trigger-conjoin* (proof-sym "CONJOIN" "ACL2"))
(defconst *h1-book-trigger-return-last* (proof-sym "RETURN-LAST" "ACL2"))
(defconst *h1-book-trigger-two* (proof-quote 2))

(defun h1-book-trigger-semantic-match (literal old new)
  (list *library-implies*
        (proof-neg (h1-book-rewrite-equal-evaluated literal))
        (proof-eq (h1-book-rewrite-equal-evaluated old)
                  (h1-book-rewrite-equal-evaluated new))))

(defun h1-book-trigger-tuple-parts (result first-is-car)
  (list (if first-is-car
            (list *library-car* result)
          (list *h1-book-trigger-mv-nth* *proof-zero* result))
        (list *h1-book-trigger-mv-nth* *proof-one* result)
        (list *h1-book-trigger-mv-nth* *h1-book-trigger-two* result)))

(defun h1-book-trigger-tuple-fields (value)
  (proof-with-checked-results
      ((literal (proof-term-at value 1))
       (tail (proof-term-at value 2))
       (old (proof-term-at tail 1))
       (last-cons (proof-term-at tail 2))
       (new (proof-term-at last-cons 1)))
    (list literal old new)))

(defun h1-book-trigger-step-term (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h1-book-trigger-restore-tuple-field (proof step expected place field)
  (let ((core (h1-tactics-prover-proof proof))
        (openings (list (cons *h1-book-trigger-mv-nth* 4)
                        (cons (proof-sym "ZP" "ACL2") 2))))
    (proof-with-checked-results
        ((equality (h1-tactics-prover-solve proof (proof-eq place field) openings 160))
         (symmetric (h1-propositions-proof-symmetric core equality)))
      (proof-proof-rewrite-result core step symmetric expected place))))

(defun h1-book-trigger-restore-tuple (proof step expected value first-is-car)
  (let ((places (h1-book-trigger-tuple-parts value first-is-car)))
    (proof-with-checked-results
        ((fields (h1-book-trigger-tuple-fields value))
         (step (h1-book-trigger-restore-tuple-field proof step expected (car places) (car fields)))
         (step (h1-book-trigger-restore-tuple-field proof step expected (cadr places) (cadr fields))))
      (h1-book-trigger-restore-tuple-field proof step expected (caddr places) (caddr fields)))))

(defun h1-book-trigger-literal-equality-equation (proof rulers number term operation)
  (let ((core (h1-tactics-prover-proof proof))
        (library (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((rule (h1-book-rewrite-equal-constraint
                proof number (h1-book-rewrite-equal-evaluated term)))
         (condition (h1-book-trigger-step-term rule 1))
         (guard (list (proof-cl "EQ") (list *library-car* term)
                      (proof-quote (proof-cl operation))))
         (known-guard (h1-book-termination-rulers-require rulers guard))
         (opened-guard (proof-proof-unfold core guard))
         (head (proof-proof-rewrite core (car known-guard) opened-guard '(1)))
         (test (proof-term-at condition 1))
         (known-test (h1-book-termination-rulers-require (cdr known-guard) test))
         (premise (h1-propositions-propositional-proof-conjoin
                   library condition (car known-test) head))
         (equation (h1-propositions-propositional-proof-modus-ponens
                    library rule premise)))
      (cons equation (cdr known-test)))))

(defun h1-book-trigger-literal-equality (proof literal tests)
  (let ((core (h1-tactics-prover-proof proof))
        (inner (list *library-car* (list *library-cdr* literal))))
    (proof-with-checked-results
        ((rulers (h1-book-termination-rulers-init proof tests))
         (first (h1-book-trigger-literal-equality-equation proof rulers 8 literal "NOT"))
         (second (h1-book-trigger-literal-equality-equation
                  proof (cdr first) 9 inner "EQUAL"))
         (negated (proof-proof-rewrite core (car first) (car second) '(1 2 1)))
         (known-false (proof-proof-assume
                       core (proof-neg (h1-book-rewrite-equal-evaluated literal)) t))
         (double-negation (proof-proof-rewrite core known-false negated '(1 1)))
         (equality (h1-book-trigger-step-term (car second) 2))
         (assumption (proof-proof-assume core equality nil))
         (result (proof-proof-cut core assumption double-negation)))
      (proof-proof-front core result equality))))

(defun h1-book-trigger-trigger-selection-signature (literal old new)
  (proof-with-checked-results
      ((claims (h1-book-cofactors-combine
                (list (proof-eq literal *library-y*)
                      (h1-book-trigger-semantic-match literal old new)))))
    (list *library-implies* literal claims)))

(defun h1-book-trigger-trigger-selection-true (proof literal old new formula tests)
  (let ((core (h1-tactics-prover-proof proof))
        (library (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((equality (h1-book-trigger-literal-equality proof literal tests))
         (goal (h1-book-trigger-semantic-match literal old new))
         (first (proof-step-first equality))
         (equality (if (equal first (caddr goal))
                       equality
                     (h1-propositions-proof-symmetric core equality)))
         (reflexive (h1-propositions-propositional-proof-reflexive library *library-y*))
         (implied (h1-propositions-propositional-proof-implies-from library goal equality))
         (claim (h1-propositions-propositional-proof-conjoin
                 library (caddr formula) reflexive implied)))
      (h1-propositions-propositional-proof-implies-from library formula claim))))

(defun h1-book-trigger-trigger-selection-leaf (value tests proof template)
  (let ((core (h1-tactics-prover-proof proof))
        (library (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((fields (h1-book-trigger-tuple-fields value))
         (formula (h1-book-trigger-trigger-selection-signature
                   (car fields) (cadr fields) (caddr fields)))
         (step (if (equal (car fields) *proof-false*)
                   (proof-with-checked-results
                       ((premise (h1-propositions-propositional-proof-false-premise
                                  library formula nil)))
                     (proof-proof-tidy core premise))
                 (h1-book-trigger-trigger-selection-true
                  proof (car fields) (cadr fields) (caddr fields) formula tests)))
         (expected (proof-subst template (list (cons *proof-result* value)))))
      (h1-book-trigger-restore-tuple proof step expected value nil))))

(defun h1-book-trigger-found-member (proof literal endp head-equality tail)
  (let ((core (h1-tactics-prover-proof proof))
        (library (h1-tactics-prover-library proof))
        (member (list *h1-book-disjoin-member* literal *library-x*)))
    (proof-with-checked-results
        ((expanded (proof-proof-unfold core member))
         (opened (h1-propositions-select-value library expanded endp))
         (opened-value (h1-book-trigger-step-term opened 2))
         (test (proof-term-at opened-value 1))
         (head (if head-equality head-equality (proof-proof-assume core test t)))
         (hit (h1-propositions-select-value library opened head))
         (cons-step (h1-book-termination-cons-from-nonatom proof endp))
         (truth (h1-book-termination-cons-implies-truth proof *library-x* cons-step))
         (yes (h1-propositions-proof-transport core truth hit)))
      (if head-equality
          yes
        (proof-with-checked-results
            ((assumption (proof-proof-assume core test nil))
             (missed (h1-propositions-select-value library opened assumption))
             (no (h1-propositions-proof-transport core tail missed)))
          (proof-proof-cases core test yes no))))))

(defun h1-book-trigger-find-selection-signature (literal old new)
  (proof-with-checked-results
      ((claims (h1-book-cofactors-combine
                (list (list *h1-book-disjoin-member* literal *library-x*)
                      (h1-book-trigger-semantic-match literal old new)))))
    (list *library-implies* literal claims)))

(defun h1-book-trigger-find-selection-recursive (proof result not-end formula bindings)
  (let ((core (h1-tactics-prover-proof proof))
        (library (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((builtin (library-library-builtin library 3 *library-x*))
         (cons-step (h1-book-termination-cons-from-nonatom proof not-end))
         (descent (proof-proof-discharge core builtin cons-step))
         (smaller (proof-step-first descent))
         (dictionary (proof-bindings-table bindings nil))
         (child-formula (proof-subst formula dictionary))
         (hypothesis (proof-proof-assume core (proof-ite smaller child-formula *proof-true*) t))
         (child (h1-propositions-proof-prove-if core hypothesis descent))
         (literal (proof-proof-assume core (cadr result) t))
         (given (h1-propositions-propositional-proof-modus-ponens library child literal))
         (parts (h1-propositions-propositional-proof-conjunct library given))
         (member (h1-book-trigger-found-member proof (cadr result) not-end nil (car parts)))
         (claim (h1-propositions-propositional-proof-conjoin
                 library (caddr result) member (cadr parts))))
      (h1-propositions-propositional-proof-implies-from library result claim))))

(defun h1-book-trigger-find-selection-direct (proof literal direct not-end)
  (let ((core (h1-tactics-prover-proof proof))
        (library (h1-tactics-prover-library proof)))
    (if (equal literal *proof-false*)
        (proof-with-checked-results
            ((premise (h1-propositions-propositional-proof-false-premise library direct nil)))
          (proof-proof-tidy core premise))
      (proof-with-checked-results
          ((trigger (library-library-cite library "TRIGGER-SIGNATURE"
                                         (list *library-y* (list *library-car* *library-x*)) nil))
           (assumption (proof-proof-assume core literal t))
           (given (h1-propositions-propositional-proof-modus-ponens library trigger assumption))
           (parts (h1-propositions-propositional-proof-conjunct library given))
           (member (h1-book-trigger-found-member proof literal not-end (car parts) nil))
           (claim (h1-propositions-propositional-proof-conjoin
                   library (caddr direct) member (cadr parts))))
        (h1-propositions-propositional-proof-implies-from library direct claim)))))

(defun h1-book-trigger-find-selection-leaf (value tests proof template formula endp bindings)
  (declare (ignore tests))
  (let ((core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((result (proof-subst template (list (cons *proof-result* value))))
         (not-end (proof-proof-assume core endp nil)))
      (if (proof-is-call value *h1-book-trigger-find*)
          (h1-book-trigger-find-selection-recursive proof result not-end formula bindings)
        (proof-with-checked-results
            ((fields (h1-book-trigger-tuple-fields value))
             (direct (h1-book-trigger-find-selection-signature
                      (car fields) (cadr fields) (caddr fields)))
             (branch (h1-book-trigger-find-selection-direct proof (car fields) direct not-end)))
          (h1-book-trigger-restore-tuple proof branch result value t))))))

; FIND-DATA holds the induction formula, end test and bindings for a search leaf.
(defun h1-book-trigger-by-value (n proof value template tests find-data)
  (declare (xargs :measure (nfix n)))
  (let ((core (h1-tactics-prover-proof proof)))
    (cond
     ((zp n) '(:failure "fuel" "h1-book-trigger-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (yes (h1-book-trigger-by-value (1- n) proof (cadr branches) template
                                          (append tests (list (list (car branches) t))) find-data))
           (no (h1-book-trigger-by-value (1- n) proof (caddr branches) template
                                         (append tests (list (list (car branches) nil))) find-data))
           (if-true (proof-proof-if-true core value))
           (true-equality (h1-propositions-proof-symmetric core if-true))
           (yes (proof-proof-rewrite-result core yes true-equality template *proof-result*))
           (if-false (proof-proof-if-false core value))
           (false-equality (h1-propositions-proof-symmetric core if-false))
           (no (proof-proof-rewrite-result core no false-equality template *proof-result*)))
        (proof-proof-cases core (car branches) yes no)))
     ((and (proof-compound value) (endp value))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta core value))
           (opened (h1-book-trigger-step-term equality 2))
           (step (h1-book-trigger-by-value (1- n) proof opened template tests find-data))
           (symmetric (h1-propositions-proof-symmetric core equality)))
        (proof-proof-rewrite-result core step symmetric template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (if find-data
                     (h1-book-trigger-find-selection-leaf value tests proof template
                                                          (car find-data) (cadr find-data)
                                                          (caddr find-data))
                   (h1-book-trigger-trigger-selection-leaf value tests proof template)))
           (first (proof-step-first step))
           (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal first target) step '(:failure "failure" "")))))))

(defun h1-book-trigger-trigger-selection (proof)
  (let ((call (list *h1-book-trigger-trigger* *library-x* *library-y*))
        (core (h1-tactics-prover-proof proof))
        (parts (h1-book-trigger-tuple-parts *proof-result* nil)))
    (proof-with-checked-results
        ((template (h1-book-trigger-trigger-selection-signature
                    (car parts) (cadr parts) (caddr parts)))
         (expansion (proof-proof-unfold core call))
         (expanded (h1-book-trigger-step-term expansion 2))
         (result (h1-book-trigger-by-value 1000000 proof expanded template nil nil))
         (symmetric (h1-propositions-proof-symmetric core expansion)))
      (proof-proof-rewrite-result core result symmetric template *proof-result*))))

(defun h1-book-trigger-find-selection (proof)
  (let ((call (list *h1-book-trigger-find* *library-y* *library-x*))
        (core (h1-tactics-prover-proof proof))
        (library (h1-tactics-prover-library proof))
        (parts (h1-book-trigger-tuple-parts *proof-result* t)))
    (proof-with-checked-results
        ((template (h1-book-trigger-find-selection-signature
                    (car parts) (cadr parts) (caddr parts)))
         (formula (proof-subst template (list (cons *proof-result* call))))
         (expansion (proof-proof-unfold core call))
         (endp (list *h1-book-rewrite-equal-endp* *library-x*))
         (bindings (list (list *library-x* (list *library-cdr* *library-x*))))
         (expanded (h1-book-trigger-step-term expansion 2))
         (branches (h1-book-trigger-by-value 1000000 proof expanded template nil
                                            (list formula endp bindings)))
         (symmetric (h1-propositions-proof-symmetric core expansion))
         (reconstructed (proof-proof-rewrite-result core branches symmetric template *proof-result*))
         (measure (list *library-count* *library-x*))
         (ordinal (descent-measure-ordinal library measure)))
      (proof-proof-induct core ordinal reconstructed formula measure (list bindings)))))

(defun h1-book-trigger-prove-rewriter-branch (proof expansion result evidence)
  (let ((core (h1-tactics-prover-proof proof))
        (library (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((value (h1-propositions-select-value library expansion evidence))
         (right (h1-book-trigger-step-term value 2))
         (value (if (proof-is-call right *h1-book-trigger-return-last*)
                    (proof-with-checked-results ((opened (proof-proof-unfold core right)))
                      (proof-proof-chain core value (list opened)))
                  value))
         (right (h1-book-trigger-step-term value 2))
         (clause (proof-term-at right 1))
         (evaluation (proof-proof-rewrite core result value '(1 1 1)))
         (singleton (library-library-cite library "CONJOIN-SINGLE-CLAUSE" (list clause) nil)))
      (proof-proof-rewrite core evaluation singleton '(1 1)))))

(defun h1-book-trigger-prove-rewriter (proof)
  (let* ((core (h1-tactics-prover-proof proof))
         (library (h1-tactics-prover-library proof))
         (rewritten (list *h1-book-trigger-rewrite* *library-x* *library-y*))
         (evaluated-clauses (h1-book-rewrite-equal-evaluated
                             (list *h1-book-trigger-conjoin-clauses* rewritten)))
         (goal (h1-book-rewrite-equal-evaluated (list *h1-book-disjoin-disjoin* *library-x*)))
         (typed (list (proof-sym "PSEUDO-TERM-LISTP" "ACL2") *library-x*))
         (alist (list (proof-sym "ALISTP" "ACL2") *h1-book-rewrite-equal-environment*)))
    (proof-with-checked-results
        ((premise (h1-book-cofactors-combine (list typed alist evaluated-clauses)))
         (assumed (proof-proof-assume core premise t))
         (components (h1-book-cofactors-components proof assumed))
         (components (proof-list-of-length components 3))
         (call (list *h1-book-trigger-find* *library-y* *library-x*))
         (parts (h1-book-trigger-tuple-parts call t))
         (literal (car parts))
         (opened (proof-proof-unfold core rewritten))
         (expansion (h1-propositions-beta-value library opened))
         (head (library-library-cite library "MV-NTH-ZERO-IS-CAR" (list call) nil))
         (present (proof-proof-assume core literal t))
         (match (h1-propositions-proof-transport core present head))
         (absent (proof-proof-assume core literal nil))
         (miss (h1-propositions-library-transport-argument library absent head 1))
         (changed (h1-book-trigger-prove-rewriter-branch proof expansion (caddr components) match))
         (unchanged (h1-book-trigger-prove-rewriter-branch proof expansion (caddr components) miss))
         (equal-step (library-library-cite library "MATCHED-EVALUATIONS"
                                           (list *library-x* *library-y*) nil))
         (condition (h1-book-trigger-step-term equal-step 1))
         (present (proof-proof-assume core literal t))
         (false-goal (proof-proof-assume core goal nil))
         (givens (h1-arithmetic-conjunction library condition
                                            (list (car components) present false-goal)))
         (equal-step (h1-propositions-propositional-proof-modus-ponens library equal-step givens))
         (transfer (library-library-cite library "REWRITE-CLAUSE-GENERAL"
                                         (list *library-x* (caddr parts) (cadr parts)) nil))
         (condition (h1-book-trigger-step-term transfer 1))
         (symmetric (h1-propositions-proof-symmetric core equal-step))
         (supplied (h1-arithmetic-conjunction library condition
                                              (list (car components) (cadr components)
                                                    symmetric changed)))
         (contradiction (h1-propositions-propositional-proof-modus-ponens library transfer supplied))
         (true-goal (proof-proof-assume core goal t))
         (positive (proof-proof-cases core goal true-goal contradiction))
         (consequence (proof-proof-cases core literal positive unchanged)))
      (h1-propositions-propositional-proof-implies-from
       library (list *library-implies* premise goal) consequence))))

(defun h1-book-trigger-lemma (proof name step)
  (proof-with-checked-results
      ((first (proof-step-first step))
       (library (library-library-lemma (h1-tactics-prover-library proof) name first step nil)))
    (h1-tactics-prover-with-library proof library)))

(defun h1-book-trigger-install-found-clause-member (proof typed literal)
  (let ((core (h1-tactics-prover-proof proof))
        (library (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((premise (h1-book-cofactors-combine (list typed literal)))
         (assumption (proof-proof-assume core premise t))
         (components (h1-propositions-propositional-proof-conjunct library assumption))
         (found (library-library-cite library "FIND-TRIGGER-SIGNATURE" (list *library-x* *library-y*) nil))
         (result (h1-propositions-propositional-proof-modus-ponens library found (cadr components)))
         (parts (h1-propositions-propositional-proof-conjunct library result))
         (member (car parts))
         (first (proof-step-first member))
         (claim (h1-propositions-propositional-proof-implies-from
                 library (list *library-implies* premise first) member))
         (recorded (h1-tactics-prover-record-formula proof "FOUND-CLAUSE-MEMBER" claim nil)))
      (cdr recorded))))

(defun h1-book-trigger-install-matched-evaluations (proof typed literal)
  (let ((core (h1-tactics-prover-proof proof))
        (library (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((premise (h1-book-cofactors-combine
                   (list typed literal (proof-neg (h1-book-rewrite-equal-evaluated
                                                    (list *h1-book-disjoin-disjoin* *library-x*))))))
         (assumption (proof-proof-assume core premise t))
         (components (h1-book-cofactors-components proof assumption))
         (components (proof-list-of-length components 3))
         (found (library-library-cite library "FIND-TRIGGER-SIGNATURE" (list *library-x* *library-y*) nil))
         (result (h1-propositions-propositional-proof-modus-ponens library found (cadr components)))
         (parts (h1-propositions-propositional-proof-conjunct library result))
         (falsity (library-library-cite library "FALSE-CLAUSE-MEMBER" (list *library-x* literal) nil))
         (condition (h1-book-trigger-step-term falsity 1))
         (given (h1-arithmetic-conjunction
                 library condition (list (car components) (caddr components) (car parts))))
         (false-member (h1-propositions-propositional-proof-modus-ponens library falsity given))
         (substitution (h1-propositions-propositional-proof-modus-ponens
                        library (cadr parts) false-member))
         (first (proof-step-first substitution))
         (claim (h1-propositions-propositional-proof-implies-from
                 library (list *library-implies* premise first) substitution))
         (recorded (h1-tactics-prover-record-formula proof "MATCHED-EVALUATIONS" claim nil)))
      (cdr recorded))))

(defun h1-book-trigger-install-triggers (proof)
  (proof-with-checked-results
      ((trigger (h1-book-trigger-trigger-selection proof))
       (proof (h1-book-trigger-lemma proof "TRIGGER-SIGNATURE" trigger))
       (found (h1-book-trigger-find-selection proof))
       (proof (h1-book-trigger-lemma proof "FIND-TRIGGER-SIGNATURE" found))
       (typed (list (proof-sym "PSEUDO-TERM-LISTP" "ACL2") *library-x*))
       (literal (list *library-car* (list *h1-book-trigger-find* *library-y* *library-x*)))
       (proof (h1-book-trigger-install-found-clause-member proof typed literal))
       (proof (h1-book-trigger-install-matched-evaluations proof typed literal))
       (zp-symbol (proof-sym "ZP" "ACL2"))
       (zero (h1-tactics-prover-solve
              proof (proof-eq (list *h1-book-trigger-mv-nth* *proof-zero* *library-x*)
                              (list *library-car* *library-x*))
              (list *h1-book-trigger-mv-nth* zp-symbol (proof-cl "ATOM")) 160))
       (proof (h1-book-trigger-lemma proof "MV-NTH-ZERO-IS-CAR" zero))
       (single (h1-tactics-prover-solve
                proof (proof-eq (list *h1-book-trigger-conjoin-clauses*
                                      (list *proof-cons* *library-x* *proof-false*))
                                (list *h1-book-disjoin-disjoin* *library-x*))
                (list (cons *h1-book-trigger-conjoin-clauses* 1)
                      (cons *h1-book-trigger-disjoin-list* 2)
                      (cons *h1-book-trigger-conjoin* 1)
                      (cons *h1-book-rewrite-equal-endp* 3))
                160))
       (proof (h1-book-trigger-lemma proof "CONJOIN-SINGLE-CLAUSE" single))
       (rewriter (h1-book-trigger-prove-rewriter proof))
       (recorded (h1-tactics-prover-record-formula proof "EQUALITY-CLAUSE-REWRITER" rewriter nil)))
    (cdr recorded)))
