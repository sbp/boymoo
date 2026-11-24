(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-total-order-strict* (proof-sym "<<" "ACL2"))
(defconst *b1-total-order-order* (proof-sym "LEXORDER" "ACL2"))

(defun b1-total-order-strict-definition (lib comparison)
  (b1-logic-bookproof-normalize lib comparison nil
                                (list *b1-total-order-strict*) nil nil nil nil))

(defun b1-total-order-strict-components-expanded (lib strict)
  (proof-with-checked-results
      ((literal (b1-logic-step-first strict))
       (definition (b1-total-order-strict-definition lib literal)))
    (proof-proof-rewrite (library-library-proof lib) strict definition '(1))))

(defun b1-total-order-strict-components (lib strict)
  (proof-with-checked-results
      ((expanded (b1-total-order-strict-components-expanded lib strict)))
    (b1-logic-bookproof-split-conjuncts lib expanded)))

(defun b1-total-order-assemble-strict (lib conclusion ordered unequal)
  (proof-with-checked-results
      ((expanded (b1-total-order-strict-definition lib conclusion))
       (literal (proof-step-first expanded))
       (target (proof-term-at literal 2))
       (step (b1-logic-bookproof-normalize-proof lib target (list ordered unequal)
                                               nil nil nil)))
    (proof-proof-transport (library-library-proof lib) step expanded)))

(defun b1-total-order-order-fact (lib name args)
  (library-library-axiom lib (concatenate 'string "LEXORDER-" name) args))

(defun b1-total-order-antisymmetric (lib first second)
  (proof-with-checked-results
      ((literal (b1-logic-step-first first))
       (fact (b1-total-order-order-fact lib "ANTI-SYMMETRIC" (cdr literal)))
       (claim (proof-step-first fact))
       (test (proof-term-at claim 1))
       (premise (b1-logic-bookproof-normalize-proof lib test (list first second)
                                                  nil nil nil)))
    (proof-proof-modus-ponens (library-library-proof lib) fact premise)))

(defun b1-total-order-strict-irreflexive (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((comparison (proof-term-at formula 1))
         (opened (b1-total-order-strict-definition lib comparison))
         (x (proof-term-at comparison 1))
         (literal (proof-step-first opened))
         (target (proof-term-at literal 2))
         (reflexive (b1-total-order-order-fact lib "REFLEXIVE" (list x)))
         (value (b1-logic-bookproof-normalize lib target (list reflexive)
                                             (list *proof-not*) nil nil nil nil))
         (reduction (proof-proof-chain proof opened (list value))))
      (b1-logic-bookproof-normalize-proof lib formula nil (list *proof-not*)
                                         (list (b1-logic-equal-to reduction)) nil))))

(defun b1-total-order-strict-implies-order (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (expanded (b1-total-order-strict-components-expanded lib premise))
       (first (b1-logic-bookproof-split-conjuncts-first lib expanded)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise first)))

(defun b1-total-order-strict-asymmetric-consequence (strict lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (b1-total-order-strict-components lib strict))
         (forward-parts (proof-list-of-length parts 2))
         (goal (proof-term-at formula 2))
         (backward-test (proof-term-at goal 1))
         (backward-step (proof-proof-assume proof backward-test t))
         (parts (b1-total-order-strict-components lib backward-step))
         (backward-parts (proof-list-of-length parts 2))
         (same (b1-total-order-antisymmetric lib (car forward-parts) (car backward-parts)))
         (impossible (proof-proof-cut proof same (cadr forward-parts))))
      (proof-proof-front proof impossible goal))))

(defun b1-total-order-strict-asymmetric (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (step (b1-total-order-strict-asymmetric-consequence premise lib formula)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise step)))

(defun b1-total-order-strict-transitive-consequence (premise lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
         (inputs (proof-list-of-length conjuncts 2))
         (parts (b1-total-order-strict-components lib (car inputs)))
         (xy-parts (proof-list-of-length parts 2))
         (parts (b1-total-order-strict-components lib (cadr inputs)))
         (yz-parts (proof-list-of-length parts 2))
         (goal (proof-term-at formula 2))
         (ends (proof-list-of-length (cdr goal) 2))
         (xy (proof-step-first (car xy-parts)))
         (y (proof-term-at xy 2))
         (law (b1-total-order-order-fact lib "TRANSITIVE" (list (car ends) y (cadr ends))))
         (claim (proof-step-first law))
         (test (proof-term-at claim 1))
         (supported (b1-logic-bookproof-normalize-proof lib test
                                                       (list (car xy-parts) (car yz-parts))
                                                       nil nil nil))
         (xz-order (proof-proof-modus-ponens proof law supported)))
      (let ((same (proof-eq (car ends) (cadr ends))))
        (proof-with-checked-results
            ((assumed (proof-proof-assume proof same t))
             (symmetric (proof-proof-symmetric proof assumed))
             (yx-order (proof-proof-rewrite proof (car yz-parts) symmetric '(1 2)))
             (parallel (b1-total-order-antisymmetric lib (car xy-parts) yx-order))
             (impossible (proof-proof-cut proof parallel (cadr xy-parts)))
             (xz-distinct (proof-proof-front proof impossible (proof-neg same))))
          (b1-total-order-assemble-strict lib goal xz-order xz-distinct))))))

(defun b1-total-order-strict-transitive (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (step (b1-total-order-strict-transitive-consequence premise lib formula)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise step)))

(defun b1-total-order-strict-total-consequence (premise lib x y forward formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
         (inputs (proof-list-of-length conjuncts 2))
         (law (b1-total-order-order-fact lib "TOTAL" (list x y)))
         (assumed (proof-proof-assume proof forward nil))
         (other (proof-proof-prove-if proof law assumed))
         (literal (proof-step-first (car inputs)))
         (reverse-test (proof-term-at literal 1))
         (inequality (b1-reciprocal-reverse-inequality lib (cadr inputs)))
         (backward (b1-total-order-assemble-strict lib reverse-test other inequality))
         (cut (proof-proof-cut proof backward (car inputs)))
         (x-le-y (proof-proof-front proof cut forward))
         (goal (proof-term-at formula 2)))
      (b1-total-order-assemble-strict lib goal x-le-y (cadr inputs)))))

(defun b1-total-order-strict-total (lib formula)
  (proof-with-checked-results
      ((goal (proof-term-at formula 2))
       (terms (proof-list-of-length (cdr goal) 2)))
    (let* ((x (car terms))
           (y (cadr terms))
           (forward (list *b1-total-order-order* x y)))
      (proof-with-checked-results
          ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
           (step (b1-total-order-strict-total-consequence premise lib x y forward formula)))
        (b1-logic-bookproof-prove-implication-with-premise lib formula premise step)))))
