(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h1-propositions-rewrite-value (lib step equality)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (proof-rewritten-term step))
         (literal (proof-step-first equality))
         (left (proof-term-at literal 1)))
      (proof-proof-rewrite-result proof step equality (proof-eq *proof-result* value) left))))

(defun h1-propositions-select-value (lib equation test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (proof-rewritten-term equation))
         (selected (h1-arithmetic-proof-select proof value test)))
      (proof-proof-chain proof equation (list selected)))))

(defund h1-propositions-beta-value-next (proof equation)
  (proof-with-checked-results ((value (proof-rewritten-term equation)))
    (if (and (consp value) (proof-compound value) (proof-compound (car value)))
        (proof-with-checked-results ((beta (proof-proof-beta proof value)))
          (proof-proof-chain proof equation (list beta)))
      nil)))

(defun h1-propositions-beta-value-loop (n proof equation)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h1-propositions-beta-value-loop")
    (proof-with-checked-results ((next (h1-propositions-beta-value-next proof equation)))
      (if next
          (h1-propositions-beta-value-loop (1- n) proof next)
        equation))))

(defun h1-propositions-beta-value (lib equation)
  (h1-propositions-beta-value-loop 1000000 (library-library-proof lib) equation))

(defun h1-propositions-computed-test (lib equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((value (proof-rewritten-term equation)))
      (cond ((equal value *proof-true*) (proof-proof-true-from-eq proof equation))
            ((equal value *proof-false*)
             (proof-with-checked-results ((not-nil (proof-proof-not-nil proof)))
               (h1-arithmetic-library-transport-argument lib not-nil equation 1)))
            (t '(:failure "failure" ""))))))

(defun h1-propositions-propositional-proof-logic-and-types (lib)
  (if (h1-arithmetic-proof-has-fact (library-library-proof lib) "SELF-GAP-ORDINAL")
      lib
    (library-library-logic-and-types lib)))

(defun h1-propositions-propositional-proof-reflexive (lib term)
  (h1-arithmetic-proof-reflexive (library-library-proof lib) term))

(defun h1-propositions-propositional-proof-select (lib term evidence)
  (h1-arithmetic-proof-select (library-library-proof lib) term evidence))

(defun h1-propositions-propositional-proof-conjoin (lib formula left right)
  (h1-arithmetic-proof-conjoin (library-library-proof lib) formula left right))

(defun h1-propositions-propositional-proof-conjunct (lib step)
  (h1-arithmetic-proof-conjunct (library-library-proof lib) step))

(defun h1-propositions-propositional-proof-modus-ponens (lib step evidence)
  (h1-arithmetic-proof-modus-ponens (library-library-proof lib) step evidence))

(defun h1-propositions-propositional-proof-false-premise (lib formula evidence)
  (h1-arithmetic-proof-false-premise (library-library-proof lib) formula evidence))

(defun h1-propositions-propositional-proof-implies-from (lib formula consequence)
  (h1-arithmetic-proof-implies-from (library-library-proof lib) formula consequence))

(defun h1-propositions-conditional-guard (lib name guard step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((front (proof-proof-front proof step guard))
         (condition (proof-step-first step)))
      (library-library-lemma lib name guard front (list condition)))))

(defun h1-propositions-setup-conditionals (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (conditional (proof-ite x *library-y* *library-z*)))
    (proof-with-checked-results
        ((true-step (h1-arithmetic-proof-if-true proof conditional))
         (false-step (h1-arithmetic-proof-if-false proof conditional))
         (lib (h1-propositions-conditional-guard lib "IF-TRUE-GUARD" (proof-neg x) true-step)))
      (h1-propositions-conditional-guard lib "IF-FALSE-GUARD" x false-step))))

(defun h1-propositions-setup-conjunction (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (both (proof-ite x y *proof-false*)))
    (proof-with-checked-results
        ((branch (h1-arithmetic-proof-if-true proof both))
         (selected (h1-arithmetic-proof-symmetric proof branch))
         (lib (h1-propositions-conditional-guard lib "CONJUNCTION-WHEN-LEFT"
                                                  (proof-neg x) selected))
         (proof (library-library-proof lib))
         (assumed (h1-arithmetic-proof-assume proof both t))
         (parts (h1-arithmetic-proof-conjunct-base proof assumed))
         (lib (library-library-lemma lib "CONJUNCTION-LEFT" x (car parts)
                                      (list (proof-neg both)))))
      (library-library-lemma lib "CONJUNCTION-RIGHT" y (cadr parts)
                             (list (proof-neg both))))))

(defun h1-propositions-setup-implication (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (implication (list *library-implies* x y)))
    (proof-with-checked-results
        ((assumed (h1-arithmetic-proof-assume proof implication t))
         (premise (h1-arithmetic-proof-assume proof x t))
         (elim (h1-arithmetic-proof-modus-ponens-base proof assumed premise))
         (lib (library-library-lemma lib "IMPLICATION-ELIM" y elim
                                      (list (proof-neg implication) (proof-neg x))))
         (known (h1-arithmetic-proof-assume (library-library-proof lib) y t))
         (consequent (h1-propositions-propositional-proof-implies-from lib implication known))
         (lib (library-library-lemma lib "IMPLICATION-CONSEQUENT" implication
                                      consequent (list (proof-neg y))))
         (false-premise (h1-propositions-propositional-proof-false-premise lib implication nil)))
      (library-library-lemma lib "IMPLICATION-NO-PREMISE" implication false-premise (list x)))))

(defun h1-propositions-propositional-proof-setup-propositions (lib)
  (proof-with-checked-results
      ((lib (h1-propositions-propositional-proof-logic-and-types lib))
       (same (h1-propositions-propositional-proof-reflexive lib *library-x*))
       (lib (library-library-lemma lib "REFLEXIVITY" (proof-eq *library-x* *library-x*) same nil))
       (lib (h1-propositions-setup-conditionals lib))
       (lib (h1-propositions-setup-conjunction lib)))
    (h1-propositions-setup-implication lib)))

(defun h1-propositions-proof-symmetric (proof equality)
  (h1-arithmetic-proof-symmetric proof equality))

(defun h1-propositions-proof-prove-if (proof step test-proof)
  (h1-arithmetic-proof-prove-if proof step test-proof))

(defun h1-propositions-proof-transport (proof step equality)
  (h1-arithmetic-proof-transport proof step equality))

(defun h1-propositions-library-transport-argument (lib step equality index)
  (h1-arithmetic-library-transport-argument lib step equality index))

(defun h1-propositions-proof-simplify (proof term evidence definitions)
  (h1-arithmetic-proof-simplify proof term evidence definitions))
