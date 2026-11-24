(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun t3-book-equivalence-parts (formula)
  (declare (xargs :measure (acl2-count formula)))
  (cond ((not (proof-is-call formula *proof-if*)) (list formula))
        ((not (consp (cdddr formula))) (proof-term-at formula 3))
        ((equal (cadddr formula) *proof-false*)
         (proof-with-checked-results
             ((rest (t3-book-equivalence-parts (caddr formula))))
           (cons (cadr formula) rest)))
        (t (list formula))))

(defun t3-book-equivalence-equality-boolean (lib equality)
  (let ((proof (library-library-proof lib))
        (definitions (list *t3-book-lemmas-booleanp* (proof-cl "EQ"))))
    (proof-with-checked-results
        ((positive (proof-proof-assume proof equality t))
         (yes (t3-book-lemmas-true-equality lib positive))
         (negative (proof-proof-assume proof equality nil))
         (no (t3-book-lemmas-nil-value lib negative))
         (first (proof-proof-prove proof (list *t3-book-lemmas-booleanp* *proof-true*)
                                  nil definitions))
         (second (proof-proof-prove proof (list *t3-book-lemmas-booleanp* *proof-false*)
                                   nil definitions))
         (first (library-library-transport-argument lib first yes 1))
         (second (library-library-transport-argument lib second no 1)))
      (proof-proof-cases proof equality first second))))

(defun t3-book-equivalence-unfold (proof terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof (car terms)))
         (rest (t3-book-equivalence-unfold proof (cdr terms))))
      (cons opened rest))))

(defun t3-book-equivalence-are-equalities (equations)
  (if (endp equations)
      t
    (proof-with-checked-results
        ((literal (proof-step-first (car equations)))
         (right (proof-term-at literal 2)))
      (and (proof-is-call right *proof-equal*)
           (t3-book-equivalence-are-equalities (cdr equations))))))

(defun t3-book-equivalence-symmetry (lib symmetry lhs forward backward)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumption (proof-proof-assume proof lhs t))
         (premise (proof-proof-rewrite proof assumption forward '(1)))
         (reversed (proof-proof-symmetric proof premise))
         (transported (proof-proof-transport proof reversed backward)))
      (t3-book-lemmas-implication lib symmetry transported))))

(defun t3-book-equivalence-transitivity (lib transitivity conditions first second target)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumption (proof-proof-assume proof conditions t))
         (conjuncts (proof-proof-conjunct proof assumption))
         (lhs (proof-proof-rewrite proof (car conjuncts) first '(1)))
         (rhs (proof-proof-rewrite proof (cadr conjuncts) second '(1)))
         (chain (proof-proof-chain proof lhs (list rhs)))
         (transported (proof-proof-transport proof chain target)))
      (t3-book-lemmas-implication lib transitivity transported))))

(defun t3-book-equivalence-assemble (proof result rules terms)
  (declare (xargs :measure (acl2-count rules)))
  (if (or (endp rules) (endp terms))
      result
    (proof-with-checked-results
        ((selected (proof-proof-select proof (car terms) (car rules)))
         (transported (proof-proof-transport proof result selected)))
      (t3-book-equivalence-assemble proof transported (cdr rules) (cdr terms)))))

(defun t3-book-equivalence-prove (lib formula symmetry lhs transitivity conditions
                                    equations argument)
  (let ((proof (library-library-proof lib))
        (typed (nth 0 equations))
        (reflexive (nth 1 equations))
        (forward (nth 2 equations))
        (backward (nth 3 equations))
        (first (nth 4 equations))
        (second (nth 5 equations))
        (target (nth 6 equations)))
    (proof-with-checked-results
        ((type-proof (t3-book-equivalence-equality-boolean lib (caddr (proof-step-first typed))))
         (type-proof (library-library-transport-argument lib type-proof typed 1))
         (refl (proof-proof-reflexive proof argument))
         (refl (proof-proof-transport proof refl reflexive))
         (sym (t3-book-equivalence-symmetry lib symmetry lhs forward backward))
         (result (t3-book-equivalence-transitivity lib transitivity conditions first second target)))
      (t3-book-equivalence-assemble proof result (list sym refl type-proof)
                                    (list (caddr (caddr formula)) (caddr formula) formula)))))

(defun t3-book-equivalence-check-equalities (lib formula symmetry lhs transitivity
                                                conditions equations)
  (let ((reflexive (caddr (proof-step-first (nth 1 equations))))
        (p (caddr (proof-step-first (nth 2 equations))))
        (q (caddr (proof-step-first (nth 3 equations))))
        (u (caddr (proof-step-first (nth 4 equations))))
        (v (caddr (proof-step-first (nth 5 equations))))
        (w (caddr (proof-step-first (nth 6 equations)))))
    (proof-with-checked-results
        ((argument (proof-term-at reflexive 1))
         (other (proof-term-at reflexive 2)))
      (if (or (not (equal argument other)) (not (equal (cdr p) (reverse (cdr q)))))
          nil
        (proof-with-checked-results
            ((middle (proof-term-at u 2))
             (next (proof-term-at v 1)))
          (if (not (equal middle next))
              nil
            (proof-with-checked-results
                ((start (proof-term-at u 1))
                 (end (proof-term-at v 2)))
              (and (equal w (proof-eq start end))
                   (t3-book-equivalence-prove lib formula symmetry lhs transitivity
                                              conditions equations argument)))))))))

(defun t3-book-equivalence-calls-p (terms symbol)
  (or (endp terms)
      (and (proof-is-call (car terms) symbol)
           (t3-book-equivalence-calls-p (cdr terms) symbol))))

(defun t3-book-equivalence-relation-conditions (lib formula relation reflexivity symmetry transitivity
                                                    sides closure)
  (let ((conditions (car closure)))
    (if (not (proof-is-call conditions *proof-if*))
        nil
      (proof-with-checked-results ((tail (proof-term-at conditions 3)))
        (let ((terms (list reflexivity (car sides) (cadr sides) (cadr conditions)
                           (caddr conditions) (cadr closure))))
          (if (not (and (equal tail *proof-false*)
                        (t3-book-equivalence-calls-p terms (car relation))))
              nil
            (proof-with-checked-results
                ((equations (t3-book-equivalence-unfold (library-library-proof lib)
                                                        (cons relation terms)))
                 (valid (t3-book-equivalence-are-equalities equations)))
              (and valid (t3-book-equivalence-check-equalities lib formula symmetry (car sides)
                                                              transitivity conditions equations)))))))))

(defun t3-book-equivalence-relation-form (lib formula relation reflexivity symmetry transitivity)
  (let ((proof (library-library-proof lib)))
    (cond ((integerp relation) '(:failure "failure" ""))
          ((or (not (equal (len relation) 3))
               (not (assoc-equal (car relation) (proof-proof-definitions proof))))
           nil)
          (t
           (proof-with-checked-results
               ((sides (proof-list-of-length (cdr symmetry) 2))
                (closure (proof-list-of-length (cdr transitivity) 2)))
             (t3-book-equivalence-relation-conditions lib formula relation reflexivity symmetry
                                                       transitivity sides closure))))))

(defun t3-book-equivalence-equality-relation (lib formula)
  (proof-with-checked-results ((components (t3-book-equivalence-parts formula)))
    (if (not (equal (len components) 4))
        nil
      (let ((typing (car components))
            (reflexivity (cadr components))
            (symmetry (caddr components))
            (transitivity (cadddr components)))
        (if (not (and (proof-is-call typing *t3-book-lemmas-booleanp*)
                      (proof-is-call symmetry *library-implies*)
                      (proof-is-call transitivity *library-implies*)))
            nil
          (proof-with-checked-results ((relation (proof-term-at typing 1)))
            (t3-book-equivalence-relation-form lib formula relation reflexivity symmetry
                                              transitivity)))))))
