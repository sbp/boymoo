(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *b2-equivalences-booleanp* (proof-sym "BOOLEANP" "ACL2"))

(defconst *b2-equivalences-equivalence-suffixes*
  '("EQUIV" "EQV" "EQUIV$INLINE" "EQV$INLINE"))

(defun b2-equivalences-equiv-call (lib call)
  (proof-with-checked-results
   ((function (b2-search-head call)))
   (let ((definitions (proof-proof-definitions (library-library-proof lib))))
     (and (assoc-equal (if (eq function :none) nil function) definitions)
          (equal (len call) 3)
          (proof-with-checked-results
           ((name (proof-term-at function 2)))
           (cond ((stringp name) (text-ends-with name *b2-equivalences-equivalence-suffixes*))
                 ((integerp name) '(:failure "failure" ""))
                 (t '(:failure "failure" ""))))))))

(defun b2-equivalences-opened-equivalence (lib call)
  (proof-with-checked-results
   ((equivalence (b2-equivalences-equiv-call lib call)))
   (if (not equivalence)
       (b2-tactics-unproved)
     (proof-with-checked-results
      ((equation (b2-tactics-tactics-normalize lib call nil (list call) nil 150 nil))
       (literal (and equation (proof-step-first equation)))
       (rhs (and equation (proof-term-at literal 2))))
      (if (and equation (proof-is-call rhs *proof-equal*))
          equation
        (b2-tactics-unproved))))))

(defun b2-equivalences-equality-of-fixed (lib step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first step)))
     (if (proof-is-call literal *proof-equal*)
         step
       (proof-with-checked-results
        ((equation (b2-equivalences-opened-equivalence lib literal))
         (step (proof-proof-rewrite proof step equation '(1))))
        (proof-proof-tidy proof step))))))

(defun b2-equivalences-equivalence-properties-parts (lib formula)
  (let ((unproved (b2-tactics-unproved)))
    (if (not (proof-is-call formula *proof-if*))
        unproved
      (proof-with-checked-results
       ((last (proof-term-at formula 3)))
       (let ((boolean (cadr formula))
             (tail (caddr formula)))
         (if (not (and (equal last *proof-false*)
                       (proof-is-call boolean *b2-equivalences-booleanp*)))
             unproved
           (proof-with-checked-results
            ((test (proof-term-at boolean 1))
             (equivalence (b2-equivalences-equiv-call lib test)))
            (if (not (and equivalence (proof-is-call tail *proof-if*)))
                unproved
              (proof-with-checked-results
               ((inner (proof-term-at tail 2)))
               (if (not (proof-is-call inner *proof-if*))
                   unproved
                 (proof-with-checked-results
                  ((parts (proof-list-of-length inner 4)))
                  (list test (cadr tail) (cadr parts) (caddr parts)))))))))))))

(defun b2-equivalences-equivalence-properties-chain (premise lib transitive)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((conjuncts (proof-proof-conjunct proof premise))
      (before (b2-equivalences-equality-of-fixed lib (car conjuncts)))
      (after (b2-equivalences-equality-of-fixed lib (cadr conjuncts)))
      (combined (proof-proof-chain proof before (list after)))
      (target (proof-term-at transitive 2))
      (equality (b2-equivalences-opened-equivalence lib target)))
     (proof-proof-transport proof combined equality))))

(defun b2-equivalences-equivalence-properties-prove (lib formula call reflexive symmetry transitive)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((equality (b2-equivalences-opened-equivalence lib call))
      (literal (proof-step-first equality))
      (test (proof-term-at literal 2))
      (goal (list *b2-equivalences-booleanp* test))
      (unfold (list *b2-equivalences-booleanp*))
      (yes (proof-proof-assume proof test t))
      (positive (b2-tactics-tactics-solve lib goal (list yes) unfold nil 0 nil))
      (no (proof-proof-assume proof test nil))
      (negative (b2-tactics-tactics-solve lib goal (list no) unfold nil 0 nil))
      (boolean-equality (proof-proof-cases proof test positive negative))
      (boolean-proof (library-library-transport-argument lib boolean-equality equality 1))
      (same (b2-tactics-tactics-solve lib reflexive nil (list reflexive) nil 0 nil))
      (sym-target (proof-term-at symmetry 2))
      (sym-rhs (b2-equivalences-opened-equivalence lib sym-target))
      (sym-condition (proof-term-at symmetry 1))
      (sym-premise (proof-proof-assume proof sym-condition t))
      (fixed (b2-equivalences-equality-of-fixed lib sym-premise))
      (reversed (proof-proof-symmetric proof fixed))
      (outcome (proof-proof-transport proof reversed sym-rhs))
      (symmetric (b2-tactics-tactics-implication lib sym-condition sym-target (cons outcome lib)))
      (trans-condition (proof-term-at transitive 1))
      (trans-target (proof-term-at transitive 2))
      (trans-premise (proof-proof-assume proof trans-condition t))
      (outcome (b2-equivalences-equivalence-properties-chain trans-premise lib transitive))
      (trans (b2-tactics-tactics-implication lib trans-condition trans-target (cons outcome lib))))
     (b2-tactics-tactics-solve lib formula (list boolean-proof same (car symmetric) (car trans))
                              nil nil 0 nil))))

(defun b2-equivalences-equivalence-properties (lib formula)
  (proof-with-checked-results
   ((parts (b2-equivalences-equivalence-properties-parts lib formula)))
   (let ((symmetry (caddr parts))
         (transitive (cadddr parts))
         (missing (b2-tactics-unproved)))
     (if (not (and (proof-is-call symmetry *library-implies*)
                   (proof-is-call transitive *library-implies*)))
         (b2-tactics-unproved)
       (proof-with-checked-results
        ((condition (proof-term-at transitive 1)))
        (if (not (proof-is-call condition *proof-if*))
            missing
          (proof-with-checked-results
           ((last (proof-term-at condition 3)))
           (if (equal last *proof-false*)
               (b2-equivalences-equivalence-properties-prove lib formula (car parts) (cadr parts)
                                                            symmetry transitive)
             missing))))))))

(mutual-recursion
 (defun b2-equivalences-any-call (lib term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (let ((equivalence (b2-equivalences-equiv-call lib term)))
     (if equivalence
         equivalence
       (and (consp term) (proof-compound term) (not (equal (car term) *proof-quote*))
            (b2-equivalences-any-call-arguments lib (cdr term))))))
 (defun b2-equivalences-any-call-arguments (lib terms)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (if (endp terms)
       nil
     (let ((equivalence (b2-equivalences-any-call lib (car terms))))
       (if equivalence
           equivalence
         (b2-equivalences-any-call-arguments lib (cdr terms)))))))

(defun b2-equivalences-congruence-equations (lib known)
  (declare (xargs :measure (acl2-count known)))
  (if (endp known)
      nil
    (let ((literal (caar known))
          (entry (cdar known)))
      (proof-with-checked-results
       ((equivalence (b2-equivalences-equiv-call lib literal)))
       (if (or equivalence (proof-is-call literal *proof-equal*))
           (proof-with-checked-results
            ((equation (b2-equivalences-equality-of-fixed lib entry))
             (others (b2-equivalences-congruence-equations lib (cdr known))))
            (cons equation others))
         (b2-equivalences-congruence-equations lib (cdr known)))))))

(defun b2-equivalences-congruence-establish (premise lib target)
  (proof-with-checked-results
   ((known (b2-tactics-tactics-evidence lib (list premise)))
    (equations (b2-equivalences-congruence-equations lib known))
    (equivalence (b2-equivalences-equiv-call lib target))
    (target-eq (and equivalence (b2-equivalences-opened-equivalence lib target)))
    (literal (and target-eq (proof-step-first target-eq)))
    (goal (if target-eq (proof-term-at literal 2) target))
    (evidence (append (table-values known) equations))
    (solver (b2-search-search-init lib 12 nil))
    (result (b2-search-search-prove solver goal evidence 2 1))
    (step (car result)))
   (if target-eq
       (proof-proof-transport (library-library-proof lib) step target-eq)
     step)))

(defun b2-equivalences-congruence (lib formula)
  (proof-with-checked-results
   ((parts (if (integerp formula)
               '(:failure "tactic-rejected" "")
             (proof-list-of-length (cdr formula) 2)))
    (condition (car parts))
    (target (cadr parts))
    (equivalence (b2-equivalences-equiv-call lib target))
    (found (or equivalence (b2-equivalences-any-call lib condition))))
   (if (not found)
       (b2-tactics-unproved)
     (proof-with-checked-results
      ((size (b2-search-size formula 110)))
      (if (>= size 110)
          (b2-tactics-unproved)
        (proof-with-checked-results
         ((premise (proof-proof-assume (library-library-proof lib) condition t))
          (step (b2-equivalences-congruence-establish premise lib target))
          (result (b2-tactics-tactics-implication lib condition target (cons step lib))))
         (car result)))))))

(defun b2-equivalences-prove-equivalence (lib formula)
  (if (proof-is-call formula *library-implies*)
      (b2-equivalences-congruence lib formula)
    (proof-with-checked-results
     ((equivalence (b2-equivalences-equiv-call lib formula)))
     (if (not equivalence)
         (b2-equivalences-equivalence-properties lib formula)
       (proof-with-checked-results
        ((equation (b2-equivalences-opened-equivalence lib formula))
         (solver (b2-search-search-init lib 12 nil))
         (first (proof-step-first equation))
         (goal (proof-term-at first 2))
         (result (b2-search-search-prove solver goal nil 2 1))
         (step (car result)))
        (proof-proof-transport (library-library-proof lib) step equation))))))
