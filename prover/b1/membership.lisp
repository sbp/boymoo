(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-membership-true-listp* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *b1-membership-item* (proof-sym "A" "ACL2"))
(defconst *b1-membership-union* (proof-sym "UNION-EQUAL" "ACL2"))
(defconst *b1-membership-difference* (proof-sym "SET-DIFFERENCE-EQUAL" "ACL2"))
(defconst *b1-membership-remove* (proof-sym "REMOVE-EQUAL" "ACL2"))
(defconst *b1-membership-remove1* (proof-sym "REMOVE1-EQUAL" "ACL2"))
(defconst *b1-membership-deduplicate* (proof-sym "REMOVE-DUPLICATES-EQUAL" "ACL2"))
(defconst *b1-membership-cons-hint* (proof-sym "CONS-WITH-HINT" "ACL2"))

(defun b1-membership-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b1-membership-membership-case-conses (evidence conses)
  (if (endp evidence)
      conses
    (proof-with-checked-results ((literal (proof-step-first (car evidence))))
      (if (proof-is-call literal *proof-consp*)
          (proof-with-checked-results ((value (proof-term-at literal 1)))
            (b1-membership-membership-case-conses
             (cdr evidence) (table-put conses value (car evidence))))
        (b1-membership-membership-case-conses (cdr evidence) conses)))))

(defun b1-membership-membership-case-evidence (lib equations conses)
  (if (endp equations)
      nil
    (proof-with-checked-results
        ((value (b1-membership-step-at (car equations) 2))
         (cons-proof (if (proof-is-call value *proof-cons*)
                         (b1-revappend-cons-value lib value)
                       (cdr (assoc-equal value conses))))
         (nonempty (if cons-proof
                       (b1-revappend-cons-is-nonempty lib cons-proof)
                     nil))
         (rest (b1-membership-membership-case-evidence lib (cdr equations) conses)))
      (if nonempty (cons nonempty rest) rest))))

(defun b1-membership-membership-case-rules (equations)
  (if (endp equations)
      nil
    (cons (b1-logic-equal-to (car equations))
          (b1-membership-membership-case-rules (cdr equations)))))

(defun b1-membership-membership-case (lib formula equations evidence induction)
  (proof-with-checked-results
      ((conses (b1-membership-membership-case-conses evidence nil))
       (derived (b1-membership-membership-case-evidence lib equations conses)))
    (let ((known (append evidence derived))
          (rules (b1-membership-membership-case-rules equations))
          (unfold (list *b1-revappend-iff* *proof-not*)))
      (if (not induction)
          (b1-logic-bookproof-case-proof lib formula known unfold rules 16)
        (proof-with-checked-results
            ((hypothesis (proof-step-first induction))
             (implication
              (b1-logic-bookproof-case-proof
               lib (list *library-implies* hypothesis formula)
               known (cons *library-implies* unfold) rules 16)))
          (proof-proof-modus-ponens (library-library-proof lib) implication induction))))))

(defun b1-membership-member-nil (lib formula)
  (proof-with-checked-results
      ((call (proof-term-at formula 1))
       (empty (b1-revappend-open-list lib call nil)))
    (b1-logic-bookproof-normalize-proof
     lib formula nil (list *proof-not*) (list (b1-logic-equal-to empty)) nil)))

(defun b1-membership-impossible-member (lib assertion empty goal)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((falsehood (proof-proof-rewrite proof assertion empty '(1)))
         (not-nil (b1-logic-proof-not-nil proof)))
      (b1-logic-bookproof-contradiction lib falsehood not-nil goal))))

(defun b1-membership-member-requires-cons (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
      (let ((call (cadr parts))
            (test (caddr parts)))
        (proof-with-checked-results
            ((atom (proof-proof-assume proof test nil))
             (have (b1-logic-bookproof-prove-implication-premise lib formula))
             (yes (proof-proof-assume proof test t))
             (empty (b1-revappend-open-list lib call (list atom)))
             (no (b1-membership-impossible-member lib have empty test))
             (consequence (proof-proof-cases proof test yes no)))
          (b1-logic-bookproof-prove-implication-with-premise lib formula have consequence))))))

(defun b1-membership-member-from-tail (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (call-parts (proof-list-of-length (caddr parts) 3)))
      (let* ((child (cadr parts))
             (call (caddr parts))
             (xs (caddr call-parts))
             (test (list *proof-consp* xs))
             (hits (proof-eq (cadr call-parts) (list *library-car* xs))))
        (proof-with-checked-results
            ((cons-step (proof-proof-assume proof test t))
             (atom (proof-proof-assume proof test nil))
             (have (b1-logic-bookproof-prove-implication-premise lib formula))
             (hit (proof-proof-assume proof hits t))
             (head (b1-revappend-open-list lib call (list cons-step hit)))
             (nonempty (b1-revappend-cons-is-nonempty lib cons-step))
             (yes (proof-proof-transport proof nonempty head))
             (miss (proof-proof-assume proof hits nil))
             (tail (b1-revappend-open-list lib call (list cons-step miss)))
             (no (proof-proof-transport proof have tail))
             (step (proof-proof-cases proof hits yes no))
             (selector (b1-structures-noncons-selector lib *library-cdr* atom))
             (lifted (b1-revappend-lift-argument lib child selector 2))
             (empty-call (b1-membership-step-at lifted 2))
             (opened (b1-revappend-open-list lib empty-call nil))
             (empty (proof-proof-chain proof lifted (list opened)))
             (impossible (b1-membership-impossible-member lib have empty call))
             (consequence (proof-proof-cases proof test step impossible)))
          (b1-logic-bookproof-prove-implication-with-premise lib formula have consequence))))))

(defun b1-membership-member-of-suffix-base (lib formula source inner claim atom)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((inner-empty (b1-revappend-open-list lib inner (list atom)))
         (lifted (b1-revappend-lift-argument lib source inner-empty 2))
         (empty-call (b1-membership-step-at lifted 2))
         (opened (b1-revappend-open-list lib empty-call nil))
         (empty (proof-proof-chain proof lifted (list opened)))
         (have (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-membership-impossible-member lib have empty claim)))
      (b1-logic-bookproof-prove-implication-with-premise lib formula have consequence))))

(defun b1-membership-member-of-suffix-step (lib formula source inner claim hit cons-step induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((have (b1-logic-bookproof-prove-implication-premise lib formula))
         (hits (proof-proof-assume proof hit t))
         (same-inner (b1-revappend-open-list lib inner (list cons-step hits)))
         (same (b1-revappend-lift-argument lib source same-inner 2))
         (yes (proof-proof-rewrite proof have same '(1)))
         (miss (proof-proof-assume proof hit nil))
         (less-inner (b1-revappend-open-list lib inner (list cons-step miss)))
         (less (b1-revappend-lift-argument lib source less-inner 2))
         (rest (proof-proof-rewrite proof have less '(1)))
         (child (proof-proof-modus-ponens proof induction rest))
         (child-literal (proof-step-first child))
         (forward (b1-logic-bookproof-from-fact
                   lib (proof-sym "MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP" "ACL2")
                   (list *library-implies* child-literal claim)))
         (no (proof-proof-modus-ponens proof forward child))
         (consequence (proof-proof-cases proof hit yes no)))
      (b1-logic-bookproof-prove-implication-with-premise lib formula have consequence))))

(defun b1-membership-member-of-suffix (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (source-parts (proof-list-of-length (cadr parts) 3))
       (inner-parts (proof-list-of-length (caddr source-parts) 3)))
    (let* ((source (cadr parts))
           (claim (caddr parts))
           (inner (caddr source-parts))
           (xs (caddr inner-parts))
           (hit (proof-eq (cadr inner-parts) (list *library-car* xs))))
      (proof-with-checked-results
          ((preparation (b1-revappend-list-induction-prepare lib formula xs nil))
           (here (b1-membership-member-of-suffix-step
                  lib formula source inner claim hit (caddr preparation) (cadddr preparation)))
           (atom (proof-proof-assume (library-library-proof lib) (cadr preparation) nil))
           (there (b1-membership-member-of-suffix-base lib formula source inner claim atom)))
        (b1-revappend-list-induction lib preparation there here)))))

(defun b1-membership-member-contrapositive (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (positive-goal (proof-term-at (caddr parts) 1))
         (suffix (proof-term-at positive-goal 2))
         (suffix-head (proof-term-at suffix 0))
         (positive-missing (proof-term-at (cadr parts) 1)))
      (let* ((goal (caddr parts))
             (name (if (equal suffix-head *b1-revappend-member*)
                       "MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-MEMBER-EQUAL"
                     "MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP")))
        (proof-with-checked-results
            ((forward (b1-logic-bookproof-from-fact
                       lib (proof-sym name "ACL2")
                       (list *library-implies* positive-goal positive-missing)))
             (premise (b1-logic-bookproof-prove-implication-premise lib formula))
             (assumed (proof-proof-assume proof positive-goal t))
             (positive (proof-proof-modus-ponens proof forward assumed))
             (cut (proof-proof-cut proof positive premise))
             (consequence (proof-proof-front proof cut goal)))
          (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))))))

(defun b1-membership-member-proper-base (lib formula call atom)
  (proof-with-checked-results
      ((empty (b1-logic-bookproof-normalize-proof
               lib (list *b1-membership-true-listp* *proof-false*) nil
               (list *b1-membership-true-listp* *b1-logic-eq*) nil nil))
       (opened (b1-revappend-open-list lib call (list atom)))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (library-library-transport-argument lib empty opened 1)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-membership-member-proper-step (lib formula call hit cons-step induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((proper (b1-logic-bookproof-prove-implication-premise lib formula))
         (hits (proof-proof-assume proof hit t))
         (head (b1-revappend-open-list lib call (list cons-step hits)))
         (yes (library-library-transport-argument lib proper head 1))
         (proper-tail (b1-structures-true-list-tail lib proper cons-step))
         (tail (proof-proof-modus-ponens proof induction proper-tail))
         (miss (proof-proof-assume proof hit nil))
         (opened (b1-revappend-open-list lib call (list cons-step miss)))
         (no (library-library-transport-argument lib tail opened 1))
         (consequence (proof-proof-cases proof hit yes no)))
      (b1-logic-bookproof-prove-implication-with-premise lib formula proper consequence))))

(defun b1-membership-member-proper (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr parts) 2))
       (call-parts (proof-list-of-length (cadr claim) 3)))
    (let* ((call (cadr claim))
           (xs (caddr call-parts))
           (hit (proof-eq (cadr call-parts) (list *library-car* xs))))
      (proof-with-checked-results
          ((preparation (b1-revappend-list-induction-prepare lib formula xs nil))
           (here (b1-membership-member-proper-step
                  lib formula call hit (caddr preparation) (cadddr preparation)))
           (atom (proof-proof-assume (library-library-proof lib) (cadr preparation) nil))
           (there (b1-membership-member-proper-base lib formula call atom)))
        (b1-revappend-list-induction lib preparation there here)))))

(defun b1-membership-list-fix-lemmas-type-base (lib fixed atom)
  (proof-with-checked-results
      ((empty (b1-logic-bookproof-normalize-proof
               lib (list *b1-membership-true-listp* *proof-false*) nil
               (list *b1-membership-true-listp* *b1-logic-eq*) nil nil))
       (opened (b1-revappend-open-list lib fixed (list atom))))
    (library-library-transport-argument lib empty opened 1)))

(defun b1-membership-list-fix-lemmas-type-step (lib fixed cons-step induction)
  (proof-with-checked-results
      ((exposed (b1-revappend-open-list lib fixed (list cons-step)))
       (value (b1-membership-step-at exposed 2))
       (opened (b1-revappend-open-list lib (list *b1-membership-true-listp* value) nil))
       (proper-pair (proof-proof-transport (library-library-proof lib) induction opened)))
    (library-library-transport-argument lib proper-pair exposed 1)))

(defun b1-membership-list-fix-lemmas-identity-base (lib identity fixed proper atom)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((have (b1-logic-bookproof-prove-implication-premise lib identity))
         (reduced (b1-logic-bookproof-normalize
                   lib proper (list atom) (list *b1-membership-true-listp* *b1-logic-eq*)
                   nil nil nil nil))
         (empty (proof-proof-rewrite proof have reduced '(1)))
         (opened (b1-revappend-open-list lib fixed (list atom)))
         (reversed (proof-proof-symmetric proof empty))
         (consequence (proof-proof-chain proof opened (list reversed))))
      (b1-logic-bookproof-prove-implication-with-premise lib identity have consequence))))

(defun b1-membership-list-fix-lemmas-identity-step (lib identity fixed cons-step induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((have (b1-logic-bookproof-prove-implication-premise lib identity))
         (proper-tail (b1-structures-true-list-tail lib have cons-step))
         (child (proof-proof-modus-ponens proof induction proper-tail))
         (opened (b1-revappend-open-list lib fixed (list cons-step)))
         (unfolded (proof-proof-rewrite proof opened child '(1 2 2)))
         (cons-literal (proof-step-first cons-step))
         (unfolded-value (b1-membership-step-at unfolded 2))
         (reconstructed (b1-logic-bookproof-from-fact
                         lib (proof-sym "CAR-CDR-ELIM" "ACL2")
                         (list *library-implies* cons-literal
                               (proof-eq unfolded-value *library-x*))))
         (reconstructed-value (proof-proof-modus-ponens proof reconstructed cons-step))
         (consequence (proof-proof-chain proof unfolded (list reconstructed-value))))
      (b1-logic-bookproof-prove-implication-with-premise lib identity have consequence))))

(defun b1-membership-list-fix-lemmas (lib)
  (let* ((fixed (list *b1-revappend-fix* *library-x*))
         (proper (list *b1-membership-true-listp* *library-x*))
         (result-type (list *b1-membership-true-listp* fixed))
         (identity (list *library-implies* proper (proof-eq fixed *library-x*)))
         (proof (library-library-proof lib)))
    (if (assoc-equal (proof-sym "SELF-TRUE-LIST-FIX-PROPER" "ACL2")
                     (proof-proof-facts proof))
        lib
      (proof-with-checked-results
          ((type-prep (b1-revappend-list-induction-prepare lib result-type *library-x* nil))
           (type-here (b1-membership-list-fix-lemmas-type-step
                       lib fixed (caddr type-prep) (cadddr type-prep)))
           (type-atom (proof-proof-assume proof (cadr type-prep) nil))
           (type-there (b1-membership-list-fix-lemmas-type-base lib fixed type-atom))
           (type-proof (b1-revappend-list-induction lib type-prep type-there type-here))
           (with-proper (library-library-lemma lib "TRUE-LIST-FIX-PROPER" result-type type-proof nil))
           (identity-prep (b1-revappend-list-induction-prepare with-proper identity *library-x* nil))
           (identity-here (b1-membership-list-fix-lemmas-identity-step
                           with-proper identity fixed (caddr identity-prep) (cadddr identity-prep)))
           (identity-atom (proof-proof-assume (library-library-proof with-proper)
                                            (cadr identity-prep) nil))
           (identity-there (b1-membership-list-fix-lemmas-identity-base
                            with-proper identity fixed proper identity-atom))
           (identity-proof (b1-revappend-list-induction with-proper identity-prep
                                                      identity-there identity-here)))
        (library-library-lemma with-proper "TRUE-LIST-FIX-IDENTITY" identity identity-proof nil)))))

(defun b1-membership-member-of-fixed-list-proper (lib name)
  (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
      lib
    (let ((property-of-member
           (list *library-implies* (list *b1-membership-true-listp* *library-x*)
                 (list *b1-membership-true-listp*
                       (list *b1-revappend-member* *b1-membership-item* *library-x*)))))
      (proof-with-checked-results ((step (b1-membership-member-proper lib property-of-member)))
        (library-library-lemma lib "MEMBER-PROPER" property-of-member step nil)))))

(defun b1-membership-member-of-fixed-list (lib formula)
  (proof-with-checked-results ((with-fix (b1-membership-list-fix-lemmas lib)))
    (let ((name (proof-sym "SELF-MEMBER-PROPER" "ACL2")))
      (proof-with-checked-results
          ((with-proper (b1-membership-member-of-fixed-list-proper with-fix name))
           (sides (if (integerp formula)
                      '(:failure "failure" "")
                    (proof-list-of-length (cdr formula) 2)))
           (call-parts (proof-list-of-length (car sides) 3))
           (underlying-list (proof-term-at (caddr call-parts) 1)))
        (let ((proof (library-library-proof with-proper))
              (call (car sides))
              (item (cadr call-parts))
              (fixed (caddr call-parts)))
          (proof-with-checked-results
              ((proper (proof-proof-fact proof (proof-sym "SELF-TRUE-LIST-FIX-PROPER" "ACL2")
                                         (list (list *library-x* underlying-list))))
               (member-type (proof-proof-fact proof name (list (list *library-x* fixed)
                                                             (list *b1-membership-item* item))))
               (identity (proof-proof-fact proof (proof-sym "SELF-TRUE-LIST-FIX-IDENTITY" "ACL2")
                                           (list (list *library-x* call))))
               (proper-member (proof-proof-modus-ponens proof member-type proper))
               (fixed-member (proof-proof-modus-ponens proof identity proper-member))
               (step (proof-proof-symmetric proof fixed-member)))
            (cons step with-proper)))))))

(defun b1-membership-membership-head-step (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (claim (proof-list-of-length (caddr parts) 3))
         (xs (proof-term-at (cadr claim) 2)))
      (let ((test (list *proof-consp* xs))
            (call (cadr claim))
            (tail (caddr claim)))
        (proof-with-checked-results
            ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
             (conjuncts (proof-proof-conjunct proof premise))
             (cons-step (proof-proof-assume proof test t))
             (atom (proof-proof-assume proof test nil))
             (selector (b1-structures-noncons-selector lib *library-cdr* atom))
             (lifted (b1-revappend-lift-argument lib tail selector 2))
             (empty-call (b1-membership-step-at lifted 2))
             (empty-tail (b1-revappend-open-list lib empty-call nil))
             (no (proof-proof-chain proof lifted (list empty-tail)))
             (yes (b1-revappend-open-list lib call (list cons-step (cadr conjuncts))))
             (empty-call (b1-revappend-open-list lib call (list atom)))
             (reversed (proof-proof-symmetric proof no))
             (atom-case (proof-proof-chain proof empty-call (list reversed)))
             (consequence (proof-proof-cases proof test yes atom-case)))
          (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))))))

(defun b1-membership-singleton-member (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (test (proof-term-at (caddr parts) 1)))
      (let ((call (cadr parts))
            (result (caddr parts)))
        (proof-with-checked-results
            ((hit (proof-proof-assume proof test t))
             (miss (proof-proof-assume proof test nil))
             (head (b1-revappend-open-list lib call (list hit)))
             (reversed-hit (proof-proof-symmetric proof hit))
             (replaced (proof-proof-rewrite proof head reversed-hit '(1 2 1)))
             (selected (proof-proof-select proof result hit))
             (reversed-selected (proof-proof-symmetric proof selected))
             (yes (proof-proof-chain proof replaced (list reversed-selected)))
             (tail (b1-revappend-open-list lib call (list miss)))
             (tail-call (b1-membership-step-at tail 2))
             (empty (b1-revappend-open-list lib tail-call nil))
             (selected (proof-proof-select proof result miss))
             (reversed-selected (proof-proof-symmetric proof selected))
             (no (proof-proof-chain proof tail (list empty reversed-selected))))
          (proof-proof-cases proof test yes no))))))

(defun b1-membership-member-of-fixed-list-iff-branch (cell limits induction lib formula left fixed right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reduced (b1-revappend-open-list lib fixed (list cell)))
         (lifted (b1-revappend-lift-argument lib left reduced 2))
         (lifted-call (b1-membership-step-at lifted 2))
         (unfolded (b1-revappend-open-list lib lifted-call limits))
         (opened (proof-proof-chain proof lifted (list unfolded)))
         (source (b1-revappend-open-list lib right (cons cell limits))))
      (b1-membership-membership-case lib formula (list opened source) (cons cell limits) induction))))

(defun b1-membership-member-of-fixed-list-iff-step (cons-step induction lib formula left fixed right hit)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((hits (proof-proof-assume proof hit t))
         (yes (b1-membership-member-of-fixed-list-iff-branch
               cons-step (list hits) nil lib formula left fixed right))
         (miss (proof-proof-assume proof hit nil))
         (no (b1-membership-member-of-fixed-list-iff-branch
              cons-step (list miss) induction lib formula left fixed right)))
      (proof-proof-cases proof hit yes no))))

(defun b1-membership-member-of-fixed-list-iff (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (left-parts (proof-list-of-length (cadr parts) 3))
       (xs (proof-term-at (caddr left-parts) 1)))
    (let* ((left (cadr parts))
           (right (caddr parts))
           (fixed (caddr left-parts))
           (hit (proof-eq (cadr left-parts) (list *library-car* xs))))
      (proof-with-checked-results
          ((preparation (b1-revappend-list-induction-prepare lib formula xs nil))
           (here (b1-membership-member-of-fixed-list-iff-step
                  (caddr preparation) (cadddr preparation) lib formula left fixed right hit))
           (atom (proof-proof-assume (library-library-proof lib) (cadr preparation) nil))
           (there (b1-membership-member-of-fixed-list-iff-branch
                   atom nil nil lib formula left fixed right)))
        (b1-revappend-list-induction lib preparation there here)))))

(defun b1-membership-member-of-set-operation-opened (cell evidence lib left operation name)
  (proof-with-checked-results
      ((reduced (b1-logic-bookproof-normalize
                 lib operation (cons cell evidence)
                 (list name *b1-logic-atom* *b1-logic-endp* *proof-not* *b1-membership-cons-hint*)
                 nil nil nil nil))
       (lifted (b1-revappend-lift-argument lib left reduced 2))
       (value (b1-membership-step-at reduced 2))
       (head (proof-term-at value 0)))
    (if (or (equal head name)
            (equal head *library-cdr*)
            (and (equal name *b1-membership-union*) (equal value (caddr operation))))
        lifted
      (proof-with-checked-results
          ((call (b1-membership-step-at lifted 2))
           (opened (b1-revappend-open-list lib call evidence)))
        (proof-proof-chain (library-library-proof lib) lifted (list opened))))))

(defun b1-membership-member-of-set-operation-prove-base-branch (premises lib claim left operation name source atom)
  (proof-with-checked-results
      ((adjusted (b1-membership-member-of-set-operation-opened atom nil lib left operation name))
       (plain (b1-revappend-open-list lib source (list atom))))
    (b1-membership-membership-case lib claim (list adjusted plain) (cons atom premises) nil)))

(defun b1-membership-member-of-set-operation-prove-base (atom lib formula guarded claim left operation name source)
  (if guarded
      (proof-with-checked-results
          ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
           (consequence (b1-membership-member-of-set-operation-prove-base-branch
                         (list premise) lib claim left operation name source atom)))
        (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))
    (b1-membership-member-of-set-operation-prove-base-branch
     nil lib claim left operation name source atom)))

(defun b1-membership-member-of-set-operation-prove-step-branch
    (hits discards more child lib claim left operation name source cons-step)
  (proof-with-checked-results
      ((adjusted (b1-membership-member-of-set-operation-opened
                  cons-step (list hits discards) lib left operation name))
       (plain (b1-revappend-open-list lib source (list cons-step hits))))
    (b1-membership-membership-case lib claim (list adjusted plain)
                                   (list* cons-step hits discards more) child)))

(defun b1-membership-member-of-set-operation-prove-step-handle-distinct
    (missing lib claim left operation name source cons-step hit discard have-head miss-head dropped kept child)
  (let ((proof (library-library-proof lib))
        (more (list missing)))
    (proof-with-checked-results
        ((reversed (proof-proof-symmetric proof dropped))
         (same-value (proof-proof-chain proof have-head (list reversed)))
         (contradiction (b1-logic-bookproof-contradiction lib same-value missing claim))
         (hit-kept (b1-membership-member-of-set-operation-prove-step-branch
                    have-head kept more child lib claim left operation name source cons-step))
         (yes (proof-proof-cases proof discard contradiction hit-kept))
         (miss-dropped (b1-membership-member-of-set-operation-prove-step-branch
                        miss-head dropped more child lib claim left operation name source cons-step))
         (miss-kept (b1-membership-member-of-set-operation-prove-step-branch
                     miss-head kept more child lib claim left operation name source cons-step))
         (no (proof-proof-cases proof discard miss-dropped miss-kept)))
      (proof-proof-cases proof hit yes no))))

(defun b1-membership-member-of-set-operation-prove-step-handle-removal
    (equated premise guarded lib claim left operation name source cons-step hit discard have-head miss-head dropped kept child)
  (if guarded
      (b1-membership-member-of-set-operation-prove-step-handle-distinct
       premise lib claim left operation name source cons-step hit discard have-head miss-head dropped kept child)
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((same (proof-proof-assume proof equated t))
           (drop (proof-proof-rewrite proof have-head same '(1 1)))
           (keep (proof-proof-rewrite proof miss-head same '(1 1 1)))
           (same-hit (b1-membership-member-of-set-operation-prove-step-branch
                      have-head drop (list same) child lib claim left operation name source cons-step))
           (same-miss (b1-membership-member-of-set-operation-prove-step-branch
                       miss-head keep (list same) child lib claim left operation name source cons-step))
           (identical (proof-proof-cases proof hit same-hit same-miss))
           (different (proof-proof-assume proof equated nil))
           (distinct (b1-membership-member-of-set-operation-prove-step-handle-distinct
                      different lib claim left operation name source cons-step hit discard
                      have-head miss-head dropped kept child)))
        (proof-proof-cases proof equated identical distinct)))))

(defun b1-membership-member-of-set-operation-prove-step-handle-same-head
    (discards lib claim left operation name source cons-step discard have-head direct child)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first discards))
         (reversed (proof-proof-symmetric proof have-head))
         (item-membership (proof-proof-rewrite proof discards reversed
                                               (if (equal literal discard) '(1 1) '(1 1 1)))))
      (b1-membership-member-of-set-operation-prove-step-branch
       have-head discards (append direct (list item-membership)) child
       lib claim left operation name source cons-step))))

(defun b1-membership-member-of-set-operation-prove-step-handle
    (premise lib guarded claim left operation name source cons-step hit discard item removed induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((child (if guarded (proof-proof-modus-ponens proof induction premise) induction))
         (have-head (proof-proof-assume proof hit t))
         (miss-head (proof-proof-assume proof hit nil))
         (dropped (proof-proof-assume proof discard t))
         (kept (proof-proof-assume proof discard nil)))
      (if (member-equal name (list *b1-membership-remove* *b1-membership-remove1*))
          (b1-membership-member-of-set-operation-prove-step-handle-removal
           (proof-eq item removed) premise guarded lib claim left operation name
           source cons-step hit discard have-head miss-head dropped kept child)
        (let ((direct (if premise (list premise) nil)))
          (proof-with-checked-results
              ((hit-dropped (b1-membership-member-of-set-operation-prove-step-handle-same-head
                             dropped lib claim left operation name source cons-step discard
                             have-head direct child))
               (hit-kept (b1-membership-member-of-set-operation-prove-step-handle-same-head
                          kept lib claim left operation name source cons-step discard
                          have-head direct child))
               (yes (proof-proof-cases proof discard hit-dropped hit-kept))
               (miss-dropped (b1-membership-member-of-set-operation-prove-step-branch
                              miss-head dropped direct child lib claim left operation name source cons-step))
               (miss-kept (b1-membership-member-of-set-operation-prove-step-branch
                           miss-head kept direct child lib claim left operation name source cons-step))
               (no (proof-proof-cases proof discard miss-dropped miss-kept)))
            (proof-proof-cases proof hit yes no)))))))

(defun b1-membership-member-of-set-operation-prove-step
    (cons-step induction lib formula guarded claim left operation name source hit discard item removed)
  (if guarded
      (proof-with-checked-results
          ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
           (consequence (b1-membership-member-of-set-operation-prove-step-handle
                         premise lib guarded claim left operation name source cons-step hit discard item removed induction)))
        (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))
    (b1-membership-member-of-set-operation-prove-step-handle
     nil lib guarded claim left operation name source cons-step hit discard item removed induction)))

(defun b1-membership-member-of-set-operation (lib formula)
  (let ((guarded (proof-is-call formula *library-implies*)))
    (proof-with-checked-results
        ((claim (if guarded (proof-term-at formula 2) formula))
         (parts (proof-list-of-length claim 3))
         (left-parts (proof-list-of-length (cadr parts) 3))
         (name (proof-term-at (caddr left-parts) 0)))
      (let* ((left (cadr parts))
             (item (cadr left-parts))
             (operation (caddr left-parts))
             (removal (member-equal name (list *b1-membership-remove* *b1-membership-remove1*))))
        (proof-with-checked-results
            ((xs (proof-term-at operation (if removal 2 1)))
             (removed (if removal (proof-term-at operation 1) nil))
             (other (cond (removal nil)
                          ((equal name *b1-membership-deduplicate*) (list *library-cdr* xs))
                          (t (proof-term-at operation 2)))))
          (let* ((head (list *library-car* xs))
                 (source (list *b1-revappend-member* item xs))
                 (hit (proof-eq item head))
                 (discard (if removal (proof-eq removed head) (list *b1-revappend-member* head other))))
            (proof-with-checked-results
                ((preparation (b1-revappend-list-induction-prepare lib formula xs nil))
                 (here (b1-membership-member-of-set-operation-prove-step
                        (caddr preparation) (cadddr preparation) lib formula guarded
                        claim left operation name source hit discard item removed))
                 (atom (proof-proof-assume (library-library-proof lib) (cadr preparation) nil))
                 (there (b1-membership-member-of-set-operation-prove-base
                         atom lib formula guarded claim left operation name source)))
              (b1-revappend-list-induction lib preparation there here))))))))

(defun b1-membership-member-of-singleton-length (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (claim-parts (proof-list-of-length (caddr parts) 3))
         (xs (proof-term-at (cadr claim-parts) 2)))
      (let* ((claim (caddr parts))
             (call (cadr claim-parts))
             (hit (caddr claim-parts))
             (length (list *library-len* xs))
             (tail (list *library-cdr* xs))
             (test (list *proof-consp* xs))
             (tail-test (list *proof-consp* tail)))
        (proof-with-checked-results
            ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
             (conjuncts (proof-proof-conjunct proof premise))
             (comparison-literal (proof-step-first (cadr conjuncts)))
             (reduced (b1-logic-bookproof-normalize
                       lib comparison-literal nil (list (proof-cl "=")) nil nil nil nil))
             (size (proof-proof-rewrite proof (cadr conjuncts) reduced '(1)))
             (cons-step (proof-proof-assume proof test t))
             (atom (proof-proof-assume proof test nil))
             (tail-cons (proof-proof-assume proof tail-test t))
             (tail-atom (proof-proof-assume proof tail-test nil))
             (empty-length (b1-revappend-open-list lib length (list atom)))
             (missing (proof-proof-rewrite proof size empty-length '(1 2)))
             (missing-literal (proof-step-first missing))
             (constant (b1-logic-bookproof-constant lib missing-literal))
             (missing (b1-membership-impossible-member lib missing constant claim))
             (expanded (b1-revappend-open-list lib length (list cons-step)))
             (expanded-value (b1-membership-step-at expanded 2))
             (positive-tail (b1-revappend-positive-length lib tail-cons))
             (too-long (library-library-less-from-difference
                        lib *proof-one* expanded-value positive-tail nil))
             (reversed-expanded (proof-proof-symmetric proof expanded))
             (too-long (proof-proof-rewrite proof too-long reversed-expanded '(1 2)))
             (reversed-size (proof-proof-symmetric proof size))
             (too-long (proof-proof-rewrite proof too-long reversed-size '(1 2)))
             (too-long-literal (proof-step-first too-long))
             (opposite (b1-logic-bookproof-normalize-proof
                        lib (proof-neg too-long-literal) nil (list *proof-not*) nil nil))
             (impossible (b1-logic-bookproof-contradiction lib too-long opposite claim))
             (have (proof-proof-assume proof hit t))
             (miss (proof-proof-assume proof hit nil))
             (head (b1-revappend-open-list lib call (list cons-step have)))
             (yes (b1-membership-membership-case lib claim (list head) (list cons-step have) nil))
             (no (b1-revappend-open-list lib call (list cons-step miss)))
             (tail-call (b1-membership-step-at no 2))
             (opened-tail (b1-revappend-open-list lib tail-call (list tail-atom)))
             (no (proof-proof-chain proof no (list opened-tail)))
             (no (b1-membership-membership-case lib claim (list no) (list miss) nil))
             (singleton (proof-proof-cases proof hit yes no))
             (cons-case (proof-proof-cases proof tail-test impossible singleton))
             (consequence (proof-proof-cases proof test cons-case missing)))
          (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))))))

(defun b1-membership-member-after-removal-base (atom lib formula left right operation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((operation-empty (b1-revappend-open-list lib operation (list atom)))
         (lifted (b1-revappend-lift-argument lib left operation-empty 2))
         (empty-call (b1-membership-step-at lifted 2))
         (opened (b1-revappend-open-list lib empty-call nil))
         (empty (proof-proof-chain proof lifted (list opened)))
         (have (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-membership-impossible-member lib have empty right)))
      (b1-logic-bookproof-prove-implication-with-premise lib formula have consequence))))

(defun b1-membership-member-after-removal-step (cons-step induction lib formula left right operation hit discard)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((have (b1-logic-bookproof-prove-implication-premise lib formula))
         (hits (proof-proof-assume proof hit t))
         (present (b1-revappend-open-list lib right (list cons-step hits)))
         (nonempty (b1-revappend-cons-is-nonempty lib cons-step))
         (yes (proof-proof-transport proof nonempty present))
         (miss (proof-proof-assume proof hit nil))
         (source (b1-revappend-open-list lib right (list cons-step miss)))
         (dropped (proof-proof-assume proof discard t))
         (kept (proof-proof-assume proof discard nil))
         (opened (b1-revappend-open-list lib operation (list cons-step dropped)))
         (skip (b1-revappend-lift-argument lib left opened 2))
         (skip-proof (proof-proof-rewrite proof have skip '(1)))
         (no (proof-proof-transport proof skip-proof source))
         (keep (b1-logic-bookproof-normalize
                lib operation (list cons-step kept)
                (list *b1-membership-remove1* *b1-membership-cons-hint*
                      *b1-logic-atom* *b1-logic-endp* *proof-not*)
                nil nil nil nil))
         (keep (b1-revappend-lift-argument lib left keep 2))
         (kept-call (b1-membership-step-at keep 2))
         (opened (b1-revappend-open-list lib kept-call (list miss)))
         (keep (proof-proof-chain proof keep (list opened)))
         (membership (proof-proof-rewrite proof have keep '(1)))
         (recursive (proof-proof-modus-ponens proof induction membership))
         (rest (proof-proof-transport proof recursive source))
         (miss-case (proof-proof-cases proof discard no rest))
         (consequence (proof-proof-cases proof hit yes miss-case)))
      (b1-logic-bookproof-prove-implication-with-premise lib formula have consequence))))

(defun b1-membership-member-after-removal (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (left-parts (proof-list-of-length (cadr parts) 3))
       (operation-parts (proof-list-of-length (caddr left-parts) 3)))
    (let* ((left (cadr parts))
           (right (caddr parts))
           (operation (caddr left-parts))
           (xs (caddr operation-parts))
           (head (list *library-car* xs))
           (hit (proof-eq (cadr left-parts) head))
           (discard (proof-eq (cadr operation-parts) head)))
      (proof-with-checked-results
          ((preparation (b1-revappend-list-induction-prepare lib formula xs nil))
           (here (b1-membership-member-after-removal-step
                  (caddr preparation) (cadddr preparation) lib formula left right operation hit discard))
           (atom (proof-proof-assume (library-library-proof lib) (cadr preparation) nil))
           (there (b1-membership-member-after-removal-base atom lib formula left right operation)))
        (b1-revappend-list-induction lib preparation there here)))))

(defun b1-membership-member-after-removal-iff (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (claim-parts (proof-list-of-length (caddr parts) 3))
         (left-parts (proof-list-of-length (cadr claim-parts) 3))
         (operation-parts (proof-list-of-length (caddr left-parts) 3))
         (other-choice (proof-term-at (caddr claim-parts) 1))
         (other-item (proof-term-at other-choice 1))
         (original (proof-term-at (caddr claim-parts) 2)))
      (let* ((claim (caddr parts))
             (left (cadr claim-parts))
             (item (cadr left-parts))
             (removed (cadr operation-parts))
             (test (proof-eq removed item)))
        (proof-with-checked-results
            ((same (proof-proof-assume proof test t))
             (different (proof-proof-assume proof test nil))
             (reflexive (proof-proof-reflexive proof other-item))
             (reduction (proof-proof-rewrite proof reflexive same '(1 2 1)))
             (contained (b1-membership-member-after-removal
                         lib (list *library-implies* left original)))
             (have (proof-proof-assume proof left t))
             (original-membership (proof-proof-modus-ponens proof contained have))
             (yes (b1-membership-membership-case
                   lib claim (list reduction) (list same have original-membership) nil))
             (miss (proof-proof-assume proof left nil))
             (empty (b1-membership-membership-case lib claim (list reduction) (list same miss) nil))
             (identical (proof-proof-cases proof left yes empty))
             (irrel (b1-logic-bookproof-from-fact
                     lib (proof-sym "MEMBER-EQUAL-OF-REMOVE1-EQUAL-IRREL" "ACL2")
                     (list *library-implies* (proof-neg (proof-eq item removed))
                           (list *b1-revappend-iff* left original))))
             (reversed (b1-reciprocal-reverse-inequality lib different))
             (equivalence (proof-proof-modus-ponens proof irrel reversed))
             (no (b1-membership-membership-case lib claim nil (list different) equivalence))
             (premise (b1-logic-bookproof-prove-implication-premise lib formula))
             (consequence (proof-proof-cases proof test identical no)))
          (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))))))

(defun b1-membership-member-at-index-consequence-recursive
    (lib claim test zero-test nth-call index xs length fixed tail child-index cons-step bound induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((nonzero (proof-proof-assume proof zero-test nil))
         (index-integer (b1-logic-bookproof-forces
                         lib (library-integer index) nonzero nil (list *b1-logic-zp* *proof-not*) nil))
         (index-positive (b1-logic-bookproof-forces
                          lib (library-lt *proof-zero* index) nonzero (list index-integer)
                          (list *b1-logic-zp* *proof-not*) nil))
         (at-least-one (b1-arithmetic-integer-discrete lib index-positive index-integer))
         (nonnegative-index (library-library-cite
                             lib "POSITIVE-NONNEGATIVE" (list index) (list index-integer index-positive)))
         (fixed-index (b1-logic-bookproof-normalize
                       lib fixed (list index-integer nonnegative-index)
                       (list *b1-revappend-nfix* *proof-not*) nil nil nil nil))
         (less (proof-proof-rewrite proof bound fixed-index '(1 1)))
         (expanded-length (b1-revappend-open-list lib length (list cons-step)))
         (less (proof-proof-rewrite proof less expanded-length '(1 2)))
         (sums (b1-arithmetic-number-sums-init lib)))
      (let* ((with-sums (b1-arithmetic-number-sums-library sums))
             (sums-proof (library-library-proof with-sums))
             (tail-length (list *library-len* tail))
             (index-evidence (list index-integer)))
        (proof-with-checked-results
            ((less-literal (proof-step-first less))
             (less-equation (b1-arithmetic-number-sums-comparison-equation
                             sums less-literal (library-lt child-index tail-length) index-evidence))
             (less (proof-proof-rewrite sums-proof less less-equation '(1)))
             (between (b1-membership-step-at at-least-one 1))
             (shift (b1-arithmetic-number-sums-comparison-equation
                     sums between (library-lt child-index *proof-zero*) index-evidence))
             (child-nonnegative (proof-proof-rewrite sums-proof at-least-one shift '(1 1)))
             (child-integer (library-library-type-of with-sums child-index index-evidence))
             (child-fixed (b1-logic-bookproof-normalize
                           with-sums (list *b1-revappend-nfix* child-index)
                           (list child-integer child-nonnegative) (list *b1-revappend-nfix* *proof-not*)
                           nil nil nil nil))
             (reversed (proof-proof-symmetric sums-proof child-fixed))
             (child-bound (proof-proof-rewrite sums-proof less reversed '(1 1)))
             (smaller (b1-induction-tree-induction-hypothesis
                       (b1-induction-tree-induction-with-lib induction with-sums)
                       (table-put (list (cons xs tail)) index child-index) (list (list test t))))
             (child (proof-proof-modus-ponens sums-proof (car smaller) child-bound))
             (reflexive (proof-proof-reflexive sums-proof claim))
             (opened (b1-revappend-open-list with-sums nth-call (list cons-step nonzero)))
             (advanced (proof-proof-rewrite sums-proof reflexive opened '(1 2 1)))
             (child-literal (proof-step-first child))
             (advanced-value (b1-membership-step-at advanced 2))
             (forward (b1-logic-bookproof-from-fact
                       with-sums (proof-sym "MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP" "ACL2")
                       (list *library-implies* child-literal advanced-value)))
             (inherited (proof-proof-modus-ponens sums-proof forward child))
             (no (proof-proof-transport sums-proof inherited advanced)))
          (list no with-sums (cdr smaller)))))))

(defun b1-membership-member-at-index-consequence
    (bound lib formula claim test zero-test nth-call index xs length fixed tail child-index induction)
  (let ((proof (library-library-proof lib))
        (internal-nfix (proof-sym "SELF-NFIX" "ACL2")))
    (proof-with-checked-results
        ((cons-step (proof-proof-assume proof test t))
         (atom (proof-proof-assume proof test nil))
         (empty-length (b1-revappend-open-list lib length (list atom)))
         (impossible (proof-proof-rewrite proof bound empty-length '(1 2)))
         (given (b1-logic-bookproof-normalize lib fixed nil (list *b1-revappend-nfix*) nil nil nil t))
         (internal (b1-logic-bookproof-normalize
                    lib (list internal-nfix index) nil (list internal-nfix *library-natp*) nil nil nil t))
         (reversed-internal (proof-proof-symmetric proof internal))
         (alignment (proof-proof-chain proof given (list reversed-internal)))
         (natural-internal (library-library-cite lib "NFIX-NATURAL" (list index) nil))
         (natural (library-library-transport-argument lib natural-internal alignment 1))
         (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE" (list fixed) (list natural)))
         (base (b1-logic-bookproof-contradiction lib impossible nonnegative claim))
         (is-zero (proof-proof-assume proof zero-test t))
         (reflexive (proof-proof-reflexive proof claim))
         (opened-nth (b1-revappend-open-list lib nth-call (list cons-step is-zero)))
         (initial (proof-proof-rewrite proof reflexive opened-nth '(1 2 1)))
         (first-call (b1-membership-step-at initial 2))
         (first (b1-revappend-open-list lib first-call (list cons-step)))
         (nonempty (b1-revappend-cons-is-nonempty lib cons-step))
         (chained (proof-proof-chain proof initial (list first)))
         (yes (proof-proof-transport proof nonempty chained))
         (recursive (b1-membership-member-at-index-consequence-recursive
                     lib claim test zero-test nth-call index xs length fixed tail child-index
                     cons-step bound induction)))
      (let* ((with-sums (cadr recursive))
             (sums-proof (library-library-proof with-sums)))
        (proof-with-checked-results
            ((cons-case (proof-proof-cases sums-proof zero-test yes (car recursive)))
             (consequence (proof-proof-cases sums-proof test cons-case base))
             (implication (b1-logic-bookproof-prove-implication-with-premise
                           with-sums formula bound consequence))
             (step (b1-induction-tree-induction-finish (caddr recursive) implication)))
          (cons step with-sums))))))

(defun b1-membership-member-at-index (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim-parts (proof-list-of-length (caddr parts) 3))
       (nth-parts (proof-list-of-length (cadr claim-parts) 3))
       (length (proof-term-at (cadr parts) 2))
       (fixed (proof-term-at (cadr parts) 1)))
    (let* ((claim (caddr parts))
           (nth-call (cadr claim-parts))
           (xs (caddr claim-parts))
           (index (cadr nth-parts))
           (test (list *proof-consp* xs))
           (zero-test (list *b1-logic-zp* index))
           (tail (list *library-cdr* xs))
           (child-index (library-plus *proof-neg-one* index))
           (induction (b1-induction-tree-induction-init lib formula xs)))
      (proof-with-checked-results
          ((bound (b1-logic-bookproof-prove-implication-premise lib formula)))
        (b1-membership-member-at-index-consequence
         bound lib formula claim test zero-test nth-call index xs length fixed tail child-index induction)))))
