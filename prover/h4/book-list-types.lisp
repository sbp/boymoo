(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-list-types-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *h4-book-list-types-synp* (proof-sym "SYNP" "ACL2"))

(defun h4-book-list-types-conjuncts (formula)
  (if (proof-is-call formula *proof-if*)
      (cond ((endp (cdddr formula)) '(:failure "failure" ""))
            ((equal (cadddr formula) *proof-false*)
             (proof-with-checked-results
                 ((first (h4-book-list-types-conjuncts (cadr formula)))
                  (second (h4-book-list-types-conjuncts (caddr formula))))
               (append first second)))
            (t (list formula)))
    (list formula)))

(defun h4-book-list-types-conjunct-proofs-visit (n p step)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h4-book-list-types-conjunct-proofs-visit")
    (proof-with-checked-results ((formula (proof-step-first step)))
      (if (proof-is-call formula *proof-if*)
          (proof-with-checked-results ((otherwise-term (proof-term-at formula 3)))
            (if (equal otherwise-term *proof-false*)
                (proof-with-checked-results
                    ((parts (h4-tactics-tactics-conjunct p step))
                     (first (h4-book-list-types-conjunct-proofs-visit
                             (1- n) p (car parts)))
                     (second (h4-book-list-types-conjunct-proofs-visit
                              (1- n) p (cadr parts))))
                  (append first second))
              (list step)))
        (list step)))))

(defun h4-book-list-types-conjunct-proofs (p step)
  (h4-book-list-types-conjunct-proofs-visit 1000000 p step))

(defun h4-book-list-types-has-syntax-guard (components)
  (and (consp components)
       (or (proof-is-call (car components) *h4-book-list-types-synp*)
           (h4-book-list-types-has-syntax-guard (cdr components)))))

(defun h4-book-list-types-syntax-context (formula)
  (if (proof-is-call formula *library-implies*)
    (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
      (let ((goal (caddr parts)))
        (if (and (proof-compound goal) (equal (len goal) 2)
                 (not (proof-compound (car goal))))
            (proof-with-checked-results
                ((components (h4-book-list-types-conjuncts (cadr parts))))
              (and (h4-book-list-types-has-syntax-guard components)
                   (list goal components)))
          nil)))
    nil))

(defun h4-book-list-types-matching-tests (member-term items components)
  (if (endp components)
      nil
    (let* ((test (car components))
           (rest (h4-book-list-types-matching-tests
                  member-term items (cdr components))))
      (if (and (proof-compound test) (equal (len test) 2)
               (not (proof-compound (car test))) (equal (cadr test) items))
          (cons (list member-term test) rest)
        rest))))

(defun h4-book-list-types-matches-for-member (member-term item components)
  (if (proof-is-call member-term *h4-book-list-types-member*)
      (proof-with-checked-results ((actual (proof-term-at member-term 1)))
        (if (equal actual item)
            (proof-with-checked-results ((items (proof-term-at member-term 2)))
              (if (proof-compound items)
                  nil
                (h4-book-list-types-matching-tests member-term items components)))
          nil))
    nil))

(defun h4-book-list-types-matches (members item components)
  (if (endp members)
      nil
    (proof-with-checked-results
        ((here (h4-book-list-types-matches-for-member
                (car members) item components))
         (rest (h4-book-list-types-matches (cdr members) item components)))
      (append here rest))))

(defun h4-book-list-types-syntax-guarded-member-types (formula)
  (proof-with-checked-results ((context (h4-book-list-types-syntax-context formula)))
    (and context
         (h4-book-list-types-matches (cadr context) (cadar context) (cadr context)))))

(defun h4-book-list-types-membership-induction-opened (step shape p)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (axiom (proof-proof-unfold pr literal))
         (right (proof-rewritten-term axiom))
         (reduction (h4-tactics-tactics-normalize
                     p right (list shape)
                     (append *h4-book-measures-selectors* (list *proof-not*)) nil nil))
         (equality (proof-proof-chain pr axiom (list reduction))))
      (proof-proof-rewrite pr step equality '(1)))))

(defun h4-book-list-types-membership-induction-atom
    (shape p given-member goal statement)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((impossible (h4-book-list-types-membership-induction-opened
                      given-member shape p))
         (literal (proof-step-first impossible)))
      (if (equal literal *proof-false*)
          (proof-with-checked-results
              ((conclusion (proof-proof-subsume
                            pr impossible (cons goal (cdr (proof-step-clause impossible))))))
            (h4-tactics-tactics-imply p statement conclusion))
        '(:failure "InapplicableStep" "")))))

(defun h4-book-list-types-membership-induction-pair-present
    (equality p head-type item)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first equality))
         (left (proof-term-at literal 1))
         (oriented (if (equal left item) (proof-proof-symmetric pr equality) equality)))
      (proof-proof-rewrite pr head-type oriented '(1 1)))))

(defun h4-book-list-types-membership-induction-pair-later
    (inequality p lookup induction tail-type)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((tail-lookup (proof-proof-prove-if pr lookup inequality))
         (literal (proof-step-first induction))
         (premise (proof-term-at literal 1))
         (conjoined (h4-tactics-tactics-conjunction p premise tail-lookup tail-type)))
      (h4-tactics-tactics-modus-ponens p induction conjoined))))

(defun h4-book-list-types-membership-induction-pair
    (shape p given-member given-list goal item items statement substitutions)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((lookup (h4-book-list-types-membership-induction-opened given-member shape p))
         (opened-list (h4-book-list-types-membership-induction-opened given-list shape p))
         (types (h4-tactics-tactics-conjunct p opened-list))
         (head-literal (proof-step-first (car types)))
         (predicate (proof-term-at goal 0)))
      (let ((head (list *library-car* items)))
        (if (not (equal head-literal (list predicate head)))
            '(:failure "InapplicableStep" "")
          (proof-with-checked-results
              ((lookup-literal (proof-step-first lookup))
               (match (proof-term-at lookup-literal 1)))
            (if (not (or (equal match (proof-eq item head))
                         (equal match (proof-eq head item))))
                '(:failure "InapplicableStep" "")
              (proof-with-checked-results
                  ((builtin (library-library-builtin p 3 items))
                   (descent (proof-proof-discharge pr builtin shape))
                   (smaller (proof-step-first descent))
                   (instance (proof-subst statement (proof-bindings-table substitutions nil)))
                   (hypothesis (proof-proof-assume pr (proof-ite smaller instance *proof-true*) t))
                   (induction (proof-proof-prove-if pr hypothesis descent))
                   (equality (proof-proof-assume pr match t))
                   (present (h4-book-list-types-membership-induction-pair-present
                             equality p (car types) item))
                   (inequality (proof-proof-assume pr match nil))
                   (later (h4-book-list-types-membership-induction-pair-later
                           inequality p lookup induction (cadr types)))
                   (cases (h4-tactics-tactics-case-of p goal match present later)))
                (h4-tactics-tactics-imply p statement cases)))))))))

(defun h4-book-list-types-membership-induction (p member-term list-test goal)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((actuals (if (integerp member-term)
                      (proof-term-at member-term 0)
                    (proof-list-of-length (cdr member-term) 2))))
      (let* ((item (car actuals))
             (items (cadr actuals))
             (tree (list *proof-consp* items))
             (tail (list *library-cdr* items))
             (premise (proof-ite member-term list-test *proof-false*))
             (statement (list *library-implies* premise goal))
             (substitutions (list (list items tail))))
        (proof-with-checked-results
            ((given (proof-proof-assume pr premise t))
             (parts (h4-tactics-tactics-conjunct p given))
             (pair-shape (proof-proof-assume pr tree t))
             (pair-proof (h4-book-list-types-membership-induction-pair
                          pair-shape p (car parts) (cadr parts) goal item items
                          statement substitutions))
             (atom-shape (proof-proof-assume pr tree nil))
             (atom-proof (h4-book-list-types-membership-induction-atom
                          atom-shape p (car parts) goal statement))
             (cases (h4-tactics-tactics-case-of p statement tree pair-proof atom-proof))
             (ordinal (library-library-builtin p 1 items)))
          (proof-proof-induct pr ordinal cases statement (list *library-count* items)
                              (list substitutions)))))))

(defun h4-book-list-types-evidence (steps evidence)
  (if (endp steps)
      evidence
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (h4-book-list-types-evidence
       (cdr steps) (table-put evidence literal (car steps))))))

(defun h4-book-list-types-evidence-at (evidence literal)
  (let ((entry (assoc-equal literal evidence)))
    (if entry (cdr entry)
      '(:failure "failure" ""))))

(defun h4-book-list-types-from-induction (p formula member-term list-test lemma)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((given (proof-proof-assume pr (cadr formula) t))
         (parts (h4-book-list-types-conjunct-proofs p given))
         (evidence (h4-book-list-types-evidence parts nil))
         (literal (proof-step-first lemma))
         (condition (proof-term-at literal 1))
         (member-step (h4-book-list-types-evidence-at evidence member-term))
         (list-step (h4-book-list-types-evidence-at evidence list-test))
         (premise (h4-tactics-tactics-conjunction p condition member-step list-step))
         (conclusion (h4-tactics-tactics-modus-ponens p lemma premise)))
      (h4-tactics-tactics-imply p formula conclusion))))

(defun h4-book-list-types-member-type-proof-tests (p formula matches)
  (if (endp matches)
      nil
    (let* ((match (car matches))
           (member-term (car match))
           (list-test (cadr match)))
      (if (assoc-equal (car list-test) (proof-proof-definitions (library-library-proof p)))
          (let ((lemma (h4-book-list-types-membership-induction
                        p member-term list-test (caddr formula))))
            (cond ((not (failure-p lemma))
                   (h4-book-list-types-from-induction p formula member-term list-test lemma))
                  ((member-equal (cadr lemma) '("InapplicableStep" "assertion"))
                   (h4-book-list-types-member-type-proof-tests p formula (cdr matches)))
                  (t lemma)))
        (h4-book-list-types-member-type-proof-tests p formula (cdr matches))))))

(defun h4-book-list-types-member-type-proof-members (p formula members item components)
  (if (endp members)
      nil
    (proof-with-checked-results
        ((matches (h4-book-list-types-matches-for-member (car members) item components))
         (found (h4-book-list-types-member-type-proof-tests p formula matches)))
      (or found
          (h4-book-list-types-member-type-proof-members
           p formula (cdr members) item components)))))

(defun h4-book-list-types-member-type-proof (p formula)
  (proof-with-checked-results ((context (h4-book-list-types-syntax-context formula)))
    (and context
         (h4-book-list-types-member-type-proof-members
          p formula (cadr context) (cadar context) (cadr context)))))
