(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-list-sets-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *b1-list-sets-intersect* (proof-sym "INTERSECTP-EQUAL" "ACL2"))
(defconst *b1-list-sets-a* (proof-sym "A" "ACL2"))
(defconst *b1-list-sets-b* (proof-sym "B" "ACL2"))

(defun b1-list-sets-step-term (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b1-list-sets-known (evidence known)
  (if (endp evidence)
      known
    (proof-with-checked-results ((term (proof-step-first (car evidence))))
      (b1-list-sets-known (cdr evidence) (table-put known term (car evidence))))))

(defun b1-list-sets-append-membership-cases-finish-normalize
    (term trial evidence rules known combined append-rule)
  (let* ((unfold (remove-equal *b1-search-iff* (b1-search-attempt-definitions trial)))
         (split-rule (list :b1-search-equivalent-test combined append-rule))
         (structural (b1-search-attempt-structural-rule trial known))
         (local-rules (cons split-rule (append rules (list structural)))))
    (let ((result (b1-search-attempt-normalize
                   trial term evidence unfold local-rules nil (list :b1-search-condition known) t)))
      (if (failure-p (car result)) (car result) result))))

(defun b1-list-sets-append-membership-cases-finish
    (evidence rules lib index formula hypothesis combined append-rule)
  (let ((trial (b1-search-attempt-init lib index 160 nil t)))
    (proof-with-checked-results
        ((known (b1-list-sets-known evidence nil))
         (normalized (b1-list-sets-append-membership-cases-finish-normalize
                      formula trial evidence rules known combined append-rule))
         (next (b1-list-sets-step-term (car normalized) 2))
         (normalized-next (b1-list-sets-append-membership-cases-finish-normalize
                           next (cdr normalized) evidence rules known combined append-rule))
         (lib (b1-search-attempt-lib (cdr normalized-next)))
         (step (proof-proof-chain (library-library-proof lib)
                                  (car normalized) (list (car normalized-next))))
         (reduced (b1-list-sets-step-term step 2))
         (hypothesis-term (proof-step-first hypothesis))
         (normalized-hypothesis (b1-list-sets-append-membership-cases-finish-normalize
                                 hypothesis-term (cdr normalized-next) evidence rules known
                                 combined append-rule))
         (lib (b1-search-attempt-lib (cdr normalized-hypothesis)))
         (child (proof-proof-rewrite (library-library-proof lib)
                                     hypothesis (car normalized-hypothesis) '(1)))
         (solved (b1-search-attempt-prove (cdr normalized-hypothesis)
                                         reduced evidence (list child) 6))
         (result (car solved))
         (lib (b1-search-attempt-lib (cdr solved)))
         (transported (proof-proof-transport (library-library-proof lib) result step)))
      (cons transported lib))))

(defun b1-list-sets-append-membership-cases-only-second
    (evidence lib intersection tail index formula hypothesis combined append-rule)
  (if (eq intersection :none)
      (b1-list-sets-append-membership-cases-finish
       evidence nil lib index formula hypothesis combined append-rule)
    (let ((child (list *b1-list-sets-intersect* tail intersection)))
      (proof-with-checked-results
          ((boolean (b1-predicates-boolean-definition lib child 1))
           (lib (cdr boolean))
           (proof (library-library-proof lib))
           (yes (proof-proof-assume proof child t))
           (no (proof-proof-assume proof child nil))
           (true-value (b1-logic-bookproof-boolean-value lib yes (car boolean)))
           (on-true (b1-list-sets-append-membership-cases-finish
                     (append evidence (list yes)) (list (b1-logic-equal-to true-value))
                     lib index formula hypothesis combined append-rule))
           (lib (cdr on-true))
           (false-value (b1-logic-bookproof-false-value lib no))
           (on-false (b1-list-sets-append-membership-cases-finish
                      (append evidence (list no)) (list (b1-logic-equal-to false-value))
                      lib index formula hypothesis combined append-rule))
           (lib (cdr on-false))
           (step (proof-proof-cases (library-library-proof lib)
                                    child (car on-true) (car on-false))))
        (cons step lib)))))

(defun b1-list-sets-append-membership-cases (lib formula driver first second intersection)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((index (b1-search-fact-index-init lib))
         (test (list *proof-consp* driver))
         (cons-step (proof-proof-assume proof test t))
         (head (list *library-car* driver))
         (tail (list *library-cdr* driver))
         (induction (b1-induction-tree-induction-init lib formula driver))
         (induction-result (b1-induction-tree-induction-hypothesis
                            induction (list (cons driver tail)) (list (list test t))))
         (hypothesis (car induction-result))
         (induction (cdr induction-result))
         (append-rule (proof-proof-fact
                       proof (proof-sym "MEMBER-EQUAL-APPEND" "ACL2")
                       (list (list *library-x* head)
                             (list *b1-list-sets-a* first)
                             (list *b1-list-sets-b* second))))
         (combined (b1-list-sets-step-term append-rule 1))
         (first-test (list *b1-list-sets-member* head first))
         (second-test (list *b1-list-sets-member* head second))
         (first-present (proof-proof-assume proof first-test t))
         (have-first (b1-list-sets-append-membership-cases-finish
                      (list cons-step first-present) nil
                      lib index formula hypothesis combined append-rule))
         (lib (cdr have-first))
         (proof (library-library-proof lib))
         (first-absent (proof-proof-assume proof first-test nil))
         (miss-first (list cons-step first-absent))
         (second-present (proof-proof-assume proof second-test t))
         (have-second (b1-list-sets-append-membership-cases-only-second
                       (append miss-first (list second-present))
                       lib intersection tail index formula hypothesis combined append-rule))
         (lib (cdr have-second))
         (proof (library-library-proof lib))
         (second-absent (proof-proof-assume proof second-test nil))
         (miss-both (b1-list-sets-append-membership-cases-finish
                     (append miss-first (list second-absent)) nil
                     lib index formula hypothesis combined append-rule))
         (lib (cdr miss-both))
         (proof (library-library-proof lib))
         (second-case (proof-proof-cases proof second-test (car have-second) (car miss-both)))
         (step (proof-proof-cases proof first-test (car have-first) second-case))
         (base-trial (b1-search-attempt-init lib index 100 nil t))
         (atom-step (proof-proof-assume proof test nil))
         (base (b1-search-attempt-prove base-trial formula (list atom-step) nil 6))
         (base-step (car base))
         (lib (b1-search-attempt-lib (cdr base)))
         (cases (proof-proof-cases (library-library-proof lib) test step base-step))
         (induction (b1-induction-tree-induction-with-lib induction lib))
         (result (b1-induction-tree-induction-finish induction cases)))
      (cons result lib))))

(defun b1-list-sets-no-duplicate-append (lib formula)
  (proof-with-checked-results
      ((left (proof-term-at formula 1))
       (append-call (proof-term-at left 1))
       (parts (proof-list-of-length append-call 3)))
    (let ((first (cadr parts))
          (second (caddr parts)))
      (b1-list-sets-append-membership-cases
       lib formula first (list *library-cdr* first) second :none))))

(defun b1-list-sets-intersect-append (lib formula)
  (proof-with-checked-results
      ((left (proof-term-at formula 1))
       (parts (proof-list-of-length left 3))
       (append-call (proof-list-of-length (caddr parts) 3)))
    (let ((first (cadr append-call))
          (second (caddr append-call)))
      (b1-list-sets-append-membership-cases lib formula (cadr parts) first second first))))

(defun b1-list-sets-appended-first-intersection-branch
    (cell evidence induction lib formula left joined tested)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-list lib joined (list cell)))
         (expanded (b1-revappend-lift-argument lib left opened 1))
         (condition (proof-step-first cell))
         (evidence (cons cell evidence))
         (expanded (if (proof-is-call condition *proof-consp*)
                       (proof-with-checked-results
                           ((term (b1-list-sets-step-term expanded 2))
                            (opened (b1-revappend-open-list lib term evidence)))
                         (proof-proof-chain proof expanded (list opened)))
                     expanded))
         (source (b1-revappend-open-list lib tested evidence)))
      (b1-logic-bookproof-case-proof
       lib formula evidence nil
       (cons (b1-logic-equal-to expanded)
             (cons (b1-logic-equal-to source)
                   (if induction (list (b1-logic-equal-to induction)) nil)))
       16))))

(defun b1-list-sets-appended-first-intersection-step
    (cons-step induction lib formula left joined tested present)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((yes (proof-proof-assume proof present t))
         (hit (b1-list-sets-appended-first-intersection-branch
               cons-step (list yes) nil lib formula left joined tested))
         (no (proof-proof-assume proof present nil))
         (miss (b1-list-sets-appended-first-intersection-branch
                cons-step (list no) induction lib formula left joined tested)))
      (proof-proof-cases proof present hit miss))))

(defun b1-list-sets-appended-first-intersection (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (left (cadr parts))
         (operands (proof-list-of-length left 3))
         (joined (cadr operands))
         (append-call (proof-list-of-length joined 3))
         (first (cadr append-call))
         (tested (proof-term-at (caddr parts) 1))
         (present (list *b1-list-sets-member* (list *library-car* first) (caddr operands)))
         (preparation (b1-revappend-list-induction-prepare lib formula first nil))
         (here (b1-list-sets-appended-first-intersection-step
                (caddr preparation) (cadddr preparation) lib formula left joined tested present))
         (atom-step (proof-proof-assume proof (cadr preparation) nil))
         (there (b1-list-sets-appended-first-intersection-branch
                 atom-step nil nil lib formula left joined tested)))
      (b1-revappend-list-induction lib preparation there here))))

(defun b1-list-sets-intersection-with-extended-second-reductions
    (cell evidence lib left original-membership original-intersection)
  (let ((evidence (cons cell evidence)))
    (proof-with-checked-results
        ((left-view (b1-revappend-open-list lib left evidence))
         (membership-view (b1-revappend-open-list lib original-membership evidence))
         (intersection-view (b1-revappend-open-list lib original-intersection evidence)))
      (list left-view membership-view intersection-view))))

(defun b1-list-sets-intersection-with-extended-second-base
    (atom-step lib formula left original-membership original-intersection)
  (proof-with-checked-results
      ((opened (b1-list-sets-intersection-with-extended-second-reductions
                atom-step nil lib left original-membership original-intersection)))
    (b1-membership-membership-case lib formula opened (list atom-step) nil)))

(defun b1-list-sets-intersection-with-extended-second-step-branch
    (test reflected lib formula head pair cons-step induction left
          original-membership original-intersection)
  (proof-with-checked-results
      ((in-extended (b1-revappend-open-list
                     lib (list *b1-list-sets-member* head pair) (list test)))
       (reductions (b1-list-sets-intersection-with-extended-second-reductions
                    cons-step (list reflected) lib left original-membership original-intersection)))
    (b1-membership-membership-case lib formula (append reductions (list in-extended))
                                   (list cons-step test reflected) induction)))

(defun b1-list-sets-intersection-with-extended-second-step
    (cons-step induction lib formula equal-head head pair left original-membership original-intersection)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((hit (proof-proof-assume proof equal-head t))
         (miss (proof-proof-assume proof equal-head nil))
         (positive (proof-proof-symmetric proof hit))
         (yes (b1-list-sets-intersection-with-extended-second-step-branch
               hit positive lib formula head pair cons-step induction left
               original-membership original-intersection))
         (negative (b1-reciprocal-reverse-inequality lib miss))
         (no (b1-list-sets-intersection-with-extended-second-step-branch
              miss negative lib formula head pair cons-step induction left
              original-membership original-intersection)))
      (proof-proof-cases proof equal-head yes no))))

(defun b1-list-sets-intersection-with-extended-second (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (left (cadr parts))
         (right (caddr parts))
         (operands (proof-list-of-length left 3))
         (first (cadr operands))
         (pair (caddr operands))
         (added (proof-term-at pair 1))
         (original-membership (proof-term-at right 1))
         (original-intersection (proof-term-at right 3))
         (head (list *library-car* first))
         (equal-head (proof-eq head added))
         (preparation (b1-revappend-list-induction-prepare lib formula first nil))
         (here (b1-list-sets-intersection-with-extended-second-step
                (caddr preparation) (cadddr preparation) lib formula equal-head head pair left
                original-membership original-intersection))
         (atom-step (proof-proof-assume proof (cadr preparation) nil))
         (there (b1-list-sets-intersection-with-extended-second-base
                 atom-step lib formula left original-membership original-intersection)))
      (b1-revappend-list-induction lib preparation there here))))
