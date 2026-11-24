(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-permutation-a* (proof-sym "A" "ACL2"))
(defconst *b1-permutation-b* (proof-sym "B" "ACL2"))
(defconst *b1-permutation-rm* (proof-sym "RM" "ACL2"))
(defconst *b1-permutation-memb* (proof-sym "MEMB" "ACL2"))
(defconst *b1-permutation-perm* (proof-sym "PERM" "ACL2"))
(defconst *b1-permutation-booleanp* (proof-sym "BOOLEANP" "ACL2"))

(defun b1-permutation-call (operator args)
  (cons operator args))

(defun b1-permutation-equation-rules (equations)
  (if (endp equations)
      nil
    (cons (b1-logic-equal-to (car equations))
          (b1-permutation-equation-rules (cdr equations)))))

(defun b1-permutation-first-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b1-permutation-use-implication (lib label bindings evidence)
  (let ((proof (library-library-proof lib))
        (name (proof-sym (concatenate 'string "SELF-" label) "ACL2")))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof name (table-items bindings)))
         (test (b1-permutation-first-at fact 1))
         (premise (b1-logic-bookproof-normalize-proof lib test evidence nil nil nil)))
      (proof-proof-modus-ponens proof fact premise))))

(defun b1-permutation-opener (lib term evidence equations)
  (proof-with-checked-results ((head (proof-term-at term 0)))
    (b1-logic-bookproof-normalize lib term evidence (list head)
                                 (b1-permutation-equation-rules equations) nil nil nil)))

(defun b1-permutation-transfer (lib claim step equations)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (if (equal claim literal)
        step
      (b1-logic-bookproof-normalize-proof lib claim (list step) nil
                                         (b1-permutation-equation-rules equations) nil))))

(defun b1-permutation-impossible (lib claim step equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((rewritten (proof-proof-rewrite proof step equation '(1)))
         (dead (proof-proof-tidy proof rewritten))
         (value (b1-permutation-first-at equation 2)))
      (if (equal value *proof-false*)
          (proof-proof-subsume proof dead (cons claim (proof-step-clause dead)))
        '(:failure "failure" "")))))

(defun b1-permutation-reversed-negative (lib negative)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equality (b1-permutation-first-at negative 1))
         (parts (proof-list-of-length equality 3)))
      (let ((test (proof-eq (caddr parts) (cadr parts))))
        (proof-with-checked-results
            ((assumed (proof-proof-assume proof test t))
             (reversed (proof-proof-symmetric proof assumed))
             (contradiction (proof-proof-cut proof reversed negative)))
          (proof-proof-front proof contradiction (proof-neg test)))))))

(defun b1-permutation-member-after-removal-consequence-reduced
    (context a-hyp b-hyp lib after before tail)
  (let ((assumptions (remove-eq nil (list context a-hyp b-hyp)))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((argument (proof-term-at after 2))
         (delete (b1-permutation-opener lib argument assumptions nil))
         (advanced (b1-conjunction-reduction-at lib after delete))
         (advanced-term (b1-permutation-first-at advanced 2))
         (argument (proof-term-at advanced-term 2))
         (advanced (if (equal argument tail)
                       advanced
                     (proof-with-checked-results
                         ((opened (b1-permutation-opener lib advanced-term assumptions nil)))
                       (proof-proof-chain proof advanced (list opened)))))
         (original (b1-permutation-opener lib before assumptions nil)))
      (list advanced original))))

(defun b1-permutation-member-after-removal-consequence-finish
    (equations a-hyp b-hyp lib disjoint premise goal a-test test tail induction)
  (let ((proof (library-library-proof lib))
        (opened-after (car equations))
        (opened-before (cadr equations)))
    (proof-with-checked-results
        ((after (b1-permutation-first-at opened-after 2))
         (before (b1-permutation-first-at opened-before 2)))
      (if (equal after before)
          (proof-with-checked-results
              ((step (if disjoint
                         (proof-with-checked-results
                             ((reversed (proof-proof-symmetric proof opened-before)))
                           (proof-proof-chain proof opened-after (list reversed)))
                       (proof-with-checked-results
                           ((rewritten (proof-proof-rewrite proof premise opened-after '(1))))
                         (proof-proof-transport proof rewritten opened-before)))))
            (cons step induction))
        (proof-with-checked-results
            ((literal (if a-hyp (proof-step-first a-hyp)
                        '(:failure "failure" ""))))
          (if (equal literal a-test)
              (proof-with-checked-results
                  ((step (if disjoint
                             (proof-with-checked-results
                                 ((reversed (proof-proof-symmetric proof b-hyp))
                                  (equality (proof-proof-chain proof a-hyp (list reversed))))
                               (b1-logic-bookproof-contradiction lib equality premise goal))
                           (proof-proof-transport proof a-hyp opened-before))))
                (cons step induction))
            (proof-with-checked-results
                ((child (b1-induction-tree-induction-hypothesis
                         induction (list (cons *library-x* tail)) (list (list test t))))
                 (step (if disjoint
                           (proof-with-checked-results
                               ((equality (proof-proof-modus-ponens proof (car child) premise))
                                (reversed (proof-proof-symmetric proof opened-before)))
                             (proof-proof-chain proof opened-after (list equality reversed)))
                         (proof-with-checked-results
                             ((rewritten (proof-proof-rewrite proof premise opened-after '(1)))
                              (result (proof-proof-modus-ponens proof (car child) rewritten)))
                           (proof-proof-transport proof result opened-before)))))
              (cons step (cdr child)))))))))

(defun b1-permutation-member-after-removal-consequence-branch-outcome
    (b-holds a-hyp lib cons-step after before tail disjoint premise goal a-test b-test
             test induction)
  (proof-with-checked-results
      ((b-hyp (proof-proof-assume (library-library-proof lib) b-test b-holds))
       (equations (b1-permutation-member-after-removal-consequence-reduced
                   cons-step a-hyp b-hyp lib after before tail)))
    (b1-permutation-member-after-removal-consequence-finish
     equations a-hyp b-hyp lib disjoint premise goal a-test test tail induction)))

(defun b1-permutation-member-after-removal-consequence-branch
    (a-holds lib cons-step after before tail disjoint premise goal a-test b-test test induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((a-hyp (proof-proof-assume proof a-test a-holds))
         (yes (b1-permutation-member-after-removal-consequence-branch-outcome
               t a-hyp lib cons-step after before tail disjoint premise goal a-test b-test
               test induction))
         (no (b1-permutation-member-after-removal-consequence-branch-outcome
              nil a-hyp lib cons-step after before tail disjoint premise goal a-test b-test
              test (cdr yes)))
         (step (proof-proof-cases proof b-test (car yes) (car no))))
      (cons step (cdr no)))))

(defun b1-permutation-member-after-removal-consequence
    (premise lib disjoint after before goal test tail a-test b-test induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((atom (proof-proof-assume proof test nil))
         (equations (b1-permutation-member-after-removal-consequence-reduced
                     atom nil nil lib after before tail))
         (base (b1-permutation-member-after-removal-consequence-finish
                equations nil nil lib disjoint premise goal a-test test tail induction))
         (cons-step (proof-proof-assume proof test t))
         (yes (b1-permutation-member-after-removal-consequence-branch
               t lib cons-step after before tail disjoint premise goal a-test b-test
               test (cdr base)))
         (no (b1-permutation-member-after-removal-consequence-branch
              nil lib cons-step after before tail disjoint premise goal a-test b-test
              test (cdr yes)))
         (cons-case (proof-proof-cases proof a-test (car yes) (car no)))
         (step (proof-proof-cases proof test cons-case (car base))))
      (cons step (cdr no)))))

(defun b1-permutation-member-after-removal (lib disjoint)
  (let* ((label (if disjoint "MEMB-RM-DISJOINT" "MEMB-RM"))
         (after (b1-permutation-call *b1-permutation-memb*
                  (list *b1-permutation-a*
                        (b1-permutation-call *b1-permutation-rm*
                          (list *b1-permutation-b* *library-x*)))))
         (before (b1-permutation-call *b1-permutation-memb*
                   (list *b1-permutation-a* *library-x*)))
         (different (proof-neg (proof-eq *b1-permutation-a* *b1-permutation-b*)))
         (goal (if disjoint (proof-eq after before) before))
         (formula (list *library-implies* (if disjoint different after) goal))
         (induction (b1-induction-tree-induction-init lib formula *library-x*))
         (test (list *proof-consp* *library-x*))
         (head (list *library-car* *library-x*))
         (tail (list *library-cdr* *library-x*))
         (a-test (proof-eq *b1-permutation-a* head))
         (b-test (proof-eq *b1-permutation-b* head)))
    (proof-with-checked-results
        ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-permutation-member-after-removal-consequence
                       premise lib disjoint after before goal test tail a-test b-test induction))
         (proof (b1-logic-bookproof-prove-implication-with-premise
                 lib formula premise (car consequence)))
         (step (b1-induction-tree-induction-finish (cdr consequence) proof)))
      (library-library-lemma lib label formula step nil))))

(defun b1-permutation-removal-order-open-at (term evidence lib tail)
  (proof-with-checked-results
      ((argument (proof-term-at term 2))
       (opened (b1-permutation-opener lib argument evidence nil))
       (first (b1-conjunction-reduction-at lib term opened))
       (value (b1-permutation-first-at first 2))
       (argument (proof-term-at value 2)))
    (if (equal argument tail)
        first
      (proof-with-checked-results ((second (b1-permutation-opener lib value evidence nil)))
        (proof-proof-chain (library-library-proof lib) first (list second))))))

(defun b1-permutation-removal-order-a-branch-b-branch
    (b-holds a-holds pa lib cons-test first second tail b-test induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((pb (proof-proof-assume proof b-test b-holds))
         (cons-step (proof-proof-assume proof cons-test t))
         (left (b1-permutation-removal-order-open-at first (list cons-step pa pb) lib tail))
         (right (b1-permutation-removal-order-open-at second (list cons-step pa pb) lib tail))
         (change (cond ((and a-holds b-holds)
                        (proof-with-checked-results
                            ((reversed (proof-proof-symmetric proof pb))
                             (same (proof-proof-chain proof pa (list reversed)))
                             (rewritten (proof-proof-rewrite proof left same '(1 2 1))))
                          (cons rewritten induction)))
                       ((and (not a-holds) (not b-holds))
                        (proof-with-checked-results
                            ((child (b1-induction-tree-induction-hypothesis
                                     induction (list (cons *library-x* tail))
                                     (list (list cons-test t))))
                             (rewritten (proof-proof-rewrite proof left (car child) '(1 2 2))))
                          (cons rewritten (cdr child))))
                       (t (cons left induction))))
         (reversed (proof-proof-symmetric proof right))
         (step (proof-proof-chain proof (car change) (list reversed))))
      (cons step (cdr change)))))

(defun b1-permutation-removal-order-a-branch
    (a-holds lib cons-test first second tail a-test b-test induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((pa (proof-proof-assume proof a-test a-holds))
         (yes (b1-permutation-removal-order-a-branch-b-branch
               t a-holds pa lib cons-test first second tail b-test induction))
         (no (b1-permutation-removal-order-a-branch-b-branch
              nil a-holds pa lib cons-test first second tail b-test (cdr yes)))
         (step (proof-proof-cases proof b-test (car yes) (car no))))
      (cons step (cdr no)))))

(defun b1-permutation-removal-order (lib)
  (let* ((proof (library-library-proof lib))
         (first (b1-permutation-call *b1-permutation-rm*
                  (list *b1-permutation-a* (b1-permutation-call *b1-permutation-rm*
                                            (list *b1-permutation-b* *library-x*)))))
         (second (b1-permutation-call *b1-permutation-rm*
                   (list *b1-permutation-b* (b1-permutation-call *b1-permutation-rm*
                                             (list *b1-permutation-a* *library-x*)))))
         (goal (proof-eq first second))
         (cons-test (list *proof-consp* *library-x*))
         (head (list *library-car* *library-x*))
         (tail (list *library-cdr* *library-x*))
         (a-test (proof-eq *b1-permutation-a* head))
         (b-test (proof-eq *b1-permutation-b* head))
         (induction (b1-induction-tree-induction-init lib goal *library-x*)))
    (proof-with-checked-results
        ((atom (proof-proof-assume proof cons-test nil))
         (left (b1-permutation-removal-order-open-at first (list atom) lib tail))
         (right (b1-permutation-removal-order-open-at second (list atom) lib tail))
         (reversed (proof-proof-symmetric proof right))
         (base (proof-proof-chain proof left (list reversed)))
         (yes (b1-permutation-removal-order-a-branch
               t lib cons-test first second tail a-test b-test induction))
         (no (b1-permutation-removal-order-a-branch
              nil lib cons-test first second tail a-test b-test (cdr yes)))
         (step (proof-proof-cases proof a-test (car yes) (car no)))
         (cases (proof-proof-cases proof cons-test step base))
         (finished (b1-induction-tree-induction-finish (cdr no) cases)))
      (library-library-lemma lib "RM-COMMUTES" goal finished nil))))

(defun b1-permutation-perm-adding-cons-consequence-branch
    (holds lib other-member call-left call-right cons-proof mem-miss remove-miss right-arg moved)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((hypothesis (proof-proof-assume proof other-member holds))
         (lhs (b1-permutation-opener lib call-left (list cons-proof hypothesis)
                                     (list mem-miss remove-miss)))
         (rhs (b1-permutation-opener lib call-right (list hypothesis) (list right-arg)))
         (reversed (proof-proof-symmetric proof rhs)))
      (proof-proof-chain proof lhs (list (and holds moved) reversed)))))

(defun b1-permutation-perm-adding-cons-consequence
    (premise lib cons-test goal member test head tail changed other-member call-left call-right
             induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((not-cons (proof-proof-assume proof cons-test nil))
         (cons-proof (proof-proof-assume proof cons-test t))
         (opened (b1-permutation-opener lib member (list not-cons) nil))
         (no (b1-permutation-impossible lib goal premise opened))
         (hit (proof-proof-assume proof test t))
         (miss (proof-proof-assume proof test nil))
         (head-hit (proof-proof-symmetric proof hit))
         (head-miss (b1-permutation-reversed-negative lib miss)))
      (let* ((extended (b1-permutation-call *proof-cons* (list *b1-permutation-a* *library-y*)))
             (old-member (b1-permutation-call *b1-permutation-memb* (list head extended)))
             (remove-head (b1-permutation-call *b1-permutation-rm* (list head extended))))
        (proof-with-checked-results
            ((mem-hit (b1-logic-bookproof-normalize-proof lib old-member (list head-hit)
                                                         (list *b1-permutation-memb*) nil nil))
             (removal (b1-permutation-opener lib remove-head (list head-hit) nil))
             (yes-lhs (b1-permutation-opener lib call-left (list cons-proof mem-hit) (list removal)))
             (argument (proof-term-at call-right 1))
             (opened (b1-permutation-opener lib argument (list cons-proof hit) nil))
             (yes-rhs (b1-conjunction-reduction-at lib call-right opened))
             (reversed (proof-proof-symmetric proof yes-rhs))
             (yes (proof-proof-chain proof yes-lhs (list reversed)))
             (mem-miss (b1-permutation-opener lib old-member (list head-miss) nil))
             (remove-miss (b1-permutation-opener lib remove-head (list head-miss) nil))
             (right-arg (b1-permutation-opener lib argument (list cons-proof miss) nil))
             (opened (b1-permutation-opener lib member (list cons-proof miss) nil))
             (member-tail (proof-proof-rewrite proof premise opened '(1)))
             (child (b1-induction-tree-induction-hypothesis
                     induction (list (cons *library-x* tail) (cons *library-y* changed))
                     (list (list cons-test t))))
             (moved (proof-proof-modus-ponens proof (car child) member-tail))
             (good (b1-permutation-perm-adding-cons-consequence-branch
                    t lib other-member call-left call-right cons-proof mem-miss remove-miss
                    right-arg moved))
             (bad (b1-permutation-perm-adding-cons-consequence-branch
                   nil lib other-member call-left call-right cons-proof mem-miss remove-miss
                   right-arg moved))
             (remaining (proof-proof-cases proof other-member good bad))
             (cons-case (proof-proof-cases proof test yes remaining))
             (step (proof-proof-cases proof cons-test cons-case no)))
          (cons step (cdr child)))))))

(defun b1-permutation-perm-adding-cons (lib)
  (let* ((call-left (b1-permutation-call *b1-permutation-perm*
                       (list *library-x* (b1-permutation-call *proof-cons*
                                           (list *b1-permutation-a* *library-y*)))))
         (call-right (b1-permutation-call *b1-permutation-perm*
                        (list (b1-permutation-call *b1-permutation-rm*
                                (list *b1-permutation-a* *library-x*)) *library-y*)))
         (goal (proof-eq call-left call-right))
         (member (b1-permutation-call *b1-permutation-memb* (list *b1-permutation-a* *library-x*)))
         (formula (list *library-implies* member goal))
         (induction (b1-induction-tree-induction-init lib formula *library-x*))
         (cons-test (list *proof-consp* *library-x*))
         (head (list *library-car* *library-x*))
         (tail (list *library-cdr* *library-x*))
         (test (proof-eq *b1-permutation-a* head))
         (changed (b1-permutation-call *b1-permutation-rm* (list head *library-y*)))
         (other-member (b1-permutation-call *b1-permutation-memb* (list head *library-y*))))
    (proof-with-checked-results
        ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-permutation-perm-adding-cons-consequence
                       premise lib cons-test goal member test head tail changed other-member
                       call-left call-right induction))
         (proof (b1-logic-bookproof-prove-implication-with-premise
                 lib formula premise (car consequence)))
         (step (b1-induction-tree-induction-finish (cdr consequence) proof)))
      (library-library-lemma lib "PERM-CONS" formula step nil))))

(defun b1-permutation-perm-parts (lib premise cons-step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first premise))
         (parts (proof-list-of-length literal 3)))
      (let ((test (b1-permutation-call *b1-permutation-memb*
                    (list (list *library-car* (cadr parts)) (caddr parts)))))
        (proof-with-checked-results
            ((member (b1-logic-bookproof-forces lib test premise (list cons-step)
                                              (list *b1-permutation-perm*) nil))
             (opened (b1-permutation-opener lib literal (list cons-step member) nil))
             (child (proof-proof-rewrite proof premise opened '(1))))
          (list member child))))))

(defun b1-permutation-atom-of-perm (lib premise atom)
  (proof-with-checked-results
      ((term (proof-step-first premise))
       (opened (b1-permutation-opener lib term (list atom) nil)))
    (proof-proof-rewrite (library-library-proof lib) premise opened '(1))))

(defun b1-permutation-perm-symmetry-consequence (premise lib formula cons-test tail head induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((atom (proof-proof-assume proof cons-test nil))
         (goal (proof-term-at formula 2))
         (other-atom (b1-permutation-atom-of-perm lib premise atom))
         (no (b1-logic-bookproof-normalize-proof lib goal (list atom other-atom)
                                               (list *b1-permutation-perm* *proof-not*) nil nil))
         (yes (proof-proof-assume proof cons-test t))
         (parts (b1-permutation-perm-parts lib premise yes))
         (argument (b1-permutation-first-at (cadr parts) 2))
         (hypothesis (b1-induction-tree-induction-hypothesis
                      induction (list (cons *library-x* tail) (cons *library-y* argument))
                      (list (list cons-test t))))
         (swapped (proof-proof-modus-ponens proof (car hypothesis) (cadr parts)))
         (equation (b1-permutation-use-implication
                    lib "PERM-CONS" (list (cons *library-x* *library-y*)
                                          (cons *library-y* tail) (cons *b1-permutation-a* head))
                    (list (car parts))))
         (result (proof-proof-transport proof swapped equation))
         (elimination (library-library-axiom lib "CAR-CDR-ELIM" (list *library-x*)))
         (rebuilt (proof-proof-modus-ponens proof elimination yes))
         (result (proof-proof-rewrite proof result rebuilt '(1 2)))
         (step (proof-proof-cases proof cons-test result no)))
      (cons step (cdr hypothesis)))))

(defun b1-permutation-perm-symmetry (lib formula)
  (let* ((cons-test (list *proof-consp* *library-x*))
         (tail (list *library-cdr* *library-x*))
         (head (list *library-car* *library-x*))
         (induction (b1-induction-tree-induction-init lib formula *library-x*)))
    (proof-with-checked-results
        ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-permutation-perm-symmetry-consequence
                       premise lib formula cons-test tail head induction))
         (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car consequence))))
      (b1-induction-tree-induction-finish (cdr consequence) step))))

(defun b1-permutation-perm-member-consequence (premise lib cons-test goal member head tail induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
         (parts (proof-list-of-length conjuncts 2))
         (atom (proof-proof-assume proof cons-test nil))
         (opened (b1-permutation-opener lib member (list atom) nil))
         (no (b1-permutation-impossible lib goal (cadr parts) opened))
         (is-cons (proof-proof-assume proof cons-test t))
         (permutation (b1-permutation-perm-parts lib (car parts) is-cons)))
      (let ((test (proof-eq *b1-permutation-a* head)))
        (proof-with-checked-results
            ((hit (proof-proof-assume proof test t))
             (reversed (proof-proof-symmetric proof hit))
             (yes (proof-proof-rewrite proof (car permutation) reversed '(1 1)))
             (miss (proof-proof-assume proof test nil))
             (opened (b1-permutation-opener lib member (list is-cons miss) nil))
             (left (proof-proof-rewrite proof (cadr parts) opened '(1)))
             (argument (b1-permutation-first-at (cadr permutation) 2))
             (child (b1-induction-tree-induction-hypothesis
                     induction (list (cons *library-x* tail) (cons *library-y* argument))
                     (list (list cons-test t))))
             (test-term (b1-permutation-first-at (car child) 1))
             (condition (b1-logic-bookproof-normalize-proof lib test-term
                                                             (list (cadr permutation) left)
                                                             nil nil nil))
             (hypothesis (proof-proof-modus-ponens proof (car child) condition))
             (residue (b1-permutation-use-implication
                       lib "MEMB-RM" (list (cons *library-x* *library-y*)
                                          (cons *b1-permutation-a* *b1-permutation-a*)
                                          (cons *b1-permutation-b* head)) (list hypothesis)))
             (cons-case (proof-proof-cases proof test yes residue))
             (step (proof-proof-cases proof cons-test cons-case no)))
          (cons step (cdr child)))))))

(defun b1-permutation-perm-member (lib)
  (let* ((p (b1-permutation-call *b1-permutation-perm* (list *library-x* *library-y*)))
         (member (b1-permutation-call *b1-permutation-memb* (list *b1-permutation-a* *library-x*)))
         (goal (b1-permutation-call *b1-permutation-memb* (list *b1-permutation-a* *library-y*)))
         (formula (list *library-implies* (proof-ite p member *proof-false*) goal))
         (induction (b1-induction-tree-induction-init lib formula *library-x*))
         (cons-test (list *proof-consp* *library-x*))
         (head (list *library-car* *library-x*))
         (tail (list *library-cdr* *library-x*)))
    (proof-with-checked-results
        ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-permutation-perm-member-consequence
                       premise lib cons-test goal member head tail induction))
         (proof (b1-logic-bookproof-prove-implication-with-premise
                 lib formula premise (car consequence)))
         (step (b1-induction-tree-induction-finish (cdr consequence) proof)))
      (library-library-lemma lib "PERM-MEMB" formula step nil))))

(defun b1-permutation-perm-remove-consequence
    (premise lib goal cons-test head tail induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((atom (proof-proof-assume proof cons-test nil))
         (other-atom (b1-permutation-atom-of-perm lib premise atom))
         (left (proof-term-at goal 1))
         (opened-left (b1-permutation-opener lib left (list atom) nil))
         (right (proof-term-at goal 2))
         (opened-right (b1-permutation-opener lib right (list other-atom) nil))
         (no (b1-logic-bookproof-normalize-proof
              lib goal nil (list *b1-permutation-perm* *proof-not*)
              (b1-permutation-equation-rules (list opened-left opened-right)) nil))
         (is-cons (proof-proof-assume proof cons-test t))
         (parts (b1-permutation-perm-parts lib premise is-cons)))
      (let ((test (proof-eq *b1-permutation-a* head)))
        (proof-with-checked-results
            ((hit (proof-proof-assume proof test t))
             (miss (proof-proof-assume proof test nil))
             (remove (b1-permutation-opener lib left (list is-cons hit) nil))
             (changed (b1-conjunction-reduction-at lib right hit))
             (yes (b1-permutation-transfer lib goal (cadr parts) (list remove changed)))
             (remove (b1-permutation-opener lib left (list is-cons miss) nil))
             (reversed (b1-permutation-reversed-negative lib miss))
             (members (b1-permutation-use-implication
                       lib "MEMB-RM-DISJOINT" (list (cons *library-x* *library-y*)
                                                   (cons *b1-permutation-a* head)
                                                   (cons *b1-permutation-b* *b1-permutation-a*))
                       (list reversed)))
             (commute (proof-proof-fact
                       proof (proof-sym "SELF-RM-COMMUTES" "ACL2")
                       (list (list *library-x* *library-y*) (list *b1-permutation-a* head)
                             (list *b1-permutation-b* *b1-permutation-a*))))
             (opened (b1-permutation-opener lib goal (list (car parts))
                                            (list remove members commute)))
             (argument (b1-permutation-first-at (cadr parts) 2))
             (smaller (b1-induction-tree-induction-hypothesis
                       induction (list (cons *library-x* tail) (cons *library-y* argument))
                       (list (list cons-test t))))
             (result (proof-proof-modus-ponens proof (car smaller) (cadr parts)))
             (successor (proof-proof-transport proof result opened))
             (cons-case (proof-proof-cases proof test yes successor))
             (step (proof-proof-cases proof cons-test cons-case no)))
          (cons step (cdr smaller)))))))

(defun b1-permutation-perm-remove (lib)
  (let* ((goal (b1-permutation-call *b1-permutation-perm*
                  (list (b1-permutation-call *b1-permutation-rm* (list *b1-permutation-a* *library-x*))
                        (b1-permutation-call *b1-permutation-rm* (list *b1-permutation-a* *library-y*)))))
         (formula (list *library-implies*
                        (b1-permutation-call *b1-permutation-perm* (list *library-x* *library-y*)) goal))
         (cons-test (list *proof-consp* *library-x*))
         (head (list *library-car* *library-x*))
         (tail (list *library-cdr* *library-x*))
         (induction (b1-induction-tree-induction-init lib formula *library-x*)))
    (proof-with-checked-results
        ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-permutation-perm-remove-consequence
                       premise lib goal cons-test head tail induction))
         (proof (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car consequence)))
         (step (b1-induction-tree-induction-finish (cdr consequence) proof)))
      (library-library-lemma lib "PERM-RM" formula step nil))))

(defun b1-permutation-perm-transitivity-consequence
    (premise lib formula cons-test head tail induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
         (parts (proof-list-of-length conjuncts 2))
         (atom (proof-proof-assume proof cons-test nil))
         (middle (b1-permutation-atom-of-perm lib (car parts) atom))
         (last (b1-permutation-atom-of-perm lib (cadr parts) middle))
         (goal (proof-term-at formula 2))
         (no (b1-logic-bookproof-normalize-proof lib goal (list atom last)
                                               (list *b1-permutation-perm* *proof-not*) nil nil))
         (is-cons (proof-proof-assume proof cons-test t))
         (permutation (b1-permutation-perm-parts lib (car parts) is-cons)))
      (let ((bindings (list (cons *library-x* *library-y*) (cons *library-y* *library-z*)
                            (cons *b1-permutation-a* head))))
        (proof-with-checked-results
            ((member-z (b1-permutation-use-implication lib "PERM-MEMB" bindings
                                                       (list (cadr parts) (car permutation))))
             (removed (b1-permutation-use-implication lib "PERM-RM" bindings (list (cadr parts))))
             (child-argument (b1-permutation-first-at (cadr permutation) 2))
             (removed-argument (b1-permutation-first-at removed 2))
             (smaller (b1-induction-tree-induction-hypothesis
                       induction (list (cons *library-x* tail) (cons *library-y* child-argument)
                                       (cons *library-z* removed-argument)) (list (list cons-test t))))
             (test (b1-permutation-first-at (car smaller) 1))
             (condition (b1-logic-bookproof-normalize-proof lib test
                                                             (list (cadr permutation) removed) nil nil nil))
             (result (proof-proof-modus-ponens proof (car smaller) condition))
             (opened (b1-permutation-opener lib goal (list is-cons member-z) nil))
             (yes (proof-proof-transport proof result opened))
             (step (proof-proof-cases proof cons-test yes no)))
          (cons step (cdr smaller)))))))

(defun b1-permutation-perm-transitivity (lib formula)
  (let* ((cons-test (list *proof-consp* *library-x*))
         (head (list *library-car* *library-x*))
         (tail (list *library-cdr* *library-x*))
         (induction (b1-induction-tree-induction-init lib formula *library-x*)))
    (proof-with-checked-results
        ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-permutation-perm-transitivity-consequence
                       premise lib formula cons-test head tail induction))
         (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car consequence))))
      (b1-induction-tree-induction-finish (cdr consequence) step))))

(defun b1-permutation-perm-reflexivity (lib formula)
  (let* ((proof (library-library-proof lib))
         (induction (b1-induction-tree-induction-init lib formula *library-x*))
         (cons-test (list *proof-consp* *library-x*))
         (head (list *library-car* *library-x*))
         (tail (list *library-cdr* *library-x*)))
    (proof-with-checked-results
        ((yes (proof-proof-assume proof cons-test t))
         (member (b1-logic-bookproof-normalize-proof
                  lib (b1-permutation-call *b1-permutation-memb* (list head *library-x*))
                  (list yes) (list *b1-permutation-memb*) nil nil))
         (removal (b1-permutation-opener
                   lib (b1-permutation-call *b1-permutation-rm* (list head *library-x*)) (list yes) nil))
         (smaller (b1-induction-tree-induction-hypothesis
                   induction (list (cons *library-x* tail)) (list (list cons-test t))))
         (opened (b1-permutation-opener lib formula (list yes member) (list removal)))
         (result (proof-proof-transport proof (car smaller) opened))
         (atom (proof-proof-assume proof cons-test nil))
         (no (b1-logic-bookproof-normalize-proof lib formula (list atom)
                                               (list *b1-permutation-perm* *proof-not*) nil nil))
         (step (proof-proof-cases proof cons-test result no)))
      (b1-induction-tree-induction-finish (cdr smaller) step))))

(defun b1-permutation-perm-boolean-base
    (holds lib p atom right true-boolean false-boolean)
  (proof-with-checked-results
      ((assumed (proof-proof-assume (library-library-proof lib) right holds))
       (reduction (b1-logic-bookproof-normalize
                   lib p (list atom assumed) (list *b1-permutation-perm* *proof-not*) nil nil nil nil)))
    (library-library-transport-argument lib (if holds false-boolean true-boolean) reduction 1)))

(defun b1-permutation-perm-boolean (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((p (proof-term-at formula 1)))
      (let* ((cons-test (list *proof-consp* *library-x*))
             (head (list *library-car* *library-x*))
             (tail (list *library-cdr* *library-x*))
             (test (b1-permutation-call *b1-permutation-memb* (list head *library-y*)))
             (induction (b1-induction-tree-induction-init lib formula *library-x*))
             (unfold (list *b1-permutation-booleanp* *b1-logic-eq*)))
        (proof-with-checked-results
            ((true-boolean (b1-logic-bookproof-normalize-proof
                            lib (list *b1-permutation-booleanp* *proof-true*) nil unfold nil nil))
             (false-boolean (b1-logic-bookproof-normalize-proof
                             lib (list *b1-permutation-booleanp* *proof-false*) nil unfold nil nil))
             (parts (if (integerp p)
                        '(:failure "failure" "")
                      (proof-list-of-length (cdr p) 2))))
          (let ((right (list *proof-consp* (cadr parts))))
            (proof-with-checked-results
                ((atom (proof-proof-assume proof cons-test nil))
                 (base-yes (b1-permutation-perm-boolean-base t lib p atom right true-boolean false-boolean))
                 (base-no (b1-permutation-perm-boolean-base nil lib p atom right true-boolean false-boolean))
                 (no (proof-proof-cases proof right base-yes base-no))
                 (is-cons (proof-proof-assume proof cons-test t))
                 (hit (proof-proof-assume proof test t))
                 (success (b1-permutation-opener lib p (list is-cons hit) nil))
                 (descendant (b1-permutation-first-at success 2))
                 (argument (proof-term-at descendant 2))
                 (smaller (b1-induction-tree-induction-hypothesis
                           induction (list (cons *library-x* tail) (cons *library-y* argument))
                           (list (list cons-test t))))
                 (good (library-library-transport-argument lib (car smaller) success 1))
                 (miss (proof-proof-assume proof test nil))
                 (failure (b1-permutation-opener lib p (list is-cons miss) nil))
                 (bad (library-library-transport-argument lib false-boolean failure 1))
                 (yes (proof-proof-cases proof test good bad))
                 (step (proof-proof-cases proof cons-test yes no)))
              (b1-induction-tree-induction-finish (cdr smaller) step))))))))

(defun b1-permutation-permutation-is-equivalence (lib formula)
  (proof-with-checked-results
      ((lib (b1-permutation-member-after-removal lib nil))
       (lib (b1-permutation-member-after-removal lib t))
       (lib (b1-permutation-removal-order lib))
       (lib (b1-permutation-perm-adding-cons lib))
       (lib (b1-permutation-perm-member lib))
       (lib (b1-permutation-perm-remove lib))
       (first (proof-term-at formula 1))
       (rest (proof-term-at formula 2))
       (second (proof-term-at rest 1))
       (rest (proof-term-at rest 2))
       (third (proof-term-at rest 1))
       (fourth (proof-term-at rest 2))
       (boolean (b1-permutation-perm-boolean lib first))
       (reflexive (b1-permutation-perm-reflexivity lib second))
       (symmetric (b1-permutation-perm-symmetry lib third))
       (transitive (b1-permutation-perm-transitivity lib fourth))
       (step (b1-logic-bookproof-normalize-proof lib formula
                                                (list boolean reflexive symmetric transitive) nil nil nil)))
    (cons step lib)))
