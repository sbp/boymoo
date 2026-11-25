(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h4-book-folds-value (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun h4-book-folds-empty-lookup-reduce (test p call)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((selected (h4-book-updates-select-result p call test))
         (value (h4-book-folds-value selected))
         (reduced (h4-tactics-tactics-normalize p value nil nil nil nil)))
      (proof-proof-chain proof selected (list reduced)))))

(defun h4-book-folds-empty-lookup-recurse (test p call goal replacement)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((value (h4-book-folds-empty-lookup-reduce test p call))
         (builtin (library-library-builtin p 9 *library-x*))
         (descent (proof-proof-discharge proof builtin test))
         (decrease (proof-step-first descent))
         (child (proof-subst goal (list (cons (caar replacement)
                                             (cadar replacement)))))
         (assumption (proof-proof-assume proof (proof-ite decrease child *proof-true*) t))
         (induction (proof-proof-prove-if proof assumption descent)))
      (proof-proof-chain proof value (list induction)))))

(defun h4-book-folds-empty-lookup (p function)
  (let* ((proof (library-library-proof p))
         (call (list function *library-x* *proof-false*))
         (goal (proof-eq call *proof-false*))
         (branch (list *h4-book-arithmetic-zp* *library-x*))
         (replacement (list (list *library-x*
                                  (h4-book-arithmetic-predecessor *library-x*)))))
    (proof-with-checked-results
        ((stop (proof-proof-assume proof branch t))
         (yes (h4-book-folds-empty-lookup-reduce stop p call))
         (active (proof-proof-assume proof branch nil))
         (no (h4-book-folds-empty-lookup-recurse active p call goal replacement))
         (cases (h4-tactics-tactics-case-of p goal branch yes no))
         (ordinal (library-library-builtin p 1 *library-x*)))
      (proof-proof-induct proof ordinal cases goal (list *library-count* *library-x*)
                          (list replacement)))))

(defun h4-book-folds-false-on-empty-state-leaf (value tests p)
  (declare (xargs :measure (acl2-count tests)))
  (let ((proof (library-library-proof p)))
    (cond
     ((equal value *proof-false*) (proof-proof-reflexive proof *proof-false*))
     ((endp tests) '(:failure "inapplicable-step" ""))
     (t
      (let ((test (caar tests)))
        (if (and (cadar tests) (proof-is-call test *proof-consp*))
            (proof-with-checked-results ((lookup (proof-term-at test 1)))
              (if (and (proof-compound lookup)
                       (equal (len lookup) 3)
                       (equal (caddr lookup) *proof-false*)
                       (assoc-equal (car lookup) (proof-proof-definitions proof)))
                  (proof-with-checked-results
                      ((theorem (h4-book-folds-empty-lookup p (car lookup)))
                       (absent (proof-proof-instantiate
                                proof theorem (list (list *library-x* (cadr lookup)))))
                       (assumption (proof-proof-assume proof test t))
                       (impossible (proof-proof-rewrite proof assumption absent '(1 1)))
                       (computed (proof-proof-compute
                                  proof (list *proof-consp* *proof-false*) *proof-nil*))
                       (contradiction (proof-proof-rewrite proof impossible computed '(1))))
                    (proof-proof-subsume
                     proof contradiction (cons (proof-eq value *proof-false*)
                                               (cdr (proof-step-clause contradiction)))))
                (h4-book-folds-false-on-empty-state-leaf value (cdr tests) p)))
          (h4-book-folds-false-on-empty-state-leaf value (cdr tests) p)))))))

(defun h4-book-folds-false-on-empty-state-visit (n proof value template tests p)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h4-book-folds-false-on-empty-state-visit"))
   ((proof-is-call value *proof-if*)
    (proof-with-checked-results
        ((parts (proof-list-of-length (cdr value) 3))
         (yes (h4-book-folds-false-on-empty-state-visit
               (1- n) proof (cadr parts) template (append tests (list (list (car parts) t))) p))
         (no (h4-book-folds-false-on-empty-state-visit
              (1- n) proof (caddr parts) template (append tests (list (list (car parts) nil))) p))
         (if-true (proof-proof-if-true proof value))
         (true-equality (proof-proof-symmetric proof if-true))
         (yes-proof (proof-proof-rewrite-result proof yes true-equality template *proof-result*))
         (if-false (proof-proof-if-false proof value))
         (false-equality (proof-proof-symmetric proof if-false))
         (no-proof (proof-proof-rewrite-result proof no false-equality template *proof-result*)))
      (proof-proof-cases proof (car parts) yes-proof no-proof)))
   ((and (proof-compound value) (not (consp value)))
    (proof-term-at value 0))
   ((and (proof-compound value) (proof-compound (car value)))
    (proof-with-checked-results
        ((equality (proof-proof-beta proof value))
         (opened (h4-book-folds-value equality))
         (step (h4-book-folds-false-on-empty-state-visit (1- n) proof opened template tests p))
         (reversed (proof-proof-symmetric proof equality)))
      (proof-proof-rewrite-result proof step reversed template *proof-result*)))
   (t (proof-with-checked-results
          ((step (h4-book-folds-false-on-empty-state-leaf value tests p))
           (first (proof-step-first step))
           (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal first target) step '(:failure "inapplicable-step" ""))))))

(defun h4-book-folds-false-on-empty-state (p condition)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof condition))
         (result (h4-book-folds-value opened))
         (value (h4-book-folds-false-on-empty-state-visit
                 1000000 proof result (proof-eq *proof-result* *proof-false*) nil p)))
      (proof-proof-chain proof opened (list value)))))

(defun h4-book-folds-fold-empty-state-no-move (shape p call)
  (h4-book-updates-select-result p call shape))

(defun h4-book-folds-fold-empty-state-move (shape p call)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (h4-book-updates-select-result p call shape))
         (value (h4-book-folds-value opened)))
      (if (not (proof-is-call value *proof-if*))
          '(:failure "inapplicable-step" "")
        (proof-with-checked-results
            ((condition (proof-term-at value 1))
             (illegal (h4-book-folds-false-on-empty-state p condition))
             (normalized (proof-proof-rewrite proof opened illegal '(1 2 1)))
             (reduced (h4-book-folds-value normalized))
             (selected (h4-tactics-tactics-select-literal p reduced)))
          (proof-proof-chain proof normalized (list selected)))))))

(defun h4-book-folds-fold-empty-state (p function sequence)
  (let* ((proof (library-library-proof p))
         (call (list function sequence *proof-false*))
         (goal (proof-eq call *proof-false*))
         (test (list *proof-consp* sequence)))
    (proof-with-checked-results
        ((pair (proof-proof-assume proof test t))
         (yes (h4-book-folds-fold-empty-state-move pair p call))
         (atom-case (proof-proof-assume proof test nil))
         (no (h4-book-folds-fold-empty-state-no-move atom-case p call)))
      (h4-tactics-tactics-case-of p goal test yes no))))

(defun h4-book-folds-fold-shape-control (body formals left initial-state)
  (and (equal (len formals) 2)
       (proof-is-call body *proof-if*)
       (proof-with-checked-results ((test (proof-term-at body 1)))
         (and (equal test (list *proof-consp* (car formals)))
              (proof-with-checked-results ((inactive (proof-term-at body 3)))
                (and (equal inactive (cadr formals))
                     (proof-subst (caddr body)
                                  (table-put (list (cons (car formals) left))
                                               (cadr formals) initial-state))))))))

(defun h4-book-folds-fold-shape-transition (control function left)
  (and (proof-is-call control *proof-if*)
       (proof-with-checked-results ((stopped (proof-term-at control 3)))
         (and (equal stopped *proof-false*)
              (proof-is-call (caddr control) function)
              (proof-with-checked-results ((remaining (proof-term-at (caddr control) 1)))
                (and (equal remaining (list *library-cdr* left))
                     (proof-with-checked-results ((transition (proof-term-at (caddr control) 2)))
                       (list (cadr control) transition))))))))

(defun h4-book-folds-fold-shape (p formula)
  (and (proof-is-call formula *proof-equal*)
    (proof-with-checked-results ((sides (proof-list-of-length (cdr formula) 2)))
      (let ((first (car sides)) (last (cadr sides)))
        (and (proof-compound first) (equal (len first) 3)
             (not (proof-compound (car first)))
             (let* ((function (car first))
                    (definitions (proof-proof-definitions (library-library-proof p)))
                    (definition (assoc-equal function definitions))
                    (operations (cadr first))
                    (initial-state (caddr first)))
               (and definition
                    (proof-compound operations) (equal (len operations) 3)
                    (not (proof-compound (car operations))) (assoc-equal (car operations) definitions)
                    (let ((left (cadr operations)) (right (caddr operations)))
                      (and (not (proof-compound left)) (not (proof-compound initial-state))
                           (not (equal left initial-state))
                           (equal last (list function right (list function left initial-state)))
                           (proof-with-checked-results
                               ((parts (proof-list-of-length (cdr definition) 2))
                                (control (h4-book-folds-fold-shape-control
                                          (cadr parts) (car parts) left initial-state))
                                (transition (h4-book-folds-fold-shape-transition control function left)))
                             (and transition (list* function operations left right initial-state transition))))))))))))

(defun h4-book-folds-compose-fold-outer (shape p left function operations first initial-state)
  (proof-with-checked-results
      ((appended (h4-book-flatten-unfold-on-list p operations first shape))
       (unfolded (h4-book-flatten-rewrite-argument p left 1 appended))
       (prior (h4-book-flatten-unfold-on-list p (list function first initial-state) first shape))
       (sequence (h4-book-folds-value appended)))
    (list unfolded sequence prior)))

(defun h4-book-folds-compose-fold-stop (shape p left right function operations first initial-state)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((outer (h4-book-folds-compose-fold-outer shape p left function operations first initial-state))
         (prior (h4-book-flatten-rewrite-argument p right 2 (caddr outer)))
         (reversed (proof-proof-symmetric proof prior)))
      (proof-proof-chain proof (car outer) (list reversed)))))

(defun h4-book-folds-compose-fold-continue--choose
    (test p first-fold provider prior right condition induction failure)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((value (h4-book-folds-value first-fold))
         (selected (proof-proof-select proof value test))
         (before (proof-proof-chain proof first-fold (list selected)))
         (value (h4-book-folds-value before))
         (reduced (h4-tactics-tactics-normalize p value nil nil nil provider))
         (before (proof-proof-chain proof before (list reduced)))
         (value (h4-book-folds-value prior))
         (selected (proof-proof-select proof value test))
         (prior-branch (proof-proof-chain proof prior (list selected)))
         (after (h4-book-flatten-rewrite-argument p right 2 prior-branch))
         (test-literal (proof-step-first test))
         (middle (if (equal test-literal condition) induction
                   (proof-proof-symmetric proof failure)))
         (reversed (proof-proof-symmetric proof after)))
      (proof-proof-chain proof before (list middle reversed)))))

(defun h4-book-folds-compose-fold-continue-
    (shape induction p formula left right function operations first initial-state provider condition failure)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((outer (h4-book-folds-compose-fold-outer shape p left function operations first initial-state))
         (value (h4-book-folds-value (car outer)))
         (unfolded (h4-book-flatten-unfold-on-list p value (cadr outer) nil))
         (first-fold (proof-proof-chain proof (car outer) (list unfolded)))
         (active (proof-proof-assume proof condition t))
         (yes (h4-book-folds-compose-fold-continue--choose
               active p first-fold provider (caddr outer) right condition induction failure))
         (inactive (proof-proof-assume proof condition nil))
         (no (h4-book-folds-compose-fold-continue--choose
              inactive p first-fold provider (caddr outer) right condition induction failure)))
      (h4-tactics-tactics-case-of p formula condition yes no))))

(defun h4-book-folds-compose-fold (p formula function operations first last initial-state condition transition)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((sides (proof-list-of-length (cdr formula) 2))
         (provider (h4-book-finite-reduction-provider p))
         (empty (h4-book-folds-fold-empty-state p function *library-x*))
         (failure (proof-proof-instantiate proof empty (list (list *library-x* last)))))
      (let ((test (list *proof-consp* first))
            (changes (list (list initial-state transition))))
        (proof-with-checked-results
            ((pair (proof-proof-assume proof test t))
             (induction (h4-book-flatten-cdr-induction-recurse pair p formula first changes))
             (step (h4-book-folds-compose-fold-continue-
                    pair induction p formula (car sides) (cadr sides) function operations
                    first initial-state provider condition failure))
             (atom-case (proof-proof-assume proof test nil))
             (base (h4-book-folds-compose-fold-stop atom-case p (car sides) (cadr sides)
                                                    function operations first initial-state)))
          (h4-book-flatten-cdr-induction p formula first base step changes))))))

(defun h4-book-folds-fold-proof (p formula)
  (proof-with-checked-results ((plan (h4-book-folds-fold-shape p formula)))
    (and plan
      (let ((result (h4-book-folds-compose-fold p formula (nth 0 plan) (nth 1 plan)
                                                 (nth 2 plan) (nth 3 plan) (nth 4 plan)
                                                 (nth 5 plan) (nth 6 plan))))
        (if (and (failure-p result)
                 (member-equal (cadr result)
                               '("inapplicable-step" "inapplicable-term" "assertion" "value")))
            nil
          result)))))
