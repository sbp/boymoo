(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-removal-ev* (proof-sym "REMOVE-HYP-EV" "ACL2"))
(defconst *b2-removal-disjoin* (proof-sym "DISJOIN" "ACL2"))
(defconst *b2-removal-disjoin2* (proof-sym "DISJOIN2" "ACL2"))
(defconst *b2-removal-conjoin-clauses* (proof-sym "CONJOIN-CLAUSES" "ACL2"))
(defconst *b2-removal-remove* (proof-sym "REMOVE-EQUAL" "ACL2"))
(defconst *b2-removal-a* (proof-sym "A" "ACL2"))
(defconst *b2-removal-quoted-true* (proof-quote (list *proof-quote* *proof-t*)))
(defconst *b2-removal-quoted-false* (proof-quote (list *proof-quote* *proof-nil*)))

(defun b2-removal-evaluated (term env)
  (list *b2-removal-ev* term env))

(defun b2-removal-truth (term)
  (proof-ite term *proof-true* *proof-false*))

(defun b2-removal-first (step)
  (if (null step)
      '(:failure "failure" "")
    (proof-step-first step)))

(defun b2-removal-right (step)
  (proof-with-checked-results ((first (b2-removal-first step)))
    (proof-term-at first 2)))

(defun b2-removal-quote-evaluates (library term env)
  (let ((goal (proof-eq (b2-removal-evaluated term env)
                        (b2-tactics-field (list *library-cdr* term) 0)))
        (proof (library-library-proof library)))
    (proof-with-checked-results
        ((known (b2-tactics-tactics-use-fact
                 library (proof-sym "REMOVE-HYP-EV-CONSTRAINT-2" "ACL2")
                 goal nil nil nil 0 nil))
         (rhs (b2-removal-right known))
         (normalized (b2-tactics-tactics-normalize library rhs nil nil nil 1500 nil)))
      (proof-proof-chain proof known (list normalized)))))

(defun b2-removal-tests-request-p (result)
  (eq (car result) :b2-removal-tests-request))

(defun b2-removal-tests-visit (library conditions replies evidence)
  (declare (xargs :measure (acl2-count conditions)))
  (if (endp conditions)
      (if (endp replies)
          (list :b2-removal-tests-request evidence library)
        (proof-with-checked-results ((reply (car replies)))
          (list (car reply) (cdr reply) (cdr replies))))
    (let ((test (car conditions))
          (rest (cdr conditions)))
      (proof-with-checked-results
          ((assumed (proof-proof-assume (library-library-proof library) test t))
           (yes (b2-removal-tests-visit
                 library rest replies (append evidence (list assumed)))))
        (if (b2-removal-tests-request-p yes)
            yes
          (let ((library (cadr yes)))
            (proof-with-checked-results
                ((assumed (proof-proof-assume (library-library-proof library) test nil))
                 (no (b2-removal-tests-visit
                      library rest (caddr yes) (append evidence (list assumed)))))
              (if (b2-removal-tests-request-p no)
                  no
                (proof-with-checked-results
                    ((step (proof-proof-cases (library-library-proof (cadr no))
                                             test (car yes) (car no))))
                  (list step (cadr no) (caddr no)))))))))))

(defun b2-removal-tests (library conditions prove evidence)
  (proof-with-checked-results
      ((result (b2-removal-tests-visit library conditions prove evidence)))
    (if (b2-removal-tests-request-p result)
        result
      (cons (car result) (cadr result)))))

(defun b2-removal-solve-tests (n library conditions replies goal evidence unfold rules)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "b2-removal-solve-tests")
    (proof-with-checked-results
        ((result (b2-removal-tests library conditions replies nil)))
      (if (b2-removal-tests-request-p result)
          (let ((current (caddr result)))
            (proof-with-checked-results
                ((reply (b2-tactics-tactics-solve
                         current goal (append evidence (cadr result)) unfold rules 0 nil)))
              (b2-removal-solve-tests
               (1- n) library conditions (append replies (list (cons reply current)))
               goal evidence unfold rules)))
        (car result)))))

(defun b2-removal-assumptions (proof signed)
  (if (endp signed)
      nil
    (proof-with-checked-results
        ((condition (proof-list-of-length (car signed) 2))
         (step (proof-proof-assume proof (car condition) (cadr condition)))
         (rest (b2-removal-assumptions proof (cdr signed))))
      (cons step rest))))

(defun b2-removal-disjoin-pair-known (proof evidence true false known)
  (if (endp evidence)
      known
    (proof-with-checked-results ((literal (b2-removal-first (car evidence))))
      (if (member-equal literal
                        (list (proof-eq *library-x* *b2-removal-quoted-true*)
                              (proof-eq *library-y* *b2-removal-quoted-true*)
                              (proof-eq *library-x* *b2-removal-quoted-false*)
                              (proof-eq *library-y* *b2-removal-quoted-false*)))
          (let ((is-true (equal (caddr literal) *b2-removal-quoted-true*)))
            (proof-with-checked-results
                ((reverse (proof-proof-symmetric proof (car evidence)))
                 (equation (proof-proof-rewrite proof (if is-true true false) reverse '(1 1 1)))
                 (result
                  (if is-true
                      (proof-proof-true-from-eq proof equation)
                    (proof-with-checked-results
                        ((not-nil (proof-proof-not-nil proof))
                         (reversed (proof-proof-symmetric proof equation))
                         (rewritten (proof-proof-rewrite proof not-nil reversed '(1 1))))
                      (proof-proof-tidy proof rewritten)))))
              (b2-removal-disjoin-pair-known
               proof (cdr evidence) true false
               (table-put known (b2-removal-evaluated (cadr literal) *b2-removal-a*) result))))
        (b2-removal-disjoin-pair-known proof (cdr evidence) true false known)))))

(defun b2-removal-disjoin-pair-rules (library value true false)
  (if (member-equal value (list *library-x* *library-y*
                               *b2-removal-quoted-true* *b2-removal-quoted-false*))
      (list true false)
    (let* ((args (list *library-cdr* value))
           (target
            (proof-eq (b2-removal-evaluated value *b2-removal-a*)
                      (proof-ite (b2-removal-evaluated (b2-tactics-field args 0) *b2-removal-a*)
                                 (b2-removal-evaluated (b2-tactics-field args 1) *b2-removal-a*)
                                 (b2-removal-evaluated (b2-tactics-field args 2) *b2-removal-a*)))))
      (proof-with-checked-results
          ((step (b2-tactics-tactics-use-fact
                  library (proof-sym "REMOVE-HYP-EV-CONSTRAINT-8" "ACL2")
                  target nil nil nil 0 nil)))
        (list true false step)))))

(defun b2-removal-disjoin-pair-leaf (value signed library template true false)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((evidence (b2-removal-assumptions proof signed))
         (rhs (proof-term-at template 2))
         (goal (proof-eq (b2-removal-truth (b2-removal-evaluated value *b2-removal-a*)) rhs))
         (known (b2-removal-disjoin-pair-known proof evidence true false nil))
         (rules (b2-removal-disjoin-pair-rules library value true false)))
      (let* ((x (b2-removal-evaluated *library-x* *b2-removal-a*))
             (y (b2-removal-evaluated *library-y* *b2-removal-a*))
             (remaining (append (if (assoc-equal x known) nil (list x))
                                (if (assoc-equal y known) nil (list y)))))
        (b2-removal-solve-tests 1000000 library remaining nil goal
                                (append evidence (table-values known)) nil rules)))))

(defun b2-removal-disjoin-pair-by-value (n library value template true false signed)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof library)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "b2-removal-disjoin-pair-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((parts (proof-list-of-length (cdr value) 3))
           (test (car parts))
           (yes (b2-removal-disjoin-pair-by-value
                 (1- n) library (cadr parts) template true false
                 (append signed (list (list test t)))))
           (no (b2-removal-disjoin-pair-by-value
                (1- n) library (caddr parts) template true false
                (append signed (list (list test nil))))))
        (proof-by-value-join proof value template yes no)))
     ((and (proof-compound value) (endp value))
      '(:failure "tactic-rejected" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (opened (b2-removal-right equality))
           (step (b2-removal-disjoin-pair-by-value
                  (1- n) library opened template true false signed))
           (reverse (proof-proof-symmetric proof equality)))
        (proof-proof-rewrite-result proof step reverse template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (b2-removal-disjoin-pair-leaf value signed library template true false))
           (first (b2-removal-first step))
           (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal first target) step '(:failure "tactic-rejected" "")))))))

(defun b2-removal-disjoin-pair (library)
  (let ((name (proof-sym "B2-DISJOIN-PAIR" "ACL2"))
        (proof (library-library-proof library)))
    (if (assoc-equal name (proof-proof-facts proof))
        (cons name library)
      (let* ((pair (list *b2-removal-disjoin2* *library-x* *library-y*))
             (template
              (proof-eq (b2-removal-truth (b2-removal-evaluated *proof-result* *b2-removal-a*))
                        (proof-ite (b2-removal-evaluated *library-x* *b2-removal-a*)
                                   *proof-true*
                                   (b2-removal-truth
                                    (b2-removal-evaluated *library-y* *b2-removal-a*))))))
        (proof-with-checked-results
            ((opened (proof-proof-unfold proof pair))
             (true (b2-removal-quote-evaluates library *b2-removal-quoted-true* *b2-removal-a*))
             (false (b2-removal-quote-evaluates library *b2-removal-quoted-false* *b2-removal-a*))
             (body (b2-removal-right opened))
             (step (b2-removal-disjoin-pair-by-value 1000000 library body template true false nil))
             (reverse (proof-proof-symmetric proof opened))
             (result (proof-proof-rewrite-result proof step reverse template *proof-result*)))
          (b2-tactics-tactics-add-lemma library "DISJOIN-PAIR" result :none))))))

(defun b2-removal-disjoin-truth-install (library)
  (proof-with-checked-results ((pair (b2-removal-disjoin-pair library)))
    (let* ((library (cdr pair))
           (proof (library-library-proof library))
           (main (list *b2-removal-disjoin* *library-x*))
           (head (list *library-car* *library-x*))
           (tail (list *library-cdr* *library-x*))
           (main-tail (list *b2-removal-disjoin* tail))
           (a (b2-removal-evaluated head *b2-removal-a*))
           (b (b2-removal-evaluated main-tail *b2-removal-a*))
           (test (list *proof-consp* *library-x*))
           (next-test (list *proof-consp* tail))
           (target (proof-eq (b2-removal-truth (b2-removal-evaluated main *b2-removal-a*))
                             (proof-ite test (proof-ite a *proof-true* (b2-removal-truth b))
                                        *proof-false*))))
      (proof-with-checked-results
          ((yes (proof-proof-assume proof test t))
           (no (proof-proof-assume proof test nil))
           (more (proof-proof-assume proof next-test t))
           (last (proof-proof-assume proof next-test nil))
           (nonempty (b2-tactics-tactics-normalize library main (list yes more)
                                                  (list main) nil 1500 nil))
           (law (proof-proof-fact proof (car pair)
                                  (list (list *library-x* head) (list *library-y* main-tail))))
           (reverse (if nonempty (proof-proof-symmetric proof nonempty)
                      (b2-removal-first nonempty)))
           (two (proof-proof-rewrite-first proof law reverse))
           (selected (proof-proof-select proof (caddr target) yes))
           (reverse (proof-proof-symmetric proof selected))
           (two (proof-proof-rewrite proof two reverse '(1 2)))
           (two (proof-proof-tidy proof two))
           (empty-quote (b2-removal-quote-evaluates library *b2-removal-quoted-false* *b2-removal-a*))
           (empty (b2-tactics-tactics-solve library target (list no) (list main)
                                          (list empty-quote) 0 nil))
           (single (b2-removal-solve-tests 1000000 library (list a) nil target
                                          (list yes last) (list main main-tail) (list empty-quote)))
           (nonempty-case (proof-proof-cases proof next-test two single))
           (step (proof-proof-cases proof test nonempty-case empty)))
        (b2-tactics-tactics-add-lemma library "DISJOIN-TRUTH" step :none)))))

(defun b2-removal-disjoin-truth (library lst env)
  (let* ((label (proof-sym "B2-DISJOIN-TRUTH" "ACL2"))
         (proof (library-library-proof library)))
    (proof-with-checked-results
        ((installed (if (assoc-equal label (proof-proof-facts proof))
                        (cons label library)
                      (b2-removal-disjoin-truth-install library)))
         (library (cdr installed))
         (step (proof-proof-fact (library-library-proof library) label
                                 (list (list *library-x* lst) (list *b2-removal-a* env)))))
      (cons step library))))

(defun b2-removal-conjoin-single (library lst)
  (let* ((label (proof-sym "B2-CONJOIN-SINGLE" "ACL2"))
         (proof (library-library-proof library)))
    (proof-with-checked-results
        ((installed
          (if (assoc-equal label (proof-proof-facts proof))
              (cons label library)
            (let ((goal (proof-eq (list *b2-removal-conjoin-clauses*
                                       (list *proof-cons* *library-x* *proof-false*))
                                  (list *b2-removal-disjoin* *library-x*))))
              (proof-with-checked-results
                  ((step (b2-tactics-tactics-solve
                          library goal nil
                          (list *b2-removal-conjoin-clauses* (proof-sym "CONJOIN" "ACL2")
                                (proof-sym "DISJOIN-LST" "ACL2"))
                          nil 0 nil)))
                (b2-tactics-tactics-add-lemma library "CONJOIN-SINGLE" step :none)))))
         (library (cdr installed))
         (step (proof-proof-fact (library-library-proof library) label
                                 (list (list *library-x* lst)))))
      (cons step library))))

(defun b2-removal-correctness (evidence)
  (if (endp evidence)
      '(:failure "failure" "")
    (proof-with-checked-results ((head (proof-term-at (caar evidence) 0)))
      (if (equal head *b2-removal-ev*)
          (cdar evidence)
        (b2-removal-correctness (cdr evidence))))))

(defun b2-removal-first-hypothesis-branch
    (library branch shorter needs-head correctness processor lst env conclusion)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((opened (b2-tactics-tactics-normalize library processor (list branch)
                                               (list processor) nil 1500 nil))
         (reduced (if opened (proof-proof-rewrite-first proof correctness opened)
                    (b2-removal-first opened)))
         (single (b2-removal-conjoin-single library shorter))
         (library (cdr single))
         (proof (library-library-proof library))
         (reduced (proof-proof-rewrite-first proof reduced (car single))))
      (if (not needs-head)
          (cons reduced library)
        (proof-with-checked-results
            ((semantic (b2-removal-disjoin-truth library lst env))
             (library (cdr semantic))
             (head (b2-removal-evaluated (list *library-car* lst) env))
             (goal (b2-removal-truth conclusion))
             (from-tail (b2-removal-solve-tests 1000000 library (list head) nil goal
                                                 (list branch reduced) nil (list (car semantic))))
             (parts (proof-proof-conjunct (library-library-proof library) from-tail)))
          (cons (car parts) library))))))

(defun b2-removal-first-hypothesis-consequent (assumption library lst env conclusion test yes no)
  (proof-with-checked-results
      ((evidence (b2-tactics-tactics-evidence library (list assumption)))
       (correctness (b2-removal-correctness evidence))
       (first (b2-removal-first correctness))
       (application (proof-term-at first 1))
       (processor (proof-term-at application 1))
       (yes-proof (b2-removal-first-hypothesis-branch
                   library yes (list *library-cdr* lst) t correctness processor lst env conclusion))
       (no-proof (b2-removal-first-hypothesis-branch
                  (cdr yes-proof) no lst nil correctness processor lst env conclusion))
       (library (cdr no-proof))
       (step (proof-proof-cases (library-library-proof library)
                                test (car yes-proof) (car no-proof))))
    (cons step library)))

(defun b2-removal-first-hypothesis (library formula)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (premise (cadr parts))
         (conclusion (caddr parts))
         (shape (proof-list-of-length conclusion 3))
         (call (proof-list-of-length (cadr shape) 2))
         (lst (cadr call))
         (env (caddr shape))
         (test (list *proof-consp* lst))
         (yes (proof-proof-assume proof test t))
         (no (proof-proof-assume proof test nil))
         (request (b2-tactics-tactics-implication library premise conclusion nil))
         (reply (b2-removal-first-hypothesis-consequent
                 (nth 3 (car request)) (cdr request) lst env conclusion test yes no)))
      (b2-tactics-tactics-implication library premise conclusion reply))))

(defun b2-removal-denied-terms (library premise source env cons-step)
  (proof-with-checked-results
      ((law (b2-removal-disjoin-truth library source env))
       (library (cdr law))
       (proof (library-library-proof library))
       (literal (b2-removal-first premise))
       (evaluated-main (proof-term-at literal 1))
       (denied (b2-tactics-tactics-solve
                library (proof-neg (b2-removal-truth evaluated-main)) (list premise) nil nil 0 nil))
       (denied (proof-proof-rewrite-first proof denied (car law)))
       (head (b2-removal-evaluated (list *library-car* source) env))
       (tail (b2-removal-evaluated (list *b2-removal-disjoin* (list *library-cdr* source)) env))
       (head-false (b2-tactics-tactics-from-impossible library (proof-neg head) denied
                                                      (list cons-step) nil nil 1500 nil))
       (tail-false (b2-tactics-tactics-from-impossible library (proof-neg tail) denied
                                                      (list cons-step head-false) nil nil 1500 nil)))
    (cons (list head-false tail-false) library)))

(defun b2-removal-remove-false-base (atom library premise result removed empty-quote)
  (proof-with-checked-results
      ((request (b2-tactics-tactics-implication library premise result nil))
       (step (b2-tactics-tactics-solve (cdr request) result (list atom)
                                      (list removed *b2-removal-disjoin*) (list empty-quote) 0 nil)))
    (b2-tactics-tactics-implication library premise result (cons step (cdr request)))))

(defun b2-removal-remove-false-advance-consequent
    (assumption library source item env removed cons-step hypothesis)
  (proof-with-checked-results
      ((denied (b2-removal-denied-terms library assumption source env cons-step))
       (library (cdr denied))
       (proof (library-library-proof library))
       (head (caar denied))
       (tail (cadar denied))
       (remain (proof-proof-modus-ponens proof hypothesis tail))
       (test (proof-eq item (list *library-car* source)))
       (yes (proof-proof-assume proof test t))
       (no (proof-proof-assume proof test nil))
       (when-removed (b2-tactics-tactics-normalize library removed (list cons-step yes)
                                                  (list removed) nil 1500 nil))
       (reverse (if when-removed (proof-proof-symmetric proof when-removed)
                  (b2-removal-first when-removed)))
       (removed-proof (proof-proof-rewrite-first proof remain reverse))
       (when-kept (b2-tactics-tactics-normalize library removed (list cons-step no)
                                               (list removed) nil 1500 nil))
       (pair (b2-removal-right when-kept))
       (law (b2-removal-disjoin-truth library pair env))
       (library (cdr law))
       (proof (library-library-proof library))
       (eval-pair (b2-removal-evaluated (list *b2-removal-disjoin* pair) env))
       (q (b2-removal-truth eval-pair))
       (negative (b2-tactics-tactics-solve
                  library (proof-neg q) (list head remain) nil (list (car law)) 0 nil))
       (kept (b2-tactics-tactics-from-impossible library (proof-neg eval-pair) negative
                                                 nil nil nil 1500 nil))
       (reverse (proof-proof-symmetric proof when-kept))
       (kept-proof (proof-proof-rewrite-first proof kept reverse))
       (step (proof-proof-cases proof test removed-proof kept-proof)))
    (cons step library)))

(defun b2-removal-remove-false-advance
    (cons-step hypothesis library source item env premise result removed)
  (proof-with-checked-results
      ((request (b2-tactics-tactics-implication library premise result nil))
       (reply (b2-removal-remove-false-advance-consequent
               (nth 3 (car request)) (cdr request) source item env removed cons-step hypothesis)))
    (b2-tactics-tactics-implication library premise result reply)))

(defun b2-removal-remove-false (library source item env)
  (let* ((premise (proof-neg (b2-removal-evaluated (list *b2-removal-disjoin* source) env)))
         (removed (list *b2-removal-remove* item source))
         (result (proof-neg (b2-removal-evaluated (list *b2-removal-disjoin* removed) env)))
         (formula (list *library-implies* premise result)))
    (proof-with-checked-results
        ((empty-quote (b2-removal-quote-evaluates library *b2-removal-quoted-false* env))
         (advance-call (b2-tactics-tactics-on-list library formula source nil nil nil))
         (advance (b2-removal-remove-false-advance
                   (nth 3 (car advance-call)) (nth 4 (car advance-call)) (cdr advance-call)
                   source item env premise result removed))
         (base-call (b2-tactics-tactics-on-list library formula source nil advance nil))
         (base (b2-removal-remove-false-base
                (nth 3 (car base-call)) (cdr base-call) premise result removed empty-quote)))
      (b2-tactics-tactics-on-list library formula source base advance nil))))

(defun b2-removal-disjoin-remove (library formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (premise (proof-list-of-length (cadr parts) 2))
       (evaluated-main (proof-list-of-length (cadr premise) 3))
       (disjoined (proof-list-of-length (cadr evaluated-main) 2))
       (source (cadr disjoined))
       (env (caddr evaluated-main))
       (application (proof-term-at (caddr parts) 1))
       (disjoined (proof-term-at application 1))
       (wrapped (proof-term-at disjoined 1))
       (unwrapped (b2-tactics-tactics-normalize library wrapped nil nil nil 1500 nil))
       (rhs (b2-removal-right unwrapped))
       (item (proof-term-at rhs 1))
       (removed (b2-removal-remove-false library source item env))
       (library (cdr removed))
       (proof (library-library-proof library))
       (reverse (proof-proof-symmetric proof unwrapped))
       (step (proof-proof-rewrite-first proof (car removed) reverse)))
    (cons step library)))

(defun b2-removal-arbitrary-hypothesis-consequent (assumption library conclusion env)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((evidence (b2-tactics-tactics-evidence library (list assumption)))
         (correctness (b2-removal-correctness evidence))
         (first (b2-removal-first correctness))
         (application (proof-term-at first 1))
         (processor (proof-term-at application 1))
         (opened (proof-proof-unfold proof processor))
         (reduced (proof-proof-rewrite-first proof correctness opened))
         (first (b2-removal-first reduced))
         (conjoined (proof-term-at first 1))
         (clauses (proof-term-at conjoined 1))
         (removed (proof-term-at clauses 1))
         (single (b2-removal-conjoin-single library removed))
         (library (cdr single))
         (proof (library-library-proof library))
         (reduced (proof-proof-rewrite-first proof reduced (car single)))
         (refused (proof-proof-assume proof conclusion nil))
         (item (proof-term-at removed 1))
         (source (proof-term-at removed 2))
         (theorem (proof-proof-fact proof (proof-sym "DISJOIN-OF-REMOVE-EQUAL" "ACL2")
                                    (list (list (proof-sym "HYP" "ACL2") item)
                                          (list *library-x* source) (list *b2-removal-a* env))))
         (impossible (proof-proof-modus-ponens proof theorem refused))
         (first (b2-removal-first impossible))
         (evaluation (proof-term-at first 1))
         (disjoined (proof-term-at evaluation 1))
         (wrapped (proof-term-at disjoined 1))
         (normalized (b2-tactics-tactics-normalize library wrapped nil nil nil 1500 nil))
         (impossible (if normalized (proof-proof-rewrite proof impossible normalized '(1 1 1 1))
                       (b2-removal-first normalized)))
         (impossible (proof-proof-tidy proof impossible))
         (cut (proof-proof-cut proof reduced impossible))
         (step (proof-proof-front proof cut conclusion)))
      (cons step library))))

(defun b2-removal-arbitrary-hypothesis (library formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (premise (cadr parts))
       (conclusion (caddr parts))
       (env (proof-term-at conclusion 2))
       (request (b2-tactics-tactics-implication library premise conclusion nil))
       (reply (b2-removal-arbitrary-hypothesis-consequent
               (nth 3 (car request)) (cdr request) conclusion env)))
    (b2-tactics-tactics-implication library premise conclusion reply)))
