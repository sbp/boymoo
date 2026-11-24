(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defun h1-book-termination-make-rulers (hypotheses search context)
  (list :h1-rulers hypotheses search context))

(defun h1-book-termination-rulers-hypotheses (rulers)
  (cadr rulers))

(defun h1-book-termination-rulers-search (rulers)
  (caddr rulers))

(defun h1-book-termination-rulers-context (rulers)
  (cadddr rulers))

(defun h1-book-termination-rulers-with-context (rulers context)
  (h1-book-termination-make-rulers (h1-book-termination-rulers-hypotheses rulers)
                                  (h1-tactics-context-search context) context))

(defun h1-book-termination-rulers-with-hypotheses (rulers hypotheses)
  (h1-book-termination-make-rulers hypotheses
                                  (h1-book-termination-rulers-search rulers)
                                  (h1-book-termination-rulers-context rulers)))

(defun h1-book-termination-rulers-record (rulers step)
  (proof-with-checked-results ((term (proof-step-first step)))
    (let* ((hypotheses (h1-book-termination-rulers-hypotheses rulers))
           (extra (descent-hypotheses-extra hypotheses))
           (context (h1-book-termination-rulers-context rulers))
           (evidence (h1-tactics-context-evidence context)))
      (proof-with-checked-results
          ((hypotheses
            (if (assoc-equal term extra)
                hypotheses
              (proof-with-checked-results
                  ((updated (descent-hypotheses-init
                             (descent-hypotheses-proof hypotheses)
                             (descent-hypotheses-tests hypotheses)
                             (append (table-values extra) (list step)))))
                (descent-hypotheses-with-found updated (descent-hypotheses-found hypotheses))))))
        (h1-book-termination-make-rulers
         hypotheses (h1-book-termination-rulers-search rulers)
         (if (assoc-equal term evidence)
             context
           (h1-tactics-context-with-evidence context (table-put evidence term step))))))))

(defun h1-book-termination-front-or-subsume (proof step term)
  (let ((clause (proof-step-clause step)))
    (if (member-equal term clause)
        (proof-proof-front proof step term)
      (proof-proof-subsume proof step (cons term clause)))))

(defun h1-book-termination-logical-expansion (n proof test step place)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "h1-book-termination-logical-expansion"))
   ((or (proof-is-call test *termination-return-last*)
        (proof-compound (h1-tactics-call-head test)))
    (proof-with-checked-results
        ((equality (if (proof-is-call test *termination-return-last*)
                       (proof-proof-unfold proof test)
                     (proof-proof-beta proof test)))
         (step (proof-proof-rewrite proof step equality place))
         (test (h1-tactics-step-at equality 2)))
      (h1-book-termination-logical-expansion (1- n) proof test step place)))
   (t (cons step test))))

(defun h1-book-termination-logical-negative-choices (n lib step rulers)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "h1-book-termination-logical-negative-choices")
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (choice (if (proof-is-call literal *proof-not*) (proof-term-at literal 1) nil)))
      (if (not (proof-is-call choice *proof-if*))
          (cons step rulers)
        (proof-with-checked-results ((parts (proof-list-of-length (seq-slice choice 1 3) 2)))
          (let ((test (car parts))
                (proof (library-library-proof lib)))
            (if (not (equal test (cadr parts)))
                (cons step rulers)
              (proof-with-checked-results
                  ((assumed (h1-arithmetic-proof-assume proof test t))
                   (selected (h1-propositions-propositional-proof-select lib choice assumed))
                   (first (proof-proof-rewrite proof step selected '(1 1)))
                   (first (proof-proof-tidy proof first))
                   (rulers (h1-book-termination-rulers-record rulers first))
                   (selected (h1-propositions-propositional-proof-select lib choice first))
                   (step (proof-proof-rewrite proof step selected '(1 1)))
                   (step (proof-proof-tidy proof step))
                   (rulers (h1-book-termination-rulers-record rulers step)))
                (h1-book-termination-logical-negative-choices (1- n) lib step rulers)))))))))

(defun h1-book-termination-logical-conjuncts (n lib step rulers)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "h1-book-termination-logical-conjuncts")
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (no (if (proof-is-call literal *proof-if*) (proof-term-at literal 3) nil)))
      (if (not (equal no *proof-false*))
          rulers
        (proof-with-checked-results
            ((parts (h1-propositions-propositional-proof-conjunct lib step))
             (rulers (h1-book-termination-rulers-record rulers (car parts)))
             (rulers (h1-book-termination-rulers-record rulers (cadr parts))))
          (h1-book-termination-logical-conjuncts (1- n) lib (cadr parts) rulers))))))

(defun h1-book-termination-rulers-add-logical-test (rulers test holds)
  (let* ((lib (descent-hypotheses-proof (h1-book-termination-rulers-hypotheses rulers)))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step (h1-arithmetic-proof-assume proof test holds))
         (expanded (h1-book-termination-logical-expansion
                    1000000 proof test step (if holds '(1) '(1 1))))
         (test (cdr expanded)))
      (let ((double-negative (and (not holds) (proof-is-call test *proof-not*))))
        (proof-with-checked-results
            ((step (if double-negative
                       (proof-with-checked-results
                           ((term (proof-term-at test 1))
                            (opposite (h1-arithmetic-proof-assume proof term nil))
                            (contrary (proof-proof-cut proof opposite (car expanded))))
                         (h1-book-termination-front-or-subsume proof contrary term))
                     (car expanded)))
             (rulers (h1-book-termination-rulers-record rulers step))
             (after-choices (h1-book-termination-logical-negative-choices 1000000 lib step rulers)))
          (if (or holds double-negative)
              (h1-book-termination-logical-conjuncts
               1000000 lib (car after-choices) (cdr after-choices))
            (cdr after-choices)))))))

(defun h1-book-termination-available-openings (names depth definitions)
  (declare (xargs :measure (acl2-count names)))
  (if (endp names)
      nil
    (let* ((name (proof-sym (car names) "ACL2"))
           (rest (h1-book-termination-available-openings (cdr names) depth definitions)))
      (if (assoc-equal name definitions)
          (cons (if depth (cons name depth) name) rest)
        rest))))

(defun h1-book-termination-rulers-add-tests (tests rulers)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      rulers
    (proof-with-checked-results
        ((signed (proof-list-of-length (car tests) 2))
         (rulers (h1-book-termination-rulers-add-logical-test rulers (car signed) (cadr signed))))
      (h1-book-termination-rulers-add-tests (cdr tests) rulers))))

(defun h1-book-termination-rulers-init (prover tests)
  (let* ((lib (h1-tactics-prover-library prover))
         (definitions (proof-proof-definitions (library-library-proof lib)))
         (openings (h1-book-termination-available-openings
                    '("FN-SYMB" "FARGN" "PSEUDO-TERMP" "THE-CHECK" "MV-LIST" "NATP")
                    nil definitions)))
    (proof-with-checked-results
        ((hypotheses (descent-hypotheses-init lib tests nil))
         (search (h1-tactics-search-init prover openings nil nil nil 6 nil))
         (context (h1-tactics-context-init search tests)))
      (h1-book-termination-rulers-add-tests
       tests (h1-book-termination-make-rulers hypotheses search context)))))

(defun h1-book-termination-hypotheses-find-conjunct (prefix tail term step lib hypotheses)
  (declare (xargs :measure (acl2-count prefix)))
  (if (endp prefix)
      (let ((hypotheses (descent-hypotheses-put-new hypotheses tail step)))
        (cons (table-get (descent-hypotheses-found hypotheses) term nil) hypotheses))
    (proof-with-checked-results ((parts (h1-propositions-propositional-proof-conjunct lib step)))
      (let* ((conjunct (car prefix))
             (hypotheses (descent-hypotheses-put-new hypotheses conjunct (car parts))))
        (if (equal term conjunct)
            (cons (table-get (descent-hypotheses-found hypotheses) term nil) hypotheses)
          (h1-book-termination-hypotheses-find-conjunct
           (cdr prefix) tail term (cadr parts) lib hypotheses))))))

(defun h1-book-termination-hypotheses-find-tests (tests term lib hypotheses)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      (cons nil hypotheses)
    (proof-with-checked-results ((signed (proof-list-of-length (car tests) 2)))
      (let ((test (car signed))
            (holds (cadr signed))
            (proof (library-library-proof lib)))
        (cond
         ((equal (if holds test (proof-neg test)) term)
          (proof-with-checked-results ((step (h1-arithmetic-proof-assume proof test holds)))
            (cons step (descent-hypotheses-remember hypotheses term step))))
         ((not holds) (h1-book-termination-hypotheses-find-tests (cdr tests) term lib hypotheses))
         (t
          (proof-with-checked-results ((parts (descent-conjuncts test nil)))
            (if (or (member-equal term (car parts)) (equal term (cdr parts)))
                (proof-with-checked-results ((step (h1-arithmetic-proof-assume proof test t)))
                  (h1-book-termination-hypotheses-find-conjunct
                   (car parts) (cdr parts) term step lib hypotheses))
              (h1-book-termination-hypotheses-find-tests (cdr tests) term lib hypotheses)))))))))

(defun h1-book-termination-hypotheses-find (hypotheses term)
  (let ((entry (or (assoc-equal term (descent-hypotheses-extra hypotheses))
                   (assoc-equal term (descent-hypotheses-found hypotheses)))))
    (if entry
        (cons (cdr entry) hypotheses)
      (h1-book-termination-hypotheses-find-tests
       (descent-hypotheses-tests hypotheses) term
       (descent-hypotheses-proof hypotheses) hypotheses))))

(defun h1-book-termination-rulers-find-integer (equalities term lib context)
  (declare (xargs :measure (acl2-count equalities)))
  (if (endp equalities)
      (cons nil context)
    (proof-with-checked-results ((first (proof-step-first (car equalities))))
      (if (not (proof-is-call first *proof-equal*))
          (h1-book-termination-rulers-find-integer (cdr equalities) term lib context)
        (proof-with-checked-results ((left (proof-term-at first 1))
                                     (argument (proof-term-at term 1)))
          (if (not (equal left argument))
              (h1-book-termination-rulers-find-integer (cdr equalities) term lib context)
            (proof-with-checked-results
                ((right (proof-term-at first 2))
                 (known (h1-tactics-context-find context (library-integer right))))
              (if (car known)
                  (proof-with-checked-results
                      ((step (h1-propositions-library-transport-argument
                              lib (car known) (car equalities) 1)))
                    (cons step (cdr known)))
                (h1-book-termination-rulers-find-integer
                 (cdr equalities) term lib (cdr known))))))))))

(defun h1-book-termination-rulers-find-by-contradiction (rulers term)
  (let* ((hypotheses (h1-book-termination-rulers-hypotheses rulers))
         (proof (library-library-proof (descent-hypotheses-proof hypotheses)))
         (search (h1-book-termination-rulers-search rulers))
         (tests (append (descent-hypotheses-tests hypotheses) (list (list term nil)))))
    (proof-with-checked-results
        ((opposite (h1-tactics-context-init search tests))
         (impossible (h1-tactics-search-contradiction search opposite)))
      (let* ((search (h1-tactics-context-search (cdr impossible)))
             (context (h1-tactics-context-with-search
                       (h1-book-termination-rulers-context rulers) search))
             (rulers (h1-book-termination-rulers-with-context rulers context)))
        (if (car impossible)
            (proof-with-checked-results
                ((result (h1-book-termination-front-or-subsume proof (car impossible) term)))
              (cons result (h1-book-termination-rulers-with-hypotheses
                            rulers (descent-hypotheses-remember hypotheses term result))))
          (cons nil rulers))))))

(defun h1-book-termination-rulers-find (rulers term)
  (proof-with-checked-results
      ((base (h1-book-termination-hypotheses-find (h1-book-termination-rulers-hypotheses rulers) term)))
    (let ((rulers (h1-book-termination-rulers-with-hypotheses rulers (cdr base))))
      (if (car base)
          (cons (car base) rulers)
        (proof-with-checked-results
            ((known (h1-tactics-context-find (h1-book-termination-rulers-context rulers) term)))
          (let* ((rulers (h1-book-termination-rulers-with-context rulers (cdr known)))
                 (head (h1-tactics-call-head term)))
            (if (or (car known)
                    (not (member-equal head (list *proof-consp* *library-natp* *proof-integerp* *proof-less*))))
                (cons (car known) rulers)
              (proof-with-checked-results
                  ((integer-proof
                    (if (equal head *proof-integerp*)
                        (h1-book-termination-rulers-find-integer
                         (table-values (descent-hypotheses-extra (cdr base))) term
                         (descent-hypotheses-proof (cdr base)) (cdr known))
                      known)))
                (let ((rulers (h1-book-termination-rulers-with-context rulers (cdr integer-proof))))
                  (if (car integer-proof)
                      (cons (car integer-proof) rulers)
                    (h1-book-termination-rulers-find-by-contradiction rulers term)))))))))))

(defun h1-book-termination-rulers-require (rulers term)
  (proof-with-checked-results ((answer (h1-book-termination-rulers-find rulers term)))
    (if (car answer) answer '(:failure "CandidateRejected" ""))))

(defun h1-book-termination-install-selector-rules (prover names)
  (declare (xargs :measure (acl2-count names)))
  (if (endp names)
      prover
    (let* ((test (list (proof-cl (car names)) *library-x*))
           (claim (list *library-implies* (proof-neg test) (list *proof-consp* *library-x*))))
      (proof-with-checked-results
          ((step (h1-tactics-prover-solve prover claim nil 160))
           (helper (h1-tactics-prover-helper prover (concatenate 'string (car names) "-FALSE-CONSP")
                                            step nil t)))
        (h1-book-termination-install-selector-rules (cdr helper) (cdr names))))))

(defun h1-book-termination-join-value (proof value template yes no)
  (proof-with-checked-results
      ((at-true (h1-arithmetic-proof-if-true proof value))
       (at-true (h1-propositions-proof-symmetric proof at-true))
       (yes (proof-proof-rewrite-result proof yes at-true template *proof-result*))
       (at-false (h1-arithmetic-proof-if-false proof value))
       (at-false (h1-propositions-proof-symmetric proof at-false))
       (no (proof-proof-rewrite-result proof no at-false template *proof-result*)))
    (proof-proof-cases proof (cadr value) yes no)))

(defun h1-book-termination-length-integer-value (n lib value template)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "h1-book-termination-length-integer-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((parts (proof-list-of-length (cdr value) 3))
           (yes (h1-book-termination-length-integer-value (1- n) lib (cadr parts) template))
           (no (h1-book-termination-length-integer-value (1- n) lib (caddr parts) template)))
        (h1-book-termination-join-value proof value template yes no)))
     ((and (proof-compound value) (endp value))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((beta (proof-proof-beta proof value))
           (opened (h1-tactics-step-at beta 2))
           (step (h1-book-termination-length-integer-value (1- n) lib opened template))
           (reversed (h1-propositions-proof-symmetric proof beta)))
        (proof-proof-rewrite-result proof step reversed template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (library-library-type-of lib value nil))
           (literal (proof-step-first step))
           (expected (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal expected) step '(:failure "failure" "")))))))

(defun h1-book-termination-install-selector-tests (prover)
  (proof-with-checked-results
      ((prover (h1-book-termination-install-selector-rules prover '("ATOM" "ENDP")))
       (lib (h1-tactics-prover-library prover))
       (proof (library-library-proof lib))
       (equation (proof-proof-unfold proof (list (proof-cl "LENGTH") *library-x*)))
       (value (h1-tactics-step-at equation 2))
       (result (h1-book-termination-length-integer-value
                1000000 lib value (library-integer *proof-result*)))
       (length-integer (h1-propositions-library-transport-argument lib result equation 1))
       (helper (h1-tactics-prover-helper prover "LENGTH-INTEGER" length-integer nil t)))
    (cdr helper)))

(defun h1-book-termination-cons-from-nonatom (prover atom-step)
  (let ((lib (h1-tactics-prover-library prover)))
    (proof-with-checked-results
        ((test (h1-tactics-step-at atom-step 1))
         (term (proof-term-at test 1))
         (head (proof-term-at test 0))
         (name (proof-term-at head 2))
         (implication (library-library-axiom
                       lib (concatenate 'string "H1-" name "-FALSE-CONSP") (list term))))
      (h1-propositions-propositional-proof-modus-ponens lib implication atom-step))))

(defun h1-book-termination-endp-noncons (prover endp-step)
  (proof-with-checked-results
      ((test (proof-step-first endp-step))
       (term (proof-term-at test 1))
       (consequence (proof-neg (list *proof-consp* term)))
       (rule (h1-tactics-prover-solve prover (list *library-implies* test consequence)
                                     (list (proof-cl "ENDP")) 160)))
    (h1-propositions-propositional-proof-modus-ponens
     (h1-tactics-prover-library prover) rule endp-step)))

(defun h1-book-termination-cons-implies-truth (prover term cons-step)
  (let ((proof (h1-tactics-prover-proof prover))
        (nil-test (proof-eq term *proof-false*)))
    (proof-with-checked-results
        ((assumed (h1-arithmetic-proof-assume proof nil-test t))
         (at-nil (proof-proof-rewrite proof cons-step assumed '(1 1)))
         (not-cons (h1-tactics-prover-solve prover (proof-neg (list *proof-consp* *proof-false*)) nil 160))
         (conflict (proof-proof-cut proof at-nil not-cons))
         (unequal (proof-proof-front proof conflict (proof-neg nil-test)))
         (nil-or-true (proof-proof-nil-or-true proof term))
         (cut (proof-proof-cut proof nil-or-true unequal)))
      (proof-proof-front proof cut term))))

(mutual-recursion
 (defun h1-book-termination-simplify (n prover term definitions)
   (declare (xargs :measure (nfix n)))
   (let ((proof (h1-tactics-prover-proof prover))
         (head (car term)))
     (cond
      ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "h1-book-termination-simplify"))
      ((or (not (proof-compound term)) (equal head *proof-quote*)) nil)
      ((endp term) '(:failure "failure" ""))
      ((or (proof-compound head) (member-equal head definitions))
       (proof-with-checked-results
           ((first (proof-simplify-expansion proof term))
            (next (h1-book-termination-simplify (1- n) prover (cadr first) definitions)))
         (proof-proof-chain proof (car first) (list next))))
      ((equal head *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at term 1))
            (first (h1-book-termination-simplify (1- n) prover test definitions))
            (redex (proof-simplify-if-redex term first))
            (branch (h1-arithmetic-simplify-branch proof redex nil))
            (selected (h1-arithmetic-simplify-chain proof term first branch))
            (right (if selected (h1-tactics-step-at selected 2) nil)))
         (if (or (not selected) (equal right redex))
             selected
           (proof-with-checked-results
               ((next (h1-book-termination-simplify (1- n) prover right definitions)))
             (proof-proof-chain proof selected (list next))))))
      (t
       (proof-with-checked-results
           ((result (h1-book-termination-simplify-arguments (1- n) prover term (cdr term) 1 nil definitions))
            (current (if result (h1-tactics-step-at result 2) term))
            (constant (h1-tactics-prover-constant prover current)))
         (cond ((not constant) result)
               (result (proof-proof-chain proof result (list constant)))
               (t constant)))))))

 (defun h1-book-termination-simplify-arguments (n prover term args index result definitions)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "h1-book-termination-simplify-arguments"))
    ((endp args) result)
    (t
     (proof-with-checked-results
         ((equality (h1-book-termination-simplify (1- n) prover (car args) definitions))
          (next (if equality
                    (let ((proof (h1-tactics-prover-proof prover)))
                      (proof-with-checked-results
                          ((reflexive (or result (h1-arithmetic-proof-reflexive proof term))))
                        (proof-proof-rewrite proof reflexive equality (list 1 2 index))))
                  result)))
       (h1-book-termination-simplify-arguments (1- n) prover term (cdr args) (1+ index) next definitions))))))

(defun h1-book-termination-prove-natural (n prover literal)
  (declare (xargs :measure (nfix n)))
  (let ((proof (h1-tactics-prover-proof prover))
        (definitions (list *library-natp* *proof-not*)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "h1-book-termination-prove-natural"))
     ((equal literal *proof-true*) (proof-proof-prove proof literal nil definitions))
     (t
      (proof-with-checked-results
          ((equation (h1-book-termination-simplify 1000000 prover literal definitions))
           (right (if equation (h1-tactics-step-at equation 2) nil)))
        (cond ((or (not equation) (equal literal right)) '(:failure "CandidateRejected" ""))
              ((equal right *proof-true*) (proof-proof-true-from-eq proof equation))
              (t (proof-with-checked-results
                     ((step (h1-book-termination-prove-natural (1- n) prover right)))
                   (h1-propositions-proof-transport proof step equation)))))))))

(mutual-recursion
 (defun h1-book-termination-natural (prover term)
   (declare (xargs :measure (acl2-count term)))
   (let ((lib (h1-tactics-prover-library prover)))
     (cond
      ((proof-is-call term *library-count*) (library-library-cite lib "COUNT-NATURAL" (cdr term) nil))
      ((proof-is-call term *library-len*) (library-library-cite lib "LEN-NATURAL" (cdr term) nil))
      ((and (consp term) (proof-is-call term *proof-plus*))
       (proof-with-checked-results
           ((steps (h1-book-termination-natural-arguments prover (cdr term))))
         (library-library-cite lib "NATURAL-SUM" (cdr term) steps)))
      (t (h1-book-termination-prove-natural 1000000 prover (list *library-natp* term))))))

 (defun h1-book-termination-natural-arguments (prover args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((step (h1-book-termination-natural prover (car args)))
          (rest (h1-book-termination-natural-arguments prover (cdr args))))
       (cons step rest)))))

(defun h1-book-termination-positive-cons-count (prover term cons-step)
  (let* ((lib (h1-tactics-prover-library prover))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((expansion (proof-proof-unfold proof (list *library-count* term)))
         (choice (h1-tactics-step-at expansion 2))
         (selected (h1-propositions-propositional-proof-select lib choice cons-step))
         (at-cons (proof-proof-chain proof expansion (list selected)))
         (count-value (h1-tactics-step-at at-cons 2))
         (children (proof-term-at count-value 2))
         (natural (h1-book-termination-natural prover children))
         (integer (library-library-cite lib "NATURAL-INTEGER" (list children) (list natural)))
         (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE" (list children) (list natural)))
         (positive (library-library-cite lib "POSITIVE-ONE-PLUS" (list children) (list integer nonnegative))))
      (h1-propositions-library-transport-argument lib positive at-cons 2))))

(defun h1-book-termination-selector-replies (n lib args rulers proxy replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "h1-book-termination-selector-replies")
    (proof-with-checked-results ((answer (descent-query-recipe :selector-chain lib args proxy replies)))
      (if (descent-request-p answer)
          (let ((term (descent-request-term answer)))
            (proof-with-checked-results
                ((found (h1-book-termination-rulers-find rulers term)))
              (h1-book-termination-selector-replies
               (1- n) lib args (cdr found) proxy
               (table-put replies term (cons (car found) nil)))))
        (car answer)))))

(defun h1-book-termination-selector-chain (lib actual root rulers)
  (proof-with-checked-results ((proxy (descent-hypotheses-init lib nil nil)))
    (h1-book-termination-selector-replies 1000000 lib (list actual root) rulers proxy nil)))

(defun h1-book-termination-find-test (query-object rulersp term)
  (if rulersp
      (h1-book-termination-rulers-find query-object term)
    (h1-book-termination-hypotheses-find query-object term)))

(defun h1-book-termination-discharge-builtin (tests proof clause step query-object rulersp)
  (declare (xargs :measure (acl2-count tests)))
  (cond
   ((endp tests) (cons step query-object))
   ((member-equal (car tests) clause)
    (h1-book-termination-discharge-builtin (cdr tests) proof clause step query-object rulersp))
   (t
    (let ((test (car tests)))
      (proof-with-checked-results
          ((evidence
            (if (proof-is-call test *proof-not*)
                (proof-with-checked-results ((inner (proof-term-at test 1)))
                  (h1-book-termination-find-test query-object rulersp inner))
              (cons nil query-object)))
           (evidence
            (if (car evidence)
                evidence
              (h1-book-termination-find-test (cdr evidence) rulersp (proof-neg test)))))
        (if (not (car evidence))
            evidence
          (proof-with-checked-results
              ((result (proof-proof-discharge proof step (car evidence))))
            (h1-book-termination-discharge-builtin
             (cdr tests) proof clause result (cdr evidence) rulersp))))))))

(defun h1-book-termination-try-builtins (matches proof clause query-object rulersp)
  (declare (xargs :measure (acl2-count matches)))
  (if (endp matches)
      (cons nil query-object)
    (proof-with-checked-results
        ((result (h1-book-termination-discharge-builtin
                  (cdr (proof-step-clause (car matches))) proof clause (car matches) query-object rulersp)))
      (if (car result)
          result
        (h1-book-termination-try-builtins (cdr matches) proof clause (cdr result) rulersp)))))

(defun h1-book-termination-direct-builtin (lib clause query-object rulersp)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((goal (if (consp clause) (car (last clause)) '(:failure "failure" "")))
         (matches (descent-builtin-matches (seq-range 1 24 1) proof clause goal nil)))
      (if (car matches)
          (cons (car matches) query-object)
        (h1-book-termination-try-builtins (cdr matches) proof clause query-object rulersp)))))

(defun h1-book-termination-selector-descent (prover goal rulers)
  (let* ((lib (h1-tactics-prover-library prover))
         (proof (library-library-proof lib))
         (child (cadr goal))
         (parent (caddr goal))
         (root (cadr parent)))
    (proof-with-checked-results
        ((opened (h1-book-termination-simplify 1000000 prover (cadr child) (list *termination-return-last*)))
         (actual (if opened (h1-tactics-step-at opened 2) (cadr child)))
         (head (proof-term-at actual 0))
         (argument (if (member-equal head *termination-selectors*) (proof-term-at actual 1) nil))
         (step
          (if (and (member-equal head *termination-selectors*) (equal argument root))
              (proof-with-checked-results
                  ((structural (library-library-builtin lib (if (equal head *library-car*) 2 3) root))
                   (cons-step (h1-book-termination-rulers-require rulers (list *proof-consp* root))))
                (proof-proof-discharge proof structural (car cons-step)))
            (proof-with-checked-results
                ((smaller (h1-book-termination-selector-chain lib actual root rulers))
                 (ordinal (library-library-ordinal-comparison lib (list *library-count* actual) parent)))
              (h1-propositions-proof-transport proof smaller ordinal)))))
      (if opened
          (proof-with-checked-results
              ((reversed (h1-propositions-proof-symmetric proof opened))
               (step (proof-proof-rewrite proof step reversed '(1 1 1))))
            (proof-proof-tidy proof step))
        step))))

(defun h1-book-termination-count-zero (prover parent root rulers)
  (let ((lib (h1-tactics-prover-library prover))
        (proof (h1-tactics-prover-proof prover))
        (smaller (list *library-count* *proof-false*)))
    (proof-with-checked-results
        ((cons-step (h1-book-termination-rulers-require rulers (list *proof-consp* root)))
         (positive (h1-book-termination-positive-cons-count prover root (car cons-step)))
         (zero (h1-book-termination-simplify 1000000 prover smaller (list *library-count*)))
         (positive (h1-propositions-library-transport-argument lib positive zero 1))
         (ordinal (library-library-ordinal-comparison lib smaller parent)))
      (h1-propositions-proof-transport proof positive ordinal))))

(defun h1-book-termination-count-finish (proof step reduced)
  (if reduced
      (proof-with-checked-results
          ((reversed (h1-propositions-proof-symmetric proof reduced))
           (step (proof-proof-rewrite proof step reversed '(1 1 1))))
        (proof-proof-tidy proof step))
    step))

(mutual-recursion
 (defun h1-book-termination-count-descent-value (n prover value template tests parent root call openings)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "h1-book-termination-count-descent-value")
     (let ((proof (h1-tactics-prover-proof prover)))
       (cond
        ((proof-is-call value *proof-if*)
         (proof-with-checked-results
             ((parts (proof-list-of-length (cdr value) 3))
              (test (car parts))
              (yes (h1-book-termination-count-descent-value
                    (1- n) prover (cadr parts) template (append tests (list (list test t)))
                    parent root call openings))
              (no (h1-book-termination-count-descent-value
                   (1- n) prover (caddr parts) template (append tests (list (list test nil)))
                   parent root call openings)))
           (h1-book-termination-join-value proof value template yes no)))
        ((and (proof-compound value) (endp value))
         '(:failure "failure" ""))
        ((and (proof-compound value) (proof-compound (car value)))
         (proof-with-checked-results
             ((beta (proof-proof-beta proof value))
              (opened (h1-tactics-step-at beta 2))
              (step (h1-book-termination-count-descent-value
                     (1- n) prover opened template tests parent root call openings))
              (reversed (h1-propositions-proof-symmetric proof beta)))
           (proof-proof-rewrite-result proof step reversed template *proof-result*)))
        (t
         (proof-with-checked-results
             ((step (h1-book-termination-count-descent-leaf
                     (1- n) value tests prover call parent root openings template))
              (literal (proof-step-first step))
              (expected (proof-subst template (list (cons *proof-result* value)))))
           (if (equal literal expected) step '(:failure "failure" ""))))))))

 (defun h1-book-termination-count-descent-leaf (n actual tests prover call parent root openings template)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "h1-book-termination-count-descent-leaf")
     (let ((lib (h1-tactics-prover-library prover))
           (proof (h1-tactics-prover-proof prover)))
       (proof-with-checked-results
           ((rulers (h1-book-termination-rulers-init prover (append (termination-call-tests call) tests)))
            (reduction (h1-tactics-search-reduce
                        (h1-book-termination-rulers-search rulers) actual
                        (h1-book-termination-rulers-context rulers) nil openings 0))
            (reduced (car reduction))
            (rulers (h1-book-termination-rulers-with-context rulers (cadr reduction)))
            (simplified (if reduced (h1-tactics-step-at reduced 2) actual))
            (goal (list *proof-ordinal-less* (list *library-count* simplified) parent))
            (direct (h1-book-termination-direct-builtin lib (list goal) rulers t))
            (step
             (cond
              ((car direct) (car direct))
              ((proof-is-call simplified *proof-if*)
               (h1-book-termination-count-descent-value
                (1- n) prover simplified template tests parent root call openings))
              (t
               (proof-with-checked-results ((path (h1-recursion-selector-path simplified root)))
                 (cond
                  (path
                   (proof-with-checked-results
                       ((root-cons (h1-book-termination-rulers-require (cdr direct) (list *proof-consp* root))))
                     (h1-book-termination-selector-descent prover goal (cdr root-cons))))
                  ((equal simplified *proof-false*)
                   (h1-book-termination-count-zero prover parent root (cdr direct)))
                  (t '(:failure "Unproved" ""))))))))
         (h1-book-termination-count-finish proof step reduced))))))

(defun h1-book-termination-count-descent (prover clause call)
  (proof-with-checked-results
      ((goal (if (consp clause) (car (last clause)) '(:failure "failure" "")))
       (parts (proof-list-of-length goal 3))
       (actual (proof-term-at (cadr parts) 1))
       (parent (caddr parts))
       (root (proof-term-at parent 1)))
    (let* ((definitions (proof-proof-definitions (h1-tactics-prover-proof prover)))
           (openings (h1-book-termination-available-openings
                      '("HARD-ERROR" "RETURN-LAST" "THE-CHECK") 8 definitions))
           (template (list *proof-ordinal-less* (list *library-count* *proof-result*) parent)))
      (h1-book-termination-count-descent-value
       1000000 prover actual template nil parent root call openings))))

(defun h1-book-termination-next-position-inside (prover rulers before bound integral)
  (let ((lib (h1-tactics-prover-library prover)))
    (proof-with-checked-results ((inside (h1-book-termination-rulers-find rulers (library-lt before bound))))
      (cond
       ((car inside) inside)
       ((proof-is-call bound *proof-plus*)
        (proof-with-checked-results ((first-addend (proof-term-at bound 1)))
          (if (not (equal first-addend *proof-one*))
              inside
            (proof-with-checked-results
                ((last-position (proof-term-at bound 2))
                 (last-integer (h1-book-termination-rulers-require
                                (cdr inside) (library-integer last-position)))
                 (earlier (h1-book-termination-rulers-require
                           (cdr last-integer) (library-lt before last-position)))
                 (greater (library-library-cite lib "SUCCESSOR-LARGER" (list last-position)
                                                (list (car last-integer))))
                 (bound-integer (library-library-type-of lib bound (list (car last-integer))))
                 (result (library-library-cite
                          lib "LESS-TRANSITIVE" (list before last-position bound)
                          (list integral (car last-integer) bound-integer (car earlier) greater))))
              (cons result (cdr earlier))))))
       (t inside)))))

(defun h1-book-termination-next-position-bound-type (prover rulers bound)
  (proof-with-checked-results ((typed (h1-book-termination-rulers-find rulers (library-integer bound))))
    (if (and (not (car typed)) (proof-is-call bound *proof-plus*))
        (proof-with-checked-results ((first-addend (proof-term-at bound 1)))
          (if (not (equal first-addend *proof-one*))
              (car typed)
            (proof-with-checked-results
                ((last-position (proof-term-at bound 2))
                 (last-typed (h1-book-termination-rulers-require (cdr typed) (library-integer last-position))))
              (library-library-type-of (h1-tactics-prover-library prover) bound (list (car last-typed))))))
      (car typed))))

(defun h1-book-termination-next-position (prover child parent call)
  (proof-with-checked-results ((parent-parts (proof-list-of-length parent 3))
                               (child-parts (proof-list-of-length child 3)))
    (let* ((bound (cadr parent-parts))
           (before (caddr parent-parts))
           (after (caddr child-parts))
           (lib (h1-tactics-prover-library prover))
           (proof (library-library-proof lib)))
      (if (not (and (equal (cadr child-parts) bound)
                    (member-equal after (list (library-plus *proof-one* before)
                                              (library-plus before *proof-one*)))))
          '(:failure "Unproved" "")
        (proof-with-checked-results
            ((rulers (h1-book-termination-rulers-init prover (termination-call-tests call)))
             (typed (h1-book-termination-rulers-require rulers (library-integer before)))
             (advance (library-library-cite lib "SUCCESSOR-LARGER" (list before) (list (car typed))))
             (successor (h1-tactics-step-at advance 2))
             (advance (if (equal after successor)
                          advance
                        (proof-with-checked-results
                            ((commute (library-library-axiom lib "COMMUTATIVITY-OF-+" (list *proof-one* before))))
                          (proof-proof-rewrite proof advance commute '(1 2)))))
             (inside (h1-book-termination-next-position-inside prover (cdr typed) before bound (car typed))))
          (if (not (car inside))
              '(:failure "Unproved" "")
            (proof-with-checked-results
                ((bound-integer (h1-book-termination-next-position-bound-type prover (cdr inside) bound)))
              (if (not bound-integer)
                  '(:failure "Unproved" "")
                (proof-with-checked-results ((after-integer (library-library-type-of lib after (list (car typed)))))
                  (library-library-cite lib "GAP-DECREASE" (list bound before after)
                                        (list bound-integer (car typed) after-integer (car inside) advance)))))))))))

(defun h1-book-termination-length-descent (prover child parent call)
  (let* ((lib (h1-tactics-prover-library prover))
         (proof (library-library-proof lib))
         (root (cadr parent)))
    (proof-with-checked-results
        ((rulers (h1-book-termination-rulers-init prover (termination-call-tests call)))
         (cons-step (h1-book-termination-rulers-require rulers (list *proof-consp* root)))
         (smaller (library-library-cite lib "LEN-CDR-LESS" (list root) (list (car cons-step))))
         (ordinal (library-library-ordinal-comparison lib child parent)))
      (h1-propositions-proof-transport proof smaller ordinal))))

(defun h1-book-termination-prove-measure-decrease (prover clause call child parent)
  (proof-with-checked-results
      ((bounded
        (if (and (proof-is-call child *library-nfix*) (proof-is-call parent *library-nfix*))
            (proof-with-checked-results ((before (proof-term-at parent 1))
                                         (after (proof-term-at child 1)))
              (h1-book-modulo-bounded-decrease prover before after (termination-call-tests call)))
          nil)))
    (cond
     (bounded bounded)
     ((and (proof-is-call child *library-count*) (proof-is-call parent *library-count*))
      (h1-book-termination-count-descent prover clause call))
     (t
      (proof-with-checked-results
          ((length-decrease
            (if (and (proof-is-call child *library-len*) (proof-is-call parent *library-len*))
                (proof-with-checked-results ((after (proof-term-at child 1)) (before (proof-term-at parent 1)))
                  (equal after (list *library-cdr* before)))
              nil)))
        (cond (length-decrease (h1-book-termination-length-descent prover child parent call))
              ((and (proof-is-call child *library-gap*) (proof-is-call parent *library-gap*))
               (h1-book-termination-next-position prover child parent call))
              (t '(:failure "Unproved" ""))))))))

(defun h1-book-termination-measure-ordinal (prover measure)
  (let ((lib (h1-tactics-prover-library prover)))
    (proof-with-checked-results
        ((direct (descent-direct-builtin lib (list (list *proof-ordinalp* measure)) nil)))
      (if (car direct)
          (car direct)
        (proof-with-checked-results ((head (proof-term-at measure 0)))
          (if (equal head *library-gap*)
              (library-library-cite lib "GAP-ORDINAL" (cdr measure) nil)
            (proof-with-checked-results ((natural (h1-book-termination-natural prover measure)))
              (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural)))))))))

(defun h1-book-termination-prove-measure-clause (prover clause call)
  (let ((lib (h1-tactics-prover-library prover)))
    (if (not call)
        (proof-with-checked-results ((first (proof-term-at clause 0)) (measure (proof-term-at first 1)))
          (if (proof-is-call measure *library-nfix*)
              (library-library-cite lib "NFIX-ORDINAL" (cdr measure) nil)
            (h1-book-termination-measure-ordinal prover measure)))
      (proof-with-checked-results
          ((hypotheses (descent-hypotheses-init lib (termination-call-tests call) nil))
           (direct (h1-book-termination-direct-builtin lib clause hypotheses nil)))
        (if (car direct)
            (car direct)
          (proof-with-checked-results ((parts (proof-list-of-length (car (last clause)) 3)))
            (h1-book-termination-prove-measure-decrease prover clause call (cadr parts) (caddr parts))))))))

(defun h1-book-termination-all-count-measures (measures)
  (declare (xargs :measure (acl2-count measures)))
  (if (endp measures)
      t
    (and (proof-is-call (cdar measures) *library-count*)
         (h1-book-termination-all-count-measures (cdr measures)))))

(defun h1-book-termination-measure-key (name dictionary)
  (let ((entry (assoc-equal name dictionary)))
    (if entry (cdr entry) '(:failure "failure" ""))))

(defun h1-book-termination-replace-measure-head (measures)
  (declare (xargs :measure (acl2-count measures)))
  (if (endp measures)
      nil
    (proof-with-checked-results
        ((argument (proof-term-at (cdar measures) 1))
         (rest (h1-book-termination-replace-measure-head (cdr measures))))
      (cons (cons (caar measures) (list *library-nfix* argument)) rest))))

(defun h1-book-termination-bounded-calls (calls measures formals)
  (declare (xargs :measure (acl2-count calls)))
  (if (endp calls)
      t
    (let* ((call (car calls))
           (callee (termination-call-callee call))
           (tests (termination-call-tests call)))
      (proof-with-checked-results
          ((parent-measure (h1-book-termination-measure-key (termination-call-caller call) measures))
           (before (proof-term-at parent-measure 1))
           (child-measure (h1-book-termination-measure-key callee measures))
           (body (proof-term-at child-measure 1))
           (variables (h1-book-termination-measure-key callee formals))
           (after (proof-subst body (termination-bindings variables (termination-call-actuals call) nil)))
           (amount (h1-book-modulo-subtraction-amount before after tests))
           (bounded (if (eq amount :none)
                        (h1-book-modulo-bounded-remainder before after tests)
                      t)))
        (if bounded
            (h1-book-termination-bounded-calls (cdr calls) measures formals)
          nil)))))

(defun h1-book-termination-bounded-measure-plan (definitions calls measures)
  (if (not (h1-book-termination-all-count-measures measures))
      :none
    (proof-with-checked-results
        ((formals (termination-formals definitions nil nil))
         (bounded (h1-book-termination-bounded-calls calls measures formals)))
      (if bounded (h1-book-termination-replace-measure-head measures) :none))))

(defun h1-book-termination-stored-measures (definitions stored measures)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      measures
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (let ((entry (assoc-equal (car definition) stored)))
        (proof-with-checked-results
            ((relation (if entry (proof-term-at (cdr entry) 1) nil))
             (measures
              (if (member-equal relation (list *proof-ordinal-less* *proof-less*))
                  (proof-with-checked-results ((measure (proof-term-at (cdr entry) 0)))
                    (table-put measures (car definition) measure))
                measures)))
          (h1-book-termination-stored-measures (cdr definitions) stored measures))))))

(defun h1-book-termination-available-terms (terms available)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      t
    (let* ((term (car terms))
           (head (h1-tactics-call-head term)))
      (and (or (member-equal head available) (eq head :none)
               (proof-is-call term *proof-quote*))
           (h1-book-termination-available-terms (cdr terms) available)))))

(defun h1-book-termination-available-measures (measures available)
  (declare (xargs :measure (acl2-count measures)))
  (if (endp measures)
      t
    (and (h1-book-termination-available-terms (h1-tactics-subterms (cdar measures)) available)
         (h1-book-termination-available-measures (cdr measures) available))))

(defun h1-book-termination-gap-measure (measure)
  (proof-with-checked-results
      ((no (if (proof-is-call measure *proof-if*) (proof-term-at measure 3) nil))
       (branch (if (equal no *proof-zero*) (proof-term-at measure 2) nil))
       (difference (if (proof-is-call branch *proof-plus*) (proof-term-at branch 2) nil)))
    (if (proof-is-call difference *proof-minus*)
        (proof-with-checked-results ((bound (proof-term-at branch 1))
                                     (position (proof-term-at difference 1)))
          (list *library-gap* bound position))
      measure)))

(defun h1-book-termination-gap-measures (measures)
  (declare (xargs :measure (acl2-count measures)))
  (if (endp measures)
      nil
    (proof-with-checked-results
        ((gap (h1-book-termination-gap-measure (cdar measures)))
         (rest (h1-book-termination-gap-measures (cdr measures))))
      (cons (cons (caar measures) gap) rest))))

(defun h1-book-termination-selector-measures (selectors)
  (declare (xargs :measure (acl2-count selectors)))
  (if (endp selectors)
      nil
    (cons (cons (caar selectors) (list *library-count* (cdar selectors)))
          (h1-book-termination-selector-measures (cdr selectors)))))

(defun h1-book-termination-countdown-calls (calls index predecessors)
  (declare (xargs :measure (acl2-count calls)))
  (if (endp calls)
      t
    (proof-with-checked-results
        ((actual (proof-term-at (termination-call-actuals (car calls)) index)))
      (if (member-equal actual predecessors)
          (h1-book-termination-countdown-calls (cdr calls) index predecessors)
        nil))))

(defun h1-book-termination-next-countdown (formals calls name measures)
  (declare (xargs :measure (acl2-count formals)))
  (if (endp formals)
      :none
    (let* ((variable (cadar formals))
           (candidate (list (cons name (list *library-count* variable))))
           (predecessors (list (library-plus variable *proof-neg-one*)
                               (library-plus *proof-neg-one* variable))))
      (proof-with-checked-results
          ((valid (h1-book-termination-countdown-calls calls (caar formals) predecessors)))
        (if (and valid (not (equal candidate measures)))
            (list candidate :countdowns (cdr formals))
          (h1-book-termination-next-countdown (cdr formals) calls name measures))))))

(defun h1-book-termination-next-measure (n stage definitions calls measures formals)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "h1-book-termination-next-measure")
    (case stage
      (:bounded
       (proof-with-checked-results
           ((candidate (h1-book-termination-bounded-measure-plan definitions calls measures)))
         (if (eq candidate :none)
             (h1-book-termination-next-measure (1- n) :gaps definitions calls measures formals)
           (list candidate :gaps formals))))
      (:gaps
       (proof-with-checked-results ((candidate (h1-book-termination-gap-measures measures)))
         (if (equal candidate measures)
             (h1-book-termination-next-measure (1- n) :stored definitions calls measures formals)
           (list candidate :stored formals))))
      (:stored (list measures :selectors formals))
      (:selectors
       (proof-with-checked-results ((selectors (termination-selector-plan definitions calls)))
         (let ((candidate (h1-book-termination-selector-measures selectors)))
           (if (and selectors (not (and (subsetp-equal candidate measures)
                                        (subsetp-equal measures candidate))))
               (list candidate :countdowns formals)
             (h1-book-termination-next-measure (1- n) :countdowns definitions calls measures formals)))))
      (:countdowns
       (if (and (consp definitions) (endp (cdr definitions)) (proof-compound (cadar definitions)))
           (h1-book-termination-next-countdown
            (if (eq formals :none) (seq-numbered (cadar definitions) 0) formals)
            calls (caar definitions) measures)
         :none))
      (otherwise :none))))

(defun h1-book-termination-measure-stage (prover definitions measures)
  (if (and (equal (len measures) (len definitions))
           (h1-book-termination-available-measures measures (h1-tactics-prover-available prover)))
      :bounded
    :selectors))

(defun h1-book-termination-proof-measures-visit (n stage definitions calls measures formals)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "h1-book-termination-proof-measures-visit")
    (proof-with-checked-results
        ((candidate (h1-book-termination-next-measure 1000000 stage definitions calls measures formals)))
      (if (eq candidate :none)
          nil
        (proof-with-checked-results
            ((rest (h1-book-termination-proof-measures-visit
                    (1- n) (cadr candidate) definitions calls measures (caddr candidate))))
          (cons (car candidate) rest))))))

(defun h1-book-termination-proof-measures (prover definitions calls stored)
  (proof-with-checked-results ((measures (h1-book-termination-stored-measures definitions stored nil)))
    (h1-book-termination-proof-measures-visit 1000000
     (h1-book-termination-measure-stage prover definitions measures) definitions calls measures :none)))

(defun h1-book-termination-prove-candidate-case (prover case seen proofs)
  (let ((clause (car case)))
    (if (member-equal clause seen)
        (cons seen proofs)
      (proof-with-checked-results ((step (h1-book-termination-prove-measure-clause prover clause (cadr case))))
        (if (not (subsetp-equal (proof-step-clause step) (cons *proof-false* clause)))
            '(:failure "Unproved" "")
          (proof-with-checked-results
              ((step (proof-proof-subsume (h1-tactics-prover-proof prover) step clause)))
            (cons (cons clause seen) (cons step proofs))))))))

(defun h1-book-termination-prove-candidate-calls (prover calls measures formals seen proofs)
  (declare (xargs :measure (acl2-count calls)))
  (if (endp calls)
      (reverse proofs)
    (proof-with-checked-results
        ((cases (termination-call-cases (list (car calls)) measures formals))
         (result (h1-book-termination-prove-candidate-case prover (car cases) seen proofs)))
      (h1-book-termination-prove-candidate-calls prover (cdr calls) measures formals
                                                 (car result) (cdr result)))))

(defun h1-book-termination-prove-candidate-ordinalities (prover definitions calls measures formals seen proofs)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      (h1-book-termination-prove-candidate-calls prover calls measures formals seen proofs)
    (proof-with-checked-results
        ((cases (termination-ordinality-cases (list (car definitions)) measures))
         (result (h1-book-termination-prove-candidate-case prover (car cases) seen proofs)))
      (h1-book-termination-prove-candidate-ordinalities prover (cdr definitions) calls measures formals
                                                       (car result) (cdr result)))))

(defun h1-book-termination-prove-candidate (prover definitions calls measures)
  (proof-with-checked-results ((formals (termination-formals definitions nil nil)))
    (h1-book-termination-prove-candidate-ordinalities prover definitions calls measures formals nil nil)))

(defun h1-book-termination-entry-measures (definitions measures)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      nil
    (proof-with-checked-results
        ((measure (h1-book-termination-measure-key (caar definitions) measures))
         (rest (h1-book-termination-entry-measures (cdr definitions) measures)))
      (cons measure rest))))

(defun h1-book-termination-termination-entry-visit (n prover stage definitions calls measures formals)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "h1-book-termination-termination-entry-visit")
    (proof-with-checked-results
        ((candidate (h1-book-termination-next-measure 1000000 stage definitions calls measures formals)))
      (if (eq candidate :none)
          '(:failure "Unproved" "")
        (let ((proofs (h1-book-termination-prove-candidate prover definitions calls (car candidate))))
          (cond
           ((failure-p proofs)
            (if (member-equal (cadr proofs) '("Unproved" "CandidateRejected" "value"))
                (h1-book-termination-termination-entry-visit
                 (1- n) prover (cadr candidate) definitions calls measures (caddr candidate))
              proofs))
           ((endp definitions) '(:failure "failure" ""))
           (t
            (proof-with-checked-results ((fields (h1-book-termination-entry-measures definitions (car candidate))))
              (proof-proof-entry "measure" (caar definitions) (cons (caar definitions) fields) proofs)))))))))

(defun h1-book-termination-termination-entry (prover definitions calls stored)
  (proof-with-checked-results ((measures (h1-book-termination-stored-measures definitions stored nil)))
    (h1-book-termination-termination-entry-visit 1000000 prover
     (h1-book-termination-measure-stage prover definitions measures) definitions calls measures :none)))
