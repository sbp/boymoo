(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *b2-strict-lexicographic-char-code* (proof-cl "CHAR-CODE"))
(defconst *b2-strict-lexicographic-realpart* (proof-cl "REALPART"))
(defconst *b2-strict-lexicographic-imagpart* (proof-cl "IMAGPART"))
(defconst *b2-strict-lexicographic-string-less* (proof-cl "STRING<"))
(defconst *b2-strict-lexicographic-string-weak* (proof-cl "STRING<="))

(defun b2-strict-lexicographic-signs (lib test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((yes (proof-proof-assume proof test t))
      (no (proof-proof-assume proof test nil)))
     (list yes no))))

(defun b2-strict-lexicographic-reverse-order (lib a b)
  (let* ((proof (library-library-proof lib))
         (strict (list *b2-strict-order-strict* a b))
         (ordered (list *b2-strict-order-lex* a b))
         (reverse (list *b2-strict-order-lex* b a))
         (same (proof-eq a b))
         (goal (proof-eq strict (proof-neg reverse))))
    (proof-with-checked-results
     ((reverse-signs (b2-strict-lexicographic-signs lib reverse))
      (total (proof-proof-fact
              proof *b2-strict-order-total*
              (list (list *library-x* b) (list *library-y* a))))
      (forward (proof-proof-prove-if proof total (cadr reverse-signs)))
      (reflexive (proof-proof-fact proof (proof-sym "LEXORDER-REFLEXIVE" "ACL2")
                                   (list (list *library-x* b))))
      (equal-assumption (proof-proof-assume proof same t))
      (symmetric (proof-proof-symmetric proof equal-assumption))
      (reflexive (proof-proof-rewrite proof reflexive symmetric '(1 2)))
      (cut (proof-proof-cut proof reflexive (cadr reverse-signs)))
      (distinct (proof-proof-front proof cut (proof-neg same)))
      (earlier (b2-tactics-tactics-solve
                lib goal (list (cadr reverse-signs) forward distinct)
                (list strict) nil 0 nil))
      (ordered-signs (b2-strict-lexicographic-signs lib ordered))
      (equal-step (b2-tactics-tactics-use-fact
                   lib *b2-strict-order-anti* same
                   (list (car ordered-signs) (car reverse-signs)) nil nil 0 nil))
      (both (b2-tactics-tactics-solve
             lib goal (list (car ordered-signs) (car reverse-signs) equal-step)
             (list strict) nil 0 nil))
      (later (b2-tactics-tactics-solve
              lib goal (list (cadr ordered-signs) (car reverse-signs))
              (list strict) nil 0 nil))
      (when-ordered (proof-proof-cases proof ordered both later)))
     (proof-proof-cases proof reverse when-ordered earlier))))

(defun b2-strict-lexicographic-strict-atom-cases-by-comparison
    (test evidence goal opens lib)
  (proof-with-checked-results
   ((signs (b2-strict-lexicographic-signs lib test))
    (yes (b2-tactics-tactics-solve lib goal (append evidence (list (car signs)))
                                  opens nil 0 nil))
    (no (b2-tactics-tactics-solve lib goal (append evidence (list (cadr signs)))
                                 opens nil 0 nil)))
   (proof-proof-cases (library-library-proof lib) test yes no)))

(defun b2-strict-lexicographic-strict-atom-cases-string-order-branch
    (same facts lib fast a b direct-goal direct-open)
  (if (not same)
      (b2-strict-lexicographic-strict-atom-cases-by-comparison
       (list *b2-strict-lexicographic-string-less* a b)
       facts direct-goal direct-open lib)
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
       ((string-negative
         (proof-proof-fact proof (proof-sym "STRING<-IRREFLEXIVE" "ACL2")
                           (list (list (proof-sym "S" "ACL2") a))))
        (string-step (proof-proof-rewrite proof string-negative same '(1 1 2)))
        (string-step (proof-proof-tidy proof string-step))
        (strict-negative
         (proof-proof-fact proof (proof-sym "<<-IRREFLEXIVE" "ACL2")
                           (list (list *library-x* a))))
        (strict-step (proof-proof-rewrite proof strict-negative same '(1 1 2)))
        (strict-step (proof-proof-tidy proof strict-step)))
       (b2-tactics-tactics-solve lib direct-goal
                                (append facts (list string-step strict-step))
                                (list fast) nil 0 nil)))))

(defun b2-strict-lexicographic-strict-atom-cases-symbol-order-branch
    (same facts lib a b evidence dual-goal reverse-open)
  (if same
      (let ((proof (library-library-proof lib))
            (type-test (list *b2-tactics-symbolp* a)))
        (proof-with-checked-results
         ((known (b2-tactics-tactics-evidence lib evidence))
          (typed (let ((found (assoc-equal type-test known)))
                   (if found (cdr found)
                     '(:failure "tactic-rejected" ""))))
          (theorem (proof-proof-fact proof (proof-sym "SYMBOL<-IRREFLEXIVE" "ACL2")
                                     (list (list *library-x* a))))
          (negative (proof-proof-modus-ponens proof theorem typed))
          (step (proof-proof-rewrite proof negative same '(1 1 2)))
          (step (proof-proof-tidy proof step)))
         (b2-tactics-tactics-solve lib dual-goal (append facts (list step))
                                  reverse-open nil 0 nil)))
    (b2-strict-lexicographic-strict-atom-cases-by-comparison
     (list *b2-lexicographic-symbol-less* a b) facts dual-goal reverse-open lib)))

(defun b2-strict-lexicographic-strict-atom-cases-with-equality
    (evidence prove lib a b fast goal opens)
  (let ((test (proof-eq a b)))
    (proof-with-checked-results
     ((signs (b2-strict-lexicographic-signs lib test))
      (yes-facts (append evidence (list (car signs))))
      (yes (if (eq prove :string)
               (b2-strict-lexicographic-strict-atom-cases-string-order-branch
                (car signs) yes-facts lib fast a b goal opens)
             (b2-strict-lexicographic-strict-atom-cases-symbol-order-branch
              (car signs) yes-facts lib a b evidence goal opens)))
      (no-facts (append evidence (list (cadr signs))))
      (no (if (eq prove :string)
              (b2-strict-lexicographic-strict-atom-cases-string-order-branch
               nil no-facts lib fast a b goal opens)
            (b2-strict-lexicographic-strict-atom-cases-symbol-order-branch
             nil no-facts lib a b evidence goal opens))))
     (proof-proof-cases (library-library-proof lib) test yes no))))

(defun b2-strict-lexicographic-strict-atom-cases-string-order
    (evidence lib a b fast direct-goal direct-open dual)
  (proof-with-checked-results
   ((result (b2-strict-lexicographic-strict-atom-cases-with-equality
             evidence :string lib a b fast direct-goal direct-open)))
   (proof-proof-chain (library-library-proof lib) result (list dual))))

(defun b2-strict-lexicographic-strict-atom-cases-symbol-order
    (evidence lib a b fast dual-goal reverse-open)
  (b2-strict-lexicographic-strict-atom-cases-with-equality
   evidence :symbol lib a b fast dual-goal reverse-open))

(defun b2-strict-lexicographic-strict-atom-cases-complex-order
    (evidence lib a b dual-goal reverse-open)
  (let* ((proof (library-library-proof lib))
         (real-a (list *b2-strict-lexicographic-realpart* a))
         (real-b (list *b2-strict-lexicographic-realpart* b))
         (compare (library-lt real-a real-b))
         (same-real (proof-eq real-a real-b)))
    (proof-with-checked-results
     ((type-a (library-library-axiom lib "COMPLEX-IMPLIES1" (list a)))
      (typed-a (proof-proof-conjunct proof type-a))
      (type-b (library-library-axiom lib "COMPLEX-IMPLIES1" (list b)))
      (typed-b (proof-proof-conjunct proof type-b))
      (signs (b2-strict-lexicographic-signs lib same-real))
      (reflection (library-library-axiom lib "<-ON-OTHERS" (list real-a real-a)))
      (inverse (library-library-axiom lib "INVERSE-OF-+" (list real-a)))
      (reflection (proof-proof-rewrite proof reflection inverse '(1 2 1)))
      (irreflexive (b2-tactics-tactics-solve
                    lib (proof-neg (library-lt real-a real-a))
                    nil nil (list reflection) 0 nil))
      (same (car signs))
      (same-reverse (proof-proof-symmetric proof same))
      (left-reflection (proof-proof-rewrite proof irreflexive same '(1 1 1)))
      (left-reflection (proof-proof-tidy proof left-reflection))
      (right-reflection (proof-proof-rewrite proof irreflexive same '(1 1 2)))
      (right-reflection (proof-proof-tidy proof right-reflection))
      (tied (b2-strict-lexicographic-strict-atom-cases-by-comparison
             (library-lt (list *b2-strict-lexicographic-imagpart* a)
                         (list *b2-strict-lexicographic-imagpart* b))
             (append evidence (list same same-reverse left-reflection right-reflection))
             dual-goal reverse-open lib))
      (compare-signs (b2-strict-lexicographic-signs lib compare))
      (different (cadr signs))
      (other-way (b2-strict-order-flipped-distinct lib real-a real-b different))
      (later (b2-rational-order-weak-from-strict
              lib (car compare-signs) (car typed-a) (car typed-b)))
      (earlier (b2-rational-order-strict-from-weak
                lib (cadr compare-signs) other-way (car typed-b) (car typed-a)))
      (left (b2-tactics-tactics-solve
             lib dual-goal (append evidence (list different other-way (car compare-signs) later))
             reverse-open nil 0 nil))
      (right (b2-tactics-tactics-solve
              lib dual-goal (append evidence (list different other-way (cadr compare-signs) earlier))
              reverse-open nil 0 nil))
      (distinct (proof-proof-cases proof compare left right)))
     (proof-proof-cases proof same-real tied distinct))))

(defun b2-strict-lexicographic-strict-atom-cases-first-kind-compare
    (kind-b typed-b kind-a typed-a lib a b fast dual base direct-goal
            direct-open dual-goal reverse-open)
  (let ((evidence (append base typed-a typed-b)))
    (cond
     ((not (equal kind-a kind-b))
      (b2-tactics-tactics-solve lib dual-goal evidence reverse-open nil 0 nil))
     ((equal kind-a *library-rationalp*)
      (b2-strict-lexicographic-strict-atom-cases-by-comparison
       (library-lt a b) evidence dual-goal reverse-open lib))
     ((equal kind-a *b2-tactics-characterp*)
      (b2-strict-lexicographic-strict-atom-cases-by-comparison
       (library-lt (list *b2-strict-lexicographic-char-code* a)
                   (list *b2-strict-lexicographic-char-code* b))
       evidence dual-goal reverse-open lib))
     ((equal kind-a *b2-lexicographic-complex*)
      (b2-strict-lexicographic-strict-atom-cases-complex-order
       evidence lib a b dual-goal reverse-open))
     ((equal kind-a *b2-lexicographic-string*)
      (b2-strict-lexicographic-strict-atom-cases-string-order
       evidence lib a b fast direct-goal direct-open dual))
     ((equal kind-a *b2-tactics-symbolp*)
      (b2-strict-lexicographic-strict-atom-cases-symbol-order
       evidence lib a b fast dual-goal reverse-open))
     (t (proof-with-checked-results
         ((step (b2-tactics-tactics-solve lib direct-goal evidence direct-open nil 0 nil)))
         (proof-proof-chain (library-library-proof lib) step (list dual)))))))

(defun b2-strict-lexicographic-strict-atom-cases-first-kind-next
    (pending kind-a typed-a lib a b fast dual base direct-goal direct-open dual-goal reverse-open)
  (let ((request (car pending)))
    (proof-with-checked-results
     ((step (b2-strict-lexicographic-strict-atom-cases-first-kind-compare
             (cadr request) (caddr request) kind-a typed-a lib a b fast dual base
             direct-goal direct-open dual-goal reverse-open))
      (replies (acons (cdr request) step (cdr pending)))
      (result (b2-lexicographic-atom-types lib b replies)))
     (cons result replies))))

(defun b2-strict-lexicographic-strict-atom-cases-first-kind-reply
    (n pending kind-a typed-a lib a b fast dual base direct-goal direct-open dual-goal reverse-open)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (acl2::o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-strict-lexicographic-strict-atom-cases-first-kind-reply"))
   ((failure-p pending) pending)
   ((not (eq (caar pending) :b2-lexicographic-atom-types)) (car pending))
   (t (b2-strict-lexicographic-strict-atom-cases-first-kind-reply
       (1- n)
       (b2-strict-lexicographic-strict-atom-cases-first-kind-next
        pending kind-a typed-a lib a b fast dual base direct-goal direct-open dual-goal reverse-open)
       kind-a typed-a lib a b fast dual base direct-goal direct-open dual-goal reverse-open))))

(defun b2-strict-lexicographic-strict-atom-cases-first-kind
    (kind-a typed-a lib a b fast dual base direct-goal direct-open dual-goal reverse-open)
  (proof-with-checked-results
   ((result (b2-lexicographic-atom-types lib b nil)))
   (b2-strict-lexicographic-strict-atom-cases-first-kind-reply
    1000000 (list result) kind-a typed-a lib a b fast dual base direct-goal
    direct-open dual-goal reverse-open)))

(defun b2-strict-lexicographic-strict-atom-cases-next
    (pending lib a b fast dual base direct-goal direct-open dual-goal reverse-open)
  (let ((request (car pending)))
    (proof-with-checked-results
     ((step (b2-strict-lexicographic-strict-atom-cases-first-kind
             (cadr request) (caddr request) lib a b fast dual base
             direct-goal direct-open dual-goal reverse-open))
      (replies (acons (cdr request) step (cdr pending)))
      (result (b2-lexicographic-atom-types lib a replies)))
     (cons result replies))))

(defun b2-strict-lexicographic-strict-atom-cases-reply
    (n pending lib a b fast dual base direct-goal direct-open dual-goal reverse-open)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (acl2::o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-strict-lexicographic-strict-atom-cases-reply"))
   ((failure-p pending) pending)
   ((not (eq (caar pending) :b2-lexicographic-atom-types)) (car pending))
   (t (b2-strict-lexicographic-strict-atom-cases-reply
       (1- n)
       (b2-strict-lexicographic-strict-atom-cases-next
        pending lib a b fast dual base direct-goal direct-open dual-goal reverse-open)
       lib a b fast dual base direct-goal direct-open dual-goal reverse-open))))

(defun b2-strict-lexicographic-strict-atom-cases (lib fast reverse dual base)
  (proof-with-checked-results
   ((parts (proof-list-of-length fast 3))
    (literal (proof-step-first dual))
    (strict (proof-term-at literal 1)))
   (let ((a (cadr parts))
         (b (caddr parts)))
     (b2-strict-lexicographic-strict-atom-cases-reply
      1000000
      (proof-with-checked-results ((result (b2-lexicographic-atom-types lib a nil)))
        (list result))
      lib a b fast dual base (proof-eq fast strict)
      (list fast strict (list *b2-strict-order-lex* a b)
            *b2-lexicographic-alpha* *b2-strict-lexicographic-string-weak*)
      (proof-eq fast (proof-neg reverse))
      (list fast reverse *b2-lexicographic-alpha*)))))

(defun b2-strict-lexicographic-equivalence-head-case
    (lib a builtin formula measure binding cons-a cons-b head-order reversed-order opens)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((ordinal (library-library-builtin lib builtin a))
      (smaller (proof-proof-discharge proof ordinal cons-a))
      (child (b2-tactics-tactics-induction-hypothesis lib formula measure binding smaller)))
     (b2-tactics-tactics-solve lib formula (list cons-a cons-b head-order reversed-order)
                              opens (list child) 0 nil))))

(defun b2-strict-lexicographic-strict-lexorder-equivalence (lib formula)
  (proof-with-checked-results
   ((formula-parts (proof-list-of-length formula 3))
    (fast (cadr formula-parts))
    (args (proof-list-of-length fast 3)))
   (let* ((proof (library-library-proof lib))
          (a (cadr args))
          (b (caddr args))
          (reverse (list *b2-strict-order-lex* b a))
          (goal (proof-eq fast (proof-neg reverse)))
          (left (list *proof-consp* a))
          (right (list *proof-consp* b))
          (measure (list *library-count* a))
          (cdr-binding (list (list a (list *library-cdr* a))
                             (list b (list *library-cdr* b))))
          (car-binding (list (list a (list *library-car* a))
                             (list b (list *library-car* b))))
          (head-a (list *library-car* a))
          (head-b (list *library-car* b))
          (tests (proof-eq head-a head-b))
          (opens (list fast reverse)))
     (proof-with-checked-results
      ((dual (b2-strict-lexicographic-reverse-order lib a b))
       (a-signs (b2-strict-lexicographic-signs lib left))
       (b-signs (b2-strict-lexicographic-signs lib right))
       (head-signs (b2-strict-lexicographic-signs lib tests))
       (same-reverse (proof-proof-symmetric proof (car head-signs)))
       (other-way (b2-strict-order-flipped-distinct lib head-a head-b (cadr head-signs)))
       (same-case (b2-strict-lexicographic-equivalence-head-case
                   lib a 3 goal measure cdr-binding (car a-signs) (car b-signs)
                   (car head-signs) same-reverse opens))
       (different-case (b2-strict-lexicographic-equivalence-head-case
                        lib a 2 goal measure car-binding (car a-signs) (car b-signs)
                        (cadr head-signs) other-way opens))
       (both (proof-proof-cases proof tests same-case different-case))
       (cons-atom (b2-tactics-tactics-solve lib goal
                                           (list (car a-signs) (cadr b-signs))
                                           opens nil 0 nil))
       (when-cons (proof-proof-cases proof right both cons-atom))
       (atoms (b2-strict-lexicographic-strict-atom-cases
               lib fast reverse dual (list (cadr a-signs) (cadr b-signs))))
       (atom-cons (b2-tactics-tactics-solve lib goal
                                           (list (cadr a-signs) (car b-signs))
                                           opens nil 0 nil))
       (when-atom (proof-proof-cases proof right atom-cons atoms))
       (ordinal (library-library-builtin lib 1 a))
       (cases (proof-proof-cases proof left when-cons when-atom))
       (induction (proof-proof-induct proof ordinal cases goal measure
                                      (list cdr-binding car-binding)))
       (symmetric (proof-proof-symmetric proof dual)))
      (proof-proof-chain proof induction (list symmetric))))))
