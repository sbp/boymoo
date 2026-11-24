(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-lists-map-names* (proof-sym "MAP-SYMBOL-NAME" "ACL2"))
(defconst *b2-lists-char-list* (proof-sym "CHARACTER-LISTP" "ACL2"))
(defconst *b2-lists-make-chars* (proof-sym "MAKE-CHARACTER-LIST" "ACL2"))
(defconst *b2-lists-fix* (proof-sym "FIX" "ACL2"))

(defmacro b2-lists-prove-on-list (lib formula variable signed hypothesis advance base)
  `(proof-with-checked-results
       ((b2-lists-request (b2-tactics-tactics-on-list ,lib ,formula ,variable nil nil nil))
        (,signed (cadddr (car b2-lists-request)))
        (,hypothesis (car (cddddr (car b2-lists-request))))
        (b2-lists-advance ,advance)
        (b2-lists-request (b2-tactics-tactics-on-list
                           ,lib ,formula ,variable nil (cons b2-lists-advance ,lib) nil))
        (,signed (cadddr (car b2-lists-request)))
        (b2-lists-base ,base)
        (b2-lists-result (b2-tactics-tactics-on-list
                          ,lib ,formula ,variable (cons b2-lists-base ,lib)
                          (cons b2-lists-advance ,lib) nil)))
     (car b2-lists-result)))

(defun b2-lists-open-literal (lib literal step evidence unfold)
  (proof-with-checked-results
      ((equality (b2-tactics-tactics-normalize lib literal evidence unfold nil 1500 nil)))
    (if equality
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results ((rewritten (proof-proof-rewrite proof step equality '(1))))
            (proof-proof-tidy proof rewritten)))
      step)))

(defun b2-lists-opened-conjuncts (lib step evidence unfold)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (opened (b2-lists-open-literal lib literal step evidence unfold)))
    (proof-proof-conjunct (library-library-proof lib) opened)))

(defun b2-lists-rational-sum-base (atom lib test goal total)
  (proof-with-checked-results
      ((request (b2-tactics-tactics-implication lib test goal nil))
       (step (b2-tactics-tactics-solve lib goal (list atom) (list total) nil 0 nil))
       (closed (b2-tactics-tactics-implication lib test goal (cons step lib))))
    (car closed)))

(defun b2-lists-rational-sum-advance-consequent
    (rational-list lib cons-step test total hypothesis)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (b2-lists-opened-conjuncts lib rational-list (list cons-step) (list test)))
         (reduced (b2-tactics-tactics-normalize lib total (list cons-step) (list total) nil 1500 nil))
         (tail-sum (proof-proof-modus-ponens proof hypothesis (cadr parts)))
         (literal (if reduced
                      (proof-step-first reduced)
                    '(:failure "failure" "")))
         (term (proof-term-at literal 2))
         (fact (b2-tactics-tactics-use-fact
                lib '("str" "rationalp-binary-+") (list *library-rationalp* term)
                (list (car parts) tail-sum) nil nil 0 nil)))
      (library-library-transport-argument lib fact reduced 1))))

(defun b2-lists-rational-sum-advance (cons-step hypothesis lib test goal total)
  (proof-with-checked-results
      ((request (b2-tactics-tactics-implication lib test goal nil))
       (step (b2-lists-rational-sum-advance-consequent
              (cadddr (car request)) lib cons-step test total hypothesis))
       (closed (b2-tactics-tactics-implication lib test goal (cons step lib))))
    (car closed)))

(defun b2-lists-rational-sum (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (test (cadr parts))
       (goal (caddr parts))
       (x (proof-term-at test 1))
       (total (proof-term-at goal 1)))
    (b2-lists-prove-on-list lib formula x signed hypothesis
      (b2-lists-rational-sum-advance signed hypothesis lib test goal total)
      (b2-lists-rational-sum-base signed lib test goal total))))

(defun b2-lists-sum-append-base-leaf (value tests lib)
  (declare (ignore tests))
  (cond ((equal value *proof-zero*)
         (b2-tactics-tactics-solve lib (list *library-numberp* *proof-zero*) nil nil nil 0 nil))
        ((integerp value) '(:failure "tactic-rejected" ""))
        (t (library-library-cite lib "SUM-NUMBER" (cdr value) nil))))

(defun b2-lists-sum-append-by-value (n lib value numeric tests)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((zp n) '(:failure "Fuel" "b2-lists-sum-append-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((parts (proof-list-of-length (cdr value) 3))
           (test (car parts))
           (yes (b2-lists-sum-append-by-value (1- n) lib (cadr parts) numeric
                                            (append tests (list (list test t)))))
           (no (b2-lists-sum-append-by-value (1- n) lib (caddr parts) numeric
                                           (append tests (list (list test nil))))))
        (proof-by-value-join proof value numeric yes no)))
     ((and (proof-compound value) (not (consp value)))
      '(:failure "tactic-rejected" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (literal (proof-step-first equality))
           (opened (proof-term-at literal 2))
           (step (b2-lists-sum-append-by-value (1- n) lib opened numeric tests))
           (symmetric (proof-proof-symmetric proof equality)))
        (proof-proof-rewrite-result proof step symmetric numeric *proof-result*)))
     (t (proof-with-checked-results ((step (b2-lists-sum-append-base-leaf value tests lib)))
          (proof-proof-by-value proof value numeric (list (cons (list value tests) step)) tests))))))

(defun b2-lists-sum-append-base (atom lib sy formula appended sx)
  (let ((proof (library-library-proof lib))
        (numeric (list *library-numberp* *proof-result*)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof sy))
         (literal (proof-step-first opened))
         (value (proof-term-at literal 2))
         (number (b2-lists-sum-append-by-value 1000000 lib value numeric nil))
         (symmetric (proof-proof-symmetric proof opened))
         (number (proof-proof-rewrite-result proof number symmetric numeric *proof-result*))
         (zero (library-library-axiom lib "UNICITY-OF-0" (list sy)))
         (fixed (b2-tactics-tactics-normalize lib (list *b2-lists-fix* sy) (list number)
                                            (list *b2-lists-fix*) nil 1500 nil))
         (zero (proof-proof-chain proof zero (list fixed))))
      (b2-tactics-tactics-solve lib formula (list atom) (list appended sx) (list zero) 0 nil))))

(defun b2-lists-sum-append-advance (cons-step hypothesis lib left right unfold)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left-step (b2-tactics-tactics-normalize lib left (list cons-step) unfold
                                                (list hypothesis) 1500 nil))
         (right-step (b2-tactics-tactics-normalize lib right (list cons-step) unfold nil 1500 nil))
         (left-literal (if left-step
                           (proof-step-first left-step)
                         '(:failure "failure" "")))
         (a (proof-term-at left-literal 2))
         (right-literal (if right-step
                            (proof-step-first right-step)
                          '(:failure "failure" "")))
         (b (proof-term-at right-literal 2)))
      (if (equal a b)
          (proof-with-checked-results ((symmetric (proof-proof-symmetric proof right-step)))
            (proof-proof-chain proof left-step (list symmetric)))
        (proof-with-checked-results
            ((first (proof-term-at a 1))
             (sum (proof-term-at a 2))
             (assoc-step (if (integerp sum)
                             '(:failure "tactic-rejected" "")
                           (library-library-axiom lib "ASSOCIATIVITY-OF-+" (cons first (cdr sum)))))
             (assoc-step (proof-proof-symmetric proof assoc-step))
             (last (proof-proof-symmetric proof right-step)))
          (proof-proof-chain proof left-step (list assoc-step last)))))))

(defun b2-lists-sum-append (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (left (cadr parts))
       (right (caddr parts))
       (appended (proof-term-at left 1))
       (append-parts (proof-list-of-length appended 3))
       (sum-parts (proof-list-of-length right 3)))
    (let* ((x (cadr append-parts))
           (sx (cadr sum-parts))
           (sy (caddr sum-parts))
           (unfold (list left appended sx)))
      (b2-lists-prove-on-list lib formula x signed hypothesis
        (b2-lists-sum-append-advance signed hypothesis lib left right unfold)
        (b2-lists-sum-append-base signed lib sy formula appended sx)))))

(defun b2-lists-mapped-recognizer-base (atom lib formula mapped pred)
  (b2-tactics-tactics-solve lib formula (list atom) (list mapped pred) nil 0 nil))

(defun b2-lists-mapped-recognizer-advance (cons-step hypothesis lib formula mapped pred function x)
  (let ((proof (library-library-proof lib))
        (evidence (list cons-step hypothesis))
        (opens (list mapped pred))
        (head (list *library-car* x)))
    (if (equal function *b2-lists-map-names*)
        (proof-with-checked-results
            ((step (proof-proof-fact proof "stringp-symbol-name" (list (list *library-x* head)))))
          (b2-tactics-tactics-solve lib formula (append evidence (list step)) opens nil 0 nil))
      (let ((test (list *b2-tactics-characterp* head)))
        (proof-with-checked-results
            ((good (proof-proof-assume proof test t))
             (bad (proof-proof-assume proof test nil))
             (null-character (library-library-axiom lib "CODE-CHAR-TYPE" (list *proof-zero*)))
             (yes (b2-tactics-tactics-solve lib formula (append evidence (list good)) opens nil 0 nil))
             (no (b2-tactics-tactics-solve lib formula (append evidence (list bad null-character))
                                         opens nil 0 nil)))
          (proof-proof-cases proof test yes no))))))

(defun b2-lists-mapped-recognizer (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 2))
       (pred (car parts))
       (mapped (cadr parts))
       (arguments (proof-list-of-length mapped 2))
       (function (car arguments))
       (x (cadr arguments)))
    (b2-lists-prove-on-list lib formula x signed hypothesis
      (b2-lists-mapped-recognizer-advance signed hypothesis lib formula mapped pred function x)
      (b2-lists-mapped-recognizer-base signed lib formula mapped pred))))
