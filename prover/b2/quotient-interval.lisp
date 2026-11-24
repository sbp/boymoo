(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-quotient-interval-force* (proof-sym "FORCE" "ACL2"))

(defun b2-quotient-interval-quotient-data
    (lib i j typed-i nonnegative-i typed-j positive-j)
  (proof-with-checked-results
      ((natural-i (library-library-cite lib "NATURAL-FROM-BOUNDS" (list i)
                                        (list typed-i nonnegative-i)))
       (lemma (b2-quotients-nonnegative-quotient lib t)))
    (let* ((lib (cdr lemma))
           (proof (library-library-proof lib))
           (q (list *b2-quotients-niq* i j))
           (reciprocal (list *b2-products-recip* j))
           (ratio (b2-products-product i reciprocal))
           (successor (library-plus *proof-one* q)))
      (proof-with-checked-results
          ((theorem (proof-proof-fact proof (car lemma)
                                      (list (list *library-x* i)
                                            (list *library-y* j))))
           (statement (proof-step-first theorem))
           (condition (proof-term-at statement 1))
           (premise (b2-tactics-tactics-solve lib condition
                                             (list natural-i typed-j positive-j)
                                             nil nil 0 nil))
           (conclusion (proof-proof-modus-ponens proof theorem premise))
           (natural-and-interval (proof-proof-conjunct proof conclusion))
           (bounds (proof-proof-conjunct proof (cadr natural-and-interval)))
           (q-int (library-library-cite lib "NATURAL-INTEGER" (list q)
                                       (list (car natural-and-interval)))))
        (let ((types (list typed-i typed-j q-int)))
          (proof-with-checked-results
              ((i-rat (library-library-rational lib i types))
               (j-rat (library-library-rational lib j types))
               (q-rat (library-library-rational lib q types))
               (succ-rat (library-library-rational lib successor types))
               (inv-rat (b2-scaling-rational-op lib "unary-/" reciprocal (list j-rat)))
               (ratio-rat (b2-scaling-rational-op lib "binary-*" ratio
                                                 (list i-rat inv-rat)))
               (j-nonzero (b2-tactics-tactics-from-impossible
                           lib (proof-neg (proof-eq j *proof-zero*)) positive-j
                           nil nil nil 1500 nil))
               (j-numeric (library-library-number lib j (list typed-j)))
               (inverse (b2-products-reciprocal-identity lib j j-numeric j-nonzero))
               (swap (b2-products-product-swap lib j i reciprocal))
               (reduce (proof-proof-rewrite proof swap inverse '(1 2 2)))
               (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list i *proof-one*)))
               (i-numeric (library-library-number lib i (list typed-i)))
               (unit (b2-products-multiplicative-unit lib i i-numeric))
               (reduce (proof-proof-chain proof reduce (list commute unit)))
               (weak (b2-scaling-rational-scale-order
                      lib ratio q j (list ratio-rat q-rat j-rat) positive-j))
               (weak-equation (proof-proof-rewrite (library-library-proof (cdr weak))
                                                   (car weak) reduce '(1 1 1)))
               (strong (b2-scaling-rational-scale-order
                        (cdr weak) ratio successor j (list ratio-rat succ-rat j-rat)
                        positive-j)))
            (let* ((lib (cdr strong))
                   (proof (library-library-proof lib)))
              (proof-with-checked-results
                  ((strong-equation (proof-proof-rewrite proof (car strong) reduce '(1 1 1)))
                   (lower (proof-proof-rewrite proof (car bounds) weak-equation '(1 1)))
                   (lower (proof-proof-tidy proof lower))
                   (upper (proof-proof-rewrite proof (cadr bounds) strong-equation '(1)))
                   (upper (proof-proof-tidy proof upper)))
                (cons (list q-int lower upper) lib)))))))))

(defun b2-quotient-interval-shift-bound (lib upper)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (proof-step-first upper))
         (comparison (proof-list-of-length first 3))
         (successor (proof-list-of-length (caddr comparison) 3)))
      (let ((ratio (cadr comparison))
            (q (caddr successor)))
        (proof-with-checked-results
            ((explicit (library-library-axiom lib "<-ON-OTHERS" (list ratio successor)))
             (move-minus (library-library-axiom lib "DISTRIBUTIVITY-OF-MINUS-OVER-+"
                                                (list *proof-one* q)))
             (computed (proof-proof-compute proof (library-minus *proof-one*) -1))
             (move-minus (proof-proof-rewrite proof move-minus computed '(1 2 1)))
             (reorder (library-library-cite lib "ADD-SWAP"
                                            (list ratio *proof-neg-one* (library-minus q)) nil))
             (association (library-library-axiom lib "ASSOCIATIVITY-OF-+"
                                                 (list *proof-neg-one* ratio (library-minus q))))
             (reassociate (proof-proof-symmetric proof association))
             (adjusted (proof-proof-rewrite proof explicit move-minus '(1 2 1 2)))
             (reorder (proof-proof-chain proof reorder (list reassociate)))
             (adjusted (proof-proof-rewrite proof adjusted reorder '(1 2 1)))
             (other (library-library-axiom lib "<-ON-OTHERS"
                                           (list (library-plus *proof-neg-one* ratio) q)))
             (other (proof-proof-symmetric proof other))
             (equation (proof-proof-chain proof adjusted (list other)))
             (rewritten (proof-proof-rewrite proof upper equation '(1))))
          (proof-proof-tidy proof rewritten))))))

(defun b2-quotient-interval-ratio-is-integer-reverse
    (typed lib q ratio q-int lower upper)
  (let ((proof (library-library-proof lib))
        (kinds (list q-int typed))
        (delta (library-diff ratio q)))
    (proof-with-checked-results
        ((dt (library-library-type-of lib delta kinds))
         (order (library-library-axiom lib "<-ON-OTHERS" (list ratio q)))
         (sign (proof-proof-rewrite proof lower order '(1 1)))
         (sign (proof-proof-tidy proof sign))
         (compare (library-library-comparison lib ratio (library-plus *proof-one* q) kinds))
         (positive-difference (proof-proof-rewrite proof upper compare '(1)))
         (upper-delta (b2-tactics-tactics-less-from-difference
                       lib delta *proof-one* positive-difference kinds))
         (above-zero (proof-proof-assume proof (library-positive delta) t))
         (discrete (proof-proof-fact proof "integer-discrete" (list (list *library-x* delta))))
         (discrete-first (proof-step-first discrete))
         (discrete-condition (proof-term-at discrete-first 1))
         (premise (b2-tactics-tactics-solve lib discrete-condition (list dt above-zero)
                                           nil nil 0 nil))
         (cannot (proof-proof-modus-ponens proof discrete premise))
         (cut (proof-proof-cut proof upper-delta cannot))
         (no-positive (proof-proof-front proof cut (proof-neg (library-positive delta))))
         (delta-zero (b2-powers-zero-from-signs lib delta dt sign no-positive))
         (arithmetic (b2-tactics-tactics-linear-equal lib (library-plus delta q) ratio kinds))
         (arithmetic (proof-proof-rewrite proof arithmetic delta-zero '(1 1 1)))
         (unit (library-library-cite lib "ADD-ZERO-LEFT" (list q) (list q-int)))
         (unit (proof-proof-symmetric proof unit)))
      (proof-proof-chain proof unit (list arithmetic)))))

(defun b2-quotient-interval-ratio-is-integer (lib q ratio q-int lower upper)
  (let* ((proof (library-library-proof lib))
         (equality (proof-eq q ratio))
         (integer-ratio (library-integer ratio))
         (goal (proof-eq equality integer-ratio)))
    (proof-with-checked-results
        ((yes (proof-proof-assume proof equality t))
         (no (proof-proof-assume proof equality nil))
         (forward (proof-proof-rewrite proof q-int yes '(1 1)))
         (forward (proof-proof-tidy proof forward))
         (positive (b2-algebra-boolean-equivalence-positive lib goal yes forward))
         (typed (proof-proof-assume proof integer-ratio t))
         (backward (b2-quotient-interval-ratio-is-integer-reverse
                    typed lib q ratio q-int lower upper)))
      (b2-algebra-boolean-equivalence-negative
       lib equality integer-ratio no positive backward))))

(defun b2-quotient-interval-quotient-signs-case
    (lib test short yes no open-short q-positive differs)
  (proof-with-checked-results
      ((positive (b2-tactics-tactics-solve lib test (list yes) nil (list open-short) 0 nil))
       (negative (b2-tactics-tactics-solve lib test (list no q-positive differs)
                                         nil nil 0 nil)))
    (proof-proof-cases (library-library-proof lib) short positive negative)))

(defun b2-quotient-interval-quotient-signs (lib i j typed-i typed-j positive-j)
  (let* ((proof (library-library-proof lib))
         (q (list *b2-quotients-niq* i j))
         (short (library-lt i j))
         (ifix (list *b2-quotients-ifix* i))
         (nfix (list *b2-quotients-nfix* j)))
    (proof-with-checked-results
        ((yes (proof-proof-assume proof short t))
         (no (proof-proof-assume proof short nil))
         (j-nonzero (b2-tactics-tactics-from-impossible
                     lib (proof-neg (proof-eq j *proof-zero*)) positive-j nil nil nil 1500 nil))
         (j-nonnegative (library-library-cite lib "POSITIVE-NONNEGATIVE"
                                              (list j) (list typed-j positive-j)))
         (fixed-i (b2-tactics-tactics-normalize lib ifix (list typed-i)
                                               (list *b2-quotients-ifix*) nil 1500 nil))
         (fixed-j (b2-tactics-tactics-normalize lib nfix (list typed-j j-nonnegative)
                                               (list *b2-quotients-nfix*) nil 1500 nil))
         (open-short (b2-tactics-tactics-normalize lib q (list yes j-nonzero)
                                                  (list q) (list fixed-i fixed-j) 1500 nil))
         (open-long (b2-tactics-tactics-normalize lib q (list no j-nonzero)
                                                 (list q) (list fixed-i fixed-j) 1500 nil))
         (lemma (b2-quotients-nonnegative-quotient lib nil)))
      (let* ((lib (cdr lemma))
             (proof (library-library-proof lib))
             (child (library-diff i j))
             (child-q (list *b2-quotients-niq* child j)))
        (proof-with-checked-results
            ((induct (proof-proof-fact proof (car lemma)
                                       (list (list *library-x* child) (list *library-y* j))))
             (child-typed (library-library-type-of lib child (list typed-i typed-j)))
             (opened (library-library-axiom lib "<-ON-OTHERS" (list i j)))
             (child-bound (proof-proof-rewrite proof no opened '(1 1)))
             (child-bound (proof-proof-tidy proof child-bound))
             (child-nat (library-library-cite lib "NATURAL-FROM-BOUNDS"
                                              (list child) (list child-typed child-bound)))
             (induct-first (proof-step-first induct))
             (condition (proof-term-at induct-first 1))
             (reached (b2-tactics-tactics-solve lib condition
                                               (list child-nat typed-j positive-j) nil nil 0 nil))
             (induct-step (proof-proof-modus-ponens proof induct reached))
             (conjuncts (proof-proof-conjunct proof induct-step))
             (cq-typed (library-library-cite lib "NATURAL-INTEGER" (list child-q)
                                             (list (car conjuncts))))
             (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE" (list child-q)
                                                (list (car conjuncts))))
             (above (library-library-cite lib "POSITIVE-ONE-PLUS" (list child-q)
                                          (list cq-typed nonnegative)))
             (q-positive (if open-long
                             (library-library-transport-argument lib above open-long 2)
                           '(:failure "failure" "")))
             (zero (proof-eq q *proof-zero*))
             (differs (b2-tactics-tactics-from-impossible
                       lib (proof-neg zero) q-positive nil nil nil 1500 nil))
             (zero-test (b2-quotient-interval-quotient-signs-case
                         lib (proof-eq zero short) short yes no open-short q-positive differs))
             (positive-test (b2-quotient-interval-quotient-signs-case
                             lib (proof-eq (library-positive q) (proof-neg short))
                             short yes no open-short q-positive differs)))
          (cons (list zero-test positive-test) lib))))))

(defun b2-quotient-interval-forced-facts (proof steps)
  (if (endp steps)
      nil
    (proof-with-checked-results
        ((first (proof-step-first (car steps)))
         (head (proof-term-at first 0)))
      (if (equal head *b2-quotient-interval-force*)
          (proof-with-checked-results
              ((equation (proof-proof-unfold proof first))
               (step (proof-proof-rewrite proof (car steps) equation '(1)))
               (step (proof-proof-tidy proof step))
               (rest (b2-quotient-interval-forced-facts proof (cdr steps))))
            (cons step rest))
        (b2-quotient-interval-forced-facts proof (cdr steps))))))

(defun b2-quotient-interval-niq-theorem-consequent (premise lib name goal)
  (proof-with-checked-results
      ((known (b2-tactics-tactics-evidence lib (list premise)))
       (facts (b2-quotient-interval-forced-facts (library-library-proof lib)
                                                (table-values known)))
       (i-step (proof-term-at facts 0))
       (i-first (proof-step-first i-step))
       (i (proof-term-at i-first 1))
       (j-step (proof-term-at facts 2))
       (j-first (proof-step-first j-step))
       (j (proof-term-at j-first 1))
       (facts (proof-list-of-length facts 4))
       (data (b2-quotient-interval-quotient-data
              lib i j (car facts) (cadr facts) (caddr facts) (cadddr facts))))
    (let* ((lib (cdr data))
           (q-int (caar data))
           (lower (cadar data))
           (upper (caddar data)))
      (if (equal name (proof-sym "NIQ-BOUNDS" "ACL2"))
          (proof-with-checked-results
              ((shifted (b2-quotient-interval-shift-bound lib upper))
               (step (b2-tactics-tactics-solve lib goal (list lower shifted) nil nil 0 nil)))
            (cons step lib))
        (proof-with-checked-results
            ((q-first (proof-step-first q-int))
             (q (proof-term-at q-first 1))
             (lower-first (proof-step-first lower))
             (inner (proof-term-at lower-first 1))
             (ratio (proof-term-at inner 1))
             (exact (b2-quotient-interval-ratio-is-integer lib q ratio q-int lower upper))
             (tests (b2-quotient-interval-quotient-signs
                     lib i j (car facts) (caddr facts) (cadddr facts)))
             (step (b2-tactics-tactics-solve (cdr tests) goal
                                             (append (car tests) (list exact)) nil nil 0 nil)))
          (cons step (cdr tests)))))))

(defun b2-quotient-interval-niq-theorem (lib name formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (request (b2-tactics-tactics-implication lib (cadr parts) (caddr parts) nil))
       (reply (b2-quotient-interval-niq-theorem-consequent
               (cadddr (car request)) (cdr request) name (caddr parts))))
    (b2-tactics-tactics-implication lib (cadr parts) (caddr parts) reply)))
