(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h2-arithmetic-zp* (proof-sym "ZP" "ACL2"))
(defconst *h2-arithmetic-nfix* (proof-sym "NFIX" "ACL2"))
(defconst *h2-arithmetic-implies* (proof-sym "IMPLIES" "ACL2"))

(defconst *h2-arithmetic-integer-rules*
  '("SELF-INTEGER-SUM" "SELF-INTEGER-NEGATION" "SELF-LESS-TRANSITIVE"
    "SELF-LESS-TO-WEAK" "SELF-WEAK-REFLEXIVE" "SELF-LESS-THEN-WEAK"
    "SELF-WEAK-THEN-LESS" "SELF-POSITIVE-ONE-PLUS" "SELF-POSITIVE-NONNEGATIVE"
    "SELF-NONNEGATIVE-SUM" "SELF-LEN-INTEGER" "SELF-LEN-NATURAL"
    "SELF-H2-INTEGER-ASYMMETRY" "SELF-H2-INTEGER-TRICHOTOMY"))

(defconst *h2-arithmetic-index-rules*
  '("SELF-H2-NFIX-WHEN-ZP" "SELF-H2-NFIX-WHEN-NOT-ZP" "SELF-H2-ADD1-SUB1"
    "SELF-H2-NFIX-PREDECESSOR" "SELF-H2-PREDECESSOR-INJECTIVE"
    "SELF-H2-LESS-IMPLIES-UNEQUAL" "SELF-H2-INTEGER-EQUAL-WHEN-NEITHER-LESS"
    "SELF-H2-POSITIVE-INDEX-INTEGER" "SELF-H2-POSITIVE-INDEX-POSITIVE"
    "SELF-H2-PREDECESSOR-NONNEGATIVE"))

(defun h2-arithmetic-nil-value (proof evidence)
  (proof-with-checked-results
      ((literal (proof-step-first evidence))
       (value (proof-term-at literal 1))
       (clause (proof-proof-nil-or-true proof value))
       (fronted (proof-proof-front proof clause value))
       (result (proof-proof-cut proof fronted evidence)))
    (proof-proof-tidy proof result)))

(defun h2-arithmetic-integer-trichotomy (p x y xy yx ints)
  (let* ((proof (library-library-proof p))
         (delta (library-diff y x))
         (delta-zero (proof-eq delta *proof-zero*)))
    (proof-with-checked-results
        ((identity (library-library-linear-equal p (library-plus delta x) y ints))
         (zero (proof-proof-assume proof delta-zero t))
         (identity (proof-proof-rewrite proof identity zero '(1 1 1)))
         (add-zero (library-library-cite p "ADD-ZERO-LEFT" (list x) (list (car ints))))
         (add-zero (proof-proof-symmetric proof add-zero))
         (equal-xy (proof-proof-chain proof add-zero (list identity)))
         (no-equal (proof-proof-assume proof (proof-eq x y) nil))
         (cut (proof-proof-cut proof equal-xy no-equal))
         (unequal-delta (proof-proof-front proof cut (proof-neg delta-zero)))
         (not-xy (proof-proof-assume proof xy nil))
         (comparison (library-library-comparison p x y ints))
         (delta-not-pos (proof-proof-rewrite proof not-xy comparison '(1 1)))
         (axiom (library-library-axiom p "TRICHOTOMY" (list delta)))
         (conjuncts (proof-proof-conjunct proof axiom))
         (number (library-library-number p delta ints))
         (trichotomy (proof-proof-modus-ponens proof (car conjuncts) number))
         (rest (proof-proof-prove-if proof trichotomy delta-not-pos))
         (opposite (proof-proof-prove-if proof rest unequal-delta))
         (comparison (library-library-comparison p y x ints))
         (value (h2-alists-logical-result comparison))
         (value (proof-term-at value 2))
         (other (h2-alists-logical-result opposite))
         (sign (library-library-linear-equal p value other ints))
         (rewritten (proof-proof-rewrite proof comparison sign '(1 2 2)))
         (claim (proof-proof-transport proof opposite rewritten))
         (ix (proof-step-first (car ints)))
         (iy (proof-step-first (cadr ints)))
         (guards (list (proof-neg ix) (proof-neg iy)))
         (p (library-library-lemma p "H2-INTEGER-TRICHOTOMY" yx claim
                                   (append guards (list xy (proof-eq x y)))))
         (proof (library-library-proof p))
         (no-yx (proof-proof-assume proof yx nil))
         (contradiction (proof-proof-cut proof claim no-yx))
         (fronted (proof-proof-front proof contradiction (proof-eq x y))))
      (library-library-lemma p "H2-INTEGER-EQUAL-WHEN-NEITHER-LESS" (proof-eq x y) fronted
                             (append guards (list xy yx))))))

(defun h2-arithmetic-integer-nonnil (p x ix)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((denied (proof-proof-assume proof x nil))
         (nil-x (h2-arithmetic-nil-value proof denied))
         (bad-type (proof-proof-rewrite proof ix nil-x '(1 1)))
         (computation (proof-proof-compute proof (library-integer *proof-false*) *proof-nil*))
         (bad-type (proof-proof-rewrite proof bad-type computation '(1)))
         (bad-type (proof-proof-tidy proof bad-type))
         (fronted (proof-proof-front proof bad-type x))
         (ix-first (proof-step-first ix)))
      (library-library-lemma p "H2-INTEGER-NONNIL" x fronted (list (proof-neg ix-first))))))

(defun h2-arithmetic-integer-order (p)
  (if (h2-alists-has-fact p "SELF-H2-INTEGER-ASYMMETRY")
      p
    (let* ((proof (library-library-proof p))
           (x *library-x*)
           (y *library-y*)
           (xy (library-lt x y))
           (yx (library-lt y x)))
      (proof-with-checked-results
          ((ints (library-library-ints p (list x y)))
           (xy-pos (proof-proof-assume proof xy t))
           (yx-pos (proof-proof-assume proof yx t))
           (loop (library-library-cite p "LESS-TRANSITIVE" (list x y x)
                                       (list (car ints) (cadr ints) (car ints) xy-pos yx-pos)))
           (no-loop (library-library-cite p "WEAK-REFLEXIVE" (list x) (list (car ints))))
           (impossible (proof-proof-cut proof loop no-loop))
           (fronted (proof-proof-front proof impossible (proof-neg yx)))
           (ix-first (proof-step-first (car ints)))
           (iy-first (proof-step-first (cadr ints)))
           (p (library-library-lemma p "H2-INTEGER-ASYMMETRY" (proof-neg yx) fronted
                                     (list (proof-neg ix-first) (proof-neg iy-first) (proof-neg xy))))
           (proof (library-library-proof p))
           (xy-eq (proof-proof-assume proof (proof-eq x y) t))
           (reversed (proof-proof-symmetric proof xy-eq))
           (loop (proof-proof-rewrite proof xy-pos reversed '(1 2)))
           (impossible (proof-proof-cut proof loop no-loop))
           (eq-first (proof-step-first xy-eq))
           (fronted (proof-proof-front proof impossible (proof-neg eq-first)))
           (p (library-library-lemma p "H2-LESS-IMPLIES-UNEQUAL" (proof-neg eq-first) fronted
                                     (list (proof-neg ix-first) (proof-neg xy))))
           (p (h2-arithmetic-integer-trichotomy p x y xy yx ints)))
        (h2-arithmetic-integer-nonnil p x (car ints))))))

(defun h2-arithmetic-index-type-and-bound (p x successor predecessor ix)
  (let* ((proof (library-library-proof p))
         (is-pos (library-positive x))
         (zp-test (list *h2-arithmetic-zp* x)))
    (proof-with-checked-results
        ((zp-body (proof-proof-unfold proof zp-test))
         (negative (proof-proof-assume proof zp-test nil))
         (denied-body (proof-proof-rewrite proof negative zp-body '(1 1)))
         (body (h2-alists-logical-result zp-body))
         (if-false (proof-proof-if-false proof body))
         (denied-true (proof-proof-rewrite proof denied-body if-false '(1 1)))
         (opening (proof-proof-unfold proof (proof-neg *proof-true*)))
         (truth (proof-proof-prove proof *proof-true* nil nil))
         (selection (proof-proof-select proof (proof-ite *proof-true* *proof-false* *proof-true*) truth))
         (not-true (proof-proof-chain proof opening (list selection)))
         (has-integer (proof-proof-rewrite proof denied-true not-true '(1)))
         (has-integer (proof-proof-tidy proof has-integer))
         (ix-first (proof-step-first ix))
         (has-integer (proof-proof-front proof has-integer ix-first))
         (p (library-library-lemma p "H2-POSITIVE-INDEX-INTEGER" ix-first has-integer (list zp-test)))
         (proof (library-library-proof p))
         (selection (proof-proof-select proof body has-integer))
         (denied-inner (proof-proof-rewrite proof denied-body selection '(1 1)))
         (negative-pos (proof-proof-assume proof is-pos nil))
         (has-positive (proof-proof-cut proof negative-pos denied-inner))
         (fronted (proof-proof-front proof has-positive is-pos))
         (p (library-library-lemma p "H2-POSITIVE-INDEX-POSITIVE" is-pos fronted (list zp-test)))
         (proof (library-library-proof p))
         (positive-index (proof-proof-front proof has-positive is-pos))
         (discrete (proof-proof-fact proof "integer-discrete" nil))
         (first (proof-step-first discrete))
         (premise (proof-term-at first 1))
         (pair (proof-proof-prove proof premise (list has-integer positive-index) nil))
         (bound (proof-proof-modus-ponens proof discrete pair))
         (axiom (library-library-axiom p "<-ON-OTHERS" (list x *proof-one*)))
         (bound (proof-proof-rewrite proof bound axiom '(1 1)))
         (shift (library-library-axiom p "COMMUTATIVITY-OF-+" (list x (library-minus *proof-one*))))
         (minus-one (proof-proof-compute proof (library-minus *proof-one*) -1))
         (shift (proof-proof-rewrite proof shift minus-one '(1 2 1)))
         (bound (proof-proof-rewrite proof bound shift '(1 1 1)))
         (p (library-library-lemma p "H2-PREDECESSOR-NONNEGATIVE"
                                   (library-nonnegative predecessor) bound (list zp-test)))
         (add1-sub1 (library-library-linear-equal p (library-plus *proof-neg-one* successor) x (list ix))))
      (library-library-lemma p "H2-ADD1-SUB1" (proof-eq (library-plus *proof-neg-one* successor) x)
                             add1-sub1 (list (proof-neg ix-first))))))

(defun h2-arithmetic-index-lemmas-equality-value (term evidence holds p)
  (let ((proof (library-library-proof p)))
    (if holds
        (proof-with-checked-results
            ((left (proof-term-at term 1))
             (step (proof-proof-fact proof "equal-same" (list (list *library-x* left)))))
          (proof-proof-rewrite proof step evidence '(1 1 2)))
      (proof-with-checked-results
          ((clause (proof-proof-fact proof "equal-different" (seq-zip (list *library-x* *library-y*) (cdr term))))
           (step (proof-proof-front proof clause (proof-eq term *proof-false*))))
        (proof-proof-discharge proof step evidence)))))

(defun h2-arithmetic-index-injectivity (p x y predecessor ix iy)
  (proof-with-checked-results
      ((drop (library-library-linear-equal p (library-plus *proof-one* predecessor) x (list ix)))
       (drop-first (proof-step-first drop))
       (ix-first (proof-step-first ix))
       (p (library-library-lemma p "H2-SUB1-ADD1" drop-first drop (list (proof-neg ix-first)))))
    (let* ((proof (library-library-proof p))
           (other (library-plus *proof-neg-one* y))
           (compare (proof-eq predecessor other)))
      (proof-with-checked-results
          ((recover (library-library-linear-equal p (library-plus *proof-one* other) y (list iy)))
           (assumed (proof-proof-assume proof compare t))
           (reversed-drop (proof-proof-symmetric proof drop))
           (reversed-assumed (proof-proof-symmetric proof assumed))
           (recover (proof-proof-rewrite proof recover reversed-assumed '(1 1 2)))
           (same (proof-proof-chain proof reversed-drop (list recover)))
           (identity (proof-proof-reflexive proof predecessor))
           (assumed (proof-proof-assume proof (proof-eq x y) t))
           (opposite-same (proof-proof-rewrite proof identity assumed '(1 2 2))))
        (let ((test (proof-eq x y)))
          (proof-with-checked-results
              ((yes-test (proof-proof-assume proof test t))
               (yes-compare (h2-arithmetic-index-lemmas-equality-value compare opposite-same t p))
               (yes-equality (h2-arithmetic-index-lemmas-equality-value test yes-test t p))
               (yes-equality (proof-proof-symmetric proof yes-equality))
               (yes (proof-proof-chain proof yes-compare (list yes-equality)))
               (no-test (proof-proof-assume proof test nil))
               (cut (proof-proof-cut proof same no-test))
               (no-compare (proof-proof-front proof cut (proof-neg compare)))
               (no-value (h2-arithmetic-index-lemmas-equality-value compare no-compare nil p))
               (no-equality (h2-arithmetic-index-lemmas-equality-value test no-test nil p))
               (no-equality (proof-proof-symmetric proof no-equality))
               (no (proof-proof-chain proof no-value (list no-equality)))
               (cases (proof-proof-cases proof test yes no))
               (iy-first (proof-step-first iy)))
            (library-library-lemma p "H2-PREDECESSOR-INJECTIVE" (proof-eq compare test) cases
                                   (list (proof-neg ix-first) (proof-neg iy-first)))))))))

(defun h2-arithmetic-index-nfix (p replies x predecessor)
  (let ((zp-test (list *h2-arithmetic-zp* x))
        (nfix-x (list *h2-arithmetic-nfix* x)))
    (h2-alists-with-derivations p replies
        ((natural (h2-alists-auxiliary
                   p replies "NFIX-WHEN-NATURAL"
                   (list *h2-arithmetic-implies*
                         (proof-ite (library-integer x) (library-nonnegative x) *proof-false*)
                         (proof-eq nfix-x x))
                   "NFIX" nil nil nil 80))
         (zero (h2-alists-auxiliary
                p replies "NFIX-WHEN-ZP"
                (list *h2-arithmetic-implies* zp-test (proof-eq nfix-x *proof-zero*))
                "NFIX ZP" '("SELF-H2-INTEGER-EQUAL-WHEN-NEITHER-LESS") nil
                (list (library-integer x) (library-positive x) (library-lt x *proof-zero*)) 80))
         (positive (h2-alists-auxiliary
                    p replies "NFIX-WHEN-NOT-ZP"
                    (list *h2-arithmetic-implies* (proof-neg zp-test) (proof-eq nfix-x x))
                    "NFIX" (list natural "SELF-H2-POSITIVE-INDEX-INTEGER" "SELF-H2-POSITIVE-INDEX-POSITIVE"
                                 "SELF-POSITIVE-NONNEGATIVE")
                    nil nil 80))
         (pred (h2-alists-auxiliary
                p replies "NFIX-PREDECESSOR"
                (list *h2-arithmetic-implies* (proof-neg zp-test)
                      (proof-eq (list *h2-arithmetic-nfix* predecessor) predecessor))
                "" (list natural "SELF-H2-POSITIVE-INDEX-INTEGER" "SELF-INTEGER-SUM"
                         "SELF-H2-PREDECESSOR-NONNEGATIVE")
                nil nil 80)))
      (h2-alists-derivation-result nil p replies))))

(defun h2-arithmetic-index-predecessor-bound (p x y predecessor ints)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((a (library-library-comparison p predecessor y ints))
         (b (library-library-comparison p x (library-plus *proof-one* y) ints))
         (a-right (h2-alists-logical-result a))
         (a-delta (proof-term-at a-right 2))
         (b-right (h2-alists-logical-result b))
         (b-delta (proof-term-at b-right 2))
         (delta (library-library-linear-equal p a-delta b-delta ints))
         (shifted (proof-proof-rewrite proof a delta '(1 2 2)))
         (reversed (proof-proof-symmetric proof b))
         (step (proof-proof-chain proof shifted (list reversed)))
         (first (proof-step-first step))
         (ix-first (proof-step-first (car ints)))
         (iy-first (proof-step-first (cadr ints))))
      (library-library-lemma p "H2-PREDECESSOR-BOUND" first step
                             (list (proof-neg ix-first) (proof-neg iy-first))))))

(defun h2-arithmetic-index-prepare (p x y successor predecessor ints)
  (if (h2-alists-has-fact p "SELF-H2-PREDECESSOR-INJECTIVE")
      p
    (proof-with-checked-results
        ((p (h2-arithmetic-index-type-and-bound p x successor predecessor (car ints))))
      (h2-arithmetic-index-injectivity p x y predecessor (car ints) (cadr ints)))))

(defun h2-arithmetic-index-derivations (p replies)
  (proof-with-checked-results ((p (h2-arithmetic-integer-order p)))
    (if (h2-alists-has-fact p "SELF-H2-PREDECESSOR-BOUND")
        (h2-alists-derivation-result nil p replies)
      (let* ((x *library-x*)
             (y *library-y*)
             (successor (library-plus *proof-one* x))
             (predecessor (library-plus *proof-neg-one* x)))
        (proof-with-checked-results
            ((ints (library-library-ints p (list x y)))
             (p (h2-arithmetic-index-prepare p x y successor predecessor ints)))
          (h2-alists-with-derivations p replies
              ((nfix (h2-arithmetic-index-nfix p replies x predecessor)))
            (proof-with-checked-results
                ((p (h2-arithmetic-index-predecessor-bound p x y predecessor ints)))
              (h2-alists-derivation-result nil p replies))))))))

(defun h2-arithmetic-finish-derivations (result)
  (cond ((failure-p result) result)
        ((h2-alists-request-p (car result)) (h2-alists-finish-derivations result))
        (t (cadr result))))

(defun h2-arithmetic-index-lemmas (p replies)
  (h2-arithmetic-finish-derivations (h2-arithmetic-index-derivations p replies)))

(defun h2-arithmetic-maximum-comparison (p label a b c d integers)
  (let ((name (concatenate 'string "H2-" label))
        (proof (library-library-proof p)))
    (if (h2-alists-has-fact p (concatenate 'string "SELF-" name))
        p
      (proof-with-checked-results
          ((shifted (library-library-comparison p a b integers))
           (direct (library-library-comparison p c d integers))
           (shifted-right (h2-alists-logical-result shifted))
           (shifted-delta (proof-term-at shifted-right 2))
           (direct-right (h2-alists-logical-result direct))
           (direct-delta (proof-term-at direct-right 2))
           (delta (library-library-linear-equal p shifted-delta direct-delta integers))
           (rewritten (proof-proof-rewrite proof shifted delta '(1 2 2)))
           (reversed (proof-proof-symmetric proof direct))
           (equality (proof-proof-chain proof rewritten (list reversed)))
           (first (proof-step-first equality)))
        (let* ((x-guard (proof-neg (library-integer *library-x*)))
               (guards (if (equal label "LESS-SUCCESSORS")
                           (list x-guard (proof-neg (library-integer *library-y*)))
                         (list x-guard))))
          (library-library-lemma p name first equality guards))))))

(defun h2-arithmetic-maximum-lemmas (p replies)
  (h2-arithmetic-finish-derivations
   (h2-alists-with-derivations p replies
       ((index (h2-arithmetic-index-derivations p replies)))
     (if (h2-alists-has-fact p "SELF-H2-MAX-SUCCESSOR")
         (h2-alists-derivation-result nil p replies)
       (let* ((x *library-x*)
              (y *library-y*)
              (successor-x (library-plus *proof-one* x))
              (successor-y (library-plus *proof-one* y))
              (maximum (proof-cl "MAX")))
         (proof-with-checked-results
             ((integers (library-library-ints p (list x y)))
              (p (h2-arithmetic-maximum-comparison p "LESS-SUCCESSORS" successor-x successor-y x y integers))
              (p (h2-arithmetic-maximum-comparison p "LESS-SUCCESSOR-ONE" successor-x *proof-one* x
                                                  *proof-zero* integers)))
           (let* ((shifted (list maximum successor-x successor-y))
                  (direct (list maximum x y))
                  (goal (list *h2-arithmetic-implies*
                              (proof-ite (library-integer x) (library-integer y) *proof-false*)
                              (proof-eq shifted (library-plus *proof-one* direct)))))
             (h2-alists-auxiliary p replies "MAX-SUCCESSOR" goal "MAX"
                                  '("SELF-H2-LESS-SUCCESSORS") nil nil 80))))))))
