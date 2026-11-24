(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-truncate-intervals-truncate-bounds*
  (proof-sym "TRUNCATE-BOUNDS" "ACL2"))

(defun b2-truncate-intervals-zero-scaled-comparisons
    (lib ratio scale ratio-type scale-type positive reduced)
  (b2-reciprocal-results lib
      ((zero-type (library-library-rational lib *proof-zero* nil))
       (zero (b2-products-zero-product lib scale) :library)
       (first (b2-scaling-rational-scale-order lib ratio *proof-zero* scale
                                              (list ratio-type zero-type scale-type)
                                              positive) :library)
       (last (b2-scaling-rational-scale-order lib *proof-zero* ratio scale
                                             (list zero-type ratio-type scale-type)
                                             positive) :library)
       (left (b2-reciprocal-rewrite lib first reduced '(1 1 1)))
       (left (b2-reciprocal-rewrite lib left zero '(1 1 2)))
       (right (b2-reciprocal-rewrite lib last reduced '(1 1 2)))
       (right (b2-reciprocal-rewrite lib right zero '(1 1 1)))
       (left (b2-reciprocal-tidy lib left))
       (right (b2-reciprocal-tidy lib right)))
    (cons (list left right) lib)))

(defun b2-truncate-intervals-positive-ratio-scale (lib x y rx ry sign negative)
  (let* ((inverse (list *b2-products-recip* y))
         (ratio (b2-products-product x inverse)))
    (b2-reciprocal-results lib
        ((inverse-type (b2-scaling-rational-op lib "unary-/" inverse (list ry)))
         (rr (b2-scaling-rational-op lib "binary-*" ratio (list rx inverse-type)))
         (cancels (b2-floor-intervals-restored-dividend lib x y rx ry sign)))
      (if (not negative)
          (cons (list ratio y rr ry sign cancels) lib)
        (let ((mirror (library-minus y)))
          (b2-reciprocal-results lib
              ((opposite (b2-scaling-opposite-sign lib y ry))
               (positive (proof-proof-transport (library-library-proof lib) sign opposite))
               (typed-scale (b2-scaling-rational-op lib "unary--" mirror (list ry)))
               (rendered (b2-fraction-reduction-negative-first lib y ratio) :library)
               (rendered (b2-reciprocal-rewrite lib rendered cancels '(1 2 1)))
               (rendered (b2-reciprocal-tidy lib rendered)))
            (cons (list ratio mirror rr typed-scale positive rendered) lib)))))))

(defun b2-truncate-intervals-ratio-comparisons (lib x y rx ry sign negative)
  (b2-reciprocal-results lib
      ((scaling (b2-truncate-intervals-positive-ratio-scale lib x y rx ry sign negative) :library)
       (bounds (b2-truncate-intervals-zero-scaled-comparisons
                lib (nth 0 scaling) (nth 1 scaling) (nth 2 scaling)
                (nth 3 scaling) (nth 4 scaling) (nth 5 scaling)) :library))
    (if (not negative)
        (cons bounds lib)
      (let ((negated-x (library-minus x)))
        (b2-reciprocal-results lib
            ((type-x (b2-scaling-rational-op lib "unary--" negated-x (list rx)))
             (reflected-positive (b2-scaling-opposite-sign lib negated-x type-x))
             (numeric (b2-scaling-number-of-rational lib x rx))
             (double (b2-fraction-reduction-twice-negated lib x numeric))
             (positive-x (b2-reciprocal-rewrite lib reflected-positive double '(1 1 2)))
             (low (b2-reciprocal-chain lib positive-x (car bounds)))
             (opposite (b2-scaling-opposite-sign lib x rx))
             (reverse (b2-reciprocal-symmetric lib opposite))
             (high (b2-reciprocal-chain lib reverse (cadr bounds))))
          (cons (list low high) lib))))))

(defun b2-truncate-intervals-truncate-interval-prove-bounds
    (low high opening is-negative lib below above)
  (b2-reciprocal-results lib
      ((back (b2-reciprocal-symmetric lib opening))
       (low-at (if is-negative '(1 1 1) '(1 1 2)))
       (high-at (if is-negative '(1 1 2) '(1 2 2)))
       (low (b2-reciprocal-rewrite lib low back low-at))
       (low (b2-reciprocal-tidy lib low))
       (high (b2-reciprocal-rewrite lib high back high-at))
       (high (b2-reciprocal-tidy lib high)))
    (b2-reciprocal-solve lib (if is-negative below above) (list low high))))

(defun b2-truncate-intervals-truncate-interval-prove-denominator-unit
    (cases lib q n nt alias goal nonnegative nonpositive above below)
  (b2-reciprocal-results lib
      ((substituted (b2-reciprocal-rewrite lib alias (car (last cases)) '(1 1 2 1)))
       (commute (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" n *proof-one*))
       (numeric (library-library-number lib n (list nt)))
       (unit (b2-products-multiplicative-unit lib n numeric))
       (mul-unit (b2-reciprocal-chain lib commute unit))
       (equality (proof-step-first substituted))
       (equation (b2-reciprocal-normalize lib (cadr equality) nil nil (list mul-unit)))
       (same (b2-reciprocal-rewrite lib substituted equation '(1 1)))
       (same (b2-reciprocal-tidy lib same))
       (opened (b2-reciprocal-normalize lib q cases (list q)))
       (low (library-library-cite lib "WEAK-REFLEXIVE" (list n) (list nt)))
       (larger (library-library-cite lib "SUCCESSOR-LARGER" (list n) (list nt)))
       (smaller (b2-bounds-prove-integer-bound
                 lib (library-lt (library-plus *proof-neg-one* n) n) (list nt)))
       (pos-lower (b2-reciprocal-rewrite lib low same '(1 1 1)))
       (pos-upper (b2-reciprocal-rewrite lib larger same '(1 1)))
       (pos (b2-truncate-intervals-truncate-interval-prove-bounds
             pos-lower pos-upper opened nil lib below above))
       (neg-lower (b2-reciprocal-rewrite lib low same '(1 1 2)))
       (neg-upper (b2-reciprocal-rewrite lib smaller same '(1 2)))
       (negated (b2-truncate-intervals-truncate-interval-prove-bounds
                 neg-lower neg-upper opened t lib below above))
       (yes (b2-reciprocal-imply lib nonnegative above premise (cons pos lib)) :library)
       (no (b2-reciprocal-imply lib nonpositive below premise (cons negated lib)) :library))
    (b2-reciprocal-return lib (b2-reciprocal-solve lib goal (list yes no)))))

(defun b2-truncate-intervals-truncate-interval-prove-denominator-numerator-impossible
    (premise lib invalid above)
  (b2-reciprocal-results lib
      ((contradiction (proof-proof-cut (library-library-proof lib) invalid premise)))
    (b2-reciprocal-return lib
      (proof-proof-subsume (library-library-proof lib) contradiction
                          (cons above (proof-step-clause contradiction))))))

(defun b2-truncate-intervals-truncate-interval-prove-denominator-numerator-cannot
    (premise lib compare n nt n-sign alias d ratio d-test below)
  (b2-reciprocal-results lib
      ((back (b2-reciprocal-symmetric lib (cadr compare)))
       (no-positive-n (b2-reciprocal-rewrite lib premise back '(1 1)))
       (no-positive-n (b2-reciprocal-tidy lib no-positive-n))
       (zero (b2-powers-zero-from-signs lib n nt n-sign no-positive-n))
       (unnamed (b2-reciprocal-rewrite lib alias zero '(1 1 1)))
       (inverse (list *b2-products-recip* d))
       (commute (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" *proof-zero* inverse))
       (zero-product (b2-products-zero-product lib inverse) :library)
       (zero-product (b2-reciprocal-chain lib commute zero-product))
       (unnamed (b2-reciprocal-rewrite lib unnamed zero-product '(1 1)))
       (typed (library-library-type-of lib *proof-zero* nil))
       (typed (b2-reciprocal-rewrite lib typed unnamed '(1 1)))
       (typed (b2-reciprocal-tidy lib typed))
       (integer-denominator (b2-products-integer-denominator lib ratio typed) :library)
       (contradiction (proof-proof-cut (library-library-proof lib) integer-denominator d-test)))
    (b2-reciprocal-return lib
      (proof-proof-subsume (library-library-proof lib) contradiction
                          (cons below (proof-step-clause contradiction))))))

(defun b2-truncate-intervals-truncate-interval-prove-denominator-numerator-negative
    (lib n d nt nr dt dp n-sign alias ratio r-type compare opened
         goal nonnegative nonpositive above below)
  (let ((magnitude (library-minus n)))
    (b2-reciprocal-results lib
        ((mag-type (library-library-type-of lib magnitude (list nt)))
         (mag-rational (library-library-rational lib magnitude (list mag-type)))
         (opposite (b2-scaling-opposite-sign lib n nr))
         (magnitude-positive (proof-proof-transport (library-library-proof lib) n-sign opposite))
         (nonneg (b2-scaling-positive-is-nonnegative lib magnitude magnitude-positive mag-rational))
         (data (b2-quotient-interval-quotient-data lib magnitude d mag-type nonneg dt dp) :library)
         (q-type (proof-step-first (car data)))
         (p (cadr q-type))
         (reflected (library-minus ratio))
         (change (b2-fraction-reduction-negative-first lib n (list *b2-products-recip* d)) :library)
         (change (b2-reciprocal-rewrite lib change alias '(1 2 1)))
         (change (b2-reciprocal-tidy lib change))
         (low (b2-reciprocal-rewrite lib (cadr data) change '(1 1 1)))
         (low (b2-reciprocal-tidy lib low))
         (high (b2-reciprocal-rewrite lib (caddr data) change '(1 1)))
         (high (b2-reciprocal-tidy lib high))
         (numeric (b2-scaling-number-of-rational lib ratio r-type))
         (double (b2-fraction-reduction-twice-negated lib ratio numeric))
         (weak-flip (b2-rational-order-reverse-negations lib p reflected))
         (weak-flip (b2-reciprocal-symmetric lib weak-flip))
         (lower (b2-reciprocal-rewrite lib low weak-flip '(1 1)))
         (lower (b2-reciprocal-tidy lib lower))
         (lower (b2-reciprocal-rewrite lib lower double '(1 1 2)))
         (lower (b2-reciprocal-tidy lib lower))
         (flip (b2-rational-order-reverse-negations lib (library-plus *proof-one* p) reflected))
         (upper (proof-proof-transport (library-library-proof lib) high flip))
         (signs-negated (b2-reciprocal-axiom lib "DISTRIBUTIVITY-OF-MINUS-OVER-+" *proof-one* p))
         (minus-one (proof-proof-compute (library-library-proof lib) (library-minus *proof-one*) -1))
         (signs-negated (b2-reciprocal-rewrite lib signs-negated minus-one '(1 2 1)))
         (signs-negated (b2-reciprocal-tidy lib signs-negated))
         (upper (b2-reciprocal-rewrite lib upper signs-negated '(1 1)))
         (upper (b2-reciprocal-rewrite lib upper double '(1 2)))
         (upper (b2-reciprocal-tidy lib upper))
         (valid (b2-truncate-intervals-truncate-interval-prove-bounds
                 lower upper opened t lib below above))
         (invalid (b2-reciprocal-rewrite lib n-sign (car compare)))
         (invalid (b2-reciprocal-tidy lib invalid))
         (yes (b2-reciprocal-imply lib nonnegative above premise
                (b2-truncate-intervals-truncate-interval-prove-denominator-numerator-impossible
                 premise lib invalid above)) :library)
         (no (b2-reciprocal-imply lib nonpositive below premise (cons valid lib)) :library))
      (b2-reciprocal-return lib (b2-reciprocal-solve lib goal (list yes no))))))

(defun b2-truncate-intervals-truncate-interval-prove-denominator-numerator
    (is-negative signs lib q n d nt nr dt dp alias ratio r-type compare
                 d-test goal nonnegative nonpositive above below)
  (b2-reciprocal-results lib
      ((n-sign (car (last signs)))
       (opened (b2-reciprocal-normalize lib q signs (list q))))
    (if is-negative
        (b2-truncate-intervals-truncate-interval-prove-denominator-numerator-negative
         lib n d nt nr dt dp n-sign alias ratio r-type compare opened
         goal nonnegative nonpositive above below)
      (b2-reciprocal-results lib
          ((data (b2-quotient-interval-quotient-data lib n d nt n-sign dt dp) :library)
           (low (b2-reciprocal-rewrite lib (cadr data) alias '(1 1 1)))
           (high (b2-reciprocal-rewrite lib (caddr data) alias '(1 1)))
           (valid (b2-truncate-intervals-truncate-interval-prove-bounds
                   low high opened nil lib below above))
           (yes (b2-reciprocal-imply lib nonnegative above premise (cons valid lib)) :library)
           (no (b2-reciprocal-imply lib nonpositive below premise
                 (b2-truncate-intervals-truncate-interval-prove-denominator-numerator-cannot
                  premise lib compare n nt n-sign alias d ratio d-test below)) :library))
        (b2-reciprocal-return lib (b2-reciprocal-solve lib goal (list yes no)))))))

(defun b2-truncate-intervals-truncate-interval-prove-denominator
    (unit cases lib q n d nt nr dt dp alias ratio r-type compare
          goal nonnegative nonpositive above below)
  (if unit
      (b2-truncate-intervals-truncate-interval-prove-denominator-unit
       cases lib q n nt alias goal nonnegative nonpositive above below)
    (let ((d-test (car (last cases))))
      (b2-reciprocal-choose lib (library-lt n *proof-zero*) cases is-negative signs
        (b2-truncate-intervals-truncate-interval-prove-denominator-numerator
         is-negative signs lib q n d nt nr dt dp alias ratio r-type compare
         d-test goal nonnegative nonpositive above below)))))

(defun b2-truncate-intervals-truncate-interval-prove
    (premise lib q ratio n d goal nonnegative nonpositive above below)
  (b2-reciprocal-results lib
      ((types (proof-proof-conjunct (library-library-proof lib) premise))
       (reciprocal-type (b2-scaling-rational-op lib "unary-/" (caddr ratio) (list (cadr types))))
       (r-type (b2-scaling-rational-op lib "binary-*" ratio (list (car types) reciprocal-type)))
       (factors (b2-products-rational-factors lib ratio r-type))
       (dt (car factors))
       (nt (cadr factors))
       (dp (caddr factors))
       (nr (library-library-rational lib n (list nt)))
       (dr (library-library-rational lib d (list dt)))
       (representation (b2-reciprocal-axiom lib "RATIONAL-IMPLIES2" ratio))
       (represented (proof-proof-modus-ponens (library-library-proof lib) representation r-type))
       (commute (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" n (list *b2-products-recip* d)))
       (alias (b2-reciprocal-chain lib commute represented))
       (commute (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" d ratio))
       (rat-product (b2-products-rational-product lib ratio r-type) :library)
       (scaled (b2-reciprocal-chain lib commute rat-product))
       (compare (b2-truncate-intervals-zero-scaled-comparisons
                 lib ratio d r-type dr dp scaled) :library))
    (b2-reciprocal-choose lib (proof-eq d *proof-one*) nil unit cases
      (b2-truncate-intervals-truncate-interval-prove-denominator
       unit cases lib q n d nt nr dt dp alias ratio r-type compare
       goal nonnegative nonpositive above below))))

(defun b2-truncate-intervals-truncate-interval-lemma (lib)
  (let* ((name (proof-sym "B2-TRUNCATE-INTERVAL" "ACL2"))
         (proof (library-library-proof lib)))
    (if (assoc-equal name (proof-proof-facts proof))
        (cons name lib)
      (let* ((q (list *b2-numeric-types-truncate* *library-x* *library-y*))
             (ratio (b2-products-product *library-x* (list *b2-products-recip* *library-y*)))
             (n (list *b2-products-num* ratio))
             (d (list *b2-products-den* ratio))
             (nonnegative (proof-neg (library-lt ratio *proof-zero*)))
             (nonpositive (proof-neg (library-lt *proof-zero* ratio))))
        (b2-reciprocal-results lib
            ((condition (b2-powers-and-terms (list (list *library-rationalp* *library-x*)
                                                 (list *library-rationalp* *library-y*))))
             (above (b2-powers-and-terms (list (proof-neg (library-lt ratio q))
                                             (library-lt ratio (library-plus *proof-one* q)))))
             (below (b2-powers-and-terms (list (proof-neg (library-lt q ratio))
                                             (library-lt (library-plus *proof-neg-one* q) ratio))))
             (goal (b2-powers-and-terms (list (list *library-implies* nonnegative above)
                                            (list *library-implies* nonpositive below))))
             (step (b2-reciprocal-imply lib condition goal premise
                     (b2-truncate-intervals-truncate-interval-prove
                      premise lib q ratio n d goal nonnegative nonpositive above below)) :library))
          (b2-tactics-tactics-add-lemma lib "TRUNCATE-INTERVAL" step :none))))))

(defun b2-truncate-intervals-truncate-interval (lib x y rx ry sign negative)
  (b2-reciprocal-results lib
      ((name (b2-truncate-intervals-truncate-interval-lemma lib) :library)
       (step (proof-proof-fact (library-library-proof lib) name
                               (list (list *library-x* x) (list *library-y* y))))
       (formula (proof-step-first step))
       (antecedent (proof-term-at formula 1))
       (kind (b2-reciprocal-solve lib antecedent (list rx ry)))
       (both (proof-proof-modus-ponens (library-library-proof lib) step kind))
       (pair (proof-proof-conjunct (library-library-proof lib) both))
       (implication (if negative (cadr pair) (car pair)))
       (consequence (proof-proof-modus-ponens (library-library-proof lib) implication sign)))
    (b2-reciprocal-return lib (proof-proof-conjunct (library-library-proof lib) consequence))))

(defun b2-truncate-intervals-add-unit-at-right (lib inequality quotient-type)
  (b2-reciprocal-results lib
      ((first (proof-step-first inequality))
       (parts (proof-list-of-length first 3))
       (left (cadr parts))
       (right (caddr parts))
       (quotient (proof-term-at left 2))
       (cancel (b2-algebra-cancel-common-shift lib *proof-one* left right))
       (lifted (proof-proof-transport (library-library-proof lib) inequality cancel))
       (one-side (b2-tactics-tactics-linear-equal
                  lib (library-plus *proof-one* left) quotient (list quotient-type)))
       (swapped (b2-reciprocal-rewrite lib lifted one-side '(1 1)))
       (commute (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-+" *proof-one* right))
       (swapped (b2-reciprocal-rewrite lib swapped commute '(1 2))))
    (b2-reciprocal-tidy lib swapped)))

(defun b2-truncate-intervals-truncation-bounds-branch-consequent
    (given lib premise bounds negative negative-divisor)
  (b2-reciprocal-results lib
      ((known (b2-quotient-algebra-with-forced lib given))
       (parts (proof-list-of-length premise 4))
       (dividend-sign (cadr parts))
       (divisor-sign (proof-term-at (caddr parts) 1))
       (rx (b2-reciprocal-evidence-at known (list *library-rationalp* *library-x*)))
       (ry (b2-reciprocal-evidence-at known (list *library-rationalp* *library-y*)))
       (sign (b2-reciprocal-evidence-at known divisor-sign))
       (comparisons (b2-truncate-intervals-ratio-comparisons
                     lib *library-x* *library-y* rx ry sign negative-divisor) :library)
       (sign (b2-reciprocal-evidence-at known dividend-sign))
       (projected (b2-reciprocal-rewrite lib sign (if negative (cadr comparisons) (car comparisons)) '(1 1)))
       (projected (b2-reciprocal-tidy lib projected))
       (interval (b2-truncate-intervals-truncate-interval
                  lib *library-x* *library-y* rx ry projected negative) :library)
       (strong
        (if negative
            (b2-reciprocal-results lib
                ((types (b2-numeric-types-types-init lib))
                 (typed (b2-numeric-types-types-quotient-integer
                         types *b2-numeric-types-truncate* *library-x* *library-y*)))
              (let ((lib (b2-numeric-types-types-lib (cdr typed))))
                (b2-reciprocal-return lib
                  (b2-truncate-intervals-add-unit-at-right lib (cadr interval) (car typed)))))
          (b2-reciprocal-return lib (b2-quotient-interval-shift-bound lib (cadr interval)))) :library))
    (b2-reciprocal-return lib (b2-reciprocal-solve lib bounds (list (car interval) strong)))))

(defun b2-truncate-intervals-truncation-bounds-branch (implication negative negative-divisor lib)
  (b2-reciprocal-results lib
      ((parts (proof-list-of-length implication 3))
       (premise (cadr parts))
       (bounds (caddr parts)))
    (b2-reciprocal-imply lib premise bounds given
      (b2-truncate-intervals-truncation-bounds-branch-consequent
       given lib premise bounds negative negative-divisor))))

(defun b2-truncate-intervals-truncation-bounds-parts (lib tail indices)
  (declare (xargs :measure (acl2-count indices)))
  (if (endp indices)
      (cons nil lib)
    (let* ((index (car indices))
           (more (proof-is-call tail *proof-if*)))
      (b2-reciprocal-results lib
          ((item (if more (proof-term-at tail 1) tail))
           (step (b2-truncate-intervals-truncation-bounds-branch
                  item (<= 2 index) (or (equal index 1) (equal index 2)) lib) :library)
           (next (if more (proof-term-at tail 2) tail))
           (rest (b2-truncate-intervals-truncation-bounds-parts lib next (cdr indices)) :library))
        (cons (cons step rest) lib)))))

(defun b2-truncate-intervals-truncation-bounds (lib formula)
  (b2-reciprocal-results lib
      ((implications (b2-truncate-intervals-truncation-bounds-parts lib formula '(0 1 2 3)) :library))
    (b2-reciprocal-return lib (b2-reciprocal-solve lib formula implications))))
