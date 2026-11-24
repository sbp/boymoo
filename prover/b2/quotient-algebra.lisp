(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-quotient-algebra-exact-floor* '("sym" "ACL2" "FLOOR-=-X/Y"))
(defconst *b2-quotient-algebra-exact-truncate* '("sym" "ACL2" "TRUNCATE-=-X/Y"))
(defconst *b2-quotient-algebra-zero-mod* '("sym" "ACL2" "MOD-=-0"))
(defconst *b2-quotient-algebra-zero-rem* '("sym" "ACL2" "REM-=-0"))
(defconst *b2-quotient-algebra-cancel-unit*
  '(("sym" "ACL2" "FLOOR-CANCEL-*") ("sym" "ACL2" "TRUNCATE-CANCEL-*")))
(defconst *b2-quotient-algebra-move-factor*
  '(("sym" "ACL2" "REWRITE-FLOOR-X*Y-Z-LEFT")
    ("sym" "ACL2" "REWRITE-FLOOR-X*Y-Z-RIGHT")))
(defconst *b2-quotient-algebra-total-factors*
  '(("sym" "ACL2" "REWRITE-TRUNCATE-X*Y-Z-LEFT")
    ("sym" "ACL2" "REWRITE-TRUNCATE-X*Y-Z-RIGHT")))
(defconst *b2-quotient-algebra-cancel-factor* '("sym" "ACL2" "FLOOR-CANCEL-*-2"))
(defconst *b2-quotient-algebra-nonrational-sum*
  '(("sym" "ACL2" "NOT-RATIONALP-RATIONALP-PLUS")
    ("sym" "ACL2" "NOT-RATIONALP-RATIONALP-UNARY---PLUS")))
(defconst *b2-quotient-algebra-quotient-identities*
  (append (list *b2-quotient-algebra-exact-floor*
                (car *b2-quotient-algebra-cancel-unit*)
                *b2-quotient-algebra-cancel-factor*
                *b2-quotient-algebra-zero-mod*)
          *b2-quotient-algebra-nonrational-sum*
          (list *b2-quotient-algebra-zero-rem*)
          *b2-quotient-algebra-move-factor*
          *b2-quotient-algebra-total-factors*
          (list *b2-quotient-algebra-exact-truncate*
                (cadr *b2-quotient-algebra-cancel-unit*))))

(defun b2-quotient-algebra-required-evidence (known literal)
  (let ((entry (assoc-equal literal known)))
    (if entry
        (cdr entry)
      '(:failure "tactic-rejected" ""))))

(defun b2-quotient-algebra-with-forced (lib premise)
  (proof-with-checked-results
      ((known (b2-tactics-tactics-evidence lib (list premise)))
       (forced (b2-floor-intervals-force-facts lib premise)))
    (b2-tactics-tactics-evidence lib (append (table-values known)
                                            (table-values forced)))))

(defun b2-quotient-algebra-require-nonzero (lib value known)
  (let ((found (assoc-equal (proof-neg (proof-eq value *proof-zero*)) known)))
    (if found
        (cdr found)
      (proof-with-checked-results
          ((reversed (b2-quotient-algebra-required-evidence
                      known (proof-neg (proof-eq *proof-zero* value)))))
        (b2-strict-order-flipped-distinct lib *proof-zero* value reversed)))))

(defun b2-quotient-algebra-inverses (lib value known)
  (let* ((proof (library-library-proof lib))
         (reciprocal (list *b2-products-recip* value))
         (numeric (cdr (assoc-equal (list *library-numberp* value) known))))
    (proof-with-checked-results
        ((numeric (or numeric
                      (proof-with-checked-results
                          ((rational (b2-quotient-algebra-required-evidence
                                      known (list *library-rationalp* value))))
                        (b2-scaling-number-of-rational lib value rational))))
         (nonzero (b2-quotient-algebra-require-nonzero lib value known))
         (inverse (b2-products-reciprocal-identity lib value numeric nonzero))
         (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list reciprocal value)))
         (reverse (proof-proof-chain proof commuted (list inverse))))
      (list inverse reverse))))

(defun b2-quotient-algebra-exact-quotient-exact (premise lib quotient ratio equality)
  (proof-with-checked-results
      ((denominator (b2-products-integer-denominator lib ratio premise))
       (lib (cdr denominator))
       (rational (library-library-rational lib ratio (list premise)))
       (representation (b2-products-rational-product lib ratio rational))
       (lib (cdr representation)))
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((scaled (proof-proof-rewrite proof (car representation) (car denominator) '(1 1 2)))
           (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list ratio *proof-one*)))
           (numeric (b2-scaling-number-of-rational lib ratio rational))
           (unit (b2-products-multiplicative-unit lib ratio numeric))
           (unit (proof-proof-chain proof commuted (list unit)))
           (numerator (proof-proof-rewrite proof scaled unit '(1 1)))
           (numerator (proof-proof-tidy proof numerator))
           (numerator (proof-proof-symmetric proof numerator))
           (result (b2-tactics-tactics-solve
                    lib equality (list premise) (list quotient)
                    (list (car denominator) numerator) 0 nil)))
        (cons result lib)))))

(defun b2-quotient-algebra-exact-quotient (lib quotient ratio)
  (let ((equality (proof-eq quotient ratio))
        (integer (list *proof-integerp* ratio)))
    (proof-with-checked-results
        ((solver (b2-numeric-types-types-init lib))
         (parts (proof-list-of-length quotient 3))
         (typed (b2-numeric-types-types-quotient-integer solver
                                                        (car parts) (cadr parts) (caddr parts)))
         (lib (b2-numeric-types-types-lib (cdr typed))))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((yes (proof-proof-assume proof equality t))
             (no (proof-proof-assume proof equality nil))
             (forward (proof-proof-rewrite proof (car typed) yes '(1 1)))
             (forward (proof-proof-tidy proof forward))
             (positive (b2-algebra-boolean-equivalence-positive
                        lib (proof-eq equality integer) yes forward))
             (premise (proof-proof-assume proof integer t))
             (backward (b2-quotient-algebra-exact-quotient-exact premise lib quotient ratio equality))
             (lib (cdr backward))
             (result (b2-algebra-boolean-equivalence-negative lib equality integer
                                                               no positive (car backward))))
          (cons result lib))))))

(defun b2-quotient-algebra-ratio-congruence (lib left right equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left (proof-proof-unfold proof left))
         (right (proof-proof-unfold proof right))
         (left-eq (proof-step-first left))
         (term (proof-term-at left-eq 2))
         (congruent (b2-algebra-congruence lib equation term '(1)))
         (right (proof-proof-symmetric proof right)))
      (proof-proof-chain proof left (list congruent right)))))

(defun b2-quotient-algebra-regroup-pairs (lib a b c d)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (library-library-axiom lib "ASSOCIATIVITY-OF-*"
                                      (list a b (b2-products-product c d))))
         (swap (b2-products-product-swap lib b c d))
         (swap (proof-proof-rewrite proof first swap '(1 2 2)))
         (last (library-library-axiom lib "ASSOCIATIVITY-OF-*"
                                     (list a c (b2-products-product b d))))
         (last (proof-proof-symmetric proof last)))
      (proof-proof-chain proof swap (list last)))))

(defun b2-quotient-algebra-reciprocal-of-pair (lib a b c d unit-a unit-b)
  (let* ((proof (library-library-proof lib))
         (scaled (b2-products-product a b))
         (proposed (b2-products-product c d))
         (zero (proof-eq scaled *proof-zero*)))
    (proof-with-checked-results
        ((result (b2-quotient-algebra-regroup-pairs lib a b c d))
         (result (proof-proof-rewrite proof result unit-a '(1 2 1)))
         (result (proof-proof-rewrite proof result unit-b '(1 2 2)))
         (one (proof-proof-compute proof (b2-products-product *proof-one* *proof-one*) 1))
         (result (proof-proof-chain proof result (list one)))
         (assumed (proof-proof-assume proof zero t))
         (impossible (proof-proof-rewrite proof result assumed '(1 1 1)))
         (zero-product (b2-products-zero-left-product lib proposed))
         (lib (cdr zero-product)))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((impossible (proof-proof-rewrite proof impossible (car zero-product) '(1 1)))
             (distinct (proof-proof-compute proof (proof-eq *proof-zero* *proof-one*) *proof-nil*))
             (impossible (proof-proof-rewrite proof impossible distinct '(1)))
             (impossible (proof-proof-tidy proof impossible))
             (nonzero (proof-proof-front proof impossible (proof-neg zero)))
             (numeric (b2-products-numeric-closure lib scaled))
             (inverse (b2-products-inverse-from-product lib result numeric nonzero))
             (symmetric (proof-proof-symmetric proof inverse)))
          (cons symmetric lib))))))

(defun b2-quotient-algebra-cancel-to-value (lib value factor known)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((units (b2-quotient-algebra-inverses lib factor known))
         (opened (library-library-axiom lib "ASSOCIATIVITY-OF-*"
                                       (list value factor (list *b2-products-recip* factor))))
         (reduced (proof-proof-rewrite proof opened (car units) '(1 2 2)))
         (rational (b2-quotient-algebra-required-evidence known (list *library-rationalp* value)))
         (numeric (b2-scaling-number-of-rational lib value rational))
         (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list value *proof-one*)))
         (unit (b2-products-multiplicative-unit lib value numeric)))
      (proof-proof-chain proof reduced (list commuted unit)))))

(defun b2-quotient-algebra-unit-cancellation (lib goal known)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length goal 4))
         (first (proof-list-of-length (cadr parts) 3))
         (quotient (proof-list-of-length (cadr first) 3))
         (numerator (proof-list-of-length (cadr quotient) 3)))
      (let* ((value (cadr numerator))
             (factor (caddr numerator))
             (right (caddr first))
             (inv (list *b2-products-recip* factor))
             (reciprocal-one (list *b2-products-recip* *proof-one*)))
        (proof-with-checked-results
            ((reduced (b2-quotient-algebra-cancel-to-value lib value factor known))
             (rational (b2-quotient-algebra-required-evidence known (list *library-rationalp* value)))
             (numeric (b2-scaling-number-of-rational lib value rational))
             (division-by-one (proof-proof-reflexive proof (b2-products-product value reciprocal-one)))
             (one (proof-proof-compute proof reciprocal-one 1))
             (division-by-one (proof-proof-rewrite proof division-by-one one '(1 2 2)))
             (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list value *proof-one*)))
             (unit (b2-products-multiplicative-unit lib value numeric))
             (division-by-one (proof-proof-chain proof division-by-one (list commuted unit)))
             (division-by-one (proof-proof-symmetric proof division-by-one))
             (division-first (proof-proof-chain proof reduced (list division-by-one)))
             (commutation (library-library-axiom lib "COMMUTATIVITY-OF-*" (list factor value)))
             (commutation (b2-algebra-congruence lib commutation
                                                (b2-products-product (b2-products-product factor value) inv)
                                                '(1)))
             (division-second (proof-proof-chain proof commutation (list division-first)))
             (first (b2-quotient-algebra-ratio-congruence lib (cadr first) right division-first))
             (second (proof-term-at (caddr parts) 1))
             (second (b2-quotient-algebra-ratio-congruence lib second right division-second)))
          (b2-tactics-tactics-solve lib goal (list first second) nil nil 0 nil))))))

(defun b2-quotient-algebra-factors-cancel (lib left right numerator denominator a b known)
  (proof-with-checked-results
      ((parts (proof-list-of-length denominator 3)))
    (let* ((z (caddr parts))
           (inv-a (list *b2-products-recip* a))
           (inv-z (list *b2-products-recip* z)))
      (proof-with-checked-results
          ((units-a (b2-quotient-algebra-inverses lib a known))
           (units-z (b2-quotient-algebra-inverses lib z known))
           (inverse (b2-quotient-algebra-reciprocal-of-pair lib a z inv-a inv-z
                                                            (car units-a) (car units-z)))
           (lib (cdr inverse)))
        (let ((proof (library-library-proof lib))
              (ratio (b2-products-product numerator (list *b2-products-recip* denominator)))
              (value (b2-products-product b inv-z)))
          (proof-with-checked-results
              ((step (b2-algebra-congruence lib (car inverse) ratio '(2)))
               (pairs (b2-quotient-algebra-regroup-pairs lib a b inv-a inv-z))
               (step (proof-proof-chain proof step (list pairs)))
               (step (proof-proof-rewrite proof step (car units-a) '(1 2 1)))
               (numeric (b2-products-numeric-closure lib value))
               (unit (b2-products-multiplicative-unit lib value numeric))
               (equation (proof-proof-chain proof step (list unit)))
               (result (b2-quotient-algebra-ratio-congruence lib left right equation)))
            (cons result lib)))))))

(defun b2-quotient-algebra-factors-move (lib left right numerator denominator a b known)
  (proof-with-checked-results
      ((parts (proof-list-of-length right 3)))
    (let* ((retained (cadr parts))
           (scaled (caddr parts))
           (factor (if (equal retained a) b a))
           (inv-factor (list *b2-products-recip* factor))
           (inv-denominator (list *b2-products-recip* denominator)))
      (proof-with-checked-results
          ((units-factor (b2-quotient-algebra-inverses lib factor known))
           (units-denominator (b2-quotient-algebra-inverses lib denominator known))
           (inverse (b2-quotient-algebra-reciprocal-of-pair lib denominator inv-factor inv-denominator
                                                            factor (car units-denominator) (cadr units-factor)))
           (lib (cdr inverse)))
        (let ((proof (library-library-proof lib))
              (source (b2-products-product numerator inv-denominator)))
          (proof-with-checked-results
              ((first (proof-proof-reflexive proof source))
               (first (if (equal a retained)
                          first
                        (proof-with-checked-results
                            ((swap (library-library-axiom lib "COMMUTATIVITY-OF-*" (list a b))))
                          (proof-proof-rewrite proof first swap '(1 2 1)))))
               (association (library-library-axiom lib "ASSOCIATIVITY-OF-*"
                                                    (list retained factor inv-denominator)))
               (first (proof-proof-chain proof first (list association)))
               (final (b2-algebra-congruence lib (car inverse)
                                              (b2-products-product retained (list *b2-products-recip* scaled))
                                              '(2)))
               (swap (library-library-axiom lib "COMMUTATIVITY-OF-*" (list inv-denominator factor)))
               (final (proof-proof-rewrite proof final swap '(1 2 2)))
               (final (proof-proof-symmetric proof final))
               (equation (proof-proof-chain proof first (list final)))
               (result (b2-quotient-algebra-ratio-congruence lib left right equation)))
            (cons result lib)))))))

(defun b2-quotient-algebra-factors (lib name goal known)
  (proof-with-checked-results
      ((parts (proof-list-of-length goal 3))
       (left (proof-list-of-length (cadr parts) 3))
       (numerator (proof-list-of-length (cadr left) 3)))
    (let ((right (caddr parts))
          (denominator (caddr left))
          (a (cadr numerator))
          (b (caddr numerator)))
      (if (equal name *b2-quotient-algebra-cancel-factor*)
          (b2-quotient-algebra-factors-cancel lib left right numerator denominator a b known)
        (b2-quotient-algebra-factors-move lib left right numerator denominator a b known)))))

(defun b2-quotient-algebra-zero-remainder-divisible
    (premise lib a b q remainder eliminate inverse-unit typed known)
  (let ((proof (library-library-proof lib))
        (reciprocal (list *b2-products-recip* b))
        (commuted (b2-products-product b q)))
    (proof-with-checked-results
        ((x-type (b2-quotient-algebra-required-evidence known (list *library-rationalp* a)))
         (numeric (b2-scaling-number-of-rational lib a x-type))
         (theorem (b2-tactics-tactics-use-fact
                   lib eliminate (proof-eq (library-plus remainder commuted) a)
                   (append (table-values known) (list numeric))
                   (list (proof-sym "FORCE" "ACL2")) nil 0 nil))
         (theorem (proof-proof-rewrite proof theorem premise '(1 1 1)))
         (numeric (b2-products-numeric-closure lib commuted))
         (unit (b2-fraction-reduction-sum-unit lib commuted numeric))
         (theorem (proof-proof-rewrite proof theorem unit '(1 1)))
         (theorem (proof-proof-tidy proof theorem))
         (numeric (library-library-number lib q (list typed)))
         (left (b2-products-distribute-cancel lib reciprocal b q inverse-unit numeric))
         (chained (proof-proof-rewrite proof left theorem '(1 1 2)))
         (chained (proof-proof-symmetric proof chained))
         (commutation (library-library-axiom lib "COMMUTATIVITY-OF-*" (list reciprocal a))))
      (proof-proof-chain proof chained (list commutation)))))

(defun b2-quotient-algebra-zero-remainder-no-remainder (premise lib remainder q restored a)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step (proof-proof-unfold proof remainder))
         (equality (proof-step-first step))
         (sum (proof-term-at equality 2))
         (opposite (proof-term-at sum 2))
         (multiplied (proof-term-at opposite 1))
         (factor (proof-term-at multiplied 1))
         (step (if (equal factor q)
                   step
                 (proof-with-checked-results
                     ((swap (library-library-axiom lib "COMMUTATIVITY-OF-*" (cdr multiplied))))
                   (proof-proof-rewrite proof step swap '(1 2 2 1)))))
         (step (proof-proof-rewrite proof step premise '(1 2 2 1 1)))
         (step (proof-proof-rewrite proof step restored '(1 2 2 1)))
         (inverse (library-library-axiom lib "INVERSE-OF-+" (list a))))
      (proof-proof-chain proof step (list inverse)))))

(defun b2-quotient-algebra-zero-remainder (lib goal known)
  (proof-with-checked-results
      ((parts (proof-list-of-length goal 3))
       (test (proof-list-of-length (cadr parts) 3))
       (operation (proof-term-at (cadr test) 0))
       (remainder (proof-list-of-length (cadr test) 3)))
    (let* ((mod-p (equal operation *b2-floor-intervals-mod*))
           (operation (if mod-p *b2-numeric-types-floor* *b2-numeric-types-truncate*))
           (exact (if mod-p *b2-quotient-algebra-exact-floor* *b2-quotient-algebra-exact-truncate*))
           (eliminate (if mod-p *b2-floor-intervals-mod-elim* *b2-floor-intervals-rem-elim*))
           (a (cadr remainder))
           (b (caddr remainder))
           (q (list operation a b))
           (reciprocal (list *b2-products-recip* b))
           (ratio (b2-products-product a reciprocal))
           (equality (proof-eq q ratio)))
      (proof-with-checked-results
          ((units (b2-quotient-algebra-inverses lib b known))
           (solver (b2-numeric-types-types-init lib))
           (typed (b2-numeric-types-types-quotient-integer solver operation a b))
           (lib (b2-numeric-types-types-lib (cdr typed))))
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results
              ((order (library-library-axiom lib "ASSOCIATIVITY-OF-*" (list a reciprocal b)))
               (swap (library-library-axiom lib "COMMUTATIVITY-OF-*" (list reciprocal b)))
               (order (proof-proof-rewrite proof order swap '(1 2 2)))
               (association (library-library-axiom lib "ASSOCIATIVITY-OF-*" (list a b reciprocal)))
               (association (proof-proof-symmetric proof association))
               (cancel (b2-quotient-algebra-cancel-to-value lib a b known))
               (restored (proof-proof-chain proof order (list association cancel)))
               (yes (proof-proof-assume proof test t))
               (no (proof-proof-assume proof test nil))
               (forward (b2-quotient-algebra-zero-remainder-divisible
                         yes lib a b q remainder eliminate (cadr units) (car typed) known))
               (positive (b2-algebra-boolean-equivalence-positive
                          lib (proof-eq test equality) yes forward))
               (premise (proof-proof-assume proof equality t))
               (backward (b2-quotient-algebra-zero-remainder-no-remainder premise lib remainder q restored a))
               (agreement (b2-algebra-boolean-equivalence-negative
                           lib test equality no positive backward))
               (exact (b2-tactics-tactics-use-fact lib exact
                                                   (proof-eq equality (list *proof-integerp* ratio))
                                                   (table-values known) (list (proof-sym "FORCE" "ACL2"))
                                                   nil 0 nil))
               (result (proof-proof-chain proof agreement (list exact))))
            (cons result lib)))))))

(defun b2-quotient-algebra-product-number (lib term)
  (if (or (proof-is-call term *proof-times*)
          (proof-is-call term *b2-products-recip*))
      (b2-products-numeric-closure lib term)
    nil))

(defun b2-quotient-algebra-completed-product-finish (lib opened evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equality (proof-step-first opened))
         (reduced (proof-term-at equality 2))
         (a (proof-term-at reduced 1))
         (known (b2-tactics-tactics-evidence lib evidence)))
      (if (proof-is-call reduced *b2-products-recip*)
          (cond ((equal a *proof-zero*)
                 (proof-with-checked-results
                     ((zero (proof-proof-compute proof reduced 0))
                      (result (proof-proof-chain proof opened (list zero))))
                   (cons result lib)))
                ((assoc-equal (proof-neg (list *library-numberp* a)) known)
                 (proof-with-checked-results
                     ((rule (library-library-axiom lib "COMPLETION-OF-UNARY-/" (list a)))
                      (rule-eq (proof-step-first rule))
                      (rhs (proof-term-at rule-eq 2))
                      (normal (b2-tactics-tactics-normalize lib rhs evidence nil nil 1500 nil))
                      (result (proof-proof-chain proof opened (list rule normal))))
                   (cons result lib)))
                (t (cons opened lib)))
        (proof-with-checked-results
            ((b (proof-term-at reduced 2)))
          (cond ((or (equal a *proof-zero*) (equal b *proof-zero*))
                 (proof-with-checked-results
                     ((zero (if (equal a *proof-zero*)
                                (b2-products-zero-left-product lib b)
                              (b2-products-zero-product lib a)))
                      (lib (cdr zero))
                      (result (proof-proof-chain (library-library-proof lib) opened (list (car zero)))))
                   (cons result lib)))
                ((or (assoc-equal (proof-neg (list *library-numberp* a)) known)
                     (assoc-equal (proof-neg (list *library-numberp* b)) known))
                 (proof-with-checked-results
                     ((number-a (b2-quotient-algebra-product-number lib a))
                      (number-b (b2-quotient-algebra-product-number lib b))
                      (rule (library-library-axiom lib "COMPLETION-OF-*" (list a b)))
                      (rule-eq (proof-step-first rule))
                      (rhs (proof-term-at rule-eq 2))
                      (normal (b2-tactics-tactics-normalize
                               lib rhs (append evidence
                                               (if number-a (list number-a) nil)
                                               (if number-b (list number-b) nil))
                               nil nil 1500 nil))
                      (result (proof-proof-chain proof opened (list rule normal))))
                   (cons result lib)))
                (t (cons opened lib))))))))

(mutual-recursion
 (defun b2-quotient-algebra-completed-product (lib term evidence)
   (declare (xargs :measure (acl2-count term)))
   (let ((proof (library-library-proof lib)))
     (if (and (consp term)
              (or (proof-is-call term *proof-times*)
                  (proof-is-call term *b2-products-recip*)))
         (proof-with-checked-results
             ((opened (proof-proof-reflexive proof term))
              (opened (b2-quotient-algebra-completed-product-children lib (cdr term) evidence opened 1)))
           (b2-quotient-algebra-completed-product-finish (cdr opened) (car opened) evidence))
       (proof-with-checked-results
           ((normal (b2-tactics-tactics-normalize lib term evidence nil nil 1500 nil))
            (result (or normal (proof-proof-reflexive proof term))))
         (cons result lib)))))

 (defun b2-quotient-algebra-completed-product-children (lib children evidence opened index)
   (declare (xargs :measure (acl2-count children)))
   (if (endp children)
       (cons opened lib)
     (proof-with-checked-results
         ((child (b2-quotient-algebra-completed-product lib (car children) evidence))
          (lib (cdr child))
          (opened (proof-proof-rewrite (library-library-proof lib) opened (car child) (list 1 2 index))))
       (b2-quotient-algebra-completed-product-children lib (cdr children) evidence opened (1+ index))))))

(defun b2-quotient-algebra-all-tests-known-p (tests known negate)
  (if (endp tests)
      t
    (and (assoc-equal (if negate (proof-neg (car tests)) (car tests)) known)
         (b2-quotient-algebra-all-tests-known-p (cdr tests) known negate))))

(defun b2-quotient-algebra-total-factor-move-completed (lib left right evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left-opened (proof-proof-unfold proof left))
         (left-eq (proof-step-first left-opened))
         (left-value (proof-term-at left-eq 2))
         (left-ratio (proof-term-at left-value 1))
         (right-opened (proof-proof-unfold proof right))
         (right-eq (proof-step-first right-opened))
         (right-value (proof-term-at right-eq 2))
         (right-ratio (proof-term-at right-value 1))
         (first (b2-quotient-algebra-completed-product lib left-ratio evidence))
         (second (b2-quotient-algebra-completed-product (cdr first) right-ratio evidence))
         (lib (cdr second)))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((second (proof-proof-symmetric proof (car second)))
             (equation (proof-proof-chain proof (car first) (list second)))
             (result (b2-quotient-algebra-ratio-congruence lib left right equation)))
          (cons result lib))))))

(defun b2-quotient-algebra-total-factor-move-prove (pending lib name goal tests evidence)
  (declare (xargs :measure (acl2-count pending)))
  (if (endp pending)
      (proof-with-checked-results
          ((known (b2-tactics-tactics-evidence lib evidence)))
        (if (and (b2-quotient-algebra-all-tests-known-p (take 3 tests) known nil)
                 (b2-quotient-algebra-all-tests-known-p (nthcdr 3 tests) known t))
            (b2-quotient-algebra-factors lib name goal known)
          (b2-quotient-algebra-total-factor-move-completed lib (cadr goal) (caddr goal) evidence)))
    (proof-with-checked-results
        ((first (b2-tactics-choose lib (car pending) evidence nil))
         (first (b2-quotient-algebra-total-factor-move-prove
                 (cdr pending) (cdr first) name goal tests (nth 4 (car first))))
         (next (b2-tactics-choose lib (car pending) evidence (list first))))
      (if (eq (caar next) :call)
          (proof-with-checked-results
              ((second (b2-quotient-algebra-total-factor-move-prove
                        (cdr pending) (cdr next) name goal tests (nth 4 (car next)))))
            (b2-tactics-choose lib (car pending) evidence (list first second)))
        next))))

(defun b2-quotient-algebra-total-factor-move (lib name goal)
  (proof-with-checked-results
      ((parts (proof-list-of-length goal 3))
       (left (proof-list-of-length (cadr parts) 3))
       (numerator (proof-list-of-length (cadr left) 3))
       (retained (proof-term-at (caddr parts) 1)))
    (let* ((a (cadr numerator))
           (b (caddr numerator))
           (z (caddr left))
           (factor (if (equal retained a) b a))
           (tests (list (list *library-numberp* a) (list *library-numberp* b)
                        (list *library-numberp* z) (proof-eq factor *proof-zero*)
                        (proof-eq z *proof-zero*))))
      (b2-quotient-algebra-total-factor-move-prove tests lib name goal tests nil))))

(defun b2-quotient-algebra-nonrational-sum (lib goal premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (proof-term-at goal 1))
         (sum (proof-term-at test 1))
         (terms (proof-list-of-length (seq-slice sum 1 :none) 2))
         (a (car terms))
         (b (cadr terms))
         (first (proof-proof-conjunct proof premise))
         (second (proof-proof-conjunct proof (cadr first)))
         (added (proof-proof-assume proof test t)))
      (let ((removed (library-minus b)))
        (proof-with-checked-results
            ((rational-opposite (b2-scaling-rational-op lib "unary--" removed (list (car second))))
             (rational (b2-scaling-rational-op lib "binary-+" (library-plus sum removed)
                                              (list added rational-opposite)))
             (identity (b2-algebra-cancel-sum lib a b))
             (normal (b2-tactics-tactics-normalize lib (list *b2-products-fix* a)
                                                   (list (car first)) (list *b2-products-fix*) nil 1500 nil))
             (identity (proof-proof-chain proof identity (list normal)))
             (result (proof-proof-rewrite proof rational identity '(1 1)))
             (result (proof-proof-tidy proof result))
             (excluded-first (proof-step-first (cadr second)))
             (result-first (proof-step-first result))
             (result (if (equal excluded-first (proof-neg result-first))
                         result
                       (b2-scaling-rational-op lib "unary--" (library-minus a) (list result))))
             (cut (proof-proof-cut proof result (cadr second)))
             (result (proof-proof-front proof cut goal)))
          (cons result lib))))))

(defun b2-quotient-algebra-identity-exact (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (equality (proof-list-of-length (cadr parts) 3)))
    (b2-quotient-algebra-exact-quotient lib (cadr equality) (caddr equality))))

(defun b2-quotient-algebra-quotient-identity-consequent (premise lib name goal)
  (cond ((member-equal name *b2-quotient-algebra-nonrational-sum*)
         (b2-quotient-algebra-nonrational-sum lib goal premise))
        ((equal name *b2-quotient-algebra-exact-truncate*)
         (b2-quotient-algebra-identity-exact lib goal))
        (t (proof-with-checked-results
               ((known (b2-quotient-algebra-with-forced lib premise)))
             (cond ((or (equal name *b2-quotient-algebra-zero-mod*)
                        (equal name *b2-quotient-algebra-zero-rem*))
                    (b2-quotient-algebra-zero-remainder lib goal known))
                   ((member-equal name *b2-quotient-algebra-cancel-unit*)
                    (proof-with-checked-results
                        ((result (b2-quotient-algebra-unit-cancellation lib goal known)))
                      (cons result lib)))
                   (t (b2-quotient-algebra-factors lib name goal known)))))))

(defun b2-quotient-algebra-quotient-identity (lib name formula)
  (cond ((member-equal name *b2-quotient-algebra-total-factors*)
         (b2-quotient-algebra-total-factor-move lib name formula))
        ((equal name *b2-quotient-algebra-exact-floor*)
         (b2-quotient-algebra-identity-exact lib formula))
        (t (proof-with-checked-results
               ((parts (proof-list-of-length formula 3)))
             (let ((condition (cadr parts))
                   (goal (caddr parts)))
               (proof-with-checked-results
                   ((request (b2-tactics-tactics-implication lib condition goal nil))
                    (reply (b2-quotient-algebra-quotient-identity-consequent
                            (nth 3 (car request)) (cdr request) name goal)))
                 (b2-tactics-tactics-implication lib condition goal reply)))))))
