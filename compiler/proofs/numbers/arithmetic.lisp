(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(defund proof-number-reduced-p (a b)
  (and (integerp a)
       (posp b)
       (equal (numerator (/ a b)) a)
       (equal (denominator (/ a b)) b)))

(defthm proof-number-rational-parts
  (implies (rationalp x)
           (and (integerp (numerator x))
                (integerp (denominator x))
                (< 0 (denominator x))))
  :hints (("Goal" :use ((:instance acl2::rational-implies1 (acl2::x x)))))
  :rule-classes ((:type-prescription :corollary
                  (implies (rationalp x) (integerp (numerator x))))
                 (:type-prescription :corollary
                  (implies (rationalp x) (posp (denominator x))))))

(defthm proof-number-quotient-of-parts
  (implies (rationalp x)
           (equal (/ (numerator x) (denominator x)) x))
  :hints (("Goal" :use ((:instance acl2::rational-implies2 (acl2::x x)))
                  :in-theory (disable acl2::rational-implies2))))

(defthm proof-number-reduced-p-of-parts
  (implies (rationalp x)
           (proof-number-reduced-p (numerator x) (denominator x)))
  :hints (("Goal" :in-theory (enable proof-number-reduced-p))))

(local
 (defthm commute-two-factors
   (equal (* x y z) (* y x z))
   :hints (("Goal" :use ((:instance acl2::associativity-of-*
                                    (acl2::x x) (acl2::y y) (acl2::z z))
                         (:instance acl2::associativity-of-*
                                    (acl2::x y) (acl2::y x) (acl2::z z)))
                   :in-theory (disable acl2::associativity-of-*)))))

(local
 (defthm divide-product
   (implies (and (acl2-numberp a) (acl2-numberp b) (not (equal b 0)))
            (equal (/ (* a b) b) a))
   :hints (("Goal" :use ((:instance acl2::associativity-of-*
                                    (acl2::x (/ b)) (acl2::y b) (acl2::z a)))
                   :in-theory (disable acl2::associativity-of-*
                                       commute-two-factors)))))

(defthm proof-number-exact-quotient-value
  (implies (proof-exact-quotient-p a b q)
           (equal (/ a b) q))
  :hints (("Goal" :use ((:instance divide-product (a q)))
                  :in-theory (disable divide-product acl2::associativity-of-*
                                      commute-two-factors)))
  :rule-classes nil)

(defthm proof-number-gcd-of-positive-denominator
  (implies (and (posp b) (proof-gcd-p a b g))
           (and (posp g)
                (proof-exact-quotient-p b g (denominator (/ a b)))))
  :rule-classes nil)

(local
 (defthm multiply-quotient
   (implies (and (acl2-numberp a) (acl2-numberp b) (not (equal b 0)))
            (equal (* b (/ a b)) a))
   :hints (("Goal" :in-theory (enable commute-two-factors)))))

(local
 (defthm rescale-product
   (implies (and (equal (* b p) a) (equal (* d p) n) (equal (* g d) b))
            (equal (* g n) a))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x g) (acl2::y d) (acl2::z p)))
            :in-theory (disable acl2::associativity-of-*
                                acl2::commutativity-of-* commute-two-factors)))
   :rule-classes nil))

(local
 (defthm multiply-equal-quotients
   (implies (and (acl2-numberp a) (acl2-numberp b)
                 (acl2-numberp n) (acl2-numberp d)
                 (not (equal b 0)) (not (equal d 0))
                 (equal b (* g d))
                 (equal (/ a b) (/ n d)))
            (equal (* g n) a))
   :hints (("Goal"
            :use ((:instance multiply-quotient)
                  (:instance multiply-quotient (a n) (b d))
                  (:instance rescale-product (p (/ n d))))
            :in-theory (disable multiply-quotient acl2::associativity-of-*
                                acl2::commutativity-of-* commute-two-factors)))
   :rule-classes nil))

(defthm proof-number-gcd-numerator
  (implies (and (posp b) (proof-gcd-p a b g))
           (proof-exact-quotient-p a g (numerator (/ a b))))
  :hints (("Goal"
           :use ((:instance proof-number-gcd-of-positive-denominator)
                 (:instance multiply-equal-quotients
                            (n (numerator (/ a b))) (d (denominator (/ a b)))))
           :in-theory (disable acl2::rational-implies2
                               acl2::commutativity-of-* acl2::associativity-of-*
                               commute-two-factors)))
  :rule-classes nil)

(defthm proof-number-reduction
  (implies (and (posp b)
                (proof-gcd-p a b g)
                (proof-exact-quotient-p a g n)
                (proof-exact-quotient-p b g d))
           (and (equal n (numerator (/ a b)))
                (equal d (denominator (/ a b)))
                (proof-number-reduced-p n d)
                (equal (/ n d) (/ a b))))
  :hints (("Goal"
           :use (proof-number-gcd-numerator
                 proof-number-gcd-of-positive-denominator
                 (:instance proof-number-exact-quotient-value (b g) (q n))
                 (:instance proof-number-exact-quotient-value (a b) (b g) (q d))
                 (:instance proof-number-exact-quotient-value
                            (b g) (q (numerator (/ a b))))
                 (:instance proof-number-exact-quotient-value
                            (a b) (b g) (q (denominator (/ a b))))
                 (:instance proof-number-reduced-p-of-parts (x (/ a b)))
                 (:instance proof-number-quotient-of-parts (x (/ a b))))
           :in-theory (disable proof-number-reduced-p-of-parts
                               proof-number-quotient-of-parts
                               proof-exact-quotient-p)))
  :rule-classes nil)

(defthm proof-number-integer-parts
  (implies (integerp x)
           (and (equal (numerator x) x)
                (equal (denominator x) 1)))
  :hints (("Goal" :use proof-number-quotient-of-parts
                  :cases ((equal (denominator x) 1))
                  :in-theory (disable proof-number-quotient-of-parts
                                      acl2::rational-implies2))))

(defthm proof-number-rational-components
  (implies (rationalp x)
           (and (equal (realpart x) x)
                (equal (imagpart x) 0))))

(defthm proof-number-components-are-rational
  (and (rationalp (realpart x))
       (rationalp (imagpart x)))
  :hints (("Goal" :use ((:instance acl2::complex-implies1 (acl2::x x)))))
  :rule-classes ((:type-prescription :corollary (rationalp (realpart x)))
                 (:type-prescription :corollary (rationalp (imagpart x)))))

(defthm proof-number-complex-completion
  (equal (complex (rfix x) (rfix y)) (complex x y))
  :hints (("Goal"
           :use ((:instance acl2::completion-of-complex
                            (acl2::x x) (acl2::y y))))))

(defthm proof-number-complex-zero-imaginary-part
  (implies (and (rationalp x) (rationalp y))
           (equal (complex-rationalp (complex x y))
                  (not (equal y 0))))
  :hints (("Goal"
           :use ((:instance acl2::nonzero-imagpart (acl2::x (complex x y))))
           :cases ((equal y 0)))))

(defund proof-number-order (x y)
  (cond ((< x y) -1)
        ((< y x) 1)
        (t 0)))

(defund proof-number-first-order (first second)
  (if (equal first 0) second first))

(defthm proof-number-order-lexicographic
  (equal (proof-number-first-order
          (proof-number-order (realpart x) (realpart y))
          (proof-number-order (imagpart x) (imagpart y)))
         (proof-number-order x y))
  :hints (("Goal"
           :use ((:instance acl2::completion-of-< (acl2::x x) (acl2::y y))
                 (:instance acl2::completion-of-< (acl2::x y) (acl2::y x)))
           :in-theory (enable proof-number-first-order proof-number-order)))
  :rule-classes nil)

(local
 (defthm minus-as-product
   (equal (- a) (* -1 a))))

(local
 (defthm negate-product
   (equal (* (- a) b) (- (* a b)))
   :hints (("Goal" :in-theory (enable minus-as-product)))))

(local
 (defthm negate-right-factor
   (equal (* a (- b)) (- (* a b)))
   :hints (("Goal" :use ((:instance negate-product (a b) (b a)))
                   :in-theory (disable negate-product minus-as-product)))))

(local (in-theory (disable minus-as-product)))

(local
 (defthm double-negation
   (equal (- (- a)) (fix a))
   :hints (("Goal"
            :use (minus-as-product
                  (:instance minus-as-product (a (- a)))
                  (:instance acl2::associativity-of-*
                             (acl2::x -1) (acl2::y -1) (acl2::z a)))
            :in-theory (disable acl2::associativity-of-* commute-two-factors
                                negate-product negate-right-factor)))))

(local
 (defthm multiply-positive-is-increasing
   (implies (and (rationalp a) (rationalp b) (rationalp c) (< 0 c) (< a b))
            (< (* a c) (* b c)))
   :hints (("Goal"
            :use ((:instance acl2::positive (acl2::x (- b a)) (acl2::y c))
                  (:instance acl2::<-on-others
                             (acl2::x (* a c)) (acl2::y (* b c))))
            :nonlinearp t))
   :rule-classes nil))

(defthm proof-number-scale-less
  (implies (and (rationalp a) (rationalp b) (rationalp c) (< 0 c))
           (equal (< (* a c) (* b c)) (< a b)))
  :hints (("Goal"
           :use (multiply-positive-is-increasing
                 (:instance multiply-positive-is-increasing (a b) (b a)))
           :cases ((equal a b))))
  :rule-classes nil)

(local
 (defthm multiply-positive-preserves-order
   (implies (and (rationalp a) (rationalp b) (rationalp c) (< 0 c))
            (equal (proof-number-order (* a c) (* b c))
                   (proof-number-order a b)))
   :hints (("Goal"
            :use (multiply-positive-is-increasing
                  (:instance multiply-positive-is-increasing (a b) (b a)))
            :in-theory (enable proof-number-order)
            :cases ((equal a b))))
   :rule-classes nil))

(local
 (defthm rational-numerator-as-product
   (implies (rationalp x)
            (equal (* x (denominator x)) (numerator x)))
   :hints (("Goal"
            :use ((:instance proof-number-quotient-of-parts)
                  (:instance multiply-quotient
                             (a (numerator x)) (b (denominator x))))
            :in-theory (disable proof-number-quotient-of-parts
                                multiply-quotient)))
   :rule-classes nil))

(defthm proof-number-rational-cross-order
  (implies (and (rationalp x) (rationalp y))
           (equal (proof-number-order (* (numerator x) (denominator y))
                                      (* (numerator y) (denominator x)))
                  (proof-number-order x y)))
  :hints (("Goal"
           :use (rational-numerator-as-product
                 (:instance rational-numerator-as-product (x y))
                 (:instance multiply-positive-preserves-order
                            (a x) (b y) (c (* (denominator x) (denominator y))))
                 (:instance acl2::positive
                            (acl2::x (denominator x)) (acl2::y (denominator y))))))
  :rule-classes nil)

(local
 (defthm reciprocal-is-unique
   (implies (and (acl2-numberp x) (not (equal x 0))
                 (acl2-numberp y) (equal (* x y) 1))
            (equal y (/ x)))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x (/ x)) (acl2::y x) (acl2::z y)))
            :in-theory (disable acl2::associativity-of-*)))
   :rule-classes nil))

(local
 (defthm rearrange-products
   (equal (* (* a b) (* c d))
          (* (* a c) (* b d)))
   :rule-classes nil))

(local
 (defthm reciprocal-of-product
   (implies (and (rationalp b) (rationalp d) (not (equal b 0)) (not (equal d 0)))
            (equal (/ (* b d)) (* (/ b) (/ d))))
   :hints (("Goal"
            :use ((:instance divide-product (a b) (b d))
                  (:instance reciprocal-is-unique (x (* b d)) (y (* (/ b) (/ d))))
                  (:instance rearrange-products (a b) (b d) (c (/ b)) (d (/ d))))
            :in-theory (disable divide-product
                                acl2::associativity-of-*
                                acl2::commutativity-of-* commute-two-factors)))))

(local
 (defthm cancel-reciprocal-factor
   (implies (and (acl2-numberp x) (not (equal x 0)))
            (equal (* x (/ x) y) (fix y)))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x x) (acl2::y (/ x)) (acl2::z y)))
            :in-theory (disable acl2::associativity-of-*
                                acl2::commutativity-of-* commute-two-factors)))))

(defthm proof-number-rational-sum
  (implies (and (rationalp a) (rationalp b) (rationalp c) (rationalp d)
                (not (equal b 0)) (not (equal d 0)))
           (equal (/ (+ (* a d) (* c b)) (* b d))
                  (+ (/ a b) (/ c d))))
  :rule-classes nil)

(defthm proof-number-rational-product
  (implies (and (rationalp a) (rationalp b) (rationalp c) (rationalp d)
                (not (equal b 0)) (not (equal d 0)))
           (equal (/ (* a c) (* b d))
                  (* (/ a b) (/ c d))))
  :rule-classes nil)

(local
 (defthm square-of-i-times
   (implies (acl2-numberp x)
            (equal (* #c(0 1) #c(0 1) x) (- x)))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x #c(0 1)) (acl2::y #c(0 1)) (acl2::z x))
                  (:instance minus-as-product (a x)))
            :in-theory (disable acl2::associativity-of-* commute-two-factors)))))

(defthm proof-number-complex-product-parts
  (implies (and (rationalp a) (rationalp b) (rationalp c) (rationalp d))
           (equal (* (complex a b) (complex c d))
                  (complex (- (* a c) (* b d)) (+ (* a d) (* b c)))))
  :hints (("Goal" :in-theory (enable acl2::complex-definition)))
  :rule-classes nil)

(defthm proof-number-complex-product
  (implies (and (acl2-numberp x) (acl2-numberp y))
           (equal (complex (- (* (realpart x) (realpart y))
                              (* (imagpart x) (imagpart y)))
                           (+ (* (realpart x) (imagpart y))
                              (* (imagpart x) (realpart y))))
                  (* x y)))
  :hints (("Goal"
           :use ((:instance proof-number-complex-product-parts
                            (a (realpart x)) (b (imagpart x))
                            (c (realpart y)) (d (imagpart y))))
           :in-theory (disable (:elim acl2::realpart-imagpart-elim))))
  :rule-classes nil)

(defthm proof-number-complex-negation
  (implies (acl2-numberp x)
           (equal (complex (- (realpart x)) (- (imagpart x))) (- x)))
  :hints (("Goal"
           :use ((:instance proof-number-complex-product (y -1))
                 (:instance minus-as-product (a (realpart x)))
                 (:instance minus-as-product (a (imagpart x)))
                 (:instance minus-as-product (a x)))))
  :rule-classes nil)

(local
 (defthm norm-is-nonzero
   (implies (and (rationalp a) (rationalp b)
                 (or (not (equal a 0)) (not (equal b 0))))
            (not (equal (+ (* a a) (* b b)) 0)))
   :hints (("Goal"
            :use ((:instance divide-product (b a))
                  (:instance divide-product (a b)))
            :nonlinearp t))))

(defthm proof-number-complex-reciprocal-parts
  (implies (and (rationalp a) (rationalp b))
           (let ((inverse (/ (+ (* a a) (* b b)))))
             (equal (complex (* a inverse) (- (* b inverse)))
                    (/ (complex a b)))))
  :hints (("Goal"
           :use ((:instance reciprocal-is-unique
                            (x (complex a b))
                            (y (complex (/ a (+ (* a a) (* b b)))
                                        (- (/ b (+ (* a a) (* b b)))))))
                 (:instance proof-number-complex-product-parts
                            (c (/ a (+ (* a a) (* b b))))
                            (d (- (/ b (+ (* a a) (* b b))))))
                 (:instance acl2::distributivity
                            (acl2::x (/ (+ (* a a) (* b b))))
                            (acl2::y (* a a)) (acl2::z (* b b)))
                 (:instance acl2::complex-equal
                            (acl2::x1 a) (acl2::y1 b) (acl2::x2 0) (acl2::y2 0)))
           :in-theory (disable acl2::distributivity)
           :cases ((and (equal a 0) (equal b 0)))))
  :rule-classes nil)

(defthm proof-number-complex-reciprocal
  (implies (acl2-numberp x)
           (let* ((a (realpart x))
                  (b (imagpart x))
                  (inverse (/ (+ (* a a) (* b b)))))
             (equal (complex (* a inverse) (- (* b inverse))) (/ x))))
  :hints (("Goal"
           :use ((:instance proof-number-complex-reciprocal-parts
                            (a (realpart x)) (b (imagpart x))))
           :in-theory (disable (:elim acl2::realpart-imagpart-elim))))
  :rule-classes nil)

; The first three results are a common divisor and two integer quotients.
; The last two results express that divisor as a linear combination.
(local
 (defun bezout-data (a b)
   (declare (xargs :measure (+ (nfix a) (nfix b))))
   (cond ((zp a) (mv (nfix b) 0 1 0 1))
         ((zp b) (mv a 1 0 1 0))
         ((< a b)
          (mv-let (g m n u v)
            (bezout-data a (- b a))
            (mv g m (+ m n) (- u v) v)))
         (t
          (mv-let (g m n u v)
            (bezout-data (- a b) b)
            (mv g (+ m n) n u (- v u)))))))

(local
 (defthm bezout-data-correct
   (implies (and (natp a) (natp b) (or (posp a) (posp b)))
            (mv-let (g m n u v)
              (bezout-data a b)
              (and (posp g) (integerp m) (integerp n)
                   (integerp u) (integerp v)
                   (equal (* g m) a)
                   (equal (* g n) b)
                   (equal (+ (* u a) (* v b)) g))))
   :hints (("Goal" :induct (bezout-data a b)))
   :rule-classes nil))

(local
 (defun unit-coefficients (a b)
   (mv-let (g m n u v)
     (bezout-data (abs a) b)
     (declare (ignore g m n))
     (mv (if (< a 0) (- u) u) v))))

(local
 (defthm canonical-pair-has-unit-coefficients
   (implies (proof-number-reduced-p a b)
            (mv-let (u v)
              (unit-coefficients a b)
              (and (integerp u) (integerp v)
                   (equal (+ (* u a) (* v b)) 1))))
   :hints (("Goal"
            :use ((:instance bezout-data-correct (a (abs a)))
                  (:instance acl2::lowest-terms
                             (acl2::x (/ a b))
                             (acl2::n (mv-nth 0 (bezout-data (abs a) b)))
                             (acl2::r (if (< a 0)
                                          (- (mv-nth 1 (bezout-data (abs a) b)))
                                        (mv-nth 1 (bezout-data (abs a) b))))
                             (acl2::q (mv-nth 2 (bezout-data (abs a) b)))))
            :in-theory (e/d (proof-number-reduced-p) (bezout-data))))
   :rule-classes nil))

(local
 (defthm cross-products-for-quotient
   (implies (and (rationalp a) (rationalp b) (not (equal b 0)))
            (equal (* a (denominator (/ a b))) (* b (numerator (/ a b)))))
   :hints (("Goal"
            :use ((:instance rational-numerator-as-product (x (/ a b)))
                  (:instance multiply-quotient)
                  (:instance acl2::associativity-of-*
                             (acl2::x b) (acl2::y (/ a b))
                             (acl2::z (denominator (/ a b)))))
            :in-theory (disable acl2::associativity-of-*
                                acl2::commutativity-of-* commute-two-factors
                                multiply-quotient)))
   :rule-classes nil))

(local
 (defthm rotate-three-factors
   (equal (* d u a) (* u a d))
   :rule-classes nil))

(local
 (defthm scale-a-cross-product
   (implies (equal (* a d) (* b n))
            (equal (* d u a) (* b u n)))
   :hints (("Goal"
            :use (rotate-three-factors
                  (:instance rotate-three-factors (d b) (a n)))
            :in-theory (disable acl2::associativity-of-* commute-two-factors)))
   :rule-classes nil))

(local
 (defthm scale-from-unit-combination
   (implies (and (equal (+ (* u a) (* v b)) 1)
                 (equal (* a d) (* b n))
                 (rationalp d))
            (equal (* b (+ (* u n) (* v d))) d))
   :hints (("Goal"
            :use ((:instance acl2::distributivity
                             (acl2::x d) (acl2::y (* u a)) (acl2::z (* v b)))
                  (:instance acl2::commutativity-of-* (acl2::x d) (acl2::y 1))
                  (:instance acl2::distributivity
                             (acl2::x b) (acl2::y (* u n)) (acl2::z (* v d)))
                  scale-a-cross-product
                  (:instance scale-a-cross-product (a b) (n d) (u v)))
            :in-theory (disable acl2::distributivity acl2::associativity-of-*
                                acl2::commutativity-of-* commute-two-factors)))
   :rule-classes nil))

(local
 (defthm numerator-scale-from-cross-products
   (implies (and (rationalp a) (rationalp b) (rationalp k) (rationalp n)
                 (< 0 b) (equal d (* b k))
                 (equal (* a d) (* b n)))
            (equal n (* a k)))
   :hints (("Goal"
            :use ((:instance multiply-positive-is-increasing
                             (a n) (b (* a k)) (c b))
                  (:instance multiply-positive-is-increasing
                             (a (* a k)) (b n) (c b)))))
   :rule-classes nil))

(local
 (defthm positive-scale-from-positive-product
   (implies (and (rationalp b) (rationalp k) (< 0 b) (< 0 (* b k)))
            (< 0 k))
   :hints (("Goal"
            :use ((:instance multiply-positive-is-increasing (a k) (b 0) (c b)))
            :cases ((equal k 0) (< k 0))))
   :rule-classes nil))

(local
 (defthm reduced-p-from-unit-combination
   (implies (and (integerp a) (posp b) (integerp u) (integerp v)
                 (equal (+ (* u a) (* v b)) 1))
            (proof-number-reduced-p a b))
   :hints (("Goal"
            :use (cross-products-for-quotient
                  (:instance scale-from-unit-combination
                             (n (numerator (/ a b))) (d (denominator (/ a b))))
                  (:instance numerator-scale-from-cross-products
                             (n (numerator (/ a b))) (d (denominator (/ a b)))
                             (k (+ (* u (numerator (/ a b)))
                                   (* v (denominator (/ a b))))))
                  (:instance positive-scale-from-positive-product
                             (k (+ (* u (numerator (/ a b)))
                                   (* v (denominator (/ a b))))))
                  (:instance acl2::lowest-terms
                             (acl2::x (/ a b))
                             (acl2::n (+ (* u (numerator (/ a b)))
                                         (* v (denominator (/ a b)))))
                             (acl2::r a) (acl2::q b)))
            :in-theory (e/d (proof-number-reduced-p) (acl2::distributivity))))
   :rule-classes nil))

(defthm proof-number-negated-parts-are-reduced
  (implies (proof-number-reduced-p a b)
           (proof-number-reduced-p (- a) b))
  :hints (("Goal"
           :use (canonical-pair-has-unit-coefficients
                 (:instance reduced-p-from-unit-combination (a (- a))
                            (u (- (mv-nth 0 (unit-coefficients a b))))
                            (v (mv-nth 1 (unit-coefficients a b)))))
           :in-theory (e/d (proof-number-reduced-p) (unit-coefficients))))
  :rule-classes nil)

(defthm proof-number-inverted-parts-are-reduced
  (implies (and (proof-number-reduced-p a b) (not (equal a 0)))
           (if (< a 0)
               (proof-number-reduced-p (- b) (- a))
             (proof-number-reduced-p b a)))
  :hints (("Goal"
           :use (canonical-pair-has-unit-coefficients
                 (:instance reduced-p-from-unit-combination (a b) (b a)
                            (u (mv-nth 1 (unit-coefficients a b)))
                            (v (mv-nth 0 (unit-coefficients a b))))
                 (:instance reduced-p-from-unit-combination
                            (a (- b)) (b (- a))
                            (u (- (mv-nth 1 (unit-coefficients a b))))
                            (v (- (mv-nth 0 (unit-coefficients a b))))))
           :in-theory (e/d (proof-number-reduced-p) (unit-coefficients))))
  :rule-classes nil)

(defthm proof-number-quotient-of-negated-numerator
  (equal (/ (- a) b) (- (/ a b)))
  :rule-classes nil)

(local
 (defthm reciprocal-of-reciprocal
   (implies (and (acl2-numberp a) (not (equal a 0)))
            (equal (/ (/ a)) a))
   :hints (("Goal" :use ((:instance reciprocal-is-unique (x (/ a)) (y a))
                         (:instance acl2::inverse-of-* (acl2::x a)))
                   :in-theory (disable acl2::inverse-of-*)))))

(defthm proof-number-reciprocal-from-parts
  (implies (and (rationalp a) (rationalp b) (not (equal b 0)))
           (equal (/ (/ a b)) (/ b a)))
  :hints (("Goal" :cases ((equal a 0))))
  :rule-classes nil)

(local
 (defthm reciprocal-of-negative
   (implies (and (rationalp a) (not (equal a 0)))
            (equal (/ (- a)) (- (/ a))))
   :hints (("Goal" :use ((:instance reciprocal-of-product (b -1) (d a))
                         minus-as-product
                         (:instance minus-as-product (a (/ a))))
                   :in-theory (disable reciprocal-of-product)))))

(defthm proof-number-reciprocal-from-negative-parts
  (implies (and (rationalp a) (rationalp b) (not (equal b 0)) (< a 0))
           (equal (/ (- b) (- a)) (/ (/ a b))))
  :hints (("Goal" :use proof-number-reciprocal-from-parts))
  :rule-classes nil)

(defthm proof-number-rational-view-of-reduced-parts
  (implies (and (proof-number-reduced-p a b) (< 1 b))
           (equal (proof-rational-value (proof-value-view a) (proof-value-view b))
                  (proof-value-view (/ a b))))
  :hints (("Goal" :in-theory (enable proof-number-reduced-p))))

(defthm proof-number-view-of-complex-parts
  (implies (and (rationalp a) (rationalp b) (not (equal b 0)))
           (equal (proof-complex-value (proof-value-view a) (proof-value-view b))
                  (proof-value-view (complex a b)))))
