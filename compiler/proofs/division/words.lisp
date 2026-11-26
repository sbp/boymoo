(in-package "BOYMOO-PROOFS")

(include-book "arithmetic")

(logic)
(set-verify-guards-eagerness 0)
(local (in-theory (disable floor mod truncate nonnegative-integer-quotient)))

(defthm division-denominator-of-integer
  (implies (integerp x)
           (equal (denominator x) 1))
  :hints (("Goal"
           :use ((:instance acl2::lowest-terms
                            (x x) (n (denominator x)) (r x) (q 1))
                 (:instance acl2::rational-implies1 (x x))
                 (:instance division-numerator-product (a x))))))

(defthm division-truncate-exact
  (implies (and (integerp q) (posp b) (equal a (* b q)))
           (equal (truncate a b) q))
  :hints (("Goal"
           :use ((:instance division-numerator-product (a q))
                 (:instance division-cancel-reciprocal (a q) (factor b)))
           :in-theory (enable truncate)))
  :rule-classes nil)

(local
 (defthm division-negative-numerator-bound
   (implies (and (rationalp x) (< x 0)
                 (not (equal (denominator x) 1)))
            (let* ((d (denominator x))
                   (n (numerator x))
                   (q (nonnegative-integer-quotient (- n) d)))
              (and (< (* d q) (- n))
                   (< (- n) (* d (1+ q))))))
   :hints (("Goal"
            :use ((:instance acl2::rational-implies1 (x x))
                  (:instance division-numerator-product (a x))
                  (:instance division-positive-product-order
                             (a x) (b 0) (factor (denominator x)))
                  (:instance division-by-subtraction-bounds
                             (a (- (numerator x))) (b (denominator x)))
                  (:instance acl2::lowest-terms
                             (x x) (n (denominator x)) (q 1)
                             (r (- (nonnegative-integer-quotient
                                    (- (numerator x)) (denominator x))))))))
   :rule-classes nil))

(local
 (defthm division-floor-of-negative-rational
   (implies (and (rationalp x) (< x 0))
            (and (<= (floor x 1) x)
                 (< x (+ 1 (floor x 1)))))
   :hints (("Goal"
            :use ((:instance acl2::rational-implies1 (x x))
                  (:instance division-numerator-product (a x))
                  (:instance division-negative-numerator-bound)
                  (:instance division-positive-product-order
                             (a x) (b 0) (factor (denominator x)))
                  (:instance division-positive-product-order
                             (a x) (b (floor x 1)) (factor (denominator x)))
                  (:instance division-positive-product-order
                             (a x) (b (+ 1 (floor x 1))) (factor (denominator x))))
            :expand ((floor x 1))))
   :rule-classes nil))

(defthm division-signed-floor-bounds
  (implies (and (integerp a) (posp b))
           (let ((q (floor a b)))
             (and (<= (* b q) a)
                  (< a (* b (+ 1 q))))))
  :hints (("Goal"
           :use ((:instance division-floor-of-nonnegative-rational (a (/ a b)))
                 (:instance division-floor-of-negative-rational (x (/ a b)))
                 (:instance division-positive-product-order
                            (a (/ a b)) (b (floor a b)) (factor b))
                 (:instance division-positive-product-order
                            (a (/ a b)) (b (+ 1 (floor a b))) (factor b)))
           :expand ((floor a b) (floor (/ a b) 1))))
  :rule-classes nil)

(defthm division-signed-floor-integer
  (implies (and (integerp a) (posp b))
           (integerp (floor a b)))
  :hints (("Goal"
           :use (:instance acl2::rational-implies1 (x (/ a b)))
           :expand ((floor a b))))
  :rule-classes :type-prescription)

(defthm division-signed-mod-bounds
  (implies (and (integerp a) (posp b))
           (and (natp (mod a b)) (< (mod a b) b)))
  :hints (("Goal" :use division-signed-floor-bounds :in-theory (enable mod)))
  :rule-classes nil)

(defthm division-signed-quotient-unique
  (implies (and (integerp q) (posp b) (natp r) (< r b)
                (equal a (+ (* b q) r)))
           (equal (floor a b) q))
  :hints (("Goal"
           :use ((:instance division-signed-floor-bounds)
                 (:instance division-positive-product-order
                            (a (floor a b)) (b (+ q 1)) (factor b))
                 (:instance division-positive-product-order
                            (a q) (b (+ 1 (floor a b))) (factor b)))
           :cases ((< q (floor a b)))))
  :rule-classes nil)

(defthm division-signed-remainder-unique
  (implies (and (integerp q) (posp b) (natp r) (< r b)
                (equal a (+ (* b q) r)))
           (equal (mod a b) r))
  :hints (("Goal" :use division-signed-quotient-unique :in-theory (enable mod)))
  :rule-classes nil)

(defthm division-power-of-two-positive
  (implies (natp width)
           (posp (expt 2 width)))
  :rule-classes :type-prescription)

(defthm division-power-of-two-step
  (implies (posp width)
           (equal (expt 2 width) (* 2 (expt 2 (1- width)))))
  :hints (("Goal" :expand ((expt 2 width))))
  :rule-classes nil)

(defthm division-ash-left
  (implies (and (integerp x) (natp width))
           (equal (ash x width) (* x (expt 2 width))))
  :hints (("Goal"
           :use (:instance division-signed-quotient-unique
                           (a (* x (expt 2 width))) (b 1)
                           (q (* x (expt 2 width))) (r 0))
           :expand ((ash x width)))))

(defthm division-evenp-remainder
  (implies (integerp x)
           (equal (evenp x) (equal (mod x 2) 0)))
  :hints (("Goal"
           :use ((:instance division-signed-remainder-unique
                            (a x) (b 2) (q (* 1/2 x)) (r 0))
                 (:instance division-signed-floor-integer (a x) (b 2))
                 (:instance division-floor-mod-identity (a x) (b 2)))
           :in-theory (disable division-floor-mod-identity)))
  :rule-classes nil)

(local
 (defthm division-mod-double
   (implies (and (integerp x) (posp divisor))
            (equal (mod x (* 2 divisor))
                   (+ (* 2 (mod (floor x 2) divisor)) (mod x 2))))
   :hints (("Goal"
            :use ((:instance division-signed-mod-bounds (a x) (b 2))
                  (:instance division-signed-mod-bounds (a (floor x 2)) (b divisor))
                  (:instance division-floor-mod-identity (a x) (b 2))
                  (:instance division-scale-equality
                             (factor 2)
                             (a (+ (mod (floor x 2) divisor)
                                   (* divisor (floor (floor x 2) divisor))))
                             (b (floor x 2)))
                  (:instance division-floor-mod-identity (a (floor x 2)) (b divisor))
                  (:instance division-signed-remainder-unique
                             (a x) (b (* 2 divisor))
                             (q (floor (floor x 2) divisor))
                             (r (+ (* 2 (mod (floor x 2) divisor)) (mod x 2)))))
            :in-theory (disable division-floor-mod-identity)))
   :rule-classes nil))

(local
 (defthm division-low-mask-halving
   (implies (posp width)
            (let ((mask (1- (expt 2 width)))
                  (half (1- (expt 2 (1- width)))))
              (and (equal (floor mask 2) half)
                   (not (evenp mask)))))
   :hints (("Goal"
            :use ((:instance division-power-of-two-step)
                  (:instance division-signed-quotient-unique
                             (a (1- (expt 2 width))) (b 2)
                             (q (1- (expt 2 (1- width)))) (r 1))
                  (:instance division-signed-remainder-unique
                             (a (1- (expt 2 width))) (b 2)
                             (q (1- (expt 2 (1- width)))) (r 1))
                  (:instance division-evenp-remainder (x (1- (expt 2 width)))))
            :in-theory (disable evenp expt)))
   :rule-classes nil))

(local
 (defthm division-mod-minus-one
   (implies (posp divisor)
            (equal (mod -1 divisor) (1- divisor)))
   :hints (("Goal" :use (:instance division-signed-remainder-unique
                                   (a -1) (b divisor) (q -1) (r (1- divisor)))))))

(local
 (defun division-bits-induct (x width)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       x
     (division-bits-induct (floor x 2) (1- width)))))

(defthm division-mask-is-remainder
  (implies (and (integerp x) (natp width))
           (equal (logand x (1- (expt 2 width))) (mod x (expt 2 width))))
  :hints (("Goal" :induct (division-bits-induct x width)
                  :in-theory (disable evenp expt acl2::binary-logand))
          ("Subgoal *1/2"
           :expand ((logand x (1- (expt 2 width)))
                    (logand 0 (1- (expt 2 width)))
                    (logand -1 (1- (expt 2 width))))
           :use ((:instance division-low-mask-halving)
                 (:instance division-power-of-two-step)
                 (:instance division-mod-double (divisor (expt 2 (1- width))))
                 (:instance division-signed-mod-bounds (a x) (b 2))
                 (:instance division-evenp-remainder))
           :cases ((equal x 0) (equal x -1)))
          ("Subgoal *1/1"
           :use (:instance division-signed-remainder-unique (a x) (b 1) (q x) (r 0))
           :in-theory (enable expt acl2::binary-logand))))

(local (in-theory (disable ash acl2::binary-logand)))

(defthm division-a64-unsigned-is-remainder
  (implies (and (integerp x) (natp width))
           (equal (boymoo-model::a64-unsigned width x) (mod x (expt 2 width))))
  :hints (("Goal"
           :use ((:instance division-mask-is-remainder)
                 (:instance division-ash-left (x 1)))
           :in-theory (disable division-mask-is-remainder))))

(defthm division-a64-unsigned-bounded
  (implies (natp width)
           (unsigned-byte-p width (boymoo-model::a64-unsigned width x)))
  :hints (("Goal"
           :use ((:instance division-signed-mod-bounds (a (ifix x)) (b (expt 2 width)))
                 (:instance division-a64-unsigned-is-remainder (x (ifix x))))
           :in-theory (disable division-a64-unsigned-is-remainder)))
  :rule-classes (:rewrite :type-prescription))

(defthm division-a64-unsigned-of-bounded
  (implies (unsigned-byte-p width x)
           (equal (boymoo-model::a64-unsigned width x) x)))

(defthm division-a64-unsigned-idempotent
  (implies (natp width)
           (equal (boymoo-model::a64-unsigned width (boymoo-model::a64-unsigned width value))
                  (boymoo-model::a64-unsigned width value)))
  :hints (("Goal" :use (:instance division-a64-unsigned-bounded (x value))
                  :in-theory (disable division-a64-unsigned-bounded boymoo-model::a64-unsigned
                                      division-a64-unsigned-is-remainder))))

(local
 (defthm division-power-of-two-inverse-product
   (implies (natp width)
            (equal (* (expt 2 (- width)) (expt 2 width)) 1))
   :hints (("Goal" :induct (division-bits-induct 0 width) :in-theory (disable expt))
           ("Subgoal *1/2"
            :expand ((expt 2 width) (expt 2 (- width))))
           ("Subgoal *1/1" :in-theory (enable expt)))
   :rule-classes nil))

(local
 (defthm division-power-of-two-reciprocal
   (implies (natp width)
            (equal (expt 2 (- width)) (/ (expt 2 width))))
   :hints (("Goal"
            :use ((:instance division-power-of-two-inverse-product)
                  (:instance division-positive-product-order
                             (a (expt 2 (- width))) (b (/ (expt 2 width)))
                             (factor (expt 2 width)))
                  (:instance division-positive-product-order
                             (a (/ (expt 2 width))) (b (expt 2 (- width)))
                             (factor (expt 2 width))))
            :in-theory (disable expt)))
   :rule-classes nil))

(defthm division-ash-right
  (implies (and (integerp x) (natp width))
           (equal (ash x (- width)) (floor x (expt 2 width))))
  :hints (("Goal"
           :use (:instance division-power-of-two-reciprocal)
           :expand ((ash x (- width)))
           :in-theory (enable floor))))
