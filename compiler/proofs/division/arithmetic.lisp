(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-radix* (expt 2 32))

(local (in-theory (disable floor mod truncate)))

(defthm division-by-subtraction-bounds
  (implies (and (natp a) (posp b))
           (let ((q (nonnegative-integer-quotient a b)))
             (and (<= (* b q) a)
                  (< a (* b (+ 1 q))))))
  :hints (("Goal" :induct (nonnegative-integer-quotient a b)))
  :rule-classes nil)

(defthm division-negated-factor
  (equal (* a (- b)) (- (* a b)))
  :hints (("Goal" :use (:instance distributivity (x a) (y b) (z (- b))))))

(defthm division-positive-product
  (implies (and (rationalp a) (rationalp b) (< 0 a) (< 0 b))
           (< 0 (* a b)))
  :hints (("Goal" :use (:instance acl2::positive (x a) (y b))))
  :rule-classes nil)

(defthm division-positive-product-order
  (implies (and (rationalp a) (rationalp b) (rationalp factor)
                (< 0 factor))
           (equal (< (* a factor) (* b factor)) (< a b)))
  :hints (("Goal" :cases ((equal a b))
                  :use ((:instance division-positive-product (a factor) (b (- b a)))
                        (:instance division-positive-product (a factor) (b (- a b))))
                  :nonlinearp t))
  :rule-classes nil)

(defthm division-scale-equality
  (implies (equal a b)
           (equal (* factor a) (* factor b)))
  :rule-classes nil)

(defthm division-swap-multipliers
  (equal (* a b c) (* b a c))
  :hints (("Goal"
           :use ((:instance associativity-of-* (x a) (y b) (z c))
                 (:instance associativity-of-* (x b) (y a) (z c)))
           :in-theory (disable associativity-of-*))))

(defthm division-cancel-reciprocal
  (implies (and (rationalp a) (rationalp factor) (not (equal factor 0)))
           (equal (* factor (/ factor) a) a))
  :hints (("Goal" :use (:instance associativity-of-* (x factor) (y (/ factor)) (z a))
                  :in-theory (disable associativity-of-*))))

(defthm division-numerator-product
  (implies (rationalp a)
           (equal (* a (denominator a)) (numerator a)))
  :hints (("Goal" :use ((:instance acl2::rational-implies1 (x a))
                        (:instance acl2::rational-implies2 (x a))
                        (:instance division-scale-equality
                                   (b (* (/ (denominator a)) (numerator a)))
                                   (factor (denominator a)))
                        (:instance division-cancel-reciprocal
                                   (a (numerator a)) (factor (denominator a))))
                  :in-theory (disable acl2::rational-implies2)))
  :rule-classes nil)

(defthm division-floor-of-nonnegative-rational
  (implies (and (rationalp a) (<= 0 a))
           (and (<= (floor a 1) a)
                (< a (+ 1 (floor a 1)))))
  :hints (("Goal"
           :use ((:instance acl2::rational-implies1 (x a))
                 (:instance division-numerator-product)
                 (:instance division-by-subtraction-bounds
                            (a (numerator a)) (b (denominator a)))
                 (:instance division-positive-product-order
                            (a 0) (b a) (factor (denominator a)))
                 (:instance division-positive-product-order
                            (a (floor a 1)) (b a) (factor (denominator a)))
                 (:instance division-positive-product-order
                            (a a) (b (+ 1 (floor a 1))) (factor (denominator a))))
           :expand ((floor a 1))
           :nonlinearp t))
  :rule-classes nil)

(defthm division-floor-bounds
  (implies (and (natp a) (posp b))
           (let ((q (floor a b)))
             (and (<= (* b q) a)
                  (< a (* b (+ 1 q))))))
  :hints (("Goal"
           :use ((:instance division-floor-of-nonnegative-rational (a (/ a b)))
                 (:instance division-positive-product-order
                            (a (/ a b)) (b (floor a b)) (factor b))
                 (:instance division-positive-product-order
                            (a (/ a b)) (b (+ 1 (floor a b))) (factor b)))
           :expand ((floor a b) (floor (/ a b) 1))
           :nonlinearp t))
  :rule-classes nil)

(defthm division-floor-nat
  (implies (and (natp a) (posp b))
           (natp (floor a b)))
  :hints (("Goal" :use division-floor-bounds :nonlinearp t))
  :rule-classes :type-prescription)

(defthm division-mod-bounds
  (implies (and (natp a) (posp b))
           (and (natp (mod a b))
                (< (mod a b) b)))
  :hints (("Goal" :use division-floor-bounds :in-theory (enable mod)))
  :rule-classes nil)

(defthm division-floor-mod-identity
  (implies (and (integerp a) (posp b))
           (equal (+ (* b (floor a b)) (mod a b)) a))
  :hints (("Goal" :in-theory (enable mod))))

(defthm division-quotient-unique
  (implies (and (integerp q) (posp b) (natp r) (< r b)
                (equal a (+ (* b q) r))
                (natp a))
           (equal (floor a b) q))
  :hints (("Goal"
           :use ((:instance division-floor-bounds)
                 (:instance division-positive-product-order
                            (a (floor a b)) (b (+ q 1)) (factor b))
                 (:instance division-positive-product-order
                            (a q) (b (+ 1 (floor a b))) (factor b)))
           :cases ((< q (floor a b)))
           :nonlinearp t))
  :rule-classes nil)

(defthm division-remainder-unique
  (implies (and (integerp q) (posp b) (natp r) (< r b)
                (equal a (+ (* b q) r))
                (natp a))
           (equal (mod a b) r))
  :hints (("Goal" :use division-quotient-unique :in-theory (enable mod)))
  :rule-classes nil)

(defthm division-floor-at-least
  (implies (and (natp a) (posp b) (integerp q))
           (equal (< (floor a b) q) (< a (* b q))))
  :hints (("Goal"
           :use ((:instance division-floor-bounds)
                 (:instance division-positive-product-order
                            (a q) (b (floor a b)) (factor b))
                 (:instance division-positive-product-order
                            (a q) (b (+ 1 (floor a b))) (factor b)))
           :cases ((< (floor a b) q) (< q (floor a b)))
           :nonlinearp t))
  :rule-classes nil)

(defthm division-floor-when-small
  (implies (and (natp a) (posp b) (< a b))
           (equal (floor a b) 0))
  :hints (("Goal" :use (:instance division-quotient-unique (q 0) (r a)))))

(defthm division-mod-when-small
  (implies (and (natp a) (posp b) (< a b))
           (equal (mod a b) a))
  :hints (("Goal" :in-theory (enable mod))))
