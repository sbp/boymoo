(in-package "BOYMOO-PROOFS")

(include-book "arithmetic")

(logic)
(set-verify-guards-eagerness 0)
(local (in-theory (disable mod floor)))

(local
 (defthm division-distribute-left
   (equal (* (+ a b) c) (+ (* a c) (* b c)))
   :hints (("Goal" :use (:instance distributivity (x c) (y a) (z b))))))

(defun division-euclid (a b)
  (declare (xargs :measure (nfix b)
                  :hints (("Goal" :use (:instance division-mod-bounds)))))
  (if (or (not (natp a)) (zp b))
      (mv (nfix a) 1 0)
    (mv-let (g left right)
      (division-euclid b (mod a b))
      (mv g right (- left (* (floor a b) right))))))

(defun division-gcd-witness-p (a b g left right)
  (and (posp g)
       (integerp left) (integerp right)
       (integerp (/ a g)) (integerp (/ b g))
       (equal (+ (* left a) (* right b)) g)))

(local
 (defthm division-scale-affine
   (equal (* factor (+ r (* b q))) (+ (* factor r) (* q (* factor b))))
   :rule-classes nil))

(local
 (defthm division-integral-scaling
   (implies (and (integerp q) (integerp (* factor r)) (integerp (* factor b)))
            (integerp (* factor (+ r (* b q)))))
   :hints (("Goal"
            :use (:instance division-scale-affine)
            :in-theory (disable distributivity division-distribute-left
                                division-swap-multipliers associativity-of-*)))
   :rule-classes nil))

(local
 (defthm division-euclid-transfer
   (implies (and (integerp a) (posp b) (natp r) (integerp q)
                 (equal a (+ (* b q) r))
                 (division-gcd-witness-p b r g left right))
            (division-gcd-witness-p a b g right (- left (* q right))))
   :hints (("Goal"
            :use ((:instance division-scale-equality
                             (factor right) (b (+ (* b q) r)))
                  (:instance division-scale-equality
                             (factor (/ g)) (b (+ (* b q) r)))
                  (:instance division-integral-scaling (factor (/ g))))))
   :rule-classes nil))

(defthm division-euclid-witness
  (implies (and (natp a) (natp b) (or (posp a) (posp b)))
           (mv-let (g left right)
             (division-euclid a b)
             (division-gcd-witness-p a b g left right)))
  :hints (("Goal" :induct (division-euclid a b)
                  :in-theory (disable division-gcd-witness-p))
          ("Subgoal *1/2"
           :use ((:instance division-mod-bounds)
                 (:instance division-floor-mod-identity)
                 (:instance division-euclid-transfer
                            (q (floor a b)) (r (mod a b))
                            (g (mv-nth 0 (division-euclid b (mod a b))))
                            (left (mv-nth 1 (division-euclid b (mod a b))))
                            (right (mv-nth 2 (division-euclid b (mod a b))))))
           :in-theory (disable division-floor-mod-identity))
          ("Subgoal *1/1" :in-theory (enable division-gcd-witness-p)))
  :rule-classes nil)

(defthm division-euclid-remainder-decreases
  (implies (and (natp a) (posp b))
           (let ((remainder (- a (* b (floor a b)))))
             (and (natp remainder) (< remainder b)
                  (equal remainder (mod a b)))))
  :hints (("Goal" :use ((:instance division-mod-bounds))
                  :in-theory (enable mod)))
  :rule-classes nil)

(defthm division-euclid-zero-first
  (implies (posp b)
           (equal (mv-nth 0 (division-euclid 0 b)) b)))

(local
 (defthm division-scale-pair
   (equal (* scale (+ (* left a) (* right b)))
          (+ (* left (* a scale)) (* right (* b scale))))
   :rule-classes nil))

(local
 (defthm division-cross-pair-factor
   (implies (and (integerp d)
                 (equal (* a d) (* b n))
                 (equal (+ (* left a) (* right b)) 1))
            (equal (* b (+ (* left n) (* right d))) d))
   :hints (("Goal"
            :use ((:instance division-scale-pair (scale d))
                  (:instance division-scale-pair (scale b) (a n) (b d)))
            :in-theory (disable distributivity division-distribute-left
                                division-swap-multipliers associativity-of-*)))
   :rule-classes nil))

(local
 (defthm division-bezout-pair-factors
   (implies (and (integerp a) (posp b)
                 (integerp left) (integerp right)
                 (integerp n) (posp d)
                 (equal (* a d) (* b n))
                 (equal (+ (* left a) (* right b)) 1))
            (let ((factor (+ (* left n) (* right d))))
              (and (equal (* b factor) d)
                   (equal (* a factor) n)
                   (posp factor))))
   :hints (("Goal"
            :use ((:instance division-cross-pair-factor)
                  (:instance division-cross-pair-factor
                             (a b) (b a) (n d) (d n) (left right) (right left))
                  (:instance division-positive-product-order
                             (a (+ (* left n) (* right d))) (b 0) (factor b)))
            :cases ((equal (+ (* left n) (* right d)) 0))))
   :rule-classes nil))

(local
 (defthm division-coprime-denominator-from-cross
   (implies (and (rationalp x) (integerp a) (posp b)
                 (integerp left) (integerp right)
                 (equal (* a (denominator x)) (* b (numerator x)))
                 (equal (+ (* left a) (* right b)) 1))
            (equal (denominator x) b))
   :hints (("Goal"
            :use ((:instance acl2::rational-implies1 (x x))
                  (:instance division-bezout-pair-factors (n (numerator x)) (d (denominator x)))
                  (:instance acl2::lowest-terms
                             (x x) (r a) (q b)
                             (n (+ (* left (numerator x)) (* right (denominator x))))))
            :in-theory (disable distributivity division-distribute-left)))
   :rule-classes nil))

(local
 (defthm division-cross-from-two-ratios
   (implies (and (equal (* b x) a) (equal (* d x) n))
            (equal (* a d) (* b n)))
   :rule-classes nil))

(local
 (defthm division-coprime-denominator
   (implies (and (rationalp x) (integerp a) (posp b)
                 (integerp left) (integerp right)
                 (equal (* b x) a)
                 (equal (+ (* left a) (* right b)) 1))
            (equal (denominator x) b))
   :hints (("Goal"
            :use ((:instance division-numerator-product (a x))
                  (:instance division-cross-from-two-ratios (d (denominator x)) (n (numerator x)))
                  (:instance division-coprime-denominator-from-cross))))
   :rule-classes nil))

(local
 (defthm division-denominator-from-gcd-witness
   (implies (and (integerp a) (posp b)
                 (division-gcd-witness-p a b g left right))
            (equal (denominator (/ a b)) (/ b g)))
   :hints (("Goal"
            :use ((:instance division-positive-product-order (a (/ b g)) (b 0) (factor g))
                  (:instance division-cancel-reciprocal (a b) (factor g))
                  (:instance division-cancel-reciprocal (a (* a (/ g))) (factor b))
                  (:instance division-cancel-reciprocal (a 1) (factor g))
                  (:instance division-scale-equality
                             (a (+ (* left a) (* right b))) (b g) (factor (/ g)))
                  (:instance division-coprime-denominator
                             (x (/ a b)) (a (/ a g)) (b (/ b g))))))
   :rule-classes nil))

(defthm division-gcd-witness-gives-contract
  (implies (and (integerp a) (posp b)
                (division-gcd-witness-p a b g left right))
           (proof-gcd-p a b g))
  :hints (("Goal" :use ((:instance division-denominator-from-gcd-witness)
                        (:instance division-cancel-reciprocal (a b) (factor g)))
                  :in-theory (disable distributivity division-distribute-left)))
  :rule-classes nil)

(local
 (defthm division-negated-left-factor
   (equal (* (- a) b) (- (* a b)))
   :hints (("Goal"
            :use (:instance division-negated-factor (a b) (b a))
            :in-theory (disable division-negated-factor)))))

(local
 (defthm division-integer-of-negation
   (implies (rationalp x)
            (equal (integerp (- x)) (integerp x)))
   :hints (("Goal" :cases ((integerp (- x)) (integerp x))))))

(defthm division-euclid-gcd-contract
  (implies (and (integerp a) (natp b))
           (proof-gcd-p a b (mv-nth 0 (division-euclid (abs a) b))))
  :hints (("Goal"
           :use ((:instance division-euclid-witness (a (abs a)))
                 (:instance division-gcd-witness-gives-contract
                            (g (mv-nth 0 (division-euclid (abs a) b)))
                            (left (if (< a 0)
                                      (- (mv-nth 1 (division-euclid (abs a) b)))
                                    (mv-nth 1 (division-euclid (abs a) b))))
                            (right (mv-nth 2 (division-euclid (abs a) b)))))
           :in-theory (disable division-euclid))
          ("Goal'" :cases ((equal b 0) (< a 0)))
          ("Subgoal 1" :in-theory (enable division-euclid))
          ("Subgoal 2" :in-theory (enable division-euclid)))
  :rule-classes nil)

(defthm division-exact-quotient-sign
  (implies (and (integerp a) (posp b) (natp magnitude)
                (equal (* b magnitude) (abs a)))
           (proof-exact-quotient-p a b (if (< a 0) (- magnitude) magnitude)))
  :rule-classes nil)

(defthm division-exact-divisor-remainder-zero
  (implies (and (posp b) (proof-exact-quotient-p a b q))
           (and (equal (mod (abs a) b) 0)
                (equal (floor (abs a) b) (abs q))))
  :hints (("Goal"
           :use ((:instance division-quotient-unique (a (abs a)) (q (abs q)) (r 0))
                 (:instance division-remainder-unique (a (abs a)) (q (abs q)) (r 0))
                 (:instance division-positive-product (a b) (b q))
                 (:instance division-positive-product (a b) (b (- q))))
           :cases ((< q 0) (equal q 0))))
  :rule-classes nil)

(defthm division-exact-immediate-fits
  (implies (and (proof-immediate-integer-p a) (posp b)
                (proof-exact-quotient-p a b q))
           (proof-immediate-integer-p q))
  :hints (("Goal"
           :use ((:instance division-positive-product-order (a b) (b 1) (factor q))
                 (:instance division-positive-product-order (a b) (b 1) (factor (- q))))
           :cases ((< q 0) (equal q 0))))
  :rule-classes nil)

(defthm division-gcd-bound
  (implies (and (posp b) (proof-gcd-p a b g))
           (and (posp g) (<= g b)))
  :hints (("Goal"
           :use ((:instance acl2::rational-implies1 (x (/ a b)))
                 (:instance division-positive-product-order
                            (a (denominator (/ a b))) (b 1) (factor g))
                 (:instance distributivity (x (denominator (/ a b))) (y 0) (z 0)))
           :cases ((equal g 0))))
  :rule-classes nil)
