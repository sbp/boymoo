(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable floor mod ash evenp oddp acl2::binary-logand acl2::binary-logior
                    acl2::binary-logxor lognot logbitp expt
                    boymoo-model::a64-unsigned boymoo-model::a64-ones
                    boymoo-model::a64-signed))

(local
 (defthm generated-quotient-bounds
   (implies (and (natp x) (posp y))
            (let ((q (nonnegative-integer-quotient x y)))
              (and (<= (* y q) x)
                   (< x (+ y (* y q))))))
   :hints (("Goal" :induct (nonnegative-integer-quotient x y)
                   :nonlinearp t))
   :rule-classes :linear))

(local
 (defthm generated-multiply-reciprocal
   (implies (and (acl2-numberp a) (not (equal a 0)))
            (equal (* a (* (/ a) b)) (fix b)))
   :hints (("Goal" :use (:instance associativity-of-*
                                  (acl2::x a) (acl2::y (/ a)) (acl2::z b))
                   :in-theory (disable associativity-of-* commutativity-of-*)))
   :rule-classes nil))

(local
 (defthm generated-numerator-times-denominator
   (implies (rationalp x)
            (equal (* x (denominator x)) (numerator x)))
   :hints (("Goal" :use ((:instance rational-implies1 (acl2::x x))
                        (:instance rational-implies2 (acl2::x x))
                        (:instance generated-multiply-reciprocal
                                   (a (denominator x)) (b (numerator x))))
                   :in-theory (disable rational-implies2)))
   :rule-classes nil))

(local
 (defthm generated-floor-unit-bounds
   (implies (rationalp x)
            (and (<= (floor x 1) x)
                 (< x (1+ (floor x 1)))))
   :hints (("Goal"
            :use (generated-numerator-times-denominator
                  (:instance rational-implies1 (acl2::x x))
                  (:instance generated-quotient-bounds
                             (x (numerator x)) (y (denominator x)))
                  (:instance generated-quotient-bounds
                             (x (- (numerator x))) (y (denominator x))))
            :in-theory (enable floor)
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm generated-floor-as-ratio
   (equal (floor x y) (floor (* x (/ y)) 1))
   :hints (("Goal" :in-theory (enable floor)))
   :rule-classes nil))

(local
 (defthm generated-order-of-multiples
   (implies (and (rationalp a) (rationalp b) (rationalp c) (< 0 c))
            (iff (< (* c a) (* c b)) (< a b)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(defthm generated-floor-bounds
  (implies (and (rationalp x) (rationalp y) (< 0 y))
           (and (<= (* y (floor x y)) x)
                (< x (+ y (* y (floor x y))))))
  :hints (("Goal" :use (generated-floor-as-ratio
                        (:instance generated-floor-unit-bounds (x (* x (/ y))))
                        (:instance generated-multiply-reciprocal (a y) (b x))
                        (:instance generated-order-of-multiples
                                   (c y) (a (* x (/ y))) (b (floor x y)))
                        (:instance generated-order-of-multiples
                                   (c y) (a (* x (/ y))) (b (1+ (floor x y)))))))
  :rule-classes :linear)

(defthm generated-integer-step
  (implies (and (integerp x) (integerp y) (< x y))
           (<= (1+ x) y))
  :rule-classes nil)

(defthm generated-floor-unique
  (implies (and (rationalp x) (rationalp y) (< 0 y)
                (integerp q) (<= (* y q) x) (< x (+ y (* y q))))
           (equal (floor x y) q))
  :hints (("Goal"
           :use (generated-floor-bounds
                 (:instance generated-integer-step (x q) (y (floor x y)))
                 (:instance generated-integer-step (x (floor x y)) (y q))
                 (:instance generated-order-of-multiples
                            (c y) (a (floor x y)) (b (1+ q)))
                 (:instance generated-order-of-multiples
                            (c y) (a q) (b (1+ (floor x y)))))
           :cases ((< (floor x y) q) (< q (floor x y)))))
  :rule-classes nil)

(defthm generated-floor-half-remainder
  (implies (integerp x)
           (or (equal x (* 2 (floor x 2)))
               (equal x (1+ (* 2 (floor x 2))))))
  :hints (("Goal"
           :use ((:instance generated-floor-bounds (y 2))
                 (:instance generated-integer-step (y (1+ (* 2 (floor x 2))))))))
  :rule-classes nil)

(local
 (defthm generated-fold-numeric-factors
   (implies (syntaxp (and (quotep a) (quotep b)))
            (equal (* a (* b x)) (* (* a b) x)))
   :hints (("Goal" :use (:instance associativity-of-*
                                  (acl2::x a) (acl2::y b) (acl2::z x))
                   :in-theory (disable associativity-of-*)))))

(defthm generated-even-double
  (implies (integerp q) (evenp (* 2 q)))
  :hints (("Goal" :in-theory (enable evenp))))

(defthm generated-odd-double-plus-one
  (implies (integerp q) (not (evenp (+ 1 (* 2 q)))))
  :hints (("Goal" :in-theory (enable evenp)
                  :use (:instance generated-integer-step (x q) (y (+ 1/2 q))))))

(defthm generated-floor-half
  (implies (integerp x)
           (equal x (+ (* 2 (floor x 2)) (if (evenp x) 0 1))))
  :hints (("Goal" :use (generated-floor-half-remainder
                        (:instance generated-even-double (q (floor x 2)))
                        (:instance generated-odd-double-plus-one (q (floor x 2))))
                  :in-theory (disable generated-even-double
                                      generated-odd-double-plus-one)))
  :rule-classes nil)

(local
 (defthm generated-floor-of-integer-times-divisor
   (implies (and (integerp q) (rationalp divisor) (< 0 divisor))
            (equal (floor (* divisor q) divisor) q))
   :hints (("Goal" :use (:instance generated-floor-unique
                                   (x (* divisor q)) (y divisor))))))

(defthm generated-powers-of-two-positive
  (and (rationalp (expt 2 n)) (< 0 (expt 2 n)))
  :hints (("Goal" :in-theory (enable expt)
                  :induct (expt 2 n)))
  :rule-classes :type-prescription)

(defthm generated-positive-powers-of-two-linear
  (< 0 (expt 2 n))
  :rule-classes :linear)

(defthm generated-powers-of-two-integer
  (implies (natp n)
           (integerp (expt 2 n)))
  :hints (("Goal" :in-theory (enable expt)
                  :induct (expt 2 n)))
  :rule-classes :type-prescription)

(defthm generated-powers-of-two-step
  (implies (posp n)
           (equal (expt 2 n) (* 2 (expt 2 (1- n)))))
  :hints (("Goal" :expand (expt 2 n))))

(defthm generated-ash-as-floor
  (implies (integerp n)
           (equal (ash x n) (floor (* (ifix x) (expt 2 n)) 1)))
  :hints (("Goal" :in-theory (enable ash))))

(defthm generated-ash-nonnegative-shift
  (implies (natp n)
           (equal (ash x n) (* (ifix x) (expt 2 n))))
  :hints (("Goal" :use (:instance generated-floor-of-integer-times-divisor
                                  (divisor 1) (q (* (ifix x) (expt 2 n)))))))

(defthm generated-ones-as-expt
  (equal (boymoo-model::a64-ones n) (1- (expt 2 (nfix n))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-ones))))

(local
 (defthm generated-logand-base
   (implies (integerp x)
            (and (equal (logand 0 x) 0)
                 (equal (logand x 0) 0)
                 (equal (logand -1 x) x)
                 (equal (logand x -1) x)))
   :hints (("Goal" :in-theory (enable acl2::binary-logand)))))

(defthm generated-logand-recurrence
  (implies (and (integerp x) (integerp y))
           (equal (logand x y)
                  (+ (* 2 (logand (floor x 2) (floor y 2)))
                     (if (or (evenp x) (evenp y)) 0 1))))
  :hints (("Goal"
           :cases ((equal x 0) (equal x -1) (equal y 0) (equal y -1))
           :expand ((logand x y) (logand (floor x 2) (floor y 2)))
           :use (generated-floor-half (:instance generated-floor-half (x y)))))
  :rule-classes nil)

(local
 (defthm generated-floor-half-of-odd
   (implies (integerp q)
            (equal (floor (+ 1 (* 2 q)) 2) q))
   :hints (("Goal" :use (:instance generated-floor-unique
                                   (x (+ 1 (* 2 q))) (y 2))))))

(local
 (defthm generated-low-recurrence
   (implies (and (posp n) (integerp x))
            (equal (boymoo-model::a64-unsigned n x)
                   (+ (* 2 (boymoo-model::a64-unsigned (1- n) (floor x 2)))
                      (if (evenp x) 0 1))))
   :hints (("Goal"
            :use ((:instance generated-logand-recurrence
                             (y (boymoo-model::a64-ones n)))
                  (:instance generated-powers-of-two-step)
                  (:instance generated-floor-half-of-odd
                             (q (1- (expt 2 (1- n)))))
                  (:instance generated-odd-double-plus-one
                             (q (1- (expt 2 (1- n))))))
            :in-theory (e/d (boymoo-model::a64-unsigned)
                            (generated-powers-of-two-step))))
   :rule-classes nil))

(local
 (defthm generated-floor-after-halving
   (implies (and (rationalp x) (posp divisor))
            (equal (floor (floor x 2) divisor)
                   (floor x (* 2 divisor))))
   :hints (("Goal"
            :use ((:instance generated-floor-bounds (y 2))
                  (:instance generated-floor-bounds (x (floor x 2)) (y divisor))
                  (:instance generated-floor-unique
                             (y (* 2 divisor)) (q (floor (floor x 2) divisor)))
                  (:instance generated-integer-step
                             (x (floor x 2))
                             (y (+ divisor (* divisor (floor (floor x 2) divisor))))))))
   :rule-classes nil))

(local
 (defun generated-low-induction (n x)
   (declare (xargs :measure (nfix n)))
   (if (zp n) x
     (generated-low-induction (1- n) (floor x 2)))))

(local
 (defthm generated-floor-of-integer-by-one
   (implies (integerp x)
            (equal (floor x 1) x))
   :hints (("Goal" :use (:instance generated-floor-of-integer-times-divisor
                                   (q x) (divisor 1))))))

(defthm generated-product-of-negative
  (implies (and (acl2-numberp a) (acl2-numberp b))
           (equal (* a (- b)) (- (* a b))))
  :hints (("Goal" :use (:instance distributivity
                                  (acl2::x a) (acl2::y b) (acl2::z (- b))))))

(local
 (defthm generated-mod-of-double-divisor
   (implies (and (integerp x) (posp divisor))
            (equal (mod x (* 2 divisor))
                   (+ (* 2 (mod (floor x 2) divisor)) (if (evenp x) 0 1))))
   :hints (("Goal" :use (generated-floor-half generated-floor-after-halving)
                   :in-theory (enable mod)
                   :nonlinearp t))
   :rule-classes nil))

(local
 (defthm generated-unsigned-as-mod-integer
   (implies (integerp x)
            (equal (boymoo-model::a64-unsigned n x) (mod x (expt 2 (nfix n)))))
   :hints (("Goal" :induct (generated-low-induction n x))
           ("Subgoal *1/2"
            :use (generated-low-recurrence
                  (:instance generated-mod-of-double-divisor
                             (divisor (expt 2 (1- n))))))
           ("Subgoal *1/1" :in-theory (enable boymoo-model::a64-unsigned mod)))
   :rule-classes nil))

(defthm generated-unsigned-as-mod
  (equal (boymoo-model::a64-unsigned n x) (mod (ifix x) (expt 2 (nfix n))))
  :hints (("Goal"
           :use (:instance generated-unsigned-as-mod-integer (x (ifix x)))
           :in-theory (enable boymoo-model::a64-unsigned)))
  :rule-classes nil)

(defthm generated-unsigned-of-bounded
  (implies (and (natp x) (< x (expt 2 (nfix n))))
           (equal (boymoo-model::a64-unsigned n x) x))
  :hints (("Goal" :in-theory (enable mod)
                  :use (generated-unsigned-as-mod
                        (:instance generated-floor-unique
                                   (y (expt 2 (nfix n))) (q 0))))))

(defthm generated-unsigned-bounds
  (and (natp (boymoo-model::a64-unsigned n x))
       (< (boymoo-model::a64-unsigned n x) (expt 2 (nfix n))))
  :hints (("Goal" :in-theory (enable mod)
                  :use (generated-unsigned-as-mod
                        (:instance generated-floor-bounds
                                   (x (ifix x)) (y (expt 2 (nfix n)))))))
  :rule-classes ((:type-prescription
                  :corollary (natp (boymoo-model::a64-unsigned n x)))
                 (:linear
                  :corollary (< (boymoo-model::a64-unsigned n x)
                                 (expt 2 (nfix n))))))

(defthm generated-unsigned-idempotent
  (equal (boymoo-model::a64-unsigned n (boymoo-model::a64-unsigned n x))
         (boymoo-model::a64-unsigned n x)))

(defthm generated-unsigned-of-remainder
  (implies (and (integerp x) (natp r) (< r (expt 2 (nfix n)))
                (integerp q) (equal x (+ r (* q (expt 2 (nfix n))))))
           (equal (boymoo-model::a64-unsigned n x) r))
  :hints (("Goal" :in-theory (enable mod)
                  :use (generated-unsigned-as-mod
                        (:instance generated-floor-unique
                                   (y (expt 2 (nfix n)))))))
  :rule-classes nil)

(defthm generated-floor-of-multiple-and-remainder
  (implies (and (integerp q) (posp divisor) (natp r) (< r divisor))
           (equal (floor (+ (* divisor q) r) divisor) q))
  :hints (("Goal" :use (:instance generated-floor-unique
                                  (x (+ (* divisor q) r)) (y divisor)))))

(defthm generated-floor-add-multiple
  (implies (and (integerp q) (integerp x) (posp divisor))
           (equal (floor (+ (* divisor q) x) divisor)
                  (+ q (floor x divisor))))
  :hints (("Goal" :use ((:instance generated-floor-unique
                                   (x (+ (* divisor q) x)) (y divisor)
                                   (q (+ q (floor x divisor))))
                         (:instance generated-floor-bounds (y divisor))))))

(defthm generated-unsigned-add-multiple
  (implies (and (integerp x) (integerp q))
           (equal (boymoo-model::a64-unsigned n (+ (* (expt 2 (nfix n)) q) x))
                  (boymoo-model::a64-unsigned n x)))
  :hints (("Goal" :in-theory (enable mod)
                  :use (generated-unsigned-as-mod
                        (:instance generated-unsigned-as-mod
                                   (x (+ (* (expt 2 (nfix n)) q) x)))
                        (:instance generated-floor-add-multiple
                                   (divisor (expt 2 (nfix n))))))))

(defthm generated-logbitp-of-bounded
  (implies (and (natp bit) (natp x) (< x (* 2 (expt 2 bit))))
           (equal (logbitp bit x) (<= (expt 2 bit) x)))
  :hints (("Goal" :cases ((< x (expt 2 bit)))
                  :use ((:instance generated-floor-unique (y (expt 2 bit)) (q 0))
                        (:instance generated-floor-unique (y (expt 2 bit)) (q 1)))
                  :in-theory (enable logbitp oddp))))

(defthm generated-signed-64-of-word
  (equal (boymoo-model::a64-signed 64 x)
         (let ((word (boymoo-model::a64-unsigned 64 x)))
           (if (< word (expt 2 63)) word (- word (expt 2 64)))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-signed)
                  :use (:instance generated-logbitp-of-bounded
                                  (bit 63) (x (boymoo-model::a64-unsigned 64 x))))))

(defthm generated-signed-64-bounds
  (let ((x (boymoo-model::a64-signed 64 bits)))
    (and (<= (- (expt 2 63)) x) (< x (expt 2 63))))
  :rule-classes :linear)

(defthm generated-signed-64-of-signed-range
  (implies (and (integerp x) (<= (- (expt 2 63)) x) (< x (expt 2 63)))
           (equal (boymoo-model::a64-signed 64 x) x))
  :hints (("Goal" :cases ((< x 0))
                  :use (:instance generated-unsigned-of-remainder
                                  (n 64) (q -1) (r (+ x (expt 2 64)))))))

; Prefer explicit uses of this signed interpretation in instruction proofs.
(in-theory (disable generated-signed-64-of-word))
