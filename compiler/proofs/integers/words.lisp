(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt)))

(local
 (defthm integer-nonnegative-quotient-bounds
   (implies (and (natp n) (posp d))
            (and (<= (* d (nonnegative-integer-quotient n d)) n)
                 (< n (* d (+ 1 (nonnegative-integer-quotient n d))))))
   :rule-classes nil
   :hints (("Goal" :induct (nonnegative-integer-quotient n d)))))

(local
 (defthm integer-cancel-reciprocal
   (implies (and (rationalp d) (not (equal d 0)) (rationalp n))
            (equal (* d (* (/ d) n)) n))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable associativity-of-*)
            :use ((:instance associativity-of-* (acl2::x d)
                                          (acl2::y (/ d)) (acl2::z n)))))))

(local
 (defthm integer-numerator-as-product
   (implies (rationalp x)
            (equal (* x (denominator x)) (numerator x)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable acl2::rational-implies2)
            :use ((:instance acl2::rational-implies2 (acl2::x x))
                  (:instance integer-cancel-reciprocal
                             (d (denominator x)) (n (numerator x))))))))

(local
 (defthm integer-product-right-negation
   (implies (and (rationalp a) (rationalp b))
            (equal (* a (- b)) (- (* a b))))
   :hints (("Goal" :in-theory (disable distributivity)
            :use ((:instance distributivity (acl2::x a)
                                            (acl2::y b) (acl2::z (- b))))))))

(local
 (defthm integer-negative-quotient-strict-bound
   (implies (and (rationalp x)
                 (< (numerator x) 0)
                 (< 1 (denominator x)))
            (< (* (denominator x)
                  (nonnegative-integer-quotient (- (numerator x))
                                               (denominator x)))
               (- (numerator x))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (disable nonnegative-integer-quotient)
            :nonlinearp t
            :use ((:instance integer-nonnegative-quotient-bounds
                             (n (- (numerator x))) (d (denominator x)))
                  (:instance acl2::lowest-terms
                             (acl2::x x) (acl2::n (denominator x))
                             (acl2::r (- (nonnegative-integer-quotient
                                          (- (numerator x)) (denominator x))))
                             (acl2::q 1)))))))

(local
 (defthm integer-floor-by-one-bounds
   (implies (rationalp x)
            (and (<= (floor x 1) x)
                 (< x (+ 1 (floor x 1)))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (floor) (nonnegative-integer-quotient))
            :nonlinearp t
            :use (integer-numerator-as-product
                  integer-negative-quotient-strict-bound
                  (:instance integer-nonnegative-quotient-bounds
                             (n (numerator x)) (d (denominator x)))
                  (:instance integer-nonnegative-quotient-bounds
                             (n (- (numerator x))) (d (denominator x))))))))

(defthm integer-floor-bounds
  (implies (and (rationalp x) (rationalp y) (< 0 y))
           (and (<= (floor x y) (/ x y))
                (< (/ x y) (+ 1 (floor x y)))))
  :rule-classes :linear
  :hints (("Goal" :in-theory (e/d (floor) (nonnegative-integer-quotient))
           :use ((:instance integer-floor-by-one-bounds (x (/ x y)))))))

(local
 (defthm integer-scale-order
   (implies (and (rationalp a) (rationalp b) (rationalp d) (< 0 d))
            (equal (< (* d a) (* d b)) (< a b)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t :cases ((< a b) (equal a b))))))

(defthm integer-floor-scaled-bounds
  (implies (and (rationalp x) (rationalp y) (< 0 y))
           (and (<= (* y (floor x y)) x)
                (< x (* y (+ 1 (floor x y))))))
  :rule-classes nil
  :hints (("Goal" :use (integer-floor-bounds
                        (:instance integer-cancel-reciprocal (d y) (n x))
                        (:instance integer-scale-order
                                   (d y) (a (/ x y)) (b (floor x y)))
                        (:instance integer-scale-order
                                   (d y) (a (/ x y)) (b (+ 1 (floor x y))))))))

(defthm integer-floor-unique
  (implies (and (rationalp x) (rationalp y) (< 0 y)
                (integerp q)
                (<= (* q y) x) (< x (* (+ 1 q) y)))
           (equal (floor x y) q))
  :rule-classes nil
  :hints (("Goal"
           :use integer-floor-scaled-bounds
           :nonlinearp t)))

(defthm integer-mod-of-division
  (implies (and (integerp q) (natp r) (posp y) (< r y))
           (equal (mod (+ (* q y) r) y) r))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable mod)
           :use ((:instance integer-floor-unique (x (+ (* q y) r)))))))

(defthm integer-floor-and-mod-decomposition
  (implies (and (integerp x) (posp d))
           (and (natp (mod x d))
                (< (mod x d) d)
                (equal (+ (mod x d) (* d (floor x d))) x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable mod)
           :use ((:instance integer-floor-scaled-bounds (y d))))))

(defthm integer-mod-bounds
  (implies (and (integerp x) (posp d))
           (and (<= 0 (mod x d)) (< (mod x d) d)))
  :rule-classes :linear
  :hints (("Goal" :use integer-floor-and-mod-decomposition)))

(defthm integer-mod-is-integer
  (implies (and (integerp x) (integerp d))
           (integerp (mod x d)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable mod))))

(defthm integer-mod-unique
  (implies (and (integerp q) (natp r) (posp d) (< r d)
                (equal x (+ (* q d) r)))
           (equal (mod x d) r))
  :rule-classes nil
  :hints (("Goal" :use ((:instance integer-mod-of-division (y d))))))

(defthm integer-mod-when-in-range
  (implies (and (natp x) (posp d) (< x d))
           (equal (mod x d) x))
  :hints (("Goal" :use ((:instance integer-mod-unique (r x) (q 0))))))

(defthm integer-mod-when-negative-and-in-range
  (implies (and (integerp x) (posp d) (<= (- d) x) (< x 0))
           (equal (mod x d) (+ d x)))
  :hints (("Goal" :use ((:instance integer-mod-unique (r (+ d x)) (q -1))))))

(defthm integer-power-of-two-is-positive
  (implies (natp width)
           (posp (expt 2 width)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (expt 2 width) :in-theory (enable expt))))

(defthmd integer-power-of-two-step
  (implies (posp width)
           (equal (expt 2 width) (* 2 (expt 2 (1- width)))))
  :hints (("Goal" :expand (expt 2 width))))

(defthm integer-oddp-by-remainder
  (implies (integerp x)
           (equal (oddp x) (equal (mod x 2) 1)))
  :hints (("Goal" :in-theory (enable oddp evenp)
           :use ((:instance integer-floor-bounds (y 2))
                 (:instance integer-floor-and-mod-decomposition (d 2))))))

(defthm integer-evenp-by-remainder
  (implies (integerp x)
           (equal (evenp x) (equal (mod x 2) 0)))
  :hints (("Goal" :in-theory (e/d (oddp) (evenp integer-oddp-by-remainder))
           :use integer-oddp-by-remainder)))

(defthm integer-floor-of-double-plus-bit
  (implies (and (integerp high) (bitp low))
           (equal (floor (+ (* 2 high) low) 2) high))
  :hints (("Goal" :use ((:instance integer-floor-unique
                                  (x (+ (* 2 high) low)) (y 2) (q high))))))

(defthm integer-mod-of-double-plus-bit
  (implies (and (integerp high) (bitp low))
           (equal (mod (+ (* 2 high) low) 2) low))
  :hints (("Goal" :use ((:instance integer-mod-of-division
                                  (q high) (r low) (y 2))))))

(local (in-theory (disable oddp evenp acl2::binary-logand)))

(defthm integer-logand-zero-and-minus-one
  (implies (integerp x)
           (and (equal (logand 0 x) 0)
                (equal (logand x 0) 0)
                (equal (logand -1 x) x)
                (equal (logand x -1) x)))
  :hints (("Goal" :expand ((logand 0 x) (logand x 0)
                           (logand -1 x) (logand x -1)))))

(defthmd integer-logand-split
  (implies (and (integerp x) (integerp y))
           (equal (logand x y)
                  (+ (* 2 (logand (floor x 2) (floor y 2)))
                     (if (and (oddp x) (oddp y)) 1 0))))
  :hints (("Goal" :expand ((logand x y))
           :use ((:instance integer-floor-and-mod-decomposition (d 2))
                 (:instance integer-floor-and-mod-decomposition (x y) (d 2))))))

(local
 (defthm integer-mod-of-twice-divisor
   (implies (and (integerp x) (posp d))
            (equal (mod x (* 2 d))
                   (+ (mod x 2) (* 2 (mod (floor x 2) d)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance integer-floor-and-mod-decomposition (d 2))
                  (:instance integer-floor-and-mod-decomposition (x (floor x 2)))
                  (:instance integer-mod-unique
                             (d (* 2 d)) (q (floor (floor x 2) d))
                             (r (+ (mod x 2) (* 2 (mod (floor x 2) d))))))
            :nonlinearp t))))

(local
 (defun integer-halving-induction (width x)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       x
     (integer-halving-induction (1- width) (floor x 2)))))

(local
 (defthm integer-mask-recurrence
   (implies (posp width)
            (let ((mask (- (expt 2 width) 1))
                  (half-mask (- (expt 2 (1- width)) 1)))
              (and (equal (floor mask 2) half-mask)
                   (oddp mask))))
   :hints (("Goal"
            :use (integer-power-of-two-step
                  (:instance integer-floor-unique
                             (x (- (expt 2 width) 1)) (y 2)
                             (q (- (expt 2 (1- width)) 1)))
                  (:instance integer-mod-unique
                             (x (- (expt 2 width) 1)) (d 2)
                             (q (- (expt 2 (1- width)) 1)) (r 1)))))))

(defthm integer-logand-low-mask
  (implies (and (integerp x) (natp width))
           (equal (logand x (1- (expt 2 width)))
                  (mod x (expt 2 width))))
  :hints (("Goal" :induct (integer-halving-induction width x))
          ("Subgoal *1/1"
           :in-theory (enable (:executable-counterpart expt)
                              (:executable-counterpart acl2::binary-logand))
           :expand ((logand x 0))
           :use ((:instance integer-mod-unique (d 1) (q x) (r 0))))
          ("Subgoal *1/2"
           :use (integer-power-of-two-step
                 (:instance integer-logand-split
                            (y (1- (expt 2 width))))
                 (:instance integer-mod-of-twice-divisor
                            (d (expt 2 (1- width)))))
           :in-theory (enable integer-mask-recurrence))))

(defthm integer-a64-unsigned-is-mod
  (implies (natp width)
           (equal (boymoo-model::a64-unsigned width x)
                  (mod (ifix x) (expt 2 width))))
  :hints (("Goal" :in-theory (enable ash)
           :use ((:instance integer-logand-low-mask (x (ifix x)))
                 (:instance integer-floor-unique
                            (x (expt 2 width)) (y 1) (q (expt 2 width)))))))

(defthm integer-a64-unsigned-type
  (implies (natp width)
           (unsigned-byte-p width (boymoo-model::a64-unsigned width x)))
  :hints (("Goal" :in-theory (e/d (unsigned-byte-p integer-range-p)
                                  (boymoo-model::a64-unsigned)))))
