(in-package "BOYMOO-PROOFS")

(include-book "../foundations/machine")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm symbols-quotient-bounds
   (implies (and (natp numerator) (posp denominator))
            (let ((q (nonnegative-integer-quotient numerator denominator)))
              (and (<= (* denominator q) numerator)
                   (< numerator (* denominator (+ 1 q))))))
   :hints (("Goal" :induct (nonnegative-integer-quotient numerator denominator)))))

(local
 (defthm symbols-positive-scaling
   (implies (and (rationalp x) (rationalp y) (rationalp factor) (< 0 factor))
            (iff (< (* factor x) (* factor y)) (< x y)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm symbols-positive-scaling-equality
   (implies (and (rationalp x) (rationalp y) (rationalp factor) (< 0 factor))
            (iff (equal (* factor x) (* factor y)) (equal x y)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm symbols-cancel-scaled-inverse
   (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp value))
            (equal (* divisor (* (/ divisor) value)) value))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x divisor) (acl2::y (/ divisor)) (acl2::z value)))
            :in-theory (disable acl2::associativity-of-*)))))

(local
 (defthm symbols-cancel-division
   (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp value)
                 (equal ratio (* (/ divisor) value)))
            (equal (* ratio divisor) value))
   :hints (("Goal" :use symbols-cancel-scaled-inverse))
   :rule-classes nil))

(local
 (defthm symbols-product-with-denominator
   (implies (rationalp x)
            (equal (* x (denominator x)) (numerator x)))
   :hints (("Goal"
            :use ((:instance acl2::rational-implies1 (acl2::x x))
                  (:instance acl2::rational-implies2 (acl2::x x))
                  (:instance symbols-cancel-division
                             (ratio x) (divisor (denominator x)) (value (numerator x))))
            :in-theory (disable acl2::rational-implies2)
            :nonlinearp t))))

(local
 (defthm symbols-numerator-over-one
   (implies (and (rationalp ratio) (equal (denominator ratio) 1))
            (equal (numerator ratio) ratio))
   :hints (("Goal"
            :use ((:instance symbols-product-with-denominator (x ratio)))
            :in-theory (disable symbols-product-with-denominator)))))

(defthm symbols-multiply-negative
  (implies (and (acl2-numberp a) (acl2-numberp b))
           (equal (* a (- b)) (- (* a b))))
  :hints (("Goal"
           :use ((:instance acl2::distributivity
                            (acl2::x a) (acl2::y b) (acl2::z (- b))))
           :in-theory (disable acl2::distributivity))))

(local
 (defthm symbols-negate-twice
   (implies (rationalp x) (equal (- (- x)) x))
   :hints (("Goal"
            :use ((:instance acl2::inverse-of-+ (acl2::x x))
                  (:instance acl2::inverse-of-+ (acl2::x (- x))))))))

(local
 (defthm symbols-floor-of-ratio-bounds
   (implies (rationalp ratio)
            (let ((q (floor ratio 1)))
              (and (<= q ratio) (< ratio (+ 1 q)))))
   :hints (("Goal"
            :cases ((equal ratio
                           (- (nonnegative-integer-quotient
                               (- (numerator ratio)) (denominator ratio)))))
            :use ((:instance acl2::rational-implies1 (acl2::x ratio))
                  (:instance symbols-quotient-bounds
                             (numerator (numerator ratio))
                             (denominator (denominator ratio)))
                  (:instance symbols-quotient-bounds
                             (numerator (- (numerator ratio)))
                             (denominator (denominator ratio)))
                  (:instance symbols-positive-scaling
                             (x ratio) (y (floor ratio 1)) (factor (denominator ratio)))
                  (:instance symbols-positive-scaling
                             (x ratio) (y (+ 1 (floor ratio 1)))
                             (factor (denominator ratio)))
                  (:instance symbols-positive-scaling-equality
                             (x ratio)
                             (y (- (nonnegative-integer-quotient
                                    (- (numerator ratio)) (denominator ratio))))
                             (factor (denominator ratio))))
            :in-theory (disable symbols-quotient-bounds)
            :nonlinearp t))))

(defthm symbols-floor-bounds
  (implies (and (rationalp x) (rationalp divisor) (< 0 divisor))
           (let ((q (floor x divisor)))
             (and (<= (* divisor q) x)
                  (< x (* divisor (+ 1 q))))))
  :hints (("Goal"
           :use ((:instance symbols-floor-of-ratio-bounds
                            (ratio (* x (/ divisor))))
                 (:instance symbols-positive-scaling
                            (x (* x (/ divisor))) (y (floor x divisor)) (factor divisor))
                 (:instance symbols-positive-scaling
                            (x (* x (/ divisor))) (y (+ 1 (floor x divisor)))
                            (factor divisor)))
           :in-theory (disable symbols-floor-of-ratio-bounds)
           :nonlinearp t))
  :rule-classes nil)

(local
 (defthm symbols-integer-gap
   (implies (and (integerp x) (integerp y) (< x y))
            (<= (1+ x) y))
   :rule-classes nil))

(defthm symbols-floor-of-decomposition
  (implies (and (integerp q) (rationalp r) (<= 0 r)
                (rationalp divisor) (< r divisor))
           (equal (floor (+ (* divisor q) r) divisor) q))
  :hints (("Goal"
           :use ((:instance symbols-floor-bounds (x (+ (* divisor q) r)))
                 (:instance symbols-positive-scaling
                            (x (floor (+ (* divisor q) r) divisor))
                            (y (+ 1 q)) (factor divisor))
                 (:instance symbols-positive-scaling
                            (x (+ 1 (floor (+ (* divisor q) r) divisor)))
                            (y q) (factor divisor))
                 (:instance symbols-integer-gap
                            (x q) (y (floor (+ (* divisor q) r) divisor)))
                 (:instance symbols-integer-gap
                            (x (floor (+ (* divisor q) r) divisor)) (y q)))
           :cases ((< (floor (+ (* divisor q) r) divisor) q))
           :in-theory (disable floor)
           :nonlinearp t)))

(defthm symbols-mod-bounds
  (implies (and (integerp x) (posp divisor))
           (< (mod x divisor) divisor))
  :hints (("Goal" :use symbols-floor-bounds :in-theory (disable floor)))
  :rule-classes :linear)

(defthm symbols-mod-natural
  (implies (and (integerp x) (posp divisor))
           (natp (mod x divisor)))
  :hints (("Goal" :use symbols-floor-bounds :in-theory (disable floor)))
  :rule-classes :type-prescription)

(defthm symbols-mod-of-decomposition
  (implies (and (integerp q) (rationalp r) (<= 0 r)
                (rationalp divisor) (< r divisor))
           (equal (mod (+ (* divisor q) r) divisor) r))
  :hints (("Goal" :use symbols-floor-of-decomposition
                  :in-theory (disable floor symbols-floor-of-decomposition))))

(local
 (defthm symbols-zero-product
   (equal (* 0 x) 0)
   :hints (("Goal"
            :use ((:instance acl2::distributivity
                             (acl2::x x) (acl2::y 0) (acl2::z 0)))
            :in-theory (disable acl2::distributivity)))))

(defthm symbols-mod-in-range
  (implies (and (rationalp x) (<= 0 x) (rationalp divisor) (< x divisor))
           (equal (mod x divisor) x))
  :hints (("Goal"
           :use ((:instance symbols-mod-of-decomposition (q 0) (r x)))
           :in-theory (disable mod symbols-mod-of-decomposition))))

(local
 (defthm symbols-integer-low-bit
   (implies (integerp x)
            (equal (mod x 2) (if (evenp x) 0 1)))
   :hints (("Goal"
            :use ((:instance symbols-mod-bounds (divisor 2))
                  (:instance symbols-mod-natural (divisor 2))
                  (:instance symbols-floor-of-decomposition
                             (q (* 1/2 x)) (r 0) (divisor 2)))
            :cases ((equal (* 1/2 x) (floor x 2)))
            :in-theory (disable floor symbols-mod-bounds
                                symbols-floor-of-decomposition)))))

(local
 (defthm symbols-logand-boundary
   (and (equal (logand 0 y) 0)
        (equal (logand x 0) 0)
        (equal (logand -1 y) (ifix y))
        (equal (logand x -1) (ifix x)))
   :hints (("Goal" :expand ((acl2::binary-logand 0 y) (acl2::binary-logand x 0)
                            (acl2::binary-logand -1 y) (acl2::binary-logand x -1))))))

(defthm symbols-logand-split
  (implies (and (integerp x) (integerp y))
           (equal (logand x y)
                  (+ (* 2 (logand (floor x 2) (floor y 2)))
                     (if (and (oddp x) (oddp y)) 1 0))))
  :hints (("Goal"
           :use ((:instance symbols-integer-low-bit (x x))
                 (:instance symbols-integer-low-bit (x y)))
           :expand ((acl2::binary-logand x y))
           :in-theory (disable floor acl2::binary-logand symbols-integer-low-bit)))
  :rule-classes nil)

(defthm symbols-power-of-two
  (implies (natp width)
           (posp (expt 2 width)))
  :hints (("Goal" :induct (expt 2 width)))
  :rule-classes :type-prescription)

(local
 (defthm symbols-power-of-two-step
   (implies (posp width)
            (equal (expt 2 width) (* 2 (expt 2 (1- width)))))
   :hints (("Goal" :expand ((expt 2 width))))
   :rule-classes nil))

(local
 (defthm symbols-mask-quotient
   (implies (posp half)
            (and (equal (floor (1- (* 2 half)) 2) (1- half))
                 (not (evenp (1- (* 2 half))))))
   :hints (("Goal"
            :use ((:instance symbols-floor-of-decomposition
                             (q (1- half)) (r 1) (divisor 2))
                  (:instance symbols-integer-low-bit (x (1- (* 2 half)))))
            :in-theory (disable floor symbols-floor-of-decomposition
                                symbols-integer-low-bit)))))

(local
 (defthm symbols-mod-of-twice-decomposition
   (implies (and (integerp quotient) (natp remainder)
                 (natp bit) (< bit 2)
                 (posp divisor) (< remainder divisor))
            (equal (mod (+ (* 2 divisor quotient) (* 2 remainder) bit)
                        (* 2 divisor))
                   (+ (* 2 remainder) bit)))
   :hints (("Goal"
            :use ((:instance symbols-mod-of-decomposition
                             (q quotient) (r (+ (* 2 remainder) bit))
                             (divisor (* 2 divisor)))
                  (:instance symbols-integer-gap (x remainder) (y divisor))
                  (:instance symbols-integer-gap (x bit) (y 2)))
            :in-theory (disable mod symbols-mod-of-decomposition)
            :nonlinearp t))))

(local
 (defthm symbols-mod-through-halving
   (implies (and (integerp x) (posp divisor))
            (equal (mod x (* 2 divisor))
                   (+ (* 2 (mod (floor x 2) divisor)) (mod x 2))))
   :hints (("Goal"
            :use ((:instance symbols-mod-of-twice-decomposition
                             (quotient (floor (floor x 2) divisor))
                             (remainder (mod (floor x 2) divisor))
                             (bit (mod x 2)))
                  (:instance symbols-mod-bounds (x (floor x 2)))
                  (:instance symbols-mod-bounds (divisor 2))
                  (:instance symbols-mod-natural (x (floor x 2)))
                  (:instance symbols-mod-natural (divisor 2)))
            :in-theory (disable floor symbols-mod-of-twice-decomposition
                                symbols-integer-low-bit)
            :nonlinearp t))))

(local
 (defun symbols-halving-induction (width x)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       x
     (symbols-halving-induction (1- width) (floor x 2)))))

(defthm symbols-logand-low-mask
  (implies (and (integerp x) (natp width))
           (equal (logand x (1- (expt 2 width)))
                  (mod x (expt 2 width))))
  :hints (("Goal" :induct (symbols-halving-induction width x)
                  :in-theory (disable acl2::binary-logand floor mod expt))
          ("Subgoal *1/2"
           :use ((:instance symbols-logand-split (y (1- (expt 2 width))))
                 (:instance symbols-power-of-two-step)
                 (:instance symbols-mask-quotient (half (expt 2 (1- width))))
                 (:instance symbols-mod-through-halving (divisor (expt 2 (1- width))))
                 (:instance symbols-integer-low-bit))
           :in-theory (disable symbols-mod-through-halving symbols-integer-low-bit
                               symbols-mask-quotient))
          ("Subgoal *1/1"
           :use ((:instance symbols-mod-of-decomposition
                            (q x) (r 0) (divisor 1))))))

(defthm symbols-unsigned-as-mod
  (equal (boymoo-model::a64-unsigned width x)
         (mod (ifix x) (expt 2 (nfix width))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned
                                     boymoo-model::a64-ones ash))))

(defthm symbols-unsigned-natural
  (natp (boymoo-model::a64-unsigned width x))
  :hints (("Goal" :in-theory (disable mod expt)))
  :rule-classes :type-prescription)

(defthm symbols-unsigned-upper-bound
  (< (boymoo-model::a64-unsigned width x) (expt 2 (nfix width)))
  :hints (("Goal" :in-theory (disable mod expt)))
  :rule-classes :linear)

(defthm symbols-unsigned-in-range
  (implies (and (integerp x) (<= 0 x) (< x (expt 2 (nfix width))))
           (equal (boymoo-model::a64-unsigned width x) x))
  :hints (("Goal" :in-theory (disable mod expt))))

(defthm symbols-unsigned-idempotent
  (equal (boymoo-model::a64-unsigned width (boymoo-model::a64-unsigned width x))
         (boymoo-model::a64-unsigned width x))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned
                                      symbols-unsigned-as-mod))))

(defthm symbols-mod-translation
  (implies (and (integerp x) (integerp q) (posp divisor))
           (equal (mod (+ x (* divisor q)) divisor)
                  (mod x divisor)))
  :hints (("Goal"
           :use ((:instance symbols-mod-of-decomposition
                            (q (+ q (floor x divisor))) (r (mod x divisor)))
                 (:instance symbols-mod-bounds)
                 (:instance symbols-mod-natural))
           :in-theory (disable symbols-mod-of-decomposition floor)
           :nonlinearp t)))

(defthm symbols-mod-of-nested-mod
  (implies (and (integerp x) (posp factor) (posp divisor))
           (equal (mod (mod x (* factor divisor)) divisor)
                  (mod x divisor)))
  :hints (("Goal"
           :use ((:instance symbols-mod-translation
                            (q (- (* factor (floor x (* factor divisor)))))))
           :in-theory (disable symbols-mod-translation floor)
           :nonlinearp t)))

(defthm symbols-unsigned-sum-left
  (implies (and (integerp x) (integerp y))
           (equal (boymoo-model::a64-unsigned
                   width (+ (boymoo-model::a64-unsigned width x) y))
                  (boymoo-model::a64-unsigned width (+ x y))))
  :hints (("Goal"
           :use ((:instance symbols-mod-translation
                            (x (+ x y)) (divisor (expt 2 (nfix width)))
                            (q (- (floor x (expt 2 (nfix width)))))))
           :in-theory (disable floor expt symbols-mod-translation)
           :nonlinearp t)))

(defthm symbols-unsigned-sum-right
  (implies (and (integerp x) (integerp y))
           (equal (boymoo-model::a64-unsigned
                   width (+ y (boymoo-model::a64-unsigned width x)))
                  (boymoo-model::a64-unsigned width (+ y x))))
  :hints (("Goal" :use symbols-unsigned-sum-left
                  :in-theory (disable boymoo-model::a64-unsigned
                                      symbols-unsigned-as-mod symbols-unsigned-sum-left))))

(local
 (defthm symbols-half-of-twice
   (equal (* 1/2 (* 2 x)) (fix x))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x 1/2) (acl2::y 2) (acl2::z x)))
            :in-theory (disable acl2::associativity-of-*)))))

(defthm symbols-doubling-keeps-mask
  (implies (and (posp count)
                (equal (logand count (1- count)) 0))
           (equal (logand (* 2 count) (1- (* 2 count))) 0))
  :hints (("Goal"
           :use ((:instance symbols-logand-split (x (* 2 count)) (y (1- (* 2 count))))
                 (:instance symbols-floor-of-decomposition (q count) (r 0) (divisor 2))
                 (:instance symbols-mask-quotient (half count)))
           :in-theory (disable acl2::binary-logand floor symbols-floor-of-decomposition
                               symbols-mask-quotient))))

(defthm symbols-ash-left-is-product
  (implies (natp count)
           (equal (ash word count) (* (ifix word) (expt 2 count))))
  :hints (("Goal"
           :use ((:instance symbols-floor-of-decomposition
                            (q (* (ifix word) (expt 2 count))) (r 0) (divisor 1)))
           :in-theory (disable floor expt symbols-floor-of-decomposition))))

(local
 (defthm symbols-commutativity-of-leading-factors
   (equal (* a (* b c)) (* b (* a c)))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-* (acl2::x a) (acl2::y b) (acl2::z c))
                  (:instance acl2::associativity-of-* (acl2::x b) (acl2::y a) (acl2::z c)))
            :in-theory (disable acl2::associativity-of-*)))))

(defthm symbols-unsigned-of-scaled-sum
  (implies (and (integerp x) (integerp scale) (integerp addend))
           (equal (boymoo-model::a64-unsigned
                   width (+ (* scale (boymoo-model::a64-unsigned width x)) addend))
                  (boymoo-model::a64-unsigned width (+ (* scale x) addend))))
  :hints (("Goal"
           :use ((:instance symbols-mod-translation
                            (x (+ (* scale x) addend)) (divisor (expt 2 (nfix width)))
                            (q (- (* scale (floor x (expt 2 (nfix width))))))))
           :in-theory (disable floor expt symbols-mod-translation)
           :nonlinearp t)))

(local
 (defthm symbols-powers-multiply
   (implies (and (natp x) (natp y))
            (equal (* (expt 2 x) (expt 2 y))
                   (expt 2 (+ x y))))
   :hints (("Goal" :induct (expt 2 x)))))

(defthm symbols-unsigned-narrower
  (implies (and (natp narrow) (natp wide) (<= narrow wide))
           (equal (boymoo-model::a64-unsigned narrow (boymoo-model::a64-unsigned wide x))
                  (boymoo-model::a64-unsigned narrow x)))
  :hints (("Goal"
           :use ((:instance symbols-mod-of-nested-mod
                            (x (ifix x)) (factor (expt 2 (- wide narrow)))
                            (divisor (expt 2 narrow)))
                 (:instance symbols-power-of-two (width (- wide narrow)))
                 (:instance symbols-powers-multiply (x (- wide narrow)) (y narrow)))
           :in-theory (disable mod floor expt
                               symbols-mod-of-nested-mod symbols-powers-multiply))))

(defthm symbols-logand-commutes
  (equal (logand x y) (logand y x))
  :hints (("Goal" :induct (logand x y)
                  :expand ((logand x y) (logand y x))
                  :in-theory (disable (:definition acl2::binary-logand) floor)))
  :rule-classes nil)

(defthm symbols-unsigned-translate-by-wider-modulus
  (implies (and (natp narrow) (natp wide) (<= narrow wide)
                (integerp x) (integerp multiple))
           (equal (boymoo-model::a64-unsigned narrow (+ x (* (expt 2 wide) multiple)))
                  (boymoo-model::a64-unsigned narrow x)))
  :hints (("Goal"
           :use ((:instance symbols-mod-translation
                            (divisor (expt 2 narrow))
                            (q (* multiple (expt 2 (- wide narrow)))))
                 (:instance symbols-power-of-two (width (- wide narrow)))
                 (:instance symbols-powers-multiply (x (- wide narrow)) (y narrow)))
           :in-theory (disable mod floor expt
                               symbols-mod-translation symbols-powers-multiply))))

(defthm symbols-signed-retains-low-bits
  (implies (and (natp narrow) (posp wide) (<= narrow wide))
           (equal (boymoo-model::a64-unsigned narrow (boymoo-model::a64-signed wide x))
                  (boymoo-model::a64-unsigned narrow x)))
  :hints (("Goal"
           :use ((:instance symbols-unsigned-translate-by-wider-modulus
                            (x (boymoo-model::a64-unsigned wide x)) (multiple -1)))
           :in-theory (disable mod floor expt logbitp
                               boymoo-model::a64-unsigned
                               symbols-unsigned-as-mod
                               symbols-unsigned-translate-by-wider-modulus))))

(defthm symbols-signed-is-integer
  (integerp (boymoo-model::a64-signed width value))
  :rule-classes :type-prescription)

(local
 (defthm symbols-floor-two-for-natural
   (implies (natp value)
            (and (natp (floor value 2)) (<= (* 2 (floor value 2)) value)))
   :hints (("Goal"
            :use ((:instance symbols-floor-bounds (x value) (divisor 2)))
            :in-theory (disable floor)))
   :rule-classes nil))

(local
 (defthm symbols-odd-value-above-double
   (implies (and (integerp value) (integerp half) (oddp value)
                 (<= (* 2 half) value))
            (< (* 2 half) value))
   :hints (("Goal" :cases ((equal value (* 2 half)))))
   :rule-classes nil))

(local
 (defthm symbols-and-step-bound
   (implies (and (natp mask) (natp half) (natp rest)
                 (<= rest half) (<= (* 2 half) mask))
            (<= (+ (* 2 rest) (if (and (oddp mask) (oddp x)) 1 0))
                mask))
   :hints (("Goal"
            :use ((:instance symbols-odd-value-above-double (value mask))
                  (:instance symbols-integer-gap (x (* 2 half)) (y mask)))))
   :rule-classes nil))

(defthm symbols-and-mask-bounds
  (implies (and (natp mask) (integerp x))
           (and (natp (logand mask x))
                (<= (logand mask x) mask)))
  :hints (("Goal" :induct (logand mask x)
                  :expand ((logand mask x))
                  :in-theory (disable (:definition acl2::binary-logand) floor))
          ("Subgoal *1/5"
           :use ((:instance symbols-floor-two-for-natural (value mask))
                 (:instance symbols-and-step-bound
                            (half (floor mask 2))
                            (rest (logand (floor mask 2) (floor x 2))))))))

(defthm symbols-and-low-aligned-is-zero
  (implies (and (natp width) (natp low) (< low (expt 2 width))
                (integerp high))
           (equal (logand low (* (expt 2 width) high)) 0))
  :hints (("Goal" :induct (symbols-halving-induction width low)
                  :in-theory (disable acl2::binary-logand floor expt))
          ("Subgoal *1/2"
           :use ((:instance symbols-power-of-two-step)
                 (:instance symbols-logand-split (x low) (y (* (expt 2 width) high)))
                 (:instance symbols-floor-two-for-natural (value low))
                 (:instance symbols-floor-of-decomposition
                            (q (* (expt 2 (1- width)) high)) (r 0) (divisor 2))
                 (:instance symbols-half-of-twice (x (* (expt 2 (1- width)) high))))
           :in-theory (disable symbols-floor-of-decomposition
                               acl2::binary-logand floor expt)
           :nonlinearp t)))

(defthm symbols-xor-with-width-mask
  (implies (and (natp width) (natp word) (< word (expt 2 width)))
           (equal (logxor word (1- (expt 2 width)))
                  (- (1- (expt 2 width)) word)))
  :hints (("Goal"
           :use ((:instance symbols-and-low-aligned-is-zero (low word) (high -1))
                 (:instance symbols-logand-commutes
                            (x (1- (expt 2 width))) (y (lognot word)))
                 (:instance symbols-logand-low-mask (x (lognot word)))
                 (:instance symbols-mod-translation (divisor (expt 2 width))
                            (x (lognot word)) (q 1))
                 (:instance symbols-mod-in-range
                            (divisor (expt 2 width))
                            (x (+ (expt 2 width) (lognot word)))))
           :in-theory (disable acl2::binary-logand floor mod expt
                               symbols-and-low-aligned-is-zero
                               symbols-logand-low-mask symbols-mod-in-range
                               symbols-mod-translation))))

(local
 (defthm symbols-sum-of-integers
   (implies (and (integerp x) (integerp y))
            (integerp (+ x y)))
   :rule-classes nil))

(local
 (defthm symbols-add-integer-keeps-integrality
   (implies (and (integerp offset) (rationalp value))
            (equal (integerp (+ offset value)) (integerp value)))
   :hints (("Goal"
            :use ((:instance symbols-sum-of-integers (x offset) (y value))
                  (:instance symbols-sum-of-integers (x (- offset)) (y (+ offset value))))))))

(local
 (defthm symbols-even-after-doubled-offset
   (implies (and (integerp offset) (integerp value))
            (equal (evenp (+ value (* 2 offset))) (evenp value)))))

(local
 (defthm symbols-floor-determined-by-bounds
   (implies (and (rationalp x) (rationalp divisor) (< 0 divisor) (integerp candidate)
                 (<= (* divisor candidate) x) (< x (* divisor (1+ candidate))))
            (equal (floor x divisor) candidate))
   :hints (("Goal"
            :use ((:instance symbols-floor-of-decomposition
                             (q candidate) (r (- x (* divisor candidate)))))
            :in-theory (disable floor symbols-floor-of-decomposition)
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm symbols-half-quotient-after-doubled-offset
   (implies (and (integerp offset) (integerp value))
            (equal (floor (+ value (* 2 offset)) 2)
                   (+ offset (floor value 2))))
   :hints (("Goal"
            :use ((:instance symbols-floor-determined-by-bounds
                             (x (+ value (* 2 offset))) (divisor 2)
                             (candidate (+ offset (floor value 2))))
                  (:instance symbols-floor-bounds (x value) (divisor 2)))
            :in-theory (disable floor)))))

(local
 (defun symbols-halving-pair (width left right)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       (cons left right)
     (symbols-halving-pair (1- width) (floor left 2) (floor right 2)))))

(defthm symbols-and-of-joined-fields
  (implies (and (natp width)
                (natp low-left) (< low-left (expt 2 width)) (integerp high-left)
                (natp low-right) (< low-right (expt 2 width)) (integerp high-right))
           (equal (logand (+ low-left (* (expt 2 width) high-left))
                          (+ low-right (* (expt 2 width) high-right)))
                  (+ (logand low-left low-right)
                     (* (expt 2 width) (logand high-left high-right)))))
  :hints (("Goal" :induct (symbols-halving-pair width low-left low-right)
                  :in-theory (disable floor expt acl2::binary-logand))
          ("Subgoal *1/2"
           :expand ((expt 2 width))
           :use ((:instance symbols-logand-split
                            (x (+ low-left (* (expt 2 width) high-left)))
                            (y (+ low-right (* (expt 2 width) high-right))))
                 (:instance symbols-logand-split (x low-left) (y low-right))
                 (:instance symbols-floor-two-for-natural (value low-left))
                 (:instance symbols-floor-two-for-natural (value low-right))
                 (:instance symbols-half-quotient-after-doubled-offset
                            (value low-left) (offset (* (expt 2 (1- width)) high-left)))
                 (:instance symbols-half-quotient-after-doubled-offset
                            (value low-right) (offset (* (expt 2 (1- width)) high-right)))
                 (:instance symbols-even-after-doubled-offset
                            (value low-left) (offset (* (expt 2 (1- width)) high-left)))
                 (:instance symbols-even-after-doubled-offset
                            (value low-right) (offset (* (expt 2 (1- width)) high-right))))
           :in-theory (disable floor expt acl2::binary-logand
                               symbols-half-quotient-after-doubled-offset
                               symbols-even-after-doubled-offset)
           :nonlinearp t)))

(local
 (defthm symbols-cancel-opposite-addends
   (implies (and (rationalp x) (rationalp y))
            (equal (+ x (- x) y) y))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-+
                             (acl2::x x) (acl2::y (- x)) (acl2::z y)))
            :in-theory (disable acl2::associativity-of-+)))))

(defthm symbols-or-of-low-and-aligned-fields
  (implies (and (natp width) (natp low) (< low (expt 2 width)) (integerp high))
           (equal (logior low (* (expt 2 width) high))
                  (+ low (* (expt 2 width) high))))
  :hints (("Goal"
           :use ((:instance symbols-and-of-joined-fields
                            (low-left (- (1- (expt 2 width)) low)) (high-left -1)
                            (low-right (1- (expt 2 width))) (high-right (- -1 high)))
                 (:instance symbols-logand-low-mask (x (- (1- (expt 2 width)) low)))
                 (:instance symbols-cancel-opposite-addends
                            (x (expt 2 width)) (y (- (* (expt 2 width) high))))
                 (:instance symbols-mod-in-range
                            (x (- (1- (expt 2 width)) low)) (divisor (expt 2 width))))
           :in-theory (disable expt mod floor acl2::binary-logand
                               symbols-and-of-joined-fields symbols-logand-low-mask
                               symbols-mod-in-range)
           :nonlinearp t)))

(defthm symbols-unsigned-keeps-low-field
  (implies (and (natp width) (natp low) (< low (expt 2 width)) (integerp high))
           (equal (boymoo-model::a64-unsigned width (+ low (* (expt 2 width) high)))
                  low))
  :hints (("Goal"
           :use ((:instance symbols-mod-of-decomposition (q high) (r low)
                            (divisor (expt 2 width))))
           :in-theory (disable mod floor expt symbols-mod-of-decomposition))))

(defthm symbols-mask-is-unsigned
  (implies (and (natp width) (integerp value))
           (equal (logand value (1- (expt 2 width)))
                  (boymoo-model::a64-unsigned width value)))
  :hints (("Goal"
           :use ((:instance symbols-logand-low-mask (x value)))
           :in-theory (disable mod expt acl2::binary-logand symbols-logand-low-mask)))
  :rule-classes nil)

(local
 (defthm symbols-fixed-negative-ash
   (and (equal (ash word -1) (floor (ifix word) 2))
        (equal (ash word -8) (floor (ifix word) 256))
        (equal (ash word -11) (floor (ifix word) 2048)))
   :hints (("Goal" :in-theory (enable ash floor)))))

(defthm symbols-fixed-right-shift-range
  (let ((quotient (floor word (expt 2 amount))))
    (implies (and (natp word) (< word (expt 2 64))
                  (member-equal amount '(1 8 11)))
             (and (natp quotient) (< quotient (expt 2 (- 64 amount))))))
  :hints (("Goal"
           :use ((:instance symbols-floor-bounds (x word) (divisor (expt 2 amount))))
           :in-theory (disable floor)))
  :rule-classes nil)

(defthm symbols-rotate-low-field-is-right-shift
  (implies (and (natp word) (< word (expt 2 64))
                (member-equal amount '(1 8 11)))
           (equal (boymoo-model::a64-unsigned
                   (- 64 amount) (boymoo-model::a64-ror 64 word amount))
                  (floor word (expt 2 amount))))
  :hints (("Goal"
           :use ((:instance symbols-fixed-right-shift-range)
                 (:instance symbols-or-of-low-and-aligned-fields
                            (width (- 64 amount)) (low (floor word (expt 2 amount)))
                            (high word))
                 (:instance symbols-unsigned-keeps-low-field
                            (width (- 64 amount)) (low (floor word (expt 2 amount)))
                            (high word)))
           :in-theory (e/d (boymoo-model::a64-ror)
                           (boymoo-model::a64-unsigned mod floor ash
                            acl2::binary-logior symbols-unsigned-as-mod
                            symbols-or-of-low-and-aligned-fields
                            symbols-unsigned-keeps-low-field)))))

(local
 (in-theory (disable symbols-unsigned-as-mod boymoo-model::a64-unsigned)))

(local
 (defthm symbols-byte-is-natural
   (natp (boymoo-model::a64-byte address memory))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-byte-is-bounded
   (< (boymoo-model::a64-byte address memory) 256)
   :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned)))
   :rule-classes :linear))

(local
 (defthm symbols-read-bytes-adds-next-byte
   (implies (posp count)
            (equal (boymoo-model::a64-read-bytes count address memory)
                   (+ (boymoo-model::a64-byte address memory)
                      (* 256 (boymoo-model::a64-read-bytes
                              (1- count) (1+ (ifix address)) memory)))))
   :hints (("Goal"
            :expand ((boymoo-model::a64-read-bytes count address memory))
            :use ((:instance symbols-or-of-low-and-aligned-fields
                             (width 8) (low (boymoo-model::a64-byte address memory))
                             (high (boymoo-model::a64-read-bytes
                                    (1- count) (1+ (ifix address)) memory))))
            :in-theory (disable boymoo-model::a64-byte boymoo-model::a64-read-bytes
                                acl2::binary-logior ash symbols-or-of-low-and-aligned-fields)))))

(local
 (defthm symbols-read-zero-bytes
   (equal (boymoo-model::a64-read-bytes 0 address memory) 0)))

(defthmd symbols-load-low-byte
  (implies (posp count)
           (equal (boymoo-model::a64-unsigned
                   8 (boymoo-model::a64-load count address machine))
                  (boymoo-model::a64-load 1 address machine)))
  :hints (("Goal"
           :use ((:instance symbols-unsigned-keeps-low-field
                            (width 8)
                            (low (boymoo-model::a64-byte address
                                                       (boymoo-model::a64-memory machine)))
                            (high (boymoo-model::a64-read-bytes
                                   (1- count) (1+ (ifix address))
                                   (boymoo-model::a64-memory machine)))))
           :in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-byte
                               (:definition boymoo-model::a64-read-bytes)
                               symbols-unsigned-keeps-low-field))))

(local
 (defthm symbols-read-bytes-width
   (let ((value (boymoo-model::a64-read-bytes count address memory)))
     (and (natp value) (< value (expt 2 (* 8 (nfix count))))))
   :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address memory)
                   :in-theory (disable (:definition boymoo-model::a64-read-bytes)
                                       boymoo-model::a64-byte expt))
           ("Subgoal *1/2"
            :use ((:instance symbols-powers-multiply (x 8) (y (* 8 (1- count))))
                  (:instance symbols-power-of-two (width (* 8 (1- count))))
                  (:instance symbols-integer-gap
                             (x (boymoo-model::a64-read-bytes
                                 (1- count) (1+ (ifix address)) memory))
                             (y (expt 2 (* 8 (1- count)))))
                  (:instance symbols-byte-is-bounded))
            :nonlinearp t)
           ("Subgoal *1/1" :expand ((boymoo-model::a64-read-bytes count address memory))))
   :rule-classes nil))

(defthm symbols-load-width
  (let ((value (boymoo-model::a64-load count address machine)))
    (and (natp value) (< value (expt 2 (* 8 (nfix count))))))
  :hints (("Goal"
           :use ((:instance symbols-read-bytes-width
                            (memory (boymoo-model::a64-memory machine))))
           :in-theory (disable boymoo-model::a64-read-bytes expt)))
  :rule-classes nil)

(defthmd symbols-word-load-fits
  (equal (boymoo-model::a64-unsigned 64 (boymoo-model::a64-load 8 address machine))
         (boymoo-model::a64-load 8 address machine))
  :hints (("Goal"
           :use ((:instance symbols-load-width (count 8)))
           :in-theory (disable boymoo-model::a64-load boymoo-model::a64-unsigned))))

(in-theory (disable symbols-unsigned-as-mod))
