(in-package "BOYMOO-PROOFS")

(include-book "execution")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash logbitp acl2::binary-logand
                           acl2::binary-logior acl2::binary-logxor
                           boymoo-model::a64-unsigned
                           boymoo-model::a64-signed)))

(local
 (defthm sequence-quotient-bounds
   (implies (and (natp dividend) (posp divisor))
            (let ((product (* divisor (nonnegative-integer-quotient dividend divisor))))
              (and (<= product dividend) (< dividend (+ divisor product)))))
   :hints (("Goal" :induct (nonnegative-integer-quotient dividend divisor)))
   :rule-classes nil))

(local
 (defthm sequence-cancel-reciprocal
   (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp value))
            (equal (* divisor (* (/ divisor) value)) value))
   :hints (("Goal" :in-theory (disable associativity-of-*)
                   :use ((:instance associativity-of-*
                                    (acl2::x divisor) (acl2::y (/ divisor))
                                    (acl2::z value)))))
   :rule-classes nil))

(local
 (defthm sequence-rational-numerator
   (implies (rationalp value)
            (equal (* value (denominator value)) (numerator value)))
   :hints (("Goal" :use ((:instance acl2::rational-implies1 (acl2::x value))
                        (:instance acl2::rational-implies2 (acl2::x value))
                        (:instance sequence-cancel-reciprocal
                                   (divisor (denominator value))
                                   (value (numerator value))))
                   :in-theory (disable acl2::rational-implies2)))
   :rule-classes nil))

(local
 (defthm sequence-floor-unit-bounds
   (implies (rationalp value)
            (and (<= (floor value 1) value)
                 (< value (+ 1 (floor value 1)))))
   :hints (("Goal"
            :in-theory (enable floor)
            :use ((:instance sequence-rational-numerator)
                  (:instance sequence-quotient-bounds
                             (dividend (numerator value)) (divisor (denominator value)))
                  (:instance sequence-quotient-bounds
                             (dividend (- (numerator value)))
                             (divisor (denominator value))))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm sequence-multiply-negation
   (equal (* scale (- value)) (- (* scale value)))
   :hints (("Goal" :in-theory (disable distributivity)
                   :use ((:instance distributivity (acl2::x scale)
                                    (acl2::y value) (acl2::z (- value))))))))

(local
 (defthm sequence-multiply-order
   (implies (and (rationalp scale) (< 0 scale)
                 (rationalp left) (rationalp right))
            (equal (< (* scale left) (* scale right))
                   (< left right)))
   :hints (("Goal" :cases ((equal left right))
                   :use ((:instance acl2::positive
                                    (acl2::x scale) (acl2::y (- right left)))
                        (:instance acl2::positive
                                    (acl2::x scale) (acl2::y (- left right))))))
   :rule-classes nil))

(defthm sequence-floor-bounds
  (implies (and (rationalp value) (posp divisor))
           (let ((product (* divisor (floor value divisor))))
             (and (<= product value) (< value (+ divisor product)))))
  :hints (("Goal" :in-theory (e/d (floor) (associativity-of-*))
                  :use ((:instance sequence-floor-unit-bounds
                                   (value (* value (/ divisor))))
                        (:instance sequence-multiply-order
                                   (scale divisor)
                                   (left (* value (/ divisor)))
                                   (right (floor value divisor)))
                        (:instance sequence-multiply-order
                                   (scale divisor)
                                   (left (* value (/ divisor)))
                                   (right (+ 1 (floor value divisor))))
                        sequence-cancel-reciprocal)
                  :nonlinearp t))
  :rule-classes nil)

(local
 (defthm sequence-ceiling-unit-upper
   (implies (and (rationalp value) (<= 0 value))
            (<= value (ceiling value 1)))
   :hints (("Goal"
            :use (sequence-rational-numerator
                  (:instance sequence-quotient-bounds
                             (dividend (numerator value)) (divisor (denominator value))))
            :nonlinearp t))
   :rule-classes nil))

(defthm sequence-align-up-covers-address
  (implies (and (natp address) (posp alignment))
           (<= address (proof-align-up address alignment)))
  :hints (("Goal"
           :in-theory (disable associativity-of-*)
           :use ((:instance sequence-ceiling-unit-upper (value (* address (/ alignment))))
                 (:instance sequence-cancel-reciprocal (divisor alignment) (value address))
                 (:instance sequence-multiply-order
                            (scale alignment) (left (ceiling address alignment))
                            (right (* address (/ alignment)))))))
  :rule-classes nil)

(local
 (defthm sequence-ceiling-unit-at-most-one-more
   (implies (and (rationalp value) (<= 0 value))
            (<= (ceiling value 1) (+ value 1)))
   :hints (("Goal"
            :use (sequence-rational-numerator
                  (:instance sequence-quotient-bounds
                             (dividend (numerator value)) (divisor (denominator value))))
            :nonlinearp t))
   :rule-classes nil))

(defthm sequence-align-up-upper-bound
  (implies (and (natp address) (posp alignment))
           (<= (proof-align-up address alignment) (+ address alignment)))
  :hints (("Goal"
           :in-theory (disable associativity-of-*)
           :use ((:instance sequence-ceiling-unit-at-most-one-more
                            (value (* address (/ alignment))))
                 (:instance sequence-cancel-reciprocal (divisor alignment) (value address))
                 (:instance sequence-multiply-order
                            (scale alignment)
                            (left (+ (* address (/ alignment)) 1))
                            (right (ceiling address alignment))))))
  :rule-classes nil)

(defthm sequence-floor-unique
  (implies (and (rationalp value) (posp divisor) (integerp quotient)
                (<= (* divisor quotient) value)
                (< value (* divisor (1+ quotient))))
           (equal (floor value divisor) quotient))
  :hints (("Goal"
           :use (sequence-floor-bounds
                 (:instance sequence-multiply-order
                            (scale divisor)
                            (left quotient)
                            (right (+ 1 (floor value divisor))))
                 (:instance sequence-multiply-order
                            (scale divisor)
                            (left (floor value divisor))
                            (right (+ 1 quotient))))
           :nonlinearp t))
  :rule-classes nil)

(defthm sequence-power-of-two-positive
  (implies (natp count)
           (posp (expt 2 count)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (expt 2 count))))

(defthm sequence-ash-left
  (implies (and (natp count) (integerp value))
           (equal (ash value count) (* (expt 2 count) value)))
  :hints (("Goal"
           :in-theory (enable ash)
           :use ((:instance sequence-floor-unique
                            (value (* (expt 2 count) value)) (divisor 1)
                            (quotient (* (expt 2 count) value)))))))

(local
 (defthm sequence-commute-factors
   (equal (* left middle right) (* middle left right))
   :hints (("Goal" :in-theory (disable associativity-of-*)
                   :use ((:instance associativity-of-* (acl2::x left)
                                    (acl2::y middle) (acl2::z right))
                         (:instance associativity-of-* (acl2::x middle)
                                    (acl2::y left) (acl2::z right)))))))

(local
 (defthm sequence-opposite-powers
   (implies (natp count)
            (equal (* (expt 2 count) (expt 2 (- count))) 1))
   :hints (("Goal" :induct (expt 2 count))
           ("Subgoal *1/3"
            :expand ((expt 2 count) (expt 2 (- count)))))))

(local
 (defthm sequence-negative-power-of-two
   (implies (natp count)
            (equal (expt 2 (- count)) (/ (expt 2 count))))
   :hints (("Goal" :in-theory (disable expt)
                   :use (sequence-opposite-powers
                         (:instance sequence-multiply-order
                                    (scale (expt 2 count))
                                    (left (expt 2 (- count)))
                                    (right (/ (expt 2 count))))
                         (:instance sequence-multiply-order
                                    (scale (expt 2 count))
                                    (right (expt 2 (- count)))
                                    (left (/ (expt 2 count)))))))))

(defthm sequence-ash-right
  (implies (and (natp count) (integerp value))
           (equal (ash value (- count)) (floor value (expt 2 count))))
  :hints (("Goal" :in-theory (enable ash floor))))

(defthm sequence-mod-bounds
  (implies (and (integerp value) (posp divisor))
           (and (integerp (mod value divisor))
                (<= 0 (mod value divisor))
                (< (mod value divisor) divisor)))
  :hints (("Goal" :in-theory (enable mod)
                  :use sequence-floor-bounds))
  :rule-classes nil)

(defthm sequence-mod-natp
  (implies (and (integerp value) (posp divisor))
           (natp (mod value divisor)))
  :hints (("Goal" :use sequence-mod-bounds))
  :rule-classes :type-prescription)

(defthm sequence-mod-upper-bound
  (implies (and (integerp value) (posp divisor))
           (< (mod value divisor) divisor))
  :hints (("Goal" :use sequence-mod-bounds))
  :rule-classes :linear)

(defthm sequence-mod-of-bounded
  (implies (and (natp value) (posp divisor) (< value divisor))
           (equal (mod value divisor) value))
  :hints (("Goal" :in-theory (enable mod)
                  :use ((:instance sequence-floor-unique (quotient 0))))))

(defthm sequence-floor-add-multiple
  (implies (and (integerp value) (posp divisor) (integerp multiple))
           (equal (floor (+ value (* divisor multiple)) divisor)
                  (+ multiple (floor value divisor))))
  :hints (("Goal" :use (sequence-floor-bounds
                        (:instance sequence-floor-unique
                                   (value (+ value (* divisor multiple)))
                                   (quotient (+ multiple (floor value divisor)))))
                  :nonlinearp t)))

(defthm sequence-mod-add-multiple
  (implies (and (integerp value) (posp divisor) (integerp multiple))
           (equal (mod (+ value (* divisor multiple)) divisor)
                  (mod value divisor)))
  :hints (("Goal" :in-theory (enable mod))))

(local
 (defthm sequence-floor-half-even
   (implies (and (integerp value) (evenp value))
            (equal (floor value 2) (* 1/2 value)))
   :hints (("Goal" :use ((:instance sequence-floor-unique
                                    (divisor 2) (quotient (* 1/2 value))))))))

(local
 (defthm sequence-floor-half-odd
   (implies (and (integerp value) (oddp value))
            (equal (* 2 (floor value 2)) (1- value)))
   :hints (("Goal" :use ((:instance sequence-floor-bounds (divisor 2)))
                   :cases ((equal value (* 2 (floor value 2)))))
           ("Subgoal 1"
            :in-theory (disable associativity-of-*)
            :use ((:instance associativity-of-* (acl2::x 1/2) (acl2::y 2)
                             (acl2::z (floor value 2))))))))

(defthm sequence-mod-two
  (implies (integerp value)
           (equal (mod value 2) (if (oddp value) 1 0)))
  :hints (("Goal" :in-theory (enable mod))))

(local
 (defthm sequence-floor-of-twice-minus-one
   (implies (integerp value)
            (equal (floor (+ -1 (* 2 value)) 2) (1- value)))
   :hints (("Goal" :use ((:instance sequence-floor-unique
                                    (value (+ -1 (* 2 value)))
                                    (divisor 2) (quotient (1- value))))))))

(local
 (defthm sequence-integer-sum
   (implies (and (integerp left) (integerp right))
            (integerp (+ left right)))
   :rule-classes nil))

(local
 (defthm sequence-odd-of-twice-minus-one
   (implies (integerp value) (oddp (+ -1 (* 2 value))))
   :hints (("Goal" :use ((:instance sequence-cancel-reciprocal (divisor 1/2))
                         (:instance sequence-integer-sum
                                    (left (- value)) (right (+ -1/2 value))))
                   :in-theory (disable associativity-of-*)))))

(local
 (defthm sequence-logand-ones-step
   (implies (and (integerp value) (natp bits))
            (equal (logand value (1- (expt 2 (1+ bits))))
                   (+ (if (oddp value) 1 0)
                      (* 2 (logand (floor value 2) (1- (expt 2 bits)))))))
   :hints (("Goal" :expand ((expt 2 (1+ bits))
                            (logand value (1- (expt 2 (1+ bits)))))
                   :in-theory (e/d (acl2::binary-logand)
                                   (sequence-odd-of-twice-minus-one))
                   :use ((:instance sequence-odd-of-twice-minus-one
                                    (value (expt 2 bits))))
                   :cases ((equal value -1) (equal value 0))))))

(local
 (defthm sequence-floor-of-floor-half
   (implies (and (integerp value) (posp divisor))
            (equal (floor (floor value 2) divisor)
                   (floor value (* 2 divisor))))
   :hints (("Goal" :use ((:instance sequence-floor-bounds (divisor 2))
                         (:instance sequence-floor-bounds (value (floor value 2)))
                         (:instance sequence-floor-unique
                                    (divisor (* 2 divisor))
                                    (quotient (floor (floor value 2) divisor))))
                   :nonlinearp t))))

(local
 (defthm sequence-mod-double-step
   (implies (and (integerp value) (posp divisor))
            (equal (mod value (* 2 divisor))
                   (+ (mod value 2) (* 2 (mod (floor value 2) divisor)))))
   :hints (("Goal" :in-theory (e/d (mod) (sequence-mod-two))
                   :use sequence-floor-of-floor-half))))

(local (in-theory (disable sequence-mod-double-step)))

(local
 (defun sequence-mask-induction (bits value)
   (declare (xargs :measure (nfix bits)))
   (if (zp bits)
       value
     (sequence-mask-induction (1- bits) (floor value 2)))))

(local
 (defthm sequence-logand-ones-as-mod
   (implies (and (integerp value) (natp bits))
            (equal (logand value (1- (expt 2 bits)))
                   (mod value (expt 2 bits))))
   :hints (("Goal" :induct (sequence-mask-induction bits value))
           ("Subgoal *1/2" :use ((:instance sequence-logand-ones-step (bits (1- bits)))
                                  (:instance sequence-mod-double-step
                                             (divisor (expt 2 (1- bits)))))
                            :in-theory (disable sequence-logand-ones-step
                                                sequence-mod-double-step))
           ("Subgoal *1/1" :in-theory (enable acl2::binary-logand mod)
                            :use ((:instance sequence-floor-unique
                                             (divisor 1) (quotient value)))))))

(defthm sequence-a64-unsigned-as-mod
  (equal (boymoo-model::a64-unsigned bits value)
         (mod (ifix value) (expt 2 (nfix bits))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned))))

(defthm sequence-unsigned-natp
  (natp (boymoo-model::a64-unsigned width value))
  :rule-classes :type-prescription)

(defthm sequence-unsigned-upper-bound
  (< (boymoo-model::a64-unsigned width value) (expt 2 (nfix width)))
  :rule-classes :linear)

(defthm sequence-unsigned-of-bounded
  (implies (unsigned-byte-p width value)
           (equal (boymoo-model::a64-unsigned width value) value)))

(defthm sequence-unsigned-of-zero
  (equal (boymoo-model::a64-unsigned width 0) 0))

(defthm sequence-power-of-two-monotonic
  (implies (and (natp small) (natp large) (<= small large))
           (<= (expt 2 small) (expt 2 large)))
  :hints (("Goal" :induct (expt 2 large)))
  :rule-classes nil)

(defthm sequence-unsigned-of-narrow-unsigned
  (implies (and (natp small) (natp large) (<= small large))
           (equal (boymoo-model::a64-unsigned large
                                              (boymoo-model::a64-unsigned small value))
                  (boymoo-model::a64-unsigned small value)))
  :hints (("Goal" :in-theory (disable sequence-a64-unsigned-as-mod)
                  :use (sequence-power-of-two-monotonic
                        (:instance sequence-unsigned-upper-bound (width small))))))

(defthm sequence-floor-half-decomposition
  (implies (integerp value)
           (equal (+ (* 2 (floor value 2)) (if (oddp value) 1 0)) value))
  :rule-classes nil)

(local
 (defthm sequence-logand-zero
   (and (equal (logand value 0) 0)
        (equal (logand 0 value) 0))
   :hints (("Goal" :in-theory (enable acl2::binary-logand)))))

(local
 (defthm sequence-logand-minus-one
   (implies (integerp value)
            (and (equal (logand value -1) value)
                 (equal (logand -1 value) value)))
   :hints (("Goal" :in-theory (enable acl2::binary-logand)))))

(local
 (defthm sequence-logand-halves
   (implies (and (integerp left) (integerp right))
            (equal (logand left right)
                   (+ (* 2 (logand (floor left 2) (floor right 2)))
                      (if (and (oddp left) (oddp right)) 1 0))))
   :hints (("Goal" :expand ((logand left right))
                   :use ((:instance sequence-floor-half-decomposition (value left))
                         (:instance sequence-floor-half-decomposition (value right)))))))

(local (in-theory (disable sequence-logand-halves)))

(local
 (defthm sequence-floor-of-twice-plus-bit
   (implies (and (integerp value) (integerp bit) (<= 0 bit) (< bit 2))
            (equal (floor (+ bit (* 2 value)) 2) value))
   :hints (("Goal" :use ((:instance sequence-floor-unique
                                    (value (+ bit (* 2 value)))
                                    (divisor 2) (quotient value)))))))

(local
 (defthm sequence-odd-of-twice-plus-bit
   (implies (and (integerp value) (integerp bit) (<= 0 bit) (< bit 2))
            (equal (oddp (+ bit (* 2 value))) (equal bit 1)))
   :hints (("Goal" :use ((:instance sequence-floor-half-decomposition
                                    (value (+ bit (* 2 value)))))))))

(local
 (defthm sequence-floor-of-logand
   (implies (and (integerp left) (integerp right))
            (equal (floor (logand left right) 2)
                   (logand (floor left 2) (floor right 2))))
   :hints (("Goal" :in-theory (disable sequence-logand-halves)
                   :use (sequence-logand-halves
                         (:instance sequence-floor-of-twice-plus-bit
                                    (value (logand (floor left 2) (floor right 2)))
                                    (bit (if (and (oddp left) (oddp right)) 1 0))))))))

(defthm sequence-odd-of-logand
  (implies (and (integerp left) (integerp right))
           (equal (oddp (logand left right))
                  (and (oddp left) (oddp right))))
  :hints (("Goal" :in-theory (disable sequence-logand-halves sequence-odd-of-twice-plus-bit)
                  :use (sequence-logand-halves
                        (:instance sequence-odd-of-twice-plus-bit
                                   (value (logand (floor left 2) (floor right 2)))
                                   (bit (if (and (oddp left) (oddp right)) 1 0)))))))

(local
 (defthm sequence-floor-of-lognot
   (implies (integerp value)
            (equal (floor (lognot value) 2) (lognot (floor value 2))))
   :hints (("Goal" :use ((:instance sequence-floor-unique
                                    (value (lognot value))
                                    (divisor 2) (quotient (lognot (floor value 2))))
                         (:instance sequence-floor-bounds (divisor 2)))))))

(local
 (defthm sequence-odd-of-lognot
   (implies (integerp value)
            (equal (oddp (lognot value)) (not (oddp value))))
   :hints (("Goal" :use (sequence-floor-of-lognot sequence-floor-half-decomposition
                         (:instance sequence-floor-half-decomposition
                                    (value (lognot value))))))))

(local
 (defthm sequence-floor-of-logior
   (implies (and (integerp left) (integerp right))
            (equal (floor (logior left right) 2)
                   (logior (floor left 2) (floor right 2))))
   :hints (("Goal" :in-theory (e/d (acl2::binary-logior) (lognot))))))

(local
 (defthm sequence-odd-of-logior
   (implies (and (integerp left) (integerp right))
            (equal (oddp (logior left right))
                   (or (oddp left) (oddp right))))
   :hints (("Goal" :in-theory (e/d (acl2::binary-logior) (lognot))))))

(local
 (defthm sequence-logior-halves
   (implies (and (integerp left) (integerp right))
            (equal (logior left right)
                   (+ (* 2 (logior (floor left 2) (floor right 2)))
                      (if (or (oddp left) (oddp right)) 1 0))))
   :hints (("Goal" :use ((:instance sequence-floor-half-decomposition
                                    (value (logior left right))))))))

(local (in-theory (disable sequence-logior-halves)))

(local
 (defthm sequence-floor-of-logxor
   (implies (and (integerp left) (integerp right))
            (equal (floor (logxor left right) 2)
                   (logxor (floor left 2) (floor right 2))))
   :hints (("Goal" :in-theory (e/d (acl2::binary-logxor acl2::binary-logeqv logorc1)
                                   (lognot))))))

(local
 (defthm sequence-odd-of-logxor
   (implies (and (integerp left) (integerp right))
            (equal (oddp (logxor left right))
                   (not (equal (oddp left) (oddp right)))))
   :hints (("Goal" :in-theory (e/d (acl2::binary-logxor acl2::binary-logeqv logorc1)
                                   (lognot))))))

(local
 (defthm sequence-logxor-halves
   (implies (and (integerp left) (integerp right))
            (equal (logxor left right)
                   (+ (* 2 (logxor (floor left 2) (floor right 2)))
                      (if (equal (oddp left) (oddp right)) 0 1))))
   :hints (("Goal" :use ((:instance sequence-floor-half-decomposition
                                    (value (logxor left right))))))))

(local (in-theory (disable sequence-logxor-halves)))

(local
 (defthm sequence-half-of-unsigned
   (implies (and (natp bits) (unsigned-byte-p (1+ bits) value))
            (unsigned-byte-p bits (floor value 2)))
   :hints (("Goal" :use ((:instance sequence-floor-bounds (divisor 2)))
                   :expand ((expt 2 (1+ bits)))))))

(local
 (defthm sequence-negative-double-floor
   (implies (integerp value)
            (equal (* -2 (floor value 2))
                   (+ (- value) (if (oddp value) 1 0))))
   :hints (("Goal" :in-theory (disable sequence-floor-half-even)
                   :use sequence-floor-half-decomposition))))

(defthm sequence-logxor-ones
  (implies (unsigned-byte-p bits value)
           (equal (logxor value (1- (expt 2 bits)))
                  (- (1- (expt 2 bits)) value)))
  :hints (("Goal" :induct (sequence-mask-induction bits value))
          ("Subgoal *1/2"
           :use (sequence-floor-half-decomposition
                 (:instance sequence-logxor-halves
                            (left value) (right (1- (expt 2 bits))))
                 (:instance sequence-odd-of-twice-minus-one
                            (value (expt 2 (1- bits))))
                 (:instance sequence-half-of-unsigned (bits (1- bits))))
           :in-theory (disable sequence-odd-of-twice-minus-one sequence-floor-half-even)
           :expand ((expt 2 bits)))))

(defthm sequence-powers-add
  (implies (and (natp left) (natp right))
           (equal (expt 2 (+ left right))
                  (* (expt 2 left) (expt 2 right))))
  :hints (("Goal" :induct (expt 2 left))
          ("Subgoal *1/3" :expand ((expt 2 (+ left right)))))
  :rule-classes nil)

(local
 (defthm sequence-floor-of-scaled-by-two
   (implies (integerp value)
            (equal (floor (* 2 value) 2) value))
   :hints (("Goal" :use ((:instance sequence-floor-unique
                                    (value (* 2 value)) (divisor 2) (quotient value)))))))

(local
 (defthm sequence-odd-of-scaled-by-two
   (implies (integerp value)
            (not (oddp (* 2 value))))
   :hints (("Goal" :use ((:instance sequence-cancel-reciprocal (divisor 1/2)))
                   :in-theory (disable associativity-of-*)))))

(local
 (defthm sequence-floor-of-aligned
   (implies (and (posp bits) (integerp value))
            (equal (floor (* (expt 2 bits) value) 2)
                   (* (expt 2 (1- bits)) value)))
   :hints (("Goal" :use ((:instance sequence-floor-of-scaled-by-two
                                    (value (* (expt 2 (1- bits)) value))))
                   :expand ((expt 2 bits))))))

(local
 (defthm sequence-odd-of-aligned
   (implies (and (posp bits) (integerp value))
            (not (oddp (* (expt 2 bits) value))))
   :hints (("Goal" :use ((:instance sequence-odd-of-scaled-by-two
                                    (value (* (expt 2 (1- bits)) value))))
                   :in-theory (disable sequence-odd-of-scaled-by-two)
                   :expand ((expt 2 bits))))))

(local
 (defthm sequence-logior-zero
   (implies (integerp value)
            (and (equal (logior 0 value) value)
                 (equal (logior value 0) value)))
   :hints (("Goal" :in-theory (enable acl2::binary-logior)))))

(defthm sequence-logior-of-aligned-and-short
  (implies (and (unsigned-byte-p bits low) (integerp high))
           (equal (logior low (* (expt 2 bits) high))
                  (+ low (* (expt 2 bits) high))))
  :hints (("Goal" :induct (sequence-mask-induction bits low))
          ("Subgoal *1/2"
           :use ((:instance sequence-logior-halves
                            (left low) (right (* (expt 2 bits) high)))
                 (:instance sequence-floor-half-decomposition (value low))
                 (:instance sequence-floor-of-aligned (value high))
                 (:instance sequence-odd-of-aligned (value high))
                 (:instance sequence-half-of-unsigned (bits (1- bits)) (value low)))
           :in-theory (disable sequence-odd-of-aligned)
           :expand ((expt 2 bits)))))

(local
 (defthm sequence-floor-of-sum-with-even
   (implies (and (integerp low) (integerp high))
            (equal (floor (+ low (* 2 high)) 2)
                   (+ (floor low 2) high)))))

(local
 (defthm sequence-odd-of-sum-with-even
   (implies (and (integerp low) (integerp high))
            (equal (oddp (+ low (* 2 high))) (oddp low)))
   :hints (("Goal" :use ((:instance sequence-floor-half-decomposition (value low))
                         (:instance sequence-floor-half-decomposition
                                    (value (+ low (* 2 high)))))))))

(defthm sequence-logand-of-shifted-mask
  (implies (and (unsigned-byte-p bits low) (integerp high) (integerp mask))
           (equal (logand (+ low (* (expt 2 bits) high)) (* (expt 2 bits) mask))
                  (* (expt 2 bits) (logand high mask))))
  :hints (("Goal" :induct (sequence-mask-induction bits low))
          ("Subgoal *1/2"
           :use ((:instance sequence-logand-halves
                            (left (+ low (* (expt 2 bits) high)))
                            (right (* (expt 2 bits) mask)))
                 (:instance sequence-floor-add-multiple
                            (value low) (divisor 2)
                            (multiple (* (expt 2 (1- bits)) high)))
                 (:instance sequence-floor-of-aligned (value mask))
                 (:instance sequence-odd-of-aligned (value mask))
                 (:instance sequence-half-of-unsigned (bits (1- bits)) (value low)))
           :in-theory (disable sequence-odd-of-aligned)
           :expand ((expt 2 bits)))))

(defthm sequence-logand-mask
  (implies (and (natp bits) (integerp value))
           (equal (logand value (1- (expt 2 bits)))
                  (boymoo-model::a64-unsigned bits value)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned))))

(local
 (defthm sequence-floor-of-scaled-sum
   (implies (and (posp scale) (posp modulus) (integerp high)
                 (natp low) (< low scale))
            (equal (floor (+ low (* scale high)) (* scale modulus))
                   (floor high modulus)))
   :hints (("Goal"
            :use ((:instance sequence-floor-bounds (value high) (divisor modulus))
                  (:instance sequence-floor-unique
                             (value (+ low (* scale high)))
                             (divisor (* scale modulus))
                             (quotient (floor high modulus)))
                  (:instance sequence-multiply-order
                             (left high) (right (* modulus (floor high modulus))))
                  (:instance sequence-multiply-order
                             (left (* modulus (+ 1 (floor high modulus))))
                             (right (+ 1 high))))
            :nonlinearp t))))

(defthm sequence-mod-of-scaled-sum
  (implies (and (posp scale) (posp modulus) (integerp high)
                (natp low) (< low scale))
           (equal (mod (+ low (* scale high)) (* scale modulus))
                  (+ low (* scale (mod high modulus)))))
  :hints (("Goal" :in-theory (e/d (mod) (sequence-floor-of-scaled-sum))
                  :use sequence-floor-of-scaled-sum)))

(defthm sequence-floor-of-unsigned
  (implies (and (natp dropped) (natp kept)
                (unsigned-byte-p (+ dropped kept) value))
           (unsigned-byte-p kept (floor value (expt 2 dropped))))
  :hints (("Goal"
           :use ((:instance sequence-floor-bounds (divisor (expt 2 dropped)))
                 (:instance sequence-powers-add (left dropped) (right kept))
                 (:instance sequence-multiply-order
                            (scale (expt 2 dropped))
                            (left (floor value (expt 2 dropped)))
                            (right (expt 2 kept))))
           :nonlinearp t))
  :rule-classes nil)

(defthm sequence-unsigned-of-difference
  (implies (and (unsigned-byte-p bits left) (unsigned-byte-p bits right))
           (equal (boymoo-model::a64-unsigned bits (- left right))
                  (if (< left right) (+ (expt 2 bits) (- left right)) (- left right))))
  :hints (("Goal"
           :cases ((< left right))
           :use ((:instance sequence-mod-add-multiple
                            (value (- left right)) (divisor (expt 2 bits)) (multiple 1))))))

(defthm sequence-sign-bit
  (implies (and (natp bit) (natp value) (< value (* 2 (expt 2 bit))))
           (equal (logbitp bit value) (<= (expt 2 bit) value)))
  :hints (("Goal"
           :cases ((< value (expt 2 bit)))
           :in-theory (enable logbitp)
           :use ((:instance sequence-floor-unique (divisor (expt 2 bit)) (quotient 0))
                 (:instance sequence-floor-unique (divisor (expt 2 bit)) (quotient 1))))))

(local
 (defthm sequence-sum-of-opposites
   (equal (+ value (- value) rest) (fix rest))
   :hints (("Goal" :in-theory (disable associativity-of-+)
                   :use ((:instance associativity-of-+
                                    (acl2::x value) (acl2::y (- value))
                                    (acl2::z rest)))))))

(defthm sequence-ror
  (implies (and (posp width) (natp rotation) (< rotation width)
                (unsigned-byte-p width value))
           (let* ((right (expt 2 rotation))
                  (left (expt 2 (- width rotation)))
                  (low (floor value right)))
             (equal (boymoo-model::a64-ror width value rotation)
                    (+ low (* left (mod value right))))))
  :hints (("Goal"
           :in-theory (disable sequence-logior-of-aligned-and-short
                               sequence-mod-of-scaled-sum
                               sequence-power-of-two-positive)
           :do-not-induct t
           :use ((:instance sequence-power-of-two-positive (count (- width rotation)))
                 (:instance sequence-power-of-two-positive (count rotation))
                 (:instance sequence-powers-add (left (- width rotation)) (right rotation))
                 (:instance sequence-floor-of-unsigned
                            (dropped rotation) (kept (- width rotation)))
                 (:instance sequence-logior-of-aligned-and-short
                            (low (floor value (expt 2 rotation)))
                            (high value) (bits (- width rotation)))
                 (:instance sequence-mod-of-scaled-sum
                            (low (floor value (expt 2 rotation))) (high value)
                            (scale (expt 2 (- width rotation)))
                            (modulus (expt 2 rotation)))))))

(defthm sequence-ror-bits
  (implies (natp width)
           (unsigned-byte-p width (boymoo-model::a64-ror width value rotation)))
  :hints (("Goal" :in-theory (disable sequence-ror))))

(defthm sequence-low-bits-of-rotated-word
  (implies (and (unsigned-byte-p 64 value) (natp rotation) (< rotation 64))
           (equal (boymoo-model::a64-unsigned
                   (- 64 rotation) (boymoo-model::a64-ror 64 value rotation))
                  (floor value (expt 2 rotation))))
  :hints (("Goal"
           :in-theory (disable sequence-ror boymoo-model::a64-ror)
           :use ((:instance sequence-ror (width 64))
                 (:instance sequence-power-of-two-positive (count (- 64 rotation)))
                 (:instance sequence-floor-of-unsigned
                            (dropped rotation) (kept (- 64 rotation)))
                 (:instance sequence-mod-add-multiple
                            (value (floor value (expt 2 rotation)))
                            (divisor (expt 2 (- 64 rotation)))
                            (multiple (mod value (expt 2 rotation)))))))
  :rule-classes nil)

(local
 (defthm sequence-double-negation
   (implies (rationalp value)
            (equal (- (- value)) value))
   :hints (("Goal" :use ((:instance inverse-of-+ (acl2::x (- value))))))))

(defthm sequence-high-bits-of-rotated-word
  (implies (and (unsigned-byte-p 64 value) (posp shift) (< shift 64)
                (unsigned-byte-p (- 64 shift) value))
           (let ((left (expt 2 shift))
                 (right (expt 2 (- 64 shift))))
             (equal (logand (boymoo-model::a64-ror 64 value (- 64 shift))
                            (* left (1- right)))
                    (* left value))))
  :hints (("Goal"
           :in-theory (disable sequence-ror boymoo-model::a64-ror
                               sequence-logand-of-shifted-mask)
           :do-not-induct t
           :use ((:instance sequence-ror (width 64) (rotation (- 64 shift)))
                 (:instance sequence-power-of-two-positive (count (- 64 shift)))
                 (:instance sequence-floor-of-unsigned
                            (dropped (- 64 shift)) (kept shift))
                 (:instance sequence-logand-of-shifted-mask
                            (bits shift) (low (floor value (expt 2 (- 64 shift))))
                            (high value) (mask (1- (expt 2 (- 64 shift))))))))
  :rule-classes nil)

(local
 (defthm sequence-mod-sum-with-reduced-addend
   (implies (and (posp divisor) (integerp left) (integerp right))
            (equal (mod (+ left (mod right divisor)) divisor)
                   (mod (+ left right) divisor)))
   :hints (("Goal"
            :in-theory (e/d (mod) (sequence-mod-add-multiple))
            :use ((:instance sequence-mod-add-multiple
                             (value (+ left (mod right divisor)))
                             (multiple (floor right divisor))))))))

(defthm sequence-wrap-sum-with-reduced-addend
  (implies (and (integerp left) (integerp right))
           (equal (boymoo-model::a64-unsigned
                   64 (+ left (boymoo-model::a64-unsigned 64 right)))
                  (boymoo-model::a64-unsigned 64 (+ left right))))
  :hints (("Goal" :in-theory (disable sequence-mod-sum-with-reduced-addend
                                      sequence-mod-of-bounded sequence-mod-of-scaled-sum
                                      sequence-mod-upper-bound)
                  :use ((:instance sequence-mod-sum-with-reduced-addend
                                   (divisor (expt 2 64)))))))

(local
 (defthm sequence-odd-of-sum-with-eight-multiple
   (implies (and (integerp value) (integerp multiple))
            (equal (oddp (+ value (* 8 multiple))) (oddp value)))
   :hints (("Goal" :in-theory (disable oddp evenp associativity-of-*
                                      sequence-odd-of-sum-with-even)
                   :use ((:instance sequence-odd-of-sum-with-even
                                    (low value) (high (* 4 multiple)))
                         (:instance associativity-of-*
                                    (acl2::x 2) (acl2::y 4) (acl2::z multiple)))))))

(defthm sequence-word-parity-of-tag
  (implies (integerp word)
           (equal (oddp (boymoo-model::a64-unsigned 3 word)) (oddp word)))
  :hints (("Goal" :in-theory (e/d (mod) (oddp evenp
                                         sequence-odd-of-sum-with-eight-multiple))
                  :use ((:instance sequence-odd-of-sum-with-eight-multiple
                                   (value word) (multiple (- (floor word 8))))))))

(defthm sequence-unsigned-one-is-parity
  (implies (integerp value)
           (equal (boymoo-model::a64-unsigned 1 value)
                  (if (oddp value) 1 0)))
  :hints (("Goal" :in-theory (e/d (sequence-a64-unsigned-as-mod mod) (oddp evenp))
                  :use sequence-floor-half-decomposition)))

(defthm sequence-word-reduction-keeps-parity
  (implies (integerp value)
           (equal (oddp (boymoo-model::a64-unsigned 64 value)) (oddp value)))
  :hints (("Goal"
           :in-theory (e/d (sequence-a64-unsigned-as-mod mod)
                           (oddp evenp associativity-of-*))
           :use ((:instance sequence-odd-of-sum-with-even
                            (low value) (high (- (* (expt 2 63) (floor value (expt 2 64))))))
                 (:instance sequence-multiply-negation
                            (scale 2) (value (* (expt 2 63) (floor value (expt 2 64)))))
                 (:instance associativity-of-*
                            (acl2::x 2) (acl2::y (expt 2 63))
                            (acl2::z (floor value (expt 2 64))))))))

(in-theory (disable floor mod ash logbitp acl2::binary-logand acl2::binary-logior
                    acl2::binary-logxor
                    boymoo-model::a64-unsigned boymoo-model::a64-signed
                    boymoo-model::a64-ror sequence-ror
                    sequence-a64-unsigned-as-mod))
