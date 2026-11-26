(in-package "BOYMOO-PROOFS")

(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt logbitp oddp
                           boymoo-model::a64-unsigned)))

(defthm integer-ash-left
  (implies (natp count)
           (equal (ash x count) (* (ifix x) (expt 2 count))))
  :hints (("Goal" :in-theory (enable ash)
           :use ((:instance integer-floor-unique
                            (x (* (ifix x) (expt 2 count)))
                            (y 1) (q (* (ifix x) (expt 2 count))))))))

(local
 (defthm integer-reciprocal-unique
   (implies (and (rationalp d) (not (equal d 0)) (rationalp r)
                 (equal (* r d) 1))
            (equal r (/ d)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable associativity-of-*)
            :use ((:instance associativity-of-*
                             (acl2::x r) (acl2::y d) (acl2::z (/ d))))))))

(local
 (defthm integer-reciprocal-of-double
   (implies (posp x)
            (equal (/ (* 2 x)) (* 1/2 (/ x))))
   :hints (("Goal" :in-theory (disable associativity-of-*)
            :use ((:instance integer-reciprocal-unique
                             (d (* 2 x)) (r (* 1/2 (/ x))))
                  (:instance associativity-of-*
                             (acl2::x 1/2) (acl2::y (/ x)) (acl2::z (* 2 x)))
                  (:instance associativity-of-*
                             (acl2::x 2) (acl2::y x) (acl2::z (/ x)))
                  (:instance associativity-of-*
                             (acl2::x 1/2) (acl2::y 2) (acl2::z (* x (/ x)))))))))

(local
 (defthm integer-expt-reciprocal
   (implies (natp count)
            (equal (expt 2 (- count)) (/ (expt 2 count))))
   :hints (("Goal" :induct (expt 2 count) :in-theory (enable expt))
           ("Subgoal *1/2" :expand ((expt 2 (- count)) (expt 2 count))))))

(local
 (defthm integer-floor-quotient
   (equal (floor (* x (/ d)) 1) (floor x d))
   :hints (("Goal" :in-theory (enable floor)))))

(defthmd integer-ash-right
  (implies (natp count)
           (equal (ash x (- count))
                  (floor (ifix x) (expt 2 count))))
  :hints (("Goal" :in-theory (enable ash))))

(defthm integer-bit-at-position
  (implies (and (natp position) (integerp x))
           (equal (logbitp position x)
                  (equal (mod (floor x (expt 2 position)) 2) 1)))
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm integer-a64-unsigned-in-range
  (implies (and (natp width) (natp x) (< x (expt 2 width)))
           (equal (boymoo-model::a64-unsigned width x) x)))

(defthm integer-a64-unsigned-idempotent
  (implies (natp width)
           (equal (boymoo-model::a64-unsigned width
                                              (boymoo-model::a64-unsigned width x))
                  (boymoo-model::a64-unsigned width x))))

(defthm integer-a64-signed-of-unsigned
  (implies (natp width)
           (equal (boymoo-model::a64-signed width
                                            (boymoo-model::a64-unsigned width x))
                  (boymoo-model::a64-signed width x))))

(defthmd integer-a64-signed-test
  (implies (posp width)
           (let ((bits (mod (ifix x) (expt 2 width))))
             (equal (boymoo-model::a64-signed width x)
                    (if (< bits (expt 2 (1- width)))
                        bits
                      (- bits (expt 2 width))))))
  :hints (("Goal"
           :use (integer-power-of-two-step
                 (:instance integer-floor-unique
                            (x (mod (ifix x) (expt 2 width)))
                            (y (expt 2 (1- width))) (q 0))
                 (:instance integer-floor-unique
                            (x (mod (ifix x) (expt 2 width)))
                            (y (expt 2 (1- width))) (q 1))))))

(defthm integer-a64-signed-in-range
  (implies (and (posp width) (integerp x)
                (<= (- (expt 2 (1- width))) x)
                (< x (expt 2 (1- width))))
           (equal (boymoo-model::a64-signed width x) x))
  :hints (("Goal" :in-theory (e/d (integer-a64-signed-test)
                                  (boymoo-model::a64-signed))
           :cases ((< x 0))
           :use (integer-power-of-two-step
                 (:instance integer-mod-unique (d (expt 2 width)) (q 0) (r x))
                 (:instance integer-mod-unique
                            (d (expt 2 width)) (q -1) (r (+ x (expt 2 width))))))))

(defthm integer-immediate-word-signed
  (implies (proof-immediate-integer-p value)
           (equal (boymoo-model::a64-signed 64 (proof-integer-word value))
                  (+ 1 (* 2 value))))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-signed
                                     integer-a64-unsigned-is-mod)
           :use ((:instance integer-a64-signed-in-range (width 64) (x (+ 1 (* 2 value))))
                 (:instance integer-a64-signed-of-unsigned
                            (width 64) (x (+ 1 (* 2 value))))))))

(defthm integer-immediate-word-odd
  (implies (proof-immediate-integer-p value)
           (oddp (proof-integer-word value)))
  :hints (("Goal" :cases ((< value 0))
           :use ((:instance integer-mod-when-in-range
                            (x (+ 1 (* 2 value))) (d (expt 2 64)))
                 (:instance integer-mod-when-negative-and-in-range
                            (x (+ 1 (* 2 value))) (d (expt 2 64)))
                 (:instance integer-mod-of-division (q value) (r 1) (y 2))
                 (:instance integer-mod-of-division
                            (q (+ value (expt 2 63))) (r 1) (y 2))))))

(defthm integer-immediate-word-type
  (unsigned-byte-p 64 (proof-integer-word value))
  :hints (("Goal" :in-theory (disable unsigned-byte-p integer-a64-unsigned-is-mod
                                     integer-a64-unsigned-in-range))))

(defthm integer-immediate-word-round-trip
  (implies (proof-immediate-integer-p value)
           (proof-value-p (proof-integer-word value) value
                          base objects packages machine))
  :hints (("Goal"
           :in-theory (e/d (integer-ash-right)
                           (unsigned-byte-p proof-integer-word
                            boymoo-model::a64-signed))
           :use ((:instance integer-floor-of-double-plus-bit (high value) (low 1))))))

(defthm integer-power-of-two-add
  (implies (and (natp a) (natp b))
           (equal (expt 2 (+ a b)) (* (expt 2 a) (expt 2 b))))
  :rule-classes nil
  :hints (("Goal" :induct (expt 2 a) :in-theory (enable (:induction expt)))
          ("Subgoal *1/3"
           :use ((:instance integer-power-of-two-step (width a))
                 (:instance integer-power-of-two-step (width (+ a b)))))))
