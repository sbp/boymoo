(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

; Use quotient bounds to relate masked machine words to integer remainders.
(local
 (defthm p6-quotient-remainder-bounds
   (implies (and (natp x) (posp d))
            (and (<= (* d (nonnegative-integer-quotient x d)) x)
                 (< x (* d (1+ (nonnegative-integer-quotient x d))))))
   :rule-classes :linear
   :hints (("Goal" :induct (nonnegative-integer-quotient x d)
                   :in-theory (enable nonnegative-integer-quotient)))))

(local
 (defthm p6-multiply-equal
   (implies (equal a b)
            (equal (* d a) (* d b)))
   :rule-classes nil))

(local
 (defthm p6-scale-inverse
   (implies (and (acl2-numberp d) (not (equal d 0)))
            (equal (* d (* (/ d) n)) (fix n)))
   :hints (("Goal" :in-theory (disable associativity-of-*)
                   :use ((:instance associativity-of-*
                                    (acl2::x d) (acl2::y (/ d)) (acl2::z n)))))))

(defthm p6-numerator-product
  (implies (rationalp x)
           (equal (* (denominator x) x) (numerator x)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable acl2::rational-implies2)
                  :use ((:instance acl2::rational-implies1 (acl2::x x))
                        (:instance acl2::rational-implies2 (acl2::x x))
                        (:instance p6-scale-inverse
                                   (d (denominator x)) (n (numerator x)))
                        (:instance p6-multiply-equal
                                   (a x) (d (denominator x))
                                   (b (* (/ (denominator x)) (numerator x))))))))

(local
 (defthm p6-floor-one-bounds
   (implies (rationalp x)
            (and (<= (floor x 1) x)
                 (< x (1+ (floor x 1)))))
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable floor)
                   :use ((:instance acl2::rational-implies1 (acl2::x x))
                         p6-numerator-product
                         (:instance p6-quotient-remainder-bounds
                                    (x (numerator x)) (d (denominator x)))
                         (:instance p6-quotient-remainder-bounds
                                    (x (- (numerator x))) (d (denominator x))))
                   :nonlinearp t))))

(local
 (defthm p6-floor-as-floor-one
   (equal (floor x d) (floor (* x (/ d)) 1))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable floor)))))

(local
 (defthm p6-scale-order
   (implies (and (rationalp a) (rationalp b) (rationalp d) (< 0 d))
            (equal (< (* d a) (* d b)) (< a b)))
   :rule-classes nil
   :hints (("Goal" :cases ((< a b) (equal a b)) :nonlinearp t))))

(defthm p6-floor-bounds
  (implies (and (rationalp x) (rationalp d) (< 0 d))
           (and (<= (* d (floor x d)) x)
                (< x (* d (1+ (floor x d))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable floor)
                  :use (p6-floor-as-floor-one
                        (:instance p6-floor-one-bounds (x (* x (/ d))))
                        (:instance p6-scale-order
                                   (a (* (/ d) x)) (b (floor x d)))
                        (:instance p6-scale-order
                                   (a (* (/ d) x)) (b (1+ (floor x d))))))))

(defthm p6-floor-unique
  (implies (and (rationalp x) (rationalp d) (< 0 d) (integerp q)
                (<= (* d q) x) (< x (* d (1+ q))))
           (equal (floor x d) q))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable floor)
                  :cases ((< (floor x d) (1+ q)) (< q (1+ (floor x d))))
                  :use (p6-floor-bounds
                        (:instance p6-scale-order (a (floor x d)) (b (1+ q)))
                        (:instance p6-scale-order (a q) (b (1+ (floor x d))))))))

(in-theory (disable floor mod ash expt acl2::binary-logand
                    boymoo-model::a64-unsigned boymoo-model::a64-ones))

(defthm p6-mod-bounds
  (implies (and (integerp x) (posp d))
           (and (integerp (mod x d)) (<= 0 (mod x d)) (< (mod x d) d)))
  :rule-classes (:rewrite
                 (:linear :corollary
                          (implies (and (integerp x) (posp d))
                                   (and (<= 0 (mod x d)) (< (mod x d) d)))))
  :hints (("Goal" :use p6-floor-bounds :in-theory (enable mod))))

(defthm p6-mod-natural
  (implies (and (integerp x) (posp d))
           (natp (mod x d)))
  :rule-classes :type-prescription)

(defthm p6-floor-small
  (implies (and (rationalp x) (rationalp d) (<= 0 x) (< x d))
           (equal (floor x d) 0))
  :hints (("Goal" :use ((:instance p6-floor-unique (q 0))))))

(defthm p6-mod-small
  (implies (and (rationalp x) (rationalp d) (<= 0 x) (< x d))
           (equal (mod x d) x))
  :hints (("Goal" :in-theory (enable mod))))

(defthm p6-floor-sum
  (implies (and (rationalp x) (rationalp d) (< 0 d) (integerp q))
           (equal (floor (+ x (* d q)) d) (+ (floor x d) q)))
  :rule-classes nil
  :hints (("Goal" :use (p6-floor-bounds
                        (:instance p6-floor-unique
                                   (x (+ x (* d q))) (q (+ (floor x d) q)))))))

(defthm p6-mod-sum
  (implies (and (rationalp x) (rationalp d) (< 0 d) (integerp q))
           (equal (mod (+ x (* d q)) d) (mod x d)))
  :rule-classes nil
  :hints (("Goal" :use p6-floor-sum :in-theory (enable mod))))

(defthm p6-mod-decomposition
  (implies (and (integerp x) (posp d))
           (equal (+ (mod x d) (* d (floor x d))) x))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable mod))))

(local
 (defthm p6-times-negative
   (equal (* s (- x)) (- (* s x)))
   :hints (("Goal" :use ((:instance distributivity
                                    (acl2::x s) (acl2::y x) (acl2::z (- x))))))))

(defthm p6-mod-double
  (implies (and (integerp x) (posp d))
           (equal (mod x (* 2 d))
                  (+ (mod x 2) (* 2 (mod (floor x 2) d)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance p6-floor-unique
                                   (q (floor (floor x 2) d)) (d (* 2 d)))
                        (:instance p6-floor-bounds (d 2))
                        (:instance p6-floor-bounds (x (floor x 2))))
                  :in-theory (enable mod))))

(defthm p6-power-of-two-positive
  (implies (natp n)
           (posp (expt 2 n)))
  :rule-classes (:type-prescription :rewrite)
  :hints (("Goal" :induct (expt 2 n) :in-theory (enable expt))))

(defthm p6-power-of-two-step
  (implies (posp n)
           (equal (expt 2 n) (* 2 (expt 2 (1- n)))))
  :rule-classes nil
  :hints (("Goal" :expand ((expt 2 n)))))

(defthm p6-floor-of-integer
  (implies (integerp x) (equal (floor x 1) x))
  :hints (("Goal" :use ((:instance p6-floor-unique (q x) (d 1))))))

(defthm p6-ash-left
  (implies (natp shift)
           (equal (ash x shift) (* (ifix x) (expt 2 shift))))
  :hints (("Goal" :in-theory (enable ash))))

(defthm p6-ash-right
  (and (equal (ash x -1) (floor (ifix x) 2))
       (equal (ash x -2) (floor (ifix x) 4))
       (equal (ash x -3) (floor (ifix x) 8))
       (equal (ash x -8) (floor (ifix x) 256)))
  :hints (("Goal" :in-theory (enable ash floor))))

(defthm p6-even-as-mod
  (implies (integerp x)
           (equal (evenp x) (equal (mod x 2) 0)))
  :hints (("Goal" :in-theory (enable mod)
                  :cases ((integerp (* 1/2 x)))
                  :use ((:instance p6-floor-as-floor-one (d 2))))))

(defthm p6-mod-two-cases
  (implies (integerp x)
           (or (equal (mod x 2) 0) (equal (mod x 2) 1)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance p6-mod-bounds (d 2))))))

(local
 (defthm p6-logand-boundary
   (and (equal (logand x 0) 0) (equal (logand 0 x) 0)
        (implies (integerp x)
                 (and (equal (logand x -1) x) (equal (logand -1 x) x))))
   :hints (("Goal" :in-theory (enable acl2::binary-logand)))))

(local
 (defthm p6-logand-step
   (implies (and (integerp x) (integerp y))
            (equal (logand x y)
                   (+ (* 2 (logand (floor x 2) (floor y 2)))
                      (if (or (equal (mod x 2) 0) (equal (mod y 2) 0)) 0 1))))
   :rule-classes nil
   :hints (("Goal"
            :expand ((acl2::binary-logand x y))
            :in-theory (enable p6-even-as-mod)
            :use ((:instance p6-mod-two-cases)
                  (:instance p6-mod-two-cases (x y))
                  (:instance p6-mod-decomposition (d 2))
                  (:instance p6-mod-decomposition (x y) (d 2)))))))

(local
 (defthm p6-mask-half
   (implies (posp width)
            (and (equal (floor (1- (expt 2 width)) 2)
                        (1- (expt 2 (1- width))))
                 (equal (mod (1- (expt 2 width)) 2) 1)))
   :rule-classes nil
   :hints (("Goal"
            :use ( (:instance p6-power-of-two-step (n width))
                   (:instance p6-floor-unique
                              (x (1- (expt 2 width))) (d 2)
                              (q (1- (expt 2 (1- width))))))
            :in-theory (enable mod)))))

(local
 (defun p6-mask-induct (x width)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       x
     (p6-mask-induct (floor x 2) (1- width)))))

(local
 (defthm p6-logand-mask
   (implies (and (integerp x) (natp width))
            (equal (logand x (1- (expt 2 width)))
                   (mod x (expt 2 width))))
   :hints (("Goal" :induct (p6-mask-induct x width))
           ("Subgoal *1/2" :use ((:instance p6-logand-step (y (1- (expt 2 width))))
                                p6-mask-half
                                (:instance p6-power-of-two-step (n width))
                                (:instance p6-mod-double (d (expt 2 (1- width))))
                                (:instance p6-mod-two-cases)))
           ("Subgoal *1/1" :use ((:instance p6-floor-unique (d 1) (q x)))
                           :in-theory (enable mod)))))

(defthm p6-unsigned-as-mod
  (equal (boymoo-model::a64-unsigned width x)
         (mod (ifix x) (expt 2 (nfix width))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned
                                   boymoo-model::a64-ones))))

(defthm p6-unsigned-range
  (implies (natp width)
           (unsigned-byte-p width (boymoo-model::a64-unsigned width x))))

(defthm p6-unsigned-identity
  (implies (unsigned-byte-p width x)
           (equal (boymoo-model::a64-unsigned width x) x)))

(defthm p6-unsigned-lower-bound
  (<= 0 (boymoo-model::a64-unsigned width x))
  :rule-classes :linear)

(defthm p6-unsigned-upper-bound
  (< (boymoo-model::a64-unsigned width x) (expt 2 (nfix width)))
  :rule-classes :linear)

(defthm p6-unsigned-add
  (equal (boymoo-model::a64-unsigned
          width (+ (boymoo-model::a64-unsigned width x) (ifix y)))
         (boymoo-model::a64-unsigned width (+ (ifix x) (ifix y))))
  :hints (("Goal" :in-theory (disable nfix)
           :use ((:instance p6-mod-sum
                            (x (+ (mod (ifix x) (expt 2 (nfix width))) (ifix y)))
                            (d (expt 2 (nfix width)))
                            (q (floor (ifix x) (expt 2 (nfix width)))))
                 (:instance p6-mod-decomposition
                            (x (ifix x)) (d (expt 2 (nfix width))))))))

(defthm p6-unsigned-sub
  (equal (boymoo-model::a64-unsigned
          width (- (boymoo-model::a64-unsigned width x) (ifix y)))
         (boymoo-model::a64-unsigned width (- (ifix x) (ifix y))))
  :hints (("Goal" :in-theory (disable p6-unsigned-as-mod p6-unsigned-add)
                  :use ((:instance p6-unsigned-add (y (- (ifix y))))))))

(defthm p6-unsigned-add-integer
  (implies (integerp y)
           (and (equal (boymoo-model::a64-unsigned
                        width (+ y (boymoo-model::a64-unsigned width x)))
                       (boymoo-model::a64-unsigned width (+ y (ifix x))))
                (equal (boymoo-model::a64-unsigned
                        width (+ (boymoo-model::a64-unsigned width x) y))
                       (boymoo-model::a64-unsigned width (+ (ifix x) y)))))
  :hints (("Goal" :in-theory (disable p6-unsigned-as-mod p6-unsigned-add)
                  :use p6-unsigned-add)))

(defthm p6-unsigned-between-wraps
  (implies (and (integerp x) (natp width)
                (<= (- (expt 2 width)) x) (< x (* 2 (expt 2 width))))
           (equal (boymoo-model::a64-unsigned width x)
                  (cond ((< x 0) (+ x (expt 2 width)))
                        ((< x (expt 2 width)) x)
                        (t (- x (expt 2 width))))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable mod)
                  :use ((:instance p6-floor-unique
                                   (d (expt 2 width))
                                   (q (cond ((< x 0) -1)
                                            ((< x (expt 2 width)) 0)
                                            (t 1))))))))

(in-theory (disable p6-unsigned-as-mod))

(defthm p6-unsigned-natural
  (natp (boymoo-model::a64-unsigned width x))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable p6-unsigned-as-mod))))

(defthm p6-low-word-bit
  (implies (and (integerp x) (posp width))
           (equal (mod (boymoo-model::a64-unsigned width x) 2) (mod x 2)))
  :hints (("Goal" :in-theory (enable p6-unsigned-as-mod)
                  :use ((:instance p6-power-of-two-step (n width))
                        (:instance p6-mod-double (d (expt 2 (1- width))))
                        (:instance p6-mod-sum
                                   (x (mod x 2)) (d 2)
                                   (q (mod (floor x 2) (expt 2 (1- width)))))
                        p6-mod-two-cases))))

(defthm p6-odd-from-tag
  (implies (integerp word)
           (equal (oddp word) (oddp (proof-word-tag word))))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable proof-word-tag))))

(defthm p6-top-bit
  (implies (and (natp bit) (unsigned-byte-p (1+ bit) x))
           (equal (logbitp bit x) (<= (expt 2 bit) x)))
  :hints (("Goal" :in-theory (enable logbitp)
                  :use ((:instance p6-power-of-two-step (n (1+ bit)))
                        (:instance p6-floor-unique
                                   (d (expt 2 bit))
                                   (q (if (< x (expt 2 bit)) 0 1)))))))

(defthm p6-signed64-in-range
  (implies (unsigned-byte-p 64 word)
           (equal (boymoo-model::a64-signed 64 word)
                  (if (< word (expt 2 63)) word (- word (expt 2 64)))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-signed)
                  :use ((:instance p6-top-bit (bit 63) (x word))))))

(defthm p6-odd-word-decodes-to-immediate
  (implies (and (unsigned-byte-p 64 word) (oddp word))
           (let ((value (ash (boymoo-model::a64-signed 64 word) -1)))
             (and (proof-immediate-integer-p value)
                  (equal (proof-integer-word value) word))))
  :rule-classes nil
  :hints (("Goal" :cases ((< word (expt 2 63)) (equal (mod word 2) 1))
                  :in-theory (disable p6-even-as-mod)
                  :use ((:instance p6-floor-bounds (x word) (d 2))
                        (:instance p6-even-as-mod (x word))
                        (:instance p6-mod-two-cases (x word))
                        (:instance p6-mod-decomposition (x word) (d 2))
                        (:instance p6-floor-sum (x word) (d 2) (q (- (expt 2 63))))
                        (:instance p6-unsigned-between-wraps
                                   (x (- word (expt 2 64))) (width 64))))))

(defthm p6-character-code-is-byte
  (unsigned-byte-p 8 (char-code value)))

(defthm p6-projected-character-code
  (implies (and (unsigned-byte-p 64 word) (equal (proof-word-tag word) 4)
                (unsigned-byte-p 8 (ash word -3)))
           (equal (proof-character-word (code-char (ash word -3))) word))
  :hints (("Goal" :in-theory (enable proof-word-tag p6-unsigned-as-mod)
                  :use ((:instance p6-mod-decomposition (x word) (d 8))))))

(local
 (defthm p6-lognot-half
   (implies (integerp x)
            (and (equal (floor (lognot x) 2) (lognot (floor x 2)))
                 (equal (mod (lognot x) 2) (- 1 (mod x 2)))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance p6-floor-unique (x (lognot x)) (d 2)
                             (q (lognot (floor x 2))))
                  (:instance p6-mod-two-cases)
                  (:instance p6-mod-decomposition (d 2)))
            :in-theory (enable mod)))))

(local
 (defthm p6-logior-step
   (implies (and (integerp x) (integerp y))
            (equal (logior x y)
                   (+ (* 2 (logior (floor x 2) (floor y 2)))
                      (if (and (equal (mod x 2) 0) (equal (mod y 2) 0)) 0 1))))
   :rule-classes nil
   :hints (("Goal"
            :use (p6-lognot-half (:instance p6-lognot-half (x y))
                  (:instance p6-logand-step (x (lognot x)) (y (lognot y)))
                  p6-mod-two-cases (:instance p6-mod-two-cases (x y)))))))

(defthm p6-floor-mod-of-scaled-sum
  (implies (and (integerp n) (rationalp lo) (rationalp d) (<= 0 lo) (< lo d))
           (and (equal (floor (+ lo (* d n)) d) n)
                (equal (mod (+ lo (* d n)) d) lo)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance p6-floor-unique (x (+ lo (* d n))) (q n)))
                  :in-theory (enable mod))))

(local
 (defthm p6-commute-factors
   (equal (* a (* b c)) (* b (* a c)))
   :hints (("Goal"
            :in-theory (disable associativity-of-*)
            :use ((:instance associativity-of-* (acl2::x a) (acl2::y b) (acl2::z c))
                  (:instance associativity-of-* (acl2::x b) (acl2::y a) (acl2::z c)))))))

(local
 (defthm p6-scaled-power-of-two-step
   (implies (posp width)
            (equal (* hi (expt 2 width)) (* 2 (* hi (expt 2 (1- width))))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance p6-power-of-two-step (n width))
                  (:instance p6-multiply-equal
                             (a (expt 2 width)) (d hi)
                             (b (* 2 (expt 2 (1- width))))))))))

(defthm p6-logior-joins-fields
  (implies (and (unsigned-byte-p width lo) (integerp hi))
           (equal (logior lo (* (expt 2 width) hi))
                  (+ lo (* (expt 2 width) hi))))
  :rule-classes nil
  :hints (("Goal" :induct (p6-mask-induct lo width)
                  :in-theory (disable acl2::binary-logior))
          ("Subgoal *1/2"
           :use ((:instance p6-power-of-two-step (n width))
                 p6-scaled-power-of-two-step
                 (:instance p6-logior-step (x lo) (y (* 2 (* (expt 2 (1- width)) hi))))
                 (:instance p6-floor-mod-of-scaled-sum
                            (d 2) (lo 0) (n (* (expt 2 (1- width)) hi)))
                 (:instance p6-floor-bounds (d 2) (x lo))
                 (:instance p6-mod-two-cases (x lo))
                 (:instance p6-mod-decomposition (x lo) (d 2)))
           :nonlinearp t)
          ("Subgoal *1/1" :in-theory (enable acl2::binary-logior))))

(defthm p6-join-byte-with-tail
  (implies (and (unsigned-byte-p 8 lo) (integerp hi))
           (and (equal (logior lo (ash hi 8)) (+ lo (* 256 hi)))
                (equal (logior lo (* 256 hi)) (+ lo (* 256 hi)))))
  :hints (("Goal" :in-theory (disable acl2::binary-logior)
                  :use ((:instance p6-logior-joins-fields (width 8))))))

(local
 (defthm p6-logand-halves
   (implies (and (integerp x) (integerp y))
            (and (equal (floor (logand x y) 2) (logand (floor x 2) (floor y 2)))
                 (equal (mod (logand x y) 2)
                        (if (or (equal (mod x 2) 0) (equal (mod y 2) 0)) 0 1))))
   :hints (("Goal"
            :use (p6-logand-step
                  (:instance p6-floor-mod-of-scaled-sum
                             (d 2) (n (logand (floor x 2) (floor y 2)))
                             (lo (if (or (equal (mod x 2) 0) (equal (mod y 2) 0)) 0 1))))))))

(local
 (defthm p6-logior-halves
   (implies (and (integerp x) (integerp y))
            (and (equal (floor (logior x y) 2) (logior (floor x 2) (floor y 2)))
                 (equal (mod (logior x y) 2)
                        (if (and (equal (mod x 2) 0) (equal (mod y 2) 0)) 0 1))))
   :hints (("Goal"
            :in-theory (disable acl2::binary-logior)
            :use (p6-logior-step
                  (:instance p6-floor-mod-of-scaled-sum
                             (d 2) (n (logior (floor x 2) (floor y 2)))
                             (lo (if (and (equal (mod x 2) 0) (equal (mod y 2) 0)) 0 1))))))))

(local
 (defthm p6-lognot-halves
   (implies (integerp x)
            (and (equal (floor (lognot x) 2) (lognot (floor x 2)))
                 (equal (mod (lognot x) 2) (- 1 (mod x 2)))))
   :hints (("Goal" :use p6-lognot-half))))

(local
 (in-theory (disable lognot acl2::binary-logior)))

(local
 (defthm p6-logxor-halves
   (implies (and (integerp x) (integerp y))
            (and (equal (floor (logxor x y) 2) (logxor (floor x 2) (floor y 2)))
                 (equal (mod (logxor x y) 2)
                        (if (equal (mod x 2) (mod y 2)) 0 1))))
   :hints (("Goal"
            :use (p6-mod-two-cases (:instance p6-mod-two-cases (x y)))
            :in-theory (enable acl2::binary-logxor acl2::binary-logeqv acl2::logorc1)))))

(local
 (defthm p6-logxor-step
   (implies (and (integerp x) (integerp y))
            (equal (logxor x y)
                   (+ (* 2 (logxor (floor x 2) (floor y 2)))
                      (if (equal (mod x 2) (mod y 2)) 0 1))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable acl2::binary-logxor)
                   :use ((:instance p6-mod-decomposition (x (logxor x y)) (d 2)))))))

(local
 (defthm p6-logxor-zero
   (implies (integerp x) (equal (logxor x 0) x))
   :hints (("Goal" :in-theory (enable lognot acl2::binary-logior acl2::binary-logxor
                                    acl2::binary-logeqv acl2::logorc1)))))

(defthm p6-logxor-complement-within-width
  (implies (unsigned-byte-p width x)
           (equal (logxor x (1- (expt 2 width))) (- (1- (expt 2 width)) x)))
  :rule-classes nil
  :hints (("Goal" :induct (p6-mask-induct x width)
                  :in-theory (disable acl2::binary-logxor))
          ("Subgoal *1/2"
           :use ((:instance p6-logxor-step (y (1- (expt 2 width))))
                 p6-mask-half
                 (:instance p6-power-of-two-step (n width))
                 (:instance p6-floor-bounds (d 2))
                 (:instance p6-mod-decomposition (d 2))
                 p6-mod-two-cases))))

(defthm p6-logxor-complement-64
  (implies (unsigned-byte-p 64 x)
           (equal (logxor x #xffffffffffffffff) (- #xffffffffffffffff x)))
  :hints (("Goal" :in-theory (disable acl2::binary-logxor)
                  :use ((:instance p6-logxor-complement-within-width (width 64))))))

(in-theory (disable acl2::binary-logxor logbitp acl2::binary-logior))

(defthm p6-small-masks
  (implies (integerp x)
           (and (equal (logand x 1) (boymoo-model::a64-unsigned 1 x))
                (equal (logand x 7) (boymoo-model::a64-unsigned 3 x))
                (equal (logand x 255) (boymoo-model::a64-unsigned 8 x))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned boymoo-model::a64-ones))))

(defthm p6-unsigned64-one-wrap
  (implies (integerp x)
           (and (equal (boymoo-model::a64-unsigned 64 (+ #x10000000000000000 x))
                       (boymoo-model::a64-unsigned 64 x))
                (equal (boymoo-model::a64-unsigned 64 (+ x #x10000000000000000))
                       (boymoo-model::a64-unsigned 64 x))))
  :hints (("Goal" :in-theory (enable p6-unsigned-as-mod)
                  :use ((:instance p6-mod-sum (d (expt 2 64)) (q 1))))))

(defthm p6-unsigned64-difference-zero
  (implies (and (unsigned-byte-p 64 x) (unsigned-byte-p 64 y))
           (equal (equal (boymoo-model::a64-unsigned 64 (- x y)) 0)
                  (equal x y)))
  :hints (("Goal" :use ((:instance p6-unsigned-between-wraps (width 64) (x (- x y)))))))

(defthm p6-unsigned-one-as-parity
  (implies (integerp x)
           (equal (boymoo-model::a64-unsigned 1 x)
                  (if (oddp x) 1 0)))
  :hints (("Goal" :in-theory (enable p6-unsigned-as-mod)
                  :use (p6-mod-two-cases))))

(local
 (defun p6-low-xor-induction (width left right)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       (list left right)
     (p6-low-xor-induction (1- width) (floor left 2) (floor right 2)))))

(defthm p6-low-xor-zero-means-low-bits-agree
  (implies (and (natp width) (integerp left) (integerp right))
           (equal (equal (mod (logxor left right) (expt 2 width)) 0)
                  (equal (mod left (expt 2 width)) (mod right (expt 2 width)))))
  :rule-classes nil
  :hints (("Goal" :induct (p6-low-xor-induction width left right))
          ("Subgoal *1/1"
           :use ((:instance p6-mod-bounds (d 1) (x left))
                 (:instance p6-mod-bounds (d 1) (x right))
                 (:instance p6-mod-bounds (d 1) (x (logxor left right)))))
          ("Subgoal *1/2"
           :in-theory (disable p6-logxor-halves)
           :use ((:instance p6-logxor-halves (x left) (y right))
                 (:instance p6-power-of-two-step (n width))
                 (:instance p6-mod-two-cases (x left))
                 (:instance p6-mod-two-cases (x right))
                 (:instance p6-mod-double (x left) (d (expt 2 (1- width))))
                 (:instance p6-mod-double (x right) (d (expt 2 (1- width))))
                 (:instance p6-mod-double (x (logxor left right)) (d (expt 2 (1- width))))))))

(local
 (defthm p6-xor-is-an-integer
   (integerp (logxor left right))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable acl2::binary-logxor acl2::binary-logeqv acl2::logorc1)))))

(local
 (defthm p6-mod-eight-after-word-wrap
   (implies (integerp x)
            (equal (mod (mod x (expt 2 64)) 8) (mod x 8)))
   :hints (("Goal"
            :in-theory (disable associativity-of-*)
            :use ((:instance p6-mod-decomposition (d (expt 2 64)))
                  (:instance p6-mod-sum (x (mod x (expt 2 64))) (d 8)
                             (q (* (expt 2 61) (floor x (expt 2 64)))))
                  (:instance associativity-of-* (acl2::x 8) (acl2::y (expt 2 61))
                             (acl2::z (floor x (expt 2 64)))))))))

(defthm p6-xor-tests-word-tags
  (implies (and (integerp left) (integerp right))
           (and (equal (equal (logand (boymoo-model::a64-unsigned 64 (logxor left right)) 7) 0)
                       (equal (proof-word-tag left) (proof-word-tag right)))
                (equal (equal (boymoo-model::a64-unsigned 3
                                                  (boymoo-model::a64-unsigned 64 (logxor left right))) 0)
                       (equal (proof-word-tag left) (proof-word-tag right)))))
  :hints (("Goal"
           :in-theory (e/d (p6-unsigned-as-mod proof-word-tag) (p6-mod-eight-after-word-wrap))
           :use ((:instance p6-low-xor-zero-means-low-bits-agree (width 3))
                 (:instance p6-mod-eight-after-word-wrap (x (logxor left right)))))))
