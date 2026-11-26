(in-package "BOYMOO-PROOFS")

(include-book "arithmetic")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm minus-as-product
   (equal (- a) (* -1 a))))

(local
 (defthm product-with-negated-factor
   (and (equal (* (- a) b) (- (* a b)))
        (equal (* b (- a)) (- (* a b))))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x b) (acl2::y -1) (acl2::z a))
                  (:instance acl2::associativity-of-*
                             (acl2::x -1) (acl2::y b) (acl2::z a)))
            :in-theory (e/d (minus-as-product) (acl2::associativity-of-*)))
           ("Subgoal 1" :in-theory (enable acl2::associativity-of-*)))))

(local (in-theory (disable minus-as-product)))

(local
 (defthm product-with-minus-one
   (and (equal (* -1 a) (- a)) (equal (* a -1) (- a)))
   :hints (("Goal" :use minus-as-product))))

(local
 (defthm integer-quotient-remainder-bounds
   (implies (and (natp n) (posp d))
            (let* ((q (acl2::nonnegative-integer-quotient n d))
                   (r (- n (* d q))))
              (and (<= 0 r) (< r d))))
   :hints (("Goal"
            :induct (acl2::nonnegative-integer-quotient n d)
            :in-theory (enable acl2::nonnegative-integer-quotient)))
   :rule-classes nil))

(local
 (defthm floor-scaled-bounds
   (implies (rationalp x)
            (let ((q (floor x 1))
                  (n (numerator x))
                  (d (denominator x)))
              (and (<= (* d q) n) (< n (* d (1+ q))))))
   :hints (("Goal"
            :use ((:instance integer-quotient-remainder-bounds
                             (n (numerator x)) (d (denominator x)))
                  (:instance integer-quotient-remainder-bounds
                             (n (- (numerator x))) (d (denominator x)))
                  (:instance proof-number-exact-quotient-value
                             (a (numerator x)) (b (denominator x))
                             (q (- (acl2::nonnegative-integer-quotient
                                    (- (numerator x)) (denominator x))))))
            :in-theory (e/d (floor) (acl2::nonnegative-integer-quotient))))
   :rule-classes nil))

(local
 (defthm quotient-times-divisor
   (implies (and (rationalp a) (rationalp b) (not (equal b 0)))
            (equal (* (/ a b) b) a))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x b) (acl2::y (/ b)) (acl2::z a))
                  (:instance acl2::associativity-of-*
                             (acl2::x (/ b)) (acl2::y a) (acl2::z b)))
            :in-theory (disable acl2::associativity-of-*)))))

(local
 (defthm floor-of-one-bounds
   (implies (rationalp x)
            (and (<= (floor x 1) x)
                 (< x (1+ (floor x 1)))))
   :hints (("Goal"
            :use (floor-scaled-bounds
                  (:instance proof-number-scale-less
                             (a x) (b (floor x 1)) (c (denominator x)))
                  (:instance proof-number-scale-less
                             (a x) (b (1+ (floor x 1))) (c (denominator x)))
                  (:instance quotient-times-divisor
                             (a (numerator x)) (b (denominator x)))
                  proof-number-quotient-of-parts)
            :in-theory (disable floor acl2::distributivity
                                acl2::associativity-of-*
                                proof-number-quotient-of-parts
                                acl2::rational-implies2 quotient-times-divisor)))
   :rule-classes nil))

(local
 (defthm floor-of-quotient
   (implies (and (rationalp a) (rationalp b))
            (equal (floor (/ a b) 1) (floor a b)))
   :hints (("Goal" :in-theory (e/d (floor) (acl2::nonnegative-integer-quotient))))))

(defthm proof-number-positive-divisor-floor-bounds
  (implies (and (rationalp a) (rationalp b) (< 0 b))
           (and (<= (* b (floor a b)) a)
                (< a (* b (1+ (floor a b))))))
  :hints (("Goal"
           :use ((:instance floor-of-one-bounds (x (/ a b)))
                 (:instance proof-number-scale-less
                            (a (/ a b)) (b (floor a b)) (c b))
                 (:instance proof-number-scale-less
                            (a (/ a b)) (b (1+ (floor a b))) (c b)))
           :in-theory (disable floor acl2::nonnegative-integer-quotient
                               acl2::distributivity acl2::associativity-of-*)))
  :rule-classes nil)

(defthm proof-number-floor-with-remainder
  (implies (and (rationalp a) (rationalp b) (< 0 b)
                (integerp q) (<= (* b q) a) (< a (* b (1+ q))))
           (equal (floor a b) q))
  :hints (("Goal"
           :use (proof-number-positive-divisor-floor-bounds
                 (:instance proof-number-scale-less
                            (a (floor a b)) (b (1+ q)) (c b))
                 (:instance proof-number-scale-less
                            (a q) (b (1+ (floor a b))) (c b)))
           :in-theory (disable floor acl2::distributivity)
           :cases ((< q (floor a b)) (equal q (floor a b)))))
  :rule-classes nil)

(defthm proof-number-modulo-bounds
  (implies (and (integerp a) (posp b))
           (and (integerp (mod a b))
                (<= 0 (mod a b))
                (< (mod a b) b)))
  :hints (("Goal"
           :use proof-number-positive-divisor-floor-bounds
           :in-theory (disable floor)))
  :rule-classes ((:type-prescription :corollary
                  (implies (and (integerp a) (posp b)) (natp (mod a b))))
                 (:linear :corollary
                  (implies (and (integerp a) (posp b)) (< (mod a b) b)))))

(defthm proof-number-mod-within-range
  (implies (and (integerp a) (posp b) (<= 0 a) (< a b))
           (equal (mod a b) a))
  :hints (("Goal"
           :use ((:instance proof-number-floor-with-remainder (q 0)))
           :in-theory (disable floor))))

(defthm proof-number-mod-with-remainder
  (implies (and (integerp a) (posp b) (integerp q) (integerp r)
                (<= 0 r) (< r b) (equal a (+ (* b q) r)))
           (equal (mod a b) r))
  :hints (("Goal"
           :use proof-number-floor-with-remainder
           :in-theory (disable floor)))
  :rule-classes nil)

(defthm proof-number-floor-of-integer
  (implies (integerp a) (equal (floor a 1) a)))

(local
 (defthm power-of-two-is-positive-integer
   (implies (natp n) (posp (expt 2 n)))
   :hints (("Goal" :induct (expt 2 n) :in-theory (enable expt)))
   :rule-classes :type-prescription))

(defthm proof-number-ash-left
  (implies (and (integerp a) (natp shift))
           (equal (ash a shift) (* a (expt 2 shift))))
  :hints (("Goal"
           :in-theory (e/d (ash) (floor expt acl2::nonnegative-integer-quotient)))))

(defthm proof-number-ash-byte-tail
  (implies (integerp a)
           (equal (ash a -8) (floor a 256)))
  :hints (("Goal"
           :use ((:instance floor-of-quotient (b 256)))
           :in-theory (e/d (ash) (floor floor-of-quotient)))))

(local
 (defthm split-at-divisor
   (implies (and (rationalp a) (rationalp b))
            (equal (+ (* b (floor a b)) (mod a b)) a))
   :hints (("Goal" :in-theory (disable floor)))
   :rule-classes nil))

(local
 (defthm parity-of-integer
   (implies (integerp a)
            (and (equal (evenp a) (equal (mod a 2) 0))
                 (equal (oddp a) (equal (mod a 2) 1))))
   :hints (("Goal"
            :use ((:instance split-at-divisor (b 2))
                  (:instance proof-number-exact-quotient-value (b 2) (q (floor a 2)))
                  (:instance proof-number-mod-with-remainder
                             (b 2) (q (* 1/2 a)) (r 0)))
            :in-theory (disable mod floor)
            :cases ((integerp (* 1/2 a)) (equal (mod a 2) 0))))))

(local (in-theory (disable floor mod evenp ash expt)))

(local
 (defthm power-of-two-step
   (implies (posp n)
            (equal (expt 2 n) (* 2 (expt 2 (1- n)))))
   :hints (("Goal" :expand ((expt 2 n))))
   :rule-classes nil))

(local
 (defthm mask-of-positive-width
   (implies (posp width)
            (equal (boymoo-model::a64-ones width)
                   (+ 1 (* 2 (boymoo-model::a64-ones (1- width))))))
   :hints (("Goal" :use ((:instance power-of-two-step (n width)))))
   :rule-classes nil))

(local
 (defthm signed-half-of-mask
   (implies (posp width)
            (and (equal (floor (boymoo-model::a64-ones width) 2)
                        (boymoo-model::a64-ones (1- width)))
                 (equal (mod (boymoo-model::a64-ones width) 2) 1)))
   :hints (("Goal"
            :use (mask-of-positive-width
                  (:instance proof-number-floor-with-remainder
                             (a (boymoo-model::a64-ones width)) (b 2)
                             (q (boymoo-model::a64-ones (1- width))))
                  (:instance proof-number-mod-with-remainder
                             (a (boymoo-model::a64-ones width)) (b 2)
                             (q (boymoo-model::a64-ones (1- width))) (r 1)))
            :in-theory (disable boymoo-model::a64-ones)))))

(local
 (defthm mask-is-natural
   (natp (boymoo-model::a64-ones width))
   :rule-classes :type-prescription))

(local
 (defthm mask-is-positive
   (implies (posp width) (< 0 (boymoo-model::a64-ones width)))
   :hints (("Goal" :use mask-of-positive-width
                   :in-theory (disable boymoo-model::a64-ones)))
   :rule-classes :linear))

(local
 (defthm and-special-values
   (and (equal (logand a 0) 0)
        (equal (logand 0 a) 0)
        (implies (integerp a)
                 (and (equal (logand -1 a) a)
                      (equal (logand a -1) a))))))

(local
 (defthm and-with-mask-by-halves
   (implies (and (posp width) (integerp a))
            (equal (boymoo-model::a64-unsigned width a)
                   (+ (mod a 2)
                      (* 2 (boymoo-model::a64-unsigned (1- width) (floor a 2))))))
   :hints (("Goal"
            :use ((:instance mask-of-positive-width))
            :expand ((boymoo-model::a64-unsigned width a)
                     (boymoo-model::a64-unsigned (1- width) (floor a 2))
                     (logand a (boymoo-model::a64-ones width)))
            :in-theory (disable acl2::binary-logand boymoo-model::a64-ones
                                boymoo-model::a64-unsigned)))
   :rule-classes nil))

(local
 (defthm modulo-power-of-two-by-halves
   (implies (and (posp width) (integerp a))
            (equal (mod a (expt 2 width))
                   (+ (mod a 2) (* 2 (mod (floor a 2) (expt 2 (1- width)))))))
   :hints (("Goal"
            :use ((:instance power-of-two-step (n width))
                  (:instance split-at-divisor (b 2))
                  (:instance split-at-divisor
                             (a (floor a 2)) (b (expt 2 (1- width))))
                  (:instance proof-number-mod-with-remainder
                             (b (expt 2 width))
                             (q (floor (floor a 2) (expt 2 (1- width))))
                             (r (+ (mod a 2)
                                   (* 2 (mod (floor a 2) (expt 2 (1- width))))))))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defun mask-induction (width a)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       a
     (mask-induction (1- width) (floor a 2)))))

(defthm proof-number-a64-unsigned-is-modulo
  (implies (and (natp width) (integerp a))
           (equal (boymoo-model::a64-unsigned width a) (mod a (expt 2 width))))
  :hints (("Goal" :induct (mask-induction width a))
          ("Subgoal *1/1"
           :use ((:instance proof-number-mod-with-remainder (b 1) (q a) (r 0)))
           :in-theory (enable boymoo-model::a64-unsigned boymoo-model::a64-ones expt))
          ("Subgoal *1/2"
           :use (modulo-power-of-two-by-halves and-with-mask-by-halves)
           :in-theory (disable boymoo-model::a64-unsigned)))
  :rule-classes nil)

(defthm proof-number-a64-unsigned-range
  (unsigned-byte-p (nfix width) (boymoo-model::a64-unsigned width a))
  :hints (("Goal"
           :use ((:instance proof-number-a64-unsigned-is-modulo
                            (width (nfix width)) (a (ifix a))))
           :in-theory (disable acl2::binary-logand)))
  :rule-classes ((:rewrite) (:type-prescription
                             :corollary (natp (boymoo-model::a64-unsigned width a)))))

(defthm proof-number-a64-unsigned-in-range
  (implies (unsigned-byte-p width a)
           (equal (boymoo-model::a64-unsigned width a) a))
  :hints (("Goal"
           :use proof-number-a64-unsigned-is-modulo
           :in-theory (disable boymoo-model::a64-unsigned boymoo-model::a64-ones))))

(defthm proof-number-a64-unsigned-bound
  (< (boymoo-model::a64-unsigned width a) (expt 2 (nfix width)))
  :hints (("Goal"
           :use proof-number-a64-unsigned-range
           :in-theory (disable boymoo-model::a64-unsigned
                               proof-number-a64-unsigned-range)))
  :rule-classes :linear)

(local
 (defthm and-by-halves
   (implies (and (integerp a) (integerp b))
            (equal (logand a b)
                   (+ (if (and (equal (mod a 2) 1) (equal (mod b 2) 1)) 1 0)
                      (* 2 (logand (floor a 2) (floor b 2))))))
   :hints (("Goal"
            :use ((:instance split-at-divisor (b 2))
                  (:instance split-at-divisor (a b) (b 2)))
            :expand ((logand a b))
            :in-theory (disable acl2::binary-logand)))
   :rule-classes nil))

(local
 (defthm complement-by-halves
   (implies (integerp a)
            (and (equal (floor (lognot a) 2) (lognot (floor a 2)))
                 (equal (mod (lognot a) 2) (- 1 (mod a 2)))))
   :hints (("Goal"
            :use ((:instance split-at-divisor (b 2))
                  (:instance proof-number-floor-with-remainder
                             (a (lognot a)) (b 2) (q (lognot (floor a 2))))
                  (:instance proof-number-mod-with-remainder
                             (a (lognot a)) (b 2) (q (lognot (floor a 2)))
                             (r (- 1 (mod a 2)))))))))

(local
 (defthm or-by-halves
   (implies (and (integerp a) (integerp b))
            (equal (logior a b)
                   (+ (if (or (equal (mod a 2) 1) (equal (mod b 2) 1)) 1 0)
                      (* 2 (logior (floor a 2) (floor b 2))))))
   :hints (("Goal"
            :use ((:instance and-by-halves (a (lognot a)) (b (lognot b))))
            :in-theory (disable acl2::binary-logand lognot)
            :expand ((lognot
                      (logand (lognot a) (lognot b)))
                     (lognot
                      (logand (lognot (floor a 2)) (lognot (floor b 2)))))))
   :rule-classes nil))

(local
 (defthm or-of-zero
   (implies (integerp a)
            (and (equal (logior a 0) a)
                 (equal (logior 0 a) a)))))

(defthm proof-number-logior-with-zero
  (and (equal (logior a 0) (ifix a))
       (equal (logior 0 a) (ifix a))))

(local
 (defthm floor-half-of-even
   (implies (integerp a)
            (and (equal (floor (* 2 a) 2) a)
                 (equal (mod (* 2 a) 2) 0)))
   :hints (("Goal"
            :use ((:instance proof-number-floor-with-remainder (a (* 2 a)) (b 2) (q a))
                  (:instance proof-number-mod-with-remainder (a (* 2 a)) (b 2) (q a) (r 0)))))))

(local
 (defthm unsigned-width-of-half
   (implies (and (posp width) (unsigned-byte-p width a))
            (unsigned-byte-p (1- width) (floor a 2)))
   :hints (("Goal"
            :use ((:instance split-at-divisor (b 2))
                  (:instance power-of-two-step (n width)))))
   :rule-classes nil))

(local
 (defthm factor-two
   (equal (* a 2 b) (* 2 a b))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x a) (acl2::y 2) (acl2::z b))
                  (:instance acl2::associativity-of-*
                             (acl2::x 2) (acl2::y a) (acl2::z b)))
            :in-theory (disable acl2::associativity-of-*)))))

(local
 (defthm shift-product-step
   (implies (posp width)
            (equal (* high (expt 2 width)) (* 2 high (expt 2 (1- width)))))
   :hints (("Goal" :use ((:instance power-of-two-step (n width)))))
   :rule-classes nil))

(local
 (defthm half-of-shifted-integer
   (implies (and (posp width) (integerp high))
            (and (equal (floor (* high (expt 2 width)) 2)
                        (* high (expt 2 (1- width))))
                 (equal (mod (* high (expt 2 width)) 2) 0)))
   :hints (("Goal"
            :use ((:instance power-of-two-step (n width))
                  (:instance floor-half-of-even (a (* high (expt 2 (1- width))))))
            :in-theory (disable floor-half-of-even)))))

(defthm proof-number-logior-join
  (implies (and (unsigned-byte-p width low) (integerp high))
           (equal (logior low (* high (expt 2 width)))
                  (+ low (* high (expt 2 width)))))
  :hints (("Goal"
           :induct (mask-induction width low)
           :in-theory (disable acl2::binary-logior acl2::binary-logand))
          ("Subgoal *1/2"
           :use (shift-product-step
                 (:instance split-at-divisor (a low) (b 2))
                 (:instance unsigned-width-of-half (a low))
                 (:instance or-by-halves (a low) (b (* high (expt 2 width)))))
           :in-theory (disable acl2::binary-logior acl2::binary-logand)))
  :rule-classes nil)

(local
 (defthm or-half-components
   (implies (and (integerp a) (integerp b))
            (let ((high (logior (floor a 2) (floor b 2)))
                  (low (if (or (equal (mod a 2) 1) (equal (mod b 2) 1)) 1 0)))
              (and (equal (floor (logior a b) 2) high)
                   (equal (mod (logior a b) 2) low))))
   :hints (("Goal"
            :use (or-by-halves
                  (:instance proof-number-floor-with-remainder
                             (a (logior a b)) (b 2) (q (logior (floor a 2) (floor b 2))))
                  (:instance proof-number-mod-with-remainder
                             (a (logior a b)) (b 2) (q (logior (floor a 2) (floor b 2)))
                             (r (if (or (equal (mod a 2) 1) (equal (mod b 2) 1)) 1 0))))
            :in-theory (disable acl2::binary-logior acl2::binary-logand)))))

(local
 (defthm xor-by-halves
   (implies (and (integerp a) (integerp b))
            (equal (logxor a b)
                   (+ (if (equal (mod a 2) (mod b 2)) 0 1)
                      (* 2 (logxor (floor a 2) (floor b 2))))))
   :hints (("Goal"
            :use ((:instance and-by-halves (a (logorc1 a b)) (b (logorc1 b a))))
            :in-theory (disable acl2::binary-logior acl2::binary-logand lognot)
            :expand ((lognot (logeqv a b))
                     (lognot (logeqv (floor a 2) (floor b 2)))
                     (lognot (logand (logorc1 a b) (logorc1 b a)))
                     (lognot (logand (logorc1 (floor a 2) (floor b 2))
                                     (logorc1 (floor b 2) (floor a 2))))
                     (lognot (logand (logior (lognot a) b)
                                     (logior (lognot b) a)))
                     (lognot (logand (logior (lognot (floor a 2)) (floor b 2))
                                     (logior (lognot (floor b 2)) (floor a 2)))))))
   :rule-classes nil))

(defthm proof-number-xor-of-word-and-mask
  (implies (unsigned-byte-p width a)
           (equal (logxor a (boymoo-model::a64-ones width))
                  (- (boymoo-model::a64-ones width) a)))
  :hints (("Goal"
           :induct (mask-induction width a)
           :in-theory (disable acl2::binary-logxor boymoo-model::a64-ones))
          ("Subgoal *1/2"
           :use (mask-of-positive-width
                 (:instance split-at-divisor (b 2))
                 unsigned-width-of-half
                 (:instance xor-by-halves (b (boymoo-model::a64-ones width)))))
          ("Subgoal *1/1"
           :in-theory (enable boymoo-model::a64-ones)))
  :rule-classes nil)

(defthm proof-number-sign-bit
  (implies (and (posp width) (unsigned-byte-p width a))
           (equal (logbitp (1- width) a) (<= (expt 2 (1- width)) a)))
  :hints (("Goal"
           :use ((:instance power-of-two-step (n width))
                 (:instance proof-number-floor-with-remainder
                            (b (expt 2 (1- width))) (q 0))
                 (:instance proof-number-floor-with-remainder
                            (b (expt 2 (1- width))) (q 1)))
           :in-theory (enable logbitp)))
  :rule-classes nil)

(defthm proof-number-a64-signed-value
  (implies (and (posp width) (unsigned-byte-p width a))
           (equal (boymoo-model::a64-signed width a)
                  (if (< a (expt 2 (1- width))) a (- a (expt 2 width)))))
  :hints (("Goal"
           :use proof-number-sign-bit
           :in-theory (disable logbitp boymoo-model::a64-unsigned)
           :expand ((ash 1 width))))
  :rule-classes nil)

(defthm proof-number-ash-half
  (implies (integerp a)
           (equal (ash a -1) (floor a 2)))
  :hints (("Goal" :use ((:instance floor-of-quotient (b 2)))
                  :in-theory (e/d (ash) (floor-of-quotient)))))

(defthm proof-number-low-bit
  (implies (integerp a)
           (equal (boymoo-model::a64-unsigned 1 a)
                  (if (oddp a) 1 0)))
  :hints (("Goal"
           :use ((:instance proof-number-a64-unsigned-is-modulo (width 1)))
           :in-theory (disable boymoo-model::a64-unsigned))))

(defthm proof-number-integer-parity
  (implies (integerp a)
           (equal (oddp a) (equal (mod a 2) 1)))
  :hints (("Goal" :use parity-of-integer)))

(defthm proof-number-logand-parity
  (implies (and (integerp a) (integerp b))
           (equal (oddp (logand a b)) (and (oddp a) (oddp b))))
  :hints (("Goal"
           :use (and-by-halves
                 (:instance proof-number-mod-with-remainder (b 2)
                            (a (+ 1 (* 2 (logand (floor a 2) (floor b 2)))))
                            (q (logand (floor a 2) (floor b 2))) (r 1))
                 (:instance proof-number-mod-with-remainder (b 2)
                            (a (* 2 (logand (floor a 2) (floor b 2))))
                            (q (logand (floor a 2) (floor b 2))) (r 0)))
           :in-theory (disable acl2::binary-logand oddp mod floor)))
  :rule-classes nil)

(defthm proof-number-quotient-and-remainder
  (implies (and (rationalp a) (rationalp b))
           (equal (+ (* b (floor a b)) (mod a b)) a))
  :hints (("Goal" :use split-at-divisor))
  :rule-classes nil)

(defthm proof-number-mod-shift-by-multiple
  (implies (and (integerp a) (posp b) (integerp times))
           (equal (mod (+ a (* times b)) b) (mod a b)))
  :hints (("Goal"
           :use (split-at-divisor
                 (:instance proof-number-mod-with-remainder
                            (a (+ a (* times b)))
                            (q (+ times (floor a b))) (r (mod a b))))))
  :rule-classes nil)

(defthm proof-number-a64-signed-after-unsigned
  (implies (signed-byte-p width a)
           (equal (boymoo-model::a64-signed
                   width (boymoo-model::a64-unsigned width a)) a))
  :hints (("Goal"
           :use ((:instance proof-number-a64-unsigned-is-modulo)
                 (:instance power-of-two-step (n width))
                 (:instance proof-number-mod-with-remainder
                            (b (expt 2 width)) (q -1) (r (+ a (expt 2 width))))
                 (:instance proof-number-a64-signed-value
                            (a (boymoo-model::a64-unsigned width a))))
           :in-theory (disable boymoo-model::a64-signed boymoo-model::a64-unsigned)
           :cases ((< a 0)))))
