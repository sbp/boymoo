(in-package "BOYMOO-PROOFS")

(include-book "words")

(logic)
(set-verify-guards-eagerness 0)
(local (in-theory (disable floor mod ash expt acl2::binary-logand acl2::binary-logior)))

(local
 (defthm division-logand-trivial-operands
   (implies (integerp x)
            (and (equal (logand 0 x) 0)
                 (equal (logand x 0) 0)
                 (equal (logand -1 x) x)
                 (equal (logand x -1) x)))
   :hints (("Goal" :in-theory (enable acl2::binary-logand)))))

(defthm division-logand-split
  (implies (and (integerp x) (integerp y))
           (equal (logand x y)
                  (+ (* 2 (logand (floor x 2) (floor y 2)))
                     (if (and (equal (mod x 2) 1) (equal (mod y 2) 1)) 1 0))))
  :hints (("Goal"
           :cases ((equal x 0) (equal x -1) (equal y 0) (equal y -1))
           :use ((:instance division-evenp-remainder)
                 (:instance division-evenp-remainder (x y))
                 (:instance division-signed-mod-bounds (a x) (b 2))
                 (:instance division-signed-mod-bounds (a y) (b 2))
                 (:instance division-floor-mod-identity (a x) (b 2))
                 (:instance division-floor-mod-identity (a y) (b 2)))
           :expand ((logand x y))
           :in-theory (disable division-floor-mod-identity evenp)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-complement-half
   (implies (integerp x)
            (and (equal (floor (lognot x) 2) (lognot (floor x 2)))
                 (equal (mod (lognot x) 2) (- 1 (mod x 2)))))
   :hints (("Goal"
            :use ((:instance division-signed-mod-bounds (a x) (b 2))
                  (:instance division-floor-mod-identity (a x) (b 2))
                  (:instance division-signed-quotient-unique
                             (a (lognot x)) (b 2) (q (lognot (floor x 2))) (r (- 1 (mod x 2))))
                  (:instance division-signed-remainder-unique
                             (a (lognot x)) (b 2) (q (lognot (floor x 2))) (r (- 1 (mod x 2)))))
            :in-theory (disable division-floor-mod-identity)))
   :rule-classes nil))

(local
 (defthm division-logior-split
   (implies (and (integerp x) (integerp y))
            (equal (logior x y)
                   (+ (* 2 (logior (floor x 2) (floor y 2)))
                      (if (or (equal (mod x 2) 1) (equal (mod y 2) 1)) 1 0))))
   :hints (("Goal"
            :use ((:instance division-logand-split (x (lognot x)) (y (lognot y)))
                  (:instance division-complement-half)
                  (:instance division-complement-half (x y))
                  (:instance division-signed-mod-bounds (a x) (b 2))
                  (:instance division-signed-mod-bounds (a y) (b 2)))
            :expand ((logior x y) (logior (floor x 2) (floor y 2)))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-logior-with-even-part
   (implies (and (integerp high) (integerp low))
            (and (equal (logior (* 2 high) low)
                        (+ (* 2 (logior high (floor low 2))) (mod low 2)))
                 (equal (logior low (* 2 high))
                        (+ (* 2 (logior (floor low 2) high)) (mod low 2)))))
   :hints (("Goal"
            :use ((:instance division-logior-split (x (* 2 high)) (y low))
                  (:instance division-logior-split (x low) (y (* 2 high)))
                  (:instance division-signed-quotient-unique (a (* 2 high)) (b 2) (q high) (r 0))
                  (:instance division-signed-remainder-unique (a (* 2 high)) (b 2) (q high) (r 0))
                  (:instance division-signed-mod-bounds (a low) (b 2)))))
   :rule-classes nil))

(local
 (defun division-logior-induct (width low)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       low
     (division-logior-induct (1- width) (floor low 2)))))

(defthm division-logior-of-disjoint-fields
  (implies (and (unsigned-byte-p width low) (integerp high))
           (and (equal (logior (* high (expt 2 width)) low)
                       (+ (* high (expt 2 width)) low))
                (equal (logior low (* high (expt 2 width)))
                       (+ (* high (expt 2 width)) low))))
  :hints (("Goal" :induct (division-logior-induct width low))
          ("Subgoal *1/2"
           :use ((:instance division-logior-with-even-part (high (* high (expt 2 (1- width)))))
                 (:instance division-signed-floor-bounds (a low) (b 2))
                 (:instance division-floor-mod-identity (a low) (b 2)))
           :expand ((expt 2 width))
           :in-theory (disable division-floor-mod-identity))
          ("Subgoal *1/1"
           :in-theory (enable expt acl2::binary-logior lognot)))
  :rule-classes nil)

(defthm division-shift-joins-carry
  (implies (and (integerp digit) (unsigned-byte-p shift carry))
           (equal (logior (ash digit shift) carry) (+ (ash digit shift) carry)))
  :hints (("Goal"
           :use ((:instance division-logior-of-disjoint-fields (width shift) (low carry) (high digit))
                 (:instance division-ash-left (x digit) (width shift)))))
  :rule-classes nil)

(defconst *division-word-modulus* (expt 2 64))
(defconst *division-word-half* (expt 2 63))

(defthm division-logbitp-word-sign
  (implies (unsigned-byte-p 64 word)
           (equal (logbitp 63 word) (<= *division-word-half* word)))
  :hints (("Goal"
           :use (:instance division-signed-quotient-unique
                           (a word) (b *division-word-half*)
                           (q (if (< word *division-word-half*) 0 1))
                           (r (if (< word *division-word-half*) word (- word *division-word-half*))))
           :expand ((logbitp 63 word))))
  :rule-classes nil)

(defthm division-signed-interpretation-of-word
  (implies (unsigned-byte-p 64 word)
           (equal (boymoo-model::a64-signed 64 word)
                  (if (< word *division-word-half*) word (- word *division-word-modulus*))))
  :hints (("Goal"
           :use (:instance division-logbitp-word-sign)
           :in-theory (disable boymoo-model::a64-unsigned division-a64-unsigned-is-remainder logbitp))))

(defthm division-negative-in-word
  (implies (and (integerp value) (<= (- *division-word-modulus*) value) (< value 0))
           (equal (boymoo-model::a64-unsigned 64 value) (+ *division-word-modulus* value)))
  :hints (("Goal"
           :use (:instance division-signed-remainder-unique
                           (a value) (b *division-word-modulus*) (q -1)
                           (r (+ *division-word-modulus* value)))
           :in-theory (disable boymoo-model::a64-unsigned))))

(defthm division-signed-word-round-trip
  (implies (signed-byte-p 64 value)
           (equal (boymoo-model::a64-signed 64 (boymoo-model::a64-unsigned 64 value)) value))
  :hints (("Goal"
           :use ((:instance division-signed-interpretation-of-word
                            (word (boymoo-model::a64-unsigned 64 value)))
                 (:instance division-a64-unsigned-bounded (width 64) (x value))
                 (:instance division-negative-in-word)
                 (:instance division-a64-unsigned-of-bounded (width 64) (x value)))
           :cases ((< value 0))
           :in-theory (disable boymoo-model::a64-signed boymoo-model::a64-unsigned
                               division-a64-unsigned-is-remainder
                               division-signed-interpretation-of-word
                               division-a64-unsigned-bounded division-negative-in-word
                               division-a64-unsigned-of-bounded))))

(defthm division-logior-zero-part
  (implies (integerp x)
           (and (equal (logior x 0) x)
                (equal (logior 0 x) x)))
  :hints (("Goal" :in-theory (enable acl2::binary-logior lognot))))

(local
 (defthm division-rotate-first-bit
   (implies (unsigned-byte-p 64 word)
            (equal (boymoo-model::a64-ror 64 word 1)
                   (+ (floor word 2) (* *division-word-half* (mod word 2)))))
   :hints (("Goal"
            :use ((:instance division-signed-floor-bounds (a word) (b 2))
                  (:instance division-signed-mod-bounds (a word) (b 2))
                  (:instance division-floor-mod-identity (a word) (b 2))
                  (:instance division-scale-equality (a (+ (* 2 (floor word 2)) (mod word 2)))
                             (b word) (factor *division-word-half*))
                  (:instance division-logior-of-disjoint-fields
                             (width 63) (high word) (low (floor word 2)))
                  (:instance division-ash-right (x word) (width 1))
                  (:instance division-signed-remainder-unique
                             (a (+ (floor word 2) (* word *division-word-half*)))
                             (b *division-word-modulus*) (q (floor word 2))
                             (r (+ (floor word 2) (* *division-word-half* (mod word 2))))))
            :in-theory (disable boymoo-model::a64-unsigned division-ash-right
                                division-floor-mod-identity)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-rotate-last-bit
   (implies (unsigned-byte-p 64 word)
            (equal (boymoo-model::a64-ror 64 word 63)
                   (+ (* 2 (mod word *division-word-half*)) (floor word *division-word-half*))))
   :hints (("Goal"
            :use ((:instance division-signed-floor-bounds (a word) (b *division-word-half*))
                  (:instance division-signed-mod-bounds (a word) (b *division-word-half*))
                  (:instance division-floor-mod-identity (a word) (b *division-word-half*))
                  (:instance division-scale-equality
                             (a (+ (* *division-word-half* (floor word *division-word-half*))
                                   (mod word *division-word-half*)))
                             (b word) (factor 2))
                  (:instance division-logior-of-disjoint-fields
                             (width 1) (high word) (low (floor word *division-word-half*)))
                  (:instance division-ash-right (x word) (width 63))
                  (:instance division-signed-remainder-unique
                             (a (+ (* 2 word) (floor word *division-word-half*)))
                             (b *division-word-modulus*) (q (floor word *division-word-half*))
                             (r (+ (* 2 (mod word *division-word-half*))
                                   (floor word *division-word-half*)))))
            :in-theory (disable boymoo-model::a64-unsigned division-ash-right
                                division-floor-mod-identity)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-clear-lowest-bit
   (implies (unsigned-byte-p 64 word)
            (equal (logand word (- *division-word-modulus* 2)) (* 2 (floor word 2))))
   :hints (("Goal"
            :use ((:instance division-logand-split (x word) (y (- *division-word-modulus* 2)))
                  (:instance division-signed-floor-bounds (a word) (b 2))
                  (:instance division-mask-is-remainder (x (floor word 2)) (width 63)))
            :in-theory (disable division-mask-is-remainder)))
   :rule-classes nil))

(defun division-asr-one-result (word)
  (logior (if (logbitp 63 word) (lognot (1- *division-word-half*)) 0)
          (logand (logand (boymoo-model::a64-ror 64 word 1) (1- *division-word-modulus*))
                  (1- *division-word-half*))))

(local
 (defthm division-asr-one-value
   (implies (unsigned-byte-p 64 word)
            (equal (division-asr-one-result word)
                   (if (< word *division-word-half*)
                       (floor word 2)
                     (- (floor word 2) *division-word-half*))))
   :hints (("Goal"
            :use ((:instance division-logbitp-word-sign)
                  (:instance division-rotate-first-bit)
                  (:instance division-signed-floor-bounds (a word) (b 2))
                  (:instance division-signed-mod-bounds (a word) (b 2))
                  (:instance division-mask-is-remainder
                             (x (boymoo-model::a64-ror 64 word 1)) (width 64))
                  (:instance division-mask-is-remainder
                             (x (boymoo-model::a64-ror 64 word 1)) (width 63))
                  (:instance division-signed-remainder-unique
                             (a (boymoo-model::a64-ror 64 word 1))
                             (b *division-word-half*) (q (mod word 2)) (r (floor word 2)))
                  (:instance division-logior-of-disjoint-fields (width 63)
                             (high -1) (low (floor word 2))))
            :cases ((< word *division-word-half*))
            :in-theory (disable division-mask-is-remainder boymoo-model::a64-ror logbitp)))
   :rule-classes nil))

(local
 (defthm division-immediate-word-value
   (implies (proof-immediate-integer-p value)
            (equal (proof-integer-word value)
                   (if (< value 0)
                       (+ *division-word-modulus* 1 (* 2 value))
                     (+ 1 (* 2 value)))))
   :hints (("Goal" :cases ((< value 0))
                   :in-theory (disable boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))
   :rule-classes nil))

(defthm division-asr-decodes-immediate
  (implies (proof-immediate-integer-p value)
           (equal (division-asr-one-result (proof-integer-word value)) value))
  :hints (("Goal"
           :use ((:instance division-asr-one-value (word (proof-integer-word value)))
                 (:instance division-immediate-word-value)
                 (:instance division-signed-quotient-unique
                            (a (proof-integer-word value)) (b 2)
                            (q (if (< value 0) (+ *division-word-half* value) value)) (r 1)))
           :cases ((< value 0))
           :in-theory (disable division-asr-one-result proof-integer-word)))
  :rule-classes nil)

(defun division-lsl-one-result (word)
  (logand (logand (boymoo-model::a64-ror 64 word 63) (- *division-word-modulus* 2))
          (1- *division-word-modulus*)))

(local
 (defthm division-lsl-one-value
   (implies (unsigned-byte-p 64 word)
            (equal (division-lsl-one-result word) (* 2 (mod word *division-word-half*))))
   :hints (("Goal"
            :use ((:instance division-rotate-last-bit)
                  (:instance division-signed-floor-bounds (a word) (b *division-word-half*))
                  (:instance division-signed-mod-bounds (a word) (b *division-word-half*))
                  (:instance division-clear-lowest-bit (word (boymoo-model::a64-ror 64 word 63)))
                  (:instance division-signed-quotient-unique
                             (a (boymoo-model::a64-ror 64 word 63))
                             (b 2) (q (mod word *division-word-half*))
                             (r (floor word *division-word-half*)))
                  (:instance division-mask-is-remainder
                             (x (* 2 (mod word *division-word-half*))) (width 64)))
            :in-theory (disable division-mask-is-remainder boymoo-model::a64-ror)))
   :rule-classes nil))

(defthm division-lsl-and-add-encode-immediate
  (implies (proof-immediate-integer-p value)
           (equal (boymoo-model::a64-unsigned
                   64 (+ 1 (division-lsl-one-result (boymoo-model::a64-unsigned 64 value))))
                  (proof-integer-word value)))
  :hints (("Goal"
           :use ((:instance division-lsl-one-value (word (boymoo-model::a64-unsigned 64 value)))
                 (:instance division-immediate-word-value)
                 (:instance division-signed-remainder-unique
                            (a (boymoo-model::a64-unsigned 64 value)) (b *division-word-half*)
                            (q (if (< value 0) 1 0))
                            (r (if (< value 0) (+ *division-word-half* value) value))))
           :cases ((< value 0))
           :in-theory (disable boymoo-model::a64-unsigned division-a64-unsigned-is-remainder
                               division-lsl-one-result proof-integer-word)))
  :rule-classes nil)

(defthm division-lsl-one-result-in-word
  (implies (unsigned-byte-p 64 word)
           (unsigned-byte-p 64 (division-lsl-one-result word)))
  :hints (("Goal"
           :use ((:instance division-lsl-one-value)
                 (:instance division-signed-mod-bounds (a word) (b *division-word-half*)))
           :in-theory (disable division-lsl-one-result)))
  :rule-classes nil)

(local
 (defthm division-high-mask-clears-low-word
   (implies (unsigned-byte-p width word)
            (equal (logand word (- (expt 2 width))) 0))
   :hints (("Goal" :induct (division-logior-induct width word))
           ("Subgoal *1/2"
            :use ((:instance division-power-of-two-step)
                  (:instance division-signed-floor-bounds (a word) (b 2))
                  (:instance division-logand-split (x word) (y (- (expt 2 width))))
                  (:instance division-signed-quotient-unique
                             (a (- (expt 2 width))) (b 2)
                             (q (- (expt 2 (1- width)))) (r 0))
                  (:instance division-signed-remainder-unique
                             (a (- (expt 2 width))) (b 2)
                             (q (- (expt 2 (1- width)))) (r 0))))
           ("Subgoal *1/1" :in-theory (enable expt)))
   :rule-classes nil))

(local
 (defthm division-double-negation
   (implies (rationalp value)
            (equal (- (- value)) value))))

(local
 (defthm division-or-complement-with-low-mask
   (implies (unsigned-byte-p width word)
            (equal (logior (lognot word) (1- (expt 2 width))) -1))
   :hints (("Goal"
            :use (:instance division-high-mask-clears-low-word)
            :in-theory (enable acl2::binary-logior)))
   :rule-classes nil))

(defthm division-xor-word-complement
  (implies (unsigned-byte-p 64 word)
           (equal (logxor word (1- *division-word-modulus*))
                  (- (1- *division-word-modulus*) word)))
  :hints (("Goal"
           :use ((:instance division-or-complement-with-low-mask (width 64))
                 (:instance division-logior-of-disjoint-fields (high -1) (width 64) (low word)))
           :in-theory (enable acl2::binary-logxor acl2::binary-logeqv logorc1)))
  :rule-classes nil)

(defthm division-word-plus-modulus
  (implies (unsigned-byte-p 64 word)
           (and (equal (boymoo-model::a64-unsigned 64 (+ word *division-word-modulus*)) word)
                (logbitp 64 (+ word *division-word-modulus*))))
  :hints (("Goal"
           :use ((:instance division-signed-quotient-unique
                            (a (+ word *division-word-modulus*)) (b *division-word-modulus*)
                            (q 1) (r word))
                 (:instance division-signed-remainder-unique
                            (a (+ word *division-word-modulus*)) (b *division-word-modulus*)
                            (q 1) (r word)))
           :in-theory (disable boymoo-model::a64-unsigned)
           :expand ((logbitp 64 (+ word *division-word-modulus*)))))
  :rule-classes nil)

(defthm division-negated-signed-word
  (implies (signed-byte-p 64 value)
           (equal (boymoo-model::a64-unsigned
                   64 (- *division-word-modulus* (boymoo-model::a64-unsigned 64 value)))
                  (boymoo-model::a64-unsigned 64 (- value))))
  :hints (("Goal"
           :use ((:instance division-negative-in-word)
                 (:instance division-negative-in-word (value (- value))))
           :cases ((< value 0) (equal value 0))
           :in-theory (disable boymoo-model::a64-unsigned division-a64-unsigned-is-remainder
                               division-negative-in-word)))
  :rule-classes nil)

(defun division-word-compare-zero-flags (word)
  (cond ((equal word 0) 6)
        ((< word *division-word-half*) 2)
        (t 10)))

(defthm division-result-flags-for-zero-comparison
  (implies (unsigned-byte-p 64 word)
           (equal (boymoo-model::a64-result-flags 64 word t nil)
                  (division-word-compare-zero-flags word)))
  :hints (("Goal" :use (:instance division-logbitp-word-sign)
                  :in-theory (disable logbitp)
                  :cases ((< word *division-word-half*) (equal word 0))))
  :rule-classes nil)

(defthm division-compare-zero-selects-negative
  (implies (signed-byte-p 64 value)
           (equal (boymoo-model::a64-condition
                   11 (division-word-compare-zero-flags (boymoo-model::a64-unsigned 64 value)))
                  (< value 0)))
  :hints (("Goal"
           :use (:instance division-negative-in-word)
           :cases ((< value 0) (equal value 0))
           :in-theory (disable boymoo-model::a64-unsigned division-a64-unsigned-is-remainder
                               division-negative-in-word)))
  :rule-classes nil)

(defthm division-and-low-bit
  (implies (and (integerp left) (integerp right))
           (equal (logand (logand left right) 1)
                  (if (and (equal (mod left 2) 1) (equal (mod right 2) 1)) 1 0)))
  :hints (("Goal"
           :use ((:instance division-logand-split (x left) (y right))
                 (:instance division-mask-is-remainder (width 1) (x (logand left right)))
                 (:instance division-signed-remainder-unique
                            (a (logand left right)) (b 2)
                            (q (logand (floor left 2) (floor right 2)))
                            (r (if (and (equal (mod left 2) 1) (equal (mod right 2) 1)) 1 0))))
           :in-theory (disable division-mask-is-remainder))))
