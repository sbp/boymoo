(in-package "BOYMOO-PROOFS")

(include-book "immediate-arithmetic")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-execute proof-instruction-effect
                     proof-segment-p proof-number-checked-block-p proof-world-machine
                     proof-world-stop proof-reg proof-world-reg proof-world-pc proof-heap-base
                     boymoo-model::a64-unsigned boymoo-model::a64-signed boymoo-model::a64-memory
                     boymoo-model::a64-read-reg boymoo-model::a64-write-reg boymoo-model::a64-set-pc
                     boymoo-model::a64-pc boymoo-model::a64-sp boymoo-model::a64-set-nzcv
                     boymoo-model::a64-condition boymoo-model::a64-nzcv
                     (:definition update-nth) (:definition nth)
                     acl2::binary-logand acl2::binary-logior proof-number-low-bit logbitp mod floor ash)))

(local
 (defthm floor-of-power-of-two-quotient
   (implies (and (integerp word) (member-equal shift '(1 63 64)))
            (equal (ash word (- shift)) (floor word (expt 2 shift))))
   :hints (("Goal"
            :in-theory (e/d (ash floor) (acl2::nonnegative-integer-quotient))
            :cases ((equal shift 1) (equal shift 63))))))

(local
 (defthm input-quotient-fits-remaining-bits
   (implies (and (unsigned-byte-p 64 word) (member-equal shift '(1 63)))
            (unsigned-byte-p (- 64 shift) (floor word (expt 2 shift))))
   :hints (("Goal"
            :use ((:instance proof-number-positive-divisor-floor-bounds (a word) (b (expt 2 shift))))
            :cases ((equal shift 1))))))

(local
 (defthm rotating-word-bits
   (implies (and (unsigned-byte-p 64 word) (member-equal shift '(1 63)))
            (equal (boymoo-model::a64-ror 64 word shift)
                   (boymoo-model::a64-unsigned
                    64 (+ (floor word (expt 2 shift)) (* word (expt 2 (- 64 shift)))))))
   :hints (("Goal"
            :use (input-quotient-fits-remaining-bits
                  (:instance proof-number-logior-join (width (- 64 shift))
                             (low (floor word (expt 2 shift))) (high word)))
            :in-theory (e/d (boymoo-model::a64-ror) (input-quotient-fits-remaining-bits))
            :cases ((equal shift 1))))
   :rule-classes nil))

(local
 (defthm unsigned-word-over-period
   (implies (and (integerp x) (member-equal width '(1 63 64)) (integerp periods))
            (equal (boymoo-model::a64-unsigned width (+ x (* (expt 2 width) periods)))
                   (boymoo-model::a64-unsigned width x)))
   :hints (("Goal"
            :use ((:instance proof-number-mod-shift-by-multiple
                             (a x) (b (expt 2 width)) (times periods))
                  (:instance proof-number-a64-unsigned-is-modulo (a x))
                  (:instance proof-number-a64-unsigned-is-modulo (a (+ x (* (expt 2 width) periods)))))
            :cases ((equal width 1) (equal width 63))))
   :rule-classes nil))

(local
 (defthm lower-bits-through-word-mask
   (implies (and (integerp word) (member-equal width '(1 63)))
            (equal (boymoo-model::a64-unsigned width (boymoo-model::a64-unsigned 64 word))
                   (boymoo-model::a64-unsigned width word)))
   :hints (("Goal"
            :use ((:instance proof-number-a64-unsigned-is-modulo (width 64) (a word))
                  (:instance proof-number-quotient-and-remainder (a word) (b (expt 2 64)))
                  (:instance unsigned-word-over-period
                             (x (boymoo-model::a64-unsigned 64 word))
                             (periods (* (expt 2 (- 64 width)) (floor word (expt 2 64)))))
                  (:instance acl2::associativity-of-*
                             (acl2::x (expt 2 width)) (acl2::y (expt 2 (- 64 width)))
                             (acl2::z (floor word (expt 2 64)))))
            :in-theory (disable acl2::associativity-of-*)
            :cases ((equal width 1))))))

(local
 (defthm rightward-bits-after-rotation
   (implies (and (unsigned-byte-p 64 word) (member-equal shift '(1 63)))
            (equal (boymoo-model::a64-unsigned (- 64 shift) (boymoo-model::a64-ror 64 word shift))
                   (floor word (expt 2 shift))))
   :hints (("Goal"
            :use (rotating-word-bits input-quotient-fits-remaining-bits
                  (:instance unsigned-word-over-period
                             (width (- 64 shift)) (x (floor word (expt 2 shift))) (periods word)))
            :in-theory (disable boymoo-model::a64-ror input-quotient-fits-remaining-bits)
            :cases ((equal shift 1))))
   :rule-classes nil))

(local
 (defthm signed-word-floor
   (implies (and (unsigned-byte-p 64 word) (member-equal shift '(1 63)))
            (equal (floor (boymoo-model::a64-signed 64 word) (expt 2 shift))
                   (+ (floor word (expt 2 shift))
                      (if (logbitp 63 word) (- (expt 2 (- 64 shift))) 0))))
   :hints (("Goal"
            :use ((:instance proof-number-a64-signed-value (width 64) (a word))
                  (:instance proof-number-sign-bit (width 64) (a word))
                  (:instance proof-number-positive-divisor-floor-bounds (a word) (b (expt 2 shift)))
                  (:instance proof-number-floor-with-remainder
                             (a (- word (expt 2 64))) (b (expt 2 shift))
                             (q (- (floor word (expt 2 shift)) (expt 2 (- 64 shift))))))
            :cases ((equal shift 1) (logbitp 63 word))))
   :rule-classes nil))

(local
 (defthm mask-is-unsigned-word
   (implies (integerp word)
            (equal (logand word (boymoo-model::a64-ones width))
                   (boymoo-model::a64-unsigned width word)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned)))))

(local
 (defthm rotated-word-fits
   (unsigned-byte-p 64 (boymoo-model::a64-ror 64 word shift))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-ror)))))

(local
 (defthm logical-and-commutes
   (equal (logand left right) (logand right left))
   :hints (("Goal" :induct (acl2::binary-logand left right)
            :in-theory (enable acl2::binary-logand)))))

(local
 (defthm logical-or-commutes
   (equal (logior left right) (logior right left))
   :hints (("Goal" :in-theory (enable acl2::binary-logior)))))

(local
 (defthm arithmetic-bitfield-signed-shift
   (let* ((rotated (boymoo-model::a64-ror 64 word shift))
          (mask (boymoo-model::a64-ones (- 64 shift)))
          (low (logand (logand rotated (boymoo-model::a64-ones 64)) mask))
          (high (if (logbitp 63 word) (lognot mask) 0)))
     (implies (and (unsigned-byte-p 64 word) (member-equal shift '(1 63)))
              (equal (logior high low) (ash (boymoo-model::a64-signed 64 word) (- shift)))))
   :hints (("Goal"
            :use (rightward-bits-after-rotation signed-word-floor
                  (:instance mask-is-unsigned-word (width 64) (word (boymoo-model::a64-ror 64 word shift)))
                  (:instance mask-is-unsigned-word (width (- 64 shift))
                             (word (boymoo-model::a64-ror 64 word shift)))
                  (:instance proof-number-logior-join (width (- 64 shift))
                             (low (floor word (expt 2 shift))) (high -1)))
            :in-theory (disable boymoo-model::a64-ror (:definition boymoo-model::a64-ones))
            :cases ((equal shift 1) (logbitp 63 word))))
   :rule-classes nil))

(defund proof-number-arithmetic-right-instruction (dest source shift)
  (list :bitfield 0 64 dest source shift 63 (boymoo-model::a64-ones 64)
        (boymoo-model::a64-ones (- 64 shift))))

(local
 (defthm read-value-register
   (equal (boymoo-model::a64-read-reg register 64 nil machine) (proof-reg register machine))
   :hints (("Goal" :in-theory (enable proof-reg)))))

(defthm proof-number-execute-arithmetic-right
  (implies (member-equal shift '(1 63))
           (equal (proof-execute (proof-number-arithmetic-right-instruction dest source shift) machine)
                  (boymoo-model::a64-write-reg
                   dest 64 nil (ash (boymoo-model::a64-signed 64 (proof-reg source machine)) (- shift))
                   (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine))))
  :hints (("Goal"
           :use ((:instance arithmetic-bitfield-signed-shift (word (proof-reg source machine))))
           :in-theory (e/d (proof-execute proof-number-arithmetic-right-instruction)
                           (boymoo-model::a64-ror (:definition boymoo-model::a64-ones)))
           :do-not-induct t)))

(local
 (defthm signed-high-word-in-range
   (implies (and (integerp product)
                 (<= (- (expt 2 126)) product) (<= product (expt 2 126)))
            (signed-byte-p 64 (floor product (expt 2 64))))
   :hints (("Goal"
            :use ((:instance proof-number-positive-divisor-floor-bounds
                             (a product) (b (expt 2 64))))))
   :rule-classes nil))

(local
 (defthm encoding-equality-for-signed-words
   (implies (and (signed-byte-p 64 a) (signed-byte-p 64 b))
            (equal (equal (boymoo-model::a64-unsigned 64 a) (boymoo-model::a64-unsigned 64 b))
                   (equal a b)))
   :hints (("Goal"
            :use ((:instance proof-number-a64-signed-after-unsigned (width 64) (a a))
                  (:instance proof-number-a64-signed-after-unsigned (width 64) (a b)))
            :in-theory (disable proof-number-a64-signed-after-unsigned)
            :cases ((equal a b))))
   :rule-classes nil))

(defthm proof-number-multiply-high-tests-signed-range
  (let* ((low (boymoo-model::a64-unsigned 64 product))
         (high (floor product (expt 2 64)))
         (sign (if (< low (expt 2 63)) 0 -1)))
    (implies (and (integerp product)
                  (<= (- (expt 2 126)) product) (<= product (expt 2 126)))
             (equal (equal (boymoo-model::a64-unsigned 64 high)
                           (boymoo-model::a64-unsigned 64 sign))
                    (signed-byte-p 64 product))))
  :hints (("Goal"
           :use (signed-high-word-in-range
                 (:instance proof-number-quotient-and-remainder (a product) (b (expt 2 64)))
                 (:instance proof-number-a64-unsigned-is-modulo (width 64) (a product))
                 (:instance encoding-equality-for-signed-words
                            (a (floor product (expt 2 64)))
                            (b (if (< (boymoo-model::a64-unsigned 64 product) (expt 2 63)) 0 -1))))
           :cases ((equal (floor product (expt 2 64)) 0)
                   (equal (floor product (expt 2 64)) -1))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm signed-word-most-significant-bit
   (implies (unsigned-byte-p 64 word)
            (equal (ash (boymoo-model::a64-signed 64 word) -63)
                   (if (< word (expt 2 63)) 0 -1)))
   :hints (("Goal"
            :use ((:instance proof-number-a64-signed-value (width 64) (a word))
                  (:instance proof-number-floor-with-remainder
                             (a word) (b (expt 2 63)) (q 0))
                  (:instance proof-number-floor-with-remainder
                             (a (- word (expt 2 64))) (b (expt 2 63)) (q -1)))
            :cases ((< word (expt 2 63)))))
   :rule-classes nil))

(local
 (defthm product-with-opposite-sign
   (implies (and (rationalp x) (rationalp y))
            (and (equal (* x (- y)) (- (* x y)))
                 (equal (* (- x) y) (- (* x y)))))
   :hints (("Goal"
            :use ((:instance acl2::distributivity (acl2::x x) (acl2::y y) (acl2::z (- y)))
                  (:instance acl2::distributivity (acl2::x y) (acl2::y x) (acl2::z (- x))))
            :in-theory (disable acl2::distributivity)))))

(local
 (defthm nonnegative-product-bounds
   (implies (and (rationalp x) (rationalp y) (rationalp x-limit) (rationalp y-limit)
                 (<= 0 x) (<= x x-limit) (<= 0 y) (<= y y-limit))
            (and (<= 0 (* x y)) (<= (* x y) (* x-limit y-limit))))
   :hints (("Goal"
            :use ((:instance acl2::positive (acl2::x x) (acl2::y y))
                  (:instance acl2::positive (acl2::x x-limit) (acl2::y y-limit))
                  (:instance proof-number-scale-less (a x-limit) (b x) (c y))
                  (:instance proof-number-scale-less (a y-limit) (b y) (c x-limit)))
            :cases ((equal x 0) (equal y 0) (equal x-limit 0))))
   :rule-classes nil))

(local
 (defthm double-factor-order
   (equal (* a 2 b) (* 2 a b))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-* (acl2::x a) (acl2::y 2) (acl2::z b))
                  (:instance acl2::associativity-of-* (acl2::x 2) (acl2::y a) (acl2::z b)))
            :in-theory (disable acl2::associativity-of-*)))
   :rule-classes nil))

(local
 (defthm product-of-immediate-operands-is-bounded
   (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b))
            (and (<= (- (expt 2 126)) (* a 2 b)) (<= (* a 2 b) (expt 2 126))))
   :hints (("Goal"
            :use (double-factor-order
                  (:instance nonnegative-product-bounds
                             (x (abs a)) (y (abs (* 2 b)))
                             (x-limit (expt 2 62)) (y-limit (expt 2 63))))
            :cases ((< a 0) (< b 0))))
   :rule-classes nil))

(local
 (defthm twice-product-fits-signed-word
   (implies (and (integerp a) (integerp b))
            (equal (signed-byte-p 64 (* a 2 b)) (proof-immediate-integer-p (* a b))))
   :hints (("Goal"
            :use double-factor-order
            :cases ((proof-immediate-integer-p (* a b)))))))

(local
 (defthm signed-word-bit-pattern
   (implies (signed-byte-p 64 value)
            (equal (boymoo-model::a64-unsigned 64 value)
                   (if (< value 0) (+ (expt 2 64) value) value)))
   :hints (("Goal"
            :use ((:instance proof-number-a64-unsigned-is-modulo (width 64) (a value))
                  (:instance proof-number-mod-with-remainder
                             (a value) (b (expt 2 64)) (q -1) (r (+ (expt 2 64) value))))
            :cases ((< value 0))))
   :rule-classes nil))

(local
 (defthm signed-and-unsigned-products-have-same-low-word
   (implies (and (signed-byte-p 64 a) (signed-byte-p 64 b))
            (equal (boymoo-model::a64-unsigned 64 (* (boymoo-model::a64-unsigned 64 a)
                                                     (boymoo-model::a64-unsigned 64 b)))
                   (boymoo-model::a64-unsigned 64 (* a b))))
   :hints (("Goal"
            :use ((:instance signed-word-bit-pattern (value a))
                  (:instance signed-word-bit-pattern (value b))
                  (:instance unsigned-word-over-period (width 64) (x (* a b))
                             (periods (+ (if (< a 0) b 0) (if (< b 0) a 0)
                                         (if (and (< a 0) (< b 0)) (expt 2 64) 0)))))
            :cases ((< a 0) (< b 0))))
   :rule-classes nil))

(local
 (defthm add-one-through-word-mask
   (implies (integerp value)
            (equal (boymoo-model::a64-unsigned 64 (+ 1 (boymoo-model::a64-unsigned 64 value)))
                   (boymoo-model::a64-unsigned 64 (+ 1 value))))
   :hints (("Goal"
            :use ((:instance proof-number-a64-unsigned-is-modulo (width 64) (a value))
                  (:instance proof-number-quotient-and-remainder (a value) (b (expt 2 64)))
                  (:instance unsigned-word-over-period (width 64)
                             (x (+ 1 (boymoo-model::a64-unsigned 64 value)))
                             (periods (floor value (expt 2 64)))))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm remove-tag-by-shift
   (implies (proof-immediate-integer-p value)
            (equal (ash (+ 1 (* 2 value)) -1) value))
   :hints (("Goal"
            :use ((:instance proof-number-floor-with-remainder
                             (a (+ 1 (* 2 value))) (b 2) (q value)))))))

(local
 (defthm remove-tag-by-subtracting-one
   (implies (proof-immediate-integer-p value)
            (equal (boymoo-model::a64-unsigned 64 (- (proof-integer-word value) 1))
                   (boymoo-model::a64-unsigned 64 (* 2 value))))
   :hints (("Goal"
            :use ((:instance unsigned-word-over-period (width 64) (x (* 2 value)) (periods 1)))
            :in-theory (disable proof-integer-word)
            :cases ((< value 0))))))

(local
 (defthm immediate-multiplication-words
   (let* ((left (boymoo-model::a64-unsigned 64 a))
          (right (boymoo-model::a64-unsigned 64 (* 2 b)))
          (low (boymoo-model::a64-unsigned 64 (* left right)))
          (high (boymoo-model::a64-unsigned
                 64 (ash (* (boymoo-model::a64-signed 64 left)
                            (boymoo-model::a64-signed 64 right)) -64)))
          (sign (boymoo-model::a64-unsigned 64 (ash (boymoo-model::a64-signed 64 low) -63))))
     (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b))
              (and (equal (equal high sign) (proof-immediate-integer-p (* a b)))
                   (equal (boymoo-model::a64-unsigned 64 (+ 1 low))
                          (proof-integer-word (* a b))))))
   :hints (("Goal"
            :use (product-of-immediate-operands-is-bounded double-factor-order
                  (:instance signed-and-unsigned-products-have-same-low-word (b (* 2 b)))
                  (:instance signed-word-most-significant-bit
                             (word (boymoo-model::a64-unsigned 64 (* a 2 b))))
                  (:instance proof-number-multiply-high-tests-signed-range (product (* a 2 b)))
                  (:instance add-one-through-word-mask (value (* a 2 b))))
            :in-theory (e/d (proof-integer-word)
                            (proof-number-immediate-word-bits proof-number-a64-unsigned-in-range))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm execute-multiply-low
   (equal (proof-execute (list :multiply dest left right) machine)
          (boymoo-model::a64-write-reg
           dest 64 nil (* (proof-reg left machine) (proof-reg right machine))
           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
   :hints (("Goal" :in-theory (enable proof-execute)))))

(local
 (defthm execute-multiply-high
   (equal (proof-execute (list :signed-multiply-high dest left right) machine)
          (boymoo-model::a64-write-reg
           dest 64 nil
           (ash (* (boymoo-model::a64-signed 64 (proof-reg left machine))
                   (boymoo-model::a64-signed 64 (proof-reg right machine))) -64)
           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
   :hints (("Goal" :in-theory (enable proof-execute)))))

(defund proof-number-immediate-multiply-instructions (pc overflow)
  (list (proof-number-arithmetic-right-instruction 2 0 1)
        '(:arithmetic-imm 2 64 3 1 1)
        '(:signed-multiply-high 4 2 3)
        '(:multiply 2 2 3)
        (proof-number-arithmetic-right-instruction 3 2 63)
        '(:arithmetic-reg 3 64 31 4 3 0 0)
        (list :branch-cond (- overflow (+ 24 pc)) 1)
        '(:arithmetic-imm 0 64 0 2 1)
        '(:branch-reg 30 nil)))

(defthm proof-number-immediate-multiply-decoding
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (let* ((entry (+ 12 (boymoo-compiler::a64-offset "prim:ACL2::BINARY-*" labels)))
           (overflow (boymoo-compiler::a64-offset "rt:z-multiply-op" labels))
           (items (take 9 (nthcdr 4 (proof-number-code-at-label
                                    "prim:ACL2::BINARY-*" (boymoo-compiler::runtime-primitive-code))))))
      (equal (proof-number-decode-items items entry labels)
             (proof-number-immediate-multiply-instructions entry overflow))))
  :rule-classes nil)

(defthm proof-number-immediate-multiply-returns-or-delegates
  (let* ((machine (proof-world-machine world))
         (pc (proof-world-pc world))
         (link (proof-world-reg 30 world))
         (product (* a b))
         (fits (proof-immediate-integer-p product))
         (count (if fits 9 7))
         (target (if fits link overflow))
         (path (take count (proof-number-immediate-multiply-instructions pc overflow)))
         (after (proof-number-execute-block path world)))
    (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b)
                  (equal (proof-world-reg 0 world) (proof-integer-word a))
                  (equal (proof-world-reg 1 world) (proof-integer-word b))
                  (unsigned-byte-p 64 (+ 32 pc)) (unsigned-byte-p 64 overflow)
                  (not (eq (car machine) :svc))
                  (proof-number-checked-block-p path (list target) world))
             (and (proof-segment-p count (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 0 after)
                         (if fits (proof-integer-word product) (proof-world-reg 0 world)))
                  (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use (immediate-multiplication-words
                 (:instance proof-number-checked-block-segment
                            (instructions (take (if (proof-immediate-integer-p (* a b)) 9 7)
                                                (proof-number-immediate-multiply-instructions
                                                 (proof-world-pc world) overflow)))
                            (cuts (list (if (proof-immediate-integer-p (* a b))
                                            (proof-world-reg 30 world) overflow)))))
           :in-theory (e/d (proof-number-immediate-multiply-instructions proof-world-reg
                            proof-world-pc proof-heap-base)
                           (proof-integer-word proof-number-immediate-word-bits
                            proof-immediate-integer-p floor-of-power-of-two-quotient
                            proof-number-a64-signed-after-unsigned
                            (:executable-counterpart proof-number-arithmetic-right-instruction)))
           :cases ((proof-immediate-integer-p (* a b)))
           :do-not-induct t))
  :rule-classes nil)
