(in-package "BOYMOO-PROOFS")

(include-book "immediate")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-execute proof-instruction-effect
                     proof-segment-p proof-number-checked-block-p proof-number-exact-prefix-p
                     proof-world-machine proof-world-stop proof-reg proof-load-word
                     proof-instruction-at-p proof-instruction-access-p proof-world-reg
                     proof-world-pc proof-heap-base proof-reg-value-p
                     boymoo-model::a64-unsigned boymoo-model::a64-signed boymoo-model::a64-memory
                     boymoo-model::a64-read-reg boymoo-model::a64-write-reg boymoo-model::a64-set-pc
                     boymoo-model::a64-pc boymoo-model::a64-sp boymoo-model::a64-set-nzcv
                     boymoo-model::a64-condition boymoo-model::a64-nzcv boymoo-model::a64-result-flags
                     (:definition update-nth) (:definition nth)
                     acl2::binary-logxor acl2::binary-logand logbitp mod floor ash)))

(local
 (defthm word-wrap-is-periodic
   (implies (and (integerp x) (integerp periods))
            (equal (boymoo-model::a64-unsigned 64 (+ x (* (expt 2 64) periods)))
                   (boymoo-model::a64-unsigned 64 x)))
   :hints (("Goal"
            :use ((:instance proof-number-mod-shift-by-multiple
                             (a x) (b (expt 2 64)) (times periods))
                  (:instance proof-number-a64-unsigned-is-modulo (width 64) (a x))
                  (:instance proof-number-a64-unsigned-is-modulo (width 64)
                             (a (+ x (* (expt 2 64) periods)))))))
   :rule-classes nil))

(local
 (defthm word-as-signed-value-is-in-range
   (implies (unsigned-byte-p 64 word)
            (signed-byte-p 64 (boymoo-model::a64-signed 64 word)))
   :hints (("Goal"
            :use ((:instance proof-number-a64-signed-value (width 64) (a word)))))
   :rule-classes nil))

(defund proof-number-signed-word-sum (subtract left right)
  (+ (boymoo-model::a64-signed 64 left)
     (if subtract (- (boymoo-model::a64-signed 64 right)) (boymoo-model::a64-signed 64 right))))

(defund proof-number-word-sum (subtract left right)
  (+ left (if subtract (- right) right)))

(local
 (defthm signed-and-unsigned-sums-have-same-bits
   (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
            (equal (boymoo-model::a64-unsigned 64 (proof-number-word-sum subtract left right))
                   (boymoo-model::a64-unsigned 64 (proof-number-signed-word-sum subtract left right))))
   :hints (("Goal"
            :use ((:instance proof-number-a64-signed-value (width 64) (a left))
                  (:instance proof-number-a64-signed-value (width 64) (a right))
                  (:instance word-wrap-is-periodic
                             (x (proof-number-signed-word-sum subtract left right))
                             (periods (+ (if (< left (expt 2 63)) 0 1)
                                         (if (< right (expt 2 63)) 0 (if subtract -1 1))))))
            :in-theory (enable proof-number-signed-word-sum proof-number-word-sum)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm signed-result-fits-exactly-when-unwrapped
   (implies (integerp result)
            (equal (equal (boymoo-model::a64-signed 64 (boymoo-model::a64-unsigned 64 result)) result)
                   (signed-byte-p 64 result)))
   :hints (("Goal"
            :use ((:instance proof-number-a64-signed-after-unsigned (width 64) (a result))
                  (:instance word-as-signed-value-is-in-range (word (boymoo-model::a64-unsigned 64 result))))
            :cases ((signed-byte-p 64 result))))
   :rule-classes nil))

(local
 (defthm subtract-with-complement-bits
   (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
            (equal (boymoo-model::a64-unsigned 64 (+ left (logxor right (boymoo-model::a64-ones 64)) 1))
                   (boymoo-model::a64-unsigned 64 (- left right))))
   :hints (("Goal"
            :use ((:instance proof-number-xor-of-word-and-mask (width 64) (a right))
                  (:instance word-wrap-is-periodic (x (- left right)) (periods 1)))
            :in-theory (disable boymoo-model::a64-ones)))))

(defund proof-number-addition-flags (left right)
  (let* ((sum (+ left right))
         (bits (boymoo-model::a64-unsigned 64 sum))
         (signed (proof-number-signed-word-sum nil left right)))
    (boymoo-model::a64-unsigned 4
     (boymoo-model::a64-result-flags 64 bits (logbitp 64 sum)
                                    (not (equal signed (boymoo-model::a64-signed 64 bits)))))))

(defthm proof-number-arithmetic-overflow-condition
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (equal (boymoo-model::a64-condition
                   6 (if subtract (proof-number-subtraction-flags left right)
                       (proof-number-addition-flags left right)))
                  (not (signed-byte-p 64 (proof-number-signed-word-sum subtract left right)))))
  :hints (("Goal"
           :use (signed-and-unsigned-sums-have-same-bits subtract-with-complement-bits
                 (:instance signed-result-fits-exactly-when-unwrapped
                            (result (proof-number-signed-word-sum subtract left right))))
           :in-theory (e/d (proof-number-addition-flags proof-number-subtraction-flags
                            proof-number-signed-word-sum proof-number-word-sum)
                           (proof-number-a64-signed-after-unsigned subtract-with-complement-bits))
           :cases ((not subtract))))
  :rule-classes nil)

(local
 (defthm read-value-register
   (equal (boymoo-model::a64-read-reg register 64 nil machine) (proof-reg register machine))
   :hints (("Goal" :in-theory (enable proof-reg)))))

(local
 (defthm execute-add-or-subtract-with-flags
   (let* ((left (proof-reg left-register machine))
          (right (proof-reg right-register machine))
          (bits (boymoo-model::a64-unsigned 64 (proof-number-word-sum subtract left right)))
          (flags (if subtract (proof-number-subtraction-flags left right)
                   (proof-number-addition-flags left right))))
     (equal (proof-execute (list :arithmetic-reg (if subtract 3 1) 64 dest
                                 left-register right-register 0 0) machine)
            (boymoo-model::a64-set-nzcv
             flags (boymoo-model::a64-write-reg
                    dest 64 nil bits
                    (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))))
   :hints (("Goal"
            :use ((:instance subtract-with-complement-bits
                             (left (proof-reg left-register machine))
                             (right (proof-reg right-register machine))))
            :in-theory (e/d (proof-execute proof-number-addition-flags proof-number-subtraction-flags
                             proof-number-signed-word-sum proof-number-word-sum)
                            (subtract-with-complement-bits))
            :cases ((not subtract))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm execute-register-add-with-flags
   (let ((left (proof-reg left-register machine))
         (right (proof-reg right-register machine)))
     (equal (proof-execute (list :arithmetic-reg 1 64 dest left-register right-register 0 0) machine)
            (boymoo-model::a64-set-nzcv
             (proof-number-addition-flags left right)
             (boymoo-model::a64-write-reg
              dest 64 nil (boymoo-model::a64-unsigned 64 (proof-number-word-sum nil left right))
              (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))))
   :hints (("Goal" :use ((:instance execute-add-or-subtract-with-flags (subtract nil)))))))

(local
 (defthm execute-register-subtract-with-flags
   (let ((left (proof-reg left-register machine))
         (right (proof-reg right-register machine)))
     (equal (proof-execute (list :arithmetic-reg 3 64 dest left-register right-register 0 0) machine)
            (boymoo-model::a64-set-nzcv
             (proof-number-subtraction-flags left right)
             (boymoo-model::a64-write-reg
              dest 64 nil (boymoo-model::a64-unsigned 64 (proof-number-word-sum t left right))
              (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))))
   :hints (("Goal" :use ((:instance execute-add-or-subtract-with-flags (subtract t)))))))

(local
 (defthm addition-flags-fit
   (unsigned-byte-p 4 (proof-number-addition-flags left right))
   :hints (("Goal" :in-theory (e/d (proof-number-addition-flags)
                                    (proof-number-a64-unsigned-in-range))))))

(local
 (defthm signed-tag-cleared-value
   (implies (proof-immediate-integer-p value)
            (equal (boymoo-model::a64-signed
                    64 (boymoo-model::a64-unsigned 64 (1- (proof-integer-word value))))
                   (* 2 value)))
   :hints (("Goal"
            :use ((:instance word-wrap-is-periodic (x (* 2 value)) (periods 1))
                  (:instance proof-number-a64-signed-after-unsigned (width 64) (a (* 2 value))))
            :in-theory (disable proof-integer-word proof-number-a64-signed-after-unsigned)
            :cases ((< value 0))))
   :rule-classes nil))

(local
 (defthm signed-tag-fits-immediate-range
   (implies (integerp value)
            (equal (signed-byte-p 64 (+ 1 (* 2 value))) (proof-immediate-integer-p value)))
   :hints (("Goal" :cases ((proof-immediate-integer-p value))))))

(local
 (defthm negative-double
   (implies (integerp value)
            (equal (* 2 (- value)) (- (* 2 value))))
   :hints (("Goal"
            :use ((:instance acl2::distributivity
                             (acl2::x 2) (acl2::y value) (acl2::z (- value))))
            :in-theory (disable acl2::distributivity)))))

(local
 (defthm add-negate-bits-and-overflow
   (let* ((left (if negate 2 (proof-integer-word a)))
          (right (if negate (proof-integer-word a)
                   (boymoo-model::a64-unsigned 64 (1- (proof-integer-word b)))))
          (result (if negate (- a) (+ a b)))
          (flags (if negate (proof-number-subtraction-flags left right)
                   (proof-number-addition-flags left right))))
     (implies (and (proof-immediate-integer-p a) (or negate (proof-immediate-integer-p b)))
              (and (equal (boymoo-model::a64-unsigned 64 (proof-number-word-sum negate left right))
                          (proof-integer-word result))
                   (equal (boymoo-model::a64-condition 6 flags)
                          (not (proof-immediate-integer-p result))))))
   :hints (("Goal"
            :use ((:instance signed-tag-cleared-value (value b))
                  (:instance signed-and-unsigned-sums-have-same-bits (subtract negate)
                             (left (if negate 2 (proof-integer-word a)))
                             (right (if negate (proof-integer-word a)
                                      (boymoo-model::a64-unsigned 64 (1- (proof-integer-word b))))))
                  (:instance proof-number-arithmetic-overflow-condition (subtract negate)
                             (left (if negate 2 (proof-integer-word a)))
                             (right (if negate (proof-integer-word a)
                                      (boymoo-model::a64-unsigned 64 (1- (proof-integer-word b)))))))
            :in-theory (e/d (proof-number-signed-word-sum proof-integer-word)
                            (proof-number-immediate-word-bits proof-number-a64-unsigned-in-range))
            :cases ((not negate))
            :do-not-induct t))
   :rule-classes nil))

(defund proof-number-add-negate-instructions (negate entry overflow)
  (append (if negate
              '((:move-wide 2 64 2 2 0) (:arithmetic-reg 3 64 2 2 0 0 0))
            '((:arithmetic-imm 2 64 2 1 1) (:arithmetic-reg 1 64 2 0 2 0 0)))
          (list (list :branch-cond (- overflow (+ entry 8)) 6)
                '(:logical-reg 1 64 0 31 2 0 0 nil)
                '(:branch-reg 30 nil))))

(defun proof-number-add-negate-decode-p (negate labels)
  (let* ((name (if negate "prim:ACL2::UNARY--" "prim:ACL2::BINARY-+"))
         (gate (if negate 2 3))
         (entry (+ (* 4 gate) (boymoo-compiler::a64-offset name labels)))
         (overflow (boymoo-compiler::a64-offset
                    (if negate "rt:z-negate-op" "rt:z-add-op") labels))
         (items (take 5 (nthcdr (1+ gate) (proof-number-code-at-label
                                           name (boymoo-compiler::runtime-primitive-code))))))
    (equal (proof-number-decode-items items entry labels)
           (proof-number-add-negate-instructions negate entry overflow))))

(defthm proof-number-add-negate-decoding
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (and (proof-number-add-negate-decode-p nil labels)
         (proof-number-add-negate-decode-p t labels)))
  :rule-classes nil)

(defthm proof-number-immediate-add-negate-returns-or-delegates
  (let* ((machine (proof-world-machine world))
         (entry (proof-world-pc world))
         (link (proof-world-reg 30 world))
         (result (if negate (- a) (+ a b)))
         (fits (proof-immediate-integer-p result))
         (target (if fits link overflow))
         (count (if fits 5 3))
         (path (take count (proof-number-add-negate-instructions negate entry overflow)))
         (after (proof-number-execute-block path world)))
    (implies (and (proof-immediate-integer-p a)
                  (or negate (proof-immediate-integer-p b))
                  (equal (proof-world-reg 0 world) (proof-integer-word a))
                  (or negate (equal (proof-world-reg 1 world) (proof-integer-word b)))
                  (unsigned-byte-p 64 (+ 16 entry))
                  (unsigned-byte-p 64 overflow)
                  (not (eq (car machine) :svc))
                  (proof-number-checked-block-p path (list target) world))
             (and (proof-segment-p count (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 0 after)
                         (if fits (proof-integer-word result) (proof-world-reg 0 world)))
                  (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :use ((:instance add-negate-bits-and-overflow (negate nil))
                 (:instance add-negate-bits-and-overflow (negate t))
                 (:instance proof-number-checked-block-segment
                            (instructions (take (if (proof-immediate-integer-p (if negate (- a) (+ a b))) 5 3)
                                                (proof-number-add-negate-instructions
                                                 negate (proof-world-pc world) overflow)))
                            (cuts (list (if (proof-immediate-integer-p (if negate (- a) (+ a b)))
                                            (proof-world-reg 30 world) overflow)))))
           :in-theory (e/d (proof-number-add-negate-instructions proof-world-reg proof-world-pc proof-heap-base)
                           (proof-integer-word proof-number-immediate-word-bits proof-immediate-integer-p))
           :cases ((not negate))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm unsigned-result-within-one-period
   (implies (and (integerp value) (<= (- (expt 2 64)) value) (< value (expt 2 64)))
            (equal (boymoo-model::a64-unsigned 64 value)
                   (if (< value 0) (+ (expt 2 64) value) value)))
   :hints (("Goal"
            :use ((:instance proof-number-a64-unsigned-is-modulo (width 64) (a value))
                  (:instance proof-number-mod-with-remainder
                             (a value) (b (expt 2 64)) (q -1) (r (+ (expt 2 64) value))))
            :cases ((< value 0))))
   :rule-classes nil))

(local
 (defthm addition-negative-condition
   (let ((sum (proof-number-signed-word-sum nil left right)))
     (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
              (equal (boymoo-model::a64-condition 11 (proof-number-addition-flags left right))
                     (< sum 0))))
   :hints (("Goal"
            :use ((:instance signed-and-unsigned-sums-have-same-bits (subtract nil))
                  (:instance word-as-signed-value-is-in-range (word left))
                  (:instance word-as-signed-value-is-in-range (word right))
                  (:instance unsigned-result-within-one-period
                             (value (proof-number-signed-word-sum nil left right)))
                  (:instance proof-number-sign-bit (width 64)
                             (a (boymoo-model::a64-unsigned 64
                                                           (proof-number-signed-word-sum nil left right))))
                  (:instance signed-result-fits-exactly-when-unwrapped
                             (result (proof-number-signed-word-sum nil left right))))
            :in-theory (e/d (proof-number-addition-flags proof-number-word-sum proof-number-signed-word-sum)
                            (proof-number-a64-signed-after-unsigned))
            :cases ((< (proof-number-signed-word-sum nil left right) 0))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm immediate-reciprocal-conditions
   (implies (proof-immediate-integer-p a)
            (let ((word (proof-integer-word a)))
              (and (equal (boymoo-model::a64-condition 11 (proof-number-addition-flags word 1))
                          (< a -1))
                   (equal (boymoo-model::a64-condition 12 (proof-number-subtraction-flags word 3))
                          (< 1 a)))))
   :hints (("Goal"
            :use ((:instance addition-negative-condition (left (proof-integer-word a)) (right 1))
                  (:instance proof-number-subtraction-conditions (left (proof-integer-word a)) (right 3)))
            :in-theory (e/d (proof-number-signed-word-sum)
                            (proof-integer-word proof-number-immediate-word-bits))
            :cases ((< a -1) (< 1 a))))
   :rule-classes nil))

(local
 (defthm execute-compare-plus-one
   (equal (proof-execute '(:arithmetic-imm 1 64 31 0 1) machine)
          (boymoo-model::a64-set-nzcv
           (proof-number-addition-flags (proof-reg 0 machine) 1)
           (boymoo-model::a64-set-pc (+ 4 (boymoo-model::a64-pc machine)) machine)))
   :hints (("Goal"
            :in-theory (enable proof-execute proof-number-addition-flags proof-number-signed-word-sum
                               boymoo-model::a64-write-reg)))))

(defund proof-number-immediate-reciprocal-instructions (entry general)
  (list '(:arithmetic-imm 1 64 31 0 1)
        (list :branch-cond (- general (+ 4 entry)) 11)
        '(:arithmetic-imm 3 64 31 0 3)
        (list :branch-cond (- general (+ 12 entry)) 12)
        '(:branch-reg 30 nil)))

(defthm proof-number-immediate-reciprocal-decoding
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (let* ((entry (+ 8 (boymoo-compiler::a64-offset "prim:ACL2::UNARY-/" labels)))
           (general (boymoo-compiler::a64-offset "rt:q-reciprocal" labels))
           (items (take 5 (nthcdr 3 (proof-number-code-at-label
                                    "prim:ACL2::UNARY-/" (boymoo-compiler::runtime-primitive-code))))))
      (equal (proof-number-decode-items items entry labels)
             (proof-number-immediate-reciprocal-instructions entry general))))
  :rule-classes nil)

(defthm proof-number-immediate-reciprocal-returns-or-delegates
  (let* ((machine (proof-world-machine world))
         (pc (proof-world-pc world))
         (count (cond ((< a -1) 2) ((< 1 a) 4) (t 5)))
         (target (if (equal count 5) (proof-world-reg 30 world) general))
         (code (take count (proof-number-immediate-reciprocal-instructions pc general)))
         (after (proof-number-execute-block code world)))
    (implies (and (proof-immediate-integer-p a)
                  (equal (proof-world-reg 0 world) (proof-integer-word a))
                  (unsigned-byte-p 64 (+ 16 pc)) (unsigned-byte-p 64 general)
                  (not (eq (car machine) :svc))
                  (proof-number-checked-block-p code (list target) world))
             (and (proof-segment-p count (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg register after) (proof-world-reg register world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine))
                  (implies (equal count 5) (equal (/ a) a)))))
  :hints (("Goal"
           :use (immediate-reciprocal-conditions
                 (:instance proof-number-checked-block-segment
                            (instructions (take (cond ((< a -1) 2) ((< 1 a) 4) (t 5))
                                                (proof-number-immediate-reciprocal-instructions
                                                 (proof-world-pc world) general)))
                            (cuts (list (if (or (< a -1) (< 1 a)) general (proof-world-reg 30 world))))))
           :in-theory (e/d (proof-number-immediate-reciprocal-instructions proof-world-reg proof-world-pc)
                           (proof-integer-word proof-number-immediate-word-bits))
           :cases ((< a -1) (< 1 a) (equal a -1) (equal a 0) (equal a 1))
           :do-not-induct t))
  :rule-classes nil)
