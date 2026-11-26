(in-package "BOYMOO-PROOFS")

(include-book "comparisons")
(include-book "views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-reg proof-world-pc proof-world-machine proof-reg
                    proof-instruction-effect proof-execute proof-linux-svc
                    boymoo-model::a64-execute boymoo-model::a64-result-flags
                    boymoo-model::a64-condition boymoo-model::a64-unsigned
                    boymoo-model::a64-signed logbitp expt mod floor))

(defthm generated-signed-64-of-unsigned
  (equal (boymoo-model::a64-signed 64 (boymoo-model::a64-unsigned 64 x))
         (boymoo-model::a64-signed 64 x))
  :hints (("Goal" :in-theory (enable generated-signed-64-of-word))))

(defthm generated-signed-64-equals-input-when-in-range
  (equal (equal (boymoo-model::a64-signed 64 x) x) (signed-byte-p 64 x))
  :hints (("Goal" :use generated-signed-64-of-signed-range
                  :in-theory (e/d (generated-signed-64-of-word signed-byte-p)
                                  (generated-signed-64-of-signed-range)))))

(local
 (defthm generated-double-negative
   (equal (- (- x)) (fix x))
   :hints (("Goal" :use (:instance inverse-of-+ (acl2::x (- x)))))))

(local
 (defthm generated-unsigned-64-add-normalized-word
   (implies (and (integerp left) (integerp right))
            (equal (boymoo-model::a64-unsigned 64
                                              (+ left (boymoo-model::a64-unsigned 64 right)))
                   (boymoo-model::a64-unsigned 64 (+ left right))))
   :hints (("Goal"
            :use ((:instance generated-unsigned-as-mod (n 64) (x right))
                  (:instance generated-unsigned-add-multiple (n 64) (x (+ left right))
                             (q (- (floor right #x10000000000000000)))))
            :in-theory (e/d (mod) (generated-unsigned-add-multiple))))))

(local
 (defthm generated-subtract-congruent-representatives
   (implies (and (integerp left) (integerp right) (integerp q)
                 (equal encoded (+ right (- (* #x10000000000000000 q)))))
            (equal (boymoo-model::a64-unsigned 64 (- left encoded))
                   (boymoo-model::a64-unsigned 64 (- left right))))
   :hints (("Goal"
            :use (:instance generated-unsigned-add-multiple (n 64) (x (- left right)))
            :in-theory (disable generated-unsigned-add-multiple)))
   :rule-classes nil))

(local
 (defthm generated-unsigned-64-subtract-normalized-word
   (implies (and (integerp left) (integerp right))
            (equal (boymoo-model::a64-unsigned 64
                                              (- left (boymoo-model::a64-unsigned 64 right)))
                   (boymoo-model::a64-unsigned 64 (- left right))))
   :hints (("Goal"
            :use ((:instance generated-unsigned-as-mod (n 64) (x right))
                  (:instance generated-subtract-congruent-representatives
                             (encoded (boymoo-model::a64-unsigned 64 right))
                             (q (floor right #x10000000000000000))))
            :in-theory (enable mod)))))

(local
 (defthm generated-encoded-integer-minus-tag
   (implies (integerp y)
            (equal (boymoo-model::a64-unsigned 64 (1- (proof-integer-word y)))
                   (boymoo-model::a64-unsigned 64 (* 2 y))))
   :hints (("Goal"
            :use (:instance generated-unsigned-64-add-normalized-word (left -1) (right (1+ (* 2 y))))
            :in-theory (disable generated-unsigned-64-add-normalized-word)))))

(local
 (defthm generated-encoded-addition
   (implies (and (integerp x) (integerp y))
            (equal (boymoo-model::a64-unsigned 64
                     (+ (proof-integer-word x) (boymoo-model::a64-unsigned 64 (* 2 y))))
                   (proof-integer-word (+ x y))))
   :hints (("Goal"
            :use ((:instance generated-unsigned-64-add-normalized-word
                             (left (proof-integer-word x)) (right (* 2 y)))
                  (:instance generated-unsigned-64-add-normalized-word
                             (left (* 2 y)) (right (1+ (* 2 x)))))
            :in-theory (disable generated-unsigned-64-add-normalized-word)))))

(local
 (defthm generated-two-times-immediate-is-signed-64
   (implies (proof-immediate-integer-p y)
            (equal (boymoo-model::a64-signed 64 (* 2 y)) (* 2 y)))))

(local
 (defthm generated-signed-normalized-immediate-payload
   (implies (proof-immediate-integer-p y)
            (equal (boymoo-model::a64-signed 64 (boymoo-model::a64-unsigned 64 (* 2 y)))
                   (* 2 y)))))

(local
 (defthm generated-immediate-tag-fits-exactly
   (implies (integerp x)
            (equal (signed-byte-p 64 (1+ (* 2 x))) (proof-immediate-integer-p x)))
   :hints (("Goal" :use ((:instance generated-integer-step (y (expt 2 62)))
                         (:instance generated-integer-step (y (- (expt 2 62)))))))))

(local
 (defthm generated-immediate-integer-type
   (implies (proof-immediate-integer-p x) (integerp x))
   :rule-classes :forward-chaining))

(local
 (defthm generated-immediate-encoding-decodes-exactly-if-fits
   (implies (integerp value)
            (equal (equal (boymoo-model::a64-signed 64 (proof-integer-word value)) (1+ (* 2 value)))
                   (proof-immediate-integer-p value)))
   :hints (("Goal" :in-theory (disable proof-immediate-integer-p)))))

(defund generated-add-flags (left right)
  (let* ((sum (+ left right))
         (bits (boymoo-model::a64-unsigned 64 sum)))
    (boymoo-model::a64-result-flags
     64 bits (logbitp 64 sum)
     (not (equal (+ (boymoo-model::a64-signed 64 left) (boymoo-model::a64-signed 64 right))
                 (boymoo-model::a64-signed 64 bits))))))

(defthm generated-fast-addition-word-and-overflow
  (let* ((left (proof-integer-word x))
         (right (boymoo-model::a64-unsigned 64 (1- (proof-integer-word y))))
         (result (boymoo-model::a64-unsigned 64 (+ left right)))
         (flags (generated-add-flags left right)))
    (implies (and (proof-immediate-integer-p x) (proof-immediate-integer-p y))
             (and (equal result (proof-integer-word (+ x y)))
                  (equal (boymoo-model::a64-condition 6 (boymoo-model::a64-unsigned 4 flags))
                         (not (proof-immediate-integer-p (+ x y)))))))
  :hints (("Goal" :use (:instance generated-immediate-encoding-decodes-exactly-if-fits
                                  (value (+ x y)))
                  :in-theory (e/d (generated-add-flags)
                                  (proof-integer-word proof-immediate-integer-p
                                   generated-unsigned-64-add-normalized-word
                                   generated-signed-64-of-unsigned
                                   generated-immediate-encoding-decodes-exactly-if-fits)))))

(local
 (defthm generated-encoded-negation
   (implies (integerp x)
            (equal (boymoo-model::a64-unsigned 64 (- 2 (proof-integer-word x)))
                   (proof-integer-word (- x))))
   :hints (("Goal" :use (:instance generated-unsigned-64-subtract-normalized-word
                                   (left 2) (right (1+ (* 2 x))))
                   :in-theory (disable generated-unsigned-64-subtract-normalized-word
                                       generated-unsigned-of-difference)))))

(defthm generated-fast-negation-word-and-overflow
  (let* ((operand (proof-integer-word x))
         (result (boymoo-model::a64-unsigned 64 (- 2 operand)))
         (flags (generated-compare-flags 2 operand)))
    (implies (proof-immediate-integer-p x)
             (and (equal result (proof-integer-word (- x)))
                  (equal (boymoo-model::a64-condition 6 (boymoo-model::a64-unsigned 4 flags))
                         (not (proof-immediate-integer-p (- x)))))))
  :hints (("Goal" :use (:instance generated-immediate-encoding-decodes-exactly-if-fits
                                  (value (- x)))
                  :in-theory (e/d (generated-compare-flags)
                                  (proof-integer-word proof-immediate-integer-p
                                   generated-unsigned-of-difference generated-signed-64-of-unsigned
                                   generated-immediate-encoding-decodes-exactly-if-fits)))))

(defthm generated-effect-of-adds-register
  (implies (and (natp rd) (< rd 31))
           (equal (proof-instruction-effect (list :arithmetic-reg 1 64 rd rn rm 0 0) world)
                  (let ((left (proof-world-reg rn world)) (right (proof-world-reg rm world)))
                    (generated-set-flags
                     (generated-add-flags left right)
                     (generated-set-reg rd (+ left right)
                                        (generated-set-pc (+ 4 (proof-world-pc world)) world))))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-machine proof-world-pc
                                    proof-world-reg proof-reg generated-add-flags
                                    generated-set-machine generated-set-pc generated-set-reg
                                    generated-set-flags))))

(local
 (defthm generated-unsigned-of-subtract-modulus
   (implies (integerp x)
            (equal (boymoo-model::a64-unsigned 64 (+ (- #x10000000000000000) x))
                   (boymoo-model::a64-unsigned 64 x)))
   :hints (("Goal" :use (:instance generated-unsigned-add-multiple (n 64) (q -1))))))

(local
 (defthm generated-unsigned-difference-of-signed-operands
   (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
            (equal (boymoo-model::a64-unsigned 64
                     (- (boymoo-model::a64-signed 64 left) (boymoo-model::a64-signed 64 right)))
                   (boymoo-model::a64-unsigned 64 (- left right))))
   :hints (("Goal" :in-theory (e/d (generated-signed-64-of-word)
                                   (generated-unsigned-of-difference))))
   :rule-classes nil))

(local
 (defthm generated-sign-bit-is-signed-negative
   (equal (logbitp 63 (boymoo-model::a64-unsigned 64 value))
          (< (boymoo-model::a64-signed 64 value) 0))
   :hints (("Goal" :in-theory (enable generated-signed-64-of-word)
                   :use (:instance generated-logbitp-of-bounded
                                   (bit 63) (x (boymoo-model::a64-unsigned 64 value)))))))

(local
 (defthm generated-sign-bit-of-bounded-word
   (implies (unsigned-byte-p 64 value)
            (equal (logbitp 63 value) (< (boymoo-model::a64-signed 64 value) 0)))
   :hints (("Goal" :use generated-sign-bit-is-signed-negative
                   :in-theory (disable generated-sign-bit-is-signed-negative)))))

(local
 (defthm generated-signed-difference-wraps-at-endpoints
   (implies (and (integerp difference) (< (- (expt 2 64)) difference) (< difference (expt 2 64)))
            (equal (boymoo-model::a64-signed 64 difference)
                   (cond ((< difference (- (expt 2 63))) (+ (expt 2 64) difference))
                         ((<= (expt 2 63) difference) (- difference (expt 2 64)))
                         (t difference))))
   :hints (("Goal" :in-theory (enable generated-signed-64-of-word)
                   :cases ((< difference 0))
                   :use (:instance generated-unsigned-of-remainder
                                   (n 64) (x difference) (q -1)
                                   (r (+ (expt 2 64) difference)))))))

(local
 (defthm generated-less-than-condition-on-signed-difference
   (implies (and (integerp difference) (< (- (expt 2 64)) difference) (< difference (expt 2 64)))
            (let* ((wrapped (boymoo-model::a64-signed 64 difference))
                   (negative (< wrapped 0))
                   (overflow (not (equal difference wrapped))))
              (equal (not (equal negative overflow)) (< difference 0))))))

(defthm generated-signed-condition-of-compare
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (equal (boymoo-model::a64-condition 11
                    (boymoo-model::a64-unsigned 4 (generated-compare-flags left right)))
                  (< (boymoo-model::a64-signed 64 left) (boymoo-model::a64-signed 64 right))))
  :hints (("Goal"
           :use (generated-unsigned-difference-of-signed-operands
                 (:instance generated-less-than-condition-on-signed-difference
                            (difference (- (boymoo-model::a64-signed 64 left)
                                           (boymoo-model::a64-signed 64 right)))))
           :in-theory (e/d (generated-compare-flags)
                           (generated-less-than-condition-on-signed-difference)))))

(defthm generated-fast-immediate-less-than
  (implies (and (proof-immediate-integer-p left) (proof-immediate-integer-p right))
           (equal (boymoo-model::a64-condition
                   11 (boymoo-model::a64-unsigned
                       4 (generated-compare-flags (proof-integer-word left) (proof-integer-word right))))
                  (< left right)))
  :hints (("Goal"
           :cases ((< left right))
           :use ((:instance generated-signed-condition-of-compare
                            (left (proof-integer-word left)) (right (proof-integer-word right)))
                 (:instance generated-signed-of-immediate-word (value left))
                 (:instance generated-signed-of-immediate-word (value right)))
           :in-theory (disable generated-signed-condition-of-compare
                               generated-signed-of-immediate-word))))
