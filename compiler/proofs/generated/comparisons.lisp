(in-package "BOYMOO-PROOFS")

(include-book "instructions")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-instruction-effect proof-execute proof-linux-svc
                    proof-world-pc proof-world-reg proof-reg
                    boymoo-model::a64-unsigned boymoo-model::a64-execute
                    boymoo-model::a64-condition boymoo-model::a64-result-flags
                    boymoo-model::a64-signed generated-sp generated-flags
                    ash logbitp acl2::binary-logxor expt))

(defthm generated-complement-of-word
  (implies (unsigned-byte-p 64 x)
           (equal (logxor x #xffffffffffffffff) (- #xffffffffffffffff x)))
  :hints (("Goal" :use (:instance generated-logxor-with-mask (width 64)))))

(defthm generated-unsigned-of-add-modulus
  (implies (integerp x)
           (equal (boymoo-model::a64-unsigned 64 (+ #x10000000000000000 x))
                  (boymoo-model::a64-unsigned 64 x)))
  :hints (("Goal" :use (:instance generated-unsigned-add-multiple (n 64) (q 1)))))

(defthm generated-unsigned-of-difference
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (equal (boymoo-model::a64-unsigned 64 (- left right))
                  (if (< left right) (+ (expt 2 64) (- left right)) (- left right))))
  :hints (("Goal" :cases ((< left right))
                  :use (:instance generated-unsigned-of-remainder
                                  (n 64) (x (- left right))
                                  (r (+ (expt 2 64) (- left right))) (q -1)))))

(defthm generated-carry-of-subtraction
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (equal (logbitp 64 (+ #x10000000000000000 (- left right))) (<= right left)))
  :hints (("Goal" :use (:instance generated-logbitp-of-bounded
                                  (bit 64) (x (+ (expt 2 64) (- left right)))))))

(defund generated-compare-flags (left right)
  (let ((result (boymoo-model::a64-unsigned 64 (- left right))))
    (boymoo-model::a64-result-flags
     64 result (<= right left)
     (not (equal (- (boymoo-model::a64-signed 64 left)
                    (boymoo-model::a64-signed 64 right))
                 (boymoo-model::a64-signed 64 result))))))

(defthm generated-condition-of-result-flags
  (let* ((flags (boymoo-model::a64-result-flags 64 bits carry overflow))
         (register (boymoo-model::a64-unsigned 4 flags)))
    (and (equal (boymoo-model::a64-condition 0 register) (equal bits 0))
         (equal (boymoo-model::a64-condition 1 register) (not (equal bits 0)))
         (equal (boymoo-model::a64-condition 2 register) (if carry t nil))
         (equal (boymoo-model::a64-condition 6 register) (if overflow t nil))
         (equal (boymoo-model::a64-condition 9 register) (or (not carry) (equal bits 0)))
         (equal (boymoo-model::a64-condition 11 register)
                (not (equal (logbitp 63 bits) (if overflow t nil))))))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-condition
                                    boymoo-model::a64-result-flags))))

(defthm generated-condition-of-compare
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (let ((flags (boymoo-model::a64-unsigned 4 (generated-compare-flags left right))))
             (and (equal (boymoo-model::a64-condition 0 flags) (equal left right))
                  (equal (boymoo-model::a64-condition 1 flags) (not (equal left right)))
                  (equal (boymoo-model::a64-condition 2 flags) (<= right left))
                  (equal (boymoo-model::a64-condition 9 flags) (<= left right)))))
  :hints (("Goal" :in-theory (enable generated-compare-flags))))

(defthm generated-effect-of-cmp-immediate
  (implies (and (generated-ordinary-machine-p world) (natp left) (< left 31)
                (unsigned-byte-p 64 right))
           (equal (proof-instruction-effect (list :arithmetic-imm 3 64 31 left right) world)
                  (generated-set-flags (generated-compare-flags (proof-world-reg left world) right)
                                       (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc
                                    generated-set-machine generated-set-pc generated-set-flags
                                    proof-world-reg proof-reg generated-compare-flags
                                    generated-ordinary-machine-p))))

(defthm generated-effect-of-cmp-register
  (implies (generated-ordinary-machine-p world)
           (equal (proof-instruction-effect (list :arithmetic-reg 3 64 31 left right 0 0) world)
                  (generated-set-flags
                   (generated-compare-flags (proof-world-reg left world) (proof-world-reg right world))
                   (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc
                                    generated-set-machine generated-set-pc generated-set-flags
                                    proof-world-reg proof-reg generated-compare-flags
                                    generated-ordinary-machine-p))))

(defthm generated-effect-of-add-immediate
  (implies (and (natp register) (< register 31))
           (equal (proof-instruction-effect (list :arithmetic-imm 0 64 register base amount) world)
                  (generated-set-reg
                   register (+ (if (equal base 31) (generated-sp world) (proof-world-reg base world))
                               amount)
                   (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc
                                    generated-set-machine generated-set-pc generated-set-reg
                                    proof-world-reg proof-reg generated-sp))))

(defthm generated-effect-of-sub-immediate
  (implies (and (natp register) (< register 31) (unsigned-byte-p 64 amount))
           (equal (proof-instruction-effect (list :arithmetic-imm 2 64 register base amount) world)
                  (generated-set-reg
                   register (- (if (equal base 31) (generated-sp world) (proof-world-reg base world))
                               amount)
                   (generated-set-pc (+ 4 (proof-world-pc world)) world))))
  :hints (("Goal" :in-theory (enable proof-instruction-effect proof-execute
                                    boymoo-model::a64-execute proof-world-pc
                                    generated-set-machine generated-set-pc generated-set-reg
                                    proof-world-reg proof-reg generated-sp))))
