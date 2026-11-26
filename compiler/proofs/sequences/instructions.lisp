(in-package "BOYMOO-PROOFS")

(include-book "state")

(logic)
(set-verify-guards-eagerness 0)

(defmacro sequence-def-low-mask (name bits)
  `(defthm ,name
     (implies (integerp value)
              (equal (logand value ,(1- (expt 2 bits)))
                     (boymoo-model::a64-unsigned ,bits value)))
     :hints (("Goal" :use ((:instance sequence-logand-mask (bits ,bits)))))))

(sequence-def-low-mask sequence-logand-one 1)
(sequence-def-low-mask sequence-logand-seven 3)
(sequence-def-low-mask sequence-logand-byte 8)
(sequence-def-low-mask sequence-logand-four-bytes 32)
(sequence-def-low-mask sequence-logand-word 64)

(defthm sequence-logior-zero-word
  (implies (integerp value)
           (and (equal (logior 0 value) value)
                (equal (logior value 0) value)))
  :hints (("Goal" :in-theory (enable acl2::binary-logior acl2::binary-logand))))

(defthm sequence-shift-zero
  (implies (unsigned-byte-p width value)
           (equal (boymoo-model::a64-shift 0 width value 0) value)))

(defthm sequence-write-register-truncates
  (implies (natp width)
           (equal (boymoo-model::a64-write-reg
                   register width use-sp (boymoo-model::a64-unsigned width value) machine)
                  (boymoo-model::a64-write-reg register width use-sp value machine)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg))))

(defthm sequence-truncate-word-plus-modulus
  (implies (integerp value)
           (equal (boymoo-model::a64-unsigned 64 (+ #x10000000000000000 value))
                  (boymoo-model::a64-unsigned 64 value)))
  :hints (("Goal" :in-theory (enable sequence-a64-unsigned-as-mod)
                  :use ((:instance sequence-mod-add-multiple
                                   (divisor #x10000000000000000) (multiple 1))))))

(defthm sequence-logxor-all-word-bits
  (implies (unsigned-byte-p 64 value)
           (equal (logxor value #xffffffffffffffff)
                  (- #xffffffffffffffff value)))
  :hints (("Goal" :use ((:instance sequence-logxor-ones (bits 64))))))

(defthm sequence-add-register-effect
  (implies (unsigned-byte-p 64 right)
           (equal (boymoo-model::a64-exec-arithmetic 0 64 rd rn right immediate machine)
                  (boymoo-model::a64-write-reg
                   rd 64 (if immediate t nil)
                   (+ (boymoo-model::a64-read-reg rn 64 immediate machine) right)
                   machine))))

(defthm sequence-subtract-register-effect
  (implies (unsigned-byte-p 64 right)
           (equal (boymoo-model::a64-exec-arithmetic 2 64 rd rn right immediate machine)
                  (boymoo-model::a64-write-reg
                   rd 64 (if immediate t nil)
                   (- (boymoo-model::a64-read-reg rn 64 immediate machine) right)
                   machine)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-write-reg))))

(defthm sequence-subtract-with-flags-effect
  (let* ((left (boymoo-model::a64-read-reg rn 64 immediate machine))
         (difference (- left right))
         (result (boymoo-model::a64-unsigned 64 difference))
         (signed-difference (- (boymoo-model::a64-signed 64 left)
                               (boymoo-model::a64-signed 64 right)))
         (overflow (not (equal signed-difference (boymoo-model::a64-signed 64 result)))))
    (implies (unsigned-byte-p 64 right)
             (equal (boymoo-model::a64-exec-arithmetic 3 64 rd rn right immediate machine)
                    (boymoo-model::a64-set-nzcv
                     (boymoo-model::a64-result-flags 64 result (<= right left) overflow)
                     (boymoo-model::a64-write-reg rd 64 nil difference machine)))))
  :hints (("Goal"
           :in-theory (e/d (boymoo-model::a64-write-reg) (boymoo-model::a64-result-flags))
           :use ((:instance sequence-sign-bit (bit 64)
                            (value (+ #x10000000000000000
                                      (- (boymoo-model::a64-read-reg rn 64 immediate machine)
                                         right))))))))

(defthm sequence-result-flags-stay-in-nzcv
  (equal (boymoo-model::a64-unsigned
          4 (boymoo-model::a64-result-flags width result carry overflow))
         (boymoo-model::a64-result-flags width result carry overflow)))

(defthm sequence-conditions-on-result-flags
  (let ((flags (boymoo-model::a64-result-flags width result carry overflow)))
    (and (equal (boymoo-model::a64-condition 0 flags) (equal result 0))
         (equal (boymoo-model::a64-condition 1 flags) (not (equal result 0)))
         (equal (boymoo-model::a64-condition 2 flags) (if carry t nil))
         (equal (boymoo-model::a64-condition 8 flags) (and carry (not (equal result 0))))
         (equal (boymoo-model::a64-condition
                 12 (boymoo-model::a64-result-flags 64 result carry nil))
                (and (not (equal result 0)) (not (logbitp 63 result))))))
  :hints (("Goal" :in-theory (enable logbitp))))

(defthm sequence-zero-for-equal-words
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (equal (equal (boymoo-model::a64-unsigned 64 (- left right)) 0)
                  (equal left right))))

(defthm sequence-repeat-pc-write
  (equal (boymoo-model::a64-set-pc next (boymoo-model::a64-set-pc previous machine))
         (boymoo-model::a64-set-pc next machine))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-set-pc update-nth))))

(defthm sequence-conditional-branch-effect
  (equal (proof-execute (list :branch-cond delta condition) machine)
         (boymoo-model::a64-set-pc
          (+ (boymoo-model::a64-pc machine)
             (if (boymoo-model::a64-condition condition (boymoo-model::a64-nzcv machine))
                 delta 4))
          machine))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-condition))))

(defthm sequence-zero-branch-effect
  (equal (proof-execute (list :branch-zero delta width register nonzero) machine)
         (boymoo-model::a64-set-pc
          (+ (boymoo-model::a64-pc machine)
             (if (if nonzero
                     (not (equal (boymoo-model::a64-read-reg register width nil machine) 0))
                   (equal (boymoo-model::a64-read-reg register width nil machine) 0))
                 delta 4))
          machine)))

(in-theory (disable boymoo-model::a64-exec-arithmetic
                    boymoo-model::a64-result-flags
                    boymoo-model::a64-condition
                    boymoo-model::a64-shift))
