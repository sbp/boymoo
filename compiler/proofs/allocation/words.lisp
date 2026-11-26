(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defconst *allocation-word-modulus* (expt 2 64))

(local
 (defthm allocation-unsigned-is-loghead
   (equal (boymoo-model::a64-unsigned width value)
          (acl2::loghead (nfix width) value))
   :hints (("Goal" :in-theory (enable acl2::loghead)))))

(defthm allocation-word-is-unsigned
  (unsigned-byte-p 64 (boymoo-model::a64-unsigned 64 value))
  :rule-classes (:rewrite :type-prescription))

(defthm allocation-unsigned-idempotent
  (equal (boymoo-model::a64-unsigned width
                                    (boymoo-model::a64-unsigned width value))
         (boymoo-model::a64-unsigned width value)))

(defthm allocation-unsigned-64-identity
  (implies (unsigned-byte-p 64 value)
           (equal (boymoo-model::a64-unsigned 64 value) value)))

(defthm allocation-unsigned-64-range
  (< (boymoo-model::a64-unsigned 64 value) *allocation-word-modulus*)
  :rule-classes :linear
  :hints (("Goal" :use allocation-word-is-unsigned
           :in-theory (enable unsigned-byte-p acl2::integer-range-p))))

(defthm allocation-unsigned-64-natural
  (natp (boymoo-model::a64-unsigned 64 value))
  :rule-classes (:rewrite :type-prescription)
  :hints (("Goal" :use allocation-word-is-unsigned
           :in-theory (enable unsigned-byte-p acl2::integer-range-p))))

(defthm allocation-register-values-fit
  (unsigned-byte-p 64 (boymoo-model::a64-read-reg register 64 use-sp machine))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned)))
  :rule-classes (:rewrite :type-prescription))

(defthm allocation-register-natural
  (natp (boymoo-model::a64-read-reg register 64 use-sp machine))
  :rule-classes :type-prescription
  :hints (("Goal" :use allocation-register-values-fit
           :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                           (boymoo-model::a64-read-reg boymoo-model::a64-unsigned)))))

(defthm allocation-register-upper-bound
  (< (boymoo-model::a64-read-reg register 64 use-sp machine)
     *allocation-word-modulus*)
  :rule-classes :linear
  :hints (("Goal" :use allocation-register-values-fit
           :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                           (boymoo-model::a64-read-reg boymoo-model::a64-unsigned)))))

(defthm allocation-write-register-wrapped
  (equal (boymoo-model::a64-write-reg
          register 64 use-sp (boymoo-model::a64-unsigned 64 value) machine)
         (boymoo-model::a64-write-reg register 64 use-sp value machine))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-unsigned))))

(local
 (defthm allocation-unsigned-64-is-mod
   (equal (boymoo-model::a64-unsigned 64 value)
          (mod (ifix value) *allocation-word-modulus*))
   :hints (("Goal" :in-theory (enable acl2::loghead)))))

(defthm allocation-unsigned-64-of-sum
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (equal (boymoo-model::a64-unsigned 64 (+ left right))
                  (if (< (+ left right) *allocation-word-modulus*)
                      (+ left right)
                    (- (+ left right) *allocation-word-modulus*))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p acl2::integer-range-p))))

(defthm allocation-unsigned-64-of-difference
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (equal (boymoo-model::a64-unsigned 64 (- left right))
                  (if (<= right left)
                      (- left right)
                    (+ *allocation-word-modulus* (- left right)))))
  :hints (("Goal" :in-theory (enable unsigned-byte-p acl2::integer-range-p))))

(local
 (defthm allocation-complement-64
   (implies (unsigned-byte-p 64 value)
            (equal (logxor value #xffffffffffffffff)
                   (- #xffffffffffffffff value)))
   :hints (("Goal"
            :use ((:instance acl2::logand-logxor
                             (i #xffffffffffffffff) (j -1) (k value)))
            :in-theory (enable acl2::loghead lognot)))))

(local
 (defthm allocation-bit-64-of-double-word
   (implies (and (integerp sum) (<= 0 sum)
                 (< sum (* 2 *allocation-word-modulus*)))
            (equal (logbitp 64 sum)
                   (<= *allocation-word-modulus* sum)))
   :hints (("Goal" :in-theory (enable logbitp acl2::logtail acl2::logbit)))))

(local
 (defthm allocation-word-with-added-modulus
   (implies (integerp value)
            (equal (boymoo-model::a64-unsigned 64 (+ *allocation-word-modulus* value))
                   (boymoo-model::a64-unsigned 64 value)))
   :hints (("Goal" :in-theory (disable allocation-unsigned-is-loghead)))))

(defun allocation-flags (subtract left right)
  (let* ((sum (if subtract (- left right) (+ left right)))
         (result (boymoo-model::a64-unsigned 64 sum))
         (signed-left (boymoo-model::a64-signed 64 left))
         (signed-right (boymoo-model::a64-signed 64 right)))
    (boymoo-model::a64-result-flags
     64 result
     (if subtract (<= right left) (<= *allocation-word-modulus* sum))
     (not (equal (+ signed-left (if subtract (- signed-right) signed-right))
                 (boymoo-model::a64-signed 64 result))))))

(defthm allocation-arithmetic-register-flags
  (implies (and (member-equal opcode '(1 3)) (unsigned-byte-p 64 right))
           (equal (boymoo-model::a64-exec-arithmetic opcode 64 rd rn right
                                                     immediate machine)
                  (let* ((left (boymoo-model::a64-read-reg rn 64 immediate machine))
                         (subtract (equal opcode 3)))
                    (boymoo-model::a64-set-nzcv
                     (allocation-flags subtract left right)
                     (boymoo-model::a64-write-reg
                      rd 64 nil (if subtract (- left right) (+ left right))
                      machine)))))
  :hints (("Goal"
           :in-theory (e/d (boymoo-model::a64-exec-arithmetic
                            unsigned-byte-p acl2::integer-range-p)
                           (allocation-unsigned-is-loghead
                            allocation-unsigned-64-is-mod
                            allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference
                            allocation-unsigned-64-identity
                            boymoo-model::a64-read-reg
                            boymoo-model::a64-unsigned
                            boymoo-model::a64-signed
                            boymoo-model::a64-result-flags
                            boymoo-model::a64-write-reg
                            boymoo-model::a64-set-nzcv)))))

(defthm allocation-arithmetic-without-flags
  (implies (and (member-equal opcode '(0 2)) (unsigned-byte-p 64 right)
                (booleanp immediate))
           (equal (boymoo-model::a64-exec-arithmetic opcode 64 rd rn right
                                                     immediate machine)
                  (let ((left (boymoo-model::a64-read-reg rn 64 immediate machine)))
                    (boymoo-model::a64-write-reg
                     rd 64 immediate (if (equal opcode 2) (- left right) (+ left right))
                     machine))))
  :hints (("Goal"
           :in-theory (e/d (boymoo-model::a64-exec-arithmetic
                            unsigned-byte-p acl2::integer-range-p)
                           (allocation-unsigned-is-loghead
                            allocation-unsigned-64-is-mod
                            allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference
                            allocation-unsigned-64-identity
                            boymoo-model::a64-unsigned
                            boymoo-model::a64-write-reg)))))

(defthm allocation-unsigned-4-identity
  (implies (unsigned-byte-p 4 value)
           (equal (boymoo-model::a64-unsigned 4 value) value)))

(defthm allocation-flags-fit
  (unsigned-byte-p 4 (allocation-flags subtract left right))
  :hints (("Goal"
           :in-theory (e/d (boymoo-model::a64-result-flags unsigned-byte-p
                            acl2::integer-range-p)
                           (allocation-unsigned-is-loghead allocation-unsigned-64-is-mod
                            boymoo-model::a64-unsigned boymoo-model::a64-signed)))))

(defthm allocation-shift-for-add
  (implies (and (member-equal shift '(0 1)) (unsigned-byte-p 64 value))
           (equal (boymoo-model::a64-shift 0 64 value shift)
                  (if (equal shift 0) value
                    (boymoo-model::a64-unsigned 64 (+ value value)))))
  :hints (("Goal"
           :in-theory (e/d (ash)
                           (allocation-unsigned-is-loghead
                            allocation-unsigned-64-is-mod
                            boymoo-model::a64-unsigned)))))

(defthm allocation-subtraction-conditions
  (implies (and (unsigned-byte-p 64 left) (unsigned-byte-p 64 right))
           (and (equal (boymoo-model::a64-condition 2 (allocation-flags t left right))
                       (<= right left))
                (equal (boymoo-model::a64-condition 3 (allocation-flags t left right))
                       (< left right))
                (equal (boymoo-model::a64-condition 8 (allocation-flags t left right))
                       (< right left))
                (equal (boymoo-model::a64-condition 9 (allocation-flags t left right))
                       (<= left right))))
  :hints (("Goal"
           :in-theory (e/d (boymoo-model::a64-condition boymoo-model::a64-field
                            boymoo-model::a64-result-flags unsigned-byte-p
                            acl2::integer-range-p)
                           (allocation-unsigned-is-loghead allocation-unsigned-64-is-mod
                            boymoo-model::a64-unsigned boymoo-model::a64-signed)))))

(defthm allocation-addition-carry
  (equal (boymoo-model::a64-condition 2 (allocation-flags nil left right))
         (<= *allocation-word-modulus* (+ left right)))
  :hints (("Goal"
           :in-theory (e/d (boymoo-model::a64-condition boymoo-model::a64-field
                            boymoo-model::a64-result-flags)
                           (allocation-unsigned-is-loghead allocation-unsigned-64-is-mod
                            boymoo-model::a64-unsigned boymoo-model::a64-signed)))))

(local
 (defthm allocation-byte-range
   (unsigned-byte-p 8 (boymoo-model::a64-byte address memory))))

(local
 (defthm allocation-byte-fits-wider-word
   (implies (and (integerp width) (<= 8 width))
            (unsigned-byte-p width (boymoo-model::a64-byte address memory)))
   :hints (("Goal" :use allocation-byte-range
            :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                            (allocation-byte-range boymoo-model::a64-byte))))))

(defthm allocation-read-bytes-range
  (implies (natp count)
           (unsigned-byte-p (* 8 count)
                            (boymoo-model::a64-read-bytes count address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address memory)
           :in-theory (disable unsigned-byte-p acl2::integer-range-p
                               acl2::ash-to-floor
                               boymoo-model::a64-byte))))
