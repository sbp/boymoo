(in-package "BOYMOO-PROOFS")

(include-book "words")

(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm allocation-bitfield-unsigned-as-loghead
   (equal (boymoo-model::a64-unsigned width word)
          (acl2::loghead (nfix width) word))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned acl2::loghead)))))

(local (in-theory (disable acl2::ash-to-floor)))

(local
 (defthm allocation-low-part-of-right-rotation
   (implies (member-equal shift '(16 32))
            (equal (acl2::loghead (- 64 shift) (boymoo-model::a64-ror 64 word shift))
                   (ash (acl2::loghead 64 word) (- shift))))
   :hints (("Goal" :cases ((equal shift 16)))
           (acl2::logbitp-reasoning))))

(local
 (defthm allocation-high-part-of-left-rotation
   (implies (member-equal shift '(1 8 16))
            (equal (logand (boymoo-model::a64-ror 64 word (- 64 shift))
                           (acl2::loghead 64 (ash -1 shift)))
                   (acl2::loghead 64 (ash (acl2::loghead 64 word) shift))))
   :hints (("Goal" :cases ((equal shift 1) (equal shift 8)))
           (acl2::logbitp-reasoning))))

(defthm allocation-exec-right-shift
  (implies (member-equal shift '(16 32))
           (equal (boymoo-model::a64-exec-bitfield
                   2 64 rd rn shift 63 #xffffffffffffffff
                   (boymoo-model::a64-ones (- 64 shift)) machine)
                  (boymoo-model::a64-write-reg
                   rd 64 nil
                   (ash (boymoo-model::a64-read-reg rn 64 nil machine) (- shift))
                   machine)))
  :hints (("Goal" :cases ((equal shift 16))
           :use ((:instance allocation-low-part-of-right-rotation
                            (word (boymoo-model::a64-read-reg rn 64 nil machine))))
           :in-theory (e/d (acl2::loghead)
                           (boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                            boymoo-model::a64-ror)))))

(defthm allocation-exec-left-shift
  (implies (member-equal shift '(1 8 16))
           (equal (boymoo-model::a64-exec-bitfield
                   2 64 rd rn (- 64 shift) (- 63 shift)
                   (boymoo-model::a64-unsigned 64 (ash -1 shift)) #xffffffffffffffff machine)
                  (boymoo-model::a64-write-reg
                   rd 64 nil (ash (boymoo-model::a64-read-reg rn 64 nil machine) shift)
                   machine)))
  :hints (("Goal" :cases ((equal shift 1) (equal shift 8))
           :use ((:instance allocation-high-part-of-left-rotation
                            (word (boymoo-model::a64-read-reg rn 64 nil machine)))
                 (:instance allocation-write-register-wrapped
                            (register rd) (use-sp nil)
                            (value (ash (boymoo-model::a64-read-reg rn 64 nil machine) shift))))
           :in-theory (disable boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                               allocation-write-register-wrapped boymoo-model::a64-ror))))

(local
 (defthm allocation-sign-bit-of-word
   (implies (unsigned-byte-p 64 word)
            (equal (logbitp 63 word) (<= (expt 2 63) word)))
   :hints (("Goal" :in-theory (enable logbitp acl2::logbit acl2::logtail
                                      unsigned-byte-p acl2::integer-range-p)))))

(defthm allocation-signed-word
  (implies (unsigned-byte-p 64 word)
           (equal (boymoo-model::a64-signed 64 word)
                  (if (< word (expt 2 63)) word (- word *allocation-word-modulus*))))
  :hints (("Goal" :in-theory (disable allocation-bitfield-unsigned-as-loghead))))

(defthm allocation-condition-ge-after-zero
  (implies (unsigned-byte-p 64 word)
           (equal (boymoo-model::a64-condition 10 (allocation-flags t word 0))
                  (< word (expt 2 63))))
  :hints (("Goal" :in-theory (disable allocation-bitfield-unsigned-as-loghead
                                     boymoo-model::a64-signed))))
