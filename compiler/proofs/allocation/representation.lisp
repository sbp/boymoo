(in-package "BOYMOO-PROOFS")

(include-book "words")

(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm allocation-publication-mask-is-loghead
   (equal (boymoo-model::a64-unsigned width value)
          (acl2::loghead (nfix width) value))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned acl2::loghead)))))

(local
 (defthm allocation-offset-with-wrap
   (implies (and (proof-span-p address 8) (unsigned-byte-p 64 base)
                 (member-equal tag '(0 2)))
            (equal (boymoo-model::a64-unsigned 64 (+ address (- base) tag))
                   (if (< (+ address tag) base)
                       (+ *allocation-word-modulus* address (- base) tag)
                     (+ address (- base) tag))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance allocation-unsigned-64-of-difference (left (+ address tag))
                          (right base)))
            :in-theory (disable allocation-publication-mask-is-loghead
                                allocation-unsigned-64-of-difference)))))

(defthm allocation-tagged-offset-round-trip
  (let ((word (boymoo-model::a64-unsigned 64 (+ address (- base) tag))))
    (implies (and (proof-span-p address 8) (unsigned-byte-p 64 base)
                  (equal (mod address 8) 0) (equal (mod base 8) 0)
                  (member-equal tag '(0 2)))
             (and (unsigned-byte-p 64 word)
                  (not (oddp word))
                  (equal (proof-word-tag word) tag)
                  (equal (proof-pointer-address word base) address))))
  :rule-classes nil
  :hints (("Goal" :cases ((< (+ address tag) base))
           :use allocation-offset-with-wrap
           :in-theory (enable acl2::loghead))))

(defun allocation-string-header (length)
  (+ 1 (* 256 (nfix length))))

(defthm allocation-string-header-fields
  (implies (natp length)
           (and (equal (proof-header-type (allocation-string-header length)) 1)
                (equal (proof-header-size (allocation-string-header length)) length)))
  :hints (("Goal" :in-theory (enable acl2::loghead))))

(defthm allocation-wrap-before-adding-tag
  (implies (and (integerp offset) (integerp tag))
           (equal (boymoo-model::a64-unsigned 64 (+ tag (boymoo-model::a64-unsigned 64 offset)))
                  (boymoo-model::a64-unsigned 64 (+ tag offset))))
  :hints (("Goal" :in-theory (enable acl2::loghead))))

(defthm allocation-string-header-fits
  (implies (and (natp length) (< length *proof-space-size*))
           (and (equal (ash length 8) (* 256 length))
                (unsigned-byte-p 64 (ash length 8))
                (unsigned-byte-p 64 (allocation-string-header length)))))

