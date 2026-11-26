(in-package "BOYMOO-PROOFS")

(include-book "object-views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-view proof-view-step proof-value-p proof-immediate-integer-p proof-word-tag
                    proof-integer-word proof-character-word proof-integer-view proof-symbol-value
                    proof-cons-value proof-rational-value proof-complex-value proof-header-size
                    generated-ash-as-floor
                    boymoo-model::a64-unsigned boymoo-model::a64-signed ash mod floor evenp oddp expt))

(local
 (defthm generated-single-bit-arithmetic-shift
   (implies (integerp word) (equal (ash word -1) (floor word 2)))
   :hints (("Goal" :in-theory (enable ash floor)))))

(local
 (defthm generated-three-bit-arithmetic-shift
   (implies (integerp word) (equal (ash word -3) (floor word 8)))
   :hints (("Goal" :in-theory (enable ash floor)))))

(local
 (defthm generated-parity-of-signed-64-bit-word
   (implies (unsigned-byte-p 64 word)
            (equal (evenp (boymoo-model::a64-signed 64 word)) (evenp word)))
   :hints (("Goal"
            :use ((:instance generated-floor-half (x word))
                  (:instance generated-even-double (q (- (floor word 2) (expt 2 63))))
                  (:instance generated-odd-double-plus-one (q (- (floor word 2) (expt 2 63)))))
            :in-theory (e/d (generated-signed-64-of-word)
                            (generated-even-double generated-odd-double-plus-one))))))

(local
 (defthm generated-unsigned-of-signed-word
   (equal (boymoo-model::a64-unsigned 64 (boymoo-model::a64-signed 64 word))
          (boymoo-model::a64-unsigned 64 word))
   :hints (("Goal"
            :use (:instance generated-unsigned-add-multiple (n 64) (q -1)
                            (x (boymoo-model::a64-unsigned 64 word)))
            :in-theory (e/d (generated-signed-64-of-word) (generated-unsigned-add-multiple))))))

(defthm generated-odd-word-has-immediate-integer-encoding
  (let* ((signed (boymoo-model::a64-signed 64 word)) (datum (ash signed -1)))
    (implies (and (unsigned-byte-p 64 word) (oddp word))
             (and (proof-immediate-integer-p datum)
                  (equal (proof-integer-word datum) word))))
  :hints (("Goal"
           :use ((:instance generated-floor-half (x (boymoo-model::a64-signed 64 word)))
                 (:instance generated-floor-bounds (x (boymoo-model::a64-signed 64 word)) (y 2))
                 (:instance generated-integer-step (x (floor (boymoo-model::a64-signed 64 word) 2))
                            (y (- (expt 2 62)))))
           :in-theory (enable proof-immediate-integer-p proof-integer-word oddp)))
  :rule-classes nil)

(defthm generated-tagged-character-has-standard-encoding
  (let ((code (floor word 8)))
    (implies (and (unsigned-byte-p 64 word) (equal (proof-word-tag word) 4) (unsigned-byte-p 8 code))
             (and (characterp (code-char code))
                  (equal (proof-character-word (code-char code)) word))))
  :hints (("Goal"
           :use (:instance generated-unsigned-as-mod (n 3) (x word))
           :in-theory (enable proof-word-tag proof-character-word mod)))
  :rule-classes nil)

(local
 (defthm generated-normalized-rational-is-not-fast-atom
   (implies (or (characterp value) (proof-immediate-integer-p value))
            (not (equal (proof-rational-value first second) (cons :value value))))
   :hints (("Goal" :in-theory (enable proof-rational-value proof-immediate-integer-p)))))

(local
 (defthm generated-nonzero-imaginary-complex-is-not-fast-atom
   (implies (or (characterp value) (proof-immediate-integer-p value))
            (not (equal (proof-complex-value first second) (cons :value value))))
   :hints (("Goal"
            :use (:instance acl2::imagpart-complex (acl2::x (proof-view-value first)) (acl2::y (proof-view-value second)))
            :in-theory (e/d (proof-complex-value proof-immediate-integer-p) (acl2::imagpart-complex))))))

(local
 (defthm generated-fast-atom-view-step-is-canonical
   (implies (and (equal (proof-view-step :word word 0 depth base objects packages machine) (proof-value-view value))
                 (or (characterp value) (proof-immediate-integer-p value)))
            (if (characterp value)
                (and (equal (proof-word-tag word) 4) (equal word (proof-character-word value)))
              (and (oddp word) (equal word (proof-integer-word value)))))
   :hints (("Goal"
            :expand (proof-view-step :word word 0 depth base objects packages machine)
            :use (generated-odd-word-has-immediate-integer-encoding generated-tagged-character-has-standard-encoding)
            :in-theory (enable proof-cons-value proof-symbol-value proof-integer-view proof-immediate-integer-p)))
   :rule-classes nil))

(defthm generated-fast-atomic-values-have-canonical-words
  (implies (and (proof-value-p word value base objects packages machine)
                (or (characterp value) (proof-immediate-integer-p value)))
           (if (characterp value)
               (and (equal (proof-word-tag word) 4) (equal word (proof-character-word value)))
             (and (oddp word) (equal word (proof-integer-word value)))))
  :hints (("Goal"
           :use (:instance generated-fast-atom-view-step-is-canonical
                           (depth (1+ (nfix (proof-object-rank (assoc-equal (proof-pointer-address word base) objects))))))
           :in-theory (enable proof-value-p proof-view)))
  :rule-classes nil)

(defthm generated-fast-atomic-word-has-atomic-value
  (implies (and (proof-value-p word value base objects packages machine)
                (or (oddp word) (equal (proof-word-tag word) 4)))
           (if (oddp word)
               (proof-immediate-integer-p value)
             (characterp value)))
  :hints (("Goal"
           :use (generated-odd-word-has-immediate-integer-encoding generated-tagged-character-has-standard-encoding)
           :expand (:free (depth) (proof-view-step :word word 0 depth base objects packages machine))
           :in-theory (enable proof-value-p proof-view)))
  :rule-classes nil)
