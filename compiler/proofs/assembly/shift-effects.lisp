(in-package "BOYMOO-PROOFS")

(include-book "word-transfers")
(include-book "signed-fields")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable ash floor mod expt logbitp
                           acl2::binary-logand acl2::binary-logior
                           assembly-power-of-two assembly-cat assembly-low assembly-high
                           boymoo-model::a64-unsigned)))

(local
 (defthm assembly-high-of-unsigned-value
   (implies (and (natp width) (natp shift) (<= shift width)
                 (unsigned-byte-p width value))
            (unsigned-byte-p (- width shift) (assembly-high shift value)))
   :hints (("Goal"
            :cases ((<= (floor value (assembly-power-of-two shift)) -1))
            :use ((:instance assembly-floor-bounds
                             (x value) (d (assembly-power-of-two shift)))
                  (:instance assembly-power-of-two-of-sum (a shift) (b (- width shift)))
                  (:instance assembly-scale-order
                             (a (floor value (assembly-power-of-two shift)))
                             (b (assembly-power-of-two (- width shift)))
                             (d (assembly-power-of-two shift)))
                  (:instance assembly-scale-order
                             (a 0) (b (+ 1 (floor value (assembly-power-of-two shift))))
                             (d (assembly-power-of-two shift))))
            :in-theory (e/d (assembly-high)
                            (unsigned-byte-p assembly-power-of-two-of-sum))))))

(local
 (defthm assembly-nonnegative-remainder-within-divisor
   (implies (and (natp value) (posp divisor) (< value divisor))
            (equal (mod value divisor) value))
   :hints (("Goal"
            :use ((:instance assembly-floor-unique (x value) (d divisor) (q 0)))
            :in-theory (enable mod)))))

(local
 (defthm assembly-shift-amount-double-negative
   (implies (rationalp amount)
            (equal (- (- amount)) amount))
   :hints (("Goal" :use ((:instance assembly-add-cancel (a (- amount)) (b amount)))
                   :in-theory (disable assembly-add-cancel)))))

(local
 (defthm assembly-join-by-oring-shift
   (implies (and (natp width) (natp low) (< low (assembly-power-of-two width))
                 (integerp high))
            (equal (logior low (* high (assembly-power-of-two width)))
                   (assembly-cat width low high)))
   :hints (("Goal" :use (assembly-logior-disjoint-fields)
                   :in-theory (e/d (assembly-cat) (assembly-logior-disjoint-fields))))))

(defthm assembly-rotate-right-fields
  (implies (and (posp width) (natp amount) (< amount width)
                (unsigned-byte-p width value))
           (equal (boymoo-model::a64-ror width value amount)
                  (assembly-cat (- width amount) (assembly-high amount value)
                                (assembly-low amount value))))
  :hints (("Goal"
           :cases ((equal amount 0))
           :use ((:instance assembly-high-of-unsigned-value (shift amount))
                 (:instance assembly-join-by-oring-shift
                            (width (- width amount)) (low (assembly-high amount value)) (high value)))
           :in-theory (disable unsigned-byte-p assembly-high-of-unsigned-value
                               assembly-join-by-oring-shift))))

(local
 (defthm assembly-ror-result-fits
   (implies (posp width) (unsigned-byte-p width (boymoo-model::a64-ror width value amount)))
   :hints (("Goal" :in-theory (disable unsigned-byte-p)))))

(local
 (defthm assembly-rotate-right-low-fields
   (implies (and (posp width) (natp amount) (< amount width)
                 (unsigned-byte-p width value))
            (equal (assembly-low (- width amount) (boymoo-model::a64-ror width value amount))
                   (assembly-high amount value)))
   :hints (("Goal"
            :use (assembly-rotate-right-fields
                  (:instance assembly-high-of-unsigned-value (shift amount)))
            :in-theory (disable assembly-high-of-unsigned-value assembly-rotate-right-fields
                                unsigned-byte-p boymoo-model::a64-ror)))))

(local
 (defthm assembly-read-64-bit-register-fits
   (unsigned-byte-p 64 (boymoo-model::a64-read-reg rn 64 use-sp machine))
   :hints (("Goal" :in-theory (disable unsigned-byte-p)))))

(defthm assembly-bitfield-logical-right-effect
  (implies (unsigned-byte-p 6 amount)
           (equal (boymoo-model::a64-exec-bitfield
                   2 64 rd rn amount 63 (1- (expt 2 64))
                   (1- (assembly-power-of-two (- 64 amount))) machine)
                  (boymoo-model::a64-write-reg
                   rd 64 nil
                   (assembly-high amount (boymoo-model::a64-read-reg rn 64 nil machine)) machine)))
  :hints (("Goal"
           :use ((:instance assembly-ror-result-fits
                            (width 64) (value (boymoo-model::a64-read-reg rn 64 nil machine)))
                 (:instance assembly-rotate-right-low-fields
                            (width 64) (value (boymoo-model::a64-read-reg rn 64 nil machine)))
                 (:instance assembly-read-64-bit-register-fits (use-sp nil)))
           :in-theory (disable unsigned-byte-p assembly-ror-result-fits
                               assembly-rotate-right-fields assembly-rotate-right-low-fields
                               assembly-read-64-bit-register-fits
                               boymoo-model::a64-ror boymoo-model::a64-read-reg
                               boymoo-model::a64-write-reg))))

(local
 (defthm assembly-left-shift-rotation-amount
   (implies (unsigned-byte-p 6 amount)
            (equal (assembly-low 6 (- amount))
                   (if (equal amount 0) 0 (- 64 amount))))
   :hints (("Goal" :cases ((equal amount 0))))))

(local
 (defthm assembly-upper-mask-field-value
   (implies (unsigned-byte-p 6 amount)
            (equal (assembly-cat amount 0 (1- (assembly-power-of-two (- 64 amount))))
                   (- (expt 2 64) (assembly-power-of-two amount))))
   :hints (("Goal"
            :use ((:instance assembly-power-of-two-of-sum (a amount) (b (- 64 amount))))
            :in-theory (enable assembly-cat)))))

(local
 (defthm assembly-upper-mask-fields
   (implies (unsigned-byte-p 6 amount)
            (let ((mask (- (expt 2 64) (assembly-power-of-two amount))))
              (and (equal (assembly-low amount mask) 0)
                   (equal (assembly-high amount mask) (1- (assembly-power-of-two (- 64 amount)))))))
   :hints (("Goal"
            :use (assembly-upper-mask-field-value
                  (:instance assembly-low-of-cat
                             (width amount) (low 0) (high (1- (assembly-power-of-two (- 64 amount)))))
                  (:instance assembly-high-of-cat
                             (width amount) (low 0) (high (1- (assembly-power-of-two (- 64 amount))))))
            :in-theory (disable assembly-upper-mask-field-value
                                assembly-low-of-cat assembly-high-of-cat)))))

(local
 (defthm assembly-shifted-word-fields
   (implies (and (unsigned-byte-p 6 amount) (integerp value))
            (equal (assembly-low 64 (* value (assembly-power-of-two amount)))
                   (assembly-cat amount 0 (assembly-low (- 64 amount) value))))
   :hints (("Goal"
            :use ((:instance assembly-split-above-cat (n amount) (width 64) (low 0) (high value)))
            :in-theory (e/d (assembly-cat) (assembly-split-above-cat))))))

(local
 (defthm assembly-left-shift-from-rotation-and-mask
   (implies (and (unsigned-byte-p 6 amount) (unsigned-byte-p 64 value))
            (equal (logand (boymoo-model::a64-ror 64 value (assembly-low 6 (- amount)))
                           (- (expt 2 64) (assembly-power-of-two amount)))
                   (assembly-low 64 (* value (assembly-power-of-two amount)))))
   :hints (("Goal"
            :cases ((equal amount 0))
            :use (assembly-upper-mask-fields
                  (:instance assembly-high-of-unsigned-value (width 64) (shift (- 64 amount))))
            :in-theory (disable unsigned-byte-p assembly-high-of-unsigned-value
                                assembly-upper-mask-fields
                                boymoo-model::a64-ror)))))

(defthm assembly-bitfield-logical-left-effect
  (implies (unsigned-byte-p 6 amount)
           (equal (boymoo-model::a64-exec-bitfield
                   2 64 rd rn (assembly-low 6 (- amount)) (- 63 amount)
                   (- (expt 2 64) (assembly-power-of-two amount)) (1- (expt 2 64)) machine)
                  (boymoo-model::a64-write-reg
                   rd 64 nil
                   (assembly-low 64 (* (boymoo-model::a64-read-reg rn 64 nil machine)
                                       (assembly-power-of-two amount))) machine)))
  :hints (("Goal"
           :use ((:instance assembly-left-shift-from-rotation-and-mask
                            (value (boymoo-model::a64-read-reg rn 64 nil machine)))
                 (:instance assembly-read-64-bit-register-fits (use-sp nil)))
           :in-theory (disable unsigned-byte-p assembly-left-shift-from-rotation-and-mask
                               assembly-left-shift-rotation-amount assembly-rotate-right-fields
                               assembly-read-64-bit-register-fits
                               boymoo-model::a64-ror boymoo-model::a64-read-reg
                               boymoo-model::a64-write-reg))))

(local
 (defthm assembly-rotate-and-mask-for-right-shift
   (implies (and (unsigned-byte-p 6 amount) (unsigned-byte-p 64 value))
            (equal (logand (logand (boymoo-model::a64-ror 64 value amount) (1- (expt 2 64)))
                           (1- (assembly-power-of-two (- 64 amount))))
                   (assembly-high amount value)))
   :hints (("Goal"
            :use ((:instance assembly-ror-result-fits (width 64))
                  (:instance assembly-rotate-right-low-fields (width 64)))
            :in-theory (disable unsigned-byte-p assembly-ror-result-fits
                                assembly-rotate-right-fields assembly-rotate-right-low-fields
                                boymoo-model::a64-ror)))))

(local
 (defthm assembly-logand-commutes
   (implies (and (integerp x) (integerp y))
            (equal (logand x y) (logand y x)))
   :hints (("Goal" :induct (logand x y)
                   :in-theory (enable acl2::binary-logand)))
   :rule-classes nil))

(local
 (defthm assembly-logior-high-and-low-fields
   (implies (and (natp width) (natp low) (< low (assembly-power-of-two width))
                 (integerp high))
            (equal (logior (assembly-cat width 0 high) low)
                   (assembly-cat width low high)))
   :hints (("Goal"
            :use (assembly-logior-disjoint-fields
                  (:instance assembly-logand-commutes
                             (x (lognot (assembly-cat width 0 high))) (y (lognot low))))
            :in-theory (e/d (acl2::binary-logior)
                            (assembly-logior-disjoint-fields))))))

(local
 (defthm assembly-lognot-of-low-mask
   (equal (lognot (1- (assembly-power-of-two width)))
          (assembly-cat width 0 -1))
   :hints (("Goal" :in-theory (enable lognot assembly-cat)))))

(local
 (defthm assembly-subtract-top-of-word
   (implies (and (unsigned-byte-p 6 amount) (integerp value))
            (equal (- value (expt 2 64))
                   (assembly-cat amount (assembly-low amount value)
                                 (- (assembly-high amount value)
                                    (assembly-power-of-two (- 64 amount))))))
   :hints (("Goal"
            :use ((:instance assembly-power-of-two-of-sum (a amount) (b (- 64 amount)))
                  (:instance assembly-cat-of-low-and-high (width amount) (x value)))
            :in-theory (e/d (assembly-cat)
                            (unsigned-byte-p assembly-power-of-two-of-sum assembly-cat-of-low-and-high))))
   :rule-classes nil))

(local
 (defthm assembly-shift-after-subtracting-top-of-word
   (implies (and (unsigned-byte-p 6 amount) (integerp value))
            (equal (assembly-high amount (- value (expt 2 64)))
                   (- (assembly-high amount value) (assembly-power-of-two (- 64 amount)))))
   :hints (("Goal" :use assembly-subtract-top-of-word
                   :in-theory (disable unsigned-byte-p)))))

(local
 (defthm assembly-signed-shift-value
   (implies (and (unsigned-byte-p 6 amount) (unsigned-byte-p 64 value))
            (equal (assembly-high amount (boymoo-model::a64-signed 64 value))
                   (if (logbitp 63 value)
                       (- (assembly-high amount value) (assembly-power-of-two (- 64 amount)))
                     (assembly-high amount value))))
   :hints (("Goal" :use (assembly-shift-after-subtracting-top-of-word)
                   :in-theory (disable unsigned-byte-p assembly-shift-after-subtracting-top-of-word)))))

(local
 (defthm assembly-cat-sign-extension
   (implies (integerp value)
            (equal (assembly-cat width value -1)
                   (- value (assembly-power-of-two width))))
   :hints (("Goal" :in-theory (enable assembly-cat)))))

(defthm assembly-bitfield-arithmetic-right-effect
  (implies (unsigned-byte-p 6 amount)
           (equal (boymoo-model::a64-exec-bitfield
                   0 64 rd rn amount 63 (1- (expt 2 64))
                   (1- (assembly-power-of-two (- 64 amount))) machine)
                  (boymoo-model::a64-write-reg
                   rd 64 nil
                   (assembly-high amount (boymoo-model::a64-signed
                                          64 (boymoo-model::a64-read-reg rn 64 nil machine)))
                   machine)))
  :hints (("Goal"
           :use ((:instance assembly-rotate-and-mask-for-right-shift
                            (value (boymoo-model::a64-read-reg rn 64 nil machine)))
                 (:instance assembly-high-of-unsigned-value
                            (width 64) (shift amount)
                            (value (boymoo-model::a64-read-reg rn 64 nil machine)))
                 (:instance assembly-logior-high-and-low-fields
                            (width (- 64 amount)) (high -1)
                            (low (assembly-high amount (boymoo-model::a64-read-reg rn 64 nil machine))))
                 (:instance assembly-read-64-bit-register-fits (use-sp nil)))
           :in-theory (disable unsigned-byte-p assembly-rotate-and-mask-for-right-shift
                               assembly-rotate-right-fields assembly-high-of-unsigned-value
                               assembly-logior-high-and-low-fields
                               assembly-read-64-bit-register-fits
                               boymoo-model::a64-ror boymoo-model::a64-signed
                               boymoo-model::a64-read-reg boymoo-model::a64-write-reg))))
