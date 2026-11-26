(in-package "BOYMOO-PROOFS")

(include-book "encodings")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt logbitp
                           assembly-high assembly-low assembly-cat assembly-power-of-two
                           boymoo-model::a64-unsigned)))

(defthm assembly-high-of-multiple
  (implies (and (integerp factor) (integerp value)
                (equal factor (assembly-power-of-two width)))
           (equal (assembly-high width (* factor value)) value))
  :hints (("Goal"
           :use ((:instance assembly-floor-unique
                            (x (* factor value)) (d (assembly-power-of-two width)) (q value)))
           :in-theory (enable assembly-high))))

(defthm assembly-high-of-multiple-of-power
  (implies (integerp value)
           (equal (assembly-high width (* value (assembly-power-of-two width))) value))
  :hints (("Goal" :use ((:instance assembly-high-of-multiple
                                   (factor (assembly-power-of-two width))))
                  :in-theory (disable assembly-high-of-multiple))))

(defthm assembly-high-of-fitting-negative
  (implies (and (integerp value) (<= (- (assembly-power-of-two width)) value) (< value 0))
           (equal (assembly-high width value) -1))
  :hints (("Goal"
           :use ((:instance assembly-floor-unique
                            (x value) (d (assembly-power-of-two width)) (q -1)))
           :in-theory (enable assembly-high))))

(defthm assembly-low-of-fitting-negative
  (implies (and (integerp value) (<= (- (assembly-power-of-two width)) value) (< value 0))
           (equal (assembly-low width value) (+ value (assembly-power-of-two width))))
  :hints (("Goal" :use (assembly-high-of-fitting-negative)
                  :in-theory (e/d (mod assembly-high assembly-low)
                                  (assembly-high-of-fitting-negative)))))

(defthm assembly-signed-width
  (equal (signed-byte-p width value)
         (and (posp width) (integerp value)
              (<= (- (assembly-power-of-two (1- width))) value)
              (< value (assembly-power-of-two (1- width)))))
  :hints (("Goal" :in-theory (enable assembly-power-of-two))))

(defthm assembly-sign-of-signed-field
  (implies (signed-byte-p width value)
           (equal (assembly-high (1- width) value) (if (< value 0) -1 0)))
  :hints (("Goal" :cases ((< value 0))
                  :in-theory (disable signed-byte-p))))

(local
 (defthm assembly-ash-for-sign
   (implies (and (integerp value) (posp width))
            (equal (ash value (- 1 width))
                   (assembly-high (1- width) value)))
   :hints (("Goal" :use ((:instance assembly-ash-right (width (1- width))))
                   :in-theory (disable assembly-ash-right)))))

(defthm assembly-signed-field-encoding
  (implies (and (integerp factor)
                (equal factor (assembly-power-of-two scale))
                (natp scale) (signed-byte-p width value))
           (equal (boymoo-compiler::a64-signed-scaled (* factor value) scale width)
                  (assembly-low width value)))
  :hints (("Goal"
           :in-theory (disable signed-byte-p))))

(defthm assembly-unscaled-signed-field-encoding
  (implies (signed-byte-p width value)
           (equal (boymoo-compiler::a64-signed-scaled value 0 width)
                  (assembly-low width value)))
  :hints (("Goal"
           :use ((:instance assembly-signed-field-encoding (scale 0) (factor 1)))
           :in-theory (disable signed-byte-p assembly-signed-field-encoding
                               boymoo-compiler::a64-signed-scaled))))

(defthm assembly-encoded-signed-field-fits
  (implies (natp width)
           (unsigned-byte-p width (assembly-low width value)))
  :hints (("Goal" :use assembly-low-bounds :in-theory (disable unsigned-byte-p))))

(local
 (defthm assembly-signed-field-bits
   (implies (signed-byte-p width value)
            (equal (assembly-low width value)
                   (if (< value 0) (+ value (assembly-power-of-two width)) value)))
   :hints (("Goal" :cases ((< value 0))
                   :use assembly-power-of-two-step
                   :in-theory (disable signed-byte-p)))))

(local
 (defthm assembly-signed-field-top-bit
   (implies (signed-byte-p width value)
            (equal (assembly-high (1- width) (assembly-low width value))
                   (if (< value 0) 1 0)))
   :hints (("Goal" :cases ((< value 0))
                   :use (assembly-power-of-two-step assembly-signed-field-bits
                         (:instance assembly-high-of-fitting-value (width (1- width)))
                         (:instance assembly-floor-unique
                                    (x (assembly-low width value))
                                    (d (assembly-power-of-two (1- width)))
                                    (q 1)))
                   :in-theory (e/d (assembly-high)
                                   (signed-byte-p assembly-signed-field-bits
                                    assembly-high-of-fitting-value))))
   :rule-classes nil))

(defthm assembly-decode-signed-field
  (implies (signed-byte-p width value)
           (equal (boymoo-model::a64-signed width (assembly-low width value)) value))
  :hints (("Goal"
           :use (assembly-signed-field-top-bit assembly-signed-field-bits)
           :in-theory (e/d (boymoo-model::a64-signed)
                           (signed-byte-p assembly-signed-field-bits assembly-low-of-fitting-negative)))))
