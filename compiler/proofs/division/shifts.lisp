(in-package "BOYMOO-PROOFS")

(include-book "bitfields")
(include-book "normalization")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod ash expt acl2::binary-logand acl2::binary-logior
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(local
 (defthm division-remainder-of-multiple-remainder
   (implies (and (integerp value) (posp scale) (posp divisor))
            (equal (mod (mod value (* scale divisor)) divisor) (mod value divisor)))
   :hints (("Goal"
            :use ((:instance division-floor-mod-identity (a value) (b (* scale divisor)))
                  (:instance division-floor-mod-identity (a (mod value (* scale divisor))) (b divisor))
                  (:instance division-signed-mod-bounds (a (mod value (* scale divisor))) (b divisor))
                  (:instance division-signed-floor-integer (a value) (b (* scale divisor)))
                  (:instance division-signed-floor-integer (a (mod value (* scale divisor))) (b divisor))
                  (:instance division-signed-remainder-unique
                             (a value) (b divisor)
                             (q (+ (* scale (floor value (* scale divisor)))
                                   (floor (mod value (* scale divisor)) divisor)))
                             (r (mod (mod value (* scale divisor)) divisor))))
            :in-theory (disable division-floor-mod-identity)
            :do-not-induct t))))

(defthm division-narrower-mask-of-word
  (implies (and (integerp value) (natp width) (<= width 64))
           (equal (boymoo-model::a64-unsigned width (boymoo-model::a64-unsigned 64 value))
                  (boymoo-model::a64-unsigned width value)))
  :hints (("Goal"
           :use ((:instance division-power-of-two-sum (left width) (right (- 64 width)))
                 (:instance division-remainder-of-multiple-remainder
                            (scale (expt 2 (- 64 width))) (divisor (expt 2 width)))
                 (:instance division-signed-mod-bounds (a value) (b (expt 2 64)))
                 (:instance division-power-of-two-positive (width (- 64 width)))
                 (:instance division-power-of-two-positive))
           :in-theory (enable division-a64-unsigned-is-remainder))))

(local
 (defthm division-mask-clears-disjoint-high-part
   (implies (and (natp width) (unsigned-byte-p width low) (integerp high))
            (equal (boymoo-model::a64-unsigned width (logior low (* high (expt 2 width))))
                   low))
   :hints (("Goal"
            :use ((:instance division-logior-of-disjoint-fields)
                  (:instance division-signed-remainder-unique
                             (a (+ low (* high (expt 2 width)))) (b (expt 2 width))
                             (q high) (r low)))
            :in-theory (enable division-a64-unsigned-is-remainder)))))

(defthm division-right-shift-fits-remaining-bits
  (implies (and (natp shift) (<= shift 64) (unsigned-byte-p 64 word))
           (unsigned-byte-p (- 64 shift) (ash word (- shift))))
  :hints (("Goal"
           :use ((:instance division-power-of-two-sum (left shift) (right (- 64 shift)))
                 (:instance division-ash-right (width shift) (x word))
                 (:instance division-floor-bounds (a word) (b (expt 2 shift))))
           :in-theory (disable division-ash-right)
           :nonlinearp t))
  :rule-classes nil)

(defthm division-right-shift-bitfield
  (implies (and (natp shift) (< shift 64) (unsigned-byte-p 64 word))
           (equal (boymoo-model::a64-unsigned
                   (- 64 shift) (boymoo-model::a64-ror 64 word shift))
                  (ash word (- shift))))
  :hints (("Goal"
           :use ((:instance division-right-shift-fits-remaining-bits)
                 (:instance division-ash-left (width (- 64 shift)) (x word)))
           :in-theory (enable boymoo-model::a64-ror))))

(defthm division-unsigned-mask-is-logand
  (implies (and (natp width) (integerp word))
           (equal (logand word (1- (expt 2 width)))
                  (boymoo-model::a64-unsigned width word)))
  :hints (("Goal"
           :use (:instance division-ash-left (width width) (x 1))
           :in-theory (enable boymoo-model::a64-unsigned))))
