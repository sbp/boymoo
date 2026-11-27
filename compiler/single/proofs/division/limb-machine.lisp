(in-package "BOYMOO-PROOFS")

(include-book "effects")
(include-book "limbs")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable ash floor mod acl2::binary-logand
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defthm division-digit-mask-value
  (implies (integerp word)
           (equal (logand word #xffffffff) (mod word *division-radix*)))
  :hints (("Goal" :use (:instance division-mask-is-remainder (width 32) (x word)))))

(defthm division-two-limb-word-fits
  (implies (and (division-digit-p low) (division-digit-p high))
           (unsigned-byte-p 64 (+ low (* *division-radix* high)))))

(defthm division-high-limb-fits
  (implies (unsigned-byte-p 64 word)
           (division-digit-p (floor word *division-radix*)))
  :hints (("Goal" :use (:instance division-floor-bounds (a word) (b *division-radix*)))))

(defthm division-floor-of-word-fits
  (implies (and (unsigned-byte-p 64 word) (posp divisor))
           (unsigned-byte-p 64 (floor word divisor)))
  :hints (("Goal"
           :use (:instance division-floor-at-least
                           (a word) (b divisor) (q *division-word-modulus*)))))

(defthm division-limb-scale-fits
  (implies (and (natp shift) (< shift 32))
           (and (posp (expt 2 shift))
                (< (expt 2 shift) *division-radix*)))
  :hints (("Goal"
           :use ((:instance division-power-of-two-positive (width shift))
                 (:instance division-power-of-two-positive (width (- 32 shift)))
                 (:instance division-power-of-two-step (width (- 32 shift)))
                 (:instance division-power-of-two-positive (width (- 31 shift)))
                 (:instance division-power-of-two-sum (left shift) (right (- 32 shift))))
           :in-theory (disable expt)
           :nonlinearp t))
  :rule-classes nil)

(defthm division-limb-borrow-is-word-sign
  (implies (and (division-digit-p a) (division-digit-p b))
           (equal (ash (boymoo-model::a64-unsigned 64 (- a b)) -63)
                  (if (< a b) 1 0)))
  :hints (("Goal"
           :cases ((< a b))
           :use ((:instance division-negative-in-word (value (- a b)))
                 (:instance division-signed-quotient-unique
                            (a (+ *division-word-modulus* a (- b))) (b *division-word-half*)
                            (q 1) (r (+ *division-word-half* a (- b)))))))
  :rule-classes nil)

(defthm division-limb-difference-mask
  (implies (and (division-digit-p a) (division-digit-p b))
           (equal (logand (boymoo-model::a64-unsigned 64 (- a b)) #xffffffff)
                  (+ (- a b) (if (< a b) *division-radix* 0))))
  :hints (("Goal"
           :cases ((< a b))
           :use ((:instance division-narrower-mask-of-word (value (- a b)) (width 32))
                 (:instance division-digit-mask-value (word (boymoo-model::a64-unsigned 64 (- a b))))
                 (:instance division-signed-remainder-unique (a (- a b)) (b *division-radix*)
                            (q -1) (r (+ *division-radix* a (- b)))))
           :in-theory (e/d (division-a64-unsigned-is-remainder)
                           (division-narrower-mask-of-word division-digit-mask-value)))))
