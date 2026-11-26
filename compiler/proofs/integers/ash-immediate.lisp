(in-package "BOYMOO-PROOFS")

; The arithmetic of the right-shift branch of the entry for ASH on an
; immediate integer.  The branch, at the label rt:ash-right in
; compiler/runtime.lisp, takes the tagged word of an immediate integer
; V and a negated shift count K, limits K to 63, shifts the tagged word
; right arithmetically, clears its low bit and adds one.

(include-book "bits")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt oddp evenp logbitp
                           boymoo-model::a64-unsigned boymoo-model::a64-signed)))

(local
 (defthm integer-ash-product-negation
   (implies (and (rationalp a) (rationalp b))
            (equal (* a (- b)) (- (* a b))))
   :hints (("Goal" :in-theory (disable distributivity)
            :use ((:instance distributivity (acl2::x a)
                                            (acl2::y b) (acl2::z (- b))))))))

(defthm integer-floor-is-integer
  (implies (and (integerp x) (integerp d))
           (integerp (floor x d)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable floor))))

(defthm integer-floor-of-floor-by-two
  (implies (and (integerp x) (posp d))
           (equal (floor (floor x d) 2) (floor x (* 2 d))))
  :hints (("Goal"
           :use ((:instance integer-floor-scaled-bounds (y d))
                 (:instance integer-floor-scaled-bounds (x (floor x d)) (y 2))
                 (:instance integer-floor-unique
                            (y (* 2 d)) (q (floor (floor x d) 2))))
           :nonlinearp t)))

(defthm integer-floor-of-odd-double
  (implies (and (integerp v) (posp d))
           (equal (floor (+ 1 (* 2 v)) (* 2 d)) (floor v d)))
  :hints (("Goal"
           :use ((:instance integer-floor-scaled-bounds (x v) (y d))
                 (:instance integer-floor-unique
                            (x (+ 1 (* 2 v))) (y (* 2 d)) (q (floor v d))))
           :nonlinearp t)))

(defthm integer-floor-plus-even
  (implies (and (integerp x) (integerp j))
           (equal (floor (+ x (* 2 j)) 2) (+ j (floor x 2))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance integer-floor-scaled-bounds (y 2))
                 (:instance integer-floor-unique
                            (x (+ x (* 2 j))) (y 2) (q (+ j (floor x 2))))))))

(defthm integer-mod-minus-multiple
  (implies (and (integerp z) (integerp tt) (posp m))
           (equal (mod (- z (* m tt)) m) (mod z m)))
  :hints (("Goal"
           :use ((:instance integer-floor-and-mod-decomposition (x z) (d m))
                 (:instance integer-mod-unique
                            (x (- z (* m tt))) (d m)
                            (q (- (floor z m) tt)) (r (mod z m)))))))

(defthm integer-mod-as-difference
  (implies (and (integerp x) (posp d))
           (equal (mod x d) (- x (* d (floor x d)))))
  :rule-classes nil
  :hints (("Goal" :use integer-floor-and-mod-decomposition)))

(defthm integer-floor-half-of-mod
  (implies (and (integerp r) (posp h))
           (equal (floor (mod r (* 2 h)) 2)
                  (- (floor r 2) (* h (floor r (* 2 h))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance integer-mod-as-difference (x r) (d (* 2 h)))
                 (:instance integer-floor-plus-even
                            (x r) (j (- (* h (floor r (* 2 h))))))))))

(defthm integer-clear-low-bit-generic
  (implies (and (integerp r) (posp h))
           (equal (mod (+ 1 (* 2 (floor (mod r (* 2 h)) 2))) (* 2 h))
                  (mod (+ 1 (* 2 (floor r 2))) (* 2 h))))
  :rule-classes nil
  :hints (("Goal"
           :use (integer-floor-half-of-mod
                 (:instance integer-mod-minus-multiple
                            (z (+ 1 (* 2 (floor r 2))))
                            (m (* 2 h)) (tt (floor r (* 2 h))))))))

; Clearing the low bit of the 64-bit pattern of R and adding one gives
; the pattern of twice the floor of half of R, plus one.
(defthm integer-clear-low-bit-of-pattern
  (implies (integerp r)
           (equal (mod (+ 1 (* 2 (floor (mod r (expt 2 64)) 2))) (expt 2 64))
                  (mod (+ 1 (* 2 (floor r 2))) (expt 2 64))))
  :hints (("Goal"
           :use ((:instance integer-clear-low-bit-generic (h (expt 2 63)))))))

(local
 (defthm integer-sum-cancel
   (implies (acl2-numberp b)
            (equal (+ a (- a) b) b))))

(defthm integer-power-of-two-at-least
  (implies (and (natp a) (natp b) (<= a b))
           (<= (expt 2 a) (expt 2 b)))
  :rule-classes :linear
  :hints (("Goal" :use ((:instance integer-power-of-two-add (b (- b a)))
                        (:instance integer-power-of-two-is-positive
                                   (width (- b a))))
           :nonlinearp t)))

(defthm integer-floor-of-immediate-by-large-power
  (implies (and (proof-immediate-integer-p v) (natp k) (<= 62 k))
           (equal (floor v (expt 2 k)) (if (< v 0) -1 0)))
  :hints (("Goal" :cases ((< v 0))
           :use ((:instance integer-power-of-two-at-least (a 62) (b k))))))

(defthm integer-floor-of-immediate-is-immediate
  (implies (and (proof-immediate-integer-p v) (posp d))
           (proof-immediate-integer-p (floor v d)))
  :hints (("Goal"
           :use ((:instance integer-floor-scaled-bounds (x v) (y d)))
           :cases ((< v 0))
           :nonlinearp t)))

(defthm integer-immediate-is-integer
  (implies (proof-immediate-integer-p v)
           (integerp v))
  :rule-classes :forward-chaining)

(defun integer-ash-right-limit (k)
  (if (< 63 k) 63 k))

; The right-shift branch of the ASH entry on an immediate integer V and
; a positive shift count K gives the tagged word of (ash V (- K)), and
; that integer is immediate.  The shift is the model's arithmetic shift
; right (a64-shift of kind 2), by K limited to 63, applied to the tagged
; word of V.  Clearing the low bit is written as twice the floor of
; half, and adding one is modulo 2 to the 64th power.
(defthm integer-ash-immediate-right-shift
  (implies (and (proof-immediate-integer-p v) (posp k))
           (let* ((shifted (boymoo-model::a64-shift
                            2 64 (proof-integer-word v)
                            (integer-ash-right-limit k)))
                  (result (boymoo-model::a64-unsigned
                           64 (+ 1 (* 2 (floor shifted 2))))))
             (and (proof-immediate-integer-p (ash v (- k)))
                  (equal result (proof-integer-word (ash v (- k)))))))
  :hints (("Goal"
           :in-theory (e/d (integer-ash-right)
                           (proof-immediate-integer-p
                            integer-ash-left))
           :cases ((< 63 k))
           :use ((:instance integer-immediate-word-signed (value v))
                 (:instance integer-clear-low-bit-of-pattern
                            (r (floor (+ 1 (* 2 v))
                                      (expt 2 (integer-ash-right-limit k)))))
                 (:instance integer-floor-of-floor-by-two
                            (x (+ 1 (* 2 v)))
                            (d (expt 2 (integer-ash-right-limit k))))
                 (:instance integer-floor-of-odd-double
                            (d (expt 2 (integer-ash-right-limit k))))
                 (:instance integer-floor-of-immediate-by-large-power (k 63))
                 (:instance integer-floor-of-immediate-is-immediate
                            (d (expt 2 k)))))))
