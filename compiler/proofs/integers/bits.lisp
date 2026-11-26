(in-package "BOYMOO-PROOFS")

(include-book "representation")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt oddp evenp logbitp
                           acl2::binary-logand acl2::binary-logior acl2::binary-logxor)))

(defthm integer-floor-of-in-range
  (implies (and (natp x) (posp d) (< x d))
           (equal (floor x d) 0))
  :hints (("Goal" :use ((:instance integer-floor-unique (y d) (q 0))))))

(defthm integer-floor-of-negative-in-range
  (implies (and (integerp x) (posp d) (<= (- d) x) (< x 0))
           (equal (floor x d) -1))
  :hints (("Goal" :use ((:instance integer-floor-unique (y d) (q -1))))))

(local
 (defthm integer-bit-product-negation
   (implies (and (rationalp a) (rationalp b))
            (equal (* a (- b)) (- (* a b))))
   :hints (("Goal" :in-theory (disable distributivity)
            :use ((:instance distributivity (acl2::x a)
                                            (acl2::y b) (acl2::z (- b))))))))

(defthm integer-lognot-half
  (implies (integerp x)
           (equal (floor (lognot x) 2) (lognot (floor x 2))))
  :hints (("Goal"
           :use ((:instance integer-floor-and-mod-decomposition (d 2))
                 (:instance integer-floor-unique
                            (x (lognot x)) (y 2) (q (lognot (floor x 2))))))))

(defthm integer-lognot-odd
  (implies (integerp x)
           (equal (oddp (lognot x)) (not (oddp x))))
  :hints (("Goal"
           :use ((:instance integer-floor-and-mod-decomposition (d 2))
                 (:instance integer-mod-unique
                            (x (lognot x)) (d 2)
                            (q (lognot (floor x 2))) (r (- 1 (mod x 2))))))))

(local
 (defthm integer-lognot-of-double-plus-bit
   (implies (and (integerp high) (bitp low))
            (equal (lognot (+ (* 2 high) low))
                   (+ (* 2 (lognot high)) (- 1 low))))))

(local (in-theory (disable lognot)))

(defthmd integer-logior-split
  (implies (and (integerp x) (integerp y))
           (equal (logior x y)
                  (+ (* 2 (logior (floor x 2) (floor y 2)))
                     (if (or (oddp x) (oddp y)) 1 0))))
  :hints (("Goal" :in-theory (e/d (acl2::binary-logior) (integer-oddp-by-remainder))
           :use ((:instance integer-logand-split (x (lognot x)) (y (lognot y)))
                 (:instance integer-lognot-of-double-plus-bit
                            (high (logand (lognot (floor x 2)) (lognot (floor y 2))))
                            (low (if (and (not (oddp x)) (not (oddp y))) 1 0)))))))

(local
 (defthm integer-logior-half
   (implies (and (integerp x) (integerp y))
            (equal (floor (logior x y) 2)
                   (logior (floor x 2) (floor y 2))))
   :hints (("Goal"
            :use (integer-logior-split
                  (:instance integer-floor-of-double-plus-bit
                             (high (logior (floor x 2) (floor y 2)))
                             (low (if (or (oddp x) (oddp y)) 1 0))))))))

(local
 (defthm integer-logior-odd
   (implies (and (integerp x) (integerp y))
            (equal (oddp (logior x y)) (if (oddp x) t (oddp y))))
   :hints (("Goal"
            :use (integer-logior-split
                  (:instance integer-mod-of-double-plus-bit
                             (high (logior (floor x 2) (floor y 2)))
                             (low (if (or (oddp x) (oddp y)) 1 0))))))))

(defun integer-bit-xor (x y)
  (if (equal x y) 0 1))

(defthmd integer-logxor-split
  (implies (and (integerp x) (integerp y))
           (equal (logxor x y)
                  (+ (* 2 (logxor (floor x 2) (floor y 2)))
                     (integer-bit-xor (mod x 2) (mod y 2)))))
  :hints (("Goal" :in-theory (e/d (acl2::binary-logxor acl2::binary-logeqv logorc1)
                           (integer-oddp-by-remainder))
           :use (integer-oddp-by-remainder
                 (:instance integer-oddp-by-remainder (x y))
                 (:instance integer-logand-split
                            (x (logior (lognot x) y))
                            (y (logior (lognot y) x)))
                 (:instance integer-lognot-of-double-plus-bit
                            (high (logand (logior (lognot (floor x 2)) (floor y 2))
                                          (logior (lognot (floor y 2)) (floor x 2))))
                            (low (if (and (or (not (oddp x)) (oddp y))
                                          (or (not (oddp y)) (oddp x)))
                                     1 0)))))))

(defthm integer-logxor-half
  (implies (and (integerp x) (integerp y))
           (equal (floor (logxor x y) 2)
                  (logxor (floor x 2) (floor y 2))))
  :hints (("Goal" :use (integer-logxor-split
                        (:instance integer-floor-of-double-plus-bit
                                   (high (logxor (floor x 2) (floor y 2)))
                                   (low (integer-bit-xor (mod x 2) (mod y 2))))))))

(local
 (defthm integer-logxor-of-bit-pairs
   (implies (and (integerp x) (integerp y) (bitp low-x) (bitp low-y))
            (equal (logxor (+ (* 2 x) low-x) (+ (* 2 y) low-y))
                   (+ (* 2 (logxor x y)) (integer-bit-xor low-x low-y))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance integer-logxor-split
                             (x (+ (* 2 x) low-x)) (y (+ (* 2 y) low-y)))
                  (:instance integer-floor-of-double-plus-bit (high x) (low low-x))
                  (:instance integer-floor-of-double-plus-bit (high y) (low low-y))
                  (:instance integer-mod-of-double-plus-bit (high x) (low low-x))
                  (:instance integer-mod-of-double-plus-bit (high y) (low low-y)))))))

(defthm integer-logxor-of-doubled-integers
  (implies (and (integerp x) (integerp y) (bitp low))
           (equal (logxor (+ (* 2 x) low) (+ (* 2 y) low))
                  (* 2 (logxor x y))))
  :hints (("Goal" :use ((:instance integer-logxor-of-bit-pairs (low-x low) (low-y low))))))

(local
 (defthm integer-mod2-of-logxor
   (implies (and (integerp x) (integerp y))
            (equal (mod (logxor x y) 2)
                   (integer-bit-xor (mod x 2) (mod y 2))))
   :hints (("Goal" :use (integer-logxor-split
                         (:instance integer-mod-of-double-plus-bit
                                    (high (logxor (floor x 2) (floor y 2)))
                                    (low (integer-bit-xor (mod x 2) (mod y 2)))))))))

(local
 (defthm integer-floor-of-halving-and-division
   (implies (and (integerp x) (posp d))
            (equal (floor (floor x 2) d)
                   (floor x (* 2 d))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance integer-floor-and-mod-decomposition (d 2))
                  (:instance integer-floor-and-mod-decomposition (x (floor x 2)))
                  (:instance integer-floor-unique
                             (y (* 2 d)) (q (floor (floor x 2) d))))
            :nonlinearp t))))

(local
 (defthm integer-mod-of-halving-and-division
   (implies (and (integerp x) (posp d))
            (equal (mod x (* 2 d))
                   (+ (mod x 2) (* 2 (mod (floor x 2) d))))) 
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance integer-floor-and-mod-decomposition (d 2))
                  (:instance integer-floor-and-mod-decomposition (x (floor x 2)))
                  (:instance integer-mod-unique
                             (d (* 2 d)) (q (floor (floor x 2) d))
                             (r (+ (mod x 2) (* 2 (mod (floor x 2) d))))))
            :nonlinearp t))))

(local
 (defun integer-logxor-induction (width x y)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       (list x y)
     (integer-logxor-induction (1- width) (floor x 2) (floor y 2)))))

(defthm integer-floor-of-logxor
  (implies (and (integerp x) (integerp y) (natp width))
           (equal (floor (logxor x y) (expt 2 width))
                  (logxor (floor x (expt 2 width))
                          (floor y (expt 2 width)))))
  :hints (("Goal" :induct (integer-logxor-induction width x y))
          ("Subgoal *1/1"
           :use ((:instance integer-floor-unique (x x) (y 1) (q x))
                 (:instance integer-floor-unique (x y) (y 1) (q y))
                 (:instance integer-floor-unique (x (logxor x y)) (y 1) (q (logxor x y)))))
          ("Subgoal *1/2"
           :use (integer-power-of-two-step
                 (:instance integer-floor-of-halving-and-division
                            (x x) (d (expt 2 (1- width))))
                 (:instance integer-floor-of-halving-and-division
                            (x y) (d (expt 2 (1- width))))
                 (:instance integer-floor-of-halving-and-division
                            (x (logxor x y)) (d (expt 2 (1- width))))))))

(defthm integer-mod-of-logxor
  (implies (and (integerp x) (integerp y) (natp width))
           (equal (mod (logxor x y) (expt 2 width))
                  (logxor (mod x (expt 2 width))
                          (mod y (expt 2 width)))))
  :hints (("Goal" :induct (integer-logxor-induction width x y))
          ("Subgoal *1/1"
           :use ((:instance integer-mod-unique (x x) (d 1) (q x) (r 0))
                 (:instance integer-mod-unique (x y) (d 1) (q y) (r 0))
                 (:instance integer-mod-unique (x (logxor x y)) (d 1) (q (logxor x y)) (r 0))))
          ("Subgoal *1/2"
           :use (integer-power-of-two-step
                 (:instance integer-mod-of-halving-and-division
                            (x x) (d (expt 2 (1- width))))
                 (:instance integer-mod-of-halving-and-division
                            (x y) (d (expt 2 (1- width))))
                 (:instance integer-mod-of-halving-and-division
                            (x (logxor x y)) (d (expt 2 (1- width))))
                 (:instance integer-logxor-of-bit-pairs
                            (x (mod (floor x 2) (expt 2 (1- width))))
                            (y (mod (floor y 2) (expt 2 (1- width))))
                            (low-x (mod x 2)) (low-y (mod y 2)))))))

(defthm integer-negative-right-shift-rounds-down
  (implies (and (natp magnitude) (natp shift))
           (equal (ash (- magnitude) (- shift))
                  (- (+ (floor magnitude (expt 2 shift))
                        (if (equal (mod magnitude (expt 2 shift)) 0) 0 1)))))
  :hints (("Goal"
           :in-theory (enable integer-ash-right)
           :use ((:instance integer-floor-and-mod-decomposition
                            (x magnitude) (d (expt 2 shift)))
                 (:instance integer-floor-unique
                            (x (- magnitude)) (y (expt 2 shift))
                            (q (- (floor magnitude (expt 2 shift)))))
                 (:instance integer-floor-unique
                            (x (- magnitude)) (y (expt 2 shift))
                            (q (- (+ 1 (floor magnitude (expt 2 shift)))))))
           :nonlinearp t)))

(defthm integer-right-shift-to-sign
  (implies (and (natp shift) (integerp x)
                (< (- (expt 2 shift)) x)
                (< x (expt 2 shift)))
           (equal (ash x (- shift)) (if (< x 0) -1 0)))
  :hints (("Goal" :in-theory (enable integer-ash-right))))
