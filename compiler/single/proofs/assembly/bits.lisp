(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt evenp
                           acl2::binary-logand acl2::binary-logior lognot)))

(local
 (defthm assembly-quotient-bounds
   (implies (and (natp n) (posp d))
            (and (<= (* d (nonnegative-integer-quotient n d)) n)
                 (< n (* d (+ 1 (nonnegative-integer-quotient n d))))))
   :hints (("Goal" :induct (nonnegative-integer-quotient n d)))
   :rule-classes nil))

(local
 (defthm assembly-multiply-equality
   (implies (equal y z)
            (equal (* d y) (* d z)))
   :rule-classes nil))

(local
 (defthm assembly-cancel-division
   (implies (and (rationalp d) (not (equal d 0)))
            (equal (* d (* (/ d) n)) (fix n)))
   :hints (("Goal" :use ((:instance acl2::associativity-of-*
                                    (acl2::x d) (acl2::y (/ d)) (acl2::z n))
                          (:instance acl2::inverse-of-* (acl2::x d)))
                   :in-theory (disable acl2::associativity-of-*
                                       acl2::inverse-of-*)
                   :nonlinearp t))))

(local
 (defthm assembly-fraction-value
   (implies (rationalp x)
            (equal (* (denominator x) x) (numerator x)))
   :hints (("Goal" :use ((:instance acl2::rational-implies1 (acl2::x x))
                        (:instance acl2::rational-implies2 (acl2::x x))
                        (:instance assembly-multiply-equality
                                   (d (denominator x)) (y x)
                                   (z (* (/ (denominator x)) (numerator x))))
                        (:instance assembly-cancel-division
                                   (d (denominator x)) (n (numerator x))))
                   :in-theory (disable acl2::rational-implies2 assembly-cancel-division)))
   :rule-classes nil))

(local
 (defthm assembly-floor-of-rational
   (implies (rationalp x)
            (and (<= (floor x 1) x)
                 (< x (+ 1 (floor x 1)))))
   :hints (("Goal"
            :use ((:instance assembly-quotient-bounds
                             (n (numerator x)) (d (denominator x)))
                  (:instance assembly-quotient-bounds
                             (n (- (numerator x))) (d (denominator x)))
                  assembly-fraction-value)
            :in-theory (enable floor)
            :nonlinearp t))
   :rule-classes nil))

(defthm assembly-scale-order
  (implies (and (rationalp a) (rationalp b) (rationalp d) (< 0 d))
           (equal (< (* d a) (* d b)) (< a b)))
  :hints (("Goal"
           :cases ((< a b) (equal a b))
           :use ((:instance acl2::distributivity
                            (acl2::x d) (acl2::y b) (acl2::z (- a)))
                 (:instance acl2::distributivity
                            (acl2::x d) (acl2::y a) (acl2::z (- b))))
           :in-theory (disable acl2::distributivity)
           :nonlinearp t))
  :rule-classes nil)

(local
 (defthm assembly-floor-via-ratio
   (equal (floor x d) (floor (* (/ d) x) 1))
   :hints (("Goal" :in-theory (enable floor)))
   :rule-classes nil))

(defthm assembly-floor-bounds
  (implies (and (rationalp x) (rationalp d) (< 0 d))
           (and (<= (* d (floor x d)) x)
                (< x (* d (+ 1 (floor x d))))))
  :hints (("Goal" :use ((:instance assembly-floor-of-rational (x (* (/ d) x)))
                        (:instance assembly-cancel-division (n x))
                        assembly-floor-via-ratio
                        (:instance assembly-scale-order
                                   (a (* (/ d) x)) (b (floor x d)))
                        (:instance assembly-scale-order
                                   (a (* (/ d) x)) (b (+ 1 (floor x d)))))
                  :in-theory (disable assembly-cancel-division)
                  :nonlinearp t))
  :rule-classes nil)

(defthm assembly-floor-unique
  (implies (and (rationalp x) (rationalp d) (< 0 d) (integerp q)
                (<= (* d q) x) (< x (* d (+ 1 q))))
           (equal (floor x d) q))
  :hints (("Goal" :use assembly-floor-bounds :nonlinearp t))
  :rule-classes nil)

(defthm assembly-product-of-negative
  (implies (and (rationalp a) (rationalp b))
           (equal (* a (- b)) (- (* a b))))
  :hints (("Goal" :use ((:instance acl2::distributivity
                                   (acl2::x a) (acl2::y b) (acl2::z (- b))))
                  :in-theory (disable acl2::distributivity))))

(defthm assembly-multiply-by-negative-one
  (implies (rationalp x)
           (equal (* -1 x) (- x)))
  :hints (("Goal" :use ((:instance assembly-product-of-negative (a x) (b 1)))
                  :in-theory (disable assembly-product-of-negative))))

(defun assembly-power-of-two (width)
  (expt 2 (nfix width)))

(defthm assembly-power-of-two-is-positive
  (posp (assembly-power-of-two width))
  :hints (("Goal" :induct (expt 2 width)
                  :in-theory (enable expt)))
  :rule-classes (:type-prescription :rewrite))

(defthm assembly-power-of-two-step
  (implies (posp width)
           (equal (assembly-power-of-two width)
                  (* 2 (assembly-power-of-two (1- width)))))
  :hints (("Goal" :expand ((expt 2 width))))
  :rule-classes nil)

(local
 (defthm assembly-reciprocal-unique
   (implies (and (rationalp x) (not (equal x 0))
                 (equal (* x y) 1))
            (equal (/ x) y))
   :hints (("Goal"
            :use ((:instance acl2::associativity-of-*
                             (acl2::x (/ x)) (acl2::y x) (acl2::z y))
                  (:instance acl2::inverse-of-* (acl2::x x)))
            :in-theory (disable acl2::associativity-of-* acl2::inverse-of-*)
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm assembly-swap-factors
   (equal (* a (* b c)) (* b (* a c)))
   :hints (("Goal" :use ((:instance acl2::associativity-of-*
                                    (acl2::x a) (acl2::y b) (acl2::z c))
                          (:instance acl2::associativity-of-*
                                    (acl2::x b) (acl2::y a) (acl2::z c)))
                   :in-theory (disable acl2::associativity-of-*)))))

(local
 (defthm assembly-product-of-opposite-powers
   (implies (natp width)
            (equal (* (assembly-power-of-two width) (expt 2 (- width))) 1))
   :hints (("Goal" :induct (expt 2 width) :in-theory (enable expt)))
   :rule-classes nil))

(local
 (defthm assembly-power-of-two-negative
   (implies (natp width)
            (equal (expt 2 (- width)) (/ (assembly-power-of-two width))))
   :hints (("Goal" :use (assembly-product-of-opposite-powers
                         (:instance assembly-reciprocal-unique
                                    (x (assembly-power-of-two width))
                                    (y (expt 2 (- width)))))))))

(defthm assembly-power-of-two-of-sum
  (implies (and (natp a) (natp b))
           (equal (assembly-power-of-two (+ a b))
                  (* (assembly-power-of-two a) (assembly-power-of-two b))))
  :hints (("Goal" :induct (expt 2 a)
                  :in-theory (enable expt))))

(defun assembly-high (width value)
  (floor (ifix value) (assembly-power-of-two width)))

(defun assembly-low (width value)
  (mod (ifix value) (assembly-power-of-two width)))

(defun assembly-cat (width low high)
  (+ (ifix low) (* (assembly-power-of-two width) (ifix high))))

(local (in-theory (disable assembly-power-of-two)))

(defthm assembly-ash-right
  (implies (and (integerp value) (natp width))
           (equal (ash value (- width)) (assembly-high width value)))
  :hints (("Goal" :in-theory (enable ash floor))))

(local
 (defthm assembly-power-of-two-expt-type
   (implies (natp width)
            (posp (expt 2 width)))
   :hints (("Goal" :use assembly-power-of-two-is-positive
                   :in-theory (enable assembly-power-of-two)))))

(defthm assembly-ash-left
  (implies (and (integerp value) (natp width))
           (equal (ash value width) (* (assembly-power-of-two width) value)))
  :hints (("Goal"
           :use (assembly-power-of-two-expt-type
                 (:instance assembly-floor-unique
                            (x (* (expt 2 width) value))
                            (q (* (expt 2 width) value)) (d 1)))
           :in-theory (e/d (ash assembly-power-of-two)
                           (assembly-power-of-two-expt-type)))))

(local
 (defthm assembly-negate-twice
   (implies (rationalp x)
            (equal (- (- x)) x))
   :hints (("Goal" :cases ((< (- (- x)) x) (< x (- (- x))))))))

(defthm assembly-ash-right-constant
  (implies (and (syntaxp (quotep amount)) (integerp amount)
                (<= amount 0) (integerp value))
           (equal (ash value amount) (assembly-high (- amount) value)))
  :hints (("Goal" :use ((:instance assembly-ash-right (width (- amount))))
                  :in-theory (disable assembly-ash-right))))

(defthm assembly-low-bits-is-low
  (implies (and (integerp x) (natp width))
           (equal (boymoo-compiler::low-bits x width) (assembly-low width x)))
  :hints (("Goal" :in-theory (enable mod assembly-low assembly-high))))

(defthm assembly-low-bounds
  (and (<= 0 (assembly-low width value))
       (< (assembly-low width value) (assembly-power-of-two width)))
  :hints (("Goal" :use ((:instance assembly-floor-bounds
                                   (x (ifix value))
                                   (d (assembly-power-of-two width))))
                  :in-theory (enable mod)))
  :rule-classes :linear)

(defthm assembly-low-is-natural
  (natp (assembly-low width value))
  :hints (("Goal" :use assembly-low-bounds :in-theory (enable mod)))
  :rule-classes :type-prescription)

(defthm assembly-high-of-cat
  (implies (and (natp low) (< low (assembly-power-of-two width)))
           (equal (assembly-high width (assembly-cat width low high)) (ifix high)))
  :hints (("Goal" :use ((:instance assembly-floor-unique
                                   (x (assembly-cat width low high))
                                   (d (assembly-power-of-two width))
                                   (q (ifix high))))
                  :nonlinearp t)))

(defthm assembly-low-of-cat
  (implies (and (natp low) (< low (assembly-power-of-two width)))
           (equal (assembly-low width (assembly-cat width low high)) low))
  :hints (("Goal" :use assembly-high-of-cat
                  :in-theory (e/d (mod) (assembly-high-of-cat)))))

(defthm assembly-cat-of-low-and-high
  (equal (assembly-cat width (assembly-low width x) (assembly-high width x))
         (ifix x))
  :hints (("Goal" :in-theory (enable mod))))

(local
 (defthm assembly-two-power-zero
   (implies (zp width) (equal (assembly-power-of-two width) 1))
   :hints (("Goal" :in-theory (enable assembly-power-of-two)))))

(defthm assembly-unsigned-width
  (equal (unsigned-byte-p width value)
         (and (natp width) (natp value) (< value (assembly-power-of-two width))))
  :hints (("Goal" :in-theory (enable assembly-power-of-two))))

(defthm assembly-high-of-fitting-value
  (implies (and (natp value) (< value (assembly-power-of-two width)))
           (equal (assembly-high width value) 0))
  :hints (("Goal" :use ((:instance assembly-floor-unique
                                   (x value) (d (assembly-power-of-two width)) (q 0))))))

(defthm assembly-low-of-fitting-value
  (implies (and (natp value) (< value (assembly-power-of-two width)))
           (equal (assembly-low width value) value))
  :hints (("Goal" :use ((:instance assembly-high-of-fitting-value))
                  :in-theory (e/d (mod) (assembly-high-of-fitting-value)))))

(defthm assembly-cat-bounds
  (implies (and (natp n) (natp m)
                (natp low) (< low (assembly-power-of-two n))
                (natp high) (< high (assembly-power-of-two m)))
           (and (<= 0 (assembly-cat n low high))
                (< (assembly-cat n low high) (assembly-power-of-two (+ n m)))))
  :hints (("Goal" :nonlinearp t))
  :rule-classes (:linear :rewrite))

(defthm assembly-cat-associate
  (implies (and (natp n) (natp m))
           (equal (assembly-cat n a (assembly-cat m b c))
                  (assembly-cat (+ n m) (assembly-cat n a b) c)))
  :hints (("Goal" :in-theory (enable acl2::distributivity) :nonlinearp t))
  :rule-classes nil)

(defthm assembly-cat-equals-value
  (implies (and (syntaxp (quotep value))
                (integerp value) (integerp high)
                (natp low) (< low (assembly-power-of-two width)))
           (equal (equal (assembly-cat width low high) value)
                  (and (equal low (assembly-low width value))
                       (equal high (assembly-high width value)))))
  :hints (("Goal"
           :use ((:instance assembly-cat-of-low-and-high (x value))
                 assembly-low-of-cat assembly-high-of-cat)
           :in-theory (disable assembly-cat assembly-low assembly-high
                               assembly-cat-of-low-and-high
                               assembly-low-of-cat assembly-high-of-cat))))

(local (in-theory (disable assembly-cat assembly-low assembly-high)))

(defthm assembly-low-one-is-a-bit
  (or (equal (assembly-low 1 x) 0)
      (equal (assembly-low 1 x) 1))
  :hints (("Goal" :use ((:instance assembly-low-bounds (width 1) (value x)))))
  :rule-classes nil)

(defthm assembly-evenp-from-low-bit
  (implies (integerp x)
           (equal (evenp x) (equal (assembly-low 1 x) 0)))
  :hints (("Goal" :use ((:instance assembly-cat-of-low-and-high (width 1))
                        assembly-low-one-is-a-bit)
                  :in-theory (e/d (evenp assembly-cat)
                                  (assembly-cat-of-low-and-high)))))

