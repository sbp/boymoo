(in-package "BOYMOO-PROOFS")

; Facts about FLOOR, ASH and MOD on natural numbers, proved from the
; definitions in the ACL2 ground theory alone. The ELF book uses them to
; read back the little-endian fields that the executable writer encodes
; with ASH.

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm linux-quotient-bounds
   (implies (and (natp n) (posp d))
            (and (<= (* d (nonnegative-integer-quotient n d)) n)
                 (< n (* d (+ 1 (nonnegative-integer-quotient n d))))))
   :hints (("Goal" :induct (nonnegative-integer-quotient n d)))))
(local
 (defthm linux-monotone-le
  (implies (and (rationalp x) (rationalp q) (rationalp d) (< 0 d) (<= (* d q) (* d x)))
           (<= q x))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t))))
(local
 (defthm linux-monotone-lt
  (implies (and (rationalp x) (rationalp q) (rationalp d) (< 0 d) (< (* d x) (* d q)))
           (< x q))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t))))
(local
 (defthm linux-cancel-inverse
  (implies (and (rationalp d) (not (equal d 0)) (acl2-numberp n))
           (equal (* d (* (/ d) n)) n))
  :hints (("Goal" :use ((:instance associativity-of-* (acl2::x d) (acl2::y (/ d)) (acl2::z n)))
                  :in-theory (disable associativity-of-*)))))

(local
 (defthm linux-denominator-times
  (implies (rationalp x) (equal (* (denominator x) x) (numerator x)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance rational-implies2 (acl2::x x))
                        (:instance linux-cancel-inverse (d (denominator x)) (n (numerator x))))
           :in-theory (disable rational-implies2 linux-cancel-inverse)))))
(defthm linux-floor-bounds
  (implies (and (rationalp x) (<= 0 x))
           (and (integerp (floor x 1))
                (<= 0 (floor x 1))
                (<= (floor x 1) x)
                (< x (+ 1 (floor x 1)))))
  :rule-classes ((:linear :trigger-terms ((floor x 1))))
  :hints (("Goal"
           :use (linux-denominator-times
                 (:instance linux-quotient-bounds (n (numerator x)) (d (denominator x)))
                 (:instance linux-monotone-le (q (nonnegative-integer-quotient (numerator x) (denominator x)))
                            (d (denominator x)))
                 (:instance linux-monotone-lt (q (+ 1 (nonnegative-integer-quotient (numerator x) (denominator x))))
                            (d (denominator x))))
           :in-theory (disable linux-quotient-bounds nonnegative-integer-quotient))))
(defthm linux-floor-integerp
  (implies (and (rationalp x) (<= 0 x))
           (and (integerp (floor x 1)) (<= 0 (floor x 1))))
  :rule-classes ((:type-prescription :typed-term (floor x 1)))
  :hints (("Goal" :use linux-floor-bounds :in-theory (disable linux-floor-bounds floor))))

(defthm linux-floor-by-divisor
  (implies (and (rationalp x) (rationalp y) (not (equal y 0)))
           (equal (floor x y) (floor (* x (/ y)) 1)))
  :rule-classes nil)

(in-theory (disable floor))

(defthm linux-floor-unique
  (implies (and (rationalp x) (<= 0 x) (integerp q) (<= q x) (< x (+ 1 q)))
           (equal (floor x 1) q))
  :rule-classes nil
  :hints (("Goal" :use linux-floor-bounds
                  :in-theory (disable linux-floor-bounds))))

(defthm linux-floor-of-natural
  (implies (natp i) (equal (floor i 1) i))
  :hints (("Goal" :use ((:instance linux-floor-unique (x i) (q i))))))

(defthm linux-floor-4
  (implies (rationalp e) (equal (floor e 4) (floor (* 1/4 e) 1)))
  :hints (("Goal" :use ((:instance linux-floor-by-divisor (x e) (y 4))))))

(defthm linux-ash-right-8
  (implies (integerp w) (equal (ash w -8) (floor (* 1/256 w) 1)))
  :hints (("Goal" :in-theory (enable ash))))

(defthm linux-ash-right-2
  (implies (integerp w) (equal (ash w -2) (floor (* 1/4 w) 1)))
  :hints (("Goal" :in-theory (enable ash))))

(defthm linux-ash-left-8
  (implies (natp w) (equal (ash w 8) (* 256 w)))
  :hints (("Goal" :in-theory (enable ash))))

(defthm linux-ash-left-2
  (implies (natp w) (equal (ash w 2) (* 4 w)))
  :hints (("Goal" :in-theory (enable ash))))

(in-theory (disable mod ash linux-floor-bounds))
(defthm linux-mod-definition
  (equal (mod x y) (- x (* y (floor x y))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance (:definition mod) (acl2::x x) (acl2::y y))))))

(defthm linux-mod-4
  (implies (natp e)
           (equal (mod e 4) (- e (* 4 (floor (* 1/4 e) 1)))))
  :hints (("Goal" :use ((:instance linux-mod-definition (x e) (y 4))))))

(defthm linux-word-aligned-test
  (implies (and (natp e) (equal (mod e 4) 0))
           (equal (ash (ash e -2) 2) e)))

(defthm linux-mod-4-of-sum
  (implies (and (natp e) (equal (mod e 4) 0) (natp c) (equal (mod c 4) 0))
           (equal (mod (+ c e) 4) 0))
  :hints (("Goal" :use ((:instance linux-floor-unique
                                   (x (* 1/4 (+ c e)))
                                   (q (+ (floor (* 1/4 c) 1) (floor (* 1/4 e) 1))))))))

; LOGAND with a mask of N one bits leaves a natural number below 2^N unchanged.

(defthm linux-floor-2
  (implies (rationalp e) (equal (floor e 2) (floor (* 1/2 e) 1)))
  :hints (("Goal" :use ((:instance linux-floor-by-divisor (x e) (y 2))))))

(defthm linux-fold-half
  (equal (* 1/2 (* 2 x)) (fix x))
  :hints (("Goal" :use ((:instance associativity-of-* (acl2::x 1/2) (acl2::y 2) (acl2::z x)))
                  :in-theory (disable associativity-of-*))))

(defthm linux-expt-2-integerp
  (implies (natp k) (integerp (expt 2 k)))
  :rule-classes (:rewrite :type-prescription))

(defthm linux-expt-2-positive
  (implies (natp k) (<= 1 (expt 2 k)))
  :rule-classes :linear)

(defthm linux-expt-2-step
  (implies (posp n)
           (equal (expt 2 n) (* 2 (expt 2 (- n 1)))))
  :rule-classes nil)

(defthm linux-floor-minus-half
  (implies (posp m)
           (equal (floor (+ -1/2 m) 1) (+ -1 m)))
  :hints (("Goal" :use ((:instance linux-floor-unique (x (+ -1/2 m)) (q (+ -1 m)))))))

(defthm linux-minus-half-not-integer
  (implies (integerp m)
           (not (integerp (+ -1/2 m))))
  :hints (("Goal" :use ((:instance linux-floor-of-natural (i (+ -1/2 m)))
                        (:instance linux-floor-minus-half))
                  :cases ((posp m)))))

(defthm linux-parity
  (implies (natp x)
           (equal (+ (* 2 (floor (* 1/2 x) 1))
                     (if (integerp (* 1/2 x)) 0 1))
                  x))
  :rule-classes nil
  :hints (("Goal" :use ((:instance linux-floor-bounds (x (* 1/2 x)))
                        (:instance linux-floor-of-natural (i (* 1/2 x))))
                  :in-theory (disable linux-floor-of-natural))))

(defun linux-bits-induction (x n)
  (if (zp n) (list x n) (linux-bits-induction (floor (* 1/2 x) 1) (- n 1))))

(defthm linux-logand-mask
  (implies (and (natp n) (natp x) (< x (expt 2 n)))
           (equal (logand x (+ -1 (expt 2 n))) x))
  :hints (("Goal" :induct (linux-bits-induction x n))
          ("Subgoal *1/2" :use ((:instance linux-floor-bounds (x (* 1/2 x)))
                                (:instance linux-parity)
                                (:instance linux-expt-2-step))
                          :expand ((acl2::binary-logand x (+ -1 (* 2 (expt 2 (+ -1 n)))))))))

; CEILING bounds a nonnegative quotient from above, so that rounding an
; address up to a multiple of a page size never lowers it.

(local
 (defthm linux-monotone-times
   (implies (and (rationalp a) (rationalp b) (rationalp d) (< 0 d) (<= a b))
            (<= (* d a) (* d b)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(defthm linux-ceiling-bound
  (implies (and (rationalp x) (<= 0 x))
           (<= x (ceiling x 1)))
  :rule-classes nil
  :hints (("Goal"
           :use (linux-denominator-times
                 (:instance linux-quotient-bounds (n (numerator x)) (d (denominator x)))
                 (:instance linux-monotone-lt
                            (q (+ 1 (nonnegative-integer-quotient (numerator x) (denominator x))))
                            (d (denominator x))))
           :in-theory (disable linux-quotient-bounds nonnegative-integer-quotient))))

(defthm linux-ceiling-by-divisor
  (implies (and (rationalp x) (rationalp y) (not (equal y 0)))
           (equal (ceiling x y) (ceiling (* x (/ y)) 1)))
  :rule-classes nil)

(defthm linux-round-up-covers
  (implies (and (natp e) (posp c))
           (<= e (* c (ceiling e c))))
  :hints (("Goal" :use ((:instance linux-ceiling-by-divisor (x e) (y c))
                        (:instance linux-ceiling-bound (x (* e (/ c))))
                        (:instance linux-monotone-times
                                   (d c) (a (* e (/ c))) (b (ceiling (* e (/ c)) 1))))
                  :in-theory (disable ceiling))))
