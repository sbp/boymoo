(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm data-cancel-reciprocal
   (implies (and (acl2-numberp n) (acl2-numberp d) (not (equal d 0)))
            (equal (* d (* (/ d) n)) n))
   :hints (("Goal" :use ((:instance associativity-of-* (acl2::x d) (acl2::y (/ d)) (acl2::z n)))
                   :in-theory (disable associativity-of-* commutativity-of-*)))))

(local
 (defthm data-multiply-quotient
   (implies (and (acl2-numberp n) (acl2-numberp d) (not (equal d 0))
                 (equal q (* (/ d) n)))
            (equal (* d q) n))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable commutativity-of-* associativity-of-*)))))

(local
 (defthm data-numerator-product
   (implies (rationalp x)
            (equal (* (denominator x) x) (numerator x)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance acl2::rational-implies1 (acl2::x x))
                        (:instance acl2::rational-implies2 (acl2::x x))
                        (:instance data-multiply-quotient (n (numerator x))
                                   (q x) (d (denominator x))))
                   :in-theory (disable acl2::rational-implies2)))))

(local
 (defthm data-natural-quotient-bounds
   (implies (and (natp n) (posp d))
            (and (<= (* d (nonnegative-integer-quotient n d)) n)
                 (< n (+ d (* d (nonnegative-integer-quotient n d))))))
   :rule-classes nil
   :hints (("Goal" :induct (nonnegative-integer-quotient n d)))))

(local
 (defthm data-numerator-not-a-multiple
   (implies (and (rationalp x) (integerp q) (< 1 (denominator x)))
            (not (equal (* (denominator x) q) (numerator x))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance acl2::lowest-terms (acl2::x x)
                                   (acl2::n (denominator x)) (acl2::r q) (acl2::q 1))
                        (:instance acl2::rational-implies1 (acl2::x x)))))))

(defthmd data-floor-one-bounds
  (implies (rationalp x)
           (and (<= (floor x 1) x) (< x (+ 1 (floor x 1)))))
  :hints (("Goal" :use ((:instance acl2::rational-implies1 (acl2::x x))
                       data-numerator-product
                       (:instance data-natural-quotient-bounds (n (numerator x))
                                  (d (denominator x)))
                       (:instance data-natural-quotient-bounds (n (- (numerator x)))
                                  (d (denominator x)))
                       (:instance data-numerator-not-a-multiple
                                  (q (- (nonnegative-integer-quotient
                                         (- (numerator x)) (denominator x))))))
                  :nonlinearp t)))

(defthm data-floor-one-of-integer
  (implies (integerp x) (equal (floor x 1) x))
  :hints (("Goal" :use data-floor-one-bounds :in-theory (disable floor))))

(defthmd data-floor-one-unique
  (implies (and (rationalp x) (integerp q) (<= q x) (< x (+ 1 q)))
           (equal (floor x 1) q))
  :hints (("Goal" :use data-floor-one-bounds :in-theory (disable floor))))

(local
 (defthm floor-through-reciprocal
   (equal (floor x d) (floor (* (/ d) x) 1))
   :rule-classes nil))

(defthm data-product-one-right
  (equal (* x 1) (fix x)))

(defthm data-product-of-minus
  (equal (* a (- b)) (- (* a b)))
  :hints (("Goal" :use ((:instance distributivity (acl2::x a) (acl2::y b) (acl2::z (- b))))
                  :in-theory (disable distributivity))))

(defthm data-swap-front-factors
  (equal (* a (* b c)) (* b (* a c)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance associativity-of-* (acl2::x a) (acl2::y b) (acl2::z c))
                       (:instance associativity-of-* (acl2::x b) (acl2::y a) (acl2::z c))
                       (:instance commutativity-of-* (acl2::x a) (acl2::y b)))
                  :in-theory (disable associativity-of-* commutativity-of-*))))

(local
 (defthm data-product-of-positives
   (implies (and (rationalp a) (rationalp b) (< 0 a) (< 0 b))
            (< 0 (* a b)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t))))

(defthmd data-positive-scaling-preserves-order
  (implies (and (rationalp a) (rationalp b) (rationalp d) (< 0 d))
           (equal (< (* d a) (* d b)) (< a b)))
  :hints (("Goal" :cases ((< a b) (< b a))
                  :use ((:instance data-product-of-positives (a d) (b (- b a)))
                        (:instance data-product-of-positives (a d) (b (- a b)))))))

(defthmd data-floor-bounds
  (implies (and (rationalp x) (rationalp d) (< 0 d))
           (and (<= (* d (floor x d)) x) (< x (+ d (* d (floor x d))))))
  :hints (("Goal" :use (floor-through-reciprocal
                       (:instance data-floor-one-bounds (x (* (/ d) x)))
                       (:instance data-positive-scaling-preserves-order
                                  (a (* (/ d) x)) (b (floor x d)))
                       (:instance data-positive-scaling-preserves-order
                                  (a (* (/ d) x)) (b (+ 1 (floor x d)))))
                  :in-theory (disable floor commutativity-of-* associativity-of-*))))

(defthmd data-floor-unique
  (implies (and (rationalp x) (rationalp d) (< 0 d) (integerp q)
                (<= (* d q) x) (< x (+ d (* d q))))
           (equal (floor x d) q))
  :hints (("Goal" :use data-floor-bounds
                  :cases ((< q (floor x d)) (< (floor x d) q))
                  :nonlinearp t
                  :in-theory (disable floor))))

(defthmd data-floor-in-two-stages
  (implies (and (rationalp x) (posp d) (posp e))
           (equal (floor (floor x d) e) (floor x (* d e))))
  :hints (("Goal" :use ((:instance data-floor-bounds)
                       (:instance data-floor-bounds (x (floor x d)) (d e))
                       (:instance data-floor-unique (d (* d e)) (q (floor (floor x d) e))))
                  :nonlinearp t
                  :in-theory (disable floor))))

(local
 (defthm data-aligned-size-eight-form
   (implies (integerp size)
            (equal (boymoo-compiler::aligned-size size 3)
                   (* 8 (floor (* 1/8 (+ size 7)) 1))))
   :hints (("Goal" :in-theory (disable floor)))))

(defthm data-aligned-size-eight-bounds
  (implies (integerp size)
           (and (integerp (boymoo-compiler::aligned-size size 3))
                (<= size (boymoo-compiler::aligned-size size 3))
                (< (boymoo-compiler::aligned-size size 3) (+ size 8))))
  :rule-classes (:rewrite
                 (:linear :corollary (implies (integerp size)
                                             (<= size (boymoo-compiler::aligned-size size 3))))
                 (:linear :corollary (implies (integerp size)
                                             (< (boymoo-compiler::aligned-size size 3)
                                                (+ size 8)))))
  :hints (("Goal" :use ((:instance data-floor-one-bounds (x (* 1/8 (+ size 7)))))
                  :in-theory (disable floor boymoo-compiler::aligned-size))))
