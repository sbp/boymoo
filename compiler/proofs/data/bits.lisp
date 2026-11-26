(in-package "BOYMOO-PROOFS")

(include-book "arithmetic")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm expt-two-step
   (implies (posp width)
            (equal (expt 2 width) (* 2 (expt 2 (1- width)))))
   :rule-classes nil
   :hints (("Goal" :expand ((expt 2 width))))))

(local
 (defthm data-reciprocal-cancels-scaled-product
   (implies (and (rationalp x) (rationalp y) (not (equal x 0))
                 (equal (* x y) 1))
            (equal (/ x) y))
   :rule-classes nil
   :hints (("Goal" :use ((:instance inverse-of-* (acl2::x x))
                        (:instance associativity-of-* (acl2::x (/ x)) (acl2::y x) (acl2::z y))
                        (:instance commutativity-of-* (acl2::x (/ x)) (acl2::y x)))
                   :in-theory (disable inverse-of-* associativity-of-* commutativity-of-*)))))

(local
 (defthm twice-times-half-of-product
   (implies (and (rationalp a) (rationalp b))
            (equal (* (* 2 a) (* 1/2 b)) (* a b)))
   :hints (("Goal" :use ((:instance data-swap-front-factors (b 1/2) (c b))
                        (:instance associativity-of-* (acl2::x 2) (acl2::y a) (acl2::z (* 1/2 b)))
                        (:instance associativity-of-* (acl2::x 2) (acl2::y 1/2) (acl2::z (* a b))))
                   :in-theory (disable associativity-of-* commutativity-of-*)))))

(local
 (defthm data-reciprocal-of-double
   (implies (and (rationalp x) (not (equal x 0)))
            (equal (/ (* 2 x)) (* 1/2 (/ x))))
   :hints (("Goal" :use ((:instance data-reciprocal-cancels-scaled-product
                                    (x (* 2 x)) (y (* 1/2 (/ x)))))
                   :in-theory (disable associativity-of-*)))))

(defthm data-expt-two-positive-integer
  (implies (natp width) (posp (expt 2 width)))
  :rule-classes :type-prescription)

(local
 (defthm expt-two-negative
   (implies (natp width)
            (equal (expt 2 (- width)) (/ (expt 2 width))))
   :hints (("Goal" :induct (expt 2 width) :expand ((expt 2 (- width)))))))

(defthmd data-ash-left
  (implies (and (integerp word) (natp width))
           (equal (ash word width) (* word (expt 2 width))))
  :hints (("Goal" :in-theory (disable floor expt))))

(defthmd data-ash-right
  (implies (and (integerp word) (natp width))
           (equal (ash word (- width)) (floor word (expt 2 width))))
  :hints (("Goal" :in-theory (disable expt))))

(defthmd data-low-bits-remainder
  (implies (and (integerp word) (natp width))
           (equal (boymoo-compiler::low-bits word width)
                  (- word (* (expt 2 width) (floor word (expt 2 width))))))
  :hints (("Goal" :in-theory (e/d (data-ash-left data-ash-right) (ash floor expt)))))

(defthm data-low-bits-in-range
  (implies (and (integerp word) (natp width))
           (and (natp (boymoo-compiler::low-bits word width))
                (< (boymoo-compiler::low-bits word width) (expt 2 width))))
  :hints (("Goal" :use ((:instance data-floor-bounds (x word) (d (expt 2 width))))
                  :in-theory (e/d (data-low-bits-remainder)
                                 (boymoo-compiler::low-bits floor expt)))))

(defthmd data-low-bits-unique
  (implies (and (integerp word) (natp width) (integerp q) (natp residue)
                (< residue (expt 2 width))
                (equal word (+ (* q (expt 2 width)) residue)))
           (equal (boymoo-compiler::low-bits word width) residue))
  :hints (("Goal" :use ((:instance data-floor-unique (x word) (d (expt 2 width))))
                  :in-theory (e/d (data-low-bits-remainder)
                                 (boymoo-compiler::low-bits floor expt)))))

(local
 (in-theory (disable boymoo-compiler::low-bits floor ash expt)))

(defthm data-low-bits-of-unsigned
  (implies (and (natp width) (natp word) (< word (expt 2 width)))
           (equal (boymoo-compiler::low-bits word width) word))
  :hints (("Goal" :use ((:instance data-low-bits-unique (q 0) (residue word))))))

(local
 (defthm data-low-bits-of-zero
   (implies (natp width) (equal (boymoo-compiler::low-bits 0 width) 0))))

(local
 (defthm data-low-bits-of-minus-one
   (implies (natp width)
            (equal (boymoo-compiler::low-bits -1 width) (1- (expt 2 width))))
   :hints (("Goal" :use ((:instance data-low-bits-unique
                                    (word -1) (q -1) (residue (1- (expt 2 width)))))))))

(local
 (defthm data-low-bits-at-width-zero
   (implies (integerp word) (equal (boymoo-compiler::low-bits word 0) 0))
   :hints (("Goal" :use ((:instance data-low-bits-unique (width 0) (q word) (residue 0)))))))

(defthm data-low-bit-parity
  (implies (integerp word)
           (equal (boymoo-compiler::low-bits word 1) (if (evenp word) 0 1)))
  :hints (("Goal" :use ((:instance data-low-bits-in-range (width 1))
                       (:instance data-floor-unique (x word) (d 2) (q (* 1/2 word))))
                  :in-theory (e/d (data-low-bits-remainder evenp) (data-low-bits-in-range)))))

(defthmd data-low-bits-split
  (implies (and (integerp word) (posp width))
           (equal (boymoo-compiler::low-bits word width)
                  (+ (boymoo-compiler::low-bits word 1)
                     (* 2 (boymoo-compiler::low-bits (floor word 2) (1- width))))))
  :hints (("Goal" :use ((:instance expt-two-step)
                       (:instance data-floor-in-two-stages
                                  (x word) (d 2) (e (expt 2 (1- width)))))
                  :in-theory (e/d (data-low-bits-remainder) (data-low-bit-parity)))))

(local
 (defthm floor-half-of-mask
   (implies (posp width)
            (equal (floor (1- (expt 2 width)) 2) (1- (expt 2 (1- width)))))
   :hints (("Goal" :use ((:instance expt-two-step)
                        (:instance data-floor-unique
                                   (x (1- (expt 2 width))) (d 2)
                                   (q (1- (expt 2 (1- width))))))))))

(local
 (defthm mask-at-positive-width-is-odd
   (implies (posp width) (not (evenp (1- (expt 2 width)))))
   :hints (("Goal" :use ((:instance expt-two-step)
                        (:instance data-low-bit-parity (word (1- (expt 2 width)))))
                   :in-theory (e/d (data-low-bits-remainder)
                                   (data-low-bit-parity evenp))))))

(local
 (defun data-mask-induction (word width)
   (declare (xargs :measure (nfix width)))
   (if (zp width) word (data-mask-induction (floor word 2) (1- width)))))

(defthmd data-logand-with-low-mask
  (implies (and (integerp word) (natp width))
           (equal (logand word (1- (expt 2 width))) (boymoo-compiler::low-bits word width)))
  :hints (("Goal" :induct (data-mask-induction word width)
                  :in-theory (disable evenp data-low-bit-parity))
          ("Subgoal *1/2" :use ((:instance data-low-bits-split) (:instance expt-two-step))
                          :in-theory (enable data-low-bit-parity)
                          :expand ((logand word (1- (expt 2 width)))))))

(defthmd data-machine-unsigned-is-low-bits
  (implies (and (integerp word) (natp width))
           (equal (boymoo-model::a64-unsigned width word)
                  (boymoo-compiler::low-bits word width)))
  :hints (("Goal" :in-theory (enable data-logand-with-low-mask data-ash-left))))

(defthmd data-two-power-of-sum
  (implies (and (natp lower) (natp upper))
           (equal (expt 2 (+ lower upper)) (* (expt 2 lower) (expt 2 upper))))
  :hints (("Goal" :induct (expt 2 lower) :in-theory (enable (:induction expt)))
          ("Subgoal *1/2" :use ((:instance expt-two-step (width lower))
                                (:instance expt-two-step (width (+ lower upper)))))
          ("Subgoal *1/3" :use ((:instance expt-two-step (width lower))
                                (:instance expt-two-step (width (+ lower upper)))))))

(defthmd data-low-bits-of-two-fields
  (implies (and (integerp word) (natp lower) (natp upper))
           (equal (boymoo-compiler::low-bits word (+ lower upper))
                  (+ (boymoo-compiler::low-bits word lower)
                     (* (expt 2 lower)
                        (boymoo-compiler::low-bits (ash word (- lower)) upper)))))
  :hints (("Goal" :use (data-two-power-of-sum
                       (:instance data-floor-in-two-stages
                                  (x word) (d (expt 2 lower)) (e (expt 2 upper))))
                  :in-theory (enable data-low-bits-remainder data-ash-right))))
