(in-package "BOYMOO-PROOFS")

(include-book "bits")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt evenp
                           acl2::binary-logand acl2::binary-logior lognot
                           assembly-cat assembly-low assembly-high assembly-power-of-two)))

(defthm assembly-logand-endpoints
  (implies (integerp x)
           (and (equal (logand 0 x) 0)
                (equal (logand x 0) 0)
                (equal (logand -1 x) x)
                (equal (logand x -1) x)))
  :hints (("Goal" :expand ((logand 0 x) (logand x 0)
                           (logand -1 x) (logand x -1))
                  :in-theory (enable zip))))

(defthm assembly-logand-by-bits
   (implies (and (integerp x) (integerp y))
            (equal (logand x y)
                   (assembly-cat 1
                                 (if (or (equal (assembly-low 1 x) 0)
                                         (equal (assembly-low 1 y) 0))
                                     0 1)
                                 (logand (assembly-high 1 x) (assembly-high 1 y)))))
   :hints (("Goal" :use ((:instance assembly-low-one-is-a-bit)
                         (:instance assembly-low-one-is-a-bit (x y))
                         (:instance assembly-cat-of-low-and-high (width 1))
                         (:instance assembly-cat-of-low-and-high (width 1) (x y)))
                   :expand ((logand x y))
                   :in-theory (e/d (assembly-cat assembly-high assembly-low)
                                   (assembly-cat-of-low-and-high))))
   :rule-classes nil)

(defthm assembly-high-of-zero-width
  (equal (assembly-high 0 value) (ifix value))
  :hints (("Goal" :use ((:instance assembly-floor-unique (x (ifix value)) (d 1) (q (ifix value))))
                  :in-theory (enable assembly-high))))

(defthm assembly-low-of-zero-width
  (equal (assembly-low 0 value) 0)
  :hints (("Goal" :use ((:instance assembly-low-bounds (width 0)))
                  :in-theory (enable assembly-power-of-two))))

(defthm assembly-cat-of-zero-width
  (equal (assembly-cat 0 low high) (+ (ifix low) (ifix high)))
  :hints (("Goal" :in-theory (enable assembly-cat assembly-power-of-two))))

(defthm assembly-cat-of-zero-high
  (equal (assembly-cat width low 0) (ifix low))
  :hints (("Goal" :in-theory (enable assembly-cat))))

(local
 (defthm assembly-cat-split-high
   (implies (and (natp n) (natp m) (integerp high))
            (equal (assembly-cat n low high)
                   (assembly-cat (+ n m)
                                 (assembly-cat n low (assembly-low m high))
                                 (assembly-high m high))))
   :hints (("Goal" :use ((:instance assembly-cat-associate
                                    (a low) (b (assembly-low m high))
                                    (c (assembly-high m high))))
                   :in-theory (disable assembly-cat-of-zero-high)))
   :rule-classes nil))

(local
 (defthm assembly-cat-split-low
   (implies (and (natp n) (natp m) (integerp low))
            (equal (assembly-cat (+ n m) low high)
                   (assembly-cat n (assembly-low n low)
                                 (assembly-cat m (assembly-high n low) high))))
   :hints (("Goal" :use ((:instance assembly-cat-associate
                                    (a (assembly-low n low)) (b (assembly-high n low))
                                    (c high)))
                   :in-theory (disable assembly-cat-of-zero-high)))
   :rule-classes nil))

(local
 (defthm assembly-cat-natural
   (implies (and (natp low) (natp high))
            (natp (assembly-cat n low high)))
   :hints (("Goal" :in-theory (enable assembly-cat)))
   :rule-classes :type-prescription))

(defthm assembly-add-cancel
  (implies (and (rationalp a) (rationalp b))
           (equal (+ a (- a) b) b))
  :hints (("Goal" :cases ((< (+ a (- a) b) b)
                           (< b (+ a (- a) b))))))

(defthm assembly-split-above-cat
  (implies (and (natp n) (natp width) (< n width)
                (natp low) (< low (assembly-power-of-two n))
                (integerp high))
           (and (equal (assembly-high width (assembly-cat n low high))
                       (assembly-high (- width n) high))
                (equal (assembly-low width (assembly-cat n low high))
                       (assembly-cat n low (assembly-low (- width n) high)))))
  :hints (("Goal"
           :use ((:instance assembly-cat-split-high (m (- width n)))
                 (:instance assembly-cat-bounds (m (- width n)) (high (assembly-low (- width n) high)))
                 (:instance assembly-high-of-cat
                            (low (assembly-cat n low (assembly-low (- width n) high)))
                            (high (assembly-high (- width n) high)))
                 (:instance assembly-low-of-cat
                            (low (assembly-cat n low (assembly-low (- width n) high)))
                            (high (assembly-high (- width n) high))))
           :in-theory (disable assembly-cat-bounds
                               assembly-high-of-cat assembly-low-of-cat))))

(defthm assembly-split-below-cat
  (implies (and (natp n) (natp width) (< width n)
                (integerp low) (integerp high))
           (and (equal (assembly-high width (assembly-cat n low high))
                       (assembly-cat (- n width) (assembly-high width low) high))
                (equal (assembly-low width (assembly-cat n low high))
                       (assembly-low width low))))
  :hints (("Goal"
           :use ((:instance assembly-cat-split-low (n width) (m (- n width)))
                 (:instance assembly-high-of-cat
                            (low (assembly-low width low))
                            (high (assembly-cat (- n width) (assembly-high width low) high)))
                 (:instance assembly-low-of-cat
                            (low (assembly-low width low))
                            (high (assembly-cat (- n width) (assembly-high width low) high))))
           :in-theory (disable assembly-high-of-cat assembly-low-of-cat))))

(local
 (defthm assembly-split-one-bit
   (implies (and (posp width) (integerp x))
            (and (equal (assembly-high width x)
                        (assembly-high (1- width) (assembly-high 1 x)))
                 (equal (assembly-low width x)
                        (assembly-cat 1 (assembly-low 1 x)
                                      (assembly-low (1- width) (assembly-high 1 x))))))
   :hints (("Goal"
            :use ((:instance assembly-split-above-cat (n 1)
                             (low (assembly-low 1 x)) (high (assembly-high 1 x))))
            :cases ((equal width 1))
            :in-theory (disable assembly-split-above-cat)))
   :rule-classes nil))

(local
 (defthm assembly-high-one-of-logand
   (implies (and (integerp x) (integerp y))
            (equal (assembly-high 1 (logand x y))
                   (logand (assembly-high 1 x) (assembly-high 1 y))))
   :hints (("Goal" :use assembly-logand-by-bits))))

(local
 (defthm assembly-low-one-of-logand
   (implies (and (integerp x) (integerp y))
            (equal (assembly-low 1 (logand x y))
                   (if (or (equal (assembly-low 1 x) 0)
                           (equal (assembly-low 1 y) 0))
                       0
                     1)))
   :hints (("Goal" :use assembly-logand-by-bits))))

(local
 (defthm assembly-logand-of-one-bit-cats
   (implies (and (natp a) (< a 2) (natp b) (< b 2)
                 (integerp x) (integerp y))
            (equal (logand (assembly-cat 1 a x) (assembly-cat 1 b y))
                   (assembly-cat 1 (if (or (equal a 0) (equal b 0)) 0 1)
                                 (logand x y))))
   :hints (("Goal"
            :use ((:instance assembly-logand-by-bits
                             (x (assembly-cat 1 a x)) (y (assembly-cat 1 b y))))))))

(local
 (defun assembly-bitwise-induction (width x y)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       (cons x y)
     (assembly-bitwise-induction (1- width) (assembly-high 1 x) (assembly-high 1 y)))))

(defthm assembly-high-of-logand
  (implies (and (natp width) (integerp x) (integerp y))
           (equal (assembly-high width (logand x y))
                  (logand (assembly-high width x) (assembly-high width y))))
  :hints (("Goal" :induct (assembly-bitwise-induction width x y))
          ("Subgoal *1/2"
           :use ((:instance assembly-split-one-bit (x (logand x y)))
                 (:instance assembly-split-one-bit)
                 (:instance assembly-split-one-bit (x y))))))

(defthm assembly-low-of-logand
  (implies (and (natp width) (integerp x) (integerp y))
           (equal (assembly-low width (logand x y))
                  (logand (assembly-low width x) (assembly-low width y))))
  :hints (("Goal" :induct (assembly-bitwise-induction width x y))
          ("Subgoal *1/2"
           :use ((:instance assembly-split-one-bit (x (logand x y)))
                 (:instance assembly-split-one-bit)
                 (:instance assembly-split-one-bit (x y))))))

(defthm assembly-logand-of-cat
  (implies (and (natp width) (natp low) (< low (assembly-power-of-two width))
                (integerp high) (integerp mask))
           (equal (logand (assembly-cat width low high) mask)
                  (assembly-cat width
                                (logand low (assembly-low width mask))
                                (logand high (assembly-high width mask)))))
  :hints (("Goal"
           :use ((:instance assembly-cat-of-low-and-high
                            (x (logand (assembly-cat width low high) mask))))
           :in-theory (disable assembly-cat-of-low-and-high))))

(defthm assembly-logand-bounded
  (implies (and (natp width) (natp x) (< x (assembly-power-of-two width))
                (integerp y))
           (and (<= 0 (logand x y))
                (< (logand x y) (assembly-power-of-two width))))
  :hints (("Goal" :use ((:instance assembly-cat-of-low-and-high (x (logand x y))))
                  :in-theory (disable assembly-cat-of-low-and-high assembly-low-of-logand)))
  :rule-classes (:linear :rewrite))

(defthm assembly-low-of-negative-one
  (equal (assembly-low width -1) (1- (assembly-power-of-two width)))
  :hints (("Goal"
           :use ((:instance assembly-floor-unique
                            (x -1) (d (assembly-power-of-two width)) (q -1)))
           :in-theory (enable assembly-low mod))))

(defthm assembly-logand-low-mask
  (implies (and (natp width) (integerp x))
           (equal (logand x (1- (assembly-power-of-two width)))
                  (assembly-low width x)))
  :hints (("Goal"
           :use ((:instance assembly-low-of-logand (y -1))
                 (:instance assembly-logand-of-cat
                            (low (assembly-low width x)) (high (assembly-high width x))
                            (mask (1- (assembly-power-of-two width)))))
           :in-theory (disable assembly-low-of-logand assembly-logand-of-cat))))

(defthm assembly-a64-unsigned-is-low
  (implies (natp width)
           (equal (boymoo-model::a64-unsigned width x) (assembly-low width x)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-ones assembly-low)
                  :use ((:instance assembly-logand-low-mask (x (ifix x)))))))

(defthm assembly-a64-field-is-low-of-high
  (implies (natp width)
           (equal (boymoo-model::a64-field word start width)
                  (assembly-low width (assembly-high (nfix start) word))))
  :hints (("Goal" :in-theory (enable assembly-high))))

(defthm assembly-logbitp-is-low-of-high
  (implies (integerp x)
           (equal (logbitp index x)
                  (not (equal (assembly-low 1 (assembly-high (nfix index) x)) 0))))
  :hints (("Goal" :in-theory (enable logbitp assembly-high assembly-power-of-two))))

(defthm assembly-logand-constant-low-mask
  (implies (and (syntaxp (quotep mask))
                (natp mask) (integerp x)
                (equal mask (1- (assembly-power-of-two (integer-length mask)))))
           (equal (logand x mask) (assembly-low (integer-length mask) x)))
  :hints (("Goal"
           :use ((:instance assembly-logand-low-mask (width (integer-length mask))))
           :in-theory (disable assembly-logand-low-mask))))

(defthm assembly-high-one-bound-for-naturals
  (implies (natp x)
           (and (<= 0 (assembly-high 1 x))
                (implies (< 0 x) (< (assembly-high 1 x) x))))
  :hints (("Goal" :use ((:instance assembly-floor-bounds (d 2)))
                  :in-theory (enable assembly-high)))
  :rule-classes :linear)

(local
 (defun assembly-nonnegative-logand-induction (x y)
   (declare (xargs :measure (nfix x)))
   (if (zp x)
       y
     (assembly-nonnegative-logand-induction (assembly-high 1 x) (assembly-high 1 y)))))

(defthm assembly-logand-at-most-first
  (implies (and (natp x) (integerp y))
           (and (<= 0 (logand x y))
                (<= (logand x y) x)))
  :hints (("Goal" :induct (assembly-nonnegative-logand-induction x y))
          ("Subgoal *1/2"
           :use (assembly-logand-by-bits
                 assembly-low-one-is-a-bit
                 (:instance assembly-cat-of-low-and-high (width 1)))
           :in-theory (e/d (assembly-cat) (assembly-cat-of-low-and-high))))
  :rule-classes :linear)
