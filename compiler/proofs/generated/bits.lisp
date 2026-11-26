(in-package "BOYMOO-PROOFS")

(include-book "arithmetic")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable floor mod ash evenp oddp acl2::binary-logand acl2::binary-logior
                    acl2::binary-logxor acl2::binary-logeqv logorc1 lognot logbitp expt
                    boymoo-model::a64-unsigned boymoo-model::a64-ones))

(local
 (defthm generated-floor-of-even-or-odd
   (implies (and (integerp q) (natp bit) (< bit 2))
            (equal (floor (+ bit (* 2 q)) 2) q))
   :hints (("Goal" :use (:instance generated-floor-of-multiple-and-remainder
                                   (divisor 2) (r bit))))))

(local
 (defthm generated-floor-of-even
   (implies (integerp q)
            (equal (floor (* 2 q) 2) q))
   :hints (("Goal" :use (:instance generated-floor-of-even-or-odd (bit 0))))))

(defthm generated-logand-identities
  (implies (integerp x)
           (and (equal (logand 0 x) 0)
                (equal (logand x 0) 0)
                (equal (logand -1 x) x)
                (equal (logand x -1) x)))
  :hints (("Goal" :in-theory (enable acl2::binary-logand))))

(defthm generated-logior-with-zero
  (implies (integerp x)
           (and (equal (logior x 0) x) (equal (logior 0 x) x)))
  :hints (("Goal" :in-theory (enable acl2::binary-logior lognot))))

(local
 (defthm generated-lognot-of-lognot
   (implies (integerp x) (equal (lognot (lognot x)) x))
   :hints (("Goal" :in-theory (enable lognot)))))

(local
 (defthm generated-floor-lognot-by-two
   (implies (integerp x)
            (equal (floor (lognot x) 2) (lognot (floor x 2))))
   :hints (("Goal" :use (generated-floor-half-remainder
                         (:instance generated-floor-unique
                                    (x (lognot x)) (y 2) (q (lognot (floor x 2)))))
                   :in-theory (enable lognot)))))

(local
 (defthm generated-evenp-of-lognot
   (implies (integerp x)
            (equal (evenp (lognot x)) (not (evenp x))))
   :hints (("Goal" :use (generated-floor-half
                         (:instance generated-even-double (q (- (1+ (floor x 2)))))
                         (:instance generated-odd-double-plus-one
                                    (q (- (1+ (floor x 2))))))
                   :in-theory (e/d (lognot) (generated-even-double
                                            generated-odd-double-plus-one))))))

(local
 (defthm generated-lognot-of-even-or-odd
   (implies (integerp q)
            (and (equal (lognot (* 2 q)) (1+ (* 2 (lognot q))))
                 (equal (lognot (1+ (* 2 q))) (* 2 (lognot q)))))
   :hints (("Goal" :in-theory (enable lognot)))))

(defthm generated-logior-recurrence
  (implies (and (integerp x) (integerp y))
           (equal (logior x y)
                  (+ (* 2 (logior (floor x 2) (floor y 2)))
                     (if (and (evenp x) (evenp y)) 0 1))))
  :hints (("Goal" :use (:instance generated-logand-recurrence
                                  (x (lognot x)) (y (lognot y)))
                  :in-theory (enable acl2::binary-logior)))
  :rule-classes nil)

(local
 (defthm generated-floor-logior-by-two
   (implies (and (integerp x) (integerp y))
            (equal (floor (logior x y) 2) (logior (floor x 2) (floor y 2))))
   :hints (("Goal" :use generated-logior-recurrence))))

(local
 (defthm generated-evenp-of-logior
   (implies (and (integerp x) (integerp y))
            (equal (evenp (logior x y)) (and (evenp x) (evenp y))))
   :hints (("Goal" :use generated-logior-recurrence))))

(local
 (defthm generated-logxor-recurrence
   (implies (and (integerp x) (integerp y))
            (equal (logxor x y)
                   (+ (* 2 (logxor (floor x 2) (floor y 2)))
                      (if (equal (evenp x) (evenp y)) 0 1))))
   :hints (("Goal" :use (:instance generated-logand-recurrence
                                   (x (logorc1 x y)) (y (logorc1 y x)))
                   :in-theory (enable acl2::binary-logxor acl2::binary-logeqv logorc1)))
   :rule-classes nil))

(local
 (defthm generated-logxor-with-zero
   (implies (integerp x)
            (and (equal (logxor x 0) x) (equal (logxor 0 x) x)))
   :hints (("Goal" :in-theory (enable acl2::binary-logxor acl2::binary-logeqv
                                     logorc1 acl2::binary-logior lognot)))))

(local
 (defun generated-bit-induction (width x y)
   (declare (xargs :measure (nfix width)))
   (if (zp width)
       (cons x y)
     (generated-bit-induction (1- width) (floor x 2) (floor y 2)))))

(defthm generated-logxor-with-mask
  (implies (and (natp x) (< x (expt 2 (nfix width))))
           (equal (logxor x (boymoo-model::a64-ones width))
                  (- (boymoo-model::a64-ones width) x)))
  :hints (("Goal" :induct (generated-bit-induction width x unused))
          ("Subgoal *1/2"
           :use (generated-floor-half
                 (:instance generated-logxor-recurrence
                            (y (boymoo-model::a64-ones width)))
                 (:instance generated-floor-of-multiple-and-remainder
                            (divisor 2) (r 1) (q (boymoo-model::a64-ones (1- width))))
                 (:instance generated-odd-double-plus-one
                            (q (boymoo-model::a64-ones (1- width))))
                 (:instance generated-floor-bounds (y 2)))))
  :rule-classes nil)

(defthm generated-unsigned-with-low-bit
  (implies (integerp x)
           (equal (boymoo-model::a64-unsigned 1 x) (if (evenp x) 0 1)))
  :hints (("Goal" :use (generated-floor-half
                         (:instance generated-unsigned-as-mod (n 1)))
                  :in-theory (enable mod))))

(local
 (defun generated-logior-shift-induction (bits low high)
   (declare (xargs :measure (nfix bits)))
   (if (zp bits)
       (cons low high)
     (generated-logior-shift-induction (1- bits) (floor low 2) high))))

(local
 (defund generated-shifted-field (bits high)
   (* (expt 2 (nfix bits)) (ifix high))))

(local
 (defthm generated-shifted-field-step
   (implies (posp bits)
            (equal (generated-shifted-field bits high)
                   (* 2 (generated-shifted-field (1- bits) high))))
   :hints (("Goal" :in-theory (enable generated-shifted-field)))))

(local
 (defthm generated-shifted-field-integer
   (integerp (generated-shifted-field bits high))
   :hints (("Goal" :in-theory (enable generated-shifted-field)))
   :rule-classes :type-prescription))

(local
 (defthm generated-logior-of-shifted-field
   (implies (and (natp bits) (natp low) (< low (expt 2 bits)) (integerp high))
            (equal (logior low (generated-shifted-field bits high))
                   (+ low (generated-shifted-field bits high))))
   :hints (("Goal" :induct (generated-logior-shift-induction bits low high))
           ("Subgoal *1/2"
            :use ((:instance generated-logior-recurrence
                             (x low) (y (generated-shifted-field bits high)))
                  (:instance generated-floor-half (x low))
                  (:instance generated-floor-bounds (x low) (y 2))))
           ("Subgoal *1/1" :in-theory (enable generated-shifted-field)))
   :rule-classes nil))

(defthm generated-logior-of-disjoint-fields
  (implies (and (natp bits) (natp low) (< low (expt 2 bits)) (integerp high))
           (equal (logior low (* (expt 2 bits) high))
                  (+ low (* (expt 2 bits) high))))
  :hints (("Goal" :use generated-logior-of-shifted-field
                  :in-theory (enable generated-shifted-field)))
  :rule-classes nil)

(local
 (defthm generated-logand-symmetric
   (implies (and (integerp x) (integerp y))
            (equal (logand x y) (logand y x)))
   :hints (("Goal" :induct (acl2::binary-logand x y)
                   :in-theory (enable acl2::binary-logand)))
   :rule-classes nil))

(defthm generated-logior-symmetric
  (implies (and (integerp x) (integerp y))
           (equal (logior x y) (logior y x)))
  :hints (("Goal" :use (:instance generated-logand-symmetric (x (lognot x)) (y (lognot y)))
                  :in-theory (enable acl2::binary-logior)))
  :rule-classes nil)

(local
 (defthm generated-logand-with-complemented-shifted-field
   (implies (and (natp bits) (natp low) (< low (expt 2 bits)) (integerp high))
            (equal (logand (lognot (generated-shifted-field bits high)) low) low))
   :hints (("Goal" :induct (generated-logior-shift-induction bits low high))
           ("Subgoal *1/2"
            :use ((:instance generated-logand-recurrence
                             (x (lognot (generated-shifted-field bits high))) (y low))
                  (:instance generated-floor-half (x low))
                  (:instance generated-floor-bounds (x low) (y 2))))
           ("Subgoal *1/1" :in-theory (enable generated-shifted-field)))
   :rule-classes nil))

(defthm generated-logand-with-high-field-cleared
  (implies (and (natp bits) (natp low) (< low (expt 2 bits)) (integerp high))
           (equal (logand (lognot (* (expt 2 bits) high)) low) low))
  :hints (("Goal" :use generated-logand-with-complemented-shifted-field
                  :in-theory (enable generated-shifted-field)))
  :rule-classes nil)
