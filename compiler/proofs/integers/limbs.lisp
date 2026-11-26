(in-package "BOYMOO-PROOFS")

(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt unsigned-byte-p)))

(defconst *integer-limb-base* #x100000000)

(defun integer-limb-p (digit)
  (and (natp digit) (< digit *integer-limb-base*)))

(defun integer-limbs-p (digits)
  (if (atom digits)
      (null digits)
    (and (integer-limb-p (car digits))
         (integer-limbs-p (cdr digits)))))

(defun integer-limb-value (digits)
  (if (atom digits)
      0
    (+ (ifix (car digits))
       (* *integer-limb-base* (integer-limb-value (cdr digits))))))

(defun integer-limb-capacity (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      1
    (* *integer-limb-base* (integer-limb-capacity (1- count)))))

(defthm integer-limb-capacity-positive
  (posp (integer-limb-capacity count))
  :rule-classes :type-prescription)

(defthm integer-limb-value-bounds
  (implies (integer-limbs-p digits)
           (and (<= 0 (integer-limb-value digits))
                (< (integer-limb-value digits)
                   (integer-limb-capacity (len digits)))))
  :rule-classes (:rewrite :linear))

(defun integer-limb-add (left right carry)
  (let ((sum (+ left right carry)))
    (mv (mod sum *integer-limb-base*) (floor sum *integer-limb-base*))))

(defun integer-limb-subtract (left right borrow)
  (let ((difference (- left (+ right borrow))))
    (mv (mod difference *integer-limb-base*) (if (< difference 0) 1 0))))

(defun integer-limb-multiply-accumulate (left right old carry)
  (let ((sum (+ (* left right) old carry)))
    (mv (mod sum *integer-limb-base*) (floor sum *integer-limb-base*))))

(defthm integer-limb-add-correct
  (implies (and (integer-limb-p left) (integer-limb-p right) (bitp carry))
           (mv-let (digit next) (integer-limb-add left right carry)
             (and (integer-limb-p digit)
                  (bitp next)
                  (equal (+ digit (* *integer-limb-base* next))
                         (+ left right carry)))))
  :hints (("Goal"
           :use ((:instance integer-floor-and-mod-decomposition
                            (x (+ left right carry)) (d *integer-limb-base*))
                 (:instance integer-floor-scaled-bounds
                            (x (+ left right carry)) (y *integer-limb-base*))))))

(defthm integer-limb-subtract-correct
  (implies (and (integer-limb-p left) (integer-limb-p right) (bitp borrow))
           (mv-let (digit next) (integer-limb-subtract left right borrow)
             (and (integer-limb-p digit)
                  (bitp next)
                  (equal (- digit (* *integer-limb-base* next))
                         (- left (+ right borrow))))))
  :hints (("Goal" :in-theory (enable bitp))))

(defthm integer-limb-multiply-accumulate-word-bound
  (implies (and (integer-limb-p left) (integer-limb-p right)
                (integer-limb-p old) (integer-limb-p carry))
           (and (natp (+ (* left right) old carry))
                (< (+ (* left right) old carry) (expt 2 64))))
  :rule-classes nil
  :hints (("Goal" :nonlinearp t)))

(defthm integer-limb-multiply-accumulate-correct
  (implies (and (integer-limb-p left) (integer-limb-p right)
                (integer-limb-p old) (integer-limb-p carry))
           (mv-let (digit next) (integer-limb-multiply-accumulate left right old carry)
             (and (integer-limb-p digit)
                  (integer-limb-p next)
                  (equal (+ digit (* *integer-limb-base* next))
                         (+ (* left right) old carry)))))
  :hints (("Goal"
           :use (integer-limb-multiply-accumulate-word-bound
                 (:instance integer-floor-and-mod-decomposition
                            (x (+ (* left right) old carry)) (d *integer-limb-base*))
                 (:instance integer-floor-scaled-bounds
                            (x (+ (* left right) old carry)) (y *integer-limb-base*))))))

(defun integer-add-limbs (left right carry)
  (if (atom left)
      (list carry)
    (mv-let (digit next) (integer-limb-add (car left) (ifix (car right)) carry)
      (cons digit (integer-add-limbs (cdr left) (cdr right) next)))))

(defun integer-subtract-limbs (left right borrow)
  (if (atom left)
      (mv nil borrow)
    (mv-let (digit next) (integer-limb-subtract (car left) (ifix (car right)) borrow)
      (mv-let (digits last) (integer-subtract-limbs (cdr left) (cdr right) next)
        (mv (cons digit digits) last)))))

(defun integer-multiply-row (factor right old carry)
  (if (atom right)
      (cons carry (cdr old))
    (mv-let (digit next)
      (integer-limb-multiply-accumulate factor (car right) (car old) carry)
      (cons digit (integer-multiply-row factor (cdr right) (cdr old) next)))))

(local
 (defthm integer-first-limb-or-zero
   (implies (integer-limbs-p digits)
            (integer-limb-p (ifix (car digits))))))

(local
 (defthm integer-bit-is-limb
   (implies (bitp bit) (integer-limb-p bit))))

(local
 (defthm integer-limb-value-split
   (implies (consp digits)
            (equal (integer-limb-value digits)
                   (+ (ifix (car digits))
                      (* *integer-limb-base* (integer-limb-value (cdr digits))))))))

(local
 (defthm integer-limb-value-when-atom
   (implies (atom digits)
            (equal (integer-limb-value digits) 0))))

(local (in-theory (disable integer-limb-add integer-limb-subtract
                           integer-limb-multiply-accumulate integer-limb-p
                           integer-limb-value)))

(defthm integer-add-limbs-correct
  (implies (and (integer-limbs-p left) (integer-limbs-p right)
                (<= (len right) (len left)) (bitp carry))
           (let ((result (integer-add-limbs left right carry)))
             (and (integer-limbs-p result)
                  (equal (len result) (1+ (len left)))
                  (equal (integer-limb-value result)
                         (+ (integer-limb-value left) (integer-limb-value right) carry)))))
  :hints (("Goal" :induct (integer-add-limbs left right carry))
          ("Subgoal *1/2"
           :use ((:instance integer-limb-add-correct
                            (left (car left)) (right (ifix (car right))))))))

(defthm integer-subtract-limbs-correct
  (implies (and (integer-limbs-p left) (integer-limbs-p right)
                (<= (len right) (len left)) (bitp borrow))
           (mv-let (result last) (integer-subtract-limbs left right borrow)
             (and (integer-limbs-p result)
                  (bitp last)
                  (equal (len result) (len left))
                  (equal (- (integer-limb-value result)
                            (* (integer-limb-capacity (len left)) last))
                         (- (integer-limb-value left) (+ (integer-limb-value right) borrow))))))
  :hints (("Goal" :induct (integer-subtract-limbs left right borrow))
          ("Subgoal *1/2"
           :use ((:instance integer-limb-subtract-correct
                            (left (car left)) (right (ifix (car right))))))))

(defthm integer-subtract-ordered-limbs
  (implies (and (integer-limbs-p left) (integer-limbs-p right)
                (<= (len right) (len left))
                (<= (integer-limb-value right) (integer-limb-value left)))
           (mv-let (result borrow) (integer-subtract-limbs left right 0)
             (and (equal borrow 0)
                  (equal (integer-limb-value result)
                         (- (integer-limb-value left) (integer-limb-value right))))))
  :hints (("Goal"
           :use ((:instance integer-subtract-limbs-correct (borrow 0))
                 (:instance integer-limb-value-bounds
                            (digits (mv-nth 0 (integer-subtract-limbs left right 0)))))
           :in-theory (e/d (bitp)
                           (integer-subtract-limbs-correct integer-limb-value-bounds
                            integer-subtract-limbs))
           :do-not-induct t)))

(local
 (defthm integer-limb-scale-product
   (equal (* factor (* *integer-limb-base* value))
          (* *integer-limb-base* (* factor value)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable associativity-of-*)
            :use ((:instance associativity-of-*
                             (acl2::x factor) (acl2::y *integer-limb-base*)
                             (acl2::z value))
                  (:instance associativity-of-*
                             (acl2::x *integer-limb-base*) (acl2::y factor)
                             (acl2::z value)))))))

(defthm integer-multiply-row-correct
  (implies (and (integer-limbs-p right) (integer-limbs-p old)
                (< (len right) (len old))
                (equal (nth (len right) old) 0)
                (integer-limb-p factor) (integer-limb-p carry))
           (let ((result (integer-multiply-row factor right old carry)))
             (and (integer-limbs-p result)
                  (equal (len result) (len old))
                  (equal (integer-limb-value result)
                         (+ (integer-limb-value old)
                            (* factor (integer-limb-value right)) carry))
                  (equal (nthcdr (+ 1 (len right)) result)
                         (nthcdr (+ 1 (len right)) old)))))
  :hints (("Goal" :induct (integer-multiply-row factor right old carry))
          ("Subgoal *1/2"
           :use ((:instance integer-limb-multiply-accumulate-correct
                            (left factor) (right (car right)) (old (car old)))
                 (:instance integer-limb-scale-product
                            (value (integer-limb-value (cdr right)))))
           :in-theory (disable integer-limb-multiply-accumulate-correct)
           :nonlinearp t)))
