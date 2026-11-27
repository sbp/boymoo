(in-package "BOYMOO-PROOFS")

(include-book "limbs")
(include-book "signed-words")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable floor mod ash expt unsigned-byte-p
                           boymoo-model::a64-unsigned)))

(defun integer-normalized-limbs-p (digits)
  (if (atom digits)
      (null digits)
    (and (integer-limb-p (car digits))
         (if (atom (cdr digits))
             (and (null (cdr digits)) (posp (car digits)))
           (integer-normalized-limbs-p (cdr digits))))))

(defun integer-trim-limbs (digits)
  (if (atom digits)
      nil
    (let ((rest (integer-trim-limbs (cdr digits))))
      (if (and (equal (car digits) 0) (null rest))
          nil
        (cons (car digits) rest)))))

(defun integer-normalized-sign (sign digits)
  (if (atom digits) 0 sign))

(defun integer-signed-limb-value (sign digits)
  (if (equal sign 1)
      (- (integer-limb-value digits))
    (integer-limb-value digits)))

(defthm integer-normalized-limbs-are-limbs
  (implies (integer-normalized-limbs-p digits)
           (integer-limbs-p digits))
  :hints (("Goal" :induct (integer-normalized-limbs-p digits))))

(defthm integer-trim-limbs-correct
  (implies (integer-limbs-p digits)
           (let ((trimmed (integer-trim-limbs digits)))
             (and (integer-normalized-limbs-p trimmed)
                  (<= (len trimmed) (len digits))
                  (equal (integer-limb-value trimmed) (integer-limb-value digits)))))
  :hints (("Goal" :induct (integer-trim-limbs digits))))

(defthm integer-trim-signed-value
  (implies (and (integer-limbs-p digits) (bitp sign))
           (let* ((trimmed (integer-trim-limbs digits))
                  (normalized-sign (integer-normalized-sign sign trimmed)))
             (and (bitp normalized-sign)
                  (implies (atom trimmed) (equal normalized-sign 0))
                  (equal (integer-signed-limb-value normalized-sign trimmed)
                         (integer-signed-limb-value sign digits)))))
  :hints (("Goal"
           :in-theory (disable integer-trim-limbs-correct)
           :use integer-trim-limbs-correct)))

(local
 (defun integer-capacity-induction (a b)
   (declare (xargs :measure (nfix b)))
   (if (or (zp a) (zp b))
       nil
     (integer-capacity-induction (1- a) (1- b)))))

(defthm integer-limb-capacity-monotone
  (implies (and (natp a) (natp b) (<= a b))
           (<= (integer-limb-capacity a) (integer-limb-capacity b)))
  :rule-classes :linear
  :hints (("Goal" :induct (integer-capacity-induction a b))))

(defthm integer-normalized-limbs-lower-bound
  (implies (and (integer-normalized-limbs-p digits) (consp digits))
           (<= (integer-limb-capacity (1- (len digits)))
               (integer-limb-value digits)))
  :rule-classes :linear
  :hints (("Goal" :induct (integer-normalized-limbs-p digits))))

(defthm integer-normalized-limb-value-positive
  (implies (and (integer-normalized-limbs-p digits) (consp digits))
           (< 0 (integer-limb-value digits)))
  :rule-classes :linear
  :hints (("Goal" :use integer-normalized-limbs-lower-bound)))

(defthm integer-normalized-limb-count-orders-magnitudes
  (implies (and (integer-normalized-limbs-p left)
                (integer-normalized-limbs-p right)
                (< (len left) (len right)))
           (< (integer-limb-value left) (integer-limb-value right)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable integer-limb-capacity
                                     integer-normalized-limbs-p)
           :use ((:instance integer-limb-capacity-monotone
                            (a (len left)) (b (1- (len right))))
                 (:instance integer-limb-value-bounds (digits left))
                 (:instance integer-normalized-limbs-lower-bound (digits right))))))

(defun integer-order (left right)
  (cond ((< left right) -1)
        ((< right left) 1)
        (t 0)))

(defun integer-compare-equal-length (left right)
  (if (atom left)
      0
    (let ((high (integer-compare-equal-length (cdr left) (cdr right))))
      (if (equal high 0)
          (integer-order (car left) (car right))
        high))))

(defthm integer-compare-equal-length-correct
  (implies (and (integer-limbs-p left) (integer-limbs-p right)
                (equal (len left) (len right)))
           (equal (integer-compare-equal-length left right)
                  (integer-order (integer-limb-value left)
                                 (integer-limb-value right))))
  :hints (("Goal" :induct (integer-compare-equal-length left right))))

(defun integer-compare-magnitudes (left right)
  (let ((length-order (integer-order (len left) (len right))))
    (if (equal length-order 0)
        (integer-compare-equal-length left right)
      length-order)))

(defthm integer-compare-magnitudes-correct
  (implies (and (integer-normalized-limbs-p left)
                (integer-normalized-limbs-p right))
           (equal (integer-compare-magnitudes left right)
                  (integer-order (integer-limb-value left)
                                 (integer-limb-value right))))
  :hints (("Goal" :in-theory (disable integer-normalized-limbs-p
                                     integer-compare-equal-length)
           :use (integer-normalized-limb-count-orders-magnitudes
                 (:instance integer-normalized-limb-count-orders-magnitudes
                            (left right) (right left))))))

(defun integer-compare-signed (left-sign left right-sign right)
  (if (equal left-sign right-sign)
      (let ((order (integer-compare-magnitudes left right)))
        (if (equal left-sign 1) (- order) order))
    (- right-sign left-sign)))

(defthm integer-compare-signed-correct
  (implies (and (integer-normalized-limbs-p left)
                (integer-normalized-limbs-p right)
                (bitp left-sign) (bitp right-sign)
                (implies (atom left) (equal left-sign 0))
                (implies (atom right) (equal right-sign 0)))
           (equal (integer-compare-signed left-sign left right-sign right)
                  (integer-order (integer-signed-limb-value left-sign left)
                                 (integer-signed-limb-value right-sign right))))
  :hints (("Goal" :in-theory (e/d (bitp)
                                  (integer-compare-magnitudes
                                   integer-normalized-limbs-p)))))

(defun integer-pack-immediate-p (sign digits)
  (and (<= (len digits) 2)
       (< (integer-limb-value digits) (+ (expt 2 62) sign))))

(defthm integer-pack-immediate-test-correct
  (implies (and (integer-normalized-limbs-p digits)
                (bitp sign))
           (equal (integer-pack-immediate-p sign digits)
                  (proof-immediate-integer-p (integer-signed-limb-value sign digits))))
  :hints (("Goal" :in-theory (e/d (bitp)
                                  (integer-normalized-limbs-p))
           :use ((:instance integer-limb-capacity-monotone
                            (a 2) (b (1- (len digits))))
                 integer-normalized-limbs-lower-bound
                 integer-limb-value-bounds))))

(defun integer-read-limbs (count address machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (proof-load-word address machine)
          (integer-read-limbs (1- count) (+ 8 address) machine))))

(defthm integer-read-limbs-length
  (equal (len (integer-read-limbs count address machine)) (nfix count))
  :hints (("Goal" :induct (integer-read-limbs count address machine))))

(defthm integer-read-limbs-nonempty
  (equal (consp (integer-read-limbs count address machine))
         (posp count))
  :hints (("Goal" :expand (integer-read-limbs count address machine))))

(defthm integer-limb-value-of-read
  (equal (integer-limb-value (integer-read-limbs count address machine))
         (proof-limb-magnitude count address machine))
  :hints (("Goal" :induct (integer-read-limbs count address machine)
           :in-theory (disable proof-load-word))))

(defthm integer-normalized-limbs-of-read
  (equal (integer-normalized-limbs-p (integer-read-limbs count address machine))
         (proof-limbs-p count address machine))
  :hints (("Goal" :induct (integer-read-limbs count address machine)
           :in-theory (e/d (unsigned-byte-p integer-range-p) (proof-load-word)))))

(defun integer-header (count)
  (+ 3 (* 2048 (+ 1 count))))

(defun integer-storage-bytes (count)
  (* 8 (+ 2 count)))

(defthm integer-header-fields
  (implies (natp count)
           (and (equal (proof-header-size (integer-header count)) (* 8 (+ 1 count)))
                (equal (proof-header-type (integer-header count)) 3)))
  :hints (("Goal" :in-theory (e/d (integer-ash-right) (proof-immediate-integer-p))
           :use ((:instance integer-floor-unique
                            (x (integer-header count)) (y 256) (q (* 8 (+ 1 count))))
                 (:instance integer-mod-unique
                            (x (integer-header count)) (q (* 8 (+ 1 count)))
                            (r 3) (d 256))))))

(defthm integer-limb-magnitude-is-integer
  (integerp (proof-limb-magnitude count address machine))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (proof-limb-magnitude count address machine)
           :in-theory (disable proof-load-word))))

(defthm integer-memory-view
  (implies (and (natp count)
                (equal (proof-load-word address (proof-world-machine world))
                       (integer-header count))
                (proof-span-p address (integer-storage-bytes count))
                (bitp (proof-load-word (+ 8 address) (proof-world-machine world)))
                (implies (equal count 0)
                         (equal (proof-load-word (+ 8 address) (proof-world-machine world))
                                0))
                (integer-normalized-limbs-p
                 (integer-read-limbs count (+ 16 address) (proof-world-machine world))))
           (let* ((machine (proof-world-machine world))
                  (value (integer-signed-limb-value
                          (proof-load-word (+ 8 address) machine)
                          (integer-read-limbs count (+ 16 address) machine))))
             (proof-integer-view-p value address count world)))
  :hints (("Goal"
           :in-theory (e/d (bitp integer-ash-right)
                           (integer-header proof-span-p proof-load-word proof-header-size
                            proof-header-type proof-limb-magnitude proof-limbs-p
                            integer-normalized-limbs-p integer-read-limbs))
           :use ((:instance (:definition integer-header))
                 (:instance integer-floor-unique
                            (x (* 8 (+ 1 count))) (y 8) (q (+ 1 count)))
                 (:instance integer-mod-of-division (q (+ 1 count)) (r 0) (y 8))))))

(defthm integer-header-count
  (implies (natp count)
           (equal (ash (integer-header count) -11) (+ 1 count)))
  :hints (("Goal" :in-theory (enable integer-ash-right)
           :use ((:instance integer-floor-unique
                            (x (integer-header count)) (y 2048) (q (+ 1 count)))))))

(defthm integer-memory-view-components
  (implies (proof-integer-view-p value address count world)
           (let* ((machine (proof-world-machine world))
                  (sign (proof-load-word (+ 8 address) machine))
                  (digits (integer-read-limbs count (+ 16 address) machine)))
             (and (proof-span-p address (integer-storage-bytes count))
                  (bitp sign)
                  (implies (equal count 0) (equal sign 0))
                  (integer-normalized-limbs-p digits)
                  (equal value (integer-signed-limb-value sign digits)))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (bitp integer-ash-right)
                           (proof-span-p proof-load-word proof-header-size
                            proof-header-type proof-limb-magnitude proof-limbs-p
                            integer-normalized-limbs-p integer-read-limbs))
           :use ((:instance integer-header-fields)
                 (:instance integer-floor-unique
                            (x (* 8 (+ 1 count))) (y 8) (q (+ 1 count)))))))

(defun integer-binary-reservation-bytes (left-count right-count)
  (* 8 (+ 3 left-count right-count)))

(defthm integer-binary-reservation
  (implies (and (natp left-count) (natp right-count)
                (<= (integer-storage-bytes left-count) *proof-space-size*)
                (<= (integer-storage-bytes right-count) *proof-space-size*))
           (let ((bytes (integer-binary-reservation-bytes left-count right-count)))
             (and (natp bytes)
                  (< bytes (expt 2 64))
                  (equal (mod bytes 8) 0)
                  (<= (integer-storage-bytes (+ 1 left-count)) bytes)
                  (<= (integer-storage-bytes (+ 1 right-count)) bytes)
                  (<= (integer-storage-bytes (+ left-count right-count)) bytes)
                  (equal (proof-resource-bound-p :allocation-size bytes world)
                         (< *proof-space-size* bytes)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance integer-mod-of-division
                            (q (+ 3 left-count right-count)) (r 0) (y 8))))))

(defthm integer-limb-capacity-as-power-of-two
  (implies (natp count)
           (equal (integer-limb-capacity count) (expt 2 (* 32 count))))
  :hints (("Goal" :induct (integer-limb-capacity count))
          ("Subgoal *1/2" :use ((:instance integer-power-of-two-add
                                          (a 32) (b (* 32 (1- count))))))))
