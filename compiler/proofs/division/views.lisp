(in-package "BOYMOO-PROOFS")

(include-book "limbs")
(include-book "words")

(logic)
(set-verify-guards-eagerness 0)
(local (in-theory (disable floor mod ash proof-load-word)))

(defun division-normalized-limbs-p (digits)
  (if (atom digits)
      (null digits)
    (and (division-digit-p (car digits))
         (if (null (cdr digits))
             (posp (car digits))
           (division-normalized-limbs-p (cdr digits))))))

(defun division-trim-limbs (digits)
  (if (atom digits)
      nil
    (let ((upper (division-trim-limbs (cdr digits))))
      (if (and (null upper) (equal (car digits) 0))
          nil
        (cons (car digits) upper)))))

(defthm division-trim-limbs-correct
  (implies (division-digits-p digits)
           (let ((trimmed (division-trim-limbs digits)))
             (and (division-normalized-limbs-p trimmed)
                  (<= (len trimmed) (len digits))
                  (equal (division-magnitude trimmed) (division-magnitude digits)))))
  :rule-classes nil)

(defun division-read-limbs (count address machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (proof-load-word address machine)
          (division-read-limbs (1- count) (+ 8 address) machine))))

(defthm division-read-limbs-count
  (equal (len (division-read-limbs count address machine)) (nfix count)))

(local
 (defthm division-read-limbs-empty
   (iff (division-read-limbs count address machine) (posp count))
   :hints (("Goal" :expand ((division-read-limbs count address machine))))))

(defthm division-read-limbs-normalized
  (equal (division-normalized-limbs-p (division-read-limbs count address machine))
         (proof-limbs-p count address machine))
  :hints (("Goal" :induct (division-read-limbs count address machine))))

(defthm division-normalized-limbs-are-digits
  (implies (division-normalized-limbs-p digits)
           (division-digits-p digits)))

(defthm division-read-limbs-view-magnitude
  (implies (division-digits-p (division-read-limbs count address machine))
           (equal (division-magnitude (division-read-limbs count address machine))
                  (proof-limb-magnitude count address machine)))
  :hints (("Goal" :induct (division-read-limbs count address machine))))

(defthm division-view-header-byte-count
  (implies (natp count)
           (let ((header (+ 3 (* 2048 (1+ count)))))
             (and (equal (proof-header-size header) (* 8 (1+ count)))
                  (equal (ash (proof-header-size header) -3) (1+ count)))))
  :hints (("Goal"
           :use ((:instance division-ash-right (x (+ 3 (* 2048 (1+ count)))) (width 8))
                 (:instance division-ash-right (x (* 8 (1+ count))) (width 3))
                 (:instance division-quotient-unique
                            (a (+ 3 (* 2048 (1+ count)))) (b 256) (q (* 8 (1+ count))) (r 3))
                 (:instance division-quotient-unique
                            (a (* 8 (1+ count))) (b 8) (q (1+ count)) (r 0)))
           :in-theory (disable division-ash-right)))
  :rule-classes nil)

(defthm division-view-magnitude-and-count
  (implies (proof-integer-view-p value address count world)
           (let* ((machine (proof-world-machine world))
                  (header (proof-load-word address machine))
                  (digits (division-read-limbs count (+ 16 address) machine)))
             (and (equal (- (proof-header-size header) 8) (* 8 count))
                  (division-normalized-limbs-p digits)
                  (equal (division-magnitude digits) (abs value)))))
  :hints (("Goal"
           :use ((:instance division-view-header-byte-count)
                 (:instance division-read-limbs-view-magnitude
                            (address (+ 16 address)) (machine (proof-world-machine world))))
           :in-theory (disable division-read-limbs-view-magnitude division-read-limbs
                               proof-limb-magnitude proof-limbs-p proof-header-size)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defun division-compare-length-induct (left right)
   (if (atom right)
       left
     (division-compare-length-induct (cdr left) (cdr right)))))

(defthm division-shorten-dividend
  (implies (and (division-digits-p left) (division-normalized-limbs-p right)
                (< (len left) (len right)))
           (< (division-magnitude left) (division-magnitude right)))
  :hints (("Goal" :induct (division-compare-length-induct left right)))
  :rule-classes nil)
