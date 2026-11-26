(in-package "BOYMOO-PROOFS")

(include-book "../foundations/kernel")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun allocation-region-bytes (regions)
  (if (atom regions)
      0
    (+ (- (cadar regions) (caar regions))
       (allocation-region-bytes (cdr regions)))))

(defun allocation-regions-within-p (lower upper regions)
  (if (atom regions)
      t
    (and (<= lower (caar regions))
         (<= (cadar regions) upper)
         (allocation-regions-within-p lower upper (cdr regions)))))

; The range tally counts the intersection of each region with the
; specified interval. At most one region contributes any one byte.
(local
 (defun allocation-region-contains-p (address region)
   (and (<= (car region) address) (< address (cadr region)))))

(local
 (defun allocation-regions-contain-p (address regions)
   (if (atom regions)
       nil
     (or (allocation-region-contains-p address (car regions))
         (allocation-regions-contain-p address (cdr regions))))))

(local
 (defun allocation-region-overlap-bytes (lower upper region)
   (nfix (- (min upper (cadr region)) (max lower (car region))))))

(local
 (defun allocation-region-range-tally (lower upper regions)
   (if (atom regions)
       0
     (+ (allocation-region-overlap-bytes lower upper (car regions))
        (allocation-region-range-tally lower upper (cdr regions))))))

(local
 (defthm allocation-point-in-disjoint-region-is-uncovered
   (implies (and (<= start address) (< address end)
                 (proof-region-disjoint-p start end regions))
            (not (allocation-regions-contain-p address regions)))
   :hints (("Goal" :induct (proof-region-disjoint-p start end regions)))))

(local
 (defthm allocation-region-overlap-advance-one-byte
   (implies (and (integerp lower) (integerp upper) (< lower upper)
                 (proof-region-p region))
            (equal (allocation-region-overlap-bytes lower upper region)
                   (+ (if (allocation-region-contains-p lower region) 1 0)
                      (allocation-region-overlap-bytes (1+ lower) upper region))))))

(local
 (defthm allocation-region-range-tally-advance-one-byte
   (implies (and (integerp lower) (integerp upper) (< lower upper) (proof-regions-p regions))
            (equal (allocation-region-range-tally lower upper regions)
                   (+ (if (allocation-regions-contain-p lower regions) 1 0)
                      (allocation-region-range-tally (1+ lower) upper regions))))
   :rule-classes nil
   :hints (("Goal" :induct (proof-regions-p regions)
            :in-theory (disable proof-region-p proof-region-disjoint-p allocation-region-overlap-bytes))
           ("Subgoal *1/2"
            :use ((:instance allocation-region-overlap-advance-one-byte (region (car regions)))
                  (:instance allocation-point-in-disjoint-region-is-uncovered
                   (start (caar regions)) (end (cadar regions)) (address lower) (regions (cdr regions))))))))

(local
 (defthm allocation-region-range-tally-of-empty-range
   (implies (<= upper lower)
            (equal (allocation-region-range-tally lower upper regions) 0))
   :hints (("Goal" :induct (allocation-region-range-tally lower upper regions)))))

(local
 (defun allocation-range-induction (lower upper)
   (declare (xargs :measure (nfix (- upper lower))))
   (if (and (integerp lower) (integerp upper) (< lower upper))
       (allocation-range-induction (1+ lower) upper)
     lower)))

(local
 (defthm allocation-region-range-tally-is-bounded
   (implies (and (integerp lower) (integerp upper) (<= lower upper)
                 (proof-regions-p regions))
            (<= (allocation-region-range-tally lower upper regions) (- upper lower)))
   :rule-classes nil
   :hints (("Goal" :induct (allocation-range-induction lower upper)
            :in-theory (disable proof-regions-p allocation-region-range-tally))
           ("Subgoal *1/1" :use allocation-region-range-tally-advance-one-byte))))

(local
 (defthm allocation-region-range-tally-counts-contained-regions
   (implies (and (allocation-regions-within-p lower upper regions)
                 (proof-regions-p regions))
            (equal (allocation-region-range-tally lower upper regions)
                   (allocation-region-bytes regions)))
   :hints (("Goal" :induct (proof-regions-p regions)
            :in-theory (disable proof-region-disjoint-p)))))

(defthm allocation-regions-total-fits-range
  (implies (and (integerp lower) (integerp upper) (<= lower upper)
                (proof-regions-p regions)
                (allocation-regions-within-p lower upper regions))
           (<= (allocation-region-bytes regions) (- upper lower)))
  :rule-classes nil
  :hints (("Goal" :use allocation-region-range-tally-is-bounded
           :in-theory (disable proof-regions-p allocation-region-bytes allocation-region-range-tally))))
