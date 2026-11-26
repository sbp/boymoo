(in-package "BOYMOO-PROOFS")

(include-book "coerce-list-view")
(include-book "subseq-list-view")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-backward-copy-records (count cell first-rank objects)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      objects
    (let ((index (1- count)))
      (cons (proof-object (+ cell (* 16 index)) :active :cons (+ first-rank index))
            (sequence-backward-copy-records index cell first-rank objects)))))

(defun sequence-forward-copy-records (count cell first-rank objects)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      objects
    (cons (proof-object cell :active :cons (+ first-rank (1- count)))
          (sequence-forward-copy-records (1- count) (+ cell 16) first-rank objects))))

(local
 (defthm sequence-higher-record-does-not-change-backward-ranks
   (implies (and (natp count) (integerp cell) (integerp address)
                 (<= (+ cell (* 16 count)) address))
            (equal (sequence-backward-copy-ranks-p
                    count cell first-rank (cons (proof-object address zone kind rank) objects))
                   (sequence-backward-copy-ranks-p count cell first-rank objects)))
   :hints
   (("Goal"
     :induct (sequence-backward-copy-ranks-p count cell first-rank objects)
     :expand ((:free (records) (sequence-backward-copy-ranks-p count cell first-rank records)))))
   :rule-classes nil))

(defthm sequence-ranked-records-for-backward-copy
  (implies (and (natp count) (integerp cell))
           (sequence-backward-copy-ranks-p
            count cell first-rank (sequence-backward-copy-records count cell first-rank objects)))
  :hints
  (("Goal"
    :induct (sequence-backward-copy-records count cell first-rank objects)
    :expand ((:free (records) (sequence-backward-copy-ranks-p count cell first-rank records))))
   ("Subgoal *1/2"
    :use ((:instance sequence-higher-record-does-not-change-backward-ranks
                     (count (1- count)) (address (+ cell (* 16 (1- count))))
                     (zone :active) (kind :cons) (rank (+ first-rank (1- count)))
                     (objects (sequence-backward-copy-records (1- count) cell first-rank objects))))))
  :rule-classes nil)

(local
 (defthm sequence-lower-record-does-not-change-forward-ranks
   (implies (and (natp count) (integerp cell) (integerp address) (< address cell))
            (equal (sequence-forward-copy-ranks-p
                    count cell first-rank (cons (proof-object address zone kind rank) objects))
                   (sequence-forward-copy-ranks-p count cell first-rank objects)))
   :hints
   (("Goal"
     :induct (sequence-forward-copy-ranks-p count cell first-rank objects)
     :expand ((:free (records) (sequence-forward-copy-ranks-p count cell first-rank records)))))
   :rule-classes nil))

(defthm sequence-ranked-records-for-forward-copy
  (implies (and (natp count) (integerp cell))
           (sequence-forward-copy-ranks-p
            count cell first-rank (sequence-forward-copy-records count cell first-rank objects)))
  :hints
  (("Goal"
    :induct (sequence-forward-copy-records count cell first-rank objects)
    :expand ((:free (records) (sequence-forward-copy-ranks-p count cell first-rank records))))
   ("Subgoal *1/2"
    :use ((:instance sequence-lower-record-does-not-change-forward-ranks
                     (count (1- count)) (cell (+ 16 cell)) (address cell)
                     (zone :active) (kind :cons) (rank (+ first-rank (1- count)))
                     (objects (sequence-forward-copy-records (1- count) (+ 16 cell) first-rank objects))))))
  :rule-classes nil)
