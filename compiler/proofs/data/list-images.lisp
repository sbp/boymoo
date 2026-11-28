(in-package "BOYMOO-PROOFS")

(include-book "bucket-views")
(include-book "collections")

(logic)
(set-verify-guards-eagerness 0)

(defun data-forward-list-cell-chunks (words tail offset)
  (if (atom words)
      nil
    (list* (car words) tail (data-forward-list-cell-chunks (cdr words) offset (+ 16 offset)))))

(local
 (defun list-cell-chunk-order-induction (words tail offset prior)
   (if (atom words)
       (list tail offset prior)
     (list-cell-chunk-order-induction (cdr words) offset (+ 16 offset) (list* tail (car words) prior)))))

(local
 (defthm append-associates-for-cell-chunks
   (equal (append (append left middle) right) (append left middle right))))

(defthmd data-list-cell-chunks-match-forward-allocation-order
  (equal (boymoo-compiler::reverse-onto (data-forward-list-cell-chunks words tail offset) prior)
         (append (data-list-cell-chunks words tail offset) prior))
  :hints (("Goal" :induct (list-cell-chunk-order-induction words tail offset prior))))

(defun data-list-cell-records-and-cars-p (words values slot base objects packages machine)
  (if (atom words)
      (and (null words) (null values))
    (let ((address (+ base (* 8 slot))))
      (and (consp values)
           (equal (assoc-equal address objects) (proof-object address :static :cons slot))
           (data-child-value-p (proof-constant-word (car words)) (car values) slot base objects packages machine)
           (data-list-cell-records-and-cars-p (cdr words) (cdr values) (+ 2 slot)
                                              base objects packages machine)))))

(local
 (defun list-cell-layout-induction (words values tail slot)
   (if (atom words)
       (list values tail slot)
     (list-cell-layout-induction (cdr words) (cdr values) (* 8 slot) (+ 2 slot)))))

(local
 (in-theory (disable proof-view proof-load-word proof-word-tag proof-pointer-address
                     data-child-value-p data-word-visible-at-rank-p data-placed-characters-p evenp)))

(local
 (defthm previous-cell-encodes-to-its-own-word
   (implies (and (natp slot) (< (* 8 slot) *proof-space-size*))
            (equal (proof-constant-word (* 8 slot)) (* 8 slot)))))

(local
 (defthm placed-span-base-is-an-integer
   (implies (proof-span-p base size) (integerp base))
   :rule-classes :forward-chaining))

(local
 (in-theory (disable proof-constant-word)))

(defthmd data-placed-list-cell-fields-give-view-layout
  (implies (and (proof-span-p base size) (< size *proof-space-size*) (posp slot)
                (<= (+ (* 8 slot) (* 16 (len words))) size)
                (data-list-cell-records-and-cars-p words values slot base objects packages machine)
                (data-word-visible-at-rank-p (proof-constant-word tail) slot base objects)
                (data-memory-words-p (data-encoded-words (data-forward-list-cell-chunks words tail (* 8 slot)))
                                     (+ base (* 8 slot)) machine))
           (data-list-cell-view-layout-p words values tail (* 8 slot) base objects packages machine))
  :hints (("Goal" :induct (list-cell-layout-induction words values tail slot))
          ("Subgoal *1/2" :use ((:instance data-static-reference-fits-and-points-at-offset (tag 0))
                                (:instance data-aligned-static-cons-is-visible-at-larger-rank (parent (+ 2 slot)))))))

(defthmd data-view-of-placed-list-cell-allocation
  (let* ((offset (car block)) (allocated (data-forward-list-cell-chunks words tail offset)))
    (implies (and (proof-span-p base size) (< size *proof-space-size*) (posp slot)
                  (equal offset (* 8 slot)) (<= (+ offset (* 16 (len words))) size)
                  (data-encodable-chunks-p allocated)
                  (data-placed-characters-p (data-forward-chunk-characters allocated) (+ base offset) machine)
                  (data-list-cell-records-and-cars-p words values slot base objects packages machine)
                  (data-child-value-p (proof-constant-word tail) tail-value slot base objects packages machine))
             (proof-value-p (proof-constant-word (mv-nth 0 (boymoo-compiler::data-list-cells words tail block)))
                            (boymoo-compiler::reverse-onto values tail-value) base objects packages machine)))
  :hints (("Goal" :use (data-placed-list-cell-fields-give-view-layout data-view-of-static-list-cell-block
                        (:instance data-placed-encodable-chunks-load-their-words
                                   (chunks (data-forward-list-cell-chunks words tail (car block)))
                                   (address (+ base (car block)))))
                  :in-theory (e/d (data-child-value-p)
                                 (proof-value-p data-list-cell-view-layout-p data-forward-list-cell-chunks
                                  data-list-cell-records-and-cars-p data-forward-chunk-characters
                                  data-memory-words-p data-encodable-chunks-p data-encoded-words
                                  boymoo-compiler::data-list-cells boymoo-compiler::reverse-onto)))))

(defthmd data-view-of-retained-list-cell-allocation
  (let* ((offset (car block)) (allocated (data-forward-list-cell-chunks words tail offset)))
    (implies (and (proof-span-p base size) (< size *proof-space-size*) (posp slot)
                  (equal offset (* 8 slot)) (<= (+ offset (* 16 (len words))) size)
                  (data-encodable-chunks-p allocated) (data-block-sized-p block 80)
                  (data-retained-chunks-p (cdr (mv-nth 1 (boymoo-compiler::data-list-cells words tail block))) body)
                  (data-placed-characters-p (data-chunks-characters body) (+ base 80) machine)
                  (data-list-cell-records-and-cars-p words values slot base objects packages machine)
                  (data-child-value-p (proof-constant-word tail) tail-value slot base objects packages machine))
             (proof-value-p (proof-constant-word (mv-nth 0 (boymoo-compiler::data-list-cells words tail block)))
                            (boymoo-compiler::reverse-onto values tail-value) base objects packages machine)))
  :hints (("Goal" :use ((:instance data-list-cells-allocate-consecutive-pairs (reversed words))
                        (:instance data-list-cell-chunks-match-forward-allocation-order
                                   (offset (car block)) (prior (cdr block)))
                        (:instance data-placed-retained-builder-allocation (before block)
                                   (allocated (data-forward-list-cell-chunks words tail (car block))))
                        data-view-of-placed-list-cell-allocation)
                  :in-theory (disable data-retained-chunks-p data-list-cell-records-and-cars-p
                                      data-chunks-characters data-forward-chunk-characters data-block-sized-p
                                      data-encodable-chunks-p data-forward-list-cell-chunks data-list-cell-chunks
                                      proof-span-p proof-value-p boymoo-compiler::data-list-cells
                                      boymoo-compiler::reverse-onto))))
