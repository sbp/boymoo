(in-package "BOYMOO-PROOFS")

(include-book "placement")

(logic)
(set-verify-guards-eagerness 0)

; A positive span which avoids an unmapped interval remains covered.
; The interval may cut a writable region into a left and a right part.
(defthm collection-removal-preserves-disjoint-coverage
  (implies (and (posp width)
                (proof-covered-p address width access regions)
                (proof-disjoint-p address (+ address width) base (+ base size)))
           (proof-covered-p address width access
                            (proof-remove-region-span base size regions)))
  :hints (("Goal" :induct (proof-remove-region-span base size regions)
                  :in-theory (disable proof-region-allows-p))))

(defun collection-region-bytes (regions)
  (if (endp regions)
      0
    (+ (nfix (- (cadar regions) (caar regions)))
       (collection-region-bytes (cdr regions)))))

(defthm collection-removal-debits-region-bytes
  (implies (proof-covered-p base size :write regions)
           (equal (+ size (collection-region-bytes
                           (proof-remove-region-span base size regions)))
                  (collection-region-bytes regions)))
  :hints (("Goal" :induct (proof-remove-region-span base size regions))))
