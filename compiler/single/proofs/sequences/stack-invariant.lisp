(in-package "BOYMOO-PROOFS")

(include-book "stack-static")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-dynamic-view proof-stack-prefix proof-dynamic-entries
                    proof-string-accounting-p proof-external-bytes
                    proof-dynamic-symbol-objects-p proof-prefix-preserved-p
                    proof-dynamic-table-preserved-p proof-heap-frame-p
                    proof-preserved-heap-p proof-fixed-heap-p))

(local
 (defthm sequence-stack-top-bounds
   (implies (proof-heap-layout-p world)
            (and (<= (proof-stack-base world) (proof-stack-top world))
                 (<= (proof-stack-top world) (proof-stack-end world))))
   :hints (("Goal" :expand ((proof-heap-layout-p world))))
   :rule-classes nil))

(defthm sequence-stack-write-keeps-value-stack-prefix
  (implies (and (proof-heap-p before objects packages)
                (sequence-stack-write-p start end before after)
                (proof-stack-prefix top before objects packages))
           (equal (proof-stack-prefix top after objects packages)
                  (proof-stack-prefix top before objects packages)))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-stack-write-p sequence-heap-registers-agree-p
                     sequence-heap-metadata-agrees-p)
                    (proof-disjoint-p proof-stack-views))
    :expand ((proof-stack-prefix top before objects packages)
             (proof-stack-prefix top after objects packages))
    :use ((:instance sequence-heap-layout-bounds (world before))
          (:instance sequence-stack-top-bounds (world before))
          sequence-stack-write-keeps-heap-metadata sequence-stack-write-keeps-heap-spans
          sequence-stack-write-keeps-published-storage
          (:instance sequence-floor-bounds (value (- top (proof-stack-base before))) (divisor 8))
          (:instance sequence-stack-views-on-agreed-storage
                     (address (proof-stack-base before))
                     (count (ash (- top (proof-stack-base before)) -3))
                     (base (proof-heap-base before))
                     (lower (proof-stack-base before)) (upper (proof-stack-end before))
                     (first (proof-world-machine before)) (last (proof-world-machine after))))))
  :rule-classes nil)

(defthm sequence-stack-write-keeps-dynamic-view
  (implies (and (proof-heap-p before objects packages)
                (sequence-stack-write-p start end before after))
           (equal (proof-dynamic-view after objects packages)
                  (proof-dynamic-view before objects packages)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-dynamic-view proof-dynamic-root sequence-stack-write-p
                     sequence-heap-registers-agree-p)
                    (proof-view proof-span-p proof-subspan-p))
    :use (sequence-stack-write-keeps-published-storage
          (:instance sequence-static-header-after-stack-write (offset 24))
          (:instance sequence-view-on-agreed-objects
                     (word (proof-load-word (+ 24 (proof-heap-base before)) (proof-world-machine before)))
                     (base (proof-heap-base before))
                     (first (proof-world-machine before)) (last (proof-world-machine after))))))
  :rule-classes nil)

(local
 (defthm sequence-stack-write-keeps-string-accounting
   (let* ((head (proof-external-head before))
          (old (proof-external-objects head (len objects) before objects))
          (new (proof-external-objects (proof-external-head after) (len objects) after objects)))
     (implies (and (proof-heap-layout-p before)
                   (sequence-stack-write-p start end before after)
                   old)
              (and (equal new old)
                   (proof-fixed-external-p (cdr old) before after)
                   (equal (proof-string-accounting-p (cdr new) after)
                          (proof-string-accounting-p (cdr old) before)))))
   :hints
   (("Goal"
     :in-theory (enable sequence-heap-metadata-agrees-p proof-string-accounting-p)
     :use (sequence-stack-write-keeps-heap-metadata
           (:instance sequence-stack-write-keeps-external-mappings
                      (head (proof-external-head before)) (fuel (len objects))))))
   :rule-classes nil))

(defthm sequence-stack-write-keeps-heap-invariant
  (implies (and (proof-heap-p before objects packages)
                (sequence-stack-write-p start end before after))
           (proof-heap-p after objects packages))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-stack-write-p sequence-heap-registers-agree-p)
                    (proof-static-p proof-object-map-p proof-span-p proof-subspan-p
                     proof-heap-object-spans-p sequence-heap-metadata-agrees-p proof-view))
    :expand ((proof-heap-p before objects packages)
             (proof-heap-p after objects packages))
    :use (sequence-stack-write-keeps-heap-layout sequence-stack-write-keeps-heap-metadata
          sequence-stack-write-keeps-static-heap sequence-stack-write-keeps-published-storage
          sequence-stack-write-keeps-dynamic-view sequence-stack-write-keeps-string-accounting
          (:instance sequence-object-map-on-agreed-storage
                     (base (proof-heap-base before)) (pending objects) (symbols nil)
                     (first (proof-world-machine before)) (last (proof-world-machine after)))
          (:instance sequence-object-spans-on-agreed-storage
                     (pending objects)
                     (external (cdr (proof-external-objects (proof-external-head before)
                                                           (len objects) before objects))))
          (:instance sequence-dynamic-symbols-on-agreed-storage
                     (pending objects) (base (proof-heap-base before))
                     (entries (cdr (proof-dynamic-entries
                                    (proof-dynamic-view before objects packages) packages)))
                     (first (proof-world-machine before)) (last (proof-world-machine after)))
          (:instance sequence-stack-write-keeps-value-stack-prefix (top (proof-stack-top before))))))
  :rule-classes nil)

(defthm sequence-confined-stack-write-preserves-heap
  (implies (and (proof-heap-p before objects packages)
                (sequence-stack-write-p start end before after))
           (and (proof-fixed-heap-p before after objects)
                (proof-preserved-heap-p nil before after objects objects packages)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-fixed-heap-p proof-preserved-heap-p
                     proof-prefix-preserved-p proof-dynamic-table-preserved-p
                     sequence-stack-write-p sequence-heap-registers-agree-p)
                    (proof-subspan-p proof-span-p proof-streams-preserved-p proof-fixed-external-p
                     proof-world-replies proof-world-stop proof-world-page-size))
    :expand ((proof-heap-p before objects packages))
    :use (sequence-stack-write-keeps-heap-invariant sequence-stack-write-keeps-caller-heap-frame
          sequence-stack-write-keeps-dynamic-view sequence-stack-write-keeps-heap-spans
          sequence-stack-write-keeps-string-accounting sequence-world-tail-fields
          (:instance sequence-stack-write-keeps-value-stack-prefix (top (proof-stack-top before))))))
  :rule-classes nil)

(defthm sequence-confined-stack-write-preserves-value
  (implies (and (proof-heap-p before objects packages)
                (sequence-stack-write-p start end before after)
                (proof-machine-value-p word datum before objects packages))
           (proof-machine-value-p word datum after objects packages))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-stack-write-p sequence-heap-registers-agree-p
                     proof-value-p proof-machine-value-p)
                    (proof-subspan-p proof-span-p proof-view))
    :use (sequence-stack-write-keeps-published-storage
          (:instance sequence-view-on-agreed-objects
                     (base (proof-heap-base before))
                     (first (proof-world-machine before)) (last (proof-world-machine after))))))
  :rule-classes nil)
