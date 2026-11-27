(in-package "BOYMOO-PROOFS")

(include-book "external-frame")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-heap-layout-p proof-world-machine proof-heap-base
                    proof-object-map-p proof-object-disjoint-p proof-heap-object-spans-p
                    proof-string-accounting-p proof-dynamic-symbol-objects-p proof-dynamic-entries
                    proof-external-objects proof-external-bytes proof-stack-prefix proof-dynamic-view
                    proof-view proof-dynamic-root proof-static-p proof-static-size proof-stack-top
                    proof-object-size proof-object-address proof-object-zone proof-object-kind
                    proof-span-p proof-subspan-p proof-disjoint-p expt))

(local
 (defthm generated-stack-update-preserves-static-data
   (implies (and (proof-heap-layout-p before) (generated-stack-update-p start end before after)
                 (proof-static-p (proof-heap-base before) objects packages (proof-world-machine before)))
            (proof-static-p (proof-heap-base after) objects packages (proof-world-machine after)))
   :hints (("Goal"
            :use (generated-stack-write-disjoint-from-main-heap
                  (:instance generated-static-data-outside-written-span
                             (base (proof-heap-base before))
                             (first (proof-world-machine before)) (last (proof-world-machine after))))
            :in-theory (enable generated-stack-update-p)))
   :rule-classes nil))

(local
 (defthm generated-stack-update-preserves-object-spans
   (implies (and (proof-heap-layout-p before) (generated-stack-update-p start end before after)
                 (generated-object-observations-agree-p pending objects (proof-heap-base before) packages
                                                       (proof-world-machine before) (proof-world-machine after)))
            (equal (proof-heap-object-spans-p pending external after)
                   (proof-heap-object-spans-p pending external before)))
   :hints (("Goal" :induct (len pending)
                   :in-theory (enable generated-object-observations-agree-p proof-heap-object-spans-p))
           ("Subgoal *1/1"
            :use generated-stack-update-preserves-runtime-fields
            :in-theory (enable generated-stack-update-p generated-object-observations-agree-p
                               proof-heap-object-spans-p)))
   :rule-classes nil))

(local
 (defthm generated-stack-update-preserves-accounting
   (implies (and (proof-heap-layout-p before) (generated-stack-update-p start end before after)
                 (equal (proof-external-bytes headers (proof-world-machine after))
                        (proof-external-bytes headers (proof-world-machine before))))
            (equal (proof-string-accounting-p headers after)
                   (proof-string-accounting-p headers before)))
   :hints (("Goal" :use generated-stack-update-preserves-runtime-fields
                   :in-theory (enable proof-string-accounting-p)))
   :rule-classes nil))

(defthm generated-stack-update-preserves-dynamic-view
  (let* ((base (proof-heap-base before))
         (first (proof-world-machine before)))
    (implies (and (proof-heap-layout-p before) (generated-stack-update-p start end before after)
                  (proof-object-map-p objects objects nil base packages first)
                  (proof-object-disjoint-p start end objects first))
             (equal (proof-dynamic-view after objects packages)
                    (proof-dynamic-view before objects packages))))
  :hints (("Goal"
           :use (generated-static-header-outside-stack-write
                 (:instance generated-published-view-unchanged-outside-written-span
                            (base (proof-heap-base before))
                            (word (proof-dynamic-root (proof-heap-base before) (proof-world-machine before)))
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (enable generated-stack-update-p proof-dynamic-view)))
  :rule-classes nil)

(defthm generated-stack-update-preserves-heap
  (implies (and (proof-heap-p before objects packages)
                (generated-stack-update-p start end before after)
                (proof-object-disjoint-p start end objects (proof-world-machine before))
                (proof-stack-prefix (proof-stack-top after) after objects packages))
           (proof-heap-p after objects packages))
  :hints (("Goal"
           :expand ((proof-heap-p before objects packages) (proof-heap-p after objects packages))
           :use (generated-stack-update-preserves-heap-layout
                 generated-stack-update-preserves-runtime-fields
                 generated-stack-update-preserves-static-data
                 generated-stack-update-preserves-dynamic-view
                 (:instance generated-object-map-outside-written-span
                            (base (proof-heap-base before))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance generated-object-observations-outside-written-span
                            (pending objects) (base (proof-heap-base before))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance generated-external-mappings-outside-written-span
                            (head (proof-external-head before)) (fuel (len objects)))
                 (:instance generated-stack-update-preserves-object-spans
                            (pending objects)
                            (external (cdr (proof-external-objects (proof-external-head before)
                                                                    (len objects) before objects))))
                 (:instance generated-stack-update-preserves-accounting
                            (headers (cdr (proof-external-objects (proof-external-head before)
                                                                   (len objects) before objects))))
                 (:instance generated-object-observations-preserve-dynamic-symbols
                            (pending objects) (base (proof-heap-base before))
                            (entries (cdr (proof-dynamic-entries (proof-dynamic-view before objects packages) packages)))
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (enable generated-stack-update-p)))
  :rule-classes nil)
