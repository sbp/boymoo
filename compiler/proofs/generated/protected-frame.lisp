(in-package "BOYMOO-PROOFS")

(include-book "stack-write")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-layout-p proof-heap-frame-p proof-byte-entries-agree-p proof-memory-span-agrees-p
                    proof-streams-preserved-p proof-stack-base proof-stack-end proof-spaces-end proof-heap-base
                    proof-world-machine proof-machine-limit proof-subspan-p proof-span-p proof-disjoint-p
                    generated-sp generated-memory-outside-p boymoo-model::a64-memory boymoo-model::a64-byte expt))

(local
 (defthm generated-byte-noninteger-address-is-zero-address
   (implies (not (integerp address))
            (equal (boymoo-model::a64-byte address bytes) (boymoo-model::a64-byte 0 bytes)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-byte boymoo-model::a64-unsigned)))))

(local
 (defthm generated-present-bytes-agree-in-disjoint-span
   (implies (and (generated-memory-outside-p written-start written-end before after)
                 (posp written-start) (natp start) (natp end) (<= end (expt 2 64))
                 (proof-disjoint-p start end written-start written-end))
            (proof-byte-entries-agree-p entries start end (boymoo-model::a64-memory before) (boymoo-model::a64-memory after)))
   :hints (("Goal" :induct (len entries) :in-theory (enable proof-byte-entries-agree-p proof-disjoint-p))
           ("Subgoal *1/1"
            :use ((:instance generated-byte-outside-written-span (address (caar entries))
                             (start written-start) (end written-end))
                  (:instance generated-byte-outside-written-span (address 0)
                             (start written-start) (end written-end)))))
   :rule-classes nil))

(defthm generated-memory-outside-positive-write-agrees-on-protected-span
  (implies (and (generated-memory-outside-p written-start written-end (proof-world-machine before) (proof-world-machine after))
                (posp written-start) (natp start) (natp end) (<= end (expt 2 64))
                (proof-disjoint-p start end written-start written-end))
           (proof-memory-span-agrees-p start end before after))
  :hints (("Goal"
           :use ((:instance generated-present-bytes-agree-in-disjoint-span
                            (entries (boymoo-model::a64-memory (proof-world-machine before)))
                            (before (proof-world-machine before)) (after (proof-world-machine after)))
                 (:instance generated-present-bytes-agree-in-disjoint-span
                            (entries (boymoo-model::a64-memory (proof-world-machine after)))
                            (before (proof-world-machine before)) (after (proof-world-machine after))))
           :in-theory (enable proof-memory-span-agrees-p)))
  :rule-classes nil)

(local
 (defthm generated-protected-static-span-minimum-size
   (implies (proof-heap-layout-p world)
            (<= 80 (proof-static-size (proof-heap-base world) (proof-world-machine world))))
   :hints (("Goal" :expand (proof-heap-layout-p world)))
   :rule-classes nil))

(local
 (defthm generated-stack-write-spares-protected-static-spans
   (let* ((base (proof-heap-base before)) (static-end (+ base (proof-static-size base (proof-world-machine before)))))
     (implies (and (proof-heap-layout-p before) (generated-stack-update-p start end before after) (posp start))
              (and (proof-memory-span-agrees-p base (+ base 24) before after)
                   (proof-memory-span-agrees-p (+ base 32) static-end before after))))
   :hints (("Goal"
            :use (generated-stack-write-disjoint-from-main-heap
                  (:instance generated-protected-static-span-minimum-size (world before))
                  (:instance generated-memory-outside-positive-write-agrees-on-protected-span
                             (written-start start) (written-end end) (start (proof-heap-base before))
                             (end (+ 24 (proof-heap-base before))))
                  (:instance generated-memory-outside-positive-write-agrees-on-protected-span
                             (written-start start) (written-end end) (start (+ 32 (proof-heap-base before)))
                             (end (+ (proof-heap-base before) (proof-static-size (proof-heap-base before) (proof-world-machine before))))))
            :in-theory (enable generated-stack-update-p proof-disjoint-p proof-span-p)))
   :rule-classes nil))

(defthm generated-stack-update-preserves-protected-heap-frame
  (let ((sp (generated-sp before)) (upper (generated-machine-stack-end before)))
    (implies (and (proof-heap-layout-p before) (generated-stack-update-p start end before after)
                  (posp start) (proof-disjoint-p sp upper start end)
                  (proof-streams-preserved-p before after))
             (proof-heap-frame-p before after)))
  :hints (("Goal"
           :use (generated-stack-write-spares-protected-static-spans generated-stack-update-preserves-runtime-fields
                 (:instance generated-heap-layout-machine-stack-bounds (world before))
                 (:instance generated-memory-outside-positive-write-agrees-on-protected-span
                            (written-start start) (written-end end) (start (generated-sp before))
                            (end (generated-machine-stack-end before))))
           :in-theory (enable proof-heap-frame-p generated-stack-update-p proof-span-p
                              generated-machine-stack-end generated-machine-stack-base generated-heap-machine-sp)))
  :rule-classes nil)

(defthm generated-value-stack-update-preserves-protected-heap-frame
  (implies (and (proof-heap-layout-p before) (generated-stack-update-p start end before after)
                (proof-subspan-p start (- end start) (proof-stack-base before) (proof-stack-end before))
                (posp start) (proof-streams-preserved-p before after))
           (proof-heap-frame-p before after))
  :hints (("Goal" :use generated-stack-update-preserves-protected-heap-frame
                  :in-theory (enable proof-heap-layout-p proof-disjoint-p proof-subspan-p
                                     generated-machine-stack-base generated-machine-stack-end generated-heap-machine-sp)))
  :rule-classes nil)
