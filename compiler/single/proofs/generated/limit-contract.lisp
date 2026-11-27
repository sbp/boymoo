(in-package "BOYMOO-PROOFS")

(include-book "runtime-flow")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-layout-p proof-heap-p proof-world-machine proof-world-reg proof-world-pc
                    proof-world-stop proof-world-regions proof-world-page-size proof-stack-base proof-stack-end
                    proof-heap-base proof-stack-top proof-stack-limit proof-heap-limit proof-box-top
                    proof-runtime-word proof-external-objects proof-heap-object-spans-p proof-string-accounting-p
                    proof-dynamic-view proof-stack-prefix proof-prefix-preserved-p
                    proof-heap-frame-p proof-fixed-heap-p proof-memory-span-agrees-p proof-byte-entries-agree-p
                    proof-fixed-external-p proof-frame-return-p proof-register-frame-p proof-reg-value-p
                    proof-datum-return-p proof-runtime-return-p proof-preserved-heap-p proof-runtime-value
                    proof-dynamic-table-preserved-p proof-world-input proof-world-stdout proof-world-stderr proof-world-replies
                    generated-sp boymoo-model::a64-memory mod expt))

(local
 (defthm generated-changing-limit-keeps-runtime-words
   (equal (proof-runtime-word offset (generated-set-reg 24 limit before))
          (proof-runtime-word offset before))
   :hints (("Goal" :in-theory (enable proof-runtime-word proof-heap-base)))))

(local
 (defun generated-limit-external-chain-induction (head fuel before)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       head
     (generated-limit-external-chain-induction
      (proof-load-word head (proof-world-machine before)) (1- fuel) before))))

(local
 (defthm generated-changing-limit-keeps-external-chain
   (equal (proof-external-objects head fuel (generated-set-reg 24 limit before) objects)
          (proof-external-objects head fuel before objects))
   :hints (("Goal" :induct (generated-limit-external-chain-induction head fuel before)
                   :in-theory (enable proof-heap-base proof-machine-limit proof-stack-base proof-stack-end proof-spaces-end))
           ("Subgoal *1/2" :expand ((proof-external-objects head fuel before objects)
                                    (proof-external-objects head fuel (generated-set-reg 24 limit before) objects)))
           ("Subgoal *1/1" :expand ((proof-external-objects head fuel before objects)
                                    (proof-external-objects head fuel (generated-set-reg 24 limit before) objects))))))

(local
 (defthm generated-changing-limit-keeps-object-spans
   (equal (proof-heap-object-spans-p objects external (generated-set-reg 24 limit before))
          (proof-heap-object-spans-p objects external before))
   :hints (("Goal" :induct (proof-heap-object-spans-p objects external before)
                   :in-theory (enable proof-heap-object-spans-p proof-cons-floor proof-active-floor
                                      proof-active-end proof-box-top)))))

(local
 (defthm generated-changing-limit-keeps-stack-views
   (equal (proof-stack-prefix top (generated-set-reg 24 limit before) objects packages)
          (proof-stack-prefix top before objects packages))
   :hints (("Goal" :in-theory (enable proof-stack-prefix proof-stack-base proof-stack-top proof-heap-base)))))

(local
 (defthm generated-changing-limit-keeps-layout
   (implies (and (proof-heap-layout-p before) (unsigned-byte-p 64 limit)
                 (<= (proof-stack-top before) limit) (<= limit (proof-stack-end before))
                 (equal (mod limit 8) 0))
            (proof-heap-layout-p (generated-set-reg 24 limit before)))
   :hints (("Goal"
            :in-theory (enable proof-heap-layout-p proof-stack-base proof-stack-top proof-stack-limit proof-stack-end
                               proof-machine-limit proof-active-floor proof-cons-floor proof-active-end proof-inactive-floor
                               proof-inactive-end proof-heap-base proof-box-top proof-heap-limit proof-spaces-end
                               proof-static-size generated-heap-machine-sp)))))

(defthm generated-resetting-aligned-value-limit-preserves-heap
  (implies (and (proof-heap-p before objects packages) (unsigned-byte-p 64 limit)
                (<= (proof-stack-top before) limit) (<= limit (proof-stack-end before))
                (equal (mod limit 8) 0))
           (and (proof-heap-p (generated-set-reg 24 limit before) objects packages)
                (equal (proof-stack-limit (generated-set-reg 24 limit before)) limit)))
  :hints (("Goal"
           :in-theory (enable proof-heap-p proof-heap-base proof-stack-limit proof-stack-top proof-external-head
                              proof-string-accounting-p proof-string-bytes-since-collection proof-string-budget
                              proof-dynamic-view proof-dynamic-root)))
  :rule-classes nil)

(local
 (defun generated-limit-frame-induction (register)
   (declare (xargs :measure (nfix register)))
   (if (zp register) register
     (generated-limit-frame-induction (1- register)))))

(local
 (defthm generated-clobbered-limit-does-not-change-register-frame-p
   (implies (member-equal 24 clobbers)
            (equal (proof-register-frame-p register clobbers before (generated-set-reg 24 limit after))
                   (proof-register-frame-p register clobbers before after)))
   :hints (("Goal" :induct (generated-limit-frame-induction register)
                   :in-theory (enable proof-register-frame-p)))))

(local
 (defthm generated-agreeing-memory-span-ignores-limit-update
   (equal (proof-memory-span-agrees-p start end before (generated-set-reg 24 limit after))
          (proof-memory-span-agrees-p start end before after))
   :hints (("Goal" :in-theory (enable proof-memory-span-agrees-p generated-memory-equiv)))))

(local
 (defthm generated-fixed-external-areas-ignore-limit-update
   (equal (proof-fixed-external-p mappings before (generated-set-reg 24 limit after))
          (proof-fixed-external-p mappings before after))
   :hints (("Goal" :induct (proof-fixed-external-p mappings before after)
                   :in-theory (enable proof-fixed-external-p)))))

(local
 (defthm generated-limit-update-does-not-touch-io
   (and (equal (proof-world-input (generated-set-reg 24 limit after)) (proof-world-input after))
        (equal (proof-world-stdout (generated-set-reg 24 limit after)) (proof-world-stdout after))
        (equal (proof-world-stderr (generated-set-reg 24 limit after)) (proof-world-stderr after))
        (equal (proof-world-replies (generated-set-reg 24 limit after)) (proof-world-replies after)))
   :hints (("Goal" :in-theory (enable generated-set-reg generated-set-machine proof-world-input
                                      proof-world-stdout proof-world-stderr proof-world-replies)))))

(defthm generated-equal-return-contract-allows-limit-at-current-top
  (let* ((limit (proof-stack-top after)) (lowered (generated-set-reg 24 limit after)))
    (implies (proof-runtime-return-p 'equal (list x y) program before after old-objects new-objects packages)
             (and (proof-runtime-return-p 'equal (list x y) program before lowered old-objects new-objects packages)
                  (equal (proof-stack-limit lowered) limit))))
  :hints (("Goal"
           :use ((:instance generated-resetting-aligned-value-limit-preserves-heap
                            (before after) (limit (proof-stack-top after)) (objects new-objects))
                 (:instance generated-heap-has-layout-and-roots (world after) (objects new-objects))
                 (:instance generated-heap-layout-value-stack-bounds (world after)))
           :in-theory (enable proof-runtime-return-p proof-runtime-clobbers proof-datum-return-p
                              proof-preserved-heap-p proof-heap-frame-p proof-frame-return-p proof-fixed-heap-p
                              proof-dynamic-table-preserved-p proof-prefix-preserved-p proof-reg-value-p
                              generated-heap-machine-sp proof-machine-value-p proof-value-p proof-dynamic-view
                              proof-dynamic-root proof-heap-base proof-stack-top
                              proof-stack-base proof-stack-end proof-spaces-end proof-heap-limit proof-box-top
                              proof-streams-preserved-p)))
  :rule-classes nil)
