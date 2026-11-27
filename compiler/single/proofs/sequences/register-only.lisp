(in-package "BOYMOO-PROOFS")

(include-book "readonly-call")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-memory-entries-agree-with-themselves
   (proof-byte-entries-agree-p entries start end memory memory)
   :hints (("Goal" :in-theory (enable proof-byte-entries-agree-p)
                   :induct (len entries)))))

(defthm sequence-identical-memory-agrees-on-span
  (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
           (sequence-machine-span-agrees-p start end first last))
  :hints (("Goal" :in-theory (enable sequence-machine-span-agrees-p))))

(defun sequence-register-only-change-p (before after)
  (let ((first (proof-world-machine before))
        (last (proof-world-machine after)))
    (and (sequence-heap-registers-agree-p before after)
         (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp first))
         (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory first))
         (equal (cdr before) (cdr after)))))

(local
 (defthm sequence-stack-pointer-is-aligned
   (implies (proof-heap-layout-p before)
            (equal (mod (boymoo-model::a64-sp (proof-world-machine before)) 16) 0))
   :hints (("Goal" :expand ((proof-heap-layout-p before))))
   :rule-classes nil))

(defthm sequence-register-only-change-keeps-heap
  (implies (and (proof-heap-p before objects packages)
                (sequence-register-only-change-p before after))
           (and (proof-heap-p after objects packages)
                (proof-fixed-heap-p before after objects)
                (proof-preserved-heap-p nil before after objects objects packages)))
  :hints
  (("Goal"
    :in-theory (enable sequence-stack-write-p sequence-machine-write-confined-p)
    :use (sequence-stack-pointer-is-aligned
          (:instance sequence-heap-layout-bounds (world before))
          (:instance sequence-stack-write-keeps-heap-invariant
                     (start (boymoo-model::a64-sp (proof-world-machine before)))
                     (end (boymoo-model::a64-sp (proof-world-machine before))))
          (:instance sequence-confined-stack-write-preserves-heap
                     (start (boymoo-model::a64-sp (proof-world-machine before)))
                     (end (boymoo-model::a64-sp (proof-world-machine before)))))))
  :rule-classes nil)

(defthm sequence-representation-on-identical-memory
  (implies (and (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
                (proof-value-p word datum base objects packages first))
           (proof-value-p word datum base objects packages last))
  :hints (("Goal"
           :in-theory (e/d (proof-value-p) (proof-view))
           :use sequence-view-of-equal-memory))
  :rule-classes nil)
