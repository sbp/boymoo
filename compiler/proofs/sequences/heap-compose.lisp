(in-package "BOYMOO-PROOFS")

(include-book "register-only")
(include-book "span-composition")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-heap-frame-metadata-word
   (let* ((base (proof-heap-base before))
          (first (proof-world-machine before))
          (last (proof-world-machine after)))
     (implies (and (proof-heap-layout-p before)
                   (proof-heap-frame-p before after))
              (and (equal (proof-static-size base last) (proof-static-size base first))
                   (natp base) (natp (proof-static-size base first))
                   (natp (sequence-machine-stack-end before)))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-heap-frame-p proof-static-size proof-load-word
                      proof-span-p proof-subspan-p)
                     (proof-world-machine proof-heap-layout-p proof-world-reg proof-heap-base
                      proof-streams-preserved-p proof-stack-base proof-stack-end proof-spaces-end
                      sequence-machine-span-agrees-p proof-disjoint-p))
     :use ((:instance sequence-heap-layout-bounds (world before))
           (:instance sequence-read-in-agreed-machine-span
                      (first (proof-world-machine before)) (last (proof-world-machine after))
                      (start (proof-heap-base before)) (end (+ 24 (proof-heap-base before)))
                      (address (proof-heap-base before)) (count 8)))))
   :rule-classes nil))

(local
 (defthm sequence-machine-frame-spans-compose
   (let* ((first (proof-world-machine before))
          (moved (proof-world-machine middle))
          (last (proof-world-machine after))
          (sp (boymoo-model::a64-sp first))
          (inner-sp (boymoo-model::a64-sp moved))
          (end (sequence-machine-stack-end before)))
     (implies
      (and (natp end) (<= inner-sp sp)
           (sequence-memory-addresses-p (boymoo-model::a64-memory first))
           (sequence-memory-addresses-p (boymoo-model::a64-memory last))
           (sequence-machine-span-agrees-p sp end first moved)
           (sequence-machine-span-agrees-p inner-sp end moved last))
      (sequence-machine-span-agrees-p sp end first last)))
   :hints
   (("Goal"
     :in-theory (disable sequence-machine-span-agrees-p sequence-machine-stack-end
                         proof-world-machine sequence-memory-addresses-p)
     :use ((:instance sequence-machine-agreement-on-subinterval
                      (first (proof-world-machine middle)) (last (proof-world-machine after))
                      (lower (boymoo-model::a64-sp (proof-world-machine middle)))
                      (upper (sequence-machine-stack-end before))
                      (start (boymoo-model::a64-sp (proof-world-machine before)))
                      (end (sequence-machine-stack-end before)))
           (:instance sequence-word-addressed-span-agreement-composes
                      (first (proof-world-machine before)) (middle (proof-world-machine middle))
                      (last (proof-world-machine after))
                      (start (boymoo-model::a64-sp (proof-world-machine before)))
                      (end (sequence-machine-stack-end before))))))
   :rule-classes nil))

(defthm sequence-word-addressed-heap-frames-compose
  (let ((first (proof-world-machine before))
        (moved (proof-world-machine middle))
        (last (proof-world-machine after)))
    (implies (and (proof-heap-layout-p before)
                  (proof-heap-frame-p before middle)
                  (proof-heap-frame-p middle after)
                  (equal (proof-machine-limit middle) (proof-machine-limit before))
                  (<= (boymoo-model::a64-sp moved) (boymoo-model::a64-sp first))
                  (sequence-memory-addresses-p (boymoo-model::a64-memory first))
                  (sequence-memory-addresses-p (boymoo-model::a64-memory last)))
             (proof-heap-frame-p before after)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-heap-frame-p proof-streams-preserved-p sequence-machine-stack-end
                     sequence-machine-stack-base)
                    (proof-heap-layout-p proof-world-reg proof-heap-base proof-world-machine
                     proof-stack-base proof-stack-end proof-spaces-end proof-machine-limit
                     proof-static-size sequence-machine-span-agrees-p sequence-memory-addresses-p))
    :use (sequence-machine-frame-spans-compose
          (:instance sequence-heap-frame-metadata-word (after middle))
          (:instance sequence-word-addressed-span-agreement-composes
                     (first (proof-world-machine before)) (middle (proof-world-machine middle))
                     (last (proof-world-machine after))
                     (start (proof-heap-base before)) (end (+ 24 (proof-heap-base before))))
          (:instance sequence-word-addressed-span-agreement-composes
                     (first (proof-world-machine before)) (middle (proof-world-machine middle))
                     (last (proof-world-machine after))
                     (start (+ 32 (proof-heap-base before)))
                     (end (+ (proof-heap-base before)
                             (proof-static-size (proof-heap-base before) (proof-world-machine before))))))))
  :rule-classes nil)

(defthm sequence-word-addressed-preserved-heaps-compose
  (let ((first (proof-world-machine before))
        (moved (proof-world-machine middle))
        (last (proof-world-machine after)))
    (implies (and (proof-heap-layout-p before)
                  (proof-preserved-heap-p nil before middle old-objects middle-objects packages)
                  (proof-preserved-heap-p nil middle after middle-objects new-objects packages)
                  (equal (proof-stack-top middle) (proof-stack-top before))
                  (equal (proof-machine-limit middle) (proof-machine-limit before))
                  (<= (boymoo-model::a64-sp moved) (boymoo-model::a64-sp first))
                  (sequence-memory-addresses-p (boymoo-model::a64-memory first))
                  (sequence-memory-addresses-p (boymoo-model::a64-memory last)))
             (proof-preserved-heap-p nil before after old-objects new-objects packages)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-preserved-heap-p proof-prefix-preserved-p proof-dynamic-table-preserved-p)
                    (proof-heap-layout-p proof-heap-p proof-heap-frame-p proof-world-machine proof-world-reg
                     proof-stack-prefix proof-stack-top proof-machine-limit
                     proof-dynamic-view sequence-memory-addresses-p))
    :use (sequence-word-addressed-heap-frames-compose)))
  :rule-classes nil)
