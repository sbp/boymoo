(in-package "BOYMOO-PROOFS")

(include-book "view-memory")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-prefix-length (top world)
  (ash (- top (proof-stack-base world)) -3))

(local
 (defthm sequence-root-prefix-base-is-natural
   (natp (proof-stack-base world))
   :rule-classes :type-prescription))

(defthm sequence-root-view-in-preserved-prefix
  (let* ((base (proof-heap-base before))
         (lower (proof-stack-base before))
         (count (sequence-prefix-length top before))
         (slot (+ lower (* 8 index))))
    (implies (and (proof-prefix-preserved-p top before after old-objects new-objects packages)
                  (equal (proof-stack-base after) lower)
                  (equal (proof-heap-base after) base)
                  (natp index) (< index count)
                  (proof-machine-value-p (proof-load-word slot (proof-world-machine before))
                                         datum before old-objects packages))
             (proof-machine-value-p (proof-load-word slot (proof-world-machine after))
                                    datum after new-objects packages)))
  :hints
  (("Goal"
    :in-theory (disable proof-stack-views proof-view proof-stack-base proof-stack-top proof-heap-base
                        proof-load-word proof-world-machine)
    :use ((:instance sequence-selected-root-view-preserved
                     (count (sequence-prefix-length top before))))))
  :rule-classes nil)

(defthm sequence-runtime-return-preserves-root-slot
  (let* ((top (proof-stack-top before))
         (slot (+ (proof-stack-base before) (* 8 index))))
    (implies (and (proof-runtime-return-p routine args program before after
                                          old-objects new-objects packages)
                  (natp index) (< index (sequence-prefix-length top before))
                  (proof-machine-value-p (proof-load-word slot (proof-world-machine before))
                                         datum before old-objects packages))
             (proof-machine-value-p (proof-load-word slot (proof-world-machine after))
                                    datum after new-objects packages)))
  :hints
  (("Goal"
    :in-theory (disable proof-view proof-load-word proof-stack-prefix proof-prefix-preserved-p
                        proof-heap-p proof-fixed-heap-p proof-frame-return-p proof-runtime-value
                        proof-memory-span-agrees-p proof-dynamic-table-preserved-p
                        proof-machine-value-p proof-stack-base proof-stack-top proof-heap-base
                        proof-reg-value-p proof-world-machine sequence-prefix-length)
    :use ((:instance sequence-root-view-in-preserved-prefix (top (proof-stack-top before))))))
  :rule-classes nil)
