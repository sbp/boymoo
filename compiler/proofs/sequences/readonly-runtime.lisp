(in-package "BOYMOO-PROOFS")

(include-book "readonly-call")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-readonly-address-is-natural
  (natp (proof-pointer-address word base))
  :hints (("Goal" :in-theory (enable proof-pointer-address)))
  :rule-classes :type-prescription)

(defthm sequence-checked-view-call-has-frame-room
  (implies (sequence-readonly-view-checked-p routine before image-base)
           (and (natp image-base)
                (sequence-caller-stack-room-p before)))
  :rule-classes ((:forward-chaining
                  :trigger-terms ((sequence-readonly-view-checked-p routine before image-base)))))

(defun sequence-readonly-view-prefix (routine before)
  (append (sequence-view-call-path routine)
          (sequence-readonly-view-path routine before)))

(defthm sequence-readonly-view-prefix-return
  (equal (sequence-execute (sequence-readonly-view-prefix routine before) before)
         (sequence-readonly-view-return routine before)))

(defthm sequence-readonly-execution-after-prefix
  (equal (sequence-execute (append (sequence-readonly-view-prefix routine before) suffix) before)
         (sequence-execute suffix (sequence-readonly-view-return routine before))))

(local
 (defthm sequence-checked-path-after-prefix
   (implies (sequence-instruction-path (append prefix suffix) cuts before)
            (sequence-instruction-path suffix cuts (sequence-execute prefix before)))
   :hints
   (("Goal" :in-theory (enable sequence-instruction-path sequence-execute)
            :induct (sequence-instruction-path prefix cuts before)))))

(defthm sequence-readonly-checked-suffix
  (implies (sequence-instruction-path (append (sequence-readonly-view-prefix routine before) suffix)
                                      cuts before)
           (sequence-instruction-path suffix cuts (sequence-readonly-view-return routine before)))
  :hints
  (("Goal"
    :in-theory (disable sequence-checked-path-after-prefix sequence-readonly-view-prefix
                        sequence-readonly-view-return acl2::binary-append)
    :use ((:instance sequence-checked-path-after-prefix
                     (prefix (sequence-readonly-view-prefix routine before))))))
  :rule-classes nil)

(defthm sequence-readonly-restored-runtime-frame
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (sp (boymoo-model::a64-sp first))
         (clobbers (sequence-readonly-clobbers routine)))
    (implies (and (member-eq routine '(length char coerce))
                  (proof-heap-p before objects packages)
                  (sequence-caller-stack-room-p before)
                  (not (proof-world-stop after))
                  (equal (proof-world-pc after) (proof-world-reg 30 before))
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 before))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
                  (equal (boymoo-model::a64-sp last) sp)
                  (equal (boymoo-model::a64-memory last) (sequence-caller-save-memory before))
                  (equal (cdr after) (cdr before))
                  (proof-register-frame-p 28 clobbers before after))
             (and (proof-frame-return-p (proof-runtime-clobbers routine) t before after)
                  (proof-fixed-heap-p before after objects)
                  (proof-preserved-heap-p nil before after objects objects packages))))
  :hints
  (("Goal"
    :in-theory (disable proof-register-frame-p proof-world-stop sequence-caller-stack-room-p
                        sequence-caller-save-memory proof-runtime-clobbers)
    :expand ((proof-runtime-clobbers routine))
    :use ((:instance sequence-heap-layout-bounds (world before))
          (:instance sequence-frame-keeps-heap-registers
                     (clobbers (sequence-readonly-clobbers routine)))
          (:instance sequence-frame-restored-registers
                     (clobbers (sequence-readonly-clobbers routine)))
          (:instance sequence-register-frame-with-more-clobbers
                     (limit 30) (old (sequence-readonly-clobbers routine))
                     (new (proof-runtime-clobbers routine)))
          sequence-stack-write-from-caller-saves
          (:instance sequence-confined-stack-write-preserves-heap
                     (start (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                     (end (boymoo-model::a64-sp (proof-world-machine before)))))))
  :rule-classes nil)

(defthm sequence-readonly-runtime-result
  (implies (member-eq routine '(length char))
           (equal (proof-runtime-value routine args program)
                  (boymoo-model::core-prelude routine args)))
  :hints (("Goal" :in-theory (e/d (boymoo-model::core-primitive)
                                   (boymoo-model::core-prelude proof-runtime-entry)))))

(local
 (defthm sequence-result-value-view
   (implies (boymoo-model::core-value-p result)
            (equal (proof-value-view (boymoo-model::core-datum result)) result))
   :hints (("Goal" :cases ((consp result))))))

(defthm sequence-readonly-datum-contract
  (let ((result (boymoo-model::core-prelude routine args)))
    (implies (and (member-eq routine '(length char))
                  (proof-frame-return-p (proof-runtime-clobbers routine) t before after)
                  (proof-fixed-heap-p before after objects)
                  (proof-preserved-heap-p nil before after objects objects packages)
                  (boymoo-model::core-value-p result)
                  (equal (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                                     objects packages (proof-world-machine after))
                         result))
             (proof-runtime-return-p routine args program before after objects objects packages)))
  :hints
  (("Goal"
    :in-theory (enable proof-runtime-return-p proof-datum-return-p proof-value-p
                       proof-machine-value-p proof-reg-value-p)
    :use ((:instance sequence-result-value-view (result (boymoo-model::core-prelude routine args))))
    :do-not-induct t))
  :rule-classes nil)

(in-theory (disable sequence-readonly-view-prefix sequence-readonly-view-link
                    sequence-readonly-view-entry sequence-readonly-view-path
                    sequence-readonly-view-return sequence-readonly-view-checked-p
                    sequence-caller-stack-room-p sequence-caller-save-memory))
