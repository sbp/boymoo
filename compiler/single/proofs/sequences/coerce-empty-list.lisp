(in-package "BOYMOO-PROOFS")

(include-book "coerce-type")
(include-book "readonly-runtime")
(include-book "register-only")

(logic)
(set-verify-guards-eagerness 0)

(sequence-defpath *sequence-coerce-empty-list-finish*
  ("prim:COMMON-LISP::COERCE" 26 1)
  ("rt:coerce-no-list" 0 2)
  ("rt:nil" 0 2))

(defun sequence-coerce-dispatched (before)
  (sequence-execute (sequence-coerce-dispatch-path before) before))

(defun sequence-coerce-empty-list-path (before)
  (let ((dispatched (sequence-coerce-dispatched before)))
    (append (sequence-coerce-dispatch-path before)
            (sequence-readonly-view-prefix 'coerce dispatched)
            *sequence-coerce-empty-list-finish*)))

(local
 (defthm sequence-coerce-dispatch-does-not-change-saves
   (let* ((after (sequence-coerce-dispatched before))
          (first (proof-world-machine before))
          (last (proof-world-machine after)))
     (implies
      (and (proof-register-frame-p 30 '(1 2 3) before after)
           (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp first))
           (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory first))
           (equal (cdr after) (cdr before)))
      (and (sequence-register-only-change-p before after)
           (proof-register-frame-p 28 '(0 1 2 3) before after)
           (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
           (equal (proof-world-reg 29 after) (proof-world-reg 29 before))
           (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
           (equal (proof-heap-base after) (proof-heap-base before))
           (equal (sequence-caller-save-memory after) (sequence-caller-save-memory before)))))
   :hints
   (("Goal"
     :in-theory (e/d (sequence-register-only-change-p sequence-caller-save-memory
                      sequence-heap-registers-agree-p)
                     (sequence-coerce-dispatched proof-world-reg proof-register-frame-p))
     :use ((:instance sequence-frame-keeps-heap-registers
                      (clobbers '(1 2 3)) (after (sequence-coerce-dispatched before)))
           (:instance sequence-register-frame-on-prefix
                      (limit 30) (prefix 28) (clobbers '(1 2 3)) (after (sequence-coerce-dispatched before)))
           (:instance sequence-register-frame-with-more-clobbers
                      (limit 28) (old '(1 2 3)) (new '(0 1 2 3)) (after (sequence-coerce-dispatched before)))
           (:instance sequence-register-in-frame
                      (limit 30) (clobbers '(1 2 3)) (register 0) (after (sequence-coerce-dispatched before)))
           (:instance sequence-register-in-frame
                      (limit 30) (clobbers '(1 2 3)) (register 29) (after (sequence-coerce-dispatched before)))
           (:instance sequence-register-in-frame
                      (limit 30) (clobbers '(1 2 3)) (register 30) (after (sequence-coerce-dispatched before))))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-list-argument-after-dispatch
   (let* ((machine (proof-world-machine before))
          (base (proof-heap-base before))
          (after (sequence-coerce-dispatched before))
          (cuts (list (+ image-base *sequence-coerce-list-offset*))))
     (implies
      (and (proof-heap-p before objects packages)
           (proof-reg-value-p 0 datum before objects packages)
           (proof-reg-value-p 1 'list before objects packages)
           (consp (boymoo-model::a64-registers machine))
           (natp image-base)
           (equal (proof-world-pc before) (+ image-base *sequence-coerce-offset*))
           (unsigned-byte-p 64 (+ image-base *sequence-coerce-string-offset*))
           (unsigned-byte-p 64 (+ base 48))
           (sequence-instruction-path (sequence-coerce-dispatch-path before) cuts before))
      (and (proof-heap-p after objects packages)
           (proof-reg-value-p 0 datum after objects packages)
           (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
           (equal (proof-world-reg 29 after) (proof-world-reg 29 before))
           (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
           (equal (proof-heap-base after) base)
           (equal (sequence-caller-save-memory after) (sequence-caller-save-memory before))
           (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
           (equal (cdr after) (cdr before))
           (proof-register-frame-p 28 '(0 1 2 3) before after))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-machine-value-p)
                     (proof-world-machine proof-world-reg proof-heap-base proof-world-pc
                      proof-register-frame-p proof-heap-p proof-value-p proof-view
                      proof-fixed-heap-p proof-preserved-heap-p proof-segment-p sequence-execute
                      sequence-caller-save-memory sequence-register-only-change-p
                      sequence-coerce-dispatch-path sequence-instruction-path))
     :use ((:instance sequence-coerce-dispatch-for-represented-type (result-type 'list))
           sequence-coerce-dispatch-does-not-change-saves
           (:instance sequence-register-only-change-keeps-heap (after (sequence-coerce-dispatched before)))
           (:instance sequence-representation-on-identical-memory
                      (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                      (first (proof-world-machine before))
                      (last (proof-world-machine (sequence-coerce-dispatched before)))))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-empty-list-finish-effects
   (let* ((machine (proof-world-machine before))
          (stack (boymoo-model::a64-sp machine))
          (after (sequence-execute *sequence-coerce-empty-list-finish* before))
          (last (proof-world-machine after)))
     (implies
      (and (consp (boymoo-model::a64-registers machine))
           (equal (proof-world-reg 2 before) 0)
           (unsigned-byte-p 64 (+ stack 16)))
      (and (equal (proof-world-reg 0 after) *proof-nil*)
           (equal (proof-world-reg 29 after) (proof-load-word stack machine))
           (equal (proof-world-reg 30 after) (proof-load-word (+ stack 8) machine))
           (equal (proof-world-pc after) (proof-load-word (+ stack 8) machine))
           (equal (cdr after) (cdr before))
           (equal (proof-world-stop after) (proof-world-stop before))
           (equal (boymoo-model::a64-sp last) (+ stack 16))
           (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory machine))
           (proof-register-frame-p 28 '(0 1 2 3) before after))))
   :hints (("Goal" :in-theory (e/d (sequence-execute proof-world-machine proof-load-word)
                                   (proof-instruction-effect))
            :expand ((:free (limit clobbers first last)
                            (proof-register-frame-p limit clobbers first last)))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-empty-list-value
   (implies (or (not (stringp datum)) (equal (len (coerce datum 'list)) 0))
            (equal (proof-runtime-value 'coerce (list datum 'list) program)
                   (boymoo-model::core-value nil)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-runtime-value)
                     (sequence-core-coerce boymoo-model::core-primitive boymoo-model::core-prelude))
     :use ((:instance sequence-core-coerce (result-type 'list)))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-empty-list-from-dispatch
   (let* ((returned (sequence-readonly-view-return 'coerce before))
          (machine (proof-world-machine before))
          (address (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before)))
          (after (sequence-execute *sequence-coerce-empty-list-finish* returned)))
     (implies
      (and (proof-heap-p before objects packages)
           (proof-reg-value-p 0 datum before objects packages)
           (sequence-readonly-view-checked-p 'coerce before image-base)
           (implies (stringp datum) (unsigned-byte-p 64 (+ address 8)))
           (or (not (stringp datum)) (equal (len (coerce datum 'list)) 0)))
      (and (equal (proof-world-reg 0 after) *proof-nil*)
           (equal (proof-world-reg 29 after) (proof-world-reg 29 before))
           (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
           (equal (proof-world-pc after) (proof-world-reg 30 before))
           (not (proof-world-stop after))
           (equal (cdr after) (cdr before))
           (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
           (equal (boymoo-model::a64-memory (proof-world-machine after)) (sequence-caller-save-memory before))
           (proof-register-frame-p 28 '(0 1 2 3) before after))))
   :hints
   (("Goal"
     :in-theory (disable proof-stack-prefix proof-heap-p proof-reg-value-p proof-view
                         proof-world-stop proof-world-reg proof-world-pc proof-pointer-address
                         proof-world-machine proof-register-frame-p proof-load-word proof-heap-base
                         sequence-stack-write-p sequence-readonly-view-checked-p sequence-caller-save-memory)
     :use ((:instance sequence-readonly-view-return-is-ready (routine 'coerce))
           (:instance sequence-coerce-empty-list-finish-effects (before (sequence-readonly-view-return 'coerce before)))
           (:instance sequence-register-frame-transitive
                      (limit 28) (clobbers '(0 1 2 3))
                      (middle (sequence-readonly-view-return 'coerce before))
                      (after (sequence-execute *sequence-coerce-empty-list-finish*
                                               (sequence-readonly-view-return 'coerce before)))))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-empty-list-path-result
   (equal (sequence-execute (sequence-coerce-empty-list-path before) before)
          (sequence-execute *sequence-coerce-empty-list-finish*
                            (sequence-readonly-view-return 'coerce (sequence-coerce-dispatched before))))
   :hints
   (("Goal"
     :in-theory (disable sequence-execute sequence-coerce-dispatched
                         sequence-readonly-view-prefix sequence-readonly-view-return
                         sequence-coerce-dispatch-path acl2::binary-append sequence-execute-append)
     :use ((:instance sequence-execute-append (world before)
                      (first (sequence-coerce-dispatch-path before))
                      (second (append (sequence-readonly-view-prefix 'coerce (sequence-coerce-dispatched before))
                                      *sequence-coerce-empty-list-finish*)))
           (:instance sequence-readonly-execution-after-prefix
                      (routine 'coerce) (before (sequence-coerce-dispatched before))
                      (suffix *sequence-coerce-empty-list-finish*)))
     :expand ((sequence-coerce-dispatched before))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-empty-list-full-frame
   (let* ((machine (proof-world-machine before))
          (base (proof-heap-base before))
          (dispatched (sequence-coerce-dispatched before))
          (address (proof-pointer-address (proof-world-reg 0 before) base))
          (path (sequence-coerce-empty-list-path before))
          (after (sequence-execute path before)))
     (implies
      (and (proof-heap-p before objects packages)
           (proof-reg-value-p 0 datum before objects packages)
           (proof-reg-value-p 1 'list before objects packages)
           (consp (boymoo-model::a64-registers machine))
           (natp image-base)
           (equal (proof-world-pc before) (+ image-base *sequence-coerce-offset*))
           (unsigned-byte-p 64 (+ image-base *sequence-coerce-string-offset*))
           (unsigned-byte-p 64 (+ base 48))
           (implies (stringp datum) (unsigned-byte-p 64 (+ address 8)))
           (or (not (stringp datum)) (equal (len (coerce datum 'list)) 0))
           (sequence-instruction-path (sequence-coerce-dispatch-path before)
                                      (list (+ image-base *sequence-coerce-list-offset*)) before)
           (sequence-readonly-view-checked-p 'coerce dispatched image-base)
           (sequence-caller-stack-room-p before))
      (and (not (proof-world-stop after))
           (equal (proof-world-pc after) (proof-world-reg 30 before))
           (equal (proof-world-reg 0 after) *proof-nil*)
           (proof-frame-return-p (proof-runtime-clobbers 'coerce) t before after)
           (proof-fixed-heap-p before after objects)
           (proof-preserved-heap-p nil before after objects objects packages))))
   :hints
   (("Goal"
     :in-theory (disable proof-heap-p proof-reg-value-p proof-view proof-pointer-address
                         proof-register-frame-p proof-frame-return-p proof-fixed-heap-p
                         proof-preserved-heap-p proof-world-machine proof-world-reg proof-world-pc
                         proof-world-stop proof-heap-base sequence-execute sequence-coerce-empty-list-path
                         sequence-coerce-dispatch-path sequence-coerce-dispatched
                         sequence-instruction-path sequence-readonly-view-checked-p)
     :use (sequence-coerce-list-argument-after-dispatch sequence-coerce-empty-list-path-result
           (:instance sequence-coerce-empty-list-from-dispatch (before (sequence-coerce-dispatched before)))
           (:instance sequence-register-frame-transitive
                      (limit 28) (clobbers '(0 1 2 3))
                      (middle (sequence-coerce-dispatched before))
                      (after (sequence-execute (sequence-coerce-empty-list-path before) before)))
           (:instance sequence-readonly-restored-runtime-frame
                      (routine 'coerce) (after (sequence-execute (sequence-coerce-empty-list-path before) before))))))
   :rule-classes nil))

(defthm sequence-coerce-empty-list-runtime-contract
  (let* ((machine (proof-world-machine before))
         (base (proof-heap-base before))
         (address (proof-pointer-address (proof-world-reg 0 before) base))
         (path (sequence-coerce-empty-list-path before))
         (cuts (list (proof-world-reg 30 before)))
         (after (sequence-execute path before)))
    (implies
     (and (proof-runtime-pre-p 'coerce (list datum 'list) program labels image-base before objects packages)
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-coerce-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-coerce-string-offset*))
          (unsigned-byte-p 64 (+ base 48))
          (implies (stringp datum) (unsigned-byte-p 64 (+ address 8)))
          (or (not (stringp datum)) (equal (len (coerce datum 'list)) 0))
          (sequence-instruction-path (sequence-coerce-dispatch-path before)
                                     (list (+ image-base *sequence-coerce-list-offset*)) before)
          (sequence-readonly-view-checked-p 'coerce (sequence-coerce-dispatched before) image-base)
          (sequence-caller-stack-room-p before)
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-runtime-return-p 'coerce (list datum 'list) program before after objects objects packages)
          (proof-fixed-heap-p before after objects))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-runtime-pre-p proof-runtime-return-p proof-datum-return-p
                     proof-preserved-heap-p proof-reg-value-p)
                    (proof-machine-value-p proof-heap-p proof-view proof-frame-return-p
                     proof-runtime-value proof-register-frame-p proof-fixed-heap-p proof-heap-frame-p
                     proof-prefix-preserved-p proof-dynamic-table-preserved-p proof-program-packages-p
                     proof-segment-p proof-instruction-at-p proof-instruction-access-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop proof-heap-base
                     proof-pointer-address sequence-coerce-empty-list-path sequence-coerce-dispatch-path
                     sequence-coerce-dispatched sequence-instruction-path sequence-execute
                     sequence-readonly-view-checked-p sequence-caller-stack-room-p))
    :use (sequence-coerce-empty-list-full-frame sequence-coerce-empty-list-value
          (:instance sequence-static-truth-values-in-heap
                     (world (sequence-execute (sequence-coerce-empty-list-path before) before)))
          (:instance sequence-segment-of-instruction-path
                     (instructions (sequence-coerce-empty-list-path before))
                     (cuts (list (proof-world-reg 30 before)))
                     (after (sequence-execute (sequence-coerce-empty-list-path before) before))))))
  :rule-classes nil)
