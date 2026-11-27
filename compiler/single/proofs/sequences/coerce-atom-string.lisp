(in-package "BOYMOO-PROOFS")

(include-book "coerce-type")
(include-book "constructor-entry")
(include-book "register-only")

(logic)
(set-verify-guards-eagerness 0)

(sequence-defpath *sequence-coerce-atom-string-tail*
  ("rt:coerce-to-string" 0 2))

(defun sequence-coerce-atom-string-path (before)
  (append (sequence-coerce-dispatch-path before) *sequence-coerce-atom-string-tail*))

(defthm sequence-coerce-noncons-takes-empty-string-branch
  (let* ((machine (proof-world-machine before))
         (path *sequence-coerce-atom-string-tail*)
         (after (sequence-execute path before)))
    (implies
     (and (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-coerce-string-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-coerce-string-offset* 4))
          (unsigned-byte-p 64 (+ image-base *sequence-empty-string-offset*))
          (not (equal (proof-word-tag (proof-world-reg 0 before)) 0)))
     (and (equal (proof-world-pc after) (+ image-base *sequence-empty-string-offset*))
          (proof-register-frame-p 30 nil before after)
          (equal (cdr after) (cdr before))
          (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
          (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine)))))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-execute proof-world-machine proof-word-tag) (proof-instruction-effect))
    :expand ((:free (limit clobbers first last)
                    (proof-register-frame-p limit clobbers first last)))))
  :rule-classes nil)

(local
 (defthm sequence-coerce-atom-has-noncons-word
   (implies (and (atom datum) (proof-reg-value-p 0 datum world objects packages))
            (not (equal (proof-word-tag (proof-world-reg 0 world)) 0)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-reg-value-p proof-machine-value-p proof-value-p proof-view)
                     (proof-view-step proof-world-machine proof-world-reg proof-heap-base
                      proof-word-tag proof-pointer-address))
     :use ((:instance sequence-word-cons-tag (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                      (machine (proof-world-machine world))
                      (depth (1+ (nfix (proof-object-rank
                                        (assoc-equal (proof-pointer-address
                                                      (proof-world-reg 0 world) (proof-heap-base world))
                                                     objects)))))))))
   :rule-classes nil))

(defthm sequence-coerce-atom-string-call
  (let* ((first (proof-world-machine before))
         (dispatch (sequence-coerce-dispatch-path before))
         (path (sequence-coerce-atom-string-path before))
         (after (sequence-execute path before))
         (last (proof-world-machine after))
         (target (+ image-base *sequence-empty-string-offset*)))
    (implies
     (and (proof-heap-p before objects packages)
          (proof-reg-value-p 0 datum before objects packages) (atom datum)
          (proof-reg-value-p 1 result-type before objects packages) (not (eq result-type 'list))
          (consp (boymoo-model::a64-registers first))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-coerce-offset*))
          (unsigned-byte-p 64 (+ image-base *sequence-coerce-string-offset* 4))
          (unsigned-byte-p 64 (+ (proof-heap-base before) 48))
          (unsigned-byte-p 64 target)
          (sequence-instruction-path dispatch (list (+ image-base *sequence-coerce-string-offset*)) before)
          (sequence-instruction-path path (list target) before))
     (and (proof-segment-p (len path) (list target) before :cut after)
          (equal (proof-world-pc after) target)
          (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
          (not (proof-world-stop after))
          (proof-register-frame-p 30 '(1 2 3) before after)
          (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp first))
          (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory first))
          (equal (cdr after) (cdr before))
          (sequence-register-only-change-p before after))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-world-stop sequence-register-only-change-p)
                    (proof-heap-p proof-reg-value-p proof-segment-p proof-register-frame-p proof-heap-base
                     proof-world-machine proof-world-pc proof-world-reg proof-word-tag sequence-instruction-path
                     sequence-coerce-dispatch-path sequence-execute acl2::binary-append sequence-execute-append))
    :use (sequence-coerce-dispatch-for-represented-type
          (:instance sequence-coerce-atom-has-noncons-word (world before))
          (:instance sequence-heap-layout-bounds (world before))
          (:instance sequence-coerce-noncons-takes-empty-string-branch
                     (before (sequence-execute (sequence-coerce-dispatch-path before) before)))
          (:instance sequence-register-in-frame (limit 30) (clobbers '(1 2 3)) (register 0)
                     (after (sequence-execute (sequence-coerce-dispatch-path before) before)))
          (:instance sequence-execute-append (world before)
                     (first (sequence-coerce-dispatch-path before)) (second *sequence-coerce-atom-string-tail*))
          (:instance sequence-register-frame-with-more-clobbers (limit 30) (old nil) (new '(1 2 3))
                     (before (sequence-execute (sequence-coerce-dispatch-path before) before))
                     (after (sequence-execute (sequence-coerce-atom-string-path before) before)))
          (:instance sequence-register-frame-transitive (limit 30) (clobbers '(1 2 3))
                     (middle (sequence-execute (sequence-coerce-dispatch-path before) before))
                     (after (sequence-execute (sequence-coerce-atom-string-path before) before)))
          (:instance sequence-register-frame-on-prefix (limit 30) (prefix 28) (clobbers '(1 2 3))
                     (after (sequence-execute (sequence-coerce-atom-string-path before) before)))
          (:instance sequence-frame-keeps-heap-registers (clobbers '(1 2 3))
                     (after (sequence-execute (sequence-coerce-atom-string-path before) before)))
          (:instance sequence-register-in-frame (limit 30) (clobbers '(1 2 3)) (register 30)
                     (after (sequence-execute (sequence-coerce-atom-string-path before) before)))
          (:instance sequence-segment-of-instruction-path (instructions (sequence-coerce-atom-string-path before))
                     (cuts (list (+ image-base *sequence-empty-string-offset*)))
                     (after (sequence-execute (sequence-coerce-atom-string-path before) before))))))
  :rule-classes nil)

(local
 (defthm sequence-register-only-prefix-keeps-preserved-heap
   (implies (and (proof-heap-p before objects packages)
                 (sequence-register-only-change-p before entered)
                 (proof-preserved-heap-p nil entered after objects final-objects packages))
            (proof-preserved-heap-p nil before after objects final-objects packages))
   :hints
   (("Goal"
     :in-theory (e/d (proof-preserved-heap-p proof-heap-frame-p proof-prefix-preserved-p
                      proof-dynamic-table-preserved-p proof-memory-span-agrees-p proof-streams-preserved-p
                      sequence-machine-span-agrees-p proof-static-size proof-load-word
                      sequence-register-only-change-p sequence-heap-registers-agree-p)
                     (proof-heap-p proof-fixed-heap-p proof-byte-entries-agree-p proof-stack-prefix
                      proof-dynamic-view proof-heap-base proof-stack-top proof-stack-base
                      proof-stack-end proof-spaces-end proof-machine-limit proof-world-machine))
     :use ((:instance sequence-register-only-change-keeps-heap (after entered))
           (:instance sequence-world-tail-fields (after entered)))))
   :rule-classes nil))

(local
 (defthm sequence-empty-string-view-with-tag
   (implies (and (equal (car view) :value) (equal (cdr view) ""))
            (equal view (proof-value-view "")))
   :hints (("Goal" :cases ((consp view))))
   :rule-classes nil))

(local
 (defthm sequence-empty-string-return-gives-empty-value
   (implies (proof-string-result-p 0 world objects packages)
            (proof-reg-value-p 0 "" world objects packages))
   :hints
   (("Goal"
     :in-theory (e/d (proof-string-result-p proof-reg-value-p proof-machine-value-p proof-value-p length)
                     (proof-covered-p proof-view acl2::coerce-inverse-2))
     :use ((:instance sequence-empty-string-view-with-tag
                      (view (proof-view (proof-world-reg 0 world) (proof-heap-base world)
                                       objects packages (proof-world-machine world))))
           (:instance acl2::coerce-inverse-2
                      (acl2::x (proof-view-value (proof-view (proof-world-reg 0 world)
                                                            (proof-heap-base world) objects packages
                                                            (proof-world-machine world))))))))
   :rule-classes nil))

(local
 (defthm sequence-coerce-of-atom-to-string-value
   (implies (and (atom datum) (not (eq result-type 'list)))
            (equal (proof-runtime-value 'coerce (list datum result-type) program)
                   (boymoo-model::core-value "")))
   :hints (("Goal"
            :in-theory (e/d (proof-runtime-value)
                            (sequence-core-coerce boymoo-model::core-primitive boymoo-model::core-prelude))
            :use sequence-core-coerce))
   :rule-classes nil))

(local
 (defthm sequence-coerce-after-empty-string-tail
   (implies
    (and (proof-heap-p before objects packages)
         (not (proof-world-stop before))
         (equal (proof-world-reg 30 entered) (proof-world-reg 30 before))
         (sequence-register-only-change-p before entered)
         (proof-register-frame-p 30 '(1 2 3) before entered)
         (proof-string-constructor-return-p 0 entered after objects final-objects packages)
         (atom datum) (not (eq result-type 'list)))
    (proof-runtime-return-p 'coerce (list datum result-type) program before after objects final-objects packages))
   :hints
   (("Goal"
     :in-theory (e/d (proof-string-constructor-return-p proof-frame-return-p
                      proof-runtime-return-p proof-datum-return-p proof-runtime-clobbers
                      sequence-register-only-change-p)
                     (proof-runtime-value proof-heap-p proof-reg-value-p proof-register-frame-p
                      proof-preserved-heap-p proof-string-result-p proof-view proof-world-reg
                      proof-world-pc proof-world-stop proof-world-machine))
     :use (sequence-register-only-prefix-keeps-preserved-heap sequence-coerce-of-atom-to-string-value
           (:instance sequence-empty-string-return-gives-empty-value (world after) (objects final-objects))
           (:instance sequence-register-frame-with-more-clobbers (limit 30) (old '(1 2 3))
                      (new (proof-runtime-clobbers 'coerce)) (after entered))
           (:instance sequence-register-frame-with-more-clobbers (limit 30)
                      (old *sequence-string-constructor-clobbers*) (new (proof-runtime-clobbers 'coerce))
                      (before entered))
           (:instance sequence-register-frame-transitive (limit 30)
                      (middle entered) (clobbers (proof-runtime-clobbers 'coerce))))))
   :rule-classes nil))

(defthm sequence-coerce-atom-string-runtime-contract
  (let* ((machine (proof-world-machine before))
         (path (sequence-coerce-atom-string-path before))
         (entered (sequence-execute path before))
         (target (+ image-base *sequence-empty-string-offset*))
         (cuts (list (proof-world-reg 30 before))))
    (implies
     (and (proof-runtime-pre-p 'coerce (list datum result-type) program labels image-base before objects packages)
          (atom datum) (not (eq result-type 'list))
          (consp (boymoo-model::a64-registers machine))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-coerce-offset*))
          (unsigned-byte-p 64 (+ (proof-heap-base before) 48))
          (unsigned-byte-p 64 (+ image-base *sequence-coerce-string-offset* 4))
          (unsigned-byte-p 64 target)
          (sequence-instruction-path (sequence-coerce-dispatch-path before)
                                     (list (+ image-base *sequence-coerce-string-offset*)) before)
          (sequence-instruction-path path (list target) before)
          (sequence-instruction-path path cuts before)
          (natp fuel)
          (proof-segment-p fuel cuts entered :cut after)
          (proof-string-constructor-return-p 0 entered after objects final-objects packages))
     (and (proof-segment-p (+ (len path) fuel) cuts before :cut after)
          (proof-runtime-return-p 'coerce (list datum result-type) program before after
                                  objects final-objects packages))))
  :hints
  (("Goal"
    :in-theory (e/d (proof-runtime-pre-p)
                    (proof-runtime-return-p proof-heap-p proof-reg-value-p proof-program-packages-p
                     proof-label-address proof-segment-p proof-string-constructor-return-p
                     proof-register-frame-p proof-world-stop proof-world-machine proof-world-reg
                     proof-world-pc proof-heap-base sequence-instruction-path sequence-execute
                     sequence-coerce-atom-string-path sequence-coerce-dispatch-path))
    :use (sequence-coerce-atom-string-call
          (:instance sequence-heap-layout-bounds (world before))
          (:instance sequence-coerce-after-empty-string-tail
                     (entered (sequence-execute (sequence-coerce-atom-string-path before) before)))
          (:instance sequence-append-checked-instructions (reason :cut) (suffix fuel)
                     (instructions (sequence-coerce-atom-string-path before))
                     (cuts (list (proof-world-reg 30 before)))))))
  :rule-classes nil)

(defthm sequence-coerce-atom-string-from-header-allocator
  (let* ((path (sequence-coerce-atom-string-path before))
         (empty (sequence-execute path before))
         (entered (sequence-execute *sequence-empty-string-dispatch* empty))
         (called (sequence-execute *sequence-small-string-request* entered))
         (after (sequence-small-constructor-continuation-after entered returned))
         (link (proof-world-reg 30 called))
         (cuts (list (proof-world-reg 30 before)))
         (target (+ image-base *sequence-empty-string-offset*))
         (published (cons (proof-object (proof-world-reg 0 returned) :active :header 0) new-objects))
         (constructor-steps (+ (len *sequence-empty-string-dispatch*)
                               (sequence-small-constructor-step-count fuel entered))))
    (implies
     (and (proof-runtime-pre-p 'coerce (list datum result-type) program labels image-base before objects packages)
          (atom datum) (not (eq result-type 'list))
          (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (natp image-base)
          (equal (proof-world-pc before) (+ image-base *sequence-coerce-offset*))
          (unsigned-byte-p 64 (+ (proof-heap-base before) 48))
          (unsigned-byte-p 64 (+ image-base *sequence-coerce-string-offset* 4))
          (unsigned-byte-p 64 (+ target 8))
          (sequence-instruction-path (sequence-coerce-dispatch-path before)
                                     (list (+ image-base *sequence-coerce-string-offset*)) before)
          (sequence-instruction-path path (list target) before)
          (sequence-instruction-path path cuts before)
          (consp (boymoo-model::a64-registers (proof-world-machine empty)))
          (equal (proof-world-reg 30 empty) (proof-world-reg 30 before))
          (sequence-instruction-path *sequence-empty-string-dispatch* cuts empty)
          (sequence-small-constructor-entry-p image-base entered)
          (sequence-instruction-path *sequence-small-string-request*
                                     (list (+ image-base *sequence-header-allocator-offset*)) entered)
          (sequence-instruction-path *sequence-small-string-request* cuts entered)
          (proof-segment-p fuel (cons link cuts) called :cut returned)
          (not (equal link (proof-world-reg 30 before)))
          (proof-allocator-return-p :header (sequence-small-string-allocation 0)
                                    called returned objects new-objects packages)
          (consp (boymoo-model::a64-registers (proof-world-machine returned)))
          (sequence-instruction-path (sequence-small-string-finish-path 0) cuts returned)
          (proof-preserved-heap-p nil empty after objects published packages))
     (and (proof-segment-p (+ (len path) constructor-steps) cuts before :cut after)
          (proof-runtime-return-p 'coerce (list datum result-type) program before after
                                  objects published packages))))
  :hints
  (("Goal"
    :do-not-induct t
    :in-theory (e/d (proof-runtime-pre-p)
                    (proof-runtime-return-p proof-string-constructor-return-p
                     proof-allocator-return-p proof-preserved-heap-p proof-segment-p proof-world-machine
                     proof-world-reg proof-world-pc proof-reg-value-p proof-heap-p proof-heap-base
                     proof-program-packages-p proof-label-address sequence-execute
                     sequence-instruction-path sequence-coerce-dispatch-path sequence-coerce-atom-string-path
                     sequence-small-constructor-entry-p sequence-small-constructor-continuation-after
                     sequence-small-string-allocation sequence-small-string-finish-path
                     sequence-small-constructor-step-count))
    :use (sequence-coerce-atom-string-call
          (:instance sequence-empty-string-constructor-with-publication
                     (before (sequence-execute (sequence-coerce-atom-string-path before) before))
                     (old-objects objects))
          (:instance sequence-coerce-atom-string-runtime-contract
                     (fuel (+ (len *sequence-empty-string-dispatch*)
                              (sequence-small-constructor-step-count
                               fuel (sequence-execute *sequence-empty-string-dispatch*
                                                      (sequence-execute (sequence-coerce-atom-string-path before) before)))))
                     (after (sequence-small-constructor-continuation-after
                             (sequence-execute *sequence-empty-string-dispatch*
                                               (sequence-execute (sequence-coerce-atom-string-path before) before))
                             returned))
                     (final-objects (cons (proof-object (proof-world-reg 0 returned) :active :header 0)
                                          new-objects))))))
  :rule-classes nil)
