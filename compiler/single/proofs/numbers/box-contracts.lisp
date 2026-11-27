(in-package "BOYMOO-PROOFS")

(include-book "publication-heap")
(include-book "stack-heap")
(include-book "numeric-frames")
(include-book "comparison-return")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-number-execute-block proof-step proof-run proof-segment-p
                     proof-execute proof-instruction-effect proof-number-checked-block-p
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-number-box-select-pre-p proof-number-box-fields-trace-p
                     proof-number-publication-pre-p proof-reserved-span-p proof-heap-p proof-heap-layout-p
                     proof-heap-frame-p proof-preserved-heap-p proof-prefix-preserved-p
                     proof-dynamic-table-preserved-p proof-reg-value-p proof-frame-return-p
                     proof-datum-return-p proof-integer-reserve-return-p proof-machine-limit
                     proof-number-reduced-p proof-number-world-byte-keys-p proof-load-word
                     boymoo-model::a64-sp boymoo-model::a64-memory mod floor ash)))

(local
 (defthm heap-implies-aligned-stack
   (implies (proof-heap-p world objects packages)
            (and (equal (mod (boymoo-model::a64-sp (proof-world-machine world)) 16) 0)
                 (not (proof-world-stop world))))
   :hints (("Goal"
            :expand ((proof-heap-p world objects packages) (proof-heap-layout-p world))
            :in-theory (disable proof-align-up proof-disjoint-p proof-covered-p proof-regions-p
                                proof-static-p proof-external-objects proof-object-map-p
                                proof-heap-object-spans-p proof-dynamic-symbol-objects-p
                                proof-dynamic-entries proof-dynamic-view proof-string-accounting-p
                                proof-stack-prefix proof-runtime-word)))))

(local
 (defthm stored-memory-bytes
   (equal (boymoo-model::a64-memory (boymoo-model::a64-store size address value machine))
          (boymoo-model::a64-write-bytes size address value (boymoo-model::a64-memory machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-store boymoo-model::a64-memory)))))

(local
 (defthm reserve-setup-effects
   (let* ((machine (proof-world-machine world))
          (saved (- (boymoo-model::a64-sp machine) 16))
          (ready (proof-number-box-reserve-ready reserve world)))
     (implies (not (eq (car machine) :svc))
              (and (equal (boymoo-model::a64-memory (proof-world-machine ready))
                          (boymoo-model::a64-memory
                           (boymoo-model::a64-store
                            8 (+ 8 saved) (proof-world-reg 30 world)
                            (boymoo-model::a64-store 8 saved (proof-world-reg 2 world) machine))))
                   (implies (not (member-equal register '(2 30)))
                            (equal (proof-world-reg register ready) (proof-world-reg register world)))
                   (equal (cdr ready) (cdr world)))))
   :hints (("Goal"
            :in-theory (e/d (proof-number-box-reserve-ready proof-number-box-reserve-instructions
                             proof-number-execute-block proof-world-reg)
                            (proof-reg boymoo-model::a64-store boymoo-model::a64-read-reg
                             boymoo-model::a64-write-reg boymoo-model::a64-unsigned
                             boymoo-model::a64-set-pc boymoo-model::a64-pc boymoo-model::a64-nzcv
                             boymoo-model::a64-write-bytes
                             (:definition nth) (:definition update-nth)))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm reserve-setup-footprint
   (let* ((first (proof-world-machine world))
          (last (proof-world-machine (proof-number-box-reserve-ready reserve world)))
          (sp (boymoo-model::a64-sp first))
          (saved (- sp 16)))
     (implies (and (not (eq (car first) :svc)) (proof-span-p saved 16))
              (proof-number-memory-change-p saved sp first last)))
   :hints (("Goal"
            :use ((:instance reserve-setup-effects (register 23))
                  (:instance proof-number-pair-store-changes-only-footprint
                             (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                             (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                             (end (boymoo-model::a64-sp (proof-world-machine world)))
                             (left (proof-world-reg 2 world)) (right (proof-world-reg 30 world))
                             (machine (proof-world-machine world)))
                  (:instance proof-number-memory-change-with-same-final-memory
                             (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                             (end (boymoo-model::a64-sp (proof-world-machine world)))
                             (first (proof-world-machine world))
                             (last (proof-world-machine (proof-number-box-reserve-ready reserve world)))
                             (other (boymoo-model::a64-store
                                     8 (- (boymoo-model::a64-sp (proof-world-machine world)) 8)
                                     (proof-world-reg 30 world)
                                     (boymoo-model::a64-store
                                      8 (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                      (proof-world-reg 2 world) (proof-world-machine world))))))
            :in-theory (disable proof-number-memory-change-p boymoo-model::a64-store)
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-box-reserve-setup-preserves-heap
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (ready (proof-number-box-reserve-ready reserve world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-save-interval-p (- sp 16) world objects)
                  (proof-number-box-fields-trace-p reserve world returned reserve-steps))
             (and (proof-preserved-heap-p nil world ready objects objects packages)
                  (equal (proof-machine-limit ready) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine ready)) (- sp 16)))))
  :hints (("Goal"
           :use (heap-implies-aligned-stack reserve-setup-footprint proof-number-box-calls-reserve
                 (:instance reserve-setup-effects (register 23))
                 (:instance reserve-setup-effects (register 24))
                 (:instance reserve-setup-effects (register 25))
                 (:instance reserve-setup-effects (register 26))
                 (:instance reserve-setup-effects (register 27))
                 (:instance reserve-setup-effects (register 28))
                 (:instance proof-number-mod-shift-by-multiple
                            (a (boymoo-model::a64-sp (proof-world-machine world))) (b 16) (times -1))
                 (:instance proof-number-machine-save-preserves-heap
                            (before world) (after (proof-number-box-reserve-ready reserve world))
                            (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))))
           :in-theory (e/d (proof-number-box-fields-trace-p proof-number-box-reserve-ready
                            proof-number-heap-registers-and-world-tail-agree-p proof-machine-limit)
                           (proof-number-save-interval-p proof-number-memory-change-p
                            proof-number-box-reserve-instructions proof-span-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-box-reserve-setup-register-frame
  (implies (not (eq (car (proof-world-machine world)) :svc))
           (proof-register-frame-p limit '(2 30) world
                                   (proof-number-box-reserve-ready reserve world)))
  :hints (("Goal"
           :induct (proof-register-frame-p limit '(2 30) world
                                           (proof-number-box-reserve-ready reserve world)))
          ("Subgoal *1/3" :use ((:instance reserve-setup-effects (register limit))))
          ("Subgoal *1/2" :use ((:instance reserve-setup-effects (register limit))))
          ("Subgoal *1/1" :use ((:instance reserve-setup-effects (register limit)))))
  :rule-classes nil)

(defthm proof-number-box-publication-register-frame
  (implies (and (not (eq (car (proof-world-machine world)) :svc))
                (<= (proof-heap-base world) (proof-world-reg 2 world)))
           (proof-register-frame-p limit '(0 3 30) world (proof-number-box-publish-after world)))
  :hints (("Goal"
           :induct (proof-register-frame-p limit '(0 3 30) world (proof-number-box-publish-after world))
           :in-theory (disable proof-heap-base))
          ("Subgoal *1/3" :use ((:instance proof-number-box-publication-register-effects (register limit))))
          ("Subgoal *1/2" :use ((:instance proof-number-box-publication-register-effects (register limit))))
          ("Subgoal *1/1" :use ((:instance proof-number-box-publication-register-effects (register limit)))))
  :rule-classes nil)

(local
 (defthm heap-after-reserve-and-restored-saves
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
          (ready (proof-number-box-reserve-ready reserve world))
          (link (proof-world-reg 30 world))
          (machine (proof-world-machine returned)))
     (implies (and (proof-number-box-fields-trace-p reserve world returned reserve-steps)
                   (proof-integer-reserve-return-p a b 24 ready returned objects reserved-objects packages))
              (and (proof-preserved-heap-p nil ready returned objects reserved-objects packages)
                   (proof-heap-p returned reserved-objects packages)
                   (equal (proof-machine-limit ready) (proof-machine-limit returned))
                   (equal (boymoo-model::a64-sp machine) (- sp 16))
                   (<= sp (proof-number-machine-stack-end returned))
                   (unsigned-byte-p 64 sp)
                   (equal (proof-load-word (boymoo-model::a64-sp machine) machine) (proof-world-reg 2 world))
                   (equal (proof-load-word (+ 8 (boymoo-model::a64-sp machine)) machine) link)
                   (proof-number-checked-block-p *proof-number-box-publish-instructions* (list link) returned)
                   (not (eq (car machine) :svc))
                   (proof-reg-value-p 0 a returned reserved-objects packages)
                   (proof-reg-value-p 1 b returned reserved-objects packages)
                   (proof-reserved-span-p :header (proof-world-reg 2 returned) 24 returned reserved-objects))))
   :hints (("Goal"
            :use (proof-number-box-calls-reserve
                  (:instance proof-number-register-frame-keeps
                             (limit 30) (register 23)
                             (clobbers (proof-number-numeric-clobbers))
                             (before (proof-number-box-reserve-ready reserve world)) (after returned))
                  (:instance proof-number-reserve-preserves-machine-saves
                             (before (proof-number-box-reserve-ready reserve world))
                             (after returned) (offset 0) (bytes 24)
                             (old-objects objects) (new-objects reserved-objects))
                  (:instance proof-number-reserve-preserves-machine-saves
                             (before (proof-number-box-reserve-ready reserve world))
                             (after returned) (offset 8) (bytes 24)
                             (old-objects objects) (new-objects reserved-objects)))
            :in-theory (e/d (proof-number-box-fields-trace-p proof-number-box-reserve-ready
                             proof-integer-reserve-return-p proof-number-numeric-clobbers
                             proof-frame-return-p proof-preserved-heap-p
                             proof-number-machine-stack-end proof-machine-limit)
                            (proof-register-frame-p proof-number-box-reserve-instructions proof-span-p))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm publication-context-after-reserve
   (let ((ready (proof-number-box-reserve-ready reserve world)))
     (implies (and (if (equal kind 4)
                       (and (proof-number-reduced-p a b) (< 1 b))
                     (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0))))
                   (equal (proof-world-reg 2 world) (+ 4096 kind))
                   (proof-number-box-fields-trace-p reserve world returned reserve-steps)
                   (proof-integer-reserve-return-p a b 24 ready returned objects reserved-objects packages))
              (and (proof-number-publication-pre-p kind a b returned reserved-objects packages)
                   (proof-preserved-heap-p nil ready returned objects reserved-objects packages)
                   (equal (proof-machine-limit ready) (proof-machine-limit returned))
                   (equal (boymoo-model::a64-sp (proof-world-machine returned))
                          (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                   (<= (+ 16 (boymoo-model::a64-sp (proof-world-machine returned)))
                       (proof-number-machine-stack-end returned)))))
   :hints (("Goal"
            :use heap-after-reserve-and-restored-saves
            :in-theory (enable proof-number-publication-pre-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm reserve-setup-keeps-byte-keys
   (implies (and (proof-number-world-byte-keys-p world)
                 (proof-number-box-fields-trace-p reserve world returned reserve-steps))
            (proof-number-world-byte-keys-p (proof-number-box-reserve-ready reserve world)))
   :hints (("Goal"
            :use (proof-number-box-calls-reserve
                  (:instance proof-number-segment-preserves-byte-keys
                             (count 3) (cuts (list reserve)) (before world) (reason :cut)
                             (after (proof-number-box-reserve-ready reserve world))))
            :in-theory (e/d (proof-number-box-fields-trace-p proof-number-box-reserve-ready)
                            (proof-span-p proof-number-box-reserve-instructions))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm box-fields-preserves-heap
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
          (ready (proof-number-box-reserve-ready reserve world))
          (after (proof-number-box-publish-after returned))
          (new-objects (proof-number-box-object-map returned reserved-objects)))
     (implies (and (if (equal kind 4)
                       (and (proof-number-reduced-p a b) (< 1 b))
                     (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0))))
                   (equal (proof-world-reg 2 world) (+ 4096 kind))
                   (proof-heap-p world objects packages)
                   (proof-number-save-interval-p (- sp 16) world objects)
                   (proof-number-box-fields-trace-p reserve world returned reserve-steps)
                   (proof-integer-reserve-return-p a b 24 ready returned objects reserved-objects packages)
                   (proof-number-world-byte-keys-p world)
                   (proof-number-world-byte-keys-p after))
              (proof-preserved-heap-p nil world after objects new-objects packages)))
   :hints (("Goal"
            :use (proof-number-box-reserve-setup-preserves-heap
                  publication-context-after-reserve reserve-setup-keeps-byte-keys
                  (:instance proof-number-box-publication-preserves-heap
                             (world returned) (objects reserved-objects))
                  (:instance proof-number-preserved-heaps-compose
                             (before (proof-number-box-reserve-ready reserve world))
                             (middle returned) (after (proof-number-box-publish-after returned))
                             (old-objects objects) (middle-objects reserved-objects)
                             (objects (proof-number-box-object-map returned reserved-objects)))
                  (:instance proof-number-preserved-heaps-compose
                             (before world) (middle (proof-number-box-reserve-ready reserve world))
                             (after (proof-number-box-publish-after returned))
                             (old-objects objects) (middle-objects objects)
                             (objects (proof-number-box-object-map returned reserved-objects))))
            :expand ((proof-preserved-heap-p nil world (proof-number-box-reserve-ready reserve world)
                                              objects objects packages))
            :in-theory (disable proof-number-box-object-map proof-number-save-interval-p
                                proof-number-box-reserve-ready proof-number-box-publish-after
                                proof-stack-top proof-number-machine-stack-end)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm heap-reservation-starts-above-base
   (implies (and (proof-heap-p world objects packages)
                 (proof-reserved-span-p :header (proof-world-reg 2 world) 24 world objects))
            (<= (proof-heap-base world) (proof-world-reg 2 world)))
   :hints (("Goal"
            :use ((:instance proof-number-reserved-header-is-local-write (address (proof-world-reg 2 world))))
            :expand ((proof-heap-p world objects packages))
            :in-theory (disable proof-heap-base proof-number-local-write-p proof-span-p
                                proof-external-objects proof-static-p proof-object-map-p
                                proof-heap-object-spans-p proof-dynamic-symbol-objects-p
                                proof-dynamic-entries proof-dynamic-view proof-string-accounting-p
                                proof-stack-prefix)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm box-fields-register-frame
   (let* ((link (proof-world-reg 30 world))
          (ready (proof-number-box-reserve-ready reserve world))
          (after (proof-number-box-publish-after returned)))
     (implies (and (proof-number-box-fields-trace-p reserve world returned reserve-steps)
                   (proof-integer-reserve-return-p a b 24 ready returned objects reserved-objects packages)
                   (equal (proof-world-reg 30 after) link))
              (proof-register-frame-p 30 (proof-number-numeric-clobbers) world after)))
   :hints (("Goal"
            :use (heap-after-reserve-and-restored-saves
                  (:instance heap-reservation-starts-above-base (world returned) (objects reserved-objects))
                  (:instance proof-number-box-reserve-setup-register-frame (limit 30))
                  (:instance proof-number-box-publication-register-frame (world returned) (limit 30))
                  (:instance proof-number-register-frame-allows-more-clobbers
                             (limit 30) (clobbers '(2 30)) (extended (cons 30 (proof-number-numeric-clobbers)))
                             (before world) (after (proof-number-box-reserve-ready reserve world)))
                  (:instance proof-number-register-frame-allows-more-clobbers
                             (limit 30) (clobbers (proof-number-numeric-clobbers))
                             (extended (cons 30 (proof-number-numeric-clobbers)))
                             (before (proof-number-box-reserve-ready reserve world)) (after returned))
                  (:instance proof-number-register-frame-allows-more-clobbers
                             (limit 30) (clobbers '(0 3 30)) (extended (cons 30 (proof-number-numeric-clobbers)))
                             (before returned) (after (proof-number-box-publish-after returned)))
                  (:instance proof-number-register-frames-compose
                             (limit 30) (clobbers (cons 30 (proof-number-numeric-clobbers)))
                             (before world) (middle (proof-number-box-reserve-ready reserve world)) (after returned))
                  (:instance proof-number-register-frames-compose
                             (limit 30) (clobbers (cons 30 (proof-number-numeric-clobbers)))
                             (before world) (middle returned) (after (proof-number-box-publish-after returned)))
                  (:instance proof-number-register-frame-can-keep-restored-register
                             (limit 30) (register 30) (clobbers (proof-number-numeric-clobbers))
                             (before world) (after (proof-number-box-publish-after returned))))
            :in-theory (e/d (proof-number-box-fields-trace-p proof-integer-reserve-return-p
                             proof-frame-return-p proof-number-numeric-clobbers)
                            (proof-register-frame-p proof-heap-base proof-number-box-reserve-instructions
                             proof-span-p proof-number-box-reserve-ready proof-number-box-publish-after))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-box-fields-datum-return
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (ready (proof-number-box-reserve-ready reserve world))
         (after (proof-number-box-publish-after returned))
         (new-objects (proof-number-box-object-map returned reserved-objects))
         (link (proof-world-reg 30 world))
         (count (+ 9 reserve-steps))
         (result (if (equal kind 4) (/ a b) (complex a b))))
    (implies (and (if (equal kind 4)
                      (and (proof-number-reduced-p a b) (< 1 b))
                    (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0))))
                  (equal (proof-world-reg 2 world) (+ 4096 kind))
                  (proof-heap-p world objects packages)
                  (proof-number-save-interval-p (- sp 16) world objects)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-box-fields-trace-p reserve world returned reserve-steps)
                  (proof-integer-reserve-return-p a b 24 ready returned objects reserved-objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (proof-datum-return-p result (proof-number-numeric-clobbers) t t nil
                                        world after objects new-objects packages))))
  :hints (("Goal"
           :use (heap-implies-aligned-stack box-fields-preserves-heap box-fields-register-frame
                 (:instance proof-number-box-fields-return (old-objects objects))
                 (:instance heap-implies-aligned-stack
                            (world (proof-number-box-publish-after returned))
                            (objects (proof-number-box-object-map returned reserved-objects)))
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (+ 9 reserve-steps)) (cuts (list (proof-world-reg 30 world)))
                            (before world) (after (proof-number-box-publish-after returned)) (reason :cut)))
           :expand ((proof-preserved-heap-p nil world (proof-number-box-publish-after returned)
                                             objects (proof-number-box-object-map returned reserved-objects) packages))
           :in-theory (e/d (proof-datum-return-p proof-frame-return-p)
                           (proof-register-frame-p proof-stack-top proof-number-save-interval-p))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm allocating-box-selection-code
   (implies (or (equal kind 4) (equal kind 5))
            (proof-number-register-only-code-p
             (proof-number-box-select-instructions kind entry unchanged fields) '(2)))
   :hints (("Goal"
            :in-theory (enable proof-number-box-select-instructions
                               proof-number-register-only-instruction-p)))))

(local
 (defthm allocating-box-selection-executes-all-instructions
   (implies (and (or (equal kind 4) (equal kind 5))
                 (not (proof-number-box-without-allocation-p kind world)))
            (equal (proof-number-box-select-after kind unchanged fields world)
                   (proof-number-execute-block
                    (proof-number-box-select-instructions kind (proof-world-pc world) unchanged fields)
                    world)))
   :hints (("Goal"
            :in-theory (enable proof-number-box-select-after proof-number-box-select-count
                               proof-number-box-select-instructions)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm object-size-is-a-memory-property
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (equal (proof-object-size object last) (proof-object-size object first)))
   :hints (("Goal"
            :in-theory (enable proof-object-size proof-load-word boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm same-memory-keeps-object-disjointness
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (equal (proof-object-disjoint-p start end objects last)
                   (proof-object-disjoint-p start end objects first)))
   :hints (("Goal"
            :induct (proof-object-disjoint-p start end objects first)
            :in-theory (disable proof-object-size proof-disjoint-p))
           ("Subgoal *1/3"
            :expand ((proof-object-disjoint-p start end objects last))
            :use ((:instance object-size-is-a-memory-property (object (car objects)))))
           ("Subgoal *1/2"
            :expand ((proof-object-disjoint-p start end objects last))
            :use ((:instance object-size-is-a-memory-property (object (car objects))))))
   :rule-classes nil))

(local
 (defthm preserved-heap-is-valid
   (implies (proof-preserved-heap-p nil before after old-objects objects packages)
            (proof-heap-p after objects packages))
   :hints (("Goal" :in-theory (enable proof-preserved-heap-p)))
   :rule-classes nil))

(local
 (defthm box-selection-preserves-heap-and-saves
   (let* ((count (if (equal kind 4) 3 4))
          (sp (boymoo-model::a64-sp (proof-world-machine world)))
          (middle (proof-number-box-select-after kind unchanged fields world)))
     (implies (and (if (equal kind 4)
                       (and (proof-number-reduced-p a b) (< 1 b))
                     (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0))))
                   (proof-heap-p world objects packages)
                   (proof-number-world-byte-keys-p world)
                   (proof-number-save-interval-p (- sp 16) world objects)
                   (proof-number-box-select-pre-p kind unchanged fields world)
                   (proof-reg-value-p 1 b world objects packages))
              (and (proof-segment-p count (list fields) world :cut middle)
                   (proof-heap-p middle objects packages)
                   (proof-preserved-heap-p nil world middle objects objects packages)
                   (proof-register-frame-p 30 (proof-number-numeric-clobbers) world middle)
                   (proof-number-world-byte-keys-p middle)
                   (equal (proof-world-reg 30 middle) (proof-world-reg 30 world))
                   (equal (proof-machine-limit middle) (proof-machine-limit world))
                   (equal (boymoo-model::a64-sp (proof-world-machine middle)) sp)
                   (equal (proof-world-reg 2 middle) (+ 4096 kind))
                   (proof-number-save-interval-p (- sp 16) middle objects))))
   :hints (("Goal"
            :use (proof-number-box-select-by-value proof-number-box-select
                  allocating-box-selection-executes-all-instructions
                  (:instance same-memory-keeps-object-disjointness
                             (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                             (end (boymoo-model::a64-sp (proof-world-machine world)))
                             (first (proof-world-machine world))
                             (last (proof-world-machine (proof-number-box-select-after kind unchanged fields world))))
                  (:instance proof-number-register-only-execution-preserves-heap
                             (clobbers '(2))
                             (instructions (proof-number-box-select-instructions
                                            kind (proof-world-pc world) unchanged fields)))
                  (:instance preserved-heap-is-valid
                             (before world) (after (proof-number-box-select-after kind unchanged fields world))
                             (old-objects objects))
                  (:instance proof-number-register-frame-allows-more-clobbers
                             (limit 30) (clobbers '(2)) (extended (proof-number-numeric-clobbers))
                             (before world) (after (proof-number-box-select-after kind unchanged fields world)))
                  (:instance proof-number-segment-preserves-byte-keys
                             (count (if (equal kind 4) 3 4)) (cuts (list fields))
                             (before world) (after (proof-number-box-select-after kind unchanged fields world))
                             (reason :cut)))
            :in-theory (e/d (proof-number-box-select-pre-p
                             proof-number-box-select-target proof-number-box-select-count
                             proof-number-save-interval-p proof-number-numeric-clobbers)
                            (proof-instructions-at-p proof-number-box-select-instructions proof-span-p
                             proof-object-disjoint-p proof-number-register-only-code-p proof-register-frame-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-box-allocated-datum-return
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (middle (proof-number-box-select-after kind unchanged fields world))
         (ready (proof-number-box-reserve-ready reserve middle))
         (after (proof-number-box-publish-after returned))
         (new-objects (proof-number-box-object-map returned reserved-objects))
         (link (proof-world-reg 30 world))
         (count (+ (if (equal kind 4) 3 4) 9 reserve-steps))
         (result (if (equal kind 4) (/ a b) (complex a b))))
    (implies (and (if (equal kind 4)
                      (and (proof-number-reduced-p a b) (< 1 b))
                    (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0))))
                  (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-save-interval-p (- sp 16) world objects)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-box-select-pre-p kind unchanged fields world)
                  (proof-number-cut-free-prefix-p (if (equal kind 4) 3 4) (list fields link) world)
                  (proof-number-box-fields-trace-p reserve middle returned reserve-steps)
                  (proof-integer-reserve-return-p a b 24 ready returned objects reserved-objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (proof-datum-return-p result (proof-number-numeric-clobbers) t t nil
                                        world after objects new-objects packages))))
  :hints (("Goal"
           :use (box-selection-preserves-heap-and-saves heap-implies-aligned-stack
                 (:instance proof-number-box-allocated-return (old-objects objects))
                 (:instance proof-number-box-fields-datum-return
                            (world (proof-number-box-select-after kind unchanged fields world)))
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (+ (if (equal kind 4) 3 4) 9 reserve-steps))
                            (cuts (list (proof-world-reg 30 world)))
                            (before world) (after (proof-number-box-publish-after returned)) (reason :cut))
                 (:instance proof-number-preserved-heaps-compose
                            (before world) (middle (proof-number-box-select-after kind unchanged fields world))
                            (after (proof-number-box-publish-after returned))
                            (old-objects objects) (middle-objects objects)
                            (objects (proof-number-box-object-map returned reserved-objects)))
                 (:instance proof-number-register-frames-compose
                            (limit 30) (clobbers (proof-number-numeric-clobbers))
                            (before world) (middle (proof-number-box-select-after kind unchanged fields world))
                            (after (proof-number-box-publish-after returned))))
           :in-theory (e/d (proof-datum-return-p proof-frame-return-p proof-number-box-fields-trace-p)
                           (proof-number-box-reserve-instructions proof-register-frame-p proof-span-p
                            proof-stack-top proof-number-box-reserve-ready proof-number-save-interval-p))
           :do-not-induct t))
  :rule-classes nil)
