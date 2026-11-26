(in-package "BOYMOO-PROOFS")

(include-book "type-effects")
(include-book "box-return")
(include-book "numeric-frames")
(include-book "comparison-return")
(include-book "box-contracts")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-execute proof-instruction-effect
                     proof-number-checked-block-p proof-number-execute-block
                     proof-number-cut-free-prefix-p proof-number-exact-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-reg-value-p proof-machine-value-p proof-heap-p proof-heap-layout-p
                     proof-number-types-completion-trace-p proof-number-box-select-pre-p
                     proof-preserved-heap-p proof-frame-return-p proof-datum-return-p
                     proof-runtime-pre-p proof-runtime-return-p proof-runtime-value
                     boymoo-model::a64-sp boymoo-model::a64-memory mod floor ash)))

(defund proof-number-collapsing-box-code (kind unchanged fields world)
  (append (take 2 (proof-number-box-select-instructions
                  kind (proof-world-pc world) unchanged fields))
          '((:branch-reg 30 nil))))

(defund proof-number-box-collapse-after (kind unchanged fields world)
  (proof-number-execute-block '((:branch-reg 30 nil))
                              (proof-number-box-select-after kind unchanged fields world)))

(local
 (defthm collapse-is-register-only-code
   (proof-number-register-only-code-p
    (proof-number-collapsing-box-code kind unchanged fields world) nil)
   :hints (("Goal" :in-theory (enable proof-number-collapsing-box-code proof-number-box-select-instructions
                                     proof-number-register-only-instruction-p)))))

(local
 (defthm collapsing-box-sequence
   (implies (proof-number-box-without-allocation-p kind world)
            (equal (proof-number-box-collapse-after kind unchanged fields world)
                   (proof-number-execute-block
                    (proof-number-collapsing-box-code kind unchanged fields world) world)))
   :hints (("Goal"
            :in-theory (enable proof-number-box-collapse-after proof-number-collapsing-box-code
                               proof-number-box-select-after proof-number-box-select-count)
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-collapse-keeps-heap-and-frame
  (let ((after (proof-number-box-collapse-after kind unchanged fields world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-box-select-pre-p kind unchanged fields world)
                  (proof-reg-value-p 1 b world objects packages)
                  (if (equal kind 4) (equal b 1) (equal b 0)))
             (and (proof-preserved-heap-p nil world after objects objects packages)
                  (proof-register-frame-p 30 (proof-number-numeric-clobbers) world after)
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world)))))
  :hints (("Goal"
           :use (proof-number-box-select-by-value collapsing-box-sequence
                 (:instance proof-number-register-only-execution-preserves-heap
                            (clobbers nil)
                            (instructions (proof-number-collapsing-box-code kind unchanged fields world)))
                 (:instance proof-number-register-only-block-effects
                            (register 30) (clobbers nil)
                            (instructions (proof-number-collapsing-box-code kind unchanged fields world)))
                 (:instance proof-number-register-frame-allows-more-clobbers
                            (limit 30) (clobbers nil) (extended (proof-number-numeric-clobbers))
                            (before world) (after (proof-number-box-collapse-after kind unchanged fields world))))
           :in-theory (e/d (proof-number-box-select-pre-p)
                           (proof-instructions-at-p proof-register-frame-p
                            proof-number-register-only-code-p))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm heap-world-running
   (implies (proof-heap-p world objects packages) (not (proof-world-stop world)))
   :hints (("Goal"
            :expand ((proof-heap-p world objects packages) (proof-heap-layout-p world))
            :in-theory (disable proof-heap-p proof-heap-layout-p proof-object-map-p proof-static-p
                                proof-external-objects proof-dynamic-view proof-dynamic-entries
                                proof-heap-object-spans-p proof-dynamic-symbol-objects-p proof-string-accounting-p
                                proof-covered-p proof-align-up proof-disjoint-p proof-runtime-word
                                proof-stack-prefix proof-regions-p)))
   :rule-classes nil))

(defthm proof-number-box-collapsed-datum-return
  (let* ((link (proof-world-reg 30 world))
         (leaf (proof-number-box-select-after kind unchanged fields world))
         (after (proof-number-box-collapse-after kind unchanged fields world))
         (result (if (equal kind 4) (/ a b) (complex a b))))
    (implies (and (if (equal kind 4)
                      (and (integerp a) (equal b 1))
                    (and (equal kind 5) (rationalp a) (equal b 0)))
                  (proof-heap-p world objects packages)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-box-select-pre-p kind unchanged fields world)
                  (proof-number-cut-free-prefix-p 2 (list unchanged link) world)
                  (proof-number-checked-block-p '((:branch-reg 30 nil)) (list link) leaf)
                  (not (eq (car (proof-world-machine leaf)) :svc))
                  (unsigned-byte-p 64 (+ 4 unchanged)))
             (and (proof-segment-p 3 (list link) world :cut after)
                  (proof-datum-return-p result (proof-number-numeric-clobbers) t t nil
                                        world after objects objects packages))))
  :hints (("Goal"
           :use (proof-number-box-collapse-return proof-number-collapse-keeps-heap-and-frame heap-world-running)
           :in-theory (e/d (proof-number-box-collapse-after proof-datum-return-p proof-frame-return-p)
                           (proof-register-frame-p complex))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-complex-collapse-trace-p (a b classifier unchanged fields world objects packages)
  (let* ((link (proof-world-reg 30 world))
         (middle (proof-number-types-completion-after t classifier world))
         (leaf (proof-number-box-select-after 5 unchanged fields middle)))
    (and (proof-number-types-completion-trace-p t classifier (list link) a b world objects packages)
         (proof-number-box-select-pre-p 5 unchanged fields middle)
         (proof-number-cut-free-prefix-p 2 (list unchanged link) middle)
         (proof-number-checked-block-p '((:branch-reg 30 nil)) (list link) leaf)
         (not (eq (car (proof-world-machine leaf)) :svc))
         (unsigned-byte-p 64 (+ 4 unchanged)))))

(local
 (defthm complex-pre-heap
   (implies (proof-runtime-pre-p 'complex (list a b) program labels base world objects packages)
            (and (proof-heap-p world objects packages)
                 (not (proof-world-stop world))))
   :hints (("Goal"
            :use heap-world-running
            :in-theory (e/d (proof-runtime-pre-p)
                            (proof-runtime-entry proof-program-packages-p proof-label-address
                             proof-register-arguments-p))))
   :rule-classes nil))

(local
 (defthm two-argument-register-views
   (equal (proof-register-arguments-p (list a b) 0 world objects packages)
          (and (proof-reg-value-p 0 a world objects packages)
               (proof-reg-value-p 1 b world objects packages)))
   :hints (("Goal"
            :expand ((proof-register-arguments-p (list a b) 0 world objects packages)
                     (proof-register-arguments-p (list b) 1 world objects packages)
                     (proof-register-arguments-p nil 2 world objects packages))))))

(local
 (defthm complex-completion-context
   (let* ((link (proof-world-reg 30 world))
          (middle (proof-number-types-completion-after t classifier world)))
     (implies (and (proof-heap-p world objects packages)
                   (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                                 world objects)
                   (proof-number-types-completion-trace-p t classifier (list link) a b world objects packages))
              (and (proof-preserved-heap-p nil world middle objects objects packages)
                   (proof-heap-p middle objects packages)
                   (proof-register-frame-p 30 (proof-number-numeric-clobbers) world middle)
                   (not (proof-world-stop middle))
                   (equal (proof-world-reg 30 middle) link)
                   (equal (proof-world-reg 23 middle) (proof-world-reg 23 world))
                   (equal (boymoo-model::a64-sp (proof-world-machine middle))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (proof-reg-value-p 0 (rfix a) middle objects packages)
                   (proof-reg-value-p 1 (rfix b) middle objects packages))))
   :hints (("Goal"
            :use ((:instance proof-number-type-completion-preserves-heap
                             (rational-only t) (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-number-type-completion-keeps-frame-registers
                             (rational-only t) (cuts (list (proof-world-reg 30 world))) (register 23))
                  (:instance proof-number-types-keep-numeric-register-frame
                             (rational-only t) (cuts (list (proof-world-reg 30 world))) (limit 30))
                  (:instance proof-number-types-return-or-fallthrough
                             (rational-only t) (cuts (list (proof-world-reg 30 world))))
                  (:instance heap-world-running
                             (world (proof-number-types-completion-after t classifier world))))
            :in-theory (e/d (proof-preserved-heap-p)
                            (proof-prefix-preserved-p proof-dynamic-table-preserved-p
                             proof-register-frame-p proof-heap-frame-p proof-register-arguments-p))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm complex-collapse-context
   (let* ((middle (proof-number-types-completion-after t classifier world))
          (after (proof-number-box-collapse-after 5 unchanged fields middle)))
     (implies (and (proof-heap-p world objects packages)
                   (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                                 world objects)
                   (equal (rfix b) 0)
                   (proof-number-world-byte-keys-p world)
                   (proof-number-world-byte-keys-p after)
                   (proof-number-complex-collapse-trace-p a b classifier unchanged fields world objects packages))
              (and (proof-preserved-heap-p nil world after objects objects packages)
                   (proof-register-frame-p 30 (proof-number-numeric-clobbers) world after)
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (not (proof-world-stop after)))))
   :hints (("Goal"
            :use (complex-completion-context
                  (:instance proof-number-collapse-keeps-heap-and-frame
                             (kind 5) (b (rfix b))
                             (world (proof-number-types-completion-after t classifier world)))
                  (:instance proof-number-preserved-heaps-compose
                             (before world)
                             (middle (proof-number-types-completion-after t classifier world))
                             (after (proof-number-box-collapse-after
                                     5 unchanged fields (proof-number-types-completion-after t classifier world)))
                             (old-objects objects) (middle-objects objects))
                  (:instance proof-number-register-frames-compose
                             (limit 30) (clobbers (proof-number-numeric-clobbers))
                             (before world)
                             (middle (proof-number-types-completion-after t classifier world))
                             (after (proof-number-box-collapse-after
                                     5 unchanged fields (proof-number-types-completion-after t classifier world)))))
            :in-theory (e/d (proof-number-complex-collapse-trace-p proof-machine-limit)
                            (proof-register-frame-p rfix))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-complex-collapsed-runtime-return
  (let* ((args (list a b))
         (middle (proof-number-types-completion-after t classifier world))
         (after (proof-number-box-collapse-after 5 unchanged fields middle))
         (link (proof-world-reg 30 world))
         (count (+ 3 (proof-number-types-completion-steps t classifier world))))
    (implies (and (proof-runtime-pre-p 'complex args program labels base world objects packages)
                  (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                                world objects)
                  (proof-number-world-byte-keys-p world)
                  (equal (rfix b) 0)
                  (proof-number-complex-collapse-trace-p a b classifier unchanged fields world objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (proof-runtime-return-p 'complex args program world after objects objects packages))))
  :hints (("Goal"
           :use (complex-pre-heap complex-collapse-context proof-number-complex-collapsed-return
                 proof-number-public-value-completions
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (+ 3 (proof-number-types-completion-steps t classifier world)))
                            (cuts (list (proof-world-reg 30 world))) (before world) (reason :cut)
                            (after (proof-number-box-collapse-after
                                    5 unchanged fields (proof-number-types-completion-after t classifier world)))))
           :in-theory (e/d (proof-number-complex-collapse-trace-p proof-number-box-collapse-after
                            proof-runtime-return-p proof-datum-return-p proof-frame-return-p)
                           (proof-register-frame-p proof-number-numeric-clobbers rfix))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-complex-allocation-trace-p
    (a b classifier unchanged fields reserve reserve-steps world returned objects reserved-objects packages)
  (let* ((link (proof-world-reg 30 world))
         (middle (proof-number-types-completion-after t classifier world))
         (selected (proof-number-box-select-after 5 unchanged fields middle))
         (ready (proof-number-box-reserve-ready reserve selected)))
    (and (proof-number-types-completion-trace-p t classifier (list link) a b world objects packages)
         (proof-number-box-select-pre-p 5 unchanged fields middle)
         (proof-number-cut-free-prefix-p 4 (list fields link) middle)
         (natp reserve-steps)
         (proof-number-box-fields-trace-p reserve selected returned reserve-steps)
         (proof-integer-reserve-return-p (rfix a) (rfix b) 24 ready returned
                                         objects reserved-objects packages))))

(local
 (defthm complex-box-allocates-with-heap-and-frame
   (let* ((after (proof-number-box-publish-after returned))
          (new-objects (proof-number-box-object-map returned reserved-objects)))
     (implies (and (proof-heap-p world objects packages)
                   (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                                 world objects)
                   (proof-number-world-byte-keys-p world)
                   (not (equal (rfix b) 0))
                   (proof-number-complex-allocation-trace-p
                    a b classifier unchanged fields reserve reserve-steps
                    world returned objects reserved-objects packages))
              (and (proof-register-frame-p 30 (proof-number-numeric-clobbers) world after)
                   (proof-preserved-heap-p nil world after objects new-objects packages)
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (not (proof-world-stop after)))))
   :hints (("Goal"
            :use (complex-completion-context
                  (:instance proof-number-type-completion-keeps-save-interval
                             (rational-only t) (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-number-types-return-or-fallthrough
                             (rational-only t) (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-number-exact-prefix-preserves-byte-keys
                             (count (proof-number-types-completion-steps t classifier world))
                             (cuts (list (proof-world-reg 30 world))) (before world)
                             (after (proof-number-types-completion-after t classifier world)))
                  (:instance proof-number-box-allocated-datum-return
                             (kind 5) (a (rfix a)) (b (rfix b))
                             (world (proof-number-types-completion-after t classifier world)))
                  (:instance proof-number-segment-preserves-byte-keys
                             (count (+ 13 reserve-steps))
                             (cuts (list (proof-world-reg 30 world)))
                             (before (proof-number-types-completion-after t classifier world))
                             (after (proof-number-box-publish-after returned)) (reason :cut))
                  (:instance proof-number-register-frames-compose
                             (limit 30) (clobbers (proof-number-numeric-clobbers))
                             (before world) (middle (proof-number-types-completion-after t classifier world))
                             (after (proof-number-box-publish-after returned)))
                  (:instance proof-number-preserved-heaps-compose
                             (before world) (middle (proof-number-types-completion-after t classifier world))
                             (after (proof-number-box-publish-after returned))
                             (old-objects objects) (middle-objects objects)
                             (objects (proof-number-box-object-map returned reserved-objects))))
            :in-theory (e/d (proof-number-complex-allocation-trace-p proof-datum-return-p proof-frame-return-p
                             proof-machine-limit)
                            (proof-number-complex-collapse-trace-p proof-integer-reserve-return-p
                             proof-number-box-fields-trace-p proof-register-frame-p
                             proof-number-exact-prefix-p proof-number-save-interval-p rfix complex))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-complex-allocated-runtime-return
  (let* ((args (list a b))
         (after (proof-number-box-publish-after returned))
         (new-objects (proof-number-box-object-map returned reserved-objects))
         (link (proof-world-reg 30 world))
         (count (+ 13 reserve-steps (proof-number-types-completion-steps t classifier world))))
    (implies (and (proof-runtime-pre-p 'complex args program labels base world objects packages)
                  (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                                world objects)
                  (proof-number-world-byte-keys-p world)
                  (not (equal (rfix b) 0))
                  (proof-number-complex-allocation-trace-p
                   a b classifier unchanged fields reserve reserve-steps
                   world returned objects reserved-objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (proof-runtime-return-p 'complex args program world after objects new-objects packages))))
  :hints (("Goal"
           :use (complex-pre-heap complex-box-allocates-with-heap-and-frame
                 (:instance proof-number-complex-allocated-return (old-objects objects))
                 proof-number-public-value-completions)
           :in-theory (e/d (proof-number-complex-allocation-trace-p
                            proof-runtime-return-p proof-datum-return-p proof-frame-return-p)
                           (proof-register-frame-p proof-integer-reserve-return-p
                            proof-number-box-fields-trace-p proof-number-numeric-clobbers rfix complex))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-complex-runtime-return
  (let* ((args (list a b))
         (collapse (equal (rfix b) 0))
         (completion (proof-number-types-completion-after t classifier world))
         (after (if collapse
                    (proof-number-box-collapse-after 5 unchanged fields completion)
                  (proof-number-box-publish-after returned)))
         (new-objects (if collapse objects (proof-number-box-object-map returned reserved-objects)))
         (link (proof-world-reg 30 world))
         (count (+ (proof-number-types-completion-steps t classifier world)
                   (if collapse 3 (+ 13 reserve-steps)))))
    (implies (and (proof-runtime-pre-p 'complex args program labels base world objects packages)
                  (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                                world objects)
                  (proof-number-world-byte-keys-p world)
                  (if collapse
                      (proof-number-complex-collapse-trace-p a b classifier unchanged fields world objects packages)
                    (proof-number-complex-allocation-trace-p
                     a b classifier unchanged fields reserve reserve-steps
                     world returned objects reserved-objects packages)))
             (and (proof-segment-p count (list link) world :cut after)
                  (proof-runtime-return-p 'complex args program world after objects new-objects packages))))
  :hints (("Goal"
           :use (proof-number-complex-collapsed-runtime-return proof-number-complex-allocated-runtime-return)
           :in-theory (disable proof-number-complex-collapse-trace-p proof-number-complex-allocation-trace-p
                               proof-number-save-interval-p proof-number-world-byte-keys-p rfix)
           :do-not-induct t))
  :rule-classes nil)
