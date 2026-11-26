(in-package "BOYMOO-PROOFS")

(include-book "public-delegation")
(include-book "dispatch-return")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-machine-limit proof-heap-p proof-heap-layout-p proof-heap-frame-p
                     proof-preserved-heap-p proof-frame-return-p proof-datum-return-p proof-reg-value-p
                     proof-number-binary-types-p proof-number-binary-types-call-trace-p
                     proof-number-classifier-trace-p proof-number-pop-link-trace-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defthm proof-number-dispatch-pop-keeps-caller-context
  (let* ((first (proof-world-machine before))
         (saved (proof-world-machine middle))
         (after (proof-number-pop-link-after middle)))
    (implies (and (proof-heap-p before objects packages)
                  (proof-heap-p middle objects packages)
                  (proof-preserved-heap-p nil before middle objects objects packages)
                  (proof-register-frame-p 30 (cons 30 (proof-number-numeric-clobbers)) before middle)
                  (equal (proof-machine-limit middle) (proof-machine-limit before))
                  (equal (boymoo-model::a64-sp saved) (- (boymoo-model::a64-sp first) 16))
                  (proof-number-pop-link-trace-p cuts middle)
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 before))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
                  (proof-number-world-byte-keys-p before)
                  (proof-number-world-byte-keys-p after))
             (and (proof-preserved-heap-p nil before after objects objects packages)
                  (proof-register-frame-p 30 (proof-number-numeric-clobbers) before after)
                  (equal (proof-machine-limit after) (proof-machine-limit before)))))
  :hints (("Goal"
           :use ((:instance proof-number-heap-machine-context (world before))
                 (:instance proof-number-pop-link-preserves-heap (world middle))
                 (:instance proof-number-pop-link-register-frame (world middle) (limit 30))
                 (:instance proof-number-preserved-heaps-compose
                            (after (proof-number-pop-link-after middle))
                            (old-objects objects) (middle-objects objects))
                 (:instance proof-number-register-frames-extend-and-compose
                            (limit 30) (clobbers (append '(29 30) (proof-number-numeric-clobbers)))
                            (first-clobbers (cons 30 (proof-number-numeric-clobbers)))
                            (last-clobbers '(29 30)) (after (proof-number-pop-link-after middle)))
                 (:instance proof-number-register-frame-can-keep-restored-register
                            (limit 30) (register 29) (clobbers (cons 30 (proof-number-numeric-clobbers)))
                            (after (proof-number-pop-link-after middle)))
                 (:instance proof-number-register-frame-can-keep-restored-register
                            (limit 30) (register 30) (clobbers (proof-number-numeric-clobbers))
                            (after (proof-number-pop-link-after middle))))
           :in-theory (e/d (proof-number-pop-link-trace-p proof-number-machine-stack-end
                            proof-number-numeric-clobbers)
                           (proof-register-frame-p proof-number-checked-block-p))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-binary-arithmetic-wrapper-trace-p (types classifier a b world objects packages)
  (let ((cuts (list (proof-world-reg 30 world))))
    (and (proof-number-binary-wrapper-save-intervals-p types world objects)
         (proof-number-binary-types-call-trace-p types classifier cuts a b world objects packages)
         (proof-number-pop-link-trace-p cuts (proof-number-binary-types-call-after types classifier world)))))

(defund proof-number-dispatch-context-p (before after objects packages)
  (and (proof-preserved-heap-p nil before after objects objects packages)
       (proof-register-frame-p 30 (proof-number-numeric-clobbers) before after)
       (equal (proof-machine-limit after) (proof-machine-limit before))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 before))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-number-world-byte-keys-p after)))

(defthm proof-number-binary-arithmetic-wrapper-keeps-dispatch-context
  (let* ((cuts (list (proof-world-reg 30 world)))
         (called (proof-number-binary-types-call-after types classifier world))
         (after (proof-number-pop-link-after called))
         (steps (+ 3 (proof-number-types-completion-steps nil classifier
                                                          (proof-number-types-first-ready types world)))))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-binary-arithmetic-wrapper-trace-p types classifier a b world objects packages))
             (and (proof-number-exact-prefix-p steps cuts world after)
                  (proof-number-dispatch-context-p world after objects packages)
                  (proof-number-binary-types-p a b after objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-binary-wrapper-reaches-dispatch (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-binary-wrapper-preserves-heap-while-saved
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-binary-wrapper-register-frame-while-saved
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count (+ 3 (proof-number-types-completion-steps
                                         nil classifier (proof-number-types-first-ready types world))))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (after (proof-number-pop-link-after
                                    (proof-number-binary-types-call-after types classifier world))))
                 (:instance proof-number-dispatch-pop-keeps-caller-context
                            (before world) (middle (proof-number-binary-types-call-after types classifier world))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (e/d (proof-number-binary-arithmetic-wrapper-trace-p proof-number-dispatch-context-p)
                           (proof-register-frame-p proof-number-binary-types-p))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-unary-wrapper-called (classifier world)
  (proof-number-classifier-after (proof-number-types-first-ready classifier world)))

(defund proof-number-unary-arithmetic-wrapper-trace-p (classifier world objects)
  (let* ((ready (proof-number-types-first-ready classifier world))
         (cuts (list (proof-world-reg 30 world)))
         (sp (boymoo-model::a64-sp (proof-world-machine world))))
    (and (proof-number-save-interval-p (- sp 16) world objects)
         (proof-number-save-and-call-trace-p classifier cuts world)
         (proof-number-classifier-trace-p cuts ready)
         (proof-number-pop-link-trace-p cuts (proof-number-unary-wrapper-called classifier world)))))

(local
 (defthm unary-classifier-path-is-register-only
   (proof-number-register-only-code-p (proof-number-classifier-path world) '(3 4 5))
   :hints (("Goal"
            :in-theory (enable proof-number-classifier-path proof-number-classifier-instructions
                               proof-number-register-only-instruction-p)))))

(local
 (defthm unary-wrapper-keeps-first-argument
   (implies (and (proof-heap-p world objects packages)
                 (proof-reg-value-p 0 a world objects packages)
                 (proof-number-unary-arithmetic-wrapper-trace-p classifier world objects))
            (proof-reg-value-p 0 a (proof-number-types-first-ready classifier world) objects packages))
   :hints (("Goal"
            :use (proof-number-heap-machine-context
                  (:instance proof-number-save-and-call-keeps-arguments
                             (target classifier) (register 0) (value a)))
            :in-theory (e/d (proof-number-unary-arithmetic-wrapper-trace-p
                             proof-number-save-and-call-trace-p proof-number-save-interval-p)
                            (proof-span-p proof-object-disjoint-p proof-object-map-p))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm unary-wrapper-preserves-context-while-saved
   (let* ((first-sp (boymoo-model::a64-sp (proof-world-machine world)))
          (called (proof-number-unary-wrapper-called classifier world)))
     (implies (and (proof-heap-p world objects packages)
                   (proof-number-world-byte-keys-p world)
                   (proof-number-unary-arithmetic-wrapper-trace-p classifier world objects))
              (and (proof-preserved-heap-p nil world called objects objects packages)
                   (proof-heap-p called objects packages)
                   (proof-register-frame-p 30 (cons 30 (proof-number-numeric-clobbers)) world called)
                   (equal (boymoo-model::a64-sp (proof-world-machine called)) (- first-sp 16))
                   (equal (proof-machine-limit called) (proof-machine-limit world)))))
   :hints (("Goal"
            :use ((:instance proof-number-save-and-call-preserves-heap
                             (target classifier) (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-number-save-and-call-register-frame (target classifier) (limit 30))
                  (:instance proof-number-checked-save-and-call
                             (target classifier) (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-number-preserved-heap-is-valid
                             (may-intern nil) (before world) (old-objects objects)
                             (after (proof-number-types-first-ready classifier world)))
                  (:instance proof-number-register-only-execution-preserves-heap
                             (clobbers '(3 4 5)) (world (proof-number-types-first-ready classifier world))
                             (instructions (proof-number-classifier-path
                                            (proof-number-types-first-ready classifier world))))
                  (:instance proof-number-classification-keeps-values
                             (cuts (list (proof-world-reg 30 world))) (register 23) (value nil) (operand nil)
                             (world (proof-number-types-first-ready classifier world)))
                  (:instance proof-number-exact-prefix-preserves-byte-keys
                             (count 2) (cuts (list (proof-world-reg 30 world))) (before world)
                             (after (proof-number-types-first-ready classifier world)))
                  (:instance proof-number-exact-prefix-preserves-byte-keys
                             (count (len (proof-number-classifier-path (proof-number-types-first-ready classifier world))))
                             (cuts (list (proof-world-reg 30 world))) (before (proof-number-types-first-ready classifier world))
                             (after (proof-number-unary-wrapper-called classifier world)))
                  (:instance proof-number-preserved-heaps-compose
                             (before world) (middle (proof-number-types-first-ready classifier world))
                             (after (proof-number-unary-wrapper-called classifier world))
                             (old-objects objects) (middle-objects objects))
                  (:instance proof-number-preserved-heap-is-valid
                             (may-intern nil) (before world) (old-objects objects)
                             (after (proof-number-unary-wrapper-called classifier world)))
                  (:instance proof-number-register-frames-extend-and-compose
                             (limit 30) (clobbers (cons 30 (proof-number-numeric-clobbers)))
                             (first-clobbers '(30)) (last-clobbers '(3 4 5)) (before world)
                             (middle (proof-number-types-first-ready classifier world))
                             (after (proof-number-unary-wrapper-called classifier world))))
            :in-theory (e/d (proof-number-unary-arithmetic-wrapper-trace-p proof-number-unary-wrapper-called
                             proof-number-classifier-after proof-number-classifier-trace-p
                             proof-number-save-and-call-trace-p proof-number-numeric-clobbers)
                            (proof-register-frame-p proof-number-register-only-code-p
                             proof-number-classifier-path proof-number-types-first-code proof-span-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-unary-arithmetic-wrapper-keeps-dispatch-context
  (let* ((cuts (list (proof-world-reg 30 world)))
         (called (proof-number-unary-wrapper-called classifier world))
         (after (proof-number-pop-link-after called))
         (steps (+ 3 (len (proof-number-classifier-path (proof-number-types-first-ready classifier world))))))
    (implies (and (proof-heap-p world objects packages)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-unary-arithmetic-wrapper-trace-p classifier world objects))
             (and (proof-number-exact-prefix-p steps cuts world after)
                  (proof-number-dispatch-context-p world after objects packages)
                  (proof-reg-value-p 0 a after objects packages)
                  (equal (proof-world-reg 3 after) (proof-number-datum-class a)))))
  :hints (("Goal"
           :use (unary-wrapper-keeps-first-argument unary-wrapper-preserves-context-while-saved
                 (:instance proof-number-unary-wrapper-reaches-dispatch (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count (+ 3 (len (proof-number-classifier-path
                                              (proof-number-types-first-ready classifier world)))))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (after (proof-number-pop-link-after (proof-number-unary-wrapper-called classifier world))))
                 (:instance proof-number-dispatch-pop-keeps-caller-context
                            (before world) (middle (proof-number-unary-wrapper-called classifier world))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (enable proof-number-unary-arithmetic-wrapper-trace-p proof-number-unary-wrapper-called
                              proof-number-dispatch-context-p)
           :do-not-induct t))
  :rule-classes nil)
