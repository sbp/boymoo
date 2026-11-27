(in-package "BOYMOO-PROOFS")

(include-book "arithmetic-returns")
(include-book "raw-return")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p proof-number-checked-block-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-heap-layout-p proof-preserved-heap-p proof-machine-limit
                     proof-frame-return-p proof-datum-return-p proof-reg-value-p
                     proof-number-order proof-number-formula-result-p proof-number-formula-contract-trace-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(local
 (defthm running-segment-cuts-at-link
   (implies (and (proof-segment-p steps (list link) world :cut after)
                 (not (proof-world-stop after)))
            (equal (proof-world-pc after) link))
   :hints (("Goal"
            :induct (proof-run steps (list link) world)
            :in-theory (e/d (proof-segment-p proof-run) (proof-step))))
   :rule-classes nil))

(local
 (defthm order-heap-is-running
   (implies (proof-heap-p world objects packages) (not (proof-world-stop world)))
   :hints (("Goal"
            :use proof-number-heap-machine-context
            :in-theory (disable proof-object-map-p proof-number-machine-stack-end)))
   :rule-classes nil))

(local
 (defthm first-order-keeps-heap-and-registers
   (let ((after (proof-number-execute-block *proof-number-first-order-code* world)))
     (implies (and (proof-heap-p world objects packages)
                   (not (eq (car (proof-world-machine world)) :svc)))
              (and (proof-preserved-heap-p nil world after objects objects packages)
                   (proof-heap-p after objects packages)
                   (proof-register-frame-p 30 (proof-number-numeric-clobbers) world after)
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world))))))
   :hints (("Goal"
            :use ((:instance proof-number-register-only-execution-preserves-heap
                             (instructions *proof-number-first-order-code*) (clobbers '(0)))
                  (:instance proof-number-preserved-heap-is-valid (may-intern nil) (before world) (old-objects objects)
                             (after (proof-number-execute-block *proof-number-first-order-code* world)))
                  (:instance proof-number-register-frame-allows-more-clobbers
                             (limit 30) (clobbers '(0)) (extended (proof-number-numeric-clobbers))
                             (before world) (after (proof-number-execute-block *proof-number-first-order-code* world))))
            :in-theory (e/d (proof-number-register-only-instruction-p proof-number-numeric-clobbers)
                            (proof-register-frame-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-first-order-datum-return
  (let* ((link (proof-world-reg 30 world))
         (after (proof-number-execute-block *proof-number-first-order-code* world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-checked-block-p *proof-number-first-order-code* (list link) world)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 (+ 8 (proof-world-pc world)))
                  (proof-reg-value-p 0 first world objects packages)
                  (proof-reg-value-p 1 second world objects packages))
             (and (proof-segment-p 3 (list link) world :cut after)
                  (proof-datum-return-p (proof-number-first-order first second) (proof-number-numeric-clobbers)
                                        t t nil world after objects objects packages))))
  :hints (("Goal"
           :use (proof-number-first-order-returns-word proof-number-first-order-returns-value
                 first-order-keeps-heap-and-registers order-heap-is-running
                 (:instance order-heap-is-running (world (proof-number-execute-block *proof-number-first-order-code* world)))
                 (:instance running-segment-cuts-at-link
                            (steps 3) (link (proof-world-reg 30 world))
                            (after (proof-number-execute-block *proof-number-first-order-code* world))))
           :in-theory (e/d (proof-datum-return-p proof-frame-return-p) (proof-register-frame-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-complex-order-datum-return
  (let* ((name "rt:c-compare")
         (args (list x y))
         (result (proof-number-order x y))
         (after (proof-number-formula-trace-after trace)))
    (implies (and (acl2-numberp x) (acl2-numberp y)
                  (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                                world objects)
                  (proof-number-formula-contract-trace-p
                   name args gcd grow growth-steps targets trace world grown objects grown-objects packages))
             (and (proof-segment-p (proof-number-formula-contract-steps name growth-steps trace)
                                   (list (proof-world-reg 30 world)) world :cut after)
                  (proof-datum-return-p result (proof-number-numeric-clobbers) t t nil
                                        world after objects (caddar (last trace)) packages))))
  :hints (("Goal"
           :use (proof-number-c-compare-formula
                 (:instance proof-number-generated-formula-datum-return
                            (name "rt:c-compare") (args (list x y)) (result (proof-number-order x y))))
           :in-theory (disable last)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-rational-cross-products-datum-return
  (let* ((name "rt:q-compare-products")
         (args (list x y))
         (result (proof-number-order x y))
         (after (proof-number-formula-trace-after trace)))
    (implies (and (rationalp x) (rationalp y)
                  (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                                world objects)
                  (proof-number-formula-contract-trace-p
                   name args gcd grow growth-steps targets trace world grown objects grown-objects packages))
             (and (proof-segment-p (proof-number-formula-contract-steps name growth-steps trace)
                                   (list (proof-world-reg 30 world)) world :cut after)
                  (proof-datum-return-p result (proof-number-numeric-clobbers) t t nil
                                        world after objects (caddar (last trace)) packages))))
  :hints (("Goal"
           :use (proof-number-q-compare-products-formula
                 (:instance proof-number-generated-formula-datum-return
                            (name "rt:q-compare-products") (args (list x y)) (result (proof-number-order x y))))
           :in-theory (disable last)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm rational-comparison-decision-is-register-only
   (proof-number-register-only-code-p (proof-number-rational-compare-path addresses world) nil)
   :hints (("Goal"
            :in-theory (enable proof-number-rational-compare-path proof-number-dispatch-path
                               proof-number-register-only-instruction-p)
            :do-not-induct t))))

(local
 (defthm rational-comparison-decision-keeps-layout
   (let ((after (proof-number-rational-compare-ready addresses world)))
     (implies (and (proof-heap-p world objects packages)
                   (proof-number-rational-compare-dispatch-trace-p a b addresses cuts world))
              (and (proof-preserved-heap-p nil world after objects objects packages)
                   (proof-register-frame-p 30 nil world after)
                   (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                   (equal (proof-machine-limit after) (proof-machine-limit world))
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world))))))
   :hints (("Goal"
            :use ((:instance proof-number-register-only-execution-preserves-heap
                             (clobbers nil) (instructions (proof-number-rational-compare-path addresses world)))
                  (:instance proof-number-register-only-block-effects
                             (clobbers nil) (instructions (proof-number-rational-compare-path addresses world))
                             (register 30)))
            :in-theory (e/d (proof-number-rational-compare-ready proof-number-rational-compare-dispatch-trace-p)
                            (proof-register-frame-p proof-number-register-only-code-p
                             proof-number-rational-compare-target assoc-equal))
            :do-not-induct t))
   :rule-classes nil))

(defund proof-number-rational-comparison-dispatched (types classifier world)
  (proof-number-pop-link-after (proof-number-binary-types-call-after types classifier world)))

(defthm proof-number-rational-comparison-prefix-keeps-context
  (let* ((link (proof-world-reg 30 world))
         (dispatch (proof-number-rational-comparison-dispatched types classifier world))
         (ready (proof-number-rational-compare-ready addresses dispatch)))
    (implies (and (not (complex-rationalp a)) (not (complex-rationalp b))
                  (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-binary-arithmetic-wrapper-trace-p types classifier a b world objects packages)
                  (proof-number-rational-compare-dispatch-trace-p a b addresses (list link) dispatch))
             (and (proof-number-dispatch-context-p world ready objects packages)
                  (rationalp (fix a)) (rationalp (fix b)))))
  :hints (("Goal"
           :use (proof-number-binary-arithmetic-wrapper-keeps-dispatch-context
                 (:instance proof-number-preserved-heap-is-valid (may-intern nil) (before world) (old-objects objects)
                            (after (proof-number-rational-comparison-dispatched types classifier world)))
                 (:instance rational-comparison-decision-keeps-layout
                            (cuts (list (proof-world-reg 30 world)))
                            (world (proof-number-rational-comparison-dispatched types classifier world)))
                 (:instance proof-number-rational-comparison-passes-operands
                            (cuts (list (proof-world-reg 30 world)))
                            (world (proof-number-rational-comparison-dispatched types classifier world)))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count (len (proof-number-rational-compare-path
                                         addresses (proof-number-rational-comparison-dispatched types classifier world))))
                            (cuts (list (proof-world-reg 30 world)))
                            (before (proof-number-rational-comparison-dispatched types classifier world))
                            (after (proof-number-rational-compare-ready
                                    addresses (proof-number-rational-comparison-dispatched types classifier world))))
                 (:instance proof-number-preserved-heaps-compose
                            (before world) (old-objects objects) (middle-objects objects)
                            (middle (proof-number-rational-comparison-dispatched types classifier world))
                            (after (proof-number-rational-compare-ready
                                    addresses (proof-number-rational-comparison-dispatched types classifier world))))
                 (:instance proof-number-register-frames-extend-and-compose
                            (limit 30) (clobbers (proof-number-numeric-clobbers))
                            (first-clobbers (proof-number-numeric-clobbers)) (last-clobbers nil)
                            (before world) (middle (proof-number-rational-comparison-dispatched types classifier world))
                            (after (proof-number-rational-compare-ready
                                    addresses (proof-number-rational-comparison-dispatched types classifier world)))))
           :in-theory (e/d (proof-number-rational-comparison-dispatched proof-number-dispatch-context-p
                            proof-number-numeric-clobbers)
                           (proof-register-frame-p proof-number-binary-types-p
                            proof-register-arguments-p fix))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-rational-comparison-datum-return
  (let* ((link (proof-world-reg 30 world))
         (dispatch (proof-number-rational-comparison-dispatched types classifier world))
         (ready (proof-number-rational-compare-ready addresses dispatch))
         (steps (+ 3 (proof-number-types-completion-steps nil classifier (proof-number-types-first-ready types world))
                   (len (proof-number-rational-compare-path addresses dispatch)) callee-steps))
         (order (proof-number-order (fix a) (fix b))))
    (implies (and (not (complex-rationalp a)) (not (complex-rationalp b))
                  (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-binary-arithmetic-wrapper-trace-p types classifier a b world objects packages)
                  (proof-number-rational-compare-dispatch-trace-p a b addresses (list link) dispatch)
                  (natp callee-steps)
                  (proof-segment-p callee-steps (list link) ready :cut after)
                  (proof-datum-return-p order (proof-number-numeric-clobbers) t t nil
                                        ready after objects new-objects packages))
             (and (proof-segment-p steps (list link) world :cut after)
                  (proof-datum-return-p order (proof-number-numeric-clobbers) t t nil
                                        world after objects new-objects packages))))
  :hints (("Goal"
           :use (proof-number-rational-comparison-returns-through-callee proof-number-rational-comparison-prefix-keeps-context
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (+ 3 (proof-number-types-completion-steps
                                         nil classifier (proof-number-types-first-ready types world))
                                      (len (proof-number-rational-compare-path
                                            addresses (proof-number-rational-comparison-dispatched types classifier world)))
                                      callee-steps))
                            (cuts (list (proof-world-reg 30 world))) (before world) (reason :cut))
                 (:instance proof-number-numeric-tail-transfer-returns
                            (datum (proof-number-order (fix a) (fix b))) (clobbers (proof-number-numeric-clobbers))
                            (before world) (middle (proof-number-rational-compare-ready
                                                   addresses
                                                   (proof-number-rational-comparison-dispatched types classifier world)))
                            (old-objects objects) (middle-objects objects) (objects new-objects)))
           :in-theory (e/d (proof-number-rational-comparison-dispatched proof-number-binary-arithmetic-wrapper-trace-p
                            proof-number-dispatch-context-p proof-number-numeric-clobbers)
                           (proof-register-frame-p proof-number-binary-types-call-trace-p fix))
           :do-not-induct t))
  :rule-classes nil)
