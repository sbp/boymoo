(in-package "BOYMOO-PROOFS")

(include-book "order-contracts")
(include-book "comparison-frame")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p proof-number-checked-block-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-preserved-heap-p proof-register-frame-p
                     proof-datum-return-p proof-runtime-pre-p proof-runtime-return-p
                     proof-number-order proof-number-formula-contract-trace-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor fix)))

(defund proof-number-rational-comparison-steps (types classifier addresses callee-steps world)
  (+ 3 (proof-number-types-completion-steps nil classifier (proof-number-types-first-ready types world))
     (len (proof-number-rational-compare-path
           addresses (proof-number-rational-comparison-dispatched types classifier world)))
     callee-steps))

(defund proof-number-rational-order-trace-p
    (a b types classifier addresses callee-steps world after objects new-objects packages
       gcd grow growth-steps targets trace grown grown-objects)
  (let* ((link (proof-world-reg 30 world))
         (dispatch (proof-number-rational-comparison-dispatched types classifier world))
         (ready (proof-number-rational-compare-ready addresses dispatch))
         (args (list (fix a) (fix b))))
    (and (not (complex-rationalp a)) (not (complex-rationalp b))
         (proof-number-binary-arithmetic-wrapper-trace-p types classifier a b world objects packages)
         (proof-number-rational-compare-dispatch-trace-p a b addresses (list link) dispatch)
         (if (equal (proof-number-rational-compare-target a b) "rt:z-compare")
             (and (natp callee-steps)
                  (proof-segment-p callee-steps (list link) ready :cut after)
                  (proof-datum-return-p (proof-number-order (fix a) (fix b))
                                        (proof-number-numeric-clobbers) t t nil
                                        ready after objects new-objects packages))
           (and (equal callee-steps (proof-number-formula-contract-steps "rt:q-compare-products" growth-steps trace))
                (equal after (proof-number-formula-trace-after trace))
                (equal new-objects (caddar (last trace)))
                (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine ready)) 16)
                                              ready objects)
                (proof-number-formula-contract-trace-p
                 "rt:q-compare-products" args gcd grow growth-steps targets trace
                 ready grown objects grown-objects packages))))))

(defthm proof-number-rational-comparison-checked-datum-return
  (implies (and (proof-heap-p world objects packages)
                (proof-number-world-byte-keys-p world)
                (proof-number-rational-order-trace-p
                 a b types classifier addresses callee-steps world after objects new-objects packages
                 gcd grow growth-steps targets trace grown grown-objects))
           (and (natp (proof-number-rational-comparison-steps types classifier addresses callee-steps world))
                (proof-segment-p (proof-number-rational-comparison-steps types classifier addresses callee-steps world)
                                 (list (proof-world-reg 30 world)) world :cut after)
                (proof-datum-return-p (proof-number-order (fix a) (fix b))
                                      (proof-number-numeric-clobbers) t t nil
                                      world after objects new-objects packages)))
  :hints (("Goal"
           :use (proof-number-rational-comparison-prefix-keeps-context
                 proof-number-rational-comparison-datum-return
                 (:instance proof-number-preserved-heap-is-valid
                            (may-intern nil) (before world) (old-objects objects)
                            (after (proof-number-rational-compare-ready
                                    addresses (proof-number-rational-comparison-dispatched types classifier world))))
                 (:instance proof-number-rational-cross-products-datum-return
                            (x (fix a)) (y (fix b))
                            (world (proof-number-rational-compare-ready
                                    addresses (proof-number-rational-comparison-dispatched types classifier world))))
                 (:instance proof-number-formula-contract-step-count-is-natural
                            (name "rt:q-compare-products") (args (list (fix a) (fix b)))
                            (world (proof-number-rational-compare-ready
                                    addresses (proof-number-rational-comparison-dispatched types classifier world)))))
           :in-theory (e/d (proof-number-rational-order-trace-p proof-number-rational-comparison-steps
                            proof-number-dispatch-context-p)
                           (last proof-number-rational-compare-path proof-number-rational-comparison-dispatched))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-less-order-trace-p
    (complex-case x y types classifier addresses callee-steps ready returned objects new-objects packages
                  gcd grow growth-steps targets trace grown grown-objects rational-steps)
  (if complex-case
      (and (equal callee-steps (proof-number-formula-contract-steps "rt:c-compare" growth-steps trace))
           (equal returned (proof-number-formula-trace-after trace))
           (equal new-objects (caddar (last trace)))
           (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine ready)) 16) ready objects)
           (proof-number-formula-contract-trace-p
            "rt:c-compare" (list x y) gcd grow growth-steps targets trace
            ready grown objects grown-objects packages))
    (and (equal callee-steps (proof-number-rational-comparison-steps types classifier addresses rational-steps ready))
         (proof-number-rational-order-trace-p
          x y types classifier addresses rational-steps ready returned objects new-objects packages
          gcd grow growth-steps targets trace grown grown-objects))))

(local
 (defthm order-fix-is-numeric-and-idempotent
   (and (acl2-numberp (fix x)) (equal (fix (fix x)) (fix x)))
   :hints (("Goal" :in-theory (enable fix)))))

(local
 (defthm less-order-trace-returns
   (implies (and (proof-heap-p ready objects packages)
                 (proof-number-world-byte-keys-p ready)
                 (proof-number-less-order-trace-p
                  complex-case (fix a) (fix b) types classifier addresses callee-steps
                  ready returned objects new-objects packages
                  gcd grow growth-steps targets trace grown grown-objects rational-steps))
            (and (natp callee-steps)
                 (proof-segment-p callee-steps (list (proof-world-reg 30 ready)) ready :cut returned)
                 (proof-datum-return-p (proof-number-order (fix a) (fix b))
                                       (proof-number-numeric-clobbers) t t nil
                                       ready returned objects new-objects packages)))
   :hints (("Goal"
            :use ((:instance proof-number-complex-order-datum-return (world ready) (x (fix a)) (y (fix b)))
                  (:instance proof-number-formula-contract-step-count-is-natural
                             (world ready) (name "rt:c-compare") (args (list (fix a) (fix b))))
                  (:instance proof-number-rational-comparison-checked-datum-return
                             (world ready) (after returned) (a (fix a)) (b (fix b)) (callee-steps rational-steps)))
            :in-theory (e/d (proof-number-less-order-trace-p) (last))
            :do-not-induct t))
   :rule-classes nil))

(defund proof-number-general-less-checked-trace-p
    (a b types classifier rational complex yes no callee-steps world returned objects new-objects packages
       addresses gcd grow growth-steps targets trace grown grown-objects rational-steps)
  (let* ((link (proof-world-reg 30 world))
         (completed (proof-number-binary-types-call-after types classifier world))
         (machine (proof-world-machine completed))
         (pc (proof-world-pc completed))
         (complex-case (equal (proof-world-reg 3 completed) 5))
         (target (if complex-case complex rational))
         (code (proof-number-less-compare-path pc rational complex complex-case))
         (ready (proof-number-less-compare-ready rational complex completed))
         (continuation (+ pc (if complex-case 20 12)))
         (sp (boymoo-model::a64-sp machine))
         (end (proof-number-machine-stack-end ready))
         (order (proof-number-order (fix a) (fix b))))
    (and (proof-number-binary-wrapper-save-intervals-p types world objects)
         (proof-number-binary-types-call-trace-p types classifier (list link) a b world objects packages)
         (not (eq (car machine) :svc))
         (unsigned-byte-p 64 (+ pc 20))
         (unsigned-byte-p 64 target)
         (proof-number-checked-block-p code (list target) completed)
         (proof-number-checked-block-p code (list link) completed)
         (<= (+ 16 sp) end) (<= end (expt 2 64))
         (proof-number-cut-free-prefix-p callee-steps (list continuation link) ready)
         (proof-number-less-order-trace-p
          complex-case (fix a) (fix b) types classifier addresses callee-steps ready returned
          objects new-objects packages gcd grow growth-steps targets trace grown grown-objects rational-steps)
         (not (eq (car (proof-world-machine returned)) :svc))
         (proof-number-checked-block-p (proof-number-less-resume-code complex-case) (list link) returned)
         (proof-number-less-tail-code-p order link yes no (proof-number-less-resumed complex-case returned)))))

(local
 (defthm less-call-registers
   (proof-number-register-only-code-p (proof-number-less-compare-path pc rational complex complex-case) '(30))
   :hints (("Goal" :in-theory (enable proof-number-less-compare-path
                                     proof-number-register-only-instruction-p)))))

(local
 (defthm less-call-keeps-heap-and-byte-keys
   (let* ((completed (proof-number-binary-types-call-after types classifier world))
          (ready (proof-number-less-compare-ready rational complex completed)))
     (implies (and (proof-heap-p world objects packages)
                   (proof-number-world-byte-keys-p world)
                   (proof-number-general-less-checked-trace-p
                    a b types classifier rational complex yes no callee-steps world returned
                    objects new-objects packages addresses gcd grow growth-steps targets trace grown grown-objects
                    rational-steps))
              (and (proof-heap-p ready objects packages)
                   (proof-number-world-byte-keys-p ready)
                   (equal (proof-world-reg 30 ready)
                          (+ (proof-world-pc completed) (if (equal (proof-world-reg 3 completed) 5) 20 12))))))
   :hints (("Goal"
            :use ((:instance proof-number-binary-wrapper-preserves-heap-while-saved
                             (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-number-binary-wrapper-completes (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-number-less-comparator-receives-completed-values
                             (cuts (list (proof-world-reg 30 world)))
                             (world (proof-number-binary-types-call-after types classifier world)))
                  (:instance proof-number-preserved-heap-is-valid
                             (may-intern nil) (old-objects objects)
                             (before (proof-number-binary-types-call-after types classifier world))
                             (after (proof-number-less-compare-ready
                                     rational complex (proof-number-binary-types-call-after types classifier world))))
                  (:instance proof-number-register-only-execution-preserves-heap
                             (clobbers '(30)) (world (proof-number-binary-types-call-after types classifier world))
                             (instructions
                              (proof-number-less-compare-path
                               (proof-world-pc (proof-number-binary-types-call-after types classifier world))
                               rational complex (equal (proof-world-reg 3 (proof-number-binary-types-call-after
                                                                           types classifier world)) 5))))
                  (:instance proof-number-exact-prefix-preserves-byte-keys
                             (count 3) (cuts (list (proof-world-reg 30 world)))
                             (before (proof-number-binary-types-call-after types classifier world))
                             (after (proof-number-less-compare-ready
                                     rational complex (proof-number-binary-types-call-after types classifier world)))))
            :in-theory (e/d (proof-number-general-less-checked-trace-p proof-number-less-compare-ready)
                            (proof-number-less-compare-path proof-number-register-only-code-p
                             proof-register-arguments-p proof-number-binary-types-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-general-less-checked-trace-gives-return-trace
  (implies (and (proof-heap-p world objects packages)
                (proof-number-world-byte-keys-p world)
                (proof-number-general-less-checked-trace-p
                 a b types classifier rational complex yes no callee-steps world returned objects new-objects packages
                 addresses gcd grow growth-steps targets trace grown grown-objects rational-steps))
           (proof-number-general-less-trace-p a b types classifier rational complex yes no callee-steps
                                               world returned objects new-objects packages))
  :hints (("Goal"
           :use (less-call-keeps-heap-and-byte-keys
                 (:instance less-order-trace-returns
                            (ready (proof-number-less-compare-ready
                                    rational complex (proof-number-binary-types-call-after types classifier world)))
                            (complex-case (equal (proof-world-reg 3 (proof-number-binary-types-call-after
                                                                     types classifier world)) 5))))
           :in-theory (enable proof-number-general-less-checked-trace-p proof-number-general-less-trace-p
                              proof-number-less-comparison-trace-p proof-number-machine-stack-end)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-public-general-less-checked-runtime-return
  (let* ((entry (proof-number-general-gate-after 2 general world))
         (after (proof-number-general-less-after a b types classifier yes no returned entry))
         (steps (proof-number-general-less-steps a b types classifier callee-steps entry)))
    (implies (and (proof-runtime-pre-p '< (list a b) program labels base world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-general-gate-trace-p 2 general world)
                  (proof-number-general-less-checked-trace-p
                   a b types classifier rational complex yes no callee-steps entry returned objects new-objects packages
                   addresses gcd grow growth-steps targets trace grown grown-objects rational-steps))
             (and (proof-segment-p (+ 3 steps) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p '< (list a b) program world after objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-runtime-entry-has-heap (name '<) (args (list a b)))
                 (:instance proof-number-general-tag-gate-reaches-runtime (arity 2) (register 30))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count 3) (cuts (list (proof-world-reg 30 world))) (before world)
                            (after (proof-number-general-gate-after 2 general world)))
                 (:instance proof-number-general-less-checked-trace-gives-return-trace
                            (world (proof-number-general-gate-after 2 general world)))
                 proof-number-public-general-less-runtime-return)
           :do-not-induct t))
  :rule-classes nil)
