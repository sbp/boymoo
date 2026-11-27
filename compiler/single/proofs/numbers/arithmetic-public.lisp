(in-package "BOYMOO-PROOFS")

(include-book "arithmetic-returns")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-heap-layout-p proof-preserved-heap-p
                     proof-frame-return-p proof-datum-return-p proof-reg-value-p
                     proof-runtime-pre-p proof-runtime-value proof-runtime-return-p
                     proof-number-arithmetic-dispatch-input-p proof-number-binary-types-p
                     proof-number-binary-arithmetic-wrapper-trace-p proof-number-unary-arithmetic-wrapper-trace-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defund proof-number-arithmetic-wrapper-after (primitive types classifier world)
  (proof-number-pop-link-after
   (if (proof-number-arithmetic-binary-p primitive)
       (proof-number-binary-types-call-after types classifier world)
     (proof-number-unary-wrapper-called classifier world))))

(defund proof-number-arithmetic-wrapper-steps (primitive types classifier world)
  (+ 3 (if (proof-number-arithmetic-binary-p primitive)
           (proof-number-types-completion-steps nil classifier (proof-number-types-first-ready types world))
         (len (proof-number-classifier-path (proof-number-types-first-ready classifier world))))))

(defund proof-number-arithmetic-wrapper-trace-p (primitive a b types classifier world objects packages)
  (and (proof-number-arithmetic-dispatch-entry primitive)
       (if (proof-number-arithmetic-binary-p primitive)
           (proof-number-binary-arithmetic-wrapper-trace-p types classifier a b world objects packages)
         (and (proof-reg-value-p 0 a world objects packages)
              (proof-number-unary-arithmetic-wrapper-trace-p classifier world objects)))))

(defthm proof-number-arithmetic-wrapper-supplies-dispatch-context
  (let* ((after (proof-number-arithmetic-wrapper-after primitive types classifier world))
         (steps (proof-number-arithmetic-wrapper-steps primitive types classifier world))
         (link (proof-world-reg 30 world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-arithmetic-wrapper-trace-p primitive a b types classifier world objects packages))
             (and (proof-number-exact-prefix-p steps (list link) world after)
                  (proof-number-dispatch-context-p world after objects packages)
                  (proof-number-arithmetic-dispatch-input-p primitive a b after objects packages))))
  :hints (("Goal"
           :use (proof-number-binary-arithmetic-wrapper-keeps-dispatch-context
                 proof-number-unary-arithmetic-wrapper-keeps-dispatch-context)
           :in-theory (enable proof-number-arithmetic-wrapper-trace-p proof-number-arithmetic-wrapper-after
                              proof-number-arithmetic-wrapper-steps proof-number-arithmetic-dispatch-input-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-general-arithmetic-returns-through-dispatch
  (let* ((middle (proof-number-arithmetic-wrapper-after primitive types classifier world))
         (steps (proof-number-arithmetic-wrapper-steps primitive types classifier world))
         (link (proof-world-reg 30 world))
         (args (proof-number-arithmetic-source-args primitive a b)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-arithmetic-wrapper-trace-p primitive a b types classifier world objects packages)
                  (natp dispatch-steps)
                  (proof-segment-p dispatch-steps (list link) middle :cut after)
                  (proof-runtime-return-p primitive args program middle after objects new-objects packages))
             (and (proof-segment-p (+ steps dispatch-steps) (list link) world :cut after)
                  (proof-runtime-return-p primitive args program world after objects new-objects packages))))
  :hints (("Goal"
           :use (proof-number-arithmetic-wrapper-supplies-dispatch-context
                 proof-number-arithmetic-primitive-and-source-result
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (proof-number-arithmetic-wrapper-steps primitive types classifier world))
                            (suffix dispatch-steps) (cuts (list (proof-world-reg 30 world))) (before world)
                            (middle (proof-number-arithmetic-wrapper-after primitive types classifier world))
                            (reason :cut))
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (+ (proof-number-arithmetic-wrapper-steps primitive types classifier world)
                                      dispatch-steps))
                            (cuts (list (proof-world-reg 30 world))) (before world) (reason :cut))
                 (:instance proof-number-numeric-runtime-return-contract
                            (name primitive) (args (proof-number-arithmetic-source-args primitive a b))
                            (before (proof-number-arithmetic-wrapper-after primitive types classifier world))
                            (old-objects objects) (objects new-objects))
                 (:instance proof-number-numeric-runtime-return-contract
                            (name primitive) (args (proof-number-arithmetic-source-args primitive a b))
                            (before world) (old-objects objects) (objects new-objects))
                 (:instance proof-number-numeric-tail-transfer-returns
                            (datum (boymoo-model::core-datum
                                    (proof-runtime-value
                                     primitive (proof-number-arithmetic-source-args primitive a b) program)))
                            (before world) (middle (proof-number-arithmetic-wrapper-after primitive types classifier world))
                            (old-objects objects) (middle-objects objects) (objects new-objects)
                            (clobbers (proof-number-numeric-clobbers))))
           :in-theory (e/d (proof-number-arithmetic-wrapper-trace-p proof-number-dispatch-context-p
                            proof-number-numeric-clobbers)
                           (proof-register-frame-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-public-general-arithmetic-runtime-return
  (let* ((args (proof-number-arithmetic-source-args primitive a b))
         (arity (len args))
         (middle (proof-number-general-gate-after arity general world))
         (link (proof-world-reg 30 world))
         (steps (+ (proof-number-arithmetic-wrapper-steps primitive types classifier middle) dispatch-steps))
         (dispatch (proof-number-arithmetic-wrapper-after primitive types classifier middle)))
    (implies (and (proof-runtime-pre-p primitive args program labels base world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-general-gate-trace-p arity general world)
                  (proof-number-arithmetic-wrapper-trace-p primitive a b types classifier
                                                          middle objects packages)
                  (natp dispatch-steps)
                  (proof-segment-p dispatch-steps (list link) dispatch :cut after)
                  (proof-runtime-return-p primitive args program dispatch after objects new-objects packages))
             (and (proof-segment-p (+ 1 arity steps) (list link) world :cut after)
                  (proof-runtime-return-p primitive args program world after objects new-objects packages))))
  :hints (("Goal"
           :use (proof-number-arithmetic-primitive-and-source-result
                 (:instance proof-number-runtime-entry-has-heap
                            (name primitive) (args (proof-number-arithmetic-source-args primitive a b)))
                 (:instance proof-number-general-tag-gate-reaches-runtime
                            (arity (len (proof-number-arithmetic-source-args primitive a b))) (register 30))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count (1+ (len (proof-number-arithmetic-source-args primitive a b))))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (after (proof-number-general-gate-after
                                    (len (proof-number-arithmetic-source-args primitive a b)) general world)))
                 (:instance proof-number-general-arithmetic-returns-through-dispatch
                            (world (proof-number-general-gate-after
                                    (len (proof-number-arithmetic-source-args primitive a b)) general world)))
                 (:instance proof-number-public-tag-gate-compose-return
                            (name primitive) (args (proof-number-arithmetic-source-args primitive a b))
                            (old-objects objects) (objects new-objects)
                            (steps (+ (proof-number-arithmetic-wrapper-steps
                                       primitive types classifier
                                       (proof-number-general-gate-after
                                        (len (proof-number-arithmetic-source-args primitive a b)) general world))
                                      dispatch-steps))))
           :in-theory (e/d (proof-number-arithmetic-wrapper-trace-p proof-number-arithmetic-wrapper-steps
                            proof-number-types-completion-steps)
                           (proof-number-classifier-path proof-register-frame-p fix))
           :do-not-induct t))
  :rule-classes nil)
