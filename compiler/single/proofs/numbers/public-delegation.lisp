(in-package "BOYMOO-PROOFS")

(include-book "wrapper-frames")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p proof-number-checked-block-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-runtime-pre-p proof-runtime-return-p proof-runtime-value proof-runtime-entry
                     proof-datum-return-p proof-frame-return-p proof-register-frame-p
                     proof-preserved-heap-p proof-heap-p proof-heap-layout-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defthm proof-number-runtime-entry-has-heap
  (implies (proof-runtime-pre-p name args program labels base world objects packages)
           (proof-heap-p world objects packages))
  :hints (("Goal"
           :in-theory (e/d (proof-runtime-pre-p)
                           (proof-label-address proof-register-arguments-p proof-program-packages-p))))
  :rule-classes nil)

(defthm proof-number-numeric-runtime-return-contract
  (let ((result (proof-runtime-value name args program)))
    (implies (member-eq name '(acl2::binary-+ acl2::binary-* acl2::unary-- acl2::unary-/ < complex))
             (equal (proof-runtime-return-p name args program before after old-objects objects packages)
                    (and (boymoo-model::core-value-p result)
                         (proof-datum-return-p (boymoo-model::core-datum result)
                                               (proof-number-numeric-clobbers) t t nil
                                               before after old-objects objects packages)))))
  :hints (("Goal"
           :in-theory (enable proof-runtime-return-p proof-number-numeric-clobbers
                              proof-runtime-allocates-p proof-runtime-clobbers)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-numeric-tail-transfer-returns
  (implies (and (proof-heap-p before old-objects packages)
                (proof-preserved-heap-p nil before middle old-objects middle-objects packages)
                (proof-register-frame-p 30 clobbers before middle)
                (subsetp-equal clobbers (proof-number-numeric-clobbers))
                (equal (proof-machine-limit before) (proof-machine-limit middle))
                (equal (boymoo-model::a64-sp (proof-world-machine before))
                       (boymoo-model::a64-sp (proof-world-machine middle)))
                (equal (proof-world-reg 30 before) (proof-world-reg 30 middle))
                (proof-number-world-byte-keys-p before)
                (proof-number-world-byte-keys-p after)
                (proof-datum-return-p datum (proof-number-numeric-clobbers) t t nil
                                      middle after middle-objects objects packages))
           (proof-datum-return-p datum (proof-number-numeric-clobbers) t t nil
                                 before after old-objects objects packages))
  :hints (("Goal"
           :use ((:instance proof-number-heap-machine-context (world before) (objects old-objects))
                 proof-number-preserved-heaps-compose
                 (:instance proof-number-register-frames-extend-and-compose
                            (limit 30) (first-clobbers clobbers)
                            (last-clobbers (proof-number-numeric-clobbers))
                            (clobbers (proof-number-numeric-clobbers))))
           :in-theory (e/d (proof-datum-return-p proof-frame-return-p)
                           (proof-reg-value-p subsetp-equal))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-public-tag-gate-compose-return
  (let* ((arity (len args))
         (middle (proof-number-general-gate-after arity general world))
         (link (proof-world-reg 30 world)))
    (implies (and (member-eq name '(acl2::binary-+ acl2::binary-* acl2::unary-- acl2::unary-/ <))
                  (proof-runtime-pre-p name args program labels base world old-objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-general-gate-trace-p arity general world)
                  (natp steps)
                  (proof-segment-p steps (list link) middle :cut after)
                  (proof-runtime-return-p name args program middle after old-objects objects packages))
             (and (proof-segment-p (+ 1 arity steps) (list link) world :cut after)
                  (proof-runtime-return-p name args program world after old-objects objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-runtime-entry-has-heap (objects old-objects))
                 (:instance proof-number-general-tag-gate-reaches-runtime
                            (arity (len args)) (objects old-objects) (register 30))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (1+ (len args))) (suffix steps) (cuts (list (proof-world-reg 30 world)))
                            (before world) (middle (proof-number-general-gate-after (len args) general world))
                            (reason :cut))
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (+ 1 (len args) steps)) (cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut))
                 (:instance proof-number-numeric-runtime-return-contract (before world))
                 (:instance proof-number-numeric-runtime-return-contract
                            (before (proof-number-general-gate-after (len args) general world)))
                 (:instance proof-number-numeric-tail-transfer-returns
                            (datum (boymoo-model::core-datum (proof-runtime-value name args program)))
                            (before world) (middle (proof-number-general-gate-after (len args) general world))
                            (clobbers '(2)) (middle-objects old-objects)))
           :in-theory (enable proof-number-numeric-clobbers)
           :do-not-induct t))
  :rule-classes nil)
