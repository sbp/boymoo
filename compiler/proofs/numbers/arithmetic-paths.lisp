(in-package "BOYMOO-PROOFS")

(include-book "arithmetic-public")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-heap-layout-p proof-preserved-heap-p
                     proof-frame-return-p proof-datum-return-p proof-reg-value-p
                     proof-runtime-pre-p proof-runtime-value proof-runtime-return-p
                     proof-number-selected-label proof-number-arithmetic-dispatch-input-p
                     proof-number-arithmetic-dispatch-entry proof-number-arithmetic-formula-labels
                     proof-number-arithmetic-dispatch-path proof-number-arithmetic-wrapper-trace-p
                     proof-number-arithmetic-decision-trace-p proof-number-formula-contract-trace-p
                     proof-number-formula-result-p proof-number-arithmetic-leaf-code
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defund proof-number-arithmetic-leaf-label-p (label)
  (member-equal label '("rt:zero" "rt:num-type-return" "rt:num-return-second")))

(defund proof-number-arithmetic-integer-label-p (label)
  (member-equal label '("rt:z-add-op" "rt:z-multiply-op" "rt:z-negate-op")))

(defthm proof-number-arithmetic-label-is-leaf-formula-or-integer
  (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
         (label (proof-number-selected-label entry world)))
    (implies (and entry (proof-number-arithmetic-dispatch-input-p primitive a b world objects packages))
             (or (proof-number-arithmetic-leaf-label-p label)
                 (member-equal label (proof-number-arithmetic-formula-labels primitive))
                 (proof-number-arithmetic-integer-label-p label))))
  :hints (("Goal"
           :use (proof-number-add-dispatch-by-value proof-number-multiply-dispatch-by-value
                 proof-number-negation-dispatch-by-value proof-number-reciprocal-dispatch-by-value)
           :in-theory (e/d (proof-number-arithmetic-dispatch-entry proof-number-arithmetic-dispatch-input-p
                            proof-number-arithmetic-binary-p proof-number-arithmetic-formula-labels
                            proof-number-arithmetic-leaf-label-p proof-number-arithmetic-integer-label-p)
                           (proof-number-binary-types-p fix))
           :cases ((eq primitive 'acl2::binary-+) (eq primitive 'acl2::binary-*)
                   (eq primitive 'acl2::unary--) (eq primitive 'acl2::unary-/))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-arithmetic-helper-trace-p
    (primitive a b addresses steps returned new-objects world objects packages
               program gcd grow growth-steps targets trace grown grown-objects)
  (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
         (label (proof-number-selected-label entry world))
         (link (proof-world-reg 30 world))
         (entered (proof-number-arithmetic-dispatch-after primitive addresses world))
         (result (boymoo-model::core-datum
                  (proof-runtime-value primitive (proof-number-arithmetic-source-args primitive a b) program))))
    (and (natp steps)
         (cond ((proof-number-arithmetic-leaf-label-p label)
                (let ((code (proof-number-arithmetic-leaf-code primitive world)))
                  (and (equal steps (len code))
                       (equal returned (proof-number-execute-block code entered))
                       (equal new-objects objects)
                       (not (eq (car (proof-world-machine entered)) :svc))
                       (unsigned-byte-p 64 (+ 4 (cdr (assoc-equal label addresses))))
                       (proof-number-checked-block-p code (list link) entered))))
               ((member-equal label (proof-number-arithmetic-formula-labels primitive))
                (and (equal steps (proof-number-formula-contract-steps label growth-steps trace))
                     (equal returned (proof-number-formula-trace-after trace))
                     (equal new-objects (caddar (last trace)))
                     (proof-number-save-interval-p
                      (- (boymoo-model::a64-sp (proof-world-machine entered)) 16) entered objects)
                     (proof-number-formula-contract-trace-p
                      label (proof-number-arithmetic-dispatch-args primitive a b)
                      gcd grow growth-steps targets trace entered grown objects grown-objects packages)))
               (t (and (proof-number-arithmetic-integer-label-p label)
                       (proof-segment-p steps (list link) entered :cut returned)
                       (proof-datum-return-p result (proof-number-numeric-clobbers) t t nil
                                             entered returned objects new-objects packages)))))))

(defthm proof-number-arithmetic-checked-choice-returns
  (let* ((steps (+ (len (proof-number-arithmetic-dispatch-path primitive addresses world)) helper-steps))
         (args (proof-number-arithmetic-source-args primitive a b)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-arithmetic-dispatch-input-p primitive a b world objects packages)
                  (proof-number-arithmetic-decision-trace-p primitive addresses world)
                  (proof-number-arithmetic-helper-trace-p
                   primitive a b addresses helper-steps returned new-objects world objects packages
                   program gcd grow growth-steps targets trace grown grown-objects))
             (and (proof-segment-p steps (list (proof-world-reg 30 world)) world :cut returned)
                  (proof-runtime-return-p primitive args program world returned objects new-objects packages))))
  :hints (("Goal"
           :use (proof-number-dispatched-leaf-runtime-return proof-number-dispatched-formula-runtime-return
                 proof-number-arithmetic-dispatch-returns-through-helper)
           :in-theory (e/d (proof-number-arithmetic-helper-trace-p proof-number-arithmetic-leaf-label-p)
                           (proof-number-arithmetic-decision-is-register-only assoc-equal last))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-public-general-arithmetic-checked-return
  (let* ((args (proof-number-arithmetic-source-args primitive a b))
         (arity (len args))
         (general-entry (proof-number-general-gate-after arity general world))
         (dispatch (proof-number-arithmetic-wrapper-after primitive types classifier general-entry))
         (dispatch-steps (+ (len (proof-number-arithmetic-dispatch-path primitive addresses dispatch)) helper-steps))
         (steps (+ 1 arity (proof-number-arithmetic-wrapper-steps primitive types classifier general-entry)
                   dispatch-steps)))
    (implies (and (proof-runtime-pre-p primitive args program labels base world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-general-gate-trace-p arity general world)
                  (proof-number-arithmetic-wrapper-trace-p primitive a b types classifier
                                                          general-entry objects packages)
                  (proof-number-arithmetic-decision-trace-p primitive addresses dispatch)
                  (proof-number-arithmetic-helper-trace-p
                   primitive a b addresses helper-steps returned new-objects dispatch objects packages
                   program gcd grow growth-steps targets trace grown grown-objects))
             (and (proof-segment-p steps (list (proof-world-reg 30 world)) world :cut returned)
                  (proof-runtime-return-p primitive args program world returned objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-runtime-entry-has-heap
                            (name primitive) (args (proof-number-arithmetic-source-args primitive a b)))
                 (:instance proof-number-general-tag-gate-reaches-runtime
                            (arity (len (proof-number-arithmetic-source-args primitive a b))) (register 30))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count (1+ (len (proof-number-arithmetic-source-args primitive a b))))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (after (proof-number-general-gate-after
                                    (len (proof-number-arithmetic-source-args primitive a b)) general world)))
                 (:instance proof-number-arithmetic-wrapper-supplies-dispatch-context
                            (world (proof-number-general-gate-after
                                    (len (proof-number-arithmetic-source-args primitive a b)) general world)))
                 (:instance proof-number-preserved-heap-is-valid
                            (may-intern nil) (old-objects objects)
                            (before (proof-number-general-gate-after
                                     (len (proof-number-arithmetic-source-args primitive a b)) general world))
                            (after (proof-number-arithmetic-wrapper-after
                                    primitive types classifier
                                    (proof-number-general-gate-after
                                     (len (proof-number-arithmetic-source-args primitive a b)) general world))))
                 (:instance proof-number-arithmetic-checked-choice-returns
                            (world (proof-number-arithmetic-wrapper-after
                                    primitive types classifier
                                    (proof-number-general-gate-after
                                     (len (proof-number-arithmetic-source-args primitive a b)) general world))))
                 (:instance proof-number-public-general-arithmetic-runtime-return
                            (after returned)
                            (dispatch-steps
                             (+ (len (proof-number-arithmetic-dispatch-path
                                      primitive addresses
                                      (proof-number-arithmetic-wrapper-after
                                       primitive types classifier
                                       (proof-number-general-gate-after
                                        (len (proof-number-arithmetic-source-args primitive a b)) general world))))
                                helper-steps))))
           :in-theory (e/d (proof-number-arithmetic-helper-trace-p proof-number-dispatch-context-p)
                           (proof-register-frame-p proof-number-arithmetic-decision-is-register-only
                            assoc-equal last))
           :do-not-induct t))
  :rule-classes nil)
