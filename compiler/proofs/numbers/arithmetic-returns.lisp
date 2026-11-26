(in-package "BOYMOO-PROOFS")

(include-book "arithmetic-dispatch")
(include-book "formula-contracts")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-heap-layout-p proof-preserved-heap-p
                     proof-frame-return-p proof-datum-return-p proof-reg-value-p
                     proof-runtime-value proof-runtime-return-p proof-number-arithmetic-dispatch-path
                     proof-number-selected-label proof-number-arithmetic-dispatch-input-p
                     proof-number-arithmetic-decision-trace-p proof-number-formula-contract-trace-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(local
 (defthm leaf-result-code-is-register-only
   (implies (member-equal leaf '("rt:zero" "rt:num-type-return" "rt:num-return-second"))
            (proof-number-register-only-code-p
             (cdr (assoc-equal leaf *proof-number-leaf-returns*)) '(0)))
   :hints (("Goal"
            :in-theory (enable proof-number-register-only-instruction-p)
            :do-not-induct t))))

(local
 (defthm register-only-parts-give-register-only-code
   (implies (and (proof-number-register-only-code-p first clobbers)
                 (proof-number-register-only-code-p second clobbers))
            (proof-number-register-only-code-p (append first second) clobbers))
   :hints (("Goal" :induct (len first)))))

(local
 (defthm arithmetic-leaf-execution-keeps-heap-and-frame
   (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
          (label (proof-number-selected-label entry world))
          (code (proof-number-arithmetic-leaf-code primitive world))
          (after (proof-number-execute-block code (proof-number-arithmetic-dispatch-after primitive addresses world))))
     (implies (and (proof-heap-p world objects packages)
                   (not (eq (car (proof-world-machine world)) :svc))
                   (member-equal label '("rt:zero" "rt:num-type-return" "rt:num-return-second")))
              (and (proof-preserved-heap-p nil world after objects objects packages)
                   (proof-heap-p after objects packages)
                   (proof-register-frame-p 30 (proof-number-numeric-clobbers) world after)
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world))))))
   :hints (("Goal"
            :use ((:instance proof-number-register-only-execution-preserves-heap
                             (clobbers '(0))
                             (instructions (append (proof-number-arithmetic-dispatch-path primitive addresses world)
                                                   (proof-number-arithmetic-leaf-code primitive world))))
                  (:instance proof-number-preserved-heap-is-valid (may-intern nil)
                             (before world) (old-objects objects)
                             (after (proof-number-execute-block
                                     (proof-number-arithmetic-leaf-code primitive world)
                                     (proof-number-arithmetic-dispatch-after primitive addresses world))))
                  (:instance proof-number-register-frame-allows-more-clobbers
                             (limit 30) (clobbers '(0)) (extended (proof-number-numeric-clobbers))
                             (before world)
                             (after (proof-number-execute-block
                                     (proof-number-arithmetic-leaf-code primitive world)
                                     (proof-number-arithmetic-dispatch-after primitive addresses world)))))
            :in-theory (e/d (proof-number-arithmetic-dispatch-after proof-number-arithmetic-leaf-code
                             proof-number-numeric-clobbers)
                            (proof-number-register-only-code-p proof-register-frame-p assoc-equal))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm arithmetic-leaf-execution-produces-source-value
   (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
          (label (proof-number-selected-label entry world))
          (target (cdr (assoc-equal label addresses)))
          (link (proof-world-reg 30 world))
          (path (proof-number-arithmetic-dispatch-path primitive addresses world))
          (entered (proof-number-arithmetic-dispatch-after primitive addresses world))
          (code (proof-number-arithmetic-leaf-code primitive world))
          (after (proof-number-execute-block code entered))
          (args (proof-number-arithmetic-source-args primitive a b))
          (result (boymoo-model::core-datum (proof-runtime-value primitive args program))))
     (implies (and (proof-number-arithmetic-dispatch-input-p primitive a b world objects packages)
                   (proof-number-arithmetic-decision-trace-p primitive addresses world)
                   (member-equal label '("rt:zero" "rt:num-type-return" "rt:num-return-second"))
                   (unsigned-byte-p 64 (+ 4 target))
                   (not (eq (car (proof-world-machine entered)) :svc))
                   (proof-number-checked-block-p code (list link) entered))
              (and (proof-segment-p (+ (len path) (len code)) (list link) world :cut after)
                   (equal (proof-world-pc after) link)
                   (proof-reg-value-p 0 result after objects packages))))
   :hints (("Goal"
            :use proof-number-dispatched-leaf-returns-source-value
            :in-theory (e/d (proof-number-arithmetic-decision-trace-p proof-number-arithmetic-dispatch-after)
                            (proof-number-arithmetic-decision-is-register-only assoc-equal))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm arithmetic-decision-has-primitive-and-initial-machine
   (implies (proof-number-arithmetic-decision-trace-p primitive addresses world)
            (and (proof-number-arithmetic-dispatch-entry primitive)
                 (not (eq (car (proof-world-machine world)) :svc))))
   :hints (("Goal" :in-theory (enable proof-number-arithmetic-decision-trace-p)))
   :rule-classes nil))

(local
 (defthm valid-heap-world-is-running
   (implies (proof-heap-p world objects packages)
            (not (proof-world-stop world)))
   :hints (("Goal"
            :use proof-number-heap-machine-context
            :in-theory (disable proof-object-map-p proof-number-machine-stack-end)))
   :rule-classes nil))

(defthm proof-number-dispatched-leaf-runtime-return
  (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
         (label (proof-number-selected-label entry world))
         (target (cdr (assoc-equal label addresses)))
         (link (proof-world-reg 30 world))
         (path (proof-number-arithmetic-dispatch-path primitive addresses world))
         (entered (proof-number-arithmetic-dispatch-after primitive addresses world))
         (code (proof-number-arithmetic-leaf-code primitive world))
         (after (proof-number-execute-block code entered))
         (args (proof-number-arithmetic-source-args primitive a b)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-arithmetic-dispatch-input-p primitive a b world objects packages)
                  (proof-number-arithmetic-decision-trace-p primitive addresses world)
                  (member-equal label '("rt:zero" "rt:num-type-return" "rt:num-return-second"))
                  (unsigned-byte-p 64 (+ 4 target))
                  (not (eq (car (proof-world-machine entered)) :svc))
                  (proof-number-checked-block-p code (list link) entered))
             (and (proof-segment-p (+ (len path) (len code)) (list link) world :cut after)
                  (proof-runtime-return-p primitive args program world after objects objects packages))))
  :hints (("Goal"
           :use (arithmetic-leaf-execution-produces-source-value
                 arithmetic-decision-has-primitive-and-initial-machine
                 arithmetic-leaf-execution-keeps-heap-and-frame
                 proof-number-arithmetic-primitive-and-source-result
                 valid-heap-world-is-running
                 (:instance valid-heap-world-is-running
                            (world (proof-number-execute-block
                                    (proof-number-arithmetic-leaf-code primitive world)
                                    (proof-number-arithmetic-dispatch-after primitive addresses world))))
                 (:instance proof-number-numeric-runtime-return-contract
                            (name primitive) (args (proof-number-arithmetic-source-args primitive a b))
                            (before world) (old-objects objects)
                            (after (proof-number-execute-block
                                    (proof-number-arithmetic-leaf-code primitive world)
                                    (proof-number-arithmetic-dispatch-after primitive addresses world)))))
           :in-theory (e/d (proof-datum-return-p proof-frame-return-p)
                           (proof-register-frame-p proof-number-arithmetic-decision-is-register-only
                            proof-world-page-size proof-streams-preserved-p
                            proof-object-map-p proof-runtime-clobbers
                            proof-number-arithmetic-leaf-code assoc-equal))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm formula-step-total-is-natural
   (natp (proof-number-formula-trace-steps calls trace))
   :hints (("Goal" :induct (proof-number-formula-trace-steps calls trace)))
   :rule-classes :type-prescription))

(defthm proof-number-formula-contract-step-count-is-natural
  (implies (proof-number-formula-contract-trace-p
            name args gcd grow growth-steps targets trace world grown objects grown-objects packages)
           (natp (proof-number-formula-contract-steps name growth-steps trace)))
  :hints (("Goal"
           :in-theory (e/d (proof-number-formula-contract-trace-p proof-number-formula-return-trace-p
                            proof-number-formula-contract-steps)
                           (proof-number-formula-body-trace-p proof-number-formula-calls
                            proof-number-formula-trace-steps last))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-dispatched-formula-runtime-return
  (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
         (label (proof-number-selected-label entry world))
         (args (proof-number-arithmetic-dispatch-args primitive a b))
         (source-args (proof-number-arithmetic-source-args primitive a b))
         (entered (proof-number-arithmetic-dispatch-after primitive addresses world))
         (link (proof-world-reg 30 world))
         (path (proof-number-arithmetic-dispatch-path primitive addresses world))
         (steps (proof-number-formula-contract-steps label growth-steps trace))
         (after (proof-number-formula-trace-after trace)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-arithmetic-decision-trace-p primitive addresses world)
                  (proof-number-arithmetic-dispatch-input-p primitive a b world objects packages)
                  (member-equal label (proof-number-arithmetic-formula-labels primitive))
                  (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine entered)) 16)
                                                entered objects)
                  (proof-number-formula-contract-trace-p
                   label args gcd grow growth-steps targets trace entered grown objects grown-objects packages))
             (and (proof-segment-p (+ (len path) steps) (list link) world :cut after)
                  (proof-runtime-return-p primitive source-args program world after
                                          objects (caddar (last trace)) packages))))
  :hints (("Goal"
           :use (proof-number-selected-formula-refines-source
                 (:instance proof-number-arithmetic-decision-keeps-dispatch-context (register 30))
                 (:instance proof-number-preserved-heap-is-valid
                            (may-intern nil) (before world) (old-objects objects)
                            (after (proof-number-arithmetic-dispatch-after primitive addresses world)))
                 (:instance proof-number-generated-formula-datum-return
                            (name (proof-number-selected-label (proof-number-arithmetic-dispatch-entry primitive) world))
                            (args (proof-number-arithmetic-dispatch-args primitive a b))
                            (result (boymoo-model::core-datum
                                     (proof-runtime-value
                                      primitive (proof-number-arithmetic-source-args primitive a b) program)))
                            (world (proof-number-arithmetic-dispatch-after primitive addresses world)))
                 (:instance proof-number-formula-contract-step-count-is-natural
                            (name (proof-number-selected-label (proof-number-arithmetic-dispatch-entry primitive) world))
                            (args (proof-number-arithmetic-dispatch-args primitive a b))
                            (world (proof-number-arithmetic-dispatch-after primitive addresses world)))
                 (:instance proof-number-arithmetic-dispatch-returns-through-helper
                            (helper-steps (proof-number-formula-contract-steps
                                           (proof-number-selected-label
                                            (proof-number-arithmetic-dispatch-entry primitive) world)
                                           growth-steps trace))
                            (returned (proof-number-formula-trace-after trace))
                            (new-objects (caddar (last trace)))))
           :in-theory (e/d (proof-number-dispatch-context-p)
                           (proof-register-frame-p proof-number-arithmetic-formula-labels
                            proof-number-arithmetic-dispatch-entry
                            proof-number-arithmetic-decision-is-register-only
                            proof-number-formula-result-p last))
           :do-not-induct t))
  :rule-classes nil)
