(in-package "BOYMOO-PROOFS")

(include-book "arithmetic-frames")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-machine-limit proof-heap-p proof-heap-layout-p proof-heap-frame-p
                     proof-preserved-heap-p proof-frame-return-p proof-datum-return-p proof-reg-value-p
                     proof-runtime-return-p proof-runtime-value proof-number-arithmetic-dispatch-path
                     proof-number-selected-label proof-number-arithmetic-dispatch-input-p
                     proof-number-binary-types-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defund proof-number-arithmetic-dispatch-after (primitive addresses world)
  (proof-number-execute-block (proof-number-arithmetic-dispatch-path primitive addresses world) world))

(defund proof-number-arithmetic-decision-trace-p (primitive addresses world)
  (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
         (row (assoc-equal entry *proof-number-dispatch-rows*))
         (path (proof-number-arithmetic-dispatch-path primitive addresses world))
         (target (cdr (assoc-equal (proof-number-selected-label entry world) addresses)))
         (pc (proof-world-pc world))
         (link (proof-world-reg 30 world)))
    (and entry row
         (not (eq (car (proof-world-machine world)) :svc))
         (unsigned-byte-p 64 (+ pc (* 8 (len (cadr row)))))
         (unsigned-byte-p 64 target)
         (proof-number-checked-block-p path (list target) world)
         (proof-number-cut-free-prefix-p (len path) (list target link) world))))

(local
 (defthm register-only-sequences-append
   (equal (proof-number-register-only-code-p (append first last) clobbers)
          (and (proof-number-register-only-code-p first clobbers)
               (proof-number-register-only-code-p last clobbers)))
   :hints (("Goal" :induct (len first)))))

(local
 (defthm dispatch-test-only-changes-pc-and-flags
   (proof-number-register-only-code-p (proof-number-dispatch-test test pc addresses) clobbers)
   :hints (("Goal"
            :in-theory (enable proof-number-register-only-instruction-p)))))

(local
 (defthm dispatch-path-is-register-only
   (proof-number-register-only-code-p (proof-number-dispatch-path tests default pc addresses world) clobbers)
   :hints (("Goal"
            :induct (proof-number-dispatch-path tests default pc addresses world)
            :in-theory (e/d (proof-number-register-only-instruction-p)
                            (proof-number-dispatch-test assoc-equal))))))

(defthm proof-number-arithmetic-decision-is-register-only
  (proof-number-register-only-code-p (proof-number-arithmetic-dispatch-path primitive addresses world) clobbers)
  :hints (("Goal"
           :in-theory (e/d (proof-number-arithmetic-dispatch-path)
                           (proof-number-dispatch-path assoc-equal)))))

(defthm proof-number-arithmetic-decision-keeps-dispatch-context
  (let* ((path (proof-number-arithmetic-dispatch-path primitive addresses world))
         (after (proof-number-arithmetic-dispatch-after primitive addresses world))
         (target (cdr (assoc-equal (proof-number-selected-label
                                   (proof-number-arithmetic-dispatch-entry primitive) world) addresses)))
         (link (proof-world-reg 30 world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-arithmetic-decision-trace-p primitive addresses world))
             (and (proof-segment-p (len path) (list target) world :cut after)
                  (proof-number-exact-prefix-p (len path) (list link) world after)
                  (proof-number-dispatch-context-p world after objects packages)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg register after) (proof-world-reg register world)))))
  :hints (("Goal"
           :use ((:instance proof-number-dispatch-reaches-selected-label
                            (name (proof-number-arithmetic-dispatch-entry primitive)))
                 (:instance proof-number-dispatch-reaches-selected-label
                            (name (proof-number-arithmetic-dispatch-entry primitive)) (register 30))
                 (:instance proof-number-register-only-execution-preserves-heap
                            (clobbers nil) (instructions (proof-number-arithmetic-dispatch-path primitive addresses world)))
                 (:instance proof-number-register-frame-allows-more-clobbers
                            (limit 30) (clobbers nil) (extended (proof-number-numeric-clobbers))
                            (before world) (after (proof-number-arithmetic-dispatch-after primitive addresses world)))
                 (:instance proof-number-segment-exact-prefix
                            (before world) (after (proof-number-arithmetic-dispatch-after primitive addresses world))
                            (count (len (proof-number-arithmetic-dispatch-path primitive addresses world)))
                            (cuts (list (proof-world-reg 30 world))) (reason :cut)
                            (local-cuts
                             (list (cdr (assoc-equal
                                         (proof-number-selected-label (proof-number-arithmetic-dispatch-entry primitive) world)
                                         addresses)))))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (before world) (after (proof-number-arithmetic-dispatch-after primitive addresses world))
                            (count (len (proof-number-arithmetic-dispatch-path primitive addresses world)))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (e/d (proof-number-arithmetic-decision-trace-p proof-number-arithmetic-dispatch-after
                            proof-number-arithmetic-dispatch-path proof-number-selected-label
                            proof-number-dispatch-context-p)
                           (proof-number-dispatch-path proof-number-dispatch-label
                            proof-number-register-only-code-p proof-register-frame-p assoc-equal))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-arithmetic-decision-passes-operand
  (implies (and (proof-number-arithmetic-decision-trace-p primitive addresses world)
                (proof-reg-value-p register value world objects packages))
           (proof-reg-value-p register value
                              (proof-number-arithmetic-dispatch-after primitive addresses world) objects packages))
  :hints (("Goal"
           :use ((:instance proof-number-dispatch-reaches-selected-label
                            (name (proof-number-arithmetic-dispatch-entry primitive)))
                 (:instance proof-number-dispatch-reaches-selected-label
                            (name (proof-number-arithmetic-dispatch-entry primitive)) (register 28))
                 (:instance proof-number-reg-value-with-same-memory
                            (before world) (after (proof-number-arithmetic-dispatch-after primitive addresses world))
                            (word (proof-world-reg register world))))
           :in-theory (e/d (proof-number-arithmetic-decision-trace-p proof-number-arithmetic-dispatch-after
                            proof-number-arithmetic-dispatch-path proof-number-selected-label proof-reg-value-p
                            proof-heap-base)
                           (proof-machine-value-p proof-number-dispatch-path proof-number-dispatch-label assoc-equal))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-selected-integer-helper-domain
  (let ((label (proof-number-selected-label (proof-number-arithmetic-dispatch-entry primitive) world))
        (source (proof-number-arithmetic-source-args primitive a b)))
    (implies (and (proof-number-arithmetic-dispatch-entry primitive)
                  (proof-number-arithmetic-dispatch-input-p primitive a b world objects packages)
                  (member-equal label '("rt:z-add-op" "rt:z-multiply-op" "rt:z-negate-op")))
             (and (integerp (fix a))
                  (if (proof-number-arithmetic-binary-p primitive)
                      (integerp (fix b))
                    (integerp a))
                  (integerp (boymoo-model::core-datum (proof-runtime-value primitive source program))))))
  :hints (("Goal"
           :use (proof-number-add-dispatch-by-value proof-number-multiply-dispatch-by-value
                 proof-number-negation-dispatch-by-value proof-number-reciprocal-dispatch-by-value
                 proof-number-public-value-completions)
           :in-theory (e/d (proof-number-arithmetic-dispatch-entry proof-number-arithmetic-dispatch-input-p
                            proof-number-arithmetic-source-args proof-number-arithmetic-binary-p)
                           (proof-number-binary-types-p))
           :cases ((eq primitive 'acl2::binary-+) (eq primitive 'acl2::binary-*)
                   (eq primitive 'acl2::unary--) (eq primitive 'acl2::unary-/))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-arithmetic-primitive-and-source-result
  (implies (proof-number-arithmetic-dispatch-entry primitive)
           (and (member-eq primitive '(acl2::binary-+ acl2::binary-* acl2::unary-- acl2::unary-/))
                (boymoo-model::core-value-p
                 (proof-runtime-value primitive (proof-number-arithmetic-source-args primitive a b) program))))
  :hints (("Goal"
           :use proof-number-public-value-completions
           :in-theory (enable proof-number-arithmetic-dispatch-entry proof-number-arithmetic-source-args
                              proof-number-arithmetic-binary-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-arithmetic-dispatch-returns-through-helper
  (let* ((args (proof-number-arithmetic-source-args primitive a b))
         (source (boymoo-model::core-datum (proof-runtime-value primitive args program)))
         (path (proof-number-arithmetic-dispatch-path primitive addresses world))
         (entered (proof-number-arithmetic-dispatch-after primitive addresses world))
         (link (proof-world-reg 30 world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-arithmetic-decision-trace-p primitive addresses world)
                  (natp helper-steps)
                  (proof-segment-p helper-steps (list link) entered :cut returned)
                  (proof-datum-return-p source (proof-number-numeric-clobbers) t t nil
                                        entered returned objects new-objects packages))
             (and (proof-segment-p (+ (len path) helper-steps) (list link) world :cut returned)
                  (proof-runtime-return-p primitive args program world returned objects new-objects packages))))
  :hints (("Goal"
           :use (proof-number-arithmetic-primitive-and-source-result
                 (:instance proof-number-arithmetic-decision-keeps-dispatch-context (register 30))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (len (proof-number-arithmetic-dispatch-path primitive addresses world)))
                            (suffix helper-steps) (cuts (list (proof-world-reg 30 world)))
                            (before world) (middle (proof-number-arithmetic-dispatch-after primitive addresses world))
                            (reason :cut) (after returned))
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (+ (len (proof-number-arithmetic-dispatch-path primitive addresses world)) helper-steps))
                            (cuts (list (proof-world-reg 30 world))) (reason :cut) (before world) (after returned))
                 (:instance proof-number-numeric-runtime-return-contract
                            (name primitive) (args (proof-number-arithmetic-source-args primitive a b))
                            (before world) (after returned) (old-objects objects) (objects new-objects))
                 (:instance proof-number-numeric-tail-transfer-returns
                            (datum (boymoo-model::core-datum
                                    (proof-runtime-value
                                     primitive (proof-number-arithmetic-source-args primitive a b) program)))
                            (before world) (middle (proof-number-arithmetic-dispatch-after primitive addresses world))
                            (after returned) (old-objects objects) (middle-objects objects) (objects new-objects)
                            (clobbers (proof-number-numeric-clobbers))))
           :in-theory (e/d (proof-number-arithmetic-decision-trace-p proof-number-dispatch-context-p
                            proof-number-numeric-clobbers)
                           (proof-register-frame-p proof-number-arithmetic-decision-is-register-only assoc-equal))
           :do-not-induct t))
  :rule-classes nil)
