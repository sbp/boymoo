(in-package "BOYMOO-PROOFS")

(include-book "arithmetic-paths")
(include-book "immediate-delegation")
(include-book "comparison-frame")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-heap-layout-p proof-preserved-heap-p
                     proof-frame-return-p proof-datum-return-p proof-reg-value-p
                     proof-runtime-pre-p proof-runtime-value proof-runtime-return-p
                     proof-number-immediate-returns-here-p proof-number-immediate-delegates-p
                     proof-number-arithmetic-decision-trace-p proof-number-arithmetic-helper-trace-p
                     proof-number-arithmetic-wrapper-trace-p proof-number-general-gate-trace-p
                     proof-number-immediate-entry-trace-p proof-number-immediate-delegation-trace-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(local
 (defthm numeric-arithmetic-argument-lists-agree
   (implies (proof-number-arithmetic-dispatch-entry primitive)
            (equal (proof-number-immediate-source-args primitive a b)
                   (proof-number-arithmetic-source-args primitive a b)))
   :hints (("Goal"
            :in-theory (enable proof-number-arithmetic-dispatch-entry proof-number-immediate-arity
                               proof-number-immediate-source-args proof-number-arithmetic-source-args
                               proof-number-arithmetic-binary-p)))))

(defund proof-number-public-arithmetic-success-trace-p
    (primitive a b general slow types classifier addresses helper-steps steps
               world returned objects new-objects program packages gcd grow growth-steps targets
               trace grown grown-objects)
  (let* ((args (proof-number-arithmetic-source-args primitive a b))
         (arity (len args))
         (pc (proof-world-pc world))
         (link (proof-world-reg 30 world)))
    (and (proof-number-arithmetic-dispatch-entry primitive)
         (cond ((proof-number-immediate-returns-here-p primitive a b)
                (let ((code (proof-number-immediate-entry-code primitive a b pc general slow 0 0)))
                  (and (proof-number-immediate-entry-trace-p primitive a b general slow 0 0 world)
                       (equal new-objects objects)
                       (equal steps (len code))
                       (equal returned (proof-number-execute-block code world)))))
               ((proof-number-immediate-delegates-p primitive a b)
                (let ((entered (proof-number-immediate-delegation-after primitive a general slow world))
                      (code (proof-number-immediate-delegation-entry-code primitive a pc general slow)))
                  (and (proof-number-immediate-delegation-trace-p primitive a b general slow world)
                       (natp helper-steps)
                       (equal steps (+ (len code) helper-steps))
                       (proof-segment-p helper-steps (list link) entered :cut returned)
                       (proof-runtime-return-p primitive args program entered returned
                                               objects new-objects packages))))
               (t
                (let* ((entry (proof-number-general-gate-after arity general world))
                       (dispatch (proof-number-arithmetic-wrapper-after primitive types classifier entry)))
                  (and (proof-number-general-gate-trace-p arity general world)
                       (proof-number-arithmetic-wrapper-trace-p primitive a b types classifier
                                                               entry objects packages)
                       (proof-number-arithmetic-decision-trace-p primitive addresses dispatch)
                       (proof-number-arithmetic-helper-trace-p
                        primitive a b addresses helper-steps returned new-objects dispatch objects packages
                        program gcd grow growth-steps targets trace grown grown-objects)
                       (equal steps (+ 1 arity (proof-number-arithmetic-wrapper-steps
                                                primitive types classifier entry)
                                       (len (proof-number-arithmetic-dispatch-path primitive addresses dispatch))
                                       helper-steps)))))))))

(defthm proof-number-public-arithmetic-runtime-return
  (let ((args (proof-number-arithmetic-source-args primitive a b)))
    (implies (and (proof-runtime-pre-p primitive args program labels base world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-public-arithmetic-success-trace-p
                   primitive a b general slow types classifier addresses helper-steps steps
                   world returned objects new-objects program packages gcd grow growth-steps targets
                   trace grown grown-objects))
             (and (proof-segment-p steps (list (proof-world-reg 30 world)) world :cut returned)
                  (proof-runtime-return-p primitive args program world returned objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-public-immediate-runtime-return (name primitive) (yes 0) (no 0))
                 (:instance proof-number-public-delegated-immediate-runtime-return
                            (name primitive) (steps helper-steps) (after returned))
                 proof-number-public-general-arithmetic-checked-return)
           :in-theory (enable proof-number-public-arithmetic-success-trace-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-public-less-runtime-return
  (let* ((fast (proof-number-immediate-returns-here-p '< a b))
         (code (proof-number-immediate-entry-code '< a b (proof-world-pc world) general 0 yes no))
         (middle (proof-number-general-gate-after 2 general world))
         (after (if fast
                    (proof-number-execute-block code world)
                  (proof-number-general-less-after a b types classifier yes no returned middle)))
         (steps (if fast (len code)
                  (+ 3 (proof-number-general-less-steps a b types classifier callee-steps middle))))
         (final-objects (if fast objects new-objects))
         (args (list a b)))
    (implies (and (proof-runtime-pre-p '< args program labels base world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (if fast
                      (proof-number-immediate-entry-trace-p '< a b general 0 yes no world)
                    (and (proof-number-general-gate-trace-p 2 general world)
                         (proof-number-general-less-trace-p a b types classifier rational complex yes no callee-steps
                                                            middle returned objects new-objects packages))))
             (and (proof-segment-p steps (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p '< args program world after objects final-objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-public-immediate-runtime-return (name '<) (slow 0))
                 proof-number-public-general-less-runtime-return)
           :in-theory (enable proof-number-immediate-source-args proof-number-immediate-arity)
           :do-not-induct t))
  :rule-classes nil)
