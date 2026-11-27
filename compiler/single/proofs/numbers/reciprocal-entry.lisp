(in-package "BOYMOO-PROOFS")

(include-book "primitive-returns")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-preserved-heap-p proof-register-frame-p
                     proof-runtime-pre-p proof-runtime-value proof-runtime-return-p
                     proof-datum-return-p proof-number-formula-result-p
                     proof-number-formula-contract-trace-p proof-number-immediate-delegation-trace-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defthm proof-number-rational-reciprocal-datum-return
  (let* ((name "rt:q-reciprocal")
         (args (list a))
         (after (proof-number-formula-trace-after trace)))
    (implies (and (rationalp a)
                  (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                                world objects)
                  (proof-number-formula-contract-trace-p
                   name args gcd grow growth-steps targets trace world grown objects grown-objects packages))
             (and (proof-segment-p (proof-number-formula-contract-steps name growth-steps trace)
                                   (list (proof-world-reg 30 world)) world :cut after)
                  (proof-datum-return-p (/ a) (proof-number-numeric-clobbers) t t nil
                                        world after objects (caddar (last trace)) packages))))
  :hints (("Goal"
           :use ((:instance proof-number-q-reciprocal-formula (x a))
                 (:instance proof-number-generated-formula-datum-return
                            (name "rt:q-reciprocal") (args (list a)) (result (/ a))))
           :in-theory (disable last)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm immediate-reciprocal-argument-is-rational
   (implies (proof-number-immediate-delegation-trace-p 'acl2::unary-/ a nil general reciprocal world)
            (rationalp a))
   :hints (("Goal"
            :in-theory (enable proof-number-immediate-delegation-trace-p proof-number-immediate-delegates-p
                               proof-immediate-integer-p)))
   :rule-classes nil))

(defthm proof-number-public-immediate-reciprocal-through-formula
  (let* ((primitive 'acl2::unary-/)
         (args (list a))
         (entered (proof-number-immediate-delegation-after primitive a general reciprocal world))
         (steps (proof-number-formula-contract-steps "rt:q-reciprocal" growth-steps trace))
         (prefix (len (proof-number-immediate-delegation-entry-code
                       primitive a (proof-world-pc world) general reciprocal)))
         (after (proof-number-formula-trace-after trace))
         (new-objects (caddar (last trace))))
    (implies (and (proof-runtime-pre-p primitive args program labels base world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-immediate-delegation-trace-p primitive a nil general reciprocal world)
                  (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine entered)) 16)
                                                entered objects)
                  (proof-number-formula-contract-trace-p
                   "rt:q-reciprocal" args gcd grow growth-steps targets trace
                   entered grown objects grown-objects packages))
             (and (proof-segment-p (+ prefix steps) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p primitive args program world after objects new-objects packages))))
  :hints (("Goal"
           :use (immediate-reciprocal-argument-is-rational
                 (:instance proof-number-runtime-entry-has-heap (name 'acl2::unary-/) (args (list a)))
                 (:instance proof-number-public-immediate-reaches-helper
                            (name 'acl2::unary-/) (b nil) (slow reciprocal))
                 (:instance proof-number-preserved-heap-is-valid
                            (may-intern nil) (before world) (old-objects objects)
                            (after (proof-number-immediate-delegation-after 'acl2::unary-/ a general reciprocal world)))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count (len (proof-number-immediate-delegation-entry-code
                                         'acl2::unary-/ a (proof-world-pc world) general reciprocal)))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (after (proof-number-immediate-delegation-after 'acl2::unary-/ a general reciprocal world)))
                 (:instance proof-number-rational-reciprocal-datum-return
                            (world (proof-number-immediate-delegation-after 'acl2::unary-/ a general reciprocal world)))
                 (:instance proof-number-formula-contract-step-count-is-natural
                            (name "rt:q-reciprocal") (args (list a))
                            (world (proof-number-immediate-delegation-after 'acl2::unary-/ a general reciprocal world)))
                 proof-number-public-value-completions
                 (:instance proof-number-numeric-runtime-return-contract
                            (name 'acl2::unary-/) (args (list a))
                            (before (proof-number-immediate-delegation-after 'acl2::unary-/ a general reciprocal world))
                            (after (proof-number-formula-trace-after trace))
                            (old-objects objects) (objects (caddar (last trace))))
                 (:instance proof-number-public-delegated-immediate-runtime-return
                            (name 'acl2::unary-/) (b nil) (slow reciprocal)
                            (steps (proof-number-formula-contract-steps "rt:q-reciprocal" growth-steps trace))
                            (after (proof-number-formula-trace-after trace)) (new-objects (caddar (last trace)))))
           :in-theory (e/d (proof-number-immediate-source-args proof-number-immediate-arity)
                           (last proof-number-immediate-delegation-after proof-number-immediate-delegation-entry-code))
           :do-not-induct t))
  :rule-classes nil)
