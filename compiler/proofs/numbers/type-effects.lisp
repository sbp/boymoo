(in-package "BOYMOO-PROOFS")

(include-book "stack-heap")
(include-book "register-effects")
(include-book "comparison-return")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-execute proof-instruction-effect
                     proof-number-checked-block-p proof-number-execute-block proof-number-exact-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-reg proof-load-word proof-heap-base proof-heap-p proof-heap-layout-p
                     proof-reg-value-p proof-machine-value-p proof-number-memory-change-p
                     proof-number-heap-registers-and-world-tail-agree-p
                     boymoo-model::a64-sp boymoo-model::a64-memory boymoo-model::a64-unsigned
                     boymoo-model::a64-store boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-pc boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                     oddp proof-word-tag proof-header-type proof-pointer-address
                     mod floor ash (:definition nth) (:definition update-nth))))

(local
 (defthm classifier-path-uses-registers
   (proof-number-register-only-code-p (proof-number-classifier-path world) '(3 4 5))
   :hints (("Goal" :in-theory (enable proof-number-classifier-path
                                     proof-number-classifier-instructions
                                     proof-number-register-only-instruction-p)))))

(defthm proof-number-classifier-keeps-world-tail
  (implies (not (eq (car (proof-world-machine world)) :svc))
           (and (equal (cdr (proof-number-classifier-after world)) (cdr world))
                (implies (not (member-equal register '(3 4 5)))
                         (equal (proof-world-reg register (proof-number-classifier-after world))
                                (proof-world-reg register world)))))
  :hints (("Goal"
           :use ((:instance proof-number-register-only-block-effects
                            (instructions (proof-number-classifier-path world)) (clobbers '(3 4 5))))
           :in-theory (enable proof-number-classifier-after)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm second-classifier-call-uses-registers
   (proof-number-register-only-code-p
    (proof-number-types-second-code rational-only pc classifier) '(0 3 6 7 30))
   :hints (("Goal" :in-theory (enable proof-number-types-second-code
                                     proof-number-register-only-instruction-p)))))

(local
 (defthm second-classifier-call-keeps-world-tail
   (let ((after (proof-number-types-second-ready rational-only classifier world)))
     (implies (not (eq (car (proof-world-machine world)) :svc))
              (and (equal (cdr after) (cdr world))
                   (implies (not (member-equal register '(0 3 6 7 30)))
                            (equal (proof-world-reg register after)
                                   (proof-world-reg register world))))))
   :hints (("Goal"
            :use ((:instance proof-number-register-only-block-effects
                             (instructions (proof-number-types-second-code
                                            rational-only (proof-world-pc world) classifier))
                             (clobbers '(0 3 6 7 30))))
            :in-theory (enable proof-number-types-second-ready)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm completion-finisher-keeps-world-tail
   (let ((after (proof-number-execute-block (proof-number-types-finish-code rational-only) world)))
     (implies (not (eq (car (proof-world-machine world)) :svc))
              (and (equal (cdr after) (cdr world))
                   (implies (not (member-equal register '(0 1 3 29 30)))
                            (equal (proof-world-reg register after) (proof-world-reg register world))))))
   :hints (("Goal"
            :in-theory (enable proof-number-types-finish-code proof-number-execute-block proof-world-reg)
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-type-completion-keeps-frame-registers
  (let ((after (proof-number-types-completion-after rational-only classifier world)))
    (implies (proof-number-types-completion-trace-p rational-only classifier cuts a b world objects packages)
             (and (equal (cdr after) (cdr world))
                  (implies (not (member-equal register '(0 1 3 4 5 6 7)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal"
           :use (proof-number-types-return-or-fallthrough
                 (:instance proof-number-save-and-call-effects (target classifier))
                 (:instance proof-number-classifier-keeps-world-tail
                            (world (proof-number-types-first-ready classifier world)))
                 (:instance second-classifier-call-keeps-world-tail
                            (world (proof-number-classifier-after (proof-number-types-first-ready classifier world))))
                 (:instance proof-number-classifier-keeps-world-tail
                            (world (proof-number-types-second-ready
                                    rational-only classifier
                                    (proof-number-classifier-after (proof-number-types-first-ready classifier world)))))
                 (:instance completion-finisher-keeps-world-tail
                            (world (proof-number-types-classified rational-only classifier world))))
           :in-theory (enable proof-number-types-completion-trace-p proof-number-types-first-trace-p
                              proof-number-types-second-trace-p proof-number-classifier-trace-p
                              proof-number-types-completion-after proof-number-types-classified)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm completion-keeps-heap-registers
   (implies (proof-number-types-completion-trace-p rational-only classifier cuts a b world objects packages)
            (proof-number-heap-registers-and-world-tail-agree-p
             world (proof-number-types-completion-after rational-only classifier world)))
   :hints (("Goal"
            :use ((:instance proof-number-type-completion-keeps-frame-registers (register 23))
                  (:instance proof-number-type-completion-keeps-frame-registers (register 24))
                  (:instance proof-number-type-completion-keeps-frame-registers (register 25))
                  (:instance proof-number-type-completion-keeps-frame-registers (register 26))
                  (:instance proof-number-type-completion-keeps-frame-registers (register 27))
                  (:instance proof-number-type-completion-keeps-frame-registers (register 28)))
            :in-theory (enable proof-number-heap-registers-and-world-tail-agree-p)))
   :rule-classes nil))

(defthm proof-number-type-completion-write-footprint
   (let* ((machine (proof-world-machine world))
          (sp (boymoo-model::a64-sp machine))
          (after (proof-number-types-completion-after rational-only classifier world)))
     (implies (proof-number-types-completion-trace-p rational-only classifier cuts a b world objects packages)
              (proof-number-memory-change-p (- sp 16) sp machine (proof-world-machine after))))
   :hints (("Goal"
            :use (proof-number-type-completion-memory-from-save
                  (:instance proof-number-save-and-call-effects (target classifier) (register 28))
                  (:instance proof-number-pair-store-changes-only-footprint
                             (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                             (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                             (end (boymoo-model::a64-sp (proof-world-machine world)))
                             (machine (proof-world-machine world))
                             (left (proof-world-reg 29 world)) (right (proof-world-reg 30 world)))
                  (:instance proof-number-memory-change-with-same-final-memory
                             (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                             (end (boymoo-model::a64-sp (proof-world-machine world)))
                             (first (proof-world-machine world))
                             (last (proof-world-machine
                                    (proof-number-types-completion-after rational-only classifier world)))
                             (other (boymoo-model::a64-store
                                     8 (- (boymoo-model::a64-sp (proof-world-machine world)) 8)
                                     (proof-world-reg 30 world)
                                     (boymoo-model::a64-store
                                      8 (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                      (proof-world-reg 29 world) (proof-world-machine world))))))
            :in-theory (enable proof-number-types-completion-trace-p proof-number-types-first-trace-p)
            :do-not-induct t))
   :rule-classes nil)

(local
 (defthm heap-has-aligned-sp
   (implies (proof-heap-p world objects packages)
            (equal (mod (boymoo-model::a64-sp (proof-world-machine world)) 16) 0))
   :hints (("Goal"
            :expand ((proof-heap-p world objects packages) (proof-heap-layout-p world))
            :in-theory (disable proof-runtime-word proof-align-up proof-covered-p proof-disjoint-p
                                proof-regions-p proof-static-p proof-object-map-p proof-external-objects
                                proof-dynamic-entries proof-dynamic-symbol-objects-p proof-heap-object-spans-p
                                proof-stack-prefix proof-string-accounting-p)))
   :rule-classes nil))

(local
 (defthm completed-types-stack-pointer
   (implies (proof-number-types-completion-trace-p rational-only classifier cuts a b world objects packages)
            (equal (boymoo-model::a64-sp
                    (proof-world-machine (proof-number-types-completion-after rational-only classifier world)))
                   (boymoo-model::a64-sp (proof-world-machine world))))
   :hints (("Goal"
            :use proof-number-types-return-or-fallthrough
            :in-theory (disable proof-register-arguments-p proof-number-binary-types-p
                                proof-number-completed-word rfix)))
   :rule-classes nil))

(defthm proof-number-type-completion-preserves-heap
  (let* ((start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
         (after (proof-number-types-completion-after rational-only classifier world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-save-interval-p start world objects)
                  (proof-number-types-completion-trace-p rational-only classifier cuts a b world objects packages))
             (proof-preserved-heap-p nil world after objects objects packages)))
  :hints (("Goal"
           :use (completed-types-stack-pointer heap-has-aligned-sp
                 completion-keeps-heap-registers proof-number-type-completion-write-footprint
                 (:instance proof-number-machine-save-preserves-heap
                            (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (before world) (after (proof-number-types-completion-after rational-only classifier world))))
           :in-theory (disable proof-preserved-heap-p)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm completion-keeps-numeric-register
   (implies (and (proof-number-types-completion-trace-p
                  rational-only classifier cuts a b world objects packages)
                 (not (member-equal register (proof-number-numeric-clobbers))))
            (equal (proof-world-reg register
                                    (proof-number-types-completion-after rational-only classifier world))
                   (proof-world-reg register world)))
   :hints (("Goal" :use proof-number-type-completion-keeps-frame-registers
                   :in-theory (enable proof-number-numeric-clobbers)
                   :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-types-keep-numeric-register-frame
  (implies (proof-number-types-completion-trace-p rational-only classifier cuts a b world objects packages)
           (proof-register-frame-p limit (proof-number-numeric-clobbers) world
                                   (proof-number-types-completion-after rational-only classifier world)))
  :hints (("Goal"
           :induct (proof-register-frame-p limit (proof-number-numeric-clobbers) world
                                           (proof-number-types-completion-after rational-only classifier world))
           :in-theory (disable proof-number-numeric-clobbers
                               (:executable-counterpart proof-number-numeric-clobbers)))
          ("Subgoal *1/3" :use ((:instance completion-keeps-numeric-register (register limit))))
          ("Subgoal *1/2" :use ((:instance completion-keeps-numeric-register (register limit))))
          ("Subgoal *1/1" :use ((:instance completion-keeps-numeric-register (register limit)))))
  :rule-classes nil)

(defthm proof-number-type-completion-keeps-save-interval
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (start (- sp 16))
         (after (proof-number-types-completion-after rational-only classifier world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-save-interval-p start world objects)
                  (proof-number-types-completion-trace-p rational-only classifier cuts a b world objects packages))
             (proof-number-save-interval-p start after objects)))
  :hints (("Goal"
           :use (proof-number-type-completion-write-footprint completed-types-stack-pointer
                 (:instance proof-number-type-completion-keeps-frame-registers (register 23))
                 (:instance proof-number-disjoint-footprint-keeps-old-values
                            (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (end (boymoo-model::a64-sp (proof-world-machine world)))
                            (before world) (after (proof-number-types-completion-after rational-only classifier world))
                            (old-objects objects) (extra nil) (word nil) (value nil))
                 (:instance proof-number-object-memory-keeps-disjointness
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (end (boymoo-model::a64-sp (proof-world-machine world)))
                            (pending objects)
                            (first (proof-world-machine world))
                            (last (proof-world-machine
                                   (proof-number-types-completion-after rational-only classifier world)))))
           :expand ((proof-heap-p world objects packages))
           :in-theory (e/d (proof-number-save-interval-p proof-machine-limit)
                           (proof-heap-layout-p proof-static-p proof-external-objects
                            proof-object-map-p proof-heap-object-spans-p proof-dynamic-symbol-objects-p
                            proof-dynamic-entries proof-dynamic-view proof-string-accounting-p proof-stack-prefix
                            proof-object-disjoint-p proof-span-p proof-number-objects-memory-p
                            proof-number-memory-change-p proof-machine-value-p))
           :do-not-induct t))
  :rule-classes nil)
