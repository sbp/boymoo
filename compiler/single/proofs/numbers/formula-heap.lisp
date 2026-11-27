(in-package "BOYMOO-PROOFS")

(include-book "formula-saves")
(include-book "value-stack")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p proof-number-checked-block-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-machine-limit proof-stack-top proof-heap-p proof-heap-layout-p
                     proof-preserved-heap-p proof-heap-frame-p proof-stack-prefix proof-reg-value-p
                     proof-frame-return-p proof-datum-return-p
                     proof-number-formula-call-instructions proof-number-formula-call-trace-p
                     proof-number-formula-spill-trace-p proof-number-formula-argument-store-instructions
                     proof-number-slot-arguments proof-number-call-value proof-number-call-domain-p
                     proof-number-frame-p proof-number-slot-indices-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defthm proof-number-formula-call-preserves-heap-and-register-frame
  (let* ((indices (cdr call))
         (returned (cadr entry))
         (new-objects (caddr entry))
         (clobbers (cons 30 (proof-number-numeric-clobbers))))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-slot-indices-p indices (len slots))
                  (proof-number-frame-p start slots world objects packages)
                  (proof-number-formula-call-trace-p call slots gcd start targets link
                                                     entry world objects packages))
             (and (proof-preserved-heap-p nil world returned objects new-objects packages)
                  (proof-heap-p returned new-objects packages)
                  (proof-number-world-byte-keys-p returned)
                  (proof-register-frame-p 30 clobbers world returned)
                  (equal (boymoo-model::a64-sp (proof-world-machine returned))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (proof-machine-limit returned) (proof-machine-limit world))
                  (proof-number-frame-p start slots returned new-objects packages))))
  :hints (("Goal"
           :use (proof-number-formula-call-keeps-slot-values
                 (:instance proof-number-register-only-execution-preserves-heap
                            (clobbers '(0 1 30))
                            (instructions (proof-number-formula-call-instructions
                                           (cdr call) (proof-world-pc world)
                                           (cdr (assoc-equal (car call) targets)))))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count (+ 1 (len (cdr call)) (car entry))) (cuts (list link))
                            (before world) (after (cadr entry)))
                 (:instance proof-number-preserved-heaps-compose
                            (before world) (middle (proof-number-formula-call-ready call targets world))
                            (after (cadr entry)) (old-objects objects) (middle-objects objects)
                            (objects (caddr entry)))
                 (:instance proof-number-preserved-heap-is-valid
                            (may-intern nil) (before world) (after (cadr entry))
                            (old-objects objects) (objects (caddr entry)))
                 (:instance proof-number-register-frames-extend-and-compose
                            (limit 30) (clobbers (cons 30 (proof-number-numeric-clobbers)))
                            (first-clobbers '(0 1 30)) (last-clobbers (proof-number-numeric-clobbers))
                            (before world) (middle (proof-number-formula-call-ready call targets world))
                            (after (cadr entry)))
                 (:instance proof-number-register-frame-keeps
                            (limit 30) (register 23) (clobbers (proof-number-numeric-clobbers))
                            (before (proof-number-formula-call-ready call targets world)) (after (cadr entry))))
           :in-theory (e/d (proof-number-formula-call-trace-p proof-number-formula-call-return-p
                            proof-number-formula-call-ready proof-datum-return-p proof-frame-return-p
                            proof-number-numeric-clobbers proof-machine-limit)
                           (proof-register-frame-p proof-number-register-only-code-p
                            proof-register-arguments-p assoc-equal proof-number-frame-address))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-formula-frame-has-initialized-prefix
  (implies (proof-number-frame-p start slots world objects packages)
           (proof-stack-prefix (proof-stack-top world) world objects packages))
  :hints (("Goal" :in-theory (enable proof-number-frame-p)))
  :rule-classes nil)

(defthm proof-number-formula-spill-preserves-heap-and-register-frame
  (let ((after (proof-number-formula-spill-after world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-frame-p start slots world objects packages)
                  (proof-number-value-append-pre-p 1 world objects packages)
                  (proof-number-formula-spill-trace-p value link world objects packages))
             (and (proof-preserved-heap-p nil world after objects objects packages)
                  (proof-heap-p after objects packages)
                  (proof-number-world-byte-keys-p after)
                  (proof-register-frame-p 30 '(25) world after)
                  (equal (proof-machine-limit after) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (proof-number-frame-p start (append slots (list value)) after objects packages))))
  :hints (("Goal"
           :use (proof-number-heap-machine-context proof-number-formula-spill-keeps-slot-values
                 (:instance proof-number-value-append-preserves-heap (arity 1))
                 (:instance proof-number-value-append-register-frame (arity 1) (limit 30))
                 (:instance proof-number-value-append-keeps-layout-coordinates (arity 1))
                 (:instance proof-number-formula-frame-has-initialized-prefix
                            (slots (append slots (list value))) (world (proof-number-formula-spill-after world)))
                 (:instance proof-number-preserved-heap-is-valid
                            (may-intern nil) (before world) (after (proof-number-formula-spill-after world))
                            (old-objects objects))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (before world) (after (proof-number-formula-spill-after world))
                            (count 2) (cuts (list link))))
           :in-theory (e/d (proof-number-formula-spill-after proof-number-formula-argument-store-instructions)
                           (proof-register-frame-p proof-argument-views proof-prefix-preserved-p))
           :do-not-induct t))
  :rule-classes nil)

(defun proof-number-formula-spill-storage-p (calls trace packages)
  (if (endp (cdr calls))
      t
    (and (proof-number-value-append-pre-p 1 (cadar trace) (caddar trace) packages)
         (proof-number-formula-spill-storage-p (cdr calls) (cdr trace) packages))))

(local
 (defthm formula-slot-count-after-spill
   (equal (len (append slots (list value))) (1+ (len slots)))
   :hints (("Goal" :induct (len slots)))))

(local
 (defthm nonempty-formula-body-has-trace-entry
   (implies (and (consp calls)
                 (proof-number-formula-body-trace-p calls trace slots gcd start targets link
                                                    world objects packages))
            (consp trace))
   :hints (("Goal"
            :expand ((proof-number-formula-body-trace-p calls trace slots gcd start targets link
                                                        world objects packages))))))

(local
 (defthm formula-call-and-spill-preserve-heap
   (let* ((returned (cadr entry))
          (new-objects (caddr entry))
          (after (proof-number-formula-spill-after returned))
          (value (proof-number-call-value (car call)
                                         (proof-number-slot-arguments (cdr call) slots) gcd))
          (clobbers (list* 25 30 (proof-number-numeric-clobbers))))
     (implies (and (proof-heap-p world objects packages)
                   (proof-number-world-byte-keys-p world)
                   (proof-number-slot-indices-p (cdr call) (len slots))
                   (proof-number-frame-p start slots world objects packages)
                   (proof-number-formula-call-trace-p call slots gcd start targets link
                                                      entry world objects packages)
                   (proof-number-value-append-pre-p 1 returned new-objects packages)
                   (proof-number-formula-spill-trace-p value link returned new-objects packages))
              (and (proof-preserved-heap-p nil world after objects new-objects packages)
                   (proof-heap-p after new-objects packages)
                   (proof-number-world-byte-keys-p after)
                   (proof-register-frame-p 30 clobbers world after)
                   (equal (proof-machine-limit after) (proof-machine-limit world))
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (proof-number-frame-p start (append slots (list value)) after new-objects packages))))
   :hints (("Goal"
            :use (proof-number-formula-call-preserves-heap-and-register-frame
                  (:instance proof-number-formula-spill-preserves-heap-and-register-frame
                             (world (cadr entry)) (objects (caddr entry))
                             (value (proof-number-call-value
                                     (car call) (proof-number-slot-arguments (cdr call) slots) gcd)))
                  (:instance proof-number-preserved-heaps-compose
                             (before world) (middle (cadr entry))
                             (after (proof-number-formula-spill-after (cadr entry)))
                             (old-objects objects) (middle-objects (caddr entry)) (objects (caddr entry)))
                  (:instance proof-number-register-frames-extend-and-compose
                             (limit 30) (clobbers (list* 25 30 (proof-number-numeric-clobbers)))
                             (first-clobbers (cons 30 (proof-number-numeric-clobbers))) (last-clobbers '(25))
                             (before world) (middle (cadr entry))
                             (after (proof-number-formula-spill-after (cadr entry)))))
            :in-theory (e/d (proof-number-numeric-clobbers) (proof-register-frame-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-formula-body-preserves-heap-and-register-frame
  (let* ((returned (cadar (last trace)))
         (new-objects (caddar (last trace)))
         (clobbers (list* 25 30 (proof-number-numeric-clobbers))))
    (implies (and (consp calls)
                  (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-call-slots-p calls (len slots))
                  (proof-number-frame-p start slots world objects packages)
                  (proof-number-formula-body-trace-p calls trace slots gcd start targets link
                                                     world objects packages)
                  (proof-number-formula-spill-storage-p calls trace packages))
             (and (proof-preserved-heap-p nil world returned objects new-objects packages)
                  (proof-heap-p returned new-objects packages)
                  (proof-number-world-byte-keys-p returned)
                  (proof-register-frame-p 30 clobbers world returned)
                  (equal (proof-machine-limit returned) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine returned))
                         (boymoo-model::a64-sp (proof-world-machine world))))))
  :hints (("Goal"
           :induct (proof-number-formula-body-trace-p calls trace slots gcd start targets link
                                                     world objects packages)
           :in-theory (disable proof-register-frame-p))
          ("Subgoal *1/3"
           :use ((:instance formula-call-and-spill-preserve-heap (call (car calls)) (entry (car trace)))
                 (:instance proof-number-preserved-heaps-compose
                            (before world) (middle (proof-number-formula-spill-after (cadar trace)))
                            (after (cadar (last trace)))
                            (old-objects objects) (middle-objects (caddar trace)) (objects (caddar (last trace))))
                 (:instance proof-number-register-frames-compose
                            (limit 30) (clobbers (list* 25 30 (proof-number-numeric-clobbers)))
                            (before world) (middle (proof-number-formula-spill-after (cadar trace)))
                            (after (cadar (last trace))))))
          ("Subgoal *1/2"
           :use ((:instance proof-number-formula-call-preserves-heap-and-register-frame
                            (call (car calls)) (entry (car trace)))
                 (:instance proof-number-register-frame-allows-more-clobbers
                            (limit 30) (clobbers (cons 30 (proof-number-numeric-clobbers)))
                            (extended (list* 25 30 (proof-number-numeric-clobbers)))
                            (before world) (after (cadar trace))))
           :in-theory (e/d (proof-number-numeric-clobbers) (proof-register-frame-p))))
  :rule-classes nil)
