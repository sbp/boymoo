(in-package "BOYMOO-PROOFS")

(include-book "numeric-comparisons")
(include-book "public-delegation")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p proof-number-checked-block-p
                     proof-execute proof-instruction-effect
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-load-word proof-machine-limit proof-heap-p proof-heap-layout-p
                     proof-datum-return-p proof-frame-return-p proof-preserved-heap-p proof-reg-value-p
                     proof-number-order proof-number-less-return-path proof-number-less-tail-code-p
                     proof-number-less-comparison-trace-p proof-number-binary-types-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defund proof-number-less-after-pop-code (order pc yes no)
  (append (cdr (proof-number-less-return-path order pc yes no))
          (cdr (assoc-equal (proof-number-less-leaf order) *proof-number-leaf-returns*))))

(local
 (defthm less-tail-remainder-is-register-only
   (proof-number-register-only-code-p (proof-number-less-after-pop-code order pc yes no) '(0))
   :hints (("Goal"
            :in-theory (enable proof-number-less-after-pop-code proof-number-less-return-path
                               proof-number-less-return-code proof-number-less-leaf
                               proof-number-register-only-instruction-p)
            :do-not-induct t))))

(local
 (defthm less-tail-executes-pop-first
   (equal (proof-number-less-tail-after order yes no world)
          (proof-number-execute-block
           (proof-number-less-after-pop-code order (proof-world-pc world) yes no)
           (proof-number-pop-link-after world)))
   :hints (("Goal"
            :in-theory (e/d (proof-number-less-tail-after proof-number-less-selected
                             proof-number-less-return-path proof-number-less-return-code
                             proof-number-less-after-pop-code proof-number-pop-link-after
                             proof-number-less-leaf proof-number-execute-block)
                            (proof-number-instruction-effect-normal))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm register-pair-update-has-entries
   (consp (put-assoc-equal register value entries))))

(local
 (defthm link-pop-produces-machine-state
   (implies (not (eq (car (proof-world-machine world)) :svc))
            (not (eq (car (proof-world-machine (proof-number-pop-link-after world))) :svc)))
   :hints (("Goal"
            :in-theory (e/d (proof-number-pop-link-after proof-number-execute-block proof-world-machine
                             boymoo-model::a64-write-reg boymoo-model::a64-registers
                             boymoo-model::a64-set-pc)
                            (proof-load-word proof-reg boymoo-model::a64-unsigned))))
   :rule-classes nil))

(defthm proof-number-less-tail-observations
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (after (proof-number-less-tail-after order yes no world)))
    (implies (and (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 (+ 16 sp))
                  (unsigned-byte-p 64 (+ 4 (proof-world-pc world))))
             (and (equal (cdr after) (cdr world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ 16 sp))
                  (implies (not (member-equal register '(0 29 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal"
           :use (less-tail-executes-pop-first link-pop-produces-machine-state
                 proof-number-pop-link-effects
                 (:instance proof-number-register-only-block-effects
                            (instructions (proof-number-less-after-pop-code order (proof-world-pc world) yes no))
                            (clobbers '(0)) (world (proof-number-pop-link-after world))))
           :in-theory (disable proof-number-register-only-code-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-less-tail-register-frame
  (implies (and (not (eq (car (proof-world-machine world)) :svc))
                (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp (proof-world-machine world))))
                (unsigned-byte-p 64 (+ 4 (proof-world-pc world))))
           (proof-register-frame-p limit '(0 29 30) world (proof-number-less-tail-after order yes no world)))
  :hints (("Goal"
           :induct (proof-register-frame-p limit '(0 29 30) world
                                           (proof-number-less-tail-after order yes no world)))
          ("Subgoal *1/3" :use ((:instance proof-number-less-tail-observations (register limit))))
          ("Subgoal *1/2" :use ((:instance proof-number-less-tail-observations (register limit))))
          ("Subgoal *1/1" :use ((:instance proof-number-less-tail-observations (register limit)))))
  :rule-classes nil)

(defthm proof-number-less-tail-preserves-heap
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (after (proof-number-less-tail-after order yes no world)))
    (implies (and (proof-heap-p world objects packages)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 (+ 16 sp))
                  (unsigned-byte-p 64 (+ 4 (proof-world-pc world)))
                  (<= (+ 16 sp) (proof-number-machine-stack-end world)))
             (and (proof-preserved-heap-p nil world after objects objects packages)
                  (equal (proof-machine-limit after) (proof-machine-limit world)))))
  :hints (("Goal"
           :use (proof-number-heap-machine-context
                 (:instance proof-number-unwritten-machine-frame-preserves-heap
                            (before world) (after (proof-number-less-tail-after order yes no world)))
                 (:instance proof-number-mod-shift-by-multiple
                            (a (boymoo-model::a64-sp (proof-world-machine world))) (b 16) (times 1))
                 (:instance proof-number-less-tail-observations (register 23))
                 (:instance proof-number-less-tail-observations (register 24))
                 (:instance proof-number-less-tail-observations (register 25))
                 (:instance proof-number-less-tail-observations (register 26))
                 (:instance proof-number-less-tail-observations (register 27))
                 (:instance proof-number-less-tail-observations (register 28)))
           :in-theory (enable proof-number-heap-registers-and-world-tail-agree-p proof-machine-limit)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm less-compare-dispatch-only-writes-link
   (proof-number-register-only-code-p
    (proof-number-less-compare-path pc rational complex complex-case) '(30))
   :hints (("Goal"
            :in-theory (enable proof-number-less-compare-path proof-number-register-only-instruction-p)))))

(local
 (defthm less-compare-dispatch-has-three-instructions
   (equal (len (proof-number-less-compare-path pc rational complex complex-case)) 3)
   :hints (("Goal" :in-theory (enable proof-number-less-compare-path)))))

(local
 (defthm less-comparison-call-keeps-heap
   (implies (and (proof-heap-p world objects packages)
                   (proof-number-world-byte-keys-p world)
                   (proof-number-less-comparison-trace-p
                    a b rational complex yes no link callee-steps world returned objects new-objects packages))
              (and (proof-preserved-heap-p nil world returned objects new-objects packages)
                   (proof-heap-p returned new-objects packages)
                   (proof-number-world-byte-keys-p returned)
                   (equal (boymoo-model::a64-sp (proof-world-machine returned))
                          (boymoo-model::a64-sp (proof-world-machine world)))
                   (equal (proof-machine-limit returned) (proof-machine-limit world))
                   (<= (+ 16 (boymoo-model::a64-sp (proof-world-machine returned)))
                       (proof-number-machine-stack-end returned))))
   :hints (("Goal"
            :use ((:instance proof-number-register-only-execution-preserves-heap
                             (clobbers '(30))
                             (instructions (proof-number-less-compare-path
                                            (proof-world-pc world) rational complex
                                            (equal (proof-world-reg 3 world) 5))))
                  (:instance proof-number-checked-block-exact-prefix
                             (cuts (list link))
                             (instructions (proof-number-less-compare-path
                                            (proof-world-pc world) rational complex
                                            (equal (proof-world-reg 3 world) 5))))
                  (:instance proof-number-exact-prefix-preserves-byte-keys
                             (count 3) (cuts (list link)) (before world)
                             (after (proof-number-less-compare-ready rational complex world)))
                  (:instance proof-number-segment-preserves-byte-keys
                             (count callee-steps) (before (proof-number-less-compare-ready rational complex world))
                             (after returned) (reason :cut)
                             (cuts (list (+ (proof-world-pc world)
                                            (if (equal (proof-world-reg 3 world) 5) 20 12)))))
                  (:instance proof-number-register-frame-keeps
                             (limit 30) (register 23) (clobbers (proof-number-numeric-clobbers))
                             (before (proof-number-less-compare-ready rational complex world)) (after returned))
                  (:instance proof-number-preserved-heaps-compose
                             (before world) (middle (proof-number-less-compare-ready rational complex world))
                             (after returned) (old-objects objects) (middle-objects objects) (objects new-objects))
                  (:instance proof-number-preserved-heap-is-valid
                             (may-intern nil) (before world) (after returned)
                             (old-objects objects) (objects new-objects)))
            :in-theory (e/d (proof-number-less-comparison-trace-p proof-number-less-compare-ready
                             proof-datum-return-p proof-frame-return-p
                             proof-machine-limit proof-number-machine-stack-end
                             proof-number-numeric-clobbers)
                            (proof-register-frame-p proof-number-register-only-code-p
                             proof-number-less-return-path proof-number-less-compare-path proof-stack-top fix))
            :expand ((proof-preserved-heap-p nil (proof-number-less-compare-ready rational complex world)
                                              returned objects new-objects packages))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm less-resume-only-changes-pc
   (proof-number-register-only-code-p (proof-number-less-resume-code complex-case) nil)
   :hints (("Goal" :in-theory (enable proof-number-less-resume-code proof-number-register-only-instruction-p)))))

(local
 (defthm less-tail-code-supplies-pop-bounds
   (let ((sp (boymoo-model::a64-sp (proof-world-machine world))))
     (implies (proof-number-less-tail-code-p order link yes no world)
              (and (not (eq (car (proof-world-machine world)) :svc))
                   (unsigned-byte-p 64 (+ 16 sp))
                   (unsigned-byte-p 64 (+ 4 (proof-world-pc world))))))
   :hints (("Goal"
            :use ((:instance proof-number-pc-range (machine (proof-world-machine world))))
            :in-theory (e/d (proof-number-less-tail-code-p proof-world-pc)
                            (proof-number-less-tail-after proof-number-less-selected
                             proof-number-less-return-path proof-number-less-leaf assoc-equal
                             boymoo-model::a64-pc))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm less-comparison-return-keeps-heap
   (let* ((after (proof-number-less-comparison-after a b yes no returned world))
          (sp (boymoo-model::a64-sp (proof-world-machine returned))))
     (implies (and (proof-heap-p returned new-objects packages)
                   (proof-number-world-byte-keys-p returned)
                   (proof-number-world-byte-keys-p after)
                   (<= (+ 16 sp) (proof-number-machine-stack-end returned))
                   (proof-number-less-comparison-trace-p
                    a b rational complex yes no link callee-steps world returned objects new-objects packages))
              (proof-preserved-heap-p nil returned after new-objects new-objects packages)))
   :hints (("Goal"
            :use ((:instance proof-number-register-only-execution-preserves-heap
                             (clobbers nil) (world returned) (objects new-objects)
                             (instructions (proof-number-less-resume-code (equal (proof-world-reg 3 world) 5))))
                  (:instance less-tail-code-supplies-pop-bounds
                             (order (proof-number-order (fix a) (fix b)))
                             (world (proof-number-less-resumed (equal (proof-world-reg 3 world) 5) returned)))
                  (:instance proof-number-less-tail-preserves-heap
                             (order (proof-number-order (fix a) (fix b))) (objects new-objects)
                             (world (proof-number-less-resumed (equal (proof-world-reg 3 world) 5) returned)))
                  (:instance proof-number-preserved-heap-is-valid
                             (may-intern nil) (before returned) (objects new-objects) (old-objects new-objects)
                             (after (proof-number-less-resumed (equal (proof-world-reg 3 world) 5) returned)))
                  (:instance proof-number-preserved-heaps-compose
                             (before returned)
                             (middle (proof-number-less-resumed (equal (proof-world-reg 3 world) 5) returned))
                             (after (proof-number-less-comparison-after a b yes no returned world))
                             (objects new-objects) (old-objects new-objects) (middle-objects new-objects)))
            :in-theory (e/d (proof-number-less-comparison-trace-p proof-number-less-resumed
                             proof-number-less-comparison-after proof-number-machine-stack-end)
                            (proof-register-frame-p proof-number-register-only-code-p
                             proof-number-less-tail-code-p proof-number-less-compare-path
                             proof-number-order fix))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-less-selected-comparison-preserves-heap
  (let ((after (proof-number-less-comparison-after a b yes no returned world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-world-byte-keys-p after)
                  (proof-number-less-comparison-trace-p
                   a b rational complex yes no link callee-steps world returned objects new-objects packages))
             (proof-preserved-heap-p nil world after objects new-objects packages)))
  :hints (("Goal"
           :use (less-comparison-call-keeps-heap less-comparison-return-keeps-heap
                 (:instance proof-number-preserved-heaps-compose
                            (before world) (middle returned)
                            (after (proof-number-less-comparison-after a b yes no returned world))
                            (old-objects objects) (middle-objects new-objects) (objects new-objects)))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm less-call-register-frame
   (implies (proof-number-less-comparison-trace-p
             a b rational complex yes no link callee-steps world returned objects new-objects packages)
            (proof-register-frame-p 30 (cons 30 (proof-number-numeric-clobbers)) world returned))
   :hints (("Goal"
            :use ((:instance proof-number-register-only-block-keeps-register-frame
                             (limit 30) (clobbers '(30))
                             (instructions (proof-number-less-compare-path
                                            (proof-world-pc world) rational complex
                                            (equal (proof-world-reg 3 world) 5))))
                  (:instance proof-number-register-frames-extend-and-compose
                             (limit 30) (clobbers (cons 30 (proof-number-numeric-clobbers)))
                             (first-clobbers '(30)) (last-clobbers (proof-number-numeric-clobbers))
                             (before world) (middle (proof-number-less-compare-ready rational complex world))
                             (after returned)))
            :in-theory (e/d (proof-number-less-compare-ready proof-number-less-comparison-trace-p
                             proof-datum-return-p proof-frame-return-p proof-number-numeric-clobbers)
                            (proof-register-frame-p proof-number-register-only-code-p
                             proof-number-less-compare-path proof-number-less-tail-code-p))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm less-return-register-frame
   (implies (proof-number-less-comparison-trace-p
             a b rational complex yes no link callee-steps world returned objects new-objects packages)
            (proof-register-frame-p 30 '(0 29 30) returned
                                    (proof-number-less-comparison-after a b yes no returned world)))
   :hints (("Goal"
            :use ((:instance proof-number-register-only-block-keeps-register-frame
                             (limit 30) (clobbers nil) (world returned)
                             (instructions (proof-number-less-resume-code (equal (proof-world-reg 3 world) 5))))
                  (:instance less-tail-code-supplies-pop-bounds
                             (order (proof-number-order (fix a) (fix b)))
                             (world (proof-number-less-resumed (equal (proof-world-reg 3 world) 5) returned)))
                  (:instance proof-number-less-tail-register-frame
                             (limit 30) (order (proof-number-order (fix a) (fix b)))
                             (world (proof-number-less-resumed (equal (proof-world-reg 3 world) 5) returned)))
                  (:instance proof-number-register-frames-extend-and-compose
                             (limit 30) (clobbers '(0 29 30)) (first-clobbers nil) (last-clobbers '(0 29 30))
                             (before returned)
                             (middle (proof-number-less-resumed (equal (proof-world-reg 3 world) 5) returned))
                             (after (proof-number-less-comparison-after a b yes no returned world))))
            :in-theory (e/d (proof-number-less-comparison-trace-p proof-number-less-comparison-after
                             proof-number-less-resumed)
                            (proof-number-register-only-code-p proof-number-order proof-register-frame-p fix))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-less-selected-comparison-register-frame
  (implies (proof-number-less-comparison-trace-p
            a b rational complex yes no link callee-steps world returned objects new-objects packages)
           (proof-register-frame-p 30 (append '(29 30) (proof-number-numeric-clobbers))
                                   world (proof-number-less-comparison-after a b yes no returned world)))
  :hints (("Goal"
           :use (less-call-register-frame less-return-register-frame
                 (:instance proof-number-register-frames-extend-and-compose
                            (limit 30) (clobbers (append '(29 30) (proof-number-numeric-clobbers)))
                            (first-clobbers (cons 30 (proof-number-numeric-clobbers)))
                            (last-clobbers '(0 29 30))
                            (before world) (middle returned)
                            (after (proof-number-less-comparison-after a b yes no returned world))))
           :in-theory (e/d (proof-number-numeric-clobbers) (proof-register-frame-p))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-general-less-after (a b types classifier yes no returned world)
  (proof-number-less-comparison-after
   a b yes no returned (proof-number-binary-types-call-after types classifier world)))

(defund proof-number-general-less-steps (a b types classifier callee-steps world)
  (+ 2 (proof-number-types-completion-steps nil classifier (proof-number-types-first-ready types world))
     (proof-number-less-comparison-steps a b callee-steps
                                         (proof-number-binary-types-call-after types classifier world))))

(defund proof-number-general-less-trace-p
    (a b types classifier rational complex yes no callee-steps world returned objects new-objects packages)
  (let ((link (proof-world-reg 30 world))
        (completed (proof-number-binary-types-call-after types classifier world)))
    (and (proof-number-binary-wrapper-save-intervals-p types world objects)
         (proof-number-binary-types-call-trace-p types classifier (list link) a b world objects packages)
         (proof-number-less-comparison-trace-p a b rational complex yes no link callee-steps
                                               completed returned objects new-objects packages))))

(local
 (defthm general-less-preserves-heap
   (let ((after (proof-number-general-less-after a b types classifier yes no returned world)))
     (implies (and (proof-heap-p world objects packages)
                   (proof-number-world-byte-keys-p world)
                   (proof-number-general-less-trace-p a b types classifier rational complex yes no callee-steps
                                                       world returned objects new-objects packages))
              (and (proof-preserved-heap-p nil world after objects new-objects packages)
                   (proof-heap-p after new-objects packages))))
   :hints (("Goal"
            :use (proof-number-general-less-returns-boolean
                  (:instance proof-number-binary-wrapper-preserves-heap-while-saved
                             (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-number-less-selected-comparison-preserves-heap
                             (link (proof-world-reg 30 world))
                             (world (proof-number-binary-types-call-after types classifier world)))
                  (:instance proof-number-segment-preserves-byte-keys
                             (count (proof-number-general-less-steps a b types classifier callee-steps world))
                             (cuts (list (proof-world-reg 30 world))) (before world) (reason :cut)
                             (after (proof-number-general-less-after a b types classifier yes no returned world)))
                  (:instance proof-number-preserved-heaps-compose
                             (before world) (middle (proof-number-binary-types-call-after types classifier world))
                             (after (proof-number-general-less-after a b types classifier yes no returned world))
                             (old-objects objects) (middle-objects objects) (objects new-objects))
                  (:instance proof-number-preserved-heap-is-valid
                             (may-intern nil) (before world)
                             (after (proof-number-general-less-after a b types classifier yes no returned world))
                             (old-objects objects) (objects new-objects)))
            :in-theory (e/d (proof-number-general-less-trace-p
                             proof-number-general-less-after proof-number-general-less-steps)
                            (proof-number-less-comparison-steps proof-number-binary-types-call-trace-p fix))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm general-less-keeps-register-frame
   (implies (proof-number-general-less-trace-p a b types classifier rational complex yes no callee-steps
                                               world returned objects new-objects packages)
            (proof-register-frame-p 30 (proof-number-numeric-clobbers)
                                    world (proof-number-general-less-after a b types classifier yes no returned world)))
   :hints (("Goal"
            :use (proof-number-general-less-returns-boolean
                  (:instance proof-number-binary-wrapper-register-frame-while-saved
                             (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-number-less-selected-comparison-register-frame
                             (link (proof-world-reg 30 world))
                             (world (proof-number-binary-types-call-after types classifier world)))
                  (:instance proof-number-register-frames-extend-and-compose
                             (limit 30) (clobbers (append '(29 30) (proof-number-numeric-clobbers)))
                             (first-clobbers (cons 30 (proof-number-numeric-clobbers)))
                             (last-clobbers (append '(29 30) (proof-number-numeric-clobbers)))
                             (before world) (middle (proof-number-binary-types-call-after types classifier world))
                             (after (proof-number-general-less-after a b types classifier yes no returned world)))
                  (:instance proof-number-register-frame-can-keep-restored-register
                             (limit 30) (register 29) (clobbers (cons 30 (proof-number-numeric-clobbers)))
                             (before world)
                             (after (proof-number-general-less-after a b types classifier yes no returned world)))
                  (:instance proof-number-register-frame-can-keep-restored-register
                             (limit 30) (register 30) (clobbers (proof-number-numeric-clobbers))
                             (before world)
                             (after (proof-number-general-less-after a b types classifier yes no returned world))))
            :in-theory (e/d (proof-number-general-less-trace-p proof-number-general-less-after
                             proof-number-numeric-clobbers)
                            (proof-number-less-comparison-steps proof-number-binary-types-call-trace-p
                             proof-register-frame-p fix))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-general-less-runtime-return
  (let* ((args (list a b))
         (after (proof-number-general-less-after a b types classifier yes no returned world))
         (steps (proof-number-general-less-steps a b types classifier callee-steps world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-general-less-trace-p a b types classifier rational complex yes no callee-steps
                                                      world returned objects new-objects packages))
             (and (proof-segment-p steps (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p '< args program world after objects new-objects packages))))
  :hints (("Goal"
           :use (proof-number-general-less-returns-boolean general-less-preserves-heap general-less-keeps-register-frame
                 proof-number-heap-machine-context proof-number-public-value-completions
                 (:instance proof-number-numeric-runtime-return-contract
                            (name '<) (args (list a b)) (before world) (old-objects objects) (objects new-objects)
                            (after (proof-number-general-less-after a b types classifier yes no returned world)))
                 (:instance proof-number-heap-machine-context
                            (world (proof-number-general-less-after a b types classifier yes no returned world))
                            (objects new-objects))
                 (:instance proof-number-boolean-words-have-views
                            (world (proof-number-general-less-after a b types classifier yes no returned world))
                            (objects new-objects)))
           :in-theory (e/d (proof-number-general-less-trace-p proof-number-general-less-after
                            proof-number-general-less-steps proof-datum-return-p proof-frame-return-p
                            proof-reg-value-p)
                           (proof-runtime-return-p proof-runtime-value proof-machine-value-p
                            proof-register-frame-p proof-number-less-comparison-steps
                            proof-number-binary-types-call-trace-p fix))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-public-general-less-runtime-return
  (let* ((args (list a b))
         (middle (proof-number-general-gate-after 2 general world))
         (after (proof-number-general-less-after a b types classifier yes no returned middle))
         (steps (proof-number-general-less-steps a b types classifier callee-steps middle)))
    (implies (and (proof-runtime-pre-p '< args program labels base world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-general-gate-trace-p 2 general world)
                  (proof-number-general-less-trace-p a b types classifier rational complex yes no callee-steps
                                                      middle returned objects new-objects packages))
             (and (proof-segment-p (+ 3 steps) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p '< args program world after objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-runtime-entry-has-heap (name '<) (args (list a b)))
                 (:instance proof-number-general-tag-gate-reaches-runtime (arity 2) (register 30))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count 3) (cuts (list (proof-world-reg 30 world))) (before world)
                            (after (proof-number-general-gate-after 2 general world)))
                 (:instance proof-number-general-less-runtime-return
                            (world (proof-number-general-gate-after 2 general world)))
                 (:instance proof-number-public-tag-gate-compose-return
                            (name '<) (args (list a b)) (old-objects objects) (objects new-objects)
                            (steps (proof-number-general-less-steps
                                    a b types classifier callee-steps (proof-number-general-gate-after 2 general world)))
                            (after (proof-number-general-less-after
                                    a b types classifier yes no returned
                                    (proof-number-general-gate-after 2 general world)))))
           :in-theory (e/d (proof-number-general-less-trace-p proof-number-general-less-steps
                            proof-number-less-comparison-steps proof-number-less-comparison-trace-p)
                           (proof-runtime-pre-p proof-runtime-return-p proof-number-binary-types-call-trace-p
                            proof-heap-p proof-number-order fix))
           :do-not-induct t))
  :rule-classes nil)
