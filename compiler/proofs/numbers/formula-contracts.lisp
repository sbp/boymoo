(in-package "BOYMOO-PROOFS")

(include-book "formula-growth")
(include-book "public-delegation")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p proof-number-checked-block-p
                     proof-execute proof-instruction-effect
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-heap-layout-p proof-preserved-heap-p proof-heap-frame-p
                     proof-prefix-preserved-p proof-dynamic-table-preserved-p proof-stack-prefix
                     proof-stack-top proof-stack-base proof-stack-limit proof-heap-base
                     proof-machine-limit proof-load-word proof-reg-value-p
                     proof-datum-return-p proof-frame-return-p
                     proof-number-formula-growth-trace-p proof-number-formula-argument-trace-p
                     proof-number-formula-body-trace-p proof-number-formula-calls proof-number-formula-result-p
                     proof-number-argument-list-p proof-number-formula-argument-store-instructions
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defund proof-number-formula-frame-clobbers ()
  (list* 19 25 30 (proof-number-numeric-clobbers)))

(local
 (defthm growth-trace-has-natural-step-count
   (implies (proof-number-formula-growth-trace-p name grow steps world grown objects grown-objects packages)
            (natp steps))
   :hints (("Goal"
            :in-theory (enable proof-number-formula-growth-trace-p)))
   :rule-classes nil))

(defthm proof-number-formula-entry-preserves-heap-and-register-frame
  (let* ((link (proof-world-reg 30 world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (body (proof-number-formula-arguments-after args grown))
         (start (len (cdr (proof-stack-prefix (proof-stack-top grown) grown grown-objects packages)))))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-save-interval-p (- sp 16) world objects)
                  (proof-number-formula-growth-trace-p name grow steps world grown
                                                       objects grown-objects packages)
                  (proof-number-formula-argument-trace-p args link grown grown-objects packages)
                  (proof-number-value-append-pre-p (len args) grown grown-objects packages))
             (and (proof-preserved-heap-p nil world body objects grown-objects packages)
                  (proof-heap-p body grown-objects packages)
                  (proof-number-world-byte-keys-p body)
                  (proof-register-frame-p 30 (proof-number-formula-frame-clobbers) world body)
                  (equal (proof-machine-limit body) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine body)) (- sp 16))
                  (equal (proof-world-reg 19 body) (proof-stack-top world))
                  (proof-number-frame-p start args body grown-objects packages))))
  :hints (("Goal"
           :use (growth-trace-has-natural-step-count
                 (:instance proof-number-formula-growth-preserves-heap-and-register-frame
                            (new-objects grown-objects))
                 (:instance proof-number-heap-machine-context (world grown) (objects grown-objects))
                 (:instance proof-number-formula-entry-initializes-frame (new-objects grown-objects))
                 (:instance proof-number-formula-frame-has-initialized-prefix
                            (slots args) (world (proof-number-formula-arguments-after args grown))
                            (objects grown-objects)
                            (start (len (cdr (proof-stack-prefix (proof-stack-top grown)
                                                                 grown grown-objects packages)))))
                 (:instance proof-number-value-append-preserves-heap
                            (arity (len args)) (world grown) (objects grown-objects))
                 (:instance proof-number-value-append-keeps-layout-coordinates
                            (arity (len args)) (world grown) (objects grown-objects))
                 (:instance proof-number-value-append-register-frame
                            (arity (len args)) (world grown) (objects grown-objects) (limit 30))
                 (:instance proof-number-register-frame-keeps
                            (limit 30) (register 19) (clobbers '(25))
                            (before grown) (after (proof-number-formula-arguments-after args grown)))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count (+ 6 steps)) (cuts (list (proof-world-reg 30 world))) (before world)
                            (after (proof-number-formula-arguments-after args grown)))
                 (:instance proof-number-preserved-heaps-compose
                            (before world) (middle grown) (after (proof-number-formula-arguments-after args grown))
                            (old-objects objects) (middle-objects grown-objects) (objects grown-objects))
                 (:instance proof-number-preserved-heap-is-valid (may-intern nil)
                            (before world) (after (proof-number-formula-arguments-after args grown))
                            (old-objects objects) (objects grown-objects))
                 (:instance proof-number-register-frames-extend-and-compose
                            (limit 30) (first-clobbers (list* 19 30 (proof-number-numeric-clobbers)))
                            (last-clobbers '(25)) (clobbers (proof-number-formula-frame-clobbers))
                            (before world) (middle grown) (after (proof-number-formula-arguments-after args grown))))
           :in-theory (e/d (proof-number-formula-arguments-after proof-number-formula-frame-clobbers
                            proof-number-numeric-clobbers)
                           (proof-register-frame-p proof-streams-preserved-p
                            proof-number-frame-address proof-number-formula-argument-store-instructions))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm formula-slot-table-lookup
   (implies (and (proof-number-formula-table-p rows) (assoc-equal name rows))
            (let ((row (assoc-equal name rows)))
              (proof-number-call-slots-p (caddr row) (cadr row))))
   :hints (("Goal"
            :induct (assoc-equal name rows)
            :in-theory (disable proof-number-call-slots-p)))
   :rule-classes nil))

(local
 (defthm formula-result-uses-initialized-slots
   (implies (proof-number-formula-result-p name args gcd result)
            (and (consp (proof-number-formula-calls name))
                 (proof-number-call-slots-p (proof-number-formula-calls name) (len args))))
   :hints (("Goal"
            :use (proof-number-generated-formulas-use-initialized-slots
                  (:instance formula-slot-table-lookup (rows *proof-number-formulas*)))
            :in-theory (e/d (proof-number-formula-result-p proof-number-formula-calls)
                            (proof-number-formula-table-p proof-number-call-slots-p
                             proof-number-evaluate-calls assoc-equal last))
            :do-not-induct t))
   :rule-classes nil))

(defund proof-number-formula-contract-trace-p
    (name args gcd grow growth-steps targets trace world grown objects grown-objects packages)
  (and (proof-number-formula-return-trace-p name args gcd grow growth-steps targets trace
                                           world grown objects grown-objects packages)
       (proof-number-value-append-pre-p (len args) grown grown-objects packages)
       (proof-number-formula-spill-storage-p (proof-number-formula-calls name) trace packages)))

(local
 (defthm formula-preserves-context-before-epilogue
   (let* ((machine (proof-world-machine world))
          (returned (cadar (last trace)))
          (new-objects (caddar (last trace)))
          (clobbers (proof-number-formula-frame-clobbers)))
     (implies (and (proof-heap-p world objects packages)
                   (proof-number-world-byte-keys-p world)
                   (proof-number-save-interval-p (- (boymoo-model::a64-sp machine) 16) world objects)
                   (proof-number-formula-result-p name args gcd result)
                   (proof-number-formula-contract-trace-p
                    name args gcd grow growth-steps targets trace world grown objects grown-objects packages))
              (and (proof-preserved-heap-p nil world returned objects new-objects packages)
                   (proof-heap-p returned new-objects packages)
                   (proof-register-frame-p 30 clobbers world returned)
                   (proof-number-world-byte-keys-p returned)
                   (equal (proof-machine-limit returned) (proof-machine-limit world))
                   (equal (proof-world-reg 19 returned) (proof-stack-top world))
                   (equal (boymoo-model::a64-sp (proof-world-machine returned))
                          (- (boymoo-model::a64-sp machine) 16)))))
   :hints (("Goal"
            :use (formula-result-uses-initialized-slots
                  (:instance proof-number-formula-entry-preserves-heap-and-register-frame (steps growth-steps))
                  (:instance proof-number-formula-body-preserves-heap-and-register-frame
                             (calls (proof-number-formula-calls name))
                             (world (proof-number-formula-arguments-after args grown)) (slots args)
                             (link (proof-world-reg 30 world)) (objects grown-objects)
                             (start (len (cdr (proof-stack-prefix (proof-stack-top grown) grown grown-objects packages)))))
                  (:instance proof-number-preserved-heaps-compose
                             (before world) (middle (proof-number-formula-arguments-after args grown))
                             (after (cadar (last trace)))
                             (old-objects objects) (middle-objects grown-objects) (objects (caddar (last trace))))
                  (:instance proof-number-register-frames-extend-and-compose
                             (limit 30) (first-clobbers (proof-number-formula-frame-clobbers))
                             (last-clobbers (list* 25 30 (proof-number-numeric-clobbers)))
                             (clobbers (proof-number-formula-frame-clobbers)) (before world)
                             (middle (proof-number-formula-arguments-after args grown)) (after (cadar (last trace))))
                  (:instance proof-number-register-frame-keeps
                             (limit 30) (register 19) (clobbers (list* 25 30 (proof-number-numeric-clobbers)))
                             (before (proof-number-formula-arguments-after args grown)) (after (cadar (last trace)))))
            :in-theory (e/d (proof-number-formula-contract-trace-p proof-number-formula-return-trace-p
                             proof-number-formula-frame-clobbers proof-number-numeric-clobbers)
                            (proof-register-frame-p proof-number-formula-spill-storage-p
                             proof-number-formula-spills-in-value-stack-p last))
            :do-not-induct t))
   :rule-classes nil))

(defund proof-number-formula-epilogue-after (world)
  (proof-number-execute-block *proof-number-formula-return-instructions* world))

(local
 (defthm formula-epilogue-machine-effects
   (let* ((first (proof-world-machine world))
          (after (proof-number-formula-epilogue-after world))
          (last (proof-world-machine after)))
     (implies (and (not (eq (car first) :svc))
                   (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp first))))
              (and (equal (cdr after) (cdr world))
                   (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory first))
                   (equal (boymoo-model::a64-sp last) (+ 16 (boymoo-model::a64-sp first)))
                   (equal (proof-stack-top after) (proof-world-reg 19 world))
                   (implies (not (member-equal register '(19 25 30)))
                            (equal (proof-world-reg register after) (proof-world-reg register world))))))
   :hints (("Goal"
            :in-theory (e/d (proof-number-formula-epilogue-after proof-number-execute-block
                             proof-world-reg proof-stack-top)
                            (proof-reg boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                             boymoo-model::a64-unsigned boymoo-model::a64-set-pc boymoo-model::a64-pc
                             boymoo-model::a64-nzcv (:definition nth) (:definition update-nth)))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-formula-epilogue-register-frame
  (implies (and (not (eq (car (proof-world-machine world)) :svc))
                (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp (proof-world-machine world)))))
           (proof-register-frame-p limit '(19 25 30) world (proof-number-formula-epilogue-after world)))
  :hints (("Goal"
           :induct (proof-register-frame-p limit '(19 25 30) world (proof-number-formula-epilogue-after world)))
          ("Subgoal *1/3" :use ((:instance formula-epilogue-machine-effects (register limit))))
          ("Subgoal *1/2" :use ((:instance formula-epilogue-machine-effects (register limit))))
          ("Subgoal *1/1" :use ((:instance formula-epilogue-machine-effects (register limit)))))
  :rule-classes nil)

(local
 (defthm formula-epilogue-keeps-layout-coordinates
   (let* ((first (proof-world-machine world))
          (after (proof-number-formula-epilogue-after world)))
     (implies (and (proof-heap-layout-p world)
                   (not (eq (car first) :svc))
                   (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp first))))
              (and (equal (proof-number-heap-coordinates world) (proof-number-heap-coordinates after))
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (proof-streams-preserved-p world after))))
   :hints (("Goal"
            :use ((:instance formula-epilogue-machine-effects (register 23))
                  (:instance formula-epilogue-machine-effects (register 24))
                  (:instance formula-epilogue-machine-effects (register 26))
                  (:instance formula-epilogue-machine-effects (register 27))
                  (:instance formula-epilogue-machine-effects (register 28))
                  (:instance proof-number-heap-layout-range-bounds)
                  (:instance proof-number-heap-layout-separates-reservations)
                  (:instance proof-number-same-world-tail-keeps-layout-observations
                             (before world) (after (proof-number-formula-epilogue-after world)))
                  (:instance proof-number-span-agreement-with-same-memory
                             (start (- (proof-heap-base world) 128)) (end (+ (proof-heap-base world) 32))
                             (first (proof-world-machine world))
                             (last (proof-world-machine (proof-number-formula-epilogue-after world))))
                  (:instance proof-number-metadata-span-keeps-heap-coordinates
                             (before world) (after (proof-number-formula-epilogue-after world))))
            :in-theory (e/d (proof-heap-base proof-machine-limit proof-stack-limit proof-heap-limit proof-box-top)
                            (proof-streams-preserved-p proof-disjoint-p proof-static-size))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm heap-value-top-fits-and-is-aligned
   (implies (proof-heap-p world objects packages)
            (and (<= (proof-stack-top world) (proof-stack-limit world))
                 (equal (mod (proof-stack-top world) 8) 0)))
   :hints (("Goal"
            :expand ((proof-heap-p world objects packages) (proof-heap-layout-p world))
            :in-theory (disable proof-align-up proof-covered-p proof-runtime-word proof-regions-p
                                proof-disjoint-p proof-static-p proof-external-objects proof-object-map-p
                                proof-heap-object-spans-p proof-dynamic-symbol-objects-p
                                proof-dynamic-entries proof-dynamic-view proof-string-accounting-p)))
   :rule-classes nil))

(defthm proof-number-formula-epilogue-preserves-heap-window
  (let* ((first (proof-world-machine world))
         (sp (boymoo-model::a64-sp first))
         (after (proof-number-formula-epilogue-after world))
         (top (proof-world-reg 19 world)))
    (implies (and (proof-heap-p world objects packages)
                  (not (eq (car first) :svc))
                  (unsigned-byte-p 64 (+ 16 sp))
                  (<= (+ 16 sp) (proof-number-machine-stack-end world))
                  (equal (mod top 8) 0)
                  (proof-stack-prefix top world objects packages))
             (and (proof-heap-p after objects packages)
                  (proof-heap-frame-p world after)
                  (proof-dynamic-table-preserved-p nil world after objects objects packages)
                  (proof-prefix-preserved-p top world after objects objects packages)
                  (equal (proof-stack-top after) top))))
  :hints (("Goal"
           :use (proof-number-heap-machine-context heap-value-top-fits-and-is-aligned
                 formula-epilogue-keeps-layout-coordinates
                 (:instance formula-epilogue-machine-effects (register 23))
                 (:instance proof-number-stack-prefix-bounds (top (proof-world-reg 19 world)))
                 (:instance proof-number-coordinate-equality-keeps-layout
                            (before world) (after (proof-number-formula-epilogue-after world)))
                 (:instance proof-number-mod-shift-by-multiple
                            (a (boymoo-model::a64-sp (proof-world-machine world))) (b 16) (times 1))
                 (:instance proof-number-value-stack-drop-keeps-heap-window
                            (before world) (after (proof-number-formula-epilogue-after world))))
           :in-theory (e/d (proof-number-machine-stack-end)
                           (proof-streams-preserved-p proof-number-machine-span-agrees-p))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm formula-epilogue-closes-heap-frame
   (let* ((stack (proof-stack-top before))
          (after (proof-number-formula-epilogue-after middle))
          (sp (boymoo-model::a64-sp (proof-world-machine middle))))
     (implies (and (proof-heap-p before old-objects packages)
                   (proof-preserved-heap-p nil before middle old-objects objects packages)
                   (proof-number-world-byte-keys-p before)
                   (proof-number-world-byte-keys-p after)
                   (not (eq (car (proof-world-machine middle)) :svc))
                   (unsigned-byte-p 64 (+ 16 sp))
                   (equal (+ 16 sp) (boymoo-model::a64-sp (proof-world-machine before)))
                   (equal (proof-machine-limit middle) (proof-machine-limit before))
                   (equal (proof-world-reg 19 middle) stack))
              (and (proof-heap-p after objects packages)
                   (proof-preserved-heap-p nil before after old-objects objects packages)
                   (equal (proof-stack-top after) stack))))
   :hints (("Goal"
            :use ((:instance proof-number-heap-machine-context (world before) (objects old-objects))
                  (:instance heap-value-top-fits-and-is-aligned (world before) (objects old-objects))
                  (:instance proof-number-formula-epilogue-preserves-heap-window (world middle))
                  (:instance proof-number-heap-frames-compose
                             (after (proof-number-formula-epilogue-after middle))))
            :in-theory (e/d (proof-preserved-heap-p proof-prefix-preserved-p
                             proof-dynamic-table-preserved-p proof-number-machine-stack-end)
                            (proof-dynamic-view proof-dynamic-entries proof-heap-frame-p))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm formula-epilogue-closes-register-frame
   (let ((after (proof-number-formula-epilogue-after middle)))
     (implies (and (proof-register-frame-p 30 (proof-number-formula-frame-clobbers) before middle)
                   (not (eq (car (proof-world-machine middle)) :svc))
                   (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp (proof-world-machine middle))))
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                   (equal (proof-world-reg 25 after) (proof-world-reg 25 before))
                   (equal (proof-world-reg 30 after) (proof-world-reg 30 before)))
              (proof-register-frame-p 30 (proof-number-numeric-clobbers) before after)))
   :hints (("Goal"
            :use ((:instance proof-number-formula-epilogue-register-frame (world middle) (limit 30))
                  (:instance proof-number-register-frames-extend-and-compose
                             (limit 30) (clobbers (proof-number-formula-frame-clobbers))
                             (first-clobbers (proof-number-formula-frame-clobbers))
                             (last-clobbers '(19 25 30)) (after (proof-number-formula-epilogue-after middle)))
                  (:instance proof-number-register-frame-can-keep-restored-register
                             (limit 30) (register 19) (clobbers (list* 25 30 (proof-number-numeric-clobbers)))
                             (after (proof-number-formula-epilogue-after middle)))
                  (:instance proof-number-register-frame-can-keep-restored-register
                             (limit 30) (register 25) (clobbers (cons 30 (proof-number-numeric-clobbers)))
                             (after (proof-number-formula-epilogue-after middle)))
                  (:instance proof-number-register-frame-can-keep-restored-register
                             (limit 30) (register 30) (clobbers (proof-number-numeric-clobbers))
                             (after (proof-number-formula-epilogue-after middle))))
            :in-theory (e/d (proof-number-formula-frame-clobbers proof-number-numeric-clobbers)
                            (proof-register-frame-p))
            :do-not-induct t))
   :rule-classes nil))

(defund proof-number-formula-contract-steps (name growth-steps trace)
  (+ 9 growth-steps (proof-number-formula-trace-steps (proof-number-formula-calls name) trace)))

(defthm proof-number-generated-formula-datum-return
  (let* ((link (proof-world-reg 30 world))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (count (proof-number-formula-contract-steps name growth-steps trace))
         (after (proof-number-formula-trace-after trace))
         (new-objects (caddar (last trace))))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-save-interval-p (- sp 16) world objects)
                  (proof-number-formula-result-p name args gcd result)
                  (proof-number-formula-contract-trace-p
                   name args gcd grow growth-steps targets trace world grown objects grown-objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (proof-datum-return-p result (proof-number-numeric-clobbers) t t nil
                                        world after objects new-objects packages))))
  :hints (("Goal"
           :use (formula-preserves-context-before-epilogue
                 proof-number-generated-formula-return-with-saved-link
                 proof-number-heap-machine-context
                 (:instance proof-number-heap-machine-context
                            (world (proof-number-formula-trace-after trace)) (objects (caddar (last trace))))
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (proof-number-formula-contract-steps name growth-steps trace))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (after (proof-number-formula-trace-after trace)) (reason :cut))
                 (:instance formula-epilogue-closes-heap-frame
                            (before world) (middle (cadar (last trace)))
                            (old-objects objects) (objects (caddar (last trace))))
                 (:instance formula-epilogue-closes-register-frame
                            (before world) (middle (cadar (last trace)))))
           :in-theory (e/d (proof-number-formula-contract-trace-p proof-number-formula-return-trace-p
                            proof-number-formula-contract-steps proof-number-formula-trace-after
                            proof-number-formula-epilogue-after proof-stack-top
                            proof-datum-return-p proof-frame-return-p)
                           (proof-register-frame-p proof-number-formula-body-trace-p
                            proof-number-formula-trace-steps proof-number-formula-spill-storage-p
                            proof-number-formula-spills-in-value-stack-p last))
           :do-not-induct t))
  :rule-classes nil)
