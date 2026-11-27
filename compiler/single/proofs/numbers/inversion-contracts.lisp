(in-package "BOYMOO-PROOFS")

(include-book "arithmetic-returns")
(include-book "raw-return")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-heap-layout-p proof-preserved-heap-p proof-datum-return-p
                     proof-frame-return-p proof-reg-value-p proof-number-reduced-p
                     proof-number-formula-result-p proof-number-formula-contract-trace-p
                     proof-number-invert-path
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defund proof-number-inversion-dispatch-trace-p (a zero negative box world)
  (let* ((path (proof-number-invert-path a zero negative box world))
         (target (proof-number-invert-target a zero negative box))
         (link (proof-world-reg 30 world)))
    (and (not (eq (car (proof-world-machine world)) :svc))
         (unsigned-byte-p 64 (+ 56 (proof-world-pc world)))
         (unsigned-byte-p 64 target)
         (proof-number-checked-block-p path (list target) world)
         (proof-number-checked-block-p path (list link) world))))

(local
 (defthm inversion-code-only-uses-scratch-registers
   (proof-number-register-only-code-p (proof-number-invert-path a zero negative box world) '(0 1 2))
   :hints (("Goal"
            :in-theory (enable proof-number-invert-instructions proof-number-invert-path
                               proof-number-register-only-instruction-p)
            :do-not-induct t))))

(defthm proof-number-inversion-dispatch-keeps-heap
  (let* ((path (proof-number-invert-path a zero negative box world))
         (after (proof-number-execute-block path world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-inversion-dispatch-trace-p a zero negative box world))
             (and (proof-number-exact-prefix-p (len path) (list (proof-world-reg 30 world)) world after)
                  (proof-preserved-heap-p nil world after objects objects packages)
                  (proof-heap-p after objects packages)
                  (proof-register-frame-p 30 '(0 1 2) world after)
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (proof-machine-limit after) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world))))))
  :hints (("Goal"
           :use ((:instance proof-number-register-only-execution-preserves-heap
                            (instructions (proof-number-invert-path a zero negative box world)) (clobbers '(0 1 2)))
                 (:instance proof-number-register-only-block-effects
                            (register 30) (instructions (proof-number-invert-path a zero negative box world))
                            (clobbers '(0 1 2)))
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-invert-path a zero negative box world))
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-preserved-heap-is-valid
                            (may-intern nil) (before world) (old-objects objects)
                            (after (proof-number-execute-block (proof-number-invert-path a zero negative box world)
                                                                world))))
           :in-theory (e/d (proof-number-inversion-dispatch-trace-p)
                           (proof-register-frame-p proof-number-register-only-code-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-inversion-returns-through-helper
  (let* ((path (proof-number-invert-path a zero negative box world))
         (entered (proof-number-execute-block path world))
         (link (proof-world-reg 30 world))
         (result (/ (/ a b))))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-inversion-dispatch-trace-p a zero negative box world)
                  (natp steps)
                  (proof-segment-p steps (list link) entered :cut after)
                  (proof-datum-return-p result (proof-number-numeric-clobbers) t t nil
                                        entered after objects new-objects packages))
             (and (proof-segment-p (+ (len path) steps) (list link) world :cut after)
                  (proof-datum-return-p result (proof-number-numeric-clobbers) t t nil
                                        world after objects new-objects packages))))
  :hints (("Goal"
           :use (proof-number-inversion-dispatch-keeps-heap
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (len (proof-number-invert-path a zero negative box world)))
                            (suffix steps) (cuts (list (proof-world-reg 30 world))) (before world) (reason :cut)
                            (middle (proof-number-execute-block (proof-number-invert-path a zero negative box world)
                                                                 world)))
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (+ (len (proof-number-invert-path a zero negative box world)) steps))
                            (cuts (list (proof-world-reg 30 world))) (before world) (reason :cut))
                 (:instance proof-number-numeric-tail-transfer-returns
                            (datum (/ (/ a b))) (clobbers '(0 1 2)) (before world)
                            (middle (proof-number-execute-block (proof-number-invert-path a zero negative box world)
                                                                 world))
                            (old-objects objects) (middle-objects objects) (objects new-objects)))
           :in-theory (e/d (proof-number-numeric-clobbers) (proof-register-frame-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-negative-inversion-datum-return
  (let* ((name "rt:q-invert-negative")
         (args (list a b))
         (path (proof-number-invert-path a zero negative box world))
         (entered (proof-number-execute-block path world))
         (count (proof-number-formula-contract-steps name growth-steps trace))
         (after (proof-number-formula-trace-after trace))
         (result (/ (/ a b))))
    (implies (and (proof-number-reduced-p a b) (< a 0)
                  (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-inversion-dispatch-trace-p a zero negative box world)
                  (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine entered)) 16)
                                                entered objects)
                  (proof-number-formula-contract-trace-p name args gcd grow growth-steps targets trace
                                                         entered grown objects grown-objects packages))
             (and (proof-segment-p (+ (len path) count) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-datum-return-p result (proof-number-numeric-clobbers) t t nil
                                        world after objects (caddar (last trace)) packages))))
  :hints (("Goal"
           :use (proof-number-q-invert-negative-formula proof-number-inversion-dispatch-keeps-heap
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count (len (proof-number-invert-path a zero negative box world)))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (after (proof-number-execute-block (proof-number-invert-path a zero negative box world)
                                                                 world)))
                 (:instance proof-number-generated-formula-datum-return
                            (name "rt:q-invert-negative") (args (list a b)) (result (/ (/ a b)))
                            (world (proof-number-execute-block (proof-number-invert-path a zero negative box world)
                                                                world)))
                 (:instance proof-number-formula-contract-step-count-is-natural
                            (name "rt:q-invert-negative") (args (list a b))
                            (world (proof-number-execute-block (proof-number-invert-path a zero negative box world)
                                                                world)))
                 (:instance proof-number-inversion-returns-through-helper
                            (steps (proof-number-formula-contract-steps "rt:q-invert-negative" growth-steps trace))
                            (after (proof-number-formula-trace-after trace)) (new-objects (caddar (last trace)))))
           :in-theory (disable proof-register-frame-p last)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm reduced-inversion-denominator-is-positive
   (implies (proof-number-reduced-p a b) (posp b))
   :hints (("Goal" :in-theory (enable proof-number-reduced-p)))
   :rule-classes nil))

(defthm proof-number-positive-inversion-datum-return
  (let* ((path (proof-number-invert-path a zero negative box world))
         (entered (proof-number-execute-block path world))
         (link (proof-world-reg 30 world)))
    (implies (and (posp a) (proof-number-reduced-p a b)
                  (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-inversion-dispatch-trace-p a zero negative box world)
                  (natp steps)
                  (proof-segment-p steps (list link) entered :cut after)
                  (proof-datum-return-p (/ b a) (proof-number-numeric-clobbers) t t nil
                                        entered after objects new-objects packages))
             (and (proof-number-reduced-p b a)
                  (proof-register-arguments-p (list b a) 0 entered objects packages)
                  (proof-segment-p (+ (len path) steps) (list link) world :cut after)
                  (proof-datum-return-p (/ (/ a b)) (proof-number-numeric-clobbers) t t nil
                                        world after objects new-objects packages))))
  :hints (("Goal"
           :use (proof-number-inversion-returns-through-helper proof-number-reciprocal-from-parts
                 reduced-inversion-denominator-is-positive
                 (:instance proof-number-positive-inversion-returns-through-box (box-steps steps)))
           :in-theory (e/d (proof-number-inversion-dispatch-trace-p proof-number-invert-target)
                           (proof-register-frame-p proof-register-arguments-p))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm inversion-blocks-keep-register-restriction
   (equal (proof-number-register-only-code-p (append first second) clobbers)
          (and (proof-number-register-only-code-p first clobbers)
               (proof-number-register-only-code-p second clobbers)))
   :hints (("Goal" :induct (len first)))))

(local
 (defthm inversion-heap-is-running
   (implies (proof-heap-p world objects packages) (not (proof-world-stop world)))
   :hints (("Goal"
            :use proof-number-heap-machine-context
            :in-theory (disable proof-object-map-p proof-number-machine-stack-end)))
   :rule-classes nil))

(local
 (defthm zero-inversion-machine-frame
   (let* ((path (proof-number-invert-path 0 zero negative box world))
          (code (cdr (assoc-equal "rt:zero" *proof-number-leaf-returns*)))
          (after (proof-number-execute-block code (proof-number-execute-block path world))))
     (implies (and (proof-heap-p world objects packages)
                   (not (eq (car (proof-world-machine world)) :svc)))
              (and (proof-preserved-heap-p nil world after objects objects packages)
                   (proof-heap-p after objects packages)
                   (proof-register-frame-p 30 (proof-number-numeric-clobbers) world after)
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world))))))
   :hints (("Goal"
            :use ((:instance proof-number-register-only-execution-preserves-heap
                             (clobbers '(0 1 2))
                             (instructions (append (proof-number-invert-path 0 zero negative box world)
                                                   (cdr (assoc-equal "rt:zero" *proof-number-leaf-returns*)))))
                  (:instance proof-number-preserved-heap-is-valid (may-intern nil) (before world) (old-objects objects)
                             (after (proof-number-execute-block
                                     (cdr (assoc-equal "rt:zero" *proof-number-leaf-returns*))
                                     (proof-number-execute-block (proof-number-invert-path 0 zero negative box world)
                                                                 world))))
                  (:instance proof-number-register-frame-allows-more-clobbers
                             (limit 30) (clobbers '(0 1 2)) (extended (proof-number-numeric-clobbers))
                             (before world)
                             (after (proof-number-execute-block
                                     (cdr (assoc-equal "rt:zero" *proof-number-leaf-returns*))
                                     (proof-number-execute-block (proof-number-invert-path 0 zero negative box world)
                                                                 world)))))
            :in-theory (e/d (proof-number-register-only-instruction-p proof-number-numeric-clobbers)
                            (proof-register-frame-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-zero-inversion-datum-return
  (let* ((path (proof-number-invert-path 0 zero negative box world))
         (entered (proof-number-execute-block path world))
         (code (cdr (assoc-equal "rt:zero" *proof-number-leaf-returns*)))
         (after (proof-number-execute-block code entered))
         (link (proof-world-reg 30 world)))
    (implies (and (proof-number-reduced-p 0 b)
                  (proof-heap-p world objects packages)
                  (proof-reg-value-p 0 0 world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-inversion-dispatch-trace-p 0 zero negative box world)
                  (proof-number-cut-free-prefix-p 2 (list zero link) world)
                  (proof-number-checked-block-p code (list link) entered)
                  (not (eq (car (proof-world-machine entered)) :svc))
                  (unsigned-byte-p 64 (+ 4 zero)))
             (and (proof-segment-p 4 (list link) world :cut after)
                  (proof-datum-return-p 0 (proof-number-numeric-clobbers) t t nil
                                        world after objects objects packages))))
  :hints (("Goal"
           :use (proof-number-zero-inversion-return zero-inversion-machine-frame inversion-heap-is-running
                 (:instance inversion-heap-is-running
                            (world (proof-number-execute-block
                                    (cdr (assoc-equal "rt:zero" *proof-number-leaf-returns*))
                                    (proof-number-execute-block (proof-number-invert-path 0 zero negative box world)
                                                                world)))))
           :in-theory (e/d (proof-number-inversion-dispatch-trace-p proof-number-invert-target
                            proof-datum-return-p proof-frame-return-p)
                           (proof-register-frame-p))
           :do-not-induct t))
  :rule-classes nil)
