(in-package "BOYMOO-PROOFS")

(include-book "formula-contracts")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-heap-layout-p proof-preserved-heap-p proof-machine-limit
                     proof-frame-return-p proof-datum-return-p proof-reg-value-p proof-gcd-p
                     proof-number-q-normalize-pre-p proof-number-formula-contract-trace-p
                     proof-number-formula-result-p proof-number-formula-trace-steps
                     boymoo-model::a64-sp boymoo-model::a64-memory mod floor ash)))

(local
 (defthm normalization-decision-keeps-register
   (equal (proof-world-reg register (proof-number-q-normalize-after zero unchanged reduce world))
          (proof-world-reg register world))
   :hints (("Goal"
            :in-theory (e/d (proof-number-q-normalize-after proof-world-reg)
                            (proof-reg boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                             proof-number-subtraction-flags (:definition update-nth) (:definition nth)))))))

(local
 (defthm normalization-decision-keeps-register-frame
   (proof-register-frame-p limit nil world (proof-number-q-normalize-after zero unchanged reduce world))
   :hints (("Goal"
            :induct (proof-register-frame-p limit nil world (proof-number-q-normalize-after zero unchanged reduce world))))))

(local
 (defthm normalization-decision-keeps-state
   (let ((after (proof-number-q-normalize-after zero unchanged reduce world)))
     (and (proof-number-same-heap-state-p world after)
          (proof-streams-preserved-p world after)))
   :hints (("Goal"
            :use ((:instance proof-number-same-world-tail-keeps-layout-observations
                             (before world) (after (proof-number-q-normalize-after zero unchanged reduce world))))
            :in-theory (e/d (proof-number-q-normalize-after proof-number-same-heap-state-p proof-world-reg)
                            (proof-streams-preserved-p proof-number-subtraction-flags
                             boymoo-model::a64-set-pc boymoo-model::a64-set-nzcv
                             proof-reg (:definition update-nth) (:definition nth)))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-normalization-decision-preserves-heap
  (let ((after (proof-number-q-normalize-after zero unchanged reduce world)))
    (implies (proof-heap-p world objects packages)
             (and (proof-heap-p after objects packages)
                  (proof-preserved-heap-p nil world after objects objects packages)
                  (proof-register-frame-p 30 nil world after)
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (proof-machine-limit after) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world))))))
  :hints (("Goal"
           :use (normalization-decision-keeps-state
                 (:instance proof-number-same-state-preserves-heap
                            (before world) (after (proof-number-q-normalize-after zero unchanged reduce world)))
                 (:instance proof-number-preserved-heap-is-valid
                            (may-intern nil) (before world) (old-objects objects)
                            (after (proof-number-q-normalize-after zero unchanged reduce world))))
           :in-theory (e/d (proof-number-same-heap-state-p proof-machine-limit)
                           (proof-register-frame-p proof-streams-preserved-p))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm valid-numeric-world-is-running
   (implies (proof-heap-p world objects packages) (not (proof-world-stop world)))
   :hints (("Goal"
            :use proof-number-heap-machine-context
            :in-theory (disable proof-object-map-p proof-number-machine-stack-end)))
   :rule-classes nil))

(local
 (defthm normalization-leaf-physical-return
   (let* ((middle (proof-number-q-normalize-after zero unchanged reduce world))
          (code (cdr (assoc-equal (if (equal a 0) "rt:zero" "rt:num-type-return") *proof-number-leaf-returns*)))
          (after (proof-number-execute-block code middle)))
     (implies (and (proof-heap-p world objects packages)
                   (not (eq (car (proof-world-machine middle)) :svc))
                   (proof-number-world-byte-keys-p world)
                   (proof-number-world-byte-keys-p after))
              (and (proof-heap-p after objects packages)
                   (proof-preserved-heap-p nil world after objects objects packages)
                   (proof-register-frame-p 30 (proof-number-numeric-clobbers) world after)
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine world))))))
   :hints (("Goal"
            :use (proof-number-normalization-decision-preserves-heap
                  (:instance proof-number-register-only-execution-preserves-heap
                             (world (proof-number-q-normalize-after zero unchanged reduce world))
                             (clobbers '(0))
                             (instructions (cdr (assoc-equal
                                                 (if (equal a 0) "rt:zero" "rt:num-type-return")
                                                 *proof-number-leaf-returns*))))
                  (:instance proof-number-register-frames-extend-and-compose
                             (limit 30) (clobbers (proof-number-numeric-clobbers))
                             (first-clobbers nil) (last-clobbers '(0)) (before world)
                             (middle (proof-number-q-normalize-after zero unchanged reduce world))
                             (after (proof-number-execute-block
                                     (cdr (assoc-equal (if (equal a 0) "rt:zero" "rt:num-type-return")
                                                       *proof-number-leaf-returns*))
                                     (proof-number-q-normalize-after zero unchanged reduce world))))
                  (:instance proof-number-preserved-heaps-compose
                             (before world) (middle (proof-number-q-normalize-after zero unchanged reduce world))
                             (old-objects objects) (middle-objects objects)
                             (after (proof-number-execute-block
                                     (cdr (assoc-equal (if (equal a 0) "rt:zero" "rt:num-type-return")
                                                       *proof-number-leaf-returns*))
                                     (proof-number-q-normalize-after zero unchanged reduce world))))
                  (:instance proof-number-preserved-heap-is-valid (may-intern nil) (before world)
                             (old-objects objects)
                             (after (proof-number-execute-block
                                     (cdr (assoc-equal (if (equal a 0) "rt:zero" "rt:num-type-return")
                                                       *proof-number-leaf-returns*))
                                     (proof-number-q-normalize-after zero unchanged reduce world)))))
            :in-theory (e/d (proof-number-register-only-instruction-p proof-number-numeric-clobbers)
                            (proof-register-frame-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-q-normalize-trivial-datum-return
  (let* ((link (proof-world-reg 30 world))
         (target (if (equal a 0) zero unchanged))
         (code (cdr (assoc-equal (if (equal a 0) "rt:zero" "rt:num-type-return") *proof-number-leaf-returns*)))
         (count (if (equal a 0) 2 4))
         (middle (proof-number-q-normalize-after zero unchanged reduce world))
         (after (proof-number-execute-block code middle)))
    (implies (and (integerp a) (posp b) (or (equal a 0) (equal b 1))
                  (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-q-normalize-pre-p zero unchanged reduce world)
                  (proof-number-cut-free-prefix-p count (list target link) world)
                  (proof-number-checked-block-p code (list link) middle)
                  (not (eq (car (proof-world-machine middle)) :svc))
                  (unsigned-byte-p 64 (+ 4 target)))
             (and (proof-segment-p (+ count (len code)) (list link) world :cut after)
                  (proof-datum-return-p (/ a b) (proof-number-numeric-clobbers) t t nil
                                        world after objects objects packages))))
  :hints (("Goal"
           :use (proof-number-q-normalize-trivial-return normalization-leaf-physical-return
                 valid-numeric-world-is-running
                 (:instance valid-numeric-world-is-running
                            (world (proof-number-execute-block
                                    (cdr (assoc-equal (if (equal a 0) "rt:zero" "rt:num-type-return")
                                                      *proof-number-leaf-returns*))
                                    (proof-number-q-normalize-after zero unchanged reduce world))))
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (if (equal a 0) 4 5)) (cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut)
                            (after (proof-number-execute-block
                                    (cdr (assoc-equal (if (equal a 0) "rt:zero" "rt:num-type-return")
                                                      *proof-number-leaf-returns*))
                                    (proof-number-q-normalize-after zero unchanged reduce world)))))
           :in-theory (e/d (proof-datum-return-p proof-frame-return-p)
                           (proof-register-frame-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-q-normalize-reduction-datum-return
  (let* ((ready (proof-number-q-normalize-after zero unchanged reduce world))
         (link (proof-world-reg 30 world))
         (args (list a b))
         (steps (proof-number-formula-contract-steps "rt:q-reduce" growth-steps trace))
         (after (proof-number-formula-trace-after trace))
         (new-objects (caddar (last trace))))
    (implies (and (integerp a) (not (equal a 0)) (posp b) (< 1 b) (proof-gcd-p a b gcd)
                  (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-q-normalize-pre-p zero unchanged reduce world)
                  (proof-number-cut-free-prefix-p 5 (list reduce link) world)
                  (proof-number-save-interval-p (- (boymoo-model::a64-sp (proof-world-machine ready)) 16)
                                                ready objects)
                  (proof-number-formula-contract-trace-p "rt:q-reduce" args gcd grow growth-steps targets trace
                                                         ready grown objects grown-objects packages)
                  (natp steps))
             (and (proof-segment-p (+ 5 steps) (list link) world :cut after)
                  (proof-datum-return-p (/ a b) (proof-number-numeric-clobbers) t t nil
                                        world after objects new-objects packages))))
  :hints (("Goal"
           :use (proof-number-q-reduce-formula proof-number-normalization-decision-preserves-heap
                 (:instance proof-number-q-normalize-dispatch-by-value (register 30))
                 (:instance proof-number-segment-preserves-byte-keys
                            (count 5) (cuts (list reduce)) (before world) (reason :cut)
                            (after (proof-number-q-normalize-after zero unchanged reduce world)))
                 (:instance proof-number-generated-formula-datum-return
                            (name "rt:q-reduce") (args (list a b)) (result (/ a b))
                            (world (proof-number-q-normalize-after zero unchanged reduce world)))
                 (:instance proof-number-compose-segments
                            (prefix 5) (suffix (proof-number-formula-contract-steps "rt:q-reduce" growth-steps trace))
                            (first-cuts (list reduce)) (last-cuts (list (proof-world-reg 30 world)))
                            (before world) (middle (proof-number-q-normalize-after zero unchanged reduce world))
                            (after (proof-number-formula-trace-after trace)) (reason :cut))
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (+ 5 (proof-number-formula-contract-steps "rt:q-reduce" growth-steps trace)))
                            (cuts (list (proof-world-reg 30 world))) (before world) (reason :cut)
                            (after (proof-number-formula-trace-after trace)))
                 (:instance proof-number-numeric-tail-transfer-returns
                            (datum (/ a b)) (clobbers nil)
                            (before world) (middle (proof-number-q-normalize-after zero unchanged reduce world))
                            (after (proof-number-formula-trace-after trace))
                            (old-objects objects) (middle-objects objects) (objects (caddar (last trace)))))
           :in-theory (disable proof-register-frame-p last)
           :do-not-induct t))
  :rule-classes nil)
