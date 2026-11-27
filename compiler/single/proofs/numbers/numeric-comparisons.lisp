(in-package "BOYMOO-PROOFS")

(include-book "comparison-return")
(include-book "type-dispatch")
(include-book "register-effects")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-advance
                     proof-number-exact-prefix-p proof-number-checked-block-p
                     proof-number-cut-free-prefix-p proof-number-execute-block
                     proof-world-pc proof-world-reg proof-world-machine proof-world-stop
                     proof-load-word proof-heap-base proof-reg-value-p proof-machine-value-p
                     proof-number-order proof-number-binary-types-p
                     proof-datum-return-p boymoo-model::a64-sp boymoo-model::a64-memory)))

(local
 (defthm less-compare-code-changes-only-link
   (proof-number-register-only-code-p
    (proof-number-less-compare-path pc rational complex complex-case) '(30))
   :hints (("Goal" :in-theory (enable proof-number-less-compare-path
                                     proof-number-register-only-instruction-p)))))

(defthm proof-number-less-comparator-receives-completed-values
  (let* ((machine (proof-world-machine world))
         (pc (proof-world-pc world))
         (complex-case (equal (proof-world-reg 3 world) 5))
         (target (if complex-case complex rational))
         (path (proof-number-less-compare-path pc rational complex complex-case))
         (after (proof-number-less-compare-ready rational complex world)))
    (implies (and (proof-number-binary-types-p a b world objects packages)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 target)
                  (unsigned-byte-p 64 (+ pc 20))
                  (proof-number-checked-block-p path (list target) world)
                  (proof-number-checked-block-p path cuts world))
             (and (proof-number-exact-prefix-p 3 cuts world after)
                  (proof-segment-p 3 (list target) world :cut after)
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 30 after) (+ pc (if complex-case 20 12)))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine))
                  (equal complex-case (or (complex-rationalp a) (complex-rationalp b)))
                  (implies (not complex-case) (and (rationalp (fix a)) (rationalp (fix b))))
                  (proof-register-arguments-p (list (fix a) (fix b)) 0 after objects packages))))
  :hints (("Goal"
           :use (proof-number-less-calls-comparator
                 (:instance less-compare-code-changes-only-link
                            (pc (proof-world-pc world)) (complex-case (equal (proof-world-reg 3 world) 5)))
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-less-compare-path
                                           (proof-world-pc world) rational complex
                                           (equal (proof-world-reg 3 world) 5))))
                 (:instance proof-number-register-only-block-effects
                            (register 28) (clobbers '(30))
                            (instructions (proof-number-less-compare-path
                                           (proof-world-pc world) rational complex
                                           (equal (proof-world-reg 3 world) 5))))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (word (proof-world-reg 0 world)) (value (fix a))
                            (before world) (after (proof-number-less-compare-ready rational complex world)))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 1) (word (proof-world-reg 1 world)) (value (fix b))
                            (before world) (after (proof-number-less-compare-ready rational complex world))))
           :in-theory (enable proof-number-less-compare-ready proof-number-less-compare-path
                              proof-number-binary-types-p proof-number-max-class proof-number-datum-class
                              proof-reg-value-p proof-heap-base
                              proof-number-register-only-code-p proof-number-register-only-instruction-p)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-less-comparison-after (a b yes no returned world)
  (proof-number-less-tail-after (proof-number-order (fix a) (fix b)) yes no
                               (proof-number-less-resumed (equal (proof-world-reg 3 world) 5)
                                                          returned)))

(defund proof-number-less-comparison-steps (a b callee-steps world)
  (+ 3 callee-steps (if (equal (proof-world-reg 3 world) 5) 0 1)
     (if (equal (proof-number-order (fix a) (fix b)) -1) 5 6)))

(defund proof-number-less-comparison-trace-p
    (a b rational complex yes no link callee-steps world returned objects new-objects packages)
  (let* ((machine (proof-world-machine world))
         (pc (proof-world-pc world))
         (complex-case (equal (proof-world-reg 3 world) 5))
         (target (if complex-case complex rational))
         (code (proof-number-less-compare-path pc rational complex complex-case))
         (ready (proof-number-less-compare-ready rational complex world))
         (sp (boymoo-model::a64-sp machine))
         (machine-end (+ (- (proof-machine-limit ready) *proof-machine-margin*)
                         *proof-machine-reservation*))
         (continuation (+ pc (if complex-case 20 12)))
         (order (proof-number-order (fix a) (fix b))))
    (and (not (eq (car machine) :svc))
         (unsigned-byte-p 64 (+ pc 20))
         (unsigned-byte-p 64 target)
         (proof-number-checked-block-p code (list target) world)
         (proof-number-checked-block-p code (list link) world)
         (<= (+ 16 sp) machine-end)
         (<= machine-end (expt 2 64))
         (natp callee-steps)
         (proof-number-cut-free-prefix-p callee-steps (list continuation link) ready)
         (proof-segment-p callee-steps (list continuation) ready :cut returned)
         (proof-datum-return-p order (proof-number-numeric-clobbers) t t nil
                               ready returned objects new-objects packages)
         (not (eq (car (proof-world-machine returned)) :svc))
         (proof-number-checked-block-p (proof-number-less-resume-code complex-case) (list link) returned)
         (proof-number-less-tail-code-p order link yes no
                                        (proof-number-less-resumed complex-case returned)))))

(local
 (defthm comparison-order-small
   (member-equal (proof-number-order a b) '(-1 0 1))
   :hints (("Goal" :in-theory (enable proof-number-order)))))

(local
 (defthm word-kept-by-comparison-call
   (let ((first (proof-world-machine world))
         (last (proof-world-machine (proof-number-less-compare-ready rational complex world))))
     (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
              (equal (proof-load-word address last) (proof-load-word address first))))
   :hints (("Goal" :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(local
 (defthm less-comparison-prefix
   (let* ((ready (proof-number-less-compare-ready rational complex world))
          (complex-case (equal (proof-world-reg 3 world) 5))
          (machine (proof-world-machine world))
          (sp (boymoo-model::a64-sp machine)))
     (implies (and (proof-number-binary-types-p a b world objects packages)
                   (proof-number-less-comparison-trace-p
                    a b rational complex yes no link callee-steps world returned objects new-objects packages))
              (and (proof-number-exact-prefix-p 3 (list link) world ready)
                   (equal (proof-world-reg 30 ready) (+ (proof-world-pc world) (if complex-case 20 12)))
                   (equal (boymoo-model::a64-sp (proof-world-machine ready)) sp)
                   (equal (proof-load-word sp (proof-world-machine ready))
                          (proof-load-word sp machine))
                   (equal (proof-load-word (+ 8 sp) (proof-world-machine ready))
                          (proof-load-word (+ 8 sp) machine)))))
   :hints (("Goal"
            :use ((:instance proof-number-less-comparator-receives-completed-values (cuts (list link)))
                  (:instance word-kept-by-comparison-call
                             (address (boymoo-model::a64-sp (proof-world-machine world))))
                  (:instance word-kept-by-comparison-call
                             (address (+ 8 (boymoo-model::a64-sp (proof-world-machine world))))))
            :in-theory (e/d (proof-number-less-comparison-trace-p)
                            (proof-register-arguments-p proof-number-order proof-number-less-uses-order-sign))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm less-comparison-suffix
   (let* ((machine (proof-world-machine world))
          (sp (boymoo-model::a64-sp machine))
          (complex-case (equal (proof-world-reg 3 world) 5))
          (order (proof-number-order (fix a) (fix b)))
          (after (proof-number-less-comparison-after a b yes no returned world)))
     (implies (and (equal (proof-load-word (+ 8 sp) machine) link)
                   (proof-number-binary-types-p a b world objects packages)
                   (proof-number-less-comparison-trace-p
                    a b rational complex yes no link callee-steps world returned objects new-objects packages))
              (and (proof-segment-p (+ (if complex-case 0 1) (if (equal order -1) 5 6))
                                    (list link) returned :cut after)
                   (equal (proof-world-pc after) link)
                   (equal (proof-world-reg 30 after) link)
                   (equal (proof-world-reg 29 after) (proof-load-word sp machine))
                   (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ 16 sp))
                   (equal (proof-world-reg 0 after)
                          (if (< (fix a) (fix b)) *proof-t* *proof-nil*)))))
   :hints (("Goal"
            :use (less-comparison-prefix
                  (:instance proof-number-comparison-return-keeps-saves
                             (ready (proof-number-less-compare-ready rational complex world))
                             (order (proof-number-order (fix a) (fix b))))
                  (:instance proof-number-less-continues-comparator-return
                             (ready (proof-number-less-compare-ready rational complex world))
                             (complex-case (equal (proof-world-reg 3 world) 5))
                             (order (proof-number-order (fix a) (fix b)))))
            :in-theory (e/d (proof-number-less-comparison-trace-p proof-number-less-comparison-after)
                            (proof-number-order proof-number-integer-parity fix))
            :cases ((equal (proof-world-reg 3 world) 5))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-less-executes-selected-comparison
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (after (proof-number-less-comparison-after a b yes no returned world)))
    (implies (and (equal (proof-load-word (+ 8 sp) machine) link)
                  (proof-number-binary-types-p a b world objects packages)
                  (proof-number-less-comparison-trace-p a b rational complex yes no link callee-steps
                                                        world returned objects new-objects packages))
             (and (proof-segment-p (proof-number-less-comparison-steps a b callee-steps world)
                                   (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-world-reg 29 after) (proof-load-word sp machine))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ 16 sp))
                  (equal (proof-world-reg 0 after)
                         (if (< (fix a) (fix b)) *proof-t* *proof-nil*)))))
  :hints (("Goal"
           :use (less-comparison-prefix less-comparison-suffix
                 (:instance proof-number-compose-segments
                            (prefix callee-steps)
                            (suffix (+ (if (equal (proof-world-reg 3 world) 5) 0 1)
                                       (if (equal (proof-number-order (fix a) (fix b)) -1) 5 6)))
                            (first-cuts (list (+ (proof-world-pc world)
                                                 (if (equal (proof-world-reg 3 world) 5) 20 12))))
                            (last-cuts (list link))
                            (before (proof-number-less-compare-ready rational complex world))
                            (middle returned) (reason :cut)
                            (after (proof-number-less-comparison-after a b yes no returned world)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix 3)
                            (suffix (+ callee-steps (if (equal (proof-world-reg 3 world) 5) 0 1)
                                       (if (equal (proof-number-order (fix a) (fix b)) -1) 5 6)))
                            (before world)
                            (middle (proof-number-less-compare-ready rational complex world))
                            (cuts (list link)) (reason :cut)
                            (after (proof-number-less-comparison-after a b yes no returned world))))
           :in-theory (e/d (proof-number-less-comparison-trace-p proof-number-less-comparison-steps)
                           (fix))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-general-less-returns-boolean
  (let* ((link (proof-world-reg 30 world))
         (completed (proof-number-binary-types-call-after types classifier world))
         (after (proof-number-less-comparison-after a b yes no returned completed))
         (count (+ 2
                   (proof-number-types-completion-steps nil classifier
                                                       (proof-number-types-first-ready types world))
                   (proof-number-less-comparison-steps a b callee-steps completed))))
    (implies (and (proof-number-binary-types-call-trace-p types classifier (list link) a b
                                                         world objects packages)
                  (proof-number-less-comparison-trace-p a b rational complex yes no link callee-steps
                                                        completed returned objects new-objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (proof-world-reg 0 after)
                         (if (< (fix a) (fix b)) *proof-t* *proof-nil*)))))
  :hints (("Goal"
           :use ((:instance proof-number-binary-wrapper-completes (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-less-executes-selected-comparison
                            (world (proof-number-binary-types-call-after types classifier world))
                            (link (proof-world-reg 30 world)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (+ 2 (proof-number-types-completion-steps
                                          nil classifier (proof-number-types-first-ready types world))))
                            (suffix (proof-number-less-comparison-steps
                                     a b callee-steps (proof-number-binary-types-call-after types classifier world)))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (middle (proof-number-binary-types-call-after types classifier world))
                            (reason :cut)
                            (after (proof-number-less-comparison-after
                                    a b yes no returned (proof-number-binary-types-call-after types classifier world)))))
           :in-theory (enable proof-number-less-comparison-steps proof-number-less-comparison-trace-p)
           :do-not-induct t))
  :rule-classes nil)
