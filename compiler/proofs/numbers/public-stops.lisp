(in-package "BOYMOO-PROOFS")

(include-book "primitive-returns")
(include-book "resource-returns")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p proof-number-checked-block-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-runtime-pre-p proof-runtime-return-p proof-heap-p proof-preserved-heap-p
                     proof-number-arithmetic-wrapper-trace-p proof-number-arithmetic-decision-trace-p
                     proof-number-binary-types-call-trace-p proof-number-binary-types-p
                     proof-resource-observation-p boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defthm proof-number-public-immediate-propagates-helper-stop
  (let* ((args (proof-number-immediate-source-args name a b))
         (code (proof-number-immediate-delegation-entry-code name a (proof-world-pc world) general slow))
         (entered (proof-number-immediate-delegation-after name a general slow world))
         (link (proof-world-reg 30 world)))
    (implies (and (proof-runtime-pre-p name args program labels base world objects packages)
                  (proof-number-immediate-delegation-trace-p name a b general slow world)
                  (natp steps)
                  (proof-segment-p steps (list link) entered '(:exit . 3) stopped)
                  (proof-resource-observation-p stopped))
             (and (proof-segment-p (+ (len code) steps) (list link) world '(:exit . 3) stopped)
                  (proof-resource-observation-p stopped))))
  :hints (("Goal"
           :use (proof-number-public-immediate-reaches-helper
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (len (proof-number-immediate-delegation-entry-code
                                          name a (proof-world-pc world) general slow)))
                            (suffix steps) (before world)
                            (middle (proof-number-immediate-delegation-after name a general slow world))
                            (cuts (list (proof-world-reg 30 world)))
                            (after stopped) (reason '(:exit . 3))))
           :in-theory (disable proof-register-frame-p)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm checked-formula-call-instruction-count
   (implies (and (consp indices)
                 (or (null (cdr indices)) (and (consp (cdr indices)) (null (cddr indices)))))
            (equal (len (proof-number-formula-call-instructions indices pc target)) (1+ (len indices))))
   :hints (("Goal" :in-theory (enable proof-number-formula-call-instructions
                                     proof-number-formula-load-instructions)
                   :do-not-induct t))))

(defthm proof-number-formula-call-propagates-resource-stop
  (let* ((pc (proof-world-pc world))
         (indices (cdr call))
         (count (1+ (len indices)))
         (target (cdr (assoc-equal (car call) targets)))
         (continuation (+ pc (* 4 count)))
         (code (proof-number-formula-call-instructions indices pc target))
         (ready (proof-number-formula-call-ready call targets world)))
    (implies (and (consp indices)
                  (or (null (cdr indices)) (and (consp (cdr indices)) (null (cddr indices))))
                  (proof-number-slot-indices-p indices (len slots))
                  (proof-number-frame-p start slots world objects packages)
                  (equal (proof-world-reg 19 world) (proof-number-frame-address start world))
                  (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 continuation) (unsigned-byte-p 64 target)
                  (proof-number-checked-block-p code (list target) world)
                  (proof-number-checked-block-p code (list link) world)
                  (proof-number-resource-return-p steps link continuation ready stopped))
             (and (equal (proof-world-pc ready) target)
                  (equal (proof-world-reg 30 ready) continuation)
                  (proof-register-arguments-p (proof-number-slot-arguments indices slots) 0 ready objects packages)
                  (proof-segment-p (+ count steps) (list link) world '(:exit . 3) stopped)
                  (proof-resource-observation-p stopped))))
  :hints (("Goal"
           :use ((:instance proof-number-formula-loads-call-arguments (indices (cdr call))
                            (target (cdr (assoc-equal (car call) targets))))
                 (:instance proof-number-formula-passes-slot-values (indices (cdr call))
                            (target (cdr (assoc-equal (car call) targets))))
                 (:instance proof-number-checked-block-exact-prefix (cuts (list link))
                            (instructions (proof-number-formula-call-instructions
                                           (cdr call) (proof-world-pc world) (cdr (assoc-equal (car call) targets)))))
                 (:instance proof-number-resource-return-with-outer-cut
                            (continuation (+ (proof-world-pc world) (* 4 (1+ (len (cdr call))))))
                            (ready (proof-number-formula-call-ready call targets world)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (1+ (len (cdr call)))) (suffix steps) (cuts (list link))
                            (before world) (middle (proof-number-formula-call-ready call targets world))
                            (after stopped) (reason '(:exit . 3))))
           :in-theory (e/d (proof-number-formula-call-ready proof-number-resource-return-p)
                           (proof-number-formula-call-instructions proof-register-arguments-p
                            proof-number-slot-indices-p proof-number-frame-address assoc-equal))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm general-arithmetic-prefix-reaches-helper
   (let* ((args (proof-number-arithmetic-source-args primitive a b))
          (arity (len args))
          (link (proof-world-reg 30 world))
          (entry (proof-number-general-gate-after arity general world))
          (dispatch (proof-number-arithmetic-wrapper-after primitive types classifier entry))
          (path (proof-number-arithmetic-dispatch-path primitive addresses dispatch))
          (after (proof-number-arithmetic-dispatch-after primitive addresses dispatch))
          (count (+ 1 arity (proof-number-arithmetic-wrapper-steps primitive types classifier entry)
                    (len path))))
     (implies (and (proof-runtime-pre-p primitive args program labels base world objects packages)
                   (proof-number-world-byte-keys-p world)
                   (proof-number-general-gate-trace-p arity general world)
                   (proof-number-arithmetic-wrapper-trace-p primitive a b types classifier entry objects packages)
                   (proof-number-arithmetic-decision-trace-p primitive addresses dispatch))
              (proof-number-exact-prefix-p count (list link) world after)))
   :hints (("Goal"
            :use ((:instance proof-number-runtime-entry-has-heap
                             (name primitive) (args (proof-number-arithmetic-source-args primitive a b)))
                  (:instance proof-number-general-tag-gate-reaches-runtime
                             (arity (len (proof-number-arithmetic-source-args primitive a b))) (register 30))
                  (:instance proof-number-exact-prefix-preserves-byte-keys
                             (count (1+ (len (proof-number-arithmetic-source-args primitive a b))))
                             (cuts (list (proof-world-reg 30 world))) (before world)
                             (after (proof-number-general-gate-after
                                     (len (proof-number-arithmetic-source-args primitive a b)) general world)))
                  (:instance proof-number-arithmetic-wrapper-supplies-dispatch-context
                             (world (proof-number-general-gate-after
                                     (len (proof-number-arithmetic-source-args primitive a b)) general world)))
                  (:instance proof-number-preserved-heap-is-valid
                             (may-intern nil) (old-objects objects)
                             (before (proof-number-general-gate-after
                                      (len (proof-number-arithmetic-source-args primitive a b)) general world))
                             (after (proof-number-arithmetic-wrapper-after
                                     primitive types classifier
                                     (proof-number-general-gate-after
                                      (len (proof-number-arithmetic-source-args primitive a b)) general world))))
                  (:instance proof-number-arithmetic-decision-keeps-dispatch-context (register 30)
                             (world (proof-number-arithmetic-wrapper-after
                                     primitive types classifier
                                     (proof-number-general-gate-after
                                      (len (proof-number-arithmetic-source-args primitive a b)) general world))))
                  (:instance proof-number-exact-prefix-append
                             (prefix (1+ (len (proof-number-arithmetic-source-args primitive a b))))
                             (suffix (proof-number-arithmetic-wrapper-steps
                                      primitive types classifier
                                      (proof-number-general-gate-after
                                       (len (proof-number-arithmetic-source-args primitive a b)) general world)))
                             (cuts (list (proof-world-reg 30 world))) (before world)
                             (middle (proof-number-general-gate-after
                                      (len (proof-number-arithmetic-source-args primitive a b)) general world))
                             (after (proof-number-arithmetic-wrapper-after
                                     primitive types classifier
                                     (proof-number-general-gate-after
                                      (len (proof-number-arithmetic-source-args primitive a b)) general world))))
                  (:instance proof-number-exact-prefix-append
                             (prefix (+ (1+ (len (proof-number-arithmetic-source-args primitive a b)))
                                        (proof-number-arithmetic-wrapper-steps
                                         primitive types classifier
                                         (proof-number-general-gate-after
                                          (len (proof-number-arithmetic-source-args primitive a b)) general world))))
                             (suffix (len (proof-number-arithmetic-dispatch-path
                                           primitive addresses
                                           (proof-number-arithmetic-wrapper-after
                                            primitive types classifier
                                            (proof-number-general-gate-after
                                             (len (proof-number-arithmetic-source-args primitive a b)) general world)))))
                             (cuts (list (proof-world-reg 30 world))) (before world)
                             (middle (proof-number-arithmetic-wrapper-after
                                      primitive types classifier
                                      (proof-number-general-gate-after
                                       (len (proof-number-arithmetic-source-args primitive a b)) general world)))
                             (after (proof-number-arithmetic-dispatch-after
                                     primitive addresses
                                     (proof-number-arithmetic-wrapper-after
                                      primitive types classifier
                                      (proof-number-general-gate-after
                                       (len (proof-number-arithmetic-source-args primitive a b)) general world))))))
            :in-theory (e/d (proof-number-dispatch-context-p)
                            (proof-register-frame-p proof-number-arithmetic-decision-is-register-only))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-public-general-arithmetic-propagates-helper-stop
  (let* ((args (proof-number-arithmetic-source-args primitive a b))
         (arity (len args))
         (link (proof-world-reg 30 world))
         (entry (proof-number-general-gate-after arity general world))
         (dispatch (proof-number-arithmetic-wrapper-after primitive types classifier entry))
         (entered (proof-number-arithmetic-dispatch-after primitive addresses dispatch))
         (prefix (+ 1 arity (proof-number-arithmetic-wrapper-steps primitive types classifier entry)
                    (len (proof-number-arithmetic-dispatch-path primitive addresses dispatch)))))
    (implies (and (proof-runtime-pre-p primitive args program labels base world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-general-gate-trace-p arity general world)
                  (proof-number-arithmetic-wrapper-trace-p primitive a b types classifier entry objects packages)
                  (proof-number-arithmetic-decision-trace-p primitive addresses dispatch)
                  (natp stop-steps)
                  (proof-segment-p stop-steps (list link) entered '(:exit . 3) stopped)
                  (proof-resource-observation-p stopped))
             (and (proof-segment-p (+ prefix stop-steps) (list link) world '(:exit . 3) stopped)
                  (proof-resource-observation-p stopped))))
  :hints (("Goal"
           :use (general-arithmetic-prefix-reaches-helper
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (+ 1 (len (proof-number-arithmetic-source-args primitive a b))
                                       (proof-number-arithmetic-wrapper-steps
                                        primitive types classifier
                                        (proof-number-general-gate-after
                                         (len (proof-number-arithmetic-source-args primitive a b)) general world))
                                       (len (proof-number-arithmetic-dispatch-path
                                             primitive addresses
                                             (proof-number-arithmetic-wrapper-after
                                              primitive types classifier
                                              (proof-number-general-gate-after
                                               (len (proof-number-arithmetic-source-args primitive a b)) general world))))))
                            (suffix stop-steps) (before world) (cuts (list (proof-world-reg 30 world)))
                            (middle (proof-number-arithmetic-dispatch-after
                                     primitive addresses
                                     (proof-number-arithmetic-wrapper-after
                                      primitive types classifier
                                      (proof-number-general-gate-after
                                       (len (proof-number-arithmetic-source-args primitive a b)) general world))))
                            (after stopped) (reason '(:exit . 3))))
           :in-theory (disable proof-number-arithmetic-decision-is-register-only)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-less-comparator-stop-trace-p
    (a b types classifier rational complex steps world stopped objects packages)
  (let* ((link (proof-world-reg 30 world))
         (completed (proof-number-binary-types-call-after types classifier world))
         (pc (proof-world-pc completed))
         (complex-case (equal (proof-world-reg 3 completed) 5))
         (target (if complex-case complex rational))
         (code (proof-number-less-compare-path pc rational complex complex-case))
         (ready (proof-number-less-compare-ready rational complex completed))
         (continuation (+ pc (if complex-case 20 12))))
    (and (proof-number-binary-types-call-trace-p types classifier (list link) a b world objects packages)
         (not (eq (car (proof-world-machine completed)) :svc))
         (unsigned-byte-p 64 (+ 20 pc))
         (unsigned-byte-p 64 target)
         (proof-number-checked-block-p code (list target) completed)
         (proof-number-checked-block-p code (list link) completed)
         (proof-number-resource-return-p steps link continuation ready stopped))))

(defthm proof-number-general-less-propagates-comparator-stop
  (let* ((link (proof-world-reg 30 world))
         (count (+ 5 (proof-number-types-completion-steps nil classifier
                                                          (proof-number-types-first-ready types world))
                   steps)))
    (implies (proof-number-less-comparator-stop-trace-p
              a b types classifier rational complex steps world stopped objects packages)
             (and (proof-segment-p count (list link) world '(:exit . 3) stopped)
                  (proof-resource-observation-p stopped))))
  :hints (("Goal"
           :use ((:instance proof-number-binary-wrapper-completes (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-less-comparator-receives-completed-values
                            (cuts (list (proof-world-reg 30 world)))
                            (world (proof-number-binary-types-call-after types classifier world)))
                 (:instance proof-number-exact-prefix-append
                            (prefix (+ 2 (proof-number-types-completion-steps
                                          nil classifier (proof-number-types-first-ready types world))))
                            (suffix 3) (cuts (list (proof-world-reg 30 world))) (before world)
                            (middle (proof-number-binary-types-call-after types classifier world))
                            (after (proof-number-less-compare-ready
                                    rational complex (proof-number-binary-types-call-after types classifier world))))
                 (:instance proof-number-resource-return-with-outer-cut
                            (link (proof-world-reg 30 world))
                            (continuation (+ (proof-world-pc (proof-number-binary-types-call-after types classifier world))
                                             (if (equal (proof-world-reg 3 (proof-number-binary-types-call-after
                                                                            types classifier world))
                                                        5)
                                                 20 12)))
                            (ready (proof-number-less-compare-ready
                                    rational complex (proof-number-binary-types-call-after types classifier world))))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (+ 5 (proof-number-types-completion-steps
                                          nil classifier (proof-number-types-first-ready types world))))
                            (suffix steps) (cuts (list (proof-world-reg 30 world))) (before world)
                            (middle (proof-number-less-compare-ready
                                     rational complex (proof-number-binary-types-call-after types classifier world)))
                            (after stopped) (reason '(:exit . 3))))
           :in-theory (e/d (proof-number-less-comparator-stop-trace-p proof-number-resource-return-p)
                           (proof-number-less-compare-path proof-register-arguments-p
                            proof-number-binary-types-p fix))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-public-less-propagates-comparator-stop
  (let* ((entry (proof-number-general-gate-after 2 general world))
         (link (proof-world-reg 30 world))
         (count (+ 8 (proof-number-types-completion-steps nil classifier
                                                          (proof-number-types-first-ready types entry))
                   steps)))
    (implies (and (proof-runtime-pre-p '< (list a b) program labels base world objects packages)
                  (proof-number-general-gate-trace-p 2 general world)
                  (proof-number-less-comparator-stop-trace-p
                   a b types classifier rational complex steps entry stopped objects packages))
             (and (proof-segment-p count (list link) world '(:exit . 3) stopped)
                  (proof-resource-observation-p stopped))))
  :hints (("Goal"
           :use ((:instance proof-number-runtime-entry-has-heap (name '<) (args (list a b)))
                 (:instance proof-number-general-tag-gate-reaches-runtime (arity 2) (register 30))
                 (:instance proof-number-general-less-propagates-comparator-stop
                            (world (proof-number-general-gate-after 2 general world)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix 3)
                            (suffix (+ 5 (proof-number-types-completion-steps
                                          nil classifier
                                          (proof-number-types-first-ready
                                           types (proof-number-general-gate-after 2 general world)))
                                       steps))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (middle (proof-number-general-gate-after 2 general world))
                            (after stopped) (reason '(:exit . 3))))
           :in-theory (e/d (proof-number-less-comparator-stop-trace-p proof-number-resource-return-p
                            proof-number-types-completion-steps)
                           (proof-register-frame-p proof-number-less-compare-path
                            proof-number-less-compare-ready fix))
           :do-not-induct t))
  :rule-classes nil)
