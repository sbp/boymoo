(in-package "BOYMOO-PROOFS")

(include-book "complex-contract")
(include-book "formula-entry")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-cut-free-prefix-p proof-number-exact-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-runtime-pre-p proof-number-box-select-pre-p proof-preserved-heap-p
                     proof-reg-value-p proof-number-types-completion-trace-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defund proof-number-resource-return-p (steps link continuation ready stopped)
  (and (natp steps)
       (proof-number-cut-free-prefix-p steps (list continuation link) ready)
       (proof-segment-p steps (list continuation) ready '(:exit . 3) stopped)
       (proof-resource-observation-p stopped)))

(local
 (defthm resource-stop-needs-no-more-steps
   (implies (proof-resource-observation-p stopped)
            (proof-segment-p 0 (list link) stopped '(:exit . 3) stopped))
   :hints (("Goal"
            :expand ((proof-segment-p 0 (list link) stopped '(:exit . 3) stopped)
                     (proof-run 0 (list link) stopped))
            :in-theory (enable proof-resource-observation-p proof-exit-status-p)))))

(defthm proof-number-resource-return-with-outer-cut
  (implies (proof-number-resource-return-p steps link continuation ready stopped)
           (proof-segment-p steps (list link) ready '(:exit . 3) stopped))
  :hints (("Goal"
           :use ((:instance proof-number-segment-exact-prefix
                            (count steps) (cuts (list link)) (local-cuts (list continuation))
                            (before ready) (reason '(:exit . 3)) (after stopped))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix steps) (suffix 0) (cuts (list link)) (before ready)
                            (middle stopped) (after stopped) (reason '(:exit . 3))))
           :in-theory (enable proof-number-resource-return-p)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-growth-stop-trace-p (name grow steps world stopped)
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (pc (proof-world-pc world))
         (link (proof-world-reg 30 world))
         (bytes (proof-number-formula-frame-bytes name))
         (required (+ (proof-stack-top world) bytes))
         (code (proof-number-formula-grow-instructions pc grow bytes))
         (ready (proof-number-formula-grow-ready name grow world)))
    (and (not (eq (car machine) :svc))
         (proof-span-p (- sp 16) 16)
         (unsigned-byte-p 64 (+ 16 pc))
         (unsigned-byte-p 64 grow)
         (unsigned-byte-p 64 required)
         (proof-number-checked-block-p code (list grow) world)
         (proof-number-checked-block-p code (list link) world)
         (proof-resource-bound-p :value-stack required ready)
         (proof-number-resource-return-p steps link (+ 16 pc) ready stopped))))

(defthm proof-number-formula-propagates-stack-exhaustion
  (let* ((link (proof-world-reg 30 world))
         (ready (proof-number-formula-grow-ready name grow world))
         (required (+ (proof-stack-top world) (proof-number-formula-frame-bytes name))))
    (implies (proof-number-growth-stop-trace-p name grow steps world stopped)
             (and (equal (proof-world-pc ready) grow)
                  (equal (proof-world-reg 8 ready) required)
                  (proof-resource-bound-p :value-stack required ready)
                  (proof-segment-p (+ 4 steps) (list link) world '(:exit . 3) stopped)
                  (proof-resource-observation-p stopped))))
  :hints (("Goal"
           :use ((:instance proof-number-formula-calls-growth
                            (bytes (proof-number-formula-frame-bytes name)))
                 (:instance proof-number-resource-return-with-outer-cut
                            (link (proof-world-reg 30 world)) (continuation (+ 16 (proof-world-pc world)))
                            (ready (proof-number-formula-grow-ready name grow world)))
                 (:instance proof-number-checked-block-exact-prefix
                            (cuts (list (proof-world-reg 30 world)))
                            (instructions (proof-number-formula-grow-instructions
                                           (proof-world-pc world) grow (proof-number-formula-frame-bytes name))))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix 4) (suffix steps) (cuts (list (proof-world-reg 30 world)))
                            (before world) (middle (proof-number-formula-grow-ready name grow world))
                            (after stopped) (reason '(:exit . 3))))
           :in-theory (e/d (proof-number-growth-stop-trace-p proof-number-formula-grow-ready
                            proof-number-formula-grow-instructions proof-number-resource-return-p)
                           (proof-resource-bound-p proof-resource-observation-p proof-span-p proof-stack-top))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-box-reservation-stop-trace-p (reserve steps world stopped)
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (pc (proof-world-pc world))
         (link (proof-world-reg 30 world))
         (code (proof-number-box-reserve-instructions pc reserve))
         (ready (proof-number-box-reserve-ready reserve world)))
    (and (not (eq (car machine) :svc))
         (proof-span-p (- sp 16) 16)
         (unsigned-byte-p 64 (+ 12 pc))
         (unsigned-byte-p 64 reserve)
         (proof-number-checked-block-p code (list reserve) world)
         (proof-number-checked-block-p code (list link) world)
         (proof-number-resource-return-p steps link (+ 12 pc) ready stopped))))

(defthm proof-number-box-propagates-reservation-stop
  (let* ((link (proof-world-reg 30 world))
         (ready (proof-number-box-reserve-ready reserve world)))
    (implies (proof-number-box-reservation-stop-trace-p reserve steps world stopped)
             (and (equal (proof-world-pc ready) reserve)
                  (equal (proof-world-reg 2 ready) 24)
                  (proof-segment-p (+ 3 steps) (list link) world '(:exit . 3) stopped)
                  (proof-resource-observation-p stopped))))
  :hints (("Goal"
           :use (proof-number-box-calls-reserve
                 (:instance proof-number-resource-return-with-outer-cut
                            (link (proof-world-reg 30 world)) (continuation (+ 12 (proof-world-pc world)))
                            (ready (proof-number-box-reserve-ready reserve world)))
                 (:instance proof-number-checked-block-exact-prefix
                            (cuts (list (proof-world-reg 30 world)))
                            (instructions (proof-number-box-reserve-instructions (proof-world-pc world) reserve)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix 3) (suffix steps) (cuts (list (proof-world-reg 30 world)))
                            (before world) (middle (proof-number-box-reserve-ready reserve world))
                            (after stopped) (reason '(:exit . 3))))
           :in-theory (e/d (proof-number-box-reservation-stop-trace-p proof-number-box-reserve-ready
                            proof-number-box-reserve-instructions proof-number-resource-return-p)
                           (proof-resource-observation-p proof-span-p))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-complex-reservation-stop-trace-p
    (a b classifier unchanged fields reserve steps world stopped objects packages)
  (let* ((link (proof-world-reg 30 world))
         (completed (proof-number-types-completion-after t classifier world))
         (selected (proof-number-box-select-after 5 unchanged fields completed)))
    (and (not (equal (rfix b) 0))
         (proof-number-types-completion-trace-p t classifier (list link) a b world objects packages)
         (proof-number-box-select-pre-p 5 unchanged fields completed)
         (proof-number-cut-free-prefix-p 4 (list fields link) completed)
         (proof-number-box-reservation-stop-trace-p reserve steps selected stopped))))

(local
 (defthm represented-second-operand
   (implies (proof-register-arguments-p (list a b) 0 world objects packages)
            (proof-reg-value-p 1 b world objects packages))
   :hints (("Goal"
            :expand ((proof-register-arguments-p (list a b) 0 world objects packages)
                     (proof-register-arguments-p (list b) 1 world objects packages))
            :in-theory (disable proof-register-arguments-p)))
   :rule-classes nil))

(local
 (defthm complex-box-selection-before-stop
   (let* ((link (proof-world-reg 30 world))
          (completed (proof-number-types-completion-after t classifier world))
          (selected (proof-number-box-select-after 5 unchanged fields completed)))
     (implies (proof-number-complex-reservation-stop-trace-p
               a b classifier unchanged fields reserve steps world stopped objects packages)
              (and (proof-segment-p 4 (list fields) completed :cut selected)
                   (equal (proof-world-reg 30 selected) link))))
   :hints (("Goal"
            :use ((:instance proof-number-types-return-or-fallthrough
                             (rational-only t) (cuts (list (proof-world-reg 30 world))))
                  (:instance represented-second-operand (a (rfix a)) (b (rfix b))
                             (world (proof-number-types-completion-after t classifier world)))
                  (:instance proof-number-box-select-by-value (kind 5) (b (rfix b))
                             (world (proof-number-types-completion-after t classifier world)))
                  (:instance proof-number-box-select (kind 5)
                             (world (proof-number-types-completion-after t classifier world))))
            :in-theory (e/d (proof-number-complex-reservation-stop-trace-p
                             proof-number-box-select-count proof-number-box-select-target)
                            (proof-register-arguments-p proof-number-box-reservation-stop-trace-p rfix))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-complex-propagates-reservation-stop
  (let* ((link (proof-world-reg 30 world))
         (count (+ (proof-number-types-completion-steps t classifier world) 7 steps)))
    (implies (and (proof-runtime-pre-p 'complex (list a b) program labels base world objects packages)
                  (proof-number-complex-reservation-stop-trace-p
                   a b classifier unchanged fields reserve steps world stopped objects packages))
             (and (proof-segment-p count (list link) world '(:exit . 3) stopped)
                  (proof-resource-observation-p stopped))))
  :hints (("Goal"
           :use (complex-box-selection-before-stop
                 (:instance proof-number-types-return-or-fallthrough
                            (rational-only t) (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-box-propagates-reservation-stop
                            (world (proof-number-box-select-after
                                    5 unchanged fields (proof-number-types-completion-after t classifier world))))
                 (:instance proof-number-compose-segments
                            (prefix 4) (suffix (+ 3 steps)) (first-cuts (list fields))
                            (last-cuts (list (proof-world-reg 30 world)))
                            (before (proof-number-types-completion-after t classifier world))
                            (middle (proof-number-box-select-after
                                     5 unchanged fields (proof-number-types-completion-after t classifier world)))
                            (reason '(:exit . 3)) (after stopped))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (proof-number-types-completion-steps t classifier world))
                            (suffix (+ 7 steps)) (cuts (list (proof-world-reg 30 world)))
                            (before world) (middle (proof-number-types-completion-after t classifier world))
                            (reason '(:exit . 3)) (after stopped)))
           :in-theory (e/d (proof-number-complex-reservation-stop-trace-p
                            proof-number-box-reservation-stop-trace-p proof-number-resource-return-p)
                           (proof-span-p proof-number-box-reserve-instructions proof-register-arguments-p
                            proof-resource-observation-p rfix))
           :do-not-induct t))
  :rule-classes nil)
