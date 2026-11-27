(in-package "BOYMOO-PROOFS")

(include-book "register-effects")
(include-book "heap-layout")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-cut-free-prefix-p proof-number-exact-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-machine-limit proof-load-word proof-stack-top proof-stack-base proof-stack-end
                     proof-frame-return-p proof-register-frame-p proof-heap-frame-p proof-heap-p proof-heap-layout-p
                     proof-datum-return-p proof-preserved-heap-p proof-number-slot-arguments
                     proof-number-call-value proof-number-call-domain-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod floor ash)))

(defund proof-number-machine-save (world)
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine)))
    (list sp (proof-machine-limit world)
          (proof-load-word sp machine) (proof-load-word (+ 8 sp) machine))))

(defund proof-number-machine-save-fits-p (world)
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (end (+ (- (proof-machine-limit world) *proof-machine-margin*)
                 *proof-machine-reservation*)))
    (and (<= (+ 16 sp) end)
         (<= end (expt 2 64)))))

(defthm proof-number-machine-save-bounds-preserved
  (implies (and (proof-number-machine-save-fits-p before)
                (equal (proof-number-machine-save before) (proof-number-machine-save after)))
           (proof-number-machine-save-fits-p after))
  :hints (("Goal"
           :in-theory (enable proof-number-machine-save-fits-p proof-number-machine-save))))

(defthm proof-number-frame-return-keeps-machine-save
  (implies (and (proof-number-machine-save-fits-p before)
                (not (member-equal 23 clobbers))
                (proof-frame-return-p clobbers changes-flags before after)
                (proof-heap-frame-p before after))
           (equal (proof-number-machine-save after) (proof-number-machine-save before)))
  :hints (("Goal"
           :use ((:instance proof-number-register-frame-keeps (limit 30) (register 23))
                 (:instance proof-number-load-agrees-inside-saved-span
                            (address (boymoo-model::a64-sp (proof-world-machine before)))
                            (start (boymoo-model::a64-sp (proof-world-machine before)))
                            (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                                    *proof-machine-reservation*)))
                 (:instance proof-number-load-agrees-inside-saved-span
                            (address (+ 8 (boymoo-model::a64-sp (proof-world-machine before))))
                            (start (boymoo-model::a64-sp (proof-world-machine before)))
                            (end (+ (- (proof-machine-limit before) *proof-machine-margin*)
                                    *proof-machine-reservation*))))
           :in-theory (e/d (proof-number-machine-save-fits-p proof-number-machine-save
                            proof-frame-return-p proof-heap-frame-p proof-machine-limit)
                           (proof-memory-span-agrees-p proof-streams-preserved-p))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm word-without-memory-change
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (equal (proof-load-word address last) (proof-load-word address first)))
   :hints (("Goal"
            :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                            (boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(defthm proof-number-formula-loads-only-write-call-registers
  (implies (and (consp indices)
                (or (null (cdr indices)) (and (consp (cdr indices)) (null (cddr indices)))))
           (proof-number-register-only-code-p
            (proof-number-formula-call-instructions indices entry target) '(0 1 30)))
  :hints (("Goal"
           :in-theory (enable proof-number-register-only-instruction-p)
           :cases ((null (cdr indices))))))

(local
 (defthm formula-call-start-keeps-machine-save
   (let* ((indices (cdr call))
          (ready (proof-number-formula-call-ready call targets world)))
     (implies (and (not (eq (car (proof-world-machine world)) :svc))
                   (consp indices)
                   (or (null (cdr indices)) (and (consp (cdr indices)) (null (cddr indices)))))
              (equal (proof-number-machine-save ready) (proof-number-machine-save world))))
   :hints (("Goal"
            :use ((:instance proof-number-register-only-block-effects
                             (register 23) (clobbers '(0 1 30))
                             (instructions (proof-number-formula-call-instructions
                                            (cdr call) (proof-world-pc world)
                                            (cdr (assoc-equal (car call) targets)))))
                  (:instance word-without-memory-change
                             (address (boymoo-model::a64-sp (proof-world-machine world)))
                             (first (proof-world-machine world))
                             (last (proof-world-machine (proof-number-formula-call-ready call targets world))))
                  (:instance word-without-memory-change
                             (address (+ 8 (boymoo-model::a64-sp (proof-world-machine world))))
                             (first (proof-world-machine world))
                             (last (proof-world-machine (proof-number-formula-call-ready call targets world)))))
            :in-theory (e/d (proof-number-formula-call-ready proof-number-machine-save proof-machine-limit)
                            (proof-number-formula-call-instructions proof-number-register-only-code-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-formula-call-preserves-machine-save
  (let ((returned (cadr entry))
        (new-objects (caddr entry)))
    (implies (and (proof-number-machine-save-fits-p world)
                  (proof-number-formula-call-trace-p call slots gcd start targets link
                                                     entry world objects packages))
             (and (proof-heap-p returned new-objects packages)
                  (equal (proof-number-machine-save returned) (proof-number-machine-save world)))))
  :hints (("Goal"
           :use (formula-call-start-keeps-machine-save
                 (:instance proof-number-machine-save-bounds-preserved
                            (before world) (after (proof-number-formula-call-ready call targets world)))
                 (:instance proof-number-frame-return-keeps-machine-save
                            (before (proof-number-formula-call-ready call targets world))
                            (after (cadr entry))
                            (clobbers (append *proof-volatile-registers* '(24 26 27)))
                            (changes-flags t)))
           :in-theory (e/d (proof-number-formula-call-trace-p proof-number-formula-call-return-p
                            proof-datum-return-p proof-preserved-heap-p)
                           (proof-prefix-preserved-p proof-dynamic-table-preserved-p proof-heap-frame-p))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm value-stack-write-is-disjoint-from-saves
   (let* ((top (proof-stack-top world))
          (end (+ size top))
          (sp (boymoo-model::a64-sp (proof-world-machine world))))
     (implies (and (proof-heap-p world objects packages)
                   (proof-number-machine-save-fits-p world)
                   (natp size)
                   (<= end (proof-stack-end world)))
              (and (proof-span-p sp 8)
                   (proof-span-p (+ 8 sp) 8)
                   (proof-disjoint-p sp (+ sp 8) top end)
                   (proof-disjoint-p (+ sp 8) (+ sp 16) top end))))
   :hints (("Goal"
            :use proof-number-heap-layout-separates-reservations
            :expand ((proof-heap-p world objects packages))
            :in-theory (e/d (proof-number-machine-save-fits-p proof-stack-prefix)
                            (proof-dynamic-entries proof-dynamic-view proof-external-objects proof-runtime-word
                             proof-heap-object-spans-p proof-string-accounting-p proof-static-p
                             proof-object-map-p proof-dynamic-symbol-objects-p proof-stack-views))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-formula-spill-preserves-machine-save
  (implies (and (proof-heap-p world objects packages)
                (proof-number-machine-save-fits-p world)
                (<= (+ 8 (proof-stack-top world)) (proof-stack-end world))
                (proof-number-formula-spill-trace-p value link world objects packages))
           (equal (proof-number-machine-save (proof-number-formula-spill-after world))
                  (proof-number-machine-save world)))
  :hints (("Goal"
           :use ((:instance value-stack-write-is-disjoint-from-saves (size 8))
                 (:instance proof-number-formula-spills-result
                            (address (boymoo-model::a64-sp (proof-world-machine world))))
                 (:instance proof-number-formula-spills-result
                            (address (+ 8 (boymoo-model::a64-sp (proof-world-machine world)))))
                 (:instance proof-number-value-store-effects (arity 1) (register 23)))
           :in-theory (enable proof-number-machine-save proof-number-formula-spill-after
                              proof-number-formula-spill-trace-p proof-number-formula-argument-store-instructions
                              proof-machine-limit)
           :do-not-induct t))
  :rule-classes nil)

(defun proof-number-formula-spills-in-value-stack-p (calls trace)
  (if (endp (cdr calls))
      t
    (and (<= (+ 8 (proof-stack-top (cadar trace))) (proof-stack-end (cadar trace)))
         (proof-number-formula-spills-in-value-stack-p (cdr calls) (cdr trace)))))

(defthm proof-number-formula-growth-preserves-machine-save
  (let* ((ready (proof-number-formula-grow-ready name grow world))
         (sp (- (boymoo-model::a64-sp (proof-world-machine world)) 16)))
    (implies (and (proof-number-formula-growth-trace-p name grow steps world grown
                                                       objects new-objects packages)
                  (proof-number-machine-save-fits-p ready))
             (and (proof-heap-p grown new-objects packages)
                  (proof-number-machine-save-fits-p grown)
                  (equal (proof-number-machine-save grown)
                         (list sp (proof-machine-limit ready)
                               (proof-world-reg 19 world) (proof-world-reg 30 world))))))
  :hints (("Goal"
           :use ((:instance proof-number-formula-calls-growth
                            (bytes (proof-number-formula-frame-bytes name)))
                 (:instance proof-number-frame-return-keeps-machine-save
                            (clobbers '(9 10 11 12 24)) (changes-flags t)
                            (before (proof-number-formula-grow-ready name grow world)) (after grown))
                 (:instance proof-number-machine-save-bounds-preserved
                            (before (proof-number-formula-grow-ready name grow world)) (after grown)))
           :in-theory (e/d (proof-number-formula-growth-trace-p proof-number-formula-grow-ready
                            proof-grow-return-p proof-preserved-heap-p proof-number-machine-save)
                           (proof-frame-return-p proof-fixed-heap-p proof-grow-limit
                            proof-prefix-preserved-p proof-dynamic-table-preserved-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-formula-arguments-preserve-machine-save
  (let* ((arity (len args))
         (after (proof-number-formula-arguments-after args world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-machine-save-fits-p world)
                  (<= (+ (proof-stack-top world) (* 8 arity)) (proof-stack-end world))
                  (proof-number-formula-argument-trace-p args link world objects packages))
             (equal (proof-number-machine-save after) (proof-number-machine-save world))))
  :hints (("Goal"
           :use ((:instance value-stack-write-is-disjoint-from-saves (size (* 8 (len args))))
                 (:instance proof-number-formula-writes-arguments
                            (arity (len args)) (address (boymoo-model::a64-sp (proof-world-machine world))))
                 (:instance proof-number-formula-writes-arguments
                            (arity (len args)) (address (+ 8 (boymoo-model::a64-sp (proof-world-machine world)))))
                 (:instance proof-number-value-store-effects (arity (len args)) (register 23)))
           :in-theory (e/d (proof-number-machine-save proof-number-formula-arguments-after
                            proof-number-formula-argument-trace-p proof-number-argument-list-p
                            proof-machine-limit)
                           (proof-prefix-preserved-p proof-register-arguments-p proof-machine-value-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-formula-body-preserves-machine-save
  (implies (and (consp calls)
                (proof-number-machine-save-fits-p world)
                (proof-number-formula-spills-in-value-stack-p calls trace)
                (proof-number-formula-body-trace-p calls trace slots gcd start targets link
                                                   world objects packages))
           (equal (proof-number-machine-save (cadar (last trace))) (proof-number-machine-save world)))
  :hints (("Goal"
           :induct (proof-number-formula-body-trace-p calls trace slots gcd start targets link
                                                     world objects packages))
          ("Subgoal *1/3"
           :use ((:instance proof-number-formula-call-preserves-machine-save (call (car calls)) (entry (car trace)))
                 (:instance proof-number-machine-save-bounds-preserved (before world) (after (cadar trace)))
                 (:instance proof-number-formula-spill-preserves-machine-save
                            (world (cadar trace)) (objects (caddar trace))
                            (value (proof-number-call-value
                                    (caar calls) (proof-number-slot-arguments (cdar calls) slots) gcd)))
                 (:instance proof-number-machine-save-bounds-preserved
                            (before (cadar trace)) (after (proof-number-formula-spill-after (cadar trace))))))
          ("Subgoal *1/2"
           :use ((:instance proof-number-formula-call-preserves-machine-save
                            (call (car calls)) (entry (car trace))))))
  :rule-classes nil)

(defund proof-number-formula-return-trace-p
    (name args gcd grow growth-steps targets trace world grown objects grown-objects packages)
  (let* ((link (proof-world-reg 30 world))
         (ready (proof-number-formula-grow-ready name grow world))
         (start (len (cdr (proof-stack-prefix (proof-stack-top grown) grown grown-objects packages))))
         (calls (proof-number-formula-calls name))
         (body (proof-number-formula-arguments-after args grown))
         (returned (cadar (last trace)))
         (machine (proof-world-machine returned)))
    (and (natp growth-steps)
         (consp calls)
         (proof-number-formula-growth-trace-p name grow growth-steps world grown
                                              objects grown-objects packages)
         (proof-number-machine-save-fits-p ready)
         (<= (+ (proof-stack-top grown) (* 8 (len args))) (proof-stack-end grown))
         (proof-number-formula-argument-trace-p args link grown grown-objects packages)
         (proof-number-formula-spills-in-value-stack-p calls trace)
         (proof-number-formula-body-trace-p calls trace args gcd start targets link
                                            body grown-objects packages)
         (proof-number-checked-block-p *proof-number-formula-return-instructions* (list link) returned)
         (not (eq (car machine) :svc))
         (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp machine))))))

(defthm proof-number-formula-epilogue-reads-original-save
  (let* ((returned (cadar (last trace)))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (machine (proof-world-machine returned)))
    (implies (proof-number-formula-return-trace-p
              name args gcd grow growth-steps targets trace world grown objects grown-objects packages)
             (and (equal (+ 16 (boymoo-model::a64-sp machine)) sp)
                  (equal (proof-load-word (boymoo-model::a64-sp machine) machine) (proof-world-reg 19 world))
                  (equal (proof-load-word (+ 8 (boymoo-model::a64-sp machine)) machine)
                         (proof-world-reg 30 world)))))
  :hints (("Goal"
           :use ((:instance proof-number-formula-growth-preserves-machine-save
                            (steps growth-steps) (new-objects grown-objects))
                 (:instance proof-number-formula-arguments-preserve-machine-save
                            (world grown) (objects grown-objects) (link (proof-world-reg 30 world)))
                 (:instance proof-number-machine-save-bounds-preserved
                            (before grown) (after (proof-number-formula-arguments-after args grown)))
                 (:instance proof-number-formula-body-preserves-machine-save
                            (calls (proof-number-formula-calls name)) (slots args)
                            (start (len (cdr (proof-stack-prefix (proof-stack-top grown)
                                                                grown grown-objects packages))))
                            (link (proof-world-reg 30 world))
                            (world (proof-number-formula-arguments-after args grown)) (objects grown-objects)))
           :in-theory (e/d (proof-number-formula-return-trace-p proof-number-machine-save)
                           (proof-stack-prefix proof-number-formula-calls proof-number-formula-body-trace-p
                            proof-number-formula-spills-in-value-stack-p
                            proof-number-formula-growth-trace-p proof-number-formula-argument-trace-p last))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-generated-formula-return-with-saved-link
  (let* ((link (proof-world-reg 30 world))
         (count (+ 9 growth-steps
                   (proof-number-formula-trace-steps (proof-number-formula-calls name) trace)))
         (after (proof-number-formula-trace-after trace)))
    (implies (and (proof-number-formula-result-p name args gcd result)
                  (proof-number-formula-return-trace-p
                   name args gcd grow growth-steps targets trace world grown objects grown-objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (proof-reg-value-p 0 result after (caddar (last trace)) packages))))
  :hints (("Goal"
           :use (proof-number-formula-epilogue-reads-original-save proof-number-generated-formula-return
                 (:instance proof-number-formula-restores-frame (world (cadar (last trace)))))
           :in-theory (e/d (proof-number-formula-return-trace-p proof-number-formula-trace-p
                            proof-number-formula-trace-after)
                           (proof-number-formula-body-trace-p proof-number-formula-calls
                            proof-number-formula-result-p proof-number-formula-trace-steps
                            proof-stack-prefix proof-world-reg proof-reg-value-p last))
           :do-not-induct t))
  :rule-classes nil)
