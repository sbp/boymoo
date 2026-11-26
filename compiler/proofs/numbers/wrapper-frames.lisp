(in-package "BOYMOO-PROOFS")

(include-book "type-effects")
(include-book "numeric-frames")
(include-book "immediate")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-base proof-stack-base proof-stack-limit proof-stack-top proof-machine-limit
                     proof-world-page-size proof-world-regions proof-load-word proof-stack-prefix
                     proof-heap-p proof-heap-layout-p proof-object-map-p proof-preserved-heap-p
                     proof-heap-frame-p proof-prefix-preserved-p proof-dynamic-table-preserved-p
                     proof-number-heap-coordinates proof-number-local-write-p
                     proof-step proof-run proof-segment-p proof-execute proof-instruction-effect
                     proof-number-execute-block proof-number-checked-block-p proof-number-cut-free-prefix-p
                     proof-number-exact-prefix-p proof-number-types-completion-trace-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defthm proof-number-heap-machine-context
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (floor (- (proof-machine-limit world) *proof-machine-margin*)))
    (implies (proof-heap-p world objects packages)
             (and (proof-heap-layout-p world)
                  (proof-object-map-p objects objects nil (proof-heap-base world) packages machine)
                  (not (proof-world-stop world))
                  (<= floor sp)
                  (<= sp (proof-number-machine-stack-end world))
                  (equal (mod sp 16) 0))))
  :hints (("Goal"
           :expand ((proof-heap-p world objects packages) (proof-heap-layout-p world))
           :in-theory (e/d (proof-number-machine-stack-end)
                           (proof-align-up proof-runtime-word proof-covered-p proof-regions-p proof-page-size-p
                            proof-disjoint-p proof-static-p proof-external-objects proof-dynamic-entries
                            proof-dynamic-view proof-heap-object-spans-p proof-dynamic-symbol-objects-p
                            proof-string-accounting-p))))
  :rule-classes nil)

(defthm proof-number-same-world-tail-keeps-layout-observations
  (implies (equal (cdr before) (cdr after))
           (and (equal (proof-world-stop before) (proof-world-stop after))
                (equal (proof-world-page-size before) (proof-world-page-size after))
                (equal (proof-world-regions before) (proof-world-regions after))
                (proof-streams-preserved-p before after)))
  :hints (("Goal"
           :in-theory (enable proof-world-stop proof-world-page-size proof-world-regions)
           :cases ((consp before) (consp after))))
  :rule-classes nil)

(local
 (defthm unwritten-machine-frame-keeps-heap-coordinates
   (implies (and (proof-heap-layout-p before)
                 (proof-number-heap-registers-and-world-tail-agree-p before after)
                 (equal (boymoo-model::a64-memory (proof-world-machine before))
                        (boymoo-model::a64-memory (proof-world-machine after))))
            (and (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                 (equal (proof-stack-top before) (proof-stack-top after))
                 (equal (proof-machine-limit before) (proof-machine-limit after))
                 (equal (proof-world-stop before) (proof-world-stop after))
                 (proof-streams-preserved-p before after)))
   :hints (("Goal"
            :use ((:instance proof-number-heap-layout-range-bounds (world before))
                  (:instance proof-number-heap-layout-separates-reservations (world before))
                  (:instance proof-number-span-agreement-with-same-memory
                             (start (- (proof-heap-base before) 128)) (end (+ (proof-heap-base before) 32))
                             (first (proof-world-machine before)) (last (proof-world-machine after)))
                  proof-number-same-world-tail-keeps-layout-observations
                  proof-number-metadata-span-keeps-heap-coordinates)
            :in-theory (e/d (proof-number-heap-registers-and-world-tail-agree-p proof-heap-base
                             proof-machine-limit proof-stack-limit proof-heap-limit proof-box-top proof-stack-top)
                            (proof-streams-preserved-p proof-disjoint-p proof-static-size))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-empty-footprint-at-heap-base-is-local
  (let ((base (proof-heap-base world)))
    (implies (proof-heap-layout-p world)
             (proof-number-local-write-p base base world)))
  :hints (("Goal"
           :use (proof-number-heap-layout-range-bounds proof-number-heap-layout-separates-reservations
                 proof-number-heap-layout-covers-static-and-machine-stack)
           :in-theory (e/d (proof-number-local-write-p proof-number-in-runtime-reservation-p
                            proof-subspan-p proof-number-machine-stack-end)
                           (proof-active-floor proof-box-top proof-spaces-end
                            proof-runtime-word proof-static-size))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm same-memory-keeps-record-memory
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (equal (proof-number-object-memory-p object objects first last)
                   (proof-number-object-memory-p object objects first first)))
   :hints (("Goal"
            :in-theory (e/d (proof-number-object-memory-p proof-number-machine-span-agrees-p proof-world-machine)
                            (proof-span-p proof-object-size proof-byte-entries-agree-p))))
   :rule-classes nil))

(local
 (defthm same-memory-keeps-object-memory
   (implies (and (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
                 (proof-number-objects-memory-p pending objects first first))
            (proof-number-objects-memory-p pending objects first last))
   :hints (("Goal"
            :induct (proof-number-objects-memory-p pending objects first last)
            :in-theory (disable proof-number-object-memory-p))
           ("Subgoal *1/3" :use ((:instance same-memory-keeps-record-memory (object (car pending)))))
           ("Subgoal *1/2" :use ((:instance same-memory-keeps-record-memory (object (car pending))))))
   :rule-classes nil))

(local
 (defthm subset-kept-by-prefixing-one-element
   (implies (subsetp-equal left right)
            (subsetp-equal left (cons item right)))
   :hints (("Goal" :induct (subsetp-equal left right)))))

(local
 (defthm subset-of-itself
   (subsetp-equal items items)
   :hints (("Goal" :induct (len items)))))

(defthm proof-number-unwritten-memory-keeps-object-map
  (let ((first (proof-world-machine before)) (last (proof-world-machine after)))
    (implies (and (proof-heap-p before objects packages)
                  (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last)))
             (and (proof-number-objects-memory-p objects objects first last)
                  (proof-object-map-p objects objects nil (proof-heap-base before) packages last))))
  :hints (("Goal"
           :use ((:instance proof-number-heap-machine-context (world before))
                 (:instance proof-number-map-spans-with-unchanged-memory
                            (pending objects) (old-objects objects) (extra nil)
                            (base (proof-heap-base before)) (machine (proof-world-machine before)))
                 (:instance same-memory-keeps-object-memory
                            (pending objects) (first (proof-world-machine before))
                            (last (proof-world-machine after)))
                 (:instance proof-number-object-map-kept
                            (pending objects) (symbols nil) (old-objects objects)
                            (base (proof-heap-base before))
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (disable proof-number-objects-memory-p)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm unwritten-machine-frame-keeps-heap-layout
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine after)))
          (floor (- (proof-machine-limit before) *proof-machine-margin*)))
     (implies (and (proof-heap-layout-p before)
                   (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                   (equal (proof-world-stop before) (proof-world-stop after))
                   (equal (proof-stack-top before) (proof-stack-top after))
                   (<= floor sp) (<= sp (proof-number-machine-stack-end before))
                   (equal (mod sp 16) 0))
              (proof-heap-layout-p after)))
   :hints (("Goal"
            :use proof-number-coordinate-equality-keeps-layout
            :expand ((proof-heap-layout-p before))
            :in-theory (e/d (proof-number-machine-stack-end)
                            (proof-align-up proof-covered-p proof-regions-p
                             proof-runtime-word proof-disjoint-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-unwritten-machine-frame-preserves-heap
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (sp (boymoo-model::a64-sp last))
         (floor (- (proof-machine-limit before) *proof-machine-margin*)))
    (implies (and (proof-heap-p before objects packages)
                  (proof-number-heap-registers-and-world-tail-agree-p before after)
                  (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
                  (<= floor sp) (<= sp (proof-number-machine-stack-end before))
                  (equal (mod sp 16) 0))
             (proof-preserved-heap-p nil before after objects objects packages)))
  :hints (("Goal"
           :use ((:instance proof-number-heap-machine-context (world before))
                 unwritten-machine-frame-keeps-heap-coordinates
                 unwritten-machine-frame-keeps-heap-layout proof-number-unwritten-memory-keeps-object-map
                 (:instance proof-number-empty-footprint-at-heap-base-is-local (world before))
                 (:instance proof-number-same-top-local-write-preserves-heap
                            (start (proof-heap-base before)) (end (proof-heap-base before))
                            (old-objects objects) (extra nil)))
           :in-theory (e/d (proof-number-memory-change-p)
                           (proof-number-objects-memory-p proof-clear-memory proof-streams-preserved-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-pop-link-preserves-heap
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (after (proof-number-pop-link-after world)))
    (implies (and (proof-heap-p world objects packages)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 16 sp))
                  (unsigned-byte-p 64 (+ 4 (proof-world-pc world)))
                  (<= (+ 16 sp) (proof-number-machine-stack-end world)))
             (and (proof-preserved-heap-p nil world after objects objects packages)
                  (equal (proof-machine-limit after) (proof-machine-limit world)))))
  :hints (("Goal"
           :use (proof-number-heap-machine-context
                 (:instance proof-number-unwritten-machine-frame-preserves-heap
                            (before world) (after (proof-number-pop-link-after world)))
                 (:instance proof-number-mod-shift-by-multiple
                            (a (boymoo-model::a64-sp (proof-world-machine world))) (b 16) (times 1))
                 (:instance proof-number-pop-link-effects (register 23))
                 (:instance proof-number-pop-link-effects (register 24))
                 (:instance proof-number-pop-link-effects (register 25))
                 (:instance proof-number-pop-link-effects (register 26))
                 (:instance proof-number-pop-link-effects (register 27))
                 (:instance proof-number-pop-link-effects (register 28)))
           :in-theory (enable proof-number-heap-registers-and-world-tail-agree-p proof-machine-limit)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-pop-link-register-frame
  (implies (and (not (eq (car (proof-world-machine world)) :svc))
                (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp (proof-world-machine world))))
                (unsigned-byte-p 64 (+ 4 (proof-world-pc world))))
           (proof-register-frame-p limit '(29 30) world (proof-number-pop-link-after world)))
  :hints (("Goal"
           :induct (proof-register-frame-p limit '(29 30) world (proof-number-pop-link-after world)))
          ("Subgoal *1/3" :use ((:instance proof-number-pop-link-effects (register limit))))
          ("Subgoal *1/2" :use ((:instance proof-number-pop-link-effects (register limit))))
          ("Subgoal *1/1" :use ((:instance proof-number-pop-link-effects (register limit)))))
  :rule-classes nil)

(local
 (defthm save-and-call-writes-only-save-pair
   (let* ((machine (proof-world-machine world))
          (sp (boymoo-model::a64-sp machine))
          (after (proof-number-types-first-ready target world)))
     (implies (proof-number-save-and-call-trace-p target cuts world)
              (proof-number-memory-change-p (- sp 16) sp machine (proof-world-machine after))))
   :hints (("Goal"
            :use ((:instance proof-number-save-and-call-effects (register 23))
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
                             (last (proof-world-machine (proof-number-types-first-ready target world)))
                             (other (boymoo-model::a64-store
                                     8 (- (boymoo-model::a64-sp (proof-world-machine world)) 8)
                                     (proof-world-reg 30 world)
                                     (boymoo-model::a64-store
                                      8 (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                      (proof-world-reg 29 world) (proof-world-machine world))))))
            :in-theory (e/d (proof-number-save-and-call-trace-p)
                            (proof-span-p proof-number-memory-change-p boymoo-model::a64-store))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-save-and-call-preserves-heap
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (ready (proof-number-types-first-ready target world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-save-interval-p (- sp 16) world objects)
                  (proof-number-save-and-call-trace-p target cuts world))
             (and (proof-preserved-heap-p nil world ready objects objects packages)
                  (equal (proof-machine-limit ready) (proof-machine-limit world)))))
  :hints (("Goal"
           :use (proof-number-heap-machine-context proof-number-checked-save-and-call
                 save-and-call-writes-only-save-pair
                 (:instance proof-number-save-and-call-effects (register 23))
                 (:instance proof-number-save-and-call-effects (register 24))
                 (:instance proof-number-save-and-call-effects (register 25))
                 (:instance proof-number-save-and-call-effects (register 26))
                 (:instance proof-number-save-and-call-effects (register 27))
                 (:instance proof-number-save-and-call-effects (register 28))
                 (:instance proof-number-mod-shift-by-multiple
                            (a (boymoo-model::a64-sp (proof-world-machine world))) (b 16) (times -1))
                 (:instance proof-number-machine-save-preserves-heap
                            (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (before world) (after (proof-number-types-first-ready target world))))
           :in-theory (e/d (proof-number-heap-registers-and-world-tail-agree-p
                            proof-number-save-and-call-trace-p proof-machine-limit)
                           (proof-span-p boymoo-model::a64-store))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-save-and-call-register-frame
  (implies (not (eq (car (proof-world-machine world)) :svc))
           (proof-register-frame-p limit '(30) world (proof-number-types-first-ready target world)))
  :hints (("Goal"
           :induct (proof-register-frame-p limit '(30) world (proof-number-types-first-ready target world))
           :in-theory (disable proof-heap-base))
          ("Subgoal *1/3" :use ((:instance proof-number-save-and-call-effects (register limit))))
          ("Subgoal *1/2" :use ((:instance proof-number-save-and-call-effects (register limit))))
          ("Subgoal *1/1" :use ((:instance proof-number-save-and-call-effects (register limit)))))
  :rule-classes nil)

(defund proof-number-binary-wrapper-save-intervals-p (types world objects)
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (ready (proof-number-types-first-ready types world)))
    (and (proof-number-save-interval-p (- sp 16) world objects)
         (proof-number-save-interval-p (- sp 32) ready objects))))

(defthm proof-number-preserved-heap-is-valid
  (implies (proof-preserved-heap-p may-intern before after old-objects objects packages)
           (proof-heap-p after objects packages))
  :hints (("Goal" :in-theory (enable proof-preserved-heap-p)))
  :rule-classes nil)

(defthm proof-number-binary-wrapper-preserves-heap-while-saved
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (after (proof-number-binary-types-call-after types classifier world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-world-byte-keys-p world)
                  (proof-number-binary-wrapper-save-intervals-p types world objects)
                  (proof-number-binary-types-call-trace-p types classifier cuts a b world objects packages))
             (and (proof-preserved-heap-p nil world after objects objects packages)
                  (proof-heap-p after objects packages)
                  (equal (proof-machine-limit after) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (- sp 16))
                  (proof-number-world-byte-keys-p after))))
  :hints (("Goal"
           :use (proof-number-binary-wrapper-completes
                 (:instance proof-number-save-and-call-preserves-heap (target types))
                 (:instance proof-number-checked-save-and-call (target types))
                 (:instance proof-number-type-completion-keeps-frame-registers
                            (rational-only nil) (register 23) (world (proof-number-types-first-ready types world)))
                 (:instance proof-number-type-completion-preserves-heap
                            (rational-only nil) (world (proof-number-types-first-ready types world)))
                 (:instance proof-number-exact-prefix-preserves-byte-keys
                            (count (+ 2 (proof-number-types-completion-steps
                                         nil classifier (proof-number-types-first-ready types world))))
                            (before world) (after (proof-number-binary-types-call-after types classifier world)))
                 (:instance proof-number-preserved-heaps-compose
                            (before world) (middle (proof-number-types-first-ready types world))
                            (after (proof-number-binary-types-call-after types classifier world))
                            (old-objects objects) (middle-objects objects))
                 (:instance proof-number-preserved-heap-is-valid
                            (may-intern nil) (before world)
                            (after (proof-number-binary-types-call-after types classifier world))
                            (old-objects objects)))
           :expand ((proof-preserved-heap-p nil world (proof-number-types-first-ready types world)
                                             objects objects packages)
                    (proof-preserved-heap-p nil (proof-number-types-first-ready types world)
                                             (proof-number-binary-types-call-after types classifier world)
                                             objects objects packages))
           :in-theory (e/d (proof-number-binary-wrapper-save-intervals-p proof-number-binary-types-call-after
                            proof-number-binary-types-call-trace-p proof-machine-limit)
                           (proof-number-binary-types-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-binary-wrapper-register-frame-while-saved
  (let* ((after (proof-number-binary-types-call-after types classifier world))
         (clobbers (cons 30 (proof-number-numeric-clobbers))))
    (implies (proof-number-binary-types-call-trace-p types classifier cuts a b world objects packages)
             (proof-register-frame-p 30 clobbers world after)))
  :hints (("Goal"
           :use ((:instance proof-number-save-and-call-register-frame (target types) (limit 30))
                 (:instance proof-number-types-keep-numeric-register-frame
                            (rational-only nil) (limit 30) (world (proof-number-types-first-ready types world)))
                 (:instance proof-number-register-frame-allows-more-clobbers
                            (limit 30) (clobbers '(30)) (extended (cons 30 (proof-number-numeric-clobbers)))
                            (before world) (after (proof-number-types-first-ready types world)))
                 (:instance proof-number-register-frame-allows-more-clobbers
                            (limit 30) (clobbers (proof-number-numeric-clobbers))
                            (extended (cons 30 (proof-number-numeric-clobbers)))
                            (before (proof-number-types-first-ready types world))
                            (after (proof-number-binary-types-call-after types classifier world)))
                 (:instance proof-number-register-frames-compose
                            (limit 30) (clobbers (cons 30 (proof-number-numeric-clobbers)))
                            (before world) (middle (proof-number-types-first-ready types world))
                            (after (proof-number-binary-types-call-after types classifier world))))
           :in-theory (e/d (proof-number-binary-types-call-trace-p proof-number-binary-types-call-after
                            proof-number-save-and-call-trace-p proof-number-numeric-clobbers)
                           (proof-register-frame-p proof-span-p))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-general-gate-after (arity general world)
  (proof-number-execute-block
   (proof-number-tag-gate-instructions arity (proof-world-pc world) general) world))

(defund proof-number-general-gate-trace-p (arity general world)
  (let* ((entry (proof-world-pc world))
         (code (proof-number-tag-gate-instructions arity entry general))
         (link (proof-world-reg 30 world)))
    (and (member-equal arity '(1 2))
         (not (eq (car (proof-world-machine world)) :svc))
         (not (and (oddp (proof-world-reg 0 world))
                   (or (equal arity 1) (oddp (proof-world-reg 1 world)))))
         (unsigned-byte-p 64 (+ entry (* 4 (1+ arity))))
         (unsigned-byte-p 64 general)
         (proof-number-checked-block-p code (list general) world)
         (proof-number-checked-block-p code (list link) world))))

(local
 (defthm tag-gate-is-register-only-code
   (proof-number-register-only-code-p (proof-number-tag-gate-instructions arity entry general) '(2))
   :hints (("Goal"
            :in-theory (enable proof-number-tag-gate-instructions proof-number-register-only-instruction-p)))))

(local
 (defthm recorded-tag-gate-length
   (implies (member-equal arity '(1 2))
            (equal (len (proof-number-tag-gate-instructions arity entry general)) (1+ arity)))
   :hints (("Goal" :in-theory (enable proof-number-tag-gate-instructions)))))

(defthm proof-number-general-tag-gate-reaches-runtime
  (let* ((after (proof-number-general-gate-after arity general world))
         (link (proof-world-reg 30 world)))
    (implies (and (proof-number-general-gate-trace-p arity general world)
                  (proof-heap-p world objects packages))
             (and (proof-segment-p (1+ arity) (list general) world :cut after)
                  (proof-number-exact-prefix-p (1+ arity) (list link) world after)
                  (proof-preserved-heap-p nil world after objects objects packages)
                  (proof-heap-p after objects packages)
                  (proof-register-frame-p 30 '(2) world after)
                  (equal (proof-world-pc after) general)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-machine-limit after) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (implies (not (equal register 2))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal"
           :use (proof-number-public-tag-gate
                 (:instance proof-number-checked-block-exact-prefix
                            (cuts (list (proof-world-reg 30 world)))
                            (instructions (proof-number-tag-gate-instructions
                                           arity (proof-world-pc world) general)))
                 (:instance proof-number-register-only-execution-preserves-heap
                            (clobbers '(2))
                            (instructions (proof-number-tag-gate-instructions
                                           arity (proof-world-pc world) general)))
                 (:instance proof-number-register-only-block-effects
                            (clobbers '(2))
                            (instructions (proof-number-tag-gate-instructions
                                           arity (proof-world-pc world) general)))
                 (:instance proof-number-preserved-heap-is-valid
                            (may-intern nil) (before world) (old-objects objects)
                            (after (proof-number-general-gate-after arity general world))))
           :in-theory (e/d (proof-number-general-gate-after proof-number-general-gate-trace-p)
                           (proof-register-frame-p proof-register-arguments-p proof-number-register-only-code-p
                            proof-number-tag-gate-instructions oddp proof-prefix-preserved-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-register-frames-extend-and-compose
  (implies (and (subsetp-equal first-clobbers clobbers)
                (subsetp-equal last-clobbers clobbers)
                (proof-register-frame-p limit first-clobbers before middle)
                (proof-register-frame-p limit last-clobbers middle after))
           (proof-register-frame-p limit clobbers before after))
  :hints (("Goal"
           :use (proof-number-register-frames-compose
                 (:instance proof-number-register-frame-allows-more-clobbers
                            (clobbers first-clobbers) (extended clobbers) (after middle))
                 (:instance proof-number-register-frame-allows-more-clobbers
                            (clobbers last-clobbers) (extended clobbers) (before middle)))
           :in-theory (disable proof-register-frame-p subsetp-equal)
           :do-not-induct t))
  :rule-classes nil)
