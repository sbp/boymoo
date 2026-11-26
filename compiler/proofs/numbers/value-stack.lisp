(in-package "BOYMOO-PROOFS")

(include-book "wrapper-frames")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p proof-number-checked-block-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-world-regions proof-world-page-size proof-machine-limit proof-load-word
                     proof-heap-base proof-stack-base proof-stack-end proof-stack-limit proof-stack-top
                     proof-heap-p proof-heap-layout-p proof-heap-frame-p proof-preserved-heap-p
                     proof-prefix-preserved-p proof-dynamic-table-preserved-p proof-stack-prefix
                     proof-object-map-p proof-object-disjoint-p proof-number-objects-memory-p
                     proof-number-memory-change-p proof-number-machine-span-agrees-p
                     proof-number-local-write-p proof-number-append-storage-p
                     boymoo-model::a64-sp boymoo-model::a64-memory mod ash floor)))

(defund proof-number-value-append-pre-p (arity world objects packages)
  (let ((size (* 8 arity)))
    (and (member-equal arity '(1 2))
         (not (eq (car (proof-world-machine world)) :svc))
         (proof-number-append-storage-p size world objects packages)
         (unsigned-byte-p 64 (+ (proof-stack-top world) size))
         (<= (+ (proof-stack-top world) size) (proof-stack-limit world)))))

(local
 (defthm value-stack-layout-limits
   (implies (proof-heap-layout-p world)
            (and (<= (proof-stack-base world) (proof-stack-top world))
                 (<= (proof-stack-limit world) (proof-stack-end world))
                 (equal (mod (proof-stack-top world) 8) 0)))
   :hints (("Goal"
            :expand ((proof-heap-layout-p world))
            :in-theory (disable proof-runtime-word proof-align-up proof-covered-p
                                proof-regions-p proof-disjoint-p proof-page-size-p)))
   :rule-classes nil))

(local
 (defthm append-is-within-value-reservation
   (let ((top (proof-stack-top world)))
     (implies (and (proof-heap-layout-p world)
                   (natp size)
                   (proof-span-p top size)
                   (<= (+ top size) (proof-stack-limit world)))
              (proof-number-in-runtime-reservation-p top (+ top size) world)))
   :hints (("Goal"
            :use (value-stack-layout-limits proof-number-heap-layout-separates-reservations)
            :in-theory (e/d (proof-number-in-runtime-reservation-p proof-subspan-p)
                            (proof-disjoint-p proof-span-p proof-runtime-word proof-static-size))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm append-slot-is-local
   (let* ((top (proof-stack-top world))
          (end (+ top size))
          (base (proof-heap-base world)))
     (implies (and (proof-heap-layout-p world)
                   (posp top) (natp size) (proof-span-p top size)
                   (<= end (proof-stack-limit world)))
              (and (proof-number-local-write-p top end world)
                   (proof-disjoint-p (- base 128) (+ base 32) top end)
                   (natp base) (<= 128 base) (<= (+ base 32) (expt 2 64)))))
   :hints (("Goal"
            :use (proof-number-heap-layout-separates-reservations proof-number-heap-layout-range-bounds
                  value-stack-layout-limits append-is-within-value-reservation)
            :in-theory (e/d (proof-number-local-write-p proof-number-machine-stack-end)
                            (proof-runtime-word proof-covered-p proof-regions-p proof-align-up
                             proof-span-p proof-static-size proof-box-top proof-heap-limit
                             proof-active-floor proof-active-end proof-cons-floor
                             proof-inactive-floor proof-inactive-end proof-spaces-end
                             proof-number-in-runtime-reservation-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-value-append-keeps-layout-coordinates
  (let* ((top (proof-stack-top world))
         (end (+ top (* 8 arity)))
         (after (proof-number-execute-block
                 (proof-number-formula-argument-store-instructions arity) world)))
    (implies (and (proof-heap-layout-p world)
                  (proof-number-value-append-pre-p arity world objects packages))
             (and (proof-number-local-write-p top end world)
                  (proof-number-memory-change-p top end
                                                (proof-world-machine world) (proof-world-machine after))
                  (equal (proof-number-heap-coordinates world) (proof-number-heap-coordinates after))
                  (equal (proof-stack-top after) end)
                  (equal (proof-machine-limit after) (proof-machine-limit world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (proof-streams-preserved-p world after)
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world))))))
  :hints (("Goal"
           :use ((:instance append-slot-is-local (size (* 8 arity)))
                 proof-number-value-store-keeps-frame-memory
                 (:instance proof-number-value-store-effects (register 23))
                 (:instance proof-number-value-store-effects (register 24))
                 (:instance proof-number-value-store-effects (register 26))
                 (:instance proof-number-value-store-effects (register 27))
                 (:instance proof-number-value-store-effects (register 28))
                 (:instance proof-number-footprint-keeps-disjoint-span
                            (lower (- (proof-heap-base world) 128)) (upper (+ (proof-heap-base world) 32))
                            (start (proof-stack-top world)) (end (+ (proof-stack-top world) (* 8 arity)))
                            (first (proof-world-machine world))
                            (last (proof-world-machine
                                   (proof-number-execute-block
                                    (proof-number-formula-argument-store-instructions arity) world))))
                 (:instance proof-number-same-world-tail-keeps-layout-observations
                            (before world) (after (proof-number-execute-block
                                                   (proof-number-formula-argument-store-instructions arity) world)))
                 (:instance proof-number-metadata-span-keeps-heap-coordinates
                            (before world) (after (proof-number-execute-block
                                                   (proof-number-formula-argument-store-instructions arity) world))))
           :in-theory (e/d (proof-number-value-append-pre-p proof-number-append-storage-p
                            proof-machine-limit proof-stack-limit proof-heap-limit proof-box-top)
                           (proof-span-p proof-streams-preserved-p proof-stack-base
                            proof-number-formula-argument-store-instructions boymoo-model::a64-store))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm append-top-fits-kept-layout
   (let ((after (proof-number-execute-block
                 (proof-number-formula-argument-store-instructions arity) world)))
     (implies (and (proof-heap-layout-p world)
                   (proof-number-value-append-pre-p arity world objects packages))
              (proof-heap-layout-p after)))
   :hints (("Goal"
            :use (proof-number-value-append-keeps-layout-coordinates
                  (:instance proof-number-coordinate-equality-keeps-layout
                             (before world) (after (proof-number-execute-block
                                                    (proof-number-formula-argument-store-instructions arity) world)))
                  (:instance proof-number-mod-shift-by-multiple
                             (a (proof-stack-top world)) (b 8) (times arity)))
            :expand ((proof-heap-layout-p world))
            :in-theory (e/d (proof-number-value-append-pre-p)
                            (proof-runtime-word proof-align-up proof-covered-p proof-regions-p proof-disjoint-p
                             proof-number-append-storage-p proof-spaces-end proof-heap-limit
                             proof-active-floor proof-active-end proof-cons-floor
                             proof-inactive-floor proof-inactive-end proof-box-top))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm append-write-keeps-object-map
   (let* ((first (proof-world-machine world))
          (after (proof-number-execute-block
                  (proof-number-formula-argument-store-instructions arity) world))
          (last (proof-world-machine after)))
     (implies (proof-number-value-append-pre-p arity world objects packages)
              (and (proof-number-objects-memory-p objects objects first last)
                   (proof-object-map-p objects objects nil (proof-heap-base world) packages last))))
   :hints (("Goal"
            :use (proof-number-value-store-keeps-frame-memory
                  (:instance proof-number-disjoint-footprint-keeps-old-values
                             (start (proof-stack-top world)) (end (+ (proof-stack-top world) (* 8 arity)))
                             (before world) (after (proof-number-execute-block
                                                    (proof-number-formula-argument-store-instructions arity) world))
                             (old-objects objects) (extra nil) (word nil) (value nil))
                  (:instance proof-number-object-map-kept
                             (pending objects) (old-objects objects) (symbols nil) (base (proof-heap-base world))
                             (first (proof-world-machine world))
                             (last (proof-world-machine
                                    (proof-number-execute-block
                                     (proof-number-formula-argument-store-instructions arity) world)))))
            :in-theory (enable proof-number-value-append-pre-p proof-number-append-storage-p)
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-value-append-preserves-heap
  (let ((after (proof-number-execute-block
                (proof-number-formula-argument-store-instructions arity) world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-number-value-append-pre-p arity world objects packages)
                  (proof-stack-prefix (proof-stack-top after) after objects packages))
             (proof-preserved-heap-p nil world after objects objects packages)))
  :hints (("Goal"
           :use (proof-number-heap-machine-context proof-number-value-append-keeps-layout-coordinates
                 append-top-fits-kept-layout append-write-keeps-object-map
                 (:instance proof-number-local-write-keeps-heap-with-initialized-stack
                            (before world) (after (proof-number-execute-block
                                                   (proof-number-formula-argument-store-instructions arity) world))
                            (start (proof-stack-top world)) (end (+ (proof-stack-top world) (* 8 arity)))
                            (old-objects objects) (extra nil))
                 (:instance proof-number-local-write-preserves-prefix
                            (before world) (after (proof-number-execute-block
                                                   (proof-number-formula-argument-store-instructions arity) world))
                            (start (proof-stack-top world)) (end (+ (proof-stack-top world) (* 8 arity)))
                            (old-objects objects)))
           :in-theory (e/d (proof-preserved-heap-p proof-number-value-append-pre-p)
                           (proof-number-append-storage-p proof-number-local-write-p proof-span-p
                            proof-heap-frame-p proof-prefix-preserved-p proof-dynamic-table-preserved-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-value-append-register-frame
  (let ((after (proof-number-execute-block
                (proof-number-formula-argument-store-instructions arity) world)))
    (implies (proof-number-value-append-pre-p arity world objects packages)
             (proof-register-frame-p limit '(25) world after)))
  :hints (("Goal"
           :induct (proof-register-frame-p limit '(25) world
                                           (proof-number-execute-block
                                            (proof-number-formula-argument-store-instructions arity) world))
           :in-theory (enable proof-number-value-append-pre-p))
          ("Subgoal *1/3" :use ((:instance proof-number-value-store-effects (register limit))))
          ("Subgoal *1/2" :use ((:instance proof-number-value-store-effects (register limit))))
          ("Subgoal *1/1" :use ((:instance proof-number-value-store-effects (register limit)))))
  :rule-classes nil)

(defthm proof-number-stack-prefix-bounds
  (implies (proof-stack-prefix top world objects packages)
           (and (natp top)
                (<= (proof-stack-base world) top)
                (<= top (proof-stack-top world))
                (equal (mod (- top (proof-stack-base world)) 8) 0)))
  :hints (("Goal" :in-theory (enable proof-stack-prefix)))
  :rule-classes nil)

(local
 (defthm the-empty-footprint-excludes-shorter-prefix
   (let ((base (proof-heap-base world)) (bottom (proof-stack-base world)))
     (implies (and (proof-number-local-write-p base base world)
                   (<= top (proof-stack-top world)))
              (and (posp base)
                   (proof-disjoint-p bottom top base base))))
   :hints (("Goal"
            :in-theory (e/d (proof-number-local-write-p)
                            (proof-number-in-runtime-reservation-p proof-static-size
                             proof-number-machine-stack-end))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm unwritten-memory-keeps-shorter-prefix
   (let ((first (proof-world-machine before))
         (last (proof-world-machine after)))
     (implies (and (proof-heap-p before objects packages)
                   (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                   (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
                   (proof-stack-prefix top before objects packages)
                   (<= top (proof-stack-top after)))
              (proof-prefix-preserved-p top before after objects objects packages)))
   :hints (("Goal"
            :use ((:instance proof-number-heap-machine-context (world before))
                  (:instance proof-number-empty-footprint-at-heap-base-is-local (world before))
                  (:instance proof-number-stack-prefix-bounds (world before))
                  (:instance the-empty-footprint-excludes-shorter-prefix (world before))
                  proof-number-unwritten-memory-keeps-object-map
                  proof-number-equal-heap-coordinates-preserve-fields
                  (:instance proof-number-disjoint-footprint-keeps-prefix
                             (start (proof-heap-base before)) (end (proof-heap-base before))
                             (old-objects objects)))
            :in-theory (e/d (proof-number-memory-change-p)
                            (proof-disjoint-p proof-clear-memory proof-static-size))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-value-stack-drop-keeps-heap-window
  (let* ((top (proof-stack-top after))
         (first (proof-world-machine before))
         (last (proof-world-machine after)))
    (implies (and (proof-heap-p before objects packages)
                  (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                  (proof-heap-layout-p after)
                  (proof-streams-preserved-p before after)
                  (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
                  (proof-stack-prefix top before objects packages))
             (and (proof-heap-p after objects packages)
                  (proof-heap-frame-p before after)
                  (proof-prefix-preserved-p top before after objects objects packages)
                  (proof-dynamic-table-preserved-p nil before after objects objects packages))))
  :hints (("Goal"
           :use ((:instance unwritten-memory-keeps-shorter-prefix (top (proof-stack-top after)))
                 (:instance proof-number-heap-machine-context (world before))
                 (:instance proof-number-empty-footprint-at-heap-base-is-local (world before))
                 proof-number-unwritten-memory-keeps-object-map
                 (:instance proof-number-local-write-keeps-heap-with-initialized-stack
                            (old-objects objects) (extra nil)
                            (start (proof-heap-base before)) (end (proof-heap-base before))))
           :in-theory (e/d (proof-number-memory-change-p proof-prefix-preserved-p)
                           (proof-clear-memory proof-streams-preserved-p))
           :do-not-induct t))
  :rule-classes nil)
