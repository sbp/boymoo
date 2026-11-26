(in-package "BOYMOO-PROOFS")

(include-book "local-heap")
(include-book "type-dispatch")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-world-page-size proof-world-regions proof-heap-base proof-stack-base
                     proof-stack-top proof-static-size proof-machine-limit proof-load-word
                     proof-number-memory-change-p proof-number-machine-span-agrees-p
                     proof-number-objects-memory-p proof-object-map-p proof-object-disjoint-p
                     proof-heap-layout-p proof-heap-p proof-preserved-heap-p proof-heap-frame-p
                     proof-number-checked-block-p proof-number-execute-block
                     proof-step proof-run proof-segment-p proof-execute proof-instruction-effect
                     boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-store mod ash floor)))

(defund proof-number-save-interval-p (start world objects)
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine)))
    (and (posp start)
         (proof-span-p start (- sp start))
         (<= (- (proof-machine-limit world) *proof-machine-margin*) start)
         (proof-object-disjoint-p start sp objects machine))))

(defund proof-number-heap-registers-and-world-tail-agree-p (before after)
  (and (equal (proof-world-reg 23 before) (proof-world-reg 23 after))
       (equal (proof-world-reg 24 before) (proof-world-reg 24 after))
       (equal (proof-world-reg 25 before) (proof-world-reg 25 after))
       (equal (proof-world-reg 26 before) (proof-world-reg 26 after))
       (equal (proof-world-reg 27 before) (proof-world-reg 27 after))
       (equal (proof-world-reg 28 before) (proof-world-reg 28 after))
       (equal (cdr before) (cdr after))))

(local
 (defthm save-interval-locality
   (let* ((machine (proof-world-machine world))
          (sp (boymoo-model::a64-sp machine))
          (base (proof-heap-base world)))
     (implies (and (proof-heap-layout-p world)
                   (proof-number-save-interval-p start world objects))
              (and (proof-number-local-write-p start sp world)
                   (proof-disjoint-p (- base 128) (+ base 32) start sp)
                   (natp base) (<= 128 base) (<= (+ base 32) (expt 2 64)))))
   :hints (("Goal"
            :use (proof-number-heap-layout-range-bounds proof-number-heap-layout-separates-reservations)
            :in-theory (e/d (proof-number-save-interval-p
                             proof-number-local-write-p proof-number-in-runtime-reservation-p
                             proof-number-machine-stack-end)
                            (proof-reg proof-runtime-word proof-regions-p proof-page-size-p
                             proof-box-top proof-heap-limit proof-stack-limit proof-stack-end
                             proof-spaces-end proof-covered-p proof-align-up
                             proof-active-end proof-active-floor proof-inactive-floor
                             proof-inactive-end proof-cons-floor))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm shared-tail-gives-streams-and-mappings
   (implies (equal (cdr before) (cdr after))
            (and (proof-streams-preserved-p before after)
                 (equal (proof-world-page-size before) (proof-world-page-size after))
                 (equal (proof-world-regions before) (proof-world-regions after))
                 (equal (proof-world-stop before) (proof-world-stop after))))
   :hints (("Goal"
            :in-theory (enable proof-world-page-size proof-world-regions proof-world-stop)
            :cases ((consp before) (consp after))))
   :rule-classes nil))

(defthm proof-number-save-keeps-heap-coordinates
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (sp (boymoo-model::a64-sp first)))
    (implies (and (proof-heap-layout-p before)
                  (proof-number-save-interval-p start before objects)
                  (proof-number-memory-change-p start sp first last)
                  (proof-number-heap-registers-and-world-tail-agree-p before after))
             (and (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                  (equal (proof-stack-top before) (proof-stack-top after))
                  (equal (proof-machine-limit before) (proof-machine-limit after))
                  (equal (proof-world-stop before) (proof-world-stop after))
                  (proof-streams-preserved-p before after))))
  :hints (("Goal"
           :use ((:instance save-interval-locality (world before))
                 shared-tail-gives-streams-and-mappings
                 (:instance proof-number-footprint-keeps-disjoint-span
                            (end (boymoo-model::a64-sp (proof-world-machine before)))
                            (lower (- (proof-heap-base before) 128)) (upper (+ (proof-heap-base before) 32))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 proof-number-metadata-span-keeps-heap-coordinates)
           :in-theory (e/d (proof-number-save-interval-p proof-number-heap-registers-and-world-tail-agree-p
                            proof-stack-top proof-machine-limit proof-heap-base)
                           (proof-streams-preserved-p))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm heap-layout-after-save
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine after)))
          (floor (- (proof-machine-limit before) *proof-machine-margin*)))
     (implies (and (proof-heap-layout-p before)
                   (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                   (equal (proof-stack-top before) (proof-stack-top after))
                   (equal (proof-world-stop before) (proof-world-stop after))
                   (<= floor sp) (<= sp (+ floor *proof-machine-reservation*))
                   (equal (mod sp 16) 0))
              (proof-heap-layout-p after)))
   :hints (("Goal"
            :use proof-number-coordinate-equality-keeps-layout
            :expand ((proof-heap-layout-p before))
            :in-theory (disable proof-align-up proof-covered-p proof-disjoint-p proof-regions-p
                                proof-runtime-word proof-stack-limit)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm heap-supplies-layout-and-map
   (implies (proof-heap-p world objects packages)
            (and (proof-heap-layout-p world)
                 (proof-object-map-p objects objects nil (proof-heap-base world) packages
                                     (proof-world-machine world))))
   :hints (("Goal"
            :expand ((proof-heap-p world objects packages))
            :in-theory (disable proof-static-p proof-heap-object-spans-p proof-external-objects
                                proof-dynamic-entries proof-dynamic-view proof-dynamic-symbol-objects-p
                                proof-string-accounting-p proof-stack-prefix)))
   :rule-classes nil))

(local
 (defthm save-footprint-keeps-object-map
   (let* ((first (proof-world-machine before))
          (last (proof-world-machine after))
          (base (proof-heap-base before))
          (sp (boymoo-model::a64-sp first)))
     (implies (and (proof-object-map-p objects objects nil base packages first)
                   (proof-number-save-interval-p start before objects)
                   (proof-number-memory-change-p start sp first last))
              (and (proof-number-objects-memory-p objects objects first last)
                   (proof-object-map-p objects objects nil base packages last))))
   :hints (("Goal"
            :use ((:instance proof-number-disjoint-footprint-keeps-old-values
                             (end (boymoo-model::a64-sp (proof-world-machine before)))
                             (old-objects objects) (extra nil) (word nil) (value nil))
                  (:instance proof-number-object-map-kept
                             (pending objects) (old-objects objects) (symbols nil)
                             (base (proof-heap-base before))
                             (first (proof-world-machine before)) (last (proof-world-machine after))))
            :in-theory (enable proof-number-save-interval-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm new-sp-fits-before-reservation
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine after)))
          (floor (- (proof-machine-limit before) *proof-machine-margin*)))
     (implies (and (proof-heap-layout-p before)
                   (proof-number-save-interval-p start before objects)
                   (<= start sp) (<= sp (boymoo-model::a64-sp (proof-world-machine before))))
              (and (<= floor sp) (<= sp (+ floor *proof-machine-reservation*)))))
   :hints (("Goal"
            :use ((:instance proof-number-heap-layout-separates-reservations (world before)))
            :in-theory (enable proof-number-save-interval-p)
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-machine-save-preserves-heap
  (let* ((first (proof-world-machine before))
         (last (proof-world-machine after))
         (sp (boymoo-model::a64-sp last)))
    (implies (and (proof-heap-p before objects packages)
                  (proof-number-save-interval-p start before objects)
                  (proof-number-memory-change-p start (boymoo-model::a64-sp first) first last)
                  (proof-number-heap-registers-and-world-tail-agree-p before after)
                  (<= start sp) (<= sp (boymoo-model::a64-sp first))
                  (equal (mod sp 16) 0))
             (proof-preserved-heap-p nil before after objects objects packages)))
  :hints (("Goal"
           :use ((:instance heap-supplies-layout-and-map (world before))
                 proof-number-save-keeps-heap-coordinates heap-layout-after-save
                 new-sp-fits-before-reservation save-footprint-keeps-object-map
                 (:instance save-interval-locality (world before))
                 (:instance proof-number-same-top-local-write-preserves-heap
                            (old-objects objects) (extra nil)
                            (end (boymoo-model::a64-sp (proof-world-machine before)))))
           :in-theory (disable proof-streams-preserved-p)
           :do-not-induct t))
  :rule-classes nil)
