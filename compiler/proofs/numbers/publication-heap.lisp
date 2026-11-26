(in-package "BOYMOO-PROOFS")

(include-book "local-heap")
(include-book "box-return")
(include-book "store-traces")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-load-word proof-heap-p proof-heap-layout-p proof-heap-base
                     proof-stack-base proof-stack-top proof-machine-limit proof-static-size
                     proof-segment-p proof-run proof-step proof-execute proof-instruction-effect
                     proof-number-checked-block-p proof-reserved-span-p proof-object-map-p
                     proof-number-memory-change-p proof-object-disjoint-p
                     proof-number-objects-memory-p proof-number-machine-span-agrees-p
                     proof-number-box-object-map proof-number-next-object-rank
                     proof-number-execute-block
                     boymoo-model::a64-sp boymoo-model::a64-pc boymoo-model::a64-memory
                     boymoo-model::a64-store boymoo-model::a64-write-reg
                     boymoo-model::a64-read-reg boymoo-model::a64-set-pc
                     boymoo-model::a64-unsigned mod floor ash
                     (:definition update-nth) (:definition nth))))

(defthm proof-number-reserved-header-is-local-write
  (let* ((machine (proof-world-machine world))
         (base (proof-heap-base world))
         (end (+ address 24)))
    (implies (and (proof-heap-layout-p world)
                  (proof-reserved-span-p :header address 24 world objects))
             (and (proof-number-local-write-p address end world)
                  (proof-disjoint-p (- base 128) (+ base 32) address end)
                  (<= 128 base) (<= (+ base 32) (expt 2 64))
                  (natp base) (<= base address)
                  (proof-span-p address 24)
                  (proof-object-disjoint-p address end objects machine))))
  :hints (("Goal"
           :use (proof-number-heap-layout-range-bounds
                 proof-number-heap-layout-separates-reservations)
           :in-theory (e/d (proof-reserved-span-p proof-number-local-write-p
                            proof-number-in-runtime-reservation-p proof-number-machine-stack-end)
                           (proof-runtime-word proof-align-up proof-covered-p
                            proof-regions-p proof-page-size-p proof-stack-limit
                            proof-box-top proof-heap-limit proof-stack-end proof-spaces-end
                            proof-active-floor proof-active-end proof-cons-floor
                            proof-inactive-floor proof-inactive-end))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm box-stores-have-24-byte-footprint
   (implies (proof-span-p address 24)
            (proof-number-memory-change-p address (+ 24 address) machine
                                          (proof-number-box-field-stores address header left right machine)))
   :hints (("Goal"
            :use ((:instance proof-number-store-changes-only-footprint
                             (start address) (end (+ 24 address)) (dest address) (size 8) (value header))
                  (:instance proof-number-pair-store-changes-only-footprint
                             (start address) (end (+ 24 address)) (address (+ 8 address))
                             (machine (boymoo-model::a64-store 8 address header machine)))
                  (:instance proof-number-memory-change-composes
                             (start address) (end (+ 24 address)) (first machine)
                             (middle (boymoo-model::a64-store 8 address header machine))
                             (last (proof-number-box-field-stores address header left right machine))))
            :in-theory (enable proof-number-box-field-stores)
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-publication-memory-footprint
  (let* ((machine (proof-world-machine world))
         (address (proof-world-reg 2 world))
         (after (proof-number-box-publish-after world)))
    (implies (and (not (eq (car machine) :svc))
                  (<= (proof-heap-base world) address)
                  (proof-span-p address 24))
             (proof-number-memory-change-p address (+ 24 address) machine (proof-world-machine after))))
  :hints (("Goal"
           :use (proof-number-box-publish-writes-only-three-fields
                 (:instance box-stores-have-24-byte-footprint
                            (address (proof-world-reg 2 world))
                            (machine (proof-world-machine world))
                            (header (proof-load-word (boymoo-model::a64-sp (proof-world-machine world))
                                                     (proof-world-machine world)))
                            (left (proof-world-reg 0 world)) (right (proof-world-reg 1 world)))
                 (:instance proof-number-memory-change-with-same-final-memory
                            (start (proof-world-reg 2 world)) (end (+ 24 (proof-world-reg 2 world)))
                            (first (proof-world-machine world))
                            (last (proof-world-machine (proof-number-box-publish-after world)))
                            (other (proof-number-box-field-stores
                                    (proof-world-reg 2 world)
                                    (proof-load-word (boymoo-model::a64-sp (proof-world-machine world))
                                                     (proof-world-machine world))
                                    (proof-world-reg 0 world) (proof-world-reg 1 world)
                                    (proof-world-machine world)))))
           :in-theory (enable proof-number-box-publish-after)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-box-publication-register-effects
  (let* ((machine (proof-world-machine world))
         (address (proof-world-reg 2 world))
         (after (proof-number-box-publish-after world)))
    (implies (and (not (eq (car machine) :svc))
                  (<= (proof-heap-base world) address))
             (and (equal (cdr world) (cdr after))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (implies (not (member-equal register '(0 3 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register world))))))
  :hints (("Goal" :in-theory (e/d (proof-number-box-publish-after proof-number-execute-block
                                  proof-heap-base proof-world-reg)
                                 (proof-reg))
                  :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-same-world-tail-keeps-streams-and-mappings
  (implies (equal (cdr before) (cdr after))
           (and (proof-streams-preserved-p before after)
                (equal (proof-world-regions before) (proof-world-regions after))
                (equal (proof-world-page-size before) (proof-world-page-size after))
                (equal (proof-world-replies before) (proof-world-replies after))))
  :hints (("Goal" :in-theory (enable (:definition nth))
                  :cases ((consp before) (consp after))))
  :rule-classes nil)

(local
 (defthm publication-keeps-heap-registers
   (let* ((address (proof-world-reg 2 world))
          (machine (proof-world-machine world))
          (after (proof-number-box-publish-after world)))
     (implies (and (not (eq (car machine) :svc)) (<= (proof-heap-base world) address))
              (and (equal (proof-heap-base after) (proof-heap-base world))
                   (equal (proof-machine-limit after) (proof-machine-limit world))
                   (equal (proof-stack-limit after) (proof-stack-limit world))
                   (equal (proof-heap-limit after) (proof-heap-limit world))
                   (equal (proof-box-top after) (proof-box-top world))
                   (equal (proof-stack-top after) (proof-stack-top world))
                   (proof-streams-preserved-p world after)
                   (equal (proof-world-page-size after) (proof-world-page-size world))
                   (equal (proof-world-regions after) (proof-world-regions world))
                   (equal (proof-world-stop after) (proof-world-stop world)))))
   :hints (("Goal"
            :use ((:instance proof-number-box-publication-register-effects (register 23))
                  (:instance proof-number-box-publication-register-effects (register 24))
                  (:instance proof-number-box-publication-register-effects (register 25))
                  (:instance proof-number-box-publication-register-effects (register 26))
                  (:instance proof-number-box-publication-register-effects (register 27))
                  (:instance proof-number-box-publication-register-effects (register 28))
                  (:instance proof-number-same-world-tail-keeps-streams-and-mappings
                             (before world) (after (proof-number-box-publish-after world))))
            :in-theory (enable proof-heap-base proof-machine-limit proof-stack-top)
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-box-publication-keeps-heap-coordinates
  (let* ((machine (proof-world-machine world))
         (address (proof-world-reg 2 world))
         (after (proof-number-box-publish-after world)))
    (implies (and (not (eq (car machine) :svc))
                  (proof-heap-layout-p world)
                  (proof-reserved-span-p :header address 24 world objects))
             (and (equal (proof-number-heap-coordinates world) (proof-number-heap-coordinates after))
                  (equal (proof-stack-top after) (proof-stack-top world))
                  (equal (proof-world-stop after) (proof-world-stop world))
                  (proof-streams-preserved-p world after))))
  :hints (("Goal"
           :use (publication-keeps-heap-registers proof-number-publication-memory-footprint
                 (:instance proof-number-reserved-header-is-local-write (address (proof-world-reg 2 world)))
                 (:instance proof-number-footprint-keeps-disjoint-span
                            (start (proof-world-reg 2 world)) (end (+ 24 (proof-world-reg 2 world)))
                            (lower (- (proof-heap-base world) 128)) (upper (+ (proof-heap-base world) 32))
                            (first (proof-world-machine world))
                            (last (proof-world-machine (proof-number-box-publish-after world))))
                 (:instance proof-number-metadata-span-keeps-heap-coordinates
                            (before world) (after (proof-number-box-publish-after world))))
           :in-theory (disable proof-streams-preserved-p proof-world-page-size proof-world-regions
                               proof-machine-limit proof-stack-limit proof-heap-limit proof-box-top)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm heap-provides-layout-and-object-map
   (implies (proof-heap-p world objects packages)
            (and (proof-heap-layout-p world)
                 (proof-object-map-p objects objects nil (proof-heap-base world) packages
                                     (proof-world-machine world))))
   :hints (("Goal" :in-theory (e/d (proof-heap-p)
                                   (proof-static-p proof-external-objects proof-external-head
                                    proof-dynamic-entries proof-dynamic-view proof-heap-object-spans-p
                                    proof-dynamic-symbol-objects-p proof-string-accounting-p
                                    proof-stack-prefix))))))

(defthm proof-number-box-publication-keeps-old-object-memory
  (let* ((machine (proof-world-machine world))
         (address (proof-world-reg 2 world))
         (new-objects (proof-number-box-object-map world objects))
         (after (proof-number-box-publish-after world)))
    (implies (and (not (eq (car machine) :svc))
                  (proof-heap-p world objects packages)
                  (proof-reserved-span-p :header address 24 world objects))
             (proof-number-objects-memory-p objects new-objects machine (proof-world-machine after))))
  :hints (("Goal"
           :use (heap-provides-layout-and-object-map proof-number-publication-memory-footprint
                 (:instance proof-number-reserved-header-is-local-write (address (proof-world-reg 2 world)))
                 (:instance proof-number-disjoint-objects-omit-address
                            (address (proof-world-reg 2 world)) (end (+ 24 (proof-world-reg 2 world)))
                            (machine (proof-world-machine world)))
                 (:instance proof-number-disjoint-footprint-keeps-old-values
                            (before world) (after (proof-number-box-publish-after world))
                            (old-objects objects) (start (proof-world-reg 2 world))
                            (end (+ 24 (proof-world-reg 2 world))) (word nil) (value nil)
                            (extra (proof-object (proof-world-reg 2 world) :active :header
                                                 (proof-number-next-object-rank objects)))))
           :in-theory (enable proof-number-box-object-map)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm preserved-layout-for-publication
   (let* ((machine (proof-world-machine world))
          (sp (boymoo-model::a64-sp machine))
          (after (proof-number-box-publish-after world)))
     (implies (and (proof-heap-layout-p world)
                   (equal (proof-number-heap-coordinates world) (proof-number-heap-coordinates after))
                   (equal (proof-stack-top after) (proof-stack-top world))
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ 16 sp))
                   (<= (+ 16 sp) (proof-number-machine-stack-end world)))
              (proof-heap-layout-p after)))
   :hints (("Goal"
            :use ((:instance proof-number-coordinate-equality-keeps-layout
                             (before world) (after (proof-number-box-publish-after world)))
                  (:instance proof-number-mod-shift-by-multiple
                             (a (boymoo-model::a64-sp (proof-world-machine world))) (b 16) (times 1)))
            :expand ((proof-heap-layout-p world))
            :in-theory (e/d (proof-number-machine-stack-end)
                            (proof-runtime-word proof-align-up proof-page-size-p proof-regions-p
                             proof-covered-p proof-disjoint-p proof-stack-limit
                             proof-active-floor proof-active-end proof-cons-floor
                             proof-inactive-floor proof-inactive-end proof-box-top proof-heap-limit))
            :do-not-induct t))
   :rule-classes nil))

(defund proof-number-publication-pre-p (kind a b world objects packages)
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (link (proof-load-word (+ 8 sp) machine)))
    (and (if (equal kind 4)
             (and (proof-number-reduced-p a b) (< 1 b))
           (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0))))
         (proof-heap-p world objects packages)
         (proof-reserved-span-p :header (proof-world-reg 2 world) 24 world objects)
         (not (eq (car machine) :svc))
         (unsigned-byte-p 64 (+ 16 sp))
         (equal (proof-load-word sp machine) (+ 4096 kind))
         (proof-reg-value-p 0 a world objects packages)
         (proof-reg-value-p 1 b world objects packages)
         (proof-number-checked-block-p *proof-number-box-publish-instructions* (list link) world))))

(local
 (defthm fresh-box-size-and-header
   (let* ((first (proof-world-machine world))
          (base (proof-heap-base world))
          (address (proof-world-reg 2 world))
          (after (proof-number-box-publish-after world))
          (last (proof-world-machine after))
          (rank (proof-number-next-object-rank objects))
          (record (proof-object address :active :header rank))
          (result (if (equal kind 4) (/ a b) (complex a b))))
     (implies (proof-number-publication-pre-p kind a b world objects packages)
              (and (proof-object-view record base (cons record objects) packages last)
                   (proof-span-p address 24)
                   (equal (mod address 8) 0)
                   (member-equal (proof-load-word address last) '(4100 4101))
                   (equal (boymoo-model::a64-sp last) (+ 16 (boymoo-model::a64-sp first)))
                   (proof-reg-value-p 0 result after (cons record objects) packages))))
   :hints (("Goal"
            :use (heap-provides-layout-and-object-map
                  (:instance proof-number-reserved-header-is-local-write (address (proof-world-reg 2 world)))
                  (:instance proof-number-reserved-box-alignment (address (proof-world-reg 2 world)))
                  (:instance proof-number-box-word-address
                             (address (proof-world-reg 2 world)) (base (proof-heap-base world)))
                  (:instance proof-number-box-publishes-reserved-value (old-objects objects))
                  proof-number-box-publishes-fields)
            :in-theory (e/d (proof-number-publication-pre-p proof-number-box-publish-after
                             proof-object-view proof-object-word proof-reg-value-p proof-machine-value-p proof-value-p)
                            (proof-view proof-number-reduced-p))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm next-rank-is-natural
   (natp (proof-number-next-object-rank objects))
   :hints (("Goal" :induct (proof-number-next-object-rank objects)
                   :in-theory (enable proof-number-next-object-rank)))
   :rule-classes :type-prescription))

(local
 (defthm active-floor-is-nonnegative
   (<= 0 (proof-active-floor world))
   :hints (("Goal"
            :in-theory (enable proof-active-floor proof-runtime-word)))
   :rule-classes :linear))

(local
 (defthm numeric-record-in-active-box-span
   (let* ((machine (proof-world-machine world))
          (record (proof-object address :active :header rank)))
     (implies (and (proof-span-p address 24)
                   (member-equal (proof-load-word address machine) '(4100 4101))
                   (<= (proof-active-floor world) address)
                   (equal (+ 24 address) (proof-box-top world)))
              (proof-number-extra-active-record-p record world)))
   :hints (("Goal"
            :in-theory (e/d (proof-number-extra-active-record-p proof-heap-object-spans-p
                             proof-symbol-object-p proof-object-size)
                            (proof-active-floor proof-box-top proof-runtime-word proof-align-up))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm coordinate-equality-keeps-active-range
   (implies (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
            (and (equal (proof-active-floor before) (proof-active-floor after))
                 (equal (proof-box-top before) (proof-box-top after))))
   :hints (("Goal" :use proof-number-equal-heap-coordinates-preserve-fields))
   :rule-classes nil))

(local
 (defthm reserved-box-range
   (implies (proof-reserved-span-p :header address 24 world objects)
            (and (<= (proof-active-floor world) address)
                 (equal (+ 24 address) (proof-box-top world))))
   :hints (("Goal"
            :in-theory (e/d (proof-reserved-span-p)
                            (proof-active-floor proof-box-top proof-runtime-word
                             proof-object-disjoint-p proof-span-p proof-covered-p))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm published-record-is-in-active-region
   (let ((after (proof-number-box-publish-after world))
         (address (proof-world-reg 2 world))
         (rank (proof-number-next-object-rank objects)))
     (implies (proof-number-publication-pre-p kind a b world objects packages)
              (proof-number-extra-active-record-p (proof-object address :active :header rank) after)))
   :hints (("Goal"
            :use (fresh-box-size-and-header proof-number-box-publication-keeps-heap-coordinates
                  (:instance reserved-box-range (address (proof-world-reg 2 world)))
                  (:instance coordinate-equality-keeps-active-range
                             (before world) (after (proof-number-box-publish-after world)))
                  (:instance numeric-record-in-active-box-span
                             (address (proof-world-reg 2 world))
                             (rank (proof-number-next-object-rank objects))
                             (world (proof-number-box-publish-after world))))
            :in-theory (e/d (proof-number-publication-pre-p)
                            (proof-number-reduced-p proof-active-floor proof-box-top
                             proof-runtime-word proof-object-disjoint-p proof-number-extra-active-record-p
                             proof-reserved-span-p proof-object-view proof-object-map-p proof-span-p
                             proof-reg-value-p proof-machine-value-p proof-value-p proof-view
                             proof-streams-preserved-p proof-heap-base proof-stack-top
                             proof-heap-limit proof-stack-limit proof-number-next-object-rank))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-box-publication-validates-object-map
  (let* ((base (proof-heap-base world))
         (after (proof-number-box-publish-after world))
         (last (proof-world-machine after))
         (new-objects (proof-number-box-object-map world objects)))
    (implies (proof-number-publication-pre-p kind a b world objects packages)
             (and (proof-object-map-p new-objects new-objects nil base packages last)
                  (proof-number-extra-active-record-p (car new-objects) after))))
  :hints (("Goal"
           :use (heap-provides-layout-and-object-map
                 fresh-box-size-and-header
                 proof-number-box-publication-keeps-old-object-memory
                 published-record-is-in-active-region
                 (:instance proof-number-reserved-header-is-local-write (address (proof-world-reg 2 world)))
                 (:instance proof-number-published-record-extends-map
                            (address (proof-world-reg 2 world))
                            (rank (proof-number-next-object-rank objects))
                            (base (proof-heap-base world)) (old-objects objects)
                            (first (proof-world-machine world))
                            (last (proof-world-machine (proof-number-box-publish-after world)))))
           :in-theory (e/d (proof-number-publication-pre-p proof-number-box-object-map
                            proof-object-address)
                           (proof-number-reduced-p proof-symbol-object-p
                            proof-view proof-object-view proof-object-size proof-heap-p
                            proof-heap-layout-p proof-object-map-p proof-number-extra-active-record-p
                            proof-reg-value-p proof-span-p proof-reserved-span-p proof-object-disjoint-p
                            proof-streams-preserved-p proof-stack-top proof-heap-limit))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-box-publication-preserves-heap
  (let* ((sp (boymoo-model::a64-sp (proof-world-machine world)))
         (after (proof-number-box-publish-after world))
         (new-objects (proof-number-box-object-map world objects)))
    (implies (and (proof-number-publication-pre-p kind a b world objects packages)
                  (<= (+ 16 sp) (proof-number-machine-stack-end world)))
             (proof-preserved-heap-p nil world after objects new-objects packages)))
  :hints (("Goal"
           :use (heap-provides-layout-and-object-map
                 fresh-box-size-and-header
                 proof-number-publication-memory-footprint
                 proof-number-box-publication-keeps-heap-coordinates
                 proof-number-box-publication-keeps-old-object-memory
                 proof-number-box-publication-validates-object-map
                 preserved-layout-for-publication
                 (:instance proof-number-reserved-header-is-local-write (address (proof-world-reg 2 world)))
                 (:instance proof-number-same-top-local-write-preserves-heap
                            (start (proof-world-reg 2 world)) (end (+ 24 (proof-world-reg 2 world)))
                            (before world) (after (proof-number-box-publish-after world))
                            (old-objects objects)
                            (extra (car (proof-number-box-object-map world objects)))))
           :in-theory (e/d (proof-number-publication-pre-p proof-number-box-object-map)
                           (proof-number-reduced-p proof-preserved-heap-p proof-heap-frame-p
                            proof-prefix-preserved-p proof-reg-value-p proof-span-p proof-object-view
                            proof-object-disjoint-p proof-number-extra-active-record-p proof-object-map-p
                            proof-number-local-write-p proof-reserved-span-p proof-static-size
                            proof-streams-preserved-p proof-stack-top proof-heap-limit))
           :do-not-induct t))
  :rule-classes nil)
