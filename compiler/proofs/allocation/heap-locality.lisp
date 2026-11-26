(in-package "BOYMOO-PROOFS")

(include-book "locality")
(include-book "heap-frames")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-static-spans-outside-prefix-write
  (implies (and (proof-static-spans-p pending base size machine)
                (proof-span-p start bytes) (<= (+ start bytes) base))
           (allocation-objects-outside-write-p start (+ start bytes) pending machine))
  :rule-classes nil
  :hints (("Goal" :induct (proof-static-spans-p pending base size machine)
           :in-theory (disable proof-object-size))))

(defthm allocation-static-spans-after-prefix-write
  (implies (and (proof-static-spans-p pending base size machine)
                (proof-span-p start bytes) (<= (+ start bytes) base))
           (proof-static-spans-p pending base size (boymoo-model::a64-store bytes start value machine)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-static-spans-p pending base size machine)
           :in-theory (disable proof-object-size boymoo-model::a64-store))
          ("Subgoal *1/2" :use ((:instance allocation-object-size-after-disjoint-write (object (car pending)))))))

(defthm allocation-home-bindings-after-prefix-write
  (implies (and (proof-static-spans-p pending base size machine)
                (proof-span-p start bytes) (<= (+ start bytes) base)
                (<= (+ base size 24) *allocation-word-modulus*)
                (allocation-objects-outside-write-p start (+ start bytes) objects machine))
           (equal (proof-home-bindings-p pending base objects packages
                                         (boymoo-model::a64-store bytes start value machine) buckets)
                  (proof-home-bindings-p pending base objects packages machine buckets)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-static-spans-p pending base size machine)
           :expand ((:free (mem) (proof-home-bindings-p pending base objects packages mem buckets)))
           :in-theory (disable (:definition proof-home-bindings-p) proof-object-size
                               proof-symbol-object-p proof-object-word proof-view proof-static-binding
                               allocation-objects-outside-write-p boymoo-model::a64-store))
          ("Subgoal *1/2"
           :use ((:instance allocation-object-size-after-disjoint-write (object (car pending)))
                 (:instance allocation-load-word-after-disjoint-write
                  (address (+ 16 (proof-object-address (car pending)))))))))

(defthm allocation-static-after-prefix-write
  (let ((size (proof-static-size base machine)))
    (implies (and (proof-static-p base objects packages machine)
                  (proof-span-p start bytes) (<= (+ start bytes) base)
                  (<= (+ base size 24) *allocation-word-modulus*))
             (proof-static-p base objects packages (boymoo-model::a64-store bytes start value machine))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-static-spans-outside-prefix-write
                  (pending (proof-static-objects objects)) (size (proof-static-size base machine)))
                 (:instance allocation-static-spans-after-prefix-write
                  (pending (proof-static-objects objects)) (size (proof-static-size base machine)))
                 (:instance allocation-object-map-after-disjoint-write
                  (pending (proof-static-objects objects)) (objects (proof-static-objects objects)) (symbols nil))
                 (:instance allocation-home-bindings-after-prefix-write
                  (pending (proof-static-objects objects)) (objects (proof-static-objects objects))
                  (size (proof-static-size base machine))
                  (buckets (cdr (proof-view (proof-load-word (+ base 16) machine)
                                            base (proof-static-objects objects) packages machine))))
                 (:instance allocation-load-word-after-disjoint-write (address base))
                 (:instance allocation-load-word-after-disjoint-write (address (+ 8 base)))
                 (:instance allocation-load-word-after-disjoint-write (address (+ 16 base))))
           :in-theory (disable proof-static-objects proof-static-spans-p proof-object-map-p
                               proof-home-bindings-p proof-view proof-packages-p proof-load-word
                               proof-static-buckets-p proof-package-bindings-p
                               allocation-objects-outside-write-p boymoo-model::a64-store mod))))

(defthm allocation-dynamic-symbols-after-disjoint-write
  (implies (and (proof-span-p start bytes)
                (allocation-objects-outside-write-p start (+ start bytes) pending machine)
                (allocation-objects-outside-write-p start (+ start bytes) objects machine))
           (equal (proof-dynamic-symbol-objects-p pending objects entries base packages
                                                  (boymoo-model::a64-store bytes start value machine))
                  (proof-dynamic-symbol-objects-p pending objects entries base packages machine)))
  :hints (("Goal" :induct (allocation-objects-outside-write-p start (+ start bytes) pending machine)
           :in-theory (disable proof-symbol-object-p proof-object-word proof-view proof-object-size
                               proof-span-p proof-disjoint-p boymoo-model::a64-store))
          ("Subgoal *1/2" :use ((:instance allocation-object-size-after-disjoint-write (object (car pending)))))))

(defthm allocation-covered-span-is-valid
  (implies (proof-covered-p address bytes access regions)
           (proof-span-p address bytes))
  :rule-classes nil
  :hints (("Goal" :induct (proof-covered-p address bytes access regions)
           :in-theory (disable proof-span-p))))

(defthm allocation-layout-storage-spans
  (let* ((base (proof-heap-base world))
         (size (proof-static-size base (proof-world-machine world)))
         (heap-start (- base *proof-heap-prefix*))
         (heap-end (proof-spaces-end world))
         (stack-start (proof-stack-base world))
         (stack-end (proof-stack-end world))
         (machine-start (- (proof-machine-limit world) *proof-machine-margin*))
         (machine-end (+ machine-start *proof-machine-reservation*)))
    (implies (proof-heap-layout-p world)
             (and (proof-regions-p (proof-world-regions world))
                  (proof-subspan-p heap-start (- heap-end heap-start) heap-start heap-end)
                  (proof-subspan-p stack-start *proof-value-reservation* stack-start stack-end)
                  (proof-subspan-p machine-start *proof-machine-reservation* machine-start machine-end)
                  (<= (proof-stack-top world) stack-end)
                  (<= machine-start (allocation-sp world))
                  (<= base heap-end)
                  (<= 80 size)
                  (<= (+ base size 24) heap-end)
                  (proof-disjoint-p heap-start heap-end stack-start stack-end)
                  (proof-disjoint-p heap-start heap-end machine-start machine-end))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-align-up-bounds
                  (size (+ (proof-heap-base world) (proof-static-size (proof-heap-base world) (proof-world-machine world))))
                  (alignment *proof-runtime-page*))
                 (:instance allocation-covered-span-is-valid
                  (address (- (proof-heap-base world) *proof-heap-prefix*))
                  (bytes (+ *proof-heap-prefix* (- (proof-spaces-end world) (proof-heap-base world))))
                  (access :write) (regions (proof-world-regions world)))
                 (:instance allocation-covered-span-is-valid
                  (address (proof-stack-base world)) (bytes *proof-value-reservation*)
                  (access :write) (regions (proof-world-regions world)))
                 (:instance allocation-covered-span-is-valid
                  (address (- (proof-machine-limit world) *proof-machine-margin*)) (bytes *proof-machine-reservation*)
                  (access :write) (regions (proof-world-regions world))))
           :in-theory (disable proof-covered-p proof-regions-p proof-align-up proof-machine-limit
                               proof-runtime-word proof-heap-base mod))))

(defthm allocation-heap-write-avoids-stack-slots
  (let* ((base (proof-heap-base world))
         (lower (proof-stack-base world))
         (count (ash (- top lower) -3)))
    (implies (and (proof-heap-layout-p world)
                  (proof-subspan-p start bytes (- base *proof-heap-prefix*) (proof-spaces-end world))
                  (natp top) (<= lower top) (<= top (proof-stack-top world)))
             (allocation-view-slots-outside-write-p :slots lower count start bytes)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-layout-storage-spans
                 (:instance allocation-slot-bytes-fit (size (- top (proof-stack-base world)))))
           :in-theory (disable proof-heap-layout-p proof-runtime-word proof-heap-base proof-machine-limit mod ash))))

(defthm allocation-stack-prefix-after-heap-write
  (let* ((base (proof-heap-base before))
         (lower (proof-stack-base before))
         (machine (proof-world-machine before)))
    (implies (and (proof-heap-layout-p before)
                  (proof-subspan-p start bytes (- base *proof-heap-prefix*) (proof-spaces-end before))
                  (allocation-objects-outside-write-p start (+ start bytes) objects machine)
                  (allocation-same-memory-p (proof-world-machine after) (boymoo-model::a64-store bytes start value machine))
                  (equal (proof-heap-base after) base)
                  (equal (proof-stack-base after) lower)
                  (equal (proof-stack-top after) (proof-stack-top before)))
             (equal (proof-stack-prefix top after objects packages)
                    (proof-stack-prefix top before objects packages))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-heap-write-avoids-stack-slots (world before))
                 (:instance allocation-stack-views-after-disjoint-write
                  (address (proof-stack-base before)) (base (proof-heap-base before))
                  (count (ash (- top (proof-stack-base before)) -3)) (machine (proof-world-machine before))))
           :in-theory (disable proof-heap-layout-p allocation-view-slots-outside-write-p proof-stack-views
                               proof-heap-base proof-stack-top proof-runtime-word proof-world-machine
                               proof-disjoint-p allocation-objects-outside-write-p boymoo-model::a64-store mod ash))))
