(in-package "BOYMOO-PROOFS")

(include-book "cell-contract")
(include-book "static-locality")
(include-book "word-writes")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable allocation-runtime-word-as-load proof-runtime-word)))

(defthm allocation-runtime-metadata-word-natural
  (natp (proof-runtime-word offset world))
  :rule-classes :type-prescription
  :hints (("Goal" :use allocation-runtime-word-as-load)))

(local
 (defthm allocation-active-subspan-is-span
   (implies (proof-subspan-p address bytes lower upper)
            (proof-span-p address bytes))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (disable proof-span-p)))))

(local
 (defthm allocation-heap-base-after-word-store
   (equal (proof-heap-base (allocation-store-word address value world))
          (proof-heap-base world))))

(defthm allocation-store-machine-keeps-sp
  (equal (boymoo-model::a64-sp (boymoo-model::a64-store bytes address value machine))
         (boymoo-model::a64-sp machine))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-write-bytes boymoo-model::a64-unsigned))))

(defthm allocation-active-word-store-bounds
  (let* ((base (proof-heap-base world))
         (size (proof-static-size base (proof-world-machine world))))
    (implies (and (proof-heap-layout-p world)
                  (proof-subspan-p address 8 (proof-active-floor world) (proof-active-end world)))
             (and (posp address)
                  (proof-subspan-p address 8 (- base *proof-heap-prefix*) (proof-spaces-end world))
                  (<= (+ base size) address)
                  (<= 80 size)
                  (proof-span-p base 32))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-static-end-below-box-top allocation-layout-storage-spans)
           :in-theory (disable proof-covered-p proof-regions-p proof-disjoint-p
                               proof-align-up proof-static-size proof-heap-base mod))))

(defthm allocation-active-word-store-keeps-metadata
  (implies (and (proof-heap-layout-p world)
                (proof-subspan-p address 8 (proof-active-floor world) (proof-active-end world))
                (natp offset) (<= offset 80))
           (equal (proof-runtime-word offset (allocation-store-word address value world))
                  (proof-runtime-word offset world)))
  :hints (("Goal"
           :use (allocation-active-word-store-bounds
                 (:instance allocation-runtime-word-as-load)
                 (:instance allocation-runtime-word-as-load (world (allocation-store-word address value world)))
                 (:instance allocation-word-after-disjoint-store
                  (word value) (probe (+ -128 offset (proof-heap-base world)))))
           :in-theory (disable proof-heap-layout-p proof-heap-base proof-static-size proof-active-floor
                               proof-active-end boymoo-model::a64-store allocation-word-after-disjoint-store))))

(defthm allocation-active-word-store-keeps-static-words
  (let ((base (proof-heap-base world))
        (changed (allocation-store-word address value world)))
    (implies (and (proof-heap-layout-p world)
                  (proof-subspan-p address 8 (proof-active-floor world) (proof-active-end world)))
             (and (equal (proof-static-size base (proof-world-machine changed))
                         (proof-static-size base (proof-world-machine world)))
                  (equal (proof-dynamic-root base (proof-world-machine changed))
                         (proof-dynamic-root base (proof-world-machine world))))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-active-word-store-bounds
                 (:instance allocation-load-word-after-disjoint-write
                  (address (proof-heap-base world)) (start address) (bytes 8) (machine (proof-world-machine world)))
                 (:instance allocation-load-word-after-disjoint-write
                  (address (+ 24 (proof-heap-base world))) (start address) (bytes 8) (machine (proof-world-machine world))))
           :in-theory (disable proof-heap-layout-p proof-heap-base proof-load-word proof-active-floor proof-active-end
                               boymoo-model::a64-store allocation-load-word-after-disjoint-write))))

(defthm allocation-active-word-store-keeps-layout
  (implies (and (proof-heap-layout-p world)
                (proof-subspan-p address 8 (proof-active-floor world) (proof-active-end world)))
           (proof-heap-layout-p (allocation-store-word address value world)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-active-word-store-keeps-static-words
                 (:instance allocation-active-word-store-keeps-metadata (offset 0))
                 (:instance allocation-active-word-store-keeps-metadata (offset 8))
                 (:instance allocation-active-word-store-keeps-metadata (offset 16))
                 (:instance allocation-active-word-store-keeps-metadata (offset 24))
                 (:instance allocation-active-word-store-keeps-metadata (offset 32))
                 (:instance allocation-active-word-store-keeps-metadata (offset 40))
                 (:instance allocation-active-word-store-keeps-metadata (offset 48))
                 (:instance allocation-active-word-store-keeps-metadata (offset 64)))
           :in-theory (disable proof-align-up proof-regions-p proof-disjoint-p proof-covered-p
                               proof-page-size-p proof-subspan-p proof-static-size proof-dynamic-root
                               allocation-active-word-store-keeps-metadata proof-load-word
                               proof-world-machine boymoo-model::a64-store mod))))

(defthm allocation-active-word-store-keeps-external-bounds
  (implies (and (proof-heap-layout-p world)
                (proof-subspan-p address 8 (proof-active-floor world) (proof-active-end world)))
           (allocation-same-external-bounds-p world (allocation-store-word address value world)))
  :hints (("Goal" :in-theory (e/d (allocation-same-external-bounds-p)
                                  (proof-heap-layout-p proof-subspan-p)))))

(defthm allocation-active-word-store-keeps-published-spans
  (let ((changed (allocation-store-word address value world)))
    (implies (and (proof-heap-layout-p world)
                  (proof-subspan-p address 8 (proof-active-floor world) (proof-active-end world))
                  (allocation-objects-outside-write-p address (+ address 8) objects (proof-world-machine world))
                  (proof-heap-object-spans-p objects headers world))
             (proof-heap-object-spans-p objects headers changed)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-object-spans-after-lowering-cell-frontier
                  (before world) (after (allocation-store-word address value world))
                  (start address) (bytes 8) (external headers)))
           :in-theory (disable proof-heap-layout-p proof-subspan-p proof-span-p
                               proof-heap-object-spans-p allocation-objects-outside-write-p boymoo-model::a64-store))))

(defthm allocation-active-word-store-keeps-external-objects
  (let* ((changed (allocation-store-word address value world))
         (external (proof-external-objects head fuel world objects)))
    (implies (and (proof-heap-layout-p world)
                  (proof-subspan-p address 8 (proof-active-floor world) (proof-active-end world))
                  external)
             (and (equal (proof-external-objects head fuel changed objects) external)
                  (equal (proof-external-bytes (cdr external) (proof-world-machine changed))
                         (proof-external-bytes (cdr external) (proof-world-machine world))))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-active-word-store-bounds allocation-layout-storage-spans
                 (:instance allocation-external-objects-after-heap-write
                  (before world) (after (allocation-store-word address value world)) (start address) (bytes 8)))
           :in-theory (disable proof-heap-layout-p proof-subspan-p proof-span-p proof-external-objects
                               proof-external-bytes proof-regions-p boymoo-model::a64-store))))

(defthm allocation-active-word-store-keeps-stack-prefix
  (implies (and (proof-heap-layout-p world)
                (proof-subspan-p address 8 (proof-active-floor world) (proof-active-end world))
                (allocation-objects-outside-write-p address (+ address 8) objects (proof-world-machine world)))
           (equal (proof-stack-prefix top (allocation-store-word address value world) objects packages)
                  (proof-stack-prefix top world objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-active-word-store-bounds
                 (:instance allocation-stack-prefix-after-heap-write
                  (before world) (after (allocation-store-word address value world)) (start address) (bytes 8)))
           :in-theory (disable proof-heap-layout-p proof-stack-prefix proof-subspan-p proof-span-p
                               allocation-objects-outside-write-p boymoo-model::a64-store))))

(defthm allocation-active-word-store-keeps-dynamic
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (changed (allocation-store-word address value world))
         (dynamic (proof-dynamic-entries (proof-dynamic-view world objects packages) packages))
         (entries (cdr dynamic)))
    (implies (and (proof-heap-layout-p world)
                  (proof-subspan-p address 8 (proof-active-floor world) (proof-active-end world))
                  (allocation-objects-outside-write-p address (+ address 8) objects machine))
             (and (equal (proof-dynamic-view changed objects packages) (proof-dynamic-view world objects packages))
                  (equal (proof-dynamic-symbol-objects-p objects objects entries base packages (proof-world-machine changed))
                         (proof-dynamic-symbol-objects-p objects objects entries base packages machine)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-active-word-store-keeps-static-words
                 (:instance allocation-view-after-disjoint-write
                  (start address) (bytes 8) (machine (proof-world-machine world)) (base (proof-heap-base world))
                  (word (proof-dynamic-root (proof-heap-base world) (proof-world-machine world))))
                 (:instance allocation-dynamic-symbols-after-disjoint-write
                  (start address) (bytes 8) (machine (proof-world-machine world)) (base (proof-heap-base world))
                  (pending objects) (entries (cdr (proof-dynamic-entries (proof-dynamic-view world objects packages) packages)))))
           :in-theory (disable proof-heap-layout-p proof-dynamic-entries proof-dynamic-symbol-objects-p
                               proof-span-p proof-view proof-dynamic-root proof-load-word
                               allocation-objects-outside-write-p boymoo-model::a64-store))))

(defthm allocation-heap-after-unpublished-active-word-store
  (implies (and (proof-heap-p world objects packages)
                (proof-subspan-p address 8 (proof-active-floor world) (proof-active-end world))
                (allocation-objects-outside-write-p address (+ address 8) objects (proof-world-machine world)))
           (proof-heap-p (allocation-store-word address value world) objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-active-word-store-bounds allocation-active-word-store-keeps-layout
                 allocation-active-word-store-keeps-dynamic
                 (:instance allocation-static-after-disjoint-range-write
                  (base (proof-heap-base world)) (machine (proof-world-machine world)) (start address) (bytes 8))
                 (:instance allocation-object-map-after-disjoint-write
                  (start address) (bytes 8) (machine (proof-world-machine world)) (base (proof-heap-base world))
                  (pending objects) (symbols nil))
                 (:instance allocation-active-word-store-keeps-external-objects
                  (head (proof-external-head world)) (fuel (len objects)))
                 (:instance allocation-active-word-store-keeps-published-spans
                  (headers (cdr (proof-external-objects (proof-external-head world) (len objects) world objects))))
                 (:instance allocation-active-word-store-keeps-stack-prefix (top (proof-stack-top world))))
           :in-theory (disable proof-heap-layout-p proof-static-p proof-object-map-p proof-external-objects
                               proof-heap-object-spans-p proof-external-bytes proof-stack-prefix proof-dynamic-entries
                               proof-dynamic-view proof-dynamic-symbol-objects-p proof-static-size proof-load-word
                               proof-align-up proof-span-p proof-subspan-p
                               allocation-objects-outside-write-p boymoo-model::a64-store mod))))
