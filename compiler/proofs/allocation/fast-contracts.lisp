(in-package "BOYMOO-PROOFS")

(include-book "reservations")
(include-book "locality")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable allocation-runtime-word-as-load)))

(defthm allocation-fast-header-frame
  (implies (allocation-fast-machine-return-p :header bytes before after)
           (and (allocation-same-heap-context-p before after)
                (equal (proof-stack-limit after) (proof-stack-limit before))
                (proof-frame-return-p (append *proof-volatile-registers* '(26 27)) t before after)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-context-from-register-frame (clobbers '(0 1 27)))
                 (:instance allocation-register-frame-member (register 24) (upper 30) (clobbers '(0 1 27)))
                 (:instance allocation-register-frame-under-more-clobbers
                            (small '(0 1 27)) (large (append *proof-volatile-registers* '(26 27)))
                            (register 30)))
           :in-theory (disable proof-cons-floor allocation-reservation-address))))

(defthm allocation-fast-header-layout
  (implies (and (proof-heap-layout-p before)
                (proof-allocation-fits-p :header bytes before)
                (allocation-fast-machine-return-p :header bytes before after))
           (proof-heap-layout-p after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-header-frame allocation-growth-layout-facts allocation-extend-layout-tops
                 (:instance allocation-aligned-eight-sum (first (proof-box-top before)) (second bytes)))
           :in-theory (disable proof-heap-layout-p proof-span-p proof-frame-return-p mod
                               proof-stack-base proof-stack-limit proof-stack-end
                               proof-active-floor proof-inactive-floor proof-active-end proof-cons-floor))))

(defthm allocation-fast-header-reserved-span
  (let* ((address (proof-box-top before))
         (end (+ address bytes)))
    (implies (and (proof-heap-layout-p before)
                  (proof-allocation-fits-p :header bytes before)
                  (allocation-fast-machine-return-p :header bytes before after)
                  (proof-object-disjoint-p address end objects (proof-world-machine before)))
             (proof-reserved-span-p :header (proof-world-reg 0 after) bytes after objects)))
  :rule-classes nil
  :hints (("Goal" :use (allocation-fast-header-frame allocation-growth-layout-facts)
           :in-theory (disable proof-heap-layout-p proof-frame-return-p proof-span-p
                               proof-object-disjoint-p proof-stack-base
                               proof-stack-limit proof-stack-end mod))))

(defthm allocation-fast-header-heap-return
  (let* ((address (proof-box-top before))
         (end (+ address bytes)))
    (implies (and (proof-heap-p before objects packages)
                  (proof-allocation-fits-p :header bytes before)
                  (allocation-fast-machine-return-p :header bytes before after)
                  (proof-object-disjoint-p address end objects (proof-world-machine before)))
             (proof-fast-allocation-return-p :header bytes before after objects objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-header-frame allocation-fast-header-layout
                 (:instance allocation-layout-of-heap (world before))
                 allocation-fast-header-reserved-span allocation-heap-with-raised-box-top
                 allocation-preserved-heap-under-same-context)
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-frame-return-p proof-reserved-span-p
                               proof-object-disjoint-p proof-preserved-heap-p proof-span-p
                               proof-static-p proof-dynamic-view proof-external-objects
                               proof-object-map-p proof-heap-object-spans-p proof-string-accounting-p
                               proof-stack-prefix proof-dynamic-symbol-objects-p mod))))

(defthm allocation-fast-cells-unchanged-register
  (implies (and (allocation-fast-machine-return-p :cons bytes before after)
                (natp register) (<= register 30)
                (not (member-equal register '(0 1 2 9 26))))
           (equal (proof-world-reg register after) (proof-world-reg register before)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal"
           :use ((:instance allocation-register-frame-member (upper 30) (clobbers '(0 1 2 9 26))))
           :in-theory (disable allocation-reservation-address proof-cons-floor proof-runtime-word
                               proof-span-p proof-streams-preserved-p))))

(local
 (defthm allocation-fast-runtime-word-from-memory
   (equal (proof-runtime-word offset world)
          (boymoo-model::a64-read-bytes
           8 (+ offset (- (proof-heap-base world) 128)) (allocation-memory world)))
   :hints (("Goal" :in-theory (enable proof-runtime-word proof-load-word)))))

(defthm allocation-fast-cells-keeps-other-metadata
  (implies (and (allocation-fast-machine-return-p :cons bytes before after)
                (<= 128 (proof-heap-base before))
                (member-equal offset '(0 8 24 32 40 48 56 64 72 80)))
           (equal (proof-runtime-word offset after) (proof-runtime-word offset before)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal"
           :use ((:instance allocation-fast-cells-unchanged-register (register 28)))
           :in-theory (disable proof-cons-floor proof-frame-return-p proof-streams-preserved-p
                               allocation-fast-cells-unchanged-register))))

(defthm allocation-fast-cells-reservation-geometry
  (let ((address (allocation-reservation-address :cons bytes before)))
    (implies (and (proof-heap-layout-p before)
                  (proof-allocation-fits-p :cons bytes before)
                  (allocation-fast-machine-return-p :cons bytes before after))
             (and (proof-span-p address bytes)
                  (equal (proof-world-reg 0 after) address)
                  (equal (proof-cons-floor after) address)
                  (<= (+ address bytes) (proof-active-end after))
                  (<= (proof-box-top before) address)
                  (equal (+ address bytes) (proof-cons-floor before)))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-growth-layout-facts
                        (:instance allocation-fast-cells-keeps-other-metadata (offset 8)))
           :in-theory (disable allocation-fast-runtime-word-from-memory proof-runtime-word
                               allocation-fast-cells-keeps-other-metadata proof-heap-layout-p
                               proof-frame-return-p proof-span-p proof-streams-preserved-p mod))))

(defthm allocation-fast-header-contract-from-heap
  (implies (and (proof-heap-p before objects packages)
                (proof-allocation-fits-p :header bytes before)
                (allocation-fast-machine-return-p :header bytes before after))
           (proof-fast-allocation-return-p :header bytes before after objects objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-header-heap-return allocation-growth-layout-facts
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-free-span-disjoint-from-published-objects
                  (start (proof-box-top before)) (end (+ (proof-box-top before) bytes))))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-object-disjoint-p
                               allocation-fast-machine-return-p proof-fast-allocation-return-p
                               proof-cons-floor proof-stack-base proof-stack-limit proof-stack-end mod))))

(defthm allocation-fast-header-checked-contract
  (let* ((path (allocation-fast-path :header))
         (cuts (list (proof-world-reg 30 before))))
    (implies (and (allocation-request-machine-pre-p :header bytes origin before)
                  (proof-heap-p before objects packages)
                  (proof-allocation-fits-p :header bytes before)
                  (allocation-path-ready-p path cuts before)
                  (equal after (allocation-path-end path before)))
             (and (proof-fast-allocation-return-p :header bytes before after objects objects packages)
                  (proof-segment-p (len path) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-fast-header-contract-from-heap
                        (:instance allocation-fast-checked-return (kind :header)))
           :in-theory (disable allocation-fast-machine-return-p allocation-request-machine-pre-p
                               allocation-path-ready-p allocation-path-end proof-heap-p
                               proof-allocation-fits-p proof-fast-allocation-return-p proof-segment-p))))

(defun allocation-cell-frontier-address (world)
  (- (proof-heap-base world) 112))

(defun allocation-fast-cells-store-machine (bytes world)
  (boymoo-model::a64-store 8 (allocation-cell-frontier-address world)
                         (allocation-reservation-address :cons bytes world)
                         (proof-world-machine world)))

(defthm allocation-fast-cells-store-describes-return-memory
  (implies (allocation-fast-machine-return-p :cons bytes before after)
           (allocation-same-memory-p (proof-world-machine after)
                                     (allocation-fast-cells-store-machine bytes before)))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (allocation-same-memory-p)
                                  (proof-frame-return-p proof-span-p proof-cons-floor
                                   boymoo-model::a64-write-bytes proof-streams-preserved-p)))))

(defthm allocation-heap-published-map
  (implies (proof-heap-p world objects packages)
           (proof-object-map-p objects objects nil (proof-heap-base world) packages (proof-world-machine world)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-heap-layout-p proof-static-p proof-dynamic-view
                                     proof-external-objects proof-object-map-p proof-heap-object-spans-p
                                     proof-string-accounting-p proof-stack-prefix proof-dynamic-symbol-objects-p))))

(defthm allocation-cell-frontier-outside-published-objects
  (let ((start (allocation-cell-frontier-address before))
        (machine (proof-world-machine before)))
    (implies (proof-heap-p before objects packages)
             (and (posp start) (proof-span-p start 8)
                  (allocation-objects-outside-write-p start (+ start 8) objects machine))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world before))
                 (:instance allocation-heap-published-map (world before))
                 allocation-growth-layout-facts
                 (:instance allocation-prefix-span-disjoint-from-published-objects
                  (start (allocation-cell-frontier-address before))
                  (end (+ 8 (allocation-cell-frontier-address before))))
                 (:instance allocation-object-map-with-disjoint-spans
                  (pending objects) (symbols nil) (base (proof-heap-base before))
                  (machine (proof-world-machine before))
                  (start (allocation-cell-frontier-address before))
                  (end (+ 8 (allocation-cell-frontier-address before)))))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-object-map-p
                               proof-object-disjoint-p allocation-objects-outside-write-p
                               proof-stack-base proof-stack-limit proof-stack-end mod))))

(defthm allocation-fast-cells-preserves-published-map
  (implies (and (proof-heap-p before objects packages)
                (allocation-fast-machine-return-p :cons bytes before after))
           (proof-object-map-p objects objects nil (proof-heap-base after) packages (proof-world-machine after)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cell-frontier-outside-published-objects
                 allocation-fast-cells-store-describes-return-memory
                 (:instance allocation-fast-cells-unchanged-register (register 28))
                 (:instance allocation-heap-published-map (world before))
                 (:instance allocation-object-map-after-disjoint-write
                  (start (allocation-cell-frontier-address before)) (bytes 8) (pending objects) (symbols nil)
                  (base (proof-heap-base before)) (machine (proof-world-machine before))
                  (value (allocation-reservation-address :cons bytes before))))
           :in-theory (disable proof-heap-p proof-object-map-p allocation-objects-outside-write-p
                               allocation-fast-machine-return-p allocation-fast-cells-unchanged-register
                               allocation-reservation-address proof-span-p boymoo-model::a64-store))))

(defthm allocation-fast-cells-reserved-span
  (implies (and (proof-heap-p before objects packages)
                (proof-allocation-fits-p :cons bytes before)
                (allocation-fast-machine-return-p :cons bytes before after))
           (proof-reserved-span-p :cons (proof-world-reg 0 after) bytes after objects))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-cells-reservation-geometry
                 allocation-cell-frontier-outside-published-objects
                 allocation-fast-cells-store-describes-return-memory
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-free-span-disjoint-from-published-objects
                  (start (allocation-reservation-address :cons bytes before)) (end (proof-cons-floor before)))
                 (:instance allocation-object-disjointness-after-write
                  (address (allocation-reservation-address :cons bytes before)) (end (proof-cons-floor before))
                  (start (allocation-cell-frontier-address before)) (bytes 8)
                  (machine (proof-world-machine before)) (value (allocation-reservation-address :cons bytes before))))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-object-disjoint-p proof-span-p
                               allocation-objects-outside-write-p allocation-fast-machine-return-p
                               allocation-object-disjointness-after-write allocation-reservation-address
                               proof-cons-floor proof-active-end boymoo-model::a64-store mod))))

(defthm allocation-fast-cells-checked-reservation
  (let* ((path (allocation-fast-path :cons))
         (cuts (list (proof-world-reg 30 before))))
    (implies (and (allocation-request-machine-pre-p :cons bytes origin before)
                  (proof-heap-p before objects packages)
                  (proof-allocation-fits-p :cons bytes before)
                  (allocation-path-ready-p path cuts before)
                  (equal after (allocation-path-end path before)))
             (and (proof-reserved-span-p :cons (proof-world-reg 0 after) bytes after objects)
                  (proof-object-map-p objects objects nil (proof-heap-base after) packages (proof-world-machine after))
                  (proof-segment-p (len path) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-fast-cells-preserves-published-map allocation-fast-cells-reserved-span
                        (:instance allocation-fast-checked-return (kind :cons)))
           :in-theory (disable allocation-fast-machine-return-p allocation-request-machine-pre-p
                               allocation-path-ready-p allocation-path-end proof-heap-p
                               proof-allocation-fits-p proof-object-map-p proof-reserved-span-p proof-segment-p))))
