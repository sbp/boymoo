(in-package "BOYMOO-PROOFS")

(include-book "fast-contracts")
(include-book "external-list")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable allocation-runtime-word-as-load proof-runtime-word)))

(local
 (defthm allocation-cell-allocator-control-frame
   (implies (allocation-fast-machine-return-p :cons bytes before after)
            (and (equal (proof-world-regions after) (proof-world-regions before))
                 (equal (proof-world-page-size after) (proof-world-page-size before))
                 (not (proof-world-stop after))
                 (equal (allocation-sp after) (allocation-sp before))
                 (equal (proof-box-top after) (proof-box-top before))
                 (equal (proof-heap-limit after) (- (proof-heap-limit before) bytes))
                 (equal (proof-cons-floor after) (- (proof-cons-floor before) bytes))
                 (proof-frame-return-p (append *proof-volatile-registers* '(26 27)) t before after)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-register-frame-under-more-clobbers
                   (small '(0 1 2 9 26)) (large (append *proof-volatile-registers* '(26 27))) (register 30)))
            :in-theory (disable proof-register-frame-p proof-span-p proof-cons-floor
                                boymoo-model::a64-write-bytes)))))

(defthm allocation-fast-cells-stable-fields
  (implies (and (proof-heap-layout-p before)
                (allocation-fast-machine-return-p :cons bytes before after))
           (and (allocation-same-external-bounds-p before after)
                (equal (proof-stack-top after) (proof-stack-top before))
                (equal (proof-stack-limit after) (proof-stack-limit before))
                (equal (proof-active-floor after) (proof-active-floor before))
                (equal (proof-active-end after) (proof-active-end before))
                (equal (proof-inactive-floor after) (proof-inactive-floor before))
                (equal (proof-inactive-end after) (proof-inactive-end before))
                (equal (proof-external-head after) (proof-external-head before))
                (equal (proof-string-bytes-since-collection after) (proof-string-bytes-since-collection before))
                (equal (proof-string-budget after) (proof-string-budget before))
                (proof-frame-return-p (append *proof-volatile-registers* '(26 27)) t before after)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-growth-layout-facts allocation-cell-allocator-control-frame
                 (:instance allocation-fast-cells-unchanged-register (register 23))
                 (:instance allocation-fast-cells-unchanged-register (register 24))
                 (:instance allocation-fast-cells-unchanged-register (register 25))
                 (:instance allocation-fast-cells-unchanged-register (register 28))
                 (:instance allocation-fast-cells-keeps-other-metadata (offset 0))
                 (:instance allocation-fast-cells-keeps-other-metadata (offset 8))
                 (:instance allocation-fast-cells-keeps-other-metadata (offset 24))
                 (:instance allocation-fast-cells-keeps-other-metadata (offset 32))
                 (:instance allocation-fast-cells-keeps-other-metadata (offset 40))
                 (:instance allocation-fast-cells-keeps-other-metadata (offset 48))
                 (:instance allocation-fast-cells-keeps-other-metadata (offset 56))
                 (:instance allocation-fast-cells-keeps-other-metadata (offset 64))
                 (:instance allocation-fast-cells-keeps-other-metadata (offset 72))
                 (:instance allocation-fast-cells-keeps-other-metadata (offset 80)))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (proof-heap-layout-p proof-frame-return-p proof-span-p proof-streams-preserved-p
                            allocation-fast-machine-return-p proof-register-frame-p proof-cons-floor
                            allocation-reservation-address
                            allocation-fast-cells-unchanged-register allocation-fast-cells-keeps-other-metadata
                            boymoo-model::a64-write-bytes mod)))))

(defthm allocation-cell-frontier-within-heap
  (let* ((base (proof-heap-base before))
         (start (allocation-cell-frontier-address before))
         (static-end (+ base (proof-static-size base (proof-world-machine before)))))
    (implies (proof-heap-layout-p before)
             (and (posp start) (proof-span-p start 8) (proof-span-p base 32) (<= (+ start 8) base)
                  (proof-subspan-p start 8 (- base *proof-heap-prefix*) (proof-spaces-end before))
                  (<= (+ static-end 24) *allocation-word-modulus*))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-layout-storage-spans (world before)) allocation-growth-layout-facts)
           :in-theory (disable proof-heap-layout-p proof-runtime-word proof-heap-base proof-static-size))))

(defthm allocation-fast-cells-static-words
  (let ((base (proof-heap-base before)))
    (implies (and (proof-heap-layout-p before)
                  (allocation-fast-machine-return-p :cons bytes before after))
             (and (equal (proof-static-size base (proof-world-machine after))
                         (proof-static-size base (proof-world-machine before)))
                  (equal (proof-dynamic-root base (proof-world-machine after))
                         (proof-dynamic-root base (proof-world-machine before))))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-fast-cells-store-describes-return-memory
                        allocation-cell-frontier-within-heap
                        (:instance allocation-load-word-after-disjoint-write
                         (address (proof-heap-base before)) (start (allocation-cell-frontier-address before))
                         (bytes 8) (value (allocation-reservation-address :cons bytes before))
                         (machine (proof-world-machine before)))
                        (:instance allocation-load-word-after-disjoint-write
                         (address (+ 24 (proof-heap-base before))) (start (allocation-cell-frontier-address before))
                         (bytes 8) (value (allocation-reservation-address :cons bytes before))
                         (machine (proof-world-machine before))))
           :in-theory (disable proof-heap-layout-p allocation-fast-machine-return-p proof-heap-base
                               proof-load-word allocation-reservation-address boymoo-model::a64-store))))

(local
 (encapsulate ()
  (local (include-book "arithmetic-5/top" :dir :system))
  (defthm allocation-aligned-frontier-differences
   (implies (and (integerp bytes) (integerp limit) (integerp floor)
                 (equal (mod bytes 16) 0) (equal (mod floor 16) 0) (equal (mod limit 8) 0))
            (and (equal (mod (- floor bytes) 16) 0)
                 (equal (mod (- limit bytes) 8) 0)))
   :rule-classes nil
   :hints (("Goal" :nonlinearp t :in-theory (disable mod))))))

(defthm allocation-fast-cells-layout
  (implies (and (proof-heap-layout-p before)
                (proof-allocation-fits-p :cons bytes before)
                (allocation-fast-machine-return-p :cons bytes before after))
           (proof-heap-layout-p after))
  :rule-classes nil
  :hints (("Goal" :use (allocation-fast-cells-stable-fields allocation-fast-cells-static-words
                        allocation-cell-allocator-control-frame
                        (:instance allocation-aligned-frontier-differences
                         (limit (proof-heap-limit before)) (floor (proof-cons-floor before))))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (proof-covered-p proof-disjoint-p proof-regions-p proof-align-up
                            allocation-fast-machine-return-p proof-frame-return-p proof-page-size-p
                            proof-heap-base proof-machine-limit proof-stack-top proof-stack-limit
                            proof-active-floor proof-active-end proof-inactive-floor proof-inactive-end
                            proof-stack-base proof-stack-end proof-spaces-end proof-static-size
                            proof-string-bytes-since-collection proof-string-budget proof-external-head
                            proof-cons-floor proof-streams-preserved-p boymoo-model::a64-write-bytes mod)))))

(defthm allocation-object-spans-after-lowering-cell-frontier
  (let ((machine (proof-world-machine before)))
    (implies (and (proof-heap-object-spans-p objects external before)
                  (proof-span-p start bytes)
                  (allocation-objects-outside-write-p start (+ start bytes) objects machine)
                  (allocation-same-memory-p (proof-world-machine after) (boymoo-model::a64-store bytes start value machine))
                  (equal (proof-active-floor after) (proof-active-floor before))
                  (equal (proof-active-end after) (proof-active-end before))
                  (equal (proof-box-top after) (proof-box-top before))
                  (natp (proof-cons-floor after))
                  (<= (proof-cons-floor after) (proof-cons-floor before)))
             (proof-heap-object-spans-p objects external after)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-heap-object-spans-p objects external before)
           :expand ((:free (world) (proof-heap-object-spans-p objects external world)))
           :in-theory (disable (:definition proof-heap-object-spans-p) proof-object-size
                               proof-active-floor proof-active-end proof-cons-floor proof-box-top
                               boymoo-model::a64-store mod))
          ("Subgoal *1/2" :use ((:instance allocation-object-size-after-disjoint-write
                                 (object (car objects)) (machine (proof-world-machine before)))))))

(defthm allocation-fast-cells-keeps-object-spans
  (implies (and (proof-heap-p before objects packages)
                (proof-heap-object-spans-p objects external before)
                (proof-allocation-fits-p :cons bytes before)
                (allocation-fast-machine-return-p :cons bytes before after))
           (proof-heap-object-spans-p objects external after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-cells-store-describes-return-memory
                 (:instance allocation-layout-of-heap (world before))
                 allocation-fast-cells-stable-fields allocation-cell-frontier-outside-published-objects
                 (:instance allocation-object-spans-after-lowering-cell-frontier
                  (start (allocation-cell-frontier-address before))
                  (bytes 8) (value (allocation-reservation-address :cons bytes before))))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-active-floor proof-active-end proof-cons-floor
                               proof-heap-object-spans-p allocation-objects-outside-write-p
                               proof-streams-preserved-p proof-frame-return-p boymoo-model::a64-store
                               boymoo-model::a64-write-bytes mod))))

(defthm allocation-fast-cells-keeps-static
  (implies (and (proof-heap-layout-p before)
                (proof-static-p (proof-heap-base before) objects packages (proof-world-machine before))
                (allocation-fast-machine-return-p :cons bytes before after))
           (proof-static-p (proof-heap-base after) objects packages (proof-world-machine after)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-cells-stable-fields allocation-cell-frontier-within-heap
                 allocation-fast-cells-store-describes-return-memory
                 (:instance allocation-static-after-prefix-write
                  (base (proof-heap-base before)) (machine (proof-world-machine before))
                  (start (allocation-cell-frontier-address before))
                  (bytes 8) (value (allocation-reservation-address :cons bytes before))))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (proof-heap-layout-p allocation-fast-machine-return-p proof-static-p proof-static-size
                            proof-span-p proof-subspan-p proof-heap-base boymoo-model::a64-store)))))

(defthm allocation-fast-cells-keeps-external-list
  (let* ((list (proof-external-objects (proof-external-head before) (len objects) before objects))
         (headers (cdr list)))
    (implies (and (proof-heap-layout-p before)
                  (allocation-fast-machine-return-p :cons bytes before after)
                  (proof-string-accounting-p headers before)
                  list)
             (and (equal (proof-external-objects (proof-external-head after) (len objects) after objects)
                         list)
                  (proof-string-accounting-p headers after))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-cells-stable-fields allocation-cell-frontier-within-heap
                 allocation-fast-cells-store-describes-return-memory
                 (:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-external-objects-after-heap-write
                  (head (proof-external-head before)) (fuel (len objects))
                  (start (allocation-cell-frontier-address before))
                  (bytes 8) (value (allocation-reservation-address :cons bytes before))))
           :in-theory (disable proof-heap-layout-p allocation-fast-machine-return-p proof-external-objects
                               proof-external-bytes proof-string-bytes-since-collection proof-string-budget
                               proof-external-head proof-static-size proof-span-p proof-subspan-p
                               proof-regions-p proof-heap-base boymoo-model::a64-store mod))))

(defthm allocation-fast-cells-keeps-dynamic-view
  (let* ((base (proof-heap-base before))
         (dynamic (proof-dynamic-entries (proof-dynamic-view before objects packages) packages))
         (entries (cdr dynamic)))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-fast-machine-return-p :cons bytes before after))
             (and (equal (proof-dynamic-view after objects packages)
                         (proof-dynamic-view before objects packages))
                  (proof-dynamic-symbol-objects-p objects objects entries base packages (proof-world-machine after)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-cells-stable-fields allocation-fast-cells-static-words
                 allocation-cell-frontier-outside-published-objects allocation-fast-cells-store-describes-return-memory
                 (:instance allocation-view-after-disjoint-write
                  (word (proof-dynamic-root (proof-heap-base before) (proof-world-machine before)))
                  (base (proof-heap-base before)) (machine (proof-world-machine before))
                  (start (allocation-cell-frontier-address before))
                  (bytes 8) (value (allocation-reservation-address :cons bytes before)))
                 (:instance allocation-dynamic-symbols-after-disjoint-write
                  (pending objects) (base (proof-heap-base before)) (machine (proof-world-machine before))
                  (entries (cdr (proof-dynamic-entries (proof-dynamic-view before objects packages) packages)))
                  (start (allocation-cell-frontier-address before))
                  (bytes 8) (value (allocation-reservation-address :cons bytes before))))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (proof-heap-layout-p proof-static-p proof-object-map-p proof-heap-object-spans-p
                            proof-external-objects proof-string-accounting-p proof-stack-prefix proof-dynamic-entries
                            proof-dynamic-symbol-objects-p proof-dynamic-root proof-heap-base proof-view
                            proof-span-p allocation-objects-outside-write-p proof-world-machine
                            allocation-fast-machine-return-p boymoo-model::a64-store)))))

(defthm allocation-fast-cells-keeps-stack-prefix
  (implies (and (proof-heap-p before objects packages)
                (allocation-fast-machine-return-p :cons bytes before after))
           (equal (proof-stack-prefix top after objects packages)
                  (proof-stack-prefix top before objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-cells-stable-fields allocation-cell-frontier-within-heap
                 allocation-cell-frontier-outside-published-objects allocation-fast-cells-store-describes-return-memory
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-stack-prefix-after-heap-write
                  (start (allocation-cell-frontier-address before))
                  (bytes 8) (value (allocation-reservation-address :cons bytes before))))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (proof-heap-p proof-heap-layout-p proof-stack-prefix proof-heap-base proof-stack-top
                            proof-stack-base proof-subspan-p proof-span-p allocation-objects-outside-write-p
                            allocation-fast-machine-return-p boymoo-model::a64-store)))))

(defthm allocation-fast-cells-heap-frame
  (implies (and (proof-heap-layout-p before)
                (allocation-fast-machine-return-p :cons bytes before after))
           (proof-heap-frame-p before after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-cells-stable-fields allocation-cell-frontier-within-heap
                 (:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-memory-span-agrees-outside-write
                  (start (allocation-cell-frontier-address before)) (bytes 8)
                  (value (allocation-reservation-address :cons bytes before))
                  (lower (proof-heap-base before)) (upper (+ 24 (proof-heap-base before))))
                 (:instance allocation-memory-span-agrees-outside-write
                  (start (allocation-cell-frontier-address before)) (bytes 8)
                  (value (allocation-reservation-address :cons bytes before))
                  (lower (+ 32 (proof-heap-base before)))
                  (upper (+ (proof-heap-base before) (proof-static-size (proof-heap-base before) (proof-world-machine before)))))
                 (:instance allocation-memory-span-agrees-outside-write
                  (start (allocation-cell-frontier-address before)) (bytes 8)
                  (value (allocation-reservation-address :cons bytes before))
                  (lower (allocation-sp before))
                  (upper (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (proof-heap-layout-p proof-frame-return-p proof-memory-span-agrees-p proof-heap-base
                            proof-stack-base proof-stack-end proof-spaces-end proof-machine-limit
                            proof-cons-floor proof-static-size proof-streams-preserved-p
                            boymoo-model::a64-write-bytes mod)))))

(defthm allocation-fast-cells-preserves-heap
  (implies (and (proof-heap-p before objects packages)
                (proof-allocation-fits-p :cons bytes before)
                (allocation-fast-machine-return-p :cons bytes before after))
           (proof-heap-p after objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-cells-layout allocation-fast-cells-keeps-static
                 allocation-fast-cells-preserves-published-map allocation-fast-cells-keeps-external-list
                 allocation-fast-cells-keeps-dynamic-view allocation-fast-cells-stable-fields
                 (:instance allocation-fast-cells-keeps-object-spans
                  (external (cdr (proof-external-objects (proof-external-head before) (len objects) before objects))))
                 (:instance allocation-fast-cells-keeps-stack-prefix (top (proof-stack-top before))))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (proof-heap-layout-p proof-static-p proof-object-map-p proof-external-objects
                            proof-heap-object-spans-p proof-string-accounting-p proof-dynamic-entries
                            proof-dynamic-view proof-dynamic-symbol-objects-p proof-stack-prefix proof-stack-top
                            proof-heap-base proof-frame-return-p proof-external-head
                            allocation-fast-machine-return-p proof-allocation-fits-p)))))

(defthm allocation-fast-cells-contract-from-heap
  (implies (and (proof-heap-p before objects packages)
                (proof-allocation-fits-p :cons bytes before)
                (allocation-fast-machine-return-p :cons bytes before after))
           (proof-fast-allocation-return-p :cons bytes before after objects objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-cells-preserves-heap allocation-fast-cells-heap-frame
                 allocation-fast-cells-stable-fields allocation-fast-cells-reserved-span
                 allocation-fast-cells-keeps-dynamic-view
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-heap-stack-prefix-exists (world before))
                 (:instance allocation-fast-cells-keeps-stack-prefix (top (proof-stack-top before))))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-heap-frame-p proof-frame-return-p
                               proof-heap-base proof-stack-prefix proof-dynamic-view proof-dynamic-entries
                               proof-dynamic-symbol-objects-p proof-stack-top proof-active-floor proof-inactive-floor
                               proof-streams-preserved-p proof-allocation-fits-p proof-reserved-span-p
                               proof-cons-floor boymoo-model::a64-write-bytes mod))))

(defthm allocation-fast-cells-checked-contract
  (let* ((path (allocation-fast-path :cons))
         (cuts (list (proof-world-reg 30 before))))
    (implies (and (allocation-request-machine-pre-p :cons bytes origin before)
                  (proof-heap-p before objects packages)
                  (proof-allocation-fits-p :cons bytes before)
                  (allocation-path-ready-p path cuts before)
                  (equal after (allocation-path-end path before)))
             (and (proof-fast-allocation-return-p :cons bytes before after objects objects packages)
                  (proof-segment-p (len path) cuts before :cut after))))
  :rule-classes nil
  :hints (("Goal" :use (allocation-fast-cells-contract-from-heap
                        (:instance allocation-fast-checked-return (kind :cons)))
           :in-theory (disable allocation-fast-machine-return-p allocation-request-machine-pre-p
                               allocation-path-ready-p allocation-path-end proof-heap-p
                               proof-allocation-fits-p proof-fast-allocation-return-p proof-segment-p))))
