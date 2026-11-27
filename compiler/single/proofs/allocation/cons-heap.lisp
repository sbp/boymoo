(in-package "BOYMOO-PROOFS")

(include-book "cons-fast-contract")
(include-book "published-heap")
(include-book "unpublished-write")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable allocation-runtime-word-as-load proof-runtime-word)))

(defun allocation-initialized-cell-world (address first second world)
  (allocation-store-word (+ 8 address) second
                         (allocation-store-word address first world)))

(defthm allocation-initialized-cell-world-machine
  (equal (proof-world-machine (allocation-initialized-cell-world address first second world))
         (allocation-store-cell address first second (proof-world-machine world)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-store))))

(defthm allocation-reserved-cell-write-addresses
  (implies (and (proof-heap-layout-p world)
                (proof-reserved-span-p :cons address 16 world objects))
           (and (proof-subspan-p address 8 (proof-active-floor world) (proof-active-end world))
                (proof-subspan-p (+ 8 address) 8 (proof-active-floor world) (proof-active-end world))
                (proof-subspan-p address 16 (proof-cons-floor world) (proof-active-end world))
                (equal (mod address 16) 0)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable proof-covered-p proof-regions-p proof-align-up
                               proof-object-disjoint-p proof-disjoint-p proof-static-size mod))))

(defthm allocation-reserved-cell-avoids-published-objects
  (implies (and (proof-heap-p world objects packages)
                (proof-reserved-span-p :cons address 16 world objects))
           (and (proof-span-p address 16)
                (allocation-objects-outside-write-p address (+ address 16) objects (proof-world-machine world))
                (not (assoc-equal address objects))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-heap-published-map
                 (:instance allocation-object-map-with-disjoint-spans
                  (pending objects) (symbols nil) (start address) (end (+ address 16))
                  (machine (proof-world-machine world)) (base (proof-heap-base world)))
                 (:instance allocation-cell-span-excludes-existing-address (machine (proof-world-machine world))))
           :in-theory (disable proof-heap-p proof-object-map-p proof-object-disjoint-p
                               proof-span-p allocation-objects-outside-write-p proof-cons-floor proof-active-end))))

(defthm allocation-initializing-cell-keeps-old-heap
  (let ((initialized (allocation-initialized-cell-world address first second world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-reserved-span-p :cons address 16 world objects))
             (and (proof-heap-p initialized objects packages)
                  (allocation-same-external-bounds-p world initialized)
                  (equal (proof-cons-floor initialized) (proof-cons-floor world))
                  (equal (proof-active-end initialized) (proof-active-end world))
                  (equal (proof-stack-prefix top initialized objects packages)
                         (proof-stack-prefix top world objects packages))
                  (equal (proof-dynamic-view initialized objects packages)
                         (proof-dynamic-view world objects packages)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-layout-of-heap allocation-reserved-cell-write-addresses
                 allocation-reserved-cell-avoids-published-objects
                 (:instance allocation-objects-outside-pair-write (start address) (machine (proof-world-machine world)))
                 (:instance allocation-heap-after-unpublished-active-word-store (value first))
                 (:instance allocation-active-word-store-keeps-layout (value first))
                 (:instance allocation-heap-after-unpublished-active-word-store
                  (world (allocation-store-word address first world)) (address (+ 8 address)) (value second))
                 (:instance allocation-active-word-store-keeps-stack-prefix (value first))
                 (:instance allocation-active-word-store-keeps-stack-prefix
                  (world (allocation-store-word address first world)) (address (+ 8 address)) (value second))
                 (:instance allocation-active-word-store-keeps-dynamic (value first))
                 (:instance allocation-active-word-store-keeps-dynamic
                  (world (allocation-store-word address first world)) (address (+ 8 address)) (value second)))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (proof-heap-p proof-heap-layout-p proof-reserved-span-p
                            proof-stack-prefix proof-stack-top proof-dynamic-view proof-dynamic-symbol-objects-p
                            proof-dynamic-entries proof-subspan-p proof-span-p allocation-objects-outside-write-p
                            boymoo-model::a64-store mod)))))

(defthm allocation-heap-under-same-context-and-frontiers
  (implies (and (proof-heap-p before objects packages)
                (allocation-same-heap-context-p before after)
                (equal (proof-stack-limit before) (proof-stack-limit after))
                (equal (proof-box-top before) (proof-box-top after))
                (equal (proof-heap-limit before) (proof-heap-limit after)))
           (proof-heap-p after objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-extend-layout-tops allocation-growth-layout-facts
                 allocation-heap-with-raised-box-top
                 (:instance allocation-layout-of-heap (world before)))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-stack-base proof-stack-limit
                               proof-box-top proof-heap-limit proof-cons-floor proof-stack-end mod))))

(defthm allocation-fast-cons-after-initialized-context
  (let* ((reserved (allocation-cons-reservation-world before))
         (address (allocation-reservation-address :cons 16 before))
         (initialized (allocation-initialized-cell-world address (proof-world-reg 0 before)
                                                        (proof-world-reg 1 before) reserved)))
    (implies (and (proof-heap-layout-p before)
                  (allocation-fast-machine-return-p :cons 16 before reserved)
                  (allocation-cons-fast-return-p before after))
             (and (allocation-same-heap-context-p initialized after)
                  (equal (proof-stack-limit initialized) (proof-stack-limit after))
                  (equal (proof-box-top initialized) (proof-box-top after))
                  (equal (proof-heap-limit initialized) (proof-heap-limit after)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-fast-initializes-reserved-cell
                 (:instance allocation-fast-cells-stable-fields (bytes 16) (after (allocation-cons-reservation-world before)))
                 (:instance allocation-register-frame-member (register 23) (upper 30) (clobbers '(0 2 9 26)))
                 (:instance allocation-register-frame-member (register 24) (upper 30) (clobbers '(0 2 9 26)))
                 (:instance allocation-register-frame-member (register 25) (upper 30) (clobbers '(0 2 9 26))))
           :in-theory (e/d (allocation-same-heap-context-p allocation-same-external-bounds-p)
                           (allocation-cons-reservation-world proof-heap-layout-p
                            proof-span-p proof-cons-floor proof-register-frame-p
                            allocation-cons-fields-p boymoo-model::a64-write-bytes mod)))))

(defthm allocation-fast-cons-initialized-heap
  (let ((address (allocation-reservation-address :cons 16 before)))
    (implies (and (allocation-cons-machine-entry-p origin before)
                  (proof-allocation-fits-p :cons 16 before)
                  (proof-heap-p before objects packages)
                  (allocation-cons-fast-return-p before after))
             (and (proof-heap-p after objects packages)
                  (allocation-same-external-bounds-p before after)
                  (not (assoc-equal address objects))
                  (equal (mod address 16) 0)
                  (proof-subspan-p address 16 (proof-cons-floor after) (proof-active-end after))
                  (equal (proof-stack-prefix top after objects packages)
                         (proof-stack-prefix top before objects packages))
                  (equal (proof-dynamic-view after objects packages)
                         (proof-dynamic-view before objects packages)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-inline-reservation allocation-fast-cons-after-initialized-context
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-layout-of-heap (world (allocation-cons-reservation-world before)))
                 (:instance allocation-fast-cells-preserves-heap (bytes 16) (after (allocation-cons-reservation-world before)))
                 (:instance allocation-fast-cells-reserved-span (bytes 16) (after (allocation-cons-reservation-world before)))
                 (:instance allocation-fast-cells-reservation-geometry (bytes 16) (after (allocation-cons-reservation-world before)))
                 (:instance allocation-fast-cells-stable-fields (bytes 16) (after (allocation-cons-reservation-world before)))
                 (:instance allocation-reserved-cell-write-addresses
                  (world (allocation-cons-reservation-world before)) (address (allocation-reservation-address :cons 16 before)))
                 (:instance allocation-reserved-cell-avoids-published-objects
                  (world (allocation-cons-reservation-world before)) (address (allocation-reservation-address :cons 16 before)))
                 (:instance allocation-fast-cells-keeps-dynamic-view (bytes 16) (after (allocation-cons-reservation-world before)))
                 (:instance allocation-fast-cells-keeps-stack-prefix (bytes 16) (after (allocation-cons-reservation-world before)))
                 (:instance allocation-initializing-cell-keeps-old-heap
                  (world (allocation-cons-reservation-world before)) (address (allocation-reservation-address :cons 16 before))
                  (first (proof-world-reg 0 before)) (second (proof-world-reg 1 before)))
                 (:instance allocation-heap-under-same-context-and-frontiers
                  (before (allocation-initialized-cell-world (allocation-reservation-address :cons 16 before)
                                                            (proof-world-reg 0 before) (proof-world-reg 1 before)
                                                            (allocation-cons-reservation-world before)))))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (allocation-cons-machine-entry-p allocation-cons-fast-return-p
                            allocation-cons-reservation-world allocation-initialized-cell-world
                            allocation-fast-machine-return-p
                            proof-heap-p proof-heap-layout-p proof-heap-frame-p proof-allocation-fits-p
                            proof-frame-return-p proof-reserved-span-p proof-subspan-p proof-span-p
                            proof-stack-prefix proof-dynamic-view proof-dynamic-symbol-objects-p proof-dynamic-entries
                            proof-prefix-preserved-p proof-dynamic-table-preserved-p
                            allocation-reservation-address mod)))))

(local
 (defthm allocation-heap-dynamic-view-exists
   (implies (proof-heap-p world objects packages)
            (proof-dynamic-view world objects packages))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-heap-layout-p proof-static-p proof-object-map-p
                                      proof-external-objects proof-heap-object-spans-p proof-string-accounting-p
                                      proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p
                                      proof-stack-prefix)))))

(defthm allocation-fast-cons-published-heap
  (let* ((address (allocation-reservation-address :cons 16 before))
         (base (proof-heap-base before))
         (record (proof-object address :active :cons rank))
         (published (cons record objects)))
    (implies (and (allocation-cons-machine-entry-p origin before)
                  (proof-allocation-fits-p :cons 16 before)
                  (proof-heap-p before objects packages)
                  (allocation-cons-fast-return-p before after)
                  (proof-reg-value-p 0 left before objects packages)
                  (proof-reg-value-p 1 right before objects packages)
                  (equal (mod address 8) 0) (equal (mod base 8) 0)
                  (natp rank)
                  (<= (allocation-word-depth (proof-world-reg 0 before) base objects) rank)
                  (<= (allocation-word-depth (proof-world-reg 1 before) base objects) rank))
             (and (proof-heap-p after published packages)
                  (proof-prefix-preserved-p (proof-stack-top before) before after objects published packages)
                  (proof-dynamic-table-preserved-p nil before after objects published packages)
                  (proof-reg-value-p 0 (cons left right) after published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-fast-publishes-cell
                 (:instance allocation-fast-cons-initialized-heap (top (proof-stack-top before)))
                 (:instance allocation-heap-stack-prefix-exists (world before))
                 (:instance allocation-heap-dynamic-view-exists (world after))
                 (:instance allocation-published-cons-admits-heap
                  (world after) (address (allocation-reservation-address :cons 16 before)))
                 (:instance allocation-cons-fast-initializes-reserved-cell)
                 allocation-cons-inline-reservation)
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-object-map-p proof-stack-prefix
                               proof-dynamic-view proof-heap-base proof-stack-top proof-cons-floor proof-active-end
                               proof-reg-value-p proof-subspan-p allocation-cons-fast-return-p
                               allocation-cons-machine-entry-p allocation-cons-reservation-world
                               proof-allocation-fits-p allocation-reservation-address allocation-word-depth mod))))

(defun allocation-fast-cons-writes (before)
  (let ((cell (allocation-reservation-address :cons 16 before)))
    (list (cons (allocation-cell-frontier-address before) cell)
          (cons cell (proof-world-reg 0 before))
          (cons (+ 8 cell) (proof-world-reg 1 before)))))

(defthm allocation-fast-cons-only-writes-frontier-and-cell
  (implies (allocation-cons-fast-return-p before after)
           (equal (allocation-memory after)
                  (allocation-memory (allocation-write-words (allocation-fast-cons-writes before) before))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable allocation-cons-fields-p proof-register-frame-p
                               proof-streams-preserved-p proof-span-p boymoo-model::a64-write-bytes))))

(local
 (defthm allocation-layout-active-end-within-spaces
   (implies (proof-heap-layout-p world)
            (<= (proof-active-end world) (proof-spaces-end world)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-align-up proof-covered-p proof-regions-p proof-disjoint-p mod)))))

(defthm allocation-fast-cons-writes-avoid-frame-spans
  (let* ((base (proof-heap-base before))
         (static-end (+ base (proof-static-size base (proof-world-machine before))))
         (sp (allocation-sp before))
         (machine-end (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))
         (writes (allocation-fast-cons-writes before)))
    (implies (and (proof-heap-layout-p before)
                  (proof-allocation-fits-p :cons 16 before)
                  (allocation-cons-fast-return-p before after))
             (and (natp base) (<= (+ base 24) *allocation-word-modulus*)
                  (natp static-end) (<= static-end *allocation-word-modulus*)
                  (natp sp) (natp machine-end) (<= machine-end *allocation-word-modulus*)
                  (allocation-word-writes-avoid-span-p writes base (+ base 24))
                  (allocation-word-writes-avoid-span-p writes (+ base 32) static-end)
                  (allocation-word-writes-avoid-span-p writes sp machine-end))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cell-frontier-within-heap
                 (:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-static-end-below-box-top (world before))
                 (:instance allocation-layout-active-end-within-spaces (world before))
                 allocation-growth-layout-facts
                 (:instance allocation-word-register-range (register 0) (world before)))
           :in-theory (disable proof-heap-layout-p proof-frame-return-p allocation-cons-fields-p
                               proof-heap-base proof-static-size proof-cons-floor proof-active-end
                               proof-box-top proof-heap-limit proof-spaces-end proof-machine-limit
                               proof-streams-preserved-p boymoo-model::a64-write-bytes mod))))

(defthm allocation-fast-cons-preserves-heap-frame
  (implies (and (allocation-cons-machine-entry-p origin before)
                (proof-heap-p before objects packages)
                (proof-allocation-fits-p :cons 16 before)
                (allocation-cons-fast-return-p before after))
           (proof-heap-frame-p before after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-fast-cons-only-writes-frontier-and-cell
                 (:instance allocation-layout-of-heap (world before))
                 allocation-fast-cons-writes-avoid-frame-spans
                 (:instance allocation-fast-cons-initialized-heap (top (proof-stack-top before)))
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-fast-cons-writes before)) (world before)
                  (lower (proof-heap-base before)) (upper (+ 24 (proof-heap-base before))))
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-fast-cons-writes before)) (world before) (lower (+ 32 (proof-heap-base before)))
                  (upper (+ (proof-heap-base before) (proof-static-size (proof-heap-base before) (proof-world-machine before)))))
                 (:instance allocation-word-writes-keep-protected-span
                  (writes (allocation-fast-cons-writes before)) (world before) (lower (allocation-sp before))
                  (upper (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           (allocation-cons-machine-entry-p proof-heap-p proof-heap-layout-p proof-allocation-fits-p
                            proof-heap-base proof-stack-base proof-stack-top proof-stack-end proof-active-end proof-cons-floor
                            proof-machine-limit proof-static-size proof-spaces-end proof-subspan-p proof-reserved-span-p
                            proof-stack-prefix proof-dynamic-view proof-memory-span-agrees-p proof-streams-preserved-p
                            proof-frame-return-p allocation-cons-fields-p allocation-fast-cons-writes
                            allocation-word-writes-avoid-span-p boymoo-model::a64-write-bytes mod)))))

(defthm allocation-fast-cons-shared-control-frame
  (implies (allocation-cons-fast-return-p before after)
           (proof-frame-return-p (proof-runtime-clobbers 'cons) t before after))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-register-frame-under-more-clobbers
                  (small '(0 2 9 26)) (large (proof-runtime-clobbers 'cons)) (register 30)))
           :in-theory (disable proof-register-frame-p proof-span-p proof-cons-floor
                               allocation-cons-fields-p proof-streams-preserved-p))))

(defthm allocation-cons-fast-runtime-return
  (let* ((address (allocation-reservation-address :cons 16 before))
         (base (proof-heap-base before))
         (published (cons (proof-object address :active :cons rank) objects))
         (cuts (list (proof-world-reg 30 before))))
    (implies (and (allocation-cons-machine-entry-p origin before)
                  (proof-heap-p before objects packages)
                  (proof-allocation-fits-p :cons 16 before)
                  (proof-reg-value-p 0 left before objects packages)
                  (proof-reg-value-p 1 right before objects packages)
                  (equal (mod address 8) 0) (equal (mod base 8) 0)
                  (natp rank)
                  (<= (allocation-word-depth (proof-world-reg 0 before) base objects) rank)
                  (<= (allocation-word-depth (proof-world-reg 1 before) base objects) rank)
                  (allocation-path-ready-p *allocation-cons-fast-path* cuts before)
                  (equal after (allocation-path-end *allocation-cons-fast-path* before)))
             (and (proof-segment-p (len *allocation-cons-fast-path*) cuts before :cut after)
                  (proof-runtime-return-p 'cons (list left right) program before after objects published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-cons-fast-checked-return allocation-fast-cons-published-heap
                 allocation-fast-cons-preserves-heap-frame allocation-fast-cons-shared-control-frame)
           :in-theory (e/d (boymoo-model::core-primitive)
                           (allocation-cons-machine-entry-p allocation-cons-fast-return-p
                            allocation-path-ready-p allocation-path-end proof-segment-p
                            proof-heap-p proof-heap-frame-p proof-frame-return-p proof-allocation-fits-p
                            proof-prefix-preserved-p proof-dynamic-table-preserved-p
                            proof-heap-base proof-reg-value-p allocation-reservation-address allocation-word-depth mod)))))
