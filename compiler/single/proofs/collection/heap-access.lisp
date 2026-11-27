(in-package "BOYMOO-PROOFS")

(include-book "published")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "kestrel/arithmetic-light/floor" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm collection-runtime-page-rounding-covers-input
   (implies (natp address)
            (<= address (proof-align-up address *proof-runtime-page*)))
   :rule-classes :linear
   :hints (("Goal"
            :use ((:instance acl2::floor-bounded-by-/
                             (acl2::x (- address)) (acl2::y *proof-runtime-page*))
                  (:instance acl2::rational-implies2
                             (acl2::x (* (/ *proof-runtime-page*) address))))
            :in-theory (e/d (ceiling)
                             (floor acl2::floor-minus acl2::floor-minus-arg1-better
                              acl2::floor-=-x/y acl2::floor-unique-equal-version
                              acl2::rational-implies2))))))

(local
 (defthm collection-static-size-is-nonnegative-word
   (unsigned-byte-p 64 (proof-static-size base machine))
   :hints (("Goal" :use ((:instance collection-loaded-word-is-unsigned
                                    (address base) (world (list machine))))
                   :in-theory (enable collection-read-word)))))

(local
 (in-theory (disable proof-load-word proof-object-size proof-static-size proof-world-machine
                     proof-world-regions proof-heap-base proof-world-stop proof-world-reg
                     proof-active-floor proof-active-end proof-inactive-floor proof-inactive-end
                     proof-cons-floor proof-box-top proof-heap-limit proof-spaces-end proof-runtime-word
                     proof-stack-base proof-stack-top proof-stack-end proof-machine-limit
                     proof-stack-limit boymoo-model::a64-sp proof-regions-p proof-align-up
                     proof-page-size-p proof-world-page-size proof-covered-p mod)))

(defthm collection-heap-layout-bounds-active-space-and-static-block
  (let* ((base (proof-heap-base world))
         (size (proof-static-size base (proof-world-machine world)))
         (floor (proof-active-floor world))
         (end (proof-active-end world)))
    (implies (proof-heap-layout-p world)
             (and (<= (+ base size) floor)
                  (<= floor (proof-cons-floor world))
                  (<= (proof-box-top world) end)
                  (<= end (proof-spaces-end world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-runtime-page-rounding-covers-input
                            (address (+ (proof-heap-base world)
                                        (proof-static-size (proof-heap-base world) (proof-world-machine world)))))
                 (:instance collection-static-size-is-nonnegative-word
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (e/d (proof-heap-base)
                            (collection-runtime-page-rounding-covers-input
                             collection-static-size-is-nonnegative-word)))))

(local
 (defthm collection-active-object-map-lookup-is-in-active-space
   (let* ((object (assoc-equal address objects))
          (size (proof-object-size object (proof-world-machine world))))
     (implies (and (proof-heap-object-spans-p objects external world)
                   object (eq (proof-object-zone object) :active)
                   (natp (proof-active-floor world)) (natp (proof-active-end world))
                   (<= (proof-active-floor world) (proof-cons-floor world))
                   (<= (proof-box-top world) (proof-active-end world)))
              (proof-subspan-p address size (proof-active-floor world) (proof-active-end world))))
   :hints (("Goal" :induct (assoc-equal address objects)
                   :in-theory (disable acl2::mod-=-0)))))

(local
 (defthm collection-runtime-word-is-natural
   (natp (proof-runtime-word offset world))
   :hints (("Goal"
            :use ((:instance collection-loaded-word-is-natural
                             (address (+ (- (proof-heap-base world) 128) offset))))
            :in-theory (enable collection-read-word proof-runtime-word)))))

(defthm collection-published-active-object-is-writable-and-in-forwarding-range
  (let* ((object (assoc-equal address objects))
         (size (proof-object-size object (proof-world-machine world)))
         (regions (proof-world-regions world)))
    (implies (and (proof-heap-p world objects packages)
                  object (eq (proof-object-zone object) :active))
             (and (proof-covered-p address size :write regions)
                  (<= (proof-active-floor world) address)
                  (< address (proof-spaces-end world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-heap-layout-bounds-active-space-and-static-block)
                 (:instance collection-runtime-word-is-natural (offset 0))
                 (:instance collection-runtime-word-is-natural (offset 8))
                 (:instance collection-active-object-map-lookup-is-in-active-space
                            (external (cdr (proof-external-objects
                                            (proof-external-head world) (len objects) world objects))))
                 (:instance collection-covered-subspan
                            (base (- (proof-heap-base world) *proof-heap-prefix*))
                            (extent (+ *proof-heap-prefix* (- (proof-spaces-end world) (proof-heap-base world))))
                            (width (proof-object-size (assoc-equal address objects) (proof-world-machine world)))
                            (access :write) (regions (proof-world-regions world))))
           :in-theory (e/d (proof-active-floor proof-active-end)
                            (proof-static-p proof-object-map-p proof-heap-object-spans-p proof-external-head
                             proof-external-objects proof-dynamic-entries proof-dynamic-view proof-stack-prefix
                             proof-dynamic-symbol-objects-p proof-string-accounting-p
                             collection-active-object-map-lookup-is-in-active-space)))))

(local
 (defthm collection-static-lookup-survives-filtering-to-static-objects
   (let ((object (assoc-equal address objects)))
     (implies (and object (eq (proof-object-zone object) :static))
              (equal (assoc-equal address (proof-static-objects objects)) object)))
   :hints (("Goal" :induct (assoc-equal address objects)))))

(local
 (defthm collection-object-lookup-respects-static-spans
   (let ((object (assoc-equal address objects)))
     (implies (and (proof-static-spans-p objects base size machine) object)
              (proof-subspan-p address (proof-object-size object machine) (+ base 32) (+ base size))))
   :hints (("Goal" :induct (assoc-equal address objects)))))

(defthm collection-published-static-object-is-in-unchanged-forwarding-range
  (let* ((object (assoc-equal address objects))
         (base (proof-heap-base world)))
    (implies (and (proof-heap-p world objects packages)
                  object (eq (proof-object-zone object) :static))
             (and (<= base address) (< address (proof-active-floor world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-heap-layout-bounds-active-space-and-static-block)
                 (:instance collection-static-lookup-survives-filtering-to-static-objects)
                 (:instance collection-object-lookup-respects-static-spans
                            (objects (proof-static-objects objects))
                            (base (proof-heap-base world)) (machine (proof-world-machine world))
                            (size (proof-static-size (proof-heap-base world) (proof-world-machine world)))))
           :in-theory (disable proof-object-map-p proof-static-spans-p proof-static-objects
                               proof-packages-p proof-load-word proof-value-p proof-view
                               proof-package-row-views proof-static-buckets-p proof-home-bindings-p
                               proof-package-bindings-p proof-heap-layout-p proof-heap-object-spans-p
                               proof-external-head proof-external-objects proof-dynamic-entries proof-dynamic-view
                               proof-stack-prefix proof-dynamic-symbol-objects-p proof-string-accounting-p
                               collection-object-lookup-respects-static-spans
                               collection-static-lookup-survives-filtering-to-static-objects))))

(local
 (defthm collection-mapped-rw-subspan-is-writable
   (implies (and (member-equal (proof-region base end :rw) regions)
                 (proof-subspan-p address bytes base end))
            (proof-covered-p address bytes :write regions))
   :hints (("Goal" :induct (member-equal (proof-region base end :rw) regions)
                   :in-theory (enable proof-covered-p)))))

(local
 (defthm collection-mapped-region-has-word-range
   (implies (and (proof-regions-p regions) (member-equal (proof-region base end :rw) regions))
            (proof-region-p (proof-region base end :rw)))
   :hints (("Goal" :induct (member-equal (proof-region base end :rw) regions)
                   :in-theory (enable proof-regions-p)))))

(local
 (defthm collection-external-header-length-is-natural
   (natp (proof-header-size (proof-load-word address machine)))
   :rule-classes :type-prescription
   :hints (("Goal"
            :use ((:instance collection-static-size-is-nonnegative-word (base address)))
            :in-theory (enable proof-static-size proof-header-size)))))

(local
 (defthm collection-external-mapping-encloses-header-and-mark
   (let* ((header (+ head 24))
          (size (proof-load-word (+ head 8) machine))
          (bytes (proof-header-size (proof-load-word header machine)))
          (end (+ head size)))
     (implies (and (proof-regions-p regions)
                   (member-equal (proof-region head end :rw) regions)
                   (equal size (proof-align-up (+ 32 bytes) *proof-runtime-page*)))
              (and (proof-subspan-p header (+ 8 bytes) head end)
                   (proof-covered-p (+ head 16) 8 :write regions))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-external-header-length-is-natural (address (+ head 24)))
                  (:instance collection-runtime-page-rounding-covers-input
                             (address (+ 32 (proof-header-size (proof-load-word (+ head 24) machine)))))
                  (:instance collection-mapped-region-has-word-range
                             (base head) (end (+ head (proof-load-word (+ head 8) machine))))
                  (:instance collection-mapped-rw-subspan-is-writable
                             (base head) (end (+ head (proof-load-word (+ head 8) machine)))
                             (address (+ head 16)) (bytes 8)))
            :in-theory (disable collection-runtime-page-rounding-covers-input
                                collection-mapped-rw-subspan-is-writable proof-header-size)))))

(local
 (defthm collection-listed-external-header-is-separated-and-markable
   (let* ((mappings (proof-external-objects head fuel world objects))
          (object (assoc-equal address objects))
          (regions (proof-world-regions world))
          (base (proof-heap-base world)))
     (implies (and (proof-regions-p regions) (member-equal address (cdr mappings)))
              (and object (eq (proof-object-zone object) :external)
                   (eq (proof-object-kind object) :header)
                   (proof-covered-p (- address 8) 8 :write regions)
                   (or (< address base) (<= (proof-spaces-end world) address)))))
   :rule-classes nil
   :hints (("Goal"
            :induct (proof-external-objects head fuel world objects)
            :in-theory (disable proof-header-size))
           (and stable-under-simplificationp
                '(:use ((:instance collection-external-mapping-encloses-header-and-mark
                                   (machine (proof-world-machine world))
                                   (regions (proof-world-regions world)))))))))

(local
 (defthm collection-heap-layout-has-checked-regions
   (implies (proof-heap-layout-p world)
            (proof-regions-p (proof-world-regions world)))))

(local
 (defthm collection-external-object-map-lookup-is-in-list
   (let ((object (assoc-equal address objects)))
     (implies (and (proof-heap-object-spans-p objects external world)
                   object (eq (proof-object-zone object) :external))
              (member-equal address external)))
   :hints (("Goal" :induct (assoc-equal address objects)))))

(defthm collection-published-external-object-has-writable-mark-and-forwarding-range
  (let* ((object (assoc-equal address objects))
         (base (proof-heap-base world)))
    (implies (and (proof-heap-p world objects packages)
                  object (eq (proof-object-zone object) :external))
             (and (eq (proof-object-kind object) :header)
                  (proof-covered-p (- address 8) 8 :write (proof-world-regions world))
                  (or (< address base) (<= (proof-spaces-end world) address)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-listed-external-header-is-separated-and-markable
                            (head (proof-external-head world)) (fuel (len objects)))
                 (:instance collection-external-object-map-lookup-is-in-list
                            (external (cdr (proof-external-objects
                                            (proof-external-head world) (len objects) world objects)))))
           :in-theory (disable proof-external-objects proof-static-p proof-object-map-p
                               proof-dynamic-entries proof-dynamic-view proof-stack-prefix proof-heap-layout-p
                               proof-dynamic-symbol-objects-p proof-string-accounting-p proof-heap-object-spans-p
                               collection-external-object-map-lookup-is-in-list)
           :do-not-induct t)))

(defthm collection-inactive-space-span-is-writable
  (let* ((lower (proof-inactive-floor world))
         (upper (proof-inactive-end world)))
    (implies (and (proof-heap-layout-p world) (proof-subspan-p address bytes lower upper))
             (proof-covered-p address bytes :write (proof-world-regions world))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-runtime-page-rounding-covers-input
                            (address (+ (proof-heap-base world)
                                        (proof-static-size (proof-heap-base world) (proof-world-machine world)))))
                 (:instance collection-static-size-is-nonnegative-word
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance collection-covered-subspan
                            (base (- (proof-heap-base world) *proof-heap-prefix*))
                            (extent (+ *proof-heap-prefix* (- (proof-spaces-end world) (proof-heap-base world))))
                            (width bytes) (access :write) (regions (proof-world-regions world))))
           :in-theory (disable collection-runtime-page-rounding-covers-input
                               collection-static-size-is-nonnegative-word))))

(local
 (defthm collection-fresh-copy-span-fits-destination-space
   (let* ((record (assoc-equal address (collection-unseen work)))
          (destination (collection-copy-address record work))
          (bytes (collection-copy-bytes record)))
     (implies (and (collection-destination-space-p work graph lower upper)
                   (collection-moved-kind-p record)
                   record)
              (and (proof-subspan-p destination bytes lower upper)
                   (unsigned-byte-p 64 (+ destination bytes)))))
   :hints (("Goal"
            :use ((:instance collection-discovery-preserves-destination-space
                             (floor lower) (end upper)))
            :in-theory (disable collection-discovery-preserves-destination-space
                                collection-header-frontier collection-cell-frontier
                                collection-unseen collection-pending-bytes)))))

(defthm collection-published-fresh-copy-has-writable-destination
  (let* ((record (assoc-equal address (collection-unseen work)))
         (destination (collection-copy-address record work))
         (bytes (collection-copy-bytes record)))
    (implies (and (proof-heap-layout-p world)
                  (collection-destination-space-p work graph
                                                  (proof-inactive-floor world)
                                                  (proof-inactive-end world))
                  record (collection-moved-kind-p record))
             (and (proof-covered-p destination bytes :write (proof-world-regions world))
                  (unsigned-byte-p 64 (+ destination bytes)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-fresh-copy-span-fits-destination-space
                            (lower (proof-inactive-floor world)) (upper (proof-inactive-end world)))
                 (:instance collection-inactive-space-span-is-writable
                            (address (collection-copy-address (assoc-equal address (collection-unseen work)) work))
                            (bytes (collection-copy-bytes (assoc-equal address (collection-unseen work))))))
           :in-theory (disable collection-unseen collection-copy-address collection-copy-bytes
                               collection-fresh-copy-span-fits-destination-space
                               proof-heap-layout-p collection-destination-space-p))))

(local
 (defthm collection-heap-layout-separates-semispace-intervals
   (implies (proof-heap-layout-p world)
            (proof-disjoint-p (proof-active-floor world) (proof-active-end world)
                              (proof-inactive-floor world) (proof-inactive-end world)))))

(defthm collection-published-movable-source-is-disjoint-from-inactive-copy
  (let* ((object (assoc-equal source objects))
         (bytes (proof-object-size object (proof-world-machine world))))
    (implies (and (proof-heap-p world objects packages)
                  object (eq (proof-object-zone object) :active)
                  (proof-subspan-p destination width
                                   (proof-inactive-floor world) (proof-inactive-end world)))
             (proof-disjoint-p source (+ source bytes) destination (+ destination width))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-heap-layout-separates-semispace-intervals)
                 (:instance collection-heap-layout-bounds-active-space-and-static-block)
                 (:instance collection-runtime-word-is-natural (offset 0))
                 (:instance collection-runtime-word-is-natural (offset 8))
                 (:instance collection-active-object-map-lookup-is-in-active-space
                            (address source)
                            (external (cdr (proof-external-objects
                                            (proof-external-head world) (len objects) world objects)))))
           :in-theory (e/d (proof-active-floor proof-active-end)
                            (proof-heap-layout-p proof-static-p proof-object-map-p
                             proof-heap-object-spans-p proof-external-objects proof-dynamic-entries
                             proof-dynamic-view proof-stack-prefix proof-dynamic-symbol-objects-p
                             proof-string-accounting-p collection-active-object-map-lookup-is-in-active-space
                             collection-heap-layout-separates-semispace-intervals)))))
