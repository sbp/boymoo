(in-package "BOYMOO-PROOFS")

(include-book "graph")
(include-book "queues")
(include-book "regions")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-load-word proof-view proof-object-view
                     proof-object-record-p proof-symbol-object-p
                     proof-pointer-address proof-word-tag proof-header-type
                     collection-reference-fields boymoo-model::a64-unsigned
                     (:definition ash) (:definition acl2::binary-logand))))

(local
 (defthm collection-aligned-up-size-is-natural
   (natp (proof-align-up count 8))
   :rule-classes :type-prescription))

(defthm collection-object-size-is-positive
  (posp (proof-object-size object machine))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable proof-align-up proof-header-size))))

(local
 (defthm collection-cons-size
   (implies (eq (proof-object-kind object) :cons)
            (equal (proof-object-size object machine) 16))))

(local
 (in-theory (disable proof-object-size proof-align-up
                     collection-word-after-flags-change
                     collection-word-after-pc-change)))

(defthm collection-published-copy-spans-are-nonempty
  (collection-nonempty-copy-spans-p
   (collection-published-object-graph pending base objects machine))
  :hints (("Goal" :induct (collection-published-object-graph pending base objects machine)
                  :in-theory (disable proof-header-size))))

(defthm collection-published-roots-start-valid-scan-cursors
  (let* ((graph (collection-published-object-graph
                 objects (proof-heap-base world) objects (proof-world-machine world)))
         (roots (collection-published-roots world objects))
         (lower (proof-inactive-floor world))
         (upper (proof-inactive-end world))
         (work (collection-discover-fields roots
                                           (collection-work graph nil nil nil lower upper))))
    (collection-scan-cursors-p lower upper work))
  :hints (("Goal" :in-theory (disable collection-published-object-graph
                                      collection-published-roots collection-discover-fields
                                      collection-scan-cursors-p collection-work
                                      proof-world-machine proof-inactive-floor proof-inactive-end
                                      proof-heap-base))))

(defun collection-separated-objects-p (objects machine)
  (if (endp objects)
      t
    (let* ((object (car objects))
           (address (proof-object-address object))
           (size (proof-object-size object machine)))
      (and (proof-object-disjoint-p address (+ address size) (cdr objects) machine)
           (collection-separated-objects-p (cdr objects) machine)))))

(local
 (defthm collection-object-map-has-separated-spans
   (implies (proof-object-map-p pending objects symbols base packages machine)
            (collection-separated-objects-p pending machine))
   :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)))))

(local
 (defthm collection-no-duplicate-key-in-extracted-records
   (implies (and (integerp address) (posp size)
                 (proof-object-disjoint-p address (+ address size) pending machine))
            (not (assoc-equal address
                              (collection-published-object-graph pending base objects machine))))
   :hints (("Goal" :induct (collection-published-object-graph pending base objects machine)
                   :in-theory (disable proof-header-size)))))

(local
 (defthm collection-source-records-admit-a-fresh-key
   (implies (and (collection-source-records-p records graph)
                 (not (assoc-equal (car record) records)))
            (collection-source-records-p records (cons record graph)))
   :hints (("Goal" :induct (collection-source-records-p records graph)
                   :in-theory (disable collection-graph-record-p)))))

(local
 (defthm collection-all-object-map-addresses-are-integers
   (implies (and (consp pending)
                 (proof-object-map-p pending objects symbols base packages machine))
            (integerp (proof-object-address (car pending))))
   :hints (("Goal" :expand ((proof-object-map-p pending objects symbols base packages machine))
                   :in-theory (enable proof-object-record-p)))))

(local
 (defthm collection-extracted-graph-is-source-consistent
   (let ((graph (collection-published-object-graph pending base objects machine)))
     (implies (proof-object-map-p pending objects symbols base packages machine)
              (collection-source-records-p graph graph)))
   :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
                   :in-theory (disable collection-reference-fields proof-header-size
                                       collection-no-duplicate-key-in-extracted-records))
           ("Subgoal *1/2"
            :use ((:instance collection-no-duplicate-key-in-extracted-records
                             (address (proof-object-address (car pending)))
                             (size (proof-object-size (car pending) machine))
                             (pending (cdr pending))))))))

(defun collection-active-spans-covered-p (objects machine regions)
  (if (endp objects)
      t
    (let ((object (car objects)))
      (and (if (eq (proof-object-zone object) :active)
               (proof-covered-p (proof-object-address object)
                                (proof-object-size object machine) :write regions)
             t)
           (collection-active-spans-covered-p (cdr objects) machine regions)))))

(local
 (defthm collection-removal-preserves-other-active-spans
   (implies (and (collection-active-spans-covered-p objects machine regions)
                 (proof-object-disjoint-p address (+ address size) objects machine))
            (collection-active-spans-covered-p
             objects machine (proof-remove-region-span address size regions)))
   :hints (("Goal" :induct (collection-active-spans-covered-p objects machine regions)
                   :in-theory (disable proof-covered-p proof-remove-region-span)))))

(local
 (defun collection-debit-active-spans (objects machine regions)
   (if (endp objects)
       regions
     (let ((object (car objects)))
       (collection-debit-active-spans
        (cdr objects) machine
        (if (eq (proof-object-zone object) :active)
            (proof-remove-region-span (proof-object-address object)
                                      (proof-object-size object machine) regions)
          regions))))))

(local
 (defthm collection-extracted-footprint-bounded-by-region-bytes
   (implies (and (collection-separated-objects-p pending machine)
                 (collection-active-spans-covered-p pending machine regions))
            (<= (collection-pending-bytes
                 (collection-published-object-graph pending base objects machine))
                (collection-region-bytes regions)))
   :rule-classes nil
   :hints (("Goal" :induct (collection-debit-active-spans pending machine regions)
                   :in-theory (disable proof-covered-p proof-remove-region-span
                                       collection-region-bytes proof-header-size
                                       collection-reference-fields
                                       collection-removal-debits-region-bytes))
           ("Subgoal *1/2"
            :use ((:instance collection-removal-debits-region-bytes
                             (base (proof-object-address (car pending)))
                             (size (proof-object-size (car pending) machine))))))))

(local
 (in-theory (disable proof-subspan-p proof-covered-p
                     proof-heap-object-spans-p proof-heap-layout-p
                     proof-world-reg proof-reg proof-world-machine proof-world-regions
                     proof-world-stop proof-world-page-size proof-page-size-p proof-regions-p
                     proof-static-size proof-disjoint-p proof-spaces-end proof-stack-base
                     proof-stack-end proof-stack-limit proof-stack-top proof-machine-limit
                     boymoo-model::a64-sp
                     mod
                     proof-active-floor proof-active-end proof-cons-floor
                     proof-box-top proof-heap-limit proof-inactive-floor
                     proof-inactive-end proof-runtime-word proof-heap-base)))

(local
 (defthm collection-metadata-word-is-unsigned
   (unsigned-byte-p 64 (proof-runtime-word offset world))
   :hints (("Goal"
            :use ((:instance collection-loaded-word-is-unsigned
                             (address (+ (- (proof-heap-base world) 128) offset))))
            :in-theory (e/d (collection-read-word proof-runtime-word)
                            (collection-loaded-word-is-unsigned
                             boymoo-model::a64-load))))))

(local
 (defthm collection-object-ends-fit-in-active-space
   (implies (proof-heap-layout-p world)
            (and (<= (proof-active-floor world) (proof-cons-floor world))
                 (<= (proof-box-top world) (proof-active-end world))
                 (natp (proof-active-floor world))
                 (natp (proof-active-end world))
                 (equal (proof-active-end world)
                        (+ (proof-active-floor world) *proof-space-size*))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-metadata-word-is-unsigned (offset 0))
                  (:instance collection-metadata-word-is-unsigned (offset 8)))
            :in-theory (e/d (proof-heap-layout-p proof-active-floor proof-active-end)
                            (collection-metadata-word-is-unsigned))))))

(local
 (defthm collection-active-spans-covered-by-original-space
   (let ((regions (list (proof-region (proof-active-floor world)
                                       (proof-active-end world) :rw))))
     (implies (and (proof-heap-layout-p world)
                   (proof-heap-object-spans-p objects external world))
              (collection-active-spans-covered-p objects (proof-world-machine world)
                                                  regions)))
   :hints (("Goal" :induct (collection-active-spans-covered-p
                            objects (proof-world-machine world)
                            (list (proof-region (proof-active-floor world)
                                                (proof-active-end world) :rw)))
                   :in-theory (enable proof-heap-object-spans-p proof-covered-p proof-subspan-p))
           ("Subgoal *1/3" :use ((:instance collection-object-ends-fit-in-active-space))))))

(defthm collection-published-graph-fits-four-gibibytes
  (let* ((machine (proof-world-machine world))
         (base (proof-heap-base world))
         (graph (collection-published-object-graph objects base objects machine)))
    (implies (proof-heap-p world objects packages)
             (and (collection-source-records-p graph graph)
                  (<= (collection-pending-bytes graph) *proof-space-size*))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-extracted-footprint-bounded-by-region-bytes
                            (pending objects)
                            (base (proof-heap-base world))
                            (machine (proof-world-machine world))
                            (regions (list (proof-region (proof-active-floor world)
                                                        (proof-active-end world) :rw))))
                 (:instance collection-active-spans-covered-by-original-space
                            (external (cdr (proof-external-objects
                                            (proof-external-head world)
                                            (len objects) world objects))))
                 (:instance collection-object-map-has-separated-spans
                            (pending objects) (symbols nil) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance collection-extracted-graph-is-source-consistent
                            (pending objects) (symbols nil) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance collection-object-ends-fit-in-active-space))
           :in-theory (disable collection-published-object-graph
                               collection-pending-bytes proof-object-map-p
                               collection-source-records-p proof-static-p
                               proof-external-objects proof-dynamic-entries
                               proof-string-accounting-p proof-dynamic-symbol-objects-p
                               proof-stack-prefix collection-active-spans-covered-by-original-space
                               collection-object-map-has-separated-spans
                               collection-extracted-graph-is-source-consistent))))

(local
 (defthm collection-inactive-space-has-matching-capacity
   (implies (proof-heap-layout-p world)
            (and (natp (proof-inactive-floor world))
                 (natp (proof-inactive-end world))
                 (< (proof-inactive-end world) (expt 2 64))
                 (equal (proof-inactive-end world)
                        (+ (proof-inactive-floor world) *proof-space-size*))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-metadata-word-is-unsigned (offset 24))
                  (:instance collection-metadata-word-is-unsigned (offset 32)))
            :in-theory (e/d (proof-inactive-floor proof-inactive-end proof-heap-layout-p)
                            (collection-metadata-word-is-unsigned))))))

(defthm collection-published-traversal-places-disjoint-copies
  (let* ((base (proof-heap-base world))
         (graph (collection-published-object-graph
                 objects base objects (proof-world-machine world)))
         (roots (collection-published-roots world objects))
         (lower (proof-inactive-floor world))
         (upper (proof-inactive-end world))
         (work (collection-traverse roots graph lower upper)))
    (implies (proof-heap-p world objects packages)
             (collection-destinations-p first second work graph lower upper)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-published-graph-fits-four-gibibytes)
                 (:instance collection-inactive-space-has-matching-capacity)
                 (:instance collection-traversal-places-moved-copies-in-disjoint-spans
                            (graph (collection-published-object-graph
                                    objects (proof-heap-base world) objects
                                    (proof-world-machine world)))
                            (roots (collection-published-roots world objects))
                            (floor (proof-inactive-floor world))
                            (end (proof-inactive-end world))))
           :in-theory (disable collection-published-object-graph collection-published-roots
                               collection-destinations-p collection-traverse
                               collection-source-records-p collection-pending-bytes
                               proof-object-map-p
                               collection-traversal-places-moved-copies-in-disjoint-spans))))
