(in-package "BOYMOO-PROOFS")

(include-book "heap-locality")
(include-book "representation")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm allocation-object-extent-is-positive
   (posp (proof-object-size object machine))
   :rule-classes :type-prescription
   :hints (("Goal"
            :use ((:instance allocation-align-up-bounds (alignment 8)
                   (size (proof-header-size (proof-load-word (proof-object-address object) machine)))))
            :in-theory (disable proof-load-word proof-header-size proof-align-up)))))

(local
 (defthm allocation-object-extent-includes-a-word
   (<= 8 (proof-object-size object machine))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable proof-load-word proof-header-size)))))

(local
 (defthm allocation-disjoint-positive-span-excludes-address
   (implies (and (proof-object-disjoint-p address (+ address bytes) objects machine) (posp bytes))
            (not (assoc-equal address objects)))
   :hints (("Goal" :induct (proof-object-disjoint-p address (+ address bytes) objects machine)
            :in-theory (disable proof-object-size)))))

(defthm allocation-record-in-published-map
  (implies (and (proof-object-map-p pending objects symbols base packages machine)
                (member-equal record pending))
           (and (equal (assoc-equal (proof-object-address record) pending) record)
                (proof-object-record-p record)
                (proof-span-p (proof-object-address record) 8)
                (proof-object-view record base objects packages machine)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
           :in-theory (disable proof-object-record-p proof-object-size proof-view
                               proof-symbol-object-p proof-object-disjoint-p proof-object-word))))

(local
 (defthm allocation-successful-symbol-step-checks-size
   (let* ((address (proof-pointer-address word base))
          (header (proof-load-word address machine)))
     (implies (and (not (oddp word)) (equal (proof-word-tag word) 2)
                   (equal (proof-header-type header) 2)
                   (proof-view-step :word word 0 depth base objects packages machine))
              (equal (proof-header-size header) 16)))
   :rule-classes nil
   :hints (("Goal"
            :expand ((proof-view-step :word word 0 depth base objects packages machine))
            :in-theory (disable (:definition proof-view-step) proof-header-size proof-header-type
                                proof-word-tag proof-pointer-address proof-load-word oddp mod)))))

(defthm allocation-valid-symbol-has-two-fields
  (let ((address (proof-object-address record)))
    (implies (and (proof-object-record-p record)
                  (proof-span-p address 8)
                  (unsigned-byte-p 64 base) (equal (mod base 8) 0)
                  (equal (assoc-equal address objects) record)
                  (proof-symbol-object-p record machine)
                  (proof-object-view record base objects packages machine))
             (equal (proof-header-size (proof-load-word address machine)) 16)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-tagged-offset-round-trip (address (proof-object-address record)) (tag 2))
                 (:instance allocation-successful-symbol-step-checks-size
                  (word (proof-object-word record base))
                  (depth (1+ (nfix (proof-object-rank record))))))
           :in-theory (disable (:definition proof-view-step) proof-header-size proof-header-type
                               proof-cons-value proof-symbol-value proof-load-word proof-integer-view
                               proof-pointer-address proof-word-tag proof-load-string proof-span-p
                               proof-limb-magnitude proof-limbs-p proof-rational-value proof-complex-value
                               mod oddp boymoo-model::a64-unsigned allocation-unsigned-64-of-difference))))

(local
 (defthm allocation-first-pending-record-in-table
   (implies (and (consp pending) (subsetp-equal pending objects))
            (member-equal (car pending) objects))))

(local
 (defthm allocation-symbol-object-kind
   (implies (proof-symbol-object-p object machine)
            (equal (proof-object-kind object) :header))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-load-word proof-header-type)))))

(defthm allocation-home-bindings-after-disjoint-static-write
  (let ((changed (boymoo-model::a64-store bytes start value machine)))
    (implies (and (proof-span-p start bytes)
                  (unsigned-byte-p 64 base) (equal (mod base 8) 0)
                  (allocation-objects-outside-write-p start (+ start bytes) objects machine)
                  (proof-object-map-p objects objects nil base packages machine)
                  (subsetp-equal pending objects))
             (equal (proof-home-bindings-p pending base objects packages changed buckets)
                    (proof-home-bindings-p pending base objects packages machine buckets))))
  :rule-classes nil
  :hints (("Goal" :induct (len pending)
           :expand ((:free (state) (proof-home-bindings-p pending base objects packages state buckets)))
           :in-theory (disable (:definition proof-home-bindings-p) proof-symbol-object-p proof-object-word
                               proof-static-binding proof-view proof-object-size proof-load-word
                               proof-object-map-p proof-span-p allocation-objects-outside-write-p boymoo-model::a64-store mod))
          ("Subgoal *1/1"
           :use ((:instance allocation-record-in-published-map (pending objects) (symbols nil) (record (car pending)))
                 (:instance allocation-symbol-object-kind (object (car pending)))
                 (:instance allocation-valid-symbol-has-two-fields (record (car pending)))
                 (:instance allocation-two-header-fields-after-write (address (proof-object-address (car pending))))
                 (:instance allocation-lookup-object-outside-write
                  (address (proof-object-address (car pending))) (end (+ start bytes)))
                 (:instance allocation-object-size-after-disjoint-write (object (car pending))))
           :in-theory (e/d (allocation-write-disjoint-from-objects-p)
                           ((:definition proof-home-bindings-p) proof-symbol-object-p proof-object-word
                            proof-static-binding proof-view proof-object-size proof-load-word proof-header-size
                            proof-object-record-p proof-span-p proof-disjoint-p proof-object-map-p
                            allocation-two-header-fields-after-write allocation-objects-outside-write-p
                            boymoo-model::a64-store mod)))))

(defthm allocation-static-spans-after-disjoint-range-write
  (implies (and (proof-static-spans-p pending base size machine)
                (proof-span-p start bytes)
                (proof-disjoint-p start (+ start bytes) base (+ base size)))
           (and (allocation-objects-outside-write-p start (+ start bytes) pending machine)
                (proof-static-spans-p pending base size (boymoo-model::a64-store bytes start value machine))))
  :rule-classes nil
  :hints (("Goal" :induct (proof-static-spans-p pending base size machine)
           :in-theory (disable proof-object-size boymoo-model::a64-store))
          ("Subgoal *1/2" :use ((:instance allocation-object-size-after-disjoint-write (object (car pending)))))))

(local
 (defthm allocation-subset-under-table-extension
   (implies (subsetp-equal pending objects)
            (subsetp-equal pending (cons object objects)))
   :hints (("Goal" :induct (subsetp-equal pending objects)))))

(local
 (defthm allocation-table-subset-of-itself
   (subsetp-equal objects objects)))

(defthm allocation-static-after-disjoint-range-write
  (let ((size (proof-static-size base machine)))
    (implies (and (proof-static-p base objects packages machine)
                  (proof-span-p start bytes)
                  (proof-disjoint-p start (+ start bytes) base (+ base size)))
             (proof-static-p base objects packages (boymoo-model::a64-store bytes start value machine))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-static-spans-after-disjoint-range-write
                  (pending (proof-static-objects objects)) (size (proof-static-size base machine)))
                 (:instance allocation-object-map-after-disjoint-write
                  (pending (proof-static-objects objects)) (objects (proof-static-objects objects)) (symbols nil))
                 (:instance allocation-home-bindings-after-disjoint-static-write
                  (pending (proof-static-objects objects)) (objects (proof-static-objects objects))
                  (buckets (cdr (proof-view (proof-load-word (+ base 16) machine)
                                            base (proof-static-objects objects) packages machine))))
                 (:instance allocation-load-word-after-disjoint-write (address base))
                 (:instance allocation-load-word-after-disjoint-write (address (+ 8 base)))
                 (:instance allocation-load-word-after-disjoint-write (address (+ 16 base))))
           :in-theory (disable proof-static-objects proof-static-spans-p proof-object-map-p
                               proof-home-bindings-p proof-view proof-packages-p proof-load-word
                               proof-static-buckets-p proof-package-bindings-p
                               allocation-objects-outside-write-p boymoo-model::a64-store mod))))
