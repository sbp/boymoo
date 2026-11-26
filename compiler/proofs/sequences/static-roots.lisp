(in-package "BOYMOO-PROOFS")

(include-book "spine-bounds")
(include-book "heap-objects")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-lookup-address-in-objects
   (implies (assoc-equal address objects)
            (member-equal address (sequence-object-addresses objects)))
   :hints (("Goal" :induct (sequence-object-addresses objects)))))

(local
 (defthm sequence-lookup-selected-in-static-map
   (implies (no-duplicatesp-equal (sequence-object-addresses objects))
            (equal (assoc-equal address (proof-static-objects objects))
                   (let ((object (assoc-equal address objects)))
                     (and (eq (proof-object-zone object) :static) object))))
   :hints (("Goal" :induct (proof-static-objects objects)))))

(local
 (defthm sequence-static-members-are-records
   (implies (member-equal object (proof-static-objects objects))
            (consp object))
   :hints (("Goal" :induct (proof-static-objects objects)))
   :rule-classes :forward-chaining))

(local
 (defthm sequence-static-objects-form-an-alist
   (alistp (proof-static-objects objects))
   :hints (("Goal" :induct (proof-static-objects objects)))))

(local
 (defthm sequence-member-record-is-found
   (implies (and (alistp objects) (consp object) (member-equal object objects))
            (assoc-equal (proof-object-address object) objects))
   :hints (("Goal" :induct (member-equal object objects)))
   :rule-classes nil))

(local
 (defthm sequence-static-lookups-agree-on-pending
   (implies (and (no-duplicatesp-equal (sequence-object-addresses objects))
                 (subsetp-equal pending (proof-static-objects objects)))
            (sequence-object-lookups-agree-p pending (proof-static-objects objects) objects))
   :hints (("Goal" :induct (len pending)
                   :in-theory (disable proof-static-objects))
           ("Subgoal *1/1" :use ((:instance sequence-member-record-is-found
                                           (object (car pending))
                                           (objects (proof-static-objects objects))))))
   :rule-classes nil))

(defthm sequence-static-lookups-agree-with-heap
  (implies (proof-heap-p world objects packages)
           (sequence-object-lookups-agree-p (proof-static-objects objects)
                                            (proof-static-objects objects) objects))
  :hints
  (("Goal"
    :in-theory (disable proof-object-map-p proof-heap-layout-p proof-static-p proof-heap-object-spans-p
                        proof-string-accounting-p proof-dynamic-view proof-dynamic-entries
                        proof-dynamic-symbol-objects-p proof-stack-prefix proof-external-objects
                        proof-static-objects sequence-object-lookups-agree-p)
    :use ((:instance sequence-static-lookups-agree-on-pending
                     (pending (proof-static-objects objects)))
          (:instance sequence-distinct-published-addresses
                     (pending objects) (symbols nil) (base (proof-heap-base world))
                     (machine (proof-world-machine world))))))
  :rule-classes nil)

(defthm sequence-value-in-agreeing-object-map
  (implies (and (proof-value-p word datum base objects packages machine)
                (sequence-object-lookups-agree-p objects objects extended))
           (proof-value-p word datum base extended packages machine))
  :hints
  (("Goal"
    :in-theory (e/d (proof-value-p proof-view)
                    (proof-view-step sequence-object-lookups-agree-p))
    :use ((:instance sequence-view-step-on-extended-map
                     (kind :word) (input word) (count 0)
                     (depth (1+ (nfix (proof-object-rank
                                       (assoc-equal (proof-pointer-address word base) objects))))))
          (:instance sequence-value-view-at-its-own-rank
                     (objects extended)
                     (depth (1+ (nfix (proof-object-rank
                                       (assoc-equal (proof-pointer-address word base) objects)))))))))
  :rule-classes nil)

(defthm sequence-static-truth-values-in-heap
  (implies (proof-heap-p world objects packages)
           (and (proof-machine-value-p *proof-nil* nil world objects packages)
                (proof-machine-value-p *proof-t* t world objects packages)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-heap-p proof-static-p proof-machine-value-p)
                    (proof-object-map-p proof-heap-layout-p proof-heap-object-spans-p
                     proof-string-accounting-p proof-dynamic-view proof-dynamic-entries
                     proof-dynamic-symbol-objects-p proof-stack-prefix proof-external-objects
                     proof-static-objects sequence-object-lookups-agree-p
                     proof-static-buckets-p proof-home-bindings-p proof-package-bindings-p
                     proof-static-spans-p proof-packages-p proof-value-p proof-view))
    :use (sequence-static-lookups-agree-with-heap
          (:instance sequence-value-in-agreeing-object-map
                     (word *proof-nil*) (datum nil) (extended objects)
                     (objects (proof-static-objects objects))
                     (base (proof-heap-base world)) (machine (proof-world-machine world)))
          (:instance sequence-value-in-agreeing-object-map
                     (word *proof-t*) (datum t) (extended objects)
                     (objects (proof-static-objects objects))
                     (base (proof-heap-base world)) (machine (proof-world-machine world))))))
  :rule-classes nil)
