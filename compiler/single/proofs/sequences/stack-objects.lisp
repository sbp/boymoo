(in-package "BOYMOO-PROOFS")

(include-book "stack-external")
(include-book "heap-objects")
(include-book "heap-bounds")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-static-p proof-heap-object-spans-p
                    proof-static-spans-p proof-object-map-p proof-object-size
                    proof-static-size proof-world-machine proof-heap-layout-p
                    proof-external-objects proof-regions-p))

(defthm sequence-heap-layout-from-heap
  (implies (proof-heap-p world objects packages)
           (proof-heap-layout-p world))
  :hints (("Goal" :in-theory (enable proof-heap-p)))
  :rule-classes :forward-chaining)

(local
 (defthm sequence-mapped-object-is-span
   (implies (and (proof-object-map-p pending objects symbols base packages machine)
                 (member-equal object pending))
            (proof-span-p (proof-object-address object) (proof-object-size object machine)))
   :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
                   :in-theory (e/d ((:induction proof-object-map-p))
                                   (proof-span-p proof-object-record-p proof-object-view
                                    proof-symbol-object-p proof-object-disjoint-p))
                   :expand ((proof-object-map-p pending objects symbols base packages machine))))
   :rule-classes nil))

(local
 (defthm sequence-dynamic-object-placement
   (let* ((address (proof-object-address object))
          (size (proof-object-size object (proof-world-machine world))))
     (implies (and (member-equal object pending)
                   (proof-heap-object-spans-p pending external world))
              (case (proof-object-zone object)
                (:static t)
                (:active
                 (if (eq (proof-object-kind object) :cons)
                     (proof-subspan-p address size (proof-cons-floor world) (proof-active-end world))
                   (proof-subspan-p address size (proof-active-floor world) (proof-box-top world))))
                (:external (member-equal address external))
                (otherwise nil))))
   :hints (("Goal" :induct (len pending)
                   :in-theory (disable proof-subspan-p)
                   :expand ((proof-heap-object-spans-p pending external world))))
   :rule-classes nil))

(local
 (defthm sequence-active-allocation-order
   (implies (proof-heap-layout-p world)
            (and (<= (proof-active-floor world) (proof-cons-floor world))
                 (<= (proof-box-top world) (proof-active-end world))))
   :hints (("Goal" :in-theory (enable proof-heap-layout-p)))
   :rule-classes nil))

(defthm sequence-object-placement-in-heap
  (let* ((machine (proof-world-machine world))
         (base (proof-heap-base world))
         (address (proof-object-address object))
         (size (proof-object-size object machine))
         (external (proof-external-objects (proof-external-head world) (len objects) world objects)))
    (implies (and (proof-heap-p world objects packages) (member-equal object objects))
             (and (proof-span-p address size)
                  (if (eq (proof-object-zone object) :external)
                      (member-equal address (cdr external))
                    (proof-subspan-p address size (- base *proof-heap-prefix*)
                                     (proof-spaces-end world))))))
  :hints
  (("Goal"
    :expand ((proof-heap-p world objects packages)
             (proof-static-p (proof-heap-base world) objects packages
                             (proof-world-machine world)))
    :in-theory (disable proof-stack-prefix proof-string-accounting-p proof-dynamic-symbol-objects-p
                        proof-dynamic-entries proof-dynamic-view proof-static-buckets-p
                        proof-home-bindings-p proof-package-bindings-p proof-packages-p
                        proof-value-p proof-view)
    :use (sequence-heap-layout-bounds sequence-active-allocation-order
          (:instance sequence-mapped-object-is-span
                     (pending objects) (symbols nil) (base (proof-heap-base world))
                     (machine (proof-world-machine world)))
          (:instance sequence-dynamic-object-placement
                     (pending objects)
                     (external (cdr (proof-external-objects (proof-external-head world)
                                                           (len objects) world objects))))
          (:instance sequence-static-span-of-member
                     (statics (proof-static-objects objects)) (base (proof-heap-base world))
                     (size (proof-static-size (proof-heap-base world) (proof-world-machine world)))
                     (machine (proof-world-machine world))))))
  :rule-classes nil)

(local
 (defthm sequence-stack-write-keeps-object-storage
   (let* ((first (proof-world-machine before))
          (last (proof-world-machine after))
          (address (proof-object-address object))
          (size (proof-object-size object first)))
     (implies (and (proof-heap-p before objects packages)
                   (sequence-stack-write-p start end before after)
                   (member-equal object objects))
              (and (proof-span-p address size)
                   (sequence-machine-span-agrees-p address (+ address size) first last))))
   :hints
   (("Goal"
     :in-theory (disable proof-span-p proof-disjoint-p)
     :use ((:instance sequence-object-placement-in-heap (world before))
           sequence-stack-write-keeps-heap-spans
           (:instance sequence-external-object-agrees-after-stack-write
                      (head (proof-external-head before)) (fuel (len objects)))
           (:instance sequence-machine-agreement-on-subinterval
                      (first (proof-world-machine before)) (last (proof-world-machine after))
                      (lower (- (proof-heap-base before) *proof-heap-prefix*))
                      (upper (proof-spaces-end before))
                      (start (proof-object-address object))
                      (end (+ (proof-object-address object)
                              (proof-object-size object (proof-world-machine before))))))))
   :rule-classes nil))

(local
 (defthm sequence-stack-write-keeps-storage-of-pending
   (let ((first (proof-world-machine before))
         (last (proof-world-machine after)))
     (implies (and (proof-heap-p before objects packages)
                   (sequence-stack-write-p start end before after)
                   (subsetp-equal pending objects))
              (sequence-object-storage-agrees-p pending first last)))
   :hints
   (("Goal"
     :in-theory (disable proof-span-p)
     :induct (len pending)
     :expand ((sequence-object-storage-agrees-p pending (proof-world-machine before)
                                               (proof-world-machine after))))
    ("Subgoal *1/1"
     :use ((:instance sequence-stack-write-keeps-object-storage (object (car pending))))))
   :rule-classes nil))

(defthm sequence-stack-write-keeps-published-storage
  (implies (and (proof-heap-p before objects packages)
                (sequence-stack-write-p start end before after))
           (sequence-object-storage-agrees-p objects
                                             (proof-world-machine before)
                                             (proof-world-machine after)))
  :hints (("Goal" :use ((:instance sequence-stack-write-keeps-storage-of-pending
                                   (pending objects)))))
  :rule-classes nil)

(defthm sequence-object-spans-on-agreed-storage
  (implies (and (sequence-heap-registers-agree-p before after)
                (sequence-heap-metadata-agrees-p before after)
                (sequence-object-storage-agrees-p pending
                                                  (proof-world-machine before)
                                                  (proof-world-machine after)))
           (equal (proof-heap-object-spans-p pending external after)
                  (proof-heap-object-spans-p pending external before)))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-heap-registers-agree-p sequence-heap-metadata-agrees-p)
                    (proof-span-p proof-subspan-p))
    :induct (len pending)
    :expand ((:free (world) (proof-heap-object-spans-p pending external world))))
   ("Subgoal *1/1"
    :use ((:instance sequence-object-head-on-agreed-storage
                     (first (proof-world-machine before)) (last (proof-world-machine after))))))
  :rule-classes nil)
