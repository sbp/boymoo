(in-package "BOYMOO-PROOFS")

(include-book "heap-update")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-heap-layout-p proof-heap-object-spans-p proof-heap-base
                    proof-static-p proof-static-size proof-static-spans-p proof-static-objects
                    proof-active-floor proof-active-end proof-box-top proof-cons-floor proof-spaces-end
                    proof-external-objects proof-external-head proof-world-machine
                    proof-object-map-p proof-object-disjoint-p proof-object-record-p proof-object-size
                    proof-span-p proof-subspan-p proof-disjoint-p proof-align-up expt))

(local
 (defthm generated-distinct-object-map-looks-up-each-record
   (implies (and (consp object) (member-equal object objects) (generated-distinct-object-addresses-p objects))
            (equal (assoc-equal (proof-object-address object) objects) object))
   :hints (("Goal" :induct (len objects)
                   :in-theory (enable generated-distinct-object-addresses-p proof-object-address)))))

(local
 (defthm generated-mapped-record-is-consp
   (implies (proof-object-record-p object) (consp object))
   :hints (("Goal" :in-theory (enable proof-object-record-p)))))

(local
 (defthm generated-heap-base-is-nonnegative
   (natp (proof-heap-base world))
   :hints (("Goal" :in-theory (enable proof-heap-base)))
   :rule-classes :type-prescription))

(local
 (defthm generated-static-span-size-is-nonnegative
   (natp (proof-static-size base machine))
   :hints (("Goal" :in-theory (enable proof-static-size)))
   :rule-classes :type-prescription))

(local
 (defthm generated-main-heap-includes-static-and-active-ranges
   (let ((base (proof-heap-base before)) (end (proof-spaces-end before)))
     (implies (proof-heap-layout-p before)
              (and (<= (+ base (proof-static-size base (proof-world-machine before))) end)
                   (<= (- base *proof-heap-prefix*) (proof-active-floor before))
                   (<= (- base *proof-heap-prefix*) (proof-cons-floor before))
                   (<= (proof-box-top before) end)
                   (<= (proof-active-end before) end))))
   :hints (("Goal" :in-theory (enable proof-heap-layout-p)))
   :rule-classes nil))

(local
 (defthm generated-heap-record-is-disjoint-from-stack-write
   (let* ((base (proof-heap-base before)) (machine (proof-world-machine before))
          (external (cdr (proof-external-objects (proof-external-head before) (len objects) before objects)))
          (address (proof-object-address object)) (size (proof-object-size object machine)))
     (implies (and (proof-heap-layout-p before) (generated-runtime-stack-span-p start end before)
                   (consp object) (member-equal object objects) (generated-distinct-object-addresses-p objects)
                   (proof-static-spans-p (proof-static-objects (list object)) base (proof-static-size base machine) machine)
                   (proof-heap-object-spans-p (list object) external before))
              (proof-disjoint-p address (+ address size) start end)))
   :hints (("Goal"
            :use (generated-main-heap-includes-static-and-active-ranges
                  generated-stack-write-disjoint-from-main-heap
                  (:instance generated-external-record-disjoint-from-stack-write
                             (world before) (head (proof-external-head before)) (fuel (len objects))
                             (address (proof-object-address object))))
            :in-theory (enable proof-static-spans-p proof-static-objects proof-heap-object-spans-p
                               proof-subspan-p proof-disjoint-p)))
   :rule-classes nil))

(local
 (defthm generated-one-heap-record-has-required-spans
   (let* ((base (proof-heap-base before)) (machine (proof-world-machine before))
          (external (cdr (proof-external-objects (proof-external-head before) (len objects) before objects)))
          (size (proof-static-size base machine)))
     (implies (and (consp pending)
                   (proof-static-spans-p (proof-static-objects pending) base size machine)
                   (proof-heap-object-spans-p pending external before))
              (and (proof-static-spans-p (proof-static-objects (list (car pending))) base size machine)
                   (proof-static-spans-p (proof-static-objects (cdr pending)) base size machine)
                   (proof-heap-object-spans-p (list (car pending)) external before)
                   (proof-heap-object-spans-p (cdr pending) external before))))
   :hints (("Goal" :in-theory (enable proof-static-objects proof-static-spans-p proof-heap-object-spans-p)))
   :rule-classes nil))

(local
 (defthm generated-heap-records-are-disjoint-from-stack-write
   (let* ((base (proof-heap-base before)) (machine (proof-world-machine before))
          (external (cdr (proof-external-objects (proof-external-head before) (len objects) before objects))))
     (implies (and (proof-heap-layout-p before) (generated-runtime-stack-span-p start end before)
                   (subsetp-equal pending objects) (generated-distinct-object-addresses-p objects)
                   (proof-static-spans-p (proof-static-objects pending) base (proof-static-size base machine) machine)
                   (proof-heap-object-spans-p pending external before)
                   (proof-object-map-p objects objects nil base packages machine))
              (proof-object-disjoint-p start end pending machine)))
   :hints (("Goal" :induct (len pending) :in-theory (enable proof-object-disjoint-p))
           ("Subgoal *1/1"
            :use (generated-one-heap-record-has-required-spans
                  (:instance generated-published-object-has-span-and-view
                             (pending objects) (symbols nil) (object (car pending))
                             (base (proof-heap-base before)) (machine (proof-world-machine before)))
                  (:instance generated-heap-record-is-disjoint-from-stack-write (object (car pending))))
            :in-theory (enable proof-object-disjoint-p proof-disjoint-p subsetp-equal)))
   :rule-classes nil))

(defthm generated-heap-disjoint-from-runtime-stack-write
  (implies (and (proof-heap-p before objects packages) (generated-runtime-stack-span-p start end before))
           (proof-object-disjoint-p start end objects (proof-world-machine before)))
  :hints (("Goal"
           :use ((:instance generated-heap-records-are-disjoint-from-stack-write (pending objects))
                 (:instance generated-published-object-addresses-are-distinct
                            (pending objects) (symbols nil) (base (proof-heap-base before))
                            (machine (proof-world-machine before))))
           :in-theory (enable proof-heap-p proof-static-p)))
  :rule-classes nil)

(defthm generated-stack-update-preserves-heap-with-valid-roots
  (implies (and (proof-heap-p before objects packages)
                (generated-stack-update-p start end before after)
                (proof-stack-prefix (proof-stack-top after) after objects packages))
           (proof-heap-p after objects packages))
  :hints (("Goal" :use (generated-heap-disjoint-from-runtime-stack-write generated-stack-update-preserves-heap)
                  :in-theory (enable generated-stack-update-p)))
  :rule-classes nil)

(defthm generated-stack-update-is-disjoint-from-published-objects
  (implies (and (proof-heap-p before objects packages)
                (generated-stack-update-p start end before after))
           (proof-object-disjoint-p start end objects (proof-world-machine before)))
  :hints (("Goal" :use generated-heap-disjoint-from-runtime-stack-write
                  :in-theory (enable generated-stack-update-p)))
  :rule-classes nil)
