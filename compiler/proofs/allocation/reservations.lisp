(in-package "BOYMOO-PROOFS")

(include-book "runtime-contracts")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-static-end-below-box-top
  (implies (proof-heap-layout-p world)
           (let ((end (+ (proof-heap-base world)
                         (proof-static-size (proof-heap-base world) (proof-world-machine world)))))
             (and (<= end (proof-active-floor world)) (<= end (proof-box-top world)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-align-up-bounds
                  (size (+ (proof-heap-base world)
                           (proof-static-size (proof-heap-base world) (proof-world-machine world))))
                  (alignment *proof-runtime-page*)))
           :in-theory (disable proof-align-up proof-covered-p proof-regions-p proof-disjoint-p mod))))

(defthm allocation-cell-frontier-below-spaces-end
  (implies (proof-heap-layout-p world)
           (<= (proof-cons-floor world) (proof-spaces-end world)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-align-up proof-covered-p proof-regions-p proof-disjoint-p mod))))

(defun allocation-external-spans-avoid-p (start end headers machine)
  (if (atom headers)
      t
    (let* ((address (car headers))
           (length (proof-header-size (proof-load-word address machine)))
           (size (max 16 (+ 8 (proof-align-up length 8)))))
      (and (proof-disjoint-p start end address (+ address size))
           (allocation-external-spans-avoid-p start end (cdr headers) machine)))))

(defthm allocation-external-object-disjoint-from-avoided-span
  (implies (and (allocation-external-spans-avoid-p start end headers machine)
                (member-equal (proof-object-address object) headers))
           (proof-disjoint-p start end (proof-object-address object)
                             (+ (proof-object-address object) (proof-object-size object machine))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-external-spans-avoid-p start end headers machine)
           :in-theory (disable proof-align-up proof-header-size proof-load-word))))

(local
 (defthm allocation-external-record-disjoint-in-its-mapping
   (implies (and (natp length)
                 (proof-disjoint-p start end head (+ head (proof-align-up (+ 32 length) *proof-runtime-page*))))
            (proof-disjoint-p start end (+ 24 head)
                              (+ 24 head (max 16 (+ 8 (proof-align-up length 8))))))
   :hints (("Goal" :use allocation-external-record-fits-mapping
            :in-theory (disable proof-align-up)))))

(defthm allocation-listed-external-spans-avoid-heap-span
  (let* ((mappings (proof-external-objects head fuel world objects))
         (machine (proof-world-machine world)))
    (implies (and mappings
                  (<= (- (proof-heap-base world) *proof-heap-prefix*) start)
                  (<= end (proof-spaces-end world)))
             (allocation-external-spans-avoid-p start end (cdr mappings) machine)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel world objects)
           :in-theory (disable proof-align-up proof-header-type proof-header-size proof-load-word
                               proof-heap-base proof-spaces-end proof-stack-base proof-stack-end
                               proof-machine-limit proof-object-kind proof-object-zone))
          ("Subgoal *1/2"
           :use ((:instance allocation-external-record-fits-mapping
                    (length (proof-header-size (proof-load-word (+ 24 head) (proof-world-machine world)))))))))

(defthm allocation-object-spans-avoid-gap-or-prefix
  (let* ((machine (proof-world-machine before))
         (base (proof-heap-base before))
         (size (proof-static-size base machine)))
    (implies (and (proof-heap-object-spans-p pending external before)
                  (proof-static-spans-p (proof-static-objects pending) base size machine)
                  (allocation-external-spans-avoid-p start end external machine)
                  (or (and (<= (+ base size) start)
                           (<= (proof-box-top before) start)
                           (<= end (proof-cons-floor before)))
                      (and (<= end base)
                           (<= base (proof-active-floor before))
                           (<= base (proof-cons-floor before)))))
             (proof-object-disjoint-p start end pending machine)))
  :rule-classes nil
  :hints (("Goal" :induct (len pending)
           :expand ((proof-heap-object-spans-p pending external before)
                    (proof-object-disjoint-p start end pending (proof-world-machine before)))
           :in-theory (disable allocation-external-spans-avoid-p proof-object-size mod
                               proof-active-floor proof-active-end proof-cons-floor proof-heap-base))
          ("Subgoal *1/1"
           :use ((:instance allocation-external-object-disjoint-from-avoided-span
                    (object (car pending)) (headers external) (machine (proof-world-machine before)))))))

(defthm allocation-heap-span-facts-for-reservations
  (let* ((base (proof-heap-base world))
         (machine (proof-world-machine world))
         (mappings (proof-external-objects (proof-external-head world) (len objects) world objects)))
    (implies (proof-heap-p world objects packages)
             (and mappings
                  (proof-static-spans-p (proof-static-objects objects) base (proof-static-size base machine) machine)
                  (proof-heap-object-spans-p objects (cdr mappings) world))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-heap-layout-p proof-static-spans-p proof-static-objects
                                     proof-static-size proof-object-map-p proof-external-objects
                                     proof-heap-object-spans-p proof-string-accounting-p
                                     proof-stack-prefix proof-dynamic-entries proof-dynamic-view
                                     proof-dynamic-symbol-objects-p proof-home-bindings-p
                                     proof-package-bindings-p proof-packages-p proof-static-buckets-p
                                     proof-package-row-views proof-value-p proof-view mod))))

(defthm allocation-free-span-disjoint-from-published-objects
  (implies (and (proof-heap-p before objects packages)
                (<= (proof-box-top before) start)
                (<= end (proof-cons-floor before)))
           (proof-object-disjoint-p start end objects (proof-world-machine before)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world before))
                 (:instance allocation-static-end-below-box-top (world before))
                 (:instance allocation-cell-frontier-below-spaces-end (world before))
                 (:instance allocation-heap-span-facts-for-reservations (world before))
                 (:instance allocation-listed-external-spans-avoid-heap-span
                  (world before) (head (proof-external-head before)) (fuel (len objects)))
                 (:instance allocation-object-spans-avoid-gap-or-prefix (pending objects)
                  (external (cdr (proof-external-objects (proof-external-head before)
                                                         (len objects) before objects)))))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-object-disjoint-p proof-object-size
                               proof-static-objects proof-static-spans-p proof-external-objects
                               allocation-external-spans-avoid-p proof-heap-object-spans-p
                               proof-heap-base proof-spaces-end proof-cons-floor proof-box-top))))

(defthm allocation-prefix-span-disjoint-from-published-objects
  (implies (and (proof-heap-p before objects packages)
                (<= (- (proof-heap-base before) *proof-heap-prefix*) start)
                (<= end (proof-heap-base before)))
           (proof-object-disjoint-p start end objects (proof-world-machine before)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world before))
                 (:instance allocation-static-end-below-box-top (world before))
                 (:instance allocation-cell-frontier-below-spaces-end (world before))
                 (:instance allocation-heap-span-facts-for-reservations (world before))
                 allocation-growth-layout-facts
                 (:instance allocation-listed-external-spans-avoid-heap-span
                  (world before) (head (proof-external-head before)) (fuel (len objects)))
                 (:instance allocation-object-spans-avoid-gap-or-prefix (pending objects)
                  (external (cdr (proof-external-objects (proof-external-head before)
                                                         (len objects) before objects)))))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-object-disjoint-p proof-object-size
                               proof-static-objects proof-static-spans-p proof-external-objects
                               allocation-external-spans-avoid-p proof-heap-object-spans-p
                               proof-heap-base proof-spaces-end proof-cons-floor proof-box-top))))
