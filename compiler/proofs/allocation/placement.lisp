(in-package "BOYMOO-PROOFS")

(include-book "large-heap")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm allocation-placement-external-end
   (equal (proof-external-objects 0 fuel world objects) '(:mappings))))

(defthm allocation-external-objects-avoid-fresh-or-stack-span
  (let* ((machine (proof-world-machine world))
         (mappings (proof-external-objects head fuel world objects))
         (machine-start (- (proof-machine-limit world) *proof-machine-margin*))
         (machine-end (+ machine-start *proof-machine-reservation*)))
    (implies (and mappings
                  (or (proof-region-disjoint-p start end (proof-world-regions world))
                      (and (<= (proof-stack-base world) start) (<= end (proof-stack-end world)))
                      (and (<= machine-start start) (<= end machine-end))))
             (allocation-external-spans-avoid-p start end (cdr mappings) machine)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel world objects)
           :expand ((proof-external-objects head fuel world objects))
           :in-theory (disable (:definition proof-external-objects) proof-align-up proof-header-type proof-header-size
                               proof-load-word proof-heap-base proof-spaces-end proof-stack-base proof-stack-end
                               proof-machine-limit proof-object-kind proof-object-zone proof-region-disjoint-p))
          ("Subgoal *1/2"
           :use ((:instance allocation-listed-region-avoids-fresh-mapping
                  (lower head) (upper (+ head (proof-load-word (+ 8 head) (proof-world-machine world))))
                  (regions (proof-world-regions world)) (mode :rw))
                 (:instance allocation-external-record-fits-mapping
                  (length (proof-header-size (proof-load-word (+ 24 head) (proof-world-machine world)))))))))

(defthm allocation-static-and-active-intervals-in-heap
  (let* ((base (proof-heap-base world))
         (size (proof-static-size base (proof-world-machine world)))
         (lower (- base *proof-heap-prefix*))
         (upper (proof-spaces-end world)))
    (implies (proof-heap-layout-p world)
             (and (<= lower (+ base 32))
                  (<= (+ base size) upper)
                  (<= lower (proof-active-floor world))
                  (<= lower (proof-cons-floor world))
                  (<= (proof-box-top world) upper)
                  (<= (proof-active-end world) upper))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-layout-storage-spans allocation-static-end-below-box-top)
           :in-theory (disable proof-align-up proof-covered-p proof-regions-p proof-disjoint-p
                               proof-static-size proof-active-end proof-cons-floor proof-active-floor
                               proof-heap-base proof-spaces-end mod))))

(local
 (defthm allocation-object-spans-avoid-outside-heap
   (let* ((machine (proof-world-machine world))
          (base (proof-heap-base world)))
     (implies (and (proof-heap-object-spans-p pending headers world)
                   (proof-static-spans-p (proof-static-objects pending) base
                                        (proof-static-size base machine) machine)
                   (allocation-external-spans-avoid-p start end headers machine)
                   (proof-disjoint-p start end lower upper)
                   (<= lower (+ base 32))
                   (<= (+ base (proof-static-size base machine)) upper)
                   (<= lower (proof-active-floor world))
                   (<= lower (proof-cons-floor world))
                   (<= (proof-box-top world) upper)
                   (<= (proof-active-end world) upper))
              (proof-object-disjoint-p start end pending machine)))
   :rule-classes nil
   :hints (("Goal" :induct (len pending)
            :expand ((proof-heap-object-spans-p pending headers world)
                     (proof-object-disjoint-p start end pending (proof-world-machine world)))
            :in-theory (disable allocation-external-spans-avoid-p proof-object-size proof-heap-base proof-static-size
                                proof-active-floor proof-active-end proof-cons-floor proof-box-top mod))
           ("Subgoal *1/1"
            :use ((:instance allocation-external-object-disjoint-from-avoided-span
                   (object (car pending)) (machine (proof-world-machine world))))))))

(defthm allocation-published-objects-avoid-fresh-or-stack-span
  (let* ((machine (proof-world-machine world))
         (base (proof-heap-base world))
         (machine-start (- (proof-machine-limit world) *proof-machine-margin*))
         (machine-end (+ machine-start *proof-machine-reservation*)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-disjoint-p start end (- base *proof-heap-prefix*) (proof-spaces-end world))
                  (or (proof-region-disjoint-p start end (proof-world-regions world))
                      (and (<= (proof-stack-base world) start) (<= end (proof-stack-end world)))
                      (and (<= machine-start start) (<= end machine-end))))
             (allocation-objects-outside-write-p start end objects machine)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-layout-of-heap allocation-heap-published-map allocation-heap-span-facts-for-reservations
                 allocation-static-and-active-intervals-in-heap
                 (:instance allocation-external-objects-avoid-fresh-or-stack-span
                  (head (proof-external-head world)) (fuel (len objects)))
                 (:instance allocation-object-spans-avoid-outside-heap
                  (lower (- (proof-heap-base world) *proof-heap-prefix*)) (upper (proof-spaces-end world))
                  (pending objects)
                  (headers (cdr (proof-external-objects (proof-external-head world) (len objects) world objects))))
                 (:instance allocation-object-map-with-disjoint-spans
                  (pending objects) (symbols nil) (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-external-objects proof-heap-object-spans-p
                               proof-static-spans-p proof-static-objects proof-external-head proof-object-map-p
                               proof-region-disjoint-p proof-object-disjoint-p allocation-objects-outside-write-p
                               allocation-external-spans-avoid-p proof-disjoint-p))))
