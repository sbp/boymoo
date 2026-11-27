(in-package "BOYMOO-PROOFS")

(include-book "word-writes")
(include-book "static-locality")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-word-writes-avoid-subspan
  (implies (and (allocation-word-writes-avoid-span-p writes lower upper)
                (<= lower start) (<= end upper))
           (allocation-word-writes-avoid-span-p writes start end))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-word-writes-avoid-span-p writes lower upper)
           :in-theory (disable proof-span-p))))

(defthm allocation-word-writes-keep-word-in-avoided-span
  (implies (and (allocation-word-writes-avoid-span-p writes lower upper)
                (proof-subspan-p address 8 lower upper) (<= upper *allocation-word-modulus*))
           (equal (proof-load-word address (proof-world-machine (allocation-write-words writes world)))
                  (proof-load-word address (proof-world-machine world))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-word-writes-keep-protected-span
                  (after (allocation-write-words writes world)))
                 (:instance allocation-word-in-agreeing-span
                  (before world) (after (allocation-write-words writes world))))
           :in-theory (e/d (allocation-load-word)
                           (proof-load-word allocation-write-words allocation-word-writes-avoid-span-p
                            proof-memory-span-agrees-p)))))

(local
 (defthm allocation-first-word-after-disjoint-static-write
   (implies (and (proof-span-p start 8) (proof-span-p base size) (<= 8 size)
                 (proof-disjoint-p start (+ start 8) base (+ base size)))
            (equal (proof-load-word base (boymoo-model::a64-store 8 start value machine))
                   (proof-load-word base machine)))
   :hints (("Goal" :use ((:instance allocation-load-word-after-disjoint-write (address base) (bytes 8)))
            :in-theory (disable allocation-load-word-after-disjoint-write proof-load-word boymoo-model::a64-store)))))

(defthm allocation-word-writes-keep-static-area
  (let* ((machine (proof-world-machine world))
         (size (proof-static-size base machine))
         (updated (proof-world-machine (allocation-write-words writes world))))
    (implies (and (proof-static-p base objects packages machine)
                  (allocation-word-writes-avoid-span-p writes base (+ base size)))
             (and (proof-static-p base objects packages updated)
                  (equal (proof-static-size base updated) size))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-write-words writes world)
           :in-theory (disable proof-static-objects proof-static-spans-p proof-object-map-p
                               proof-home-bindings-p proof-view proof-packages-p proof-load-word
                               proof-static-buckets-p proof-package-bindings-p proof-span-p proof-disjoint-p
                               allocation-objects-outside-write-p boymoo-model::a64-store mod))
          ("Subgoal *1/2"
           :use ((:instance allocation-static-after-disjoint-range-write
                  (start (caar writes)) (bytes 8) (value (cdar writes)) (machine (proof-world-machine world)))))))

(defthm allocation-word-writes-keep-stack-views
  (let* ((machine (proof-world-machine world))
         (updated (proof-world-machine (allocation-write-words writes world))))
    (implies (and (allocation-word-writes-outside-objects-p writes objects machine)
                  (proof-span-p address (* 8 count))
                  (allocation-word-writes-avoid-span-p writes address (+ address (* 8 count))))
             (equal (proof-stack-views count address base objects packages updated)
                    (proof-stack-views count address base objects packages machine))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-write-words writes world)
           :in-theory (disable proof-stack-views proof-view allocation-objects-outside-write-p
                               proof-span-p proof-disjoint-p boymoo-model::a64-store))
          ("Subgoal *1/2"
           :use ((:instance allocation-stack-views-after-disjoint-write
                  (start (caar writes)) (bytes 8) (value (cdar writes)) (machine (proof-world-machine world)))))))

(defthm allocation-word-writes-keep-dynamic-symbols
  (let* ((machine (proof-world-machine world))
         (updated (proof-world-machine (allocation-write-words writes world))))
    (implies (allocation-word-writes-outside-objects-p writes objects machine)
             (equal (proof-dynamic-symbol-objects-p objects objects entries base packages updated)
                    (proof-dynamic-symbol-objects-p objects objects entries base packages machine))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-write-words writes world)
           :in-theory (disable proof-dynamic-symbol-objects-p proof-view allocation-objects-outside-write-p
                               proof-span-p boymoo-model::a64-store))))

(local
 (defthm allocation-size-lookup-address
   (implies (assoc-equal address objects)
            (equal (car (assoc-equal address objects)) address))))

(defthm allocation-word-writes-keep-object-size
  (let* ((machine (proof-world-machine world))
         (updated (proof-world-machine (allocation-write-words writes world))))
    (implies (and (allocation-word-writes-outside-objects-p writes objects machine)
                  (assoc-equal address objects))
             (equal (proof-object-size (assoc-equal address objects) updated)
                    (proof-object-size (assoc-equal address objects) machine))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-write-words writes world)
           :in-theory (disable proof-object-size allocation-objects-outside-write-p proof-span-p boymoo-model::a64-store))
          ("Subgoal *1/2"
           :use ((:instance allocation-lookup-object-outside-write
                  (start (caar writes)) (end (+ 8 (caar writes))) (machine (proof-world-machine world)))
                 (:instance allocation-object-size-after-disjoint-write
                  (object (assoc-equal address objects)) (start (caar writes)) (bytes 8)
                  (value (cdar writes)) (machine (proof-world-machine world)))))))

(defthm allocation-word-writes-keep-heap-object-spans
  (let ((machine (proof-world-machine before)))
    (implies (and (proof-object-map-p objects objects nil base packages machine)
                  (subsetp-equal pending objects)
                  (allocation-word-writes-outside-objects-p writes objects machine)
                  (allocation-same-memory-p (proof-world-machine after)
                                            (proof-world-machine (allocation-write-words writes before)))
                  (equal (proof-active-floor after) (proof-active-floor before))
                  (equal (proof-active-end after) (proof-active-end before))
                  (equal (proof-box-top after) (proof-box-top before))
                  (equal (proof-cons-floor after) (proof-cons-floor before))
                  (proof-heap-object-spans-p pending headers before))
             (proof-heap-object-spans-p pending headers after)))
  :rule-classes nil
  :hints (("Goal" :induct (len pending)
           :expand ((:free (world) (proof-heap-object-spans-p pending headers world)))
           :in-theory (disable (:definition proof-heap-object-spans-p) proof-object-map-p proof-object-size
                               proof-span-p proof-subspan-p proof-active-floor proof-active-end proof-cons-floor
                               proof-box-top allocation-word-writes-outside-objects-p allocation-write-words
                               allocation-equal-memory-is-model-equivalence mod))
          ("Subgoal *1/1"
           :use ((:instance allocation-record-in-published-map
                  (pending objects) (symbols nil) (record (car pending)) (machine (proof-world-machine before)))
                 (:instance allocation-word-writes-keep-object-size
                  (address (proof-object-address (car pending))) (world before))))))
