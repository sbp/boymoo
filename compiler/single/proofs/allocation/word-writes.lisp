(in-package "BOYMOO-PROOFS")

(include-book "cons-publication")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun allocation-write-words (writes world)
  (if (atom writes)
      world
    (allocation-write-words (cdr writes)
                            (allocation-store-word (caar writes) (cdar writes) world))))

(defthm allocation-store-word-changes-machine-memory
  (equal (proof-world-machine (allocation-store-word address value world))
         (boymoo-model::a64-store 8 address value (proof-world-machine world)))
  :hints (("Goal" :in-theory (e/d (allocation-store-word proof-world-machine) (boymoo-model::a64-store)))))

(defun allocation-word-writes-outside-objects-p (writes objects machine)
  (if (atom writes)
      t
    (let ((address (caar writes)))
      (and (proof-span-p address 8)
           (allocation-objects-outside-write-p address (+ address 8) objects machine)
           (allocation-word-writes-outside-objects-p (cdr writes) objects machine)))))

(defthm allocation-word-writes-keep-disjointness-after-store
  (implies (and (proof-span-p start bytes)
                (allocation-objects-outside-write-p start (+ start bytes) objects machine))
           (equal (allocation-word-writes-outside-objects-p
                   writes objects (boymoo-model::a64-store bytes start value machine))
                  (allocation-word-writes-outside-objects-p writes objects machine)))
  :hints (("Goal" :induct (allocation-word-writes-outside-objects-p writes objects machine)
           :in-theory (disable allocation-objects-outside-write-p proof-span-p boymoo-model::a64-store))))

(defthm allocation-word-writes-keep-published-map
  (let* ((machine (proof-world-machine world))
         (updated (proof-world-machine (allocation-write-words writes world))))
    (implies (and (allocation-word-writes-outside-objects-p writes objects machine)
                  (proof-object-map-p objects objects nil base packages machine))
             (proof-object-map-p objects objects nil base packages updated)))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-write-words writes world)
           :in-theory (disable proof-object-map-p allocation-objects-outside-write-p proof-span-p boymoo-model::a64-store))
          ("Subgoal *1/2"
           :use ((:instance allocation-object-map-after-disjoint-write
                  (pending objects) (symbols nil) (start (caar writes)) (bytes 8)
                  (value (cdar writes)) (machine (proof-world-machine world)))))))

(defthm allocation-word-writes-keep-views
  (let* ((machine (proof-world-machine world))
         (updated (proof-world-machine (allocation-write-words writes world))))
    (implies (allocation-word-writes-outside-objects-p writes objects machine)
             (equal (proof-view word base objects packages updated)
                    (proof-view word base objects packages machine))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-write-words writes world)
           :in-theory (disable proof-view allocation-objects-outside-write-p proof-span-p boymoo-model::a64-store))))

(defun allocation-word-writes-avoid-span-p (writes lower upper)
  (if (atom writes)
      t
    (let ((address (caar writes)))
      (and (posp address) (proof-span-p address 8)
           (proof-disjoint-p address (+ address 8) lower upper)
           (allocation-word-writes-avoid-span-p (cdr writes) lower upper)))))

(local
 (defthm allocation-byte-entries-agree-transitive
   (implies (and (proof-byte-entries-agree-p entries lower upper first middle)
                 (proof-byte-entries-agree-p entries lower upper middle last))
            (proof-byte-entries-agree-p entries lower upper first last))
   :rule-classes nil
   :hints (("Goal" :induct (proof-byte-entries-agree-p entries lower upper first middle)
            :in-theory (disable boymoo-model::a64-byte)))))

(defthm allocation-word-writes-keep-protected-entries
  (let ((first (allocation-memory world))
        (last (allocation-memory (allocation-write-words writes world))))
    (implies (and (allocation-word-writes-avoid-span-p writes lower upper)
                  (natp lower) (natp upper) (<= upper *allocation-word-modulus*))
             (and (proof-byte-entries-agree-p entries lower upper first last)
                  (proof-byte-entries-agree-p entries lower upper last first))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-write-words writes world)
           :in-theory (disable proof-byte-entries-agree-p boymoo-model::a64-write-bytes
                               proof-span-p proof-disjoint-p allocation-byte-entries-agree-outside-write))
          ("Subgoal *1/2"
           :use ((:instance allocation-byte-entries-agree-outside-write
                  (start (caar writes)) (bytes 8) (value (cdar writes)) (memory (allocation-memory world)))
                 (:instance allocation-byte-entries-agree-transitive
                  (first (allocation-memory world))
                  (middle (allocation-memory (allocation-store-word (caar writes) (cdar writes) world)))
                  (last (allocation-memory (allocation-write-words writes world))))
                 (:instance allocation-byte-entries-agree-transitive
                  (last (allocation-memory world))
                  (middle (allocation-memory (allocation-store-word (caar writes) (cdar writes) world)))
                  (first (allocation-memory (allocation-write-words writes world))))))))

(defthm allocation-word-writes-keep-protected-span
  (implies (and (allocation-word-writes-avoid-span-p writes lower upper)
                (natp lower) (natp upper) (<= upper *allocation-word-modulus*)
                (equal (allocation-memory after) (allocation-memory (allocation-write-words writes world))))
           (proof-memory-span-agrees-p lower upper world after))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-word-writes-keep-protected-entries (entries (allocation-memory world)))
                 (:instance allocation-word-writes-keep-protected-entries (entries (allocation-memory after))))
           :in-theory (disable allocation-write-words proof-byte-entries-agree-p allocation-word-writes-avoid-span-p))))

(defthm allocation-word-writes-keep-inspected-span-disjoint
  (let* ((machine (proof-world-machine world))
         (updated (proof-world-machine (allocation-write-words writes world))))
    (implies (allocation-word-writes-outside-objects-p writes objects machine)
             (equal (proof-object-disjoint-p lower upper objects updated)
                    (proof-object-disjoint-p lower upper objects machine))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-write-words writes world)
           :in-theory (disable proof-object-disjoint-p allocation-objects-outside-write-p
                               proof-span-p boymoo-model::a64-store))
          ("Subgoal *1/2"
           :use ((:instance allocation-object-disjointness-after-write
                  (address lower) (end upper) (start (caar writes)) (bytes 8)
                  (value (cdar writes)) (machine (proof-world-machine world)))))))
