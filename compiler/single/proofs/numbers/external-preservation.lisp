(in-package "BOYMOO-PROOFS")

(include-book "heap-layout")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-load-word proof-header-type proof-header-size
                     proof-world-machine proof-world-reg proof-world-regions
                     proof-heap-base proof-stack-base proof-stack-end
                     proof-machine-limit proof-spaces-end proof-align-up
                     proof-number-machine-span-agrees-p proof-number-memory-change-p
                     proof-number-objects-memory-p proof-number-object-memory-p
                     boymoo-model::a64-memory boymoo-model::a64-unsigned mod floor ash)))

(defund proof-number-in-runtime-reservation-p (start end world)
  (let* ((bytes (- end start))
         (base (proof-heap-base world))
         (machine-start (- (proof-machine-limit world) *proof-machine-margin*)))
    (or (proof-subspan-p start bytes (- base *proof-heap-prefix*) (proof-spaces-end world))
        (proof-subspan-p start bytes (proof-stack-base world) (proof-stack-end world))
        (proof-subspan-p start bytes machine-start (+ machine-start *proof-machine-reservation*)))))

(local
 (defthm member-region-is-valid
   (implies (and (proof-regions-p regions) (member-equal region regions))
            (proof-region-p region))
   :hints (("Goal" :induct (proof-regions-p regions)
                   :in-theory (disable proof-region-p proof-region-disjoint-p)))))

(local
 (defthm external-region-excludes-runtime-footprint
   (let ((floor (- (proof-machine-limit world) *proof-machine-margin*)))
     (implies (and (proof-number-in-runtime-reservation-p start end world)
                   (proof-disjoint-p head limit (- (proof-heap-base world) *proof-heap-prefix*)
                                     (proof-spaces-end world))
                   (proof-disjoint-p head limit (proof-stack-base world) (proof-stack-end world))
                   (proof-disjoint-p head limit floor (+ floor *proof-machine-reservation*)))
              (proof-disjoint-p head limit start end)))
   :hints (("Goal" :in-theory (enable proof-number-in-runtime-reservation-p)))
   :rule-classes nil))

(local
 (defthm external-node-words-kept
   (let* ((first (proof-world-machine before))
          (last (proof-world-machine after))
          (size (proof-load-word (+ head 8) first))
          (limit (+ head size))
          (floor (- (proof-machine-limit before) *proof-machine-margin*)))
     (implies (and (proof-number-in-runtime-reservation-p start end before)
                   (proof-regions-p (proof-world-regions before))
                   (member-equal (proof-region head limit :rw) (proof-world-regions before))
                   (<= 32 size)
                   (proof-disjoint-p head limit (- (proof-heap-base before) *proof-heap-prefix*)
                                     (proof-spaces-end before))
                   (proof-disjoint-p head limit (proof-stack-base before) (proof-stack-end before))
                   (proof-disjoint-p head limit floor (+ floor *proof-machine-reservation*))
                   (proof-number-memory-change-p start end first last)
                   (posp start))
              (and (equal (proof-load-word head last) (proof-load-word head first))
                   (equal (proof-load-word (+ head 8) last) (proof-load-word (+ head 8) first))
                   (equal (proof-load-word (+ head 16) last) (proof-load-word (+ head 16) first))
                   (equal (proof-load-word (+ head 24) last) (proof-load-word (+ head 24) first)))))
   :hints (("Goal"
            :use ((:instance external-region-excludes-runtime-footprint
                             (world before) (limit (+ head (proof-load-word (+ head 8)
                                                                            (proof-world-machine before)))))
                  (:instance member-region-is-valid
                             (regions (proof-world-regions before))
                             (region (proof-region head (+ head (proof-load-word
                                                                 (+ head 8) (proof-world-machine before))) :rw)))
                  (:instance proof-number-footprint-keeps-disjoint-span
                             (lower head) (upper (+ head (proof-load-word (+ head 8) (proof-world-machine before))))
                             (first (proof-world-machine before)) (last (proof-world-machine after)))
                  (:instance proof-number-word-agrees-in-machine-span
                             (address head)
                             (lower head) (upper (+ head (proof-load-word (+ head 8) (proof-world-machine before))))
                             (first (proof-world-machine before)) (last (proof-world-machine after)))
                  (:instance proof-number-word-agrees-in-machine-span
                             (address (+ head 8))
                             (lower head) (upper (+ head (proof-load-word (+ head 8) (proof-world-machine before))))
                             (first (proof-world-machine before)) (last (proof-world-machine after)))
                  (:instance proof-number-word-agrees-in-machine-span
                             (address (+ head 16))
                             (lower head) (upper (+ head (proof-load-word (+ head 8) (proof-world-machine before))))
                             (first (proof-world-machine before)) (last (proof-world-machine after)))
                  (:instance proof-number-word-agrees-in-machine-span
                             (address (+ head 24))
                             (lower head) (upper (+ head (proof-load-word (+ head 8) (proof-world-machine before))))
                             (first (proof-world-machine before)) (last (proof-world-machine after))))
            :in-theory (disable proof-regions-p proof-disjoint-p member-region-is-valid)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lookup-start
   (implies (assoc-equal address objects)
            (equal (car (assoc-equal address objects)) address))
   :hints (("Goal" :induct (assoc-equal address objects)))))

(local
 (defthm external-record-lookup-kept
   (implies (and (assoc-equal address old-objects)
                 (proof-number-objects-memory-p old-objects objects first last))
            (equal (assoc-equal address objects) (assoc-equal address old-objects)))
   :hints (("Goal"
            :use ((:instance proof-number-object-memory-at-lookup (pending old-objects)))
            :in-theory (e/d (proof-number-object-memory-p)
                            (proof-number-object-memory-at-lookup))))
   :rule-classes nil))

(local
 (defthm external-string-allocation-covers-prefix
   (<= 32 (proof-align-up (+ 32 (proof-header-size (proof-load-word address machine)))
                        *proof-runtime-page*))
   :hints (("Goal"
            :use ((:instance proof-number-alignment-does-not-shrink
                             (size (+ 32 (proof-header-size (proof-load-word address machine))))
                             (alignment *proof-runtime-page*))
                  (:instance proof-number-positive-divisor-floor-bounds (a (proof-load-word address machine))
                             (b 256)))
            :in-theory (enable proof-header-size)
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-external-chain-and-accounting-kept
  (let* ((external (proof-external-objects head fuel before old-objects))
         (first (proof-world-machine before))
         (last (proof-world-machine after)))
    (implies (and external (natp fuel) (natp additional-fuel)
                  (equal (proof-number-heap-coordinates before) (proof-number-heap-coordinates after))
                  (proof-regions-p (proof-world-regions before))
                  (proof-number-in-runtime-reservation-p start end before)
                  (proof-number-objects-memory-p old-objects objects first last)
                  (proof-number-memory-change-p start end first last)
                  (posp start))
             (and (equal (proof-external-objects head (+ fuel additional-fuel) after objects) external)
                  (equal (proof-external-bytes (cdr external) last)
                         (proof-external-bytes (cdr external) first)))))
  :hints (("Goal"
           :induct (proof-external-objects head fuel before old-objects)
           :in-theory (disable (:definition proof-external-objects) proof-object-kind proof-object-zone
                               proof-external-bytes proof-disjoint-p proof-regions-p)
           :expand ((proof-external-objects head fuel before old-objects)
                    (:free (remaining) (proof-external-objects head remaining after objects))))
          ("Subgoal *1/2"
           :use (proof-number-equal-heap-coordinates-preserve-fields
                 external-node-words-kept
                 (:instance external-string-allocation-covers-prefix
                            (address (+ 24 head)) (machine (proof-world-machine before)))
                 (:instance external-record-lookup-kept
                            (address (+ 24 head))
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (enable proof-external-bytes))
          ("Subgoal *1/1" :in-theory (enable proof-external-objects proof-external-bytes)))
  :rule-classes nil)
