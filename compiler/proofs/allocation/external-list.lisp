(in-package "BOYMOO-PROOFS")

(include-book "heap-locality")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-region-member-has-valid-span
  (implies (and (proof-regions-p regions) (member-equal (proof-region start end mode) regions))
           (and (unsigned-byte-p 64 start) (natp end)
                (< start end) (<= end *allocation-word-modulus*)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-regions-p regions)
           :in-theory (disable proof-region-disjoint-p))))

(defthm allocation-external-record-after-disjoint-write
  (let ((changed (boymoo-model::a64-store bytes start value machine)))
    (implies (and (proof-regions-p regions) (member-equal (proof-region head end :rw) regions)
                  (<= (+ head 32) end) (proof-span-p start bytes)
                  (proof-disjoint-p start (+ start bytes) head end))
             (and (equal (proof-load-word head changed) (proof-load-word head machine))
                  (equal (proof-load-word (+ head 8) changed) (proof-load-word (+ head 8) machine))
                  (equal (proof-load-word (+ head 16) changed) (proof-load-word (+ head 16) machine))
                  (equal (proof-load-word (+ head 24) changed) (proof-load-word (+ head 24) machine)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-region-member-has-valid-span (start head) (mode :rw))
                 (:instance allocation-load-word-after-disjoint-write (address head))
                 (:instance allocation-load-word-after-disjoint-write (address (+ head 8)))
                 (:instance allocation-load-word-after-disjoint-write (address (+ head 16)))
                 (:instance allocation-load-word-after-disjoint-write (address (+ head 24))))
           :in-theory (disable proof-regions-p proof-region proof-load-word boymoo-model::a64-store))))

(defund allocation-same-external-bounds-p (before after)
  (and (equal (proof-heap-base after) (proof-heap-base before))
       (equal (proof-spaces-end after) (proof-spaces-end before))
       (equal (proof-stack-base after) (proof-stack-base before))
       (equal (proof-stack-end after) (proof-stack-end before))
       (equal (proof-machine-limit after) (proof-machine-limit before))
       (equal (proof-world-regions after) (proof-world-regions before))))

(local
 (defthm allocation-external-list-at-zero
   (equal (proof-external-objects 0 fuel world objects) '(:mappings))))

(defthm allocation-external-objects-after-heap-write
  (let* ((old-machine (proof-world-machine before))
         (old-list (proof-external-objects head fuel before objects))
         (changed (boymoo-model::a64-store bytes start value old-machine)))
    (implies (and old-list (allocation-same-external-bounds-p before after)
                  (allocation-same-memory-p (proof-world-machine after) changed)
                  (proof-regions-p (proof-world-regions before))
                  (proof-subspan-p start bytes (- (proof-heap-base before) *proof-heap-prefix*)
                                   (proof-spaces-end before)))
             (and (equal (proof-external-objects head fuel after objects) old-list)
                  (equal (proof-external-bytes (cdr old-list) (proof-world-machine after))
                         (proof-external-bytes (cdr old-list) old-machine)))))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel before objects)
           :expand ((:free (world) (proof-external-objects head fuel world objects)))
           :in-theory (e/d (allocation-same-external-bounds-p)
                           ((:definition proof-external-objects) proof-heap-base proof-machine-limit
                            proof-runtime-word allocation-runtime-word-as-load proof-load-word proof-align-up proof-regions-p
                            proof-header-size proof-header-type boymoo-model::a64-store)))
          ("Subgoal *1/2"
           :use ((:instance allocation-align-up-bounds
                  (size (+ 32 (proof-header-size (proof-load-word (+ head 24) (proof-world-machine before)))))
                  (alignment *proof-runtime-page*))
                 (:instance allocation-external-record-after-disjoint-write
                  (end (+ head (proof-load-word (+ head 8) (proof-world-machine before))))
                  (machine (proof-world-machine before)) (regions (proof-world-regions before)))))))

(defthm allocation-external-list-after-table-extension
  (implies (and (proof-external-objects head fuel world objects)
                (not (assoc-equal (car object) objects)))
           (equal (proof-external-objects head fuel world (cons object objects))
                  (proof-external-objects head fuel world objects)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel world objects)
           :expand ((:free (table) (proof-external-objects head fuel world table)))
           :in-theory (disable (:definition proof-external-objects) proof-runtime-word
                               allocation-runtime-word-as-load proof-load-word proof-align-up
                               proof-header-size proof-header-type proof-heap-base proof-machine-limit))))

(defthm allocation-external-list-one-more-fuel
  (implies (proof-external-objects head fuel world objects)
           (equal (proof-external-objects head (1+ (nfix fuel)) world objects)
                  (proof-external-objects head fuel world objects)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel world objects)
           :expand ((:free (limit) (proof-external-objects head limit world objects)))
           :in-theory (disable (:definition proof-external-objects) proof-runtime-word
                               allocation-runtime-word-as-load proof-load-word proof-align-up
                               proof-header-size proof-header-type proof-heap-base proof-machine-limit))))

(defthm allocation-external-list-with-new-head
  (let* ((object (proof-object (+ head 24) :external :header 0))
         (machine (proof-world-machine world))
         (header (proof-load-word (+ head 24) machine))
         (size (proof-load-word (+ head 8) machine))
         (end (+ head size))
         (machine-start (- (proof-machine-limit world) *proof-machine-margin*))
         (next (proof-load-word head machine))
         (old-list (proof-external-objects next (len objects) world objects)))
    (implies (and (not (equal head 0))
                  (not (assoc-equal (+ head 24) objects))
                  (equal (proof-external-head world) head)
                  (equal (proof-header-type header) 1)
                  (< (proof-header-size header) *proof-space-size*)
                  (equal (proof-load-word (+ head 16) machine) 0)
                  (equal size (proof-align-up (+ 32 (proof-header-size header)) *proof-runtime-page*))
                  (proof-disjoint-p head end (- (proof-heap-base world) *proof-heap-prefix*) (proof-spaces-end world))
                  (proof-disjoint-p head end (proof-stack-base world) (proof-stack-end world))
                  (proof-disjoint-p head end machine-start (+ machine-start *proof-machine-reservation*))
                  (member-equal (proof-region head end :rw) (proof-world-regions world))
                  old-list)
             (equal (proof-external-objects (proof-external-head world) (len (cons object objects)) world
                                            (cons object objects))
                    (list* :mappings (+ head 24) (cdr old-list)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-external-list-after-table-extension
                  (head (proof-load-word head (proof-world-machine world))) (fuel (len objects))
                  (object (proof-object (+ head 24) :external :header 0))))
           :expand ((:free (start table) (proof-external-objects start (+ 1 (len objects)) world table)))
           :in-theory (disable (:definition proof-external-objects) proof-load-word proof-align-up proof-runtime-word
                               allocation-runtime-word-as-load proof-header-size proof-header-type
                               proof-heap-base proof-machine-limit proof-disjoint-p))))
