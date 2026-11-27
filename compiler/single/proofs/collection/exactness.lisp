(in-package "BOYMOO-PROOFS")

(include-book "published")

(logic)
(set-verify-guards-eagerness 0)

; Forwarding keys are unique. Each assigned source has left the
; unseen set, so a later discovery can only reuse its assignment.
(defun collection-forwarding-partition-p (entries unseen)
  (if (endp entries)
      t
    (and (not (assoc-equal (caar entries) (cdr entries)))
         (not (assoc-equal (caar entries) unseen))
         (collection-forwarding-partition-p (cdr entries) unseen))))

(local
 (defthm collection-forwarding-partition-excludes-unseen
   (implies (and (collection-forwarding-partition-p entries unseen)
                 (assoc-equal address unseen))
            (not (assoc-equal address entries)))
   :hints (("Goal" :induct (assoc-equal address entries)))))

(local
 (defthm collection-assoc-after-removal
   (equal (assoc-equal query (remove-assoc-equal address entries))
          (and (not (equal query address)) (assoc-equal query entries)))))

(local
 (defthm collection-partition-removing-unseen
   (implies (collection-forwarding-partition-p entries unseen)
            (collection-forwarding-partition-p entries (remove-assoc-equal address unseen)))
   :hints (("Goal" :induct (len entries)))))

(local
 (defthm collection-discovery-keeps-forwarding-partition
   (implies (collection-forwarding-partition-p (collection-forwarding work)
                                                (collection-unseen work))
            (let ((next (collection-discover address work)))
              (collection-forwarding-partition-p (collection-forwarding next)
                                                   (collection-unseen next))))
   :hints (("Goal" :in-theory (enable collection-discover)))))

(local (in-theory (disable collection-forwarding-partition-p)))

(local
 (defthm collection-field-discovery-keeps-forwarding-partition
   (implies (collection-forwarding-partition-p (collection-forwarding work)
                                                (collection-unseen work))
            (let ((next (collection-discover-fields fields work)))
              (collection-forwarding-partition-p (collection-forwarding next)
                                                   (collection-unseen next))))
   :hints (("Goal" :induct (collection-discover-fields fields work)
                   :in-theory (disable collection-forwarding collection-unseen)))))

(local
 (defthm collection-partition-unchanged-by-pop
   (implies (or (equal index 2) (equal index 3))
            (equal (collection-forwarding-partition-p
                    (collection-forwarding (update-nth index queue work))
                    (collection-unseen (update-nth index queue work)))
                   (collection-forwarding-partition-p (collection-forwarding work)
                                                        (collection-unseen work))))
   :hints (("Goal" :in-theory (disable nth update-nth)))))

(local
 (defthm collection-scan-keeps-forwarding-partition
   (implies (collection-forwarding-partition-p (collection-forwarding work)
                                                (collection-unseen work))
            (let ((next (collection-scan-one work)))
              (collection-forwarding-partition-p (collection-forwarding next)
                                                   (collection-unseen next))))
   :hints (("Goal"
            :in-theory (e/d (collection-scan-one)
                            (collection-discover-fields nth update-nth
                             collection-forwarding collection-unseen))))))

(local
 (defthm collection-finish-keeps-forwarding-partition
   (implies (collection-forwarding-partition-p (collection-forwarding work)
                                                (collection-unseen work))
            (let ((next (collection-finish-scan work)))
              (collection-forwarding-partition-p (collection-forwarding next)
                                                   (collection-unseen next))))
   :hints (("Goal" :induct (collection-finish-scan work)
                   :in-theory (disable collection-forwarding collection-unseen)))))

(local
 (defthm collection-initial-work-partitions-source-addresses
   (let ((work (collection-work graph nil nil nil lower upper)))
     (collection-forwarding-partition-p (collection-forwarding work) (collection-unseen work)))
   :hints (("Goal" :in-theory (enable collection-forwarding-partition-p)))))

(defthm collection-traversal-assigns-each-source-at-most-once
  (let ((work (collection-traverse roots graph lower upper)))
    (collection-forwarding-partition-p (collection-forwarding work) (collection-unseen work)))
  :hints (("Goal" :in-theory (disable collection-work collection-forwarding collection-unseen
                                      collection-discover-fields collection-finish-scan))))

(defthm collection-published-forwarding-has-root-witness
  (let* ((graph (collection-published-object-graph
                 objects (proof-heap-base world) objects (proof-world-machine world)))
         (roots (collection-published-roots world objects))
         (lower (proof-inactive-floor world))
         (upper (proof-inactive-end world))
         (work (collection-traverse roots graph lower upper))
         (paths (collection-traversal-paths roots graph lower upper))
         (path (cdr (assoc-equal address paths))))
    (implies (and (proof-heap-p world objects packages)
                  (assoc-equal address (collection-forwarding work)))
             (and (equal (car path) address)
                  (collection-reverse-path-p path roots graph))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-published-graph-fits-four-gibibytes)
                 (:instance collection-traversal-forwards-only-reachable-objects
                            (graph (collection-published-object-graph
                                    objects (proof-heap-base world) objects
                                    (proof-world-machine world)))
                            (roots (collection-published-roots world objects))
                            (lower (proof-inactive-floor world))
                            (upper (proof-inactive-end world))))
           :in-theory (disable proof-heap-p proof-heap-base proof-inactive-floor
                               proof-inactive-end proof-world-machine
                               collection-published-object-graph collection-published-roots
                               collection-traverse collection-traversal-paths
                               collection-source-records-p collection-reverse-path-p
                               collection-pending-bytes collection-forwarding assoc-equal))))
