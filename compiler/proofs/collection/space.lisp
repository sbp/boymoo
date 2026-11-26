(in-package "BOYMOO-PROOFS")

(include-book "reachability")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-moved-kind-p (record)
  (member-eq (cadr record) '(:cons :header)))

(defun collection-copy-bytes (record)
  (case (cadr record)
    (:cons 16)
    (:header (nfix (caddr record)))
    (otherwise 0)))

(defun collection-pending-bytes (records)
  (if (endp records)
      0
    (+ (collection-copy-bytes (car records))
       (collection-pending-bytes (cdr records)))))

(local
 (defthm collection-remove-assoc-does-not-increase-bytes
   (<= (collection-pending-bytes (remove-assoc-equal address records))
       (collection-pending-bytes records))
   :rule-classes :linear
   :hints (("Goal" :induct (remove-assoc-equal address records)
                   :in-theory (disable collection-copy-bytes)))))

(local
 (defthm collection-discovery-debits-at-least-copy-size
   (implies (assoc-equal address records)
            (<= (+ (collection-copy-bytes (assoc-equal address records))
                   (collection-pending-bytes (remove-assoc-equal address records)))
                (collection-pending-bytes records)))
   :rule-classes :linear
   :hints (("Goal" :induct (remove-assoc-equal address records)
                   :in-theory (disable collection-copy-bytes)))))

(defun collection-destination-space-p (work graph floor end)
  (let ((low (collection-header-frontier work))
        (high (collection-cell-frontier work)))
    (and (natp floor) (natp end) (< end (expt 2 64))
         (integerp low) (integerp high)
         (<= floor low) (<= high end)
         (<= (+ low (collection-pending-bytes (collection-unseen work))) high)
         (collection-source-records-p (collection-unseen work) graph))))

(local (in-theory (disable collection-source-records-p collection-pending-bytes)))

(defthm collection-discovery-preserves-destination-space
  (implies (collection-destination-space-p work graph floor end)
           (collection-destination-space-p
            (collection-discover address work) graph floor end))
  :hints (("Goal"
           :use ((:instance collection-discovery-debits-at-least-copy-size
                            (records (collection-unseen work))))
           :in-theory (e/d (collection-discover)
                           (collection-discovery-debits-at-least-copy-size)))))

(defthm collection-forwarding-lookup-after-discovery
  (equal (assoc-equal query (collection-forwarding (collection-discover address work)))
         (let ((record (assoc-equal address (collection-unseen work))))
           (if (and record (equal query address))
               (cons address (collection-copy-address record work))
             (assoc-equal query (collection-forwarding work)))))
  :hints (("Goal" :in-theory (enable collection-discover))))

(defthm collection-discovery-advances-destination-frontiers
  (let* ((record (assoc-equal address (collection-unseen work)))
         (bytes (collection-copy-bytes record))
         (next (collection-discover address work)))
    (and (equal (collection-header-frontier next)
                (if (eq (cadr record) :header)
                    (+ (collection-header-frontier work) bytes)
                  (collection-header-frontier work)))
         (equal (collection-cell-frontier next)
                (if (eq (cadr record) :cons)
                    (- (collection-cell-frontier work) bytes)
                  (collection-cell-frontier work)))))
  :hints (("Goal" :in-theory (enable collection-discover))))

(local
 (defthm collection-forwarding-source-key
   (implies (assoc-equal address graph)
            (equal (car (assoc-equal address graph)) address))))

(local
 (in-theory (disable collection-unseen collection-forwarding collection-header-frontier
                     collection-cell-frontier)))

(defun collection-copy-in-space-p (address work graph floor end)
  (let* ((entry (assoc-equal address (collection-forwarding work)))
         (record (assoc-equal address graph))
         (copy (cdr entry))
         (size (collection-copy-bytes record)))
    (or (not entry)
        (and record
             (case (cadr record)
               (:cons (proof-subspan-p copy size (collection-cell-frontier work) end))
               (:header (proof-subspan-p copy size floor (collection-header-frontier work)))
               (:external (equal copy address)))))))

(local
 (defthm collection-new-copy-fits-its-space
   (implies (and (collection-destination-space-p work graph floor end)
                 (assoc-equal address (collection-unseen work)))
            (collection-copy-in-space-p
             address (collection-discover address work) graph floor end))
   :hints (("Goal"
            :use ((:instance collection-source-lookup-agrees-with-graph
                             (records (collection-unseen work)))
                  (:instance collection-discovery-preserves-destination-space))
            :in-theory (disable
                        collection-discovery-preserves-destination-space
                        collection-discover-installs-its-forwarding-entry)))))

(defthm collection-discovery-preserves-copy-placement
  (implies (and (collection-destination-space-p work graph floor end)
                (collection-copy-in-space-p query work graph floor end))
           (collection-copy-in-space-p
            query (collection-discover address work) graph floor end))
  :hints (("Goal"
           :use ((:instance collection-discovery-preserves-destination-space))
           :cases ((and (equal address query)
                        (assoc-equal address (collection-unseen work))))
           :in-theory (disable collection-discovery-preserves-destination-space
                               collection-discover-installs-its-forwarding-entry))
          ("Subgoal 1" :in-theory (disable collection-copy-in-space-p))))

(defun collection-copies-apart-p (first second work graph)
  (let* ((left (assoc-equal first (collection-forwarding work)))
         (right (assoc-equal second (collection-forwarding work)))
         (old-left (assoc-equal first graph))
         (old-right (assoc-equal second graph)))
    (or (equal first second) (not left) (not right)
        (not (collection-moved-kind-p old-left))
        (not (collection-moved-kind-p old-right))
        (proof-disjoint-p (cdr left) (+ (cdr left) (collection-copy-bytes old-left))
                          (cdr right) (+ (cdr right) (collection-copy-bytes old-right))))))

(local
 (defthm collection-new-copy-is-disjoint-from-old-copy
   (implies (and (collection-destination-space-p work graph floor end)
                 (collection-copy-in-space-p other work graph floor end)
                 (assoc-equal address (collection-unseen work))
                 (not (equal address other)))
            (collection-copies-apart-p
             address other (collection-discover address work) graph))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-source-lookup-agrees-with-graph
                             (records (collection-unseen work)))
                  (:instance collection-discovery-preserves-destination-space))
            :in-theory (disable
                        collection-discovery-preserves-destination-space
                        collection-discover-installs-its-forwarding-entry)))))

(local
 (defthm collection-copies-apart-is-symmetric
   (equal (collection-copies-apart-p first second work graph)
          (collection-copies-apart-p second first work graph))
   :rule-classes nil))

(local
 (defthm collection-copies-apart-after-other-discovery
   (implies (or (not (assoc-equal address (collection-unseen work)))
                (and (not (equal address first)) (not (equal address second))))
            (equal (collection-copies-apart-p
                    first second (collection-discover address work) graph)
                   (collection-copies-apart-p first second work graph)))
   :hints (("Goal" :in-theory (disable collection-discover-installs-its-forwarding-entry)))))

(local
 (defthm collection-copies-apart-when-queries-coincide
   (collection-copies-apart-p address address work graph)))

(defthm collection-discovery-preserves-disjoint-copies
  (implies (and (collection-destination-space-p work graph floor end)
                (collection-copy-in-space-p first work graph floor end)
                (collection-copy-in-space-p second work graph floor end)
                (collection-copies-apart-p first second work graph))
           (collection-copies-apart-p
            first second (collection-discover address work) graph))
  :hints (("Goal"
           :use ((:instance collection-new-copy-is-disjoint-from-old-copy (other first))
                 (:instance collection-new-copy-is-disjoint-from-old-copy (other second))
                 (:instance collection-copies-apart-is-symmetric
                            (work (collection-discover address work)))
                 (:instance collection-copies-apart-after-other-discovery))
           :cases ((and (equal address first) (assoc-equal address (collection-unseen work)))
                   (and (equal address second) (assoc-equal address (collection-unseen work))))
           :in-theory (disable collection-copies-apart-p collection-copy-in-space-p
                               collection-destination-space-p
                               collection-copies-apart-after-other-discovery))))

; This invariant gives the room still required and the separation of a
; queried pair of forwarding entries. Quantifying over the query pair
; gives separation for the entire forwarding map.
(defun collection-destinations-p (first second work graph floor end)
  (and (collection-destination-space-p work graph floor end)
       (collection-copy-in-space-p first work graph floor end)
       (collection-copy-in-space-p second work graph floor end)
       (collection-copies-apart-p first second work graph)))

(local
 (in-theory (disable collection-copy-in-space-p collection-copies-apart-p
                     collection-destination-space-p)))

(local
 (defthm collection-destinations-after-discovery
   (implies (collection-destinations-p first second work graph floor end)
            (collection-destinations-p first second (collection-discover address work)
                                       graph floor end))))

(local
 (defthm collection-destinations-after-popping-queue
   (implies (or (equal cursor 2) (equal cursor 3))
            (equal (collection-destinations-p
                    first second (update-nth cursor queue work) graph floor end)
                   (collection-destinations-p first second work graph floor end)))
   :hints (("Goal"
            :cases ((equal cursor 2))
            :in-theory (e/d (collection-unseen collection-forwarding collection-header-frontier
                                               collection-cell-frontier collection-copy-in-space-p
                                               collection-copies-apart-p
                                               collection-destination-space-p)
                            (nth update-nth))))))

(local (in-theory (disable collection-destinations-p)))

(local
 (defthm collection-destinations-after-discovering-fields
   (implies (collection-destinations-p first second work graph floor end)
            (collection-destinations-p
             first second (collection-discover-fields fields work) graph floor end))
   :hints (("Goal" :induct (collection-discover-fields fields work)))))

(local
 (defthm collection-destinations-after-scanning-one
   (implies (collection-destinations-p first second work graph floor end)
            (collection-destinations-p
             first second (collection-scan-one work) graph floor end))
   :hints (("Goal" :in-theory (e/d (collection-scan-one)
                                   (collection-discover-fields nth update-nth))))))

(defthm collection-destinations-after-scanning
  (implies (collection-destinations-p first second work graph floor end)
           (collection-destinations-p
            first second (collection-finish-scan work) graph floor end))
  :hints (("Goal" :induct (collection-finish-scan work))))

(local
 (defthm collection-initial-destinations
   (implies (and (collection-source-records-p graph graph)
                 (natp floor) (natp end) (< end (expt 2 64))
                 (<= (+ floor (collection-pending-bytes graph)) end))
            (collection-destinations-p
             first second (collection-work graph nil nil nil floor end) graph floor end))
   :hints (("Goal" :in-theory (enable collection-destinations-p
                                      collection-destination-space-p
                                      collection-copy-in-space-p collection-copies-apart-p
                                      collection-unseen collection-forwarding
                                      collection-header-frontier collection-cell-frontier)))))

(defthm collection-traversal-places-moved-copies-in-disjoint-spans
  (implies (and (collection-source-records-p graph graph)
                (natp floor) (natp end) (< end (expt 2 64))
                (<= (+ floor (collection-pending-bytes graph)) end))
           (collection-destinations-p
            first second (collection-traverse roots graph floor end) graph floor end))
  :hints (("Goal" :in-theory (disable collection-work collection-discover-fields
                                      collection-finish-scan))))
