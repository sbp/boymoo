(in-package "BOYMOO-PROOFS")

(include-book "scan-fields")
(include-book "scan-traversal")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-source-pending-p (address work)
  (and address
       (or (assoc-equal address (collection-cell-queue work))
           (assoc-equal address (collection-header-queue work)))))

(defun collection-selected-record (work)
  (if (consp (collection-cell-queue work))
      (car (collection-cell-queue work))
    (car (collection-header-queue work))))

(defun collection-work-after-dequeue (work)
  (if (consp (collection-cell-queue work))
      (update-nth 2 (cdr (collection-cell-queue work)) work)
    (if (consp (collection-header-queue work))
        (update-nth 3 (cdr (collection-header-queue work)) work)
      work)))

(local
 (in-theory (disable collection-header-queue collection-cell-queue collection-forwarding collection-unseen
                     collection-scan-one collection-discover collection-discover-fields
                     collection-datum-assigned-p collection-relocate-datum
                     proof-load-word proof-world-machine collection-read-word
                     collection-slot-words collection-rewrite-slots collection-reference-fields)))

(local
 (defthm collection-scan-one-discovers-dequeued-record-fields
   (equal (collection-scan-one work)
          (collection-discover-fields (cdddr (collection-selected-record work))
                                      (collection-work-after-dequeue work)))
   :hints (("Goal" :in-theory (enable collection-scan-one collection-discover-fields)))))

(local
 (defthm collection-scan-lookup-key
   (implies (assoc-equal query records)
            (equal (car (assoc-equal query records)) query))))

(local
 (defthm collection-scan-lookup-through-queue-append
   (implies address
            (equal (assoc-equal address (append queue tail))
                   (or (assoc-equal address queue) (assoc-equal address tail))))))

(local
 (defthm collection-discovery-keeps-already-pending-source
   (implies (collection-source-pending-p query work)
            (collection-source-pending-p query (collection-discover address work)))
   :hints (("Goal"
            :in-theory (enable collection-discover collection-cell-queue collection-header-queue
                               collection-unseen)))))

(local
 (defthm collection-field-discovery-keeps-already-pending-source
   (implies (collection-source-pending-p query work)
            (collection-source-pending-p query (collection-discover-fields fields work)))
   :hints (("Goal"
            :induct (collection-discover-fields fields work)
            :in-theory (e/d (collection-discover-fields) (collection-source-pending-p))))))

(local
 (defthm collection-dequeue-keeps-unselected-pending-source
   (implies (and (collection-source-pending-p query work)
                 (not (equal query (car (collection-selected-record work)))))
            (collection-source-pending-p query (collection-work-after-dequeue work)))
   :hints (("Goal"
            :in-theory (e/d (collection-cell-queue collection-header-queue)
                             (nth update-nth))))))

(defthm collection-scan-keeps-unselected-source-pending
  (implies (and (collection-source-pending-p query work)
                (not (equal query (car (collection-selected-record work)))))
           (collection-source-pending-p query (collection-scan-one work)))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable collection-work-after-dequeue collection-source-pending-p
                               collection-selected-record))))

(local
 (defthm collection-discovery-does-not-queue-source-outside-unseen
   (implies (and (not (assoc-equal query (collection-unseen work)))
                 (not (collection-source-pending-p query work)))
            (not (collection-source-pending-p query (collection-discover address work))))
   :hints (("Goal"
            :in-theory (enable collection-discover collection-unseen
                               collection-cell-queue collection-header-queue)))))

(local
 (defthm collection-field-discovery-does-not-queue-source-outside-unseen
   (implies (and (not (assoc-equal query (collection-unseen work)))
                 (not (collection-source-pending-p query work)))
            (not (collection-source-pending-p query (collection-discover-fields fields work))))
   :hints (("Goal"
            :induct (collection-discover-fields fields work)
            :in-theory (e/d (collection-discover-fields) (collection-source-pending-p))))))

(local
 (defthm collection-dequeue-does-not-queue-source-outside-unseen
   (implies (and (not (assoc-equal query (collection-unseen work)))
                 (not (collection-source-pending-p query work)))
            (and (not (assoc-equal query (collection-unseen (collection-work-after-dequeue work))))
                 (not (collection-source-pending-p query (collection-work-after-dequeue work)))))
   :hints (("Goal"
            :in-theory (e/d (collection-cell-queue collection-header-queue collection-unseen)
                             (nth update-nth))))))

(defthm collection-scan-cannot-requeue-a-committed-source
  (implies (and (not (assoc-equal query (collection-unseen work)))
                (not (collection-source-pending-p query work)))
           (not (collection-source-pending-p query (collection-scan-one work))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (disable collection-work-after-dequeue collection-source-pending-p
                               collection-selected-record))))

(defthm collection-selected-slot-discovery-is-abstract-scan
  (let ((machine (proof-world-machine original)))
    (implies (equal (cdddr (collection-selected-record work))
                    (collection-reference-fields count source base objects machine))
             (equal (mv-nth 1 (collection-rewrite-slots count source base objects machine
                                                       (collection-work-after-dequeue work)))
                    (collection-scan-one work))))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable collection-selected-record collection-work-after-dequeue))))

(defthm collection-selected-copy-becomes-committed-by-its-field-rewrites
  (let* ((record (collection-selected-record work))
         (dequeued (collection-work-after-dequeue work))
         (machine (proof-world-machine original)))
    (mv-let (words result)
      (collection-rewrite-slots count source base objects machine dequeued)
      (declare (ignore result))
      (implies (and (equal (cdddr record) (collection-reference-fields count source base objects machine))
                    (collection-slot-sources-known-p count source base objects machine dequeued)
                    (equal (collection-slot-words count target current) words))
               (collection-scanned-fields-p count source target base objects original current
                                           (collection-scan-one work)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-selected-slot-discovery-is-abstract-scan)
                 (:instance collection-writing-the-abstract-rewrites-commits-all-fields
                            (work (collection-work-after-dequeue work))))
           :in-theory (theory 'minimal-theory)
           :do-not-induct t)))
