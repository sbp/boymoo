(in-package "BOYMOO-PROOFS")

(include-book "space")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-scan-step-address (kind cursor record)
  (if (eq kind :cons)
      (- cursor (collection-copy-bytes record))
    (+ cursor (collection-copy-bytes record))))

(defun collection-queue-frontier (kind work)
  (if (eq kind :cons)
      (collection-cell-frontier work)
    (collection-header-frontier work)))

; From the scan cursor to the allocation frontier, queue records
; describe adjacent, nonempty spans in the order they are visited.
(defun collection-queued-spans-p (kind queue cursor frontier work)
  (if (endp queue)
      (equal cursor frontier)
    (let* ((record (car queue))
           (address (car record))
           (next (collection-scan-step-address kind cursor record))
           (copy (if (eq kind :cons) next cursor)))
      (and (eq (cadr record) kind)
           (posp (collection-copy-bytes record))
           (not (assoc-equal address (collection-unseen work)))
           (equal (assoc-equal address (collection-forwarding work)) (cons address copy))
           (collection-queued-spans-p kind (cdr queue) next frontier work)))))

(defun collection-nonempty-copy-spans-p (records)
  (if (endp records)
      t
    (and (or (not (collection-moved-kind-p (car records)))
             (posp (collection-copy-bytes (car records))))
         (collection-nonempty-copy-spans-p (cdr records)))))

(local
 (defthm collection-copy-size-positive-for-pending-moved-record
   (implies (and (collection-nonempty-copy-spans-p records)
                 (collection-moved-kind-p (assoc-equal address records)))
            (posp (collection-copy-bytes (assoc-equal address records))))
   :hints (("Goal" :induct (assoc-equal address records)
                   :in-theory (disable collection-copy-bytes collection-moved-kind-p)))))

(local
 (defthm collection-nonempty-copy-spans-after-discovery
   (implies (collection-nonempty-copy-spans-p records)
            (collection-nonempty-copy-spans-p (remove-assoc-equal address records)))
   :hints (("Goal" :induct (remove-assoc-equal address records)
                   :in-theory (disable collection-copy-bytes collection-moved-kind-p)))))

(defun collection-queue-after-discovery (kind queue record)
  (if (and record (eq (cadr record) kind))
      (append queue (list record))
    queue))

(local
 (defthm collection-queue-frontier-after-discovery
   (let ((record (assoc-equal address (collection-unseen work))))
     (implies (member-eq kind '(:cons :header))
              (equal (collection-queue-frontier kind (collection-discover address work))
                     (if (and record (eq (cadr record) kind))
                         (collection-scan-step-address
                          kind (collection-queue-frontier kind work) record)
                       (collection-queue-frontier kind work)))))))

(local
 (defthm collection-queue-address-key
   (implies (assoc-equal address records)
            (equal (car (assoc-equal address records)) address))))

(local
 (in-theory (disable collection-cell-frontier collection-header-frontier
                     collection-unseen collection-forwarding
                     collection-queue-frontier collection-discover-installs-its-forwarding-entry)))

(local
 (defthm collection-queued-spans-after-discovery
   (let ((record (assoc-equal address (collection-unseen work))))
     (implies (and (member-eq kind '(:cons :header))
                   (collection-nonempty-copy-spans-p (collection-unseen work))
                   (collection-queued-spans-p kind queue cursor
                                              (collection-queue-frontier kind work) work))
              (collection-queued-spans-p
               kind (collection-queue-after-discovery kind queue record)
               cursor (collection-queue-frontier kind (collection-discover address work))
               (collection-discover address work))))
   :hints (("Goal"
            :induct (collection-queued-spans-p
                     kind queue cursor (collection-queue-frontier kind work) work)
            :in-theory (disable append collection-copy-bytes collection-nonempty-copy-spans-p))
           ("Subgoal *1/1"
            :use ((:instance collection-copy-size-positive-for-pending-moved-record
                             (records (collection-unseen work))))
            :in-theory (e/d (append collection-copy-bytes collection-queue-frontier)
                            (collection-copy-size-positive-for-pending-moved-record)))
           ("Subgoal *1/2"
            :in-theory (enable append collection-copy-bytes collection-queue-frontier)))))

(local
 (defthm collection-work-queues-after-discovery
   (let ((record (assoc-equal address (collection-unseen work)))
         (after (collection-discover address work)))
     (and (equal (collection-cell-queue after)
                 (collection-queue-after-discovery :cons (collection-cell-queue work) record))
          (equal (collection-header-queue after)
                 (collection-queue-after-discovery :header (collection-header-queue work) record))
          (equal (collection-unseen after)
                 (if record
                     (remove-assoc-equal address (collection-unseen work))
                   (collection-unseen work)))))
   :hints (("Goal" :in-theory (enable collection-discover collection-unseen
                                      collection-forwarding collection-cell-frontier
                                      collection-header-frontier)))))

(defun collection-scan-cursors-p (header cell work)
  (and (collection-nonempty-copy-spans-p (collection-unseen work))
       (collection-queued-spans-p :header (collection-header-queue work) header
                                  (collection-queue-frontier :header work) work)
       (collection-queued-spans-p :cons (collection-cell-queue work) cell
                                  (collection-queue-frontier :cons work) work)))

(local (in-theory (disable collection-cell-queue collection-header-queue
                            collection-queued-spans-p collection-queue-after-discovery)))

(defthm collection-discovery-preserves-scan-cursors
  (implies (collection-scan-cursors-p header cell work)
           (collection-scan-cursors-p header cell (collection-discover address work)))
  :hints (("Goal"
           :use ((:instance collection-queued-spans-after-discovery
                            (kind :header) (queue (collection-header-queue work))
                            (cursor header))
                 (:instance collection-queued-spans-after-discovery
                            (kind :cons) (queue (collection-cell-queue work))
                            (cursor cell)))
           :in-theory (disable collection-queue-frontier-after-discovery
                               collection-queued-spans-after-discovery
                               collection-nonempty-copy-spans-p))))

(defthm collection-field-discovery-preserves-scan-cursors
  (implies (collection-scan-cursors-p header cell work)
           (collection-scan-cursors-p header cell (collection-discover-fields fields work)))
  :hints (("Goal" :induct (collection-discover-fields fields work)
                  :in-theory (disable collection-scan-cursors-p))))

(local
 (defthm collection-queued-spans-have-ordered-frontiers
   (implies (and (collection-queued-spans-p kind queue cursor frontier work)
                 (integerp cursor))
            (and (iff (consp queue)
                      (if (eq kind :cons) (< frontier cursor) (< cursor frontier)))
                 (implies (consp queue)
                          (equal (assoc-equal (caar queue) (collection-forwarding work))
                                 (cons (caar queue)
                                       (if (eq kind :cons) (- cursor 16) cursor))))))
   :hints (("Goal"
            :induct (collection-queued-spans-p kind queue cursor frontier work)
            :in-theory (enable collection-queued-spans-p)))))

(defthm collection-queue-frontiers-select-pending-scan
  (let ((headers (collection-header-queue work))
        (cells (collection-cell-queue work)))
    (implies (and (collection-scan-cursors-p header cell work)
                  (integerp header) (integerp cell))
             (and (iff (consp cells) (< (collection-cell-frontier work) cell))
                  (iff (consp headers) (< header (collection-header-frontier work)))
                  (implies (consp cells)
                           (equal (assoc-equal (caar cells) (collection-forwarding work))
                                  (cons (caar cells) (- cell 16))))
                  (implies (consp headers)
                           (equal (assoc-equal (caar headers) (collection-forwarding work))
                                  (cons (caar headers) header))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-queued-spans-have-ordered-frontiers
                            (kind :cons) (queue (collection-cell-queue work))
                            (cursor cell) (frontier (collection-cell-frontier work)))
                 (:instance collection-queued-spans-have-ordered-frontiers
                            (kind :header) (queue (collection-header-queue work))
                            (cursor header) (frontier (collection-header-frontier work))))
           :in-theory (enable collection-queue-frontier))))

(local
 (defthm collection-popping-queue-keeps-unseen-map-and-frontiers
   (implies (or (equal index 2) (equal index 3))
            (and (equal (collection-unseen (update-nth index queue work))
                        (collection-unseen work))
                 (equal (collection-forwarding (update-nth index queue work))
                        (collection-forwarding work))
                 (equal (collection-queue-frontier kind (update-nth index queue work))
                        (collection-queue-frontier kind work))))
   :hints (("Goal" :in-theory (e/d (collection-unseen collection-forwarding
                                                   collection-queue-frontier
                                                   collection-header-frontier
                                                   collection-cell-frontier)
                                   (nth update-nth))))))

(local
 (defthm collection-queued-spans-ignore-queue-update
   (implies (or (equal index 2) (equal index 3))
            (equal (collection-queued-spans-p kind records cursor frontier
                                              (update-nth index queue work))
                   (collection-queued-spans-p kind records cursor frontier work)))
   :hints (("Goal" :induct (collection-queued-spans-p kind records cursor frontier work)
                   :in-theory (e/d (collection-queued-spans-p) (nth update-nth))))))

(local
 (defthm collection-queued-cons-tail
   (implies (and (consp records) (collection-queued-spans-p :cons records cell frontier work))
            (collection-queued-spans-p :cons (cdr records) (- cell 16) frontier work))
   :hints (("Goal" :in-theory (enable collection-queued-spans-p)))))

(local
 (defthm collection-queued-header-tail
   (implies (and (consp records)
                 (collection-queued-spans-p :header records header frontier work))
            (collection-queued-spans-p
             :header (cdr records)
             (collection-scan-step-address :header header (car records)) frontier work))
   :hints (("Goal" :in-theory (enable collection-queued-spans-p)))))

(local
 (defthm collection-cursors-after-popping-cons
   (let ((queue (collection-cell-queue work)))
     (implies (and (collection-scan-cursors-p header cell work) (consp queue))
              (collection-scan-cursors-p header (- cell 16)
                                         (update-nth 2 (cdr queue) work))))
   :hints (("Goal"
            :in-theory (e/d (collection-cell-queue collection-header-queue)
                            (nth update-nth))))))

(local
 (defthm collection-cursors-after-popping-header
   (let* ((queue (collection-header-queue work))
          (next (collection-scan-step-address :header header (car queue))))
     (implies (and (collection-scan-cursors-p header cell work) (consp queue))
              (collection-scan-cursors-p next cell (update-nth 3 (cdr queue) work))))
   :hints (("Goal"
            :in-theory (e/d (collection-cell-queue collection-header-queue)
                            (nth update-nth collection-scan-step-address
                             collection-copy-bytes))))))

(defun collection-header-cursor-after-scan (header work)
  (if (and (endp (collection-cell-queue work)) (consp (collection-header-queue work)))
      (collection-scan-step-address :header header (car (collection-header-queue work)))
    header))

(defun collection-cons-cursor-after-scan (cell work)
  (if (consp (collection-cell-queue work)) (- cell 16) cell))

(defthm collection-scan-one-preserves-pending-span-layout
  (implies (collection-scan-cursors-p header cell work)
           (collection-scan-cursors-p
            (collection-header-cursor-after-scan header work)
            (collection-cons-cursor-after-scan cell work)
            (collection-scan-one work)))
  :hints (("Goal"
           :in-theory (e/d (collection-scan-one)
                           (collection-scan-cursors-p collection-discover-fields
                            collection-scan-step-address collection-copy-bytes nth update-nth)))))

(defthm collection-empty-queues-start-at-allocation-frontiers
  (implies (collection-nonempty-copy-spans-p graph)
           (collection-scan-cursors-p lower upper
                                      (collection-work graph nil nil nil lower upper)))
  :hints (("Goal"
           :in-theory (enable collection-queued-spans-p collection-queue-frontier
                              collection-unseen collection-header-queue collection-cell-queue
                              collection-header-frontier collection-cell-frontier))))
