(in-package "BOYMOO-PROOFS")

(include-book "work")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable collection-unseen collection-forwarding)))

(defthm collection-unseen-lookup-after-discovering-fields
  (equal (assoc-equal address (collection-unseen (collection-discover-fields fields work)))
         (and (not (member-equal address fields))
              (assoc-equal address (collection-unseen work))))
  :hints (("Goal" :induct (collection-discover-fields fields work))))

(defun collection-fields-discovered-p (fields work)
  (if (endp fields)
      t
    (and (not (assoc-equal (car fields) (collection-unseen work)))
         (collection-fields-discovered-p (cdr fields) work))))

(defthm collection-all-requested-fields-are-discovered
  (collection-fields-discovered-p fields (collection-discover-fields fields work))
  :hints (("Goal" :induct (collection-discover-fields fields work))))

(defthm collection-discovery-preserves-discovered-fields
  (implies (collection-fields-discovered-p fields work)
           (collection-fields-discovered-p fields (collection-discover address work)))
  :hints (("Goal" :induct (len fields))))

(defun collection-graph-record-p (record)
  (and (consp record)
       (or (member-eq (cadr record) '(:cons :header))
           (and (eq (cadr record) :external) (endp (cdddr record))))))

; A discovered object is pending on one of the two cursors or has had
; every field discovered. An unseen object still has its original
; record, which supplies the fields when a cursor reaches its copy.
(defun collection-record-accounted-for-p (record work)
  (or (equal (assoc-equal (car record) (collection-unseen work)) record)
      (member-equal record (collection-cell-queue work))
      (member-equal record (collection-header-queue work))
      (collection-fields-discovered-p (cdddr record) work)))

(local
 (defthm collection-member-of-queue-with-new-object
   (iff (member-equal record (append queue (list item)))
        (or (member-equal record queue) (equal record item)))))

(local
 (defthm collection-discover-preserves-accounted-record
   (implies (and (collection-graph-record-p record)
                 (collection-record-accounted-for-p record work))
            (collection-record-accounted-for-p record (collection-discover address work)))
   :hints (("Goal" :use ((:instance collection-discovery-preserves-discovered-fields
                                    (fields (cdddr record)))
                         (:instance collection-discover-removes-only-its-object
                                    (query (car record))))
                   :in-theory (enable collection-discover collection-unseen
                                      collection-forwarding)))))

(local (in-theory (disable collection-record-accounted-for-p collection-graph-record-p)))

(defthm collection-field-discovery-preserves-accounted-record
  (implies (and (collection-graph-record-p record)
                (collection-record-accounted-for-p record work))
           (collection-record-accounted-for-p record (collection-discover-fields fields work)))
  :hints (("Goal" :induct (collection-discover-fields fields work))))

(local
 (defthm collection-fields-discovered-after-cursor-update
   (implies (or (equal cursor 2) (equal cursor 3))
            (equal (collection-fields-discovered-p fields (update-nth cursor queue work))
                   (collection-fields-discovered-p fields work)))
   :hints (("Goal" :induct (len fields)
                   :in-theory (e/d (collection-unseen) (nth update-nth))))))

(local
 (defthm collection-pop-preserves-other-records
   (implies (and (or (equal cursor 2) (equal cursor 3))
                 (not (equal record (car (nth cursor work))))
                 (collection-record-accounted-for-p record work))
            (collection-record-accounted-for-p
             record (update-nth cursor (cdr (nth cursor work)) work)))
   :hints (("Goal" :cases ((equal cursor 2))
                   :in-theory (e/d (collection-record-accounted-for-p collection-unseen)
                                     (nth update-nth))))))

(local
 (defthm collection-accounted-for-when-fields-discovered
   (implies (collection-fields-discovered-p (cdddr record) work)
            (collection-record-accounted-for-p record work))
   :hints (("Goal" :in-theory (enable collection-record-accounted-for-p)))))

(local
 (defthm collection-processing-queue-preserves-accounted-record
   (implies (and (or (equal cursor 2) (equal cursor 3))
                 (consp (nth cursor work))
                 (collection-graph-record-p record)
                 (collection-record-accounted-for-p record work))
            (collection-record-accounted-for-p
             record
             (collection-discover-fields (cdddar (nth cursor work))
                                         (update-nth cursor (cdr (nth cursor work)) work))))
   :hints (("Goal" :cases ((equal record (car (nth cursor work))))
                   :in-theory (disable collection-discover-fields nth update-nth)))))

(defthm collection-scan-one-preserves-accounted-record
  (implies (and (collection-graph-record-p record)
                (collection-record-accounted-for-p record work))
           (collection-record-accounted-for-p record (collection-scan-one work)))
  :hints (("Goal" :in-theory (e/d (collection-scan-one)
                                  (collection-discover-fields nth update-nth)))))

(defthm collection-scan-finish-preserves-accounted-record
  (implies (and (collection-graph-record-p record)
                (collection-record-accounted-for-p record work))
           (collection-record-accounted-for-p record (collection-finish-scan work)))
  :hints (("Goal" :induct (collection-finish-scan work))))

(defthm collection-finished-scan-discovers-fields-of-reached-record
  (let ((finished (collection-finish-scan work)))
    (implies (and (collection-graph-record-p record)
                  (collection-record-accounted-for-p record work)
                  (not (assoc-equal (car record) (collection-unseen finished))))
             (collection-fields-discovered-p (cdddr record) finished)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance collection-scan-finish-preserves-accounted-record)
                        (:instance collection-finish-scan-drains-both-queues))
                  :in-theory (enable collection-record-accounted-for-p
                                     collection-graph-record-p))))

(defun collection-traverse (roots graph lower upper)
  (collection-finish-scan
   (collection-discover-fields roots (collection-work graph nil nil nil lower upper))))

(local
 (defthm collection-unseen-after-cursor-update
   (implies (or (equal cursor 2) (equal cursor 3))
            (equal (collection-unseen (update-nth cursor queue work))
                   (collection-unseen work)))
   :hints (("Goal" :in-theory (e/d (collection-unseen) (nth update-nth))))))

(local
 (defthm collection-scan-cannot-restore-unseen
   (implies (not (assoc-equal address (collection-unseen work)))
            (not (assoc-equal address (collection-unseen (collection-scan-one work)))))
   :hints (("Goal" :in-theory (e/d (collection-scan-one)
                                     (collection-discover-fields nth update-nth))))))

(local
 (defthm collection-finish-cannot-restore-unseen
   (implies (not (assoc-equal address (collection-unseen work)))
            (not (assoc-equal address (collection-unseen (collection-finish-scan work)))))
   :hints (("Goal" :induct (collection-finish-scan work)))))

(defthm collection-traverse-discovers-roots
  (implies (member-equal address roots)
           (not (assoc-equal address
                             (collection-unseen (collection-traverse roots graph lower upper)))))
  :hints (("Goal" :in-theory (disable collection-discover-fields collection-finish-scan))))

(local
 (defthm collection-initial-graph-object-accounted-for
   (implies (equal (assoc-equal (car record) graph) record)
            (collection-record-accounted-for-p
             record (collection-work graph nil nil nil lower upper)))
   :hints (("Goal" :in-theory (enable collection-record-accounted-for-p collection-unseen)))))

(defthm collection-traverse-discovers-fields-of-reached-record
  (let ((finish (collection-traverse roots graph lower upper)))
    (implies (and (equal (assoc-equal (car record) graph) record)
                  (collection-graph-record-p record)
                  (not (assoc-equal (car record) (collection-unseen finish))))
             (collection-fields-discovered-p (cdddr record) finish)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-finished-scan-discovers-fields-of-reached-record
                            (work (collection-discover-fields
                                   roots (collection-work graph nil nil nil lower upper)))))
           :in-theory (disable collection-discover-fields collection-finish-scan
                               collection-work))))

(local
 (defthm collection-discovered-field-members-have-left-unseen
   (implies (and (collection-fields-discovered-p fields work)
                 (member-equal address fields))
            (not (assoc-equal address (collection-unseen work))))
   :hints (("Goal" :induct (len fields)))))

(defun collection-edge-path-p (path graph)
  (if (or (endp path) (endp (cdr path)))
      t
    (let ((record (assoc-equal (car path) graph)))
      (and (collection-graph-record-p record)
           (member-equal (cadr path) (cdddr record))
           (collection-edge-path-p (cdr path) graph)))))

(local
 (defthm collection-follow-reached-edge
   (implies (and (let ((record (assoc-equal parent graph)))
                   (and (collection-graph-record-p record)
                        (equal (car record) parent)
                        (member-equal child (cdddr record))))
                 (not (assoc-equal parent
                                   (collection-unseen
                                    (collection-traverse roots graph lower upper)))))
            (not (assoc-equal child (collection-unseen
                                     (collection-traverse roots graph lower upper)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance collection-traverse-discovers-fields-of-reached-record
                                    (record (assoc-equal parent graph))))
                   :in-theory (disable collection-traverse)))))

(local
 (defthm collection-assoc-has-original-key
   (implies (assoc-equal address graph)
            (equal (car (assoc-equal address graph)) address))))

(local
 (defthm collection-valid-record-is-consp
   (implies (collection-graph-record-p record) (consp record))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (enable collection-graph-record-p)))))

(defthm collection-traverse-discovers-reachable-path
  (let ((finish (collection-traverse roots graph lower upper)))
    (implies (and (collection-edge-path-p path graph)
                  (not (assoc-equal (car path) (collection-unseen finish))))
             (collection-fields-discovered-p path finish)))
  :hints (("Goal" :induct (collection-edge-path-p path graph)
                  :in-theory (disable collection-traverse assoc-equal)
                  :do-not '(generalize))
          (and stable-under-simplificationp
               '(:use ((:instance collection-follow-reached-edge
                                  (parent (car path)) (child (cadr path))))))))

(defun collection-known-address-p (address work)
  (or (assoc-equal address (collection-unseen work))
      (assoc-equal address (collection-forwarding work))))

(local
 (defthm collection-discover-preserves-known-addresses
   (iff (collection-known-address-p query (collection-discover address work))
        (collection-known-address-p query work))
   :hints (("Goal" :use ((:instance collection-discover-removes-only-its-object))
                   :in-theory (enable collection-discover collection-unseen
                                       collection-forwarding)))))

(local
 (defthm collection-cursor-update-preserves-known-addresses
   (implies (or (equal cursor 2) (equal cursor 3))
            (equal (collection-known-address-p query (update-nth cursor queue work))
                   (collection-known-address-p query work)))
   :hints (("Goal" :in-theory (e/d (collection-unseen collection-forwarding)
                                     (nth update-nth))))))

(local (in-theory (disable collection-known-address-p)))

(local
 (defthm collection-discover-fields-preserves-known-addresses
   (iff (collection-known-address-p address (collection-discover-fields fields work))
        (collection-known-address-p address work))
   :hints (("Goal" :induct (collection-discover-fields fields work)))))

(local
 (defthm collection-scan-one-preserves-known-addresses
   (iff (collection-known-address-p address (collection-scan-one work))
        (collection-known-address-p address work))
   :hints (("Goal" :in-theory (e/d (collection-scan-one)
                                     (nth update-nth collection-discover-fields))))))

(local
 (defthm collection-finish-scan-preserves-known-addresses
   (iff (collection-known-address-p address (collection-finish-scan work))
        (collection-known-address-p address work))
   :hints (("Goal" :induct (collection-finish-scan work)))))

(local
 (defthm collection-initially-knows-source-addresses
   (iff (collection-known-address-p address (collection-work graph nil nil nil low high))
        (assoc-equal address graph))
   :hints (("Goal" :in-theory (enable collection-known-address-p
                                      collection-unseen collection-forwarding)))))

(defthm collection-traversal-keeps-source-domain
  (iff (collection-known-address-p address (collection-traverse roots graph lower upper))
       (assoc-equal address graph))
  :hints (("Goal" :in-theory (disable collection-work collection-discover-fields
                                      collection-finish-scan))))

(defthm collection-traversal-assigns-every-reachable-object
  (implies (and (member-equal (car path) roots)
                (collection-edge-path-p path graph)
                (member-equal address path) (assoc-equal address graph))
           (assoc-equal address
                        (collection-forwarding (collection-traverse roots graph lower upper))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-traverse-discovers-reachable-path)
                 (:instance collection-traversal-keeps-source-domain)
                 (:instance collection-discovered-field-members-have-left-unseen
                            (fields path) (work (collection-traverse roots graph lower upper))))
           :in-theory (e/d (collection-known-address-p)
                           (collection-traverse collection-edge-path-p
                            collection-fields-discovered-p assoc-equal
                            collection-traversal-keeps-source-domain)))))

(defun collection-forwarding-agrees-p (address entry work)
  (and (not (assoc-equal address (collection-unseen work)))
       (equal (assoc-equal address (collection-forwarding work)) entry)))

(local
 (defthm collection-discovery-keeps-forwarding-association
   (implies (collection-forwarding-agrees-p query entry work)
            (collection-forwarding-agrees-p query entry (collection-discover address work)))
   :hints (("Goal" :use ((:instance collection-discover-removes-only-its-object))
                   :in-theory (enable collection-discover collection-unseen
                                       collection-forwarding)))))

(local
 (defthm collection-cursor-update-keeps-forwarding-association
   (implies (or (equal cursor 2) (equal cursor 3))
            (equal (collection-forwarding-agrees-p address entry (update-nth cursor queue work))
                   (collection-forwarding-agrees-p address entry work)))
   :hints (("Goal" :in-theory (e/d (collection-unseen collection-forwarding)
                                     (nth update-nth))))))

(local (in-theory (disable collection-forwarding-agrees-p)))

(local
 (defthm collection-field-discovery-keeps-forwarding-association
   (implies (collection-forwarding-agrees-p address entry work)
            (collection-forwarding-agrees-p address entry (collection-discover-fields fields work)))
   :hints (("Goal" :induct (collection-discover-fields fields work)))))

(local
 (defthm collection-scan-keeps-forwarding-association
   (implies (collection-forwarding-agrees-p address entry work)
            (collection-forwarding-agrees-p address entry (collection-scan-one work)))
   :hints (("Goal" :in-theory (e/d (collection-scan-one)
                                     (nth update-nth collection-discover-fields))))))

(defthm collection-finish-scan-keeps-forwarding-association
  (implies (collection-forwarding-agrees-p address entry work)
           (collection-forwarding-agrees-p address entry (collection-finish-scan work)))
  :hints (("Goal" :induct (collection-finish-scan work))))
