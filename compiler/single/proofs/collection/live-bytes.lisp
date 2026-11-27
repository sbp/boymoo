(in-package "BOYMOO-PROOFS")

(include-book "published")
(include-book "budget")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-assigned-bytes (forwarding graph)
  (if (endp forwarding)
      0
    (+ (collection-copy-bytes (assoc-equal (caar forwarding) graph))
       (collection-assigned-bytes (cdr forwarding) graph))))

(defun collection-frontiers-account-for-assigned-bytes-p (work graph floor end)
  (and (integerp floor) (integerp end)
       (integerp (collection-header-frontier work))
       (integerp (collection-cell-frontier work))
       (collection-source-records-p (collection-unseen work) graph)
       (equal (collection-retained-bytes floor (collection-header-frontier work)
                                         (collection-cell-frontier work) end)
              (collection-assigned-bytes (collection-forwarding work) graph))))

(local
 (in-theory (disable collection-source-records-p collection-unseen collection-forwarding
                     collection-header-frontier collection-cell-frontier)))

(local
 (defthm collection-forwarding-after-discovery-is-original-or-extended
   (let ((record (assoc-equal address (collection-unseen work))))
     (equal (collection-forwarding (collection-discover address work))
            (if record
                (acons address (collection-copy-address record work) (collection-forwarding work))
              (collection-forwarding work))))
   :hints (("Goal" :in-theory (enable collection-discover collection-forwarding)))))

(local
 (defthm collection-discovery-accounts-for-exact-record-size
   (let* ((record (assoc-equal address (collection-unseen work)))
          (next (collection-discover address work)))
     (implies (collection-source-records-p (collection-unseen work) graph)
              (equal (collection-assigned-bytes (collection-forwarding next) graph)
                     (+ (collection-copy-bytes record)
                        (collection-assigned-bytes (collection-forwarding work) graph)))))
   :hints (("Goal" :use ((:instance collection-source-lookup-agrees-with-graph
                                    (records (collection-unseen work))))))))

(local
 (defthm collection-discovery-keeps-unseen-source-records
   (implies (collection-source-records-p (collection-unseen work) graph)
            (collection-source-records-p (collection-unseen (collection-discover address work)) graph))
   :hints (("Goal" :in-theory (enable collection-discover collection-unseen)))))

(defthm collection-discovery-keeps-exact-frontier-accounting
  (implies (collection-frontiers-account-for-assigned-bytes-p work graph floor end)
           (collection-frontiers-account-for-assigned-bytes-p (collection-discover address work) graph floor end))
  :hints (("Goal" :in-theory (disable collection-forwarding-after-discovery-is-original-or-extended))))

(local (in-theory (disable collection-frontiers-account-for-assigned-bytes-p)))

(local
 (defthm collection-discover-fields-keeps-exact-frontier-accounting
   (implies (collection-frontiers-account-for-assigned-bytes-p work graph floor end)
            (collection-frontiers-account-for-assigned-bytes-p (collection-discover-fields fields work)
                                                              graph floor end))
   :hints (("Goal" :induct (collection-discover-fields fields work)))))

(local
 (defthm collection-queue-update-keeps-exact-frontier-accounting
   (implies (member-eq slot '(2 3))
            (equal (collection-frontiers-account-for-assigned-bytes-p
                    (update-nth slot queue work) graph floor end)
                   (collection-frontiers-account-for-assigned-bytes-p work graph floor end)))
   :hints (("Goal"
            :in-theory (e/d (collection-frontiers-account-for-assigned-bytes-p
                             collection-header-frontier collection-cell-frontier
                             collection-unseen collection-forwarding)
                            (nth update-nth))))))

(local
 (defthm collection-scan-one-keeps-exact-frontier-accounting
   (implies (collection-frontiers-account-for-assigned-bytes-p work graph floor end)
            (collection-frontiers-account-for-assigned-bytes-p (collection-scan-one work) graph floor end))
   :hints (("Goal" :in-theory (e/d (collection-scan-one) (nth update-nth collection-discover-fields))))))

(defthm collection-scan-keeps-exact-frontier-accounting
  (implies (collection-frontiers-account-for-assigned-bytes-p work graph floor end)
           (collection-frontiers-account-for-assigned-bytes-p (collection-finish-scan work) graph floor end))
  :hints (("Goal" :induct (collection-finish-scan work))))

(local
 (defthm collection-empty-frontiers-account-for-zero-assigned-bytes
   (implies (and (integerp floor) (integerp end) (collection-source-records-p graph graph))
            (collection-frontiers-account-for-assigned-bytes-p
             (collection-work graph nil nil nil floor end) graph floor end))
   :hints (("Goal" :in-theory (enable collection-frontiers-account-for-assigned-bytes-p
                                      collection-unseen collection-forwarding
                                      collection-header-frontier collection-cell-frontier)))))

(defthm collection-traversal-frontiers-count-exactly-assigned-bytes
  (let ((work (collection-traverse roots graph floor end)))
    (implies (and (integerp floor) (integerp end) (collection-source-records-p graph graph))
             (equal (collection-retained-bytes floor (collection-header-frontier work)
                                               (collection-cell-frontier work) end)
                    (collection-assigned-bytes (collection-forwarding work) graph))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-empty-frontiers-account-for-zero-assigned-bytes)
                 (:instance collection-discover-fields-keeps-exact-frontier-accounting
                            (fields roots) (work (collection-work graph nil nil nil floor end)))
                 (:instance collection-scan-keeps-exact-frontier-accounting
                            (work (collection-discover-fields roots (collection-work graph nil nil nil floor end)))))
           :in-theory (e/d (collection-frontiers-account-for-assigned-bytes-p
                            collection-header-frontier collection-cell-frontier
                            collection-forwarding collection-unseen)
                           (collection-discover-fields collection-finish-scan
                            collection-discover-fields-keeps-exact-frontier-accounting
                            collection-scan-keeps-exact-frontier-accounting)))))
