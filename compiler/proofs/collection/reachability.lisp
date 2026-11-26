(in-package "BOYMOO-PROOFS")

(include-book "closure")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm collection-lookup-has-queried-address
   (implies (assoc-equal address entries)
            (equal (car (assoc-equal address entries)) address))))

; A reverse path starts at the discovered address and ends at a root.
; Extending a witness by one edge adds one address to the front.
(defun collection-reverse-path-p (path roots graph)
  (and (consp path)
       (if (endp (cdr path))
           (member-equal (car path) roots)
         (let ((parent (assoc-equal (cadr path) graph)))
           (and (collection-graph-record-p parent)
                (member-equal (car path) (cdddr parent))
                (collection-reverse-path-p (cdr path) roots graph))))))

(local
 (defthm collection-a-path-has-an-endpoint
   (implies (collection-reverse-path-p path roots graph) (consp path))
   :rule-classes :forward-chaining))

(local
 (defthm collection-prepend-path-edge
   (implies (and (collection-reverse-path-p parent roots graph)
                 (collection-graph-record-p (assoc-equal (car parent) graph))
                 (member-equal child (cdddr (assoc-equal (car parent) graph))))
            (collection-reverse-path-p (cons child parent) roots graph))
   :hints (("Goal" :expand ((collection-reverse-path-p (cons child parent) roots graph))
                   :in-theory (disable collection-reverse-path-p
                                       collection-graph-record-p)))))

(defun collection-path-table-p (entries roots graph)
  (if (endp entries)
      t
    (let ((entry (car entries)))
      (and (equal (car entry) (cadr entry))
           (collection-reverse-path-p (cdr entry) roots graph)
           (collection-path-table-p (cdr entries) roots graph)))))

(defun collection-remember-path (address parent paths)
  (if (assoc-equal address paths)
      paths
    (acons address (cons address parent) paths)))

(local
 (defthm collection-path-lookup-is-a-witness
   (implies (and (collection-path-table-p paths roots graph)
                 (assoc-equal address paths))
            (and (equal (cadr (assoc-equal address paths)) address)
                 (collection-reverse-path-p
                  (cdr (assoc-equal address paths)) roots graph)))
   :hints (("Goal" :induct (assoc-equal address paths)
                   :in-theory (disable collection-reverse-path-p)))))

(local
 (defthm collection-remembered-path-domain
   (iff (assoc-equal query (collection-remember-path address parent paths))
        (or (equal query address) (assoc-equal query paths)))))

(local
 (defthm collection-remember-path-preserves-witnesses
   (implies (and (collection-path-table-p paths roots graph)
                 (collection-reverse-path-p (cons address parent) roots graph))
            (collection-path-table-p
             (collection-remember-path address parent paths) roots graph))
   :hints (("Goal" :in-theory (disable collection-reverse-path-p)))))

(defun collection-remember-fields (fields parent paths)
  (if (endp fields)
      paths
    (collection-remember-fields (cdr fields) parent
                                (collection-remember-path (car fields) parent paths))))

(local (in-theory (disable collection-remember-path)))

(local
 (defthm collection-remembered-fields-domain
   (iff (assoc-equal query (collection-remember-fields fields parent paths))
        (or (member-equal query fields) (assoc-equal query paths)))
   :hints (("Goal" :induct (collection-remember-fields fields parent paths)))))

(local
 (defthm collection-paths-for-root-fields
   (implies (and (collection-path-table-p paths roots graph)
                 (subsetp-equal fields roots))
            (collection-path-table-p
             (collection-remember-fields fields nil paths) roots graph))
   :hints (("Goal" :induct (collection-remember-fields fields nil paths)))))

(local
 (defthm collection-paths-for-child-fields
   (implies (and (collection-path-table-p paths roots graph)
                 (collection-reverse-path-p parent roots graph)
                 (collection-graph-record-p (assoc-equal (car parent) graph))
                 (subsetp-equal fields (cdddr (assoc-equal (car parent) graph))))
            (collection-path-table-p
             (collection-remember-fields fields parent paths) roots graph))
   :hints (("Goal" :induct (collection-remember-fields fields parent paths)
                   :in-theory (disable collection-reverse-path-p
                                       collection-graph-record-p)))))

(defun collection-source-records-p (records graph)
  (if (endp records)
      t
    (and (collection-graph-record-p (car records))
         (equal (assoc-equal (caar records) graph) (car records))
         (collection-source-records-p (cdr records) graph))))

(defthm collection-source-lookup-agrees-with-graph
  (implies (and (collection-source-records-p records graph)
                (assoc-equal address records))
           (and (collection-graph-record-p (assoc-equal address records))
                (equal (assoc-equal address records) (assoc-equal address graph))))
  :rule-classes nil
  :hints (("Goal" :induct (assoc-equal address records))))

(defthm collection-source-records-after-removal
  (implies (collection-source-records-p records graph)
           (collection-source-records-p (remove-assoc-equal address records) graph))
  :hints (("Goal" :induct (remove-assoc-equal address records))))

(local
 (defthm collection-source-records-after-append
   (equal (collection-source-records-p (append first second) graph)
          (and (collection-source-records-p first graph)
               (collection-source-records-p second graph)))))

(defun collection-addresses-covered-p (records paths)
  (if (endp records)
      t
    (and (assoc-equal (caar records) paths)
         (collection-addresses-covered-p (cdr records) paths))))

(local
 (defthm collection-covered-after-append
   (equal (collection-addresses-covered-p (append first second) paths)
          (and (collection-addresses-covered-p first paths)
               (collection-addresses-covered-p second paths)))))

(local
 (defthm collection-covered-after-remembering
   (implies (collection-addresses-covered-p records paths)
            (collection-addresses-covered-p
             records (collection-remember-path address parent paths)))
   :hints (("Goal" :induct (collection-addresses-covered-p records paths)))))

(local
 (defthm collection-lookup-of-covered-address
   (implies (and (collection-addresses-covered-p records paths)
                 (assoc-equal address records))
            (assoc-equal address paths))
   :hints (("Goal" :induct (assoc-equal address records)))))

(defun collection-path-work-p (work paths graph)
  (and (collection-source-records-p (collection-unseen work) graph)
       (collection-source-records-p (collection-cell-queue work) graph)
       (collection-source-records-p (collection-header-queue work) graph)
       (collection-addresses-covered-p (collection-cell-queue work) paths)
       (collection-addresses-covered-p (collection-header-queue work) paths)
       (collection-addresses-covered-p (collection-forwarding work) paths)))

(local
 (defthm collection-discover-preserves-path-work
   (implies (collection-path-work-p work paths graph)
            (collection-path-work-p (collection-discover address work)
                                    (collection-remember-path address parent paths)
                                    graph))
   :hints (("Goal"
            :use ((:instance collection-source-lookup-agrees-with-graph
                             (records (collection-unseen work))))
            :in-theory (enable collection-discover)))))

(local (in-theory (disable collection-path-work-p)))

(local
 (defun collection-path-field-induction (fields work parent paths)
   (if (endp fields)
       (list work paths)
     (collection-path-field-induction
      (cdr fields) (collection-discover (car fields) work) parent
      (collection-remember-path (car fields) parent paths)))))

(local
 (defthm collection-discover-fields-preserves-path-work
   (implies (collection-path-work-p work paths graph)
            (collection-path-work-p (collection-discover-fields fields work)
                                    (collection-remember-fields fields parent paths)
                                    graph))
   :hints (("Goal" :induct (collection-path-field-induction fields work parent paths)
                   :expand ((collection-discover-fields fields work)
                            (collection-remember-fields fields parent paths))
                   :in-theory (disable collection-discover-fields
                                       collection-remember-fields)))))

(defun collection-scan-paths (work paths)
  (let ((queue (if (consp (collection-cell-queue work))
                   (collection-cell-queue work)
                 (collection-header-queue work))))
    (if (consp queue)
        (collection-remember-fields
         (cdddar queue) (cdr (assoc-equal (caar queue) paths)) paths)
      paths)))

(local
 (defthm collection-pop-preserves-path-work
   (implies (and (or (equal cursor 2) (equal cursor 3))
                 (collection-path-work-p work paths graph))
            (collection-path-work-p
             (update-nth cursor (cdr (nth cursor work)) work) paths graph))
   :hints (("Goal" :cases ((equal cursor 2))
                   :in-theory (e/d (collection-path-work-p) (nth update-nth))))))

(local
 (defthm collection-scan-one-preserves-path-work
   (implies (collection-path-work-p work paths graph)
            (collection-path-work-p (collection-scan-one work)
                                    (collection-scan-paths work paths) graph))
   :hints (("Goal" :use ((:instance collection-pop-preserves-path-work (cursor 2))
                         (:instance collection-pop-preserves-path-work (cursor 3)))
                   :in-theory (e/d (collection-scan-one)
                                   (collection-remember-fields collection-discover-fields
                                    nth update-nth))))))

(local
 (defthm collection-subset-remains-after-cons
   (implies (subsetp-equal fields entries)
            (subsetp-equal fields (cons value entries)))
   :hints (("Goal" :induct (len fields)))))

(local
 (defthm collection-subset-reflexive
   (subsetp-equal entries entries)
   :hints (("Goal" :induct (len entries)))))

(local
 (defthm collection-paths-for-queue-head
   (implies (and (consp queue)
                 (collection-source-records-p queue graph)
                 (collection-addresses-covered-p queue paths)
                 (collection-path-table-p paths roots graph))
            (collection-path-table-p
             (collection-remember-fields
              (cdddar queue) (cdr (assoc-equal (caar queue) paths)) paths)
             roots graph))
   :hints (("Goal"
            :use ((:instance collection-paths-for-child-fields
                             (parent (cdr (assoc-equal (caar queue) paths)))
                             (fields (cdddar queue))))
            :expand ((collection-source-records-p queue graph)
                     (collection-addresses-covered-p queue paths))
            :in-theory (disable collection-path-table-p collection-reverse-path-p
                                collection-remember-fields
                                collection-paths-for-child-fields
                                collection-graph-record-p)))))

(local
 (defthm collection-scan-one-preserves-path-table
   (implies (and (collection-path-work-p work paths graph)
                 (collection-path-table-p paths roots graph))
            (collection-path-table-p (collection-scan-paths work paths) roots graph))
   :hints (("Goal" :in-theory (e/d (collection-path-work-p)
                                   (collection-remember-fields collection-path-table-p)))
           (and stable-under-simplificationp
                '(:in-theory (enable collection-remember-fields))))))

(defun collection-finish-paths (work paths)
  (declare (xargs :measure (collection-work-size work)
                  :hints (("Goal" :in-theory (disable collection-scan-one)))))
  (if (or (consp (collection-cell-queue work))
          (consp (collection-header-queue work)))
      (collection-finish-paths (collection-scan-one work)
                               (collection-scan-paths work paths))
    paths))

(local
 (defthm collection-finish-paths-preserves-invariants
   (implies (and (collection-path-work-p work paths graph)
                 (collection-path-table-p paths roots graph))
            (let ((final-paths (collection-finish-paths work paths)))
              (and (collection-path-work-p (collection-finish-scan work)
                                           final-paths graph)
                   (collection-path-table-p final-paths roots graph))))
   :hints (("Goal" :induct (collection-finish-paths work paths)
                   :in-theory (disable collection-scan-paths collection-path-table-p
                                       collection-cell-queue collection-header-queue)))))

(defun collection-traversal-paths (roots graph lower upper)
  (collection-finish-paths
   (collection-discover-fields roots (collection-work graph nil nil nil lower upper))
   (collection-remember-fields roots nil nil)))

(local
 (defthm collection-initial-work-has-empty-path-table
   (implies (collection-source-records-p graph graph)
            (collection-path-work-p
             (collection-work graph nil nil nil lower upper) nil graph))
   :hints (("Goal" :in-theory (enable collection-path-work-p)))))

(local
 (defthm collection-forwarding-lookup-has-path-witness
   (implies (and (collection-path-work-p work paths graph)
                 (collection-path-table-p paths roots graph)
                 (assoc-equal address (collection-forwarding work)))
            (let ((path (cdr (assoc-equal address paths))))
              (and (equal (car path) address)
                   (collection-reverse-path-p path roots graph))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-lookup-of-covered-address
                             (records (collection-forwarding work)))
                  (:instance collection-path-lookup-is-a-witness))
            :in-theory (e/d (collection-path-work-p)
                            (collection-path-table-p collection-reverse-path-p
                             collection-path-lookup-is-a-witness
                             collection-lookup-of-covered-address))))))

(defthm collection-traversal-forwards-only-reachable-objects
  (let ((work (collection-traverse roots graph lower upper))
        (paths (collection-traversal-paths roots graph lower upper)))
    (implies (and (collection-source-records-p graph graph)
                  (assoc-equal address (collection-forwarding work)))
             (let ((path (cdr (assoc-equal address paths))))
               (and (equal (car path) address)
                    (collection-reverse-path-p path roots graph)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-finish-paths-preserves-invariants
                            (work (collection-discover-fields
                                   roots (collection-work graph nil nil nil lower upper)))
                            (paths (collection-remember-fields roots nil nil)))
                 (:instance collection-forwarding-lookup-has-path-witness
                            (work (collection-traverse roots graph lower upper))
                            (paths (collection-traversal-paths roots graph lower upper))))
           :in-theory (disable collection-finish-paths collection-finish-scan
                               collection-work collection-discover-fields collection-remember-fields
                               collection-reverse-path-p
                               collection-finish-paths-preserves-invariants))))
