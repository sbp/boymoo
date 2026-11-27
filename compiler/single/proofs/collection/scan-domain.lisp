(in-package "BOYMOO-PROOFS")

(include-book "scan-fields")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-load-word proof-pointer-address proof-object-size
                     proof-header-size proof-header-type proof-word-tag
                     collection-reference-fields collection-discover collection-known-address-p
                     collection-forwarding collection-unseen
                     boymoo-model::a64-unsigned (:definition ash))))

(local
 (defthm collection-extraction-includes-movable-object-map-keys
   (let ((object (assoc-equal address pending)))
     (implies (and object
                   (member-eq (proof-object-zone object) '(:active :external)))
              (assoc-equal address (collection-published-object-graph pending base objects machine))))
   :hints (("Goal" :induct (assoc-equal address pending)))))

(defthm collection-movable-reference-is-an-extracted-graph-key
  (let ((source (collection-movable-reference word base objects)))
    (implies source
             (assoc-equal source (collection-published-object-graph objects base objects machine))))
  :hints (("Goal" :in-theory (disable collection-published-object-graph))))

(defun collection-work-knows-graph-p (graph work)
  (or (endp graph)
      (and (collection-known-address-p (caar graph) work)
           (collection-work-knows-graph-p (cdr graph) work))))

(local
 (defthm collection-covered-graph-key-is-known
   (implies (and (collection-work-knows-graph-p graph work)
                 (assoc-equal address graph))
            (collection-known-address-p address work))
   :rule-classes nil
   :hints (("Goal" :induct (assoc-equal address graph)))))

(local
 (defthm collection-initial-work-knows-each-source-record
   (implies (collection-source-records-p pending graph)
            (collection-work-knows-graph-p pending (collection-work graph nil nil nil lower upper)))
   :hints (("Goal"
            :induct (collection-source-records-p pending graph)
            :in-theory (enable collection-known-address-p collection-unseen collection-forwarding)))))

(defthm collection-initial-work-knows-its-graph
  (implies (collection-source-records-p graph graph)
           (collection-work-knows-graph-p graph (collection-work graph nil nil nil lower upper)))
  :hints (("Goal"
           :use ((:instance collection-initial-work-knows-each-source-record (pending graph)))
           :in-theory (disable collection-initial-work-knows-each-source-record
                               collection-source-records-p collection-work-knows-graph-p collection-work))))

(local
 (defthm collection-known-sources-survive-field-discovery
   (iff (collection-known-address-p address (collection-discover-fields fields work))
        (collection-known-address-p address work))
   :hints (("Goal" :induct (collection-discover-fields fields work)))))

(local
 (defthm collection-known-source-survives-cursor-update
   (implies (or (equal cursor 2) (equal cursor 3))
            (equal (collection-known-address-p address (update-nth cursor queue work))
                   (collection-known-address-p address work)))
   :hints (("Goal"
            :in-theory (e/d (collection-known-address-p collection-unseen collection-forwarding)
                             (nth update-nth))))))

(local
 (defthm collection-known-sources-survive-scan-one
   (iff (collection-known-address-p address (collection-scan-one work))
        (collection-known-address-p address work))
   :hints (("Goal"
            :in-theory (e/d (collection-scan-one)
                             (nth update-nth collection-discover-fields))))))

(defthm collection-field-discovery-keeps-graph-domain
  (implies (collection-work-knows-graph-p graph work)
           (collection-work-knows-graph-p graph (collection-discover-fields fields work)))
  :hints (("Goal" :induct (collection-work-knows-graph-p graph work)
                  :in-theory (disable collection-discover-fields))))

(defthm collection-scanning-keeps-graph-domain
  (implies (collection-work-knows-graph-p graph work)
           (collection-work-knows-graph-p graph (collection-scan-one work)))
  :hints (("Goal" :induct (collection-work-knows-graph-p graph work))))

(local
 (in-theory (disable collection-movable-reference collection-published-object-graph
                     collection-work-knows-graph-p)))

(defthm collection-graph-domain-supplies-known-slot-sources
  (let ((graph (collection-published-object-graph objects base objects machine)))
    (implies (collection-work-knows-graph-p graph work)
             (collection-slot-sources-known-p count address base objects machine work)))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-slot-sources-known-p count address base objects machine work))
          ("Subgoal *1/3"
           :use ((:instance collection-covered-graph-key-is-known
                            (graph (collection-published-object-graph objects base objects machine))
                            (address (collection-movable-reference
                                      (proof-load-word address machine) base objects)))))))
