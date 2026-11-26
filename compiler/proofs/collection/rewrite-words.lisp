(in-package "BOYMOO-PROOFS")

(include-book "published")
(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

; A datum contributes scan work only if it names a movable object or an
; external mapping. Its relocation changes the datum bits only for a
; movable object that has been assigned a destination.
(defun collection-discover-datum (word base objects work)
  (let ((address (collection-movable-reference word base objects)))
    (if address (collection-discover address work) work)))

(defun collection-relocate-datum (word base objects work)
  (let* ((address (collection-movable-reference word base objects))
         (entry (and address (assoc-equal address (collection-forwarding work)))))
    (if (and entry (eq (proof-object-zone (assoc-equal address objects)) :active))
        (boymoo-model::a64-unsigned 64 (+ (- (cdr entry) base) (proof-word-tag word)))
      word)))

(defun collection-rewrite-slots (count address base objects machine work)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (mv nil work)
    (let* ((word (proof-load-word address machine))
           (next (collection-discover-datum word base objects work))
           (copy (collection-relocate-datum word base objects next)))
      (mv-let (remaining final)
        (collection-rewrite-slots (1- count) (+ 8 address) base objects machine next)
        (mv (cons copy remaining) final)))))

(local
 (in-theory (disable proof-load-word proof-word-tag proof-pointer-address
                     collection-movable-reference collection-discover collection-forwarding
                     collection-unseen boymoo-model::a64-unsigned)))

(defthm collection-slot-rewrites-discover-exactly-the-graph-edges
  (equal (mv-nth 1 (collection-rewrite-slots count address base objects machine work))
         (collection-discover-fields
          (collection-reference-fields count address base objects machine) work))
  :hints (("Goal" :induct (collection-rewrite-slots count address base objects machine work)
                  :in-theory (disable collection-relocate-datum))))

(defun collection-datum-assigned-p (word base objects work)
  (let* ((address (collection-movable-reference word base objects))
         (entry (assoc-equal address (collection-forwarding work))))
    (or (not address)
        (and entry (collection-forwarding-agrees-p address entry work)))))

(defun collection-slot-sources-known-p (count address base objects machine work)
  (declare (xargs :measure (nfix count)))
  (or (zp count)
      (let ((source (collection-movable-reference (proof-load-word address machine) base objects)))
        (and (or (not source) (collection-known-address-p source work))
             (collection-slot-sources-known-p (1- count) (+ 8 address) base objects machine work)))))

(defun collection-relocated-slot-list (count address base objects machine work)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (collection-relocate-datum (proof-load-word address machine) base objects work)
          (collection-relocated-slot-list (1- count) (+ 8 address) base objects machine work))))

(defthm collection-discover-datum-establishes-its-assignment
  (let ((source (collection-movable-reference word base objects)))
    (implies (or (not source) (collection-known-address-p source work))
             (collection-datum-assigned-p word base objects
                                          (collection-discover-datum word base objects work)))))

(local
 (defthm collection-word-discovery-preserves-known-source
   (implies (collection-known-address-p source work)
            (collection-known-address-p source (collection-discover-datum word base objects work)))))

(local
 (defthm collection-word-discovery-keeps-slot-sources-known
   (implies (collection-slot-sources-known-p count address base objects machine work)
            (collection-slot-sources-known-p count address base objects machine
                                            (collection-discover-datum word base objects work)))
   :hints (("Goal" :induct (collection-slot-sources-known-p count address base objects machine work)
                   :in-theory (disable collection-discover-datum collection-known-address-p)))))

(local
 (defthm collection-field-discovery-preserves-existing-lookup
   (implies (collection-forwarding-agrees-p source entry work)
            (collection-forwarding-agrees-p source entry (collection-discover-fields fields work)))
   :hints (("Goal" :induct (collection-discover-fields fields work)))))

(local
 (defthm collection-relocated-datum-agrees-after-slot-discovery
   (let ((next (mv-nth 1 (collection-rewrite-slots count address base objects machine work))))
     (implies (collection-datum-assigned-p word base objects work)
              (and (collection-datum-assigned-p word base objects next)
                   (equal (collection-relocate-datum word base objects next)
                          (collection-relocate-datum word base objects work)))))
   :hints (("Goal"
            :use ((:instance collection-field-discovery-preserves-existing-lookup
                             (source (collection-movable-reference word base objects))
                             (entry (assoc-equal (collection-movable-reference word base objects)
                                                 (collection-forwarding work)))
                             (fields (collection-reference-fields count address base objects machine))))
            :in-theory (disable collection-rewrite-slots collection-discover-fields
                                collection-field-discovery-preserves-existing-lookup)))))

(defthm collection-slot-rewrites-agree-with-resulting-forwarding-map
  (mv-let (rewritten final)
    (collection-rewrite-slots count address base objects machine work)
    (implies (collection-slot-sources-known-p count address base objects machine work)
             (equal rewritten (collection-relocated-slot-list count address base objects machine final))))
  :hints (("Goal" :induct (collection-rewrite-slots count address base objects machine work)
                  :in-theory (disable collection-discover-datum collection-known-address-p
                                      collection-relocate-datum collection-datum-assigned-p
                                      collection-slot-rewrites-discover-exactly-the-graph-edges))
          ("Subgoal *1/2"
           :use ((:instance collection-discover-datum-establishes-its-assignment
                            (word (proof-load-word address machine)))))))

(defthm collection-assigned-datum-stays-at-its-destination-through-scan
  (implies (collection-datum-assigned-p word base objects work)
           (equal (collection-relocate-datum word base objects (collection-finish-scan work))
                  (collection-relocate-datum word base objects work)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-finish-scan-keeps-forwarding-association
                            (address (collection-movable-reference word base objects))
                            (entry (assoc-equal (collection-movable-reference word base objects)
                                                (collection-forwarding work)))))
           :in-theory (disable collection-finish-scan-keeps-forwarding-association))))
