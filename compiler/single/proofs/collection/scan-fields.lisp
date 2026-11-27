(in-package "BOYMOO-PROOFS")

(include-book "slot-rewrites")
(include-book "exactness")

(logic)
(set-verify-guards-eagerness 0)

; A committed slot contains the relocation of its original word under
; the current forwarding map. An immediate or static word needs no
; assignment. A movable word or external reference needs a stable one.
(local
 (in-theory (disable collection-read-word proof-load-word
                     collection-movable-reference collection-known-address-p
                     collection-discover collection-relocate-datum
                     collection-forwarding collection-unseen
                     collection-work collection-slot-words
                     collection-reference-fields collection-rewrite-slots
                     proof-world-machine proof-world-reg proof-heap-base
                     proof-inactive-floor proof-inactive-end
                     proof-stack-base proof-stack-top
                     proof-dynamic-root proof-pointer-address proof-word-tag
                     boymoo-model::a64-unsigned boymoo-model::a64-load
                     boymoo-model::a64-read-bytes boymoo-model::a64-memory
                     (:definition ash))))

(defun collection-scanned-fields-p (count source target base objects original current work)
  (declare (xargs :measure (nfix count)
                  :hints (("Goal" :in-theory (disable collection-datum-assigned-p)))))
  (or (zp count)
      (let ((word (collection-read-word source original)))
        (and (collection-datum-assigned-p word base objects work)
             (equal (collection-read-word target current)
                    (collection-relocate-datum word base objects work))
             (collection-scanned-fields-p (1- count) (+ source 8) (+ target 8)
                                          base objects original current work)))))

(local
 (defthm collection-original-word-is-machine-lookup
   (equal (proof-load-word address (proof-world-machine world))
          (collection-read-word address world))
   :hints (("Goal" :in-theory (enable collection-read-word)))))

(local
 (defthm collection-scan-assignment-agrees-after-discovery
   (implies (collection-forwarding-agrees-p address entry work)
            (collection-forwarding-agrees-p address entry (collection-discover query work)))
   :hints (("Goal" :in-theory (enable collection-forwarding-agrees-p)))))

(local
 (defthm collection-scan-assignment-agrees-after-field-discovery
   (implies (collection-forwarding-agrees-p address entry work)
            (collection-forwarding-agrees-p address entry (collection-discover-fields fields work)))
   :hints (("Goal" :induct (collection-discover-fields fields work)))))

(local
 (defthm collection-field-assignment-survives-queue-update
   (implies (or (equal cursor 2) (equal cursor 3))
            (equal (collection-forwarding-agrees-p address entry (update-nth cursor queue work))
                   (collection-forwarding-agrees-p address entry work)))
   :hints (("Goal"
            :in-theory (e/d (collection-forwarding-agrees-p collection-unseen collection-forwarding)
                             (nth update-nth))))))

(defthm collection-scan-assignment-agrees-after-scan-one
  (implies (collection-forwarding-agrees-p address entry work)
           (collection-forwarding-agrees-p address entry (collection-scan-one work)))
  :hints (("Goal"
           :in-theory (e/d (collection-scan-one)
                            (collection-forwarding-agrees-p nth update-nth
                             collection-discover-fields)))))

(local
 (defthm collection-agreeing-assignment-keeps-relocated-word
   (let ((address (collection-movable-reference word base objects)))
     (implies (and (collection-datum-assigned-p word base objects work)
                   (collection-forwarding-agrees-p address
                                                   (assoc-equal address (collection-forwarding work))
                                                   next))
              (and (collection-datum-assigned-p word base objects next)
                   (equal (collection-relocate-datum word base objects next)
                          (collection-relocate-datum word base objects work)))))
   :hints (("Goal" :in-theory (enable collection-relocate-datum collection-forwarding-agrees-p)))))

(local
 (defthm collection-committed-word-stays-assigned-through-scan
   (implies (collection-datum-assigned-p word base objects work)
            (and (collection-datum-assigned-p word base objects (collection-scan-one work))
                 (equal (collection-relocate-datum word base objects (collection-scan-one work))
                        (collection-relocate-datum word base objects work))))
   :hints (("Goal"
            :cases ((collection-movable-reference word base objects))
            :use ((:instance collection-agreeing-assignment-keeps-relocated-word
                             (next (collection-scan-one work))))
            :in-theory (e/d (collection-relocate-datum)
                             (collection-agreeing-assignment-keeps-relocated-word
                              collection-forwarding-agrees-p))))))

(local
 (in-theory (disable collection-datum-assigned-p collection-forwarding-agrees-p
                     collection-scan-assignment-agrees-after-scan-one)))

(defthm collection-later-scan-preserves-committed-fields
  (implies (and (collection-scanned-fields-p count source target base objects original before work)
                (equal (collection-slot-words count target after)
                       (collection-slot-words count target before)))
           (collection-scanned-fields-p count source target base objects original after
                                       (collection-scan-one work)))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-scanned-fields-p count source target base objects original before work)
           :in-theory (enable collection-slot-words))))

(local
 (defthm collection-abstract-field-discovery-keeps-a-committed-word
   (let ((next (mv-nth 1 (collection-rewrite-slots count source base objects machine work))))
     (implies (collection-datum-assigned-p word base objects work)
              (and (collection-datum-assigned-p word base objects next)
                   (equal (collection-relocate-datum word base objects next)
                          (collection-relocate-datum word base objects work)))))
   :hints (("Goal"
            :cases ((collection-movable-reference word base objects))
            :use ((:instance collection-agreeing-assignment-keeps-relocated-word
                             (next (mv-nth 1 (collection-rewrite-slots count source base objects machine work)))))
            :in-theory (e/d (collection-datum-assigned-p collection-relocate-datum)
                             (collection-agreeing-assignment-keeps-relocated-word
                              collection-discover-fields collection-discover-datum
                              collection-slot-rewrites-agree-with-resulting-forwarding-map))))))

(defthm collection-field-discovery-preserves-known-address
  (iff (collection-known-address-p query (collection-discover address work))
       (collection-known-address-p query work))
  :hints (("Goal" :in-theory (enable collection-known-address-p))))

(local
 (defthm collection-field-discovery-keeps-known-sources
   (implies (collection-slot-sources-known-p count source base objects machine work)
            (collection-slot-sources-known-p count source base objects machine
                                            (collection-discover-datum word base objects work)))
   :hints (("Goal"
            :induct (collection-slot-sources-known-p count source base objects machine work)
            :in-theory (enable collection-discover-datum)))))

(local
 (defun collection-field-write-induction (count source target base objects original work)
   (declare (xargs :measure (nfix count)))
   (if (zp count)
       (list source target work)
     (collection-field-write-induction
      (1- count) (+ source 8) (+ target 8) base objects original
      (collection-discover-datum (collection-read-word source original) base objects work)))))

(defthm collection-writing-the-abstract-rewrites-commits-all-fields
  (let ((machine (proof-world-machine original)))
    (mv-let (words next)
      (collection-rewrite-slots count source base objects machine work)
    (implies (and (collection-slot-sources-known-p count source base objects machine work)
                    (equal (collection-slot-words count target current) words))
             (collection-scanned-fields-p count source target base objects original current
                                           next))))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-field-write-induction count source target base objects original work)
           :in-theory (disable collection-slot-rewrites-discover-exactly-the-graph-edges
                               collection-slot-rewrites-agree-with-resulting-forwarding-map
                               collection-abstract-field-discovery-keeps-a-committed-word
                               collection-slot-sources-known-p
                               collection-discover-datum collection-scanned-fields-p
                               collection-slot-words))
          ("Subgoal *1/2"
           :expand ((collection-rewrite-slots count source base objects (proof-world-machine original) work)
                    (collection-slot-sources-known-p count source base objects (proof-world-machine original) work))
           :use ((:instance collection-discover-datum-establishes-its-assignment
                            (word (collection-read-word source original)))
                 (:instance collection-abstract-field-discovery-keeps-a-committed-word
                            (count (1- count)) (source (+ source 8))
                            (word (collection-read-word source original))
                            (machine (proof-world-machine original))
                            (work (collection-discover-datum (collection-read-word source original) base objects work))))
           :in-theory (e/d (collection-scanned-fields-p collection-slot-words)
                            (collection-slot-rewrites-discover-exactly-the-graph-edges
                             collection-slot-rewrites-agree-with-resulting-forwarding-map
                             collection-abstract-field-discovery-keeps-a-committed-word
                             collection-discover-datum-establishes-its-assignment
                             collection-slot-sources-known-p collection-discover-datum)))
          ("Subgoal *1/1"
           :in-theory (enable collection-scanned-fields-p))))
