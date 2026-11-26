(in-package "BOYMOO-PROOFS")

(include-book "object-memory")
(include-book "view-memory")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-existing-object-lookup-in-extension
  (implies (and (sequence-object-lookups-agree-p pending objects extended)
                (assoc-equal address pending))
           (equal (assoc-equal address extended) (assoc-equal address objects)))
  :hints (("Goal" :induct (assoc-equal address pending)))
  :rule-classes nil)

(defthm sequence-valid-view-on-extended-map
  (implies (and (proof-view word base objects packages machine)
                (sequence-object-lookups-agree-p objects objects extended))
           (equal (proof-view word base extended packages machine)
                  (proof-view word base objects packages machine)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-view)
                    (proof-view-step proof-pointer-address proof-object-rank proof-word-tag
                     sequence-object-lookups-agree-p oddp evenp))
    :expand ((:free (depth)
                    (proof-view-step :word word 0 depth base objects packages machine))
             (:free (depth)
                    (proof-view-step :word word 0 depth base extended packages machine)))
    :use ((:instance sequence-existing-object-lookup-in-extension
                     (address (proof-pointer-address word base)) (pending objects))
          (:instance sequence-view-step-on-extended-map
                     (kind :word) (input word) (count 0)
                     (depth (1+ (nfix (proof-object-rank
                                       (assoc-equal (proof-pointer-address word base) objects)))))))))
  :rule-classes nil)

(defthm sequence-old-view-after-publication
  (implies (and (proof-view word base objects packages first)
                (sequence-object-storage-agrees-p objects first last)
                (sequence-object-lookups-agree-p objects objects extended))
           (equal (proof-view word base extended packages last)
                  (proof-view word base objects packages first)))
  :hints
  (("Goal"
    :in-theory (disable proof-view proof-view-step sequence-object-lookups-agree-p)
    :use (sequence-view-on-agreed-objects
          (:instance sequence-valid-view-on-extended-map (machine last)))))
  :rule-classes nil)

(defthm sequence-old-value-after-publication
  (implies (and (proof-value-p word datum base objects packages first)
                (sequence-object-storage-agrees-p objects first last)
                (sequence-object-lookups-agree-p objects objects extended))
           (proof-value-p word datum base extended packages last))
  :hints
  (("Goal" :in-theory (e/d (proof-value-p) (proof-view sequence-object-lookups-agree-p))
           :use sequence-old-view-after-publication))
  :rule-classes nil)

(defun sequence-ranks-below-p (records limit)
  (if (atom records)
      t
    (and (< (proof-object-rank (car records)) limit)
         (sequence-ranks-below-p (cdr records) limit))))

(defthm sequence-existing-object-rank-below-limit
  (implies (and (sequence-ranks-below-p records limit)
                (assoc-equal address records))
           (< (proof-object-rank (assoc-equal address records)) limit))
  :hints (("Goal" :induct (assoc-equal address records)))
  :rule-classes nil)

(defun sequence-new-records-miss-existing-keys-p (pending new)
  (if (atom pending)
      t
    (and (natp (proof-object-address (car pending)))
         (not (assoc-equal (proof-object-address (car pending)) new))
         (sequence-new-records-miss-existing-keys-p (cdr pending) new))))

(local
 (defthm sequence-assoc-equal-of-append
   (implies (not (null address))
            (equal (assoc-equal address (append first second))
                   (or (assoc-equal address first) (assoc-equal address second))))
   :hints (("Goal" :induct (len first)))))

(defthm sequence-fresh-keys-keep-old-lookups
  (implies (sequence-new-records-miss-existing-keys-p pending new)
           (sequence-object-lookups-agree-p pending objects (append new objects)))
  :hints (("Goal" :induct (sequence-new-records-miss-existing-keys-p pending new)))
  :rule-classes nil)
