(in-package "BOYMOO-PROOFS")

(include-book "publication-map")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-disjoint-reservation-preserves-object-storage
  (implies (and (proof-object-map-p pending objects seen base packages first)
                (proof-object-disjoint-p start end pending first)
                (sequence-machine-write-confined-p start end first last))
           (sequence-object-storage-agrees-p pending first last))
  :hints
  (("Goal"
    :in-theory (e/d ((:induction proof-object-map-p) sequence-object-storage-agrees-p
                     proof-object-disjoint-p proof-span-p proof-disjoint-p)
                    (proof-object-record-p proof-object-size proof-object-view
                     proof-symbol-object-p proof-view-value
                     sequence-machine-write-confined-p sequence-machine-span-agrees-p))
    :induct (proof-object-map-p pending objects seen base packages first)
    :expand ((proof-object-map-p pending objects seen base packages first)))
   ("Subgoal *1/1"
    :use ((:instance sequence-agreement-outside-confined-write
                     (lower (proof-object-address (car pending)))
                     (upper (+ (proof-object-address (car pending))
                               (proof-object-size (car pending) first))))))
   ("Subgoal *1/2"
    :use ((:instance sequence-agreement-outside-confined-write
                     (lower (proof-object-address (car pending)))
                     (upper (+ (proof-object-address (car pending))
                               (proof-object-size (car pending) first)))))))
  :rule-classes nil)

(local
 (defthm sequence-publication-load-word-is-unsigned
   (unsigned-byte-p 64 (proof-load-word address machine))
   :hints (("Goal" :in-theory (enable proof-load-word)
            :use ((:instance sequence-read-bytes-bits
                             (count 8) (memory (boymoo-model::a64-memory machine))))))))

(local
 (defthm sequence-object-storage-size-is-positive
   (implies (proof-object-map-p pending objects seen base packages machine)
            (implies (consp pending) (< 0 (proof-object-size (car pending) machine))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-object-size proof-header-size)
                     (proof-object-record-p proof-object-view proof-symbol-object-p
                      proof-object-disjoint-p proof-load-word sequence-publication-load-word-is-unsigned
                      proof-align-up proof-span-p))
     :expand ((proof-object-map-p pending objects seen base packages machine))
     :use ((:instance sequence-publication-load-word-is-unsigned
                      (address (proof-object-address (car pending))))
           (:instance sequence-align-up-covers-address (alignment 8)
                      (address (proof-header-size
                                (proof-load-word (proof-object-address (car pending)) machine))))
           (:instance sequence-floor-of-unsigned (dropped 8) (kept 56)
                      (value (proof-load-word (proof-object-address (car pending)) machine))))))
   :rule-classes nil))

(defthm sequence-reservation-contains-no-published-address
  (implies (and (proof-object-map-p pending objects seen base packages machine)
                (proof-object-disjoint-p start end pending machine)
                (<= start address) (< address end))
           (not (assoc-equal address pending)))
  :hints
  (("Goal"
    :in-theory (e/d ((:induction proof-object-map-p) proof-object-disjoint-p proof-disjoint-p)
                    (proof-object-record-p proof-object-view proof-object-size
                     proof-symbol-object-p proof-view-value proof-span-p))
    :induct (proof-object-map-p pending objects seen base packages machine)
    :expand ((proof-object-map-p pending objects seen base packages machine)))
   ("Subgoal *1/1" :use sequence-object-storage-size-is-positive)
   ("Subgoal *1/2" :use sequence-object-storage-size-is-positive))
  :rule-classes nil)
