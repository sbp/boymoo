(in-package "BOYMOO-PROOFS")

(include-book "record-words")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-object-disjoint-p proof-object-record-p proof-object-size
                     proof-subspan-p proof-span-p proof-symbol-object-p proof-object-view
                     proof-object-word proof-view proof-view-value)))

(local
 (defthm lookup-result-is-in-witness
   (implies (assoc-equal address witness)
            (member-equal (assoc-equal address witness) witness))
   :hints (("Goal" :induct (assoc-equal address witness)))))

(local
 (defthm known-map-members-are-in-witness
   (implies (and (data-static-known-records-p records witness) (member-equal object records))
            (member-equal object witness))
   :hints (("Goal" :induct (data-static-known-records-p records witness))
           ("Subgoal *1/2" :use ((:instance lookup-result-is-in-witness (address (caar records))))))))

(local
 (defthm records-in-a-valid-map-have-views
   (implies (and (proof-object-map-p pending objects symbols base packages machine)
                 (member-equal object pending))
            (proof-object-view object base objects packages machine))
   :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)))))

(local
 (defthm symbols-in-a-valid-map-are-absent-from-seen-set
   (implies (and (proof-object-map-p pending objects symbols base packages machine)
                 (member-equal object pending) (proof-symbol-object-p object machine))
            (not (member-equal (proof-view-value (proof-object-view object base objects packages machine)) symbols)))
   :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)))))

(local
 (defthm distinct-symbols-in-a-valid-map-have-distinct-values
   (implies (and (proof-object-map-p pending objects symbols base packages machine)
                 (member-equal first pending) (member-equal second pending) (not (equal first second))
                 (proof-symbol-object-p first machine) (proof-symbol-object-p second machine))
            (not (equal (proof-view-value (proof-object-view first base objects packages machine))
                        (proof-view-value (proof-object-view second base objects packages machine)))))
   :rule-classes nil
   :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine))
           ("Subgoal *1/2"
            :use ((:instance symbols-in-a-valid-map-are-absent-from-seen-set
                             (object first) (pending (cdr pending))
                             (symbols (cons (proof-view-value (proof-object-view (car pending) base objects packages machine))
                                            symbols)))
                  (:instance symbols-in-a-valid-map-are-absent-from-seen-set
                             (object second) (pending (cdr pending))
                             (symbols (cons (proof-view-value (proof-object-view (car pending) base objects packages machine))
                                            symbols))))))))

(local
 (defthm member-record-word-is-present
   (implies (and (data-static-record-words-present-p pending base objects) (member-equal object pending))
            (data-static-word-present-p (proof-object-word object base) base objects))
   :hints (("Goal" :induct (data-static-record-words-present-p pending base objects)
                   :in-theory (disable data-static-word-present-p)))))

(local
 (defthm record-view-agrees-with-witness-map
   (implies (and (data-static-known-records-p objects witness)
                 (data-static-records-children-present-p objects base objects machine)
                 (data-static-word-present-p (proof-object-word record base) base objects))
            (equal (proof-object-view record base objects packages machine)
                   (proof-object-view record base witness packages machine)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-view-agrees-with-witness-map (word (proof-object-word record base))))
                   :in-theory (e/d (proof-object-view)
                                  (data-static-word-present-p data-static-known-records-p
                                   data-static-records-children-present-p))))))

(local
 (defun no-seen-symbol-views-p (pending seen base objects packages machine)
   (or (atom pending)
       (and (or (not (proof-symbol-object-p (car pending) machine))
                (not (member-equal (proof-view-value (proof-object-view (car pending) base objects packages machine))
                                   seen)))
            (no-seen-symbol-views-p (cdr pending) seen base objects packages machine)))))

(local
 (defthm empty-set-has-no-seen-symbol-views
   (no-seen-symbol-views-p pending nil base objects packages machine)))

(local
 (in-theory (disable proof-object-map-p data-static-known-records-p data-static-word-present-p
                     data-static-records-children-present-p data-static-record-words-present-p)))

(local
 (defthm witnessed-record-has-view
   (implies (and (data-static-known-records-p pending witness)
                 (data-static-record-words-present-p pending base objects)
                 (member-equal record pending)
                 (data-static-known-records-p objects witness)
                 (data-static-records-children-present-p objects base objects machine)
                 (proof-object-map-p witness witness nil base packages machine))
            (proof-object-view record base objects packages machine))
   :rule-classes nil
   :hints (("Goal" :use (record-view-agrees-with-witness-map
                         (:instance known-map-members-are-in-witness (records pending) (object record))
                         (:instance member-record-word-is-present (object record))
                         (:instance records-in-a-valid-map-have-views (pending witness) (objects witness)
                                    (object record) (symbols nil)))
                   :in-theory (disable records-in-a-valid-map-have-views known-map-members-are-in-witness
                                       member-record-word-is-present)))))

(local
 (defthm distinct-discovered-symbols-are-distinct-in-view
   (implies (and (not (equal first second)) (proof-symbol-object-p first machine) (proof-symbol-object-p second machine)
                 (member-equal first witness) (member-equal second witness)
                 (data-static-word-present-p (proof-object-word first base) base objects)
                 (data-static-word-present-p (proof-object-word second base) base objects)
                 (data-static-known-records-p objects witness)
                 (data-static-records-children-present-p objects base objects machine)
                 (proof-object-map-p witness witness nil base packages machine))
            (not (equal (proof-view-value (proof-object-view first base objects packages machine))
                        (proof-view-value (proof-object-view second base objects packages machine)))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance record-view-agrees-with-witness-map (record first))
                         (:instance record-view-agrees-with-witness-map (record second))
                         (:instance distinct-symbols-in-a-valid-map-have-distinct-values
                                    (pending witness) (objects witness) (symbols nil)))))))

(local
 (defthm a-distinct-witnessed-symbol-is-fresh-for-the-tail
   (implies (and (no-seen-symbol-views-p pending seen base objects packages machine)
                 (not (member-equal record pending)) (member-equal record witness)
                 (proof-symbol-object-p record machine)
                 (data-static-word-present-p (proof-object-word record base) base objects)
                 (data-static-known-records-p pending witness)
                 (data-static-record-words-present-p pending base objects)
                 (data-static-known-records-p objects witness)
                 (data-static-records-children-present-p objects base objects machine)
                 (proof-object-map-p witness witness nil base packages machine))
            (no-seen-symbol-views-p
             pending (cons (proof-view-value (proof-object-view record base objects packages machine)) seen)
             base objects packages machine))
   :rule-classes nil
   :hints (("Goal" :induct (no-seen-symbol-views-p pending seen base objects packages machine)
                   :in-theory (enable data-static-known-records-p data-static-record-words-present-p))
           ("Subgoal *1/2" :use ((:instance distinct-discovered-symbols-are-distinct-in-view
                                            (first record) (second (car pending)))
                                 (:instance known-map-members-are-in-witness
                                            (records pending) (object (car pending))))
                           :in-theory (e/d (data-static-known-records-p data-static-record-words-present-p)
                                          (known-map-members-are-in-witness))))))

(local
 (defthm spans-give-record-view-preconditions
   (implies (and (consp pending) (data-static-object-spans-p pending base size machine))
            (let* ((object (car pending)) (address (proof-object-address object))
                   (bytes (proof-object-size object machine)))
              (and (proof-object-record-p object) (proof-span-p address bytes)
                   (proof-object-disjoint-p address (+ address bytes) (cdr pending) machine))))
   :rule-classes ((:forward-chaining :trigger-terms ((data-static-object-spans-p pending base size machine))))
   :hints (("Goal" :in-theory (enable proof-subspan-p)))))

(local
 (defthm static-records-witnessed-by-valid-map-are-valid
   (implies (and (data-static-object-spans-p pending base size machine)
                 (data-static-known-records-p pending witness)
                 (data-static-record-words-present-p pending base objects)
                 (data-static-known-records-p objects witness)
                 (data-static-records-children-present-p objects base objects machine)
                 (no-seen-symbol-views-p pending symbols base objects packages machine)
                 (proof-object-map-p witness witness nil base packages machine))
            (proof-object-map-p pending objects symbols base packages machine))
   :rule-classes nil
   :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
                   :in-theory (e/d (proof-object-map-p data-static-known-records-p data-static-record-words-present-p)
                                  (data-static-word-present-p data-static-rank)))
           ("Subgoal *1/2" :use ((:instance data-static-head-is-absent-from-disjoint-tail (objects pending))
                                 (:instance witnessed-record-has-view (record (car pending)))
                                 (:instance a-distinct-witnessed-symbol-is-fresh-for-the-tail
                                            (pending (cdr pending)) (record (car pending)) (seen symbols))
                                 (:instance known-map-members-are-in-witness
                                            (records pending) (object (car pending)))))
           ("Subgoal *1/5" :use ((:instance witnessed-record-has-view (record (car pending))))))))

(defthmd data-discovered-map-has-valid-views-and-unique-symbols
  (implies (and (data-static-object-spans-p objects base size machine)
                (proof-span-p base size) (< size *proof-space-size*) (equal (mod base 8) 0)
                (data-static-known-records-p objects witness)
                (data-static-records-children-present-p objects base objects machine)
                (proof-object-map-p witness witness nil base packages machine))
           (proof-object-map-p objects objects nil base packages machine))
  :hints (("Goal" :use (data-static-map-record-words-are-present
                        (:instance static-records-witnessed-by-valid-map-are-valid
                                   (pending objects) (symbols nil)))
                  :in-theory (disable data-static-object-spans-p no-seen-symbol-views-p mod))))
