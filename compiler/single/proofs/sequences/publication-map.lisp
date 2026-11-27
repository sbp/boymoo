(in-package "BOYMOO-PROOFS")

(include-book "publication-views")
(include-book "heap-objects")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defun sequence-extend-map-induction (pending objects symbols base packages machine)
   (if (atom pending)
       symbols
     (sequence-extend-map-induction
      (cdr pending) objects
      (if (proof-symbol-object-p (car pending) machine)
          (cons (proof-view-value (proof-object-view (car pending) base objects packages machine))
                symbols)
        symbols)
      base packages machine))))

(defthm sequence-existing-object-map-in-extension
  (implies (and (proof-object-map-p pending objects symbols base packages machine)
                (sequence-object-lookups-agree-p objects objects extended))
           (proof-object-map-p pending extended symbols base packages machine))
  :hints
  (("Goal"
    :in-theory (disable proof-object-view proof-object-size proof-object-record-p
                        proof-object-disjoint-p proof-symbol-object-p proof-view-value
                        proof-span-p sequence-object-lookups-agree-p)
    :expand ((:free (records)
                    (proof-object-map-p pending records symbols base packages machine)))
    :induct (sequence-extend-map-induction pending objects symbols base packages machine))
   ("Subgoal *1/1"
    :in-theory (enable proof-object-map-p))
   ("Subgoal *1/2"
    :in-theory (enable proof-object-view)
    :use ((:instance sequence-valid-view-on-extended-map (word (proof-object-word (car pending) base))))))
  :rule-classes nil)

(defun sequence-added-object-records-p (records old extended base packages machine)
  (if (atom records)
      (null records)
    (let* ((record (car records))
           (address (proof-object-address record))
           (size (proof-object-size record machine)))
      (and (proof-object-record-p record)
           (eq (proof-object-zone record) :active)
           (not (proof-symbol-object-p record machine))
           (proof-span-p address size)
           (proof-object-view record base extended packages machine)
           (proof-object-disjoint-p address (+ address size) (append (cdr records) old) machine)
           (sequence-added-object-records-p (cdr records) old extended base packages machine)))))

(local
 (defthm sequence-publish-nonsymbol-records
   (implies (and (proof-object-map-p old extended nil base packages machine)
                 (sequence-added-object-records-p records old extended base packages machine))
            (and (proof-object-map-p (append records old) extended nil base packages machine)
                 (equal (proof-static-objects (append records old)) (proof-static-objects old))))
   :hints
   (("Goal"
     :in-theory (disable proof-object-view proof-object-size proof-object-record-p proof-object-zone
                         proof-object-disjoint-p proof-symbol-object-p proof-view-value
                         proof-span-p (:definition proof-object-map-p))
     :induct (sequence-added-object-records-p records old extended base packages machine)
     :expand ((proof-object-map-p (append records old) extended nil base packages machine)
              (proof-object-map-p (cons (car records) (append (cdr records) old))
                                  extended nil base packages machine))))
   :rule-classes nil))

(defthm sequence-object-map-after-publication
  (let ((extended (append records objects)))
    (implies (and (proof-object-map-p objects objects nil base packages first)
                  (sequence-object-storage-agrees-p objects first last)
                  (sequence-new-records-miss-existing-keys-p objects records)
                  (sequence-added-object-records-p records objects extended base packages last))
             (and (proof-object-map-p extended extended nil base packages last)
                  (equal (proof-static-objects extended) (proof-static-objects objects)))))
  :hints
  (("Goal"
    :in-theory (disable proof-object-map-p proof-static-objects
                        sequence-new-records-miss-existing-keys-p sequence-added-object-records-p)
    :use ((:instance sequence-object-map-on-agreed-storage (pending objects) (symbols nil))
          (:instance sequence-fresh-keys-keep-old-lookups (pending objects) (new records))
          (:instance sequence-existing-object-map-in-extension
                     (pending objects) (symbols nil) (machine last) (extended (append records objects)))
          (:instance sequence-publish-nonsymbol-records (old objects)
                     (machine last) (extended (append records objects))))))
  :rule-classes nil)

(defthm sequence-valid-stack-views-on-extended-map
  (implies (and (proof-stack-views count address base objects packages machine)
                (sequence-object-lookups-agree-p objects objects extended))
           (equal (proof-stack-views count address base extended packages machine)
                  (proof-stack-views count address base objects packages machine)))
  :hints
  (("Goal"
    :in-theory (e/d ((:induction proof-stack-views))
                    (proof-view proof-load-word sequence-object-lookups-agree-p))
    :induct (proof-stack-views count address base objects packages machine)
    :expand ((:free (records) (proof-stack-views count address base records packages machine))))
   ("Subgoal *1/2"
    :use ((:instance sequence-valid-view-on-extended-map (word (proof-load-word address machine))))))
  :rule-classes nil)

(defthm sequence-external-mapping-list-on-extended-map
  (implies (and (proof-external-objects head fuel world objects)
                (natp extra)
                (sequence-object-lookups-agree-p objects objects extended))
           (equal (proof-external-objects head (+ fuel extra) world extended)
                  (proof-external-objects head fuel world objects)))
  :hints
  (("Goal"
    :in-theory (e/d ((:induction proof-external-objects))
                    ((:definition proof-external-objects) proof-object-zone proof-object-kind
                     proof-align-up proof-load-word proof-disjoint-p proof-world-regions
                     sequence-object-lookups-agree-p))
    :induct (proof-external-objects head fuel world objects)
    :expand ((:free (remaining map)
                    (proof-external-objects head remaining world map))
             (:free (remaining map)
                    (proof-external-objects 0 remaining world map))))
   ("Subgoal *1/2"
    :use ((:instance sequence-existing-object-lookup-in-extension
                     (pending objects) (address (+ head 24))))))
  :rule-classes nil)
