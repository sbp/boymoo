(in-package "BOYMOO-PROOFS")

(include-book "object-map-agreement")
(include-book "constant-roots")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-object-address proof-symbol-object-p proof-object-view proof-object-word
                     proof-load-word proof-view proof-view-value proof-static-binding
                     data-static-word-present-p data-static-record-children-present-p
                     data-static-image-map data-static-object-spans-p)))

(local
 (defthm witness-lookup-is-a-member
   (implies (assoc-equal address witness)
            (member-equal (assoc-equal address witness) witness))
   :hints (("Goal" :induct (assoc-equal address witness)))))

(local
 (defthm known-record-head-is-in-witness
   (implies (and (consp pending) (data-static-known-records-p pending witness))
            (member-equal (car pending) witness))
   :hints (("Goal" :use ((:instance witness-lookup-is-a-member (address (caar pending))))
                   :in-theory (disable witness-lookup-is-a-member)))))

(local
 (defthm witness-home-binding-matches-an-owned-record
   (let* ((address (proof-object-address record))
          (symbol (proof-view-value (proof-object-view record base witness packages machine)))
          (name (symbol-name symbol))
          (number (proof-view-value (proof-view (proof-load-word (+ address 16) machine)
                                                base witness packages machine))))
     (implies (and (proof-home-bindings-p pending base witness packages machine buckets)
                   (member-equal record pending) (proof-symbol-object-p record machine))
              (equal (proof-static-binding number name buckets) (cons (cons number name) symbol))))
   :rule-classes nil
   :hints (("Goal" :induct (proof-home-bindings-p pending base witness packages machine buckets)))))

(local
 (defthm witnessed-home-binding-is-the-same
   (let* ((address (proof-object-address record))
          (symbol (proof-view-value (proof-object-view record base objects packages machine)))
          (name (symbol-name symbol))
          (number (proof-view-value (proof-view (proof-load-word (+ address 16) machine)
                                                base objects packages machine))))
     (implies (and (proof-home-bindings-p witness base witness packages machine buckets)
                   (member-equal record witness) (proof-symbol-object-p record machine)
                   (data-static-record-children-present-p record base objects machine)
                   (data-static-word-present-p (proof-object-word record base) base objects)
                   (data-static-known-records-p objects witness)
                   (data-static-records-children-present-p objects base objects machine))
              (equal (proof-static-binding number name buckets) (cons (cons number name) symbol))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance witness-home-binding-matches-an-owned-record (pending witness))
                         data-symbol-record-has-present-fields
                         (:instance data-view-agrees-with-witness-map (word (proof-object-word record base)))
                         (:instance data-view-agrees-with-witness-map
                                    (word (proof-load-word (+ (proof-object-address record) 16) machine))))
                   :in-theory (enable proof-object-view)))))

(defthmd data-discovered-home-bindings-agree-with-witness
  (implies (and (proof-home-bindings-p witness base witness packages machine buckets)
                (data-static-known-records-p objects witness)
                (data-static-records-children-present-p objects base objects machine)
                (data-static-known-records-p pending witness)
                (data-static-records-children-present-p pending base objects machine)
                (data-static-record-words-present-p pending base objects))
           (proof-home-bindings-p pending base objects packages machine buckets))
  :hints (("Goal" :induct (proof-home-bindings-p pending base objects packages machine buckets))
          ("Subgoal *1/3" :use ((:instance witnessed-home-binding-is-the-same (record (car pending)))
                                known-record-head-is-in-witness)
                          :in-theory (disable known-record-head-is-in-witness))))

(local
 (defthm discovered-root-views-agree-with-witness
   (implies (and (data-static-known-records-p objects witness)
                 (data-static-records-children-present-p objects base objects machine)
                 (data-static-word-present-p *proof-nil* base objects)
                 (data-static-word-present-p *proof-t* base objects)
                 (data-static-field-words-present-p (+ base 8) 2 base objects machine))
            (and (equal (proof-view *proof-nil* base objects packages machine)
                        (proof-view *proof-nil* base witness packages machine))
                 (equal (proof-view *proof-t* base objects packages machine)
                        (proof-view *proof-t* base witness packages machine))
                 (equal (proof-view (proof-load-word (+ base 8) machine) base objects packages machine)
                        (proof-view (proof-load-word (+ base 8) machine) base witness packages machine))
                 (equal (proof-view (proof-load-word (+ base 16) machine) base objects packages machine)
                        (proof-view (proof-load-word (+ base 16) machine) base witness packages machine))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance data-view-agrees-with-witness-map (word *proof-nil*))
                         (:instance data-view-agrees-with-witness-map (word *proof-t*))
                         (:instance data-view-agrees-with-witness-map (word (proof-load-word (+ base 8) machine)))
                         (:instance data-view-agrees-with-witness-map (word (proof-load-word (+ base 16) machine))))
                   :expand ((:free (address) (data-static-field-words-present-p address 2 base objects machine))
                            (:free (address) (data-static-field-words-present-p address 1 base objects machine)))))))

(local
 (defthm static-view-obligations-transfer-to-discovered-map
   (implies (and (data-static-views-p base witness packages machine)
                 (proof-span-p base size) (< size *proof-space-size*) (equal (mod base 8) 0)
                 (data-static-object-spans-p objects base size machine)
                 (data-static-known-records-p objects witness)
                 (data-static-records-children-present-p objects base objects machine)
                 (data-static-word-present-p *proof-nil* base objects)
                 (data-static-word-present-p *proof-t* base objects)
                 (data-static-field-words-present-p (+ base 8) 2 base objects machine))
            (data-static-views-p base objects packages machine))
   :rule-classes nil
   :hints (("Goal" :use (discovered-root-views-agree-with-witness
                         data-discovered-map-has-valid-views-and-unique-symbols data-static-map-record-words-are-present
                         (:instance data-discovered-home-bindings-agree-with-witness
                                    (pending objects)
                                    (buckets (cdr (proof-view (proof-load-word (+ base 16) machine)
                                                              base witness packages machine)))))
                   :in-theory (disable proof-span-p mod proof-object-map-p proof-home-bindings-p
                                       proof-packages-p proof-static-buckets-p proof-package-bindings-p
                                       proof-package-row-views data-static-field-words-present-p
                                       data-static-records-children-present-p data-static-known-records-p)))))

(defthmd data-image-scan-establishes-static-view-obligations
  (let ((size (car image)))
    (implies (and (data-static-image-witness-p base image constants machine witness)
                  (data-static-views-p base witness packages machine)
                  (proof-span-p base size) (< size *proof-space-size*) (equal (mod base 8) 0))
             (mv-let (ok objects) (data-static-image-map base image constants machine)
               (and ok (data-static-views-p base objects packages machine)))))
  :hints (("Goal" :use (data-static-image-map-succeeds-for-ranked-graph data-static-map-on-success-covers-roots
                        data-static-image-map-on-success-closes-object-children
                        (:instance static-view-obligations-transfer-to-discovered-map (size (car image))
                                   (objects (mv-nth 1 (data-static-image-map base image constants machine)))))
                  :in-theory (disable data-static-views-p proof-span-p mod
                                      data-static-records-children-present-p data-static-known-records-p
                                      data-static-field-words-present-p data-static-image-witness-p))))

(defthmd data-build-initial-static-from-placed-witness
  (mv-let (image constants) (boymoo-compiler::data-build lines package-lines)
    (implies (and (proof-image-at-p image base machine)
                  (< (car image) *proof-space-size*) (equal (mod base 8) 0)
                  (data-static-image-witness-p base image constants machine witness)
                  (data-static-views-p base witness packages machine))
             (mv-let (ok objects) (data-static-image-map base image constants machine)
               (and ok (proof-static-initial-p base objects packages machine)))))
  :hints (("Goal" :use (data-build-initial-static-under-view-obligations
                        (:instance data-image-scan-establishes-static-view-obligations
                                   (image (car (boymoo-compiler::data-build lines package-lines)))
                                   (constants (mv-nth 1 (boymoo-compiler::data-build lines package-lines)))))
                  :in-theory (disable boymoo-compiler::data-build data-static-image-witness-p
                                      data-static-views-p mod proof-span-p proof-static-initial-p
                                      proof-fragments-at-p proof-image-p))))
