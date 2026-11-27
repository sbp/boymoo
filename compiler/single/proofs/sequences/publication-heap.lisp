(in-package "BOYMOO-PROOFS")

(include-book "publication-memory")
(include-book "stack-invariant")
(include-book "root-storage")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-static-heap-depends-on-static-records
   (implies (equal (proof-static-objects first-map) (proof-static-objects last-map))
            (equal (proof-static-p base first-map packages machine)
                   (proof-static-p base last-map packages machine)))
   :hints
   (("Goal"
     :in-theory (disable proof-object-map-p proof-static-spans-p proof-view proof-value-p
                         proof-static-size proof-load-word proof-home-bindings-p
                         proof-static-buckets-p proof-package-bindings-p proof-packages-p
                         proof-package-row-views proof-static-objects)
     :expand ((proof-static-p base first-map packages machine)
              (proof-static-p base last-map packages machine))))
   :rule-classes nil))

(local
 (defthm sequence-object-placements-on-append
   (equal (proof-heap-object-spans-p (append first second) external world)
          (and (proof-heap-object-spans-p first external world)
               (proof-heap-object-spans-p second external world)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-heap-object-spans-p) (proof-subspan-p proof-object-size))
     :induct (len first)))))

(local
 (defthm sequence-dynamic-symbols-in-extended-map
   (implies (and (proof-object-map-p pending objects seen base packages machine)
                 (proof-dynamic-symbol-objects-p pending objects entries base packages machine)
                 (sequence-object-lookups-agree-p objects objects extended))
            (proof-dynamic-symbol-objects-p pending extended entries base packages machine))
   :hints
   (("Goal"
     :in-theory (e/d ((:induction proof-object-map-p))
                     (proof-object-size proof-object-record-p proof-object-disjoint-p
                      proof-span-p proof-symbol-object-p proof-object-view proof-view-value
                      sequence-object-lookups-agree-p))
     :induct (proof-object-map-p pending objects seen base packages machine)
     :expand ((proof-object-map-p pending objects seen base packages machine)
              (:free (map) (proof-dynamic-symbol-objects-p pending map entries base packages machine))))
    ("Subgoal *1/1" :in-theory (enable proof-dynamic-symbol-objects-p))
    ("Subgoal *1/3"
     :use ((:instance sequence-valid-view-on-extended-map (word (proof-object-word (car pending) base))))
     :in-theory (enable proof-object-view))
    ("Subgoal *1/2"
     :use ((:instance sequence-valid-view-on-extended-map (word (proof-object-word (car pending) base))))
     :in-theory (enable proof-object-view)))
   :rule-classes nil))

(local
 (defthm sequence-nonsymbol-records-keep-dynamic-symbols
   (implies (and (sequence-added-object-records-p records old extended base packages machine)
                 (proof-dynamic-symbol-objects-p old extended entries base packages machine))
            (proof-dynamic-symbol-objects-p (append records old) extended entries base packages machine))
   :hints
   (("Goal"
     :in-theory (disable proof-span-p proof-object-size proof-object-record-p
                         proof-object-disjoint-p proof-symbol-object-p proof-object-view
                         proof-view-value)
     :induct (sequence-added-object-records-p records old extended base packages machine)
     :expand ((proof-dynamic-symbol-objects-p (cons (car records) (append (cdr records) old))
                                              extended entries base packages machine))))
   :rule-classes nil))

(local
 (defthm sequence-dynamic-entries-require-a-view
   (implies (proof-dynamic-entries view packages) view)
   :hints (("Goal" :in-theory (enable proof-dynamic-entries)))
   :rule-classes :forward-chaining))

(local
 (defthm sequence-dynamic-root-after-publication
   (let* ((base (proof-heap-base before))
          (first (proof-world-machine before))
          (last (proof-world-machine after))
          (word (proof-dynamic-root base first)))
     (implies
      (and (proof-dynamic-entries (proof-dynamic-view before objects packages) packages)
           (equal (proof-heap-base after) base)
           (equal (proof-dynamic-root base last) word)
           (sequence-object-storage-agrees-p objects first last)
           (sequence-object-lookups-agree-p objects objects extended))
      (equal (proof-dynamic-view after extended packages) (proof-dynamic-view before objects packages))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-dynamic-view)
                     (proof-dynamic-root proof-view proof-dynamic-entries sequence-object-lookups-agree-p))
     :use ((:instance sequence-old-view-after-publication
                      (base (proof-heap-base before))
                      (word (proof-dynamic-root (proof-heap-base before) (proof-world-machine before)))
                      (first (proof-world-machine before)) (last (proof-world-machine after))))))
   :rule-classes nil))

(local
 (defthm sequence-root-prefix-after-publication
   (let* ((base (proof-heap-base before))
          (first (proof-world-machine before))
          (last (proof-world-machine after))
          (lower (proof-stack-base before))
          (top (proof-stack-top before)))
     (implies
      (and (proof-stack-prefix top before objects packages)
           (equal (proof-heap-base after) base)
           (equal (proof-stack-base after) lower)
           (equal (proof-stack-top after) top)
           (proof-span-p lower (- top lower))
           (sequence-machine-span-agrees-p lower top first last)
           (sequence-object-storage-agrees-p objects first last)
           (sequence-object-lookups-agree-p objects objects extended))
      (proof-prefix-preserved-p top before after objects extended packages)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-stack-prefix proof-prefix-preserved-p)
                     (proof-stack-views proof-view proof-load-word proof-subspan-p
                      proof-span-p proof-stack-base proof-stack-top proof-heap-base
                      sequence-object-lookups-agree-p sequence-object-storage-agrees-p))
     :use ((:instance sequence-pushed-root-views (more 0))
           (:instance sequence-valid-stack-views-on-extended-map
                      (machine (proof-world-machine after)) (base (proof-heap-base before))
                      (address (proof-stack-base before))
                      (count (ash (- (proof-stack-top before) (proof-stack-base before)) -3))))
     :expand ((:free (address base map)
                     (proof-stack-views 0 address base map packages (proof-world-machine after))))))
   :rule-classes nil))

(defun sequence-publication-preserves-storage-p (before after objects packages)
  (let* ((base (proof-heap-base before))
         (first (proof-world-machine before))
         (last (proof-world-machine after))
         (lower (proof-stack-base before))
         (top (proof-stack-top before))
         (external (proof-external-objects (proof-external-head before) (len objects) before objects)))
    (and (proof-heap-layout-p after)
         (proof-heap-frame-p before after)
         (sequence-heap-registers-agree-p before after)
         (sequence-heap-metadata-agrees-p before after)
         (sequence-object-storage-agrees-p objects first last)
         (proof-static-p base objects packages last)
         (equal (proof-external-objects (proof-external-head after) (len objects) after objects) external)
         (equal (proof-string-accounting-p (cdr external) after)
                (proof-string-accounting-p (cdr external) before))
         (equal (proof-dynamic-root base last) (proof-dynamic-root base first))
         (proof-span-p lower (- top lower))
         (sequence-machine-span-agrees-p lower top first last))))

(local
 (defthm sequence-append-length-for-publication
   (equal (len (append first second)) (+ (len first) (len second)))
   :hints (("Goal" :induct (len first)))))

(defthm sequence-publish-active-nonsymbol-objects
  (let* ((base (proof-heap-base before))
         (last (proof-world-machine after))
         (extended (append records objects))
         (external (proof-external-objects (proof-external-head before) (len objects) before objects)))
    (implies
     (and (proof-heap-p before objects packages)
          (sequence-publication-preserves-storage-p before after objects packages)
          (sequence-new-records-miss-existing-keys-p objects records)
          (sequence-added-object-records-p records objects extended base packages last)
          (proof-heap-object-spans-p records (cdr external) after))
     (proof-preserved-heap-p nil before after objects extended packages)))
  :hints
  (("Goal"
    :in-theory (e/d (proof-preserved-heap-p proof-dynamic-table-preserved-p proof-prefix-preserved-p
                     sequence-heap-registers-agree-p sequence-heap-metadata-agrees-p)
                    (proof-heap-layout-p proof-heap-frame-p proof-static-p proof-object-map-p
                     proof-external-objects proof-dynamic-view proof-dynamic-entries
                     proof-dynamic-symbol-objects-p proof-stack-prefix
                     proof-heap-object-spans-p proof-string-accounting-p proof-dynamic-root
                     sequence-new-records-miss-existing-keys-p sequence-added-object-records-p))
    :expand ((proof-heap-p before objects packages)
             (proof-heap-p after (append records objects) packages))
    :use
    ((:instance sequence-object-map-after-publication (base (proof-heap-base before))
                (first (proof-world-machine before)) (last (proof-world-machine after)))
     (:instance sequence-fresh-keys-keep-old-lookups (pending objects) (new records))
     (:instance sequence-static-heap-depends-on-static-records
                (base (proof-heap-base before)) (first-map objects) (last-map (append records objects))
                (machine (proof-world-machine after)))
     (:instance sequence-external-mapping-list-on-extended-map
                (head (proof-external-head after)) (fuel (len objects)) (world after)
                (extended (append records objects)) (extra (len records)))
     (:instance sequence-object-spans-on-agreed-storage (pending objects)
                (external (cdr (proof-external-objects (proof-external-head before) (len objects) before objects))))
     (:instance sequence-dynamic-root-after-publication (extended (append records objects)))
     (:instance sequence-dynamic-symbols-on-agreed-storage (pending objects) (base (proof-heap-base before))
                (entries (cdr (proof-dynamic-entries (proof-dynamic-view before objects packages) packages)))
                (first (proof-world-machine before)) (last (proof-world-machine after)))
     (:instance sequence-object-map-on-agreed-storage (pending objects) (symbols nil) (base (proof-heap-base before))
                (first (proof-world-machine before)) (last (proof-world-machine after)))
     (:instance sequence-dynamic-symbols-in-extended-map (pending objects) (seen nil) (base (proof-heap-base before))
                (entries (cdr (proof-dynamic-entries (proof-dynamic-view before objects packages) packages)))
                (machine (proof-world-machine after)) (extended (append records objects)))
     (:instance sequence-nonsymbol-records-keep-dynamic-symbols (old objects) (base (proof-heap-base before))
                (entries (cdr (proof-dynamic-entries (proof-dynamic-view before objects packages) packages)))
                (machine (proof-world-machine after)) (extended (append records objects)))
     (:instance sequence-root-prefix-after-publication (extended (append records objects))))
    :do-not-induct t))
  :rule-classes nil)
