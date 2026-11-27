(in-package "BOYMOO-PROOFS")

(include-book "publication")
(include-book "external-list")

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-stack-prefix-after-table-extension
  (implies (and (proof-stack-prefix top world objects packages)
                (not (assoc-equal (car object) objects)))
           (equal (proof-stack-prefix top world (cons object objects) packages)
                  (proof-stack-prefix top world objects packages)))
  :hints (("Goal" :in-theory (disable proof-stack-views proof-stack-top proof-view proof-heap-base))))

(defthm allocation-static-after-nonstatic-publication
  (implies (not (eq (proof-object-zone object) :static))
           (equal (proof-static-p base (cons object objects) packages machine)
                  (proof-static-p base objects packages machine)))
  :hints (("Goal" :in-theory (disable proof-static-spans-p proof-object-map-p proof-home-bindings-p
                                     proof-package-bindings-p proof-static-buckets-p proof-value-p
                                     proof-view proof-static-size proof-load-word mod))))

(defthm allocation-dynamic-view-required-by-entries
  (implies (proof-dynamic-entries view packages) view)
  :rule-classes :forward-chaining
  :hints (("Goal" :in-theory (disable proof-dynamic-buckets))))

(defthm allocation-dynamic-view-after-table-extension
  (implies (and (proof-dynamic-view world objects packages)
                (not (assoc-equal (car object) objects)))
           (equal (proof-dynamic-view world (cons object objects) packages)
                  (proof-dynamic-view world objects packages)))
  :hints (("Goal" :in-theory (disable proof-view proof-heap-base proof-dynamic-root))))

(defthm allocation-existing-external-list-after-publication
  (implies (and (proof-external-objects head (len objects) world objects)
                (not (assoc-equal (car object) objects)))
           (equal (proof-external-objects head (len (cons object objects)) world (cons object objects))
                  (proof-external-objects head (len objects) world objects)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-external-list-one-more-fuel (fuel (len objects)))
                 (:instance allocation-external-list-after-table-extension (fuel (1+ (len objects)))))
           :in-theory (disable proof-external-objects))))

(defthm allocation-cons-extends-heap-spans
  (implies (and (equal (mod address 16) 0)
                (proof-subspan-p address 16 (proof-cons-floor world) (proof-active-end world))
                (proof-heap-object-spans-p objects headers world))
           (proof-heap-object-spans-p (cons (proof-object address :active :cons rank) objects) headers world))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-subspan-p proof-cons-floor proof-active-end mod))))

(defthm allocation-cons-adds-no-dynamic-symbol
  (equal (proof-dynamic-symbol-objects-p (cons (proof-object address :active :cons rank) pending)
                                        table entries base packages machine)
         (proof-dynamic-symbol-objects-p pending table entries base packages machine))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable proof-object-view))))

(defthm allocation-published-cons-admits-heap
  (let* ((object (proof-object address :active :cons rank))
         (published (cons object objects))
         (base (proof-heap-base world))
         (machine (proof-world-machine world)))
    (implies (and (proof-heap-p world objects packages)
                  (not (assoc-equal address objects))
                  (equal (mod address 16) 0)
                  (proof-subspan-p address 16 (proof-cons-floor world) (proof-active-end world))
                  (proof-object-map-p published published nil base packages machine))
             (proof-heap-p world published packages)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-existing-external-list-after-publication
                  (head (proof-external-head world)) (object (proof-object address :active :cons rank)))
                 (:instance allocation-cons-extends-heap-spans
                  (headers (cdr (proof-external-objects (proof-external-head world) (len objects) world objects))))
                 (:instance allocation-cons-adds-no-dynamic-symbol
                  (pending objects) (table (cons (proof-object address :active :cons rank) objects))
                  (entries (cdr (proof-dynamic-entries (proof-dynamic-view world objects packages) packages)))
                  (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance allocation-old-dynamic-symbols-after-publication
                  (pending objects) (object (proof-object address :active :cons rank))
                  (entries (cdr (proof-dynamic-entries (proof-dynamic-view world objects packages) packages)))
                  (symbols nil) (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (disable proof-heap-layout-p proof-static-p proof-object-map-p proof-external-objects
                               (:definition proof-heap-object-spans-p) proof-string-accounting-p
                               proof-dynamic-view proof-dynamic-entries (:definition proof-dynamic-symbol-objects-p)
                               proof-stack-prefix proof-stack-top proof-load-word proof-view proof-symbol-object-p
                               proof-heap-base proof-external-head proof-cons-floor proof-active-end
                               proof-subspan-p mod))))
