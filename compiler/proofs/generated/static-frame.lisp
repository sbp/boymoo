(in-package "BOYMOO-PROOFS")

(include-book "object-frame")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-static-p proof-static-size proof-static-spans-p proof-static-objects
                    proof-object-map-p proof-object-size proof-object-view proof-symbol-object-p
                    proof-object-disjoint-p proof-load-word proof-dynamic-root proof-value-p proof-view
                    proof-home-bindings-p proof-static-binding proof-packages-p proof-package-row-views
                    proof-static-buckets-p proof-package-bindings-p proof-span-p proof-subspan-p
                    proof-disjoint-p expt))

(defthm generated-static-header-outside-written-span
  (implies (and (proof-span-p base size) (<= 32 size)
                (proof-disjoint-p base (+ base size) start end)
                (generated-memory-outside-p start end first last))
           (and (equal (proof-static-size base last) (proof-static-size base first))
                (equal (proof-load-word (+ base 8) last) (proof-load-word (+ base 8) first))
                (equal (proof-load-word (+ base 16) last) (proof-load-word (+ base 16) first))
                (equal (proof-dynamic-root base last) (proof-dynamic-root base first))))
  :hints (("Goal"
           :use ((:instance generated-word-outside-written-span (address base) (before first) (after last))
                 (:instance generated-word-outside-written-span (address (+ base 8)) (before first) (after last))
                 (:instance generated-word-outside-written-span (address (+ base 16)) (before first) (after last))
                 (:instance generated-word-outside-written-span (address (+ base 24)) (before first) (after last)))
           :in-theory (enable proof-span-p proof-disjoint-p proof-static-size proof-dynamic-root)))
  :rule-classes nil)

(defthm generated-static-spans-exclude-disjoint-span
  (implies (and (natp base)
                (proof-static-spans-p statics base size machine)
                (proof-disjoint-p base (+ base size) start end))
           (proof-object-disjoint-p start end statics machine))
  :hints (("Goal" :induct (len statics)
                  :in-theory (enable proof-static-spans-p proof-subspan-p proof-disjoint-p
                                     proof-object-disjoint-p proof-span-p)))
  :rule-classes nil)

(local
 (defthm generated-static-package-number-word-outside-write
   (let ((address (proof-object-address object)))
     (implies (and (proof-span-p base (+ size 16))
                   (proof-subspan-p address (proof-object-size object first) (+ base 32) (+ base size))
                   (proof-disjoint-p base (+ base size 16) start end)
                   (generated-memory-outside-p start end first last))
              (equal (proof-load-word (+ address 16) last)
                     (proof-load-word (+ address 16) first))))
   :hints (("Goal"
            :use (:instance generated-word-outside-written-span
                            (address (+ 16 (proof-object-address object))) (before first) (after last))
            :in-theory (enable proof-subspan-p proof-span-p proof-disjoint-p)))
   :rule-classes nil))

(local
 (defthm generated-static-home-bindings-outside-write
   (implies (and (proof-span-p base (+ size 16))
                 (proof-disjoint-p base (+ base size 16) start end)
                 (generated-memory-outside-p start end first last)
                 (proof-static-spans-p pending base size first)
                 (proof-object-map-p statics statics nil base packages first)
                 (proof-object-disjoint-p start end statics first)
                 (generated-object-observations-agree-p pending statics base packages first last))
            (equal (proof-home-bindings-p pending base statics packages last buckets)
                   (proof-home-bindings-p pending base statics packages first buckets)))
   :hints (("Goal" :induct (len pending)
                   :in-theory (enable proof-home-bindings-p proof-static-spans-p
                                      generated-object-observations-agree-p))
           ("Subgoal *1/1"
            :use ((:instance generated-static-package-number-word-outside-write (object (car pending)))
                  (:instance generated-published-view-unchanged-outside-written-span
                             (objects statics)
                             (word (proof-load-word (+ 16 (proof-object-address (car pending))) first))))))
   :rule-classes nil))

(defthm generated-static-data-outside-written-span
  (let ((size (proof-static-size base first)))
    (implies (and (proof-static-p base objects packages first)
                  (proof-span-p base (+ size 16))
                  (proof-disjoint-p base (+ base size 16) start end)
                  (generated-memory-outside-p start end first last))
             (and (proof-static-p base objects packages last)
                  (equal (proof-static-size base last) size)
                  (equal (proof-dynamic-root base last) (proof-dynamic-root base first)))))
  :hints (("Goal"
           :expand ((proof-static-p base objects packages first) (proof-static-p base objects packages last))
           :use ((:instance generated-static-header-outside-written-span (size (proof-static-size base first)))
                 (:instance generated-static-spans-exclude-disjoint-span
                            (statics (proof-static-objects objects)) (machine first)
                            (size (proof-static-size base first)))
                 (:instance generated-object-map-outside-written-span (objects (proof-static-objects objects)))
                 (:instance generated-object-observations-outside-written-span
                            (pending (proof-static-objects objects)) (objects (proof-static-objects objects)))
                 (:instance generated-object-observations-preserve-static-spans
                            (pending (proof-static-objects objects)) (objects (proof-static-objects objects))
                            (size (proof-static-size base first)))
                 (:instance generated-static-home-bindings-outside-write
                            (pending (proof-static-objects objects)) (statics (proof-static-objects objects))
                            (size (proof-static-size base first))
                            (buckets (cdr (proof-view (proof-load-word (+ base 16) first)
                                                      base (proof-static-objects objects) packages first))))
                 (:instance generated-published-view-unchanged-outside-written-span
                            (objects (proof-static-objects objects)) (word *proof-nil*))
                 (:instance generated-published-view-unchanged-outside-written-span
                            (objects (proof-static-objects objects)) (word *proof-t*))
                 (:instance generated-published-view-unchanged-outside-written-span
                            (objects (proof-static-objects objects)) (word (proof-load-word (+ base 8) first)))
                 (:instance generated-published-view-unchanged-outside-written-span
                            (objects (proof-static-objects objects)) (word (proof-load-word (+ base 16) first))))
           :in-theory (enable proof-disjoint-p proof-span-p proof-value-p)))
  :rule-classes nil)
