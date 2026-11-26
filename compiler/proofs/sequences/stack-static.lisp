(in-package "BOYMOO-PROOFS")

(include-book "stack-objects")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm sequence-static-interval-has-room-for-fields
   (let* ((base (proof-heap-base world))
          (size (proof-static-size base (proof-world-machine world))))
     (implies (proof-heap-layout-p world)
              (and (proof-span-p base (+ size 24))
                   (<= (+ base size 24) (proof-spaces-end world)))))
   :hints
   (("Goal"
     :use (sequence-heap-layout-bounds
           (:instance sequence-align-up-covers-address
                      (address (+ (proof-heap-base world)
                                  (proof-static-size (proof-heap-base world)
                                                     (proof-world-machine world))))
                      (alignment *proof-runtime-page*)))
     :expand ((proof-heap-layout-p world))))
   :rule-classes nil))

(local
 (defthm sequence-static-head-fields-agree
   (let* ((address (proof-object-address (car pending)))
          (word (proof-load-word (+ address 16) first)))
     (implies (and (consp pending)
                   (sequence-object-storage-agrees-p pending first last)
                   (sequence-object-storage-agrees-p objects first last)
                   (proof-static-spans-p pending base size first)
                   (proof-span-p base (+ size 24))
                   (sequence-machine-span-agrees-p base (+ base size 24) first last))
              (and (equal (proof-symbol-object-p (car pending) last)
                          (proof-symbol-object-p (car pending) first))
                   (equal (proof-object-view (car pending) base objects packages last)
                          (proof-object-view (car pending) base objects packages first))
                   (equal (proof-view (proof-load-word (+ address 16) last)
                                      base objects packages last)
                          (proof-view word base objects packages first))
                   (proof-static-spans-p (cdr pending) base size first)
                   (sequence-object-storage-agrees-p (cdr pending) first last))))
   :hints
   (("Goal"
     :in-theory (enable proof-load-word)
     :expand ((proof-static-spans-p pending base size first))
     :use (sequence-object-head-on-agreed-storage
           (:instance sequence-object-view-on-agreed-storage (object (car pending)))
           (:instance sequence-view-on-agreed-objects
                      (word (proof-load-word (+ 16 (proof-object-address (car pending))) first)))
           (:instance sequence-read-in-agreed-machine-span
                      (start base) (end (+ base size 24)) (count 8)
                      (address (+ 16 (proof-object-address (car pending))))))))
   :rule-classes nil))

(local
 (defthm sequence-home-bindings-on-agreed-storage
   (implies (and (sequence-object-storage-agrees-p pending first last)
                 (sequence-object-storage-agrees-p objects first last)
                 (proof-static-spans-p pending base size first)
                 (proof-span-p base (+ size 24))
                 (sequence-machine-span-agrees-p base (+ base size 24) first last))
            (equal (proof-home-bindings-p pending base objects packages last buckets)
                   (proof-home-bindings-p pending base objects packages first buckets)))
   :hints
   (("Goal"
     :in-theory (disable proof-symbol-object-p proof-object-view proof-view
                         proof-static-binding proof-span-p proof-home-bindings-p)
     :induct (len pending)
     :expand ((:free (machine)
                     (proof-home-bindings-p pending base objects packages machine buckets))))
    ("Subgoal *1/1" :use sequence-static-head-fields-agree))
   :rule-classes nil))

(local
 (defthm sequence-static-metadata-on-agreed-storage
   (implies (and (proof-span-p base (+ size 24))
                 (natp size) (<= 24 size)
                 (sequence-machine-span-agrees-p base (+ base size 24) first last))
            (and (equal (proof-static-size base last) (proof-static-size base first))
                 (equal (proof-load-word (+ base 8) last) (proof-load-word (+ base 8) first))
                 (equal (proof-load-word (+ base 16) last) (proof-load-word (+ base 16) first))))
   :hints
   (("Goal"
     :in-theory (enable proof-load-word proof-static-size)
     :use ((:instance sequence-read-in-agreed-machine-span
                      (start base) (end (+ base size 24)) (address base) (count 8))
           (:instance sequence-read-in-agreed-machine-span
                      (start base) (end (+ base size 24)) (address (+ base 8)) (count 8))
           (:instance sequence-read-in-agreed-machine-span
                      (start base) (end (+ base size 24)) (address (+ base 16)) (count 8)))))
   :rule-classes nil))

(local
 (defthm sequence-static-p-on-agreed-storage
   (let* ((statics (proof-static-objects objects))
          (size (proof-static-size base first)))
     (implies (and (proof-static-p base objects packages first)
                   (sequence-object-storage-agrees-p statics first last)
                   (proof-span-p base (+ size 24))
                   (sequence-machine-span-agrees-p base (+ base size 24) first last))
              (proof-static-p base objects packages last)))
   :hints
   (("Goal"
     :in-theory (e/d (proof-value-p)
                     (proof-object-map-p proof-static-spans-p proof-view proof-home-bindings-p
                      proof-static-buckets-p proof-package-bindings-p proof-packages-p
                      proof-package-row-views proof-object-size proof-static-objects))
     :expand ((proof-static-p base objects packages first)
              (proof-static-p base objects packages last))
     :use ((:instance sequence-static-metadata-on-agreed-storage
                      (size (proof-static-size base first)))
           (:instance sequence-object-map-on-agreed-storage
                      (symbols nil) (pending (proof-static-objects objects))
                      (objects (proof-static-objects objects)))
           (:instance sequence-static-spans-on-agreed-objects
                      (pending (proof-static-objects objects)) (size (proof-static-size base first)))
           (:instance sequence-view-on-agreed-objects
                      (objects (proof-static-objects objects)) (word *proof-nil*))
           (:instance sequence-view-on-agreed-objects
                      (objects (proof-static-objects objects)) (word *proof-t*))
           (:instance sequence-view-on-agreed-objects
                      (objects (proof-static-objects objects))
                      (word (proof-load-word (+ base 8) first)))
           (:instance sequence-view-on-agreed-objects
                      (objects (proof-static-objects objects))
                      (word (proof-load-word (+ base 16) first)))
           (:instance sequence-home-bindings-on-agreed-storage
                      (size (proof-static-size base first)) (pending (proof-static-objects objects))
                      (objects (proof-static-objects objects))
                      (buckets (cdr (proof-view (proof-load-word (+ base 16) first)
                                                base (proof-static-objects objects)
                                                packages first)))))))
   :rule-classes nil))

(defthm sequence-stack-write-keeps-static-heap
  (implies (and (proof-heap-p before objects packages)
                (sequence-stack-write-p start end before after))
           (proof-static-p (proof-heap-base after) objects packages
                           (proof-world-machine after)))
  :hints
  (("Goal"
    :in-theory (e/d (sequence-stack-write-p sequence-heap-registers-agree-p)
                    (proof-span-p proof-subspan-p proof-stack-prefix proof-string-accounting-p
                     proof-dynamic-symbol-objects-p proof-dynamic-entries proof-dynamic-view))
    :expand ((proof-heap-p before objects packages))
    :use ((:instance sequence-static-interval-has-room-for-fields (world before))
          sequence-stack-write-keeps-heap-spans sequence-stack-write-keeps-published-storage
          (:instance sequence-static-storage-on-agreed-objects
                     (pending objects)
                     (first (proof-world-machine before)) (last (proof-world-machine after)))
          (:instance sequence-static-p-on-agreed-storage
                     (base (proof-heap-base before))
                     (first (proof-world-machine before)) (last (proof-world-machine after)))
          (:instance sequence-machine-agreement-on-subinterval
                     (first (proof-world-machine before)) (last (proof-world-machine after))
                     (lower (- (proof-heap-base before) *proof-heap-prefix*))
                     (upper (proof-spaces-end before))
                     (start (proof-heap-base before))
                     (end (+ (proof-heap-base before) 24
                             (proof-static-size (proof-heap-base before)
                                                (proof-world-machine before))))))))
  :rule-classes nil)
