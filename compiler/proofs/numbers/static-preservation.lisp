(in-package "BOYMOO-PROOFS")

(include-book "heap-layout")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-load-word proof-view proof-object-size proof-object-word
                     proof-object-map-p proof-object-record-p proof-object-disjoint-p
                     proof-pointer-address proof-word-tag proof-header-size proof-header-type
                     proof-number-machine-span-agrees-p proof-number-object-memory-p
                     proof-number-objects-memory-p proof-symbol-object-p proof-object-view
                     proof-static-spans-p proof-home-bindings-p
                     boymoo-model::a64-unsigned boymoo-model::a64-memory boymoo-model::a64-byte
                     acl2::binary-logand mod floor ash oddp)))

(local
 (defthm byte-entries-agreement-is-symmetric
   (implies (proof-byte-entries-agree-p entries start end first last)
            (proof-byte-entries-agree-p entries start end last first))
   :hints (("Goal" :induct (proof-byte-entries-agree-p entries start end first last)))))

(defthm proof-number-machine-span-agreement-is-symmetric
  (implies (proof-number-machine-span-agrees-p start end first last)
           (proof-number-machine-span-agrees-p start end last first))
  :hints (("Goal" :in-theory (e/d (proof-number-machine-span-agrees-p)
                                 (proof-byte-entries-agree-p))))
  :rule-classes nil)

(local
 (defthm object-memory-is-symmetric
   (implies (proof-number-object-memory-p object objects first last)
            (proof-number-object-memory-p object objects last first))
   :hints (("Goal"
            :use (proof-number-object-memory-keeps-size
                  (:instance proof-number-machine-span-agreement-is-symmetric
                             (start (proof-object-address object))
                             (end (+ (proof-object-address object) (proof-object-size object first)))))
            :in-theory (enable proof-number-object-memory-p)))
   :rule-classes nil))

(defthm proof-number-object-memory-reverses
  (implies (proof-number-objects-memory-p pending objects first last)
           (proof-number-objects-memory-p pending objects last first))
  :hints (("Goal"
           :induct (proof-number-objects-memory-p pending objects first last)
           :in-theory (enable proof-number-objects-memory-p))
          ("Subgoal *1/2" :use ((:instance object-memory-is-symmetric (object (car pending)))))
          ("Subgoal *1/3" :use ((:instance object-memory-is-symmetric (object (car pending))))))
  :rule-classes nil)

(defthm proof-number-view-equality-with-same-map
  (implies (proof-number-objects-memory-p objects objects first last)
           (equal (proof-view word base objects packages last)
                  (proof-view word base objects packages first)))
  :hints (("Goal"
           :use ((:instance proof-number-view-kept-with-object-memory (old-objects objects))
                 (:instance proof-number-view-kept-with-object-memory
                            (old-objects objects) (first last) (last first))
                 (:instance proof-number-object-memory-reverses (pending objects)))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm static-object-mapped-by-block
   (let* ((address (proof-object-address object))
          (bytes (proof-object-size object first)))
     (implies (and (proof-subspan-p address bytes (+ base 32) (+ base size))
                   (proof-number-object-memory-p object objects first first)
                   (proof-number-machine-span-agrees-p base (+ base size) first last))
              (proof-number-object-memory-p object objects first last)))
   :hints (("Goal"
            :use ((:instance proof-number-subspan-agrees
                             (lower base) (upper (+ base size))
                             (start (proof-object-address object))
                             (end (+ (proof-object-address object) (proof-object-size object first)))))
            :in-theory (e/d (proof-number-object-memory-p) (proof-span-p))))
   :rule-classes nil))

(defthm proof-number-static-objects-kept-by-block
  (implies (and (proof-static-spans-p pending base size first)
                (proof-number-objects-memory-p pending objects first first)
                (proof-number-machine-span-agrees-p base (+ base size) first last))
           (proof-number-objects-memory-p pending objects first last))
  :hints (("Goal"
           :induct (proof-static-spans-p pending base size first)
           :in-theory (e/d (proof-static-spans-p proof-number-objects-memory-p) (proof-subspan-p)))
          ("Subgoal *1/2" :use ((:instance static-object-mapped-by-block (object (car pending)))))
          ("Subgoal *1/3" :use ((:instance static-object-mapped-by-block (object (car pending))))))
  :rule-classes nil)

(local
 (defthm still-static-spans
   (implies (and (proof-static-spans-p pending base size first)
                 (proof-number-objects-memory-p pending objects first last))
            (proof-static-spans-p pending base size last))
   :hints (("Goal"
            :induct (proof-static-spans-p pending base size first)
            :in-theory (e/d (proof-static-spans-p proof-number-objects-memory-p) (proof-subspan-p)))
           ("Subgoal *1/2" :use ((:instance proof-number-object-memory-keeps-size (object (car pending)))))
           ("Subgoal *1/3" :use ((:instance proof-number-object-memory-keeps-size (object (car pending))))))
   :rule-classes nil))

(local
 (defthm static-symbol-field-count
   (let* ((address (proof-object-address object))
          (header (proof-load-word address machine)))
     (implies (and (proof-object-record-p object)
                   (proof-object-view object base objects packages machine)
                   (proof-symbol-object-p object machine)
                   (equal (assoc-equal address objects) object)
                   (proof-span-p address 24)
                   (natp base) (<= base address) (equal (mod base 8) 0))
              (equal (proof-header-size header) 16)))
   :hints (("Goal"
            :use ((:instance proof-number-box-word-address (address (proof-object-address object))))
            :in-theory (e/d (proof-object-view proof-object-word proof-object-record-p
                             proof-symbol-object-p proof-view)
                            (proof-view-step proof-load-string proof-integer-view
                             proof-cons-value proof-complex-value proof-symbol-value
                             proof-rational-value proof-number-integer-parity))
            :expand ((:free (depth word)
                             (proof-view-step :word word 0 depth base objects packages machine)))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm static-symbol-package-word-kept
   (let* ((address (proof-object-address object))
          (bytes (proof-object-size object first)))
     (implies (and (proof-object-record-p object)
                   (proof-object-view object base statics packages first)
                   (proof-symbol-object-p object first)
                   (proof-number-object-memory-p object statics first last)
                   (proof-subspan-p address bytes (+ base 32) (+ base size))
                   (proof-span-p base (+ size 24))
                   (equal (mod base 8) 0))
              (equal (proof-load-word (+ 16 address) last)
                     (proof-load-word (+ 16 address) first))))
   :hints (("Goal"
            :use ((:instance static-symbol-field-count (objects statics) (machine first))
                  (:instance proof-number-word-agrees-in-machine-span
                             (address (+ 16 (proof-object-address object)))
                             (lower (proof-object-address object))
                             (upper (+ (proof-object-address object)
                                       (proof-object-size object first)))))
            :in-theory (e/d (proof-number-object-memory-p proof-object-size proof-symbol-object-p)
                            (proof-align-up))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm static-home-bindings-kept
   (implies (and (proof-object-map-p pending statics symbols base packages first)
                 (proof-static-spans-p pending base size first)
                 (proof-number-objects-memory-p statics statics first last)
                 (proof-number-objects-memory-p pending statics first last)
                 (proof-home-bindings-p pending base statics packages first buckets)
                 (proof-span-p base (+ size 24))
                 (equal (mod base 8) 0))
            (proof-home-bindings-p pending base statics packages last buckets))
   :hints (("Goal"
            :induct (proof-object-map-p pending statics symbols base packages first)
            :in-theory (e/d (proof-home-bindings-p proof-number-objects-memory-p
                             proof-static-spans-p (:induction proof-object-map-p))
                            (proof-subspan-p proof-span-p proof-static-binding))
            :expand ((proof-object-map-p pending statics symbols base packages first)))
           (and (member-equal '(not (consp pending)) clause)
                '(:use ((:instance static-symbol-package-word-kept (object (car pending)))
                        (:instance proof-number-object-memory-keeps-symbol-test
                                   (object (car pending)) (objects statics))
                        (:instance proof-number-object-view-kept
                                   (object (car pending)) (old-objects statics) (objects statics))
                        (:instance proof-number-view-equality-with-same-map
                                   (word (proof-load-word (+ 16 (proof-object-address (car pending))) first))
                                   (objects statics))))))
   :rule-classes nil))

(local
 (defthm subset-of-cons
   (implies (subsetp-equal subset whole)
            (subsetp-equal subset (cons item whole)))
   :hints (("Goal" :induct (subsetp-equal subset whole)))))

(local
 (defthm subset-is-reflexive
   (subsetp-equal objects objects)
   :hints (("Goal" :induct (len objects)))))

(local
 (defthm static-block-supplies-object-memory
   (let ((statics (proof-static-objects objects))
         (size (proof-static-size base first)))
     (implies (and (proof-static-p base objects packages first)
                   (proof-number-machine-span-agrees-p base (+ base size) first last))
              (proof-number-objects-memory-p statics statics first last)))
   :hints (("Goal"
            :use ((:instance proof-number-map-spans-with-unchanged-memory
                             (old-objects (proof-static-objects objects))
                             (pending (proof-static-objects objects))
                             (machine first) (extra nil))
                  (:instance proof-number-static-objects-kept-by-block
                             (pending (proof-static-objects objects))
                             (objects (proof-static-objects objects))
                             (size (proof-static-size base first))))
            :in-theory (disable proof-static-buckets-p proof-package-bindings-p proof-packages-p
                                proof-static-binding proof-static-objects)
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-static-block-kept
  (let* ((statics (proof-static-objects old-objects))
         (size (proof-static-size base first)))
    (implies (and (proof-static-p base old-objects packages first)
                  (proof-span-p base (+ size 24))
                  (proof-number-machine-span-agrees-p base (+ base size) first last)
                  (equal (proof-static-objects objects) statics))
             (proof-static-p base objects packages last)))
  :hints (("Goal"
           :use ((:instance static-block-supplies-object-memory (objects old-objects))
                 (:instance proof-number-object-map-kept
                            (pending (proof-static-objects old-objects))
                            (old-objects (proof-static-objects old-objects))
                            (objects (proof-static-objects old-objects))
                            (symbols nil))
                 (:instance still-static-spans
                            (pending (proof-static-objects old-objects))
                            (objects (proof-static-objects old-objects)) (size (proof-static-size base first)))
                 (:instance static-home-bindings-kept
                            (pending (proof-static-objects old-objects))
                            (statics (proof-static-objects old-objects))
                            (symbols nil) (size (proof-static-size base first))
                            (buckets (cdr (proof-view (proof-load-word (+ base 16) first)
                                                       base (proof-static-objects old-objects) packages first))))
                 (:instance proof-number-word-agrees-in-machine-span
                            (address base) (lower base) (upper (+ base (proof-static-size base first))))
                 (:instance proof-number-word-agrees-in-machine-span
                            (address (+ base 8)) (lower base) (upper (+ base (proof-static-size base first))))
                 (:instance proof-number-word-agrees-in-machine-span
                            (address (+ base 16)) (lower base) (upper (+ base (proof-static-size base first))))
                 (:instance proof-number-view-equality-with-same-map
                            (word *proof-nil*) (objects (proof-static-objects old-objects)))
                 (:instance proof-number-view-equality-with-same-map
                            (word *proof-t*) (objects (proof-static-objects old-objects)))
                 (:instance proof-number-view-equality-with-same-map
                            (word (proof-load-word (+ base 8) first))
                            (objects (proof-static-objects old-objects)))
                 (:instance proof-number-view-equality-with-same-map
                            (word (proof-load-word (+ base 16) first))
                            (objects (proof-static-objects old-objects))))
           :in-theory (e/d (proof-static-size)
                           (proof-static-buckets-p proof-package-bindings-p proof-packages-p
                            proof-static-binding proof-static-objects))
           :do-not-induct t))
  :rule-classes nil)
