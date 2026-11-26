(in-package "BOYMOO-PROOFS")

(include-book "contracts")
(include-book "byte-ranges")
(include-book "heap-views")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable proof-object-view proof-object-size proof-static-p
                           proof-object-map-p proof-static-spans-p proof-external-objects
                           proof-heap-layout-p proof-heap-object-spans-p
                           proof-string-accounting-p proof-dynamic-symbol-objects-p
                           proof-stack-prefix proof-dynamic-entries proof-dynamic-view
                           proof-object-disjoint-p proof-object-record-p
                           proof-span-p proof-subspan-p proof-static-size
                           proof-static-objects proof-load-word)))

(local
 (defthm p6-load-natural
   (natp (boymoo-model::a64-load count address machine))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable boymoo-model::a64-load)))))

(local
 (defthm p6-loaded-word-natural
   (natp (proof-load-word address machine))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable proof-load-word)))))

(local
 (defthm p6-static-size-natural
   (natp (proof-static-size base machine))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable proof-static-size proof-load-word)))))

(defthm p6-writable-span-is-readable
  (implies (proof-covered-p address size :write regions)
           (proof-covered-p address size :read regions))
  :hints (("Goal" :induct (proof-covered-p address size :write regions)
                  :in-theory (enable proof-covered-p proof-region-allows-p))))

(local
 (defthm p6-read-from-region-entry
   (implies (and (member-equal (proof-region low high :rw) regions)
                 (proof-subspan-p address size low high))
            (proof-covered-p address size :read regions))
   :rule-classes nil
   :hints (("Goal" :induct (member-equal (proof-region low high :rw) regions)
                   :in-theory (enable proof-covered-p proof-region-allows-p)))))

(local
 (defthm p6-aligned-address-upper-bound
   (implies (and (natp address) (member-equal delta '(8 65536)))
            (<= address (proof-align-up address delta)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable proof-align-up ceiling floor)
                   :use ((:instance p6-floor-bounds (x address) (d delta))
                         (:instance p6-numerator-product (x (* address (/ delta)))))))))

(defthm p6-static-fits-heap-range
  (implies (proof-heap-layout-p world)
           (<= (+ (proof-heap-base world)
                  (proof-static-size (proof-heap-base world) (proof-world-machine world))
                  (* 2 *proof-space-size*))
               (proof-spaces-end world)))
  :rule-classes nil
  :hints (("Goal" :in-theory (enable proof-heap-layout-p)
                  :use ((:instance p6-aligned-address-upper-bound
                                   (address (+ (proof-heap-base world)
                                               (proof-static-size (proof-heap-base world)
                                                                  (proof-world-machine world))))
                                   (delta *proof-runtime-page*))))))

(local
 (defthm p6-heap-read-from-interior
   (implies (and (proof-heap-layout-p world)
                 (proof-subspan-p address size (- (proof-heap-base world) *proof-heap-prefix*)
                                  (proof-spaces-end world)))
            (proof-covered-p address size :read (proof-world-regions world)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (proof-heap-layout-p proof-subspan-p)
                                   (proof-align-up proof-page-size-p proof-disjoint-p proof-regions-p))
                   :use ((:instance p6-covered-subspan
                                    (address (- (proof-heap-base world) *proof-heap-prefix*))
                                    (size (+ *proof-heap-prefix* (- (proof-spaces-end world)
                                                                   (proof-heap-base world))))
                                    (access :write) (part address) (width size)
                                    (regions (proof-world-regions world))))))))

(local
 (defthm p6-static-record-in-filtered-map
   (implies (and (consp (assoc-equal address objects))
                 (eq (proof-object-zone (assoc-equal address objects)) :static))
            (equal (assoc-equal address (proof-static-objects objects))
                   (assoc-equal address objects)))
   :hints (("Goal" :induct (assoc-equal address objects)
                   :in-theory (enable proof-static-objects)))))

(local
 (defthm p6-static-record-span
   (let ((record (assoc-equal address statics)))
     (implies (and (consp record) (proof-static-spans-p statics base size machine))
              (proof-subspan-p address (proof-object-size record machine)
                               (+ base 32) (+ base size))))
   :rule-classes nil
   :hints (("Goal" :induct (assoc-equal address statics)
                   :in-theory (enable proof-static-spans-p proof-object-address)))))

(local
 (defthm p6-heap-layout-has-prefix-room
   (implies (proof-heap-layout-p world)
            (<= *proof-heap-prefix* (proof-heap-base world)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (proof-heap-layout-p)
                                   (proof-align-up proof-page-size-p proof-disjoint-p proof-regions-p))))))

(local
 (defthm p6-static-object-is-readable
   (let* ((object (assoc-equal address objects))
          (base (proof-heap-base world)) (machine (proof-world-machine world)))
     (implies (and (consp object) (eq (proof-object-zone object) :static)
                   (proof-heap-layout-p world) (proof-static-p base objects packages machine))
              (proof-covered-p address (proof-object-size object machine) :read
                               (proof-world-regions world))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (proof-static-p proof-subspan-p)
                                   (proof-packages-p proof-static-buckets-p proof-home-bindings-p
                                    proof-package-bindings-p proof-package-row-views))
                   :use (p6-static-fits-heap-range p6-heap-layout-has-prefix-room
                         (:instance p6-static-record-span
                                    (statics (proof-static-objects objects))
                                    (base (proof-heap-base world)) (machine (proof-world-machine world))
                                    (size (proof-static-size (proof-heap-base world) (proof-world-machine world))))
                         (:instance p6-heap-read-from-interior
                                    (size (proof-object-size (assoc-equal address objects)
                                                             (proof-world-machine world)))))))))

(local
 (defthm p6-active-record-span
   (let* ((object (assoc-equal address objects))
          (size (proof-object-size object (proof-world-machine world))))
     (implies (and (consp object) (eq (proof-object-zone object) :active)
                   (proof-heap-object-spans-p objects external world))
              (if (eq (proof-object-kind object) :cons)
                  (proof-subspan-p address size (proof-cons-floor world) (proof-active-end world))
                (proof-subspan-p address size (proof-active-floor world) (proof-box-top world)))))
   :rule-classes nil
   :hints (("Goal" :induct (assoc-equal address objects)
                   :in-theory (enable proof-heap-object-spans-p proof-object-address)))))

(local
 (defthm p6-active-span-within-heap-range
   (implies (proof-heap-layout-p world)
            (and (<= (- (proof-heap-base world) *proof-heap-prefix*) (proof-active-floor world))
                 (<= (proof-active-floor world) (proof-cons-floor world))
                 (<= (proof-box-top world) (proof-active-end world))
                 (<= (proof-active-end world) (proof-spaces-end world))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (proof-heap-layout-p)
                                   (proof-align-up proof-page-size-p proof-disjoint-p proof-regions-p))
                   :use ((:instance p6-aligned-address-upper-bound
                                    (address (+ (proof-heap-base world)
                                                (proof-static-size (proof-heap-base world) (proof-world-machine world))))
                                    (delta *proof-runtime-page*)))))))

(local
 (defthm p6-active-object-is-readable
   (let* ((object (assoc-equal address objects))
          (size (proof-object-size object (proof-world-machine world))))
     (implies (and (consp object) (eq (proof-object-zone object) :active)
                   (proof-heap-layout-p world) (proof-heap-object-spans-p objects external world))
              (proof-covered-p address size :read (proof-world-regions world))))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable proof-subspan-p)
                   :use (p6-active-record-span p6-active-span-within-heap-range p6-heap-layout-has-prefix-room
                         (:instance p6-heap-read-from-interior
                                    (size (proof-object-size (assoc-equal address objects)
                                                             (proof-world-machine world)))))))))

(defthm p6-listed-region-is-valid
  (implies (and (proof-regions-p regions) (member-equal region regions))
           (proof-region-p region))
  :rule-classes nil
  :hints (("Goal" :induct (member-equal region regions)
                  :in-theory (disable proof-region-p proof-region-disjoint-p))))

(local
 (defthm p6-interior-of-readable-mapping
   (implies (and (proof-regions-p regions)
                 (member-equal (proof-region low high :rw) regions)
                 (integerp address) (posp size) (<= low address) (<= (+ address size) high))
            (proof-covered-p address size :read regions))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable proof-span-p proof-subspan-p)
                   :use (p6-read-from-region-entry
                         (:instance p6-listed-region-is-valid (region (proof-region low high :rw))))))))

(local
 (defthm p6-external-mapping-includes-contents
   (let* ((header (+ 24 head))
          (size (proof-header-size (proof-load-word header (proof-world-machine world))))
          (extent (proof-align-up (+ 32 size) *proof-runtime-page*)))
     (implies (and (integerp head) (proof-regions-p (proof-world-regions world))
                   (member-equal (proof-region head (+ head extent) :rw) (proof-world-regions world)))
              (proof-covered-p header (+ 8 size) :read (proof-world-regions world))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (disable proof-regions-p proof-align-up)
            :use ((:instance p6-aligned-address-upper-bound (delta *proof-runtime-page*)
                             (address (+ 32 (proof-header-size
                                             (proof-load-word (+ 24 head) (proof-world-machine world))))))
                  (:instance p6-interior-of-readable-mapping
                             (low head) (address (+ 24 head))
                             (size (+ 8 (proof-header-size
                                         (proof-load-word (+ 24 head) (proof-world-machine world)))))
                             (high (+ head (proof-align-up
                                            (+ 32 (proof-header-size
                                                   (proof-load-word (+ 24 head) (proof-world-machine world))))
                                            *proof-runtime-page*)))
                             (regions (proof-world-regions world))))))))

(local
 (defthm p6-external-object-is-readable
   (let* ((mappings (proof-external-objects head fuel world objects))
          (machine (proof-world-machine world))
          (header (proof-load-word address machine)))
     (implies (and (natp head) (proof-regions-p (proof-world-regions world)) (member-equal address (cdr mappings)))
              (and (equal (proof-object-kind (assoc-equal address objects)) :header)
                   (equal (proof-header-type header) 1)
                   (proof-covered-p address (+ 8 (proof-header-size header)) :read
                                    (proof-world-regions world)))))
   :rule-classes nil
   :hints (("Goal"
            :induct (proof-external-objects head fuel world objects)
            :in-theory (e/d (proof-external-objects)
                            (proof-align-up proof-region-p proof-regions-p proof-disjoint-p))
            :do-not '(generalize eliminate-destructors))
           (and stable-under-simplificationp
                '(:use p6-external-mapping-includes-contents)))))

(local
 (defthm p6-record-zone-and-external-membership
   (let ((object (assoc-equal address objects)))
     (implies (and (consp object) (proof-heap-object-spans-p objects external world))
              (and (member-eq (proof-object-zone object) '(:static :active :external))
                   (implies (eq (proof-object-zone object) :external)
                            (member-equal address external)))))
   :rule-classes nil
   :hints (("Goal" :induct (assoc-equal address objects)
                   :in-theory (enable proof-heap-object-spans-p proof-object-address)))))

(defund p6-object-content-size (address object machine)
  (if (eq (proof-object-kind object) :cons)
      16
    (+ 8 (proof-header-size (proof-load-word address machine)))))

(local
 (defthm p6-map-record-has-key
   (implies (consp (assoc-equal address objects))
            (equal (car (assoc-equal address objects)) address))
   :hints (("Goal" :induct (assoc-equal address objects)))))

(local
 (defthm p6-record-content-subspan
   (let* ((object (assoc-equal address objects)) (size (proof-object-size object machine)))
     (implies (and (consp object) (proof-span-p address size))
              (proof-subspan-p address (p6-object-content-size address object machine) address (+ address size))))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (proof-span-p proof-subspan-p proof-object-size proof-object-address
                                          p6-object-content-size) (proof-align-up))
            :use ((:instance p6-aligned-address-upper-bound (delta 8)
                             (address (proof-header-size (proof-load-word address machine)))))))))

(defthm p6-covered-span-is-valid
  (implies (proof-covered-p address size access regions)
           (proof-span-p address size))
  :rule-classes nil
  :hints (("Goal" :induct (proof-covered-p address size access regions)
                  :in-theory (enable proof-covered-p proof-subspan-p))))

(local
 (defthm p6-read-object-content-from-size
   (let* ((object (assoc-equal address objects)) (size (proof-object-size object machine)))
     (implies (and (consp object) (proof-covered-p address size :read regions))
              (proof-covered-p address (p6-object-content-size address object machine) :read regions)))
   :rule-classes nil
   :hints (("Goal" :use (p6-record-content-subspan
                         (:instance p6-covered-span-is-valid
                                    (access :read) (size (proof-object-size (assoc-equal address objects) machine)))
                         (:instance p6-covered-subspan
                                    (access :read) (size (proof-object-size (assoc-equal address objects) machine))
                                    (part address)
                                    (width (p6-object-content-size address (assoc-equal address objects) machine))))))))

(defthm p6-published-object-contents-are-readable
  (let* ((object (assoc-equal address objects)) (machine (proof-world-machine world)))
    (implies (and (consp object) (proof-heap-p world objects packages))
             (proof-covered-p address (p6-object-content-size address object machine) :read
                              (proof-world-regions world))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable proof-heap-p p6-object-content-size)
           :use (p6-static-object-is-readable
                 (:instance p6-active-object-is-readable
                            (external (cdr (proof-external-objects (proof-external-head world)
                                                                   (len objects) world objects))))
                 (:instance p6-record-zone-and-external-membership
                            (external (cdr (proof-external-objects (proof-external-head world)
                                                                   (len objects) world objects))))
                 (:instance p6-external-object-is-readable (head (proof-external-head world)) (fuel (len objects)))
                 (:instance p6-read-object-content-from-size
                            (machine (proof-world-machine world)) (regions (proof-world-regions world)))))
          (and stable-under-simplificationp '(:in-theory (enable proof-heap-layout-p)))))

(defund p6-machine-reservation-start (world)
  (- (proof-machine-limit world) *proof-machine-margin*))

(defund p6-reservations-disjoint-p (start end world)
  (let ((machine-start (p6-machine-reservation-start world)))
    (and (proof-disjoint-p start end (proof-stack-base world) (proof-stack-end world))
         (proof-disjoint-p start end machine-start (+ machine-start *proof-machine-reservation*)))))

(defthm p6-heap-area-is-outside-stack-reservations
  (implies (and (proof-heap-layout-p world)
                (<= (- (proof-heap-base world) *proof-heap-prefix*) start)
                (<= end (proof-spaces-end world)))
           (p6-reservations-disjoint-p start end world))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (p6-reservations-disjoint-p p6-machine-reservation-start
                                                           proof-heap-layout-p proof-disjoint-p)
                                  (proof-align-up proof-page-size-p proof-regions-p)))))

(local
 (defthm p6-external-content-is-outside-stack-reservations
   (let* ((mappings (proof-external-objects head fuel world objects))
          (machine (proof-world-machine world))
          (content (p6-object-content-size address (assoc-equal address objects) machine)))
     (implies (and (natp head) (member-equal address (cdr mappings)))
              (p6-reservations-disjoint-p address (+ address content) world)))
   :rule-classes nil
   :hints (("Goal"
            :induct (proof-external-objects head fuel world objects)
            :in-theory (e/d (proof-external-objects p6-object-content-size
                                                   p6-reservations-disjoint-p p6-machine-reservation-start
                                                   proof-disjoint-p)
                            (proof-align-up proof-load-word proof-header-size p6-loaded-header-fields))
            :do-not '(generalize eliminate-destructors))
           (and stable-under-simplificationp
                '(:use ((:instance p6-aligned-address-upper-bound (delta *proof-runtime-page*)
                                   (address (+ 32 (proof-header-size
                                                   (proof-load-word (+ 24 head)
                                                                    (proof-world-machine world))))))))))))

(local
 (defthm p6-static-content-is-outside-stack-reservations
   (let* ((object (assoc-equal address objects))
          (base (proof-heap-base world)) (machine (proof-world-machine world))
          (content (p6-object-content-size address object machine)))
     (implies (and (consp object) (eq (proof-object-zone object) :static)
                   (proof-heap-layout-p world) (proof-static-p base objects packages machine))
              (p6-reservations-disjoint-p address (+ address content) world)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (e/d (proof-static-p proof-span-p proof-subspan-p)
                            (proof-packages-p proof-static-buckets-p proof-home-bindings-p
                             proof-package-bindings-p proof-package-row-views))
            :use (p6-static-fits-heap-range p6-heap-layout-has-prefix-room
                  (:instance p6-static-record-span (statics (proof-static-objects objects))
                             (base (proof-heap-base world)) (machine (proof-world-machine world))
                             (size (proof-static-size (proof-heap-base world) (proof-world-machine world))))
                  (:instance p6-record-content-subspan (machine (proof-world-machine world)))
                  (:instance p6-heap-area-is-outside-stack-reservations (start address)
                             (end (+ address (p6-object-content-size address (assoc-equal address objects)
                                                                      (proof-world-machine world))))))))))

(local
 (defthm p6-active-content-is-outside-stack-reservations
   (let* ((object (assoc-equal address objects))
          (machine (proof-world-machine world))
          (content (p6-object-content-size address object machine)))
     (implies (and (consp object) (eq (proof-object-zone object) :active)
                   (proof-heap-layout-p world)
                   (proof-heap-object-spans-p objects external world))
              (p6-reservations-disjoint-p address (+ address content) world)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (enable proof-span-p proof-subspan-p)
            :use (p6-active-record-span p6-active-span-within-heap-range
                  (:instance p6-record-content-subspan (machine (proof-world-machine world)))
                  (:instance p6-heap-area-is-outside-stack-reservations (start address)
                             (end (+ address (p6-object-content-size address (assoc-equal address objects)
                                                                      (proof-world-machine world))))))))))

(defthm p6-published-object-contents-avoid-stacks
  (let* ((object (assoc-equal address objects))
         (content (p6-object-content-size address object (proof-world-machine world))))
    (implies (and (consp object) (proof-heap-p world objects packages))
             (and (proof-span-p address content)
                  (p6-reservations-disjoint-p address (+ address content) world))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (enable proof-heap-p)
           :use (p6-static-content-is-outside-stack-reservations
                 (:instance p6-active-content-is-outside-stack-reservations
                            (external (cdr (proof-external-objects (proof-external-head world)
                                                                    (len objects) world objects))))
                 (:instance p6-record-zone-and-external-membership
                            (external (cdr (proof-external-objects (proof-external-head world)
                                                                    (len objects) world objects))))
                 (:instance p6-external-content-is-outside-stack-reservations
                            (head (proof-external-head world)) (fuel (len objects)))
                 p6-published-object-contents-are-readable
                 (:instance p6-covered-span-is-valid (access :read) (regions (proof-world-regions world))
                            (size (p6-object-content-size address (assoc-equal address objects)
                                                           (proof-world-machine world))))))))

(defthm p6-pointer-view-has-object-record
  (let* ((tag (proof-word-tag word)) (address (proof-pointer-address word base))
         (object (assoc-equal address objects)))
    (implies (and (proof-view word base objects packages machine) (member-equal tag '(0 2)))
             (and (consp object)
                  (equal (proof-object-kind object) (if (equal tag 0) :cons :header)))))
  :rule-classes nil
  :hints (("Goal"
           :expand ((proof-view word base objects packages machine)
                    (:free (depth) (proof-view-step :word word 0 depth base objects packages machine)))
           :in-theory (e/d (proof-object-kind)
                           (proof-cons-value proof-integer-view proof-symbol-value
                            proof-rational-value proof-complex-value))
           :use p6-even-tag-is-not-an-immediate-integer)))

(local
 (defthm p6-cons-address-with-field-offset
   (let* ((word (proof-world-reg 0 world)) (base (proof-heap-base world))
          (address (proof-pointer-address word base)))
     (implies (and (equal (proof-word-tag word) 0) (proof-span-p address 16))
              (equal (p6-projection-address name word base) (+ address (if (eq name 'car) 0 8)))))
   :hints (("Goal" :in-theory (e/d (proof-span-p proof-pointer-address p6-projection-address)
                                   (p6-unsigned-add p6-unsigned-add-integer))
                   :use ((:instance p6-unsigned-add-integer
                                    (width 64) (x (+ (proof-world-reg 0 world) (proof-heap-base world)))
                                    (y (if (eq name 'car) 0 8)))
                         (:instance p6-unsigned-identity
                                    (width 64) (x (+ 8 (proof-pointer-address (proof-world-reg 0 world)
                                                                              (proof-heap-base world))))))))))

(local
 (defthm p6-header-load-address
   (implies (equal (proof-word-tag (proof-world-reg 0 world)) 2)
            (equal (p6-header-address world)
                   (proof-pointer-address (proof-world-reg 0 world) (proof-heap-base world))))
   :hints (("Goal" :in-theory (enable p6-header-address proof-pointer-address)))))

(defthm p6-leaf-loads-readable-from-heap
  (implies (and (proof-heap-p world objects packages) (proof-reg-value-p 0 value world objects packages))
           (p6-leaf-primitive-loads-p name world))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (p6-leaf-primitive-loads-p proof-reg-value-p proof-machine-value-p
                                                     proof-value-p p6-object-content-size proof-subspan-p proof-span-p)
                           (p6-cons-address-with-field-offset))
           :use ((:instance p6-pointer-view-has-object-record
                            (word (proof-world-reg 0 world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance p6-published-object-contents-are-readable
                            (address (proof-pointer-address (proof-world-reg 0 world) (proof-heap-base world))))
                 p6-cons-address-with-field-offset
                 (:instance p6-covered-span-is-valid
                            (size 16) (access :read) (regions (proof-world-regions world))
                            (address (proof-pointer-address (proof-world-reg 0 world) (proof-heap-base world))))
                 (:instance p6-covered-span-is-valid
                            (address (p6-header-address world)) (access :read) (regions (proof-world-regions world))
                            (size (+ 8 (proof-header-size (proof-load-word (p6-header-address world)
                                                                           (proof-world-machine world))))))
                 (:instance p6-covered-subspan
                            (address (proof-pointer-address (proof-world-reg 0 world) (proof-heap-base world)))
                            (size 16) (access :read) (width 8)
                            (part (p6-projection-address name (proof-world-reg 0 world) (proof-heap-base world)))
                            (regions (proof-world-regions world)))
                 (:instance p6-covered-subspan
                            (address (p6-header-address world)) (access :read) (width 1)
                            (size (+ 8 (proof-header-size (proof-load-word (p6-header-address world)
                                                                           (proof-world-machine world)))))
                            (part (p6-header-address world)) (regions (proof-world-regions world)))))))

(defthm p6-mapped-leaf-primitive-runtime-contract
  (let* ((sites (p6-leaf-primitive-sites name world))
         (after (p6-path-end sites world)))
    (implies (and (p6-leaf-primitive-p name) (consp args)
                  (proof-runtime-pre-p name args program labels code-base world objects packages)
                  (p6-path-entry-p sites runtime-base world))
             (and (proof-segment-p (len sites) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p name args program world after objects objects packages))))
  :rule-classes nil
  :hints (("Goal" :use (p6-heap-has-boolean-views p6-leaf-primitive-runtime-contract
                        (:instance p6-leaf-loads-readable-from-heap (value (car args)))))))
