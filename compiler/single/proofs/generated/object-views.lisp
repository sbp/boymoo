(in-package "BOYMOO-PROOFS")

(include-book "list-views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-object-map-p proof-object-disjoint-p proof-object-record-p
                    proof-object-size proof-object-view proof-symbol-object-p proof-static-objects
                    proof-view proof-view-step proof-static-p proof-heap-p proof-value-p
                    proof-heap-layout-p proof-load-word proof-load-string
                    proof-integer-view proof-cons-value proof-complex-value proof-rational-value
                    proof-symbol-value proof-immediate-integer-p proof-pointer-address
                    proof-word-tag proof-span-p proof-subspan-p proof-disjoint-p expt))

(local
 (defthm generated-object-size-positive
   (posp (proof-object-size object machine))
   :hints (("Goal" :in-theory (enable proof-object-size proof-align-up ceiling floor)))
   :rule-classes (:type-prescription
                  (:linear :corollary (< 0 (proof-object-size object machine))))))

(local
 (defthm generated-disjoint-objects-exclude-start
   (implies (and (integerp start) (< start end)
                 (proof-object-disjoint-p start end objects machine))
            (not (assoc-equal start objects)))
   :hints (("Goal" :induct (proof-object-disjoint-p start end objects machine)
                   :in-theory (enable proof-object-disjoint-p proof-disjoint-p)))
   :rule-classes nil))

(defund generated-distinct-object-addresses-p (objects)
  (if (atom objects)
      t
    (and (not (assoc-equal (caar objects) (cdr objects)))
         (generated-distinct-object-addresses-p (cdr objects)))))

(defthm generated-published-object-addresses-are-distinct
  (implies (proof-object-map-p pending objects symbols base packages machine)
           (generated-distinct-object-addresses-p pending))
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
                  :in-theory (enable proof-object-map-p proof-object-address proof-span-p
                                     generated-distinct-object-addresses-p))
          ("Subgoal *1/2"
           :use (:instance generated-disjoint-objects-exclude-start
                           (start (caar pending))
                           (end (+ (caar pending) (proof-object-size (car pending) machine)))
                           (objects (cdr pending)))))
  :rule-classes nil)

(defthm generated-static-lookup-in-full-map
  (implies (and (generated-distinct-object-addresses-p objects)
                (assoc-equal address (proof-static-objects objects)))
           (equal (assoc-equal address objects)
                  (assoc-equal address (proof-static-objects objects))))
  :hints (("Goal" :induct (proof-static-objects objects)
                  :in-theory (enable proof-static-objects generated-distinct-object-addresses-p)))
  :rule-classes nil)

(local
 (defthm generated-static-lookup-in-full-map-reversed
   (implies (and (generated-distinct-object-addresses-p objects)
                 (assoc-equal address (proof-static-objects objects)))
            (equal (assoc-equal address (proof-static-objects objects))
                   (assoc-equal address objects)))
   :hints (("Goal" :use generated-static-lookup-in-full-map))))

(defthm generated-static-view-step-in-full-map
  (implies (and (generated-distinct-object-addresses-p objects)
                (proof-view-step kind input count depth base (proof-static-objects objects)
                                 packages machine))
           (equal (proof-view-step kind input count depth base objects packages machine)
                  (proof-view-step kind input count depth base (proof-static-objects objects)
                                   packages machine)))
  :hints (("Goal"
           :induct (proof-view-step kind input count depth base (proof-static-objects objects)
                                    packages machine)
           :in-theory (enable proof-view-step proof-cons-value proof-complex-value
                              proof-rational-value proof-symbol-value)))
  :rule-classes nil)

(defthm generated-static-view-in-full-map
  (implies (and (generated-distinct-object-addresses-p objects)
                (proof-view word base (proof-static-objects objects) packages machine))
           (equal (proof-view word base objects packages machine)
                  (proof-view word base (proof-static-objects objects) packages machine)))
  :hints (("Goal" :use ((:instance generated-static-view-step-in-full-map (kind :word)
                                   (input word) (count 0)
                                   (depth (+ 1 (nfix (proof-object-rank
                                                      (assoc-equal (proof-pointer-address word base)
                                                                   (proof-static-objects objects)))))))
                           (:instance generated-valid-word-view-at-full-depth
                                      (depth (+ 1 (nfix (proof-object-rank
                                                         (assoc-equal (proof-pointer-address word base)
                                                                      (proof-static-objects objects))))))))
                  :expand ((proof-view word base (proof-static-objects objects) packages machine))))
  :rule-classes nil)

(defthm generated-static-booleans-in-published-heap
  (implies (proof-heap-p world objects packages)
           (and (proof-machine-value-p *proof-nil* nil world objects packages)
                (proof-machine-value-p *proof-t* t world objects packages)))
  :hints (("Goal"
           :use ((:instance generated-published-object-addresses-are-distinct (pending objects)
                            (symbols nil) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance generated-static-view-in-full-map (word *proof-nil*)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance generated-static-view-in-full-map (word *proof-t*)
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (enable proof-heap-p proof-static-p proof-machine-value-p proof-value-p)))
  :rule-classes nil)

(defthm generated-lookup-record-is-published
  (let ((record (assoc-equal address objects)))
    (implies record
             (and (member-equal record objects)
                  (equal (proof-object-address record) address))))
  :hints (("Goal" :induct (assoc-equal address objects))))

(local
 (defthm generated-symbol-lookup-needs-header
   (let ((record (assoc-equal (proof-pointer-address word base) objects)))
     (implies (and (symbolp value)
                   (equal (proof-view-step :word word 0 depth base objects packages machine)
                          (proof-value-view value)))
              (and (unsigned-byte-p 64 word) (equal (proof-word-tag word) 2)
                   record (proof-symbol-object-p record machine))))
   :hints (("Goal"
            :use (:instance generated-lookup-record-is-published
                            (address (proof-pointer-address word base)))
            :expand (proof-view-step :word word 0 depth base objects packages machine)
            :in-theory (enable proof-symbol-object-p proof-cons-value proof-integer-view
                               proof-complex-value proof-rational-value)))
   :rule-classes nil))

(local
 (defthm generated-offset-after-normalizing
   (implies (and (integerp word) (integerp offset))
            (equal (+ (- offset) (boymoo-model::a64-unsigned 64 (+ offset word)))
                   (+ word (- (* (expt 2 64) (floor (+ offset word) (expt 2 64)))))))
   :hints (("Goal" :use (:instance generated-unsigned-as-mod (n 64) (x (+ word offset)))
                   :in-theory (enable mod)))))

(local
 (defthm generated-offset-round-trip
   (implies (and (unsigned-byte-p 64 word) (integerp offset))
            (equal (boymoo-model::a64-unsigned
                    64 (- (boymoo-model::a64-unsigned 64 (+ word offset)) offset))
                   word))
   :hints (("Goal"
            :use (generated-offset-after-normalizing
                  (:instance generated-unsigned-add-multiple (n 64) (x word)
                             (q (- (floor (+ offset word) (expt 2 64))))))
            :in-theory (disable generated-unsigned-add-multiple)))))

(local
 (defthm generated-symbol-word-is-object-word
   (let ((record (assoc-equal (proof-pointer-address word base) objects)))
     (implies (and (integerp base) (unsigned-byte-p 64 word) (equal (proof-word-tag word) 2)
                   (proof-symbol-object-p record machine) record)
              (equal (proof-object-word record base) word)))
   :hints (("Goal"
            :use (:instance generated-offset-round-trip (offset (- base 2)))
            :in-theory (enable proof-pointer-address proof-object-word proof-symbol-object-p)))))

(local
 (defthm generated-represented-symbol-is-published
   (let ((record (assoc-equal (proof-pointer-address word base) objects)))
     (implies (and (integerp base) (symbolp value)
                   (proof-value-p word value base objects packages machine))
              (and (member-equal record objects)
                   (proof-symbol-object-p record machine)
                   (equal (proof-object-word record base) word)
                   (equal (proof-object-view record base objects packages machine)
                          (proof-value-view value)))))
   :hints (("Goal"
            :use (:instance generated-symbol-lookup-needs-header
                            (depth (1+ (nfix (proof-object-rank
                                               (assoc-equal (proof-pointer-address word base)
                                                            objects))))))
            :expand (proof-view word base objects packages machine)
            :in-theory (enable proof-value-p proof-object-view)))
   :rule-classes nil))

(local
 (defthm generated-published-symbol-is-fresh-in-prefix
   (implies (and (proof-object-map-p pending objects seen base packages machine)
                 (member-equal record pending) (proof-symbol-object-p record machine))
            (not (member-eq (proof-view-value (proof-object-view record base objects packages machine))
                            seen)))
   :hints (("Goal" :induct (proof-object-map-p pending objects seen base packages machine)
                   :in-theory (enable proof-object-map-p)))
   :rule-classes nil))

(local
 (defthm generated-published-symbol-record-is-unique
   (implies (and (proof-object-map-p pending objects seen base packages machine)
                 (member-equal first pending) (member-equal second pending)
                 (proof-symbol-object-p first machine) (proof-symbol-object-p second machine)
                 (equal (proof-object-view first base objects packages machine)
                        (proof-object-view second base objects packages machine)))
            (equal first second))
   :hints (("Goal" :induct (proof-object-map-p pending objects seen base packages machine)
                   :in-theory (enable proof-object-map-p))
           ("Subgoal *1/2"
            :use ((:instance generated-published-symbol-is-fresh-in-prefix
                             (pending (cdr pending)) (record first)
                             (seen (cons (proof-view-value
                                          (proof-object-view (car pending) base objects packages machine))
                                         seen)))
                  (:instance generated-published-symbol-is-fresh-in-prefix
                             (pending (cdr pending)) (record second)
                             (seen (cons (proof-view-value
                                          (proof-object-view (car pending) base objects packages machine))
                                         seen))))))
   :rule-classes nil))

(defthm generated-published-symbol-has-unique-word
  (implies (and (integerp base) (symbolp value)
                (proof-object-map-p objects objects nil base packages machine)
                (proof-value-p first value base objects packages machine)
                (proof-value-p second value base objects packages machine))
           (equal first second))
  :hints (("Goal"
           :use ((:instance generated-represented-symbol-is-published (word first))
                 (:instance generated-represented-symbol-is-published (word second))
                 (:instance generated-published-symbol-record-is-unique
                            (pending objects) (seen nil)
                            (first (assoc-equal (proof-pointer-address first base) objects))
                            (second (assoc-equal (proof-pointer-address second base) objects))))))
  :rule-classes nil)

(defthm generated-nil-has-canonical-word-in-heap
  (implies (and (proof-heap-p world objects packages)
                (proof-machine-value-p word value world objects packages))
           (equal (equal word *proof-nil*) (equal value nil)))
  :hints (("Goal"
           :use (generated-static-booleans-in-published-heap
                 (:instance generated-published-symbol-has-unique-word
                            (value nil) (first word) (second *proof-nil*)
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (enable proof-heap-p proof-machine-value-p proof-value-p)))
  :rule-classes nil)

(local
 (defthm generated-cons-view-step-finds-spanned-record
   (let* ((address (proof-pointer-address word base))
          (record (assoc-equal address objects)))
     (implies (and (consp value) (equal (proof-word-tag word) 0)
                   (equal (proof-view-step :word word 0 depth base objects packages machine)
                          (proof-value-view value)))
              (and (unsigned-byte-p 64 word) (member-equal record objects)
                   (equal (proof-object-address record) address)
                   (eq (proof-object-kind record) :cons)
                   (proof-span-p address 16))))
   :hints (("Goal" :use (:instance generated-lookup-record-is-published
                                   (address (proof-pointer-address word base)))
                   :expand (proof-view-step :word word 0 depth base objects packages machine)))
   :rule-classes nil))

(local
 (defthm generated-static-member-is-in-static-projection
   (implies (and (member-equal record objects) (eq (proof-object-zone record) :static))
            (member-equal record (proof-static-objects objects)))
   :hints (("Goal" :induct (proof-static-objects objects)
                   :in-theory (enable proof-static-objects)))))

(local
 (defthm generated-static-record-comes-after-base
   (implies (and (member-equal record statics)
                 (proof-static-spans-p statics base bytes machine))
            (<= (+ base 32) (proof-object-address record)))
   :hints (("Goal" :induct (proof-static-spans-p statics base bytes machine)
                   :in-theory (enable proof-static-spans-p proof-subspan-p)))
   :rule-classes nil))

(local
 (defthm generated-heap-record-span-follows-zone
   (implies (and (member-equal record objects)
                 (eq (proof-object-kind record) :cons)
                 (proof-heap-object-spans-p objects external world))
            (or (eq (proof-object-zone record) :static)
                (and (eq (proof-object-zone record) :active)
                     (<= (proof-cons-floor world) (proof-object-address record)))
                (and (eq (proof-object-zone record) :external)
                     (member-equal (proof-object-address record) external))))
   :hints (("Goal" :induct (proof-heap-object-spans-p objects external world)
                   :in-theory (e/d (proof-heap-object-spans-p proof-subspan-p)
                                   (proof-cons-floor proof-active-end))))
   :rule-classes nil))

(local
 (defthm generated-listed-external-record-has-header
   (implies (member-equal address (cdr (proof-external-objects head fuel world objects)))
            (equal (proof-object-kind (assoc-equal address objects)) :header))
   :hints (("Goal" :induct (proof-external-objects head fuel world objects)
                   :in-theory (e/d (proof-external-objects)
                                   (proof-world-machine proof-align-up proof-header-size
                                    proof-header-type proof-regions-p proof-world-regions
                                    proof-heap-base proof-stack-base proof-stack-end
                                    proof-spaces-end proof-machine-limit))))
   :rule-classes nil))

(local
 (defthm generated-page-alignment-does-not-decrease
   (implies (natp address)
            (<= address (proof-align-up address *proof-runtime-page*)))
   :hints (("Goal"
            :use ((:instance generated-floor-bounds (x (* 1/65536 address)) (y 1))
                  (:instance rational-implies1 (acl2::x (* 1/65536 address)))
                  (:instance rational-implies2 (acl2::x (* 1/65536 address))))
            :in-theory (e/d (proof-align-up ceiling floor) (rational-implies2))))
   :rule-classes :linear))

(local
 (defthm generated-heap-cons-floor-comes-after-base
   (implies (proof-heap-layout-p world)
            (<= (proof-heap-base world) (proof-cons-floor world)))
   :hints (("Goal"
            :use (:instance generated-page-alignment-does-not-decrease
                            (address (+ (proof-heap-base world)
                                        (proof-static-size (proof-heap-base world)
                                                           (proof-world-machine world)))))
            :in-theory (e/d (proof-heap-layout-p)
                            (proof-heap-base proof-cons-floor proof-active-floor proof-active-end
                             proof-inactive-floor proof-inactive-end proof-spaces-end proof-box-top
                             proof-heap-limit proof-static-size proof-align-up proof-covered-p
                             proof-regions-p proof-world-regions proof-stack-base proof-stack-end))))
   :rule-classes nil))

(local
 (defthm generated-published-cons-comes-after-base
   (let ((record (assoc-equal address objects)))
     (implies (and (proof-heap-p world objects packages)
                   record (eq (proof-object-kind record) :cons))
              (<= (proof-heap-base world) address)))
   :hints (("Goal"
            :use ((:instance generated-lookup-record-is-published)
                  (:instance generated-heap-record-span-follows-zone
                             (record (assoc-equal address objects))
                             (external (cdr (proof-external-objects
                                             (proof-external-head world) (len objects) world objects))))
                  (:instance generated-listed-external-record-has-header
                             (head (proof-external-head world)) (fuel (len objects)))
                  (:instance generated-static-record-comes-after-base
                             (record (assoc-equal address objects))
                             (statics (proof-static-objects objects)) (base (proof-heap-base world))
                             (bytes (proof-static-size (proof-heap-base world) (proof-world-machine world)))
                             (machine (proof-world-machine world)))
                  generated-heap-cons-floor-comes-after-base)
            :in-theory (e/d (proof-static-p proof-heap-p)
                            (proof-object-kind proof-object-address proof-object-zone
                             proof-word-tag proof-external-objects proof-external-head
                             proof-heap-object-spans-p proof-static-spans-p proof-static-size
                             proof-heap-base proof-world-machine))))
   :rule-classes nil))

(local
 (defthm generated-address-at-or-above-base-does-not-wrap
   (implies (and (unsigned-byte-p 64 base) (unsigned-byte-p 64 word)
                 (<= base (boymoo-model::a64-unsigned 64 (+ base word))))
            (and (< (+ base word) (expt 2 64))
                 (equal (boymoo-model::a64-unsigned 64 (+ base word)) (+ base word))))
   :hints (("Goal" :cases ((< (+ base word) (expt 2 64)))
                   :use (:instance generated-unsigned-of-remainder (n 64) (x (+ base word))
                                   (q 1) (r (- (+ base word) (expt 2 64))))))
   :rule-classes nil))

(defthm generated-published-cons-field-addresses-fit
  (let* ((base (proof-heap-base world))
         (address (proof-pointer-address word base)))
    (implies (and (proof-heap-p world objects packages)
                  (consp value) (proof-machine-value-p word value world objects packages))
             (and (equal address (+ base word))
                  (proof-span-p (+ base word) 16)
                  (< (+ base word 8) (expt 2 64)))))
  :hints (("Goal"
           :use ((:instance generated-cons-tag-in-value-view (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance generated-cons-view-step-finds-spanned-record
                            (base (proof-heap-base world)) (machine (proof-world-machine world))
                            (depth (1+ (nfix (proof-object-rank
                                               (assoc-equal (proof-pointer-address word (proof-heap-base world))
                                                            objects))))))
                 (:instance generated-published-cons-comes-after-base
                            (address (proof-pointer-address word (proof-heap-base world))))
                 (:instance generated-address-at-or-above-base-does-not-wrap
                            (base (proof-heap-base world))))
           :in-theory (e/d (proof-machine-value-p proof-value-p proof-view proof-pointer-address
                           proof-heap-base proof-span-p)
                          (generated-cons-tag-in-value-view))))
  :rule-classes nil)
