(in-package "BOYMOO-PROOFS")

(include-book "heap-bounds")
(include-book "length")

(logic)
(set-verify-guards-eagerness 0)

(defun sequence-object-addresses (objects)
  (if (atom objects)
      nil
    (cons (proof-object-address (car objects))
          (sequence-object-addresses (cdr objects)))))

(local
 (defthm sequence-object-has-positive-size
   (< 0 (proof-object-size object machine))
   :hints (("Goal"
            :in-theory (disable proof-align-up)
            :use ((:instance sequence-floor-of-unsigned
                             (dropped 8) (kept 56)
                             (value (proof-load-word (proof-object-address object) machine)))
                  (:instance sequence-align-up-covers-address
                             (address (proof-header-size
                                       (proof-load-word (proof-object-address object) machine)))
                             (alignment 8)))))
   :rule-classes :linear))

(local
 (defthm sequence-disjoint-address-not-in-map
   (implies (and (< address end)
                 (proof-object-disjoint-p address end objects machine))
            (not (member-equal address (sequence-object-addresses objects))))
   :hints (("Goal" :induct (proof-object-disjoint-p address end objects machine)
                   :in-theory (disable proof-object-size)))
   :rule-classes ((:forward-chaining
                   :trigger-terms ((proof-object-disjoint-p address end objects machine))))))

(defthm sequence-distinct-published-addresses
  (implies (proof-object-map-p pending objects symbols base packages machine)
           (no-duplicatesp-equal (sequence-object-addresses pending)))
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
                  :in-theory (disable proof-object-disjoint-p proof-object-size
                                      proof-object-record-p proof-object-view
                                      proof-symbol-object-p))
          ("Subgoal *1/2"
           :use ((:instance sequence-object-has-positive-size (object (car pending)))
                 (:instance sequence-disjoint-address-not-in-map
                            (address (proof-object-address (car pending)))
                            (end (+ (proof-object-address (car pending))
                                    (proof-object-size (car pending) machine)))
                            (objects (cdr pending)))))))

(local
 (defthm sequence-member-address-in-map
   (implies (member-equal object objects)
            (member-equal (proof-object-address object)
                          (sequence-object-addresses objects)))
   :hints (("Goal" :induct (sequence-object-addresses objects)))))

(local
 (defthm sequence-unique-address-selects-member
   (implies (and (no-duplicatesp-equal (sequence-object-addresses objects))
                 (member-equal object objects)
                 (consp object))
            (equal (assoc-equal (proof-object-address object) objects) object))
   :hints (("Goal" :induct (sequence-object-addresses objects))
           ("Subgoal *1/2" :use ((:instance sequence-member-address-in-map
                                            (objects (cdr objects))))))
   :rule-classes nil))

(local
 (defthm sequence-external-address-selects-header
   (implies (member-equal address (cdr (proof-external-objects head fuel world objects)))
            (eq (proof-object-kind (assoc-equal address objects)) :header))
   :hints (("Goal" :induct (proof-external-objects head fuel world objects)
                   :in-theory (disable proof-load-word proof-header-size proof-header-type
                                       proof-align-up proof-disjoint-p)))
   :rule-classes nil))

(local
 (defthm sequence-cons-object-span-of-member
   (implies
    (and (eq (proof-object-kind object) :cons)
         (member-equal object objects)
         (proof-heap-object-spans-p objects external world))
    (case (proof-object-zone object)
      (:static t)
      (:active (proof-subspan-p (proof-object-address object) 16
                                (proof-cons-floor world) (proof-active-end world)))
      (:external (member-equal (proof-object-address object) external))
      (otherwise nil)))
   :hints (("Goal" :induct (proof-heap-object-spans-p objects external world)
                   :in-theory (disable proof-subspan-p proof-cons-floor proof-active-end)))
   :rule-classes nil))

(local
 (defthm sequence-member-is-object-record
   (implies (and (proof-object-map-p pending objects symbols base packages machine)
                 (member-equal object pending))
            (proof-object-record-p object))
   :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
                   :in-theory (disable proof-object-record-p proof-object-size
                                       proof-object-view proof-symbol-object-p
                                       proof-object-disjoint-p proof-span-p)))
   :rule-classes nil))

(local
 (defthm sequence-layout-bounds-active-cells
   (let* ((base (proof-heap-base world))
          (size (proof-static-size base (proof-world-machine world))))
     (implies (and (proof-heap-layout-p world) (< size *proof-space-size*))
              (and (<= base (proof-cons-floor world))
                   (<= (proof-active-end world) (+ base (expt 2 34))))))
   :hints (("Goal"
            :in-theory (disable proof-align-up proof-load-word proof-covered-p
                                proof-spaces-end proof-disjoint-p proof-regions-p)
            :use ((:instance sequence-align-up-covers-address
                             (address (+ (proof-heap-base world)
                                         (proof-static-size (proof-heap-base world)
                                                            (proof-world-machine world))))
                             (alignment *proof-runtime-page*))
                  (:instance sequence-align-up-upper-bound
                             (address (+ (proof-heap-base world)
                                         (proof-static-size (proof-heap-base world)
                                                            (proof-world-machine world))))
                             (alignment *proof-runtime-page*)))))
   :rule-classes nil))

(defthm sequence-published-cons-address-bounds
  (let ((base (proof-heap-base world))
        (address (proof-object-address object)))
    (implies (and (proof-heap-p world objects packages) (member-equal object objects)
                  (eq (proof-object-kind object) :cons))
             (and (natp address)
                  (equal (mod address 8) 0)
                  (<= base address)
                  (< address (+ base (expt 2 34))))))
  :hints
  (("Goal"
    :in-theory (disable proof-heap-layout-p proof-external-objects proof-heap-object-spans-p
                        proof-static-spans-p proof-object-map-p proof-load-word proof-view
                        proof-string-accounting-p proof-stack-prefix proof-static-buckets-p
                        proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p
                        proof-package-bindings-p proof-home-bindings-p proof-value-p
                        proof-cons-floor proof-active-end proof-heap-base proof-world-machine)
    :use
    (sequence-layout-bounds-active-cells
     (:instance sequence-unique-address-selects-member)
     (:instance sequence-distinct-published-addresses
                (pending objects) (symbols nil)
                (base (proof-heap-base world)) (machine (proof-world-machine world)))
     (:instance sequence-member-is-object-record
                (pending objects) (symbols nil)
                (base (proof-heap-base world)) (machine (proof-world-machine world)))
     (:instance sequence-cons-object-span-of-member
                (external (cdr (proof-external-objects (proof-external-head world)
                                                      (len objects) world objects))))
     (:instance sequence-external-address-selects-header
                (address (proof-object-address object))
                (head (proof-external-head world)) (fuel (len objects)))
     (:instance sequence-static-span-of-member
                (statics (proof-static-objects objects)) (base (proof-heap-base world))
                (size (proof-static-size (proof-heap-base world) (proof-world-machine world)))
                (machine (proof-world-machine world))))))
  :rule-classes nil)

(local
 (defthm sequence-cons-offsets-in-heap-subset
   (implies (and (proof-heap-p world objects packages)
                 (subsetp-equal pending objects))
            (sequence-cons-offsets-ordinary-p pending (proof-heap-base world)))
   :hints (("Goal" :induct (sequence-object-addresses pending)
                   :in-theory (disable proof-heap-p proof-heap-base))
           ("Subgoal *1/2" :use ((:instance sequence-published-cons-address-bounds
                                            (object (car pending))))))
   :rule-classes nil))

(local
 (defthm sequence-subset-of-extended-list
   (implies (subsetp-equal pending objects)
            (subsetp-equal pending (cons object objects)))
   :hints (("Goal" :induct (subsetp-equal pending objects)))))

(local
 (defthm sequence-subset-reflexive
   (subsetp-equal objects objects)
   :hints (("Goal" :induct (sequence-object-addresses objects)))))

(defthm sequence-ordinary-cons-offsets-of-heap
  (implies (proof-heap-p world objects packages)
           (sequence-cons-offsets-ordinary-p objects (proof-heap-base world)))
  :hints (("Goal" :in-theory (disable proof-heap-p proof-heap-base)
                  :use ((:instance sequence-cons-offsets-in-heap-subset (pending objects))))))

(local
 (defun sequence-keys-below-p (keys limit)
   (if (endp keys)
       t
     (and (natp (car keys))
          (< (car keys) limit)
          (sequence-keys-below-p (cdr keys) limit)))))

(local
 (defun sequence-key-without-gap (key gap)
   (if (< key gap) key (1- key))))

(local
 (defun sequence-close-key-gap (keys gap)
   (if (endp keys)
       nil
     (cons (sequence-key-without-gap (car keys) gap)
           (sequence-close-key-gap (cdr keys) gap)))))

(local
 (defthm sequence-closing-gap-preserves-length
   (equal (len (sequence-close-key-gap keys gap)) (len keys))))

(local
 (defthm sequence-keys-distinct-after-gap
   (implies (and (natp left) (natp right) (natp gap)
                 (not (equal left gap)) (not (equal right gap)))
            (equal (equal (sequence-key-without-gap left gap)
                          (sequence-key-without-gap right gap))
                   (equal left right)))))

(local
 (defthm sequence-membership-after-key-gap
   (implies (and (natp key) (natp gap) (not (equal key gap))
                 (not (member-equal gap keys)) (sequence-keys-below-p keys limit))
            (iff (member-equal (sequence-key-without-gap key gap)
                               (sequence-close-key-gap keys gap))
                 (member-equal key keys)))
   :hints (("Goal" :induct (sequence-close-key-gap keys gap)
                   :in-theory (disable sequence-key-without-gap)
                   :expand ((sequence-keys-below-p keys limit))))))

(local
 (defthm sequence-closing-gap-preserves-distinctness
   (implies (and (natp gap)
                 (no-duplicatesp-equal keys) (not (member-equal gap keys))
                 (sequence-keys-below-p keys limit))
            (no-duplicatesp-equal (sequence-close-key-gap keys gap)))
   :hints (("Goal" :induct (sequence-close-key-gap keys gap)
                   :in-theory (disable sequence-key-without-gap
                                       sequence-membership-after-key-gap))
           ("Subgoal *1/2"
            :use ((:instance sequence-membership-after-key-gap
                             (key (car keys)) (keys (cdr keys))))))))

(local
 (defthm sequence-keys-in-smaller-range-after-gap
   (implies (and (natp gap) (integerp limit) (< gap limit)
                 (not (member-equal gap keys)) (sequence-keys-below-p keys limit))
            (sequence-keys-below-p (sequence-close-key-gap keys gap) (1- limit)))
   :hints (("Goal" :induct (sequence-close-key-gap keys gap)))))

(local
 (defun sequence-bounded-keys-induction (keys limit)
   (declare (xargs :measure (nfix limit)))
   (if (or (zp limit) (endp keys))
       nil
     (sequence-bounded-keys-induction
      (sequence-close-key-gap (cdr keys) (car keys)) (1- limit)))))

(local
 (defthm sequence-distinct-keys-count-bounded
   (implies (and (natp limit) (sequence-keys-below-p keys limit)
                 (no-duplicatesp-equal keys))
            (<= (len keys) limit))
   :hints (("Goal" :induct (sequence-bounded-keys-induction keys limit)
                   :in-theory (disable sequence-close-key-gap
                                       sequence-closing-gap-preserves-distinctness))
           ("Subgoal *1/1"
            :expand ((sequence-keys-below-p keys limit)))
           ("Subgoal *1/2"
            :use ((:instance sequence-closing-gap-preserves-distinctness
                             (keys (cdr keys)) (gap (car keys))))))))

(local
 (defun sequence-cons-key (address base)
   (and (natp address) (* 1/8 (- address base)))))

(local
 (defun sequence-cons-keys (objects base)
   (if (atom objects)
       nil
     (let* ((object (car objects))
            (rest (sequence-cons-keys (cdr objects) base)))
       (if (eq (proof-object-kind object) :cons)
           (cons (sequence-cons-key (proof-object-address object) base) rest)
         rest)))))

(local
 (defthm sequence-key-membership-implies-address-membership
   (implies (and (natp address)
                 (member-equal (sequence-cons-key address base) (sequence-cons-keys objects base)))
            (member-equal address (sequence-object-addresses objects)))
   :hints (("Goal" :induct (sequence-cons-keys objects base)))))

(local
 (defthm sequence-cons-keys-are-distinct
   (implies (and (no-duplicatesp-equal (sequence-object-addresses objects))
                 (sequence-keys-below-p (sequence-cons-keys objects base) limit))
            (no-duplicatesp-equal (sequence-cons-keys objects base)))
   :hints (("Goal" :induct (sequence-cons-keys objects base)
                   :in-theory (disable sequence-key-membership-implies-address-membership))
           ("Subgoal *1/2"
            :use ((:instance sequence-key-membership-implies-address-membership
                             (address (proof-object-address (car objects)))
                             (objects (cdr objects))))))))

(local
 (defthm sequence-scaled-remainder-eight
   (implies (integerp value)
            (equal (* 1/8 (mod value 8))
                   (- (* 1/8 value) (floor value 8))))
   :hints (("Goal"
            :in-theory (e/d (mod) (distributivity))
            :use ((:instance distributivity
                             (acl2::x 1/8) (acl2::y (* 8 (floor value 8)))
                             (acl2::z (- (* 8 (floor value 8)))))
                  (:instance distributivity
                             (acl2::x 1/8) (acl2::y value)
                             (acl2::z (- (* 8 (floor value 8))))))))
   :rule-classes nil))

(local
 (defthm sequence-aligned-key-is-integral
   (implies (and (natp address) (natp base)
                 (equal (mod address 8) 0) (equal (mod base 8) 0))
            (equal (sequence-cons-key address base)
                   (- (floor address 8) (floor base 8))))
   :hints (("Goal" :use ((:instance sequence-scaled-remainder-eight (value address))
                        (:instance sequence-scaled-remainder-eight (value base))
                        (:instance distributivity
                                   (acl2::x 1/8) (acl2::y base) (acl2::z (- base))))))))

(local
 (defthm sequence-heap-base-is-aligned
   (implies (proof-heap-p world objects packages)
            (equal (mod (proof-heap-base world) 8) 0))
   :hints (("Goal"
            :in-theory (disable proof-align-up proof-covered-p proof-load-word proof-world-reg
                                proof-object-map-p proof-external-objects
                                proof-heap-object-spans-p proof-stack-prefix
                                proof-static-p proof-string-accounting-p proof-dynamic-view
                                proof-dynamic-entries proof-dynamic-symbol-objects-p)))
   :rule-classes nil))

(local
 (defthm sequence-heap-base-natural
   (natp (proof-heap-base world))
   :rule-classes :type-prescription))

(local
 (defthm sequence-heap-base-bits
   (unsigned-byte-p 64 (proof-heap-base world))))

(local
 (defthm sequence-key-in-range-of-aligned-address
   (implies (and (natp address) (natp base)
                 (equal (mod address 8) 0) (equal (mod base 8) 0)
                 (<= base address) (< address (+ base (expt 2 34))))
            (and (natp (sequence-cons-key address base))
                 (< (sequence-cons-key address base) (expt 2 31))))
   :hints (("Goal" :in-theory (disable sequence-aligned-key-is-integral)
                   :use (sequence-aligned-key-is-integral
                         (:instance distributivity
                                    (acl2::x 1/8) (acl2::y base) (acl2::z (- base))))))
   :rule-classes nil))

(local
 (defthm sequence-heap-keys-below-capacity
   (implies (and (proof-heap-p world objects packages)
                 (subsetp-equal pending objects))
            (sequence-keys-below-p (sequence-cons-keys pending (proof-heap-base world))
                                   (expt 2 31)))
   :hints (("Goal" :induct (sequence-cons-keys pending (proof-heap-base world))
                   :in-theory (disable proof-heap-p proof-heap-base
                                       sequence-cons-key))
           ("Subgoal *1/2"
            :use (sequence-heap-base-is-aligned
                  (:instance sequence-published-cons-address-bounds (object (car pending)))
                  (:instance sequence-key-in-range-of-aligned-address
                             (address (proof-object-address (car pending)))
                             (base (proof-heap-base world))))))
   :rule-classes nil))

(local
 (defthm sequence-published-cons-count-bounded
   (implies (proof-heap-p world objects packages)
            (<= (len (sequence-cons-keys objects (proof-heap-base world))) (expt 2 31)))
   :hints (("Goal"
            :in-theory (disable proof-heap-base proof-static-p proof-heap-layout-p
                                proof-external-objects proof-heap-object-spans-p
                                proof-object-map-p proof-string-accounting-p proof-stack-prefix
                                proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p)
            :use
            ((:instance sequence-distinct-keys-count-bounded
                        (keys (sequence-cons-keys objects (proof-heap-base world)))
                        (limit (expt 2 31)))
             (:instance sequence-cons-keys-are-distinct
                        (base (proof-heap-base world)) (limit (expt 2 31)))
             (:instance sequence-distinct-published-addresses
                        (pending objects) (symbols nil)
                        (base (proof-heap-base world)) (machine (proof-world-machine world)))
             (:instance sequence-heap-keys-below-capacity (pending objects)))))
   :rule-classes nil))

(local
 (defun sequence-cons-count-below-rank (objects depth)
   (if (atom objects)
       0
     (+ (if (and (eq (proof-object-kind (car objects)) :cons)
                 (< (proof-object-rank (car objects)) depth))
            1 0)
        (sequence-cons-count-below-rank (cdr objects) depth)))))

(local
 (defthm sequence-cons-count-bounded-by-keys
   (<= (sequence-cons-count-below-rank objects depth)
       (len (sequence-cons-keys objects base)))
   :hints (("Goal" :induct (sequence-cons-keys objects base)))
   :rule-classes nil))

(local
 (defthm sequence-cons-count-monotone-in-rank
   (implies (<= lesser greater)
            (<= (sequence-cons-count-below-rank objects lesser)
                (sequence-cons-count-below-rank objects greater)))
   :hints (("Goal" :induct (sequence-object-addresses objects)))
   :rule-classes nil))

(local
 (defthm sequence-selected-cons-makes-rank-count-decrease
   (implies (and (member-equal object objects)
                 (eq (proof-object-kind object) :cons)
                 (< (proof-object-rank object) depth))
            (< (sequence-cons-count-below-rank objects (proof-object-rank object))
               (sequence-cons-count-below-rank objects depth)))
   :hints (("Goal" :induct (sequence-object-addresses objects))
           ("Subgoal *1/2"
            :use ((:instance sequence-cons-count-monotone-in-rank
                             (objects (cdr objects)) (lesser (proof-object-rank object))
                             (greater depth)))))
   :rule-classes nil))

(local
 (defun sequence-spine-rank-induction (datum word depth base objects machine)
   (if (atom datum)
       depth
     (let* ((address (proof-pointer-address word base))
            (rank (proof-object-rank (assoc-equal address objects))))
       (sequence-spine-rank-induction (cdr datum) (proof-load-word (+ address 8) machine)
                                    rank base objects machine)))))

(local
 (defthm sequence-selected-cons-is-member
   (implies (eq (proof-object-kind (assoc-equal address objects)) :cons)
            (member-equal (assoc-equal address objects) objects))
   :hints (("Goal" :induct (assoc-equal address objects)))))

(local
 (defthm sequence-nonodd-word-for-cons
   (implies (and (consp datum)
                 (equal (proof-view-step :word word 0 depth base objects packages machine)
                        (proof-value-view datum)))
            (not (oddp word)))
   :hints (("Goal"
            :in-theory (disable proof-view-step sequence-signed-word)
            :expand ((proof-view-step :word word 0 depth base objects packages machine))))))

(local
 (defthm sequence-cons-spine-count-bounded-by-rank-count
   (implies (equal (proof-view-step :word word 0 depth base objects packages machine)
                   (proof-value-view datum))
            (<= (len datum) (sequence-cons-count-below-rank objects depth)))
   :hints (("Goal" :induct (sequence-spine-rank-induction datum word depth base objects machine)
                   :in-theory (disable proof-view-step proof-pointer-address proof-load-word
                                       proof-object-rank proof-object-kind))
           ("Subgoal *1/2"
            :use (sequence-nonodd-word-for-cons
                  sequence-cons-view-of-represented-value
                  sequence-cons-fields-of-represented-value
                  (:instance sequence-selected-cons-makes-rank-count-decrease
                             (object (assoc-equal (proof-pointer-address word base) objects))))))
   :rule-classes nil))

(defthm sequence-represented-cons-spine-length-bounded
  (let ((base (proof-heap-base world))
        (machine (proof-world-machine world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-value-p word datum base objects packages machine))
             (<= (len datum) (expt 2 31))))
  :hints
  (("Goal"
    :in-theory (disable proof-heap-p proof-view-step proof-heap-base proof-world-machine
                        proof-pointer-address proof-object-rank)
    :use
    (sequence-published-cons-count-bounded
     (:instance sequence-cons-spine-count-bounded-by-rank-count
                (base (proof-heap-base world)) (machine (proof-world-machine world))
                (depth (1+ (nfix (proof-object-rank
                                  (assoc-equal (proof-pointer-address word (proof-heap-base world))
                                               objects))))))
     (:instance sequence-cons-count-bounded-by-keys
                (base (proof-heap-base world))
                (depth (1+ (nfix (proof-object-rank
                                  (assoc-equal (proof-pointer-address word (proof-heap-base world))
                                               objects)))))))))
  :rule-classes nil)

(defthm sequence-represented-sequence-length-bounded
  (implies (and (proof-heap-p world objects packages)
                (proof-machine-value-p word datum world objects packages))
           (< (len (sequence-elements datum)) *proof-space-size*))
  :hints (("Goal"
           :in-theory (disable proof-heap-p proof-value-p proof-heap-base proof-world-machine
                               proof-load-string)
           :use (sequence-represented-string-length-bounded
                 sequence-represented-cons-spine-length-bounded)))
  :rule-classes nil)

(defthm sequence-cons-spine-of-represented-datum
  (let ((base (proof-heap-base world))
        (machine (proof-world-machine world)))
    (implies (and (proof-heap-p world objects packages)
                  (proof-machine-value-p word datum world objects packages))
             (sequence-cons-spine-p datum word base machine)))
  :hints
  (("Goal"
    :in-theory (disable proof-heap-p proof-heap-base proof-world-machine proof-view-step
                        proof-pointer-address proof-object-rank sequence-cons-spine-p
                        sequence-ordinary-cons-offsets-of-heap)
    :use
    (sequence-ordinary-cons-offsets-of-heap
     (:instance sequence-cons-spine-from-value-view
                (base (proof-heap-base world)) (machine (proof-world-machine world))
                (depth (1+ (nfix (proof-object-rank
                                  (assoc-equal (proof-pointer-address word (proof-heap-base world))
                                               objects)))))))))
  :rule-classes nil)

(defthm sequence-list-length-for-represented-datum
  (let* ((path (sequence-list-length-path datum))
         (cuts (list (proof-world-reg 30 before)))
         (after (sequence-execute path before)))
    (implies
     (and (proof-heap-p before objects packages)
          (proof-reg-value-p 0 datum before objects packages)
          (not (proof-world-stop before))
          (consp (boymoo-model::a64-registers (proof-world-machine before)))
          (unsigned-byte-p 64 (+ 32 (proof-world-pc before)))
          (sequence-instruction-path path cuts before))
     (and (proof-segment-p (len path) cuts before :cut after)
          (proof-frame-return-p '(2 3) t before after)
          (equal (proof-world-reg 2 after) (len datum))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (boymoo-model::a64-memory (proof-world-machine before)))
          (equal (proof-world-regions after) (proof-world-regions before)))))
  :hints
  (("Goal"
    :in-theory (disable proof-heap-p proof-frame-return-p proof-segment-p
                        proof-world-machine proof-world-reg proof-world-pc proof-heap-base
                        proof-value-p sequence-list-length-path sequence-cons-spine-p)
    :use
    (sequence-list-length-contract
     (:instance sequence-cons-spine-of-represented-datum
                (word (proof-world-reg 0 before)) (world before))
     (:instance sequence-represented-cons-spine-length-bounded
                (word (proof-world-reg 0 before)) (world before)))))
  :rule-classes nil)
