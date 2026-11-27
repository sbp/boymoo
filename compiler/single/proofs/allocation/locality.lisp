(in-package "BOYMOO-PROOFS")

(include-book "memory")
(include-book "alignment")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-read-after-disjoint-write
  (implies (and (proof-span-p start bytes)
                (proof-span-p address count)
                (proof-disjoint-p start (+ start bytes) address (+ address count)))
           (equal (boymoo-model::a64-load count address
                                         (boymoo-model::a64-store bytes start value machine))
                  (boymoo-model::a64-load count address machine)))
  :hints (("Goal" :in-theory (disable proof-span-p proof-disjoint-p))))

(defthm allocation-load-word-after-disjoint-write
  (implies (and (proof-span-p start bytes)
                (proof-span-p address 8)
                (proof-disjoint-p start (+ start bytes) address (+ address 8)))
           (equal (proof-load-word address (boymoo-model::a64-store bytes start value machine))
                  (proof-load-word address machine)))
  :hints (("Goal" :use ((:instance allocation-read-after-disjoint-write (count 8)))
           :in-theory (e/d (proof-load-word)
                           (allocation-read-after-disjoint-write proof-span-p proof-disjoint-p)))))

(defthm allocation-byte-list-after-disjoint-write
  (implies (and (proof-span-p start bytes)
                (proof-span-p address count)
                (proof-disjoint-p start (+ start bytes) address (+ address count)))
           (equal (proof-byte-list count address (boymoo-model::a64-store bytes start value machine))
                  (proof-byte-list count address machine)))
  :hints (("Goal" :induct (proof-byte-list count address machine)
           :expand ((proof-byte-list count address (boymoo-model::a64-store bytes start value machine)))
           :in-theory (disable boymoo-model::a64-load boymoo-model::a64-store))))

(defthm allocation-string-after-disjoint-write
  (implies (and (proof-span-p start bytes)
                (proof-span-p address count)
                (proof-disjoint-p start (+ start bytes) address (+ address count)))
           (equal (proof-load-string count address (boymoo-model::a64-store bytes start value machine))
                  (proof-load-string count address machine)))
  :hints (("Goal" :in-theory (disable proof-byte-list proof-byte-characters
                                     boymoo-model::a64-store proof-span-p proof-disjoint-p))))

(defthm allocation-limb-magnitude-after-disjoint-write
  (implies (and (proof-span-p start bytes)
                (proof-span-p address (* 8 count))
                (proof-disjoint-p start (+ start bytes) address (+ address (* 8 count)))
                (natp count))
           (equal (proof-limb-magnitude count address (boymoo-model::a64-store bytes start value machine))
                  (proof-limb-magnitude count address machine)))
  :hints (("Goal" :induct (proof-limb-magnitude count address machine)
           :expand ((proof-limb-magnitude count address (boymoo-model::a64-store bytes start value machine)))
           :in-theory (disable boymoo-model::a64-store))))

(defthm allocation-limbs-after-disjoint-write
  (implies (and (proof-span-p start bytes)
                (proof-span-p address (* 8 count))
                (proof-disjoint-p start (+ start bytes) address (+ address (* 8 count)))
                (natp count))
           (equal (proof-limbs-p count address (boymoo-model::a64-store bytes start value machine))
                  (proof-limbs-p count address machine)))
  :hints (("Goal" :induct (proof-limbs-p count address machine)
           :expand ((proof-limbs-p count address (boymoo-model::a64-store bytes start value machine)))
           :in-theory (disable boymoo-model::a64-store))))

; A record has an ordinary byte span disjoint from the whole write.
(defun allocation-objects-outside-write-p (start end objects machine)
  (if (atom objects)
      t
    (let* ((object (car objects))
           (address (proof-object-address object))
           (size (proof-object-size object machine)))
      (and (proof-span-p address size)
           (proof-disjoint-p start end address (+ address size))
           (allocation-objects-outside-write-p start end (cdr objects) machine)))))

(defthm allocation-lookup-object-outside-write
  (let* ((object (assoc-equal address objects))
         (size (proof-object-size object machine)))
    (implies (and (allocation-objects-outside-write-p start end objects machine) object)
             (and (proof-span-p address size)
                  (proof-disjoint-p start end address (+ address size)))))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-objects-outside-write-p start end objects machine)
           :in-theory (disable proof-object-size proof-span-p proof-disjoint-p))))

(defthm allocation-object-map-with-disjoint-spans
  (implies (and (proof-object-map-p pending objects symbols base packages machine)
                (proof-object-disjoint-p start end pending machine))
           (allocation-objects-outside-write-p start end pending machine))
  :rule-classes nil
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
           :in-theory (disable proof-object-view proof-object-record-p proof-symbol-object-p
                               proof-object-size proof-span-p proof-disjoint-p))))

(defthm allocation-object-size-covers-payload
  (let* ((address (proof-object-address object))
         (payload (proof-header-size (proof-load-word address machine))))
    (implies (not (eq (proof-object-kind object) :cons))
             (and (natp payload) (<= (+ 8 payload) (proof-object-size object machine)))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-align-up-bounds
                         (size (proof-header-size (proof-load-word (proof-object-address object) machine)))
                         (alignment 8)))
           :in-theory (disable proof-align-up proof-load-word proof-header-size))))

(defthm allocation-object-header-after-disjoint-write
  (let ((address (proof-object-address object))
        (size (proof-object-size object machine)))
    (implies (and (proof-span-p start bytes)
                  (proof-span-p address size)
                  (proof-disjoint-p start (+ start bytes) address (+ address size)))
             (equal (proof-load-word address (boymoo-model::a64-store bytes start value machine))
                    (proof-load-word address machine))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-object-size-covers-payload
                 (:instance allocation-load-word-after-disjoint-write
                  (address (proof-object-address object))))
           :in-theory (disable allocation-load-word-after-disjoint-write proof-align-up
                               proof-header-size boymoo-model::a64-store))))

(defthm allocation-object-size-after-disjoint-write
  (let ((address (proof-object-address object))
        (size (proof-object-size object machine)))
    (implies (and (proof-span-p start bytes)
                  (proof-span-p address size)
                  (proof-disjoint-p start (+ start bytes) address (+ address size)))
             (and (equal (proof-object-size object (boymoo-model::a64-store bytes start value machine))
                         size)
                  (equal (proof-symbol-object-p object (boymoo-model::a64-store bytes start value machine))
                         (proof-symbol-object-p object machine)))))
  :rule-classes nil
  :hints (("Goal" :use allocation-object-header-after-disjoint-write
           :in-theory (disable boymoo-model::a64-store proof-align-up proof-header-size
                               proof-header-type proof-span-p proof-disjoint-p))))

(local
 (defthm allocation-empty-limbs
   (implies (zp count)
            (and (proof-limbs-p count address machine)
                 (equal (proof-limb-magnitude count address machine) 0)))))

(defthm allocation-integer-view-after-disjoint-write
  (let* ((size (proof-header-size (proof-load-word address machine)))
         (total (+ 8 size)))
    (implies (and (proof-span-p start bytes)
                  (proof-span-p address total)
                  (proof-disjoint-p start (+ start bytes) address (+ address total)))
             (equal (proof-integer-view address (boymoo-model::a64-store bytes start value machine))
                    (proof-integer-view address machine))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-slot-bytes-fit (size (proof-header-size (proof-load-word address machine))))
                 (:instance allocation-limbs-after-disjoint-write
                  (address (+ 16 address)) (count (1- (ash (proof-header-size (proof-load-word address machine)) -3))))
                 (:instance allocation-limb-magnitude-after-disjoint-write
                  (address (+ 16 address)) (count (1- (ash (proof-header-size (proof-load-word address machine)) -3)))))
           :in-theory (disable boymoo-model::a64-store proof-header-size proof-header-type
                               proof-limbs-p proof-limb-magnitude mod ash
                               allocation-limbs-after-disjoint-write allocation-limb-magnitude-after-disjoint-write))))

(local
 (defthm allocation-address-of-looked-up-object
   (implies (assoc-equal address objects)
            (equal (car (assoc-equal address objects)) address))))

(defun allocation-write-disjoint-from-objects-p (start bytes objects machine)
  (and (proof-span-p start bytes)
       (allocation-objects-outside-write-p start (+ start bytes) objects machine)))

(defthm allocation-write-disjoint-from-objects-facts
  (implies (allocation-write-disjoint-from-objects-p start bytes objects machine)
           (and (proof-span-p start bytes)
                (allocation-objects-outside-write-p start (+ start bytes) objects machine)))
  :rule-classes :forward-chaining)

(defthm allocation-known-object-header-after-write
  (implies (and (allocation-write-disjoint-from-objects-p start bytes objects machine)
                (assoc-equal address objects))
           (equal (proof-load-word address (boymoo-model::a64-store bytes start value machine))
                  (proof-load-word address machine)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal"
           :use ((:instance allocation-lookup-object-outside-write (end (+ start bytes)))
                 (:instance allocation-object-header-after-disjoint-write (object (assoc-equal address objects))))
           :in-theory (disable allocation-objects-outside-write-p proof-object-size proof-span-p
                               proof-disjoint-p boymoo-model::a64-store))))

(defthm allocation-known-object-field-after-write
  (let ((object (assoc-equal address objects)))
    (implies (and (allocation-write-disjoint-from-objects-p start bytes objects machine)
                  object (natp offset) (<= (+ offset 8) (proof-object-size object machine)))
             (equal (proof-load-word (+ offset address) (boymoo-model::a64-store bytes start value machine))
                    (proof-load-word (+ offset address) machine))))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal"
           :use ((:instance allocation-lookup-object-outside-write (end (+ start bytes)))
                 (:instance allocation-load-word-after-disjoint-write (address (+ offset address))))
           :in-theory (disable allocation-objects-outside-write-p proof-object-size
                               allocation-load-word-after-disjoint-write boymoo-model::a64-store))))

(defthm allocation-known-header-payload-after-write
  (let* ((object (assoc-equal address objects))
         (size (proof-header-size (proof-load-word address machine))))
    (implies (and (allocation-write-disjoint-from-objects-p start bytes objects machine)
                  object (eq (proof-object-kind object) :header)
                  (or (posp size) (equal size 0)))
             (and (equal (proof-load-string size (+ 8 address) (boymoo-model::a64-store bytes start value machine))
                         (proof-load-string size (+ 8 address) machine))
                  (equal (proof-integer-view address (boymoo-model::a64-store bytes start value machine))
                         (proof-integer-view address machine)))))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal"
           :use ((:instance allocation-lookup-object-outside-write (end (+ start bytes)))
                 allocation-integer-view-after-disjoint-write
                 (:instance allocation-object-size-covers-payload (object (assoc-equal address objects)))
                 (:instance allocation-string-after-disjoint-write
                  (address (+ 8 address)) (count (proof-header-size (proof-load-word address machine)))))
           :in-theory (disable allocation-objects-outside-write-p proof-object-size proof-header-size
                               proof-integer-view allocation-string-after-disjoint-write
                               boymoo-model::a64-store))))

(defthm allocation-cons-object-size
  (implies (eq (proof-object-kind object) :cons)
           (equal (proof-object-size object machine) 16)))

(defthm allocation-noncons-payload-size-bound
  (implies (not (eq (proof-object-kind object) :cons))
           (<= (+ 8 (proof-header-size (proof-load-word (proof-object-address object) machine)))
               (proof-object-size object machine)))
  :rule-classes :linear
  :hints (("Goal" :use allocation-object-size-covers-payload
           :in-theory (disable proof-object-size proof-load-word proof-header-size))))

(defthm allocation-cons-cdr-after-write
  (implies (and (allocation-write-disjoint-from-objects-p start bytes objects machine)
                (assoc-equal address objects)
                (eq (proof-object-kind (assoc-equal address objects)) :cons))
           (equal (proof-load-word (+ 8 address) (boymoo-model::a64-store bytes start value machine))
                  (proof-load-word (+ 8 address) machine)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal" :use ((:instance allocation-known-object-field-after-write (offset 8)))
           :in-theory (disable allocation-known-object-field-after-write boymoo-model::a64-store))))

(defthm allocation-two-header-fields-after-write
  (implies (and (allocation-write-disjoint-from-objects-p start bytes objects machine)
                (assoc-equal address objects)
                (eq (proof-object-kind (assoc-equal address objects)) :header)
                (equal (proof-header-size (proof-load-word address machine)) 16))
           (and (equal (proof-load-word (+ 8 address) (boymoo-model::a64-store bytes start value machine))
                       (proof-load-word (+ 8 address) machine))
                (equal (proof-load-word (+ 16 address) (boymoo-model::a64-store bytes start value machine))
                       (proof-load-word (+ 16 address) machine))))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal"
           :use ((:instance allocation-known-object-field-after-write (offset 8))
                 (:instance allocation-known-object-field-after-write (offset 16))
                 (:instance allocation-object-size-covers-payload (object (assoc-equal address objects))))
           :in-theory (disable allocation-known-object-field-after-write proof-header-size
                               proof-object-size boymoo-model::a64-store))))

(defun allocation-view-slots-outside-write-p (kind input count start bytes)
  (or (not (eq kind :slots)) (zp count)
      (and (proof-span-p input (* 8 count))
           (proof-disjoint-p start (+ start bytes) input (+ input (* 8 count))))))

(defthm allocation-nonslot-view-needs-no-slot-span
  (implies (not (eq kind :slots))
           (allocation-view-slots-outside-write-p kind input count start bytes)))

(defthm allocation-slot-span-after-first-slot
  (implies (allocation-view-slots-outside-write-p :slots input count start bytes)
           (allocation-view-slots-outside-write-p :slots (+ 8 input) (1- count) start bytes)))

(defthm allocation-first-slot-after-disjoint-write
  (implies (and (allocation-view-slots-outside-write-p :slots input count start bytes)
                (proof-span-p start bytes) (posp count))
           (equal (proof-load-word input (boymoo-model::a64-store bytes start value machine))
                  (proof-load-word input machine)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-store))))

(defthm allocation-header-slots-outside-write
  (let* ((object (assoc-equal address objects))
         (size (proof-header-size (proof-load-word address machine))))
    (implies (and (allocation-write-disjoint-from-objects-p start bytes objects machine)
                  object (eq (proof-object-kind object) :header))
             (allocation-view-slots-outside-write-p :slots (+ 8 address) (ash size -3) start bytes)))
  :rule-classes ((:rewrite :match-free :once))
  :hints (("Goal"
           :use ((:instance allocation-lookup-object-outside-write (end (+ start bytes)))
                 (:instance allocation-object-size-covers-payload (object (assoc-equal address objects)))
                 (:instance allocation-slot-bytes-fit (size (proof-header-size (proof-load-word address machine)))))
           :in-theory (disable allocation-objects-outside-write-p proof-object-size proof-header-size ash))))

(defthm allocation-view-step-after-disjoint-write
  (implies (and (allocation-write-disjoint-from-objects-p start bytes objects machine)
                (allocation-view-slots-outside-write-p kind input count start bytes))
           (equal (proof-view-step kind input count depth base objects packages
                                   (boymoo-model::a64-store bytes start value machine))
                  (proof-view-step kind input count depth base objects packages machine)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-view-step kind input count depth base objects packages machine)
           :expand ((:free (mode mem) (proof-view-step mode input count depth base objects packages mem)))
           :in-theory (disable (:definition proof-view-step)
                               allocation-write-disjoint-from-objects-p
                               allocation-view-slots-outside-write-p
                               allocation-objects-outside-write-p proof-object-size
                               proof-pointer-address proof-word-tag proof-header-type proof-header-size
                               proof-load-string proof-integer-view proof-cons-value proof-symbol-value
                               proof-rational-value proof-complex-value
                               boymoo-model::a64-store mod oddp ash))))

(defthm allocation-view-after-disjoint-write
  (implies (and (proof-span-p start bytes)
                (allocation-objects-outside-write-p start (+ start bytes) objects machine))
           (equal (proof-view word base objects packages (boymoo-model::a64-store bytes start value machine))
                  (proof-view word base objects packages machine)))
  :hints (("Goal"
           :use ((:instance allocation-view-step-after-disjoint-write
                  (kind :word) (input word) (count 0)
                  (depth (1+ (nfix (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) objects)))))))
           :in-theory (disable proof-view-step proof-pointer-address proof-object-rank
                               allocation-objects-outside-write-p boymoo-model::a64-store))))

(defthm allocation-object-disjointness-after-write
  (implies (and (proof-span-p start bytes)
                (allocation-objects-outside-write-p start (+ start bytes) objects machine))
           (equal (proof-object-disjoint-p address end objects (boymoo-model::a64-store bytes start value machine))
                  (proof-object-disjoint-p address end objects machine)))
  :hints (("Goal" :induct (allocation-objects-outside-write-p start (+ start bytes) objects machine)
           :in-theory (disable proof-object-size proof-span-p proof-disjoint-p boymoo-model::a64-store))
          ("Subgoal *1/2" :use ((:instance allocation-object-size-after-disjoint-write (object (car objects)))))))

(defthm allocation-object-map-after-disjoint-write
  (implies (and (proof-span-p start bytes)
                (allocation-objects-outside-write-p start (+ start bytes) objects machine)
                (allocation-objects-outside-write-p start (+ start bytes) pending machine)
                (proof-object-map-p pending objects symbols base packages machine))
           (proof-object-map-p pending objects symbols base packages (boymoo-model::a64-store bytes start value machine)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
           :in-theory (disable proof-object-size proof-span-p proof-disjoint-p proof-view
                               proof-symbol-object-p proof-object-record-p boymoo-model::a64-store))
          ("Subgoal *1/2" :use ((:instance allocation-object-size-after-disjoint-write (object (car pending)))))))

(defthm allocation-stack-views-after-disjoint-write
  (implies (and (proof-span-p start bytes)
                (allocation-objects-outside-write-p start (+ start bytes) objects machine)
                (allocation-view-slots-outside-write-p :slots address count start bytes))
           (equal (proof-stack-views count address base objects packages (boymoo-model::a64-store bytes start value machine))
                  (proof-stack-views count address base objects packages machine)))
  :hints (("Goal" :induct (proof-stack-views count address base objects packages machine)
           :expand ((:free (mem) (proof-stack-views count address base objects packages mem)))
           :in-theory (disable (:definition proof-stack-views) proof-view
                               allocation-objects-outside-write-p boymoo-model::a64-store))))
