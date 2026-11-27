(in-package "BOYMOO-PROOFS")

(include-book "frame-memory")
(include-book "view-memory")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-byte-entries-agree-p
                    sequence-machine-span-agrees-p sequence-machine-write-confined-p
                    proof-load-word proof-object-size proof-header-type
                    proof-pointer-address proof-word-tag))

(local
 (defmacro sequence-def-agreed-loads (name operation width)
   (let ((scheme (if (equal width 1) 'proof-byte-list 'proof-limb-magnitude)))
     `(defthm ,name
        (implies (and (sequence-machine-span-agrees-p start end first last)
                      (proof-subspan-p address (* ,width (nfix count)) start end))
                 (equal (,operation count address first)
                        (,operation count address last)))
        :hints (("Goal" :induct (,scheme count address first)
                        :expand ((:free (machine) (,operation count address machine)))
                        :in-theory (e/d ((:induction ,scheme))
                                        ((:definition ,operation))))
                ("Subgoal *1/2"
                 :in-theory (enable proof-load-word)
                 :use ((:instance sequence-read-in-agreed-machine-span
                                  (count ,width)))
                 :cases ((equal count 1))))
        :rule-classes nil))))

(local (sequence-def-agreed-loads sequence-agreed-byte-list proof-byte-list 1))
(local (sequence-def-agreed-loads sequence-agreed-limbs-p proof-limbs-p 8))
(local (sequence-def-agreed-loads sequence-agreed-limb-magnitude proof-limb-magnitude 8))

(defthm sequence-string-from-agreed-span
  (implies (and (sequence-machine-span-agrees-p start end first last)
                (proof-subspan-p address (nfix count) start end))
           (equal (proof-load-string count address first)
                  (proof-load-string count address last)))
  :hints (("Goal" :in-theory (disable proof-byte-list)
                  :use sequence-agreed-byte-list))
  :rule-classes nil)

(local
 (defthm sequence-payload-size-is-natural
   (natp (proof-header-size (proof-load-word address machine)))
   :hints (("Goal" :in-theory (enable proof-load-word)
                   :use ((:instance sequence-floor-of-unsigned
                                    (dropped 8) (kept 56)
                                    (value (proof-load-word address machine))))))
   :rule-classes :type-prescription))

(local (in-theory (disable proof-header-size)))

(local
 (defthm sequence-word-in-agreed-span
   (implies (and (sequence-machine-span-agrees-p start end first last)
                 (proof-subspan-p address 8 start end))
            (equal (proof-load-word address last)
                   (proof-load-word address first)))
   :hints (("Goal" :in-theory (enable proof-load-word)
                   :use ((:instance sequence-read-in-agreed-machine-span (count 8)))))
   :rule-classes nil))

(local
 (defthm sequence-zero-integer-limbs
   (and (proof-limbs-p 0 address machine)
        (equal (proof-limb-magnitude 0 address machine) 0))
   :hints (("Goal" :expand ((proof-limbs-p 0 address machine)
                            (proof-limb-magnitude 0 address machine))))))

(local
 (defthm sequence-integer-views-from-agreed-fields
   (let* ((header (proof-load-word address first))
          (size (proof-header-size header))
          (count (1- (ash size -3))))
     (implies (and (equal (proof-load-word address last) header)
                   (implies (<= 8 size)
                            (and (equal (proof-load-word (+ address 8) last)
                                        (proof-load-word (+ address 8) first))
                                 (equal (proof-limbs-p count (+ address 16) first)
                                        (proof-limbs-p count (+ address 16) last))
                                 (equal (proof-limb-magnitude count (+ address 16) first)
                                        (proof-limb-magnitude count (+ address 16) last)))))
              (equal (proof-integer-view address first)
                     (proof-integer-view address last))))
   :hints (("Goal" :in-theory (disable proof-limbs-p proof-limb-magnitude)))
   :rule-classes nil))

(local
 (defthm sequence-integer-limb-count-fits
   (implies (and (natp size) (<= 8 size))
            (and (natp (1- (ash size -3)))
                 (<= (+ 8 (* 8 (1- (ash size -3)))) size)))
   :hints (("Goal" :use ((:instance sequence-floor-bounds (value size) (divisor 8)))))
   :rule-classes nil))

(local
 (defthm sequence-integer-from-agreed-span
   (let ((size (proof-header-size (proof-load-word address first))))
     (implies (and (sequence-machine-span-agrees-p start end first last)
                   (proof-subspan-p address (+ 8 size) start end))
              (equal (proof-integer-view address first)
                     (proof-integer-view address last))))
   :hints
   (("Goal"
     :in-theory (disable proof-limbs-p proof-limb-magnitude proof-integer-view)
     :cases ((< (proof-header-size (proof-load-word address first)) 8)
             (equal (ash (proof-header-size (proof-load-word address first)) -3) 1))
     :use (sequence-integer-views-from-agreed-fields
           sequence-word-in-agreed-span
           (:instance sequence-word-in-agreed-span (address (+ address 8)))
           (:instance sequence-integer-limb-count-fits
                      (size (proof-header-size (proof-load-word address first))))
           (:instance sequence-agreed-limbs-p
                      (count (1- (ash (proof-header-size (proof-load-word address first)) -3)))
                      (address (+ address 16)))
           (:instance sequence-agreed-limb-magnitude
                      (count (1- (ash (proof-header-size (proof-load-word address first)) -3)))
                      (address (+ address 16))))))
   :rule-classes nil))

(defun sequence-slot-storage-agrees-p (address count first last)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (equal (proof-load-word address first) (proof-load-word address last))
         (sequence-slot-storage-agrees-p (+ 8 address) (1- count) first last))))

(local
 (defthm sequence-empty-storage-views
   (and (equal (proof-load-string 0 address machine) "")
        (sequence-slot-storage-agrees-p address 0 first last))
   :hints (("Goal" :expand ((proof-byte-list 0 address machine))))))

(local
 (defthm sequence-slot-storage-from-agreed-span
   (implies (and (sequence-machine-span-agrees-p start end first last)
                 (proof-subspan-p address (* 8 (nfix count)) start end))
            (sequence-slot-storage-agrees-p address count first last))
   :hints (("Goal" :induct (proof-limb-magnitude count address first))
           ("Subgoal *1/2"
            :in-theory (enable proof-load-word)
            :use ((:instance sequence-read-in-agreed-machine-span (count 8)))
            :cases ((equal count 1))))
   :rule-classes nil))

(defun sequence-object-storage-agrees-p (pending first last)
  (if (atom pending)
      t
    (let* ((object (car pending))
           (address (proof-object-address object))
           (size (proof-object-size object first)))
      (and (proof-span-p address size)
           (sequence-machine-span-agrees-p address (+ address size) first last)
           (sequence-object-storage-agrees-p (cdr pending) first last)))))

(local
 (defthm sequence-storage-of-member
   (let ((address (proof-object-address object))
         (size (proof-object-size object first)))
     (implies (and (member-equal object pending)
                   (sequence-object-storage-agrees-p pending first last))
              (and (proof-span-p address size)
                   (sequence-machine-span-agrees-p address (+ address size) first last))))
   :hints (("Goal" :induct (member-equal object pending)
                   :in-theory (disable proof-span-p)))
   :rule-classes nil))

(local
 (defthm sequence-lookup-address-of-object
   (implies (assoc-equal address objects)
            (equal (proof-object-address (assoc-equal address objects)) address))
   :hints (("Goal" :induct (assoc-equal address objects)))))

(local
 (defthm sequence-lookup-is-member
   (implies (assoc-equal address objects)
            (member-equal (assoc-equal address objects) objects))
   :hints (("Goal" :induct (assoc-equal address objects)))))

(local
 (defthm sequence-data-size-fits-object
   (implies (not (eq (proof-object-kind object) :cons))
            (<= (+ 8 (proof-header-size
                      (proof-load-word (proof-object-address object) machine)))
                (proof-object-size object machine)))
   :hints (("Goal"
            :in-theory (enable proof-object-size)
            :use ((:instance sequence-align-up-covers-address
                             (address (proof-header-size
                                       (proof-load-word (proof-object-address object) machine)))
                             (alignment 8)))))
   :rule-classes nil))

(local (in-theory (disable proof-object-address)))

(local
 (defthm sequence-agreed-object-fields
   (let* ((object (assoc-equal address objects))
          (header (proof-load-word address first))
          (size (proof-header-size header)))
     (implies (and object (sequence-object-storage-agrees-p objects first last))
              (and (equal (proof-load-word address last) header)
                   (implies (or (eq (proof-object-kind object) :cons)
                                (and (eq (proof-object-kind object) :header) (equal size 16)))
                            (equal (proof-load-word (+ address 8) last)
                                   (proof-load-word (+ address 8) first)))
                   (implies (eq (proof-object-kind object) :header)
                            (and (equal (proof-load-string size (+ address 8) last)
                                        (proof-load-string size (+ address 8) first))
                                 (equal (proof-integer-view address last)
                                        (proof-integer-view address first))
                                 (implies (equal size 16)
                                          (equal (proof-load-word (+ address 16) last)
                                                 (proof-load-word (+ address 16) first)))
                                 (implies (equal (mod size 8) 0)
                                          (sequence-slot-storage-agrees-p
                                           (+ address 8) (ash size -3) first last)))))))
   :hints
   (("Goal"
     :in-theory (e/d (proof-object-size)
                     (sequence-object-storage-agrees-p proof-align-up
                      proof-integer-view proof-load-string sequence-slot-storage-agrees-p))
     :cases ((equal (proof-header-size (proof-load-word address first)) 0))
     :use ((:instance sequence-storage-of-member
                      (object (assoc-equal address objects)) (pending objects))
           (:instance sequence-data-size-fits-object
                      (object (assoc-equal address objects)) (machine first))
           (:instance sequence-floor-bounds
                      (value (proof-header-size (proof-load-word address first))) (divisor 8))
           (:instance sequence-word-in-agreed-span
                      (start address) (end (+ address (proof-object-size
                                                       (assoc-equal address objects) first))))
           (:instance sequence-word-in-agreed-span
                      (start address) (end (+ address (proof-object-size
                                                       (assoc-equal address objects) first)))
                      (address (+ address 8)))
           (:instance sequence-word-in-agreed-span
                      (start address) (end (+ address (proof-object-size
                                                       (assoc-equal address objects) first)))
                      (address (+ address 16)))
           (:instance sequence-string-from-agreed-span
                      (start address) (end (+ address (proof-object-size
                                                       (assoc-equal address objects) first)))
                      (address (+ address 8)) (count (proof-header-size (proof-load-word address first))))
           (:instance sequence-integer-from-agreed-span
                      (start address) (end (+ address (proof-object-size
                                                       (assoc-equal address objects) first))))
           (:instance sequence-slot-storage-from-agreed-span
                      (start address) (end (+ address (proof-object-size
                                                       (assoc-equal address objects) first)))
                      (address (+ address 8))
                      (count (ash (proof-header-size (proof-load-word address first)) -3))))))
   :rule-classes nil))

(local
 (defthm sequence-header-on-agreed-objects
   (implies (and (sequence-object-storage-agrees-p objects first last)
                 (assoc-equal address objects))
            (equal (proof-load-word address last)
                   (proof-load-word address first)))
   :hints (("Goal" :use sequence-agreed-object-fields))
   :rule-classes ((:rewrite :match-free :all))))

(local
 (defthm sequence-first-slot-on-agreed-objects
   (let* ((object (assoc-equal address objects))
          (size (proof-header-size (proof-load-word address first))))
     (implies (and (sequence-object-storage-agrees-p objects first last)
                   object
                   (or (eq (proof-object-kind object) :cons)
                       (and (eq (proof-object-kind object) :header) (equal size 16))))
              (equal (proof-load-word (+ 8 address) last)
                     (proof-load-word (+ 8 address) first))))
   :hints (("Goal" :use sequence-agreed-object-fields))
   :rule-classes ((:rewrite :match-free :all))))

(local
 (defthm sequence-second-header-slot-on-agreed-objects
   (let* ((object (assoc-equal address objects))
          (size (proof-header-size (proof-load-word address first))))
     (implies (and (sequence-object-storage-agrees-p objects first last)
                   object (eq (proof-object-kind object) :header) (equal size 16))
              (equal (proof-load-word (+ 16 address) last)
                     (proof-load-word (+ 16 address) first))))
   :hints (("Goal" :use sequence-agreed-object-fields))
   :rule-classes ((:rewrite :match-free :all))))

(local
 (defthm sequence-integer-on-agreed-objects
   (let ((object (assoc-equal address objects)))
     (implies (and (sequence-object-storage-agrees-p objects first last)
                   object (eq (proof-object-kind object) :header))
              (equal (proof-integer-view address last)
                     (proof-integer-view address first))))
   :hints (("Goal" :in-theory (disable proof-integer-view)
                   :use sequence-agreed-object-fields))
   :rule-classes ((:rewrite :match-free :all))))

(local
 (defthm sequence-string-on-agreed-objects
   (let ((object (assoc-equal address objects)))
     (implies (and (sequence-object-storage-agrees-p objects first last)
                   object (eq (proof-object-kind object) :header)
                   (equal size (proof-header-size (proof-load-word address first))))
              (equal (proof-load-string size (+ 8 address) last)
                     (proof-load-string size (+ 8 address) first))))
   :hints (("Goal" :in-theory (disable proof-load-string)
                   :use sequence-agreed-object-fields))
   :rule-classes ((:rewrite :match-free :all))))

(local
 (defthm sequence-slots-on-agreed-vector
   (let* ((object (assoc-equal address objects))
          (size (proof-header-size (proof-load-word address first))))
     (implies (and (sequence-object-storage-agrees-p objects first last)
                   object (eq (proof-object-kind object) :header)
                   (equal (mod size 8) 0)
                   (equal count (ash size -3)))
              (sequence-slot-storage-agrees-p (+ 8 address) count first last)))
   :hints (("Goal" :in-theory (disable sequence-slot-storage-agrees-p)
                   :use sequence-agreed-object-fields))
   :rule-classes ((:rewrite :match-free :all))))

(defthm sequence-view-step-on-agreed-objects
  (implies (and (sequence-object-storage-agrees-p objects first last)
                (implies (eq kind :slots)
                         (sequence-slot-storage-agrees-p input count first last)))
           (equal (proof-view-step kind input count depth base objects packages first)
                  (proof-view-step kind input count depth base objects packages last)))
  :hints
  (("Goal"
    :induct (proof-view-step kind input count depth base objects packages first)
    :expand ((:free (state kind)
                    (proof-view-step kind input count depth base objects packages state)))
    :in-theory (e/d ((:induction proof-view-step))
                    ((:definition proof-view-step) proof-limbs-p proof-limb-magnitude
                     proof-byte-list proof-symbol-value proof-rational-value
                     proof-complex-value proof-load-string proof-integer-view
                     sequence-object-storage-agrees-p))
    :do-not '(generalize fertilize)
    :do-not-induct t))
  :rule-classes nil)

(defthm sequence-view-on-agreed-objects
  (implies (sequence-object-storage-agrees-p objects first last)
           (equal (proof-view word base objects packages first)
                  (proof-view word base objects packages last)))
  :hints (("Goal"
           :in-theory (disable proof-view-step sequence-object-storage-agrees-p)
           :use ((:instance sequence-view-step-on-agreed-objects
                            (kind :word) (input word) (count 0)
                            (depth (1+ (nfix (proof-object-rank
                                              (assoc-equal (proof-pointer-address word base)
                                                           objects)))))))))
  :rule-classes nil)

(in-theory (disable sequence-slot-storage-agrees-p sequence-object-storage-agrees-p
                    proof-view-step proof-integer-view))
