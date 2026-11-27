(in-package "BOYMOO-PROOFS")

(include-book "object-locality")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-load-word proof-view proof-word-tag proof-pointer-address
                     proof-object-size proof-object-address proof-object-map-p
                     proof-number-object-memory-p proof-number-objects-memory-p
                     proof-number-machine-span-agrees-p proof-byte-entries-agree-p
                     boymoo-model::a64-byte boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes boymoo-model::a64-store
                     boymoo-model::a64-unsigned acl2::binary-logand mod floor ash)))

(defund proof-number-memory-change-p (start end first last)
  (equal (proof-clear-memory start end (boymoo-model::a64-memory first))
         (proof-clear-memory start end (boymoo-model::a64-memory last))))

(local
 (defthm clear-memory-after-put-inside
   (implies (and (<= start address) (< address end))
            (equal (proof-clear-memory start end (put-assoc-equal address value memory))
                   (proof-clear-memory start end memory)))
   :hints (("Goal" :induct (put-assoc-equal address value memory)))))

(local
 (defthm clear-memory-after-write-inside
   (implies (and (natp dest) (natp size)
                 (<= start dest) (<= (+ dest size) end)
                 (<= (+ dest size) (expt 2 64)))
            (equal (proof-clear-memory start end
                                       (boymoo-model::a64-write-bytes size dest value memory))
                   (proof-clear-memory start end memory)))
   :hints (("Goal" :induct (boymoo-model::a64-write-bytes size dest value memory)
                   :in-theory (e/d (boymoo-model::a64-write-bytes) (proof-clear-memory))))))

(defthm proof-number-store-changes-only-footprint
  (implies (and (proof-span-p dest size) (<= start dest) (<= (+ dest size) end))
           (proof-number-memory-change-p start end machine
                                         (boymoo-model::a64-store size dest value machine)))
  :hints (("Goal" :in-theory (e/d (proof-number-memory-change-p boymoo-model::a64-store
                                   boymoo-model::a64-memory)
                                 (proof-clear-memory))))
  :rule-classes nil)

(defthm proof-number-memory-change-composes
  (implies (and (proof-number-memory-change-p start end first middle)
                (proof-number-memory-change-p start end middle last))
           (proof-number-memory-change-p start end first last))
  :hints (("Goal" :in-theory (e/d (proof-number-memory-change-p) (proof-clear-memory))))
  :rule-classes nil)

(defthm proof-number-memory-change-from-same-memory
  (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
           (proof-number-memory-change-p start end first last))
  :hints (("Goal" :in-theory (enable proof-number-memory-change-p)))
  :rule-classes nil)

(defthm proof-number-memory-change-with-same-final-memory
  (implies (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory other))
           (equal (proof-number-memory-change-p start end first last)
                  (proof-number-memory-change-p start end first other)))
  :hints (("Goal" :in-theory (enable proof-number-memory-change-p)))
  :rule-classes nil)

(local
 (defthm keep-key-outside-cleared-memory
   (implies (or (< address start) (<= end address))
            (equal (assoc-equal address (proof-clear-memory start end memory))
                   (assoc-equal address memory)))
   :hints (("Goal" :induct (proof-clear-memory start end memory)))))

(local
 (defthm byte-at-noninteger-key
   (implies (not (integerp address))
            (equal (boymoo-model::a64-byte address memory)
                   (boymoo-model::a64-byte 0 memory)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-byte boymoo-model::a64-unsigned)))))

(local
 (defthm byte-outside-footprint
   (implies (and (unsigned-byte-p 64 address)
                 (or (< address start) (<= end address))
                 (equal (proof-clear-memory start end first)
                        (proof-clear-memory start end last)))
            (equal (boymoo-model::a64-byte address last)
                   (boymoo-model::a64-byte address first)))
   :hints (("Goal"
            :use ((:instance keep-key-outside-cleared-memory (memory first))
                  (:instance keep-key-outside-cleared-memory (memory last)))
            :in-theory (e/d (boymoo-model::a64-byte)
                            (keep-key-outside-cleared-memory proof-clear-memory))))
   :rule-classes nil))

(local
 (defthm entries-outside-footprint
   (implies (and (or (posp start) (proof-number-memory-byte-keys-p entries))
                 (natp lower) (<= upper (expt 2 64))
                 (proof-disjoint-p lower upper start end)
                 (equal (proof-clear-memory start end first)
                        (proof-clear-memory start end last)))
            (proof-byte-entries-agree-p entries lower upper first last))
   :hints (("Goal"
            :induct (proof-byte-entries-agree-p entries lower upper first last)
            :in-theory (e/d (proof-byte-entries-agree-p)
                            (proof-clear-memory)))
           (and stable-under-simplificationp
                '(:use ((:instance byte-outside-footprint
                                   (address (if (integerp (caar entries))
                                                (caar entries) 0)))))))
   :rule-classes nil))

(defthm proof-number-footprint-keeps-disjoint-span
  (implies (and (proof-number-memory-change-p start end first last)
                (or (posp start)
                    (and (proof-number-memory-byte-keys-p (boymoo-model::a64-memory first))
                         (proof-number-memory-byte-keys-p (boymoo-model::a64-memory last))))
                (natp lower) (<= upper (expt 2 64))
                (proof-disjoint-p lower upper start end))
           (proof-number-machine-span-agrees-p lower upper first last))
  :hints (("Goal"
           :use ((:instance entries-outside-footprint
                            (entries (boymoo-model::a64-memory first))
                            (first (boymoo-model::a64-memory first))
                            (last (boymoo-model::a64-memory last)))
                 (:instance entries-outside-footprint
                            (entries (boymoo-model::a64-memory last))
                            (first (boymoo-model::a64-memory first))
                            (last (boymoo-model::a64-memory last))))
           :in-theory (e/d (proof-number-machine-span-agrees-p proof-number-memory-change-p)
                           (proof-clear-memory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm mapped-span-outside-footprint
   (let* ((object (car pending))
          (address (proof-object-address object)))
     (implies (and (consp pending)
                   (proof-object-map-p pending old-objects symbols base packages first)
                   (proof-object-disjoint-p start stop pending first)
                   (equal (assoc-equal address objects) object)
                   (proof-number-memory-change-p start stop first last)
                   (posp start))
              (proof-number-object-memory-p object objects first last)))
   :hints (("Goal"
            :use ((:instance proof-number-footprint-keeps-disjoint-span
                             (end stop) (lower (proof-object-address (car pending)))
                             (upper (+ (proof-object-address (car pending))
                                       (proof-object-size (car pending) first)))))
            :in-theory (e/d (proof-number-object-memory-p proof-object-map-p)
                            (proof-object-record-p proof-object-view proof-symbol-object-p
                             proof-object-address proof-object-size))))
   :rule-classes nil))

(defthm proof-number-footprint-keeps-object-map-spans
  (implies (and (proof-object-map-p pending old-objects symbols base packages first)
                (proof-object-disjoint-p start end pending first)
                (proof-number-memory-change-p start end first last)
                (posp start)
                (proof-number-objects-memory-p pending objects first first))
           (proof-number-objects-memory-p pending objects first last))
  :hints (("Goal"
           :induct (proof-object-map-p pending old-objects symbols base packages first)
           :in-theory (e/d ((:induction proof-object-map-p) proof-number-objects-memory-p)
                           (proof-object-view proof-object-record-p proof-symbol-object-p
                            proof-object-disjoint-p))
           :expand ((proof-object-map-p pending old-objects symbols base packages first)
                    (proof-object-disjoint-p start end pending first)))
          (and stable-under-simplificationp
               '(:use ((:instance mapped-span-outside-footprint (stop end)))
                 :in-theory (enable proof-number-object-memory-p))))
  :rule-classes nil)

(local
 (defthm member-has-same-memory
   (implies (and (proof-object-map-p old-objects old-objects nil base packages machine)
                 (member-equal object old-objects)
                 (implies extra (not (assoc-equal (car extra) old-objects))))
            (proof-number-object-memory-p object
                                          (if extra (cons extra old-objects) old-objects)
                                          machine machine))
   :hints (("Goal"
            :use ((:instance proof-number-object-map-member-record-and-lookup
                             (pending old-objects) (objects old-objects) (symbols nil))
                  (:instance proof-number-span-agreement-with-same-memory
                             (first machine) (last machine)
                             (start (proof-object-address object))
                             (end (+ (proof-object-address object)
                                     (proof-object-size object machine)))))
            :in-theory (e/d (proof-number-object-memory-p) (proof-span-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-map-spans-with-unchanged-memory
  (implies (and (proof-object-map-p old-objects old-objects nil base packages machine)
                (subsetp-equal pending old-objects)
                (implies extra (not (assoc-equal (car extra) old-objects))))
           (proof-number-objects-memory-p pending
                                          (if extra (cons extra old-objects) old-objects)
                                          machine machine))
  :hints (("Goal"
           :induct (subsetp-equal pending old-objects)
           :in-theory (enable proof-number-objects-memory-p))
          ("Subgoal *1/2"
           :use ((:instance member-has-same-memory (object (car pending)))))
          ("Subgoal *1/3"
           :use ((:instance member-has-same-memory (object (car pending))))))
  :rule-classes nil)

(local
 (defthm subset-of-enlarged-list
   (implies (subsetp-equal left right)
            (subsetp-equal left (cons object right)))
   :hints (("Goal" :induct (subsetp-equal left right)))))

(local
 (defthm subset-of-self
   (subsetp-equal objects objects)
   :hints (("Goal" :induct (len objects)))))

(defthm proof-number-disjoint-footprint-keeps-old-values
  (let ((first (proof-world-machine before))
        (last (proof-world-machine after))
        (base (proof-heap-base before))
        (objects (if extra (cons extra old-objects) old-objects)))
    (implies (and (proof-object-map-p old-objects old-objects nil base packages first)
                  (proof-object-disjoint-p start end old-objects first)
                  (proof-number-memory-change-p start end first last)
                  (posp start)
                  (implies extra (not (assoc-equal (car extra) old-objects))))
             (and (proof-number-objects-memory-p old-objects objects first last)
                  (implies (and (equal (proof-heap-base after) base)
                                (proof-machine-value-p word value before old-objects packages))
                           (proof-machine-value-p word value after objects packages)))))
  :hints (("Goal"
           :use ((:instance proof-number-map-spans-with-unchanged-memory
                            (pending old-objects) (base (proof-heap-base before))
                            (machine (proof-world-machine before)))
                 (:instance proof-number-footprint-keeps-object-map-spans
                            (pending old-objects) (symbols nil)
                            (base (proof-heap-base before))
                            (objects (if extra (cons extra old-objects) old-objects))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance proof-number-value-kept-with-object-memory
                            (objects (if extra (cons extra old-objects) old-objects))))
           :in-theory (disable proof-heap-base proof-world-machine proof-machine-value-p
                               proof-object-disjoint-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-disjoint-footprint-keeps-prefix
  (let* ((lower (proof-stack-base before))
         (first (proof-world-machine before))
         (last (proof-world-machine after)))
    (implies (and (proof-stack-prefix top before old-objects packages)
                  (equal (proof-stack-base after) lower)
                  (equal (proof-heap-base after) (proof-heap-base before))
                  (<= top (proof-stack-top after))
                  (proof-number-objects-memory-p old-objects objects first last)
                  (posp start)
                  (proof-number-memory-change-p start end first last)
                  (proof-disjoint-p lower top start end))
             (proof-prefix-preserved-p top before after old-objects objects packages)))
  :hints (("Goal"
           :use (proof-number-prefix-kept-with-object-memory
                 (:instance proof-number-footprint-keeps-disjoint-span
                            (lower (proof-stack-base before)) (upper top)
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (disable proof-heap-base proof-world-machine proof-stack-base proof-stack-top
                               proof-stack-views proof-prefix-preserved-p)
           :do-not-induct t))
  :rule-classes nil)
