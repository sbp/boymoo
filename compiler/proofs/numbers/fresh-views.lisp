(in-package "BOYMOO-PROOFS")

(include-book "publication")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-load-word proof-value-p proof-view proof-word-tag
                     proof-pointer-address proof-header-type proof-header-size
                     boymoo-model::a64-load boymoo-model::a64-unsigned boymoo-model::a64-signed
                     acl2::binary-logand acl2::binary-logior
                     proof-number-integer-parity oddp mod floor ash)))

(defund proof-number-machine-span-agrees-p (lower upper first last)
  (proof-memory-span-agrees-p lower upper (list first) (list last)))

(defthm proof-number-word-agrees-in-machine-span
  (implies (and (natp address) (<= lower address)
                (<= (+ 8 address) upper) (<= upper (expt 2 64))
                (proof-number-machine-span-agrees-p lower upper first last))
           (equal (proof-load-word address last) (proof-load-word address first)))
  :hints (("Goal"
           :use ((:instance proof-number-load-agrees-inside-saved-span
                            (start lower) (end upper) (before (list first)) (after (list last))))
           :in-theory (e/d (proof-number-machine-span-agrees-p)
                           (proof-memory-span-agrees-p))))
  :rule-classes nil)

(local
 (defthm unchanged-limb-words
   (implies (and (natp count) (natp address) (<= lower address)
                 (<= (+ address (* 8 count)) upper) (<= upper (expt 2 64))
                 (proof-number-machine-span-agrees-p lower upper first last))
            (and (equal (proof-limb-magnitude count address last)
                        (proof-limb-magnitude count address first))
                 (equal (proof-limbs-p count address last)
                        (proof-limbs-p count address first))))
   :hints (("Goal" :induct (proof-limb-magnitude count address first))
           ("Subgoal *1/2" :use proof-number-word-agrees-in-machine-span))
   :rule-classes nil))

(local
 (defthm byte-count-to-limbs
   (implies (and (integerp size) (<= 8 size))
            (and (natp (1- (ash size -3)))
                 (<= (* 8 (ash size -3)) size)))
   :hints (("Goal"
            :use ((:instance proof-number-positive-divisor-floor-bounds (a size) (b 8)))
            :cases ((< (floor size 8) 1))))
   :rule-classes nil))

(defthm proof-number-integer-scratch-view-kept
  (let* ((size (proof-header-size (proof-load-word address first)))
         (end (+ address 8 size)))
    (implies (and (proof-integer-view address first)
                  (natp size)
                  (proof-number-machine-span-agrees-p address end first last))
             (equal (proof-integer-view address last)
                    (proof-integer-view address first))))
  :hints (("Goal"
           :use ((:instance byte-count-to-limbs
                            (size (proof-header-size (proof-load-word address first))))
                 (:instance proof-number-word-agrees-in-machine-span (lower address)
                            (upper (+ address 8 (proof-header-size (proof-load-word address first)))))
                 (:instance proof-number-word-agrees-in-machine-span (lower address)
                            (address (+ address 8))
                            (upper (+ address 8 (proof-header-size (proof-load-word address first)))))
                 (:instance unchanged-limb-words
                            (lower address) (address (+ address 16))
                            (count (1- (ash (proof-header-size (proof-load-word address first)) -3)))
                            (upper (+ address 8 (proof-header-size (proof-load-word address first))))))
           :in-theory (disable proof-limbs-p proof-limb-magnitude)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-header-kept-p (object objects first last)
  (let* ((address (proof-object-address object))
         (size (proof-header-size (proof-load-word address first)))
         (bytes (+ 8 size)))
    (and (equal (assoc-equal address objects) object)
         (natp size)
         (proof-span-p address bytes)
         (proof-number-machine-span-agrees-p address (+ address bytes) first last))))

(defun proof-number-headers-kept-p (old-objects objects first last)
  (if (endp old-objects)
      t
    (and (or (not (eq (proof-object-kind (car old-objects)) :header))
             (proof-number-header-kept-p (car old-objects) objects first last))
         (proof-number-headers-kept-p (cdr old-objects) objects first last))))

(defthm proof-number-kept-header-from-map
  (implies (and (proof-number-headers-kept-p old-objects objects first last)
                (eq (proof-object-kind (assoc-equal address old-objects)) :header))
           (proof-number-header-kept-p (assoc-equal address old-objects) objects first last))
  :hints (("Goal" :induct (proof-number-headers-kept-p old-objects objects first last))))

(local
 (defthm associated-record-key
   (implies (assoc-equal key objects)
            (equal (car (assoc-equal key objects)) key))
   :hints (("Goal" :induct (assoc-equal key objects)))))

(local
 (defthm ranked-boxed-integer-has-header
   (let* ((address (proof-pointer-address word base))
          (record (assoc-equal address objects))
          (header (proof-load-word address machine)))
     (implies (and (integerp value) (not (oddp word))
                   (equal (proof-view-step :word word 0 depth base objects packages machine)
                          (proof-value-view value)))
              (and (unsigned-byte-p 64 word) (equal (proof-word-tag word) 2)
                   (posp depth) record (eq (proof-object-kind record) :header)
                   (natp (proof-object-rank record)) (< (proof-object-rank record) depth)
                   (equal (proof-header-type header) 3)
                   (proof-span-p address (+ 8 (proof-header-size header)))
                   (equal (proof-integer-view address machine) (proof-value-view value))
                   (not (proof-immediate-integer-p value)))))
   :hints (("Goal"
            :expand ((proof-view-step :word word 0 depth base objects packages machine))
            :in-theory (disable proof-view-step proof-integer-view proof-load-string)))
   :rule-classes nil))

(defthm proof-number-integer-view-kept-with-headers
  (implies (and (integerp value)
                (equal (proof-view-step :word word 0 depth base old-objects packages first)
                       (proof-value-view value))
                (proof-number-headers-kept-p old-objects objects first last))
           (equal (proof-view-step :word word 0 depth base objects packages last)
                  (proof-value-view value)))
  :hints (("Goal"
           :use ((:instance ranked-boxed-integer-has-header (objects old-objects) (machine first))
                 (:instance proof-number-kept-header-from-map
                            (address (proof-pointer-address word base)))
                 (:instance proof-number-integer-scratch-view-kept
                            (address (proof-pointer-address word base)))
                 (:instance proof-number-word-agrees-in-machine-span
                            (lower (proof-pointer-address word base))
                            (address (proof-pointer-address word base))
                            (upper (+ 8 (proof-pointer-address word base)
                                      (proof-header-size
                                       (proof-load-word (proof-pointer-address word base) first))))))
           :expand ((proof-view-step :word word 0 depth base objects packages last))
           :in-theory (e/d (proof-number-header-kept-p)
                           (proof-integer-view proof-view-step proof-load-string
                            proof-number-headers-kept-p proof-number-kept-header-from-map))
           :cases ((oddp word))
           :do-not-induct t)
          ("Subgoal 1"
           :expand ((proof-view-step :word word 0 depth base old-objects packages first)
                    (proof-view-step :word word 0 depth base objects packages last))))
  :rule-classes nil)

(local
 (defthm restore-value-from-view
   (implies (equal (car view) :value)
            (equal (cons :value (cdr view)) view))))

(local
 (defthm ranked-fraction-has-header-and-fields
   (let* ((address (proof-pointer-address word base))
          (record (assoc-equal address objects))
          (rank (proof-object-rank record))
          (header (proof-load-word address machine))
          (num-word (proof-load-word (+ address 8) machine))
          (den-word (proof-load-word (+ address 16) machine))
          (first (proof-view-step :word num-word 0 rank base objects packages machine))
          (second (proof-view-step :word den-word 0 rank base objects packages machine)))
     (implies (and (rationalp value) (not (integerp value))
                   (equal (proof-view-step :word word 0 depth base objects packages machine)
                          (proof-value-view value)))
              (and (unsigned-byte-p 64 word) (not (oddp word)) (equal (proof-word-tag word) 2)
                   (posp depth) record (eq (proof-object-kind record) :header)
                   (natp rank) (< rank depth)
                   (equal (proof-header-size header) 16)
                   (equal (proof-header-type header) 4)
                   (proof-span-p address 24)
                   (equal first (proof-value-view (numerator value)))
                   (equal second (proof-value-view (denominator value)))
                   (equal (proof-rational-value first second) (proof-value-view value)))))
   :hints (("Goal"
            :expand ((proof-view-step :word word 0 depth base objects packages machine))
            :in-theory (disable proof-view-step proof-load-string
                                proof-limb-magnitude proof-limbs-p)))
   :rule-classes nil))

(defthm proof-number-fraction-view-kept-with-headers
  (implies (and (rationalp value) (not (integerp value))
                (equal (proof-view-step :word word 0 depth base old-objects packages first)
                       (proof-value-view value))
                (proof-number-headers-kept-p old-objects objects first last))
           (equal (proof-view-step :word word 0 depth base objects packages last)
                  (proof-value-view value)))
  :hints (("Goal"
           :use ((:instance ranked-fraction-has-header-and-fields
                            (objects old-objects) (machine first))
                 (:instance proof-number-kept-header-from-map (address (proof-pointer-address word base)))
                 (:instance proof-number-word-agrees-in-machine-span
                            (lower (proof-pointer-address word base))
                            (upper (+ 24 (proof-pointer-address word base)))
                            (address (proof-pointer-address word base)))
                 (:instance proof-number-word-agrees-in-machine-span
                            (lower (proof-pointer-address word base))
                            (upper (+ 24 (proof-pointer-address word base)))
                            (address (+ 8 (proof-pointer-address word base))))
                 (:instance proof-number-word-agrees-in-machine-span
                            (lower (proof-pointer-address word base))
                            (upper (+ 24 (proof-pointer-address word base)))
                            (address (+ 16 (proof-pointer-address word base))))
                 (:instance proof-number-integer-view-kept-with-headers
                            (word (proof-load-word (+ 8 (proof-pointer-address word base)) first))
                            (value (numerator value))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) old-objects))))
                 (:instance proof-number-integer-view-kept-with-headers
                            (word (proof-load-word (+ 16 (proof-pointer-address word base)) first))
                            (value (denominator value))
                            (depth (proof-object-rank
                                    (assoc-equal (proof-pointer-address word base) old-objects)))))
           :expand ((proof-view-step :word word 0 depth base objects packages last))
           :in-theory (e/d (proof-number-header-kept-p)
                           (proof-integer-view proof-view-step proof-load-string
                            proof-rational-value proof-number-headers-kept-p
                            proof-number-kept-header-from-map))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-rational-view-kept-with-headers
  (implies (and (rationalp value)
                (equal (proof-view-step :word word 0 depth base old-objects packages first)
                       (proof-value-view value))
                (proof-number-headers-kept-p old-objects objects first last))
           (equal (proof-view-step :word word 0 depth base objects packages last)
                  (proof-value-view value)))
  :hints (("Goal"
           :use (proof-number-integer-view-kept-with-headers
                 proof-number-fraction-view-kept-with-headers)
           :in-theory (disable proof-view-step proof-number-headers-kept-p)))
  :rule-classes nil)

(defthm proof-number-outer-view-at-higher-rank
  (implies (and (proof-value-p word value base objects packages machine)
                (or (oddp word)
                    (let ((record (assoc-equal (proof-pointer-address word base) objects)))
                      (and (posp depth) (natp (proof-object-rank record))
                           (< (proof-object-rank record) depth)))))
           (equal (proof-view-step :word word 0 depth base objects packages machine)
                  (proof-value-view value)))
  :hints (("Goal"
           :expand ((:free (limit)
                     (proof-view-step :word word 0 limit base objects packages machine)))
           :in-theory (e/d (proof-value-p proof-view)
                           (proof-view-step proof-load-string proof-integer-view
                            proof-rational-value proof-complex-value proof-symbol-value
                            proof-cons-value))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-word-below-rank-p (word rank base objects)
  (or (oddp word)
      (let ((record (assoc-equal (proof-pointer-address word base) objects)))
        (and (posp rank) (natp (proof-object-rank record))
             (< (proof-object-rank record) rank)))))

(defthm proof-number-box-keeps-rational-fields-with-headers
  (let* ((base (proof-heap-base before))
         (machine (proof-world-machine before))
         (left (proof-world-reg 0 before))
         (right (proof-world-reg 1 before)))
    (implies (and (rationalp a) (rationalp b)
                  (proof-reg-value-p 0 a before old-objects packages)
                  (proof-reg-value-p 1 b before old-objects packages)
                  (proof-number-word-below-rank-p left rank base old-objects)
                  (proof-number-word-below-rank-p right rank base old-objects)
                  (proof-number-headers-kept-p old-objects objects machine
                                               (proof-world-machine after)))
             (proof-number-box-field-views-preserved-p rank before after old-objects objects packages)))
  :hints (("Goal"
           :use ((:instance proof-number-outer-view-at-higher-rank
                            (word (proof-world-reg 0 before)) (value a) (depth rank)
                            (base (proof-heap-base before)) (objects old-objects)
                            (machine (proof-world-machine before)))
                 (:instance proof-number-outer-view-at-higher-rank
                            (word (proof-world-reg 1 before)) (value b) (depth rank)
                            (base (proof-heap-base before)) (objects old-objects)
                            (machine (proof-world-machine before)))
                 (:instance proof-number-rational-view-kept-with-headers
                            (word (proof-world-reg 0 before)) (value a) (depth rank)
                            (base (proof-heap-base before))
                            (first (proof-world-machine before)) (last (proof-world-machine after)))
                 (:instance proof-number-rational-view-kept-with-headers
                            (word (proof-world-reg 1 before)) (value b) (depth rank)
                            (base (proof-heap-base before))
                            (first (proof-world-machine before)) (last (proof-world-machine after))))
           :in-theory (e/d (proof-number-word-below-rank-p proof-number-box-field-views-preserved-p
                                                         proof-value-p)
                           (proof-view-step proof-view proof-heap-base
                            proof-number-headers-kept-p))
           :do-not-induct t))
  :rule-classes nil)

(defun proof-number-memory-byte-keys-p (memory)
  (if (atom memory)
      (null memory)
    (and (unsigned-byte-p 64 (caar memory))
         (proof-number-memory-byte-keys-p (cdr memory)))))

(local
 (defthm byte-keys-after-put
   (implies (and (unsigned-byte-p 64 address)
                 (proof-number-memory-byte-keys-p memory))
            (proof-number-memory-byte-keys-p (put-assoc-equal address byte memory)))
   :hints (("Goal" :induct (put-assoc-equal address byte memory)))))

(defthm proof-number-byte-keys-after-write
  (implies (proof-number-memory-byte-keys-p memory)
           (proof-number-memory-byte-keys-p
            (boymoo-model::a64-write-bytes count address value memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count address value memory))))

(local
 (defthm byte-at-noninteger-address
   (implies (not (integerp address))
            (equal (boymoo-model::a64-byte address memory)
                   (boymoo-model::a64-byte 0 memory)))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-byte boymoo-model::a64-unsigned)
                                  (acl2::binary-logand))))))

(local
 (defthm entries-kept-by-disjoint-store
   (implies (and (or (posp dest) (proof-number-memory-byte-keys-p entries))
                 (natp lower) (<= upper (expt 2 64))
                 (proof-span-p dest size)
                 (proof-disjoint-p lower upper dest (+ dest size)))
            (proof-byte-entries-agree-p
             entries lower upper memory
             (boymoo-model::a64-write-bytes size dest value memory)))
   :hints (("Goal"
            :induct (proof-byte-entries-agree-p
                     entries lower upper memory
                     (boymoo-model::a64-write-bytes size dest value memory))
            :in-theory (disable boymoo-model::a64-byte boymoo-model::a64-write-bytes))
           (and stable-under-simplificationp
                '(:use ((:instance proof-number-byte-after-write-outside
                                   (count size)
                                   (address (if (integerp (caar entries)) (caar entries) 0)))))))
   :rule-classes nil))

(defthm proof-number-store-keeps-disjoint-span
  (implies (and (or (posp dest)
                    (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine)))
                (natp lower) (<= upper (expt 2 64))
                (proof-span-p dest size)
                (proof-disjoint-p lower upper dest (+ dest size)))
           (proof-number-machine-span-agrees-p
            lower upper machine (boymoo-model::a64-store size dest value machine)))
  :hints (("Goal"
           :use ((:instance entries-kept-by-disjoint-store
                            (memory (boymoo-model::a64-memory machine))
                            (entries (boymoo-model::a64-memory machine)))
                 (:instance entries-kept-by-disjoint-store
                            (memory (boymoo-model::a64-memory machine))
                            (entries (boymoo-model::a64-write-bytes
                                      size dest value (boymoo-model::a64-memory machine)))))
           :in-theory (e/d (proof-number-machine-span-agrees-p)
                           (proof-byte-entries-agree-p boymoo-model::a64-write-bytes))))
  :rule-classes nil)

(defund proof-number-box-field-stores (address header left right machine)
  (boymoo-model::a64-store
   8 (+ 16 address) right
   (boymoo-model::a64-store
    8 (+ 8 address) left
    (boymoo-model::a64-store 8 address header machine))))

(local
 (defthm byte-outside-box-field-stores
   (implies (and (unsigned-byte-p 64 byte-address)
                 (proof-span-p address 24)
                 (or (< byte-address address) (<= (+ address 24) byte-address)))
            (equal (boymoo-model::a64-byte
                    byte-address
                    (boymoo-model::a64-memory
                     (proof-number-box-field-stores address header left right machine)))
                   (boymoo-model::a64-byte byte-address (boymoo-model::a64-memory machine))))
   :hints (("Goal"
            :in-theory (e/d (proof-number-box-field-stores)
                            (boymoo-model::a64-byte boymoo-model::a64-write-bytes))))))

(local
 (defthm entries-outside-box-field-stores
   (implies (and (or (posp address) (proof-number-memory-byte-keys-p entries))
                 (natp lower) (<= upper (expt 2 64))
                 (proof-span-p address 24)
                 (proof-disjoint-p lower upper address (+ 24 address)))
            (proof-byte-entries-agree-p
             entries lower upper (boymoo-model::a64-memory machine)
             (boymoo-model::a64-memory
              (proof-number-box-field-stores address header left right machine))))
   :hints (("Goal"
            :induct (proof-byte-entries-agree-p
                     entries lower upper (boymoo-model::a64-memory machine)
                     (boymoo-model::a64-memory
                      (proof-number-box-field-stores address header left right machine)))
            :in-theory (disable boymoo-model::a64-byte boymoo-model::a64-memory))
           (and stable-under-simplificationp
                '(:use ((:instance byte-outside-box-field-stores
                                   (byte-address (if (integerp (caar entries))
                                                     (caar entries) 0)))))))
   :rule-classes nil))

(local
 (defthm keys-after-box-field-stores
   (implies (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine))
            (proof-number-memory-byte-keys-p
             (boymoo-model::a64-memory
              (proof-number-box-field-stores address header left right machine))))
   :hints (("Goal"
            :in-theory (e/d (proof-number-box-field-stores)
                            (boymoo-model::a64-write-bytes))))))

(defthm proof-number-box-field-stores-keep-disjoint-span
  (implies (and (or (posp address)
                    (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine)))
                (natp lower) (<= upper (expt 2 64))
                (proof-span-p address 24)
                (proof-disjoint-p lower upper address (+ 24 address)))
           (proof-number-machine-span-agrees-p
            lower upper machine (proof-number-box-field-stores address header left right machine)))
  :hints (("Goal"
           :use ((:instance entries-outside-box-field-stores
                            (entries (boymoo-model::a64-memory machine)))
                 (:instance entries-outside-box-field-stores
                            (entries (boymoo-model::a64-memory
                                      (proof-number-box-field-stores address header left right machine)))))
           :in-theory (e/d (proof-number-machine-span-agrees-p)
                           (proof-byte-entries-agree-p boymoo-model::a64-memory))))
  :rule-classes nil)

(defund proof-number-header-avoids-box-p (object old-objects address machine)
  (let* ((start (proof-object-address object))
         (size (proof-header-size (proof-load-word start machine)))
         (bytes (+ 8 size)))
    (and (equal (assoc-equal start old-objects) object)
         (natp size)
         (proof-span-p start bytes)
         (proof-disjoint-p start (+ start bytes) address (+ address 24)))))

(defun proof-number-headers-avoid-box-p (pending old-objects address machine)
  (if (endp pending)
      t
    (and (or (not (eq (proof-object-kind (car pending)) :header))
             (proof-number-header-avoids-box-p (car pending) old-objects address machine))
         (proof-number-headers-avoid-box-p (cdr pending) old-objects address machine))))

(local
 (defthm one-header-kept-with-fresh-box
   (implies (and (proof-number-header-avoids-box-p object old-objects address machine)
                 (or (posp address)
                     (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine)))
                 (proof-span-p address 24))
            (proof-number-header-kept-p
             object (cons (proof-object address :active :header rank) old-objects)
             machine (proof-number-box-field-stores address header left right machine)))
   :hints (("Goal"
            :use ((:instance proof-number-box-field-stores-keep-disjoint-span
                             (lower (proof-object-address object))
                             (upper (+ (proof-object-address object) 8
                                       (proof-header-size (proof-load-word
                                                           (proof-object-address object) machine))))))
            :in-theory (enable proof-number-header-avoids-box-p proof-number-header-kept-p)))
   :rule-classes nil))

(defthm proof-number-headers-kept-after-fresh-box-stores
  (implies (and (proof-number-headers-avoid-box-p pending old-objects address machine)
                (or (posp address)
                    (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine)))
                (proof-span-p address 24))
           (proof-number-headers-kept-p
            pending (cons (proof-object address :active :header rank) old-objects)
            machine (proof-number-box-field-stores address header left right machine)))
  :hints (("Goal" :induct (proof-number-headers-avoid-box-p pending old-objects address machine))
          ("Subgoal *1/2"
           :use ((:instance one-header-kept-with-fresh-box (object (car pending))))))
  :rule-classes nil)

(local
 (defthm stored-machine-memory
   (equal (boymoo-model::a64-memory (boymoo-model::a64-store count address value machine))
          (boymoo-model::a64-write-bytes count address value (boymoo-model::a64-memory machine)))))

(defthm proof-number-box-publish-writes-only-three-fields
  (let* ((machine (proof-world-machine world))
         (stack (boymoo-model::a64-sp machine))
         (address (proof-world-reg 2 world))
         (after (proof-number-execute-block *proof-number-box-publish-instructions* world)))
    (implies (and (not (eq (car machine) :svc))
                  (<= (proof-heap-base world) address))
             (equal (boymoo-model::a64-memory (proof-world-machine after))
                    (boymoo-model::a64-memory
                     (proof-number-box-field-stores
                      address (proof-load-word stack machine)
                      (proof-world-reg 0 world) (proof-world-reg 1 world) machine)))))
  :hints (("Goal"
           :in-theory (e/d (proof-number-box-field-stores)
                           (proof-execute proof-instruction-effect proof-reg proof-world-machine
                            boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                            boymoo-model::a64-set-pc boymoo-model::a64-pc boymoo-model::a64-sp
                            boymoo-model::a64-store boymoo-model::a64-write-bytes
                            boymoo-model::a64-memory (:definition update-nth) (:definition nth)))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm header-kept-with-same-final-memory
   (implies (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory other))
            (equal (proof-number-header-kept-p object objects first last)
                   (proof-number-header-kept-p object objects first other)))
   :hints (("Goal"
            :in-theory (e/d (proof-number-header-kept-p proof-number-machine-span-agrees-p)
                            (proof-byte-entries-agree-p))))
   :rule-classes nil))

(local
 (defthm headers-kept-with-same-final-memory
   (implies (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory other))
            (equal (proof-number-headers-kept-p pending objects first last)
                   (proof-number-headers-kept-p pending objects first other)))
   :hints (("Goal" :induct (proof-number-headers-kept-p pending objects first last))
           ("Subgoal *1/3"
            :use ((:instance header-kept-with-same-final-memory (object (car pending)))))
           ("Subgoal *1/2"
            :use ((:instance header-kept-with-same-final-memory (object (car pending))))))
   :rule-classes nil))

(defthm proof-number-publish-keeps-old-headers
  (let* ((machine (proof-world-machine world))
         (address (proof-world-reg 2 world))
         (after (proof-number-execute-block *proof-number-box-publish-instructions* world))
         (objects (cons (proof-object address :active :header rank) old-objects)))
    (implies (and (not (eq (car machine) :svc))
                  (<= (proof-heap-base world) address)
                  (proof-span-p address 24)
                  (or (posp address)
                      (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine)))
                  (proof-number-headers-avoid-box-p old-objects old-objects address machine))
             (proof-number-headers-kept-p old-objects objects machine (proof-world-machine after))))
  :hints (("Goal"
           :use (proof-number-box-publish-writes-only-three-fields
                 (:instance proof-number-headers-kept-after-fresh-box-stores
                            (pending old-objects) (address (proof-world-reg 2 world))
                            (machine (proof-world-machine world))
                            (header (proof-load-word
                                     (boymoo-model::a64-sp (proof-world-machine world))
                                     (proof-world-machine world)))
                            (left (proof-world-reg 0 world)) (right (proof-world-reg 1 world)))
                 (:instance headers-kept-with-same-final-memory (pending old-objects)
                            (objects (cons (proof-object (proof-world-reg 2 world)
                                                         :active :header rank)
                                           old-objects))
                            (first (proof-world-machine world))
                            (last (proof-world-machine
                                   (proof-number-execute-block
                                    *proof-number-box-publish-instructions* world)))
                            (other (proof-number-box-field-stores
                                    (proof-world-reg 2 world)
                                    (proof-load-word (boymoo-model::a64-sp (proof-world-machine world))
                                                     (proof-world-machine world))
                                    (proof-world-reg 0 world) (proof-world-reg 1 world)
                                    (proof-world-machine world)))))
           :in-theory (disable proof-number-execute-block proof-number-headers-kept-p
                               proof-number-memory-byte-keys-p proof-number-headers-avoid-box-p
                               proof-world-machine boymoo-model::a64-memory)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-box-publishes-in-fresh-span
  (let* ((machine (proof-world-machine world))
         (stack (boymoo-model::a64-sp machine))
         (base (proof-heap-base world))
         (address (proof-world-reg 2 world))
         (link (proof-load-word (+ 8 stack) machine))
         (objects (cons (proof-object address :active :header rank) old-objects))
         (after (proof-number-execute-block *proof-number-box-publish-instructions* world))
         (result (if (equal kind 4) (/ a b) (complex a b))))
    (implies (and (if (equal kind 4)
                      (and (proof-number-reduced-p a b) (< 1 b))
                    (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0))))
                  (proof-number-checked-block-p *proof-number-box-publish-instructions*
                                               (list link) world)
                  (not (eq (car machine) :svc))
                  (proof-span-p address 24)
                  (unsigned-byte-p 64 (+ 16 stack))
                  (<= base address)
                  (equal (mod address 8) 0)
                  (equal (mod base 8) 0)
                  (equal (proof-load-word stack machine) (+ 4096 kind))
                  (proof-reg-value-p 0 a world old-objects packages)
                  (proof-reg-value-p 1 b world old-objects packages)
                  (natp rank)
                  (proof-number-word-below-rank-p (proof-world-reg 0 world) rank base old-objects)
                  (proof-number-word-below-rank-p (proof-world-reg 1 world) rank base old-objects)
                  (or (posp address)
                      (proof-number-memory-byte-keys-p (boymoo-model::a64-memory machine)))
                  (proof-number-headers-avoid-box-p old-objects old-objects address machine))
             (and (proof-segment-p 6 (list link) world :cut after)
                  (proof-reg-value-p 0 result after objects packages))))
  :hints (("Goal"
           :use (proof-number-publish-keeps-old-headers
                 (:instance proof-number-box-keeps-rational-fields-with-headers
                            (before world)
                            (after (proof-number-execute-block
                                    *proof-number-box-publish-instructions* world))
                            (objects (cons (proof-object (proof-world-reg 2 world)
                                                         :active :header rank)
                                           old-objects)))
                 (:instance proof-number-box-publishes-canonical-value
                            (objects (cons (proof-object (proof-world-reg 2 world)
                                                         :active :header rank)
                                           old-objects))))
           :in-theory (e/d (proof-number-reduced-p)
                           (proof-number-execute-block proof-number-headers-kept-p
                            proof-number-headers-avoid-box-p proof-number-checked-block-p
                            proof-world-machine proof-world-reg proof-heap-base proof-segment-p))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm exact-alignment-product
   (implies (and (natp size) (posp alignment)
                 (equal (denominator (/ size alignment)) 1))
            (equal (* alignment (numerator (/ size alignment))) size))
   :hints (("Goal"
            :use ((:instance proof-number-quotient-of-parts (x (/ size alignment)))
                  (:instance acl2::associativity-of-*
                             (acl2::x alignment) (acl2::y (/ alignment)) (acl2::z size))
                  (:instance acl2::associativity-of-*
                             (acl2::x (/ alignment)) (acl2::y size) (acl2::z alignment)))
            :in-theory (disable proof-number-quotient-of-parts acl2::associativity-of-*)))
   :rule-classes nil))

(defthm proof-number-alignment-does-not-shrink
  (implies (and (natp size) (posp alignment))
           (<= size (proof-align-up size alignment)))
  :hints (("Goal"
           :use ((:instance proof-number-positive-divisor-floor-bounds
                            (a size) (b alignment))
                 exact-alignment-product)
           :expand ((floor size alignment))
           :in-theory (e/d (ceiling proof-align-up) (floor acl2::nonnegative-integer-quotient))))
  :rule-classes :linear)

(local
 (defthm header-payload-is-natural
   (natp (proof-header-size (proof-load-word address machine)))
   :hints (("Goal"
            :use ((:instance proof-number-positive-divisor-floor-bounds
                             (a (proof-load-word address machine)) (b 256)))
            :in-theory (enable proof-header-size)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm positive-object-size
   (< 0 (proof-object-size object machine))
   :hints (("Goal" :in-theory (disable proof-align-up proof-header-size)))
   :rule-classes :linear))

(defthm proof-number-disjoint-objects-omit-address
  (implies (and (integerp address) (< address end)
                (proof-object-disjoint-p address end objects machine))
           (not (assoc-equal address objects)))
  :hints (("Goal" :induct (proof-object-disjoint-p address end objects machine)
           :in-theory (disable proof-object-size)))
  :rule-classes nil)

(defthm proof-number-object-map-member-record-and-lookup
  (let ((address (proof-object-address object)))
    (implies (and (proof-object-map-p pending objects symbols base packages machine)
                  (member-equal object pending))
             (and (equal (assoc-equal address pending) object)
                  (proof-object-record-p object)
                  (proof-span-p address (proof-object-size object machine)))))
  :hints (("Goal" :induct (proof-object-map-p pending objects symbols base packages machine)
           :in-theory (disable proof-object-size proof-object-record-p
                               proof-object-address proof-span-p
                               proof-object-disjoint-p proof-object-view proof-symbol-object-p))
          ("Subgoal *1/2" :use ((:instance proof-number-disjoint-objects-omit-address
                                           (address (proof-object-address (car pending)))
                                           (end (+ (proof-object-address (car pending))
                                                   (proof-object-size (car pending) machine)))
                                           (objects (cdr pending))))
           :in-theory (enable proof-object-address proof-span-p)))
  :rule-classes nil)

(local
 (defthm span-disjoint-from-member
   (implies (and (member-equal object objects)
                 (proof-object-disjoint-p address end objects machine))
            (proof-disjoint-p address end (proof-object-address object)
                              (+ (proof-object-address object) (proof-object-size object machine))))
   :hints (("Goal" :induct (proof-object-disjoint-p address end objects machine)
            :in-theory (disable proof-object-size proof-disjoint-p)))
   :rule-classes nil))

(local
 (defthm reserved-span-avoids-member-header
   (implies (and (member-equal object objects)
                 (eq (proof-object-kind object) :header)
                 (proof-object-map-p objects objects nil base packages machine)
                 (proof-object-disjoint-p address (+ 24 address) objects machine))
            (proof-number-header-avoids-box-p object objects address machine))
   :hints (("Goal"
            :use ((:instance proof-number-object-map-member-record-and-lookup
                             (pending objects) (symbols nil))
                  (:instance span-disjoint-from-member (end (+ address 24))))
            :in-theory (e/d (proof-number-header-avoids-box-p)
                            (proof-object-map-p proof-object-disjoint-p proof-align-up))))
   :rule-classes nil))

(local
 (defthm reserved-span-avoids-header-subset
   (implies (and (subsetp-equal pending objects)
                 (proof-object-map-p objects objects nil base packages machine)
                 (proof-object-disjoint-p address (+ 24 address) objects machine))
            (proof-number-headers-avoid-box-p pending objects address machine))
   :hints (("Goal" :induct (proof-number-headers-avoid-box-p pending objects address machine)
            :in-theory (disable proof-object-map-p proof-object-disjoint-p))
           ("Subgoal *1/3" :use ((:instance reserved-span-avoids-member-header
                                            (object (car pending)))))
           ("Subgoal *1/2" :use ((:instance reserved-span-avoids-member-header
                                            (object (car pending))))))
   :rule-classes nil))

(local
 (defthm subset-kept-with-extra-member
   (implies (subsetp-equal left right)
            (subsetp-equal left (cons entry right)))
   :hints (("Goal" :induct (subsetp-equal left right)))))

(local
 (defthm subset-reflexive
   (subsetp-equal objects objects)
   :hints (("Goal" :induct (len objects)))))

(defthm proof-number-reserved-span-avoids-old-headers
  (let ((machine (proof-world-machine world))
        (base (proof-heap-base world)))
    (implies (and (proof-object-map-p objects objects nil base packages machine)
                  (proof-reserved-span-p :header address 24 world objects))
             (proof-number-headers-avoid-box-p objects objects address machine)))
  :hints (("Goal"
           :use ((:instance reserved-span-avoids-header-subset (pending objects)
                            (machine (proof-world-machine world)) (base (proof-heap-base world))))
           :in-theory (disable proof-object-map-p proof-object-disjoint-p
                               proof-number-headers-avoid-box-p proof-heap-base
                               proof-box-top proof-active-floor proof-world-machine)))
  :rule-classes nil)

(defun proof-number-next-object-rank (objects)
  (if (endp objects)
      1
    (max (1+ (nfix (proof-object-rank (car objects))))
         (proof-number-next-object-rank (cdr objects)))))

(local
 (defthm next-object-rank-exceeds-lookup
   (< (nfix (proof-object-rank (assoc-equal key objects)))
      (proof-number-next-object-rank objects))
   :hints (("Goal" :induct (assoc-equal key objects)))
   :rule-classes :linear))

(defthm proof-number-rational-fits-next-object-rank
  (implies (and (rationalp value) (proof-value-p word value base objects packages machine))
           (proof-number-word-below-rank-p word (proof-number-next-object-rank objects)
                                         base objects))
  :hints (("Goal"
           :use ((:instance ranked-boxed-integer-has-header
                            (depth (1+ (nfix (proof-object-rank
                                              (assoc-equal (proof-pointer-address word base)
                                                           objects))))))
                 (:instance ranked-fraction-has-header-and-fields
                            (depth (1+ (nfix (proof-object-rank
                                              (assoc-equal (proof-pointer-address word base)
                                                           objects))))))
                 (:instance next-object-rank-exceeds-lookup
                            (key (proof-pointer-address word base))))
           :in-theory (e/d (proof-value-p proof-view proof-number-word-below-rank-p)
                           (proof-view-step proof-number-next-object-rank proof-object-rank
                            next-object-rank-exceeds-lookup))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-reserved-box-alignment
  (let ((base (proof-heap-base world)))
    (implies (and (proof-heap-layout-p world)
                  (proof-reserved-span-p :header address 24 world objects))
             (and (proof-span-p address 24)
                  (posp address)
                  (<= base address)
                  (equal (mod base 8) 0)
                  (equal (mod address 8) 0))))
  :hints (("Goal"
           :use ((:instance proof-number-mod-shift-by-multiple
                            (a (+ 24 address)) (b 8) (times -3))
                 (:instance proof-number-alignment-does-not-shrink
                            (size (+ (proof-heap-base world)
                                     (proof-static-size (proof-heap-base world)
                                                        (proof-world-machine world))))
                            (alignment *proof-runtime-page*)))
           :in-theory (disable proof-active-floor proof-active-end proof-box-top
                               proof-static-size proof-heap-base proof-world-machine
                               proof-object-disjoint-p proof-align-up
                               proof-covered-p proof-page-size-p proof-regions-p
                               proof-number-alignment-does-not-shrink)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-box-publishes-reserved-value
  (let* ((machine (proof-world-machine world))
         (stack (boymoo-model::a64-sp machine))
         (address (proof-world-reg 2 world))
         (link (proof-load-word (+ 8 stack) machine))
         (rank (proof-number-next-object-rank old-objects))
         (objects (cons (proof-object address :active :header rank) old-objects))
         (after (proof-number-execute-block *proof-number-box-publish-instructions* world))
         (result (if (equal kind 4) (/ a b) (complex a b))))
    (implies (and (if (equal kind 4)
                      (and (proof-number-reduced-p a b) (< 1 b))
                    (and (equal kind 5) (rationalp a) (rationalp b) (not (equal b 0))))
                  (proof-heap-p world old-objects packages)
                  (proof-reserved-span-p :header address 24 world old-objects)
                  (proof-number-checked-block-p *proof-number-box-publish-instructions*
                                               (list link) world)
                  (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 16 stack))
                  (equal (proof-load-word stack machine) (+ 4096 kind))
                  (proof-reg-value-p 0 a world old-objects packages)
                  (proof-reg-value-p 1 b world old-objects packages))
             (and (proof-segment-p 6 (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 30 after) link)
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ 16 stack))
                  (proof-reg-value-p 0 result after objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-box-publishes-in-fresh-span
                            (rank (proof-number-next-object-rank old-objects)))
                 (:instance proof-number-box-publishes-fields)
                 (:instance proof-number-reserved-box-alignment
                            (address (proof-world-reg 2 world)) (objects old-objects))
                 (:instance proof-number-reserved-span-avoids-old-headers
                            (address (proof-world-reg 2 world)) (objects old-objects))
                 (:instance proof-number-rational-fits-next-object-rank
                            (word (proof-world-reg 0 world)) (value a) (objects old-objects)
                            (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance proof-number-rational-fits-next-object-rank
                            (word (proof-world-reg 1 world)) (value b) (objects old-objects)
                            (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (e/d (proof-number-reduced-p)
                           (proof-heap-layout-p proof-object-map-p proof-stack-prefix
                            proof-static-p proof-external-objects proof-dynamic-entries
                            proof-dynamic-symbol-objects-p proof-heap-object-spans-p
                            proof-reserved-span-p
                            proof-value-p proof-segment-p proof-number-execute-block
                            proof-number-checked-block-p proof-number-headers-avoid-box-p
                            proof-number-next-object-rank proof-world-reg proof-world-machine
                            proof-heap-base boymoo-model::a64-sp boymoo-model::a64-memory))
           :do-not-induct t))
  :rule-classes nil)
