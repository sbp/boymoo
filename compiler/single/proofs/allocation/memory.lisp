(in-package "BOYMOO-PROOFS")

(include-book "execution")

(local (include-book "ihs/logops-lemmas" :dir :system))
(local (include-book "centaur/bitops/ihsext-basics" :dir :system))
(local (include-book "centaur/bitops/equal-by-logbitp" :dir :system))
(local (include-book "arithmetic-5/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-model-load-word-natural
  (natp (proof-load-word address machine))
  :rule-classes :type-prescription
  :hints (("Goal" :use ((:instance allocation-read-bytes-range (count 8)
                          (memory (boymoo-model::a64-memory machine))))
           :in-theory (e/d (proof-load-word unsigned-byte-p acl2::integer-range-p)
                           (allocation-read-bytes-range)))))

(local
 (defthm allocation-write-zero-bytes
   (equal (boymoo-model::a64-write-bytes 0 address value memory) memory)
   :hints (("Goal" :in-theory (enable boymoo-model::a64-write-bytes)))))

(local
 (defthm allocation-unsigned-zero-width
   (equal (boymoo-model::a64-unsigned 0 value) 0)
   :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned)))))

(local
 (defthm allocation-read-one-byte
   (equal (boymoo-model::a64-read-bytes 1 address memory)
          (boymoo-model::a64-byte address memory))
   :hints (("Goal" :expand ((boymoo-model::a64-read-bytes 1 address memory)
                            (:free (probe) (boymoo-model::a64-read-bytes 0 probe memory)))
            :in-theory (disable boymoo-model::a64-byte)))))

(local
 (defthm allocation-byte-after-binding
   (equal (boymoo-model::a64-byte
           address (put-assoc-equal key (boymoo-model::a64-unsigned 8 value) memory))
          (if (equal (boymoo-model::a64-unsigned 64 address) key)
              (boymoo-model::a64-unsigned 8 value)
            (boymoo-model::a64-byte address memory)))
   :hints (("Goal" :in-theory (disable put-assoc-equal)))))

(defthm allocation-byte-outside-written-span
  (implies (and (proof-span-p start count)
                (unsigned-byte-p 64 address)
                (or (< address start) (<= (+ start count) address)))
           (equal (boymoo-model::a64-byte
                   address (boymoo-model::a64-write-bytes count start value memory))
                  (boymoo-model::a64-byte address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count start value memory)
           :in-theory (e/d (boymoo-model::a64-write-bytes unsigned-byte-p
                            acl2::integer-range-p)
                           (put-assoc-equal boymoo-model::a64-byte
                            boymoo-model::a64-unsigned)))))

(defthm allocation-read-outside-written-span
  (implies (and (proof-span-p start count)
                (proof-span-p address size)
                (proof-disjoint-p start (+ start count) address (+ address size)))
           (equal (boymoo-model::a64-read-bytes
                   size address (boymoo-model::a64-write-bytes count start value memory))
                  (boymoo-model::a64-read-bytes size address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes size address memory)
           :in-theory (e/d (boymoo-model::a64-read-bytes unsigned-byte-p
                            acl2::integer-range-p)
                           (boymoo-model::a64-write-bytes boymoo-model::a64-byte
                            boymoo-model::a64-unsigned)))))

(local
 (defthm allocation-head-of-written-span
   (implies (and (proof-span-p address count) (posp count))
            (equal (boymoo-model::a64-byte
                    address (boymoo-model::a64-write-bytes count address value memory))
                   (boymoo-model::a64-unsigned 8 value)))
   :hints (("Goal" :cases ((equal count 1))
            :expand ((boymoo-model::a64-write-bytes count address value memory)
                     (boymoo-model::a64-write-bytes 1 address value memory))
            :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                            (boymoo-model::a64-write-bytes boymoo-model::a64-byte
                             boymoo-model::a64-unsigned))))))

(local
 (defthm allocation-byte-before-write-tail
   (implies (and (proof-span-p address count) (posp count))
            (equal (boymoo-model::a64-byte
                    address (boymoo-model::a64-write-bytes
                             (1- count) (1+ address) value memory))
                   (boymoo-model::a64-byte address memory)))
   :hints (("Goal" :cases ((equal count 1))
            :use ((:instance allocation-byte-outside-written-span
                             (start (1+ address)) (count (1- count))))
            :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                            (allocation-byte-outside-written-span
                             boymoo-model::a64-write-bytes boymoo-model::a64-byte))))))

(local
 (defthm allocation-mask-is-loghead
   (equal (boymoo-model::a64-unsigned width value)
          (acl2::loghead (nfix width) value))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-unsigned acl2::loghead)))))

(local (in-theory (disable acl2::ash-to-floor)))

(local
 (defthm allocation-low-byte-joins
   (equal (logior (acl2::loghead 8 low) (ash high 8))
          (acl2::logapp 8 low high))
   :hints ((acl2::logbitp-reasoning))))

(local
 (defthm allocation-join-written-byte
   (implies (and (posp size) (integerp value))
            (equal (logior (boymoo-model::a64-unsigned 8 value)
                           (ash (boymoo-model::a64-unsigned
                                 (* 8 (1- size)) (ash value -8))
                                8))
                   (boymoo-model::a64-unsigned (* 8 size) value)))
   :hints (("Goal" :use ((:instance acl2::loghead-logapp-loghead-logtail
                          (acl2::size 8) (acl2::size1 (* 8 (1- size))) (acl2::i value)))
            :in-theory (disable acl2::loghead-logapp-loghead-logtail
                                acl2::ash-to-floor)))))

(defthm allocation-read-written-span
  (implies (and (proof-span-p address count) (integerp value))
           (equal (boymoo-model::a64-read-bytes
                   count address (boymoo-model::a64-write-bytes count address value memory))
                  (boymoo-model::a64-unsigned (* 8 count) value)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count address value memory)
           :expand ((boymoo-model::a64-write-bytes count address value memory))
           :in-theory (e/d ((:induction boymoo-model::a64-write-bytes)
                            boymoo-model::a64-read-bytes
                            unsigned-byte-p acl2::integer-range-p)
                           (allocation-mask-is-loghead acl2::ash-to-floor
                            acl2::right-shift-to-logtail acl2::|(logior y x)|
                            acl2::commutativity-of-logior
                            boymoo-model::a64-byte boymoo-model::a64-unsigned
                            put-assoc-equal (:definition boymoo-model::a64-write-bytes))))
          ("Subgoal *1/2" :use ((:instance allocation-join-written-byte (size count))))))

(defthm allocation-word-after-store
  (implies (and (proof-span-p address 8) (integerp word))
           (equal (allocation-load-word address (allocation-store-word address word world))
                  (boymoo-model::a64-unsigned 64 word)))
  :hints (("Goal" :in-theory (e/d (allocation-load-word proof-load-word)
                                (allocation-mask-is-loghead)))))

(defthm allocation-word-after-disjoint-store
  (implies (and (proof-span-p address 8)
                (proof-span-p probe 8)
                (proof-disjoint-p address (+ 8 address) probe (+ 8 probe)))
           (equal (allocation-load-word probe (allocation-store-word address word world))
                  (allocation-load-word probe world)))
  :hints (("Goal" :in-theory (enable allocation-load-word proof-load-word))))

(defthm allocation-assoc-after-clear
  (equal (assoc-equal address (proof-clear-memory begin end memory))
         (if (and (<= begin address) (< address end))
             nil
           (assoc-equal address memory)))
  :hints (("Goal" :induct (proof-clear-memory begin end memory))))

(defthm allocation-byte-in-clear-span
  (implies (and (unsigned-byte-p 64 address) (<= begin address) (< address end))
           (equal (boymoo-model::a64-byte address (proof-clear-memory begin end memory))
                  0))
  :hints (("Goal" :in-theory (disable proof-clear-memory))))

(defthm allocation-byte-outside-clear-span
  (implies (and (unsigned-byte-p 64 address) (or (< address begin) (<= end address)))
           (equal (boymoo-model::a64-byte address (proof-clear-memory begin end memory))
                  (boymoo-model::a64-byte address memory)))
  :hints (("Goal" :in-theory (disable proof-clear-memory))))

(local
 (defthm allocation-byte-with-noninteger-address
   (implies (not (integerp address))
            (equal (boymoo-model::a64-byte address memory)
                   (boymoo-model::a64-byte 0 memory)))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-byte boymoo-model::a64-unsigned)
                                   (allocation-mask-is-loghead assoc-equal))))))

(defthm allocation-byte-entries-agree-outside-write
  (let ((updated (boymoo-model::a64-write-bytes bytes start value memory)))
    (implies (and (proof-span-p start bytes) (posp start)
                  (natp lower) (natp upper) (<= upper *allocation-word-modulus*)
                  (proof-disjoint-p start (+ start bytes) lower upper))
             (and (proof-byte-entries-agree-p entries lower upper memory updated)
                  (proof-byte-entries-agree-p entries lower upper updated memory))))
  :hints (("Goal" :induct (proof-byte-entries-agree-p entries lower upper memory memory)
           :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                           (boymoo-model::a64-byte boymoo-model::a64-write-bytes)))
          ("Subgoal *1/2" :cases ((integerp (caar entries))))))

(defthm allocation-memory-span-agrees-outside-write
  (implies (and (proof-span-p start bytes) (posp start)
                (natp lower) (natp upper) (<= upper *allocation-word-modulus*)
                (proof-disjoint-p start (+ start bytes) lower upper)
                (equal (allocation-memory after)
                       (boymoo-model::a64-write-bytes bytes start value (allocation-memory before))))
           (proof-memory-span-agrees-p lower upper before after))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-byte-entries-agree-outside-write
                  (entries (allocation-memory before)) (memory (allocation-memory before)))
                 (:instance allocation-byte-entries-agree-outside-write
                  (entries (allocation-memory after)) (memory (allocation-memory before))))
           :in-theory (disable proof-byte-entries-agree-p boymoo-model::a64-write-bytes
                               allocation-byte-entries-agree-outside-write))))
