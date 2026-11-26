(in-package "BOYMOO-PROOFS")

(include-book "state")

(logic)
(set-verify-guards-eagerness 0)

(defthm sequence-byte-bits
  (unsigned-byte-p 8 (boymoo-model::a64-byte address memory))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-byte))))

(defthm sequence-byte-is-natural
  (natp (boymoo-model::a64-byte address memory))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable boymoo-model::a64-byte))))

(defthm sequence-byte-bound
  (< (boymoo-model::a64-byte address memory) 256)
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable boymoo-model::a64-byte))))

(defthm sequence-read-bytes-integer
  (integerp (boymoo-model::a64-read-bytes count address memory))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (enable boymoo-model::a64-read-bytes))))

(defthm sequence-read-bytes-zero
  (implies (zp count)
           (equal (boymoo-model::a64-read-bytes count address memory) 0))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-read-bytes))))

(defthm sequence-read-bytes-as-sum
  (implies (posp count)
           (equal (boymoo-model::a64-read-bytes count address memory)
                  (+ (boymoo-model::a64-byte address memory)
                     (* 256 (boymoo-model::a64-read-bytes (1- count)
                                                        (1+ (ifix address)) memory)))))
  :hints (("Goal"
           :expand ((boymoo-model::a64-read-bytes count address memory))
           :use ((:instance sequence-logior-of-aligned-and-short
                            (bits 8) (low (boymoo-model::a64-byte address memory))
                            (high (boymoo-model::a64-read-bytes (1- count)
                                                               (1+ (ifix address)) memory))))))
  :rule-classes nil)

(defthm sequence-read-one-byte
  (equal (boymoo-model::a64-read-bytes 1 address memory)
         (boymoo-model::a64-byte address memory))
  :hints (("Goal" :use ((:instance sequence-read-bytes-as-sum (count 1))))))

(defthm sequence-low-byte-of-read
  (implies (posp count)
           (equal (boymoo-model::a64-unsigned
                   8 (boymoo-model::a64-read-bytes count address memory))
                  (boymoo-model::a64-byte address memory)))
  :hints (("Goal"
           :in-theory (e/d (sequence-a64-unsigned-as-mod)
                           (sequence-mod-add-multiple))
           :use (sequence-read-bytes-as-sum
                 (:instance sequence-mod-add-multiple
                            (value (boymoo-model::a64-byte address memory))
                            (divisor 256)
                            (multiple (boymoo-model::a64-read-bytes
                                       (1- count) (1+ (ifix address)) memory)))))))

(local
 (defthm sequence-byte-and-remainder-bits
   (implies (and (unsigned-byte-p 8 byte) (unsigned-byte-p bits rest))
            (unsigned-byte-p (+ 8 bits) (+ byte (* 256 rest))))
   :hints (("Goal" :use ((:instance sequence-powers-add (left 8) (right bits)))))))

(defthm sequence-read-bytes-bits
  (implies (natp count)
           (unsigned-byte-p (* 8 count) (boymoo-model::a64-read-bytes count address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address memory)
                  :in-theory (enable (:induction boymoo-model::a64-read-bytes)))
          ("Subgoal *1/2"
           :use (sequence-read-bytes-as-sum
                 (:instance sequence-byte-and-remainder-bits
                            (bits (* 8 (1- count)))
                            (byte (boymoo-model::a64-byte address memory))
                            (rest (boymoo-model::a64-read-bytes
                                   (1- count) (1+ (ifix address)) memory))))
           :in-theory (disable boymoo-model::a64-read-bytes
                               sequence-byte-and-remainder-bits))))

(defthm sequence-read-bytes-natural
  (natp (boymoo-model::a64-read-bytes count address memory))
  :rule-classes :type-prescription
  :hints (("Goal" :use sequence-read-bytes-bits)))

(defthm sequence-read-word-is-unsigned
  (equal (boymoo-model::a64-unsigned
          64 (boymoo-model::a64-read-bytes 8 address memory))
         (boymoo-model::a64-read-bytes 8 address memory)))

(defthm sequence-byte-after-put
  (equal (boymoo-model::a64-byte address (put-assoc-equal slot value memory))
         (if (equal (boymoo-model::a64-unsigned 64 address) slot)
             (boymoo-model::a64-unsigned 8 value)
           (boymoo-model::a64-byte address memory)))
  :hints (("Goal" :in-theory (enable boymoo-model::a64-byte))))

(defthm sequence-write-bytes-zero
  (implies (zp count)
           (equal (boymoo-model::a64-write-bytes count address value memory) memory))
  :hints (("Goal" :expand ((boymoo-model::a64-write-bytes count address value memory)))))

(defthm sequence-write-one-byte
  (equal (boymoo-model::a64-write-bytes 1 address value memory)
         (put-assoc-equal (boymoo-model::a64-unsigned 64 address)
                          (boymoo-model::a64-unsigned 8 value) memory))
  :hints (("Goal" :expand ((boymoo-model::a64-write-bytes 1 address value memory)))))

(defthm sequence-byte-outside-write
  (implies
   (and (proof-span-p start count) (unsigned-byte-p 64 address)
        (or (< address start) (<= (+ start count) address)))
   (equal (boymoo-model::a64-byte address
                                 (boymoo-model::a64-write-bytes count start value memory))
          (boymoo-model::a64-byte address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count start value memory)
                  :in-theory (enable boymoo-model::a64-write-bytes))))

(defthm sequence-first-byte-of-write
  (implies (and (posp count) (proof-span-p start count))
           (equal (boymoo-model::a64-byte
                   start (boymoo-model::a64-write-bytes count start value memory))
                  (boymoo-model::a64-unsigned 8 value)))
  :hints (("Goal" :expand ((boymoo-model::a64-write-bytes count start value memory))
                  :cases ((equal count 1)))))

(defthm sequence-byte-in-zero-span
  (implies (and (proof-span-p start count) (unsigned-byte-p 64 address)
                (<= start address) (< address (+ start count)))
           (equal (boymoo-model::a64-byte
                   address (boymoo-model::a64-write-bytes count start 0 memory))
                  0))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count start 0 memory)
                  :in-theory (enable (:induction boymoo-model::a64-write-bytes)))
          ("Subgoal *1/2"
           :expand ((boymoo-model::a64-write-bytes count start 0 memory))
           :use ((:instance sequence-first-byte-of-write (value 0)))
           :cases ((equal address start)))))

(local
 (defthm sequence-byte-and-quotient-sum
   (implies (integerp value)
            (equal (+ (mod value 256) (* 256 (floor value 256))) value))
   :hints (("Goal" :in-theory (enable mod)))
   :rule-classes nil))

(local
 (defthm sequence-word-split-at-byte
   (implies (and (natp bits) (integerp value))
            (equal (boymoo-model::a64-unsigned (+ 8 bits) value)
                   (+ (boymoo-model::a64-unsigned 8 value)
                      (* 256 (boymoo-model::a64-unsigned bits (ash value -8))))))
   :hints (("Goal" :in-theory (e/d (sequence-a64-unsigned-as-mod)
                                   (sequence-mod-of-scaled-sum))
                   :use (sequence-byte-and-quotient-sum
                         (:instance sequence-powers-add (left 8) (right bits))
                         (:instance sequence-mod-bounds (divisor 256))
                         (:instance sequence-mod-of-scaled-sum
                                    (scale 256) (modulus (expt 2 bits))
                                    (high (floor value 256)) (low (mod value 256))))))))

(local (in-theory (disable sequence-word-split-at-byte)))

(defthm sequence-read-after-own-write
  (implies (and (integerp value) (proof-span-p address count))
           (equal (boymoo-model::a64-read-bytes
                   count address
                   (boymoo-model::a64-write-bytes count address value memory))
                  (boymoo-model::a64-unsigned (* 8 count) value)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count address value memory)
                  :in-theory (enable (:induction boymoo-model::a64-write-bytes)))
          ("Subgoal *1/2"
           :use ((:instance sequence-read-bytes-as-sum
                            (memory (boymoo-model::a64-write-bytes count address value memory)))
                 (:instance sequence-first-byte-of-write (start address))
                 (:instance sequence-word-split-at-byte (bits (* 8 (1- count)))))
           :expand ((boymoo-model::a64-write-bytes count address value memory))
           :cases ((equal count 1))
           :in-theory (disable sequence-word-split-at-byte))))

(defthm sequence-read-outside-write
  (implies (and (proof-span-p start size) (proof-span-p address count)
                (proof-disjoint-p address (+ address count) start (+ start size)))
           (equal (boymoo-model::a64-read-bytes
                   count address (boymoo-model::a64-write-bytes size start value memory))
                  (boymoo-model::a64-read-bytes count address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address memory)
                  :in-theory (enable (:induction boymoo-model::a64-read-bytes)))
          ("Subgoal *1/2"
           :use (sequence-read-bytes-as-sum
                 (:instance sequence-read-bytes-as-sum
                            (memory (boymoo-model::a64-write-bytes size start value memory))))
           :cases ((equal count 1)))))

(defthm sequence-covered-subspan
  (implies (and (proof-covered-p start count access regions)
                (proof-subspan-p address size start (+ start count)))
           (proof-covered-p address size access regions))
  :hints (("Goal" :induct (proof-covered-p start count access regions)))
  :rule-classes nil)

(defthm sequence-covered-for-read
  (implies (proof-covered-p address size :write regions)
           (proof-covered-p address size :read regions))
  :hints (("Goal" :induct (proof-covered-p address size :write regions))))

(local
 (defthm sequence-byte-agreement-in-entries
   (implies (and (assoc-equal address entries) (<= start address) (< address end)
                 (proof-byte-entries-agree-p entries start end first last))
            (equal (boymoo-model::a64-byte address first)
                   (boymoo-model::a64-byte address last)))
   :hints (("Goal" :induct (assoc-equal address entries)))
   :rule-classes nil))

(local
 (defthm sequence-absent-byte-is-zero
   (implies (and (unsigned-byte-p 64 address) (not (assoc-equal address memory)))
            (equal (boymoo-model::a64-byte address memory) 0))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-byte)
                                   (sequence-unsigned-of-bounded))
                   :use ((:instance sequence-unsigned-of-bounded
                                    (width 64) (value address)))))))

(defthm sequence-agreement-preserves-byte
  (let ((first (boymoo-model::a64-memory (proof-world-machine before)))
        (last (boymoo-model::a64-memory (proof-world-machine after))))
    (implies (and (proof-memory-span-agrees-p start end before after)
                  (unsigned-byte-p 64 address) (<= start address) (< address end))
             (equal (boymoo-model::a64-byte address first)
                    (boymoo-model::a64-byte address last))))
  :hints
  (("Goal"
    :use
    ((:instance sequence-byte-agreement-in-entries
                (entries (boymoo-model::a64-memory (proof-world-machine before)))
                (first (boymoo-model::a64-memory (proof-world-machine before)))
                (last (boymoo-model::a64-memory (proof-world-machine after))))
     (:instance sequence-byte-agreement-in-entries
                (entries (boymoo-model::a64-memory (proof-world-machine after)))
                (first (boymoo-model::a64-memory (proof-world-machine before)))
                (last (boymoo-model::a64-memory (proof-world-machine after)))))))
  :rule-classes nil)

(defthm sequence-agreement-preserves-load
  (implies (and (proof-memory-span-agrees-p start end before after)
                (proof-subspan-p address count start end))
           (equal (boymoo-model::a64-load count address (proof-world-machine before))
                  (boymoo-model::a64-load count address (proof-world-machine after))))
  :hints
  (("Goal" :induct (boymoo-model::a64-read-bytes
                    count address (boymoo-model::a64-memory (proof-world-machine before)))
           :in-theory (e/d ((:induction boymoo-model::a64-read-bytes))
                           (proof-memory-span-agrees-p proof-world-machine)))
   ("Subgoal *1/2"
    :use (sequence-agreement-preserves-byte
          (:instance sequence-read-bytes-as-sum
                     (memory (boymoo-model::a64-memory (proof-world-machine before))))
          (:instance sequence-read-bytes-as-sum
                     (memory (boymoo-model::a64-memory (proof-world-machine after)))))
    :cases ((equal count 1))))
  :rule-classes nil)
