(in-package "BOYMOO-PROOFS")

(include-book "actions")

(logic)
(set-verify-guards-eagerness 0)

(local (in-theory (disable boymoo-model::a64-unsigned
                          (:definition ash) (:definition acl2::binary-logior))))

(local
 (defthm collection-assoc-after-put
   (implies (alistp alist)
            (equal (assoc-equal address (put-assoc-equal key value alist))
                   (if (equal address key) (cons key value)
                     (assoc-equal address alist))))))

(local
 (defthm collection-put-keeps-memory-alist
   (implies (alistp memory)
            (alistp (put-assoc-equal address value memory)))))

(local (in-theory (disable assoc-equal put-assoc-equal)))

(defthm collection-store-bytes-keeps-memory-alist
  (implies (alistp memory)
           (alistp (boymoo-model::a64-write-bytes count start value memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count start value memory))))

(defthm collection-byte-store-preserves-outside-address
  (implies (and (alistp memory) (unsigned-byte-p 64 address)
                (natp start) (natp count)
                (<= (+ start count) (expt 2 64))
                (or (< address start) (<= (+ start count) address)))
           (equal (assoc-equal address
                               (boymoo-model::a64-write-bytes count start value memory))
                  (assoc-equal address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count start value memory))))

(local (in-theory (disable boymoo-model::a64-write-bytes)))

(defthm collection-read-first-byte-of-store
  (implies (and (alistp memory) (natp start) (posp count)
                (<= (+ start count) (expt 2 64)))
           (equal (boymoo-model::a64-byte
                   start (boymoo-model::a64-write-bytes count start value memory))
                  (boymoo-model::a64-unsigned 8 value)))
  :hints (("Goal" :expand ((boymoo-model::a64-write-bytes count start value memory)))))

(defthm collection-disjoint-byte-store-preserves-read
  (implies (and (alistp memory)
                (natp address) (natp width) (<= (+ address width) (expt 2 64))
                (natp start) (natp count) (<= (+ start count) (expt 2 64))
                (proof-disjoint-p address (+ address width) start (+ start count)))
           (equal (boymoo-model::a64-read-bytes
                   width address (boymoo-model::a64-write-bytes count start value memory))
                  (boymoo-model::a64-read-bytes width address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes width address memory))))

(defthm collection-disjoint-word-store-preserves-word
  (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                (proof-span-p address 8) (proof-span-p start 8)
                (proof-disjoint-p address (+ address 8) start (+ start 8)))
           (equal (collection-read-word address (collection-write-word start value world))
                  (collection-read-word address world)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-read-bytes))))

(local
 (defthm collection-byte-combines-with-remaining-read
   (implies (and (posp count) (unsigned-byte-p 8 low)
                 (unsigned-byte-p (* 8 (1- count)) high))
            (unsigned-byte-p (* 8 count) (logior low (ash high 8))))
   :hints (("Goal" :use ((:instance collection-width-of-byte-and-shifted-high-bits
                                    (width (* 8 (1- count)))))
                   :in-theory (disable unsigned-byte-p
                                       collection-width-of-byte-and-shifted-high-bits)))))

(defthm collection-byte-read-has-requested-width
  (implies (natp count)
           (unsigned-byte-p (* 8 count) (boymoo-model::a64-read-bytes count address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address memory)
                  :in-theory (disable unsigned-byte-p))))

(defthm collection-loaded-word-is-unsigned
  (unsigned-byte-p 64 (collection-read-word address world))
  :hints (("Goal" :use ((:instance collection-byte-read-has-requested-width
                                   (count 8)
                                   (memory (boymoo-model::a64-memory
                                            (proof-world-machine world)))))
                  :in-theory (disable unsigned-byte-p boymoo-model::a64-read-bytes))))

(defthm collection-loaded-word-is-natural
  (natp (collection-read-word address world))
  :rule-classes :type-prescription
  :hints (("Goal" :use collection-loaded-word-is-unsigned
                  :in-theory (disable collection-read-word collection-loaded-word-is-unsigned))))

(defthm collection-loaded-word-bounds
  (and (<= 0 (collection-read-word address world))
       (< (collection-read-word address world) (expt 2 64)))
  :rule-classes :linear
  :hints (("Goal" :use collection-loaded-word-is-unsigned
                  :in-theory (disable collection-read-word collection-loaded-word-is-unsigned))))

(local
 (defthm collection-byte-outside-store-is-unchanged
   (implies (and (alistp memory) (unsigned-byte-p 64 address)
                 (natp start) (natp count) (<= (+ start count) (expt 2 64))
                 (or (< address start) (<= (+ start count) address)))
            (equal (boymoo-model::a64-byte
                    address (boymoo-model::a64-write-bytes count start value memory))
                   (boymoo-model::a64-byte address memory)))))

(local
 (defthm collection-byte-after-inserting-its-key
   (implies (and (alistp memory) (unsigned-byte-p 64 address))
            (equal (boymoo-model::a64-byte address (put-assoc-equal address value memory))
                   (boymoo-model::a64-unsigned 8 value)))))

(local (in-theory (disable boymoo-model::a64-byte)))

(defthm collection-read-of-same-byte-span
  (implies (and (alistp memory) (natp start) (natp count) (integerp value)
                (<= (+ start count) (expt 2 64)))
           (equal (boymoo-model::a64-read-bytes
                   count start (boymoo-model::a64-write-bytes count start value memory))
                  (boymoo-model::a64-unsigned (* 8 count) value)))
  :hints (("Goal"
           :induct (boymoo-model::a64-write-bytes count start value memory)
           :in-theory (enable (:induction boymoo-model::a64-write-bytes))
           :expand ((boymoo-model::a64-write-bytes count start value memory)))))

(defthm collection-read-of-same-word
  (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                (proof-span-p address 8) (unsigned-byte-p 64 value))
           (equal (collection-read-word address (collection-write-word address value world))
                  value))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-read-bytes))))

(defthm collection-word-store-keeps-memory-alist
  (implies (alistp (boymoo-model::a64-memory (proof-world-machine world)))
           (alistp (boymoo-model::a64-memory
                    (proof-world-machine (collection-write-word address value world))))))
