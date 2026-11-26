(in-package "BOYMOO-PROOFS")

(include-book "bitfields")
(include-book "normalization")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable ash floor mod acl2::binary-logior proof-decode
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(local
 (defthm division-memory-assoc-after-put
   (equal (assoc-equal key (put-assoc-equal address datum memory))
          (if (equal key address) (cons address datum) (assoc-equal key memory)))
   :hints (("Goal" :induct (put-assoc-equal address datum memory)))))

(local
 (defthm division-byte-after-put
   (implies (and (unsigned-byte-p 64 address) (unsigned-byte-p 64 query)
                 (unsigned-byte-p 8 byte))
            (equal (boymoo-model::a64-byte query (put-assoc-equal address byte memory))
                   (if (equal query address) byte (boymoo-model::a64-byte query memory))))))

(defthm division-byte-after-disjoint-write
  (implies (and (proof-span-p address count) (unsigned-byte-p 64 query)
                (or (< query address) (<= (+ address count) query)))
           (equal (boymoo-model::a64-byte
                   query (boymoo-model::a64-write-bytes count address value memory))
                  (boymoo-model::a64-byte query memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count address value memory)
                  :in-theory (disable boymoo-model::a64-byte))
          ("Subgoal *1/2"
           :use (:instance division-a64-unsigned-bounded (width 8) (x value))
           :in-theory (disable division-a64-unsigned-bounded))))

(defthm division-read-after-disjoint-write
  (implies (and (proof-span-p address count) (proof-span-p query size)
                (proof-disjoint-p address (+ address count) query (+ query size)))
           (equal (boymoo-model::a64-read-bytes
                   size query (boymoo-model::a64-write-bytes count address value memory))
                  (boymoo-model::a64-read-bytes size query memory)))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes size query memory)
                  :in-theory (disable boymoo-model::a64-write-bytes boymoo-model::a64-byte))
          ("Subgoal *1/2"
           :expand ((boymoo-model::a64-read-bytes
                     size query (boymoo-model::a64-write-bytes count address value memory))))))

(defthm division-load-after-disjoint-store
  (implies (and (proof-span-p address count) (proof-span-p query size)
                (proof-disjoint-p address (+ address count) query (+ query size)))
           (equal (boymoo-model::a64-load size query
                                         (boymoo-model::a64-store count address value machine))
                  (boymoo-model::a64-load size query machine)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-read-bytes
                                      boymoo-model::a64-write-bytes))))

(defthm division-covered-span
  (implies (proof-covered-p address size access regions)
           (proof-span-p address size))
  :hints (("Goal" :induct (proof-covered-p address size access regions)))
  :rule-classes nil)

(defthm division-instruction-at-after-disjoint-write
  (implies (and (equal (proof-world-regions before) (proof-world-regions after))
                (equal (boymoo-model::a64-memory (proof-world-machine after))
                       (boymoo-model::a64-write-bytes
                        count address value (boymoo-model::a64-memory (proof-world-machine before))))
                (proof-span-p address count)
                (proof-disjoint-p address (+ address count) pc (+ pc 4)))
           (equal (proof-instruction-at-p instruction pc after)
                  (proof-instruction-at-p instruction pc before)))
  :hints (("Goal"
           :use (:instance division-covered-span (address pc) (size 4)
                           (access :execute) (regions (proof-world-regions after)))
           :in-theory (disable boymoo-model::a64-read-bytes boymoo-model::a64-write-bytes
                               boymoo-model::a64-memory proof-world-machine proof-world-regions)))
  :rule-classes nil)

(defthm division-instructions-at-after-disjoint-write
  (implies (and (equal (proof-world-regions before) (proof-world-regions after))
                (equal (boymoo-model::a64-memory (proof-world-machine after))
                       (boymoo-model::a64-write-bytes
                        count address value (boymoo-model::a64-memory (proof-world-machine before))))
                (proof-span-p address count)
                (proof-disjoint-p address (+ address count)
                                  pc (+ pc (* 4 (len instructions)))))
           (equal (proof-instructions-at-p instructions pc after)
                  (proof-instructions-at-p instructions pc before)))
  :hints (("Goal" :induct (proof-instructions-at-p instructions pc before)
                  :in-theory (disable proof-instruction-at-p boymoo-model::a64-write-bytes
                                      boymoo-model::a64-memory proof-world-machine proof-world-regions))
          ("Subgoal *1/2"
           :use (:instance division-instruction-at-after-disjoint-write
                           (instruction (car instructions)))
           :expand ((proof-instructions-at-p instructions pc after)))
          ("Subgoal *1/3"
           :use (:instance division-instruction-at-after-disjoint-write
                           (instruction (car instructions)))
           :expand ((proof-instructions-at-p instructions pc after))))
  :rule-classes nil)

(local
 (defthm division-empty-write
   (equal (boymoo-model::a64-write-bytes 0 address value memory) memory)
   :hints (("Goal" :expand ((boymoo-model::a64-write-bytes 0 address value memory))))))

(local
 (defthm division-byte-at-write-start
   (implies (and (proof-span-p address count) (posp count)
                 (unsigned-byte-p 8 byte))
            (equal (boymoo-model::a64-byte
                    address
                    (boymoo-model::a64-write-bytes
                     (1- count) (1+ address) tail (put-assoc-equal address byte memory)))
                   byte))
   :hints (("Goal" :cases ((equal count 1))
                   :use (:instance division-byte-after-disjoint-write
                                   (query address) (address (1+ address)) (count (1- count))
                                   (value tail) (memory (put-assoc-equal address byte memory)))
                   :in-theory (disable division-byte-after-disjoint-write
                                       boymoo-model::a64-write-bytes boymoo-model::a64-byte)))))

(local
 (defthm division-tail-fits-in-remaining-bytes
   (implies (and (posp count) (unsigned-byte-p (* 8 count) value))
            (unsigned-byte-p (* 8 (1- count)) (ash value -8)))
   :hints (("Goal"
            :use ((:instance division-power-of-two-sum (left 8) (right (* 8 (1- count))))
                  (:instance division-ash-right (width 8) (x value))
                  (:instance division-floor-bounds (a value) (b 256)))
            :in-theory (disable division-ash-right expt)))))

(defthm division-read-one-byte
  (equal (boymoo-model::a64-read-bytes 1 address memory)
         (boymoo-model::a64-byte address memory))
  :hints (("Goal"
           :use ((:instance division-logior-of-disjoint-fields
                            (high 0) (width 8) (low (boymoo-model::a64-byte address memory)))
                 (:instance division-a64-unsigned-bounded
                            (width 8)
                            (x (cdr (assoc-equal (boymoo-model::a64-unsigned 64 address) memory)))))
           :expand ((boymoo-model::a64-read-bytes 1 address memory)
                    (boymoo-model::a64-read-bytes 0 (1+ (ifix address)) memory)))))

(defthm division-read-after-fitting-write
  (implies (and (proof-span-p address count) (unsigned-byte-p (* 8 count) value))
           (equal (boymoo-model::a64-read-bytes
                   count address (boymoo-model::a64-write-bytes count address value memory))
                  value))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count address value memory)
                  :in-theory (disable boymoo-model::a64-byte))
          ("Subgoal *1/2"
           :expand ((boymoo-model::a64-read-bytes
                     count address (boymoo-model::a64-write-bytes count address value memory)))
           :use ((:instance division-tail-fits-in-remaining-bytes)
                 (:instance division-a64-unsigned-bounded (width 8) (x value))
                 (:instance division-logior-of-disjoint-fields
                            (high (ash value -8)) (width 8)
                            (low (boymoo-model::a64-unsigned 8 value)))
                 (:instance division-ash-right (width 8) (x value))
                 (:instance division-ash-left (width 8) (x (ash value -8)))
                 (:instance division-a64-unsigned-is-remainder (width 8) (x value))
                 (:instance division-floor-mod-identity (a value) (b 256)))
           :in-theory (disable division-a64-unsigned-bounded division-ash-right division-ash-left
                               division-floor-mod-identity boymoo-model::a64-byte))
          ("Subgoal *1/2.1" :cases ((equal count 1)))))

(defthm division-load-after-fitting-store
  (implies (and (proof-span-p address count) (unsigned-byte-p (* 8 count) value))
           (equal (boymoo-model::a64-load
                   count address (boymoo-model::a64-store count address value machine))
                  value))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-read-bytes
                                      boymoo-model::a64-write-bytes))))

(defthm division-byte-value-range
  (unsigned-byte-p 8 (boymoo-model::a64-byte address memory))
  :hints (("Goal" :use (:instance division-a64-unsigned-bounded
                                  (width 8)
                                  (x (cdr (assoc-equal (boymoo-model::a64-unsigned 64 address) memory)))))))

(local
 (defthm division-read-bytes-integer
   (integerp (boymoo-model::a64-read-bytes count address memory))
   :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address memory)))
   :rule-classes :type-prescription))

(defthm division-read-bytes-little-endian
  (implies (posp count)
           (equal (boymoo-model::a64-read-bytes count address memory)
                  (+ (boymoo-model::a64-byte address memory)
                     (* 256 (boymoo-model::a64-read-bytes
                             (1- count) (1+ (ifix address)) memory)))))
  :hints (("Goal"
           :expand ((boymoo-model::a64-read-bytes count address memory))
           :use ((:instance division-logior-of-disjoint-fields
                            (width 8) (low (boymoo-model::a64-byte address memory))
                            (high (boymoo-model::a64-read-bytes
                                   (1- count) (1+ (ifix address)) memory)))
                 (:instance division-ash-left (width 8)
                            (x (boymoo-model::a64-read-bytes
                                (1- count) (1+ (ifix address)) memory))))
           :in-theory (disable boymoo-model::a64-byte boymoo-model::a64-read-bytes
                               division-ash-left)))
  :rule-classes nil)

(defthm division-read-bytes-value-range
  (implies (natp count)
           (unsigned-byte-p (* 8 count) (boymoo-model::a64-read-bytes count address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address memory)
                  :in-theory (disable boymoo-model::a64-byte expt))
          ("Subgoal *1/2"
           :use ((:instance division-read-bytes-little-endian)
                 (:instance division-byte-value-range)
                 (:instance division-power-of-two-sum (left 8) (right (* 8 (1- count)))))
           :in-theory (disable expt boymoo-model::a64-byte division-byte-value-range
                               boymoo-model::a64-read-bytes)))
  :rule-classes nil)

(defun division-decoded-word-at-p (instruction address memory regions)
  (and (equal (mod address 4) 0)
       (proof-covered-p address 4 :execute regions)
       (equal (proof-decode (boymoo-model::a64-read-bytes 4 address memory))
              instruction)))

(defthmd division-instruction-at-depends-on-bytes
  (equal (proof-instruction-at-p instruction address world)
         (division-decoded-word-at-p instruction address
                                    (boymoo-model::a64-memory (proof-world-machine world))
                                    (proof-world-regions world)))
  :hints (("Goal" :in-theory (disable boymoo-model::a64-read-bytes
                                      boymoo-model::a64-memory proof-world-machine proof-world-regions))))
