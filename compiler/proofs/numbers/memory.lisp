(in-package "BOYMOO-PROOFS")

(include-book "words")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod ash acl2::binary-logand acl2::binary-logior
                     boymoo-model::a64-unsigned
                     acl2::nonnegative-integer-quotient)))

(defthm proof-number-a64-byte-range
  (unsigned-byte-p 8 (boymoo-model::a64-byte address memory))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary
                  (natp (boymoo-model::a64-byte address memory)))
                 (:linear :corollary (< (boymoo-model::a64-byte address memory) 256))))

(local
 (defthm read-bytes-as-sum
   (equal (boymoo-model::a64-read-bytes count address memory)
          (if (zp count)
              0
            (+ (boymoo-model::a64-byte address memory)
               (* 256 (boymoo-model::a64-read-bytes
                       (1- count) (1+ (ifix address)) memory)))))
   :hints (("Goal"
            :use ((:instance proof-number-logior-join (width 8)
                             (low (boymoo-model::a64-byte address memory))
                             (high (boymoo-model::a64-read-bytes
                                    (1- count) (1+ (ifix address)) memory))))
            :expand ((boymoo-model::a64-read-bytes count address memory))
            :in-theory (disable boymoo-model::a64-read-bytes boymoo-model::a64-byte)))
   :rule-classes nil))

(local
 (defthm byte-radix-power
   (implies (natp count) (posp (expt 256 count)))
   :hints (("Goal" :induct (expt 256 count)))
   :rule-classes :type-prescription))

(local
 (defthm read-bytes-bounds
   (and (natp (boymoo-model::a64-read-bytes count address memory))
        (< (boymoo-model::a64-read-bytes count address memory) (expt 256 (nfix count))))
   :hints (("Goal"
            :induct (boymoo-model::a64-read-bytes count address memory)
            :in-theory (disable (:definition boymoo-model::a64-read-bytes)
                                boymoo-model::a64-byte expt))
           ("Subgoal *1/2" :use read-bytes-as-sum :expand ((expt 256 count)))
           ("Subgoal *1/1" :use read-bytes-as-sum))
   :rule-classes nil))

(defthm proof-number-load-word-range
  (unsigned-byte-p 64 (proof-load-word address machine))
  :hints (("Goal"
           :use ((:instance read-bytes-bounds (count 8)
                            (memory (boymoo-model::a64-memory machine))))
           :in-theory (disable boymoo-model::a64-read-bytes)))
  :rule-classes ((:rewrite)
                 (:type-prescription :corollary (natp (proof-load-word address machine)))))

(defthm proof-number-loaded-low-byte
  (equal (proof-header-type (proof-load-word address machine))
         (boymoo-model::a64-load 1 address machine))
  :hints (("Goal"
           :use ((:instance read-bytes-as-sum (count 8)
                            (memory (boymoo-model::a64-memory machine)))
                 (:instance read-bytes-as-sum (count 1)
                            (memory (boymoo-model::a64-memory machine)))
                 (:instance proof-number-a64-unsigned-is-modulo (width 8)
                            (a (boymoo-model::a64-read-bytes
                                8 address (boymoo-model::a64-memory machine))))
                 (:instance proof-number-mod-shift-by-multiple
                            (b 256)
                            (a (boymoo-model::a64-byte address
                                                      (boymoo-model::a64-memory machine)))
                            (times (boymoo-model::a64-read-bytes
                                    7 (1+ (ifix address))
                                    (boymoo-model::a64-memory machine)))))
           :in-theory (enable boymoo-model::a64-load)))
  :rule-classes nil)

(defthm proof-number-assoc-equal-after-put-assoc
  (equal (assoc-equal key (put-assoc-equal stored value entries))
         (if (equal key stored) (cons stored value) (assoc-equal key entries)))
  :hints (("Goal" :induct (put-assoc-equal stored value entries))))

(local
 (defthm byte-after-put-assoc
   (implies (and (unsigned-byte-p 64 address) (unsigned-byte-p 64 dest))
            (equal (boymoo-model::a64-byte address (put-assoc-equal dest value memory))
                   (if (equal address dest)
                       (boymoo-model::a64-unsigned 8 value)
                     (boymoo-model::a64-byte address memory))))))

(local
 (in-theory (disable boymoo-model::a64-byte)))

(defthm proof-number-byte-after-write-outside
  (implies (and (unsigned-byte-p 64 address) (natp dest) (natp count)
                (<= (+ dest count) (expt 2 64))
                (or (< address dest) (<= (+ dest count) address)))
           (equal (boymoo-model::a64-byte
                   address (boymoo-model::a64-write-bytes count dest value memory))
                  (boymoo-model::a64-byte address memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count dest value memory))))

(local
 (defthm first-byte-after-write
   (implies (and (natp dest) (posp count)
                 (<= (+ dest count) (expt 2 64)))
            (equal (boymoo-model::a64-byte
                    dest (boymoo-model::a64-write-bytes count dest value memory))
                   (boymoo-model::a64-unsigned 8 value)))
   :hints (("Goal"
            :expand ((boymoo-model::a64-write-bytes count dest value memory))
            :in-theory (disable boymoo-model::a64-write-bytes)))))

(local
 (defthm write-value-tail-fits
   (implies (and (posp count) (natp value) (< value (expt 256 count)))
            (and (natp (floor value 256))
                 (< (floor value 256) (expt 256 (1- count)))))
   :hints (("Goal"
            :use ((:instance proof-number-positive-divisor-floor-bounds
                             (a value) (b 256)))
            :expand ((expt 256 count))
            :in-theory (disable expt)))
   :rule-classes ((:type-prescription :corollary
                   (implies (natp value) (integerp (floor value 256))))
                  (:linear :corollary
                   (implies (and (posp count) (natp value) (< value (expt 256 count)))
                            (< (floor value 256) (expt 256 (1- count))))))))

(local
 (defthm split-word-at-byte
   (implies (integerp value)
            (equal (+ (boymoo-model::a64-unsigned 8 value) (* 256 (floor value 256)))
                   value))
   :hints (("Goal"
            :use ((:instance proof-number-a64-unsigned-is-modulo (width 8) (a value)))
            :in-theory (enable mod)))
   :rule-classes nil))

(local
 (defthm read-bytes-after-write-at-same-address
   (implies (and (natp dest) (natp count)
                 (<= (+ dest count) (expt 2 64))
                 (natp value) (< value (expt 256 count)))
            (equal (boymoo-model::a64-read-bytes
                    count dest (boymoo-model::a64-write-bytes count dest value memory))
                   value))
   :hints (("Goal"
            :induct (boymoo-model::a64-write-bytes count dest value memory)
            :in-theory (disable boymoo-model::a64-read-bytes expt))
           ("Subgoal *1/2"
            :use (split-word-at-byte
                  (:instance read-bytes-as-sum
                             (address dest)
                             (memory (boymoo-model::a64-write-bytes count dest value memory)))
                  (:instance write-value-tail-fits))
            :in-theory (disable boymoo-model::a64-read-bytes expt))
           ("Subgoal *1/1" :use ((:instance read-bytes-as-sum (address dest)))
                            :in-theory (e/d (expt) (boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(defthm proof-number-load-after-store-at-same-address
  (implies (and (proof-span-p address 8) (unsigned-byte-p 64 value))
           (equal (proof-load-word address (boymoo-model::a64-store 8 address value machine))
                  value))
  :hints (("Goal"
           :use ((:instance read-bytes-after-write-at-same-address
                            (count 8) (dest address) (memory (boymoo-model::a64-memory machine))))
           :in-theory (disable boymoo-model::a64-read-bytes boymoo-model::a64-write-bytes))))

(local
 (defthm read-bytes-after-disjoint-write
   (implies (and (natp address) (natp count)
                 (natp dest) (natp size)
                 (<= (+ address count) (expt 2 64))
                 (<= (+ dest size) (expt 2 64))
                 (proof-disjoint-p address (+ address count) dest (+ dest size)))
            (equal (boymoo-model::a64-read-bytes
                    count address (boymoo-model::a64-write-bytes size dest value memory))
                   (boymoo-model::a64-read-bytes count address memory)))
   :hints (("Goal"
            :induct (boymoo-model::a64-read-bytes count address memory)
            :in-theory (disable (:definition boymoo-model::a64-read-bytes)
                                boymoo-model::a64-write-bytes))
           ("Subgoal *1/2"
            :use (read-bytes-as-sum
                  (:instance read-bytes-as-sum
                             (memory (boymoo-model::a64-write-bytes size dest value memory)))))
           ("Subgoal *1/1"
            :use (read-bytes-as-sum
                  (:instance read-bytes-as-sum
                             (memory (boymoo-model::a64-write-bytes size dest value memory))))))
   :rule-classes nil))

(defthm proof-number-load-after-disjoint-store
  (implies (and (proof-span-p address 8) (proof-span-p dest size)
                (proof-disjoint-p address (+ address 8) dest (+ dest size)))
           (equal (proof-load-word address (boymoo-model::a64-store size dest value machine))
                  (proof-load-word address machine)))
  :hints (("Goal"
           :use ((:instance read-bytes-after-disjoint-write (count 8)
                            (memory (boymoo-model::a64-memory machine))))
           :in-theory (disable boymoo-model::a64-read-bytes boymoo-model::a64-write-bytes))))
