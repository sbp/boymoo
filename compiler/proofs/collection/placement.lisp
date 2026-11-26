(in-package "BOYMOO-PROOFS")

(include-book "memory")
(include-book "segments")

(logic)
(set-verify-guards-eagerness 0)

(defthm collection-covered-subspan
  (implies (and (proof-covered-p base extent access regions)
                (proof-subspan-p address width base (+ base extent)))
           (proof-covered-p address width access regions))
  :rule-classes nil
  :hints (("Goal" :induct (proof-covered-p base extent access regions))))

(defthm collection-writable-span-is-readable
  (implies (proof-covered-p address size :write regions)
           (proof-covered-p address size :read regions))
  :hints (("Goal" :induct (proof-covered-p address size :write regions)
                  :in-theory (disable proof-subspan-p))))

(local
 (defthm collection-covered-span-respects-region-separation
   (implies (and (proof-region-disjoint-p base end regions)
                 (proof-covered-p address size access regions))
            (proof-disjoint-p base end address (+ address size)))
   :hints (("Goal" :induct (proof-covered-p address size access regions)))))

(defthm collection-executable-and-writable-spans-are-disjoint
  (implies (and (proof-regions-p regions)
                (proof-covered-p pc fetch-width :execute regions)
                (proof-covered-p address write-width :write regions))
           (proof-disjoint-p pc (+ pc fetch-width) address (+ address write-width)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-regions-p regions)
                  :in-theory (disable collection-covered-span-respects-region-separation))
          (and stable-under-simplificationp
               '(:use ((:instance collection-covered-span-respects-region-separation
                                  (base (caar regions)) (end (cadar regions))
                                  (regions (cdr regions)) (size write-width)
                                  (access :write))
                       (:instance collection-covered-span-respects-region-separation
                                  (base (caar regions)) (end (cadar regions))
                                  (regions (cdr regions)) (address pc)
                                  (size fetch-width) (access :execute)))))))

(defthm collection-covered-address-is-a-span
  (implies (proof-covered-p address width access regions)
           (proof-span-p address width))
  :hints (("Goal" :induct (proof-covered-p address width access regions)
                  :in-theory (disable proof-span-p))))

(local
 (in-theory (disable boymoo-model::a64-unsigned
                     boymoo-model::a64-read-bytes boymoo-model::a64-write-bytes
                     (:definition ash) (:definition acl2::binary-logand)
                     (:definition acl2::binary-logior))))

(defthm collection-regions-after-register-change
  (equal (proof-world-regions (collection-write-register register value world))
         (proof-world-regions world)))

(defthm collection-regions-after-pc-change
  (equal (proof-world-regions (collection-write-pc address world))
         (proof-world-regions world)))

(defthm collection-regions-after-flags-change
  (equal (proof-world-regions (collection-write-flags flags world))
         (proof-world-regions world)))

(defthm collection-regions-after-word-store
  (equal (proof-world-regions (collection-write-word address value world))
         (proof-world-regions world)))

(defthm collection-regions-after-sp-change
  (equal (proof-world-regions (collection-write-sp address world))
         (proof-world-regions world)))

(local
 (in-theory (disable collection-write-register collection-write-pc
                     collection-write-flags collection-write-sp collection-write-word
                     proof-world-regions proof-world-machine proof-decode
                     proof-covered-p proof-span-p proof-regions-p
                     boymoo-model::a64-read-bytes boymoo-model::a64-write-bytes)))

(defthm collection-instruction-at-after-register-change
  (equal (proof-instruction-at-p instruction pc
                                 (collection-write-register register value world))
         (proof-instruction-at-p instruction pc world)))

(defthm collection-instruction-at-after-pc-change
  (equal (proof-instruction-at-p instruction pc
                                 (collection-write-pc address world))
         (proof-instruction-at-p instruction pc world)))

(defthm collection-instruction-at-after-flags-change
  (equal (proof-instruction-at-p instruction pc
                                 (collection-write-flags flags world))
         (proof-instruction-at-p instruction pc world)))

(defthm collection-instruction-at-after-sp-change
  (equal (proof-instruction-at-p instruction pc
                                 (collection-write-sp address world))
         (proof-instruction-at-p instruction pc world)))

(defthm collection-instruction-at-after-writable-word-store
  (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                (proof-regions-p (proof-world-regions world))
                (proof-covered-p address 8 :write (proof-world-regions world)))
           (equal (proof-instruction-at-p instruction pc
                                          (collection-write-word address value world))
                  (proof-instruction-at-p instruction pc world)))
  :hints (("Goal"
           :use ((:instance collection-executable-and-writable-spans-are-disjoint
                            (regions (proof-world-regions world))
                            (fetch-width 4) (write-width 8))
                 (:instance collection-covered-address-is-a-span
                            (address pc) (width 4) (access :execute)
                            (regions (proof-world-regions world)))
                 (:instance collection-covered-address-is-a-span
                            (width 8) (access :write)
                            (regions (proof-world-regions world)))
                 (:instance collection-disjoint-byte-store-preserves-read
                            (address pc) (width 4) (start address) (count 8)
                            (memory (boymoo-model::a64-memory (proof-world-machine world)))))
           :in-theory (e/d (proof-span-p)
                           (collection-disjoint-byte-store-preserves-read
                            collection-covered-address-is-a-span
                            boymoo-model::a64-memory)))))
