(in-package "BOYMOO-PROOFS")

(include-book "retirement")
(include-book "frame-protection")

(logic)
(set-verify-guards-eagerness 0)

(local
 (defthm collection-region-disjoint-from-subinterval
   (implies (and (proof-region-disjoint-p start end regions)
                 (<= start lower) (<= upper end))
            (proof-region-disjoint-p lower upper regions))
   :hints (("Goal" :induct (proof-region-disjoint-p start end regions)))))

(local
 (defthm collection-region-removal-keeps-separation
   (implies (proof-region-disjoint-p start end regions)
            (proof-region-disjoint-p start end (proof-remove-region-span base size regions)))
   :hints (("Goal" :induct (proof-remove-region-span base size regions)))))

(defthm collection-unmapping-keeps-regions-well-formed
  (implies (proof-regions-p regions)
           (proof-regions-p (proof-remove-region-span base size regions)))
  :hints (("Goal" :induct (proof-remove-region-span base size regions))))

(local
 (defthm collection-unmap-keeps-executable-coverage
   (equal (proof-covered-p address width :execute (proof-remove-region-span base size regions))
          (proof-covered-p address width :execute regions))
   :hints (("Goal" :induct (proof-remove-region-span base size regions)
                   :in-theory (disable proof-subspan-p)))))

(local
 (defthm collection-unmap-keeps-disjoint-byte
   (implies (and (alistp memory) (unsigned-byte-p 64 address)
                 (or (< address base) (<= end address)))
            (equal (boymoo-model::a64-byte address (proof-clear-memory base end memory))
                   (boymoo-model::a64-byte address memory)))
   :hints (("Goal" :in-theory (e/d (boymoo-model::a64-byte) (boymoo-model::a64-unsigned))))))

(local
 (defthm collection-unmap-keeps-disjoint-fetch-bytes
   (implies (and (alistp memory) (proof-span-p pc width)
                 (proof-disjoint-p pc (+ pc width) base end))
            (equal (boymoo-model::a64-read-bytes width pc (proof-clear-memory base end memory))
                   (boymoo-model::a64-read-bytes width pc memory)))
   :hints (("Goal"
            :induct (boymoo-model::a64-read-bytes width pc memory)
            :in-theory (disable proof-clear-memory boymoo-model::a64-byte
                                boymoo-model::a64-unsigned (:definition ash)
                                (:definition acl2::binary-logior))))))

(defthm collection-clear-keeps-memory-alist
  (implies (alistp memory)
           (alistp (proof-clear-memory base end memory)))
  :hints (("Goal" :induct (proof-clear-memory base end memory))))

(local
 (in-theory (disable proof-clear-memory proof-covered-p proof-regions-p
                     proof-decode boymoo-model::a64-read-bytes boymoo-model::a64-unsigned
                     boymoo-model::a64-load (:definition ash)
                     (:definition acl2::binary-logior))))

(defthm collection-unmap-keeps-instruction-placement
  (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                (proof-regions-p (proof-world-regions world))
                (proof-covered-p base size :write (proof-world-regions world)))
           (equal (proof-instruction-at-p instruction pc
                                          (collection-relinquish-range t base size world))
                  (proof-instruction-at-p instruction pc world)))
  :hints (("Goal"
           :use ((:instance collection-executable-and-writable-spans-are-disjoint
                            (regions (proof-world-regions world))
                            (address base) (write-width size) (fetch-width 4))
                 (:instance collection-covered-address-is-a-span
                            (regions (proof-world-regions world))
                            (address pc) (width 4) (access :execute)))
           :in-theory (e/d (boymoo-model::a64-load)
                             (collection-covered-address-is-a-span proof-remove-region-span
                              collection-unsigned-width)))))
