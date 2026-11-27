(in-package "BOYMOO-PROOFS")

(include-book "one-limb-loop")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable mod ash proof-world-machine boymoo-model::a64-memory
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(local
 (defthm division-agreement-entries-at-key
   (implies (and (proof-byte-entries-agree-p entries start end first last)
                 (assoc-equal address entries) (<= start address) (< address end))
            (equal (boymoo-model::a64-byte address first)
                   (boymoo-model::a64-byte address last)))
   :hints (("Goal" :induct (assoc-equal address entries)
                   :in-theory (disable boymoo-model::a64-byte)))
   :rule-classes nil))

(defthm division-span-agreement-covers-byte
  (implies (and (proof-memory-span-agrees-p start end before after)
                (unsigned-byte-p 64 address) (<= start address) (< address end))
           (equal (boymoo-model::a64-byte
                   address (boymoo-model::a64-memory (proof-world-machine before)))
                  (boymoo-model::a64-byte
                   address (boymoo-model::a64-memory (proof-world-machine after)))))
  :hints (("Goal"
           :use ((:instance division-agreement-entries-at-key
                            (entries (boymoo-model::a64-memory (proof-world-machine before)))
                            (first (boymoo-model::a64-memory (proof-world-machine before)))
                            (last (boymoo-model::a64-memory (proof-world-machine after))))
                 (:instance division-agreement-entries-at-key
                            (entries (boymoo-model::a64-memory (proof-world-machine after)))
                            (first (boymoo-model::a64-memory (proof-world-machine before)))
                            (last (boymoo-model::a64-memory (proof-world-machine after)))))
           :in-theory (disable proof-byte-entries-agree-p)))
  :rule-classes nil)

(defthm division-read-after-span-agreement
  (implies (and (proof-subspan-p address count start end)
                (proof-memory-span-agrees-p start end before after))
           (equal (boymoo-model::a64-load count address (proof-world-machine after))
                  (boymoo-model::a64-load count address (proof-world-machine before))))
  :hints (("Goal"
           :induct (boymoo-model::a64-read-bytes count address memory)
           :in-theory (disable boymoo-model::a64-byte proof-memory-span-agrees-p))
          ("Subgoal *1/2"
           :use (:instance division-span-agreement-covers-byte)
           :cases ((equal count 1))
           :expand ((boymoo-model::a64-read-bytes
                     count address (boymoo-model::a64-memory (proof-world-machine before)))
                    (boymoo-model::a64-read-bytes
                     count address (boymoo-model::a64-memory (proof-world-machine after))))))
  :rule-classes nil)

(defthm division-limbs-after-span-agreement
  (implies (and (natp count) (proof-subspan-p address (* 8 count) start end)
                (proof-memory-span-agrees-p start end before after))
           (equal (division-read-limbs count address (proof-world-machine after))
                  (division-read-limbs count address (proof-world-machine before))))
  :hints (("Goal" :induct (division-read-limbs count address machine)
                  :in-theory (disable boymoo-model::a64-load proof-memory-span-agrees-p))
          ("Subgoal *1/2"
           :use (:instance division-read-after-span-agreement (count 8))
           :cases ((equal count 1))
           :expand ((division-read-limbs count address (proof-world-machine after))
                    (division-read-limbs count address (proof-world-machine before)))))
  :rule-classes nil)

(defun division-view-bytes (count)
  (+ 16 (* 8 count)))

(local
 (defthm division-view-read-zero-limbs
   (equal (division-read-limbs 0 address machine) nil)
   :hints (("Goal" :expand ((division-read-limbs 0 address machine))))))

(defthm division-view-value-determined-by-words
   (let ((first (proof-world-machine before))
         (last (proof-world-machine after)))
     (implies (and (proof-integer-view-p value address count before)
                   (equal (proof-load-word address last) (proof-load-word address first))
                   (equal (proof-load-word (+ 8 address) last) (proof-load-word (+ 8 address) first))
                   (equal (division-read-limbs count (+ 16 address) last)
                          (division-read-limbs count (+ 16 address) first)))
              (proof-integer-view-p value address count after)))
   :hints (("Goal"
            :use ((:instance division-view-header-byte-count)
                  (:instance division-read-limbs-normalized
                             (address (+ 16 address)) (machine (proof-world-machine before)))
                  (:instance division-read-limbs-normalized
                             (address (+ 16 address)) (machine (proof-world-machine after)))
                  (:instance division-read-limbs-view-magnitude
                             (address (+ 16 address)) (machine (proof-world-machine before)))
                  (:instance division-read-limbs-view-magnitude
                             (address (+ 16 address)) (machine (proof-world-machine after))))
            :in-theory (disable proof-header-size proof-load-word proof-limb-magnitude
                                proof-limbs-p division-read-limbs division-read-limbs-normalized)
            :do-not-induct t))
  :rule-classes nil)

(defthm division-integer-view-after-span-agreement
  (implies (and (proof-integer-view-p value address count before)
                (proof-subspan-p address (division-view-bytes count) start end)
                (proof-memory-span-agrees-p start end before after))
           (proof-integer-view-p value address count after))
  :hints (("Goal"
           :cases ((posp count))
           :use ((:instance division-view-value-determined-by-words)
                 (:instance division-read-after-span-agreement (count 8))
                 (:instance division-read-after-span-agreement (count 8) (address (+ 8 address)))
                 (:instance division-limbs-after-span-agreement (address (+ 16 address))))
           :in-theory (disable proof-integer-view boymoo-model::a64-load
                               proof-memory-span-agrees-p division-read-limbs)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-integer-view-after-equal-memory
  (implies (and (proof-integer-view-p value address count before)
                (equal (boymoo-model::a64-memory (proof-world-machine after))
                       (boymoo-model::a64-memory (proof-world-machine before))))
           (proof-integer-view-p value address count after))
  :hints (("Goal"
           :use ((:instance division-view-value-determined-by-words)
                 (:instance division-read-limbs-from-same-memory
                            (address (+ address 16)) (first (proof-world-machine before))
                            (second (proof-world-machine after))))
           :in-theory (disable proof-integer-view division-read-limbs boymoo-model::a64-read-bytes)
           :do-not-induct t))
  :rule-classes nil)
