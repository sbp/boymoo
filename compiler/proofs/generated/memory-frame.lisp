(in-package "BOYMOO-PROOFS")

(include-book "copy")
(include-book "views")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-machine proof-load-word proof-span-p proof-disjoint-p
                    generated-load-word generated-store-word generated-copy-words
                    boymoo-model::a64-load boymoo-model::a64-store boymoo-model::a64-unsigned
                    boymoo-model::a64-byte boymoo-model::a64-memory
                    boymoo-model::a64-read-bytes expt))

; Bytes absent from both memory maps are zero. Only unsigned word addresses
; can be keys of byte lookups in the A64 model.
(defun generated-outside-entries-p (entries start end first last)
  (if (atom entries)
      t
    (let ((address (caar entries)))
      (and (if (and (unsigned-byte-p 64 address)
                    (or (< address start) (<= end address)))
               (equal (boymoo-model::a64-byte address first)
                      (boymoo-model::a64-byte address last))
             t)
           (generated-outside-entries-p (cdr entries) start end first last)))))

(defund generated-memory-outside-p (start end before after)
  (let ((first (boymoo-model::a64-memory before))
        (last (boymoo-model::a64-memory after)))
    (and (generated-outside-entries-p first start end first last)
         (generated-outside-entries-p last start end first last))))

(defcong generated-memory-equiv equal (generated-memory-outside-p start end before after) 3
  :hints (("Goal" :in-theory (enable generated-memory-outside-p generated-memory-equiv))))

(defcong generated-memory-equiv equal (generated-memory-outside-p start end before after) 4
  :hints (("Goal" :in-theory (enable generated-memory-outside-p generated-memory-equiv))))

(local
 (defthm generated-outside-entries-symmetric
   (equal (generated-outside-entries-p entries start end last first)
          (generated-outside-entries-p entries start end first last))
   :hints (("Goal" :induct (len entries)))
   :rule-classes nil))

(defthm generated-memory-outside-symmetric
  (implies (generated-memory-outside-p start end first last)
           (generated-memory-outside-p start end last first))
  :hints (("Goal"
           :use ((:instance generated-outside-entries-symmetric
                            (entries (boymoo-model::a64-memory first))
                            (first (boymoo-model::a64-memory first)) (last (boymoo-model::a64-memory last)))
                 (:instance generated-outside-entries-symmetric
                            (entries (boymoo-model::a64-memory last))
                            (first (boymoo-model::a64-memory first)) (last (boymoo-model::a64-memory last))))
           :in-theory (enable generated-memory-outside-p)))
  :rule-classes nil)

(local
 (defthm generated-present-byte-agrees-outside-span
   (implies (and (generated-outside-entries-p entries start end first last)
                 (unsigned-byte-p 64 address) (or (< address start) (<= end address))
                 (assoc-equal address entries))
            (equal (boymoo-model::a64-byte address last)
                   (boymoo-model::a64-byte address first)))
   :hints (("Goal" :induct (generated-outside-entries-p entries start end first last)))
   :rule-classes nil))

(local
 (defthm generated-absent-memory-byte-is-zero
   (implies (and (unsigned-byte-p 64 address) (not (assoc-equal address memory)))
            (equal (boymoo-model::a64-byte address memory) 0))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-byte)))))

(defthm generated-byte-outside-written-span
  (let ((first (boymoo-model::a64-memory before))
        (last (boymoo-model::a64-memory after)))
    (implies (and (generated-memory-outside-p start end before after)
                  (unsigned-byte-p 64 address) (or (< address start) (<= end address)))
             (equal (boymoo-model::a64-byte address last)
                    (boymoo-model::a64-byte address first))))
  :hints (("Goal"
           :use ((:instance generated-present-byte-agrees-outside-span
                            (entries (boymoo-model::a64-memory before))
                            (first (boymoo-model::a64-memory before))
                            (last (boymoo-model::a64-memory after)))
                 (:instance generated-present-byte-agrees-outside-span
                            (entries (boymoo-model::a64-memory after))
                            (first (boymoo-model::a64-memory before))
                            (last (boymoo-model::a64-memory after))))
           :in-theory (e/d (generated-memory-outside-p) (generated-outside-entries-p))))
  :rule-classes nil)

(defthm generated-load-outside-written-span
  (implies (and (generated-memory-outside-p start end before after)
                (proof-span-p address count)
                (proof-disjoint-p address (+ address count) start end))
           (equal (boymoo-model::a64-load count address after)
                  (boymoo-model::a64-load count address before)))
  :hints (("Goal"
           :induct (boymoo-model::a64-read-bytes count address (boymoo-model::a64-memory before))
           :in-theory (enable proof-span-p proof-disjoint-p boymoo-model::a64-load
                              boymoo-model::a64-read-bytes))
          ("Subgoal *1/2" :use generated-byte-outside-written-span))
  :rule-classes nil)

(defthm generated-word-outside-written-span
  (implies (and (generated-memory-outside-p start end before after)
                (proof-span-p address 8)
                (proof-disjoint-p address (+ address 8) start end))
           (equal (proof-load-word address after) (proof-load-word address before)))
  :hints (("Goal" :use (:instance generated-load-outside-written-span (count 8))
                  :in-theory (enable proof-load-word)))
  :rule-classes nil)

(local
 (defthm generated-byte-outside-word-store
   (implies (and (proof-span-p address 8) (unsigned-byte-p 64 query)
                 (or (< query address) (<= (+ address 8) query)))
            (equal (boymoo-model::a64-byte query
                        (boymoo-model::a64-memory
                         (proof-world-machine (generated-store-word address value world))))
                   (boymoo-model::a64-byte query
                        (boymoo-model::a64-memory (proof-world-machine world)))))
   :hints (("Goal"
            :use (:instance generated-byte-after-writing-outside
                            (count 8) (memory (boymoo-model::a64-memory (proof-world-machine world))))
            :in-theory (e/d (proof-span-p generated-store-word boymoo-model::a64-store
                             boymoo-model::a64-memory)
                            (generated-byte-after-writing-outside))))))

(local
 (defthm generated-byte-outside-copy
   (implies (and (generated-word-block-span-p destination count) (unsigned-byte-p 64 query)
                 (or (< query destination) (<= (+ destination (* 8 count)) query)))
            (equal (boymoo-model::a64-byte query
                        (boymoo-model::a64-memory
                         (proof-world-machine (generated-copy-words count source destination world))))
                   (boymoo-model::a64-byte query
                        (boymoo-model::a64-memory (proof-world-machine world)))))
   :hints (("Goal" :induct (generated-copy-words count source destination world)
                   :in-theory (enable generated-copy-words proof-span-p)))))

(local
 (defthm generated-entries-outside-word-store
   (implies (and (proof-span-p address 8) (<= start address) (<= (+ address 8) end))
            (generated-outside-entries-p
             entries start end (boymoo-model::a64-memory (proof-world-machine world))
             (boymoo-model::a64-memory (proof-world-machine (generated-store-word address value world)))))
   :hints (("Goal" :induct (len entries)))))

(local
 (defthm generated-entries-outside-copy
   (implies (and (generated-word-block-span-p destination count)
                 (<= start destination) (<= (+ destination (* 8 count)) end))
            (generated-outside-entries-p
             entries start end (boymoo-model::a64-memory (proof-world-machine world))
             (boymoo-model::a64-memory
              (proof-world-machine (generated-copy-words count source destination world)))))
   :hints (("Goal" :induct (len entries)))))

(defthm generated-word-store-writes-only-inside-span
  (implies (and (proof-span-p address 8) (<= start address) (<= (+ address 8) end))
           (generated-memory-outside-p
            start end (proof-world-machine world)
            (proof-world-machine (generated-store-word address value world))))
  :hints (("Goal" :in-theory (enable generated-memory-outside-p))))

(defthm generated-word-copy-writes-only-inside-span
  (implies (and (generated-word-block-span-p destination count)
                (<= start destination) (<= (+ destination (* 8 count)) end))
           (generated-memory-outside-p
            start end (proof-world-machine world)
            (proof-world-machine (generated-copy-words count source destination world))))
  :hints (("Goal" :in-theory (enable generated-memory-outside-p))))
