(in-package "BOYMOO-PROOFS")

(include-book "memory")
(include-book "pages")

(logic)
(set-verify-guards-eagerness 0)

(defun collection-memory-keys-p (entries)
  (if (atom entries)
      (null entries)
    (and (unsigned-byte-p 64 (caar entries))
         (collection-memory-keys-p (cdr entries)))))

(local
 (in-theory (disable proof-world-machine boymoo-model::a64-memory
                     boymoo-model::a64-unsigned boymoo-model::a64-byte
                     (:definition ash) (:definition acl2::binary-logior))))

(local
 (defthm collection-entry-agreement-applies-at-key
   (implies (and (proof-byte-entries-agree-p entries start end old new)
                 (assoc-equal address entries)
                 (<= start address) (< address end))
            (equal (boymoo-model::a64-byte address old)
                   (boymoo-model::a64-byte address new)))
   :rule-classes nil
   :hints (("Goal" :induct (len entries)))))

(local
 (defthm collection-byte-absent-at-unsigned-key-is-zero
   (implies (and (unsigned-byte-p 64 address)
                 (not (assoc-equal address memory)))
            (equal (boymoo-model::a64-byte address memory) 0))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-byte)))))

(local (in-theory (disable proof-byte-entries-agree-p)))

(defthm collection-span-agreement-implies-equal-byte
  (implies (and (proof-memory-span-agrees-p start end before after)
                (unsigned-byte-p 64 address) (<= start address) (< address end))
           (equal (boymoo-model::a64-byte
                   address (boymoo-model::a64-memory (proof-world-machine before)))
                  (boymoo-model::a64-byte
                   address (boymoo-model::a64-memory (proof-world-machine after)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-entry-agreement-applies-at-key
                            (entries (boymoo-model::a64-memory (proof-world-machine before)))
                            (old (boymoo-model::a64-memory (proof-world-machine before)))
                            (new (boymoo-model::a64-memory (proof-world-machine after))))
                 (:instance collection-entry-agreement-applies-at-key
                            (entries (boymoo-model::a64-memory (proof-world-machine after)))
                            (old (boymoo-model::a64-memory (proof-world-machine before)))
                            (new (boymoo-model::a64-memory (proof-world-machine after))))))))

(local (in-theory (disable proof-memory-span-agrees-p)))

(local
 (defthm collection-byte-entries-agree-through-intermediate
   (implies (and (collection-memory-keys-p entries)
                 (proof-memory-span-agrees-p start end before middle)
                 (proof-memory-span-agrees-p start end middle after))
            (proof-byte-entries-agree-p
             entries start end
             (boymoo-model::a64-memory (proof-world-machine before))
             (boymoo-model::a64-memory (proof-world-machine after))))
   :hints (("Goal" :induct (len entries)
                   :in-theory (enable proof-byte-entries-agree-p))
           ("Subgoal *1/1"
            :use ((:instance collection-span-agreement-implies-equal-byte
                             (address (caar entries)) (after middle))
                  (:instance collection-span-agreement-implies-equal-byte
                             (address (caar entries)) (before middle)))))))

(defthm collection-memory-span-agrees-transitively
  (implies (and (collection-memory-keys-p
                 (boymoo-model::a64-memory (proof-world-machine before)))
                (collection-memory-keys-p
                 (boymoo-model::a64-memory (proof-world-machine after)))
                (proof-memory-span-agrees-p start end before middle)
                (proof-memory-span-agrees-p start end middle after))
           (proof-memory-span-agrees-p start end before after))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-byte-entries-agree-through-intermediate
                            (entries (boymoo-model::a64-memory (proof-world-machine before))))
                 (:instance collection-byte-entries-agree-through-intermediate
                            (entries (boymoo-model::a64-memory (proof-world-machine after)))))
           :expand ((proof-memory-span-agrees-p start end before after)))))

(local
 (defthm collection-agreeing-spans-have-equal-byte-reads
   (implies (and (proof-memory-span-agrees-p start end before after)
                 (natp address) (natp count) (<= start address)
                 (<= (+ address count) end) (<= end (expt 2 64)))
            (equal (boymoo-model::a64-read-bytes
                    count address (boymoo-model::a64-memory (proof-world-machine before)))
                   (boymoo-model::a64-read-bytes
                    count address (boymoo-model::a64-memory (proof-world-machine after)))))
   :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address nil))
           ("Subgoal *1/2"
            :use ((:instance collection-span-agreement-implies-equal-byte))))))

(defthm collection-span-agreement-preserves-word
  (implies (and (proof-memory-span-agrees-p start end before after)
                (proof-subspan-p address 8 start end)
                (<= end (expt 2 64)))
           (equal (collection-read-word address before)
                  (collection-read-word address after)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance collection-agreeing-spans-have-equal-byte-reads
                                   (count 8)))
                  :in-theory (disable boymoo-model::a64-read-bytes
                                      collection-agreeing-spans-have-equal-byte-reads))))

(local
 (defthm collection-put-byte-preserves-unsigned-address-keys
   (implies (and (collection-memory-keys-p memory) (unsigned-byte-p 64 address))
            (collection-memory-keys-p (put-assoc-equal address value memory)))
   :hints (("Goal" :induct (put-assoc-equal address value memory)))))

(defthm collection-byte-store-preserves-unsigned-address-keys
  (implies (collection-memory-keys-p memory)
           (collection-memory-keys-p (boymoo-model::a64-write-bytes count address value memory)))
  :hints (("Goal" :induct (boymoo-model::a64-write-bytes count address value memory))))

(defthm collection-clear-preserves-unsigned-address-keys
  (implies (collection-memory-keys-p memory)
           (collection-memory-keys-p (proof-clear-memory base end memory)))
  :hints (("Goal" :induct (proof-clear-memory base end memory))))

(local
 (defthm collection-disjoint-store-keeps-byte-entries
   (let ((written (boymoo-model::a64-write-bytes count base value memory)))
     (implies (and (alistp memory) (collection-memory-keys-p entries)
                   (proof-span-p base count)
                   (proof-disjoint-p start end base (+ base count)))
              (proof-byte-entries-agree-p entries start end memory written)))
   :hints (("Goal"
            :induct (len entries)
            :in-theory (e/d (proof-byte-entries-agree-p boymoo-model::a64-byte)
                             (assoc-equal boymoo-model::a64-write-bytes)))
           ("Subgoal *1/1"
            :use ((:instance collection-byte-store-preserves-outside-address
                             (address (caar entries)) (start base)))))))

(defthm collection-disjoint-word-store-preserves-span-agreement
  (let* ((old (boymoo-model::a64-memory (proof-world-machine world)))
         (after (collection-write-word base value world)))
    (implies (and (alistp old) (collection-memory-keys-p old)
                  (proof-span-p base 8) (proof-disjoint-p start end base (+ base 8)))
             (proof-memory-span-agrees-p start end world after)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-disjoint-store-keeps-byte-entries
                            (entries (boymoo-model::a64-memory (proof-world-machine world)))
                            (memory (boymoo-model::a64-memory (proof-world-machine world))) (count 8))
                 (:instance collection-disjoint-store-keeps-byte-entries
                            (entries (boymoo-model::a64-write-bytes
                                      8 base value (boymoo-model::a64-memory (proof-world-machine world))))
                            (memory (boymoo-model::a64-memory (proof-world-machine world))) (count 8)))
           :in-theory (e/d (proof-memory-span-agrees-p)
                            (collection-write-word boymoo-model::a64-write-bytes
                             collection-disjoint-store-keeps-byte-entries)))))

(local
 (defthm collection-disjoint-clear-keeps-byte-entries
   (implies (and (alistp memory) (collection-memory-keys-p entries)
                 (proof-disjoint-p start end base limit))
            (proof-byte-entries-agree-p entries start end memory
                                        (proof-clear-memory base limit memory)))
   :hints (("Goal" :induct (len entries)
                   :in-theory (e/d (proof-byte-entries-agree-p boymoo-model::a64-byte)
                                    (proof-clear-memory))))))

(defthm collection-disjoint-clear-preserves-span-agreement
  (let ((old (boymoo-model::a64-memory (proof-world-machine world))))
    (implies (and (alistp old) (collection-memory-keys-p old)
                  (proof-disjoint-p start end base limit))
             (proof-memory-span-agrees-p start end world (proof-clear-span base limit world))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-disjoint-clear-keeps-byte-entries
                            (entries (boymoo-model::a64-memory (proof-world-machine world)))
                            (memory (boymoo-model::a64-memory (proof-world-machine world))))
                 (:instance collection-disjoint-clear-keeps-byte-entries
                            (entries (proof-clear-memory base limit
                                                         (boymoo-model::a64-memory (proof-world-machine world))))
                            (memory (boymoo-model::a64-memory (proof-world-machine world)))))
           :in-theory (e/d (proof-memory-span-agrees-p proof-clear-span proof-world-machine boymoo-model::a64-memory)
                            (proof-clear-memory collection-disjoint-clear-keeps-byte-entries)))))
