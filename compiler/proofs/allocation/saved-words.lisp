(in-package "BOYMOO-PROOFS")

(include-book "memory")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-byte-entry-agreement
  (implies (and (proof-byte-entries-agree-p entries lower upper memory other)
                (assoc-equal address entries) (<= lower address) (< address upper))
           (equal (boymoo-model::a64-byte address other)
                  (boymoo-model::a64-byte address memory)))
  :rule-classes nil
  :hints (("Goal" :induct (assoc-equal address entries)
           :in-theory (disable boymoo-model::a64-byte))))

(defthm allocation-byte-agreement-in-span
  (implies (and (proof-memory-span-agrees-p lower upper before after)
                (unsigned-byte-p 64 address) (<= lower address) (< address upper))
           (equal (boymoo-model::a64-byte address (allocation-memory after))
                  (boymoo-model::a64-byte address (allocation-memory before))))
  :rule-classes nil
  :hints (("Goal" :cases ((assoc-equal address (allocation-memory before))
                         (assoc-equal address (allocation-memory after)))
           :use ((:instance allocation-byte-entry-agreement
                  (entries (allocation-memory before)) (memory (allocation-memory before))
                  (other (allocation-memory after)))
                 (:instance allocation-byte-entry-agreement
                  (entries (allocation-memory after)) (memory (allocation-memory before))
                  (other (allocation-memory after))))
           :in-theory (disable proof-byte-entries-agree-p))))

(defthm allocation-read-bytes-in-agreeing-span
  (implies (and (proof-memory-span-agrees-p lower upper before after)
                (proof-subspan-p address count lower upper))
           (equal (boymoo-model::a64-read-bytes count address (allocation-memory after))
                  (boymoo-model::a64-read-bytes count address (allocation-memory before))))
  :rule-classes nil
  :hints (("Goal" :induct (boymoo-model::a64-read-bytes count address (allocation-memory before))
           :in-theory (e/d (boymoo-model::a64-read-bytes)
                           (proof-memory-span-agrees-p boymoo-model::a64-byte)))
          ("Subgoal *1/2"
           :use allocation-byte-agreement-in-span
           :expand ((boymoo-model::a64-read-bytes count address (allocation-memory before))
                    (boymoo-model::a64-read-bytes count address (allocation-memory after))))))

(defthm allocation-word-in-agreeing-span
  (implies (and (proof-memory-span-agrees-p lower upper before after)
                (proof-subspan-p address 8 lower upper))
           (equal (allocation-load-word address after) (allocation-load-word address before)))
  :rule-classes nil
  :hints (("Goal" :use ((:instance allocation-read-bytes-in-agreeing-span (count 8)))
           :in-theory (e/d (allocation-load-word proof-load-word)
                           (proof-memory-span-agrees-p proof-subspan-p)))))

(defthm allocation-allocator-preserves-saved-word
  (let ((end (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*)))
    (implies (and (proof-allocator-return-p kind bytes before after old-objects new-objects packages)
                  (proof-subspan-p address 8 (allocation-sp before) end))
             (equal (allocation-load-word address after) (allocation-load-word address before))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-word-in-agreeing-span (lower (allocation-sp before))
                  (upper (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*))))
           :in-theory (disable proof-heap-p proof-stack-base proof-stack-end proof-spaces-end proof-static-size
                               proof-stack-prefix proof-memory-span-agrees-p proof-reserved-span-p
                               proof-dynamic-table-preserved-p proof-subspan-p))))
