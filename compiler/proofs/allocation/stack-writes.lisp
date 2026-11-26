(in-package "BOYMOO-PROOFS")

(include-book "placement")
(include-book "memory-keys")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defthm allocation-word-writes-preserve-memory-keys
  (implies (allocation-memory-addresses-are-words-p (allocation-memory before))
           (allocation-memory-addresses-are-words-p (allocation-memory (allocation-write-words writes before))))
  :hints (("Goal" :induct (allocation-write-words writes before)
           :in-theory (e/d (allocation-word-keys-after-byte-writes)
                           (boymoo-model::a64-write-bytes allocation-memory-addresses-are-words-p)))))

(defun allocation-stack-word-writes-p (writes world)
  (if (atom writes)
      t
    (let* ((address (caar writes))
           (machine-start (- (proof-machine-limit world) *proof-machine-margin*)))
      (and (posp address)
           (or (proof-subspan-p address 8 (proof-stack-base world) (proof-stack-end world))
               (proof-subspan-p address 8 machine-start (+ machine-start *proof-machine-reservation*)))
           (allocation-stack-word-writes-p (cdr writes) world)))))

(defthm allocation-stack-writes-avoid-disjoint-span
  (let* ((machine-start (- (proof-machine-limit world) *proof-machine-margin*))
         (machine-end (+ machine-start *proof-machine-reservation*)))
    (implies (and (allocation-stack-word-writes-p writes world)
                  (proof-disjoint-p lower upper (proof-stack-base world) (proof-stack-end world))
                  (proof-disjoint-p lower upper machine-start machine-end))
             (allocation-word-writes-avoid-span-p writes lower upper)))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-stack-word-writes-p writes world)
           :in-theory (disable proof-span-p proof-stack-base proof-stack-end proof-machine-limit
                               proof-runtime-word allocation-runtime-word-as-load))))

(defthm allocation-stack-writes-avoid-heap-reservation
  (let ((lower (- (proof-heap-base world) *proof-heap-prefix*))
        (upper (proof-spaces-end world)))
    (implies (and (proof-heap-layout-p world)
                  (allocation-stack-word-writes-p writes world))
             (allocation-word-writes-avoid-span-p writes lower upper)))
  :rule-classes nil
  :hints (("Goal" :use (allocation-layout-storage-spans
                        (:instance allocation-stack-writes-avoid-disjoint-span
                         (lower (- (proof-heap-base world) *proof-heap-prefix*)) (upper (proof-spaces-end world))))
           :in-theory (disable proof-heap-layout-p proof-disjoint-p proof-span-p
                               allocation-stack-word-writes-p allocation-word-writes-avoid-span-p))))

(defthm allocation-stack-writes-avoid-published-objects
  (implies (and (proof-heap-p world objects packages)
                (allocation-stack-word-writes-p writes world))
           (allocation-word-writes-outside-objects-p writes objects (proof-world-machine world)))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-stack-word-writes-p writes world)
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-span-p allocation-objects-outside-write-p
                               proof-stack-base proof-stack-end proof-heap-base proof-spaces-end proof-machine-limit))
          ("Subgoal *1/2"
           :use (allocation-layout-of-heap allocation-layout-storage-spans
                 (:instance allocation-published-objects-avoid-fresh-or-stack-span
                  (start (caar writes)) (end (+ 8 (caar writes))))))))

(local
 (defthm allocation-stack-write-external-end
   (equal (proof-external-objects 0 fuel world objects) '(:mappings))))

(defthm allocation-stack-writes-avoid-external-mappings
  (let ((mappings (proof-external-objects head fuel world objects)))
    (implies (and mappings
                  (proof-regions-p (proof-world-regions world))
                  (allocation-stack-word-writes-p writes world))
             (allocation-external-spans-avoid-writes-p (cdr mappings) writes world)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel world objects)
           :expand ((proof-external-objects head fuel world objects))
           :in-theory (disable (:definition proof-external-objects) proof-header-type proof-header-size
                               proof-align-up proof-load-word proof-regions-p proof-disjoint-p
                               proof-region proof-stack-base proof-stack-end proof-machine-limit
                               allocation-stack-word-writes-p allocation-word-writes-avoid-span-p))
          ("Subgoal *1/2"
           :use ((:instance allocation-stack-writes-avoid-disjoint-span
                  (lower head) (upper (+ head (proof-load-word (+ head 8) (proof-world-machine world)))))
                 (:instance allocation-region-member-has-valid-span
                  (start head) (end (+ head (proof-load-word (+ head 8) (proof-world-machine world))))
                  (mode :rw) (regions (proof-world-regions world)))))))

(defund allocation-stack-write-state-p (writes before after)
  (and (allocation-stack-word-writes-p writes before)
       (equal (allocation-memory after) (allocation-memory (allocation-write-words writes before)))
       (equal (proof-heap-base after) (proof-heap-base before))
       (equal (proof-box-top after) (proof-box-top before))
       (equal (proof-heap-limit after) (proof-heap-limit before))
       (equal (proof-machine-limit after) (proof-machine-limit before))
       (equal (proof-world-regions after) (proof-world-regions before))
       (proof-streams-preserved-p before after)
       (not (proof-world-stop after))))

(defund allocation-stack-pointers-in-original-reservations-p (before after)
  (let ((machine-start (- (proof-machine-limit before) *proof-machine-margin*))
        (sp (allocation-sp after))
        (top (proof-stack-top after))
        (limit (proof-stack-limit after)))
    (and (<= (proof-stack-base before) top)
         (<= top limit)
         (<= limit (proof-stack-end before))
         (equal (mod top 8) 0)
         (equal (mod limit 8) 0)
         (<= machine-start sp)
         (<= sp (+ machine-start *proof-machine-reservation*))
         (equal (mod sp 16) 0))))

(defthm allocation-stack-write-state-protects-heap
  (let ((lower (- (proof-heap-base before) *proof-heap-prefix*))
        (upper (proof-spaces-end before)))
    (implies (and (proof-heap-layout-p before)
                  (allocation-stack-write-state-p writes before after))
             (proof-memory-span-agrees-p lower upper before after)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-stack-writes-avoid-heap-reservation (world before))
                 (:instance allocation-word-writes-keep-protected-span
                  (world before) (lower (- (proof-heap-base before) *proof-heap-prefix*))
                  (upper (proof-spaces-end before))))
           :in-theory (e/d (allocation-stack-write-state-p)
                           (proof-heap-layout-p proof-memory-span-agrees-p proof-disjoint-p
                            allocation-stack-word-writes-p allocation-word-writes-avoid-span-p allocation-write-words
                            proof-heap-base proof-spaces-end proof-streams-preserved-p
                            proof-runtime-word allocation-runtime-word-as-load)))))

(defthm allocation-stack-write-state-keeps-runtime-words
  (implies (and (proof-heap-layout-p before)
                (allocation-stack-write-state-p writes before after)
                (natp offset) (<= offset 80))
           (equal (proof-runtime-word offset after) (proof-runtime-word offset before)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-stack-write-state-protects-heap
                 (:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-word-in-agreeing-span
                  (lower (- (proof-heap-base before) *proof-heap-prefix*)) (upper (proof-spaces-end before))
                  (address (+ (- (proof-heap-base before) 128) offset))))
           :in-theory (e/d (allocation-stack-write-state-p allocation-runtime-word-as-load)
                           (proof-heap-layout-p proof-runtime-word proof-heap-base proof-spaces-end
                            proof-memory-span-agrees-p allocation-write-words proof-streams-preserved-p
                            allocation-stack-word-writes-p)))))

(defthm allocation-stack-write-state-keeps-static-size-and-dynamic-root
  (let ((base (proof-heap-base before)))
    (implies (and (proof-heap-layout-p before)
                  (allocation-stack-write-state-p writes before after))
             (and (equal (proof-static-size base (proof-world-machine after))
                         (proof-static-size base (proof-world-machine before)))
                  (equal (proof-dynamic-root base (proof-world-machine after))
                         (proof-dynamic-root base (proof-world-machine before))))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-stack-write-state-protects-heap
                 (:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-word-in-agreeing-span
                  (lower (- (proof-heap-base before) *proof-heap-prefix*)) (upper (proof-spaces-end before))
                  (address (proof-heap-base before)))
                 (:instance allocation-word-in-agreeing-span
                  (lower (- (proof-heap-base before) *proof-heap-prefix*)) (upper (proof-spaces-end before))
                  (address (+ 24 (proof-heap-base before)))))
           :in-theory (e/d (allocation-load-word)
                           (proof-heap-layout-p proof-load-word proof-heap-base proof-spaces-end
                            proof-memory-span-agrees-p proof-runtime-word allocation-runtime-word-as-load)))))

(defthm allocation-stack-write-state-keeps-layout
  (implies (and (proof-heap-layout-p before)
                (allocation-stack-write-state-p writes before after)
                (allocation-stack-pointers-in-original-reservations-p before after))
           (proof-heap-layout-p after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-stack-write-state-keeps-static-size-and-dynamic-root
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 0))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 8))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 16))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 24))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 32))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 40))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 48))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 64)))
           :in-theory (e/d (allocation-stack-write-state-p allocation-stack-pointers-in-original-reservations-p)
                           (allocation-stack-word-writes-p allocation-write-words proof-runtime-word
                            allocation-runtime-word-as-load proof-disjoint-p proof-align-up proof-covered-p
                            proof-regions-p proof-page-size-p proof-static-size proof-dynamic-root mod)))))

(local
 (defthm allocation-stack-write-state-keeps-external-bounds
   (implies (and (proof-heap-layout-p before)
                 (allocation-stack-write-state-p writes before after))
            (allocation-same-external-bounds-p before after))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-stack-write-state-keeps-runtime-words (offset 40))
                  (:instance allocation-stack-write-state-keeps-runtime-words (offset 48))
                  (:instance allocation-stack-write-state-keeps-runtime-words (offset 64)))
            :in-theory (e/d (allocation-stack-write-state-p allocation-same-external-bounds-p)
                            (proof-heap-layout-p proof-runtime-word allocation-runtime-word-as-load
                             allocation-stack-word-writes-p allocation-write-words proof-streams-preserved-p))))))

(defthm allocation-stack-write-state-keeps-external-account
  (let* ((head (proof-external-head before))
         (mappings (proof-external-objects head (len objects) before objects)))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-stack-write-state-p writes before after))
             (and (equal (proof-external-objects (proof-external-head after) (len objects) after objects) mappings)
                  (proof-string-accounting-p (cdr mappings) after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world before))
                 (:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-heap-span-facts-for-reservations (world before))
                 (:instance allocation-stack-writes-avoid-external-mappings
                  (world before) (head (proof-external-head before)) (fuel (len objects)))
                 (:instance allocation-word-writes-keep-external-mapping-spans
                  (before before) (headers (cdr (proof-external-objects (proof-external-head before) (len objects) before objects))))
                 (:instance allocation-external-objects-from-fixed-mapping-memory
                  (head (proof-external-head before)) (fuel (len objects)))
                 allocation-stack-write-state-keeps-external-bounds
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 56))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 72))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 80)))
           :in-theory (e/d (allocation-stack-write-state-p)
                           (proof-heap-layout-p proof-runtime-word allocation-runtime-word-as-load
                            proof-external-objects proof-external-bytes proof-fixed-external-p
                            proof-static-p proof-object-map-p proof-heap-object-spans-p
                            proof-stack-prefix proof-dynamic-entries proof-dynamic-symbol-objects-p proof-dynamic-view
                            allocation-stack-word-writes-p allocation-write-words proof-streams-preserved-p
                            allocation-external-spans-avoid-writes-p proof-regions-p proof-disjoint-p mod)))))

(defthm allocation-stack-write-state-keeps-static-and-object-map
  (let ((base (proof-heap-base before)))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-stack-write-state-p writes before after))
             (and (proof-static-p base objects packages (proof-world-machine after))
                  (proof-object-map-p objects objects nil base packages (proof-world-machine after)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world before))
                 (:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-stack-writes-avoid-heap-reservation (world before))
                 (:instance allocation-stack-writes-avoid-published-objects (world before))
                 (:instance allocation-word-writes-avoid-subspan
                  (lower (- (proof-heap-base before) *proof-heap-prefix*))
                  (upper (proof-spaces-end before))
                  (start (proof-heap-base before))
                  (end (+ (proof-heap-base before) (proof-static-size (proof-heap-base before) (proof-world-machine before)))))
                 (:instance allocation-word-writes-keep-static-area (base (proof-heap-base before)) (world before))
                 (:instance allocation-word-writes-keep-published-map (base (proof-heap-base before)) (world before))
                 (:instance allocation-equal-memory-is-model-equivalence (first after) (last (allocation-write-words writes before))))
           :in-theory (e/d (allocation-stack-write-state-p)
                           (proof-heap-layout-p proof-static-p proof-object-map-p proof-heap-object-spans-p
                            proof-string-accounting-p proof-stack-prefix proof-external-objects
                            proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p
                            proof-heap-base proof-spaces-end proof-static-size proof-runtime-word proof-disjoint-p
                            allocation-runtime-word-as-load allocation-equal-memory-is-model-equivalence
                            allocation-stack-word-writes-p allocation-word-writes-avoid-span-p
                            allocation-word-writes-outside-objects-p allocation-write-words mod)))))

(defthm allocation-stack-write-state-keeps-dynamic-entries
  (let* ((base (proof-heap-base before))
         (entries (cdr (proof-dynamic-entries (proof-dynamic-view before objects packages) packages))))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-stack-write-state-p writes before after))
             (and (equal (proof-dynamic-view after objects packages) (proof-dynamic-view before objects packages))
                  (proof-dynamic-symbol-objects-p objects objects entries base packages (proof-world-machine after)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world before))
                 allocation-stack-write-state-keeps-static-size-and-dynamic-root
                 (:instance allocation-stack-writes-avoid-published-objects (world before))
                 (:instance allocation-word-writes-keep-views
                  (world before) (base (proof-heap-base before))
                  (word (proof-dynamic-root (proof-heap-base before) (proof-world-machine before))))
                 (:instance allocation-word-writes-keep-dynamic-symbols
                  (world before) (base (proof-heap-base before))
                  (entries (cdr (proof-dynamic-entries (proof-dynamic-view before objects packages) packages))))
                 (:instance allocation-equal-memory-is-model-equivalence (first after) (last (allocation-write-words writes before))))
           :in-theory (e/d (allocation-stack-write-state-p)
                           (proof-heap-layout-p proof-static-p proof-object-map-p proof-heap-object-spans-p
                            proof-string-accounting-p proof-stack-prefix proof-external-objects proof-dynamic-root
                            proof-dynamic-entries proof-dynamic-symbol-objects-p proof-heap-base proof-view
                            allocation-equal-memory-is-model-equivalence allocation-stack-word-writes-p
                            allocation-word-writes-outside-objects-p allocation-write-words mod)))))

(local
 (defthm allocation-subset-survives-prepending
   (implies (subsetp-equal subset objects)
            (subsetp-equal subset (cons object objects)))
   :hints (("Goal" :induct (subsetp-equal subset objects)))))

(local
 (defthm allocation-objects-in-their-own-list
   (subsetp-equal objects objects)
   :hints (("Goal" :induct (len objects)))))

(defthm allocation-stack-write-state-keeps-heap-with-new-stack-prefix
  (implies (and (proof-heap-p before objects packages)
                (allocation-stack-write-state-p writes before after)
                (allocation-stack-pointers-in-original-reservations-p before after)
                (proof-stack-prefix (proof-stack-top after) after objects packages))
           (proof-heap-p after objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world before))
                 allocation-stack-write-state-keeps-layout allocation-stack-write-state-keeps-external-account
                 allocation-stack-write-state-keeps-static-and-object-map allocation-stack-write-state-keeps-dynamic-entries
                 (:instance allocation-stack-writes-avoid-published-objects (world before))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 0))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 8))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 16))
                 (:instance allocation-word-writes-keep-heap-object-spans
                  (pending objects) (base (proof-heap-base before))
                  (headers (cdr (proof-external-objects (proof-external-head before) (len objects) before objects))))
                 (:instance allocation-equal-memory-is-model-equivalence (first after) (last (allocation-write-words writes before))))
           :in-theory (e/d (allocation-stack-write-state-p)
                           (proof-heap-layout-p proof-static-p proof-object-map-p proof-heap-object-spans-p
                            proof-string-accounting-p proof-stack-prefix proof-external-objects proof-dynamic-root
                            proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p proof-heap-base
                            proof-runtime-word allocation-runtime-word-as-load allocation-equal-memory-is-model-equivalence
                            allocation-stack-word-writes-p allocation-word-writes-outside-objects-p allocation-write-words mod)))))

(defthm allocation-stack-write-state-keeps-caller-heap-frame
  (let ((sp (allocation-sp before))
        (end (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*)))
    (implies (and (proof-heap-layout-p before)
                  (allocation-stack-write-state-p writes before after)
                  (allocation-word-writes-avoid-span-p writes sp end))
             (proof-heap-frame-p before after)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-stack-write-state-keeps-external-bounds allocation-stack-write-state-protects-heap
                 (:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-word-writes-keep-protected-span
                  (world before) (lower (allocation-sp before))
                  (upper (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*)))
                 (:instance allocation-memory-span-agreement-in-contained-span
                  (lower (- (proof-heap-base before) *proof-heap-prefix*)) (upper (proof-spaces-end before))
                  (start (proof-heap-base before)) (end (+ 24 (proof-heap-base before))))
                 (:instance allocation-memory-span-agreement-in-contained-span
                  (lower (- (proof-heap-base before) *proof-heap-prefix*)) (upper (proof-spaces-end before))
                  (start (+ 32 (proof-heap-base before)))
                  (end (+ (proof-heap-base before) (proof-static-size (proof-heap-base before) (proof-world-machine before))))))
           :in-theory (e/d (allocation-stack-write-state-p allocation-same-external-bounds-p)
                           (proof-heap-layout-p proof-memory-span-agrees-p proof-runtime-word
                            allocation-runtime-word-as-load proof-heap-base proof-spaces-end proof-static-size
                            proof-machine-limit allocation-word-writes-avoid-span-p
                            allocation-stack-word-writes-p allocation-write-words proof-streams-preserved-p)))))

(local
 (defthm allocation-old-stack-index-distance
   (implies (and (natp index) (integerp base) (equal top (+ base (* 8 index))))
            (and (equal (ash (- top base) -3) index)
                 (equal (mod (- top base) 8) 0)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable ash)))))

(defthm allocation-stack-write-state-keeps-live-prefix
  (let* ((top (proof-stack-top before))
         (stack (proof-stack-base before)))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-stack-write-state-p writes before after)
                  (natp index) (equal top (+ stack (* 8 index)))
                  (<= top (proof-stack-top after))
                  (allocation-word-writes-avoid-span-p writes stack top))
             (proof-prefix-preserved-p top before after objects objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world before))
                 (:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-heap-stack-prefix-exists (world before))
                 (:instance allocation-stack-write-state-keeps-runtime-words (offset 40))
                 (:instance allocation-stack-writes-avoid-published-objects (world before))
                 (:instance allocation-old-stack-index-distance (top (proof-stack-top before)) (base (proof-stack-base before)))
                 (:instance allocation-word-writes-keep-stack-views
                  (count index) (address (proof-stack-base before)) (base (proof-heap-base before)) (world before))
                 (:instance allocation-equal-memory-is-model-equivalence (first after) (last (allocation-write-words writes before))))
           :in-theory (e/d (allocation-stack-write-state-p)
                           (proof-heap-p proof-heap-layout-p proof-runtime-word allocation-runtime-word-as-load
                            proof-heap-base proof-stack-views allocation-equal-memory-is-model-equivalence
                            allocation-word-writes-avoid-span-p allocation-stack-word-writes-p
                            allocation-word-writes-outside-objects-p allocation-write-words ash mod)))))

(defthm allocation-stack-write-state-keeps-existing-heap
  (let* ((top (proof-stack-top before))
         (stack (proof-stack-base before))
         (end (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*)))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-stack-write-state-p writes before after)
                  (allocation-stack-pointers-in-original-reservations-p before after)
                  (natp index) (equal top (+ stack (* 8 index)))
                  (equal (proof-stack-top after) top)
                  (allocation-word-writes-avoid-span-p writes stack top)
                  (allocation-word-writes-avoid-span-p writes (allocation-sp before) end))
             (proof-preserved-heap-p nil before after objects objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world before))
                 allocation-stack-write-state-keeps-heap-with-new-stack-prefix
                 allocation-stack-write-state-keeps-caller-heap-frame
                 allocation-stack-write-state-keeps-dynamic-entries
                 allocation-stack-write-state-keeps-live-prefix)
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-heap-frame-p proof-stack-top proof-stack-base
                               proof-stack-prefix proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p
                               allocation-word-writes-avoid-span-p))))
