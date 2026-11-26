(in-package "BOYMOO-PROOFS")

(include-book "large-map")
(include-book "large-layout")
(include-book "placement")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun allocation-memory-in-readable-regions-p (memory regions)
  (if (atom memory)
      (null memory)
    (and (proof-covered-p (caar memory) 1 :read regions)
         (allocation-memory-in-readable-regions-p (cdr memory) regions))))

(defthm allocation-fresh-mapping-clears-no-existing-entries
  (implies (and (allocation-memory-in-readable-regions-p memory regions)
                (proof-region-disjoint-p start end regions))
           (equal (proof-clear-memory start end memory) memory))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-memory-in-readable-regions-p memory regions)
           :expand ((proof-clear-memory start end memory))
           :in-theory (disable proof-covered-p proof-region-disjoint-p))
          ("Subgoal *1/2"
           :use ((:instance allocation-fresh-mapping-disjoint-from-covered-span
                  (address (caar memory)) (size 1) (access :read))))))

(defthm allocation-memory-in-readable-regions-has-word-keys
  (implies (allocation-memory-in-readable-regions-p memory regions)
           (allocation-memory-addresses-are-words-p memory))
  :rule-classes nil
  :hints (("Goal" :induct (allocation-memory-in-readable-regions-p memory regions)
           :in-theory (disable proof-covered-p proof-span-p))
          ("Subgoal *1/2"
           :use ((:instance allocation-covered-span-is-valid (address (caar memory)) (bytes 1) (access :read)))
           :in-theory (enable proof-span-p))))

(defund allocation-mapping-preserves-heap-data-p (before after)
  (and (allocation-same-memory-p (proof-world-machine before) (proof-world-machine after))
       (equal (proof-heap-base before) (proof-heap-base after))
       (equal (proof-machine-limit before) (proof-machine-limit after))
       (equal (proof-stack-top before) (proof-stack-top after))
       (equal (proof-stack-limit before) (proof-stack-limit after))
       (equal (proof-box-top before) (proof-box-top after))
       (equal (proof-heap-limit before) (proof-heap-limit after))
       (equal (allocation-sp before) (allocation-sp after))
       (equal (proof-world-stop before) (proof-world-stop after))
       (proof-streams-preserved-p before after)))

(local (in-theory (disable allocation-equal-memory-is-model-equivalence allocation-runtime-word-as-load)))

(local
 (defthm allocation-old-coverage-in-extended-regions
   (implies (proof-covered-p address bytes access regions)
            (proof-covered-p address bytes access (cons region regions)))
   :hints (("Goal" :expand ((proof-covered-p address bytes access (cons region regions)))
            :in-theory (disable proof-covered-p proof-region-allows-p proof-subspan-p)))))

(defthm allocation-heap-layout-with-appended-region
  (implies (and (proof-heap-layout-p before)
                (allocation-mapping-preserves-heap-data-p before after)
                (equal (proof-world-regions after) (cons region (proof-world-regions before)))
                (proof-regions-p (proof-world-regions after)))
           (proof-heap-layout-p after))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (allocation-mapping-preserves-heap-data-p)
                                  (proof-align-up proof-covered-p proof-regions-p proof-disjoint-p
                                   proof-span-p proof-subspan-p proof-page-size-p proof-load-word mod)))))

(local
 (defthm allocation-extended-regions-external-list-end
   (equal (proof-external-objects 0 fuel world objects) '(:mappings))))

(defthm allocation-external-list-with-appended-region
  (let ((headers (proof-external-objects head fuel before objects)))
    (implies (and headers
                  (allocation-mapping-preserves-heap-data-p before after)
                  (equal (proof-world-regions after) (cons region (proof-world-regions before))))
             (equal (proof-external-objects head fuel after objects) headers)))
  :rule-classes nil
  :hints (("Goal" :induct (proof-external-objects head fuel before objects)
           :expand ((:free (world) (proof-external-objects head fuel world objects)))
           :in-theory (e/d (allocation-mapping-preserves-heap-data-p)
                           ((:definition proof-external-objects) proof-header-type proof-header-size
                            proof-load-word proof-align-up proof-disjoint-p mod)))))

(local
 (defthm allocation-object-spans-with-mapping-preserving-heap-data
   (implies (allocation-mapping-preserves-heap-data-p before after)
            (equal (proof-heap-object-spans-p objects external after)
                   (proof-heap-object-spans-p objects external before)))
   :rule-classes nil
   :hints (("Goal" :induct (len objects)
            :expand ((:free (world) (proof-heap-object-spans-p objects external world)))
            :in-theory (e/d (allocation-mapping-preserves-heap-data-p)
                            ((:definition proof-heap-object-spans-p) proof-object-size proof-subspan-p mod))))))

(defthm allocation-heap-preservation-with-appended-region
  (implies (and (proof-heap-p before objects packages)
                (allocation-mapping-preserves-heap-data-p before after)
                (equal (proof-world-regions after) (cons region (proof-world-regions before)))
                (proof-regions-p (proof-world-regions after)))
           (proof-preserved-heap-p nil before after objects objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-heap-layout-with-appended-region
                 (:instance allocation-external-list-with-appended-region
                  (head (proof-external-head before)) (fuel (len objects)))
                 (:instance allocation-object-spans-with-mapping-preserving-heap-data
                  (external (cdr (proof-external-objects (proof-external-head before) (len objects) before objects))))
                 (:instance allocation-equal-memory-is-model-equivalence (first before) (last after)))
           :in-theory (e/d (allocation-mapping-preserves-heap-data-p)
                           (proof-heap-layout-p proof-static-p proof-object-map-p proof-external-objects
                            proof-heap-object-spans-p proof-stack-views proof-dynamic-entries
                            proof-dynamic-symbol-objects-p proof-external-bytes proof-load-word
                            proof-view proof-align-up proof-regions-p proof-page-size-p proof-memory-span-agrees-p mod)))))

(defthm allocation-large-map-keeps-heap-registers
  (implies (allocation-large-map-call-result-p before after)
           (and (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
                (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
                (equal (proof-machine-limit after) (proof-machine-limit before))
                (equal (proof-stack-limit after) (proof-stack-limit before))
                (equal (proof-stack-top after) (proof-stack-top before))
                (equal (proof-heap-limit after) (proof-heap-limit before))
                (equal (proof-box-top after) (proof-box-top before))
                (equal (proof-heap-base after) (proof-heap-base before))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-register-frame-member (register 19) (upper 30) (clobbers *allocation-large-map-clobbers*))
                 (:instance allocation-register-frame-member (register 20) (upper 30) (clobbers *allocation-large-map-clobbers*))
                 (:instance allocation-register-frame-member (register 21) (upper 30) (clobbers *allocation-large-map-clobbers*))
                 (:instance allocation-register-frame-member (register 23) (upper 30) (clobbers *allocation-large-map-clobbers*))
                 (:instance allocation-register-frame-member (register 24) (upper 30) (clobbers *allocation-large-map-clobbers*))
                 (:instance allocation-register-frame-member (register 25) (upper 30) (clobbers *allocation-large-map-clobbers*))
                 (:instance allocation-register-frame-member (register 26) (upper 30) (clobbers *allocation-large-map-clobbers*))
                 (:instance allocation-register-frame-member (register 27) (upper 30) (clobbers *allocation-large-map-clobbers*))
                 (:instance allocation-register-frame-member (register 28) (upper 30) (clobbers *allocation-large-map-clobbers*)))
           :in-theory (e/d (allocation-large-map-call-result-p)
                           (proof-register-frame-p proof-clear-memory proof-streams-preserved-p proof-linux-errno-p)))))

(defthm allocation-large-map-success-keeps-old-data
  (let* ((reply (car (proof-world-replies before)))
         (size (proof-world-reg 20 before))
         (regions (proof-world-regions before)))
    (implies (and (allocation-large-map-call-result-p before after)
                  (allocation-map-admissible-success-p reply size before)
                  (posp size) (not (proof-world-stop before))
                  (allocation-memory-in-readable-regions-p (allocation-memory before) regions))
             (and (allocation-mapping-preserves-heap-data-p before after)
                  (equal (allocation-memory after) (allocation-memory before))
                  (equal (proof-world-regions after) (cons (proof-region reply (+ reply size) :rw) regions))
                  (implies (proof-regions-p regions) (proof-regions-p (proof-world-regions after))))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-map-keeps-heap-registers
                 (:instance allocation-map-success-regions-well-formed
                  (mapping (car (proof-world-replies before))) (size (proof-world-reg 20 before)))
                 (:instance allocation-fresh-mapping-clears-no-existing-entries
                  (memory (allocation-memory before)) (regions (proof-world-regions before))
                  (start (car (proof-world-replies before)))
                  (end (+ (car (proof-world-replies before)) (proof-world-reg 20 before)))))
           :in-theory (e/d (allocation-large-map-call-result-p allocation-mapping-preserves-heap-data-p
                            allocation-same-memory-p)
                           (proof-regions-p proof-region-disjoint-p proof-clear-memory
                            allocation-memory-in-readable-regions-p proof-register-frame-p proof-streams-preserved-p
                            proof-covered-p allocation-map-success-world mod)))))

(local
 (defthm allocation-mapping-layout-has-regions-and-running-machine
   (implies (proof-heap-layout-p world)
            (and (proof-regions-p (proof-world-regions world)) (not (proof-world-stop world))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (disable proof-regions-p proof-align-up proof-covered-p proof-disjoint-p mod)))))

(defthm allocation-large-successful-map-keeps-old-heap
  (let* ((reply (car (proof-world-replies before)))
         (size (proof-world-reg 20 before))
         (regions (proof-world-regions before)))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-large-map-call-result-p before after)
                  (allocation-map-admissible-success-p reply size before)
                  (posp size)
                  (allocation-memory-in-readable-regions-p (allocation-memory before) regions))
             (and (proof-preserved-heap-p nil before after objects objects packages)
                  (proof-heap-layout-p after)
                  (equal (allocation-memory after) (allocation-memory before)))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-map-success-keeps-old-data
                 (:instance allocation-heap-preservation-with-appended-region
                  (region (proof-region (car (proof-world-replies before))
                                        (+ (car (proof-world-replies before)) (proof-world-reg 20 before)) :rw)))
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-layout-of-heap (world after)))
           :in-theory (e/d (proof-preserved-heap-p)
                           (allocation-large-map-call-result-p allocation-map-admissible-success-p
                            allocation-memory-in-readable-regions-p proof-heap-layout-p proof-heap-p
                            proof-regions-p proof-heap-frame-p proof-register-frame-p proof-prefix-preserved-p
                            proof-dynamic-table-preserved-p proof-streams-preserved-p proof-stack-top)))))

(defthm allocation-admitted-map-outside-old-reservations
  (let* ((base (proof-heap-base world))
         (heap-start (- base *proof-heap-prefix*))
         (heap-end (proof-spaces-end world))
         (stack-start (proof-stack-base world))
         (machine-start (- (proof-machine-limit world) *proof-machine-margin*))
         (regions (proof-world-regions world)))
    (implies (and (proof-heap-layout-p world)
                  (proof-region-disjoint-p start end regions))
             (and (proof-disjoint-p start end heap-start heap-end)
                  (proof-disjoint-p start end stack-start (proof-stack-end world))
                  (proof-disjoint-p start end machine-start (+ machine-start *proof-machine-reservation*)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-fresh-mapping-disjoint-from-covered-span
                  (address (- (proof-heap-base world) *proof-heap-prefix*))
                  (size (+ *proof-heap-prefix* (- (proof-spaces-end world) (proof-heap-base world))))
                  (access :write) (regions (proof-world-regions world)))
                 (:instance allocation-fresh-mapping-disjoint-from-covered-span
                  (address (proof-stack-base world)) (size *proof-value-reservation*)
                  (access :write) (regions (proof-world-regions world)))
                 (:instance allocation-fresh-mapping-disjoint-from-covered-span
                  (address (- (proof-machine-limit world) *proof-machine-margin*)) (size *proof-machine-reservation*)
                  (access :write) (regions (proof-world-regions world))))
           :in-theory (disable proof-covered-p proof-region-disjoint-p proof-disjoint-p proof-align-up proof-regions-p
                               proof-static-size proof-load-word proof-page-size-p mod))))

(defthm allocation-successful-map-outside-runtime-reservations
  (let* ((reply (car (proof-world-replies before)))
         (size (proof-world-reg 20 before)))
    (implies (and (proof-heap-layout-p before)
                  (allocation-mapping-preserves-heap-data-p before after)
                  (allocation-large-map-call-result-p before after)
                  (allocation-map-admissible-success-p reply size before))
             (allocation-large-mapping-outside-reservations-p after)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-map-keeps-heap-registers
                 (:instance allocation-admitted-map-outside-old-reservations
                  (world before) (start (car (proof-world-replies before)))
                  (end (+ (car (proof-world-replies before)) (proof-world-reg 20 before)))))
           :in-theory (e/d (allocation-mapping-preserves-heap-data-p allocation-large-map-call-result-p
                            allocation-large-mapping-outside-reservations-p)
                           (proof-heap-layout-p proof-region-disjoint-p proof-disjoint-p proof-streams-preserved-p
                            proof-register-frame-p proof-clear-memory proof-load-word mod)))))

(defthm allocation-large-rounded-size-is-mappable
  (implies (natp length)
           (let ((size (allocation-large-mapping-size length)))
             (and (posp size) (<= 32 size) (equal (mod size *proof-runtime-page*) 0))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-align-up-bounds (size (+ 32 length)) (alignment *proof-runtime-page*)))
           :in-theory (disable proof-align-up mod))))

(local
 (defcong allocation-same-memory-p equal (allocation-objects-outside-write-p start end objects machine) 4
   :hints (("Goal" :induct (allocation-objects-outside-write-p start end objects machine)
            :in-theory (disable proof-object-size proof-span-p proof-disjoint-p)))))

(defthm allocation-large-mapped-outside-old-objects
  (let* ((reply (car (proof-world-replies before)))
         (size (proof-world-reg 20 before)))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-map-admissible-success-p reply size before)
                  (allocation-same-memory-p (proof-world-machine before) (proof-world-machine after)))
             (allocation-objects-outside-write-p reply (+ reply size) objects (proof-world-machine after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world before))
                 (:instance allocation-admitted-map-outside-old-reservations
                  (world before) (start (car (proof-world-replies before)))
                  (end (+ (car (proof-world-replies before)) (proof-world-reg 20 before))))
                 (:instance allocation-published-objects-avoid-fresh-or-stack-span
                  (world before) (start (car (proof-world-replies before)))
                  (end (+ (car (proof-world-replies before)) (proof-world-reg 20 before)))))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-region-disjoint-p
                               allocation-objects-outside-write-p proof-disjoint-p mod))))

(local
 (defthm allocation-map-keeps-runtime-words
   (implies (allocation-mapping-preserves-heap-data-p before after)
            (equal (proof-runtime-word offset after) (proof-runtime-word offset before)))
   :rule-classes nil
   :hints (("Goal" :in-theory (enable allocation-mapping-preserves-heap-data-p)))))

(defthm allocation-map-keeps-save-span-and-account
  (implies (allocation-mapping-preserves-heap-data-p before after)
           (and (allocation-same-memory-p (proof-world-machine before) (proof-world-machine after))
                (equal (allocation-sp after) (allocation-sp before))
                (equal (proof-machine-limit after) (proof-machine-limit before))
                (equal (proof-string-bytes-since-collection after) (proof-string-bytes-since-collection before))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-map-keeps-runtime-words (offset 72)))
           :in-theory (e/d (allocation-mapping-preserves-heap-data-p) (proof-runtime-word)))))

(defthm allocation-mapping-success-geometry
   (let* ((size (proof-world-reg 20 before))
          (reply (car (proof-world-replies before))))
     (implies (and (allocation-large-map-call-result-p before after)
                   (allocation-map-admissible-success-p reply size before)
                   (<= 32 size))
              (and (allocation-machine-state-p after)
                   (not (proof-world-stop after))
                   (posp (proof-world-reg 0 after))
                   (equal (proof-world-reg 0 after) reply)
                   (proof-span-p reply size)
                   (< (+ reply 32) *allocation-word-modulus*))))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (allocation-large-map-call-result-p)
                                   (proof-register-frame-p proof-streams-preserved-p mod
                                    proof-region-disjoint-p proof-clear-memory)))))

(defthm allocation-mapped-entry-with-safe-stack
   (let* ((mapping (proof-world-reg 0 world))
          (size (proof-world-reg 20 world))
          (length (proof-world-reg 19 world))
          (base (proof-heap-base world))
          (save (allocation-sp world))
          (machine-start (- (proof-machine-limit world) *proof-machine-margin*))
          (machine-end (+ machine-start *proof-machine-reservation*)))
     (implies (and (allocation-code-origin-p origin)
                   (allocation-machine-state-p world)
                   (equal (proof-world-pc world) (allocation-large-string-address origin 21))
                   (proof-heap-layout-p world)
                   (proof-subspan-p save 32 machine-start machine-end)
                   (< (+ save 32) *allocation-word-modulus*)
                   (allocation-large-mapping-outside-reservations-p world)
                   (posp mapping) (<= 32 size) (proof-span-p mapping size)
                   (< (+ mapping 32) *allocation-word-modulus*)
                   (< length *proof-space-size*)
                   (equal (proof-world-reg 21 world) (- base 128))
                   (< (+ (proof-string-bytes-since-collection world) size) *allocation-word-modulus*))
              (allocation-large-mapped-entry-p origin world)))
   :rule-classes nil
   :hints (("Goal"
            :use (allocation-layout-storage-spans)
            :in-theory (e/d (allocation-large-mapped-entry-p allocation-large-mapping-outside-reservations-p)
                            (proof-heap-layout-p allocation-code-origin-p allocation-large-string-address
                             proof-regions-p proof-load-word proof-span-p mod)))))
