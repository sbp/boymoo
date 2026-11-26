(in-package "BOYMOO-PROOFS")

(include-book "sweep-readiness")
(include-book "sweep-snapshot")
(local (include-book "std/lists/update-nth" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun collection-sweep-zero-replies-p (count replies)
  (declare (xargs :measure (nfix count)))
  (or (zp count)
      (and (consp replies) (equal (car replies) 0)
           (collection-sweep-zero-replies-p (1- count) (cdr replies)))))

(defun collection-sweep-loop-code (origin)
  (append (collection-linux-trace "rt:sweep-string" '(0 1) origin)
          (collection-sweep-retain-trace origin)
          (collection-sweep-discard-trace origin)))

; The remaining links, sizes and marks are recorded in the snapshot.
; The link register names a writable word outside those mappings.
; The budget bound concerns the accumulator plus all bytes still to add.
(defun collection-sweep-loop-invariant-p (records origin world)
  (let* ((entry (collection-linux-offset "rt:sweep-string"))
         (link (proof-world-reg 19 world))
         (regions (proof-world-regions world)))
    (and (collection-sweep-entry-p entry origin world)
         (not (proof-world-stop world))
         (alistp (boymoo-model::a64-memory (proof-world-machine world)))
         (proof-regions-p regions)
         (proof-page-size-p (proof-world-page-size world))
         (collection-trace-placed-p (collection-sweep-loop-code origin) world)
         (proof-covered-p link 8 :write regions)
         (equal (collection-read-word link world) (collection-sweep-next-head records))
         (collection-sweep-spans-separate-p link (+ link 8) records)
         (collection-sweep-spans-disjoint-p records)
         (collection-sweep-snapshot-p records world)
         (unsigned-byte-p 64 (+ (proof-world-reg 22 world) (collection-sweep-retained-bytes records)))
         (collection-sweep-zero-replies-p (collection-sweep-discard-count records)
                                          (proof-world-replies world)))))

(local
 (in-theory (disable proof-world-pc proof-world-reg proof-world-machine proof-world-regions
                     proof-world-stop proof-world-replies proof-world-page-size
                     proof-load-word proof-instruction-effect proof-instruction-at-p
                     proof-advance proof-segment-p proof-span-p proof-disjoint-p
                     proof-covered-p proof-regions-p proof-page-size-p proof-align-up mod
                     collection-read-word collection-write-word collection-cpu-p
                     collection-sweep-entry-p collection-trace-effect collection-trace-placed-p
                     collection-trace-ready-p collection-loop-round-ready-p
                     collection-sweep-retain-trace collection-sweep-discard-trace
                     collection-sweep-retained-bytes collection-sweep-discard-count
                     collection-sweep-retains-one-mapping-and-resets-mark
                     collection-sweep-discards-one-mapping-and-relinks
                     boymoo-model::a64-memory boymoo-model::a64-unsigned)))

(local
 (defthm collection-sweep-loop-places-all-branches
   (equal (collection-trace-placed-p (collection-sweep-loop-code origin) world)
          (and (collection-trace-placed-p (collection-linux-trace "rt:sweep-string" '(0 1) origin) world)
               (collection-trace-placed-p (collection-sweep-retain-trace origin) world)
               (collection-trace-placed-p (collection-sweep-discard-trace origin) world)))
   :hints (("Goal" :in-theory (disable collection-linux-trace)))))

(local
 (in-theory (disable collection-sweep-loop-code)))

(local
 (defthm collection-sweep-snapshot-gives-round-premises
   (implies (and (collection-sweep-loop-invariant-p records origin world) (consp records))
            (collection-sweep-round-input-p (car records) world))
   :hints (("Goal"
            :use ((:instance collection-covered-address-is-a-span
                             (address (proof-world-reg 19 world)) (width 8) (access :write)
                             (regions (proof-world-regions world)))
                  (:instance collection-covered-subspan
                             (address (caar records)) (base (caar records))
                             (width 24) (extent (cadar records)) (access :write)
                             (regions (proof-world-regions world)))
                  (:instance collection-covered-address-is-a-span
                             (address (caar records)) (width 24) (access :write)
                             (regions (proof-world-regions world))))
            :expand ((collection-sweep-retained-bytes records)
                     (collection-sweep-discard-count records))
            :in-theory (e/d (collection-relinquish-p proof-span-p proof-subspan-p)
                             (collection-covered-address-is-a-span))))))

(local
 (defthm collection-sweep-snapshot-gives-round-readiness
   (implies (and (collection-sweep-loop-invariant-p records origin world) (consp records))
            (collection-loop-round-ready-p (collection-sweep-round-trace (car records) origin) world))
   :hints (("Goal"
            :cases ((caddar records))
            :use ((:instance collection-covered-subspan
                             (address (caar records)) (base (caar records))
                             (width 24) (extent (cadar records)) (access :write)
                             (regions (proof-world-regions world)))
                  (:instance collection-placed-sweep-retain-round-is-ready)
                  (:instance collection-placed-sweep-discard-round-is-ready)
                  (:instance collection-sweep-snapshot-gives-round-premises))
            :in-theory (e/d (proof-subspan-p proof-span-p)
                             (collection-placed-sweep-retain-round-is-ready
                              collection-placed-sweep-discard-round-is-ready
                              collection-sweep-snapshot-gives-round-premises))))))

(local
 (defun collection-sweep-round-memory-world (record world)
   (let ((head (car record)))
     (if (caddr record)
         (collection-write-word (+ head 16) 0 world)
       (collection-relinquish-range
        t head (cadr record)
        (collection-write-word (proof-world-reg 19 world) (collection-read-word head world) world))))))

(local
 (defthm collection-sweep-modified-world-observations
   (let ((after (collection-relinquish-range t head size world)))
     (and (equal (proof-world-page-size after) (proof-world-page-size world))
          (equal (proof-world-page-size (collection-write-word address value world))
                 (proof-world-page-size world))
          (equal (proof-world-regions after)
                 (proof-remove-region-span head size (proof-world-regions world)))
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (proof-clear-memory head (+ head size)
                                     (boymoo-model::a64-memory (proof-world-machine world))))))
   :hints (("Goal"
            :in-theory (e/d (collection-relinquish-range proof-clear-span proof-world-machine
                                                       boymoo-model::a64-memory
                                                       proof-world-regions proof-world-page-size)
                             (proof-remove-region-span proof-clear-memory update-nth))))))

(local
 (defthm collection-sweep-round-matches-its-memory-world
   (let* ((after (collection-trace-effect (collection-sweep-round-trace record origin) world))
          (written (collection-sweep-round-memory-world record world)))
     (implies (and (collection-sweep-entry-p (collection-linux-offset "rt:sweep-string") origin world)
                   (collection-sweep-round-input-p record world))
              (and (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory (proof-world-machine written)))
                   (equal (proof-world-regions after) (proof-world-regions written))
                   (equal (proof-world-page-size after) (proof-world-page-size written)))))
   :hints (("Goal"
            :cases ((caddr record))
            :use ((:instance collection-sweep-retains-one-mapping-and-resets-mark)
                  (:instance collection-sweep-discards-one-mapping-and-relinks))
            :in-theory (e/d (proof-streams-preserved-p)
                             (collection-relinquish-range proof-clear-memory
                              proof-remove-region-span collection-memory-after-word-store))))))

(local
 (defthm collection-sweep-nonempty-span-remains-covered
   (implies (and (proof-covered-p link 8 :write regions)
                 (proof-disjoint-p link (+ link 8) base (+ base size)))
            (proof-covered-p link 8 :write (proof-remove-region-span base size regions)))
   :hints (("Goal"
            :use ((:instance collection-removal-preserves-disjoint-coverage
                             (address link) (width 8) (access :write)))))))

(local
 (defthm collection-sweep-writable-store-keeps-code-placement
   (implies (and (alistp (boymoo-model::a64-memory (proof-world-machine world)))
                 (proof-regions-p (proof-world-regions world))
                 (proof-covered-p address 8 :write (proof-world-regions world)))
            (equal (collection-trace-placed-p trace (collection-write-word address value world))
                   (collection-trace-placed-p trace world)))
   :hints (("Goal"
            :induct (len trace)
            :in-theory (enable collection-trace-placed-p)))))

(local
 (defthm collection-sweep-keep-write-covers-mark-and-link
   (implies (and (proof-covered-p head size :write regions) (natp size) (<= 24 size))
            (and (proof-subspan-p (+ head 16) 8 head (+ head size))
                 (proof-covered-p (+ head 16) 8 :write regions)
                 (proof-covered-p head 8 :write regions)
                 (proof-span-p (+ head 16) 8)
                 (proof-span-p head 8)
                 (proof-disjoint-p head (+ head 8) (+ head 16) (+ head 24))))
   :hints (("Goal"
            :use ((:instance collection-covered-address-is-a-span
                             (address head) (width size) (access :write))
                  (:instance collection-covered-subspan
                             (address (+ head 16)) (base head) (width 8) (extent size) (access :write))
                  (:instance collection-covered-subspan
                             (address head) (base head) (width 8) (extent size) (access :write)))
            :in-theory (e/d (proof-span-p proof-disjoint-p)
                             (collection-covered-address-is-a-span))))))

(local
 (defthm collection-sweep-updating-map-keeps-unvisited-snapshot
   (implies (and (collection-sweep-loop-invariant-p records origin world) (consp records))
            (collection-sweep-snapshot-p (cdr records)
                                         (collection-sweep-round-memory-world (car records) world)))
   :hints (("Goal"
            :cases ((caddar records))
            :use ((:instance collection-sweep-keep-write-covers-mark-and-link
                             (head (caar records)) (size (cadar records))
                             (regions (proof-world-regions world)))
                  (:instance collection-sweep-subspan-separates-from-same-mappings
                             (address (+ 16 (caar records))) (width 8) (start (caar records))
                             (end (+ (caar records) (cadar records))) (records (cdr records)))
                  (:instance collection-separated-store-preserves-sweep-snapshot
                             (records (cdr records)) (start (+ 16 (caar records))) (value 0))
                  (:instance collection-separated-store-preserves-sweep-snapshot
                             (records (cdr records)) (start (proof-world-reg 19 world))
                             (value (collection-read-word (caar records) world)))
                  (:instance collection-separated-unmap-preserves-sweep-snapshot
                             (records (cdr records)) (base (caar records)) (bytes (cadar records))
                             (world (collection-write-word (proof-world-reg 19 world)
                                                           (collection-read-word (caar records) world) world)))
                  (:instance collection-covered-address-is-a-span
                             (address (proof-world-reg 19 world)) (width 8) (access :write)
                             (regions (proof-world-regions world))))
            :in-theory (disable collection-sweep-keep-write-covers-mark-and-link
                                collection-relinquish-range proof-remove-region-span
                                collection-covered-address-is-a-span)))))

(local
 (defthm collection-sweep-updating-map-keeps-loop-code
   (implies (and (collection-sweep-loop-invariant-p records origin world) (consp records))
            (collection-trace-placed-p (collection-sweep-loop-code origin)
                                       (collection-sweep-round-memory-world (car records) world)))
   :hints (("Goal"
            :cases ((caddar records))
            :use ((:instance collection-sweep-keep-write-covers-mark-and-link
                             (head (caar records)) (size (cadar records))
                             (regions (proof-world-regions world)))
                  (:instance collection-sweep-writable-store-keeps-code-placement
                             (address (+ 16 (caar records))) (value 0)
                             (trace (collection-sweep-loop-code origin)))
                  (:instance collection-sweep-writable-store-keeps-code-placement
                             (address (proof-world-reg 19 world))
                             (value (collection-read-word (caar records) world))
                             (trace (collection-sweep-loop-code origin)))
                  (:instance collection-unmap-keeps-trace-placement
                             (trace (collection-sweep-loop-code origin))
                             (base (caar records)) (size (cadar records))
                             (world (collection-write-word (proof-world-reg 19 world)
                                                           (collection-read-word (caar records) world) world))))
            :in-theory (disable collection-sweep-writable-store-keeps-code-placement
                                collection-sweep-keep-write-covers-mark-and-link
                                collection-sweep-loop-code collection-unmap-keeps-trace-placement
                                collection-relinquish-range proof-remove-region-span)))))

(local
 (defthm collection-sweep-clearing-mark-keeps-link-word
   (implies (and (proof-span-p head 24)
                 (alistp (boymoo-model::a64-memory (proof-world-machine world))))
            (equal (collection-read-word head (collection-write-word (+ head 16) 0 world))
                   (collection-read-word head world)))
   :hints (("Goal" :in-theory (enable proof-span-p proof-disjoint-p)))))

(local
 (defthm collection-sweep-round-controls-and-link-value
   (let* ((after (collection-trace-effect (collection-sweep-round-trace record origin) world))
          (link (proof-world-reg 19 world))
          (head (car record))
          (size (cadr record))
          (keep (caddr record))
          (entry (collection-linux-offset "rt:sweep-string")))
     (implies (and (collection-sweep-entry-p entry origin world)
                   (collection-sweep-round-input-p record world))
              (and (collection-sweep-entry-p entry origin after)
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (equal (proof-world-page-size after) (proof-world-page-size world))
                   (equal (proof-world-reg 19 after) (if keep head link))
                   (equal (proof-world-reg 22 after) (+ (proof-world-reg 22 world) (if keep size 0)))
                   (equal (proof-world-replies after)
                          (if keep (proof-world-replies world) (cdr (proof-world-replies world))))
                   (equal (collection-read-word (if keep head link) after)
                          (collection-read-word head world))
                   (equal (proof-world-regions after)
                          (if keep (proof-world-regions world)
                            (proof-remove-region-span head size (proof-world-regions world)))))))
   :hints (("Goal"
            :cases ((caddr record))
            :in-theory (e/d (collection-sweep-entry-p proof-streams-preserved-p)
                             (proof-clear-memory proof-remove-region-span collection-relinquish-p
                              collection-sweep-clearing-mark-keeps-link-word))
            :do-not-induct t)
           ("Subgoal 1"
            :use ((:instance collection-sweep-retains-one-mapping-and-resets-mark (register 19))
                  (:instance collection-sweep-clearing-mark-keeps-link-word (head (car record)))
                  (:instance collection-word-read-from-equal-memories
                             (address (car record))
                             (first (collection-trace-effect (collection-sweep-retain-trace origin) world))
                             (second (collection-write-word (+ 16 (car record)) 0 world)))))
           ("Subgoal 2"
            :use ((:instance collection-sweep-discards-one-mapping-and-relinks (register 19)))))))

(local
 (defthm collection-sweep-round-preserves-link-and-loop-controls
   (let* ((after (collection-trace-effect (collection-sweep-round-trace (car records) origin) world))
          (link (proof-world-reg 19 after))
          (entry (collection-linux-offset "rt:sweep-string")))
     (implies (and (collection-sweep-loop-invariant-p records origin world) (consp records))
              (and (collection-sweep-entry-p entry origin after)
                   (not (proof-world-stop after))
                   (proof-page-size-p (proof-world-page-size after))
                   (equal (collection-read-word link after) (collection-sweep-next-head (cdr records)))
                   (proof-covered-p link 8 :write (proof-world-regions after))
                   (collection-sweep-spans-separate-p link (+ link 8) (cdr records))
                   (unsigned-byte-p 64 (+ (proof-world-reg 22 after)
                                          (collection-sweep-retained-bytes (cdr records))))
                   (collection-sweep-zero-replies-p (collection-sweep-discard-count (cdr records))
                                                    (proof-world-replies after)))))
   :hints (("Goal"
            :cases ((caddar records))
            :use ((:instance collection-sweep-snapshot-gives-round-premises)
                  (:instance collection-sweep-round-controls-and-link-value (record (car records)))
                  (:instance collection-sweep-keep-write-covers-mark-and-link
                             (head (caar records)) (size (cadar records))
                             (regions (proof-world-regions world)))
                  (:instance collection-sweep-subspan-separates-from-same-mappings
                             (address (caar records)) (width 8) (start (caar records))
                             (end (+ (caar records) (cadar records))) (records (cdr records)))
                  (:instance collection-sweep-nonempty-span-remains-covered
                             (base (caar records)) (size (cadar records))
                             (link (proof-world-reg 19 world)) (regions (proof-world-regions world))))
            :expand ((collection-sweep-retained-bytes records)
                     (collection-sweep-discard-count records))
            :in-theory (e/d (proof-subspan-p proof-span-p)
                             (collection-sweep-snapshot-gives-round-premises
                              collection-sweep-round-controls-and-link-value
                              collection-sweep-round-trace collection-sweep-round-input-p
                              collection-sweep-nonempty-span-remains-covered
                              collection-sweep-keep-write-covers-mark-and-link
                              proof-clear-memory proof-remove-region-span))))))
(local
 (defthm collection-sweep-snapshot-head-size-is-natural
   (implies (and (consp records) (collection-sweep-snapshot-p records world))
            (natp (cadar records)))
   :rule-classes :forward-chaining))

(defthm collection-sweep-round-maintains-unvisited-list-invariant
  (let ((after (collection-trace-effect (collection-sweep-round-trace (car records) origin) world)))
    (implies (and (collection-sweep-loop-invariant-p records origin world) (consp records))
             (collection-sweep-loop-invariant-p (cdr records) origin after)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-sweep-snapshot-gives-round-premises)
                 (:instance collection-sweep-round-matches-its-memory-world (record (car records)))
                 (:instance collection-sweep-round-preserves-link-and-loop-controls)
                 (:instance collection-sweep-updating-map-keeps-unvisited-snapshot)
                 (:instance collection-sweep-updating-map-keeps-loop-code)
                 (:instance collection-sweep-snapshot-depends-on-memory-regions-and-page-size
                            (records (cdr records))
                            (first (collection-trace-effect (collection-sweep-round-trace (car records) origin) world))
                            (second (collection-sweep-round-memory-world (car records) world)))
                 (:instance collection-matching-code-memory-and-regions-give-placement
                            (trace (collection-sweep-loop-code origin))
                            (first (collection-trace-effect (collection-sweep-round-trace (car records) origin) world))
                            (second (collection-sweep-round-memory-world (car records) world))))
           :cases ((caddar records))
           :in-theory (disable collection-sweep-round-trace collection-sweep-snapshot-p
                               collection-sweep-round-input-p collection-relinquish-range
                               proof-clear-memory proof-remove-region-span collection-sweep-loop-code))))

(local
 (defthm collection-sweep-round-excludes-accounting-entry
   (not (intersectp-equal
         (strip-cars (collection-sweep-round-trace record origin))
         (list (+ origin (collection-linux-offset "rt:sweep-done")))))
   :hints (("Goal"
            :cases ((caddr record))
            :in-theory (enable collection-sweep-retain-trace collection-sweep-discard-trace)))))

(local
 (defthm collection-sweep-empty-invariant-admits-exit
   (implies (and (collection-sweep-loop-invariant-p records origin world) (endp records))
            (and (collection-sweep-traversal-input-p records origin world)
                 (collection-trace-ready-p
                  (collection-sweep-traversal-trace records origin)
                  (list (+ origin (collection-linux-offset "rt:sweep-done"))) world)))
   :hints (("Goal" :use ((:instance collection-placed-sweep-terminator-is-ready))
                   :in-theory (disable collection-placed-sweep-terminator-is-ready)))))

(local
 (in-theory (disable collection-sweep-loop-invariant-p collection-sweep-round-input-p
                     collection-sweep-round-trace collection-sweep-snapshot-gives-round-premises
                     collection-sweep-snapshot-gives-round-readiness)))

(local
 (defthm collection-sweep-invariant-includes-loop-entry
   (implies (collection-sweep-loop-invariant-p records origin world)
            (collection-sweep-entry-p (collection-linux-offset "rt:sweep-string") origin world))
   :hints (("Goal" :in-theory (enable collection-sweep-loop-invariant-p)))))

(local
 (defthm collection-sweep-checked-round-precedes-traversal-suffix
   (let* ((round (collection-sweep-round-trace (car records) origin))
          (after (collection-trace-effect round world))
          (cut (list (+ origin (collection-linux-offset "rt:sweep-done")))))
     (implies (and (collection-sweep-loop-invariant-p records origin world)
                   (consp records)
                   (collection-sweep-traversal-input-p (cdr records) origin after)
                   (collection-trace-ready-p (collection-sweep-traversal-trace (cdr records) origin) cut after))
              (and (collection-sweep-traversal-input-p records origin world)
                   (collection-trace-ready-p (collection-sweep-traversal-trace records origin) cut world))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-sweep-invariant-includes-loop-entry)
                  (:instance collection-sweep-round-excludes-accounting-entry (record (car records)))
                  (:instance collection-sweep-snapshot-gives-round-premises)
                  (:instance collection-sweep-snapshot-gives-round-readiness)
                  (:instance collection-ready-loop-round-precedes-ready-suffix
                             (round (collection-sweep-round-trace (car records) origin))
                             (suffix (collection-sweep-traversal-trace (cdr records) origin))
                             (cuts (list (+ origin (collection-linux-offset "rt:sweep-done"))))))
            :expand ((collection-sweep-traversal-input-p records origin world)
                     (collection-sweep-traversal-trace records origin))
            :in-theory (disable collection-ready-loop-round-precedes-ready-suffix
                                collection-sweep-invariant-includes-loop-entry
                                collection-sweep-round-excludes-accounting-entry
                                collection-sweep-traversal-input-p collection-sweep-traversal-trace)))))

(local
 (defun collection-sweep-loop-induction (records origin world)
   (declare (xargs :measure (acl2-count records)))
   (if (endp records)
       world
     (collection-sweep-loop-induction
      (cdr records) origin
      (collection-trace-effect (collection-sweep-round-trace (car records) origin) world)))))

(defthm collection-sweep-invariant-supplies-checked-traversal
  (implies (collection-sweep-loop-invariant-p records origin world)
           (and (collection-sweep-traversal-input-p records origin world)
                (collection-trace-ready-p
                 (collection-sweep-traversal-trace records origin)
                 (list (+ origin (collection-linux-offset "rt:sweep-done"))) world)))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-sweep-loop-induction records origin world)
           :in-theory (disable collection-sweep-traversal-input-p collection-sweep-traversal-trace))
          ("Subgoal *1/2"
           :use ((:instance collection-sweep-round-maintains-unvisited-list-invariant)
                 (:instance collection-sweep-checked-round-precedes-traversal-suffix)))
          ("Subgoal *1/1"
           :use ((:instance collection-sweep-empty-invariant-admits-exit)))))

(defthm collection-sweep-from-snapshot-reaches-accounting-with-exact-effects
  (let* ((trace (collection-sweep-traversal-trace records origin))
         (after (collection-trace-effect trace world))
         (cut (list (+ origin (collection-linux-offset "rt:sweep-done"))))
         (link (proof-world-reg 19 world)))
    (implies (collection-sweep-loop-invariant-p records origin world)
             (and (proof-segment-p (len trace) cut world :cut after)
                  (collection-sweep-surviving-links-p link records after)
                  (equal (proof-world-reg 22 after)
                         (+ (proof-world-reg 22 world) (collection-sweep-retained-bytes records)))
                  (equal (proof-world-replies after)
                         (nthcdr (collection-sweep-discard-count records) (proof-world-replies world)))
                  (equal (proof-world-regions after)
                         (collection-sweep-surviving-regions records (proof-world-regions world))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance collection-sweep-invariant-supplies-checked-traversal)
                 (:instance collection-checked-sweep-traversal-reaches-accounting)
                 (:instance collection-sweep-traversal-links-survivors-and-clears-their-marks)
                 (:instance collection-sweep-traversal-removes-exactly-discarded-regions))
           :in-theory (e/d (collection-sweep-loop-invariant-p)
                            (collection-sweep-traversal-input-p collection-sweep-traversal-trace
                             collection-sweep-surviving-links-p collection-sweep-surviving-regions)))))
