(in-package "BOYMOO-PROOFS")

(include-book "sweep-contents")
(include-book "unmap-placement")
(include-book "marks")
(local (include-book "std/lists/update-nth" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defun collection-sweep-next-head (records)
  (if (endp records) 0 (caar records)))

; A snapshot describes only the mappings the sweep has yet to visit.
; It records links, sizes and marks and the kernel conditions on the
; individual mappings. The link that starts the suffix is separate.
(defun collection-sweep-snapshot-p (records world)
  (if (endp records)
      t
    (let* ((head (caar records))
           (size (cadar records))
           (page (proof-world-page-size world)))
      (and (posp head) (natp size) (<= 24 size)
           (proof-covered-p head size :write (proof-world-regions world))
           (equal (mod head page) 0)
           (equal (proof-align-up size page) size)
           (equal (collection-read-word head world) (collection-sweep-next-head (cdr records)))
           (equal (collection-read-word (+ head 8) world) size)
           (equal (collection-read-word (+ head 16) world) (if (caddar records) 1 0))
           (collection-sweep-snapshot-p (cdr records) world)))))

(local
 (in-theory (disable collection-read-word proof-load-word proof-world-machine
                     proof-world-regions proof-world-page-size proof-world-reg proof-world-stop
                     proof-region-p proof-regions-p proof-covered-p proof-align-up mod
                     collection-write-word collection-relinquish-range proof-clear-span
                     proof-remove-region-span proof-clear-memory boymoo-model::a64-memory
                     boymoo-model::a64-read-bytes boymoo-model::a64-unsigned
                     (:definition ash) (:definition acl2::binary-logior)
                     nth update-nth)))

(local
 (defthm collection-snapshot-page-size-after-memory-change
   (and (equal (proof-world-page-size (collection-write-word address value world))
               (proof-world-page-size world))
        (equal (proof-world-page-size (collection-relinquish-range t base size world))
               (proof-world-page-size world)))
   :hints (("Goal"
            :in-theory (enable proof-world-page-size collection-relinquish-range proof-clear-span nth)))))

(defthm collection-sweep-snapshot-depends-on-memory-regions-and-page-size
  (implies (and (equal (boymoo-model::a64-memory (proof-world-machine first))
                       (boymoo-model::a64-memory (proof-world-machine second)))
                (equal (proof-world-regions first) (proof-world-regions second))
                (equal (proof-world-page-size first) (proof-world-page-size second)))
           (equal (collection-sweep-snapshot-p records first)
                  (collection-sweep-snapshot-p records second)))
  :rule-classes nil
  :hints (("Goal"
           :induct (len records)
           :in-theory (enable collection-read-word proof-load-word
                              boymoo-model::a64-load))))

(local
 (defthm collection-sweep-mapping-metadata-is-disjoint-from-other-span
   (implies (and (proof-span-p head size) (<= 24 size)
                 (proof-disjoint-p start end head (+ head size)))
            (and (proof-span-p head 8)
                 (proof-span-p (+ head 8) 8)
                 (proof-span-p (+ head 16) 8)
                 (proof-disjoint-p head (+ head 8) start end)
                 (proof-disjoint-p (+ head 8) (+ head 16) start end)
                 (proof-disjoint-p (+ head 16) (+ head 24) start end)))))

(defthm collection-separated-store-preserves-sweep-snapshot
  (implies (and (collection-sweep-snapshot-p records world)
                (collection-sweep-spans-separate-p start (+ start 8) records)
                (proof-span-p start 8)
                (alistp (boymoo-model::a64-memory (proof-world-machine world))))
           (collection-sweep-snapshot-p records (collection-write-word start value world)))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-sweep-snapshot-p records world)
           :in-theory (disable proof-disjoint-p proof-span-p
                               collection-sweep-mapping-metadata-is-disjoint-from-other-span))
          ("Subgoal *1/2"
           :use ((:instance collection-sweep-mapping-metadata-is-disjoint-from-other-span
                            (head (caar records)) (size (cadar records)) (end (+ start 8)))))))

(local
 (defthm collection-sweep-unmap-keeps-other-mapping-covered
   (implies (and (posp size)
                 (proof-covered-p head size :write regions)
                 (proof-disjoint-p base (+ base bytes) head (+ head size)))
            (proof-covered-p head size :write (proof-remove-region-span base bytes regions)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance collection-removal-preserves-disjoint-coverage
                             (address head) (width size) (size bytes) (access :write)))
            :in-theory (disable collection-removal-preserves-disjoint-coverage)))))

(local
 (defthm collection-sweep-relinquish-regions-and-word
   (let ((after (collection-relinquish-range t base size world)))
     (and (equal (proof-world-regions after)
                 (proof-remove-region-span base size (proof-world-regions world)))
          (equal (collection-read-word address after)
                 (collection-read-word address (proof-clear-span base (+ base size) world)))))
   :hints (("Goal"
            :in-theory (enable proof-world-regions proof-world-machine
                               collection-read-word collection-relinquish-range)))))

(defthm collection-separated-unmap-preserves-sweep-snapshot
  (implies (and (collection-sweep-snapshot-p records world)
                (collection-sweep-spans-separate-p base (+ base bytes) records)
                (alistp (boymoo-model::a64-memory (proof-world-machine world))))
           (collection-sweep-snapshot-p records (collection-relinquish-range t base bytes world)))
  :rule-classes nil
  :hints (("Goal"
           :induct (collection-sweep-snapshot-p records world)
           :in-theory (disable proof-disjoint-p proof-span-p
                               collection-removal-preserves-disjoint-coverage))
          ("Subgoal *1/2"
           :use ((:instance collection-sweep-unmap-keeps-other-mapping-covered
                            (regions (proof-world-regions world))
                            (head (caar records)) (size (cadar records)))
                 (:instance collection-sweep-mapping-metadata-is-disjoint-from-other-span
                            (head (caar records)) (size (cadar records))
                            (start base) (end (+ base bytes)))))))
