(in-package "BOYMOO-PROOFS")

(include-book "rehash-table")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-load-word proof-world-machine
                     boymoo-model::a64-unsigned boymoo-model::a64-store
                     symbols-box-address symbols-load-register-word symbols-dynamic-mask-at
                     symbols-logical-right-shift-bits symbols-dynamic-bucket-at
                     symbols-rehash-entry-writes symbols-rehash-chain-links-p)))

(defun symbols-rehash-old-link-slot (word heap)
  (+ 24 (symbols-box-address word heap)))

(defun symbols-rehash-old-link-snapshot-p (links heap world)
  (if (atom links)
      (null links)
    (and (not (equal (car links) *proof-nil*))
         (equal (symbols-load-register-word (symbols-rehash-old-link-slot (car links) heap) world)
                (symbols-rehash-chain-head (cdr links)))
         (symbols-rehash-old-link-snapshot-p (cdr links) heap world))))

(defun symbols-rehash-old-slots-disjoint-from-p (links heap lower upper)
  (if (atom links)
      (null links)
    (let ((address (symbols-rehash-old-link-slot (car links) heap)))
      (and (proof-span-p address 8)
           (proof-disjoint-p address (+ address 8) lower upper)
           (symbols-rehash-old-slots-disjoint-from-p (cdr links) heap lower upper)))))

(defun symbols-rehash-old-link-layout-p (links heap table end)
  (if (atom links)
      (null links)
    (let ((address (symbols-rehash-old-link-slot (car links) heap)))
      (and (proof-span-p address 8)
           (proof-disjoint-p address (+ address 8) table end)
           (symbols-rehash-old-slots-disjoint-from-p (cdr links) heap address (+ address 8))
           (symbols-rehash-old-link-layout-p (cdr links) heap table end)))))

(local
 (in-theory (disable symbols-rehash-old-link-slot)))

(local
 (defthm symbols-rehash-layout-separates-old-slots-from-table
   (implies (symbols-rehash-old-link-layout-p links heap table end)
            (symbols-rehash-old-slots-disjoint-from-p links heap table end))
   :hints (("Goal" :induct (symbols-rehash-old-link-layout-p links heap table end)
                   :in-theory (disable proof-span-p proof-disjoint-p)))))

(local
 (defthm symbols-rehash-old-slots-separate-from-contained-span
   (implies (and (symbols-rehash-old-slots-disjoint-from-p links heap lower upper)
                 (<= lower start) (<= end upper))
            (symbols-rehash-old-slots-disjoint-from-p links heap start end))
   :hints (("Goal" :induct (symbols-rehash-old-slots-disjoint-from-p links heap lower upper)
                   :in-theory (disable proof-span-p)))
   :rule-classes nil))

(local
 (defthm symbols-rehash-box-address-is-natural
   (natp (symbols-box-address word heap))
   :hints (("Goal" :in-theory (enable symbols-box-address)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-rehash-shifted-hash-is-natural
   (natp (symbols-logical-right-shift-bits word 1))
   :hints (("Goal" :in-theory (enable symbols-logical-right-shift-bits)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-rehash-layout-bucket-address-in-table
   (let* ((address (symbols-dynamic-bucket-at table hash world))
          (end (+ table 16 (* 8 size))))
     (implies (and (posp size) (proof-span-p table (+ 16 (* 8 size)))
                   (equal (symbols-dynamic-mask-at table world) (1- size)))
              (and (proof-span-p address 8)
                   (<= (+ table 16) address)
                   (<= (+ address 8) end))))
   :hints (("Goal"
            :use ((:instance symbols-and-mask-bounds (mask (1- size))
                             (x (symbols-logical-right-shift-bits hash 1)))
                  (:instance symbols-logand-commutes (x (1- size)) (y (symbols-logical-right-shift-bits hash 1))))
            :in-theory (e/d (symbols-dynamic-bucket-at)
                            (acl2::binary-logand symbols-and-mask-bounds))))
   :rule-classes nil))

(local
 (defthm symbols-rehash-layout-loaded-word-is-view-word
   (equal (symbols-load-register-word address world) (proof-load-word address (proof-world-machine world)))
   :hints (("Goal" :in-theory (e/d (symbols-load-register-word proof-load-word symbols-word-load-fits)
                                   (boymoo-model::a64-load))))))

(local
 (defthm symbols-rehash-layout-two-stores-preserve-word
   (let ((after (symbols-write-words (list (cons first value) (cons second other)) world)))
     (implies (and (proof-span-p address 8) (proof-span-p first 8) (proof-span-p second 8)
                   (proof-disjoint-p address (+ address 8) first (+ first 8))
                   (proof-disjoint-p address (+ address 8) second (+ second 8)))
              (equal (symbols-load-register-word address after)
                     (symbols-load-register-word address world))))
   :hints (("Goal" :in-theory (disable update-nth)))
   :rule-classes nil))

(local
 (defthm symbols-rehash-unread-next-words-survive-two-stores
   (let ((after (symbols-write-words (list (cons first value) (cons second other)) world)))
     (implies (and (symbols-rehash-old-link-snapshot-p links heap world)
                   (proof-span-p first 8) (proof-span-p second 8)
                   (symbols-rehash-old-slots-disjoint-from-p links heap first (+ first 8))
                   (symbols-rehash-old-slots-disjoint-from-p links heap second (+ second 8)))
              (symbols-rehash-old-link-snapshot-p links heap after)))
   :hints (("Goal" :induct (symbols-rehash-old-link-snapshot-p links heap world)
                   :in-theory (disable symbols-write-words symbols-rehash-chain-head proof-span-p proof-disjoint-p))
           ("Subgoal *1/2"
            :use ((:instance symbols-rehash-layout-two-stores-preserve-word
                             (address (symbols-rehash-old-link-slot (car links) heap))))
            :in-theory (disable symbols-write-words symbols-rehash-chain-head proof-span-p proof-disjoint-p)))
   :rule-classes nil))

(local
 (defthm symbols-rehash-mask-reads-only-header
   (implies (equal (symbols-load-register-word table first) (symbols-load-register-word table last))
            (equal (symbols-dynamic-mask-at table first) (symbols-dynamic-mask-at table last)))
   :hints (("Goal"
            :in-theory (enable symbols-dynamic-mask-at)))
   :rule-classes nil))

(local
 (defthm symbols-rehash-separated-step-preserves-snapshot-and-mask
   (let* ((end (+ table 16 (* 8 size)))
          (after (symbols-write-words (symbols-rehash-entry-writes (car links) table heap before) before)))
     (implies (and (consp links) (posp size)
                   (proof-span-p table (+ 16 (* 8 size)))
                   (symbols-rehash-old-link-layout-p links heap table end)
                   (equal (symbols-dynamic-mask-at table before) (1- size))
                   (symbols-rehash-old-link-snapshot-p (cdr links) heap before))
              (and (symbols-rehash-old-link-snapshot-p (cdr links) heap after)
                   (equal (symbols-dynamic-mask-at table after) (1- size)))))
   :hints (("Goal"
            :use ((:instance symbols-rehash-layout-bucket-address-in-table
                             (world before)
                             (hash (symbols-load-register-word
                                    (+ 16 (symbols-box-address (car links) heap)) before)))
                  (:instance symbols-rehash-layout-separates-old-slots-from-table
                             (links (cdr links)) (end (+ table 16 (* 8 size))))
                  (:instance symbols-rehash-old-slots-separate-from-contained-span (links (cdr links))
                             (lower table) (upper (+ table 16 (* 8 size)))
                             (start (symbols-dynamic-bucket-at table (symbols-load-register-word
                                      (+ 16 (symbols-box-address (car links) heap)) before) before))
                             (end (+ 8 (symbols-dynamic-bucket-at table (symbols-load-register-word
                                         (+ 16 (symbols-box-address (car links) heap)) before) before))))
                  (:instance symbols-rehash-unread-next-words-survive-two-stores
                             (links (cdr links)) (world before)
                             (first (symbols-rehash-old-link-slot (car links) heap))
                             (second (caadr (symbols-rehash-entry-writes (car links) table heap before)))
                             (value (cdar (symbols-rehash-entry-writes (car links) table heap before)))
                             (other (car links)))
                  (:instance symbols-rehash-layout-two-stores-preserve-word
                             (address table) (world before)
                             (first (symbols-rehash-old-link-slot (car links) heap))
                             (second (caadr (symbols-rehash-entry-writes (car links) table heap before)))
                             (value (cdar (symbols-rehash-entry-writes (car links) table heap before)))
                             (other (car links)))
                  (:instance symbols-rehash-mask-reads-only-header (first before)
                             (last (symbols-write-words
                                    (symbols-rehash-entry-writes (car links) table heap before) before))))
            :in-theory (e/d (symbols-rehash-entry-writes symbols-rehash-old-link-slot)
                            (symbols-write-words symbols-rehash-old-link-snapshot-p
                             symbols-rehash-old-slots-disjoint-from-p
                             symbols-rehash-layout-separates-old-slots-from-table))))
   :rule-classes nil))

(local
 (defun symbols-rehash-separated-chain-induction (links table heap before)
   (if (atom links)
       before
     (symbols-rehash-separated-chain-induction
      (cdr links) table heap
      (symbols-write-words (symbols-rehash-entry-writes (car links) table heap before) before)))))

(defthm symbols-rehash-chain-schedule-follows-from-disjoint-link-slots
  (implies (and (posp size) (proof-span-p table (+ 16 (* 8 size)))
                (equal (symbols-dynamic-mask-at table before) (1- size))
                (symbols-rehash-old-link-layout-p links heap table (+ table 16 (* 8 size)))
                (symbols-rehash-old-link-snapshot-p links heap before))
           (symbols-rehash-chain-links-p links table heap before))
  :hints (("Goal"
           :induct (symbols-rehash-separated-chain-induction links table heap before)
           :in-theory (disable symbols-write-words proof-span-p proof-disjoint-p))
          ("Subgoal *1/2"
           :expand ((symbols-rehash-chain-links-p links table heap before))
           :use ((:instance symbols-rehash-separated-step-preserves-snapshot-and-mask))
           :in-theory (enable symbols-rehash-old-link-slot))
          ("Subgoal *1/1"
           :in-theory (enable symbols-rehash-chain-links-p)))
  :rule-classes nil)

(local
 (defthm symbols-rehash-entry-writes-preserve-unrelated-word
   (let* ((first (symbols-rehash-old-link-slot link heap))
          (end (+ table 16 (* 8 size)))
          (after (symbols-write-words (symbols-rehash-entry-writes link table heap before) before)))
     (implies (and (posp size) (proof-span-p table (+ 16 (* 8 size)))
                   (equal (symbols-dynamic-mask-at table before) (1- size))
                   (proof-span-p first 8) (proof-span-p address 8)
                   (proof-disjoint-p first (+ first 8) address (+ address 8))
                   (proof-disjoint-p address (+ address 8) (+ table 16) end))
              (equal (symbols-load-register-word address after)
                     (symbols-load-register-word address before))))
   :hints (("Goal"
            :use ((:instance symbols-rehash-layout-bucket-address-in-table (world before)
                             (hash (symbols-load-register-word (+ 16 (symbols-box-address link heap)) before)))
                  (:instance symbols-rehash-layout-two-stores-preserve-word (world before)
                             (first (car (car (symbols-rehash-entry-writes link table heap before))))
                             (second (caadr (symbols-rehash-entry-writes link table heap before)))
                             (value (cdar (symbols-rehash-entry-writes link table heap before)))
                             (other link)))
            :in-theory (e/d (symbols-rehash-entry-writes symbols-rehash-old-link-slot)
                            (symbols-write-words))))
   :rule-classes nil))

(defthm symbols-rehash-chain-preserves-disjoint-word
  (let ((after (symbols-rehash-chain-memory links table heap before))
        (end (+ table 16 (* 8 size))))
    (implies (and (posp size) (proof-span-p table (+ 16 (* 8 size)))
                  (equal (symbols-dynamic-mask-at table before) (1- size))
                  (proof-span-p address 8)
                  (proof-disjoint-p address (+ address 8) (+ table 16) end)
                  (symbols-rehash-old-slots-disjoint-from-p links heap address (+ address 8))
                  (symbols-rehash-old-link-layout-p links heap table end)
                  (symbols-rehash-old-link-snapshot-p links heap before))
             (and (equal (symbols-load-register-word address after)
                         (symbols-load-register-word address before))
                  (equal (symbols-dynamic-mask-at table after) (1- size)))))
  :hints (("Goal"
           :induct (symbols-rehash-separated-chain-induction links table heap before)
           :in-theory (disable symbols-write-words proof-span-p proof-disjoint-p))
          ("Subgoal *1/2"
           :use ((:instance symbols-rehash-separated-step-preserves-snapshot-and-mask)
                 (:instance symbols-rehash-entry-writes-preserve-unrelated-word (link (car links))))
           :in-theory (disable symbols-write-words proof-span-p proof-disjoint-p))
          ("Subgoal *1/1" :in-theory (enable symbols-rehash-chain-memory)))
  :rule-classes nil)

(defun symbols-rehash-old-table-snapshot-p (chains slot heap world)
  (if (atom chains)
      (null chains)
    (and (equal (symbols-load-register-word slot world) (symbols-rehash-chain-head (car chains)))
         (symbols-rehash-old-link-snapshot-p (car chains) heap world)
         (symbols-rehash-old-table-snapshot-p (cdr chains) (+ 8 slot) heap world))))

(defun symbols-rehash-next-slots-separate-from-chain-p (pending active heap table end)
  (if (atom pending)
      (null pending)
    (let ((address (symbols-rehash-old-link-slot (car pending) heap)))
      (and (proof-span-p address 8)
           (proof-disjoint-p address (+ address 8) table end)
           (symbols-rehash-old-slots-disjoint-from-p active heap address (+ address 8))
           (symbols-rehash-next-slots-separate-from-chain-p (cdr pending) active heap table end)))))

(defun symbols-rehash-buckets-separate-from-chain-p (pending active heap table end)
  (if (atom pending)
      (null pending)
    (and (symbols-rehash-next-slots-separate-from-chain-p (car pending) active heap table end)
         (symbols-rehash-buckets-separate-from-chain-p (cdr pending) active heap table end))))

(defun symbols-rehash-table-link-layout-p (chains heap table end old-start old-end)
  (if (atom chains)
      (null chains)
    (and (symbols-rehash-old-link-layout-p (car chains) heap table end)
         (symbols-rehash-old-slots-disjoint-from-p (car chains) heap old-start old-end)
         (symbols-rehash-buckets-separate-from-chain-p (cdr chains) (car chains) heap table end)
         (symbols-rehash-table-link-layout-p (cdr chains) heap table end old-start old-end))))

(defun symbols-rehash-old-head-positions-p (chains slot old-start old-end table end)
  (and (natp slot) (natp old-start) (natp old-end) (< old-end (expt 2 64))
       (<= old-start slot) (<= (+ slot (* 8 (len chains))) old-end)
       (proof-disjoint-p old-start old-end table end)))

(local
 (defthm symbols-rehash-current-head-position-is-disjoint
   (implies (and (consp chains) (symbols-rehash-old-head-positions-p chains slot old-start old-end table end))
            (and (symbols-rehash-old-head-positions-p (cdr chains) (+ 8 slot) old-start old-end table end)
                 (proof-span-p slot 8)
                 (<= old-start slot)
                 (<= (+ 8 slot) old-end)
                 (proof-disjoint-p slot (+ 8 slot) table end)))
   :hints (("Goal" :expand ((len chains))))
   :rule-classes nil))

(local
 (defthm symbols-rehash-separate-word-spans
   (implies (and (proof-disjoint-p address (+ address 8) table end)
                 (natp table) (natp end))
            (proof-disjoint-p address (+ address 8) (+ 16 table) end))))

(local
 (defthm symbols-rehash-chain-preserves-other-bucket-snapshot
   (let* ((end (+ table 16 (* 8 size)))
          (after (symbols-rehash-chain-memory active table heap before)))
     (implies (and (symbols-rehash-old-link-snapshot-p pending heap before)
                   (symbols-rehash-next-slots-separate-from-chain-p pending active heap table end)
                   (posp size) (proof-span-p table (+ 16 (* 8 size)))
                   (equal (symbols-dynamic-mask-at table before) (1- size))
                   (symbols-rehash-old-link-layout-p active heap table end)
                   (symbols-rehash-old-link-snapshot-p active heap before))
              (symbols-rehash-old-link-snapshot-p pending heap after)))
   :hints (("Goal"
            :induct (symbols-rehash-old-link-snapshot-p pending heap before)
            :in-theory (disable symbols-rehash-chain-memory symbols-rehash-chain-head
                                symbols-rehash-old-link-layout-p symbols-rehash-old-slots-disjoint-from-p))
           ("Subgoal *1/2"
            :use ((:instance symbols-rehash-chain-preserves-disjoint-word (links active)
                             (address (symbols-rehash-old-link-slot (car pending) heap))))
            :in-theory (disable symbols-rehash-chain-memory symbols-rehash-chain-head
                                symbols-rehash-old-link-layout-p symbols-rehash-old-slots-disjoint-from-p)))
   :rule-classes nil))

(local
 (defun symbols-rehash-old-head-snapshot-induction (chains slot)
   (if (atom chains)
       slot
     (symbols-rehash-old-head-snapshot-induction (cdr chains) (+ 8 slot)))))

(local
 (defthm symbols-rehash-chain-preserves-rest-of-table-snapshot
   (let* ((end (+ table 16 (* 8 size)))
          (after (symbols-rehash-chain-memory active table heap before)))
     (implies (and (symbols-rehash-old-table-snapshot-p pending slot heap before)
                   (symbols-rehash-old-head-positions-p pending slot old-start old-end table end)
                   (symbols-rehash-old-slots-disjoint-from-p active heap old-start old-end)
                   (symbols-rehash-buckets-separate-from-chain-p pending active heap table end)
                   (posp size) (proof-span-p table (+ 16 (* 8 size)))
                   (equal (symbols-dynamic-mask-at table before) (1- size))
                   (symbols-rehash-old-link-layout-p active heap table end)
                   (symbols-rehash-old-link-snapshot-p active heap before))
              (symbols-rehash-old-table-snapshot-p pending slot heap after)))
   :hints (("Goal"
            :induct (symbols-rehash-old-head-snapshot-induction pending slot)
            :in-theory (disable symbols-rehash-chain-memory symbols-rehash-chain-head
                                symbols-rehash-old-link-snapshot-p symbols-rehash-old-link-layout-p
                                symbols-rehash-old-head-positions-p symbols-rehash-old-slots-disjoint-from-p
                                symbols-rehash-next-slots-separate-from-chain-p))
           ("Subgoal *1/2"
            :use ((:instance symbols-rehash-current-head-position-is-disjoint
                             (chains pending) (end (+ table 16 (* 8 size))))
                  (:instance symbols-rehash-old-slots-separate-from-contained-span (links active) (lower old-start)
                             (upper old-end) (start slot) (end (+ 8 slot)))
                  (:instance symbols-rehash-chain-preserves-disjoint-word (links active) (address slot))
                  (:instance symbols-rehash-chain-preserves-other-bucket-snapshot (pending (car pending))))
            :in-theory (disable symbols-rehash-chain-memory symbols-rehash-chain-head
                                symbols-rehash-old-link-snapshot-p symbols-rehash-old-link-layout-p
                                symbols-rehash-old-head-positions-p symbols-rehash-old-slots-disjoint-from-p
                                symbols-rehash-next-slots-separate-from-chain-p)))
   :rule-classes nil))

(local
 (defun symbols-rehash-static-table-induction (chains slot heap table before)
   (if (atom chains)
       (cons slot before)
     (symbols-rehash-static-table-induction
      (cdr chains) (+ 8 slot) heap table
      (symbols-rehash-chain-memory (car chains) table heap before)))))

(defthm symbols-rehash-table-schedule-follows-from-disjoint-link-layout
  (let ((end (+ table 16 (* 8 size))))
    (implies (and (posp size) (proof-span-p table (+ 16 (* 8 size)))
                  (equal (symbols-dynamic-mask-at table before) (1- size))
                  (symbols-rehash-old-head-positions-p chains slot old-start old-end table end)
                  (symbols-rehash-table-link-layout-p chains heap table end old-start old-end)
                  (symbols-rehash-old-table-snapshot-p chains slot heap before))
             (symbols-rehash-table-chains-p chains slot table heap before)))
  :hints (("Goal"
           :induct (symbols-rehash-static-table-induction chains slot heap table before)
           :in-theory (disable symbols-rehash-table-chains-p symbols-rehash-chain-memory
                               symbols-rehash-chain-head symbols-rehash-old-head-positions-p
                               symbols-rehash-old-link-layout-p symbols-rehash-old-link-snapshot-p
                               symbols-rehash-old-slots-disjoint-from-p
                               symbols-rehash-buckets-separate-from-chain-p))
          ("Subgoal *1/2"
           :use ((:instance symbols-rehash-current-head-position-is-disjoint (end (+ table 16 (* 8 size))))
                 (:instance symbols-rehash-old-slots-separate-from-contained-span (links (car chains))
                            (lower old-start) (upper old-end) (start slot) (end (+ 8 slot)))
                 (:instance symbols-rehash-chain-preserves-disjoint-word (links (car chains)) (address slot))
                 (:instance symbols-rehash-chain-schedule-follows-from-disjoint-link-slots (links (car chains)))
                 (:instance symbols-rehash-chain-preserves-rest-of-table-snapshot
                            (pending (cdr chains)) (active (car chains)) (slot (+ 8 slot))))
           :expand ((symbols-rehash-table-chains-p chains slot table heap before))
           :in-theory (disable symbols-rehash-table-chains-p symbols-rehash-chain-memory
                               symbols-rehash-chain-head symbols-rehash-old-head-positions-p
                               symbols-rehash-old-link-layout-p symbols-rehash-old-link-snapshot-p
                               symbols-rehash-old-slots-disjoint-from-p
                               symbols-rehash-buckets-separate-from-chain-p))
          ("Subgoal *1/1" :in-theory (enable symbols-rehash-table-chains-p)))
  :rule-classes nil)

(defthm symbols-run-rehash-table-from-disjoint-layout
  (let* ((slot (proof-world-reg 6 before))
         (old-end (proof-world-reg 7 before))
         (table (proof-world-reg 1 before))
         (heap (proof-heap-base before))
         (end (+ table 16 (* 8 size))))
    (implies (and (symbols-rehash-bucket-pre-p code-base before)
                  (equal old-end (+ slot (* 8 (len chains))))
                  (posp size) (proof-span-p table (+ 16 (* 8 size)))
                  (equal (symbols-dynamic-mask-at table before) (1- size))
                  (symbols-rehash-old-head-positions-p chains slot slot old-end table end)
                  (symbols-rehash-table-link-layout-p chains heap table end slot old-end)
                  (symbols-rehash-old-table-snapshot-p chains slot heap before)
                  (symbols-rehash-table-ready-p chains code-base before))
             (symbols-rehash-table-frame-p chains code-base before
                                          (proof-advance (symbols-rehash-table-fuel chains) before))))
  :hints (("Goal"
           :use ((:instance symbols-run-rehash-all-buckets)
                 (:instance symbols-rehash-table-schedule-follows-from-disjoint-link-layout
                            (slot (proof-world-reg 6 before)) (old-start (proof-world-reg 6 before))
                            (old-end (proof-world-reg 7 before)) (table (proof-world-reg 1 before))
                            (heap (proof-heap-base before))))
           :in-theory (disable proof-advance proof-world-reg proof-heap-base symbols-rehash-table-fuel
                               symbols-rehash-bucket-pre-p symbols-rehash-table-frame-p
                               symbols-rehash-table-ready-p symbols-rehash-table-chains-p
                               symbols-rehash-old-head-positions-p symbols-rehash-table-link-layout-p
                               symbols-rehash-old-table-snapshot-p)))
  :rule-classes nil)
