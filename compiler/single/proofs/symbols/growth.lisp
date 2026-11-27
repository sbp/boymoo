(in-package "BOYMOO-PROOFS")

(include-book "rehash")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                    (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg
                     proof-advance proof-register-frame-p proof-advance-append
                     boymoo-model::a64-unsigned
                     symbols-path-ready-p symbols-runtime-offset
                     symbols-no-memory-or-kernel-change-p)))

(defun symbols-clear-buckets-writes (count address)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (cons address *proof-nil*)
          (symbols-clear-buckets-writes (1- count) (+ address 8)))))

(defun symbols-clear-buckets-input-p (count base world)
  (and (posp count)
       (symbols-clear-bucket-pre-p base world)
       (equal (proof-world-reg 2 world) (+ (proof-world-reg 4 world) (* 8 count)))
       (equal (proof-world-reg 0 world) *proof-nil*)))

(defun symbols-clear-buckets-ready-p (count base before)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (and (symbols-path-ready-p *symbols-clear-bucket-path* base nil before)
         (symbols-clear-buckets-ready-p
          (1- count) base (proof-advance (len *symbols-clear-bucket-path*) before)))))

(defun symbols-clear-buckets-frame-p (count base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (+ 16 (symbols-runtime-address "rt:intern-clear-buckets" base)))
       (equal (proof-world-reg 4 after) (+ (proof-world-reg 4 before) (* 8 count)))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-register-frame-p 30 '(4) before after)
       (symbols-no-memory-or-kernel-change-p
        (symbols-write-words (symbols-clear-buckets-writes count (proof-world-reg 4 before)) before)
        after)))

(local
 (defthm symbols-clear-register-fits-word
   (< (proof-world-reg register world) (expt 2 64))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))
   :rule-classes :linear))

(local
 (defthm symbols-clear-next-input
   (implies (and (symbols-clear-buckets-input-p count base before) (< 1 count)
                 (symbols-clear-bucket-frame-p base before middle))
            (symbols-clear-buckets-input-p (1- count) base middle))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (clobbers '(4)) (register 0) (after middle))
                  (:instance symbols-frame-gives-register (highest 30) (clobbers '(4)) (register 2) (after middle))
                  (:instance symbols-clear-register-fits-word (register 2) (world before)))
            :in-theory (disable symbols-clear-bucket-memory)))
   :rule-classes nil))

(local
 (defthm symbols-clear-write-uses-same-memory
   (implies (symbols-no-memory-or-kernel-change-p first last)
            (symbols-no-memory-or-kernel-change-p
             (update-nth 0 (boymoo-model::a64-store 8 address value (proof-world-machine first)) first)
             (update-nth 0 (boymoo-model::a64-store 8 address value (proof-world-machine last)) last)))
   :hints (("Goal"
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p boymoo-model::a64-store
                             boymoo-model::a64-memory proof-world-machine)
                            (boymoo-model::a64-write-bytes update-nth))))))

(local
 (defthm symbols-clear-writes-use-same-memory
   (implies (symbols-no-memory-or-kernel-change-p first last)
            (symbols-no-memory-or-kernel-change-p (symbols-write-words writes first)
                                                  (symbols-write-words writes last)))
   :hints (("Goal" :induct (list (symbols-write-words writes first) (symbols-write-words writes last))
                   :in-theory (disable boymoo-model::a64-store update-nth proof-world-machine)))))

(local
 (defthm symbols-clear-write-leading-word
   (equal (symbols-write-words (cons (cons address value) rest) before)
          (symbols-write-words rest
                               (update-nth 0 (boymoo-model::a64-store 8 address value
                                                                        (proof-world-machine before)) before)))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-store update-nth)))))

(local
 (defthm symbols-clear-buckets-frames-compose
   (implies (and (symbols-clear-buckets-input-p count base before) (< 1 count)
                 (symbols-clear-bucket-frame-p base before middle)
                 (symbols-clear-buckets-frame-p (1- count) base middle after))
            (symbols-clear-buckets-frame-p count base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-is-transitive (highest 30) (clobbers '(4)) (first before) (last after))
                  (:instance symbols-clear-writes-use-same-memory
                             (writes (symbols-clear-buckets-writes (1- count) (+ 8 (proof-world-reg 4 before))))
                             (first (symbols-clear-bucket-memory before)) (last middle))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-write-words (symbols-clear-buckets-writes count (proof-world-reg 4 before))
                                                         before))
                             (middle (symbols-write-words
                                      (symbols-clear-buckets-writes (1- count) (+ 8 (proof-world-reg 4 before))) middle))
                             (last after)))
            :expand ((symbols-clear-buckets-writes count (proof-world-reg 4 before)))
            :in-theory (disable symbols-clear-buckets-writes symbols-write-words
                                symbols-clear-writes-use-same-memory boymoo-model::a64-store update-nth)))
   :rule-classes nil))

(local
 (defthm symbols-clear-last-bucket-finishes
   (implies (and (symbols-clear-buckets-input-p 1 base before)
                 (symbols-clear-bucket-frame-p base before after))
            (symbols-clear-buckets-frame-p 1 base before after))
   :hints (("Goal" :in-theory (disable boymoo-model::a64-store update-nth)))
   :rule-classes nil))

(defthm symbols-run-clear-buckets
  (implies (and (symbols-clear-buckets-input-p count code-base before)
                (symbols-clear-buckets-ready-p count code-base before))
           (symbols-clear-buckets-frame-p count code-base before (proof-advance (* 4 count) before)))
  :hints (("Goal" :induct (symbols-clear-buckets-ready-p count code-base before)
                  :in-theory (disable symbols-clear-buckets-input-p symbols-clear-buckets-frame-p))
          ("Subgoal *1/2"
           :use ((:instance symbols-run-clear-bucket)
                 (:instance symbols-clear-next-input (base code-base) (middle (proof-advance 4 before)))
                 (:instance symbols-clear-last-bucket-finishes (base code-base) (after (proof-advance 4 before)))
                 (:instance proof-advance-append (prefix 4) (suffix (* 4 (1- count))) (world before))
                 (:instance symbols-clear-buckets-frames-compose (base code-base)
                            (middle (proof-advance 4 before)) (after (proof-advance (* 4 count) before))))
           :in-theory (disable symbols-clear-buckets-frame-p symbols-clear-bucket-frame-p))
          ("Subgoal *1/1" :in-theory (enable symbols-clear-buckets-input-p)))
  :rule-classes nil)

(defun symbols-rehash-entry-writes (word table heap before)
  (let* ((entry (symbols-box-address word heap))
         (hash (symbols-load-register-word (+ entry 16) before))
         (slot (symbols-dynamic-bucket-at table hash before))
         (head (symbols-load-register-word slot before)))
    (list (cons (+ entry 24) head) (cons slot word))))

(defun symbols-rehash-chain-memory (links table heap before)
  (if (atom links)
      before
    (symbols-rehash-chain-memory
     (cdr links) table heap
     (symbols-write-words (symbols-rehash-entry-writes (car links) table heap before) before))))

; Each link in the list must be readable as the next old entry at
; the point when the algorithm consumes it. The last entry ends in NIL.
(defun symbols-rehash-chain-links-p (links table heap before)
  (if (atom links)
      (null links)
    (let* ((link (car links))
           (next (if (consp (cdr links)) (cadr links) *proof-nil*))
           (address (symbols-box-address link heap)))
      (and (not (equal link *proof-nil*))
           (equal (symbols-load-register-word (+ address 24) before) next)
           (symbols-rehash-chain-links-p
            (cdr links) table heap
            (symbols-write-words (symbols-rehash-entry-writes link table heap before) before))))))

(local
 (defthm symbols-rehash-chain-memory-agrees-with-step
   (equal (symbols-write-words
           (symbols-rehash-entry-writes (proof-world-reg 5 before) (proof-world-reg 1 before)
                                        (proof-heap-base before) before)
           before)
          (symbols-rehash-memory-effect before))
   :hints (("Goal" :in-theory (disable symbols-dynamic-bucket-at symbols-load-register-word symbols-box-address
                                      boymoo-model::a64-store update-nth)))))

(local
 (defthm symbols-rehash-entry-writes-depend-on-memory
   (implies (symbols-no-memory-or-kernel-change-p first last)
            (and (equal (symbols-rehash-entry-writes word table heap first)
                        (symbols-rehash-entry-writes word table heap last))
                 (equal (symbols-load-register-word address first)
                        (symbols-load-register-word address last))))
   :hints (("Goal" :in-theory (e/d (symbols-no-memory-or-kernel-change-p boymoo-model::a64-load)
                                   (symbols-box-address symbols-logical-right-shift-bits))))))

(defthmd symbols-rehash-chain-links-depend-on-memory
  (implies (symbols-no-memory-or-kernel-change-p first last)
           (equal (symbols-rehash-chain-links-p links table heap first)
                  (symbols-rehash-chain-links-p links table heap last)))
  :hints (("Goal" :induct (list (symbols-rehash-chain-links-p links table heap first)
                                 (symbols-rehash-chain-links-p links table heap last))
                  :in-theory (disable symbols-rehash-entry-writes symbols-box-address symbols-load-register-word
                                      symbols-write-words))))

(defthmd symbols-rehash-chain-memory-uses-equivalent-inputs
  (implies (symbols-no-memory-or-kernel-change-p first last)
           (symbols-no-memory-or-kernel-change-p (symbols-rehash-chain-memory links table heap first)
                                                 (symbols-rehash-chain-memory links table heap last)))
  :hints (("Goal" :induct (list (symbols-rehash-chain-memory links table heap first)
                                 (symbols-rehash-chain-memory links table heap last))
                  :in-theory (disable symbols-rehash-entry-writes symbols-write-words))))

(defun symbols-rehash-chain-head (links)
  (if (consp links) (car links) *proof-nil*))

(defun symbols-rehash-chain-input-p (links base before)
  (and (symbols-rehash-prefix-pre-p base before)
       (equal (proof-world-reg 5 before) (symbols-rehash-chain-head links))
       (symbols-rehash-chain-links-p links (proof-world-reg 1 before) (proof-heap-base before) before)))

(defun symbols-rehash-chain-ready-p (links base before)
  (and (symbols-rehash-entry-ready-p base before)
       (or (atom links) (symbols-rehash-chain-ready-p (cdr links) base (symbols-rehash-entry-finish before)))))

(defconst *symbols-rehash-chain-clobbers* '(3 4 5 8 9 10 30))

(defun symbols-rehash-chain-frame-p (links base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-rehash-bucket" base))
       (equal (proof-world-reg 5 after) *proof-nil*)
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-register-frame-p 30 *symbols-rehash-chain-clobbers* before after)
       (symbols-no-memory-or-kernel-change-p
        (symbols-rehash-chain-memory links (proof-world-reg 1 before) (proof-heap-base before) before) after)))

(local
 (defthm symbols-rehash-nonempty-plan-reads-link
   (implies (and (consp links) (symbols-rehash-chain-links-p links table heap before))
            (and (not (equal (car links) *proof-nil*))
                 (equal (symbols-load-register-word (+ (symbols-box-address (car links) heap) 24) before)
                        (symbols-rehash-chain-head (cdr links)))
                 (symbols-rehash-chain-links-p
                  (cdr links) table heap
                  (symbols-write-words (symbols-rehash-entry-writes (car links) table heap before) before))))
   :hints (("Goal"
            :expand ((symbols-rehash-chain-links-p links table heap before))
            :in-theory (disable symbols-rehash-chain-links-p symbols-rehash-entry-writes
                                symbols-load-register-word symbols-write-words symbols-box-address)))
   :rule-classes nil))

(local
 (defthm symbols-rehash-next-in-chain
   (implies (and (consp links) (symbols-rehash-chain-input-p links base before)
                 (symbols-rehash-entry-frame-p base before middle))
            (symbols-rehash-chain-input-p (cdr links) base middle))
   :hints (("Goal"
            :use ((:instance symbols-rehash-nonempty-plan-reads-link
                             (table (proof-world-reg 1 before)) (heap (proof-heap-base before)))
                  (:instance symbols-rehash-chain-memory-agrees-with-step)
                  (:instance symbols-frame-gives-register (highest 30) (register 1)
                             (clobbers *symbols-rehash-chain-clobbers*) (after middle))
                  (:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers *symbols-rehash-chain-clobbers*) (after middle))
                  (:instance symbols-rehash-chain-links-depend-on-memory (links (cdr links))
                             (table (proof-world-reg 1 before)) (heap (proof-heap-base before))
                             (first (symbols-rehash-memory-effect before)) (last middle)))
            :in-theory (e/d (proof-heap-base)
                            (symbols-rehash-chain-links-p symbols-rehash-chain-links-depend-on-memory
                             symbols-rehash-memory-effect symbols-rehash-entry-writes symbols-write-words
                             symbols-rehash-selected-bucket symbols-load-register-word symbols-box-address
                             symbols-rehash-chain-memory-agrees-with-step))))
   :rule-classes nil))

(local
 (defthm symbols-rehash-chain-frame-composition
   (implies (and (consp links) (symbols-rehash-chain-input-p links base before)
                 (symbols-rehash-entry-frame-p base before middle)
                 (symbols-rehash-chain-frame-p (cdr links) base middle after))
            (symbols-rehash-chain-frame-p links base before after))
   :hints (("Goal"
            :use ((:instance symbols-rehash-nonempty-plan-reads-link
                             (table (proof-world-reg 1 before)) (heap (proof-heap-base before)))
                  (:instance symbols-rehash-chain-memory-agrees-with-step)
                  (:instance symbols-frame-gives-register (highest 30) (register 1)
                             (clobbers *symbols-rehash-chain-clobbers*) (after middle))
                  (:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers *symbols-rehash-chain-clobbers*) (after middle))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-rehash-chain-clobbers*)
                             (first before) (last after))
                  (:instance symbols-rehash-chain-memory-uses-equivalent-inputs (links (cdr links))
                             (table (proof-world-reg 1 before)) (heap (proof-heap-base before))
                             (first (symbols-rehash-memory-effect before)) (last middle))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-rehash-chain-memory links (proof-world-reg 1 before)
                                                                 (proof-heap-base before) before))
                             (middle (symbols-rehash-chain-memory (cdr links) (proof-world-reg 1 before)
                                                                  (proof-heap-base before) middle))
                             (last after)))
            :expand ((:free (heap) (symbols-rehash-chain-memory links (proof-world-reg 1 before) heap before)))
            :in-theory (e/d (proof-heap-base)
                            (symbols-rehash-chain-links-p symbols-rehash-chain-memory symbols-rehash-memory-effect
                             symbols-rehash-entry-writes symbols-rehash-chain-memory-uses-equivalent-inputs
                             symbols-write-words symbols-rehash-selected-bucket symbols-load-register-word
                             symbols-box-address symbols-rehash-chain-memory-agrees-with-step))))
   :rule-classes nil))

(local
 (defthm symbols-empty-rehash-chain-finishes
   (implies (and (atom links) (symbols-rehash-chain-input-p links base before)
                 (symbols-rehash-entry-frame-p base before after))
            (symbols-rehash-chain-frame-p links base before after))))

(defconst *symbols-rehash-entry-step-count*
  (+ (len *symbols-rehash-prefix-path*) (len *symbols-bucket-address-path*) (len *symbols-rehash-link-path*)))

(defun symbols-rehash-chain-fuel (links)
  (+ (len *symbols-rehash-skip-path*) (* (len links) *symbols-rehash-entry-step-count*)))

(local
 (defthm symbols-rehash-chain-input-selects-step
   (implies (symbols-rehash-chain-input-p links base before)
            (equal (symbols-rehash-end-of-chain-p before) (atom links)))
   :hints (("Goal"
            :use ((:instance symbols-rehash-nonempty-plan-reads-link
                             (table (proof-world-reg 1 before)) (heap (proof-heap-base before))))
            :in-theory (disable symbols-rehash-chain-links-p proof-heap-base)))
   :rule-classes nil))

(local
 (defthm symbols-rehash-step-count-agrees-with-advance
   (equal (symbols-rehash-entry-finish before)
          (proof-advance (if (symbols-rehash-end-of-chain-p before) (len *symbols-rehash-skip-path*)
                           *symbols-rehash-entry-step-count*) before))
   :hints (("Goal"
            :use ((:instance proof-advance-append
                             (prefix (len *symbols-rehash-prefix-path*)) (suffix (len *symbols-bucket-address-path*))
                             (world before))
                  (:instance proof-advance-append
                             (prefix (+ (len *symbols-rehash-prefix-path*) (len *symbols-bucket-address-path*)))
                             (suffix (len *symbols-rehash-link-path*)) (world before)))
            :in-theory (disable symbols-rehash-end-of-chain-p)))))

(defthm symbols-run-rehash-chain
  (implies (and (symbols-rehash-chain-input-p links code-base before)
                (symbols-rehash-chain-ready-p links code-base before))
           (symbols-rehash-chain-frame-p links code-base before
                                         (proof-advance (symbols-rehash-chain-fuel links) before)))
  :hints (("Goal" :induct (symbols-rehash-chain-ready-p links code-base before)
                  :in-theory (disable symbols-rehash-chain-input-p symbols-rehash-chain-frame-p
                                      symbols-rehash-entry-ready-p))
          ("Subgoal *1/2"
           :use ((:instance symbols-run-rehash-entry)
                 (:instance symbols-rehash-chain-input-selects-step (base code-base))
                 (:instance symbols-rehash-step-count-agrees-with-advance)
                 (:instance symbols-rehash-next-in-chain (base code-base) (middle (symbols-rehash-entry-finish before)))
                 (:instance symbols-rehash-chain-frame-composition (base code-base) (middle (symbols-rehash-entry-finish before))
                            (after (proof-advance (symbols-rehash-chain-fuel links) before)))
                 (:instance proof-advance-append (prefix *symbols-rehash-entry-step-count*)
                            (suffix (symbols-rehash-chain-fuel (cdr links)))
                            (world before)))
           :in-theory (disable symbols-rehash-chain-frame-p symbols-rehash-entry-frame-p
                               symbols-rehash-chain-links-p symbols-rehash-entry-ready-p
                               symbols-rehash-memory-effect symbols-rehash-entry-writes symbols-rehash-entry-finish
                               symbols-rehash-step-count-agrees-with-advance)
           :expand ((len links)))
          ("Subgoal *1/1"
           :use ((:instance symbols-run-rehash-entry)
                 (:instance symbols-rehash-chain-input-selects-step (base code-base))
                 (:instance symbols-rehash-step-count-agrees-with-advance)
                 (:instance symbols-empty-rehash-chain-finishes (base code-base) (after (symbols-rehash-entry-finish before))))
           :in-theory (disable symbols-rehash-chain-frame-p symbols-rehash-entry-frame-p
                               symbols-rehash-chain-links-p symbols-rehash-entry-ready-p symbols-rehash-entry-finish
                               symbols-rehash-step-count-agrees-with-advance)
           :expand ((len links))))
  :rule-classes nil)
