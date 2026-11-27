(in-package "BOYMOO-PROOFS")

(include-book "growth")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                    (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg proof-heap-base
                     proof-advance proof-advance-append proof-register-frame-p symbols-runtime-offset
                     symbols-path-ready-p symbols-no-memory-or-kernel-change-p
                     symbols-load-register-word symbols-rehash-chain-memory symbols-rehash-chain-links-p)))

(defun symbols-rehash-table-memory (chains table heap before)
  (if (atom chains)
      before
    (symbols-rehash-table-memory (cdr chains) table heap
                                 (symbols-rehash-chain-memory (car chains) table heap before))))

; The remaining old bucket slots give the heads of the stated chains
; at the times when the loop reads those slots.
(defun symbols-rehash-table-chains-p (chains slot table heap before)
  (if (atom chains)
      (null chains)
    (let ((chain (car chains)))
      (and (equal (symbols-load-register-word slot before) (symbols-rehash-chain-head chain))
           (symbols-rehash-chain-links-p chain table heap before)
           (symbols-rehash-table-chains-p (cdr chains) (+ 8 slot) table heap
                                           (symbols-rehash-chain-memory chain table heap before))))))

(defun symbols-rehash-table-input-p (chains base before)
  (let ((slot (proof-world-reg 6 before)))
    (and (symbols-rehash-bucket-pre-p base before)
         (equal (proof-world-reg 7 before) (+ slot (* 8 (len chains))))
         (symbols-rehash-table-chains-p chains slot (proof-world-reg 1 before) (proof-heap-base before) before))))

(defun symbols-rehash-read-head (before)
  (proof-advance (len (symbols-rehash-bucket-path before)) before))

(defun symbols-rehash-finish-bucket (chain before)
  (proof-advance (symbols-rehash-chain-fuel chain) (symbols-rehash-read-head before)))

(defun symbols-rehash-table-ready-p (chains base before)
  (and (symbols-path-ready-p (symbols-rehash-bucket-path before) base
                             (symbols-rehash-bucket-target base before) before)
       (or (atom chains)
           (and (symbols-rehash-chain-ready-p (car chains) base (symbols-rehash-read-head before))
                (symbols-rehash-table-ready-p (cdr chains) base (symbols-rehash-finish-bucket (car chains) before))))))

(defconst *symbols-rehash-table-clobbers* '(3 4 5 6 8 9 10 30))

(defun symbols-rehash-table-step-frame-p (chain base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-rehash-bucket" base))
       (equal (proof-world-reg 6 after) (+ 8 (proof-world-reg 6 before)))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-register-frame-p 30 *symbols-rehash-table-clobbers* before after)
       (symbols-no-memory-or-kernel-change-p
        (symbols-rehash-chain-memory chain (proof-world-reg 1 before) (proof-heap-base before) before) after)))

(local
 (defthm symbols-rehash-table-has-next-bucket
   (implies (symbols-rehash-table-input-p chains base before)
            (equal (symbols-rehash-buckets-exhausted-p before) (atom chains)))
   :hints (("Goal" :expand ((len chains))
                   :in-theory (disable symbols-rehash-table-chains-p symbols-rehash-bucket-pre-p)))
   :rule-classes nil))

(local
 (defthm symbols-rehash-read-depends-on-memory
   (implies (symbols-no-memory-or-kernel-change-p first last)
            (equal (symbols-load-register-word slot first) (symbols-load-register-word slot last)))
   :hints (("Goal"
            :in-theory (enable symbols-load-register-word symbols-no-memory-or-kernel-change-p boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defun symbols-rehash-same-layout-induction (chains slot table heap first last)
   (if (atom chains)
       (list slot first last)
     (symbols-rehash-same-layout-induction
      (cdr chains) (+ 8 slot) table heap
      (symbols-rehash-chain-memory (car chains) table heap first)
      (symbols-rehash-chain-memory (car chains) table heap last)))))

(local
 (defthm symbols-rehash-table-maps-depend-on-memory
   (implies (symbols-no-memory-or-kernel-change-p first last)
            (equal (symbols-rehash-table-chains-p chains slot table heap first)
                   (symbols-rehash-table-chains-p chains slot table heap last)))
   :hints (("Goal"
            :induct (symbols-rehash-same-layout-induction chains slot table heap first last)
            :in-theory (disable symbols-rehash-chain-head))
           ("Subgoal *1/2"
            :use ((:instance symbols-rehash-read-depends-on-memory)
                  (:instance symbols-rehash-chain-memory-uses-equivalent-inputs (links (car chains)))
                  (:instance symbols-rehash-chain-links-depend-on-memory (links (car chains))))
            :in-theory (disable symbols-rehash-chain-head)))))

(local
 (defthm symbols-rehash-table-memory-uses-equivalent-inputs
   (implies (symbols-no-memory-or-kernel-change-p first last)
            (symbols-no-memory-or-kernel-change-p (symbols-rehash-table-memory chains table heap first)
                                                  (symbols-rehash-table-memory chains table heap last)))
   :hints (("Goal" :induct (list (symbols-rehash-table-memory chains table heap first)
                                 (symbols-rehash-table-memory chains table heap last))
                   :in-theory (enable symbols-rehash-chain-memory-uses-equivalent-inputs)))))

(local
 (defthm symbols-rehash-table-first-bucket-layout
   (implies (and (consp chains) (symbols-rehash-table-chains-p chains slot table heap before))
            (and (equal (symbols-load-register-word slot before) (symbols-rehash-chain-head (car chains)))
                 (symbols-rehash-chain-links-p (car chains) table heap before)))
   :hints (("Goal" :expand ((symbols-rehash-table-chains-p chains slot table heap before))))
   :rule-classes nil))

(local
 (defthm symbols-rehash-table-read-head-enters-chain
   (implies (and (consp chains)
                 (symbols-rehash-table-input-p chains base before)
                 (symbols-rehash-bucket-frame-p base before entry))
            (symbols-rehash-chain-input-p (car chains) base entry))
   :hints (("Goal"
            :use ((:instance symbols-rehash-table-has-next-bucket)
                  (:instance symbols-rehash-table-first-bucket-layout
                             (slot (proof-world-reg 6 before)) (table (proof-world-reg 1 before))
                             (heap (proof-heap-base before)))
                  (:instance symbols-frame-gives-register (highest 30) (clobbers '(5 6))
                             (register 1) (after entry))
                  (:instance symbols-frame-gives-register (highest 30) (clobbers '(5 6))
                             (register 28) (after entry))
                  (:instance symbols-rehash-chain-links-depend-on-memory (links (car chains))
                             (table (proof-world-reg 1 before)) (heap (proof-heap-base before))
                             (first before) (last entry)))
            :in-theory (e/d (proof-heap-base)
                            (symbols-rehash-table-maps-depend-on-memory symbols-rehash-table-chains-p))))
   :rule-classes nil))

(local
 (defthm symbols-rehash-table-end-register-fits
   (< (proof-world-reg 7 world) (expt 2 64))
   :hints (("Goal" :in-theory (e/d (proof-world-reg proof-reg boymoo-model::a64-read-reg)
                                   (boymoo-model::a64-unsigned))))
   :rule-classes :linear))

(local
 (defthm symbols-rehash-table-links-one-bucket
   (implies (and (consp chains)
                 (symbols-rehash-table-input-p chains base before)
                 (symbols-rehash-bucket-frame-p base before entry)
                 (symbols-rehash-chain-frame-p (car chains) base entry after))
            (symbols-rehash-table-step-frame-p (car chains) base before after))
   :hints (("Goal"
            :use ((:instance symbols-rehash-table-has-next-bucket)
                  (:instance symbols-frame-gives-register (highest 30) (register 1) (clobbers '(5 6)) (after entry))
                  (:instance symbols-frame-gives-register (highest 30) (register 28) (clobbers '(5 6)) (after entry))
                  (:instance symbols-frame-gives-register (highest 30) (register 6)
                             (clobbers *symbols-rehash-chain-clobbers*) (before entry))
                  (:instance symbols-frame-gives-register (highest 30) (register 7)
                             (clobbers *symbols-rehash-chain-clobbers*) (before entry))
                  (:instance symbols-frame-gives-register (highest 30) (register 7) (clobbers '(5 6)) (after entry))
                  (:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(5 6))
                             (allowed *symbols-rehash-table-clobbers*) (after entry))
                  (:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers *symbols-rehash-chain-clobbers*)
                             (allowed *symbols-rehash-table-clobbers*) (before entry))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-rehash-table-clobbers*)
                             (first before) (middle entry) (last after))
                  (:instance symbols-rehash-chain-memory-uses-equivalent-inputs
                             (links (car chains)) (table (proof-world-reg 1 before)) (heap (proof-heap-base before))
                             (first before) (last entry))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-rehash-chain-memory (car chains) (proof-world-reg 1 before)
                                                                 (proof-heap-base before) before))
                             (middle (symbols-rehash-chain-memory (car chains) (proof-world-reg 1 before)
                                                                  (proof-heap-base before) entry))
                             (last after)))
            :expand ((len chains))
            :in-theory (e/d (proof-heap-base) (symbols-rehash-table-chains-p))))
   :rule-classes nil))

(defthm symbols-run-rehash-one-bucket
  (let* ((entry (symbols-rehash-read-head before))
         (after (symbols-rehash-finish-bucket (car chains) before)))
    (implies (and (consp chains)
                  (symbols-rehash-table-input-p chains code-base before)
                  (symbols-path-ready-p (symbols-rehash-bucket-path before) code-base
                                        (symbols-rehash-bucket-target code-base before) before)
                  (symbols-rehash-chain-ready-p (car chains) code-base entry))
             (symbols-rehash-table-step-frame-p (car chains) code-base before after)))
  :hints (("Goal"
           :use ((:instance symbols-run-rehash-bucket-step)
                 (:instance symbols-run-rehash-chain (links (car chains)) (before (symbols-rehash-read-head before)))
                 (:instance symbols-rehash-table-read-head-enters-chain (base code-base)
                            (entry (symbols-rehash-read-head before)))
                 (:instance symbols-rehash-table-links-one-bucket (base code-base)
                            (entry (symbols-rehash-read-head before))
                            (after (symbols-rehash-finish-bucket (car chains) before))))
           :in-theory (disable symbols-rehash-table-step-frame-p symbols-rehash-chain-input-p
                               symbols-rehash-chain-frame-p symbols-rehash-bucket-frame-p
                               symbols-rehash-table-chains-p symbols-rehash-chain-ready-p)))
  :rule-classes nil)

(local
 (defthm symbols-rehash-table-continues-with-remaining-buckets
   (implies (and (consp chains) (symbols-rehash-table-input-p chains base before)
                 (symbols-rehash-table-step-frame-p (car chains) base before middle))
            (symbols-rehash-table-input-p (cdr chains) base middle))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 1)
                             (clobbers *symbols-rehash-table-clobbers*) (after middle))
                  (:instance symbols-frame-gives-register (highest 30) (register 7)
                             (clobbers *symbols-rehash-table-clobbers*) (after middle))
                  (:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers *symbols-rehash-table-clobbers*) (after middle))
                  (:instance symbols-rehash-table-maps-depend-on-memory (chains (cdr chains))
                             (slot (+ 8 (proof-world-reg 6 before))) (table (proof-world-reg 1 before))
                             (heap (proof-heap-base before))
                             (first (symbols-rehash-chain-memory (car chains) (proof-world-reg 1 before)
                                                                 (proof-heap-base before) before))
                             (last middle)))
            :expand ((len chains) (len (cdr chains))
                     (:free (slot table heap) (symbols-rehash-table-chains-p chains slot table heap before)))
            :cases ((consp (cdr chains)))
            :in-theory (e/d (proof-heap-base)
                            (symbols-rehash-table-chains-p symbols-rehash-table-maps-depend-on-memory
                             symbols-rehash-chain-head))))
   :rule-classes nil))

(defun symbols-rehash-table-frame-p (chains base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-grown" base))
       (equal (proof-world-reg 6 after) (proof-world-reg 7 before))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-register-frame-p 30 *symbols-rehash-table-clobbers* before after)
       (symbols-no-memory-or-kernel-change-p
        (symbols-rehash-table-memory chains (proof-world-reg 1 before) (proof-heap-base before) before) after)))

(local
 (defthm symbols-rehash-table-collects-each-bucket
   (implies (and (consp chains) (symbols-rehash-table-step-frame-p (car chains) base before middle)
                 (symbols-rehash-table-frame-p (cdr chains) base middle after))
            (symbols-rehash-table-frame-p chains base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 1)
                             (clobbers *symbols-rehash-table-clobbers*) (after middle))
                  (:instance symbols-frame-gives-register (highest 30) (register 7)
                             (clobbers *symbols-rehash-table-clobbers*) (after middle))
                  (:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers *symbols-rehash-table-clobbers*) (after middle))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-rehash-table-clobbers*)
                             (first before) (last after))
                  (:instance symbols-rehash-table-memory-uses-equivalent-inputs (chains (cdr chains))
                             (table (proof-world-reg 1 before)) (heap (proof-heap-base before))
                             (first (symbols-rehash-chain-memory (car chains) (proof-world-reg 1 before)
                                                                 (proof-heap-base before) before))
                             (last middle))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-rehash-table-memory chains (proof-world-reg 1 before)
                                                                 (proof-heap-base before) before))
                             (middle (symbols-rehash-table-memory (cdr chains) (proof-world-reg 1 before)
                                                                  (proof-heap-base before) middle))
                             (last after)))
            :expand ((:free (table heap) (symbols-rehash-table-memory chains table heap before)))
            :in-theory (e/d (proof-heap-base)
                            (symbols-rehash-table-memory symbols-rehash-table-memory-uses-equivalent-inputs
                             symbols-rehash-bucket-pre-p))))
   :rule-classes nil))

(local
 (defthm symbols-exhausted-rehash-table-finishes
   (implies (and (atom chains) (symbols-rehash-table-input-p chains base before)
                 (symbols-rehash-bucket-frame-p base before after))
            (symbols-rehash-table-frame-p chains base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(5 6))
                             (allowed *symbols-rehash-table-clobbers*)))
            :expand ((len chains))
            :in-theory (disable symbols-rehash-table-chains-p symbols-rehash-bucket-pre-p)))
   :rule-classes nil))

(defun symbols-rehash-table-fuel (chains)
  (if (atom chains)
      (len *symbols-rehash-last-bucket-path*)
    (+ (len *symbols-rehash-load-bucket-path*)
       (symbols-rehash-chain-fuel (car chains))
       (symbols-rehash-table-fuel (cdr chains)))))

(local
 (defthm symbols-rehash-table-bucket-fuel-splits
   (implies (and (consp chains) (symbols-rehash-table-input-p chains base before))
            (equal (proof-advance (symbols-rehash-table-fuel chains) before)
                   (proof-advance (symbols-rehash-table-fuel (cdr chains))
                                  (symbols-rehash-finish-bucket (car chains) before))))
   :hints (("Goal"
            :use ((:instance symbols-rehash-table-has-next-bucket)
                  (:instance proof-advance-append
                             (prefix (len *symbols-rehash-load-bucket-path*))
                             (suffix (symbols-rehash-chain-fuel (car chains))) (world before))
                  (:instance proof-advance-append
                             (prefix (+ (len *symbols-rehash-load-bucket-path*) (symbols-rehash-chain-fuel (car chains))))
                             (suffix (symbols-rehash-table-fuel (cdr chains))) (world before)))
            :in-theory (disable symbols-rehash-table-input-p symbols-rehash-buckets-exhausted-p
                                symbols-rehash-chain-fuel)))
   :rule-classes nil))

(defthm symbols-run-rehash-all-buckets
  (implies (and (symbols-rehash-table-input-p chains code-base before)
                (symbols-rehash-table-ready-p chains code-base before))
           (symbols-rehash-table-frame-p chains code-base before
                                        (proof-advance (symbols-rehash-table-fuel chains) before)))
  :hints (("Goal" :induct (symbols-rehash-table-ready-p chains code-base before)
                  :in-theory (disable symbols-rehash-table-input-p symbols-rehash-table-frame-p
                                      symbols-rehash-table-fuel symbols-rehash-finish-bucket
                                      symbols-rehash-read-head symbols-rehash-chain-ready-p))
          ("Subgoal *1/2"
           :use ((:instance symbols-run-rehash-one-bucket)
                 (:instance symbols-rehash-table-has-next-bucket (base code-base))
                 (:instance symbols-rehash-table-continues-with-remaining-buckets (base code-base)
                            (middle (symbols-rehash-finish-bucket (car chains) before)))
                 (:instance symbols-rehash-table-bucket-fuel-splits (base code-base))
                 (:instance symbols-rehash-table-collects-each-bucket (base code-base)
                            (middle (symbols-rehash-finish-bucket (car chains) before))
                            (after (proof-advance (symbols-rehash-table-fuel chains) before))))
           :in-theory (disable symbols-rehash-table-input-p
                               symbols-rehash-table-frame-p symbols-rehash-table-fuel))
          ("Subgoal *1/1"
           :use ((:instance symbols-run-rehash-bucket-step)
                 (:instance symbols-rehash-table-has-next-bucket (base code-base))
                 (:instance symbols-exhausted-rehash-table-finishes (base code-base)
                            (after (proof-advance (len *symbols-rehash-last-bucket-path*) before))))
           :in-theory (disable symbols-rehash-table-chains-p symbols-rehash-buckets-exhausted-p
                               symbols-rehash-bucket-frame-p symbols-rehash-table-frame-p)))
  :rule-classes nil)
