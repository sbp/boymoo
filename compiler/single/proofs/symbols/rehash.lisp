(in-package "BOYMOO-PROOFS")

(include-book "loops")
(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                     (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg proof-heap-base
                     proof-advance proof-advance-append proof-segment-p
                     boymoo-model::a64-unsigned symbols-runtime-offset
                     symbols-no-memory-or-kernel-change-p symbols-path-ready-p
                     symbols-rehash-prefix-path symbols-dynamic-mask-at
                     symbols-dynamic-bucket-at symbols-load-register-word
                     symbols-rehash-entry-address symbols-rehash-entry-hash
                     symbols-rehash-next-entry)))

(defun symbols-rehash-call-state (before)
  (proof-advance (len (symbols-rehash-prefix-path before)) before))

(defun symbols-rehash-bucket-state (before)
  (proof-advance (len *symbols-bucket-address-path*) (symbols-rehash-call-state before)))

(defun symbols-rehash-entry-ready-p (base before)
  (let ((call (symbols-rehash-call-state before))
        (bucket (symbols-rehash-bucket-state before)))
    (and (symbols-path-ready-p (symbols-rehash-prefix-path before) base
                               (symbols-rehash-prefix-target base before) before)
         (implies (not (symbols-rehash-end-of-chain-p before))
                  (and (symbols-path-ready-p *symbols-bucket-address-path* base
                                             (proof-world-reg 30 call) call)
                       (symbols-path-ready-p *symbols-rehash-link-path* base
                                             (symbols-runtime-address "rt:intern-rehash-entry" base)
                                             bucket))))))

(defun symbols-rehash-selected-bucket (before)
  (symbols-dynamic-bucket-at (proof-world-reg 1 before) (symbols-rehash-entry-hash before) before))

(defun symbols-rehash-memory-effect (before)
  (let* ((bucket (symbols-rehash-selected-bucket before))
         (entry (symbols-rehash-entry-address before))
         (head (symbols-load-register-word bucket before))
         (first (boymoo-model::a64-store 8 (+ entry 24) head (proof-world-machine before))))
    (update-nth 0 (boymoo-model::a64-store 8 bucket (proof-world-reg 5 before) first) before)))

(defun symbols-rehash-entry-frame-p (base before after)
  (let ((end (symbols-rehash-end-of-chain-p before)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after)
                (symbols-runtime-address (if end "rt:intern-rehash-bucket" "rt:intern-rehash-entry") base))
         (equal (proof-world-reg 5 after)
                (if end *proof-nil* (symbols-rehash-next-entry before)))
         (implies (not end)
                  (equal (proof-world-reg 4 after) (symbols-rehash-selected-bucket before)))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 '(3 4 5 8 9 10 30) before after)
         (symbols-no-memory-or-kernel-change-p
          (if end before (symbols-rehash-memory-effect before)) after))))

(local
 (defthm symbols-bucket-contents-depend-on-memory
   (implies (equal (symbols-machine-memory before) (symbols-machine-memory after))
            (equal (symbols-dynamic-bucket-at table tagged-hash before)
                   (symbols-dynamic-bucket-at table tagged-hash after)))
   :hints (("Goal" :in-theory (enable symbols-dynamic-bucket-at symbols-dynamic-mask-at
                                     boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm symbols-rehash-bucket-returns
   (let ((state (proof-advance (len *symbols-bucket-address-path*) call)))
     (implies (and (symbols-runtime-base-p base)
                   (not (symbols-rehash-end-of-chain-p before))
                   (symbols-rehash-prefix-frame-p base before call)
                   (symbols-path-ready-p *symbols-bucket-address-path* base
                                         (proof-world-reg 30 call) call))
              (and (proof-frame-return-p '(3 4) nil call state)
                   (not (eq (car (proof-world-machine state)) :svc))
                   (equal (proof-world-reg 4 state) (symbols-rehash-selected-bucket before))
                   (symbols-no-memory-or-kernel-change-p call state))))
   :hints (("Goal"
            :use ((:instance symbols-run-bucket-address (code-base base) (before call))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 1) (clobbers '(8 9 10 30)) (after call))
                  (:instance symbols-bucket-contents-depend-on-memory
                             (table (proof-world-reg 1 before))
                             (tagged-hash (symbols-rehash-entry-hash before)) (after call)))
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p)
                            (symbols-run-bucket-address))))
   :rule-classes nil))

(local
 (defthm symbols-rehash-links-after-bucket-return
   (let ((after (proof-advance (len *symbols-rehash-link-path*) bucket)))
     (implies (and (symbols-runtime-base-p base)
                   (not (symbols-rehash-end-of-chain-p before))
                   (symbols-rehash-prefix-frame-p base before call)
                   (proof-frame-return-p '(3 4) nil call bucket)
                   (not (eq (car (proof-world-machine bucket)) :svc))
                   (symbols-path-ready-p *symbols-rehash-link-path* base
                                         (symbols-runtime-address "rt:intern-rehash-entry" base) bucket))
              (symbols-rehash-link-frame-p base bucket after)))
   :hints (("Goal" :use ((:instance symbols-run-rehash-link (code-base base) (before bucket)))
                   :in-theory (disable symbols-run-rehash-link symbols-rehash-link-frame-p)))
   :rule-classes nil))

(local
 (defthm symbols-rehash-link-memory-agreement
   (implies (and (equal (proof-world-reg 4 bucket) (symbols-rehash-selected-bucket before))
                 (equal (proof-world-reg 5 bucket) (proof-world-reg 5 before))
                 (equal (proof-world-reg 8 bucket) (symbols-rehash-entry-address before))
                 (symbols-no-memory-or-kernel-change-p before bucket))
            (symbols-no-memory-or-kernel-change-p (symbols-rehash-memory-effect before)
                                                  (symbols-rehash-linked-world bucket)))
   :hints (("Goal"
            :in-theory (enable symbols-no-memory-or-kernel-change-p
                               symbols-load-register-word boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm symbols-rehash-piece-frames-compose
   (implies (and (symbols-rehash-prefix-frame-p base before call)
                 (not (symbols-rehash-end-of-chain-p before))
                 (proof-frame-return-p '(3 4) nil call bucket)
                 (equal (proof-world-reg 4 bucket) (symbols-rehash-selected-bucket before))
                 (symbols-no-memory-or-kernel-change-p call bucket)
                 (symbols-rehash-link-frame-p base bucket after))
            (symbols-rehash-entry-frame-p base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register
                             (highest 30) (register 5) (clobbers '(8 9 10 30)) (after call))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 5) (clobbers '(3 4)) (before call) (after bucket))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 8) (clobbers '(3 4)) (before call) (after bucket))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 10) (clobbers '(3 4)) (before call) (after bucket))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 4) (clobbers '(3 5)) (before bucket))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(8 9 10 30)) (allowed '(3 4 5 8 9 10 30)) (after call))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(3 4)) (allowed '(3 4 5 8 9 10 30)) (before call) (after bucket))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(3 5)) (allowed '(3 4 5 8 9 10 30)) (before bucket))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers '(3 4 5 8 9 10 30))
                             (first before) (middle call) (last bucket))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers '(3 4 5 8 9 10 30))
                             (first before) (middle bucket) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first before) (middle call) (last bucket))
                  (:instance symbols-rehash-link-memory-agreement)
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-rehash-memory-effect before))
                             (middle (symbols-rehash-linked-world bucket)) (last after)))
            :in-theory (disable symbols-rehash-linked-world symbols-rehash-memory-effect
                                symbols-rehash-selected-bucket)))
   :rule-classes nil))

(local
 (defthm symbols-rehash-skip-keeps-frame
   (implies (and (symbols-rehash-end-of-chain-p before)
                 (symbols-rehash-prefix-frame-p base before after))
            (symbols-rehash-entry-frame-p base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register
                             (highest 30) (register 5) (clobbers '(8 9 10 30)))
                  (:instance symbols-frame-allows-more-clobbers
                             (highest 30) (clobbers '(8 9 10 30)) (allowed '(3 4 5 8 9 10 30))))))
   :rule-classes nil))

(defun symbols-rehash-entry-finish (before)
  (if (symbols-rehash-end-of-chain-p before)
      (symbols-rehash-call-state before)
    (proof-advance (len *symbols-rehash-link-path*) (symbols-rehash-bucket-state before))))

(defthm symbols-run-rehash-entry
  (implies (and (symbols-rehash-prefix-pre-p code-base before)
                (symbols-rehash-entry-ready-p code-base before))
           (symbols-rehash-entry-frame-p code-base before (symbols-rehash-entry-finish before)))
  :hints (("Goal"
           :use ((:instance symbols-run-rehash-prefix)
                 (:instance symbols-rehash-bucket-returns
                            (base code-base) (call (symbols-rehash-call-state before)))
                 (:instance symbols-rehash-links-after-bucket-return
                            (base code-base) (call (symbols-rehash-call-state before))
                            (bucket (symbols-rehash-bucket-state before)))
                 (:instance symbols-rehash-piece-frames-compose (base code-base)
                            (call (symbols-rehash-call-state before))
                            (bucket (symbols-rehash-bucket-state before))
                            (after (symbols-rehash-entry-finish before)))
                 (:instance symbols-rehash-skip-keeps-frame
                            (base code-base) (after (symbols-rehash-call-state before))))
           :in-theory (disable symbols-rehash-entry-frame-p symbols-rehash-prefix-frame-p
                               symbols-rehash-link-frame-p symbols-rehash-selected-bucket
                               symbols-rehash-prefix-target symbols-rehash-end-of-chain-p)))
  :rule-classes nil)
