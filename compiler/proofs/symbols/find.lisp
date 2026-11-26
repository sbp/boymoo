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
                     proof-advance proof-advance-append proof-byte-list
                     boymoo-model::a64-unsigned symbols-runtime-offset
                     symbols-load-register-word symbols-stack-word
                     symbols-logical-right-shift-bits symbols-box-at-slot
                     symbols-no-memory-or-kernel-change-p symbols-path-ready-p
                     symbols-find-step-ready-p symbols-find-step-fuel
                     symbols-found-candidate symbols-candidate-name-size
                     symbols-candidate-name-address)))

; A row is a pair of its name bytes and the address of its vector.
(defun symbols-find-rows-p (rows slot world)
  (if (atom rows)
      (null rows)
    (let* ((row (symbols-box-at-slot slot world))
           (name (symbols-box-at-slot (+ row 8) world))
           (bytes (caar rows))
           (size (len bytes)))
      (and (consp (car rows))
           (not (equal row 0))
           (equal row (cdar rows))
           (equal (symbols-logical-right-shift-bits
                   (symbols-load-register-word name world) 8)
                  size)
           (equal (proof-byte-list size (boymoo-model::a64-unsigned 64 (+ name 8))
                                   (proof-world-machine world))
                  bytes)
           (symbols-find-rows-p (cdr rows) (+ 8 slot) world)))))

(defun symbols-find-loop-input-p (rows query base world)
  (let ((slot (proof-world-reg 7 world)))
    (and (symbols-find-step-pre-p base world)
         (equal (proof-world-reg 8 world) (+ slot (* 8 (len rows))))
         (equal (proof-world-reg 6 world) (len query))
         (equal (proof-byte-list (len query) (proof-world-reg 5 world)
                                 (proof-world-machine world))
                query)
         (symbols-find-rows-p rows slot world))))

(local
 (defthm symbols-word-register-bound
   (< (proof-world-reg register world) (expt 2 64))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))
   :rule-classes :linear))

(local
 (defthm symbols-word-register-is-natural
   (natp (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-find-vector-end-and-match
   (implies (symbols-find-loop-input-p rows query base world)
            (and (equal (symbols-find-iteration-exhausted-p world) (atom rows))
                 (equal (symbols-find-candidate-matches-p world)
                        (and (consp rows) (equal (caar rows) query)))
                 (implies (consp rows)
                          (equal (symbols-found-candidate world) (cdar rows)))))
   :hints (("Goal" :cases ((consp rows))
                   :in-theory (enable symbols-found-candidate symbols-candidate-name-address
                                      symbols-candidate-name-size)
                   :expand ((len rows)
                            (symbols-find-rows-p rows (proof-world-reg 7 world) world))))
   :rule-classes nil))

(local
 (defthm symbols-find-rows-depend-on-memory
   (implies (and (equal (symbols-machine-memory before) (symbols-machine-memory after))
                 (equal (proof-heap-base before) (proof-heap-base after))
                 (symbols-find-rows-p rows slot before))
            (symbols-find-rows-p rows slot after))
   :hints (("Goal" :induct (symbols-find-rows-p rows slot before)
                   :in-theory (enable symbols-box-at-slot symbols-load-register-word
                                      boymoo-model::a64-load))
           ("Subgoal *1/2"
            :use ((:instance symbols-byte-list-depends-on-memory
                             (size (len (caar rows)))
                             (address (boymoo-model::a64-unsigned
                                       64 (+ 8 (symbols-box-at-slot
                                                (+ 8 (symbols-box-at-slot slot before)) before))))
                             (first (proof-world-machine before)) (last (proof-world-machine after))))
            :in-theory (enable symbols-box-at-slot symbols-load-register-word
                               boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm symbols-find-next-slot-is-in-range
   (implies (and (consp rows) (symbols-find-loop-input-p rows query base before))
            (equal (boymoo-model::a64-unsigned 64 (+ 8 (proof-world-reg 7 before)))
                   (+ 8 (proof-world-reg 7 before))))
   :hints (("Goal" :use ((:instance symbols-word-register-bound (register 8) (world before))
                         (:instance symbols-unsigned-in-range
                                    (width 64) (x (+ 8 (proof-world-reg 7 before)))))
                   :in-theory (disable symbols-find-rows-p symbols-find-step-pre-p)
                   :expand ((len rows))))
   :rule-classes nil))

(local
 (defthm symbols-find-input-survives-miss
   (implies (and (consp rows) (symbols-find-loop-input-p rows query base before)
                 (not (symbols-find-step-finishes-p before))
                 (symbols-find-step-frame-p base before after))
            (symbols-find-loop-input-p (cdr rows) query base after))
   :hints (("Goal"
            :use ((:instance symbols-find-next-slot-is-in-range)
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 5) (clobbers *symbols-find-loop-clobbers*))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 6) (clobbers *symbols-find-loop-clobbers*))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 8) (clobbers *symbols-find-loop-clobbers*))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 28) (clobbers *symbols-find-loop-clobbers*))
                  (:instance symbols-byte-list-depends-on-memory
                             (size (len query)) (address (proof-world-reg 5 before))
                             (first (proof-world-machine before)) (last (proof-world-machine after)))
                  (:instance symbols-find-rows-depend-on-memory
                             (rows (cdr rows)) (slot (+ 8 (proof-world-reg 7 before)))))
            :in-theory (enable proof-heap-base symbols-no-memory-or-kernel-change-p)
            :expand ((len rows))))
   :rule-classes nil))

; Each element of byte-fuels bounds the byte comparison for its row.
; A length mismatch or a completed search requires no comparison call.
(defun symbols-find-scan-ready-p (rows byte-fuels base before)
  (and (symbols-find-step-ready-p (car byte-fuels) base before)
       (or (atom rows) (symbols-find-step-finishes-p before)
           (symbols-find-scan-ready-p
            (cdr rows) (cdr byte-fuels) base
            (proof-advance (symbols-find-step-fuel (car byte-fuels) before) before)))))

(defun symbols-find-scan-fuel (rows byte-fuels before)
  (let ((step (symbols-find-step-fuel (car byte-fuels) before)))
    (if (or (atom rows) (symbols-find-step-finishes-p before))
        step
      (+ step (symbols-find-scan-fuel
               (cdr rows) (cdr byte-fuels) (proof-advance step before))))))

(defun symbols-find-scan-frame-p (rows query before after)
  (let ((binding (assoc-equal query rows)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after) (symbols-stack-word 8 before))
         (equal (proof-world-reg 0 after) (if binding (cdr binding) 0))
         (equal (proof-world-reg 29 after) (symbols-stack-word 0 before))
         (equal (proof-world-reg 30 after) (symbols-stack-word 8 before))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (+ 16 (boymoo-model::a64-sp (proof-world-machine before))))
         (proof-register-frame-p 30 *symbols-find-loop-clobbers* before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-find-completed-step-returns
   (implies (and (symbols-find-loop-input-p rows query base before)
                 (symbols-find-step-finishes-p before)
                 (symbols-find-step-frame-p base before after))
            (symbols-find-scan-frame-p rows query before after))
   :hints (("Goal"
            :use ((:instance symbols-find-vector-end-and-match (world before)))
            :in-theory (disable symbols-find-step-pre-p symbols-find-candidate-matches-p
                                symbols-find-iteration-exhausted-p)))
   :rule-classes nil))

(local
 (defthm symbols-find-scan-frames-compose
   (implies (and (consp rows) (symbols-find-loop-input-p rows query base before)
                 (not (symbols-find-step-finishes-p before))
                 (symbols-find-step-frame-p base before middle)
                 (symbols-find-scan-frame-p (cdr rows) query middle after))
            (symbols-find-scan-frame-p rows query before after))
   :hints (("Goal"
            :use ((:instance symbols-find-vector-end-and-match (world before))
                  (:instance symbols-frame-is-transitive
                             (highest 30) (clobbers *symbols-find-loop-clobbers*)
                             (first before) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first before) (last after))
                  (:instance symbols-saved-word-preserved-by-read-only-frame
                             (offset 0) (after middle))
                  (:instance symbols-saved-word-preserved-by-read-only-frame
                             (offset 8) (after middle)))
            :in-theory (disable symbols-find-step-pre-p symbols-find-candidate-matches-p
                                symbols-find-iteration-exhausted-p)))
   :rule-classes nil))

(local
 (defthm symbols-find-scan-advance-splits
   (let* ((step (symbols-find-step-fuel (car byte-fuels) before))
          (middle (proof-advance step before))
          (remaining (symbols-find-scan-fuel (cdr rows) (cdr byte-fuels) middle)))
     (implies (and (consp rows) (not (symbols-find-step-finishes-p before)))
              (equal (proof-advance (symbols-find-scan-fuel rows byte-fuels before) before)
                     (proof-advance remaining middle))))
   :hints (("Goal"
            :use ((:instance proof-advance-append
                             (prefix (symbols-find-step-fuel (car byte-fuels) before))
                             (suffix (symbols-find-scan-fuel
                                      (cdr rows) (cdr byte-fuels)
                                      (proof-advance
                                       (symbols-find-step-fuel (car byte-fuels) before) before)))
                             (world before)))
            :in-theory (disable symbols-find-step-finishes-p)))
   :rule-classes nil))

(defthm symbols-run-find-scan
  (implies (and (symbols-find-loop-input-p rows query code-base before)
                (symbols-find-scan-ready-p rows byte-fuels code-base before))
           (symbols-find-scan-frame-p
            rows query before
            (proof-advance (symbols-find-scan-fuel rows byte-fuels before) before)))
  :hints (("Goal"
           :induct (symbols-find-scan-ready-p rows byte-fuels code-base before)
           :in-theory (disable symbols-find-loop-input-p symbols-find-step-pre-p
                               symbols-find-step-frame-p symbols-find-scan-frame-p
                               symbols-find-step-finishes-p))
          ("Subgoal *1/3"
           :use ((:instance symbols-run-find-step (byte-fuel (car byte-fuels)))
                 (:instance symbols-find-input-survives-miss (base code-base)
                            (after (proof-advance (symbols-find-step-fuel (car byte-fuels) before)
                                                  before)))
                 (:instance symbols-find-scan-frames-compose (base code-base)
                            (middle (proof-advance (symbols-find-step-fuel (car byte-fuels) before)
                                                   before))
                            (after (proof-advance (symbols-find-scan-fuel rows byte-fuels before)
                                                  before)))
                 (:instance symbols-find-scan-advance-splits))
           :in-theory (enable symbols-find-loop-input-p))
          ("Subgoal *1/2"
           :use ((:instance symbols-run-find-step (byte-fuel (car byte-fuels)))
                 (:instance symbols-find-completed-step-returns (base code-base)
                            (after (proof-advance (symbols-find-step-fuel (car byte-fuels) before)
                                                  before))))
           :in-theory (enable symbols-find-loop-input-p))
          ("Subgoal *1/1"
           :use ((:instance symbols-run-find-step (byte-fuel (car byte-fuels)))
                 (:instance symbols-find-vector-end-and-match (base code-base) (world before))
                 (:instance symbols-find-completed-step-returns (base code-base)
                            (after (proof-advance (symbols-find-step-fuel (car byte-fuels) before)
                                                  before))))
           :in-theory (e/d (symbols-find-loop-input-p symbols-find-step-finishes-p)
                           (symbols-find-iteration-exhausted-p symbols-find-candidate-matches-p))))
  :rule-classes nil)

(defun symbols-find-package-input-p (rows query base before)
  (let* ((heap (proof-heap-base before))
         (saved (symbols-saved-link-world before))
         (sp (boymoo-model::a64-sp (proof-world-machine before)))
         (size (len query))
         (address (proof-world-reg 1 before))
         (slot (symbols-find-first-slot heap saved))
         (bytes (symbols-find-vector-size heap saved)))
    (and (symbols-find-setup-pre-p base before)
         (equal (proof-world-reg 2 before) size)
         (proof-span-p address size)
         (proof-disjoint-p address (+ address size) (- sp 16) sp)
         (equal (proof-byte-list size address (proof-world-machine before)) query)
         (equal bytes (* 8 (len rows)))
         (< (+ slot bytes) (expt 2 64))
         (symbols-find-rows-p rows slot saved))))

(local
 (defthm symbols-sp-is-natural
   (natp (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-sp-fits-word
   (< (boymoo-model::a64-sp machine) (expt 2 64))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :linear))

(local
 (defthm symbols-save-space-does-not-change-query
   (let* ((size (len query))
          (address (proof-world-reg 1 before))
          (saved (symbols-saved-link-world before)))
     (implies (symbols-find-package-input-p rows query base before)
              (equal (proof-byte-list size address (proof-world-machine saved)) query)))
   :hints (("Goal" :in-theory (disable symbols-find-first-slot symbols-find-vector-size
                                       symbols-find-rows-p)
                   :use ((:instance symbols-sp-fits-word (machine (proof-world-machine before))))))
   :rule-classes nil))

(local
 (defthm symbols-find-saved-base
   (equal (proof-heap-base (symbols-saved-link-world before)) (proof-heap-base before))
   :hints (("Goal" :in-theory (enable proof-heap-base proof-world-reg proof-reg)))))

(local
 (defthm symbols-find-setup-gives-loop-input
   (implies (and (symbols-find-package-input-p rows query base before)
                 (symbols-find-setup-frame-p base before start))
            (symbols-find-loop-input-p rows query base start))
   :hints (("Goal"
            :in-theory (e/d (proof-heap-base symbols-no-memory-or-kernel-change-p)
                            (symbols-find-rows-p symbols-find-first-slot symbols-find-vector-size
                             symbols-saved-link-world proof-span-p symbols-find-saved-base))
            :use ((:instance symbols-save-space-does-not-change-query)
                  (:instance symbols-find-saved-base)
                  (:instance symbols-sp-fits-word (machine (proof-world-machine before)))
                  (:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers '(5 6 7 8)) (after start))
                  (:instance symbols-find-rows-depend-on-memory
                             (before (symbols-saved-link-world before)) (after start)
                             (slot (symbols-find-first-slot (proof-heap-base before)
                                                            (symbols-saved-link-world before))))
                  (:instance symbols-byte-list-depends-on-memory
                             (size (len query)) (address (proof-world-reg 1 before))
                             (first (proof-world-machine (symbols-saved-link-world before)))
                             (last (proof-world-machine start))))))
   :rule-classes nil))

(local
 (defthm symbols-find-read-saved-registers
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine before)))
          (saved (symbols-saved-link-world before)))
     (implies (<= 16 sp)
              (and (equal (symbols-load-register-word (- sp 16) saved) (proof-world-reg 29 before))
                   (equal (symbols-load-register-word (- sp 8) saved) (proof-world-reg 30 before)))))
   :hints (("Goal" :in-theory (e/d (symbols-load-register-word proof-world-reg proof-reg
                                    boymoo-model::a64-read-reg)
                                   (proof-load-word))))))

(local
 (defthm symbols-register-word-depends-on-memory
   (implies (equal (symbols-machine-memory before) (symbols-machine-memory after))
            (equal (symbols-load-register-word address before)
                   (symbols-load-register-word address after)))
   :hints (("Goal" :in-theory (enable symbols-load-register-word boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm symbols-find-setup-stack-words
   (implies (and (symbols-find-setup-pre-p base before)
                 (symbols-find-setup-frame-p base before start))
            (and (equal (symbols-stack-word 0 start) (proof-world-reg 29 before))
                 (equal (symbols-stack-word 8 start) (proof-world-reg 30 before))))
   :hints (("Goal"
            :use ((:instance symbols-find-read-saved-registers)
                  (:instance symbols-register-word-depends-on-memory
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                             (before (symbols-saved-link-world before)) (after start))
                  (:instance symbols-register-word-depends-on-memory
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 8))
                             (before (symbols-saved-link-world before)) (after start)))
            :in-theory (e/d (symbols-stack-word symbols-no-memory-or-kernel-change-p)
                            (symbols-saved-link-world symbols-find-read-saved-registers
                             symbols-find-first-slot symbols-find-vector-size))))
   :rule-classes nil))

(defconst *symbols-find-package-clobbers* '(0 1 2 3 4 5 6 7 8 9))

(defun symbols-find-package-return-p (rows query before after)
  (let ((binding (assoc-equal query rows)))
    (and (proof-frame-return-p *symbols-find-package-clobbers* t before after)
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-reg 0 after) (if binding (cdr binding) 0))
         (symbols-no-memory-or-kernel-change-p (symbols-saved-link-world before) after))))

(local
 (defthm symbols-find-return-registers
   (implies (and (proof-register-frame-p 30 '(5 6 7 8) before start)
                 (proof-register-frame-p 30 *symbols-find-loop-clobbers* start after)
                 (equal (proof-world-reg 29 after) (proof-world-reg 29 before))
                 (equal (proof-world-reg 30 after) (proof-world-reg 30 before)))
            (proof-register-frame-p 30 *symbols-find-package-clobbers* before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers
                             (highest 30) (clobbers '(5 6 7 8))
                             (allowed '(0 1 2 3 4 5 6 7 8 9 29 30)) (after start))
                  (:instance symbols-frame-allows-more-clobbers
                             (highest 30) (clobbers *symbols-find-loop-clobbers*)
                             (allowed '(0 1 2 3 4 5 6 7 8 9 29 30)) (before start))
                  (:instance symbols-frame-is-transitive
                             (highest 30) (clobbers '(0 1 2 3 4 5 6 7 8 9 29 30))
                             (first before) (middle start) (last after))
                  (:instance symbols-frame-keeps-restored-register
                             (highest 30) (register 29) (clobbers '(0 1 2 3 4 5 6 7 8 9 29 30)))
                  (:instance symbols-frame-keeps-restored-register
                             (highest 30) (register 30) (clobbers '(0 1 2 3 4 5 6 7 8 9 30))))))
   :rule-classes nil))

(local
 (defthm symbols-find-return-frames-compose
   (implies (and (symbols-find-setup-pre-p base before)
                 (symbols-find-setup-frame-p base before start)
                 (symbols-find-scan-frame-p rows query start after))
            (symbols-find-package-return-p rows query before after))
   :hints (("Goal"
            :use ((:instance symbols-find-setup-stack-words)
                  (:instance symbols-find-return-registers)
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-saved-link-world before)) (middle start) (last after)))
            :in-theory (disable symbols-saved-link-world symbols-find-first-slot
                                symbols-find-vector-size assoc-equal)))
   :rule-classes nil))

(defun symbols-find-package-fuel (rows byte-fuels before)
  (let ((setup (len *symbols-find-setup-path*)))
    (+ setup (symbols-find-scan-fuel rows byte-fuels (proof-advance setup before)))))

(defthm symbols-run-find-package
  (let* ((start (proof-advance (len *symbols-find-setup-path*) before))
         (after (proof-advance (symbols-find-package-fuel rows byte-fuels before) before)))
    (implies (and (symbols-find-package-input-p rows query code-base before)
                  (symbols-path-ready-p *symbols-find-setup-path* code-base
                                        (symbols-runtime-address "rt:find-package-loop" code-base)
                                        before)
                  (symbols-find-scan-ready-p rows byte-fuels code-base start))
             (symbols-find-package-return-p rows query before after)))
  :hints (("Goal"
           :use ((:instance symbols-run-find-setup)
                 (:instance symbols-find-setup-gives-loop-input (base code-base) (start (proof-advance 10 before)))
                 (:instance symbols-run-find-scan (before (proof-advance 10 before)))
                 (:instance symbols-find-return-frames-compose (base code-base)
                            (start (proof-advance 10 before))
                            (after (proof-advance (+ 10 (symbols-find-scan-fuel
                                                         rows byte-fuels (proof-advance 10 before)))
                                                  before)))
                 (:instance proof-advance-append (prefix 10) (world before)
                            (suffix (symbols-find-scan-fuel rows byte-fuels (proof-advance 10 before)))))
           :in-theory (disable symbols-run-find-setup symbols-find-scan-ready-p
                               symbols-find-scan-fuel symbols-find-setup-frame-p
                               symbols-find-scan-frame-p symbols-find-loop-input-p
                               symbols-find-package-return-p symbols-saved-link-world
                               symbols-replay proof-segment-p symbols-find-rows-p)))
  :rule-classes nil)
