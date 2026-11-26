(in-package "BOYMOO-PROOFS")

(include-book "routines")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                     (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg proof-heap-base
                     proof-advance proof-advance-append
                     boymoo-model::a64-unsigned symbols-runtime-offset
                     symbols-no-memory-or-kernel-change-p symbols-hash-byte
                     proof-byte-list proof-string-bytes symbols-path-ready-p)))

(defthm symbols-frame-gives-register
  (implies (and (natp highest) (natp register) (<= register highest)
                (not (member-equal register clobbers))
                (proof-register-frame-p highest clobbers before after))
           (equal (proof-world-reg register before) (proof-world-reg register after)))
  :hints (("Goal" :induct (proof-register-frame-p highest clobbers before after)
                  :in-theory (enable proof-register-frame-p)))
  :rule-classes nil)

(defthm symbols-frame-is-transitive
  (implies (and (proof-register-frame-p highest clobbers first middle)
                (proof-register-frame-p highest clobbers middle last))
           (proof-register-frame-p highest clobbers first last))
  :hints (("Goal" :induct (proof-register-frame-p highest clobbers first middle)
                  :in-theory (enable proof-register-frame-p)))
  :rule-classes nil)

(local
 (defthm symbols-member-after-remove
   (iff (member-equal register (remove-equal restored clobbers))
        (and (not (equal register restored)) (member-equal register clobbers)))))

(defthm symbols-frame-keeps-restored-register
  (implies (and (proof-register-frame-p highest clobbers before after)
                (equal (proof-world-reg register before) (proof-world-reg register after)))
           (proof-register-frame-p highest (remove-equal register clobbers) before after))
  :hints (("Goal" :induct (proof-register-frame-p highest clobbers before after)
                  :in-theory (enable proof-register-frame-p)))
  :rule-classes nil)

(defthm symbols-memory-and-kernel-frame-is-transitive
  (implies (and (symbols-no-memory-or-kernel-change-p first middle)
                (symbols-no-memory-or-kernel-change-p middle last))
           (symbols-no-memory-or-kernel-change-p first last))
  :hints (("Goal" :in-theory (enable symbols-no-memory-or-kernel-change-p)))
  :rule-classes nil)

(local
 (defthm symbols-memory-and-kernel-frame-of-self
   (symbols-no-memory-or-kernel-change-p world world)
   :hints (("Goal" :in-theory (enable symbols-no-memory-or-kernel-change-p)))))

(defthm symbols-byte-list-depends-on-memory
  (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
           (equal (proof-byte-list size address first) (proof-byte-list size address last)))
  :hints (("Goal" :induct (proof-byte-list size address first)
                  :in-theory (enable proof-byte-list boymoo-model::a64-load)))
  :rule-classes nil)

; Each step requires the decoded instruction to be present and its
; memory access to be permitted. This predicate checks those premises
; for each loop path. The input predicate states which bytes it reads.
(defun symbols-hash-iterations-ready-p (characters base world)
  (if (atom characters)
      (symbols-path-ready-p *symbols-hash-loop-done-path* base nil world)
    (and (symbols-path-ready-p *symbols-hash-loop-byte-path* base nil world)
         (symbols-hash-iterations-ready-p (cdr characters) base (proof-advance 7 world)))))

(defun symbols-hash-input-p (characters base world)
  (let ((index (proof-world-reg 4 world)))
    (and (symbols-hash-loop-pre-p base world)
         (equal (proof-world-reg 21 world) (+ index (len characters)))
         (equal (proof-byte-list (len characters) (+ (proof-world-reg 8 world) index)
                                 (proof-world-machine world))
                (proof-string-bytes characters)))))

(defun symbols-hash-iterations-fuel (characters)
  (+ 2 (* 7 (len characters))))

(local
 (defthm symbols-hash-iteration-splits-fuel
   (equal (proof-advance (+ 9 (* 7 (len remaining))) before)
          (proof-advance (+ 2 (* 7 (len remaining))) (proof-advance 7 before)))
   :hints (("Goal"
            :use ((:instance proof-advance-append (prefix 7)
                             (suffix (+ 2 (* 7 (len remaining))))
                             (world before)))))))

(local
 (defthm symbols-word-register-fits
   (equal (boymoo-model::a64-unsigned 64 (proof-world-reg register world))
          (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))))

(local
 (defthm symbols-hash-limit-exhausted-at-end
   (implies (symbols-hash-input-p characters base world)
            (equal (symbols-hash-loop-done-p world) (atom characters)))
   :hints (("Goal" :cases ((consp characters)) :expand ((len characters))))
   :rule-classes nil))

(local
 (defthm symbols-hash-iteration-reads-head
   (implies (and (consp characters) (symbols-hash-input-p characters base world))
            (equal (symbols-hash-loop-byte world) (char-code (car characters))))
   :hints (("Goal" :in-theory (enable proof-string-bytes proof-byte-list)))
   :rule-classes nil))

(local
 (defthm symbols-hash-iteration-carries-input
   (implies (and (consp characters)
                 (symbols-hash-input-p characters base before)
                 (symbols-hash-loop-frame-p base before after))
            (symbols-hash-input-p (cdr characters) base after))
   :hints (("Goal"
            :use ((:instance symbols-hash-limit-exhausted-at-end (world before))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 8) (clobbers '(3 4 5)))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 21) (clobbers '(3 4 5)))
                  (:instance symbols-byte-list-depends-on-memory
                             (size (len (cdr characters)))
                             (address (+ 1 (proof-world-reg 4 before) (proof-world-reg 8 before)))
                             (first (proof-world-machine before))
                             (last (proof-world-machine after))))
            :in-theory (e/d (proof-string-bytes proof-byte-list
                             symbols-no-memory-or-kernel-change-p)
                            (symbols-hash-loop-byte symbols-hash-loop-done-p))))
   :rule-classes nil))

(defthm symbols-run-hash-iterations
  (let ((after (proof-advance (symbols-hash-iterations-fuel characters) before)))
    (implies (and (symbols-hash-input-p characters code-base before)
                  (symbols-hash-iterations-ready-p characters code-base before))
             (and (not (proof-world-stop after))
                  (not (eq (car (proof-world-machine after)) :svc))
                  (equal (proof-world-pc after)
                         (symbols-runtime-address "rt:intern-bucket" code-base))
                  (equal (proof-world-reg 4 after) (proof-world-reg 21 before))
                  (equal (proof-world-reg 3 after)
                         (proof-hash-characters characters (proof-world-reg 3 before) 64))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine before)))
                  (proof-register-frame-p 30 '(3 4 5) before after)
                  (symbols-no-memory-or-kernel-change-p before after))))
  :hints (("Goal"
           :induct (symbols-hash-iterations-ready-p characters code-base before)
           :in-theory (disable symbols-hash-input-p symbols-hash-loop-pre-p
                               symbols-hash-loop-done-p symbols-hash-loop-byte
                               proof-hash-characters symbols-machine-name-hash-agrees))
          ("Subgoal *1/2"
           :use ((:instance symbols-hash-limit-exhausted-at-end (base code-base) (world before))
                 (:instance symbols-hash-iteration-reads-head (base code-base) (world before))
                 (:instance symbols-run-hash-loop-iteration)
                 (:instance symbols-frame-gives-register
                            (highest 30) (register 21) (clobbers '(3 4 5))
                            (after (proof-advance 7 before)))
                 (:instance symbols-hash-iteration-carries-input
                            (base code-base) (after (proof-advance 7 before)))
                 (:instance symbols-frame-is-transitive
                            (highest 30) (clobbers '(3 4 5))
                            (first before) (middle (proof-advance 7 before))
                            (last (proof-advance (symbols-hash-iterations-fuel characters)
                                                  before)))
                 (:instance symbols-memory-and-kernel-frame-is-transitive
                            (first before) (middle (proof-advance 7 before))
                            (last (proof-advance (symbols-hash-iterations-fuel characters)
                                                  before))))
           :in-theory (e/d (symbols-hash-input-p symbols-hash-loop-frame-p
                            symbols-hash-byte-is-polynomial-step)
                           (symbols-hash-loop-done-p proof-byte-list proof-string-bytes))
           :expand ((proof-hash-characters characters (proof-world-reg 3 before) 64)))
          ("Subgoal *1/1"
           :use ((:instance symbols-hash-limit-exhausted-at-end (base code-base) (world before))
                 (:instance symbols-run-hash-loop-iteration))
           :in-theory (enable symbols-hash-input-p symbols-hash-loop-frame-p proof-hash-characters)))
  :rule-classes nil)

(local
 (defthm symbols-subset-contains-member
   (implies (and (subsetp-equal subset superset) (member-equal element subset))
            (member-equal element superset))
   :hints (("Goal" :induct (subsetp-equal subset superset)))))

(defthm symbols-frame-allows-more-clobbers
  (implies (and (proof-register-frame-p highest clobbers before after)
                (subsetp-equal clobbers allowed))
           (proof-register-frame-p highest allowed before after))
  :hints (("Goal" :induct (proof-register-frame-p highest clobbers before after)
                  :in-theory (enable proof-register-frame-p)))
  :rule-classes nil)

(defun symbols-find-byte-call-p (world)
  (and (not (symbols-find-iteration-exhausted-p world))
       (equal (symbols-candidate-name-size world) (proof-world-reg 6 world))))

(defun symbols-find-probe (world)
  (proof-advance (len (symbols-find-iteration-path world)) world))

(defun symbols-find-compared (byte-fuel before)
  (let ((probe (symbols-find-probe before)))
    (if (symbols-find-byte-call-p before)
        (proof-advance (nfix byte-fuel) probe)
      probe)))

; The byte comparison is a separate runtime call. Its return contract
; describes a comparison of the two spans passed in X0 and X1.
(defun symbols-byte-equality-return-p (before after)
  (let ((size (proof-world-reg 2 before))
        (machine (proof-world-machine before)))
    (and (proof-frame-return-p '(0 1 2 3 4) t before after)
         (not (eq (car (proof-world-machine after)) :svc))
         (symbols-no-memory-or-kernel-change-p before after)
         (equal (proof-world-reg 0 after)
                (if (equal (proof-byte-list size (proof-world-reg 0 before) machine)
                           (proof-byte-list size (proof-world-reg 1 before) machine))
                    1
                  0)))))

(defun symbols-find-candidate-matches-p (world)
  (and (symbols-find-byte-call-p world)
       (let ((size (proof-world-reg 6 world))
             (machine (proof-world-machine world))
             (candidate (boymoo-model::a64-unsigned
                         64 (+ 8 (symbols-candidate-name-address world)))))
         (equal (proof-byte-list size candidate machine)
                (proof-byte-list size (proof-world-reg 5 world) machine)))))

(defun symbols-find-step-pre-p (base world)
  (and (symbols-runtime-base-p base)
       (not (proof-world-stop world))
       (not (eq (car (proof-world-machine world)) :svc))
       (equal (proof-world-pc world) (symbols-runtime-address "rt:find-package-loop" base))
       (< (+ 16 (boymoo-model::a64-sp (proof-world-machine world))) (expt 2 64))))

(defun symbols-find-step-ready-p (byte-fuel base before)
  (let* ((probe (symbols-find-probe before))
         (compared (symbols-find-compared byte-fuel before))
         (exhausted (symbols-find-iteration-exhausted-p before))
         (call (symbols-find-byte-call-p before)))
    (and (symbols-path-ready-p (symbols-find-iteration-path before) base nil before)
         (implies call (symbols-byte-equality-return-p probe compared))
         (implies (or exhausted call)
                  (symbols-path-ready-p (symbols-find-result-path exhausted compared) base
                                        (symbols-find-result-target exhausted base compared)
                                        compared)))))

(defun symbols-find-step-fuel (byte-fuel before)
  (let* ((exhausted (symbols-find-iteration-exhausted-p before))
         (call (symbols-find-byte-call-p before))
         (compared (symbols-find-compared byte-fuel before)))
    (+ (len (symbols-find-iteration-path before))
       (if call (nfix byte-fuel) 0)
       (if (or exhausted call) (len (symbols-find-result-path exhausted compared)) 0))))

(local
 (defthm symbols-advance-zero
   (equal (proof-advance 0 world) world)
   :hints (("Goal" :in-theory (enable proof-advance)))))

(local
 (defthm symbols-find-step-advance-splits
   (let ((exhausted (symbols-find-iteration-exhausted-p before))
         (call (symbols-find-byte-call-p before))
         (compared (symbols-find-compared byte-fuel before)))
     (equal (proof-advance (symbols-find-step-fuel byte-fuel before) before)
            (if (or exhausted call)
                (proof-advance (len (symbols-find-result-path exhausted compared)) compared)
              (symbols-find-probe before))))
   :hints (("Goal"
            :use ((:instance proof-advance-append
                             (prefix (len (symbols-find-iteration-path before)))
                             (suffix (+ (if (symbols-find-byte-call-p before) (nfix byte-fuel) 0)
                                        (if (or (symbols-find-iteration-exhausted-p before)
                                                (symbols-find-byte-call-p before))
                                            (len (symbols-find-result-path
                                                  (symbols-find-iteration-exhausted-p before)
                                                  (symbols-find-compared byte-fuel before)))
                                          0)))
                             (world before))
                  (:instance proof-advance-append
                             (prefix (nfix byte-fuel))
                             (suffix (len (symbols-find-result-path
                                           (symbols-find-iteration-exhausted-p before)
                                           (symbols-find-compared byte-fuel before))))
                             (world (symbols-find-probe before))))
            :in-theory (disable symbols-find-byte-call-p symbols-find-iteration-exhausted-p
                                symbols-find-result-path symbols-find-iteration-path)))))

(local
 (defthm symbols-find-probe-has-frame
   (implies (and (symbols-find-step-pre-p base before)
                 (symbols-path-ready-p (symbols-find-iteration-path before) base nil before))
            (symbols-find-iteration-frame-p base before (symbols-find-probe before)))
   :hints (("Goal"
            :use ((:instance symbols-run-find-iteration (code-base base)))
            :in-theory (disable symbols-find-iteration-path symbols-find-iteration-frame-p
                                symbols-replay symbols-run-find-iteration)))
   :rule-classes nil))

(local
 (defthm symbols-compared-word-agrees-with-name
   (implies (and (symbols-find-byte-call-p before)
                 (symbols-find-iteration-frame-p base before probe)
                 (symbols-byte-equality-return-p probe compared))
            (equal (proof-world-reg 0 compared)
                   (if (symbols-find-candidate-matches-p before) 1 0)))
   :hints (("Goal"
            :use ((:instance symbols-byte-list-depends-on-memory
                             (size (proof-world-reg 6 before))
                             (address (proof-world-reg 5 before))
                             (first (proof-world-machine probe)) (last (proof-world-machine before)))
                  (:instance symbols-byte-list-depends-on-memory
                             (size (proof-world-reg 6 before))
                             (address (boymoo-model::a64-unsigned
                                       64 (+ 8 (symbols-candidate-name-address before))))
                             (first (proof-world-machine probe)) (last (proof-world-machine before))))
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p)
                            (symbols-candidate-name-address symbols-candidate-name-size
                             symbols-found-candidate proof-frame-return-p))))
   :rule-classes nil))

(local
 (defthm symbols-join-register-frames
   (implies (and (proof-register-frame-p highest left first middle)
                 (proof-register-frame-p highest right middle last)
                 (subsetp-equal left allowed) (subsetp-equal right allowed))
            (proof-register-frame-p highest allowed first last))
   :hints (("Goal" :use ((:instance symbols-frame-is-transitive (clobbers allowed))
                         (:instance symbols-frame-allows-more-clobbers
                                    (clobbers left) (before first) (after middle))
                         (:instance symbols-frame-allows-more-clobbers
                                    (clobbers right) (before middle) (after last)))))
   :rule-classes nil))

(defthm symbols-saved-word-preserved-by-read-only-frame
  (implies (and (symbols-no-memory-or-kernel-change-p before after)
                (equal (boymoo-model::a64-sp (proof-world-machine before))
                       (boymoo-model::a64-sp (proof-world-machine after))))
           (equal (symbols-stack-word offset before) (symbols-stack-word offset after)))
  :hints (("Goal" :in-theory (enable symbols-no-memory-or-kernel-change-p
                                    boymoo-model::a64-load)))
  :rule-classes nil)

(local
 (defthm symbols-find-compared-preserves-frame
   (let ((probe (symbols-find-probe before))
         (compared (symbols-find-compared byte-fuel before)))
     (implies (symbols-find-step-ready-p byte-fuel base before)
              (and (proof-register-frame-p 30 '(0 1 2 3 4) probe compared)
                   (symbols-no-memory-or-kernel-change-p probe compared)
                   (equal (boymoo-model::a64-sp (proof-world-machine probe))
                          (boymoo-model::a64-sp (proof-world-machine compared))))))
   :hints (("Goal" :in-theory (disable symbols-find-probe symbols-find-byte-call-p
                                       symbols-find-result-path symbols-find-result-target
                                       symbols-find-iteration-path)))
   :rule-classes nil))

(local
 (defthm symbols-find-ending-has-frame
   (let* ((probe (symbols-find-probe before))
          (compared (symbols-find-compared byte-fuel before))
          (exhausted (symbols-find-iteration-exhausted-p before))
          (path (symbols-find-result-path exhausted compared)))
     (implies (and (symbols-find-step-pre-p base before)
                   (or exhausted (symbols-find-byte-call-p before))
                   (symbols-find-step-ready-p byte-fuel base before)
                   (symbols-find-iteration-frame-p base before probe))
              (symbols-find-result-frame-p exhausted base compared
                                           (proof-advance (len path) compared))))
   :hints (("Goal"
            :use ((:instance symbols-run-find-result
                             (code-base base)
                             (before (symbols-find-compared byte-fuel before))
                             (exhausted (symbols-find-iteration-exhausted-p before))))
            :in-theory (disable symbols-find-result-path symbols-find-probe symbols-replay
                                symbols-find-result-frame-p proof-segment-p
                                symbols-run-find-result symbols-candidate-name-size)))
   :rule-classes nil))

(defconst *symbols-find-loop-clobbers* '(0 1 2 3 4 7 9 29 30))

(defun symbols-find-step-finishes-p (world)
  (or (symbols-find-iteration-exhausted-p world)
      (symbols-find-candidate-matches-p world)))

(defun symbols-find-step-frame-p (base before after)
  (let ((finished (symbols-find-step-finishes-p before))
        (sp (boymoo-model::a64-sp (proof-world-machine before))))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after)
                (if finished (symbols-stack-word 8 before)
                  (symbols-runtime-address "rt:find-package-loop" base)))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (if finished (+ sp 16) sp))
         (if finished
             (and (equal (proof-world-reg 0 after)
                         (if (symbols-find-iteration-exhausted-p before) 0
                           (symbols-found-candidate before)))
                  (equal (proof-world-reg 29 after) (symbols-stack-word 0 before))
                  (equal (proof-world-reg 30 after) (symbols-stack-word 8 before)))
           (equal (proof-world-reg 7 after)
                  (boymoo-model::a64-unsigned 64 (+ 8 (proof-world-reg 7 before)))))
         (proof-register-frame-p 30 *symbols-find-loop-clobbers* before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-find-step-frames-compose
   (let ((exhausted (symbols-find-iteration-exhausted-p before))
         (call (symbols-find-byte-call-p before)))
     (implies (and (symbols-find-iteration-frame-p base before probe)
                   (proof-register-frame-p 30 '(0 1 2 3 4) probe compared)
                   (symbols-no-memory-or-kernel-change-p probe compared)
                   (equal (boymoo-model::a64-sp (proof-world-machine probe))
                          (boymoo-model::a64-sp (proof-world-machine compared)))
                   (implies (not call) (equal compared probe))
                   (implies call (equal (proof-world-reg 0 compared)
                                        (if (symbols-find-candidate-matches-p before) 1 0)))
                   (if (or exhausted call)
                       (symbols-find-result-frame-p exhausted base compared after)
                     (equal after probe)))
              (symbols-find-step-frame-p base before after)))
   :hints (("Goal"
            :use ((:instance symbols-join-register-frames (highest 30)
                             (left '(0 1 2 7 9 30)) (right '(0 1 2 3 4))
                             (allowed *symbols-find-loop-clobbers*)
                             (first before) (middle probe) (last compared))
                  (:instance symbols-join-register-frames (highest 30)
                             (left *symbols-find-loop-clobbers*) (right '(0 29 30))
                             (allowed *symbols-find-loop-clobbers*)
                             (first before) (middle compared) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first before) (middle probe) (last compared))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first before) (middle compared) (last after))
                  (:instance symbols-saved-word-preserved-by-read-only-frame
                             (offset 0) (after compared))
                  (:instance symbols-saved-word-preserved-by-read-only-frame
                             (offset 8) (after compared))
                  (:instance symbols-frame-gives-register (highest 30) (register 7)
                             (clobbers '(0 1 2 3 4)) (before probe) (after compared))
                  (:instance symbols-frame-gives-register (highest 30) (register 9)
                             (clobbers '(0 1 2 3 4)) (before probe) (after compared))
                  (:instance symbols-frame-gives-register (highest 30) (register 7)
                             (clobbers '(0 29 30)) (before compared)))
            :in-theory (disable symbols-found-candidate symbols-stack-word
                                symbols-candidate-name-size symbols-candidate-name-address)))
   :rule-classes nil))

(defthm symbols-run-find-step
  (implies (and (symbols-find-step-pre-p code-base before)
                (symbols-find-step-ready-p byte-fuel code-base before))
           (symbols-find-step-frame-p code-base before
                                     (proof-advance (symbols-find-step-fuel byte-fuel before)
                                                    before)))
  :hints (("Goal"
           :use ((:instance symbols-find-probe-has-frame (base code-base))
                 (:instance symbols-find-ending-has-frame (base code-base))
                 (:instance symbols-find-compared-preserves-frame (base code-base))
                 (:instance symbols-compared-word-agrees-with-name
                            (base code-base) (probe (symbols-find-probe before))
                            (compared (symbols-find-compared byte-fuel before)))
                 (:instance symbols-find-step-frames-compose
                            (base code-base) (probe (symbols-find-probe before))
                            (compared (symbols-find-compared byte-fuel before))
                            (after (proof-advance (symbols-find-step-fuel byte-fuel before)
                                                  before))))
           :in-theory (disable symbols-find-iteration-path symbols-find-iteration-frame-p
                               symbols-find-result-path symbols-find-result-frame-p
                               symbols-find-step-fuel symbols-find-probe
                               symbols-find-step-frame-p symbols-candidate-name-size
                               symbols-byte-equality-return-p symbols-find-step-pre-p
                               symbols-find-result-target)))
  :rule-classes nil)
