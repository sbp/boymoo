(in-package "BOYMOO-PROOFS")

(include-book "divide-return")
(include-book "left-bitfield")
(include-book "long-traversal")
(include-book "sign-view")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-normalizer-entry-code* (division-runtime-block "rt:z-normalize" 0 1))
(defconst *division-normalizer-trim-code* (division-runtime-block "rt:z-trim" 0 6))
(defconst *division-normalizer-zero-code* (division-runtime-block "rt:z-trim-zero" 0 1))
(defconst *division-normalizer-header-code* (division-runtime-block "rt:z-write-header" 0 5))

(local
 (in-theory (disable ash floor mod proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-instruction-effect proof-segment-p division-before-cuts-p
                     division-instruction-prefix-ready-p division-instruction-sequence-ready-p
                     proof-frame-return-p proof-integer-view-p boymoo-model::a64-sp
                     boymoo-model::a64-nzcv boymoo-model::a64-memory boymoo-model::a64-write-bytes
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-normalizer-frame-p (before after)
  (and (proof-register-frame-p 30 '(1 2 3 4) before after)
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (equal (boymoo-model::a64-nzcv (proof-world-machine after))
              (boymoo-model::a64-nzcv (proof-world-machine before)))
       (equal (proof-world-regions after) (proof-world-regions before))
       (equal (proof-world-stop after) (proof-world-stop before))
       (equal (division-ordinary-world-p after) (division-ordinary-world-p before))))

(local
 (defthm division-normalizer-register-frame-reflexive
   (proof-register-frame-p limit clobbers world world)
   :hints (("Goal" :induct (proof-register-frame-p limit clobbers world world)))))

(local
 (defthm division-normalizer-register-frame-ignores-pc
   (equal (proof-register-frame-p limit clobbers before (division-set-pc pc after))
          (proof-register-frame-p limit clobbers before after))
   :hints (("Goal" :induct (proof-register-frame-p limit clobbers before after)))))

(local
 (defthm division-normalizer-register-frame-ignores-store
   (equal (proof-register-frame-p limit clobbers before (division-store-word address word after))
          (proof-register-frame-p limit clobbers before after))
   :hints (("Goal" :induct (proof-register-frame-p limit clobbers before after)))))

(local
 (defthm division-normalizer-register-frame-ignores-clobbers
   (implies (member-equal register clobbers)
            (equal (proof-register-frame-p limit clobbers before (division-write-reg register use-sp value after))
                   (proof-register-frame-p limit clobbers before after)))
   :hints (("Goal" :induct (proof-register-frame-p limit clobbers before after))
           ("Subgoal *1/3" :cases ((equal register limit))
            :expand ((proof-register-frame-p limit clobbers before (division-write-reg register use-sp value after))))
           ("Subgoal *1/2" :cases ((equal register limit)))
           ("Subgoal *1/1" :cases ((equal register limit))))))

(local
 (defthm division-normalizer-register-frame-transitive
   (implies (and (proof-register-frame-p limit clobbers first middle)
                 (proof-register-frame-p limit clobbers middle last))
            (proof-register-frame-p limit clobbers first last))
   :hints (("Goal" :induct (proof-register-frame-p limit clobbers first last)))))

(local
 (defthm division-normalizer-frame-transitive
   (implies (and (division-normalizer-frame-p first middle)
                 (division-normalizer-frame-p middle last))
            (division-normalizer-frame-p first last))
   :hints (("Goal"
            :use (:instance division-normalizer-register-frame-transitive (limit 30) (clobbers '(1 2 3 4)))
            :in-theory (disable proof-register-frame-p)))
   :rule-classes nil))

(local
 (defthm division-normalizer-register-frame-keeps-register
   (implies (and (proof-register-frame-p limit clobbers before after)
                 (natp limit) (natp register) (<= register limit)
                 (not (member-equal register clobbers)))
            (equal (proof-world-reg register after) (proof-world-reg register before)))
   :hints (("Goal" :induct (proof-register-frame-p limit clobbers before after))
           ("Subgoal *1/1" :cases ((equal register limit))))
   :rule-classes nil))

(local
 (defthm division-normalizer-frame-keeps-link-and-destination
   (implies (division-normalizer-frame-p before after)
            (and (equal (proof-world-reg 0 after) (proof-world-reg 0 before))
                 (equal (proof-world-reg 30 after) (proof-world-reg 30 before))))
   :hints (("Goal"
            :use ((:instance division-normalizer-register-frame-keeps-register
                             (register 0) (limit 30) (clobbers '(1 2 3 4)))
                  (:instance division-normalizer-register-frame-keeps-register
                             (register 30) (limit 30) (clobbers '(1 2 3 4))))
            :in-theory (disable proof-register-frame-p)))
   :rule-classes nil))

(defun division-normalizer-pending-limbs (world)
  (division-read-limbs (proof-world-reg 1 world) (+ 8 (proof-world-reg 3 world)) (proof-world-machine world)))

(defun division-normalizer-top-word (world)
  (proof-load-word (+ (proof-world-reg 3 world) (* 8 (proof-world-reg 1 world)))
                   (proof-world-machine world)))

(defun division-normalizer-trim-continues-p (world)
  (and (posp (proof-world-reg 1 world))
       (equal (division-normalizer-top-word world) 0)))

(defun division-normalizer-trim-instructions (world)
  (cond ((equal (proof-world-reg 1 world) 0)
         (cons (car *division-normalizer-trim-code*) *division-normalizer-zero-code*))
        ((division-normalizer-trim-continues-p world) *division-normalizer-trim-code*)
        (t (take 4 *division-normalizer-trim-code*))))

(defun division-normalizer-trim-inputs-p (world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 28 (proof-world-pc world)))
       (proof-span-p (proof-world-reg 3 world) (+ 8 (* 8 (proof-world-reg 1 world))))))

(defun division-normalizer-trim-outputs-p (world after)
  (let ((continues (division-normalizer-trim-continues-p world)))
    (and (division-normalizer-frame-p world after)
         (equal (proof-world-reg 3 after) (proof-world-reg 3 world))
         (equal (proof-world-reg 1 after)
                (if continues (1- (proof-world-reg 1 world)) (proof-world-reg 1 world)))
         (equal (proof-world-reg 2 after)
                (if (equal (proof-world-reg 1 world) 0) 0 (proof-world-reg 2 world)))
         (equal (proof-world-pc after)
                (if continues (proof-world-pc world) (+ 28 (proof-world-pc world))))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-memory (proof-world-machine world))))))

(local
 (defthm division-normalizer-load-is-word
   (unsigned-byte-p 64 (proof-load-word address machine))
   :hints (("Goal"
            :use (:instance division-read-bytes-value-range
                            (count 8) (memory (boymoo-model::a64-memory machine)))
            :in-theory (enable proof-load-word boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm division-normalizer-trim-effects
   (implies (division-normalizer-trim-inputs-p world)
            (division-normalizer-trim-outputs-p
             world (division-instruction-sequence (division-normalizer-trim-instructions world) world)))
   :hints (("Goal"
            :cases ((equal (proof-world-reg 1 world) 0)
                    (equal (division-normalizer-top-word world) 0))
            :use ((:instance division-normalizer-load-is-word
                             (address (+ (proof-world-reg 3 world) (* 8 (proof-world-reg 1 world))))
                             (machine (proof-world-machine world)))
                  (:instance division-world-register-in-word (register 1))
                  (:instance division-world-register-in-word (register 2))
                  (:instance division-world-register-in-word (register 3)))
            :in-theory (disable boymoo-model::a64-shift)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-normalizer-trim-checks-one-position
  (let* ((instructions (division-normalizer-trim-instructions world))
         (steps (len instructions)))
    (implies (and (division-normalizer-trim-inputs-p world)
                  (division-instruction-prefix-ready-p instructions cuts world))
             (and (division-before-cuts-p steps cuts world)
                  (division-normalizer-trim-outputs-p world (proof-advance steps world)))))
  :hints (("Goal"
           :use ((:instance division-normalizer-trim-effects)
                 (:instance division-instruction-prefix-advances
                            (instructions (division-normalizer-trim-instructions world))))
           :in-theory (disable division-normalizer-trim-inputs-p division-normalizer-trim-outputs-p
                               division-normalizer-trim-instructions division-instruction-sequence)))
  :rule-classes nil)

(local
 (defthm division-last-limb-determines-trim
   (equal (division-trim-limbs (append low (list high)))
          (if (equal high 0) (division-trim-limbs low) (append low (list high))))
   :hints (("Goal" :induct (append low (list high)))
           ("Subgoal *1/2" :cases ((equal high 0))))))

(local
 (defthm division-normalizer-read-one-limb
   (equal (division-read-limbs 1 address machine)
          (list (proof-load-word address machine)))
   :hints (("Goal" :expand ((division-read-limbs 1 address machine)
                            (division-read-limbs 0 (+ 8 address) machine))))))

(local
 (defthm division-normalizer-pending-limbs-split
   (implies (posp (proof-world-reg 1 world))
            (equal (division-normalizer-pending-limbs world)
                   (append (division-read-limbs (1- (proof-world-reg 1 world))
                                                (+ 8 (proof-world-reg 3 world))
                                                (proof-world-machine world))
                           (list (division-normalizer-top-word world)))))
   :hints (("Goal"
            :use (:instance division-read-adjacent-limb-spans
                            (low (1- (proof-world-reg 1 world))) (high 1)
                            (address (+ 8 (proof-world-reg 3 world))) (machine (proof-world-machine world)))
            :in-theory (disable division-read-limbs)))
   :rule-classes nil))

(local
 (defthm division-normalizer-trim-pending-limbs
   (implies (posp (proof-world-reg 1 world))
            (equal (division-trim-limbs (division-normalizer-pending-limbs world))
                   (if (equal (division-normalizer-top-word world) 0)
                       (division-trim-limbs (division-read-limbs (1- (proof-world-reg 1 world))
                                                               (+ 8 (proof-world-reg 3 world))
                                                               (proof-world-machine world)))
                     (division-normalizer-pending-limbs world))))
   :hints (("Goal"
            :use (:instance division-normalizer-pending-limbs-split)
            :in-theory (disable division-normalizer-pending-limbs division-normalizer-top-word
                                division-read-limbs)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-normalizer-trim-one-position
   (implies (division-normalizer-trim-outputs-p before after)
            (equal (if (division-normalizer-trim-continues-p before)
                       (division-trim-limbs (division-normalizer-pending-limbs after))
                     (division-normalizer-pending-limbs after))
                   (division-trim-limbs (division-normalizer-pending-limbs before))))
   :hints (("Goal"
            :use ((:instance division-normalizer-trim-pending-limbs (world before))
                  (:instance division-read-limbs-from-same-memory
                             (count (proof-world-reg 1 after)) (address (+ 8 (proof-world-reg 3 before)))
                             (first (proof-world-machine before)) (second (proof-world-machine after))))
            :in-theory (disable division-normalizer-frame-p)
            :cases ((posp (proof-world-reg 1 before)))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defun division-normalizer-trim-run-ready-p (limit cuts world)
  (declare (xargs :measure (nfix limit)))
  (and (equal limit (proof-world-reg 1 world))
       (division-normalizer-trim-inputs-p world)
       (division-instruction-prefix-ready-p (division-normalizer-trim-instructions world) cuts world)
       (or (not (division-normalizer-trim-continues-p world))
           (and (posp limit)
                (division-normalizer-trim-run-ready-p (1- limit) cuts (proof-advance 6 world))))))

(defun division-normalizer-trim-steps (limit world)
  (declare (xargs :measure (nfix limit)))
  (if (and (posp limit) (division-normalizer-trim-continues-p world))
      (+ 6 (division-normalizer-trim-steps (1- limit) (proof-advance 6 world)))
    (len (division-normalizer-trim-instructions world))))

(defun division-normalizer-trim-result-p (before after)
  (and (division-normalizer-frame-p before after)
       (equal (proof-world-reg 3 after) (proof-world-reg 3 before))
       (equal (proof-world-pc after) (+ 28 (proof-world-pc before)))
       (equal (division-normalizer-pending-limbs after)
              (division-trim-limbs (division-normalizer-pending-limbs before)))
       (equal (proof-world-reg 2 after)
              (if (atom (division-normalizer-pending-limbs after)) 0 (proof-world-reg 2 before)))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine before)))))

(local
 (defthm division-normalizer-trim-steps-is-natural
   (natp (division-normalizer-trim-steps limit world))
   :hints (("Goal" :induct (division-normalizer-trim-steps limit world)))
   :rule-classes :type-prescription))

(local
 (defthm division-normalizer-empty-pending-limbs
   (and (iff (consp (division-normalizer-pending-limbs world)) (posp (proof-world-reg 1 world)))
        (iff (division-normalizer-pending-limbs world) (posp (proof-world-reg 1 world))))
   :hints (("Goal"
            :expand ((division-read-limbs (proof-world-reg 1 world) (+ 8 (proof-world-reg 3 world))
                                          (proof-world-machine world)))))))

(local
 (defthm division-normalizer-trim-last-position
   (let ((steps (len (division-normalizer-trim-instructions world))))
     (implies (and (division-normalizer-trim-inputs-p world)
                   (division-instruction-prefix-ready-p (division-normalizer-trim-instructions world) cuts world)
                   (not (division-normalizer-trim-continues-p world)))
              (and (division-before-cuts-p steps cuts world)
                   (division-normalizer-trim-result-p world (proof-advance steps world)))))
   :hints (("Goal"
            :use ((:instance division-normalizer-trim-checks-one-position)
                  (:instance division-normalizer-trim-one-position
                             (before world) (after (proof-advance (len (division-normalizer-trim-instructions world)) world))))
            :in-theory (disable division-normalizer-pending-limbs division-normalizer-trim-instructions
                                division-normalizer-trim-inputs-p division-normalizer-frame-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-normalizer-trim-repeat-count
   (implies (division-normalizer-trim-continues-p world)
            (equal (len (division-normalizer-trim-instructions world)) 6))))

(defthm division-normalizer-trims-limb-list
  (let ((steps (division-normalizer-trim-steps limit world)))
    (implies (division-normalizer-trim-run-ready-p limit cuts world)
             (and (division-before-cuts-p steps cuts world)
                  (division-normalizer-trim-result-p world (proof-advance steps world)))))
  :hints (("Goal" :induct (division-normalizer-trim-steps limit world)
                  :in-theory (disable division-normalizer-frame-p division-normalizer-trim-continues-p
                                      division-normalizer-trim-instructions division-normalizer-pending-limbs
                                      division-normalizer-trim-run-ready-p division-normalizer-trim-inputs-p
                                      proof-advance-append division-before-cuts-append))
          ("Subgoal *1/2"
           :use ((:instance division-normalizer-trim-last-position))
           :expand ((division-normalizer-trim-run-ready-p limit cuts world)
                    (division-normalizer-trim-steps limit world))
           :cases ((division-normalizer-trim-continues-p world)))
          ("Subgoal *1/1"
           :expand ((division-normalizer-trim-run-ready-p limit cuts world)
                    (division-normalizer-trim-steps limit world))
           :use ((:instance division-normalizer-trim-checks-one-position)
                 (:instance division-normalizer-trim-one-position
                            (before world) (after (proof-advance 6 world)))
                 (:instance division-normalizer-frame-transitive
                            (first world) (middle (proof-advance 6 world))
                            (last (proof-advance (division-normalizer-trim-steps (1- limit) (proof-advance 6 world))
                                                 (proof-advance 6 world))))
                 (:instance proof-advance-append (prefix 6)
                            (suffix (division-normalizer-trim-steps (1- limit) (proof-advance 6 world))))
                 (:instance division-before-cuts-append (prefix 6)
                            (suffix (division-normalizer-trim-steps (1- limit) (proof-advance 6 world)))))))
  :rule-classes nil)

(defun division-normalizer-header-word (count)
  (+ 3 (* 2048 (1+ count))))

(defun division-normalizer-header-inputs-p (world)
  (and (division-ordinary-world-p world)
       (proof-span-p (proof-world-reg 0 world) 16)
       (unsigned-byte-p 64 (division-normalizer-header-word (proof-world-reg 1 world)))))

(defun division-normalizer-header-memory (address count sign memory)
  (division-write-window-limbs (list (division-normalizer-header-word count) sign) address memory))

(defun division-normalizer-header-outputs-p (world after)
  (and (division-normalizer-frame-p world after)
       (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
       (equal (proof-world-reg 2 after) (proof-world-reg 2 world))
       (equal (proof-world-pc after) (proof-world-reg 30 world))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (division-normalizer-header-memory (proof-world-reg 0 world) (proof-world-reg 1 world)
                                                 (proof-world-reg 2 world)
                                                 (boymoo-model::a64-memory (proof-world-machine world))))))

(local
 (defthm division-normalizer-header-effects
   (implies (division-normalizer-header-inputs-p world)
            (division-normalizer-header-outputs-p world (division-instruction-sequence
                                                         *division-normalizer-header-code* world)))
   :hints (("Goal"
            :in-theory (disable division-normalizer-register-frame-transitive)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-normalizer-complete-sequence-is-prefix
   (implies (division-instruction-sequence-ready-p instructions cuts world)
            (division-instruction-prefix-ready-p instructions cuts world))
   :hints (("Goal"
            :induct (division-instruction-sequence-ready-p instructions cuts world)
            :in-theory (e/d (division-instruction-sequence-ready-p division-instruction-prefix-ready-p)
                            (proof-instruction-at-p proof-instruction-access-p proof-instruction-effect
                             proof-world-stop proof-world-pc member-equal))
            :do-not '(generalize fertilize)))))

(defthm division-normalizer-writes-header-and-returns
  (let ((cuts (list (proof-world-reg 30 world))))
    (implies (and (division-normalizer-header-inputs-p world)
                  (division-instruction-sequence-ready-p *division-normalizer-header-code* cuts world))
             (and (division-before-cuts-p 5 cuts world)
                  (proof-segment-p 5 cuts world :cut (proof-advance 5 world))
                  (division-normalizer-header-outputs-p world (proof-advance 5 world)))))
  :hints (("Goal"
           :use ((:instance division-normalizer-header-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-normalizer-header-code*) (cuts (list (proof-world-reg 30 world))))
                 (:instance division-instruction-prefix-advances
                            (instructions *division-normalizer-header-code*) (cuts (list (proof-world-reg 30 world))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-normalizer-header-code*) (cuts (list (proof-world-reg 30 world)))))
           :in-theory (disable division-normalizer-header-inputs-p division-normalizer-header-outputs-p
                               division-instruction-sequence)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-normalizer-entry-effects
   (let* ((after (division-instruction-sequence *division-normalizer-entry-code* world))
          (address (proof-world-reg 0 world)))
     (implies (and (division-ordinary-world-p world)
                   (unsigned-byte-p 64 (+ 8 address))
                   (unsigned-byte-p 64 (+ 4 (proof-world-pc world))))
              (and (division-normalizer-frame-p world after)
                   (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
                   (equal (proof-world-reg 2 after) (proof-world-reg 2 world))
                   (equal (proof-world-reg 3 after) (+ 8 address))
                   (equal (proof-world-pc after) (+ 4 (proof-world-pc world)))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory (proof-world-machine world))))))
   :hints (("Goal" :do-not-induct t))
   :rule-classes nil))

(defthm division-normalizer-enters-trim-loop
  (let ((after (proof-advance 1 world))
        (address (proof-world-reg 0 world)))
    (implies (and (division-ordinary-world-p world)
                  (unsigned-byte-p 64 (+ 8 address))
                  (unsigned-byte-p 64 (+ 4 (proof-world-pc world)))
                  (division-instruction-prefix-ready-p *division-normalizer-entry-code* cuts world))
             (and (division-before-cuts-p 1 cuts world)
                  (division-normalizer-frame-p world after)
                  (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
                  (equal (proof-world-reg 2 after) (proof-world-reg 2 world))
                  (equal (proof-world-reg 3 after) (+ 8 address))
                  (equal (proof-world-pc after) (+ 4 (proof-world-pc world)))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world))))))
  :hints (("Goal"
           :use ((:instance division-normalizer-entry-effects)
                 (:instance division-instruction-prefix-advances (instructions *division-normalizer-entry-code*)))
           :in-theory (disable division-normalizer-frame-p division-instruction-sequence)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-normalizer-loads-header-and-sign
   (let* ((memory (boymoo-model::a64-memory before))
          (header (division-normalizer-header-word count))
          (updated (division-normalizer-header-memory address count sign memory)))
     (implies (and (proof-span-p address 16)
                   (unsigned-byte-p 64 header) (unsigned-byte-p 64 sign)
                   (equal (boymoo-model::a64-memory after) updated))
              (and (equal (proof-load-word address after) header)
                   (equal (proof-load-word (+ 8 address) after) sign))))
   :hints (("Goal"
            :use ((:instance division-read-after-fitting-write (count 8)
                             (value (division-normalizer-header-word count))
                             (memory (boymoo-model::a64-memory before)))
                  (:instance division-read-after-fitting-write (count 8) (address (+ 8 address))
                             (value sign) (memory (boymoo-model::a64-write-bytes
                                                   8 address (division-normalizer-header-word count)
                                                   (boymoo-model::a64-memory before))))
                  (:instance division-read-after-disjoint-write (count 8) (address (+ 8 address))
                             (size 8) (query address) (value sign)
                             (memory (boymoo-model::a64-write-bytes
                                      8 address (division-normalizer-header-word count)
                                      (boymoo-model::a64-memory before)))))
            :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                            (boymoo-model::a64-read-bytes division-read-after-fitting-write
                             division-read-after-disjoint-write))
            :do-not-induct t))
   :rule-classes nil))

(defun division-normalizer-header-state (digits world)
  (let ((trim (proof-advance 1 world)))
    (proof-advance (division-normalizer-trim-steps (len digits) trim) trim)))

(defun division-normalizer-prefix-steps (digits world)
  (+ 1 (division-normalizer-trim-steps (len digits) (proof-advance 1 world))))

(defun division-normalizer-call-steps (digits world)
  (+ 5 (division-normalizer-prefix-steps digits world)))

(defun division-normalizer-call-ready-p (digits world)
  (let* ((address (proof-world-reg 0 world))
         (count (len digits))
         (cuts (list (proof-world-reg 30 world)))
         (trim (proof-advance 1 world))
         (header (division-normalizer-header-state digits world)))
    (and (division-normalize-arguments-p address digits world)
         (proof-span-p address (division-view-bytes count))
         (unsigned-byte-p 64 (division-normalizer-header-word count))
         (unsigned-byte-p 64 (+ 4 (proof-world-pc world)))
         (division-ordinary-world-p world)
         (division-instruction-prefix-ready-p *division-normalizer-entry-code* cuts world)
         (division-normalizer-trim-run-ready-p count cuts trim)
         (division-instruction-sequence-ready-p *division-normalizer-header-code* cuts header))))

(local
 (defthm division-normalizer-reads-no-limbs
   (equal (division-read-limbs 0 address machine) nil)
   :hints (("Goal" :expand ((division-read-limbs 0 address machine))))))

(local
 (defthm division-normalizer-trim-count
   (equal (len (division-normalizer-pending-limbs world))
          (proof-world-reg 1 world))))

(local
 (defthm division-trimmed-limbs-empty-when-atom
   (implies (not (consp (division-trim-limbs digits)))
            (equal (division-trim-limbs digits) nil))
   :hints (("Goal" :expand ((division-trim-limbs digits))))))

(local
 (defthm division-normalizer-reads-entry-digits
   (implies (division-normalizer-call-ready-p digits world)
            (equal (division-normalizer-pending-limbs (proof-advance 1 world)) digits))
   :hints (("Goal"
            :use ((:instance division-normalizer-enters-trim-loop (cuts (list (proof-world-reg 30 world))))
                  (:instance division-read-limbs-from-same-memory
                             (count (len digits)) (address (+ 16 (proof-world-reg 0 world)))
                             (first (proof-world-machine world)) (second (proof-world-machine (proof-advance 1 world)))))
            :in-theory (disable division-normalizer-frame-p division-normalizer-trim-run-ready-p
                                division-normalizer-header-state division-normalizer-empty-pending-limbs
                                division-read-limbs division-digits-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-normalizer-pending-list-is-trimmed-input
   (implies (and (division-normalizer-trim-result-p before after)
                 (equal (division-normalizer-pending-limbs before) digits)
                 (equal (proof-world-reg 2 before) 0))
            (and (equal (division-normalizer-pending-limbs after) (division-trim-limbs digits))
                 (equal (proof-world-reg 1 after) (len (division-trim-limbs digits)))
                 (equal (proof-world-reg 2 after) 0)))
   :hints (("Goal"
            :use (:instance division-normalizer-trim-count (world after))
            :in-theory (disable division-normalizer-pending-limbs division-trim-limbs division-normalizer-frame-p
                                division-normalizer-empty-pending-limbs division-normalizer-trim-count)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-normalizer-trim-phase-frame
   (implies (and (division-normalizer-frame-p entry trim)
                 (division-normalizer-trim-result-p trim header)
                 (equal (proof-world-reg 3 trim) (+ 8 (proof-world-reg 0 entry)))
                 (equal (boymoo-model::a64-memory (proof-world-machine trim))
                        (boymoo-model::a64-memory (proof-world-machine entry))))
            (and (division-normalizer-frame-p entry header)
                 (equal (proof-world-reg 0 header) (proof-world-reg 0 entry))
                 (equal (proof-world-reg 30 header) (proof-world-reg 30 entry))
                 (equal (proof-world-reg 3 header) (+ 8 (proof-world-reg 0 entry)))
                 (equal (division-ordinary-world-p header) (division-ordinary-world-p entry))
                 (equal (boymoo-model::a64-memory (proof-world-machine header))
                        (boymoo-model::a64-memory (proof-world-machine entry)))))
   :hints (("Goal"
            :use ((:instance division-normalizer-frame-transitive (first entry) (middle trim) (last header))
                  (:instance division-normalizer-frame-keeps-link-and-destination (before entry) (after header)))
            :in-theory (disable proof-register-frame-p division-normalizer-pending-limbs division-trim-limbs
                                division-normalizer-empty-pending-limbs)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-normalizer-pending-limbs-at-destination
   (implies (and (equal (proof-world-reg 3 world) (+ 8 address))
                 (equal (proof-world-reg 1 world) count)
                 (equal (division-normalizer-pending-limbs world) digits))
            (equal (division-read-limbs count (+ 16 address) (proof-world-machine world)) digits))
   :hints (("Goal"
            :in-theory (disable division-read-limbs division-normalizer-empty-pending-limbs)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-normalizer-call-prepares-header
   (let ((header (division-normalizer-header-state digits world))
         (address (proof-world-reg 0 world))
         (trimmed (division-trim-limbs digits)))
     (implies (division-normalizer-call-ready-p digits world)
              (and (division-normalizer-frame-p world header)
                   (division-normalizer-header-inputs-p header)
                   (equal (proof-world-reg 0 header) address)
                   (equal (proof-world-reg 30 header) (proof-world-reg 30 world))
                   (equal (proof-world-reg 1 header) (len trimmed))
                   (equal (proof-world-reg 2 header) 0)
                   (proof-span-p address (division-view-bytes (len trimmed)))
                   (equal (division-read-limbs (len trimmed) (+ 16 address) (proof-world-machine header))
                          trimmed)
                   (equal (boymoo-model::a64-memory (proof-world-machine header))
                          (boymoo-model::a64-memory (proof-world-machine world))))))
   :hints (("Goal"
            :use ((:instance division-normalizer-enters-trim-loop (cuts (list (proof-world-reg 30 world))))
                  (:instance division-normalizer-reads-entry-digits)
                  (:instance division-normalizer-trims-limb-list
                             (limit (len digits)) (cuts (list (proof-world-reg 30 world))) (world (proof-advance 1 world)))
                  (:instance division-normalizer-pending-list-is-trimmed-input
                             (before (proof-advance 1 world)) (after (division-normalizer-header-state digits world)))
                  (:instance division-normalizer-trim-phase-frame
                             (entry world) (trim (proof-advance 1 world))
                             (header (division-normalizer-header-state digits world)))
                  (:instance division-normalizer-pending-limbs-at-destination
                             (address (proof-world-reg 0 world))
                             (world (division-normalizer-header-state digits world))
                             (count (len (division-trim-limbs digits)))
                             (digits (division-trim-limbs digits)))
                  (:instance division-trim-limbs-correct))
            :in-theory (disable division-normalizer-trim-run-ready-p division-normalizer-trim-steps
                                division-normalizer-trim-result-p division-normalizer-frame-p
                                division-normalizer-pending-limbs division-read-limbs-view-magnitude
                                division-trim-limbs division-read-limbs division-normalizer-trim-count
                                division-normalizer-empty-pending-limbs
                                proof-register-frame-p division-normalized-limbs-p
                                division-magnitude division-digits-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-normalizer-call-meets-caller-cut
   (let* ((header (division-normalizer-header-state digits world))
          (after (proof-advance 5 header))
          (steps (division-normalizer-call-steps digits world))
          (cut (list (proof-world-reg 30 world))))
     (implies (division-normalizer-call-ready-p digits world)
              (and (equal (proof-advance steps world) after)
                   (proof-segment-p steps cut world :cut after)
                   (division-normalizer-frame-p world after)
                   (division-normalizer-header-outputs-p header after))))
   :hints (("Goal"
            :use ((:instance division-normalizer-call-prepares-header)
                  (:instance division-normalizer-enters-trim-loop (cuts (list (proof-world-reg 30 world))))
                  (:instance division-normalizer-trims-limb-list
                             (limit (len digits)) (cuts (list (proof-world-reg 30 world))) (world (proof-advance 1 world)))
                  (:instance division-normalizer-writes-header-and-returns
                             (world (division-normalizer-header-state digits world)))
                  (:instance division-normalizer-frame-transitive
                             (first world) (middle (division-normalizer-header-state digits world))
                             (last (proof-advance 5 (division-normalizer-header-state digits world))))
                  (:instance proof-advance-append (prefix 1)
                             (suffix (division-normalizer-trim-steps (len digits) (proof-advance 1 world))))
                  (:instance proof-advance-append (prefix (division-normalizer-prefix-steps digits world)) (suffix 5))
                  (:instance division-before-cuts-append (prefix 1) (cuts (list (proof-world-reg 30 world)))
                             (suffix (division-normalizer-trim-steps (len digits) (proof-advance 1 world))))
                  (:instance division-before-cuts-append (prefix (division-normalizer-prefix-steps digits world))
                             (suffix 5) (cuts (list (proof-world-reg 30 world))))
                  (:instance division-segment-from-cut-free-prefix
                             (count (division-normalizer-call-steps digits world)) (cuts (list (proof-world-reg 30 world)))))
            :in-theory (disable division-normalizer-trim-run-ready-p division-normalizer-trim-steps
                                division-normalizer-trim-result-p proof-register-frame-p
                                division-normalizer-header-inputs-p division-normalize-arguments-p
                                division-trim-limbs division-magnitude division-normalizer-header-word
                                division-normalizer-header-memory division-read-limbs
                                division-before-cuts-append proof-advance-append)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-normalizer-stores-normalized-view
   (let* ((address (proof-world-reg 0 world))
          (trimmed (division-trim-limbs digits))
          (count (len trimmed))
          (before (division-normalizer-header-state digits world))
          (after (proof-advance 5 before)))
     (implies (division-normalizer-call-ready-p digits world)
              (and (proof-integer-view-p (division-magnitude digits) address count after)
                   (equal (proof-world-reg 1 after) count)
                   (equal (proof-world-reg 2 after) 0))))
   :hints (("Goal"
            :use ((:instance division-normalizer-call-prepares-header)
                  (:instance division-normalizer-call-meets-caller-cut)
                  (:instance division-normalizer-loads-header-and-sign
                             (count (len (division-trim-limbs digits))) (sign 0) (address (proof-world-reg 0 world))
                             (before (proof-world-machine (division-normalizer-header-state digits world)))
                             (after (proof-world-machine (proof-advance 5 (division-normalizer-header-state digits world)))))
                  (:instance division-limbs-after-disjoint-window-writes
                             (count (len (division-trim-limbs digits))) (address (+ 16 (proof-world-reg 0 world)))
                             (target (proof-world-reg 0 world))
                             (written (list (division-normalizer-header-word (len (division-trim-limbs digits))) 0))
                             (before (proof-world-machine (division-normalizer-header-state digits world)))
                             (after (proof-world-machine (proof-advance 5 (division-normalizer-header-state digits world)))))
                  (:instance division-view-from-normalized-words
                             (count (len (division-trim-limbs digits))) (address (proof-world-reg 0 world))
                             (world (proof-advance 5 (division-normalizer-header-state digits world))))
                  (:instance division-trim-limbs-correct))
            :in-theory (e/d (division-normalizer-header-inputs-p)
                            (division-normalizer-header-state division-normalizer-trim-run-ready-p
                             division-normalizer-frame-p division-normalizer-call-steps
                             division-trim-limbs division-magnitude division-read-limbs
                             division-normalized-limbs-p division-digits-p
                             division-write-window-limbs division-ordinary-world-p))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-normalizer-ready-start-is-unstopped
   (implies (division-normalizer-call-ready-p digits world)
            (not (proof-world-stop world)))
   :hints (("Goal"
            :expand ((division-instruction-prefix-ready-p *division-normalizer-entry-code*
                                                          (list (proof-world-reg 30 world)) world))
            :in-theory (disable division-normalizer-trim-run-ready-p division-normalizer-header-state
                                division-normalize-arguments-p proof-instruction-at-p
                                proof-instruction-access-p proof-span-p division-ordinary-world-p)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-normalizer-returns-unsigned-view
  (let* ((steps (division-normalizer-call-steps digits world))
         (after (proof-advance steps world))
         (address (proof-world-reg 0 world))
         (count (len (division-trim-limbs digits))))
    (implies (division-normalizer-call-ready-p digits world)
             (and (proof-segment-p steps (list (proof-world-reg 30 world)) world :cut after)
                  (division-unsigned-normalize-return-p digits world after)
                  (equal (proof-world-reg 1 after) count)
                  (equal (proof-world-reg 2 after) 0)
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (division-normalizer-header-memory address count 0
                                                            (boymoo-model::a64-memory (proof-world-machine world)))))))
  :hints (("Goal"
           :use ((:instance division-normalizer-ready-start-is-unstopped)
                 (:instance division-normalizer-stores-normalized-view)
                 (:instance division-normalizer-call-prepares-header)
                 (:instance division-normalizer-call-meets-caller-cut))
           :in-theory (e/d (proof-frame-return-p)
                           (division-normalizer-header-state division-normalizer-trim-run-ready-p
                            division-normalizer-call-steps division-normalizer-header-memory
                            division-trim-limbs division-magnitude division-read-limbs
                            proof-register-frame-p division-normalize-arguments-p
                            division-normalizer-header-inputs-p division-ordinary-world-p))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
