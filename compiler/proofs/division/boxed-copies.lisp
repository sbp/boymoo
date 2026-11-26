(in-package "BOYMOO-PROOFS")

(include-book "boxed-entry")
(include-book "copy")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-gcd-first-copy-prefix* (division-runtime-block "rt:z-gcd-copy" 0 5))
(defconst *division-gcd-second-copy-prefix* (division-runtime-block "rt:z-gcd-copy" 5 4))
(defconst *division-gcd-copy-to-copy*
  (- (division-runtime-offset "rt:z-copy") (division-runtime-offset "rt:z-gcd-copy")))

(local
 (in-theory (disable floor mod ash proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-load-word proof-segment-p
                     division-instruction-sequence-ready-p division-copy-call-ready-p
                     division-step-sum proof-integer-view-p proof-memory-span-agrees-p
                     boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-gcd-copy-prefix (second)
  (if second *division-gcd-second-copy-prefix* *division-gcd-first-copy-prefix*))

(defun division-gcd-copy-target (second world)
  (+ (proof-world-pc world) *division-gcd-copy-to-copy* (if second -20 0)))

(defun division-gcd-copy-address (second world)
  (division-buffer-base (proof-world-reg 19 world) (proof-world-reg 20 world) (if second 4 3)))

(defun division-gcd-copy-prefix-inputs-p (second world)
  (let ((stride (proof-world-reg 20 world)))
    (and (division-ordinary-world-p world) (posp stride)
         (unsigned-byte-p 64 (+ (if second 16 20) (proof-world-pc world)))
         (unsigned-byte-p 64 (division-gcd-copy-target second world))
         (proof-span-p (proof-world-reg 19 world) (* 5 stride))
         (or (not second) (equal (proof-world-reg 21 world) (division-gcd-copy-address nil world))))))

(defun division-gcd-copy-prefix-output-p (second world after)
  (let ((target (division-gcd-copy-address second world)))
    (and (equal (proof-world-pc after) (division-gcd-copy-target second world))
         (equal (proof-world-reg 30 after) (+ (if second 16 20) (proof-world-pc world)))
         (equal (proof-world-reg 0 after) (proof-world-reg (if second 22 21) world))
         (equal (proof-world-reg 1 after) target)
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
         (equal (proof-world-reg 21 after) (if second (proof-world-reg 21 world) target))
         (equal (proof-world-reg 22 after) (if second target (proof-world-reg 22 world)))
         (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp (proof-world-machine world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory (proof-world-machine world))))))

(local
 (defthm division-gcd-copy-prefix-effects
   (implies (division-gcd-copy-prefix-inputs-p second world)
            (division-gcd-copy-prefix-output-p
             second world (division-instruction-sequence (division-gcd-copy-prefix second) world)))
   :hints (("Goal" :cases (second) :do-not-induct t))
   :rule-classes nil))

(defthm division-gcd-copy-passes-operands
  (let* ((instructions (division-gcd-copy-prefix second))
         (steps (len instructions))
         (cuts (list (division-gcd-copy-target second world)))
         (after (proof-advance steps world)))
    (implies (and (division-gcd-copy-prefix-inputs-p second world)
                  (division-instruction-sequence-ready-p instructions cuts world))
             (and (proof-segment-p steps cuts world :cut after)
                  (division-gcd-copy-prefix-output-p second world after))))
  :hints (("Goal"
           :use ((:instance division-gcd-copy-prefix-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions (division-gcd-copy-prefix second))
                            (cuts (list (division-gcd-copy-target second world))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions (division-gcd-copy-prefix second))
                            (cuts (list (division-gcd-copy-target second world)))))
           :in-theory (disable division-gcd-copy-prefix-inputs-p division-gcd-copy-prefix-output-p
                               division-gcd-copy-target division-instruction-sequence)))
  :rule-classes nil)

(defun division-gcd-copy-counts (a-count b-count)
  (list 5 (division-step-sum (division-copy-call-counts a-count)) 4
        (division-step-sum (division-copy-call-counts b-count))))

(defun division-gcd-copy-steps (a-count b-count)
  (division-step-sum (division-gcd-copy-counts a-count b-count)))

(defun division-gcd-copy-state (phase a-count b-count world)
  (division-advance-chain (take phase (division-gcd-copy-counts a-count b-count)) world))

(defun division-gcd-copy-prefix-ready-p (second world)
  (and (division-gcd-copy-prefix-inputs-p second world)
       (division-instruction-sequence-ready-p (division-gcd-copy-prefix second)
                                              (list (division-gcd-copy-target second world)) world)))

(defun division-gcd-copies-ready-p (a b a-count b-count world)
  (let* ((a-copy (division-gcd-copy-state 1 a-count b-count world))
         (a-done (division-gcd-copy-state 2 a-count b-count world))
         (b-copy (division-gcd-copy-state 3 a-count b-count world))
         (b-done (division-gcd-copy-state 4 a-count b-count world))
         (left (division-gcd-copy-address nil world))
         (left-bytes (division-view-bytes a-count))
         (slot (division-boxed-stack-address 80 world)))
    (and (division-gcd-copy-prefix-ready-p nil world)
         (division-copy-call-ready-p a a-count a-copy)
         (division-gcd-copy-prefix-ready-p t a-done)
         (division-copy-call-ready-p b b-count b-copy)
         (proof-span-p left left-bytes)
         (proof-memory-span-agrees-p left (+ left left-bytes) a-done b-done)
         (proof-span-p slot 8)
         (proof-memory-span-agrees-p slot (+ slot 8) world b-done))))

(local
 (defthm division-gcd-copy-states-advance
   (equal (division-gcd-copy-state 4 a-count b-count world)
          (proof-advance (division-gcd-copy-steps a-count b-count) world))
   :hints (("Goal"
            :use (:instance division-advance-chain-sum (counts (division-gcd-copy-counts a-count b-count)))
            :in-theory (disable division-advance-chain division-copy-call-counts)))
   :rule-classes nil))

(local
 (defthm division-gcd-copies-move-views-to-reservation
   (let* ((a-done (division-gcd-copy-state 2 a-count b-count world))
          (after (division-gcd-copy-state 4 a-count b-count world))
          (left (division-gcd-copy-address nil world))
          (right (division-gcd-copy-address t world))
          (sp (boymoo-model::a64-sp (proof-world-machine world))))
     (implies (division-gcd-copies-ready-p a b a-count b-count world)
              (and (proof-integer-view-p a left a-count a-done)
                   (proof-integer-view-p b right b-count after)
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                   (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
                   (equal (proof-world-reg 21 after) left)
                   (equal (proof-world-reg 22 after) right)
                   (equal (boymoo-model::a64-sp (proof-world-machine after)) sp)
                   (equal (proof-world-pc after) (+ 36 (proof-world-pc world))))))
   :hints (("Goal"
            :use ((:instance division-gcd-copy-passes-operands (second nil))
                  (:instance division-copy-call-returns-view
                             (value a) (count a-count) (world (division-gcd-copy-state 1 a-count b-count world)))
                  (:instance division-gcd-copy-passes-operands
                             (second t) (world (division-gcd-copy-state 2 a-count b-count world)))
                  (:instance division-copy-call-returns-view
                             (value b) (count b-count) (world (division-gcd-copy-state 3 a-count b-count world))))
            :in-theory (disable division-gcd-copy-prefix-inputs-p division-gcd-copy-target
                                division-copy-call-counts division-view-bytes)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-gcd-copies-initialize-rotation
  (let* ((after (proof-advance (division-gcd-copy-steps a-count b-count) world))
         (slot (division-boxed-stack-address 80 world)))
    (implies (division-gcd-copies-ready-p a b a-count b-count world)
             (and (proof-integer-view-p a (proof-world-reg 21 after) a-count after)
                  (proof-integer-view-p b (proof-world-reg 22 after) b-count after)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
                  (equal (proof-world-reg 21 after) (division-gcd-copy-address nil world))
                  (equal (proof-world-reg 22 after) (division-gcd-copy-address t world))
                  (equal (proof-world-pc after) (+ 36 (proof-world-pc world)))
                  (equal (division-boxed-stack-address 80 after) slot)
                  (equal (proof-load-word slot (proof-world-machine after))
                         (proof-load-word slot (proof-world-machine world))))))
  :hints (("Goal"
           :use ((:instance division-gcd-copy-states-advance)
                 (:instance division-gcd-copies-move-views-to-reservation)
                 (:instance division-integer-view-after-span-agreement
                            (value a) (count a-count)
                            (address (division-gcd-copy-address nil world)) (start (division-gcd-copy-address nil world))
                            (end (+ (division-gcd-copy-address nil world) (division-view-bytes a-count)))
                            (before (division-gcd-copy-state 2 a-count b-count world))
                            (after (division-gcd-copy-state 4 a-count b-count world)))
                 (:instance division-read-after-span-agreement
                            (count 8) (start (division-boxed-stack-address 80 world))
                            (end (+ 8 (division-boxed-stack-address 80 world)))
                            (address (division-boxed-stack-address 80 world)) (before world)
                            (after (division-gcd-copy-state 4 a-count b-count world))))
           :in-theory (e/d (proof-load-word)
                           (boymoo-model::a64-load division-view-bytes division-gcd-copy-address
                            division-gcd-copy-state division-gcd-copy-prefix-ready-p))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
