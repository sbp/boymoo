(in-package "BOYMOO-PROOFS")

(include-book "shift-loops")
(include-book "divide-return")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-left-shift-entry-instructions*
  (division-runtime-block "rt:z-divide-shift-left" 0 2))
(defconst *division-left-shift-return-instructions*
  (division-runtime-block "rt:z-divide-shift-left" 11 1))

(local
 (in-theory (disable floor mod ash expt proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-load-word proof-segment-p
                     division-before-cuts-p division-instruction-prefix-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-sp)))

(defun division-shift-init-output-p (world after)
  (and (equal (proof-world-pc after) (+ 8 (proof-world-pc world)))
       (equal (proof-world-reg 4 after) 0)
       (equal (proof-world-reg 6 after) 0)
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (division-left-shift-frame-p world after)))

(local
 (defthm division-shift-init-effects
   (implies (and (division-ordinary-world-p world) (unsigned-byte-p 64 (+ 8 (proof-world-pc world))))
            (division-shift-init-output-p
             world (division-instruction-sequence *division-left-shift-entry-instructions* world)))
   :rule-classes nil))

(defthm division-shift-left-initializes-offset-and-carry
  (implies (and (division-ordinary-world-p world) (unsigned-byte-p 64 (+ 8 (proof-world-pc world)))
                (division-instruction-prefix-ready-p *division-left-shift-entry-instructions* cuts world))
           (and (division-before-cuts-p 2 cuts world)
                (division-shift-init-output-p world (proof-advance 2 world))))
  :hints (("Goal"
           :use ((:instance division-shift-init-effects)
                 (:instance division-instruction-prefix-advances (instructions *division-left-shift-entry-instructions*)))
           :in-theory (disable division-shift-init-output-p division-instruction-sequence)))
  :rule-classes nil)

(defun division-shift-left-return-output-p (world after)
  (and (equal (proof-world-pc after) (proof-world-reg 30 world))
       (equal (proof-world-reg 6 after) (proof-world-reg 6 world))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (division-left-shift-frame-p world after)))

(local
 (defthm division-shift-left-return-effects
   (implies (division-ordinary-world-p world)
            (division-shift-left-return-output-p
             world (division-instruction-sequence *division-left-shift-return-instructions* world)))
   :rule-classes nil))

(defthm division-shift-left-return-advances
  (implies (and (division-ordinary-world-p world)
                (division-instruction-prefix-ready-p *division-left-shift-return-instructions* cuts world))
           (and (division-before-cuts-p 1 cuts world)
                (division-shift-left-return-output-p world (proof-advance 1 world))))
  :hints (("Goal"
           :use ((:instance division-shift-left-return-effects)
                 (:instance division-instruction-prefix-advances (instructions *division-left-shift-return-instructions*)))
           :in-theory (disable division-shift-left-return-output-p division-instruction-sequence)))
  :rule-classes nil)

(defun division-left-shift-call-counts (digits)
  (list 2 (* 9 (len digits)) 1))

(defun division-left-shift-call-steps (digits)
  (division-step-sum (division-left-shift-call-counts digits)))

(defun division-left-shift-call-ready-p (digits world)
  (let* ((cuts (list (proof-world-reg 30 world)))
         (start (proof-advance 2 world))
         (end (proof-advance (* 9 (len digits)) start))
         (bytes (* 8 (len digits)))
         (shift (proof-world-reg 3 world)))
    (and (consp digits) (division-digits-p digits)
         (division-ordinary-world-p world) (not (proof-world-stop world))
         (unsigned-byte-p 64 (+ 8 (proof-world-pc world)))
         (natp shift) (< shift 32)
         (equal (proof-world-reg 2 world) bytes)
         (proof-span-p (proof-world-reg 1 world) bytes)
         (division-instruction-prefix-ready-p *division-left-shift-entry-instructions* cuts world)
         (division-left-shift-loop-ready-p digits start)
         (division-before-cuts-p (* 9 (len digits)) cuts start)
         (division-ordinary-world-p end)
         (division-instruction-prefix-ready-p *division-left-shift-return-instructions* cuts end))))

(local
 (defthm division-left-shift-call-goes-to-exit
   (let* ((start (proof-advance 2 world))
          (end (proof-advance (* 9 (len digits)) start))
          (after (proof-advance (division-left-shift-call-steps digits) world))
          (cuts (list (proof-world-reg 30 world))))
     (implies (division-left-shift-call-ready-p digits world)
              (and (division-before-cuts-p (division-left-shift-call-steps digits) cuts world)
                   (division-shift-init-output-p world start)
                   (division-left-shift-loop-output-p digits start end)
                   (division-shift-left-return-output-p end after))))
   :hints (("Goal"
            :use ((:instance division-shift-left-initializes-offset-and-carry (cuts (list (proof-world-reg 30 world))))
                  (:instance division-left-shift-loop-correct (world (proof-advance 2 world)))
                  (:instance division-shift-left-return-advances
                             (cuts (list (proof-world-reg 30 world)))
                             (world (proof-advance (* 9 (len digits)) (proof-advance 2 world))))
                  (:instance division-advance-chain-sum (counts (division-left-shift-call-counts digits)))
                  (:instance division-chain-keeps-before-cuts
                             (counts (division-left-shift-call-counts digits)) (cuts (list (proof-world-reg 30 world)))))
            :in-theory (disable division-left-shift-loop-output-p division-shift-left-return-output-p
                                division-left-shift-loop-ready-p division-step-sum)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-left-shift-call-returns-shifted-limbs
  (let* ((steps (division-left-shift-call-steps digits))
         (after (proof-advance steps world))
         (cuts (list (proof-world-reg 30 world)))
         (target (proof-world-reg 1 world))
         (scale (expt 2 (proof-world-reg 3 world)))
         (written (division-read-limbs (len digits) target (proof-world-machine after))))
    (implies (division-left-shift-call-ready-p digits world)
             (mv-let (shifted carry)
               (division-left-shift-limbs digits 0 scale)
               (and (proof-segment-p steps cuts world :cut after)
                    (equal (proof-world-pc after) (proof-world-reg 30 world))
                    (division-left-shift-frame-p world after)
                    (equal written shifted)
                    (equal (proof-world-reg 6 after) carry)
                    (equal (boymoo-model::a64-memory (proof-world-machine after))
                           (division-write-window-limbs
                            shifted target (boymoo-model::a64-memory (proof-world-machine world))))))))
  :hints (("Goal"
           :use ((:instance division-left-shift-call-goes-to-exit)
                 (:instance division-limb-scale-fits (shift (proof-world-reg 3 world)))
                 (:instance division-left-shift-limbs-correct (carry 0) (scale (expt 2 (proof-world-reg 3 world))))
                 (:instance division-read-window-limb-writes
                            (digits (mv-nth 0 (division-left-shift-limbs digits 0 (expt 2 (proof-world-reg 3 world)))))
                            (address (proof-world-reg 1 world))
                            (before (proof-world-machine world))
                            (after (proof-world-machine (proof-advance (division-left-shift-call-steps digits) world))))
                 (:instance division-segment-from-cut-free-prefix
                            (count (division-left-shift-call-steps digits)) (cuts (list (proof-world-reg 30 world)))))
           :in-theory (disable division-left-shift-loop-ready-p division-left-shift-call-steps
                               division-left-shift-limbs division-read-limbs division-write-window-limbs
                               division-digits-p division-place-value division-magnitude)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
