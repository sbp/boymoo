(in-package "BOYMOO-PROOFS")

(include-book "normalization-machine")
(include-book "left-shift-call")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-first-left-shift-call-instructions*
  (division-runtime-block "rt:z-divide" 25 5))
(defconst *division-second-left-shift-call-instructions*
  (division-runtime-block "rt:z-divide" 30 6))
(defconst *division-scale-window-setup-instructions*
  (division-runtime-block "rt:z-divide" 36 5))

(defun division-scale-call-offset (second)
  (- (division-runtime-offset "rt:z-divide-shift-left")
     (+ (division-runtime-offset "rt:z-divide") (if second 120 100))))

(defun division-scale-call-instructions (second)
  (if second *division-second-left-shift-call-instructions* *division-first-left-shift-call-instructions*))

(local
 (in-theory (disable floor mod ash expt proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-load-word proof-segment-p
                     division-instruction-sequence-ready-p division-instruction-prefix-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-sp boymoo-model::a64-write-bytes
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-scale-scratch-frame-p (world after)
  (and (equal (proof-world-reg 7 after) (proof-world-reg 7 world))
       (equal (proof-world-reg 8 after) (proof-world-reg 8 world))
       (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
       (equal (proof-world-reg 10 after) (proof-world-reg 10 world))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
       (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine world)))
       (equal (proof-world-stop after) (proof-world-stop world))))

(defun division-scale-carry-address (world)
  (+ (proof-world-reg 19 world) (proof-world-reg 9 world)))

(defun division-scale-call-inputs-p (second world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ (if second 24 20) (proof-world-pc world)))
       (unsigned-byte-p 64 (+ (division-scale-call-offset second) (proof-world-pc world)))
       (or (not second) (proof-span-p (division-scale-carry-address world) 8))))

(defun division-scale-call-output-p (second world after)
  (let ((memory (boymoo-model::a64-memory (proof-world-machine world))))
    (and (equal (proof-world-reg 0 after) (proof-world-reg (if second 8 7) world))
         (equal (proof-world-reg 1 after) (proof-world-reg (if second 20 19) world))
         (equal (proof-world-reg 2 after) (proof-world-reg (if second 22 9) world))
         (equal (proof-world-reg 3 after) (proof-world-reg 10 world))
         (equal (proof-world-reg 30 after) (+ (if second 24 20) (proof-world-pc world)))
         (equal (proof-world-pc after) (+ (division-scale-call-offset second) (proof-world-pc world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (if second
                    (boymoo-model::a64-write-bytes 8 (division-scale-carry-address world)
                                                  (proof-world-reg 6 world) memory)
                  memory))
         (division-scale-scratch-frame-p world after)
         (division-ordinary-world-p after))))

(local
 (defthm division-scale-shift-call-effects
   (implies (division-scale-call-inputs-p second world)
            (division-scale-call-output-p
             second world (division-instruction-sequence (division-scale-call-instructions second) world)))
   :hints (("Goal" :cases (second) :do-not-induct t))
   :rule-classes nil))

(defthm division-scale-shift-call-passes-limb-spans
  (let* ((instructions (division-scale-call-instructions second))
         (cuts (list (+ (division-scale-call-offset second) (proof-world-pc world))))
         (steps (len instructions))
         (after (proof-advance steps world)))
    (implies (and (division-scale-call-inputs-p second world)
                  (division-instruction-sequence-ready-p instructions cuts world))
             (and (proof-segment-p steps cuts world :cut after)
                  (division-scale-call-output-p second world after))))
  :hints (("Goal"
           :use ((:instance division-scale-shift-call-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions (division-scale-call-instructions second))
                            (cuts (list (+ (division-scale-call-offset second) (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions (division-scale-call-instructions second))
                            (cuts (list (+ (division-scale-call-offset second) (proof-world-pc world))))))
           :in-theory (disable division-scale-call-inputs-p division-scale-call-output-p
                               division-instruction-sequence)
           :do-not-induct t))
  :rule-classes nil)

(defun division-scaled-divisor-word (from-top world)
  (proof-load-word (+ (proof-world-reg 20 world) (proof-world-reg 22 world) (- from-top))
                   (proof-world-machine world)))

(local
 (defthm division-scaled-divisor-word-fits
   (unsigned-byte-p 64 (division-scaled-divisor-word from-top world))
   :hints (("Goal"
            :use (:instance division-read-bytes-value-range
                            (count 8)
                            (address (+ (proof-world-reg 20 world) (proof-world-reg 22 world) (- from-top)))
                            (memory (boymoo-model::a64-memory (proof-world-machine world))))
            :in-theory (enable proof-load-word)))
   :rule-classes nil))

(defun division-scale-window-setup-inputs-p (world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 20 (proof-world-pc world)))
       (<= 16 (proof-world-reg 22 world))
       (<= (proof-world-reg 22 world) (proof-world-reg 9 world))
       (proof-span-p (proof-world-reg 20 world) (proof-world-reg 22 world))))

(defun division-scale-window-setup-output-p (world after)
  (and (equal (proof-world-reg 11 after) (division-scaled-divisor-word 8 world))
       (equal (proof-world-reg 12 after) (division-scaled-divisor-word 16 world))
       (equal (proof-world-reg 13 after) (- (proof-world-reg 9 world) (proof-world-reg 22 world)))
       (equal (proof-world-pc after) (+ 20 (proof-world-pc world)))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
       (division-ordinary-world-p after)
       (division-scale-scratch-frame-p world after)))

(local
 (defthm division-scale-window-setup-effects
   (implies (division-scale-window-setup-inputs-p world)
            (division-scale-window-setup-output-p
             world (division-instruction-sequence *division-scale-window-setup-instructions* world)))
   :hints (("Goal"
            :use ((:instance division-world-register-in-word (register 9))
                  (:instance division-world-register-in-word (register 22))
                  (:instance division-scaled-divisor-word-fits (from-top 8))
                  (:instance division-scaled-divisor-word-fits (from-top 16)))
            :do-not-induct t))
   :rule-classes nil))

(defthm division-scale-enters-first-window
  (let* ((cuts (list (+ 20 (proof-world-pc world))))
         (after (proof-advance 5 world)))
    (implies (and (division-scale-window-setup-inputs-p world)
                  (division-instruction-sequence-ready-p *division-scale-window-setup-instructions* cuts world))
             (and (proof-segment-p 5 cuts world :cut after)
                  (division-scale-window-setup-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-scale-window-setup-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-scale-window-setup-instructions*)
                            (cuts (list (+ 20 (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-scale-window-setup-instructions*)
                            (cuts (list (+ 20 (proof-world-pc world))))))
           :in-theory (disable division-scale-window-setup-inputs-p division-scale-window-setup-output-p
                               division-instruction-sequence)))
  :rule-classes nil)
