(in-package "BOYMOO-PROOFS")

(include-book "shift-machine")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-choose-normalization-instructions* (division-runtime-block "rt:z-divide" 18 7))
(defconst *division-undo-normalization-instructions* (division-runtime-block "rt:z-divide-store" 3 6))
(defconst *division-undo-to-normalize-offset*
  (- (division-runtime-offset "rt:z-divide-normalize") (+ 12 (division-runtime-offset "rt:z-divide-store"))))

(local
 (in-theory (disable floor mod ash proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-instruction-effect proof-segment-p division-instruction-sequence-ready-p
                     boymoo-model::a64-sp boymoo-model::a64-nzcv boymoo-model::a64-condition
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-unnormalized-leading-limb (world)
  (proof-load-word (+ 8 (proof-world-reg 1 world) (proof-world-reg 22 world))
                   (proof-world-machine world)))

(defun division-choose-normalization-inputs-p (world)
  (and (division-ordinary-world-p world)
       (<= 16 (proof-world-reg 22 world))
       (unsigned-byte-p 64 (+ 16 (proof-world-reg 0 world)))
       (unsigned-byte-p 64 (+ 16 (proof-world-reg 1 world)))
       (unsigned-byte-p 64 (+ 8 (proof-world-reg 1 world) (proof-world-reg 22 world)))
       (unsigned-byte-p 64 (+ 28 (proof-world-pc world)))
       (proof-span-p (boymoo-model::a64-sp (proof-world-machine world)) 16)
       (division-digit-p (division-unnormalized-leading-limb world))
       (posp (division-unnormalized-leading-limb world))))

(defun division-choose-normalization-output-p (world after)
  (let* ((shift (division-normalization-shift (division-unnormalized-leading-limb world)))
         (sp (boymoo-model::a64-sp (proof-world-machine world)))
         (machine (proof-world-machine after)))
    (and (equal (proof-world-reg 7 after) (+ 16 (proof-world-reg 0 world)))
         (equal (proof-world-reg 8 after) (+ 16 (proof-world-reg 1 world)))
         (equal (proof-world-reg 10 after) shift)
         (equal (proof-load-word sp machine) shift)
         (equal (proof-load-word (+ sp 8) machine) (proof-world-reg 9 world))
         (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (boymoo-model::a64-sp machine) sp)
         (equal (proof-world-pc after) (+ 28 (proof-world-pc world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(defthm division-chooses-and-saves-clz-shift-effects
  (implies (division-choose-normalization-inputs-p world)
           (division-choose-normalization-output-p
            world (division-instruction-sequence *division-choose-normalization-instructions* world)))
  :hints (("Goal"
           :use ((:instance division-clz-shift-bounds (leading (division-unnormalized-leading-limb world)))
                 (:instance division-world-register-in-word (register 9)))
           :in-theory (disable integer-length)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-chooses-and-saves-clz-shift
  (let* ((cuts (list (+ 28 (proof-world-pc world))))
         (after (proof-advance 7 world)))
    (implies (and (division-choose-normalization-inputs-p world)
                  (division-instruction-sequence-ready-p *division-choose-normalization-instructions* cuts world))
             (and (proof-segment-p 7 cuts world :cut after)
                  (division-choose-normalization-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-chooses-and-saves-clz-shift-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-choose-normalization-instructions*)
                            (cuts (list (+ 28 (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-choose-normalization-instructions*)
                            (cuts (list (+ 28 (proof-world-pc world))))))
           :in-theory (disable division-choose-normalization-inputs-p division-choose-normalization-output-p
                               division-instruction-sequence)))
  :rule-classes nil)

(defun division-saved-normalization-shift (world)
  (let ((machine (proof-world-machine world)))
    (proof-load-word (boymoo-model::a64-sp machine) machine)))

(defun division-saved-dividend-bytes (world)
  (let ((machine (proof-world-machine world)))
    (proof-load-word (+ 8 (boymoo-model::a64-sp machine)) machine)))

(defun division-undo-normalization-instructions (world)
  (take (if (equal (division-saved-normalization-shift world) 0) 4 6)
        *division-undo-normalization-instructions*))

(defun division-undo-normalization-target (world)
  (+ (proof-world-pc world)
     (if (equal (division-saved-normalization-shift world) 0)
         *division-undo-to-normalize-offset* 24)))

(defun division-undo-normalization-inputs-p (world)
  (let* ((shift (division-saved-normalization-shift world))
         (bytes (division-saved-dividend-bytes world))
         (divisor-bytes (proof-world-reg 22 world)))
    (and (division-ordinary-world-p world)
         (unsigned-byte-p 64 (+ *division-undo-to-normalize-offset* (proof-world-pc world)))
         (unsigned-byte-p 5 shift)
         (<= divisor-bytes bytes)
         (unsigned-byte-p 64 (+ 8 bytes)))))

(defun division-undo-normalization-output-p (world after)
  (let* ((shift (division-saved-normalization-shift world))
         (divisor-bytes (proof-world-reg 22 world)))
    (and (equal (proof-world-reg 9 after) (+ 8 (- (division-saved-dividend-bytes world) divisor-bytes)))
         (equal (proof-world-reg 10 after) shift)
         (implies (posp shift)
                  (and (equal (proof-world-reg 0 after) divisor-bytes)
                       (equal (proof-world-reg 1 after) 0)))
         (equal (proof-world-pc after) (division-undo-normalization-target world))
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) divisor-bytes)
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-memory (proof-world-machine world)))
         (equal (proof-world-stop after) (proof-world-stop world))
         (equal (proof-world-regions after) (proof-world-regions world)))))

(defthm division-undo-normalization-setup-effects
  (implies (division-undo-normalization-inputs-p world)
           (division-undo-normalization-output-p
            world (division-instruction-sequence (division-undo-normalization-instructions world) world)))
  :hints (("Goal" :cases ((equal (division-saved-normalization-shift world) 0))
                  :do-not '(generalize fertilize)
                  :do-not-induct t))
  :rule-classes nil)

(defthm division-undo-normalization-setup-runs
  (let* ((instructions (division-undo-normalization-instructions world))
         (steps (len instructions))
         (cuts (list (division-undo-normalization-target world)))
         (after (proof-advance steps world)))
    (implies (and (division-undo-normalization-inputs-p world)
                  (division-instruction-sequence-ready-p instructions cuts world))
             (and (proof-segment-p steps cuts world :cut after)
                  (division-undo-normalization-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-undo-normalization-setup-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions (division-undo-normalization-instructions world))
                            (cuts (list (division-undo-normalization-target world))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions (division-undo-normalization-instructions world))
                            (cuts (list (division-undo-normalization-target world)))))
           :in-theory (disable division-undo-normalization-output-p division-undo-normalization-inputs-p
                               division-undo-normalization-instructions division-undo-normalization-target
                               division-instruction-sequence)))
  :rule-classes nil)
