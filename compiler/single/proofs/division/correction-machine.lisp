(in-package "BOYMOO-PROOFS")

(include-book "limb-machine")
(include-book "linked")
(include-book "cutpoints")
(include-book "correction")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-subtract-limb-instructions*
  (division-runtime-block "rt:z-divide-subtract-limb" 0 14))

(defconst *division-add-back-limb-instructions*
  (division-runtime-block "rt:z-divide-add-back" 0 10))

(local
 (in-theory (disable ash floor mod acl2::binary-logand
                     proof-step proof-advance proof-world-pc proof-world-reg proof-world-machine
                     proof-world-stop proof-world-regions proof-instruction-effect proof-load-word
                     boymoo-model::a64-nzcv boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes boymoo-model::a64-shift boymoo-model::a64-condition
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-window-limb (base world)
  (proof-load-word (+ (proof-world-reg base world) (proof-world-reg 0 world))
                   (proof-world-machine world)))

(defun division-window-limb-layout-p (steps world)
  (let* ((offset (proof-world-reg 0 world))
         (divisor (+ (proof-world-reg 20 world) offset))
         (window (+ (proof-world-reg 14 world) offset)))
    (and (division-ordinary-world-p world)
         (unsigned-byte-p 64 (+ (* 4 steps) (proof-world-pc world)))
         (<= (+ offset 8) (proof-world-reg 22 world))
         (proof-span-p divisor 8)
         (proof-span-p window 8)
         (division-digit-p (division-window-limb 20 world))
         (division-digit-p (division-window-limb 14 world)))))

(defun division-window-limb-output-p (steps digit carry world after)
  (let* ((offset (proof-world-reg 0 world))
         (target (+ (proof-world-reg 14 world) offset)))
    (and (equal (proof-world-reg 0 after) (+ offset 8))
         (equal (proof-world-reg 1 after) carry)
         (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
         (equal (proof-world-reg 14 after) (proof-world-reg 14 world))
         (equal (proof-world-reg 15 after) (proof-world-reg 15 world))
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (proof-world-pc after)
                (if (< (+ offset 8) (proof-world-reg 22 world))
                    (proof-world-pc world)
                  (+ (* 4 steps) (proof-world-pc world))))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes
                 8 target digit (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(local
 (defthm division-subtract-limb-word-values
   (implies (and (division-digit-p digit) (division-digit-p divisor-digit)
                 (division-digit-p guess) (natp carry) (<= carry guess))
            (let* ((product (* guess divisor-digit))
                   (word (+ product carry))
                   (low (mod word *division-radix*))
                   (high (floor word *division-radix*))
                   (difference (boymoo-model::a64-unsigned 64 (- digit low)))
                   (borrow (if (< digit low) 1 0)))
              (and (unsigned-byte-p 64 product)
                   (unsigned-byte-p 64 word)
                   (division-digit-p low)
                   (division-digit-p high)
                   (equal (floor difference *division-word-half*) borrow)
                   (equal (logand difference #xffffffff)
                          (mv-nth 0 (division-subtract-digit digit divisor-digit guess carry)))
                   (division-digit-p (mv-nth 0 (division-subtract-digit digit divisor-digit guess carry)))
                   (division-digit-p (+ high borrow)))))
   :hints (("Goal"
            :use ((:instance division-subtract-product-word)
                  (:instance division-subtract-digit-correct)
                  (:instance division-mod-bounds (a (+ (* guess divisor-digit) carry)) (b *division-radix*))
                  (:instance division-limb-borrow-is-word-sign
                             (a digit) (b (mod (+ (* guess divisor-digit) carry) *division-radix*)))
                  (:instance division-limb-difference-mask
                             (a digit) (b (mod (+ (* guess divisor-digit) carry) *division-radix*))))
            :in-theory (disable division-digit-mask-value division-limb-difference-mask)))
   :rule-classes nil))

(defthm division-subtract-limb-effects
  (let ((guess (proof-world-reg 15 world))
        (carry (proof-world-reg 1 world))
        (digit (division-window-limb 14 world))
        (divisor (division-window-limb 20 world)))
    (implies (and (division-window-limb-layout-p 14 world)
                  (division-digit-p guess) (<= carry guess))
             (mv-let (written next)
               (division-subtract-digit digit divisor guess carry)
               (division-window-limb-output-p
                14 written next world
                (division-instruction-sequence *division-subtract-limb-instructions* world)))))
  :hints (("Goal"
           :use (:instance division-subtract-limb-word-values
                           (digit (division-window-limb 14 world))
                           (divisor-digit (division-window-limb 20 world))
                           (guess (proof-world-reg 15 world)) (carry (proof-world-reg 1 world)))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-add-back-limb-effects
  (let ((carry (proof-world-reg 1 world))
        (digit (division-window-limb 14 world))
        (divisor (division-window-limb 20 world)))
    (implies (and (division-window-limb-layout-p 10 world)
                  (<= carry 1))
             (mv-let (written next)
               (division-add-back-digit digit divisor carry)
               (division-window-limb-output-p
                10 written next world
                (division-instruction-sequence *division-add-back-limb-instructions* world)))))
  :hints (("Goal"
           :use (:instance division-add-back-digit-correct
                           (digit (division-window-limb 14 world))
                           (divisor-digit (division-window-limb 20 world))
                           (carry (proof-world-reg 1 world)))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-subtract-limb-runs
  (let* ((cuts (list (+ 56 (proof-world-pc world))))
         (guess (proof-world-reg 15 world))
         (carry (proof-world-reg 1 world)))
    (implies (and (division-window-limb-layout-p 14 world)
                  (division-digit-p guess) (<= carry guess)
                  (division-instruction-prefix-ready-p
                   *division-subtract-limb-instructions* cuts world))
             (mv-let (written next)
               (division-subtract-digit (division-window-limb 14 world)
                                        (division-window-limb 20 world) guess carry)
               (and (division-before-cuts-p 14 cuts world)
                    (division-window-limb-output-p 14 written next world (proof-advance 14 world))))))
  :hints (("Goal"
           :use ((:instance division-subtract-limb-effects)
                 (:instance division-instruction-prefix-advances
                            (instructions *division-subtract-limb-instructions*)
                            (cuts (list (+ 56 (proof-world-pc world))))))
           :in-theory (disable division-instruction-prefix-ready-p division-instruction-sequence
                               division-window-limb-output-p division-window-limb-layout-p
                               division-subtract-digit division-before-cuts-p)))
  :rule-classes nil)

(defthm division-add-back-limb-runs
  (let* ((cuts (list (+ 40 (proof-world-pc world))))
         (carry (proof-world-reg 1 world)))
    (implies (and (division-window-limb-layout-p 10 world)
                  (<= carry 1)
                  (division-instruction-prefix-ready-p
                   *division-add-back-limb-instructions* cuts world))
             (mv-let (written next)
               (division-add-back-digit (division-window-limb 14 world)
                                        (division-window-limb 20 world) carry)
               (and (division-before-cuts-p 10 cuts world)
                    (division-window-limb-output-p 10 written next world (proof-advance 10 world))))))
  :hints (("Goal"
           :use ((:instance division-add-back-limb-effects)
                 (:instance division-instruction-prefix-advances
                            (instructions *division-add-back-limb-instructions*)
                            (cuts (list (+ 40 (proof-world-pc world))))))
           :in-theory (disable division-instruction-prefix-ready-p division-instruction-sequence
                               division-window-limb-output-p division-window-limb-layout-p
                               division-add-back-digit division-before-cuts-p)))
  :rule-classes nil)
