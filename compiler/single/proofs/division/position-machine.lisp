(in-package "BOYMOO-PROOFS")

(include-book "estimate-machine")
(include-book "correction-loops")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-position-instructions* (division-runtime-block "rt:z-divide-position" 0 13))
(defconst *division-subtract-high-instructions*
  (division-runtime-block "rt:z-divide-subtract-limb" 14 5))
(defconst *division-add-back-setup-instructions*
  (division-runtime-block "rt:z-divide-subtract-limb" 19 3))
(defconst *division-add-back-high-instructions*
  (division-runtime-block "rt:z-divide-add-back" 10 4))
(defconst *division-store-position-instructions*
  (division-runtime-block "rt:z-divide-store" 0 3))
(defconst *division-subtract-high-to-store*
  (- (division-runtime-offset "rt:z-divide-store")
     (+ 56 (division-runtime-offset "rt:z-divide-subtract-limb"))))
(defconst *division-store-to-position*
  (- (division-runtime-offset "rt:z-divide-position") (division-runtime-offset "rt:z-divide-store")))

(local
 (in-theory (disable ash floor mod acl2::binary-logand acl2::binary-logior
                     proof-step proof-advance proof-world-pc proof-world-reg proof-world-machine
                     proof-world-stop proof-world-regions proof-instruction-effect proof-load-word
                     boymoo-model::a64-nzcv boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes boymoo-model::a64-shift boymoo-model::a64-condition
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-position-window (world)
  (+ (proof-world-reg 19 world) (proof-world-reg 13 world)))

(defun division-position-word (from-top world)
  (proof-load-word (+ (division-position-window world) (proof-world-reg 22 world) (- from-top))
                   (proof-world-machine world)))

(defun division-position-head (world)
  (+ (division-position-word 8 world) (* *division-radix* (division-position-word 0 world))))

(defun division-position-inputs-p (world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 52 (proof-world-pc world)))
       (<= 16 (proof-world-reg 22 world))
       (proof-span-p (division-position-window world) (+ 8 (proof-world-reg 22 world)))
       (division-leading-digit-p (proof-world-reg 11 world))
       (division-digit-p (proof-world-reg 12 world))
       (division-digit-p (division-position-word 0 world))
       (division-digit-p (division-position-word 8 world))
       (division-digit-p (division-position-word 16 world))))

(defun division-position-setup-output-p (world after)
  (let* ((head (division-position-head world))
         (lead (proof-world-reg 11 world))
         (guess (division-first-estimate head lead)))
    (and (equal (proof-world-reg 14 after) (division-position-window world))
         (equal (proof-world-reg 15 after) guess)
         (equal (proof-world-reg 16 after) (- head (* guess lead)))
         (equal (proof-world-reg 17 after) (division-position-word 16 world))
         (equal (proof-world-reg 11 after) lead)
         (equal (proof-world-reg 12 after) (proof-world-reg 12 world))
         (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (proof-world-pc after) (+ 52 (proof-world-pc world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-memory (proof-world-machine world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(defthm division-position-setup-effects
  (implies (division-position-inputs-p world)
           (division-position-setup-output-p
            world (division-instruction-sequence *division-position-instructions* world)))
  :hints (("Goal"
           :use ((:instance division-two-limb-word-fits
                            (low (division-position-word 8 world)) (high (division-position-word 0 world)))
                 (:instance division-first-estimate-bounds
                            (head (division-position-head world)) (lead (proof-world-reg 11 world))))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-position-setup-runs
  (let* ((cuts (list (+ 52 (proof-world-pc world))))
         (after (proof-advance 13 world)))
    (implies (and (division-position-inputs-p world)
                  (division-instruction-sequence-ready-p *division-position-instructions* cuts world))
             (and (proof-segment-p 13 cuts world :cut after)
                  (division-position-setup-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-position-setup-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-position-instructions*)
                            (cuts (list (+ 52 (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-position-instructions*)
                            (cuts (list (+ 52 (proof-world-pc world))))))
           :in-theory (disable division-position-inputs-p division-position-setup-output-p
                               proof-segment-p division-instruction-sequence-ready-p
                               division-instruction-sequence)))
  :rule-classes nil)

(defun division-window-high-address (world)
  (+ (proof-world-reg 14 world) (proof-world-reg 22 world)))

(defun division-window-high-limb (world)
  (proof-load-word (division-window-high-address world) (proof-world-machine world)))

(defun division-subtract-high-target (world)
  (+ (proof-world-pc world)
     (if (< (division-window-high-limb world) (proof-world-reg 1 world))
         20 *division-subtract-high-to-store*)))

(defun division-subtract-high-inputs-p (world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ *division-subtract-high-to-store* (proof-world-pc world)))
       (proof-span-p (division-window-high-address world) 8)
       (division-digit-p (division-window-high-limb world))
       (division-digit-p (proof-world-reg 1 world))))

(defun division-window-high-output-p (digit target world after)
  (let ((address (division-window-high-address world)))
    (and (equal (proof-world-pc after) target)
         (equal (proof-load-word address (proof-world-machine after)) digit)
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes
                 8 address digit (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
         (equal (proof-world-reg 14 after) (proof-world-reg 14 world))
         (equal (proof-world-reg 15 after) (proof-world-reg 15 world))
         (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(defun division-subtracted-high-limb (world)
  (let ((high (division-window-high-limb world)) (carry (proof-world-reg 1 world)))
    (+ (- high carry) (if (< high carry) *division-radix* 0))))

(defthm division-subtract-high-effects
  (implies (division-subtract-high-inputs-p world)
           (division-window-high-output-p
            (division-subtracted-high-limb world) (division-subtract-high-target world) world
            (division-instruction-sequence *division-subtract-high-instructions* world)))
  :hints (("Goal"
           :cases ((< (division-window-high-limb world) (proof-world-reg 1 world)))
           :use (:instance division-limb-difference-mask
                           (a (division-window-high-limb world)) (b (proof-world-reg 1 world)))
           :in-theory (disable division-digit-mask-value division-limb-difference-mask)
           :do-not-induct t))
  :rule-classes nil)

(defun division-add-back-setup-output-p (world after)
  (and (equal (proof-world-pc after) (+ 12 (proof-world-pc world)))
       (equal (proof-world-reg 0 after) 0)
       (equal (proof-world-reg 1 after) 0)
       (equal (proof-world-reg 15 after) (1- (proof-world-reg 15 world)))
       (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
       (equal (proof-world-reg 14 after) (proof-world-reg 14 world))
       (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (proof-world-regions after) (proof-world-regions world))
       (equal (proof-world-stop after) (proof-world-stop world))
       (division-ordinary-world-p after)))

(defthm division-add-back-setup-effects
  (implies (and (division-ordinary-world-p world)
                (posp (proof-world-reg 15 world))
                (unsigned-byte-p 64 (+ 12 (proof-world-pc world))))
           (division-add-back-setup-output-p
            world (division-instruction-sequence *division-add-back-setup-instructions* world)))
  :hints (("Goal" :do-not-induct t))
  :rule-classes nil)

(defthm division-add-back-setup-runs
  (let* ((cuts (list (+ 12 (proof-world-pc world))))
         (after (proof-advance 3 world)))
    (implies (and (division-ordinary-world-p world)
                  (posp (proof-world-reg 15 world))
                  (unsigned-byte-p 64 (+ 12 (proof-world-pc world)))
                  (division-instruction-sequence-ready-p *division-add-back-setup-instructions* cuts world))
             (and (proof-segment-p 3 cuts world :cut after)
                  (division-add-back-setup-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-add-back-setup-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-add-back-setup-instructions*)
                            (cuts (list (+ 12 (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-add-back-setup-instructions*)
                            (cuts (list (+ 12 (proof-world-pc world))))))
           :in-theory (disable division-add-back-setup-output-p proof-segment-p
                               division-instruction-sequence-ready-p division-instruction-sequence)))
  :rule-classes nil)

(defun division-add-back-high-inputs-p (world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 16 (proof-world-pc world)))
       (proof-span-p (division-window-high-address world) 8)
       (division-digit-p (division-window-high-limb world))
       (<= (proof-world-reg 1 world) 1)))

(defun division-added-back-high-limb (world)
  (mod (+ (division-window-high-limb world) (proof-world-reg 1 world)) *division-radix*))

(defthm division-add-back-high-effects
  (implies (division-add-back-high-inputs-p world)
           (division-window-high-output-p
            (division-added-back-high-limb world) (+ 16 (proof-world-pc world)) world
            (division-instruction-sequence *division-add-back-high-instructions* world)))
  :hints (("Goal"
           :use (:instance division-mod-bounds
                           (a (+ (division-window-high-limb world) (proof-world-reg 1 world)))
                           (b *division-radix*))
           :do-not-induct t))
  :rule-classes nil)

(defthm division-add-back-high-runs
  (let* ((cuts (list (+ 16 (proof-world-pc world))))
         (after (proof-advance 4 world)))
    (implies (and (division-add-back-high-inputs-p world)
                  (division-instruction-sequence-ready-p *division-add-back-high-instructions* cuts world))
             (and (proof-segment-p 4 cuts world :cut after)
                  (division-window-high-output-p
                   (division-added-back-high-limb world) (+ 16 (proof-world-pc world)) world after))))
  :hints (("Goal"
           :use ((:instance division-add-back-high-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-add-back-high-instructions*)
                            (cuts (list (+ 16 (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-add-back-high-instructions*)
                            (cuts (list (+ 16 (proof-world-pc world))))))
           :in-theory (disable division-add-back-high-inputs-p division-window-high-output-p
                               division-added-back-high-limb proof-segment-p
                               division-instruction-sequence-ready-p division-instruction-sequence)))
  :rule-classes nil)

(defun division-store-position-target (world)
  (+ (proof-world-pc world)
     (if (<= 8 (proof-world-reg 13 world)) *division-store-to-position* 12)))

(defun division-store-position-inputs-p (world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 12 (proof-world-pc world)))
       (unsigned-byte-p 64 (division-store-position-target world))
       (proof-span-p (+ (proof-world-reg 21 world) (proof-world-reg 13 world)) 8)
       (division-digit-p (proof-world-reg 15 world))))

(defun division-store-position-output-p (world after)
  (let* ((offset (proof-world-reg 13 world))
         (address (+ (proof-world-reg 21 world) offset))
         (quotient (proof-world-reg 15 world)))
    (and (equal (proof-world-pc after) (division-store-position-target world))
         (equal (proof-load-word address (proof-world-machine after)) quotient)
         (equal (proof-world-reg 13 after) (boymoo-model::a64-unsigned 64 (- offset 8)))
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes
                 8 address quotient (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(defthm division-store-position-effects
  (implies (division-store-position-inputs-p world)
           (division-store-position-output-p
            world (division-instruction-sequence *division-store-position-instructions* world)))
  :hints (("Goal" :do-not-induct t))
  :rule-classes nil)

(defthm division-store-position-runs
  (let* ((cuts (list (+ 12 (proof-world-pc world))))
         (after (proof-advance 3 world)))
    (implies (and (division-store-position-inputs-p world)
                  (division-instruction-prefix-ready-p *division-store-position-instructions* cuts world))
             (and (division-before-cuts-p 3 cuts world)
                  (division-store-position-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-store-position-effects)
                 (:instance division-instruction-prefix-advances
                            (instructions *division-store-position-instructions*)
                            (cuts (list (+ 12 (proof-world-pc world))))))
           :in-theory (disable division-store-position-inputs-p division-store-position-output-p
                               division-before-cuts-p division-instruction-prefix-ready-p
                               division-instruction-sequence)))
  :rule-classes nil)

(defthm division-subtract-high-runs
  (let* ((cuts (list (division-subtract-high-target world)))
         (after (proof-advance 5 world)))
    (implies (and (division-subtract-high-inputs-p world)
                  (division-instruction-sequence-ready-p *division-subtract-high-instructions* cuts world))
             (and (proof-segment-p 5 cuts world :cut after)
                  (division-window-high-output-p
                   (division-subtracted-high-limb world) (division-subtract-high-target world) world after))))
  :hints (("Goal"
           :use ((:instance division-subtract-high-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-subtract-high-instructions*)
                            (cuts (list (division-subtract-high-target world))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-subtract-high-instructions*)
                            (cuts (list (division-subtract-high-target world)))))
           :in-theory (disable division-subtract-high-inputs-p division-window-high-output-p
                               division-subtracted-high-limb division-subtract-high-target
                               proof-segment-p division-instruction-sequence-ready-p
                               division-instruction-sequence)))
  :rule-classes nil)
