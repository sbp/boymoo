(in-package "BOYMOO-PROOFS")

(include-book "effects")
(include-book "linked")
(include-book "cutpoints")
(include-book "one-limb-loop")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-divide-entry-instructions* (division-runtime-block "rt:z-divide" 0 18))
(defconst *division-divide-short-offset*
  (- (division-runtime-offset "rt:z-divide-short") (division-runtime-offset "rt:z-divide")))
(defconst *division-divide-one-offset*
  (- (division-runtime-offset "rt:z-divide-one") (division-runtime-offset "rt:z-divide")))
(defconst *division-one-setup-instructions* (division-runtime-block "rt:z-divide-one" 0 4))
(defconst *division-one-remainder-instructions* (division-runtime-block "rt:z-divide-one" 11 2))
(defconst *division-one-remainder-target-offset*
  (- (division-runtime-offset "rt:z-divide-normalize")
     (+ 44 (division-runtime-offset "rt:z-divide-one"))))
(defconst *division-quotient-normalize-instructions*
  (division-runtime-block "rt:z-divide-normalize" 0 4))
(defconst *division-remainder-normalize-instructions*
  (division-runtime-block "rt:z-divide-normalize" 4 4))
(defconst *division-divide-restore-instructions* (division-runtime-block "rt:z-divide-normalize" 8 5))
(defconst *division-quotient-normalize-target-offset*
  (- (division-runtime-offset "rt:z-normalize") (division-runtime-offset "rt:z-divide-normalize")))

(local
 (in-theory (disable ash floor mod acl2::binary-logand acl2::binary-logior
                     proof-step proof-advance proof-world-pc proof-world-reg proof-world-machine
                     proof-world-stop proof-world-regions proof-instruction-effect proof-load-word
                     boymoo-model::a64-nzcv boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes boymoo-model::a64-shift boymoo-model::a64-condition
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-divide-dispatch-offset (a-count b-count)
  (cond ((< a-count b-count) *division-divide-short-offset*)
        ((equal b-count 1) *division-divide-one-offset*)
        (t 72)))

(defun division-divide-dispatch-instructions (a-count b-count)
  (take (cond ((< a-count b-count) 15)
              ((equal b-count 1) 17)
              (t 18))
        *division-divide-entry-instructions*))

(defun division-divide-saved-registers-p (entry world)
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine)))
    (and (equal sp (- (boymoo-model::a64-sp (proof-world-machine entry)) 64))
         (equal (proof-load-word (+ sp 48) machine) (proof-world-reg 19 entry))
         (equal (proof-load-word (+ sp 56) machine) (proof-world-reg 20 entry))
         (equal (proof-load-word (+ sp 32) machine) (proof-world-reg 21 entry))
         (equal (proof-load-word (+ sp 40) machine) (proof-world-reg 22 entry))
         (equal (proof-load-word (+ sp 16) machine) (proof-world-reg 29 entry))
         (equal (proof-load-word (+ sp 24) machine) (proof-world-reg 30 entry)))))

(defun division-divide-entry-inputs-p (a-count b-count world)
  (let* ((pc (proof-world-pc world))
         (machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (a (proof-world-reg 0 world))
         (b (proof-world-reg 1 world)))
    (and (division-ordinary-world-p world)
         (natp a-count) (posp b-count)
         (< a-count (expt 2 29)) (< b-count (expt 2 29))
         (unsigned-byte-p 64
                          (+ pc (max 72 (max *division-divide-short-offset* *division-divide-one-offset*))))
         (<= 64 sp)
         (proof-span-p (- sp 48) 48)
         (proof-span-p a 8) (proof-span-p b 8)
         (proof-disjoint-p (- sp 48) sp a (+ a 8))
         (proof-disjoint-p (- sp 48) sp b (+ b 8))
         (unsigned-byte-p 64 (+ 16 (proof-world-reg 2 world)))
         (unsigned-byte-p 64 (+ 16 (proof-world-reg 3 world)))
         (equal (proof-load-word a machine) (+ 3 (* 2048 (1+ a-count))))
         (equal (proof-load-word b machine) (+ 3 (* 2048 (1+ b-count)))))))

(defun division-divide-dispatch-output-p (a-count b-count world after)
  (and (equal (proof-world-pc after) (+ (proof-world-pc world)
                                        (division-divide-dispatch-offset a-count b-count)))
       (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
       (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
       (equal (proof-world-reg 2 after) (proof-world-reg 2 world))
       (equal (proof-world-reg 3 after) (proof-world-reg 3 world))
       (equal (proof-world-reg 9 after) (* 8 a-count))
       (equal (proof-world-reg 19 after) (+ 16 (proof-world-reg 3 world)))
       (equal (proof-world-reg 20 after) (proof-world-reg 4 world))
       (equal (proof-world-reg 21 after) (+ 16 (proof-world-reg 2 world)))
       (equal (proof-world-reg 22 after) (* 8 b-count))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
       (equal (proof-world-regions after) (proof-world-regions world))
       (equal (proof-world-stop after) (proof-world-stop world))
       (division-ordinary-world-p after)
       (division-divide-saved-registers-p world after)))

(defthm division-divide-dispatch-effects
  (implies (division-divide-entry-inputs-p a-count b-count world)
           (division-divide-dispatch-output-p
            a-count b-count world
            (division-instruction-sequence (division-divide-dispatch-instructions a-count b-count) world)))
  :hints (("Goal"
           :cases ((< a-count b-count) (equal b-count 1))
           :use ((:instance division-view-header-byte-count (count a-count))
                 (:instance division-view-header-byte-count (count b-count)))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-divide-dispatch-runs
  (let* ((instructions (division-divide-dispatch-instructions a-count b-count))
         (cuts (list (+ (proof-world-pc world) (division-divide-dispatch-offset a-count b-count))))
         (steps (len instructions))
         (after (proof-advance steps world)))
    (implies (and (division-divide-entry-inputs-p a-count b-count world)
                  (division-instruction-sequence-ready-p instructions cuts world))
             (and (proof-segment-p steps cuts world :cut after)
                  (division-divide-dispatch-output-p a-count b-count world after))))
  :hints (("Goal"
           :use ((:instance division-divide-dispatch-effects)
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions (division-divide-dispatch-instructions a-count b-count))
                            (cuts (list (+ (proof-world-pc world)
                                           (division-divide-dispatch-offset a-count b-count)))))
                 (:instance division-instruction-sequence-advances
                            (instructions (division-divide-dispatch-instructions a-count b-count))
                            (cuts (list (+ (proof-world-pc world)
                                           (division-divide-dispatch-offset a-count b-count))))))
           :in-theory (disable division-divide-entry-inputs-p division-divide-dispatch-output-p
                               division-instruction-sequence division-instruction-sequence-ready-p
                               division-divide-dispatch-offset division-divide-dispatch-instructions
                               proof-segment-p)))
  :rule-classes nil)

(defun division-one-setup-inputs-p (world)
  (let* ((machine (proof-world-machine world))
         (b-limb (+ 16 (proof-world-reg 1 world)))
         (divisor (proof-load-word b-limb machine)))
    (and (division-ordinary-world-p world)
         (unsigned-byte-p 64 (+ 16 (proof-world-pc world)))
         (unsigned-byte-p 64 (+ 16 (proof-world-reg 0 world)))
         (proof-span-p b-limb 8)
         (division-digit-p divisor)
         (posp divisor))))

(defun division-one-setup-output-p (world after)
  (let ((machine (proof-world-machine world)))
    (and (equal (proof-world-reg 3 after) (proof-load-word (+ 16 (proof-world-reg 1 world)) machine))
         (equal (proof-world-reg 0 after) (+ 16 (proof-world-reg 0 world)))
         (equal (proof-world-reg 4 after) (proof-world-reg 9 world))
         (equal (proof-world-reg 5 after) 0)
         (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (proof-world-pc after) (+ 16 (proof-world-pc world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after)) (boymoo-model::a64-memory machine))
         (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(defthm division-divide-one-setup-effects
  (implies (division-one-setup-inputs-p world)
           (division-one-setup-output-p
            world (division-instruction-sequence *division-one-setup-instructions* world)))
  :hints (("Goal" :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-one-setup-ready-from-code
   (let* ((pc (proof-world-pc world))
          (b-limb (+ 16 (proof-world-reg 1 world))))
     (implies (and (not (proof-world-stop world))
                   (division-one-setup-inputs-p world)
                   (proof-instructions-at-p *division-one-setup-instructions* pc world)
                   (proof-covered-p b-limb 8 :read (proof-world-regions world)))
              (division-instruction-sequence-ready-p
               *division-one-setup-instructions* (list (+ 16 pc)) world)))
   :hints (("Goal"
            :in-theory (e/d (division-instruction-at-depends-on-bytes)
                            (proof-instruction-at-p division-decoded-word-at-p proof-covered-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm division-divide-one-setup-runs
  (let* ((pc (proof-world-pc world))
         (cuts (list (+ 16 pc)))
         (b-limb (+ 16 (proof-world-reg 1 world)))
         (after (proof-advance 4 world)))
    (implies (and (not (proof-world-stop world))
                  (division-one-setup-inputs-p world)
                  (proof-instructions-at-p *division-one-setup-instructions* pc world)
                  (proof-covered-p b-limb 8 :read (proof-world-regions world)))
             (and (proof-segment-p 4 cuts world :cut after)
                  (division-one-setup-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-one-setup-ready-from-code)
                 (:instance division-divide-one-setup-effects)
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-one-setup-instructions*)
                            (cuts (list (+ 16 (proof-world-pc world)))))
                 (:instance division-instruction-sequence-advances
                            (instructions *division-one-setup-instructions*)
                            (cuts (list (+ 16 (proof-world-pc world))))))
           :in-theory (disable division-one-setup-inputs-p division-one-setup-output-p
                               division-instruction-sequence division-instruction-sequence-ready-p
                               proof-instructions-at-p proof-covered-p proof-segment-p)))
  :rule-classes nil)

(defun division-one-remainder-inputs-p (world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ *division-one-remainder-target-offset* (proof-world-pc world)))
       (proof-span-p (proof-world-reg 19 world) 8)))

(defun division-one-remainder-output-p (world after)
  (let* ((address (proof-world-reg 19 world))
         (remainder (proof-world-reg 5 world)))
    (and (equal (proof-world-pc after) (+ *division-one-remainder-target-offset* (proof-world-pc world)))
         (equal (proof-load-word address (proof-world-machine after)) remainder)
         (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
         (equal (proof-world-reg 19 after) address)
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes
                 8 address remainder (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(defthm division-divide-one-remainder-effects
  (implies (division-one-remainder-inputs-p world)
           (division-one-remainder-output-p
            world (division-instruction-sequence *division-one-remainder-instructions* world)))
  :hints (("Goal"
           :use (:instance division-world-register-in-word (register 5))
           :do-not-induct t))
  :rule-classes nil)

(defthm division-divide-one-remainder-runs
  (let* ((cut (+ *division-one-remainder-target-offset* (proof-world-pc world)))
         (after (proof-advance 2 world)))
    (implies (and (division-one-remainder-inputs-p world)
                  (division-instruction-sequence-ready-p
                   *division-one-remainder-instructions* (list cut) world))
             (and (proof-segment-p 2 (list cut) world :cut after)
                  (division-one-remainder-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-divide-one-remainder-effects)
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-one-remainder-instructions*)
                            (cuts (list (+ *division-one-remainder-target-offset* (proof-world-pc world)))))
                 (:instance division-instruction-sequence-advances
                            (instructions *division-one-remainder-instructions*)
                            (cuts (list (+ *division-one-remainder-target-offset* (proof-world-pc world))))))
           :in-theory (disable division-one-remainder-inputs-p division-one-remainder-output-p
                               division-instruction-sequence division-instruction-sequence-ready-p proof-segment-p)))
  :rule-classes nil)

(defun division-normalize-instructions (remainder)
  (if remainder *division-remainder-normalize-instructions*
    *division-quotient-normalize-instructions*))

(defun division-normalize-target (remainder world)
  (+ (proof-world-pc world) *division-quotient-normalize-target-offset*
     (if remainder -16 0)))

(defun division-normalization-address (remainder world)
  (- (proof-world-reg (if remainder 19 21) world) 16))

(defun division-normalization-bytes (remainder world)
  (proof-world-reg (if remainder 22 9) world))

(defun division-normalize-setup-p (remainder count world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 16 (proof-world-pc world)))
       (unsigned-byte-p 64 (division-normalize-target remainder world))
       (unsigned-byte-p 64 (division-normalization-address remainder world))
       (natp count)
       (equal (division-normalization-bytes remainder world) (* 8 count))))

(defun division-normalize-arguments-p (address digits world)
  (and (equal (proof-world-reg 0 world) address)
       (equal (proof-world-reg 1 world) (len digits))
       (equal (proof-world-reg 2 world) 0)
       (division-digits-p digits)
       (equal (division-read-limbs (len digits) (+ 16 address) (proof-world-machine world))
              digits)))

(defun division-unsigned-normalize-return-p (digits entered returned)
  (let ((address (proof-world-reg 0 entered)))
    (and (division-normalize-arguments-p address digits entered)
         (proof-frame-return-p '(1 2 3 4) nil entered returned)
         (equal (proof-world-regions returned) (proof-world-regions entered))
         (proof-integer-view-p (division-magnitude digits) address
                               (len (division-trim-limbs digits)) returned))))

(defun division-normalize-setup-output-p (remainder count world after)
  (and (equal (proof-world-reg 0 after) (division-normalization-address remainder world))
       (equal (proof-world-reg 1 after) count)
       (equal (proof-world-reg 2 after) 0)
       (equal (proof-world-pc after) (division-normalize-target remainder world))
       (equal (proof-world-reg 30 after) (+ 16 (proof-world-pc world)))
       (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine world)))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (proof-world-regions after) (proof-world-regions world))
       (equal (proof-world-stop after) (proof-world-stop world))
       (division-ordinary-world-p after)))

(defthm division-divide-normalize-call-effects
  (implies (division-normalize-setup-p remainder count world)
           (division-normalize-setup-output-p
            remainder count world
            (division-instruction-sequence (division-normalize-instructions remainder) world)))
  :hints (("Goal"
           :cases (remainder)
           :use ((:instance division-quotient-unique (a (* 8 count)) (b 8) (q count) (r 0)))
           :do-not-induct t))
  :rule-classes nil)

(defthm division-divide-normalize-call-runs
  (let* ((instructions (division-normalize-instructions remainder))
         (cuts (list (division-normalize-target remainder world)))
         (after (proof-advance 4 world)))
    (implies (and (division-normalize-setup-p remainder count world)
                  (division-instruction-sequence-ready-p instructions cuts world))
             (and (proof-segment-p 4 cuts world :cut after)
                  (division-normalize-setup-output-p remainder count world after))))
  :hints (("Goal"
           :use ((:instance division-divide-normalize-call-effects)
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions (division-normalize-instructions remainder))
                            (cuts (list (division-normalize-target remainder world))))
                 (:instance division-instruction-sequence-advances
                            (instructions (division-normalize-instructions remainder))
                            (cuts (list (division-normalize-target remainder world)))))
           :in-theory (disable division-normalize-setup-p division-normalize-setup-output-p
                               division-instruction-sequence division-instruction-sequence-ready-p
                               proof-segment-p)))
  :rule-classes nil)

(defun division-restore-output-p (entry world after)
  (and (equal (proof-world-pc after) (proof-world-reg 30 entry))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine entry)))
       (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 entry))
       (equal (proof-world-reg 20 after) (proof-world-reg 20 entry))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 entry))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 entry))
       (equal (proof-world-reg 29 after) (proof-world-reg 29 entry))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 entry))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (proof-world-regions after) (proof-world-regions world))
       (equal (proof-world-stop after) (proof-world-stop world))))

(defthm division-divide-restore-effects
  (implies (and (division-divide-saved-registers-p entry world)
                (division-ordinary-world-p world)
                (<= 64 (boymoo-model::a64-sp (proof-world-machine entry))))
           (division-restore-output-p
            entry world (division-instruction-sequence *division-divide-restore-instructions* world)))
  :hints (("Goal"
           :use ((:instance division-world-sp-in-word (world entry))
                 (:instance division-world-register-in-word (world entry) (register 19))
                 (:instance division-world-register-in-word (world entry) (register 20))
                 (:instance division-world-register-in-word (world entry) (register 21))
                 (:instance division-world-register-in-word (world entry) (register 22))
                 (:instance division-world-register-in-word (world entry) (register 29))
                 (:instance division-world-register-in-word (world entry) (register 30)))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-divide-restore-runs
  (let* ((cuts (list (proof-world-reg 30 entry)))
         (after (proof-advance 5 world)))
    (implies (and (division-divide-saved-registers-p entry world)
                  (division-ordinary-world-p world)
                  (<= 64 (boymoo-model::a64-sp (proof-world-machine entry)))
                  (division-instruction-sequence-ready-p *division-divide-restore-instructions* cuts world))
             (and (proof-segment-p 5 cuts world :cut after)
                  (division-restore-output-p entry world after))))
  :hints (("Goal"
           :use ((:instance division-divide-restore-effects)
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-divide-restore-instructions*)
                            (cuts (list (proof-world-reg 30 entry))))
                 (:instance division-instruction-sequence-advances
                            (instructions *division-divide-restore-instructions*)
                            (cuts (list (proof-world-reg 30 entry)))))
           :in-theory (disable division-divide-saved-registers-p division-restore-output-p
                               division-instruction-sequence division-instruction-sequence-ready-p
                               proof-segment-p)))
  :rule-classes nil)
