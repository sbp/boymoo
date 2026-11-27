(in-package "BOYMOO-PROOFS")

(include-book "limb-machine")
(include-book "linked")
(include-book "cutpoints")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-left-shift-limb-instructions*
  (division-runtime-block "rt:z-divide-shift-limb" 0 9))

(defconst *division-right-shift-limb-instructions*
  (division-runtime-block "rt:z-divide-shift-right" 0 8))

(local
 (in-theory (disable ash floor mod expt acl2::binary-logand acl2::binary-logior
                     proof-step proof-advance proof-world-pc proof-world-reg proof-world-machine
                     proof-world-stop proof-world-regions proof-instruction-effect proof-load-word
                     boymoo-model::a64-nzcv boymoo-model::a64-memory boymoo-model::a64-write-bytes boymoo-model::a64-sp
                     boymoo-model::a64-shift boymoo-model::a64-condition boymoo-model::a64-unsigned
                     division-a64-unsigned-is-remainder)))

(defun division-left-shift-limb-inputs-p (world)
  (let* ((offset (proof-world-reg 4 world))
         (shift (proof-world-reg 3 world))
         (source (+ (proof-world-reg 0 world) offset))
         (target (+ (proof-world-reg 1 world) offset)))
    (and (division-ordinary-world-p world)
         (unsigned-byte-p 64 (+ 36 (proof-world-pc world)))
         (<= (+ offset 8) (proof-world-reg 2 world))
         (< shift 32)
         (unsigned-byte-p shift (proof-world-reg 6 world))
         (proof-span-p source 8)
         (proof-span-p target 8)
         (division-digit-p (proof-load-word source (proof-world-machine world))))))

(defun division-left-shift-frame-p (world after)
  (and (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
       (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
       (equal (proof-world-reg 2 after) (proof-world-reg 2 world))
       (equal (proof-world-reg 3 after) (proof-world-reg 3 world))
       (equal (proof-world-reg 7 after) (proof-world-reg 7 world))
       (equal (proof-world-reg 8 after) (proof-world-reg 8 world))
       (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
       (equal (proof-world-reg 10 after) (proof-world-reg 10 world))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
       (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine world)))
       (equal (proof-world-regions after) (proof-world-regions world))
       (equal (proof-world-stop after) (proof-world-stop world))))

(defun division-left-shift-limb-output-p (world after)
  (let* ((offset (proof-world-reg 4 world))
         (source (+ (proof-world-reg 0 world) offset))
         (target (+ (proof-world-reg 1 world) offset))
         (digit (proof-load-word source (proof-world-machine world)))
         (shift (proof-world-reg 3 world)))
    (mv-let (written carry)
      (division-left-shift-digit digit (proof-world-reg 6 world) (expt 2 shift))
      (and (equal (proof-world-reg 4 after) (+ offset 8))
           (equal (proof-world-reg 5 after) written)
           (equal (proof-world-reg 6 after) carry)
           (division-left-shift-frame-p world after)
           (equal (proof-world-pc after)
                  (if (< (+ offset 8) (proof-world-reg 2 world))
                      (proof-world-pc world)
                    (+ 36 (proof-world-pc world))))
           (equal (boymoo-model::a64-memory (proof-world-machine after))
                  (boymoo-model::a64-write-bytes
                   8 target written (boymoo-model::a64-memory (proof-world-machine world))))
           (division-ordinary-world-p after)))))

(local
 (defthm division-left-shift-limb-word-values
   (implies (and (division-digit-p digit) (natp shift) (< shift 32)
                 (unsigned-byte-p shift carry))
            (let* ((scale (expt 2 shift))
                   (shifted (* digit scale))
                   (word (+ shifted carry)))
              (and (equal (logior shifted carry) word)
                   (unsigned-byte-p 64 shifted)
                   (unsigned-byte-p 64 word)
                   (division-digit-p (floor word *division-radix*))
                   (division-digit-p (mod word *division-radix*)))))
   :hints (("Goal"
            :use ((:instance division-limb-scale-fits)
                  (:instance division-left-shift-digit-correct (scale (expt 2 shift)))
                  (:instance division-logior-of-disjoint-fields
                             (width shift) (low carry) (high digit)))))
   :rule-classes nil))

(defthm division-left-shift-limb-effects
  (implies (division-left-shift-limb-inputs-p world)
           (division-left-shift-limb-output-p
            world (division-instruction-sequence *division-left-shift-limb-instructions* world)))
  :hints (("Goal"
           :use (:instance division-left-shift-limb-word-values
                           (digit (proof-load-word (+ (proof-world-reg 0 world) (proof-world-reg 4 world))
                                                   (proof-world-machine world)))
                           (shift (proof-world-reg 3 world)) (carry (proof-world-reg 6 world)))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-left-shift-limb-runs
  (let* ((cuts (list (+ 36 (proof-world-pc world))))
         (after (proof-advance 9 world)))
    (implies (and (division-left-shift-limb-inputs-p world)
                  (division-instruction-prefix-ready-p
                   *division-left-shift-limb-instructions* cuts world))
             (and (division-before-cuts-p 9 cuts world)
                  (division-left-shift-limb-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-left-shift-limb-effects)
                 (:instance division-instruction-prefix-advances
                            (instructions *division-left-shift-limb-instructions*)
                            (cuts (list (+ 36 (proof-world-pc world))))))
           :in-theory (disable division-instruction-sequence division-instruction-prefix-ready-p
                               division-left-shift-limb-inputs-p division-left-shift-limb-output-p
                               division-before-cuts-p)))
  :rule-classes nil)

(defun division-right-shift-offset (world)
  (- (proof-world-reg 0 world) 8))

(defun division-right-shift-limb-inputs-p (world)
  (let* ((offset (division-right-shift-offset world))
         (address (+ (proof-world-reg 19 world) offset))
         (machine (proof-world-machine world)))
    (and (division-ordinary-world-p world)
         (unsigned-byte-p 64 (+ 32 (proof-world-pc world)))
         (natp offset)
         (proof-span-p address 8)
         (< (proof-world-reg 10 world) 32)
         (division-digit-p (proof-world-reg 1 world))
         (division-digit-p (proof-load-word address machine)))))

(defun division-right-shift-limb-output-p (world after)
  (let* ((offset (division-right-shift-offset world))
         (address (+ (proof-world-reg 19 world) offset))
         (machine (proof-world-machine world))
         (digit (proof-load-word address machine))
         (upper (proof-world-reg 1 world))
         (shift (proof-world-reg 10 world))
         (written (mod (floor (+ digit (* *division-radix* upper)) (expt 2 shift))
                       *division-radix*)))
    (and (equal (proof-world-reg 0 after) offset)
         (equal (proof-world-reg 1 after) digit)
         (equal (proof-world-reg 3 after) written)
         (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
         (equal (proof-world-reg 10 after) shift)
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (proof-world-pc after)
                (if (equal offset 0) (+ 32 (proof-world-pc world)) (proof-world-pc world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes 8 address written (boymoo-model::a64-memory machine)))
         (equal (boymoo-model::a64-sp (proof-world-machine after)) (boymoo-model::a64-sp machine))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(defthm division-right-shift-limb-effects
  (implies (division-right-shift-limb-inputs-p world)
           (division-right-shift-limb-output-p
            world (division-instruction-sequence *division-right-shift-limb-instructions* world)))
  :hints (("Goal"
           :use ((:instance division-limb-scale-fits (shift (proof-world-reg 10 world)))
                 (:instance division-mod-bounds
                            (a (floor (+ (proof-load-word (+ (proof-world-reg 19 world)
                                                             (- (proof-world-reg 0 world) 8))
                                                          (proof-world-machine world))
                                         (* *division-radix* (proof-world-reg 1 world)))
                                      (expt 2 (proof-world-reg 10 world))))
                            (b *division-radix*)))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-right-shift-limb-runs
  (let* ((cuts (list (+ 32 (proof-world-pc world))))
         (after (proof-advance 8 world)))
    (implies (and (division-right-shift-limb-inputs-p world)
                  (division-instruction-prefix-ready-p
                   *division-right-shift-limb-instructions* cuts world))
             (and (division-before-cuts-p 8 cuts world)
                  (division-right-shift-limb-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-right-shift-limb-effects)
                 (:instance division-instruction-prefix-advances
                            (instructions *division-right-shift-limb-instructions*)
                            (cuts (list (+ 32 (proof-world-pc world))))))
           :in-theory (disable division-instruction-sequence division-instruction-prefix-ready-p
                               division-right-shift-limb-inputs-p division-right-shift-limb-output-p
                               division-before-cuts-p)))
  :rule-classes nil)
