(in-package "BOYMOO-PROOFS")

(include-book "divide-flow")
(include-book "window-memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod proof-step proof-advance proof-world-machine proof-world-reg proof-world-pc
                     proof-world-stop proof-world-regions proof-load-word proof-instructions-at-p
                     proof-segment-p division-instruction-sequence-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-sp boymoo-model::a64-write-bytes)))

(defun division-one-path-layout-p (digits b world)
  (let* ((source (+ 16 (proof-world-reg 0 world)))
         (target (proof-world-reg 21 world))
         (remainder (proof-world-reg 19 world))
         (pc (proof-world-pc world))
         (bytes (* 8 (len digits)))
         (regions (proof-world-regions world)))
    (and (consp digits) (division-digits-p digits)
         (division-one-setup-inputs-p world)
         (not (proof-world-stop world))
         (equal (proof-world-reg 9 world) bytes)
         (equal (proof-world-reg 22 world) 8)
         (equal b (proof-load-word (+ 16 (proof-world-reg 1 world)) (proof-world-machine world)))
         (equal (division-read-limbs (len digits) source (proof-world-machine world)) digits)
         (proof-span-p source bytes)
         (proof-span-p target bytes)
         (proof-span-p remainder 8)
         (proof-covered-p source bytes :read regions)
         (proof-covered-p target bytes :write regions)
         (proof-covered-p (+ 16 (proof-world-reg 1 world)) 8 :read regions)
         (proof-disjoint-p target (+ target bytes) source (+ source bytes))
         (proof-disjoint-p target (+ target bytes) remainder (+ remainder 8))
         (proof-disjoint-p target (+ target bytes) (+ pc 16) (+ pc 44))
         (unsigned-byte-p 64 (+ pc 44))
         (proof-instructions-at-p *division-one-setup-instructions* pc world)
         (proof-instructions-at-p *division-one-limb-instructions* (+ pc 16) world))))

(defun division-one-path-loop-end (digits world)
  (proof-advance (* 7 (len digits)) (proof-advance 4 world)))

(defun division-one-path-steps (digits)
  (+ 6 (* 7 (len digits))))

(local
 (defthm division-one-path-sets-loop-inputs
   (implies (division-one-path-layout-p digits b world)
            (and (division-one-limb-prefix-layout-p digits 0 (proof-advance 4 world))
                 (equal (proof-world-reg 3 (proof-advance 4 world)) b)
                 (division-one-setup-output-p world (proof-advance 4 world))))
   :hints (("Goal"
            :use ((:instance division-divide-one-setup-runs)
                  (:instance division-instructions-placement-preserved
                             (instructions *division-one-limb-instructions*)
                             (address (+ 16 (proof-world-pc world)))
                             (before world) (after (proof-advance 4 world)))
                  (:instance division-read-limbs-from-same-memory
                             (count (len digits)) (address (+ 16 (proof-world-reg 0 world)))
                             (first (proof-world-machine world))
                             (second (proof-world-machine (proof-advance 4 world)))))
            :in-theory (disable division-read-limbs proof-covered-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defun division-one-path-remainder-ready-p (digits world)
  (let* ((middle (division-one-path-loop-end digits world))
         (cut (+ *division-one-remainder-target-offset* (proof-world-pc middle))))
    (and (division-one-remainder-inputs-p middle)
         (division-instruction-sequence-ready-p *division-one-remainder-instructions* (list cut) middle))))

(local
 (defthm division-one-path-runs-remainder-store
   (implies (division-one-path-remainder-ready-p digits world)
            (division-one-remainder-output-p
             (division-one-path-loop-end digits world)
             (proof-advance (division-one-path-steps digits) world)))
   :hints (("Goal"
            :use ((:instance division-divide-one-remainder-runs (world (division-one-path-loop-end digits world)))
                  (:instance proof-advance-append
                             (prefix 4) (suffix (* 7 (len digits))))
                  (:instance proof-advance-append
                             (prefix (+ 4 (* 7 (len digits)))) (suffix 2)))
            :in-theory (disable proof-advance-append division-one-remainder-output-p
                                division-one-remainder-inputs-p)
            :do-not-induct t))
   :rule-classes nil))

(defun division-one-path-output-p (digits divisor world after)
  (let* ((machine (proof-world-machine after))
         (input (division-magnitude digits))
         (q-limbs (division-read-limbs (len digits) (proof-world-reg 21 world) machine))
         (remainder (proof-load-word (proof-world-reg 19 world) machine)))
    (and (division-digits-p q-limbs)
         (division-digit-p remainder)
         (equal (division-magnitude q-limbs) (floor input divisor))
         (equal remainder (mod input divisor))
         (equal (proof-world-pc after)
                (+ (proof-world-pc world) 44 *division-one-remainder-target-offset*))
         (equal (proof-world-reg 9 after) (* 8 (len digits)))
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) 8)
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (boymoo-model::a64-sp machine) (boymoo-model::a64-sp (proof-world-machine world)))
         (not (proof-world-stop after)))))

(defthm division-divide-one-writes-quotient-and-remainder
  (implies (and (division-one-path-layout-p digits divisor world)
                (division-one-path-remainder-ready-p digits world))
           (division-one-path-output-p digits divisor world
                                       (proof-advance (division-one-path-steps digits) world)))
  :hints (("Goal"
           :use ((:instance division-one-path-sets-loop-inputs (b divisor))
                 (:instance division-one-limb-loop-from-layout (world (proof-advance 4 world)))
                 (:instance division-one-path-runs-remainder-store)
                 (:instance division-mod-bounds (a (division-magnitude digits)) (b divisor))
                 (:instance division-limbs-after-disjoint-word-write
                            (count (len digits)) (address (proof-world-reg 21 world))
                            (target (proof-world-reg 19 world))
                            (value (proof-world-reg 5 (division-one-path-loop-end digits world)))
                            (before (proof-world-machine (division-one-path-loop-end digits world)))
                            (after (proof-world-machine (proof-advance (division-one-path-steps digits) world)))))
           :in-theory (disable division-one-limb-prefix-layout-p division-one-path-remainder-ready-p
                               division-read-limbs division-magnitude division-write-quotient-limbs
                               proof-covered-p)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
