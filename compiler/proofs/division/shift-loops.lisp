(in-package "BOYMOO-PROOFS")

(include-book "shift-machine")
(include-book "window-memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod ash proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-segment-p division-before-cuts-p division-instruction-prefix-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes boymoo-model::a64-sp
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defun division-left-shift-loop-ready-p (digits world)
  (if (atom digits)
      (null digits)
    (and (division-left-shift-loop-ready-p (cdr digits) (proof-advance 9 world))
         (division-left-shift-limb-inputs-p world)
         (division-instruction-prefix-ready-p
          *division-left-shift-limb-instructions* (list (+ 36 (proof-world-pc world))) world)
         (equal (proof-load-word (+ (proof-world-reg 0 world) (proof-world-reg 4 world))
                                 (proof-world-machine world))
                (car digits)))))

(local
 (defthm division-shift-advance-zero
   (equal (proof-advance 0 world) world)
   :hints (("Goal" :expand ((proof-advance 0 world))))))

(local
 (defthm division-shift-before-cuts-zero
   (division-before-cuts-p 0 cuts world)
   :hints (("Goal" :expand ((division-before-cuts-p 0 cuts world))))))

(local
 (defthm division-shift-nonempty-count-positive
   (implies (consp digits) (< 0 (len digits)))
   :hints (("Goal" :expand ((len digits))))
   :rule-classes :linear))

(defun division-left-shift-loop-output-p (digits world after)
  (let* ((offset (proof-world-reg 4 world))
         (target (+ (proof-world-reg 1 world) offset))
         (carry (proof-world-reg 6 world))
         (shift (proof-world-reg 3 world))
         (count (len digits)))
    (mv-let (written upper)
      (division-left-shift-limbs digits carry (expt 2 shift))
      (and (equal (proof-world-reg 4 after) (+ offset (* 8 count)))
           (equal (proof-world-reg 6 after) upper)
           (division-left-shift-frame-p world after)
           (equal (proof-world-pc after) (+ (proof-world-pc world) (if (consp digits) 36 0)))
           (equal (boymoo-model::a64-memory (proof-world-machine after))
                  (division-write-window-limbs written target
                                               (boymoo-model::a64-memory (proof-world-machine world))))))))

(defthm division-left-shift-loop-correct
  (let* ((steps (* 9 (len digits)))
         (after (proof-advance steps world)))
    (implies (and (division-left-shift-loop-ready-p digits world)
                  (equal (proof-world-reg 2 world) (+ (proof-world-reg 4 world) (* 8 (len digits)))))
             (and (division-left-shift-loop-output-p digits world after)
                  (division-before-cuts-p steps (list (+ 36 (proof-world-pc world))) world))))
  :hints (("Goal"
           :induct (division-left-shift-loop-ready-p digits world)
           :in-theory (disable division-left-shift-limb-inputs-p division-left-shift-digit
                               proof-advance-append division-before-cuts-append))
          ("Subgoal *1/2"
           :use ((:instance division-left-shift-limb-runs)
                 (:instance proof-advance-append (prefix 9) (suffix (* 9 (len (cdr digits)))))
                 (:instance division-before-cuts-append
                            (cuts (list (+ 36 (proof-world-pc world))))
                            (prefix 9) (suffix (* 9 (len (cdr digits))))))))
  :rule-classes nil)

(defthm division-left-shift-loop-writes-scaled-value
  (let* ((steps (* 9 (len digits)))
         (after (proof-advance steps world))
         (cuts (list (+ 36 (proof-world-pc world))))
         (count (len digits))
         (address (+ (proof-world-reg 1 world) (proof-world-reg 4 world)))
         (written (division-read-limbs count address (proof-world-machine after)))
         (carry (proof-world-reg 6 world))
         (shift (proof-world-reg 3 world))
         (scale (expt 2 shift)))
    (implies (and (consp digits) (division-digits-p digits)
                  (not (proof-world-stop world))
                  (< shift 32) (unsigned-byte-p shift carry)
                  (proof-span-p address (* 8 count))
                  (division-left-shift-loop-ready-p digits world)
                  (equal (proof-world-reg 2 world) (+ (proof-world-reg 4 world) (* 8 count))))
             (and (proof-segment-p steps cuts world :cut after)
                  (division-digits-p written)
                  (< (proof-world-reg 6 after) scale)
                  (equal (+ (division-magnitude written)
                            (* (division-place-value count) (proof-world-reg 6 after)))
                         (+ (* scale (division-magnitude digits)) carry)))))
  :hints (("Goal"
           :use ((:instance division-left-shift-loop-correct)
                 (:instance division-left-shift-limbs-correct
                            (carry (proof-world-reg 6 world)) (scale (expt 2 (proof-world-reg 3 world))))
                 (:instance division-limb-scale-fits (shift (proof-world-reg 3 world)))
                 (:instance division-segment-from-cut-free-prefix
                            (count (* 9 (len digits))) (cuts (list (+ 36 (proof-world-pc world)))))
                 (:instance division-read-window-limb-writes
                            (digits (mv-nth 0 (division-left-shift-limbs
                                               digits (proof-world-reg 6 world)
                                               (expt 2 (proof-world-reg 3 world)))))
                            (address (+ (proof-world-reg 1 world) (proof-world-reg 4 world)))
                            (before (proof-world-machine world))
                            (after (proof-world-machine (proof-advance (* 9 (len digits)) world)))))
           :in-theory (disable division-left-shift-loop-ready-p division-left-shift-limbs
                               division-write-window-limbs division-read-limbs division-magnitude
                               division-place-value expt)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
