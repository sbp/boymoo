(in-package "BOYMOO-PROOFS")

(include-book "correction-machine")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod ash proof-step proof-world-reg proof-world-pc proof-world-stop
                     proof-world-machine proof-world-regions proof-load-word proof-advance
                     division-before-cuts-p division-instruction-prefix-ready-p
                     boymoo-model::a64-write-bytes boymoo-model::a64-memory boymoo-model::a64-sp)))

(defun division-window-loop-instructions (add-back)
  (if add-back *division-add-back-limb-instructions* *division-subtract-limb-instructions*))

(defun division-window-loop-limb-steps (add-back)
  (if add-back 10 14))

(defun division-window-loop-ready-p (add-back dividend divisor world)
  (if (atom divisor)
      (and (null divisor) (null dividend))
    (let* ((steps (division-window-loop-limb-steps add-back))
           (cuts (list (+ (* 4 steps) (proof-world-pc world)))))
      (and (consp dividend)
           (division-window-limb-layout-p steps world)
           (division-instruction-prefix-ready-p (division-window-loop-instructions add-back) cuts world)
           (equal (division-window-limb 14 world) (car dividend))
           (equal (division-window-limb 20 world) (car divisor))
           (division-window-loop-ready-p add-back (cdr dividend) (cdr divisor)
                                         (proof-advance steps world))))))

(defun division-window-loop-word (add-back digit divisor guess carry)
  (if add-back
      (division-add-back-digit digit divisor carry)
    (division-subtract-digit digit divisor guess carry)))

(defun division-window-loop-digits (add-back dividend divisor guess carry)
  (if add-back
      (division-add-back-limbs dividend divisor carry)
    (division-subtract-limbs dividend divisor guess carry)))

(defun division-write-window-limbs (digits address memory)
  (if (atom digits)
      memory
    (division-write-window-limbs
     (cdr digits) (+ 8 address) (boymoo-model::a64-write-bytes 8 address (car digits) memory))))

(defun division-window-carry-p (add-back guess carry)
  (and (natp carry)
       (if add-back
           (<= carry 1)
         (and (division-digit-p guess) (<= carry guess)))))

(local
 (defthm division-window-loop-word-preserves-carry
   (implies (and (division-window-carry-p add-back guess carry)
                 (division-digit-p digit) (division-digit-p divisor))
            (division-window-carry-p
             add-back guess (mv-nth 1 (division-window-loop-word add-back digit divisor guess carry))))
   :hints (("Goal"
            :cases (add-back)
            :use ((:instance division-add-back-digit-correct (divisor-digit divisor))
                  (:instance division-subtract-digit-correct (divisor-digit divisor)))
            :in-theory (disable division-subtract-digit division-add-back-digit)))
   :rule-classes nil))

(local
 (defthm division-window-loop-limb-runs
   (let* ((steps (division-window-loop-limb-steps add-back))
          (cuts (list (+ (* 4 steps) (proof-world-pc world))))
          (guess (proof-world-reg 15 world))
          (carry (proof-world-reg 1 world))
          (digit (division-window-limb 14 world))
          (divisor (division-window-limb 20 world)))
     (implies (and (division-window-limb-layout-p steps world)
                   (division-instruction-prefix-ready-p (division-window-loop-instructions add-back) cuts world)
                   (division-window-carry-p add-back guess carry))
              (mv-let (written next)
                (division-window-loop-word add-back digit divisor guess carry)
                (and (division-before-cuts-p steps cuts world)
                     (division-window-limb-output-p steps written next world (proof-advance steps world))))))
   :hints (("Goal"
            :cases (add-back)
            :use ((:instance division-add-back-limb-runs) (:instance division-subtract-limb-runs))
            :in-theory (disable division-window-limb-layout-p division-window-limb-output-p
                                division-subtract-digit division-add-back-digit division-window-limb)))
   :rule-classes nil))

(local
 (defthm division-window-advance-zero
   (equal (proof-advance 0 world) world)
   :hints (("Goal" :expand ((proof-advance 0 world))))))

(local
 (defthm division-window-before-cuts-zero
   (division-before-cuts-p 0 cuts world)
   :hints (("Goal" :expand ((division-before-cuts-p 0 cuts world))))))

(local
 (defun division-window-loop-induct (add-back dividend divisor world)
   (declare (xargs :measure (acl2-count divisor)))
   (if (atom divisor)
       (list dividend world)
     (division-window-loop-induct
      add-back (cdr dividend) (cdr divisor)
      (proof-advance (division-window-loop-limb-steps add-back) world)))))

(local
 (defthm division-window-limb-layout-has-digits
   (implies (division-window-limb-layout-p steps world)
            (and (division-digit-p (division-window-limb 14 world))
                 (division-digit-p (division-window-limb 20 world))))
   :rule-classes nil))

(local
 (defthm division-window-positive-list-length
   (implies (consp limbs) (< 0 (len limbs)))
   :hints (("Goal" :expand ((len limbs))))
   :rule-classes :linear))

(local
 (defthm division-window-loop-ready-at-step
   (let* ((steps (division-window-loop-limb-steps add-back))
          (cuts (list (+ (* 4 steps) (proof-world-pc world)))))
     (implies (and (consp divisor) (division-window-loop-ready-p add-back dividend divisor world))
              (and (consp dividend)
                   (division-window-limb-layout-p steps world)
                   (division-instruction-prefix-ready-p (division-window-loop-instructions add-back) cuts world)
                   (equal (division-window-limb 14 world) (car dividend))
                   (equal (division-window-limb 20 world) (car divisor))
                   (division-window-loop-ready-p add-back (cdr dividend) (cdr divisor)
                                                 (proof-advance steps world)))))
   :hints (("Goal" :expand ((division-window-loop-ready-p add-back dividend divisor world))
                   :in-theory (disable division-window-limb-layout-p division-window-limb
                                       division-window-loop-limb-steps division-window-loop-instructions)))
   :rule-classes nil))

(local
 (defthm division-window-loop-ready-at-end
   (implies (and (atom divisor) (division-window-loop-ready-p add-back dividend divisor world))
            (and (null divisor) (null dividend)))
   :hints (("Goal" :expand ((division-window-loop-ready-p add-back dividend divisor world))))
   :rule-classes nil))

(local
 (defthm division-window-loop-step
   (let* ((steps (division-window-loop-limb-steps add-back))
          (cuts (list (+ (* 4 steps) (proof-world-pc world))))
          (after (proof-advance steps world))
          (guess (proof-world-reg 15 world))
          (carry (proof-world-reg 1 world)))
     (implies (and (consp divisor)
                   (division-window-loop-ready-p add-back dividend divisor world)
                   (division-window-carry-p add-back guess carry))
              (mv-let (written next)
                (division-window-loop-word add-back (car dividend) (car divisor) guess carry)
                (and (consp dividend)
                     (division-before-cuts-p steps cuts world)
                     (division-window-limb-output-p steps written next world after)
                     (division-window-loop-ready-p add-back (cdr dividend) (cdr divisor) after)
                     (division-window-carry-p add-back (proof-world-reg 15 after) (proof-world-reg 1 after))))))
   :hints (("Goal"
            :use ((:instance division-window-loop-ready-at-step)
                  (:instance division-window-loop-limb-runs)
                  (:instance division-window-limb-layout-has-digits
                             (steps (division-window-loop-limb-steps add-back)))
                  (:instance division-window-loop-word-preserves-carry
                             (digit (car dividend)) (divisor (car divisor))
                             (guess (proof-world-reg 15 world)) (carry (proof-world-reg 1 world))))
            :in-theory (disable division-window-limb division-window-limb-layout-p
                                division-window-loop-ready-p division-window-carry-p
                                division-window-loop-word division-window-loop-limb-steps
                                division-window-loop-instructions)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-window-loop-correct
  (let* ((steps (division-window-loop-limb-steps add-back))
         (count (len divisor))
         (after (proof-advance (* steps count) world))
         (guess (proof-world-reg 15 world))
         (carry (proof-world-reg 1 world))
         (offset (proof-world-reg 0 world))
         (window (proof-world-reg 14 world))
         (pc (proof-world-pc world))
         (limit (proof-world-reg 22 world))
         (cuts (list (+ (* 4 steps) pc))))
    (implies (and (division-window-loop-ready-p add-back dividend divisor world)
                  (division-window-carry-p add-back guess carry)
                  (equal limit (+ offset (* 8 count))))
             (mv-let (written final-carry)
               (division-window-loop-digits add-back dividend divisor guess carry)
               (and (division-before-cuts-p (* steps count) cuts world)
                    (equal (proof-world-pc after) (if (consp divisor) (+ (* 4 steps) pc) pc))
                    (equal (proof-world-reg 0 after) limit)
                    (equal (proof-world-reg 1 after) final-carry)
                    (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
                    (equal (proof-world-reg 14 after) window)
                    (equal (proof-world-reg 15 after) guess)
                    (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                    (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
                    (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                    (equal (proof-world-reg 22 after) limit)
                    (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                    (equal (boymoo-model::a64-sp (proof-world-machine after))
                           (boymoo-model::a64-sp (proof-world-machine world)))
                    (equal (boymoo-model::a64-memory (proof-world-machine after))
                           (division-write-window-limbs
                            written (+ window offset) (boymoo-model::a64-memory (proof-world-machine world))))
                    (equal (proof-world-regions after) (proof-world-regions world))
                    (equal (proof-world-stop after) (proof-world-stop world))))))
  :hints (("Goal"
           :induct (division-window-loop-induct add-back dividend divisor world)
           :do-not '(generalize fertilize)
           :in-theory (disable division-subtract-digit division-add-back-digit
                               division-window-limb division-before-cuts-append proof-advance-append
                               division-window-limb-layout-p division-window-carry-p
                               (:definition division-window-loop-ready-p)))
          ("Subgoal *1/1" :use (:instance division-window-loop-ready-at-end))
          ("Subgoal *1/2"
           :use ((:instance division-window-loop-step)
                 (:instance proof-advance-append
                            (prefix (division-window-loop-limb-steps add-back))
                            (suffix (* (division-window-loop-limb-steps add-back) (len (cdr divisor)))))
                 (:instance division-before-cuts-append
                            (cuts (list (+ (* 4 (division-window-loop-limb-steps add-back))
                                           (proof-world-pc world))))
                            (prefix (division-window-loop-limb-steps add-back))
                            (suffix (* (division-window-loop-limb-steps add-back) (len (cdr divisor))))))))
  :rule-classes nil)
