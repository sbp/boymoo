(in-package "BOYMOO-PROOFS")

(include-book "effects")
(include-book "linked")
(include-book "cutpoints")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-estimate-instructions*
  (division-runtime-block "rt:z-divide-estimate" 0 9))

(defthm division-estimate-target-is-subtraction
  (equal (division-runtime-offset "rt:z-divide-subtract")
         (+ 36 (division-runtime-offset "rt:z-divide-estimate")))
  :rule-classes nil)

(local
 (in-theory (disable floor mod ash truncate proof-step proof-world-pc proof-world-reg
                     proof-world-machine proof-world-regions proof-world-stop
                     proof-instruction-at-p proof-instruction-effect proof-instruction-access-p
                     boymoo-model::a64-memory boymoo-model::a64-unsigned boymoo-model::a64-shift
                     boymoo-model::a64-condition boymoo-model::a64-nzcv
                     division-a64-unsigned-is-remainder)))

(defun division-estimate-registers-p (world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 36 (proof-world-pc world)))
       (division-leading-digit-p (proof-world-reg 11 world))
       (division-digit-p (proof-world-reg 12 world))
       (division-digit-p (proof-world-reg 15 world))
       (division-digit-p (proof-world-reg 17 world))))

(defun division-estimate-iteration-length (guess rest next digit)
  (cond ((<= *division-radix* rest) 2)
        ((division-estimate-stop-p guess rest next digit) 6)
        (t 9)))

(defun division-estimate-iteration-instructions (world)
  (take (division-estimate-iteration-length
         (proof-world-reg 15 world) (proof-world-reg 16 world)
         (proof-world-reg 12 world) (proof-world-reg 17 world))
        *division-estimate-instructions*))

(defun division-estimate-iteration-result-p (world after)
  (let* ((guess (proof-world-reg 15 world))
         (rest (proof-world-reg 16 world))
         (stop (division-estimate-stop-p guess rest
                                         (proof-world-reg 12 world) (proof-world-reg 17 world))))
    (and (equal (proof-world-reg 15 after) (if stop guess (1- guess)))
         (equal (proof-world-reg 16 after) (if stop rest (+ rest (proof-world-reg 11 world))))
         (equal (proof-world-pc after) (+ (proof-world-pc world) (if stop 36 0)))
         (equal (proof-world-reg 11 after) (proof-world-reg 11 world))
         (equal (proof-world-reg 12 after) (proof-world-reg 12 world))
         (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
         (equal (proof-world-reg 14 after) (proof-world-reg 14 world))
         (equal (proof-world-reg 17 after) (proof-world-reg 17 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-memory (proof-world-machine world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world))
         (division-ordinary-world-p after))))

(local
 (defthm division-estimate-comparison-operands-fit
   (implies (and (division-digit-p guess) (division-digit-p next)
                 (division-digit-p digit) (division-digit-p rest)
                 (division-digit-p lead))
            (and (unsigned-byte-p 64 (* guess next))
                 (unsigned-byte-p 64 (* *division-radix* rest))
                 (unsigned-byte-p 64 (+ (* *division-radix* rest) digit))
                 (unsigned-byte-p 64 (+ rest lead))))
   :hints (("Goal" :use (:instance division-digit-product-bound (x guess) (y next))))
   :rule-classes nil))

(local
 (defthm division-estimate-rest-reaches-radix
   (implies (unsigned-byte-p 64 rest)
            (and (equal (equal (ash rest -32) 0) (< rest *division-radix*))
                 (unsigned-byte-p 64 (ash rest -32))))
   :hints (("Goal"
            :use ((:instance division-floor-at-least (a rest) (b *division-radix*) (q 1))
                  (:instance division-floor-bounds (a rest) (b *division-radix*))
                  (:instance division-right-shift-fits-remaining-bits (word rest) (shift 32)))))
   :rule-classes nil))

(local
 (defthm division-estimate-decrement-fits
   (implies (and (division-digit-p guess) (natp next) (natp rest) (natp digit)
                 (< (+ (* *division-radix* rest) digit) (* guess next)))
            (and (posp guess) (unsigned-byte-p 64 (1- guess))))
   :hints (("Goal" :cases ((equal guess 0))
                   :nonlinearp t))
   :rule-classes nil))

(defthm division-estimate-iteration-effects
  (implies (division-estimate-registers-p world)
           (division-estimate-iteration-result-p
            world (division-instruction-sequence (division-estimate-iteration-instructions world) world)))
  :hints (("Goal"
           :cases ((< (proof-world-reg 16 world) *division-radix*)
                   (equal (proof-world-reg 15 world) 0)
                   (<= (* (proof-world-reg 15 world) (proof-world-reg 12 world))
                       (+ (* *division-radix* (proof-world-reg 16 world)) (proof-world-reg 17 world))))
           :use ((:instance division-estimate-comparison-operands-fit
                            (guess (proof-world-reg 15 world)) (rest (proof-world-reg 16 world))
                            (lead (proof-world-reg 11 world)) (next (proof-world-reg 12 world))
                            (digit (proof-world-reg 17 world)))
                 (:instance division-estimate-rest-reaches-radix (rest (proof-world-reg 16 world)))
                 (:instance division-estimate-decrement-fits
                            (guess (proof-world-reg 15 world)) (rest (proof-world-reg 16 world))
                            (next (proof-world-reg 12 world)) (digit (proof-world-reg 17 world))))
           :in-theory (disable division-runtime-block)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-estimate-entry-p (world)
  (and (division-estimate-registers-p world)
       (not (proof-world-stop world))
       (proof-instructions-at-p *division-estimate-instructions* (proof-world-pc world) world)))

(local
 (defthm division-estimate-iteration-prefix-ready
   (implies (division-estimate-entry-p world)
            (division-instruction-prefix-ready-p
             (division-estimate-iteration-instructions world)
             (list (+ 36 (proof-world-pc world))) world))
   :hints (("Goal"
            :cases ((< (proof-world-reg 16 world) *division-radix*)
                    (equal (proof-world-reg 15 world) 0)
                    (<= (* (proof-world-reg 15 world) (proof-world-reg 12 world))
                        (+ (* *division-radix* (proof-world-reg 16 world)) (proof-world-reg 17 world))))
            :use ((:instance division-estimate-comparison-operands-fit
                             (guess (proof-world-reg 15 world)) (rest (proof-world-reg 16 world))
                             (lead (proof-world-reg 11 world)) (next (proof-world-reg 12 world))
                             (digit (proof-world-reg 17 world)))
                  (:instance division-estimate-rest-reaches-radix (rest (proof-world-reg 16 world))))
            :in-theory (e/d (division-instruction-at-depends-on-bytes proof-instruction-access-p)
                            (division-decoded-word-at-p division-runtime-block))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-estimate-instructions-are-iteration-length
   (equal (len (division-estimate-iteration-instructions world))
          (division-estimate-iteration-length
           (proof-world-reg 15 world) (proof-world-reg 16 world)
           (proof-world-reg 12 world) (proof-world-reg 17 world)))))

(defthm division-estimate-iteration-checked
  (let* ((steps (len (division-estimate-iteration-instructions world)))
         (after (proof-advance steps world)))
    (implies (division-estimate-entry-p world)
             (and (division-before-cuts-p steps (list (+ 36 (proof-world-pc world))) world)
                  (division-estimate-iteration-result-p world after))))
  :hints (("Goal"
           :use ((:instance division-estimate-iteration-prefix-ready)
                 (:instance division-estimate-iteration-effects)
                 (:instance division-instruction-prefix-advances
                            (instructions (division-estimate-iteration-instructions world))
                            (cuts (list (+ 36 (proof-world-pc world))))))
           :in-theory (disable division-estimate-iteration-result-p
                               division-instruction-sequence division-instruction-prefix-ready-p
                               division-estimate-iteration-instructions division-estimate-iteration-length
                               division-estimate-registers-p proof-instructions-at-p
                               division-before-cuts-p proof-advance)))
  :rule-classes nil)

(local
 (defthm division-estimate-back-edge-ready
   (let* ((after (proof-advance 9 world))
          (guess (proof-world-reg 15 world))
          (rest (proof-world-reg 16 world))
          (next (proof-world-reg 12 world))
          (digit (proof-world-reg 17 world)))
     (implies (and (division-estimate-entry-p world)
                   (not (division-estimate-stop-p guess rest next digit)))
              (and (posp guess) (division-estimate-entry-p after))))
   :hints (("Goal"
            :use ((:instance division-estimate-iteration-checked)
                  (:instance division-estimate-decrement-fits
                             (guess (proof-world-reg 15 world)) (rest (proof-world-reg 16 world))
                             (next (proof-world-reg 12 world)) (digit (proof-world-reg 17 world)))
                  (:instance division-instructions-placement-preserved
                             (instructions *division-estimate-instructions*) (address (proof-world-pc world))
                             (before world) (after (proof-advance 9 world))))
            :in-theory (disable proof-advance proof-instructions-at-p division-estimate-iteration-instructions
                                division-before-cuts-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defun division-estimate-loop-steps (guess rest lead next digit)
  (declare (xargs :measure (nfix guess)))
  (if (or (zp guess) (division-estimate-stop-p guess rest next digit))
      (division-estimate-iteration-length guess rest next digit)
    (+ 9 (division-estimate-loop-steps (1- guess) (+ rest lead) lead next digit))))

(local
 (defthm division-zero-estimate-stops
   (implies (and (natp rest) (natp digit))
            (division-estimate-stop-p 0 rest next digit))))

(defthm division-estimate-loop-step-bound
  (implies (and (natp guess) (natp rest) (natp lead) (natp next) (natp digit))
           (<= (division-estimate-loop-steps guess rest lead next digit)
               (+ 6 (* 9 (- guess (division-correct-estimate guess rest lead next digit))))))
  :hints (("Goal"
           :induct (division-estimate-loop-steps guess rest lead next digit)
           :in-theory (disable division-estimate-stop-p)))
  :rule-classes nil)

(local
 (defun division-estimate-world-induct (guess rest lead next digit world)
   (declare (xargs :measure (nfix guess)
                   :hints (("Goal" :in-theory (disable proof-advance)))))
   (if (or (zp guess) (division-estimate-stop-p guess rest next digit))
       world
     (division-estimate-world-induct (1- guess) (+ rest lead) lead next digit
                                    (proof-advance 9 world)))))

(local
 (defthm division-estimate-machine-loop
   (let* ((steps (division-estimate-loop-steps guess rest lead next digit))
          (after (proof-advance steps world))
          (estimate (division-correct-estimate guess rest lead next digit)))
     (implies (and (division-estimate-entry-p world)
                   (equal guess (proof-world-reg 15 world))
                   (equal rest (proof-world-reg 16 world))
                   (equal lead (proof-world-reg 11 world))
                   (equal next (proof-world-reg 12 world))
                   (equal digit (proof-world-reg 17 world)))
              (and (division-before-cuts-p steps (list (+ 36 (proof-world-pc world))) world)
                   (equal (proof-world-pc after) (+ 36 (proof-world-pc world)))
                   (equal (proof-world-reg 15 after) estimate)
                   (equal (proof-world-reg 16 after) (+ rest (* (- guess estimate) lead)))
                   (equal (proof-world-reg 11 after) lead)
                   (equal (proof-world-reg 12 after) next)
                   (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
                   (equal (proof-world-reg 14 after) (proof-world-reg 14 world))
                   (equal (proof-world-reg 17 after) digit)
                   (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                   (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                   (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory (proof-world-machine world)))
                   (equal (proof-world-regions after) (proof-world-regions world))
                   (not (proof-world-stop after))
                   (division-ordinary-world-p after))))
   :hints (("Goal"
            :induct (division-estimate-world-induct guess rest lead next digit world)
            :in-theory (disable proof-advance division-before-cuts-p
                                division-estimate-iteration-instructions proof-instructions-at-p
                                division-before-cuts-append proof-advance-append))
           ("Subgoal *1/2"
            :use ((:instance division-estimate-back-edge-ready)
                  (:instance division-estimate-iteration-checked)
                  (:instance proof-advance-append
                             (prefix 9)
                             (suffix (division-estimate-loop-steps
                                      (1- guess) (+ rest lead) lead next digit)))
                  (:instance division-before-cuts-append
                             (cuts (list (+ 36 (proof-world-pc world))))
                             (prefix 9)
                             (suffix (division-estimate-loop-steps
                                      (1- guess) (+ rest lead) lead next digit)))))
           ("Subgoal *1/1" :use (:instance division-estimate-iteration-checked)))
   :rule-classes nil))

(defthm division-estimate-loop-reaches-subtraction
  (let* ((guess (proof-world-reg 15 world))
         (rest (proof-world-reg 16 world))
         (lead (proof-world-reg 11 world))
         (next (proof-world-reg 12 world))
         (digit (proof-world-reg 17 world))
         (steps (division-estimate-loop-steps guess rest lead next digit))
         (after (proof-advance steps world))
         (estimate (division-correct-estimate guess rest lead next digit)))
    (implies (division-estimate-entry-p world)
             (and (proof-segment-p steps (list (+ 36 (proof-world-pc world))) world :cut after)
                  (equal (proof-world-pc after) (+ 36 (proof-world-pc world)))
                  (equal (proof-world-reg 15 after) estimate)
                  (equal (proof-world-reg 16 after) (+ rest (* (- guess estimate) lead)))
                  (equal (proof-world-reg 11 after) lead)
                  (equal (proof-world-reg 12 after) next)
                  (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
                  (equal (proof-world-reg 14 after) (proof-world-reg 14 world))
                  (equal (proof-world-reg 17 after) digit)
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-regions after) (proof-world-regions world)))))
  :hints (("Goal"
           :use ((:instance division-estimate-machine-loop
                            (guess (proof-world-reg 15 world)) (rest (proof-world-reg 16 world))
                            (lead (proof-world-reg 11 world)) (next (proof-world-reg 12 world))
                            (digit (proof-world-reg 17 world)))
                 (:instance division-segment-from-cut-free-prefix
                            (cuts (list (+ 36 (proof-world-pc world))))
                            (count (division-estimate-loop-steps
                                    (proof-world-reg 15 world) (proof-world-reg 16 world)
                                    (proof-world-reg 11 world) (proof-world-reg 12 world)
                                    (proof-world-reg 17 world)))))
           :in-theory (disable proof-advance proof-segment-p division-before-cuts-p
                               division-estimate-entry-p division-estimate-loop-steps
                               division-correct-estimate)))
  :rule-classes nil)

(defthm division-estimate-loop-from-head
  (let* ((lead (proof-world-reg 11 world))
         (next (proof-world-reg 12 world))
         (digit (proof-world-reg 17 world))
         (guess (division-first-estimate head lead))
         (rest (- head (* guess lead)))
         (steps (division-estimate-loop-steps guess rest lead next digit))
         (after (proof-advance steps world)))
    (implies (and (division-estimate-entry-p world) (unsigned-byte-p 64 head)
                  (equal (proof-world-reg 15 world) guess)
                  (equal (proof-world-reg 16 world) rest))
             (and (<= steps 24)
                  (proof-segment-p steps (list (+ 36 (proof-world-pc world))) world :cut after)
                  (equal (proof-world-pc after) (+ 36 (proof-world-pc world)))
                  (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
                  (equal (proof-world-reg 14 after) (proof-world-reg 14 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-reg 15 after)
                         (division-two-limb-estimate head lead next digit)))))
  :hints (("Goal"
           :use ((:instance division-estimate-loop-reaches-subtraction)
                 (:instance division-estimate-loop-step-bound
                            (guess (proof-world-reg 15 world)) (rest (proof-world-reg 16 world))
                            (lead (proof-world-reg 11 world)) (next (proof-world-reg 12 world))
                            (digit (proof-world-reg 17 world)))
                 (:instance division-estimate-at-most-two-corrections
                            (lead (proof-world-reg 11 world)) (next (proof-world-reg 12 world))
                            (digit (proof-world-reg 17 world))))
           :in-theory (disable proof-advance proof-segment-p proof-instructions-at-p
                               division-first-estimate division-estimate-loop-steps
                               division-correct-estimate)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
