(in-package "BOYMOO-PROOFS")

(include-book "long-traversal")
(include-book "long-scale")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod proof-advance proof-world-reg proof-world-machine
                     proof-load-word division-position-after division-position-steps
                     division-position-geometry-p division-position-machine-ready-p
                     division-long-stage-ready-p division-long-run-ready-p
                     division-long-scale-ready-p division-long-scale-stage
                     division-long-scaled-divisor division-a64-unsigned-is-remainder
                     boymoo-model::a64-unsigned boymoo-model::a64-load)))

(local
 (defthm division-loaded-word-is-natural
   (natp (proof-load-word address machine))
   :hints (("Goal"
            :use (:instance division-read-bytes-value-range
                            (count 8) (memory (boymoo-model::a64-memory machine)))
            :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                            (boymoo-model::a64-read-bytes))))
   :rule-classes :type-prescription))

(local
 (defthm division-one-read-limb
   (equal (division-read-limbs 1 address machine)
          (list (proof-load-word address machine)))
   :hints (("Goal" :expand ((division-read-limbs 1 address machine)
                            (division-read-limbs 0 (+ 8 address) machine))))))

(local
 (defthm division-position-value-reads-full-span
   (implies (equal (proof-world-reg 22 world) (* 8 (len divisor)))
            (equal (division-position-value divisor world)
                   (division-magnitude
                    (division-read-limbs (1+ (len divisor)) (division-position-window world)
                                         (proof-world-machine world)))))
   :hints (("Goal"
            :use ((:instance division-read-limb-span-value
                             (low (len divisor)) (high 1) (address (division-position-window world))
                             (machine (proof-world-machine world)))
                  (:instance division-world-register-in-word (register 13))
                  (:instance division-world-register-in-word (register 19)))
            :in-theory (disable division-read-limbs division-place-value)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-position-offset-does-not-wrap
   (implies (<= 8 (proof-world-reg 13 world))
            (equal (boymoo-model::a64-unsigned 64 (- (proof-world-reg 13 world) 8))
                   (- (proof-world-reg 13 world) 8)))
   :hints (("Goal" :use (:instance division-world-register-in-word (register 13))))
   :rule-classes nil))

(local
 (defthm division-next-position-window-address
   (let ((after (division-position-after divisor world)))
     (implies (and (division-long-stage-ready-p positions divisor world)
                   (< 1 positions))
              (equal (+ 8 (division-position-window after)) (division-position-window world))))
   :hints (("Goal"
            :use ((:instance division-position-from-memory)
                  (:instance division-position-offset-does-not-wrap))
            :in-theory (e/d (division-long-stage-ready-p)
                            (division-digits-p division-magnitude division-position-value
                             division-position-word division-read-limbs division-long-buffers-p
                             division-before-cuts-p division-long-position-quotient))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-next-position-appends-one-limb
  (let* ((after (division-position-after divisor world))
         (machine (proof-world-machine after))
         (digit (proof-load-word (division-position-window after) machine))
         (residue (division-read-limbs (len divisor) (division-position-window world) machine)))
    (implies (and (division-long-stage-ready-p positions divisor world)
                  (< 1 positions)
                  (equal (proof-world-reg 22 after) (* 8 (len divisor))))
             (equal (division-position-value divisor after)
                    (+ digit (* *division-radix* (division-magnitude residue))))))
  :hints (("Goal"
           :use ((:instance division-next-position-window-address)
                 (:instance division-position-value-reads-full-span
                            (world (division-position-after divisor world)))
                 (:instance division-read-limb-span-value
                            (low 1) (high (len divisor))
                            (address (division-position-window (division-position-after divisor world)))
                            (machine (proof-world-machine (division-position-after divisor world))))
                 (:instance division-world-register-in-word (register 13)
                            (world (division-position-after divisor world)))
                 (:instance division-world-register-in-word (register 19)
                            (world (division-position-after divisor world))))
           :in-theory (disable division-read-limbs division-position-value)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-digit-and-residue-are-below-window-bound
   (implies (and (division-digit-p digit)
                 (integerp residue) (integerp divisor) (< residue divisor))
            (< (+ digit (* *division-radix* residue)) (* *division-radix* divisor)))))

(defthm division-next-position-window-bound
  (let* ((after (division-position-after divisor world))
         (digit (proof-load-word (division-position-window after) (proof-world-machine after))))
    (implies (and (division-long-stage-ready-p positions divisor world)
                  (< 1 positions)
                  (equal (proof-world-reg 22 after) (* 8 (len divisor)))
                  (division-digit-p digit))
             (< (division-position-value divisor after) (* *division-radix* (division-magnitude divisor)))))
  :hints (("Goal"
           :use ((:instance division-next-position-appends-one-limb)
                 (:instance division-position-from-memory)
                 (:instance division-digit-and-residue-are-below-window-bound
                            (digit (proof-load-word (division-position-window (division-position-after divisor world))
                                                    (proof-world-machine (division-position-after divisor world))))
                            (residue (division-magnitude
                                      (division-read-limbs (len divisor) (division-position-window world)
                                                           (proof-world-machine (division-position-after divisor world)))))
                            (divisor (division-magnitude divisor))))
           :in-theory (e/d (division-long-stage-ready-p)
                           (division-digits-p division-magnitude division-position-value division-position-word
                            division-read-limbs division-long-buffers-p division-before-cuts-p
                            division-position-window division-digit-and-residue-are-below-window-bound))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-place-value-adds-exponents
   (implies (and (natp low) (natp high))
            (equal (division-place-value (+ low high))
                   (* (division-place-value low) (division-place-value high))))
   :hints (("Goal" :induct (division-place-value low)
                   :do-not '(generalize fertilize))
           ("Subgoal *1/2" :expand ((division-place-value (+ low high)))))))

(local
 (defthm division-positive-leading-limb-bounds-magnitude
   (implies (and (consp digits) (posp (division-leading-limb digits)))
            (<= (division-place-value (1- (len digits))) (division-magnitude digits)))
   :hints (("Goal" :induct (division-leading-limb digits)
                   :do-not '(generalize fertilize))
           ("Subgoal *1/1" :cases ((consp (cdr digits)))))))

(local
 (defthm division-window-bound-before-scaling
   (let* ((a (division-magnitude dividend))
          (b (division-magnitude divisor))
          (weight (division-place-value (- (len dividend) (len divisor)))))
     (implies (and (consp divisor) (<= (len divisor) (len dividend))
                   (division-digits-p dividend)
                   (posp (division-leading-limb divisor)))
              (< a (* weight *division-radix* b))))
   :hints (("Goal"
            :use ((:instance division-magnitude-bound (digits dividend))
                  (:instance division-positive-leading-limb-bounds-magnitude (digits divisor))
                  (:instance division-place-value-adds-exponents
                             (low (- (len dividend) (len divisor))) (high (len divisor)))
                  (:instance division-positive-product-order
                             (a (division-magnitude divisor))
                             (b (division-place-value (1- (len divisor))))
                             (factor (* *division-radix*
                                        (division-place-value (- (len dividend) (len divisor)))))))
            :expand ((division-place-value (len divisor)))
            :in-theory (disable division-magnitude-bound division-positive-leading-limb-bounds-magnitude
                                division-place-value-adds-exponents division-place-value
                                division-digits-p division-leading-limb division-magnitude)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-first-window-is-fitted-suffix
   (let* ((after (division-long-scale-stage 6 dividend divisor world))
          (base (proof-world-reg 19 after))
          (machine (proof-world-machine after))
          (positions (division-long-scale-position-count dividend divisor))
          (shifted (division-long-scaled-divisor dividend divisor world))
          (low (1- positions)))
     (implies (and (division-long-scale-ready-p dividend divisor world)
                   (equal (proof-world-reg 22 after) (* 8 (len divisor))))
              (equal (division-long-dividend-value positions shifted after)
                     (+ (division-magnitude (division-read-limbs low base machine))
                        (* (division-place-value low) (division-position-value shifted after))))))
   :hints (("Goal"
            :use ((:instance division-long-scale-prepares-operands)
                  (:instance division-position-value-reads-full-span
                             (divisor (division-long-scaled-divisor dividend divisor world))
                             (world (division-long-scale-stage 6 dividend divisor world)))
                  (:instance division-read-limb-span-value
                             (low (- (len dividend) (len divisor))) (high (1+ (len divisor)))
                             (address (proof-world-reg 19 (division-long-scale-stage 6 dividend divisor world)))
                             (machine (proof-world-machine (division-long-scale-stage 6 dividend divisor world))))
                  (:instance division-world-register-in-word (register 19)
                             (world (division-long-scale-stage 6 dividend divisor world))))
            :in-theory (disable division-long-scale-shift division-position-value division-magnitude
                                division-read-limbs division-place-value division-leading-digit-p
                                division-digits-p division-leading-limb)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-scaling-keeps-first-window-bound
   (implies (and (rationalp a) (rationalp b) (rationalp low) (rationalp window)
                 (rationalp scale) (< 0 scale) (rationalp weight) (< 0 weight)
                 (<= 0 low) (< a (* weight *division-radix* b))
                 (equal (+ low (* weight window)) (* scale a)))
            (< window (* *division-radix* scale b)))
   :hints (("Goal"
            :use ((:instance division-positive-product-order
                             (b (* weight *division-radix* b)) (factor scale))
                  (:instance division-positive-product-order
                             (a window) (b (* *division-radix* scale b)) (factor weight)))))
   :rule-classes nil))

(local
 (defthm division-long-scale-arithmetic-inputs
   (implies (division-long-scale-ready-p dividend divisor world)
            (and (consp divisor)
                 (<= (len divisor) (len dividend))
                 (division-digits-p dividend)
                 (posp (division-leading-limb divisor))))
   :hints (("Goal"
            :in-theory (e/d (division-long-scale-ready-p division-choose-normalization-inputs-p)
                            (division-unnormalized-leading-limb division-leading-limb division-digits-p
                             division-scale-call-inputs-p division-scale-window-setup-inputs-p
                             division-left-shift-call-ready-p division-instruction-sequence-ready-p
                             proof-span-p proof-disjoint-p division-ordinary-world-p))
            :do-not-induct t))
   :rule-classes nil))

(defthm division-first-scaled-position-window-bound
  (let* ((after (division-long-scale-stage 6 dividend divisor world))
         (shifted (division-long-scaled-divisor dividend divisor world)))
    (implies (and (division-long-scale-ready-p dividend divisor world)
                  (equal (proof-world-reg 22 after) (* 8 (len divisor))))
             (< (division-position-value shifted after) (* *division-radix* (division-magnitude shifted)))))
  :hints (("Goal"
           :use ((:instance division-long-scale-arithmetic-inputs)
                 (:instance division-long-scale-prepares-operands)
                 (:instance division-first-window-is-fitted-suffix)
                 (:instance division-window-bound-before-scaling)
                 (:instance division-scaling-keeps-first-window-bound
                            (a (division-magnitude dividend)) (b (division-magnitude divisor))
                            (scale (expt 2 (division-long-scale-shift divisor)))
                            (window (division-position-value (division-long-scaled-divisor dividend divisor world)
                                                            (division-long-scale-stage 6 dividend divisor world)))
                            (low (division-magnitude
                                  (division-read-limbs
                                   (- (len dividend) (len divisor))
                                   (proof-world-reg 19 (division-long-scale-stage 6 dividend divisor world))
                                   (proof-world-machine (division-long-scale-stage 6 dividend divisor world)))))
                            (weight (division-place-value (- (len dividend) (len divisor))))))
           :in-theory (disable division-read-limbs division-position-value division-magnitude division-place-value
                               division-leading-limb division-digits-p division-leading-digit-p division-long-scale-shift
                               division-long-dividend-value)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-long-stage-layout-ready-p (positions divisor world)
  (and (division-long-stage-access-p positions divisor world)
       (division-position-layout-p divisor world)))

(defun division-long-run-layout-ready-p (positions divisor world)
  (declare (xargs :measure (nfix positions)
                  :hints (("Goal" :in-theory (disable division-long-stage-layout-ready-p)))))
  (and (posp positions)
       (division-long-stage-layout-ready-p positions divisor world)
       (or (equal positions 1)
           (division-long-run-layout-ready-p (1- positions) divisor (division-position-after divisor world)))))

(local
 (defthm division-long-window-bound-completes-layout
   (implies (and (division-long-stage-layout-ready-p positions divisor world)
                 (< (division-position-value divisor world) (* *division-radix* (division-magnitude divisor))))
            (division-long-stage-ready-p positions divisor world))
   :hints (("Goal"
            :in-theory (e/d (division-long-stage-ready-p division-position-geometry-p)
                            (division-long-stage-access-p division-position-layout-p
                             division-position-value division-magnitude))))
   :rule-classes nil))

(local
 (defthm division-long-layout-fits-low-digit
   (implies (division-long-stage-layout-ready-p positions divisor world)
            (and (equal (proof-world-reg 22 world) (* 8 (len divisor)))
                 (division-digit-p (proof-load-word (division-position-window world) (proof-world-machine world)))))
   :hints (("Goal"
            :use (:instance division-limb-read-at-index
                            (index 0) (count (len divisor)) (address (division-position-window world))
                            (machine (proof-world-machine world)))
            :expand ((division-read-limbs (len divisor) (division-position-window world)
                                         (proof-world-machine world)))
            :in-theory (disable division-long-stage-access-p division-position-window
                                division-read-limbs division-leading-limb division-position-word)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-one-window-bound-suffices-for-traversal
  (implies (and (division-long-run-layout-ready-p positions divisor world)
                (< (division-position-value divisor world) (* *division-radix* (division-magnitude divisor))))
           (division-long-run-ready-p positions divisor world))
  :hints (("Goal"
           :induct (division-long-run-steps positions divisor world)
           :in-theory (disable division-long-stage-layout-ready-p division-position-value division-magnitude
                               division-position-window division-digit-p))
          ("Subgoal *1/2"
           :cases ((equal positions 1))
           :expand ((division-long-run-layout-ready-p positions divisor world)
                    (division-long-run-ready-p positions divisor world)
                    (division-long-run-layout-ready-p (1- positions) divisor (division-position-after divisor world)))
           :use ((:instance division-long-window-bound-completes-layout)
                 (:instance division-long-layout-fits-low-digit
                            (positions (1- positions)) (world (division-position-after divisor world)))
                 (:instance division-next-position-window-bound)))
          ("Subgoal *1/2.1" :expand ((division-long-run-ready-p 1 divisor world)))
          ("Subgoal *1/1" :expand ((division-long-run-layout-ready-p positions divisor world))))
  :rule-classes nil)

(defthm division-long-run-ready-after-scaling
  (let* ((after (division-long-scale-stage 6 dividend divisor world))
         (divisor-limbs (division-long-scaled-divisor dividend divisor world))
         (positions (division-long-scale-position-count dividend divisor)))
    (implies (and (division-long-scale-ready-p dividend divisor world)
                  (division-long-run-layout-ready-p positions divisor-limbs after))
             (division-long-run-ready-p positions divisor-limbs after)))
  :hints (("Goal"
           :use ((:instance division-long-scale-prepares-operands)
                 (:instance division-first-scaled-position-window-bound)
                 (:instance division-long-layout-fits-low-digit
                            (divisor (division-long-scaled-divisor dividend divisor world))
                            (positions (division-long-scale-position-count dividend divisor))
                            (world (division-long-scale-stage 6 dividend divisor world)))
                 (:instance division-one-window-bound-suffices-for-traversal
                            (divisor (division-long-scaled-divisor dividend divisor world))
                            (positions (division-long-scale-position-count dividend divisor))
                            (world (division-long-scale-stage 6 dividend divisor world))))
           :in-theory (disable division-long-stage-layout-ready-p division-long-run-layout-ready-p
                               division-position-value division-magnitude division-leading-digit-p
                               division-digits-p division-leading-limb division-long-dividend-value
                               division-long-scale-position-count division-position-window division-digit-p)
           :expand ((division-long-run-layout-ready-p (division-long-scale-position-count dividend divisor)
                                                      (division-long-scaled-divisor dividend divisor world)
                                                      (division-long-scale-stage 6 dividend divisor world)))
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
