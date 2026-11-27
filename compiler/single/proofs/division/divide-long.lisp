(in-package "BOYMOO-PROOFS")

(include-book "traversal-invariants")
(include-book "long-finish")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable abs floor mod expt proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-segment-p division-before-cuts-p
                     division-instruction-prefix-ready-p division-divide-entry-inputs-p
                     division-long-scale-ready-p division-long-run-ready-p division-long-run-layout-ready-p
                     division-unscale-ready-p
                     division-normalization-return-ready-p division-chain-before-cuts-p
                     division-long-scale-stage division-long-scale-shift division-long-scaled-divisor
                     division-long-scale-position-count division-long-scale-steps
                     division-long-finish-raw division-long-finish-prefix-counts division-long-finish-steps
                     division-long-run-after division-long-remainder division-long-quotient division-step-sum
                     division-read-limbs division-read-limbs-view-magnitude division-magnitude
                     boymoo-model::a64-sp)))

(defun division-long-call-view-limbs (divisor count world)
  (division-read-limbs count (+ 16 (proof-world-reg (if divisor 1 0) world))
                       (proof-world-machine world)))

(defun division-long-call-first-position (a-count b-count world)
  (let ((a (division-long-call-view-limbs nil a-count world))
        (b (division-long-call-view-limbs t b-count world)))
    (division-long-scale-stage 6 a b (proof-advance 18 world))))

(defun division-long-call-scaled-divisor (a-count b-count world)
  (let ((a (division-long-call-view-limbs nil a-count world))
        (b (division-long-call-view-limbs t b-count world)))
    (division-long-scaled-divisor a b (proof-advance 18 world))))

(defun division-long-call-prefix-counts (a-count b-count world)
  (list 18 (division-long-scale-steps (division-long-call-view-limbs nil a-count world)
                                      (division-long-call-view-limbs t b-count world))))

(defun division-long-call-ready-p (a b a-count b-count q-steps r-steps world)
  (let* ((choose (proof-advance 18 world))
         (entered (division-long-call-first-position a-count b-count world))
         (dividend (division-long-call-view-limbs nil a-count world))
         (divisor (division-long-call-view-limbs t b-count world))
         (shifted (division-long-call-scaled-divisor a-count b-count world))
         (positions (division-long-scale-position-count dividend divisor))
         (loop-done (division-long-run-after positions shifted entered))
         (raw (division-long-finish-raw positions shifted entered))
         (cuts (list (proof-world-reg 30 world))))
    (and (natp a-count) (natp b-count) (<= 2 b-count) (<= b-count a-count)
         (not (equal b 0))
         (proof-integer-view-p a (proof-world-reg 0 world) a-count world)
         (proof-integer-view-p b (proof-world-reg 1 world) b-count world)
         (division-divide-entry-inputs-p a-count b-count world)
         (division-instruction-prefix-ready-p (division-divide-dispatch-instructions a-count b-count) cuts world)
         (division-long-scale-ready-p dividend divisor choose)
         (division-before-cuts-p (division-long-scale-steps dividend divisor) cuts choose)
         (equal (division-saved-normalization-shift loop-done) (division-long-scale-shift divisor))
         (division-long-run-layout-ready-p positions shifted entered)
         (division-unscale-ready-p positions (division-long-remainder shifted loop-done) loop-done)
         (division-chain-before-cuts-p (division-long-finish-prefix-counts positions shifted entered) cuts entered)
         (division-normalization-return-ready-p
          world (division-long-quotient positions raw) (division-long-remainder shifted raw) q-steps r-steps raw))))

(local
 (defthm division-long-call-prologue-advances
   (implies (and (<= 2 b-count) (<= b-count a-count)
                 (division-divide-entry-inputs-p a-count b-count world)
                 (division-instruction-prefix-ready-p (division-divide-dispatch-instructions a-count b-count) cuts world))
            (and (division-divide-dispatch-output-p a-count b-count world (proof-advance 18 world))
                 (division-before-cuts-p 18 cuts world)))
   :hints (("Goal"
            :use ((:instance division-divide-dispatch-effects)
                  (:instance division-instruction-prefix-advances
                             (instructions (division-divide-dispatch-instructions a-count b-count))))
            :in-theory (disable division-divide-dispatch-output-p division-instruction-sequence)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-call-passes-scaled-operands
   (let* ((entered (division-long-call-first-position a-count b-count world))
          (shifted (division-long-call-scaled-divisor a-count b-count world))
          (positions (division-long-scale-position-count (division-long-call-view-limbs nil a-count world)
                                                         (division-long-call-view-limbs t b-count world))))
     (implies (division-long-call-ready-p a b a-count b-count q-steps r-steps world)
              (division-long-finish-result-ready-p a b world positions shifted q-steps r-steps entered)))
   :hints (("Goal"
            :use ((:instance division-long-call-prologue-advances (cuts (list (proof-world-reg 30 world))))
                  (:instance division-long-scale-prepares-operands
                             (dividend (division-long-call-view-limbs nil a-count world))
                             (divisor (division-long-call-view-limbs t b-count world))
                             (world (proof-advance 18 world)))
                  (:instance division-long-run-ready-after-scaling
                             (dividend (division-long-call-view-limbs nil a-count world))
                             (divisor (division-long-call-view-limbs t b-count world))
                             (world (proof-advance 18 world)))
                  (:instance division-view-magnitude-and-count (value a) (count a-count) (address (proof-world-reg 0 world)))
                  (:instance division-view-magnitude-and-count (value b) (count b-count) (address (proof-world-reg 1 world))))
            :in-theory (disable proof-integer-view division-leading-limb division-normalized-limbs-p
                                division-divide-saved-registers-p division-saved-normalization-shift)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-scale-stage-six-advances
   (equal (division-long-scale-stage 6 dividend divisor world)
          (proof-advance (division-long-scale-steps dividend divisor) world))
   :hints (("Goal"
            :use (:instance division-advance-chain-sum (counts (division-long-scale-counts dividend divisor)))
            :in-theory (e/d (division-long-scale-stage division-long-scale-steps)
                            (division-advance-chain division-left-shift-call-steps))))
   :rule-classes nil))

(local
 (defthm division-long-call-goes-to-first-position
   (let* ((counts (division-long-call-prefix-counts a-count b-count world))
          (cuts (list (proof-world-reg 30 world)))
          (steps (division-step-sum counts)))
     (implies (division-long-call-ready-p a b a-count b-count q-steps r-steps world)
              (and (division-before-cuts-p steps cuts world)
                   (equal (proof-advance steps world) (division-long-call-first-position a-count b-count world)))))
   :hints (("Goal"
            :use ((:instance division-long-call-prologue-advances (cuts (list (proof-world-reg 30 world))))
                  (:instance division-long-scale-stage-six-advances
                             (dividend (division-long-call-view-limbs nil a-count world))
                             (divisor (division-long-call-view-limbs t b-count world))
                             (world (proof-advance 18 world)))
                  (:instance division-advance-chain-sum (counts (division-long-call-prefix-counts a-count b-count world)))
                  (:instance division-chain-keeps-before-cuts
                             (counts (division-long-call-prefix-counts a-count b-count world))
                             (cuts (list (proof-world-reg 30 world)))))
            :in-theory (e/d (division-chain-before-cuts-p)
                            (proof-integer-view-p division-divide-dispatch-output-p
                             division-long-call-view-limbs division-saved-normalization-shift))
            :do-not-induct t))
   :rule-classes nil))

(defun division-long-call-steps (a-count b-count q-steps r-steps world)
  (let* ((dividend (division-long-call-view-limbs nil a-count world))
         (divisor (division-long-call-view-limbs t b-count world))
         (shifted (division-long-call-scaled-divisor a-count b-count world))
         (positions (division-long-scale-position-count dividend divisor))
         (entered (division-long-call-first-position a-count b-count world)))
    (+ (division-step-sum (division-long-call-prefix-counts a-count b-count world))
       (division-long-finish-steps positions shifted q-steps r-steps entered))))

(local
 (defthm division-long-call-joins-finish
   (let* ((entry (division-long-call-first-position a-count b-count world))
          (prefix (division-step-sum (division-long-call-prefix-counts a-count b-count world)))
          (steps (division-long-call-steps a-count b-count q-steps r-steps world))
          (cuts (list (proof-world-reg 30 world))))
     (implies (and (division-long-call-ready-p a b a-count b-count q-steps r-steps world)
                   (natp suffix)
                   (equal steps (+ prefix suffix))
                   (proof-segment-p suffix cuts entry :cut (proof-advance suffix entry)))
              (and (proof-segment-p steps cuts world :cut (proof-advance steps world))
                   (equal (proof-advance steps world) (proof-advance suffix entry)))))
   :hints (("Goal"
            :use ((:instance division-long-call-goes-to-first-position)
                  (:instance division-run-after-cut-free-prefix
                             (prefix (division-step-sum (division-long-call-prefix-counts a-count b-count world)))
                             (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-advance-append
                             (prefix (division-step-sum (division-long-call-prefix-counts a-count b-count world)))))
            :in-theory (e/d (proof-segment-p)
                            (proof-run division-long-call-ready-p division-long-call-steps
                             division-long-call-prefix-counts division-long-call-first-position
                             division-run-after-cut-free-prefix proof-advance-append))
            :do-not-induct t))
   :rule-classes nil))

(defthm division-multi-limb-entry-to-return
  (let* ((steps (division-long-call-steps a-count b-count q-steps r-steps world))
         (after (proof-advance steps world))
         (entered (division-long-call-first-position a-count b-count world))
         (shifted (division-long-call-scaled-divisor a-count b-count world))
         (positions (division-long-scale-position-count (division-long-call-view-limbs nil a-count world)
                                                        (division-long-call-view-limbs t b-count world)))
         (raw (division-long-finish-raw positions shifted entered))
         (q-limbs (division-long-quotient positions raw))
         (r-limbs (division-long-remainder shifted raw)))
    (implies (division-long-call-ready-p a b a-count b-count q-steps r-steps world)
             (and (proof-segment-p steps (list (proof-world-reg 30 world)) world :cut after)
                  (proof-integer-view-p (floor (abs a) (abs b)) (proof-world-reg 2 world)
                                        (len (division-trim-limbs q-limbs)) after)
                  (proof-integer-view-p (mod (abs a) (abs b)) (proof-world-reg 3 world)
                                        (len (division-trim-limbs r-limbs)) after)
                  (equal (proof-world-reg 0 after) (proof-world-reg 3 world))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world))))))
  :hints (("Goal"
           :use ((:instance division-long-call-passes-scaled-operands)
                 (:instance division-long-normalized-entry-to-return
                            (world (division-long-call-first-position a-count b-count world))
                            (entry world) (divisor (division-long-call-scaled-divisor a-count b-count world))
                            (positions (division-long-scale-position-count (division-long-call-view-limbs nil a-count world)
                                                                          (division-long-call-view-limbs t b-count world))))
                 (:instance division-long-call-joins-finish
                            (suffix (division-long-finish-steps
                                     (division-long-scale-position-count (division-long-call-view-limbs nil a-count world)
                                                                        (division-long-call-view-limbs t b-count world))
                                     (division-long-call-scaled-divisor a-count b-count world) q-steps r-steps
                                     (division-long-call-first-position a-count b-count world)))))
           :in-theory (disable proof-integer-view-p division-long-call-ready-p
                               division-long-call-view-limbs division-long-finish-result-ready-p
                               division-long-call-first-position division-long-call-scaled-divisor)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
