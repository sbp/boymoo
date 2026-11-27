(in-package "BOYMOO-PROOFS")

(include-book "long-traversal")
(include-book "unscale")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod expt proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-segment-p division-before-cuts-p
                     division-long-run-ready-p division-long-run-steps division-unscale-ready-p
                     division-unscale-steps division-saved-normalization-shift
                     division-read-limbs division-magnitude division-read-limbs-view-magnitude
                     boymoo-model::a64-sp)))

(defun division-long-finish-prefix-counts (positions divisor world)
  (let* ((scaled-end (division-long-run-after positions divisor world))
         (scaled-remainder (division-long-remainder divisor scaled-end)))
    (list (division-long-run-steps positions divisor world)
          (division-unscale-steps scaled-remainder scaled-end))))

(defun division-long-finish-raw (positions divisor world)
  (division-advance-chain (division-long-finish-prefix-counts positions divisor world) world))

(defun division-long-finish-result-ready-p (a b entry positions divisor q-steps r-steps world)
  (let* ((scaled-end (division-long-run-after positions divisor world))
         (scaled-remainder (division-long-remainder divisor scaled-end))
         (shift (division-saved-normalization-shift scaled-end))
         (scale (expt 2 shift))
         (counts (division-long-finish-prefix-counts positions divisor world))
         (raw (division-long-finish-raw positions divisor world))
         (q-digits (division-long-quotient positions raw))
         (r-digits (division-long-remainder divisor raw)))
    (and (integerp a) (integerp b) (not (equal b 0))
         (natp shift) (< shift 32)
         (equal (proof-world-reg 19 world) (+ 16 (proof-world-reg 3 entry)))
         (equal (proof-world-reg 21 world) (+ 16 (proof-world-reg 2 entry)))
         (equal (division-long-dividend-value positions divisor world) (* scale (abs a)))
         (equal (division-magnitude divisor) (* scale (abs b)))
         (division-long-run-ready-p positions divisor world)
         (division-unscale-ready-p positions scaled-remainder scaled-end)
         (division-chain-before-cuts-p counts (list (proof-world-reg 30 entry)) world)
         (division-normalization-return-ready-p entry q-digits r-digits q-steps r-steps raw))))

(local
 (defthm division-scaled-division-outputs
   (implies (and (natp a) (posp b) (posp scale) (natp q) (natp r)
                 (equal scaled-a (* scale a))
                 (equal scaled-b (* scale b))
                 (equal scaled-a (+ (* scaled-b q) r))
                 (< r scaled-b))
            (and (equal q (floor a b))
                 (equal (floor r scale) (mod a b))))
   :hints (("Goal" :use (:instance division-undo-normalization (scaled-remainder r))))
   :rule-classes nil))

(local
 (defthm division-absolute-integer-sizes
   (implies (and (integerp a) (integerp b) (not (equal b 0)))
            (and (natp (abs a)) (posp (abs b))))
   :rule-classes nil))

(local
 (defthm division-long-finish-has-raw-values
   (let* ((raw (division-long-finish-raw positions divisor world))
          (q-digits (division-long-quotient positions raw))
          (r-digits (division-long-remainder divisor raw)))
     (implies (division-long-finish-result-ready-p a b entry positions divisor q-steps r-steps world)
              (and (equal (division-normalization-address nil raw) (proof-world-reg 2 entry))
                   (equal (division-normalization-address t raw) (proof-world-reg 3 entry))
                   (equal (division-magnitude q-digits) (floor (abs a) (abs b)))
                   (equal (division-magnitude r-digits) (mod (abs a) (abs b))))))
   :hints (("Goal"
            :use ((:instance division-long-traversal-writes-quotient-and-scaled-remainder)
                  (:instance division-absolute-integer-sizes)
                  (:instance division-unscales-remainder-and-keeps-quotient
                             (digits (division-long-remainder divisor (division-long-run-after positions divisor world)))
                             (world (division-long-run-after positions divisor world)))
                  (:instance division-limb-scale-fits
                             (shift (division-saved-normalization-shift (division-long-run-after positions divisor world))))
                  (:instance division-scaled-division-outputs
                             (a (abs a)) (b (abs b))
                             (scaled-a (division-long-dividend-value positions divisor world))
                             (scaled-b (division-magnitude divisor))
                             (scale (expt 2 (division-saved-normalization-shift
                                            (division-long-run-after positions divisor world))))
                             (q (division-magnitude
                                 (division-long-quotient positions (division-long-run-after positions divisor world))))
                             (r (division-magnitude
                                 (division-long-remainder divisor (division-long-run-after positions divisor world))))))
            :in-theory (disable abs division-normalization-return-ready-p
                                division-chain-before-cuts-p proof-disjoint-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defun division-long-finish-steps (positions divisor q-steps r-steps world)
  (+ (division-step-sum (division-long-finish-prefix-counts positions divisor world))
     (division-step-sum (division-normalization-return-steps q-steps r-steps))))

(local
 (defthm division-long-finish-composes-segments
   (let* ((counts (division-long-finish-prefix-counts positions divisor world))
          (prefix (division-step-sum counts))
          (suffix (division-step-sum (division-normalization-return-steps q-steps r-steps)))
          (raw (division-long-finish-raw positions divisor world))
          (after (proof-advance suffix raw))
          (cuts (list (proof-world-reg 30 entry))))
     (implies (and (division-chain-before-cuts-p counts cuts world)
                   (proof-segment-p suffix cuts raw :cut after))
              (and (proof-segment-p (+ prefix suffix) cuts world :cut after)
                   (equal (proof-advance (+ prefix suffix) world) after))))
   :hints (("Goal"
            :use ((:instance division-advance-chain-sum (counts (division-long-finish-prefix-counts positions divisor world)))
                  (:instance division-chain-keeps-before-cuts
                             (counts (division-long-finish-prefix-counts positions divisor world))
                             (cuts (list (proof-world-reg 30 entry))))
                  (:instance division-run-after-cut-free-prefix
                             (prefix (division-step-sum (division-long-finish-prefix-counts positions divisor world)))
                             (suffix (division-step-sum (division-normalization-return-steps q-steps r-steps)))
                             (cuts (list (proof-world-reg 30 entry))))
                  (:instance proof-advance-append
                             (prefix (division-step-sum (division-long-finish-prefix-counts positions divisor world)))
                             (suffix (division-step-sum (division-normalization-return-steps q-steps r-steps)))))
            :in-theory (e/d (proof-segment-p)
                            (division-step-sum division-normalization-return-steps division-long-finish-prefix-counts
                             division-advance-chain division-chain-before-cuts-p proof-run
                             division-run-after-cut-free-prefix proof-advance-append))
            :do-not-induct t))
   :rule-classes nil))

(defthm division-long-normalized-entry-to-return
  (let* ((steps (division-long-finish-steps positions divisor q-steps r-steps world))
         (raw (division-long-finish-raw positions divisor world))
         (q-digits (division-long-quotient positions raw))
         (r-digits (division-long-remainder divisor raw))
         (after (proof-advance steps world)))
    (implies (division-long-finish-result-ready-p a b entry positions divisor q-steps r-steps world)
             (and (proof-segment-p steps (list (proof-world-reg 30 entry)) world :cut after)
                  (proof-integer-view-p (floor (abs a) (abs b)) (proof-world-reg 2 entry)
                                        (len (division-trim-limbs q-digits)) after)
                  (proof-integer-view-p (mod (abs a) (abs b)) (proof-world-reg 3 entry)
                                        (len (division-trim-limbs r-digits)) after)
                  (equal (proof-world-reg 0 after) (proof-world-reg 3 entry))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 entry))
                  (equal (proof-world-reg 20 after) (proof-world-reg 20 entry))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 entry))
                  (equal (proof-world-reg 22 after) (proof-world-reg 22 entry))
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 entry))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 entry))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine entry))))))
  :hints (("Goal"
           :use ((:instance division-long-finish-has-raw-values)
                 (:instance division-long-finish-composes-segments)
                 (:instance division-divide-normalize-and-return
                            (world (division-long-finish-raw positions divisor world))
                            (q-digits (division-long-quotient positions (division-long-finish-raw positions divisor world)))
                            (r-digits (division-long-remainder divisor (division-long-finish-raw positions divisor world)))))
           :in-theory (disable abs division-long-finish-raw division-long-finish-prefix-counts division-step-sum
                               division-normalization-return-steps division-normalization-return-ready-p
                               division-chain-before-cuts-p division-normalization-address
                               proof-integer-view-p division-long-quotient division-long-remainder)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
