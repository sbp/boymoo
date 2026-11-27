(in-package "BOYMOO-PROOFS")

(include-book "divide-one")
(include-book "divide-return")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-segment-p division-before-cuts-p division-instruction-prefix-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-sp)))

(defun division-one-call-digits (count world)
  (division-read-limbs count (+ 16 (proof-world-reg 0 world)) (proof-world-machine world)))

(defun division-one-call-prefix-counts (count)
  (list 17 (+ 6 (* 7 count))))

(defun division-one-call-raw (count world)
  (division-advance-chain (division-one-call-prefix-counts count) world))

(defun division-one-call-quotient (count world)
  (division-read-limbs count (proof-world-reg 21 world) (proof-world-machine world)))

(defun division-one-call-remainder (world)
  (list (proof-load-word (proof-world-reg 19 world) (proof-world-machine world))))

(defun division-one-call-ready-p (a b count q-steps r-steps world)
  (let* ((cuts (list (proof-world-reg 30 world)))
         (before-loop (proof-advance 17 world))
         (raw (division-one-call-raw count world))
         (digits (division-one-call-digits count world)))
    (and (posp count)
         (proof-integer-view-p a (proof-world-reg 0 world) count world)
         (proof-integer-view-p b (proof-world-reg 1 world) 1 world)
         (not (equal b 0))
         (division-divide-entry-inputs-p count 1 world)
         (division-instruction-prefix-ready-p
          (division-divide-dispatch-instructions count 1) cuts world)
         (division-one-path-layout-p digits (abs b) before-loop)
         (division-one-path-remainder-ready-p digits before-loop)
         (division-before-cuts-p (division-one-path-steps digits) cuts before-loop)
         (division-normalization-return-ready-p
          world (division-one-call-quotient count raw) (division-one-call-remainder raw)
          q-steps r-steps raw))))

(local
 (defthm division-one-call-dispatch-advances
   (implies (and (posp count) (division-divide-entry-inputs-p count 1 world)
                 (division-instruction-prefix-ready-p
                  (division-divide-dispatch-instructions count 1) cuts world))
            (and (division-divide-dispatch-output-p count 1 world (proof-advance 17 world))
                 (division-before-cuts-p 17 cuts world)))
   :hints (("Goal"
            :use ((:instance division-divide-dispatch-effects (a-count count) (b-count 1))
                  (:instance division-instruction-prefix-advances
                             (instructions (division-divide-dispatch-instructions count 1))))
            :in-theory (disable division-divide-entry-inputs-p division-divide-dispatch-output-p
                                division-instruction-sequence)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-one-call-raw-values
   (let* ((raw (division-one-call-raw count world))
          (prefix (division-one-call-prefix-counts count))
          (cuts (list (proof-world-reg 30 world))))
     (implies (division-one-call-ready-p a b count q-steps r-steps world)
              (and (division-chain-before-cuts-p prefix cuts world)
                   (equal (division-normalization-address nil raw) (proof-world-reg 2 world))
                   (equal (division-normalization-address t raw) (proof-world-reg 3 world))
                   (equal (division-magnitude (division-one-call-quotient count raw))
                          (floor (abs a) (abs b)))
                   (equal (division-magnitude (division-one-call-remainder raw))
                          (mod (abs a) (abs b))))))
   :hints (("Goal"
            :use ((:instance division-one-call-dispatch-advances (cuts (list (proof-world-reg 30 world))))
                  (:instance division-divide-one-writes-quotient-and-remainder
                             (digits (division-one-call-digits count world)) (divisor (abs b))
                             (world (proof-advance 17 world)))
                  (:instance division-view-magnitude-and-count (address (proof-world-reg 0 world)) (value a)))
            :in-theory (disable division-normalization-return-ready-p division-read-limbs division-one-path-layout-p
                                division-one-path-remainder-ready-p
                                proof-integer-view proof-integer-view-p division-divide-saved-registers-p
                                division-digits-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defun division-one-call-steps (count q-steps r-steps)
  (+ (division-step-sum (division-one-call-prefix-counts count))
     (division-step-sum (division-normalization-return-steps q-steps r-steps))))

(local
 (defthm division-one-call-final-cut
   (let* ((raw (division-one-call-raw count world))
          (prefix (division-step-sum (division-one-call-prefix-counts count)))
          (suffix (division-step-sum (division-normalization-return-steps q-steps r-steps)))
          (after (proof-advance suffix raw))
          (cuts (list (proof-world-reg 30 world))))
     (implies (and (division-one-call-ready-p a b count q-steps r-steps world)
                   (proof-segment-p suffix cuts raw :cut after))
              (proof-segment-p (+ prefix suffix) cuts world :cut after)))
   :hints (("Goal"
            :use ((:instance division-one-call-raw-values)
                  (:instance division-advance-chain-sum (counts (division-one-call-prefix-counts count)))
                  (:instance division-chain-keeps-before-cuts
                             (counts (division-one-call-prefix-counts count))
                             (cuts (list (proof-world-reg 30 world))))
                  (:instance division-run-after-cut-free-prefix
                             (prefix (division-step-sum (division-one-call-prefix-counts count)))
                             (suffix (division-step-sum (division-normalization-return-steps q-steps r-steps)))
                             (cuts (list (proof-world-reg 30 world)))))
            :in-theory (e/d (proof-segment-p)
                            (division-one-call-ready-p
                             division-one-call-prefix-counts division-step-sum
                             division-normalization-return-steps division-normalization-address
                             division-one-call-quotient division-one-call-remainder division-magnitude
                             proof-run division-run-after-cut-free-prefix))
            :do-not-induct t))
   :rule-classes nil))

(defthm division-one-limb-entry-to-return
  (let* ((steps (division-one-call-steps count q-steps r-steps))
         (raw (division-one-call-raw count world))
         (after (proof-advance steps world))
         (q-limbs (division-one-call-quotient count raw))
         (r-limbs (division-one-call-remainder raw)))
    (implies (division-one-call-ready-p a b count q-steps r-steps world)
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
           :use ((:instance division-one-call-raw-values)
                 (:instance division-one-call-final-cut)
                 (:instance division-divide-normalize-and-return
                            (entry world) (world (division-one-call-raw count world))
                            (q-digits (division-one-call-quotient count (division-one-call-raw count world)))
                            (r-digits (division-one-call-remainder (division-one-call-raw count world))))
                 (:instance division-advance-chain-sum (counts (division-one-call-prefix-counts count)))
                 (:instance proof-advance-append
                            (prefix (division-step-sum (division-one-call-prefix-counts count)))
                            (suffix (division-step-sum (division-normalization-return-steps q-steps r-steps)))))
           :in-theory (disable division-one-call-prefix-counts division-step-sum
                               division-normalization-return-steps division-normalization-address
                               division-normalization-return-ready-p division-magnitude division-trim-limbs
                               division-one-call-quotient division-one-call-remainder proof-integer-view-p
                               division-one-path-layout-p division-one-path-remainder-ready-p
                               division-read-limbs division-divide-entry-inputs-p proof-advance-append)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
