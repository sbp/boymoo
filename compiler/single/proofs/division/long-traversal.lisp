(in-package "BOYMOO-PROOFS")

(include-book "position-layout")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-load-word proof-segment-p
                     division-before-cuts-p division-position-after division-position-steps
                     division-position-geometry-p division-position-machine-ready-p
                     division-position-estimate-ready-p division-position-write-ready-p
                     division-position-subtraction-start division-position-iteration-counts division-step-sum
                     boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)))

(defthm division-read-adjacent-limb-spans
  (implies (and (natp low) (natp high) (integerp address))
           (equal (division-read-limbs (+ low high) address machine)
                  (append (division-read-limbs low address machine)
                          (division-read-limbs high (+ address (* 8 low)) machine))))
  :hints (("Goal" :induct (division-read-limbs low address machine)
                  :do-not '(generalize fertilize))
          ("Subgoal *1/2" :cases ((equal low 1) (equal high 0))))
  :rule-classes nil)

(defthm division-magnitude-of-adjacent-limbs
  (equal (division-magnitude (append low high))
         (+ (division-magnitude low)
            (* (division-place-value (len low)) (division-magnitude high))))
  :hints (("Goal" :induct (append low high))))

(defthm division-read-limb-span-value
  (implies (and (natp low) (natp high) (integerp address))
           (equal (division-magnitude (division-read-limbs (+ low high) address machine))
                  (+ (division-magnitude (division-read-limbs low address machine))
                     (* (division-place-value low)
                        (division-magnitude (division-read-limbs high (+ address (* 8 low)) machine))))))
  :hints (("Goal"
           :use (:instance division-read-adjacent-limb-spans)
           :in-theory (disable division-read-limbs division-magnitude division-place-value)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-single-read-limb-value
   (equal (division-magnitude (division-read-limbs 1 address machine))
          (nfix (proof-load-word address machine)))
   :hints (("Goal" :expand ((division-read-limbs 1 address machine)
                            (division-read-limbs 0 (+ 8 address) machine))))))

(local
 (defthm division-read-no-limb-list
   (equal (division-read-limbs 0 address machine) nil)
   :hints (("Goal" :expand ((division-read-limbs 0 address machine))))))

(defun division-long-dividend-value (positions divisor world)
  (division-magnitude
   (division-read-limbs (+ positions (len divisor)) (proof-world-reg 19 world) (proof-world-machine world))))

(defun division-long-remainder (divisor world)
  (division-read-limbs (len divisor) (proof-world-reg 19 world) (proof-world-machine world)))

(defun division-long-quotient (positions world)
  (division-read-limbs positions (proof-world-reg 21 world) (proof-world-machine world)))

(defun division-long-buffers-p (positions divisor world)
  (let ((r-address (proof-world-reg 19 world))
        (q-address (proof-world-reg 21 world))
        (r-size (* 8 (+ positions (len divisor))))
        (q-size (* 8 positions)))
    (and (proof-span-p r-address r-size)
         (proof-span-p q-address q-size)
         (proof-disjoint-p r-address (+ r-address r-size) q-address (+ q-address q-size)))))

(defun division-long-stage-access-p (positions divisor world)
  (let ((after (division-position-after divisor world)))
    (and (posp positions)
         (not (proof-world-stop world))
         (not (proof-world-stop after))
         (equal (proof-world-reg 13 world) (* 8 (1- positions)))
         (division-long-buffers-p positions divisor world)
         (division-position-machine-ready-p divisor world)
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (division-before-cuts-p (division-position-steps divisor world)
                                 (list (+ 252 (proof-world-pc world))) world))))

(defun division-long-stage-ready-p (positions divisor world)
  (and (division-long-stage-access-p positions divisor world)
       (division-position-geometry-p divisor world)))

(defun division-long-run-ready-p (positions divisor world)
  (declare (xargs :measure (nfix positions)))
  (and (posp positions)
       (division-long-stage-ready-p positions divisor world)
       (or (equal positions 1)
           (division-long-run-ready-p (1- positions) divisor (division-position-after divisor world)))))

(defun division-long-run-steps (positions divisor world)
  (declare (xargs :measure (nfix positions)))
  (if (zp positions)
      0
    (+ (division-position-steps divisor world)
       (division-long-run-steps (1- positions) divisor (division-position-after divisor world)))))

(defun division-long-run-after (positions divisor world)
  (proof-advance (division-long-run-steps positions divisor world) world))

(local
 (defthm division-long-position-steps-are-natural
   (natp (division-position-steps divisor world))
   :hints (("Goal" :in-theory (enable division-position-steps)))
   :rule-classes :type-prescription))

(local
 (defthm division-long-run-steps-are-natural
   (natp (division-long-run-steps positions divisor world))
   :hints (("Goal" :induct (division-long-run-steps positions divisor world)))
   :rule-classes :type-prescription))

(local
 (defthm division-long-run-goes-to-next-position
   (implies (posp positions)
            (equal (division-long-run-after positions divisor world)
                   (division-long-run-after (1- positions) divisor (division-position-after divisor world))))
   :hints (("Goal"
            :use (:instance proof-advance-append
                            (prefix (division-position-steps divisor world))
                            (suffix (division-long-run-steps (1- positions) divisor
                                                            (division-position-after divisor world))))
            :in-theory (e/d (division-position-after) (proof-advance-append))
            :expand ((division-long-run-steps positions divisor world))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-zero-positions
   (equal (division-long-run-after 0 divisor world) world)
   :hints (("Goal" :expand ((proof-advance 0 world) (division-long-run-steps 0 divisor world))))))

(local
 (defthm division-position-value-is-its-span
   (implies (division-position-geometry-p divisor world)
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
            :in-theory (e/d (division-position-geometry-p)
                            (division-digits-p division-read-limbs division-magnitude division-place-value))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defun division-long-position-quotient (world after)
  (proof-load-word (+ (proof-world-reg 21 world) (proof-world-reg 13 world))
                   (proof-world-machine after)))

(local
 (defthm division-long-position-window-address
   (implies (division-long-stage-ready-p positions divisor world)
            (equal (division-position-window world)
                   (+ (proof-world-reg 19 world) (* 8 (1- positions)))))
   :hints (("Goal" :in-theory (disable division-long-buffers-p)
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-stage-keeps-low-limbs
   (let* ((low (1- positions))
          (base (proof-world-reg 19 world))
          (after (division-position-after divisor world)))
     (implies (division-long-stage-ready-p positions divisor world)
              (equal (division-read-limbs low base (proof-world-machine after))
                     (division-read-limbs low base (proof-world-machine world)))))
   :hints (("Goal"
            :use (:instance division-position-preserves-disjoint-limbs
                            (digits (division-position-digits divisor world)) (count (1- positions))
                            (query (proof-world-reg 19 world)))
            :in-theory (e/d (division-position-machine-ready-p division-position-after division-position-steps)
                            (division-position-digits division-read-limbs division-position-iteration-counts
                             division-step-sum))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-weighted-conservation
   (implies (and (acl2-numberp weight) (acl2-numberp q) (acl2-numberp divisor)
                 (acl2-numberp residue) (acl2-numberp low)
                 (equal window (+ (* divisor q) residue))
                 (equal before (+ low (* weight window)))
                 (equal after (+ low (* weight residue))))
            (equal before (+ after (* divisor q weight))))
   :rule-classes nil))

(local
 (defthm division-long-stage-dividend-identity
   (let* ((low (1- positions))
          (after (division-position-after divisor world))
          (q (division-long-position-quotient world after))
          (b (division-magnitude divisor))
          (old-value (division-long-dividend-value positions divisor world))
          (new-value (division-long-dividend-value low divisor after)))
     (implies (division-long-stage-ready-p positions divisor world)
              (equal old-value (+ (* b q (division-place-value low)) new-value))))
   :hints (("Goal"
            :use ((:instance division-position-from-memory)
                  (:instance division-position-value-is-its-span)
                  (:instance division-long-position-window-address)
                  (:instance division-long-stage-keeps-low-limbs)
                  (:instance division-read-limb-span-value
                             (low (1- positions)) (high (1+ (len divisor)))
                             (address (proof-world-reg 19 world)) (machine (proof-world-machine world)))
                  (:instance division-read-limb-span-value
                             (low (1- positions)) (high (len divisor)) (address (proof-world-reg 19 world))
                             (machine (proof-world-machine (division-position-after divisor world))))
                  (:instance division-long-weighted-conservation
                             (before (division-long-dividend-value positions divisor world))
                             (after (division-long-dividend-value (1- positions) divisor (division-position-after divisor world)))
                             (low (division-magnitude (division-read-limbs
                                                       (1- positions) (proof-world-reg 19 world) (proof-world-machine world))))
                             (q (division-long-position-quotient world (division-position-after divisor world)))
                             (divisor (division-magnitude divisor))
                             (residue (division-magnitude (division-read-limbs
                                                           (len divisor) (division-position-window world)
                                                           (proof-world-machine (division-position-after divisor world)))))
                             (window (division-position-value divisor world))
                             (weight (division-place-value (1- positions)))))
            :in-theory (disable division-read-limbs division-magnitude division-place-value
                                division-position-value division-position-window division-digits-p
                                division-read-limbs-view-magnitude division-long-buffers-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-stage-preserves-external-limbs
   (let* ((r-address (proof-world-reg 19 world))
          (q-address (proof-world-reg 21 world))
          (r-size (* 8 (+ positions (len divisor))))
          (q-size (* 8 positions))
          (end (+ query (* 8 count)))
          (after (division-position-after divisor world)))
     (implies (and (division-long-stage-ready-p positions divisor world)
                   (natp count) (proof-span-p query (* 8 count))
                   (proof-disjoint-p r-address (+ r-address r-size) query end)
                   (proof-disjoint-p q-address (+ q-address q-size) query end))
              (equal (division-read-limbs count query (proof-world-machine after))
                     (division-read-limbs count query (proof-world-machine world)))))
   :hints (("Goal"
            :use (:instance division-position-preserves-disjoint-limbs
                            (digits (division-position-digits divisor world)))
            :in-theory (e/d (division-position-machine-ready-p division-position-after division-position-steps)
                            (division-position-digits division-read-limbs division-position-iteration-counts
                             division-step-sum))
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-long-run-preserves-external-limbs
  (let* ((r-address (proof-world-reg 19 world))
         (q-address (proof-world-reg 21 world))
         (r-size (* 8 (+ positions (len divisor))))
         (q-size (* 8 positions))
         (end (+ query (* 8 count)))
         (after (division-long-run-after positions divisor world)))
    (implies (and (division-long-run-ready-p positions divisor world)
                  (natp count) (proof-span-p query (* 8 count))
                  (proof-disjoint-p r-address (+ r-address r-size) query end)
                  (proof-disjoint-p q-address (+ q-address q-size) query end))
             (equal (division-read-limbs count query (proof-world-machine after))
                    (division-read-limbs count query (proof-world-machine world)))))
  :hints (("Goal"
           :induct (division-long-run-steps positions divisor world)
           :in-theory (disable division-read-limbs division-long-run-after division-long-buffers-p))
          ("Subgoal *1/2"
           :cases ((equal positions 1))
           :use ((:instance division-long-stage-preserves-external-limbs)
                 (:instance division-long-run-goes-to-next-position))))
  :rule-classes nil)

(local
 (defthm division-long-run-keeps-bases
   (let ((after (division-long-run-after positions divisor world)))
     (implies (division-long-run-ready-p positions divisor world)
              (and (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                   (equal (proof-world-reg 21 after) (proof-world-reg 21 world)))))
   :hints (("Goal"
            :induct (division-long-run-steps positions divisor world)
            :in-theory (disable division-long-run-after division-long-buffers-p))
           ("Subgoal *1/2"
            :cases ((equal positions 1))
            :use (:instance division-long-run-goes-to-next-position)))
   :rule-classes nil))

(local
 (defthm division-long-run-finishes-at-fallthrough
   (let* ((cuts (list (+ 252 (proof-world-pc world))))
          (steps (division-long-run-steps positions divisor world))
          (after (division-long-run-after positions divisor world)))
     (implies (division-long-run-ready-p positions divisor world)
              (and (division-before-cuts-p steps cuts world)
                   (equal (proof-world-pc after) (+ 252 (proof-world-pc world)))
                   (not (proof-world-stop after)))))
   :hints (("Goal"
            :induct (division-long-run-steps positions divisor world)
            :in-theory (disable division-long-run-after division-long-buffers-p division-before-cuts-append))
           ("Subgoal *1/2"
            :cases ((equal positions 1))
            :use ((:instance division-long-run-goes-to-next-position)
                  (:instance division-position-from-memory)
                  (:instance division-before-cuts-append
                             (cuts (list (+ 252 (proof-world-pc world))))
                             (prefix (division-position-steps divisor world))
                             (suffix (division-long-run-steps (1- positions) divisor
                                                             (division-position-after divisor world)))))
            :in-theory (enable division-position-after)))
   :rule-classes nil))

(local
 (defthm division-read-single-limb-list
   (equal (division-read-limbs 1 address machine) (list (proof-load-word address machine)))
   :hints (("Goal" :expand ((division-read-limbs 1 address machine)
                            (division-read-limbs 0 (+ 8 address) machine))))))

(local
 (defthm division-long-position-quotient-at-index
   (implies (division-long-stage-ready-p positions divisor world)
            (equal (division-long-position-quotient world after)
                   (proof-load-word (+ (proof-world-reg 21 world) (* 8 (1- positions)))
                                    (proof-world-machine after))))
   :hints (("Goal"
            :use (:instance division-scale-equality
                            (a (proof-world-reg 13 world)) (b (* 8 (1- positions))) (factor 1))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-quotient-from-lower-positions-and-top
   (let* ((lower (1- positions))
          (next (division-position-after divisor world))
          (after (division-long-run-after positions divisor world))
          (digit (division-long-position-quotient world next)))
     (implies (division-long-run-ready-p positions divisor world)
              (equal (division-long-quotient positions after)
                     (append (division-long-quotient lower after) (list digit)))))
   :hints (("Goal"
            :cases ((equal positions 1))
            :use ((:instance division-long-run-goes-to-next-position)
                  (:instance division-read-adjacent-limb-spans
                             (low (1- positions)) (high 1)
                             (address (proof-world-reg 21 (division-long-run-after positions divisor world)))
                             (machine (proof-world-machine (division-long-run-after positions divisor world))))
                  (:instance division-long-run-keeps-bases)
                  (:instance division-long-position-quotient-at-index (after (division-position-after divisor world)))
                  (:instance division-long-run-preserves-external-limbs
                             (count 1) (positions (1- positions))
                             (query (+ (proof-world-reg 21 world) (* 8 (1- positions))))
                             (world (division-position-after divisor world))))
            :in-theory (disable division-read-limbs division-long-run-steps division-long-run-after
                                division-long-position-quotient)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-digit-lists-append
   (implies (and (division-digits-p first) (division-digits-p last))
            (division-digits-p (append first last)))
   :hints (("Goal" :induct (append first last)))))

(local
 (defthm division-long-quotient-extension
   (implies (and (equal quotient (append lower (list digit)))
                 (division-digits-p lower) (division-digit-p digit))
            (and (division-digits-p quotient)
                 (equal (division-magnitude quotient)
                        (+ (division-magnitude lower) (* (division-place-value (len lower)) digit)))))
   :rule-classes nil))

(local
 (defthm division-long-quotient-conservation
   (implies (and (acl2-numberp divisor) (acl2-numberp digit) (acl2-numberp weight)
                 (acl2-numberp lower) (acl2-numberp remainder)
                 (equal before (+ (* divisor digit weight) next))
                 (equal next (+ (* divisor lower) remainder))
                 (equal quotient (+ lower (* weight digit))))
            (equal (+ (* divisor quotient) remainder) before))
   :rule-classes nil))

(local
 (defthm division-long-run-value-and-range
   (let* ((after (division-long-run-after positions divisor world))
          (quotient (division-long-quotient positions after))
          (remainder (division-long-remainder divisor after))
          (q (division-magnitude quotient))
          (r (division-magnitude remainder))
          (b (division-magnitude divisor)))
     (implies (division-long-run-ready-p positions divisor world)
              (and (division-digits-p quotient)
                   (division-digits-p remainder)
                   (< r b)
                   (equal (+ (* b q) r) (division-long-dividend-value positions divisor world)))))
   :hints (("Goal"
            :induct (division-long-run-steps positions divisor world)
            :in-theory (disable division-long-run-after division-read-limbs division-magnitude
                                division-digits-p division-long-buffers-p division-position-value
                                division-read-limbs-view-magnitude))
           ("Subgoal *1/2"
            :cases ((equal positions 1))
            :use ((:instance division-long-stage-dividend-identity)
                  (:instance division-long-run-goes-to-next-position)
                  (:instance division-long-quotient-from-lower-positions-and-top)
                  (:instance division-position-from-memory)
                  (:instance division-long-quotient-extension
                             (quotient (division-long-quotient positions (division-long-run-after positions divisor world)))
                             (lower (division-long-quotient (1- positions) (division-long-run-after positions divisor world)))
                             (digit (division-long-position-quotient world (division-position-after divisor world))))
                  (:instance division-long-quotient-conservation
                             (divisor (division-magnitude divisor))
                             (before (division-long-dividend-value positions divisor world))
                             (next (division-long-dividend-value (1- positions) divisor (division-position-after divisor world)))
                             (quotient (division-magnitude
                                        (division-long-quotient positions (division-long-run-after positions divisor world))))
                             (lower (division-magnitude
                                     (division-long-quotient (1- positions) (division-long-run-after positions divisor world))))
                             (weight (division-place-value (1- positions)))
                             (remainder (division-magnitude
                                         (division-long-remainder divisor (division-long-run-after positions divisor world))))
                             (digit (division-long-position-quotient world (division-position-after divisor world)))))))
   :rule-classes nil))

(defthm division-long-traversal-writes-quotient-and-scaled-remainder
  (let* ((steps (division-long-run-steps positions divisor world))
         (after (division-long-run-after positions divisor world))
         (quotient (division-long-quotient positions after))
         (remainder (division-long-remainder divisor after))
         (q (division-magnitude quotient))
         (r (division-magnitude remainder))
         (b (division-magnitude divisor)))
    (implies (division-long-run-ready-p positions divisor world)
             (and (proof-segment-p steps (list (+ 252 (proof-world-pc world))) world :cut after)
                  (division-digits-p quotient)
                  (division-digits-p remainder)
                  (< r b)
                  (equal (+ (* b q) r) (division-long-dividend-value positions divisor world))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world)))))
  :hints (("Goal"
           :use ((:instance division-long-run-keeps-bases)
                 (:instance division-long-run-finishes-at-fallthrough)
                 (:instance division-long-run-value-and-range)
                 (:instance division-segment-from-cut-free-prefix
                            (count (division-long-run-steps positions divisor world))
                            (cuts (list (+ 252 (proof-world-pc world))))))
           :in-theory (disable division-long-run-ready-p division-long-run-steps division-read-limbs
                               division-magnitude division-digits-p)
           :do-not-induct t))
  :rule-classes nil)
