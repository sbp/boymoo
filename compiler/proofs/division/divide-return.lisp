(in-package "BOYMOO-PROOFS")

(include-book "divide-flow")
(include-book "view-frame")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-advance proof-world-pc proof-world-reg proof-world-machine
                     proof-world-stop proof-world-regions proof-load-word proof-segment-p
                     division-before-cuts-p division-instruction-prefix-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-sp)))

(defun division-step-sum (counts)
  (if (atom counts)
      0
    (+ (nfix (car counts)) (division-step-sum (cdr counts)))))

(defun division-advance-chain (counts world)
  (if (atom counts)
      world
    (division-advance-chain (cdr counts) (proof-advance (car counts) world))))

(defun division-chain-before-cuts-p (counts cuts world)
  (if (atom counts)
      t
    (and (division-before-cuts-p (car counts) cuts world)
         (division-chain-before-cuts-p (cdr counts) cuts (proof-advance (car counts) world)))))

(defthm division-advance-chain-sum
  (equal (division-advance-chain counts world)
         (proof-advance (division-step-sum counts) world))
  :hints (("Goal" :induct (division-advance-chain counts world)
                  :in-theory (disable proof-advance-append))
          ("Subgoal *1/2"
           :use (:instance proof-advance-append
                           (prefix (car counts)) (suffix (division-step-sum (cdr counts)))))
          ("Subgoal *1/1" :expand ((proof-advance 0 world))))
  :rule-classes nil)

(defthm division-chain-keeps-before-cuts
  (implies (division-chain-before-cuts-p counts cuts world)
           (division-before-cuts-p (division-step-sum counts) cuts world))
  :hints (("Goal" :induct (division-advance-chain counts world)
                  :in-theory (disable division-before-cuts-append))
          ("Subgoal *1/2"
           :use (:instance division-before-cuts-append
                           (prefix (car counts)) (suffix (division-step-sum (cdr counts)))))
          ("Subgoal *1/1" :expand ((division-before-cuts-p 0 cuts world))))
  :rule-classes nil)

(local
 (defthm division-normalize-code-length
   (equal (len (division-normalize-instructions remainder)) 4)))

(defthm division-normalize-prefix-advances
  (implies (and (division-normalize-setup-p remainder count world)
                (division-instruction-prefix-ready-p (division-normalize-instructions remainder)
                                                     cuts world))
           (and (division-before-cuts-p 4 cuts world)
                (division-normalize-setup-output-p remainder count world (proof-advance 4 world))))
  :hints (("Goal"
           :use ((:instance division-divide-normalize-call-effects)
                 (:instance division-instruction-prefix-advances
                            (instructions (division-normalize-instructions remainder))))
           :in-theory (disable division-normalize-setup-p division-normalize-setup-output-p
                               division-normalize-instructions division-instruction-sequence)))
  :rule-classes nil)

(defthm division-restore-prefix-advances
  (implies (and (division-divide-saved-registers-p entry world)
                (division-ordinary-world-p world)
                (<= 64 (boymoo-model::a64-sp (proof-world-machine entry)))
                (division-instruction-prefix-ready-p *division-divide-restore-instructions* cuts world))
           (and (division-before-cuts-p 5 cuts world)
                (division-restore-output-p entry world (proof-advance 5 world))))
  :hints (("Goal"
           :use ((:instance division-divide-restore-effects)
                 (:instance division-instruction-prefix-advances
                            (instructions *division-divide-restore-instructions*)))
           :in-theory (disable division-divide-saved-registers-p division-restore-output-p
                               division-instruction-sequence)))
  :rule-classes nil)

(local
 (defthm division-register-frame-includes-register
   (implies (and (proof-register-frame-p last clobbers before after)
                 (natp last) (natp register) (<= register last) (not (member-equal register clobbers)))
            (equal (proof-world-reg register after) (proof-world-reg register before)))
   :hints (("Goal" :induct (proof-register-frame-p last clobbers before after))
           ("Subgoal *1/1" :cases ((equal register last))))))

(defthm division-normalize-return-frame
  (implies (division-unsigned-normalize-return-p digits entered returned)
           (and (equal (proof-world-reg 0 returned) (proof-world-reg 0 entered))
                (equal (proof-world-reg 9 returned) (proof-world-reg 9 entered))
                (equal (proof-world-reg 19 returned) (proof-world-reg 19 entered))
                (equal (proof-world-reg 21 returned) (proof-world-reg 21 entered))
                (equal (proof-world-reg 22 returned) (proof-world-reg 22 entered))
                (equal (proof-world-reg 30 returned) (proof-world-reg 30 entered))
                (equal (proof-world-pc returned) (proof-world-reg 30 entered))
                (equal (boymoo-model::a64-sp (proof-world-machine returned))
                       (boymoo-model::a64-sp (proof-world-machine entered)))
                (equal (proof-world-regions returned) (proof-world-regions entered))
                (not (proof-world-stop returned))))
  :hints (("Goal"
           :use ((:instance division-register-frame-includes-register
                            (last 30) (clobbers '(1 2 3 4)) (before entered) (after returned) (register 0))
                 (:instance division-register-frame-includes-register
                            (last 30) (clobbers '(1 2 3 4)) (before entered) (after returned) (register 9))
                 (:instance division-register-frame-includes-register
                            (last 30) (clobbers '(1 2 3 4)) (before entered) (after returned) (register 19))
                 (:instance division-register-frame-includes-register
                            (last 30) (clobbers '(1 2 3 4)) (before entered) (after returned) (register 21))
                 (:instance division-register-frame-includes-register
                            (last 30) (clobbers '(1 2 3 4)) (before entered) (after returned) (register 22))
                 (:instance division-register-frame-includes-register
                            (last 30) (clobbers '(1 2 3 4)) (before entered) (after returned) (register 30)))
           :in-theory (disable proof-register-frame-p division-normalize-arguments-p proof-integer-view-p
                               division-register-frame-includes-register division-trim-limbs)
           :do-not-induct t))
  :rule-classes nil)

(defun division-normalization-return-ready-p (entry q-digits r-digits q-steps r-steps world)
  (let* ((cuts (list (proof-world-reg 30 entry)))
         (q-call (proof-advance 4 world))
         (q-done (proof-advance q-steps q-call))
         (r-call (proof-advance 4 q-done))
         (r-done (proof-advance r-steps r-call))
         (q-address (division-normalization-address nil world))
         (q-count (len (division-trim-limbs q-digits)))
         (q-end (+ q-address (division-view-bytes q-count))))
    (and (natp q-steps) (natp r-steps)
         (division-normalize-setup-p nil (len q-digits) world)
         (division-instruction-prefix-ready-p *division-quotient-normalize-instructions* cuts world)
         (division-before-cuts-p q-steps cuts q-call)
         (division-unsigned-normalize-return-p q-digits q-call q-done)
         (division-normalize-setup-p t (len r-digits) q-done)
         (division-instruction-prefix-ready-p *division-remainder-normalize-instructions* cuts q-done)
         (division-before-cuts-p r-steps cuts r-call)
         (division-unsigned-normalize-return-p r-digits r-call r-done)
         (proof-span-p q-address (division-view-bytes q-count))
         (proof-memory-span-agrees-p q-address q-end q-done r-done)
         (division-divide-saved-registers-p entry r-done)
         (division-ordinary-world-p r-done)
         (<= 64 (boymoo-model::a64-sp (proof-world-machine entry)))
         (division-instruction-prefix-ready-p *division-divide-restore-instructions* cuts r-done))))

(defun division-normalization-return-steps (q-steps r-steps)
  (list 4 q-steps 4 r-steps 5))

(local
 (defthm division-normalization-return-has-frame-and-cuts
   (let* ((counts (division-normalization-return-steps q-steps r-steps))
          (cuts (list (proof-world-reg 30 entry)))
          (q-call (proof-advance 4 world))
          (q-done (proof-advance q-steps q-call))
          (r-call (proof-advance 4 q-done))
          (r-done (proof-advance r-steps r-call))
          (after (division-advance-chain counts world)))
     (implies (division-normalization-return-ready-p entry q-digits r-digits q-steps r-steps world)
              (and (division-chain-before-cuts-p counts cuts world)
                   (division-normalize-setup-output-p nil (len q-digits) world q-call)
                   (division-normalize-setup-output-p t (len r-digits) q-done r-call)
                   (division-restore-output-p entry r-done after))))
   :hints (("Goal"
            :use ((:instance division-normalize-prefix-advances
                             (remainder nil) (count (len q-digits)) (cuts (list (proof-world-reg 30 entry))))
                  (:instance division-normalize-prefix-advances
                             (remainder t) (count (len r-digits)) (cuts (list (proof-world-reg 30 entry)))
                             (world (proof-advance q-steps (proof-advance 4 world))))
                  (:instance division-restore-prefix-advances
                             (cuts (list (proof-world-reg 30 entry)))
                             (world (proof-advance r-steps
                                      (proof-advance 4 (proof-advance q-steps (proof-advance 4 world)))))))
            :in-theory (disable division-normalize-setup-p division-restore-output-p
                                division-normalize-setup-output-p division-divide-saved-registers-p
                                division-unsigned-normalize-return-p division-view-bytes proof-memory-span-agrees-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-normalization-return-has-views
   (let* ((q-call (proof-advance 4 world))
          (q-done (proof-advance q-steps q-call))
          (r-call (proof-advance 4 q-done))
          (r-done (proof-advance r-steps r-call))
          (q-address (division-normalization-address nil world))
          (r-address (division-normalization-address t world))
          (counts (division-normalization-return-steps q-steps r-steps))
          (after (division-advance-chain counts world)))
     (implies (division-normalization-return-ready-p entry q-digits r-digits q-steps r-steps world)
              (and (proof-integer-view-p (division-magnitude q-digits) q-address
                                         (len (division-trim-limbs q-digits)) r-done)
                   (proof-integer-view-p (division-magnitude r-digits) r-address
                                         (len (division-trim-limbs r-digits)) r-done)
                   (equal (proof-world-reg 0 r-done) r-address)
                   (not (proof-world-stop after)))))
   :hints (("Goal"
            :use ((:instance division-normalization-return-has-frame-and-cuts)
                  (:instance division-normalize-return-frame
                             (digits q-digits) (entered (proof-advance 4 world))
                             (returned (proof-advance q-steps (proof-advance 4 world))))
                  (:instance division-normalize-return-frame
                             (digits r-digits)
                             (entered (proof-advance 4 (proof-advance q-steps (proof-advance 4 world))))
                             (returned (proof-advance r-steps
                                        (proof-advance 4 (proof-advance q-steps (proof-advance 4 world))))))
                  (:instance division-integer-view-after-span-agreement
                             (value (division-magnitude q-digits))
                             (address (division-normalization-address nil world))
                             (count (len (division-trim-limbs q-digits)))
                             (start (division-normalization-address nil world))
                             (end (+ (division-normalization-address nil world)
                                     (division-view-bytes (len (division-trim-limbs q-digits)))))
                             (before (proof-advance q-steps (proof-advance 4 world)))
                             (after (proof-advance r-steps
                                     (proof-advance 4 (proof-advance q-steps (proof-advance 4 world)))))))
            :in-theory (disable proof-frame-return-p division-normalize-arguments-p proof-integer-view-p
                                division-magnitude division-trim-limbs proof-memory-span-agrees-p
                                division-chain-before-cuts-p division-divide-saved-registers-p
                                division-normalize-setup-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-divide-normalize-and-return
  (let* ((counts (division-normalization-return-steps q-steps r-steps))
         (steps (division-step-sum counts))
         (after (proof-advance steps world))
         (q-address (division-normalization-address nil world))
         (r-address (division-normalization-address t world))
         (r-done (proof-advance r-steps (proof-advance 4 (proof-advance q-steps (proof-advance 4 world))))))
    (implies (division-normalization-return-ready-p entry q-digits r-digits q-steps r-steps world)
             (and (proof-segment-p steps (list (proof-world-reg 30 entry)) world :cut after)
                  (proof-integer-view-p (division-magnitude q-digits) q-address
                                        (len (division-trim-limbs q-digits)) after)
                  (proof-integer-view-p (division-magnitude r-digits) r-address
                                        (len (division-trim-limbs r-digits)) after)
                  (equal (proof-world-reg 0 after) r-address)
                  (division-restore-output-p entry r-done after))))
  :hints (("Goal"
           :use ((:instance division-normalization-return-has-frame-and-cuts)
                 (:instance division-normalization-return-has-views)
                 (:instance division-advance-chain-sum
                            (counts (division-normalization-return-steps q-steps r-steps)))
                 (:instance division-chain-keeps-before-cuts
                            (counts (division-normalization-return-steps q-steps r-steps))
                            (cuts (list (proof-world-reg 30 entry))))
                 (:instance division-segment-from-cut-free-prefix
                            (count (division-step-sum (division-normalization-return-steps q-steps r-steps)))
                            (cuts (list (proof-world-reg 30 entry))))
                 (:instance division-integer-view-after-equal-memory
                            (value (division-magnitude q-digits))
                            (address (division-normalization-address nil world))
                            (count (len (division-trim-limbs q-digits)))
                            (before (proof-advance r-steps
                                     (proof-advance 4 (proof-advance q-steps (proof-advance 4 world)))))
                            (after (proof-advance (division-step-sum
                                                  (division-normalization-return-steps q-steps r-steps)) world)))
                 (:instance division-integer-view-after-equal-memory
                            (value (division-magnitude r-digits))
                            (address (division-normalization-address t world))
                            (count (len (division-trim-limbs r-digits)))
                            (before (proof-advance r-steps
                                     (proof-advance 4 (proof-advance q-steps (proof-advance 4 world)))))
                            (after (proof-advance (division-step-sum
                                                  (division-normalization-return-steps q-steps r-steps)) world))))
           :in-theory (disable division-normalization-return-ready-p division-normalize-setup-output-p
                               division-step-sum division-chain-before-cuts-p proof-integer-view-p
                               division-magnitude division-trim-limbs)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
