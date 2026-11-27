(in-package "BOYMOO-PROOFS")

(include-book "normalization-machine")
(include-book "right-shift")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-right-shift-exit-instructions*
  (division-runtime-block "rt:z-divide-shift-right" 8 1))
(defconst *division-right-shift-to-normalize*
  (- (division-runtime-offset "rt:z-divide-normalize")
     (+ 32 (division-runtime-offset "rt:z-divide-shift-right"))))

(local
 (in-theory (disable floor mod ash expt proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-load-word proof-segment-p
                     division-before-cuts-p division-instruction-sequence-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-sp)))

(defun division-right-shift-exit-target (world)
  (+ *division-right-shift-to-normalize* (proof-world-pc world)))

(defun division-right-shift-exit-ready-p (world)
  (and (division-ordinary-world-p world)
       (not (proof-world-stop world))
       (unsigned-byte-p 64 (division-right-shift-exit-target world))
       (division-instruction-sequence-ready-p *division-right-shift-exit-instructions*
                                              (list (division-right-shift-exit-target world)) world)))

(defun division-right-shift-exit-output-p (world after)
  (and (equal (proof-world-pc after) (division-right-shift-exit-target world))
       (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (not (proof-world-stop after))))

(local
 (defthm division-right-shift-exit-effects
   (implies (and (division-ordinary-world-p world) (not (proof-world-stop world))
                 (unsigned-byte-p 64 (division-right-shift-exit-target world)))
            (division-right-shift-exit-output-p
             world (division-instruction-sequence *division-right-shift-exit-instructions* world)))
   :rule-classes nil))

(defthm division-right-shift-exit-reaches-normalize
  (implies (division-right-shift-exit-ready-p world)
           (division-right-shift-exit-output-p world (proof-advance 1 world)))
  :hints (("Goal"
           :use ((:instance division-right-shift-exit-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-right-shift-exit-instructions*)
                            (cuts (list (division-right-shift-exit-target world)))))
           :in-theory (disable division-right-shift-exit-target division-right-shift-exit-output-p
                               division-instruction-sequence)))
  :rule-classes nil)

(defun division-unscale-loop-start (world)
  (proof-advance 6 world))

(defun division-unscale-loop-end (digits world)
  (proof-advance (* 8 (len digits)) (division-unscale-loop-start world)))

(defun division-unscale-steps (digits world)
  (if (equal (division-saved-normalization-shift world) 0) 4 (+ 7 (* 8 (len digits)))))

(defun division-unscale-target (world)
  (+ *division-undo-to-normalize-offset* (proof-world-pc world)))

(defun division-unscale-ready-p (positions digits world)
  (let* ((branch (division-unscale-loop-end digits world))
         (start (division-unscale-loop-start world))
         (r-address (proof-world-reg 19 world))
         (q-address (proof-world-reg 21 world))
         (r-bytes (* 8 (len digits)))
         (q-bytes (* 8 positions))
         (shift (division-saved-normalization-shift world))
         (cuts (list (division-unscale-target world))))
    (and (posp positions) (consp digits) (division-digits-p digits)
         (not (proof-world-stop world))
         (proof-span-p r-address r-bytes) (proof-span-p q-address q-bytes)
         (proof-disjoint-p r-address (+ r-address r-bytes) q-address (+ q-address q-bytes))
         (equal digits (division-read-limbs (len digits) r-address (proof-world-machine world)))
         (equal (proof-world-reg 22 world) r-bytes)
         (equal (+ 8 (- (division-saved-dividend-bytes world) r-bytes)) q-bytes)
         (division-undo-normalization-inputs-p world)
         (division-instruction-sequence-ready-p (division-undo-normalization-instructions world)
                                                (list (division-undo-normalization-target world)) world)
         (or (equal shift 0)
             (and (division-right-shift-prefix-ready-p digits 0 start)
                  (division-right-shift-exit-ready-p branch)))
         (division-before-cuts-p (division-unscale-steps digits world) cuts world))))

(local
 (defthm division-unscale-setup-values
   (implies (division-unscale-ready-p positions digits world)
            (let* ((skip (equal (division-saved-normalization-shift world) 0))
                   (after (proof-advance (if skip 4 6) world)))
              (division-undo-normalization-output-p world after)))
   :hints (("Goal"
            :use (:instance division-undo-normalization-setup-runs)
            :in-theory (disable division-read-limbs division-right-shift-prefix-ready-p
                                division-right-shift-exit-ready-p division-undo-normalization-output-p
                                division-unscale-loop-end division-undo-normalization-inputs-p)
            :cases ((equal (division-saved-normalization-shift world) 0))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-unscale-nonzero-advance
   (implies (not (equal (division-saved-normalization-shift world) 0))
            (equal (proof-advance (division-unscale-steps digits world) world)
                   (proof-advance 1 (division-unscale-loop-end digits world))))
   :hints (("Goal"
            :use ((:instance proof-advance-append
                             (prefix 6) (suffix (+ 1 (* 8 (len digits)))))
                  (:instance proof-advance-append
                             (prefix (* 8 (len digits))) (suffix 1) (world (division-unscale-loop-start world))))
            :in-theory (disable proof-advance-append)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-unscale-nonzero-loop
   (let* ((end (division-unscale-loop-end digits world))
          (r-address (proof-world-reg 19 world))
          (q-address (proof-world-reg 21 world))
          (q-digits (division-read-limbs positions q-address (proof-world-machine end)))
          (r-digits (division-read-limbs (len digits) r-address (proof-world-machine end)))
          (shift (division-saved-normalization-shift world)))
     (implies (and (division-unscale-ready-p positions digits world) (not (equal shift 0)))
              (and (division-digits-p r-digits)
                   (equal (division-magnitude r-digits) (floor (division-magnitude digits) (expt 2 shift)))
                   (equal q-digits (division-read-limbs positions q-address (proof-world-machine world)))
                   (equal (proof-world-reg 9 end) (* 8 positions))
                   (equal (proof-world-reg 19 end) r-address)
                   (equal (proof-world-reg 21 end) q-address)
                   (equal (proof-world-reg 22 end) (* 8 (len digits)))
                   (equal (proof-world-pc end) (+ 56 (proof-world-pc world))))))
   :hints (("Goal"
            :use ((:instance division-unscale-setup-values)
                  (:instance division-right-shift-loop-writes-unscaled-value (world (division-unscale-loop-start world)))
                  (:instance division-right-shift-prefix-writes-limbs (pending 0) (world (division-unscale-loop-start world)))
                  (:instance division-right-shift-preserves-disjoint-limbs
                             (query (proof-world-reg 21 world)) (count positions) (world (division-unscale-loop-start world)))
                  (:instance division-read-limbs-from-same-memory
                             (count positions) (address (proof-world-reg 21 world))
                             (first (proof-world-machine (division-unscale-loop-start world)))
                             (second (proof-world-machine world))))
            :in-theory (disable division-read-limbs division-right-shift-prefix-ready-p
                                division-write-quotient-limbs division-right-shift-digits
                                division-right-shift-exit-ready-p
                                division-magnitude division-digits-p division-saved-normalization-shift)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-unscales-remainder-and-keeps-quotient
  (let* ((steps (division-unscale-steps digits world))
         (cuts (list (division-unscale-target world)))
         (after (proof-advance steps world))
         (r-address (proof-world-reg 19 world))
         (q-address (proof-world-reg 21 world))
         (r-digits (division-read-limbs (len digits) r-address (proof-world-machine after)))
         (q-digits (division-read-limbs positions q-address (proof-world-machine after)))
         (shift (division-saved-normalization-shift world)))
    (implies (division-unscale-ready-p positions digits world)
             (and (proof-segment-p steps cuts world :cut after)
                  (equal (proof-world-reg 9 after) (* 8 positions))
                  (equal (proof-world-reg 19 after) r-address)
                  (equal (proof-world-reg 21 after) q-address)
                  (equal (proof-world-reg 22 after) (* 8 (len digits)))
                  (division-digits-p r-digits)
                  (equal (division-magnitude r-digits) (floor (division-magnitude digits) (expt 2 shift)))
                  (equal q-digits (division-read-limbs positions q-address (proof-world-machine world))))))
  :hints (("Goal"
           :cases ((equal (division-saved-normalization-shift world) 0))
           :use ((:instance division-unscale-setup-values)
                 (:instance division-unscale-nonzero-loop)
                 (:instance division-unscale-nonzero-advance)
                 (:instance division-right-shift-exit-reaches-normalize (world (division-unscale-loop-end digits world)))
                 (:instance division-segment-from-cut-free-prefix
                            (count (division-unscale-steps digits world)) (cuts (list (division-unscale-target world))))
                 (:instance division-quotient-unique (a (division-magnitude digits)) (b 1)
                            (q (division-magnitude digits)) (r 0))
                 (:instance division-read-limbs-from-same-memory
                            (count positions) (address (proof-world-reg 21 world))
                            (first (proof-world-machine (proof-advance (division-unscale-steps digits world) world)))
                            (second (if (equal (division-saved-normalization-shift world) 0)
                                        (proof-world-machine world)
                                      (proof-world-machine (division-unscale-loop-end digits world)))))
                 (:instance division-read-limbs-from-same-memory
                            (count (len digits)) (address (proof-world-reg 19 world))
                            (first (proof-world-machine (proof-advance (division-unscale-steps digits world) world)))
                            (second (if (equal (division-saved-normalization-shift world) 0)
                                        (proof-world-machine world)
                                      (proof-world-machine (division-unscale-loop-end digits world))))))
           :in-theory (disable division-read-limbs division-undo-normalization-inputs-p
                               division-right-shift-exit-ready-p division-right-shift-prefix-ready-p
                               division-magnitude division-digits-p division-saved-normalization-shift
                               division-unscale-loop-end)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
