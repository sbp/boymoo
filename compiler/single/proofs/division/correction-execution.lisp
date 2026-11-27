(in-package "BOYMOO-PROOFS")

(include-book "position-machine")
(include-book "window-memory")
(include-book "window")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable ash floor mod proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-segment-p division-before-cuts-p division-instruction-sequence-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes)))

(defun division-window-low-phase-inputs-p (add-back digits divisor world)
  (and (consp divisor)
       (division-digits-p digits) (division-digits-p divisor)
       (equal (len digits) (len divisor))
       (equal (proof-world-reg 0 world) 0)
       (equal (proof-world-reg 1 world) 0)
       (equal (proof-world-reg 22 world) (* 8 (len divisor)))
       (division-window-carry-p add-back (proof-world-reg 15 world) 0)
       (proof-span-p (proof-world-reg 14 world) (* 8 (1+ (len divisor))))
       (division-window-loop-ready-p add-back digits divisor world)))

(defun division-window-low-phase-end (add-back divisor world)
  (proof-advance (* (division-window-loop-limb-steps add-back) (len divisor)) world))

(defun division-window-low-phase-output-p (add-back digits divisor world after)
  (let* ((count (len divisor))
         (address (proof-world-reg 14 world))
         (guess (proof-world-reg 15 world))
         (machine (proof-world-machine after))
         (steps (division-window-loop-limb-steps add-back)))
    (mv-let (written carry)
      (division-window-loop-digits add-back digits divisor guess 0)
      (and (equal (proof-world-pc after) (+ (* 4 steps) (proof-world-pc world)))
           (equal (proof-world-reg 0 after) (* 8 count))
           (equal (proof-world-reg 1 after) carry)
           (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
           (equal (proof-world-reg 14 after) address)
           (equal (proof-world-reg 15 after) guess)
           (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
           (equal (proof-world-reg 22 after) (* 8 count))
           (equal (division-read-limbs count address machine) written)
           (equal (division-window-high-limb after) (division-window-high-limb world))))))

(local
 (defthm division-window-phase-written-digits
   (implies (and (division-digits-p digits) (division-digits-p divisor)
                 (equal (len digits) (len divisor))
                 (division-window-carry-p add-back guess 0))
            (let ((written (mv-nth 0 (division-window-loop-digits add-back digits divisor guess 0))))
              (and (division-digits-p written) (equal (len written) (len divisor)))))
   :hints (("Goal"
            :cases (add-back)
            :use ((:instance division-add-back-limbs-correct (dividend digits) (carry 0))
                  (:instance division-subtract-limbs-correct (dividend digits) (carry 0)))
            :in-theory (disable division-add-back-limbs division-subtract-limbs)))
   :rule-classes nil))

(defthm division-window-low-phase-reads-back
  (implies (division-window-low-phase-inputs-p add-back digits divisor world)
           (division-window-low-phase-output-p
            add-back digits divisor world (division-window-low-phase-end add-back divisor world)))
  :hints (("Goal"
           :use ((:instance division-window-loop-correct (dividend digits))
                 (:instance division-window-phase-written-digits (guess (proof-world-reg 15 world)))
                 (:instance division-read-window-limb-writes
                            (address (proof-world-reg 14 world))
                            (before (proof-world-machine world))
                            (after (proof-world-machine (division-window-low-phase-end add-back divisor world)))
                            (digits (mv-nth 0 (division-window-loop-digits
                                               add-back digits divisor (proof-world-reg 15 world) 0))))
                 (:instance division-load-word-after-window-writes
                            (address (proof-world-reg 14 world)) (query (division-window-high-address world))
                            (before (proof-world-machine world))
                            (after (proof-world-machine (division-window-low-phase-end add-back divisor world)))
                            (digits (mv-nth 0 (division-window-loop-digits
                                               add-back digits divisor (proof-world-reg 15 world) 0)))))
           :in-theory (disable division-window-loop-ready-p division-window-loop-limb-steps
                               division-window-loop-digits division-write-window-limbs division-read-limbs)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-window-high-phase-target (add-back world)
  (if add-back (+ 16 (proof-world-pc world)) (division-subtract-high-target world)))

(defun division-window-phase-ready-p (add-back digits divisor world)
  (let* ((middle (division-window-low-phase-end add-back divisor world))
         (cuts (list (division-window-high-phase-target add-back middle))))
    (and (division-window-low-phase-inputs-p add-back digits divisor world)
         (if add-back
             (and (division-add-back-high-inputs-p middle)
                  (division-instruction-sequence-ready-p *division-add-back-high-instructions* cuts middle))
           (and (division-subtract-high-inputs-p middle)
                (division-instruction-sequence-ready-p *division-subtract-high-instructions* cuts middle))))))

(defun division-window-phase-steps (add-back divisor)
  (+ (* (division-window-loop-limb-steps add-back) (len divisor)) (if add-back 4 5)))

(local
 (defthm division-window-phase-starts-low-loop
   (implies (division-window-phase-ready-p add-back digits divisor world)
            (division-window-low-phase-inputs-p add-back digits divisor world))
   :hints (("Goal" :in-theory (disable division-window-low-phase-inputs-p
                                       division-add-back-high-inputs-p division-subtract-high-inputs-p)))
   :rule-classes nil))

(defun division-window-phase-digits (add-back digits high divisor guess)
  (if add-back
      (division-add-back-window digits high divisor)
    (division-subtract-window digits high divisor guess)))

(local
 (defthm division-high-phase-does-expected-store
   (implies (division-window-phase-ready-p add-back digits divisor world)
            (let* ((middle (division-window-low-phase-end add-back divisor world))
                   (after (proof-advance (division-window-phase-steps add-back divisor) world))
                   (high (if add-back
                             (division-added-back-high-limb middle)
                           (division-subtracted-high-limb middle))))
              (division-window-high-output-p high (division-window-high-phase-target add-back middle)
                                             middle after)))
   :hints (("Goal"
            :cases (add-back)
            :use ((:instance division-add-back-high-runs
                             (world (division-window-low-phase-end add-back divisor world)))
                  (:instance division-subtract-high-runs
                             (world (division-window-low-phase-end add-back divisor world)))
                  (:instance proof-advance-append
                             (prefix (* (division-window-loop-limb-steps add-back) (len divisor)))
                             (suffix (if add-back 4 5))))
            :in-theory (disable division-window-low-phase-inputs-p division-window-high-output-p
                                division-subtract-high-inputs-p division-add-back-high-inputs-p
                                division-subtracted-high-limb division-added-back-high-limb proof-advance-append)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-high-subtraction-wrap
   (implies (and (division-digit-p high) (division-digit-p carry))
            (equal (mod (- high carry) *division-radix*)
                   (+ (- high carry) (if (< high carry) *division-radix* 0))))
   :hints (("Goal"
            :cases ((< high carry))
            :use (:instance division-signed-remainder-unique
                            (a (- high carry)) (b *division-radix*)
                            (q (if (< high carry) -1 0))
                            (r (+ (- high carry) (if (< high carry) *division-radix* 0))))))))

(defthm division-window-phase-writes-digits
  (let* ((middle (division-window-low-phase-end add-back divisor world))
         (after (proof-advance (division-window-phase-steps add-back divisor) world))
         (address (proof-world-reg 14 world))
         (high (division-window-high-limb world))
         (guess (proof-world-reg 15 world)))
    (implies (division-window-phase-ready-p add-back digits divisor world)
             (mv-let (written top flag)
               (division-window-phase-digits add-back digits high divisor guess)
               (declare (ignore flag))
               (and (equal (division-read-limbs (len divisor) address (proof-world-machine after)) written)
                    (equal (division-window-high-limb after) top)
                    (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
                    (equal (proof-world-reg 14 after) address)
                    (equal (proof-world-reg 15 after) guess)
                    (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                    (equal (proof-world-reg 22 after) (* 8 (len divisor)))
                    (equal (proof-world-pc after) (division-window-high-phase-target add-back middle))))))
  :hints (("Goal"
           :cases (add-back)
           :use ((:instance division-window-low-phase-reads-back)
                 (:instance division-high-phase-does-expected-store)
                 (:instance division-high-subtraction-wrap
                            (high (division-window-high-limb world))
                            (carry (mv-nth 1 (division-subtract-limbs
                                               digits divisor (proof-world-reg 15 world) 0))))
                 (:instance division-limbs-after-disjoint-word-write
                            (count (len divisor)) (address (proof-world-reg 14 world))
                            (target (division-window-high-address
                                     (division-window-low-phase-end add-back divisor world)))
                            (before (proof-world-machine (division-window-low-phase-end add-back divisor world)))
                            (after (proof-world-machine
                                    (proof-advance (division-window-phase-steps add-back divisor) world)))
                            (value (if add-back
                                       (division-added-back-high-limb
                                        (division-window-low-phase-end add-back divisor world))
                                     (division-subtracted-high-limb
                                      (division-window-low-phase-end add-back divisor world))))))
           :in-theory (disable division-window-loop-ready-p division-read-limbs
                               division-add-back-limbs division-subtract-limbs division-high-subtraction-wrap)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-window-phase-preserves-disjoint-limbs
  (let* ((base (proof-world-reg 14 world))
         (bytes (* 8 (1+ (len divisor))))
         (after (proof-advance (division-window-phase-steps add-back divisor) world))
         (before-machine (proof-world-machine world))
         (after-machine (proof-world-machine after))
         (query-bytes (* 8 count)))
    (implies (and (division-window-phase-ready-p add-back digits divisor world)
                  (natp count) (proof-span-p query query-bytes)
                  (proof-disjoint-p base (+ base bytes) query (+ query query-bytes)))
             (equal (division-read-limbs count query after-machine)
                    (division-read-limbs count query before-machine))))
  :hints (("Goal"
           :use ((:instance division-window-phase-starts-low-loop)
                 (:instance division-window-low-phase-reads-back)
                 (:instance division-window-loop-correct (dividend digits))
                 (:instance division-window-phase-written-digits (guess (proof-world-reg 15 world)))
                 (:instance division-high-phase-does-expected-store)
                 (:instance division-limbs-after-disjoint-window-writes
                            (address query) (target (proof-world-reg 14 world))
                            (written (mv-nth 0 (division-window-loop-digits
                                                add-back digits divisor (proof-world-reg 15 world) 0)))
                            (before (proof-world-machine world))
                            (after (proof-world-machine (division-window-low-phase-end add-back divisor world))))
                 (:instance division-limbs-after-disjoint-word-write
                            (address query)
                            (target (division-window-high-address
                                     (division-window-low-phase-end add-back divisor world)))
                            (value (if add-back
                                       (division-added-back-high-limb (division-window-low-phase-end add-back divisor world))
                                     (division-subtracted-high-limb (division-window-low-phase-end add-back divisor world))))
                            (before (proof-world-machine (division-window-low-phase-end add-back divisor world)))
                            (after (proof-world-machine
                                    (proof-advance (division-window-phase-steps add-back divisor) world)))))
           :in-theory (disable division-window-phase-ready-p division-window-loop-ready-p
                               division-window-loop-limb-steps division-window-loop-digits
                               division-window-high-phase-target division-window-high-limb
                               division-subtracted-high-limb division-added-back-high-limb
                               division-read-limbs division-write-window-limbs)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-window-borrows-p (digits divisor world)
  (mv-let (written top borrowed)
    (division-subtract-window digits (division-window-high-limb world) divisor (proof-world-reg 15 world))
    (declare (ignore written top))
    borrowed))

(defun division-window-correction-steps (digits divisor world)
  (+ (division-window-phase-steps nil divisor)
     (if (division-window-borrows-p digits divisor world)
         (+ 3 (division-window-phase-steps t divisor))
       0)))

(defun division-window-correction-ready-p (digits divisor world)
  (let* ((sub-end (proof-advance (division-window-phase-steps nil divisor) world))
         (add-start (proof-advance 3 sub-end)))
    (mv-let (subtracted top borrowed)
      (division-subtract-window digits (division-window-high-limb world) divisor (proof-world-reg 15 world))
      (declare (ignore top))
      (and (division-window-phase-ready-p nil digits divisor world)
           (or (not borrowed)
               (and (division-ordinary-world-p sub-end)
                    (posp (proof-world-reg 15 sub-end))
                    (unsigned-byte-p 64 (+ 12 (proof-world-pc sub-end)))
                    (division-instruction-sequence-ready-p
                     *division-add-back-setup-instructions* (list (+ 12 (proof-world-pc sub-end))) sub-end)
                    (division-window-phase-ready-p t subtracted divisor add-start)))))))

(local
 (defthm division-subtracted-window-goes-to-its-branch
   (let* ((after (proof-advance (division-window-phase-steps nil divisor) world))
          (offset (if (division-window-borrows-p digits divisor world)
                      76 (+ 56 *division-subtract-high-to-store*))))
     (implies (division-window-phase-ready-p nil digits divisor world)
              (equal (proof-world-pc after) (+ (proof-world-pc world) offset))))
   :hints (("Goal"
            :use ((:instance division-window-low-phase-reads-back (add-back nil))
                  (:instance division-window-phase-writes-digits (add-back nil)))
            :in-theory (disable division-subtract-limbs division-read-limbs
                                division-window-low-phase-inputs-p division-subtract-high-inputs-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-add-back-setup-keeps-high-limb
   (implies (division-add-back-setup-output-p world after)
            (equal (division-window-high-limb after) (division-window-high-limb world)))
   :hints (("Goal" :in-theory (enable proof-load-word)))))

(local
 (defthm division-add-back-window-reaches-store-offset
   (implies (division-window-phase-ready-p t digits divisor world)
            (equal (proof-world-pc (proof-advance (division-window-phase-steps t divisor) world))
                   (+ 56 (proof-world-pc world))))
   :hints (("Goal"
            :use ((:instance division-window-phase-starts-low-loop (add-back t))
                  (:instance division-window-low-phase-reads-back (add-back t))
                  (:instance division-window-phase-writes-digits (add-back t)))
            :in-theory (disable division-window-phase-ready-p division-window-low-phase-inputs-p
                                division-add-back-window division-add-back-limbs division-read-limbs
                                division-window-high-limb)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defun division-corrected-window-output-p (digits divisor world after)
  (let* ((address (proof-world-reg 14 world))
         (high (division-window-high-limb world))
         (guess (proof-world-reg 15 world)))
    (mv-let (quotient written top)
      (division-correct-window digits high divisor guess)
      (and (equal (proof-world-pc after) (+ 144 (proof-world-pc world)))
           (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
           (equal (proof-world-reg 14 after) address)
           (equal (proof-world-reg 15 after) quotient)
           (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
           (equal (proof-world-reg 22 after) (* 8 (len divisor)))
           (equal (division-read-limbs (len divisor) address (proof-world-machine after)) written)
           (equal (division-window-high-limb after) top)))))

(defthm division-window-correction-reaches-store
  (implies (division-window-correction-ready-p digits divisor world)
           (division-corrected-window-output-p
            digits divisor world (proof-advance (division-window-correction-steps digits divisor world) world)))
  :hints (("Goal"
           :cases ((division-window-borrows-p digits divisor world))
           :use ((:instance division-window-phase-writes-digits (add-back nil))
                 (:instance division-subtracted-window-goes-to-its-branch)
                 (:instance division-add-back-setup-runs
                            (world (proof-advance (division-window-phase-steps nil divisor) world)))
                 (:instance division-add-back-setup-keeps-high-limb
                            (world (proof-advance (division-window-phase-steps nil divisor) world))
                            (after (proof-advance 3 (proof-advance (division-window-phase-steps nil divisor) world))))
                 (:instance division-window-phase-writes-digits
                            (add-back t)
                            (digits (mv-nth 0 (division-subtract-window
                                               digits (division-window-high-limb world)
                                               divisor (proof-world-reg 15 world))))
                            (world (proof-advance 3 (proof-advance (division-window-phase-steps nil divisor) world))))
                 (:instance division-add-back-window-reaches-store-offset
                            (digits (mv-nth 0 (division-subtract-window
                                               digits (division-window-high-limb world)
                                               divisor (proof-world-reg 15 world))))
                            (world (proof-advance 3 (proof-advance (division-window-phase-steps nil divisor) world))))
                 (:instance proof-advance-append
                            (prefix (division-window-phase-steps nil divisor))
                            (suffix (+ 3 (division-window-phase-steps t divisor))))
                 (:instance proof-advance-append
                            (world (proof-advance (division-window-phase-steps nil divisor) world))
                            (prefix 3) (suffix (division-window-phase-steps t divisor))))
           :in-theory (disable division-window-phase-ready-p division-window-high-limb
                               division-subtract-window division-add-back-window
                               division-read-limbs proof-advance-append division-add-back-setup-keeps-high-limb)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-window-correction-preserves-disjoint-limbs
  (let* ((base (proof-world-reg 14 world))
         (bytes (* 8 (1+ (len divisor))))
         (after (proof-advance (division-window-correction-steps digits divisor world) world)))
    (implies (and (division-window-correction-ready-p digits divisor world)
                  (natp count) (proof-span-p query (* 8 count))
                  (proof-disjoint-p base (+ base bytes) query (+ query (* 8 count))))
             (equal (division-read-limbs count query (proof-world-machine after))
                    (division-read-limbs count query (proof-world-machine world)))))
  :hints (("Goal"
           :cases ((division-window-borrows-p digits divisor world))
           :use ((:instance division-window-phase-writes-digits (add-back nil))
                 (:instance division-window-phase-preserves-disjoint-limbs (add-back nil))
                 (:instance division-add-back-setup-runs
                            (world (proof-advance (division-window-phase-steps nil divisor) world)))
                 (:instance division-window-phase-preserves-disjoint-limbs
                            (add-back t)
                            (digits (mv-nth 0 (division-subtract-window
                                               digits (division-window-high-limb world)
                                               divisor (proof-world-reg 15 world))))
                            (world (proof-advance 3 (proof-advance (division-window-phase-steps nil divisor) world))))
                 (:instance division-read-limbs-from-same-memory
                            (count count) (address query)
                            (first (proof-world-machine (proof-advance (division-window-phase-steps nil divisor) world)))
                            (second (proof-world-machine
                                     (proof-advance 3 (proof-advance (division-window-phase-steps nil divisor) world)))))
                 (:instance proof-advance-append
                            (prefix (division-window-phase-steps nil divisor))
                            (suffix (+ 3 (division-window-phase-steps t divisor))))
                 (:instance proof-advance-append
                            (prefix 3) (suffix (division-window-phase-steps t divisor))
                            (world (proof-advance (division-window-phase-steps nil divisor) world))))
           :in-theory (disable division-window-phase-ready-p division-subtract-window
                               division-window-high-limb division-read-limbs proof-advance-append)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-correction-starts-with-subtraction
   (implies (division-window-correction-ready-p digits divisor world)
            (division-window-phase-ready-p nil digits divisor world))
   :hints (("Goal" :in-theory (disable division-window-phase-ready-p division-subtract-window)))
   :rule-classes nil))

(local
 (defthm division-subtraction-high-load-is-a-limb
   (implies (division-window-phase-ready-p nil digits divisor world)
            (division-digit-p (division-window-high-limb (division-window-low-phase-end nil divisor world))))
   :hints (("Goal" :in-theory (disable division-window-low-phase-inputs-p division-window-high-limb
                                       division-subtract-high-target division-window-high-address)))
   :rule-classes nil))

(local
 (defthm division-window-correction-ready-gives-digits
   (implies (division-window-correction-ready-p digits divisor world)
            (and (division-digits-p digits) (division-digits-p divisor)
                 (equal (len digits) (len divisor))
                 (division-digit-p (division-window-high-limb world))))
   :hints (("Goal"
            :use ((:instance division-correction-starts-with-subtraction)
                  (:instance division-window-phase-starts-low-loop (add-back nil))
                  (:instance division-window-low-phase-reads-back (add-back nil))
                  (:instance division-subtraction-high-load-is-a-limb))
            :in-theory (disable division-window-correction-ready-p division-window-phase-ready-p
                                division-window-loop-ready-p division-window-high-limb division-read-limbs
                                division-window-loop-digits proof-span-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-window-magnitude-at-zero-top
   (equal (division-window-magnitude digits 0) (division-magnitude digits))))

(defthm division-machine-normalized-window-result
  (let* ((after (proof-advance (division-window-correction-steps digits divisor world) world))
         (remainder (division-read-limbs (len divisor) (proof-world-reg 14 world)
                                         (proof-world-machine after)))
         (value (division-magnitude remainder))
         (b (division-magnitude divisor))
         (high (division-window-high-limb world)))
    (implies (and (division-window-correction-ready-p digits divisor world)
                  (division-window-p head lead next digit a-tail b-tail scale)
                  (equal (proof-world-reg 15 world) (division-two-limb-estimate head lead next digit))
                  (equal (division-window-magnitude digits high)
                         (division-prefix-value (+ (* *division-radix* head) digit) a-tail scale))
                  (equal b (division-prefix-value (+ (* *division-radix* lead) next) b-tail scale)))
             (and (division-digit-p (proof-world-reg 15 after))
                  (division-digits-p remainder)
                  (< value b)
                  (equal (+ (* b (proof-world-reg 15 after)) value) (division-window-magnitude digits high))
                  (equal (division-window-high-limb after) 0)
                  (equal (proof-world-pc after) (+ 144 (proof-world-pc world))))))
  :hints (("Goal"
           :use ((:instance division-window-correction-reaches-store)
                 (:instance division-window-correction-ready-gives-digits)
                 (:instance division-normalized-window-iteration (high (division-window-high-limb world))))
           :in-theory (disable division-window-correction-ready-p division-window-high-limb
                               division-subtract-window division-correct-window division-window-p
                               division-prefix-value division-read-limbs division-magnitude division-window-magnitude
                               division-two-limb-estimate division-window-correction-steps)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
