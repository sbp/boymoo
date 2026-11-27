(in-package "BOYMOO-PROOFS")

(include-book "scale-setup")
(include-book "long-traversal")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable ash floor mod expt proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-load-word proof-segment-p
                     division-before-cuts-p division-instruction-sequence-ready-p
                     division-left-shift-call-ready-p division-left-shift-call-steps
                     division-left-shift-limbs division-write-window-limbs division-read-limbs
                     division-read-limbs-view-magnitude division-magnitude
                     boymoo-model::a64-sp boymoo-model::a64-memory boymoo-model::a64-write-bytes)))

(defun division-long-scale-counts (dividend divisor)
  (list 7 5 (division-left-shift-call-steps dividend) 6 (division-left-shift-call-steps divisor) 5))

(defun division-long-scale-stage (stage dividend divisor world)
  (division-advance-chain (take stage (division-long-scale-counts dividend divisor)) world))

(defun division-long-scale-steps (dividend divisor)
  (division-step-sum (division-long-scale-counts dividend divisor)))

(defun division-long-scale-shift (divisor)
  (division-normalization-shift (division-leading-limb divisor)))

(defun division-long-scale-ready-p (dividend divisor world)
  (let* ((choose (division-long-scale-stage 1 dividend divisor world))
         (a-call (division-long-scale-stage 2 dividend divisor world))
         (a-return (division-long-scale-stage 3 dividend divisor world))
         (b-call (division-long-scale-stage 4 dividend divisor world))
         (b-return (division-long-scale-stage 5 dividend divisor world))
         (r-address (proof-world-reg 19 world))
         (v-address (proof-world-reg 20 world))
         (a-bytes (* 8 (len dividend)))
         (b-bytes (* 8 (len divisor))))
    (and (<= 2 (len divisor)) (<= (len divisor) (len dividend))
         (division-digits-p dividend) (division-digits-p divisor)
         (equal (division-unnormalized-leading-limb world) (division-leading-limb divisor))
         (equal (proof-world-reg 9 world) a-bytes)
         (equal (proof-world-reg 22 world) b-bytes)
         (proof-span-p r-address (+ 8 a-bytes)) (proof-span-p v-address b-bytes)
         (proof-disjoint-p r-address (+ r-address 8 a-bytes) v-address (+ v-address b-bytes))
         (division-choose-normalization-inputs-p world)
         (division-instruction-sequence-ready-p
          *division-choose-normalization-instructions* (list (+ 28 (proof-world-pc world))) world)
         (division-scale-call-inputs-p nil choose)
         (division-instruction-sequence-ready-p
          *division-first-left-shift-call-instructions*
          (list (+ (division-scale-call-offset nil) (proof-world-pc choose))) choose)
         (division-left-shift-call-ready-p dividend a-call)
         (division-scale-call-inputs-p t a-return)
         (division-instruction-sequence-ready-p
          *division-second-left-shift-call-instructions*
          (list (+ (division-scale-call-offset t) (proof-world-pc a-return))) a-return)
         (division-left-shift-call-ready-p divisor b-call)
         (division-scale-window-setup-inputs-p b-return)
         (division-instruction-sequence-ready-p
          *division-scale-window-setup-instructions* (list (+ 20 (proof-world-pc b-return))) b-return))))

(local
 (defun division-scale-shift-value-p (digits shift target before after)
   (mv-let (written carry)
     (division-left-shift-limbs digits 0 (expt 2 shift))
     (and (equal (proof-world-reg 6 after) carry)
          (equal (boymoo-model::a64-memory (proof-world-machine after))
                 (division-write-window-limbs written target (boymoo-model::a64-memory (proof-world-machine before))))
          (equal (division-read-limbs (len digits) target (proof-world-machine after)) written)))))

(local
 (defthm division-long-scale-dividend-shift
   (let* ((choose (division-long-scale-stage 1 dividend divisor world))
          (call (division-long-scale-stage 2 dividend divisor world))
          (returned (division-long-scale-stage 3 dividend divisor world))
          (shift (division-long-scale-shift divisor)))
     (implies (division-long-scale-ready-p dividend divisor world)
              (and (division-scale-shift-value-p dividend shift (proof-world-reg 19 world) call returned)
                   (equal (proof-world-reg 9 returned) (proof-world-reg 9 world))
                   (equal (proof-world-reg 10 returned) shift)
                   (equal (proof-world-reg 19 returned) (proof-world-reg 19 world))
                   (equal (proof-world-reg 20 returned) (proof-world-reg 20 world))
                   (equal (proof-world-reg 21 returned) (proof-world-reg 21 world))
                   (equal (proof-world-reg 22 returned) (proof-world-reg 22 world))
                   (equal (proof-world-reg 8 returned) (proof-world-reg 8 choose))
                   (equal (proof-world-pc returned) (+ 48 (proof-world-pc world))))))
   :hints (("Goal"
            :use ((:instance division-chooses-and-saves-clz-shift)
                  (:instance division-scale-shift-call-passes-limb-spans (second nil) (world (proof-advance 7 world)))
                  (:instance division-left-shift-call-returns-shifted-limbs (digits dividend)
                             (world (division-long-scale-stage 2 dividend divisor world))))
            :in-theory (disable division-choose-normalization-inputs-p division-scale-call-inputs-p
                                division-scale-window-setup-inputs-p
                                division-unnormalized-leading-limb division-normalization-shift)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-scale-divisor-shift
   (let* ((a-return (division-long-scale-stage 3 dividend divisor world))
          (b-call (division-long-scale-stage 4 dividend divisor world))
          (b-return (division-long-scale-stage 5 dividend divisor world))
          (after (division-long-scale-stage 6 dividend divisor world))
          (shift (division-long-scale-shift divisor)))
     (implies (division-long-scale-ready-p dividend divisor world)
              (and (division-scale-shift-value-p divisor shift (proof-world-reg 20 world) b-call b-return)
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                   (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
                   (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                   (equal (proof-world-reg 22 after) (* 8 (len divisor)))
                   (equal (proof-world-reg 11 after) (division-scaled-divisor-word 8 b-return))
                   (equal (proof-world-reg 12 after) (division-scaled-divisor-word 16 b-return))
                   (equal (proof-world-reg 13 after) (* 8 (- (len dividend) (len divisor))))
                   (equal (proof-world-pc after) (+ 92 (proof-world-pc world)))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory (proof-world-machine b-return)))
                   (equal (boymoo-model::a64-memory (proof-world-machine b-call))
                          (boymoo-model::a64-write-bytes
                           8 (+ (proof-world-reg 19 world) (* 8 (len dividend)))
                           (proof-world-reg 6 a-return) (boymoo-model::a64-memory (proof-world-machine a-return)))))))
   :hints (("Goal"
            :use ((:instance division-long-scale-dividend-shift)
                  (:instance division-scale-shift-call-passes-limb-spans (second t)
                             (world (division-long-scale-stage 3 dividend divisor world)))
                  (:instance division-left-shift-call-returns-shifted-limbs (digits divisor)
                             (world (division-long-scale-stage 4 dividend divisor world)))
                  (:instance division-scale-enters-first-window (world (division-long-scale-stage 5 dividend divisor world))))
            :in-theory (disable division-choose-normalization-inputs-p division-scale-call-inputs-p
                                division-scale-window-setup-inputs-p division-scaled-divisor-word
                                division-unnormalized-leading-limb division-normalization-shift)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defun division-long-scale-position-count (dividend divisor)
  (+ 1 (- (len dividend) (len divisor))))

(defun division-long-scaled-divisor (dividend divisor world)
  (let ((after (division-long-scale-stage 6 dividend divisor world)))
    (division-read-limbs (len divisor) (proof-world-reg 20 after) (proof-world-machine after))))

(local
 (defthm division-long-scale-shift-bound
   (implies (division-long-scale-ready-p dividend divisor world)
            (and (posp (division-leading-limb divisor))
                 (division-digit-p (division-leading-limb divisor))
                 (natp (division-long-scale-shift divisor))
                 (< (division-long-scale-shift divisor) 32)))
   :hints (("Goal"
            :use (:instance division-clz-shift-bounds (leading (division-leading-limb divisor)))
            :in-theory (disable division-normalization-shift division-leading-limb division-unnormalized-leading-limb
                                division-scale-call-inputs-p division-scale-window-setup-inputs-p division-digits-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-scale-divisor-value
   (let* ((shift (division-long-scale-shift divisor))
          (scale (expt 2 shift))
          (result (division-long-scaled-divisor dividend divisor world)))
     (implies (division-long-scale-ready-p dividend divisor world)
              (and (division-digits-p result)
                   (division-leading-digit-p (division-leading-limb result))
                   (equal (len result) (len divisor))
                   (equal (division-magnitude result) (* scale (division-magnitude divisor))))))
   :hints (("Goal"
            :use ((:instance division-long-scale-shift-bound)
                  (:instance division-long-scale-divisor-shift)
                  (:instance division-left-shift-normalizes-divisor
                             (digits divisor) (scale (expt 2 (division-long-scale-shift divisor))) (carry 0))
                  (:instance division-left-shift-limbs-correct
                             (digits divisor) (scale (expt 2 (division-long-scale-shift divisor))) (carry 0))
                  (:instance division-limb-scale-fits (shift (division-long-scale-shift divisor)))
                  (:instance division-read-limbs-from-same-memory
                             (count (len divisor)) (address (proof-world-reg 20 world))
                             (first (proof-world-machine (division-long-scale-stage 5 dividend divisor world)))
                             (second (proof-world-machine (division-long-scale-stage 6 dividend divisor world)))))
            :in-theory (disable division-choose-normalization-inputs-p division-scale-call-inputs-p
                                division-scale-window-setup-inputs-p division-leading-digit-p
                                division-leading-limb division-normalization-shift division-digits-p
                                division-scaled-divisor-word division-unnormalized-leading-limb)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-read-fitted-word
   (implies (and (proof-span-p address 8) (unsigned-byte-p 64 word)
                 (equal (boymoo-model::a64-memory after)
                        (boymoo-model::a64-write-bytes 8 address word (boymoo-model::a64-memory before))))
            (equal (proof-load-word address after) word))
   :hints (("Goal"
            :use (:instance division-read-after-fitting-write (count 8) (value word)
                            (memory (boymoo-model::a64-memory before)))
            :in-theory (e/d (proof-load-word)
                            (division-read-after-fitting-write boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(local
 (defthm division-long-scale-buffer-spans
   (let* ((a-bytes (* 8 (len dividend)))
          (b-bytes (* 8 (len divisor)))
          (r-address (proof-world-reg 19 world))
          (v-address (proof-world-reg 20 world))
          (high (+ r-address a-bytes))
          (v-end (+ v-address b-bytes)))
     (implies (division-long-scale-ready-p dividend divisor world)
              (and (division-digits-p dividend) (division-digits-p divisor)
                   (proof-span-p r-address a-bytes)
                   (proof-span-p high 8)
                   (proof-span-p v-address b-bytes)
                   (proof-disjoint-p r-address high v-address v-end)
                   (proof-disjoint-p high (+ high 8) v-address v-end))))
   :hints (("Goal"
            :in-theory (disable division-long-scale-stage division-choose-normalization-inputs-p
                                division-scale-call-inputs-p division-scale-window-setup-inputs-p
                                division-unnormalized-leading-limb division-leading-limb division-digits-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-scale-dividend-span
   (let* ((a-return (division-long-scale-stage 3 dividend divisor world))
          (after (division-long-scale-stage 6 dividend divisor world))
          (address (proof-world-reg 19 world))
          (head-address (+ address (* 8 (len dividend))))
          (scale (expt 2 (division-long-scale-shift divisor)))
          (shifted (mv-nth 0 (division-left-shift-limbs dividend 0 scale))))
     (implies (division-long-scale-ready-p dividend divisor world)
              (and (equal (division-read-limbs (len dividend) address (proof-world-machine after)) shifted)
                   (equal (proof-load-word head-address (proof-world-machine after)) (proof-world-reg 6 a-return)))))
   :hints (("Goal"
            :use ((:instance division-long-scale-dividend-shift)
                  (:instance division-long-scale-divisor-shift)
                  (:instance division-long-scale-buffer-spans)
                  (:instance division-long-scale-shift-bound)
                  (:instance division-limb-scale-fits (shift (division-long-scale-shift divisor)))
                  (:instance division-left-shift-limbs-correct
                             (digits divisor) (carry 0) (scale (expt 2 (division-long-scale-shift divisor))))
                  (:instance division-world-register-in-word
                             (register 6) (world (division-long-scale-stage 3 dividend divisor world)))
                  (:instance division-long-read-fitted-word
                             (address (+ (proof-world-reg 19 world) (* 8 (len dividend))))
                             (word (proof-world-reg 6 (division-long-scale-stage 3 dividend divisor world)))
                             (before (proof-world-machine (division-long-scale-stage 3 dividend divisor world)))
                             (after (proof-world-machine (division-long-scale-stage 4 dividend divisor world))))
                  (:instance division-limbs-after-disjoint-word-write
                             (count (len dividend)) (address (proof-world-reg 19 world))
                             (target (+ (proof-world-reg 19 world) (* 8 (len dividend))))
                             (value (proof-world-reg 6 (division-long-scale-stage 3 dividend divisor world)))
                             (before (proof-world-machine (division-long-scale-stage 3 dividend divisor world)))
                             (after (proof-world-machine (division-long-scale-stage 4 dividend divisor world))))
                  (:instance division-limbs-after-disjoint-window-writes
                             (count (len dividend)) (address (proof-world-reg 19 world)) (target (proof-world-reg 20 world))
                             (written (mv-nth 0 (division-left-shift-limbs
                                                divisor 0 (expt 2 (division-long-scale-shift divisor)))))
                             (before (proof-world-machine (division-long-scale-stage 4 dividend divisor world)))
                             (after (proof-world-machine (division-long-scale-stage 6 dividend divisor world))))
                  (:instance division-load-word-after-window-writes
                             (address (proof-world-reg 20 world))
                             (query (+ (proof-world-reg 19 world) (* 8 (len dividend))))
                             (digits (mv-nth 0 (division-left-shift-limbs
                                               divisor 0 (expt 2 (division-long-scale-shift divisor)))))
                             (before (proof-world-machine (division-long-scale-stage 4 dividend divisor world)))
                             (after (proof-world-machine (division-long-scale-stage 6 dividend divisor world)))))
            :in-theory (disable division-long-scale-ready-p division-leading-limb division-normalization-shift
                                division-long-scale-stage division-scaled-divisor-word division-unnormalized-leading-limb
                                division-digits-p)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-long-scaled-high-word-value
   (implies (natp (proof-load-word address machine))
            (equal (division-magnitude (division-read-limbs 1 address machine))
                   (proof-load-word address machine)))
   :hints (("Goal"
            :expand ((division-read-limbs 1 address machine)
                     (division-read-limbs 0 (+ 8 address) machine))
            :in-theory (enable division-magnitude)))))

(defthm division-long-scale-prepares-operands
  (let* ((after (division-long-scale-stage 6 dividend divisor world))
         (shift (division-long-scale-shift divisor))
         (scale (expt 2 shift))
         (shifted-divisor (division-long-scaled-divisor dividend divisor world))
         (positions (division-long-scale-position-count dividend divisor)))
    (implies (division-long-scale-ready-p dividend divisor world)
             (and (posp positions)
                  (natp shift) (< shift 32)
                  (equal (proof-world-pc after) (+ 92 (proof-world-pc world)))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 13 after) (* 8 (1- positions)))
                  (division-digits-p shifted-divisor)
                  (division-leading-digit-p (division-leading-limb shifted-divisor))
                  (equal (len shifted-divisor) (len divisor))
                  (equal (division-magnitude shifted-divisor) (* scale (division-magnitude divisor)))
                  (equal (division-long-dividend-value positions shifted-divisor after)
                         (* scale (division-magnitude dividend))))))
  :hints (("Goal"
           :use ((:instance division-long-scale-shift-bound)
                 (:instance division-long-scale-divisor-shift)
                 (:instance division-long-scale-divisor-value)
                 (:instance division-long-scale-dividend-shift)
                 (:instance division-long-scale-dividend-span)
                 (:instance division-limb-scale-fits (shift (division-long-scale-shift divisor)))
                 (:instance division-left-shift-limbs-correct
                            (digits dividend) (carry 0) (scale (expt 2 (division-long-scale-shift divisor))))
                 (:instance division-read-limb-span-value
                            (low (len dividend)) (high 1) (address (proof-world-reg 19 world))
                            (machine (proof-world-machine (division-long-scale-stage 6 dividend divisor world)))))
           :in-theory (disable division-choose-normalization-inputs-p division-scale-call-inputs-p
                               division-scale-window-setup-inputs-p division-leading-limb division-normalization-shift
                               division-long-scale-stage division-scaled-divisor-word division-unnormalized-leading-limb
                               division-digits-p division-leading-digit-p division-long-scaled-divisor)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
