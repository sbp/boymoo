(in-package "BOYMOO-PROOFS")

(include-book "shift-machine")
(include-book "one-limb-loop")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod ash expt proof-step proof-advance proof-world-reg
                     proof-world-pc proof-world-machine proof-world-stop proof-world-regions
                     proof-load-word proof-segment-p division-before-cuts-p
                     division-instruction-prefix-ready-p boymoo-model::a64-memory
                     boymoo-model::a64-sp boymoo-model::a64-write-bytes)))

(defun division-right-shift-lower-carry (digits upper)
  (if (consp digits) (car digits) upper))

(defun division-right-shift-digits (digits upper scale)
  (if (atom digits)
      nil
    (let* ((carry (division-right-shift-lower-carry (cdr digits) upper))
           (word (+ (car digits) (* *division-radix* carry))))
      (cons (mod (floor word scale) *division-radix*)
            (division-right-shift-digits (cdr digits) upper scale)))))

(defthm division-right-shift-length
  (equal (len (division-right-shift-digits digits upper scale)) (len digits))
  :hints (("Goal" :induct (division-right-shift-digits digits upper scale))))

(local
 (defthm division-right-shift-step-remainder
   (implies (and (division-digit-p digit) (division-digit-p upper)
                 (division-digit-p scale) (posp scale)
                 (natp factor) (equal (* scale factor) *division-radix*))
            (equal (mv-nth 1 (division-one-limb-step digit (mod upper scale) scale))
                   (mod digit scale)))
   :hints (("Goal"
            :use ((:instance division-mod-bounds (a digit) (b scale))
                  (:instance division-mod-bounds (a upper) (b scale))
                  (:instance division-floor-mod-identity (a digit) (b scale))
                  (:instance division-floor-mod-identity
                             (a (+ digit (* *division-radix* (mod upper scale)))) (b scale))
                  (:instance associativity-of-* (x factor) (y scale) (z (mod upper scale)))
                  (:instance division-remainder-unique
                             (a (+ digit (* *division-radix* (mod upper scale))))
                             (b scale)
                             (q (+ (floor digit scale) (* factor (mod upper scale))))
                             (r (mod digit scale))))
            :in-theory (disable division-floor-mod-identity associativity-of-*)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-right-shift-agrees-with-one-limb
   (implies (and (division-digits-p digits) (division-digit-p upper)
                 (division-digit-p scale) (posp scale)
                 (natp factor) (equal (* scale factor) *division-radix*)
                 (equal (mod upper scale) 0))
            (and (equal (division-right-shift-digits digits upper scale)
                        (mv-nth 0 (division-one-limb-loop digits scale)))
                 (equal (mod (division-right-shift-lower-carry digits upper) scale)
                        (mv-nth 1 (division-one-limb-loop digits scale)))))
   :hints (("Goal" :induct (division-one-limb-loop digits scale)
                   :in-theory (disable division-one-limb-step))
           ("Subgoal *1/2"
            :use ((:instance division-right-shift-digit-correct
                             (digit (car digits))
                             (upper (division-right-shift-lower-carry (cdr digits) upper)))
                  (:instance division-right-shift-step-remainder
                             (digit (car digits))
                             (upper (division-right-shift-lower-carry (cdr digits) upper))))))
   :rule-classes nil))

(defthm division-right-shift-digits-value
  (let* ((scale (expt 2 shift))
         (written (division-right-shift-digits digits 0 scale)))
    (implies (and (division-digits-p digits) (natp shift) (< shift 32))
             (and (division-digits-p written)
                  (equal (division-magnitude written)
                         (floor (division-magnitude digits) scale)))))
  :hints (("Goal"
           :use ((:instance division-limb-scale-fits)
                 (:instance division-power-of-two-positive (width (- 32 shift)))
                 (:instance division-power-of-two-sum (left shift) (right (- 32 shift)))
                 (:instance division-right-shift-agrees-with-one-limb
                            (upper 0) (scale (expt 2 shift)) (factor (expt 2 (- 32 shift))))
                 (:instance division-one-limb-loop-correct (divisor (expt 2 shift)))
                 (:instance division-quotient-unique
                            (a (division-magnitude digits)) (b (expt 2 shift))
                            (q (division-magnitude (mv-nth 0 (division-one-limb-loop digits (expt 2 shift)))))
                            (r (mv-nth 1 (division-one-limb-loop digits (expt 2 shift))))))
           :in-theory (disable division-one-limb-loop division-magnitude division-digits-p
                               division-right-shift-digits division-right-shift-lower-carry)
           :do-not-induct t))
  :rule-classes nil)

(defun division-right-shift-prefix-ready-p (digits pending world)
  (if (atom digits)
      (null digits)
    (let* ((before (proof-advance (* 8 (len (cdr digits))) world))
           (offset (* 8 pending))
           (address (+ (proof-world-reg 19 before) offset))
           (cuts (list (+ 32 (proof-world-pc world)))))
      (and (division-right-shift-prefix-ready-p (cdr digits) (1+ pending) world)
           (division-right-shift-limb-inputs-p before)
           (equal (division-right-shift-offset before) offset)
           (equal (proof-load-word address (proof-world-machine before)) (car digits))
           (division-instruction-prefix-ready-p *division-right-shift-limb-instructions* cuts before)))))

(local
 (defthm division-right-shift-advance-zero
   (equal (proof-advance 0 world) world)
   :hints (("Goal" :expand ((proof-advance 0 world))))))

(local
 (defthm division-right-shift-before-cuts-zero
   (division-before-cuts-p 0 cuts world)
   :hints (("Goal" :expand ((division-before-cuts-p 0 cuts world))))))

(defun division-right-shift-prefix-output-p (digits pending world after)
  (let* ((pc (proof-world-pc world))
         (shift (proof-world-reg 10 world))
         (address (proof-world-reg 19 world))
         (upper (proof-world-reg 1 world))
         (written (division-right-shift-digits digits upper (expt 2 shift))))
    (and (equal (proof-world-reg 0 after) (* 8 pending))
         (equal (proof-world-reg 1 after) (division-right-shift-lower-carry digits upper))
         (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
         (equal (proof-world-reg 10 after) shift)
         (equal (proof-world-reg 19 after) address)
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (proof-world-pc after) (if (and (consp digits) (equal pending 0)) (+ 32 pc) pc))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (division-write-quotient-limbs written pending address
                                              (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine world)))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (proof-world-stop after) (proof-world-stop world)))))

(defthm division-right-shift-prefix-writes-limbs
  (let* ((steps (* 8 (len digits)))
         (after (proof-advance steps world)))
    (implies (and (natp pending)
                  (equal (proof-world-reg 0 world) (* 8 (+ pending (len digits))))
                  (division-right-shift-prefix-ready-p digits pending world))
             (and (division-before-cuts-p steps (list (+ 32 (proof-world-pc world))) world)
                  (division-right-shift-prefix-output-p digits pending world after))))
  :hints (("Goal"
           :induct (division-right-shift-prefix-ready-p digits pending world)
           :in-theory (disable division-right-shift-limb-inputs-p division-right-shift-offset proof-advance-append
                               division-before-cuts-append))
          ("Subgoal *1/2"
           :use ((:instance division-right-shift-limb-runs
                            (world (proof-advance (* 8 (len (cdr digits))) world)))
                 (:instance proof-advance-append (prefix (* 8 (len (cdr digits)))) (suffix 8))
                 (:instance division-before-cuts-append (cuts (list (+ 32 (proof-world-pc world))))
                            (prefix (* 8 (len (cdr digits)))) (suffix 8)))))
  :rule-classes nil)

(defthm division-right-shift-loop-writes-unscaled-value
  (let* ((count (len digits))
         (address (proof-world-reg 19 world))
         (shift (proof-world-reg 10 world))
         (steps (* 8 count))
         (cuts (list (+ 32 (proof-world-pc world))))
         (after (proof-advance steps world))
         (written (division-read-limbs count address (proof-world-machine after))))
    (implies (and (consp digits) (division-digits-p digits)
                  (not (proof-world-stop world))
                  (natp shift) (< shift 32)
                  (proof-span-p address (* 8 count))
                  (equal (proof-world-reg 0 world) (* 8 count))
                  (equal (proof-world-reg 1 world) 0)
                  (division-right-shift-prefix-ready-p digits 0 world))
             (and (proof-segment-p steps cuts world :cut after)
                  (division-digits-p written)
                  (equal (division-magnitude written)
                         (floor (division-magnitude digits) (expt 2 shift))))))
  :hints (("Goal"
           :use ((:instance division-right-shift-prefix-writes-limbs (pending 0))
                 (:instance division-right-shift-digits-value (shift (proof-world-reg 10 world)))
                 (:instance division-segment-from-cut-free-prefix
                            (count (* 8 (len digits))) (cuts (list (+ 32 (proof-world-pc world)))))
                 (:instance division-read-quotient-limb-writes
                            (pending 0) (base (proof-world-reg 19 world))
                            (digits (division-right-shift-digits digits 0 (expt 2 (proof-world-reg 10 world))))
                            (before (proof-world-machine world))
                            (after (proof-world-machine (proof-advance (* 8 (len digits)) world)))))
           :in-theory (disable division-right-shift-prefix-ready-p division-right-shift-digits
                               division-read-limbs division-write-quotient-limbs division-magnitude
                               division-digits-p)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-read-after-disjoint-descending-writes
  (let* ((target (+ base (* 8 pending)))
         (bytes (* 8 (len words))))
    (implies (and (natp pending) (natp base)
                  (proof-span-p target bytes) (proof-span-p query size)
                  (proof-disjoint-p target (+ target bytes) query (+ query size)))
             (equal (boymoo-model::a64-read-bytes
                     size query (division-write-quotient-limbs words pending base memory))
                    (boymoo-model::a64-read-bytes size query memory))))
  :hints (("Goal"
           :induct (division-write-quotient-limbs words pending base memory)
           :in-theory (disable boymoo-model::a64-read-bytes))
          ("Subgoal *1/2" :cases ((consp (cdr words)))))
  :rule-classes nil)

(defthm division-limbs-after-disjoint-descending-writes
  (let* ((target (+ base (* 8 pending)))
         (bytes (* 8 (len written))))
    (implies (and (natp pending) (natp base) (natp count)
                  (proof-span-p target bytes) (proof-span-p query (* 8 count))
                  (proof-disjoint-p target (+ target bytes) query (+ query (* 8 count)))
                  (equal (boymoo-model::a64-memory after)
                         (division-write-quotient-limbs written pending base (boymoo-model::a64-memory before))))
             (equal (division-read-limbs count query after)
                    (division-read-limbs count query before))))
  :hints (("Goal"
           :induct (division-read-limbs count query before)
           :in-theory (e/d (proof-load-word)
                           (boymoo-model::a64-read-bytes division-write-quotient-limbs)))
          ("Subgoal *1/2"
           :use (:instance division-read-after-disjoint-descending-writes
                           (words written) (size 8) (memory (boymoo-model::a64-memory before)))
           :cases ((equal count 1))
           :expand ((division-read-limbs count query after))))
  :rule-classes nil)

(defthm division-right-shift-preserves-disjoint-limbs
  (let* ((address (proof-world-reg 19 world))
         (bytes (* 8 (len digits)))
         (after (proof-advance bytes world)))
    (implies (and (equal (proof-world-reg 0 world) bytes)
                  (proof-span-p address bytes) (natp count) (proof-span-p query (* 8 count))
                  (proof-disjoint-p address (+ address bytes) query (+ query (* 8 count)))
                  (division-right-shift-prefix-ready-p digits 0 world))
             (equal (division-read-limbs count query (proof-world-machine after))
                    (division-read-limbs count query (proof-world-machine world)))))
  :hints (("Goal"
           :use ((:instance division-right-shift-prefix-writes-limbs (pending 0))
                 (:instance division-limbs-after-disjoint-descending-writes
                            (pending 0) (base (proof-world-reg 19 world))
                            (written (division-right-shift-digits
                                      digits (proof-world-reg 1 world) (expt 2 (proof-world-reg 10 world))))
                            (before (proof-world-machine world))
                            (after (proof-world-machine (proof-advance (* 8 (len digits)) world)))))
           :in-theory (disable division-right-shift-prefix-ready-p division-right-shift-digits
                               division-write-quotient-limbs division-read-limbs)
           :do-not-induct t))
  :rule-classes nil)
