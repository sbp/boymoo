(in-package "BOYMOO-PROOFS")

(include-book "correction-execution")
(include-book "sign-view")

(logic)
(set-verify-guards-eagerness 0)

(defthm division-position-layout-offsets
  (and (equal (division-runtime-offset "rt:z-divide-estimate")
              (+ 52 (division-runtime-offset "rt:z-divide-position")))
       (equal (division-runtime-offset "rt:z-divide-subtract-limb")
              (+ 96 (division-runtime-offset "rt:z-divide-position")))
       (equal (division-runtime-offset "rt:z-divide-store")
              (+ 240 (division-runtime-offset "rt:z-divide-position"))))
  :rule-classes nil)

(local
 (in-theory (disable floor mod ash proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     division-instruction-prefix-ready-p division-before-cuts-p
                     boymoo-model::a64-memory boymoo-model::a64-write-bytes)))

(defun division-position-corrected-world (digits divisor world)
  (proof-advance (division-window-correction-steps digits divisor world) world))

(defun division-position-write-ready-p (digits divisor world)
  (let* ((corrected (division-position-corrected-world digits divisor world))
         (window (proof-world-reg 14 world))
         (window-bytes (* 8 (1+ (len divisor))))
         (quotient (+ (proof-world-reg 21 world) (proof-world-reg 13 world))))
    (and (division-window-correction-ready-p digits divisor world)
         (proof-span-p window window-bytes)
         (proof-disjoint-p window (+ window window-bytes) quotient (+ quotient 8))
         (division-store-position-inputs-p corrected)
         (division-instruction-prefix-ready-p
          *division-store-position-instructions* (list (+ 12 (proof-world-pc corrected))) corrected))))

(defun division-position-write-count (digits divisor world)
  (+ 3 (division-window-correction-steps digits divisor world)))

(defthm division-position-store-preserves-disjoint-limbs
  (let* ((after (proof-advance (division-position-write-count digits divisor world) world))
         (base (proof-world-reg 14 world))
         (q-address (+ (proof-world-reg 21 world) (proof-world-reg 13 world)))
         (query-end (+ query (* 8 count))))
    (implies (and (division-position-write-ready-p digits divisor world)
                  (natp count) (proof-span-p query (* 8 count))
                  (proof-disjoint-p base (+ base (* 8 (1+ (len divisor)))) query query-end)
                  (proof-disjoint-p q-address (+ q-address 8) query query-end))
             (equal (division-read-limbs count query (proof-world-machine after))
                    (division-read-limbs count query (proof-world-machine world)))))
  :hints (("Goal"
           :use ((:instance division-window-correction-reaches-store)
                 (:instance division-window-correction-preserves-disjoint-limbs)
                 (:instance division-store-position-runs (world (division-position-corrected-world digits divisor world)))
                 (:instance proof-advance-append
                            (prefix (division-window-correction-steps digits divisor world)) (suffix 3))
                 (:instance division-limbs-after-disjoint-word-write
                            (address query) (target (+ (proof-world-reg 21 world) (proof-world-reg 13 world)))
                            (value (proof-world-reg 15 (division-position-corrected-world digits divisor world)))
                            (before (proof-world-machine (division-position-corrected-world digits divisor world)))
                            (after (proof-world-machine
                                    (proof-advance (division-position-write-count digits divisor world) world)))))
           :in-theory (disable division-window-correction-ready-p division-window-correction-steps
                               division-correct-window division-read-limbs proof-advance-append)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-window-stores-digit-and-keeps-remainder
   (let* ((corrected (division-position-corrected-world digits divisor world))
          (after (proof-advance (division-position-write-count digits divisor world) world))
          (base (proof-world-reg 14 world))
          (count (len divisor))
          (q-address (+ (proof-world-reg 21 world) (proof-world-reg 13 world))))
     (implies (division-position-write-ready-p digits divisor world)
              (and (equal (proof-load-word q-address (proof-world-machine after)) (proof-world-reg 15 corrected))
                   (equal (division-read-limbs count base (proof-world-machine after))
                          (division-read-limbs count base (proof-world-machine corrected)))
                   (equal (proof-load-word (+ base (* 8 count)) (proof-world-machine after))
                          (division-window-high-limb corrected))
                   (equal (proof-world-pc after)
                          (+ (proof-world-pc world) 144
                             (if (<= 8 (proof-world-reg 13 world)) *division-store-to-position* 12)))
                   (equal (proof-world-reg 13 after)
                          (boymoo-model::a64-unsigned 64 (- (proof-world-reg 13 world) 8))))))
   :hints (("Goal"
            :use ((:instance division-window-correction-reaches-store)
                  (:instance division-store-position-runs (world (division-position-corrected-world digits divisor world)))
                  (:instance proof-advance-append
                             (prefix (division-window-correction-steps digits divisor world)) (suffix 3))
                  (:instance division-limbs-after-disjoint-word-write
                             (count (len divisor)) (address (proof-world-reg 14 world))
                             (target (+ (proof-world-reg 21 world) (proof-world-reg 13 world)))
                             (value (proof-world-reg 15 (division-position-corrected-world digits divisor world)))
                             (before (proof-world-machine (division-position-corrected-world digits divisor world)))
                             (after (proof-world-machine
                                     (proof-advance (division-position-write-count digits divisor world) world))))
                  (:instance division-load-word-after-disjoint-written-word
                             (address (+ (proof-world-reg 14 world) (* 8 (len divisor))))
                             (target (+ (proof-world-reg 21 world) (proof-world-reg 13 world)))
                             (word (proof-world-reg 15 (division-position-corrected-world digits divisor world)))
                             (before (proof-world-machine (division-position-corrected-world digits divisor world)))
                             (after (proof-world-machine
                                     (proof-advance (division-position-write-count digits divisor world) world)))))
            :in-theory (disable division-window-correction-ready-p division-window-correction-steps
                                division-correct-window division-read-limbs proof-advance-append
                                division-before-cuts-p
                                boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-normalized-window-writes-quotient-and-remainder
  (let* ((after (proof-advance (division-position-write-count digits divisor world) world))
         (base (proof-world-reg 14 world))
         (high (division-window-high-limb world))
         (q-address (+ (proof-world-reg 21 world) (proof-world-reg 13 world)))
         (machine (proof-world-machine after))
         (remainder (division-read-limbs (len divisor) base machine))
         (b (division-magnitude divisor))
         (q (proof-load-word q-address machine))
         (r (division-magnitude remainder)))
    (implies (and (division-position-write-ready-p digits divisor world)
                  (division-window-p head lead next digit a-tail b-tail scale)
                  (equal (proof-world-reg 15 world) (division-two-limb-estimate head lead next digit))
                  (equal (division-window-magnitude digits high)
                         (division-prefix-value (+ (* *division-radix* head) digit) a-tail scale))
                  (equal b (division-prefix-value (+ (* *division-radix* lead) next) b-tail scale)))
             (and (division-digit-p q) (division-digits-p remainder)
                  (< r b)
                  (equal (+ (* b q) r) (division-window-magnitude digits high))
                  (equal (proof-load-word (+ base (* 8 (len divisor))) machine) 0)
                  (equal (proof-world-pc after)
                         (+ (proof-world-pc world)
                            (if (<= 8 (proof-world-reg 13 world))
                                (+ 144 *division-store-to-position*)
                              156)))
                  (equal (proof-world-reg 13 after)
                         (boymoo-model::a64-unsigned 64 (- (proof-world-reg 13 world) 8))))))
  :hints (("Goal"
           :use ((:instance division-window-stores-digit-and-keeps-remainder)
                 (:instance division-machine-normalized-window-result))
           :in-theory (disable division-window-correction-ready-p division-window-p division-position-write-count
                               division-window-high-limb division-window-magnitude division-prefix-value
                               division-two-limb-estimate division-read-limbs division-magnitude
                               boymoo-model::a64-unsigned division-a64-unsigned-is-remainder)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
