(in-package "BOYMOO-PROOFS")

(include-book "position-result")
(include-book "divide-return")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-subtraction-start-instructions* (division-runtime-block "rt:z-divide-subtract" 0 2))

(local
 (in-theory (disable floor mod ash proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-instruction-effect proof-segment-p division-instruction-sequence-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-unsigned
                     division-a64-unsigned-is-remainder)))

(defun division-subtraction-start-ready-p (world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 8 (proof-world-pc world)))
       (division-instruction-sequence-ready-p *division-subtraction-start-instructions*
                                              (list (+ 8 (proof-world-pc world))) world)))

(defun division-subtraction-start-output-p (world after)
  (and (equal (proof-world-pc after) (+ 8 (proof-world-pc world)))
       (equal (proof-world-reg 0 after) 0)
       (equal (proof-world-reg 1 after) 0)
       (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
       (equal (proof-world-reg 14 after) (proof-world-reg 14 world))
       (equal (proof-world-reg 15 after) (proof-world-reg 15 world))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))))

(local
 (defthm division-subtraction-start-effects
   (implies (and (division-ordinary-world-p world)
                 (unsigned-byte-p 64 (+ 8 (proof-world-pc world))))
            (division-subtraction-start-output-p
             world (division-instruction-sequence *division-subtraction-start-instructions* world)))
   :rule-classes nil))

(defthm division-subtraction-start-clears-offset-and-carry
  (implies (division-subtraction-start-ready-p world)
           (division-subtraction-start-output-p world (proof-advance 2 world)))
  :hints (("Goal"
           :use ((:instance division-subtraction-start-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-subtraction-start-instructions*)
                            (cuts (list (+ 8 (proof-world-pc world))))))
           :in-theory (disable division-subtraction-start-output-p division-instruction-sequence)))
  :rule-classes nil)

(defun division-position-estimate-start (world)
  (proof-advance 13 world))

(defun division-position-estimate-count (world)
  (let ((entry (division-position-estimate-start world)))
    (division-estimate-loop-steps
     (proof-world-reg 15 entry) (proof-world-reg 16 entry)
     (proof-world-reg 11 entry) (proof-world-reg 12 entry) (proof-world-reg 17 entry))))

(defun division-position-estimate-end (world)
  (proof-advance (division-position-estimate-count world) (division-position-estimate-start world)))

(defun division-position-subtraction-start (world)
  (proof-advance 2 (division-position-estimate-end world)))

(defun division-position-estimate-ready-p (world)
  (and (division-position-inputs-p world)
       (division-instruction-sequence-ready-p *division-position-instructions*
                                              (list (+ 52 (proof-world-pc world))) world)
       (division-estimate-entry-p (division-position-estimate-start world))
       (division-subtraction-start-ready-p (division-position-estimate-end world))))

(local
 (defthm division-position-head-is-word
   (implies (division-position-inputs-p world) (unsigned-byte-p 64 (division-position-head world)))
   :hints (("Goal"
            :use (:instance division-two-limb-word-fits
                            (low (division-position-word 8 world)) (high (division-position-word 0 world)))
            :in-theory (disable division-position-word division-position-window division-two-limb-word-fits)))
   :rule-classes nil))

(local
 (defthm division-window-high-kept-from-position
   (implies (and (equal (proof-world-reg 14 after) (division-position-window world))
                 (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                 (equal (boymoo-model::a64-memory (proof-world-machine after))
                        (boymoo-model::a64-memory (proof-world-machine world))))
            (equal (division-window-high-limb after) (division-position-word 0 world)))
   :hints (("Goal" :in-theory (e/d (proof-load-word)
                                   (division-position-window boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(defthm division-position-prepares-window-correction
  (let* ((after (division-position-subtraction-start world))
         (head (division-position-head world))
         (lead (proof-world-reg 11 world))
         (next (proof-world-reg 12 world))
         (digit (division-position-word 16 world)))
    (implies (division-position-estimate-ready-p world)
             (and (<= (division-position-estimate-count world) 24)
                  (equal (proof-world-pc after) (+ 96 (proof-world-pc world)))
                  (equal (proof-world-reg 15 after) (division-two-limb-estimate head lead next digit))
                  (equal (proof-world-reg 0 after) 0)
                  (equal (proof-world-reg 1 after) 0)
                  (equal (proof-world-reg 13 after) (proof-world-reg 13 world))
                  (equal (proof-world-reg 14 after) (division-position-window world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (division-window-high-limb after) (division-position-word 0 world)))))
  :hints (("Goal"
           :use ((:instance division-position-setup-runs)
                 (:instance division-position-head-is-word)
                 (:instance division-estimate-loop-from-head
                            (head (division-position-head world)) (world (division-position-estimate-start world)))
                 (:instance division-subtraction-start-clears-offset-and-carry
                            (world (division-position-estimate-end world)))
                 (:instance division-window-high-kept-from-position
                            (after (division-position-subtraction-start world))))
           :in-theory (disable division-position-inputs-p division-position-head division-position-word
                               division-position-window division-window-high-limb division-estimate-entry-p
                               division-estimate-loop-steps division-subtraction-start-ready-p
                               division-first-estimate division-two-limb-estimate)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-position-iteration-counts (digits divisor world)
  (list 13 (division-position-estimate-count world) 2
        (division-position-write-count digits divisor (division-position-subtraction-start world))))

(local
 (defthm division-position-iteration-ends-after-store
   (equal (proof-advance (division-step-sum (division-position-iteration-counts digits divisor world)) world)
          (proof-advance (division-position-write-count digits divisor (division-position-subtraction-start world))
                         (division-position-subtraction-start world)))
   :hints (("Goal"
            :use (:instance division-advance-chain-sum
                            (counts (division-position-iteration-counts digits divisor world)))
            :in-theory (disable division-step-sum division-window-correction-steps division-estimate-loop-steps)))
   :rule-classes nil))

(defthm division-position-preserves-disjoint-limbs
  (let* ((before (division-position-subtraction-start world))
         (steps (division-step-sum (division-position-iteration-counts digits divisor world)))
         (after (proof-advance steps world))
         (base (division-position-window world))
         (q-address (+ (proof-world-reg 21 world) (proof-world-reg 13 world)))
         (query-end (+ query (* 8 count))))
    (implies (and (division-position-estimate-ready-p world)
                  (division-position-write-ready-p digits divisor before)
                  (natp count) (proof-span-p query (* 8 count))
                  (proof-disjoint-p base (+ base (* 8 (1+ (len divisor)))) query query-end)
                  (proof-disjoint-p q-address (+ q-address 8) query query-end))
             (equal (division-read-limbs count query (proof-world-machine after))
                    (division-read-limbs count query (proof-world-machine world)))))
  :hints (("Goal"
           :use ((:instance division-position-prepares-window-correction)
                 (:instance division-position-iteration-ends-after-store)
                 (:instance division-position-store-preserves-disjoint-limbs
                            (world (division-position-subtraction-start world)))
                 (:instance division-read-limbs-from-same-memory
                            (count count) (address query)
                            (first (proof-world-machine (division-position-subtraction-start world)))
                            (second (proof-world-machine world))))
           :in-theory (disable division-position-estimate-ready-p division-position-write-ready-p
                               division-step-sum division-position-iteration-counts
                               division-position-subtraction-start division-position-write-count
                               division-position-window division-read-limbs division-magnitude)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defthm division-one-normalized-position-executes
  (let* ((sub-start (division-position-subtraction-start world))
         (steps (division-step-sum (division-position-iteration-counts digits divisor world)))
         (after (proof-advance steps world))
         (head (division-position-head world))
         (high (division-position-word 0 world))
         (digit (division-position-word 16 world))
         (lead (proof-world-reg 11 world))
         (next (proof-world-reg 12 world))
         (base (division-position-window world))
         (offset (proof-world-reg 13 world))
         (q-address (+ (proof-world-reg 21 world) offset))
         (machine (proof-world-machine after))
         (q (proof-load-word q-address machine))
         (r-limbs (division-read-limbs (len divisor) base machine))
         (r (division-magnitude r-limbs))
         (b (division-magnitude divisor)))
    (implies (and (division-position-estimate-ready-p world)
                  (division-position-write-ready-p digits divisor sub-start)
                  (division-window-p head lead next digit a-tail b-tail scale)
                  (equal (division-window-magnitude digits high)
                         (division-prefix-value (+ (* *division-radix* head) digit) a-tail scale))
                  (equal b (division-prefix-value (+ (* *division-radix* lead) next) b-tail scale)))
             (and (division-digit-p q)
                  (division-digits-p r-limbs)
                  (< r b)
                  (equal (+ (* b q) r) (division-window-magnitude digits high))
                  (equal (proof-load-word (+ base (* 8 (len divisor))) machine) 0)
                  (equal (proof-world-reg 13 after) (boymoo-model::a64-unsigned 64 (- offset 8)))
                  (equal (proof-world-pc after)
                         (if (<= 8 offset) (proof-world-pc world) (+ 252 (proof-world-pc world)))))))
  :hints (("Goal"
           :use ((:instance division-position-prepares-window-correction)
                 (:instance division-position-iteration-ends-after-store)
                 (:instance division-normalized-window-writes-quotient-and-remainder
                            (head (division-position-head world)) (lead (proof-world-reg 11 world))
                            (next (proof-world-reg 12 world)) (digit (division-position-word 16 world))
                            (world (division-position-subtraction-start world))))
           :in-theory (disable division-position-estimate-ready-p division-position-write-ready-p
                               division-step-sum division-position-iteration-counts division-position-write-count
                               division-position-subtraction-start division-position-estimate-count
                               division-position-head division-position-window division-position-word
                               division-window-p division-window-high-limb division-window-magnitude
                               division-prefix-value division-magnitude division-read-limbs division-two-limb-estimate)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
