(in-package "BOYMOO-PROOFS")

(include-book "limb-machine")
(include-book "linked")
(include-book "cutpoints")
(include-book "sign-view")
(include-book "divide-return")

(logic)
(set-verify-guards-eagerness 0)

(defconst *division-copy-instructions* (division-runtime-block "rt:z-copy" 0 2))
(defconst *division-copy-loop-instructions* (division-runtime-block "rt:z-copy-loop" 0 5))
(defconst *division-copy-return-instructions* (division-runtime-block "rt:z-copy-return" 0 1))

(local
 (in-theory (disable floor mod ash proof-step proof-advance proof-world-pc proof-world-reg
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-instruction-effect proof-segment-p division-before-cuts-p
                     division-instruction-prefix-ready-p division-instruction-sequence-ready-p
                     boymoo-model::a64-sp boymoo-model::a64-memory boymoo-model::a64-write-bytes
                     boymoo-model::a64-condition boymoo-model::a64-nzcv boymoo-model::a64-unsigned
                     division-a64-unsigned-is-remainder)))

(defun division-copy-iteration-instructions (offset)
  (if (equal offset 0)
      (take 3 *division-copy-loop-instructions*)
    *division-copy-loop-instructions*))

(defun division-copy-iteration-inputs-p (world)
  (let* ((offset (proof-world-reg 2 world))
         (source (+ (proof-world-reg 0 world) offset))
         (target (+ (proof-world-reg 1 world) offset)))
    (and (division-ordinary-world-p world)
         (unsigned-byte-p 64 (+ 20 (proof-world-pc world)))
         (or (equal offset 0) (<= 8 offset))
         (proof-span-p source 8) (proof-span-p target 8))))

(defun division-copy-iteration-output-p (world after)
  (let* ((offset (proof-world-reg 2 world))
         (source (+ (proof-world-reg 0 world) offset))
         (target (+ (proof-world-reg 1 world) offset))
         (word (proof-load-word source (proof-world-machine world))))
    (and (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
         (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
         (equal (proof-world-reg 2 after) (if (equal offset 0) 0 (- offset 8)))
         (equal (proof-world-reg 3 after) word)
         (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
         (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
         (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
         (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
         (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
         (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
         (equal (proof-world-pc after)
                (if (equal offset 0) (+ 20 (proof-world-pc world)) (proof-world-pc world)))
         (equal (boymoo-model::a64-memory (proof-world-machine after))
                (boymoo-model::a64-write-bytes 8 target word
                                              (boymoo-model::a64-memory (proof-world-machine world))))
         (equal (proof-world-stop after) (proof-world-stop world))
         (equal (proof-world-regions after) (proof-world-regions world))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine world)))
         (division-ordinary-world-p after))))

(local
 (defthm division-copy-load-in-word
   (unsigned-byte-p 64 (proof-load-word address machine))
   :hints (("Goal"
            :use (:instance division-read-bytes-value-range
                            (count 8) (memory (boymoo-model::a64-memory machine)))
            :in-theory (enable proof-load-word)))
   :rule-classes nil))

(defthm division-copy-iteration-effects
  (implies (division-copy-iteration-inputs-p world)
           (division-copy-iteration-output-p
            world (division-instruction-sequence
                   (division-copy-iteration-instructions (proof-world-reg 2 world)) world)))
  :hints (("Goal"
           :cases ((equal (proof-world-reg 2 world) 0))
           :use (:instance division-copy-load-in-word
                           (address (+ (proof-world-reg 0 world) (proof-world-reg 2 world)))
                           (machine (proof-world-machine world)))
           :do-not-induct t))
  :rule-classes nil)

(defthm division-copy-iteration-runs
  (let* ((offset (proof-world-reg 2 world))
         (instructions (division-copy-iteration-instructions offset))
         (steps (len instructions))
         (cuts (list (+ 20 (proof-world-pc world))))
         (after (proof-advance steps world)))
    (implies (and (division-copy-iteration-inputs-p world)
                  (division-instruction-prefix-ready-p instructions cuts world))
             (and (division-before-cuts-p steps cuts world)
                  (division-copy-iteration-output-p world after))))
  :hints (("Goal"
           :use ((:instance division-copy-iteration-effects)
                 (:instance division-instruction-prefix-advances
                            (instructions (division-copy-iteration-instructions (proof-world-reg 2 world)))
                            (cuts (list (+ 20 (proof-world-pc world))))))
           :in-theory (disable division-copy-iteration-inputs-p division-copy-iteration-output-p
                               division-copy-iteration-instructions division-instruction-sequence)))
  :rule-classes nil)

(defun division-copy-prefix-steps (words pending)
  (if (atom words)
      0
    (- (* 5 (len words)) (if (equal pending 0) 2 0))))

(defun division-copy-prefix-ready-p (words pending world)
  (if (atom words)
      (null words)
    (let* ((before (proof-advance (* 5 (len (cdr words))) world))
           (offset (* 8 pending))
           (source (+ (proof-world-reg 0 before) offset))
           (cuts (list (+ 20 (proof-world-pc world)))))
      (and (division-copy-prefix-ready-p (cdr words) (1+ pending) world)
           (division-copy-iteration-inputs-p before)
           (equal (proof-world-reg 2 before) offset)
           (equal (proof-load-word source (proof-world-machine before)) (car words))
           (division-instruction-prefix-ready-p (division-copy-iteration-instructions offset) cuts before)))))

(local
 (defthm division-copy-advance-zero
   (equal (proof-advance 0 world) world)
   :hints (("Goal" :expand ((proof-advance 0 world))))))

(local
 (defthm division-copy-before-cuts-zero
   (division-before-cuts-p 0 cuts world)
   :hints (("Goal" :expand ((division-before-cuts-p 0 cuts world))))))

(defthm division-copy-prefix-writes-words
  (let* ((steps (division-copy-prefix-steps words pending))
         (after (proof-advance steps world))
         (pc (proof-world-pc world))
         (source (proof-world-reg 0 world))
         (target (proof-world-reg 1 world)))
    (implies (and (natp pending) (division-copy-prefix-ready-p words pending world))
             (and (equal (proof-world-reg 0 after) source)
                  (equal (proof-world-reg 1 after) target)
                  (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (proof-world-pc after)
                         (if (and (consp words) (equal pending 0)) (+ 20 pc) pc))
                  (division-before-cuts-p steps (list (+ 20 pc)) world)
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (division-write-quotient-limbs
                          words pending target (boymoo-model::a64-memory (proof-world-machine world))))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (proof-world-regions after) (proof-world-regions world))
                  (equal (proof-world-stop after) (proof-world-stop world)))))
  :hints (("Goal"
           :induct (division-copy-prefix-ready-p words pending world)
           :in-theory (disable division-copy-iteration-inputs-p
                               division-before-cuts-append proof-advance-append))
          ("Subgoal *1/2"
           :use ((:instance division-copy-iteration-runs
                            (world (proof-advance (* 5 (len (cdr words))) world)))
                 (:instance proof-advance-append
                            (prefix (* 5 (len (cdr words)))) (suffix (if (equal pending 0) 3 5)))
                 (:instance division-before-cuts-append
                            (cuts (list (+ 20 (proof-world-pc world))))
                            (prefix (* 5 (len (cdr words)))) (suffix (if (equal pending 0) 3 5))))))
  :rule-classes nil)

(defun division-copy-setup-inputs-p (count world)
  (and (division-ordinary-world-p world)
       (unsigned-byte-p 64 (+ 8 (proof-world-pc world)))
       (natp count) (< count (expt 2 29))
       (equal (proof-load-word (proof-world-reg 0 world) (proof-world-machine world))
              (+ 3 (* 2048 (1+ count))))))

(defun division-copy-setup-output-p (count world after)
  (and (equal (proof-world-reg 2 after) (* 8 (1+ count)))
       (equal (proof-world-pc after) (+ 8 (proof-world-pc world)))
       (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
       (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
       (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
       (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (proof-world-regions after) (proof-world-regions world))
       (equal (proof-world-stop after) (proof-world-stop world))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine world)))
       (division-ordinary-world-p after)))

(defthm division-copy-setup-effects
  (implies (division-copy-setup-inputs-p count world)
           (division-copy-setup-output-p
            count world (division-instruction-sequence *division-copy-instructions* world)))
  :hints (("Goal" :use (:instance division-view-header-byte-count)
                  :do-not-induct t))
  :rule-classes nil)

(defthm division-copy-setup-runs
  (let* ((cuts (list (+ 8 (proof-world-pc world))))
         (after (proof-advance 2 world)))
    (implies (and (division-copy-setup-inputs-p count world)
                  (division-instruction-sequence-ready-p *division-copy-instructions* cuts world))
             (and (proof-segment-p 2 cuts world :cut after)
                  (division-copy-setup-output-p count world after))))
  :hints (("Goal"
           :use ((:instance division-copy-setup-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-copy-instructions*)
                            (cuts (list (+ 8 (proof-world-pc world)))))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-copy-instructions*)
                            (cuts (list (+ 8 (proof-world-pc world))))))
           :in-theory (disable division-copy-setup-inputs-p division-copy-setup-output-p
                               division-instruction-sequence)))
  :rule-classes nil)

(local
 (defthm division-copy-read-words-are-words
   (division-word-list-p (division-read-limbs count address machine))
   :hints (("Goal" :induct (division-read-limbs count address machine))
           ("Subgoal *1/2" :use (:instance division-copy-load-in-word)))))

(local
 (defthm division-copy-read-one-more-word
   (implies (posp count)
            (equal (division-read-limbs count address machine)
                   (cons (proof-load-word address machine)
                         (division-read-limbs (1- count) (+ address 8) machine))))
   :hints (("Goal" :expand ((division-read-limbs count address machine))))
   :rule-classes nil))

(defthm division-copy-view-words
  (implies (natp count)
           (equal (division-read-limbs (+ 2 count) address machine)
                  (cons (proof-load-word address machine)
                        (cons (proof-load-word (+ 8 address) machine)
                              (division-read-limbs count (+ 16 address) machine)))))
  :hints (("Goal"
           :use ((:instance division-copy-read-one-more-word (count (+ 2 count)))
                 (:instance division-copy-read-one-more-word (count (+ 1 count)) (address (+ 8 address))))
           :in-theory (disable division-read-limbs)))
  :rule-classes nil)

(defthm division-copy-view-from-equal-words
  (implies (and (proof-integer-view-p value source count before)
                (proof-span-p target (division-view-bytes count))
                (equal (division-read-limbs (+ 2 count) target (proof-world-machine after))
                       (division-read-limbs (+ 2 count) source (proof-world-machine before))))
           (proof-integer-view-p value target count after))
  :hints (("Goal"
           :use ((:instance division-view-sign-and-limbs (address source) (world before))
                 (:instance division-view-from-normalized-words (address target) (world after))
                 (:instance division-copy-view-words (address target) (machine (proof-world-machine after)))
                 (:instance division-copy-view-words (address source) (machine (proof-world-machine before))))
           :in-theory (disable proof-integer-view-p division-read-limbs division-magnitude
                               division-read-limbs-view-magnitude division-normalized-limbs-p
                               division-read-limbs-normalized)
           :do-not '(generalize)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-copy-positive-word-count
   (implies (posp count)
            (consp (division-read-limbs count address machine)))
   :hints (("Goal" :expand ((division-read-limbs count address machine))))))

(defthm division-copy-loop-produces-view
  (let* ((source (proof-world-reg 0 world))
         (target (proof-world-reg 1 world))
         (words (division-read-limbs (+ 2 count) source (proof-world-machine world)))
         (steps (division-copy-prefix-steps words 0))
         (cuts (list (+ 20 (proof-world-pc world))))
         (after (proof-advance steps world)))
    (implies (and (not (proof-world-stop world))
                  (proof-integer-view-p value source count world)
                  (proof-span-p target (division-view-bytes count))
                  (division-copy-prefix-ready-p words 0 world))
             (and (proof-segment-p steps cuts world :cut after)
                  (proof-integer-view-p value target count after)
                  (equal (proof-world-reg 0 after) source)
                  (equal (proof-world-reg 1 after) target)
                  (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world))))))
  :hints (("Goal"
           :use ((:instance division-copy-prefix-writes-words
                            (pending 0)
                            (words (division-read-limbs (+ 2 count) (proof-world-reg 0 world)
                                                       (proof-world-machine world))))
                 (:instance division-read-back-word-writes
                            (pending 0) (base (proof-world-reg 1 world))
                            (digits (division-read-limbs (+ 2 count) (proof-world-reg 0 world)
                                                        (proof-world-machine world)))
                            (before (proof-world-machine world))
                            (after (proof-world-machine
                                    (proof-advance (division-copy-prefix-steps
                                                    (division-read-limbs (+ 2 count) (proof-world-reg 0 world)
                                                                         (proof-world-machine world))
                                                    0) world))))
                 (:instance division-copy-view-from-equal-words
                            (source (proof-world-reg 0 world)) (target (proof-world-reg 1 world))
                            (before world)
                            (after (proof-advance (division-copy-prefix-steps
                                                   (division-read-limbs (+ 2 count) (proof-world-reg 0 world)
                                                                        (proof-world-machine world))
                                                   0) world)))
                 (:instance division-segment-from-cut-free-prefix
                            (count (division-copy-prefix-steps
                                    (division-read-limbs (+ 2 count) (proof-world-reg 0 world)
                                                         (proof-world-machine world))
                                    0))
                            (cuts (list (+ 20 (proof-world-pc world))))))
           :in-theory (disable proof-integer-view division-copy-prefix-ready-p division-read-limbs
                               division-copy-prefix-steps division-write-quotient-limbs
                               division-word-list-p)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-copy-setup-prefix-advances
   (implies (and (division-copy-setup-inputs-p count world)
                 (division-instruction-prefix-ready-p *division-copy-instructions* cuts world))
            (and (division-before-cuts-p 2 cuts world)
                 (division-copy-setup-output-p count world (proof-advance 2 world))))
   :hints (("Goal"
            :use ((:instance division-copy-setup-effects)
                  (:instance division-instruction-prefix-advances (instructions *division-copy-instructions*)))
            :in-theory (disable division-copy-setup-inputs-p division-copy-setup-output-p
                                division-instruction-sequence)))
   :rule-classes nil))

(defun division-copy-return-output-p (world after)
  (and (equal (proof-world-pc after) (proof-world-reg 30 world))
       (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
       (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
       (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
       (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
       (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
       (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
       (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
       (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
       (equal (boymoo-model::a64-memory (proof-world-machine after))
              (boymoo-model::a64-memory (proof-world-machine world)))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine world)))
       (equal (proof-world-stop after) (proof-world-stop world))))

(local
 (defthm division-copy-return-effects
   (implies (division-ordinary-world-p world)
            (division-copy-return-output-p
             world (division-instruction-sequence *division-copy-return-instructions* world)))
   :rule-classes nil))

(defthm division-copy-return-prefix-advances
  (implies (and (division-ordinary-world-p world)
                (division-instruction-prefix-ready-p *division-copy-return-instructions* cuts world))
           (and (division-before-cuts-p 1 cuts world)
                (division-copy-return-output-p world (proof-advance 1 world))))
  :hints (("Goal"
           :use ((:instance division-copy-return-effects)
                 (:instance division-instruction-prefix-advances (instructions *division-copy-return-instructions*)))
           :in-theory (disable division-instruction-sequence division-copy-return-output-p)))
  :rule-classes nil)

(defun division-copy-loop-count (count)
  (+ 8 (* 5 count)))

(defun division-copy-call-counts (count)
  (list 2 (division-copy-loop-count count) 1))

(defun division-copy-call-words (count world)
  (division-read-limbs (+ 2 count) (proof-world-reg 0 world) (proof-world-machine world)))

(defun division-copy-call-ready-p (value count world)
  (let* ((cuts (list (proof-world-reg 30 world)))
         (start (proof-advance 2 world))
         (end (proof-advance (division-copy-loop-count count) start)))
    (and (not (proof-world-stop world))
         (proof-integer-view-p value (proof-world-reg 0 world) count world)
         (proof-span-p (proof-world-reg 1 world) (division-view-bytes count))
         (division-copy-setup-inputs-p count world)
         (division-instruction-prefix-ready-p *division-copy-instructions* cuts world)
         (division-copy-prefix-ready-p (division-copy-call-words count start) 0 start)
         (division-before-cuts-p (division-copy-loop-count count) cuts start)
         (division-ordinary-world-p end)
         (not (proof-world-stop end))
         (division-instruction-prefix-ready-p *division-copy-return-instructions* cuts end))))

(local
 (defthm division-copy-loop-has-known-count
   (implies (natp count)
            (equal (division-copy-prefix-steps (division-read-limbs (+ 2 count) source machine) 0)
                   (division-copy-loop-count count)))
   :hints (("Goal" :in-theory (disable division-read-limbs)))))

(local
 (defthm division-copy-call-passes-input-view
   (implies (division-copy-call-ready-p value count world)
            (let ((start (proof-advance 2 world)))
              (and (proof-integer-view-p value (proof-world-reg 0 start) count start)
                   (proof-span-p (proof-world-reg 1 start) (division-view-bytes count))
                   (not (proof-world-stop start))
                   (division-copy-setup-output-p count world start)
                   (division-before-cuts-p 2 (list (proof-world-reg 30 world)) world))))
   :hints (("Goal"
            :use ((:instance division-copy-setup-prefix-advances (cuts (list (proof-world-reg 30 world))))
                  (:instance division-integer-view-after-equal-memory
                             (address (proof-world-reg 0 world)) (before world) (after (proof-advance 2 world))))
            :in-theory (disable proof-integer-view-p proof-span-p division-view-bytes
                                division-copy-prefix-ready-p division-copy-setup-inputs-p
                                division-copy-call-words)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-copy-call-returns-view
  (let* ((counts (division-copy-call-counts count))
         (steps (division-step-sum counts))
         (cuts (list (proof-world-reg 30 world)))
         (after (proof-advance steps world)))
    (implies (division-copy-call-ready-p value count world)
             (and (proof-segment-p steps cuts world :cut after)
                  (proof-integer-view-p value (proof-world-reg 1 world) count after)
                  (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 world))
                  (equal (proof-world-reg 1 after) (proof-world-reg 1 world))
                  (equal (proof-world-reg 9 after) (proof-world-reg 9 world))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 world))
                  (equal (proof-world-reg 20 after) (proof-world-reg 20 world))
                  (equal (proof-world-reg 21 after) (proof-world-reg 21 world))
                  (equal (proof-world-reg 22 after) (proof-world-reg 22 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world))))))
  :hints (("Goal"
           :use ((:instance division-copy-call-passes-input-view)
                 (:instance division-copy-loop-produces-view (world (proof-advance 2 world)))
                 (:instance division-copy-return-prefix-advances
                            (cuts (list (proof-world-reg 30 world)))
                            (world (proof-advance (division-copy-loop-count count) (proof-advance 2 world))))
                 (:instance division-advance-chain-sum (counts (division-copy-call-counts count)))
                 (:instance division-chain-keeps-before-cuts
                            (counts (division-copy-call-counts count)) (cuts (list (proof-world-reg 30 world))))
                 (:instance division-segment-from-cut-free-prefix
                            (count (division-step-sum (division-copy-call-counts count)))
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance division-integer-view-after-equal-memory
                            (address (proof-world-reg 1 world))
                            (before (proof-advance (division-copy-loop-count count) (proof-advance 2 world)))
                            (after (proof-advance (division-step-sum (division-copy-call-counts count)) world))))
           :in-theory (disable division-copy-prefix-ready-p division-copy-prefix-steps division-read-limbs
                               division-step-sum proof-integer-view proof-span-p division-view-bytes
                               division-copy-setup-inputs-p)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
