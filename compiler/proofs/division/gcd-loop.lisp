(in-package "BOYMOO-PROOFS")

(include-book "machine-arithmetic")
(include-book "euclid")

(logic)
(set-verify-guards-eagerness 0)

(defun division-gcd-word-loop-ready-p (fuel world)
  (declare (xargs :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable proof-advance division-gcd-word-iteration-ready-p)))))
  (if (equal (proof-world-reg 1 world) 0)
      t
    (and (not (zp fuel))
         (division-gcd-word-iteration-ready-p world)
         (division-gcd-word-loop-ready-p (1- fuel) (proof-advance 5 world)))))

(defun division-gcd-word-iterations (fuel world)
  (declare (xargs :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable proof-advance)))))
  (if (or (zp fuel) (equal (proof-world-reg 1 world) 0))
      0
    (1+ (division-gcd-word-iterations (1- fuel) (proof-advance 5 world)))))

(local
 (defthm division-gcd-advance-zero
   (equal (proof-advance 0 world) world)
   :hints (("Goal" :expand ((proof-advance 0 world))))))

(defthm division-gcd-word-loop-correct
  (implies (and (natp (proof-world-reg 0 world))
                (natp (proof-world-reg 1 world))
                (division-gcd-word-loop-ready-p fuel world))
           (let* ((a (proof-world-reg 0 world))
                  (b (proof-world-reg 1 world))
                  (count (division-gcd-word-iterations fuel world))
                  (after (proof-advance (* 5 count) world)))
             (and (<= count b)
                  (equal (proof-world-reg 1 after) 0)
                  (equal (proof-world-reg 0 after) (mv-nth 0 (division-euclid a b)))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (proof-world-pc after)
                         (if (equal b 0) (proof-world-pc world) (+ 20 (proof-world-pc world))))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world)))))
  :hints (("Goal"
           :induct (division-gcd-word-loop-ready-p fuel world)
           :in-theory (disable mod proof-step proof-world-pc proof-world-reg proof-world-stop
                               boymoo-model::a64-memory division-gcd-word-iteration-ready-p
                               (:definition proof-advance)))
          ("Subgoal *1/2"
           :use ((:instance division-gcd-word-iteration-advances)
                 (:instance proof-advance-append
                            (prefix 5)
                            (suffix (* 5 (division-gcd-word-iterations
                                          (1- fuel) (proof-advance 5 world))))))))
  :rule-classes nil)

(defthm division-gcd-word-loop-realizes-contract
  (implies (and (natp (proof-world-reg 0 world))
                (posp (proof-world-reg 1 world))
                (division-gcd-word-loop-ready-p fuel world))
           (let* ((count (division-gcd-word-iterations fuel world))
                  (after (proof-advance (* 5 count) world)))
             (proof-gcd-p (proof-world-reg 0 world) (proof-world-reg 1 world)
                          (proof-world-reg 0 after))))
  :hints (("Goal"
           :use ((:instance division-gcd-word-loop-correct)
                 (:instance division-euclid-gcd-contract
                            (a (proof-world-reg 0 world)) (b (proof-world-reg 1 world))))
           :in-theory (disable proof-advance proof-world-reg proof-gcd-p division-euclid
                               division-gcd-word-loop-ready-p division-gcd-word-iterations)))
  :rule-classes nil)

(defthm division-gcd-word-loop-zero-first
  (implies (and (equal (proof-world-reg 0 world) 0)
                (posp (proof-world-reg 1 world))
                (division-gcd-word-iteration-ready-p world))
           (let ((after (proof-advance 5 world)))
             (and (equal (proof-world-reg 0 after) (proof-world-reg 1 world))
                  (equal (proof-world-reg 1 after) 0)
                  (equal (proof-world-pc after) (+ 20 (proof-world-pc world))))))
  :hints (("Goal"
           :use (:instance division-gcd-word-iteration-advances)
           :in-theory (disable mod proof-advance proof-step proof-world-reg proof-world-pc
                               division-gcd-word-iteration-ready-p)))
  :rule-classes nil)

(defun division-gcd-immediate-loop-start (world)
  (proof-advance 5 world))

(defun division-gcd-immediate-count (fuel world)
  (division-gcd-word-iterations fuel (division-gcd-immediate-loop-start world)))

(defun division-gcd-immediate-loop-end (fuel world)
  (proof-advance (* 5 (division-gcd-immediate-count fuel world))
                 (division-gcd-immediate-loop-start world)))

(defun division-gcd-immediate-ready-p (fuel world)
  (and (division-instruction-sequence-ready-p
        *division-gcd-immediate-setup-instructions* (list (+ 20 (proof-world-pc world))) world)
       (division-gcd-word-loop-ready-p fuel (division-gcd-immediate-loop-start world))
       (division-instruction-sequence-ready-p
        *division-immediate-return-instructions* (list (proof-world-reg 30 world))
        (division-gcd-immediate-loop-end fuel world))))

(defthm division-gcd-immediate-returns
  (implies (and (division-gcd-immediate-inputs-p a b world)
                (division-gcd-immediate-ready-p fuel world))
           (let* ((steps (+ 8 (* 5 (division-gcd-immediate-count fuel world))))
                  (after (proof-advance steps world))
                  (value (proof-world-reg 0 (division-gcd-immediate-loop-end fuel world))))
             (and (proof-gcd-p a b value)
                  (equal (proof-world-reg 0 after) (proof-integer-word value))
                  (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world)))))
  :hints (("Goal"
           :use ((:instance division-gcd-immediate-setup-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-gcd-immediate-setup-instructions*)
                            (cuts (list (+ 20 (proof-world-pc world)))))
                 (:instance division-gcd-word-loop-correct
                            (world (division-gcd-immediate-loop-start world)))
                 (:instance division-euclid-gcd-contract)
                 (:instance division-gcd-bound
                            (g (proof-world-reg 0 (division-gcd-immediate-loop-end fuel world))))
                 (:instance division-instruction-sequence-advances
                            (instructions *division-immediate-return-instructions*)
                            (cuts (list (proof-world-reg 30 world)))
                            (world (division-gcd-immediate-loop-end fuel world)))
                 (:instance division-immediate-result-return-effects
                            (world (division-gcd-immediate-loop-end fuel world))
                            (value (proof-world-reg 0 (division-gcd-immediate-loop-end fuel world))))
                 (:instance proof-advance-append (prefix 5)
                            (suffix (+ 3 (* 5 (division-gcd-immediate-count fuel world)))))
                 (:instance proof-advance-append
                            (prefix (* 5 (division-gcd-immediate-count fuel world))) (suffix 3)
                            (world (division-gcd-immediate-loop-start world))))
           :in-theory (disable proof-advance proof-step proof-world-pc proof-world-reg proof-world-stop
                               boymoo-model::a64-unsigned boymoo-model::a64-memory proof-integer-word
                               division-a64-unsigned-is-remainder proof-gcd-p division-euclid
                               division-instruction-sequence division-instruction-sequence-ready-p
                               division-gcd-word-iterations division-gcd-word-loop-ready-p)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-gcd-word-entry-after-iteration
   (implies (division-gcd-word-loop-entry-p world)
            (let ((next (proof-advance 5 world)))
              (or (equal (proof-world-reg 1 next) 0)
                  (division-gcd-word-loop-entry-p next))))
   :hints (("Goal"
            :use ((:instance division-gcd-word-iteration-ready-from-code)
                  (:instance division-gcd-word-iteration-advances)
                  (:instance division-instructions-placement-preserved
                             (instructions *division-gcd-word-instructions*)
                             (address (proof-world-pc world))
                             (before world) (after (proof-advance 5 world))))
            :in-theory (disable mod proof-advance proof-world-reg proof-world-pc proof-world-stop
                                proof-world-regions boymoo-model::a64-memory proof-instructions-at-p
                                division-gcd-word-iteration-ready-p)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-gcd-word-loop-ready-from-code
  (implies (and (natp fuel) (natp (proof-world-reg 1 world))
                (<= (proof-world-reg 1 world) fuel)
                (or (equal (proof-world-reg 1 world) 0)
                    (division-gcd-word-loop-entry-p world)))
           (division-gcd-word-loop-ready-p fuel world))
  :hints (("Goal"
           :induct (division-gcd-word-iterations fuel world)
           :in-theory (disable mod proof-advance proof-world-reg proof-world-pc proof-world-stop
                               division-gcd-word-loop-entry-p division-gcd-word-iteration-ready-p))
          ("Subgoal *1/2"
           :use ((:instance division-gcd-word-entry-after-iteration)
                 (:instance division-gcd-word-iteration-ready-from-code)
                 (:instance division-gcd-word-iteration-advances))))
  :rule-classes nil)

(defthm division-gcd-immediate-returns-from-loop-entry
  (let* ((entry (division-gcd-immediate-loop-start world))
         (exit (division-gcd-immediate-loop-end b world))
         (value (proof-world-reg 0 exit))
         (after (proof-advance (+ 8 (* 5 (division-gcd-immediate-count b world))) world)))
    (implies (and (division-gcd-immediate-inputs-p a b world)
                  (division-instruction-sequence-ready-p
                   *division-gcd-immediate-setup-instructions* (list (+ 20 (proof-world-pc world))) world)
                  (division-gcd-word-loop-entry-p entry)
                  (division-instruction-sequence-ready-p
                   *division-immediate-return-instructions* (list (proof-world-reg 30 world)) exit))
             (and (proof-gcd-p a b value)
                  (equal (proof-world-reg 0 after) (proof-integer-word value))
                  (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine world)))
                  (equal (proof-world-stop after) (proof-world-stop world)))))
  :hints (("Goal"
           :use ((:instance division-gcd-immediate-setup-effects)
                 (:instance division-instruction-sequence-advances
                            (instructions *division-gcd-immediate-setup-instructions*)
                            (cuts (list (+ 20 (proof-world-pc world)))))
                 (:instance division-gcd-word-loop-ready-from-code
                            (fuel b) (world (division-gcd-immediate-loop-start world)))
                 (:instance division-gcd-immediate-returns (fuel b)))
           :in-theory (disable proof-advance proof-world-reg proof-world-pc proof-integer-word proof-gcd-p
                               division-gcd-immediate-count division-gcd-immediate-loop-end
                               division-gcd-word-loop-entry-p division-gcd-word-loop-ready-p
                               division-instruction-sequence division-instruction-sequence-ready-p)
           :do-not-induct t))
  :rule-classes nil)
