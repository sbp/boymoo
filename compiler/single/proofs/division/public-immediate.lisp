(in-package "BOYMOO-PROOFS")

(include-book "dispatch")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable floor mod ash proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-world-regions proof-load-word
                     proof-instruction-effect proof-segment-p division-before-cuts-p
                     division-instruction-prefix-ready-p division-instruction-sequence-ready-p
                     boymoo-model::a64-memory boymoo-model::a64-sp boymoo-model::a64-unsigned)))

(defun division-public-prefix-count (gcd world)
  (division-public-dispatch-steps gcd (proof-world-reg 0 world) (proof-world-reg 1 world)))

(defun division-public-body (gcd world)
  (proof-advance (division-public-prefix-count gcd world) world))

(defun division-public-prefix-ready-p (gcd world)
  (and (not (proof-world-stop world))
       (division-public-dispatch-layout-p gcd world)
       (division-instruction-prefix-ready-p (division-public-instructions gcd world)
                                            (list (proof-world-reg 30 world)) world)))

(local
 (defthm division-public-prefix-count-is-code-length
   (equal (len (division-public-instructions gcd world)) (division-public-prefix-count gcd world))))

(defthm division-public-prefix-passes-arguments
  (implies (division-public-prefix-ready-p gcd world)
           (and (division-before-cuts-p (division-public-prefix-count gcd world)
                                       (list (proof-world-reg 30 world)) world)
                (division-public-dispatch-output-p gcd world (division-public-body gcd world))))
  :hints (("Goal"
           :use ((:instance division-public-dispatch-effects)
                 (:instance division-instruction-prefix-advances
                            (instructions (division-public-instructions gcd world))
                            (cuts (list (proof-world-reg 30 world)))))
           :in-theory (disable division-public-dispatch-output-p division-public-dispatch-layout-p
                               division-public-instructions division-public-prefix-count division-instruction-sequence)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-public-two-immediates-dispatch
   (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b)
                 (not (equal b 1)) (or (not gcd) (not (equal a 1)))
                 (equal (proof-world-reg 0 world) (proof-integer-word a))
                 (equal (proof-world-reg 1 world) (proof-integer-word b)))
            (equal (division-public-prefix-count gcd world) (if gcd 7 5)))
   :hints (("Goal"
            :use ((:instance division-one-word-identifies-one (value a))
                  (:instance division-one-word-identifies-one (value b))
                  (:instance division-immediate-word-has-low-bit (value a))
                  (:instance division-immediate-word-has-low-bit (value b)))
            :in-theory (disable proof-integer-word division-one-word-identifies-one
                                division-immediate-word-has-low-bit)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-public-body-segment-composes
   (let* ((prefix (division-public-prefix-count gcd world))
          (body (division-public-body gcd world))
          (cuts (list (proof-world-reg 30 world)))
          (after (proof-advance suffix body)))
     (implies (and (division-public-prefix-ready-p gcd world) (natp suffix)
                   (proof-segment-p suffix cuts body :cut after))
              (and (proof-segment-p (+ prefix suffix) cuts world :cut after)
                   (equal (proof-advance (+ prefix suffix) world) after))))
   :hints (("Goal"
            :use ((:instance division-public-prefix-passes-arguments)
                  (:instance division-run-after-cut-free-prefix
                             (prefix (division-public-prefix-count gcd world))
                             (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-advance-append (prefix (division-public-prefix-count gcd world))))
            :in-theory (e/d (proof-segment-p)
                            (division-public-prefix-ready-p division-public-prefix-count
                             division-public-dispatch-output-p proof-run division-run-after-cut-free-prefix
                             proof-advance-append))
            :do-not-induct t))
   :rule-classes nil))

(defthm division-public-immediate-quotient-returns
  (let* ((body (division-public-body nil world))
         (cuts (list (proof-world-reg 30 world)))
         (after (proof-advance 11 world)))
    (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b)
                  (posp b) (not (equal b 1)) (proof-exact-quotient-p a b quotient)
                  (equal (proof-world-reg 0 world) (proof-integer-word a))
                  (equal (proof-world-reg 1 world) (proof-integer-word b))
                  (division-public-prefix-ready-p nil world)
                  (division-instruction-sequence-ready-p *division-immediate-quotient-instructions* cuts body))
             (and (proof-segment-p 11 cuts world :cut after)
                  (equal (proof-world-reg 0 after) (proof-integer-word quotient)))))
  :hints (("Goal"
           :use ((:instance division-public-two-immediates-dispatch (gcd nil))
                 (:instance division-public-prefix-passes-arguments (gcd nil))
                 (:instance division-exact-immediate-fits (q quotient))
                 (:instance division-immediate-quotient-returns (world (division-public-body nil world)))
                 (:instance division-instruction-sequence-advances
                            (instructions *division-immediate-quotient-instructions*)
                            (cuts (list (proof-world-reg 30 world)))
                            (world (division-public-body nil world)))
                 (:instance division-public-body-segment-composes (gcd nil) (suffix 6)))
           :in-theory (disable division-public-prefix-count division-public-body
                               division-public-prefix-ready-p division-public-target division-public-route
                               proof-immediate-integer-p proof-exact-quotient-p proof-integer-word
                               division-instruction-sequence)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-public-gcd-body-steps (b world)
  (+ 8 (* 5 (division-gcd-immediate-count b (division-public-body t world)))))

(defun division-public-gcd-value (b world)
  (proof-world-reg 0 (division-gcd-immediate-loop-end b (division-public-body t world))))

(defthm division-gcd-contract-at-zero-first
  (implies (and (posp b) (proof-gcd-p 0 b gcd))
           (equal gcd b))
  :hints (("Goal" :in-theory (enable proof-gcd-p)))
  :rule-classes nil)

(defthm division-public-immediate-gcd-returns
  (let* ((body (division-public-body t world))
         (cuts (list (proof-world-reg 30 world)))
         (body-steps (division-public-gcd-body-steps b world))
         (steps (+ 7 body-steps))
         (after (proof-advance steps world))
         (value (division-public-gcd-value b world)))
    (implies (and (proof-immediate-integer-p a) (proof-immediate-integer-p b)
                  (posp b) (not (equal a 1)) (not (equal b 1))
                  (equal (proof-world-reg 0 world) (proof-integer-word a))
                  (equal (proof-world-reg 1 world) (proof-integer-word b))
                  (division-public-prefix-ready-p t world)
                  (unsigned-byte-p 64 (+ 20 (proof-world-pc body)))
                  (division-instruction-sequence-ready-p
                   *division-gcd-immediate-setup-instructions* (list (+ 20 (proof-world-pc body))) body)
                  (division-gcd-word-loop-entry-p (division-gcd-immediate-loop-start body))
                  (division-instruction-sequence-ready-p
                   *division-immediate-return-instructions* cuts (division-gcd-immediate-loop-end b body))
                  (division-before-cuts-p body-steps cuts body))
             (and (proof-segment-p steps cuts world :cut after)
                  (proof-gcd-p a b value)
                  (equal (proof-world-reg 0 after) (proof-integer-word value))
                  (implies (equal a 0)
                           (equal (proof-world-reg 0 after) (proof-integer-word b))))))
  :hints (("Goal"
           :use ((:instance division-public-two-immediates-dispatch (gcd t))
                 (:instance division-public-prefix-passes-arguments (gcd t))
                 (:instance division-gcd-contract-at-zero-first (gcd (division-public-gcd-value b world)))
                 (:instance division-gcd-immediate-returns-from-loop-entry (world (division-public-body t world)))
                 (:instance division-segment-from-cut-free-prefix
                            (count (division-public-gcd-body-steps b world))
                            (cuts (list (proof-world-reg 30 world)))
                            (world (division-public-body t world)))
                 (:instance division-public-body-segment-composes
                            (gcd t) (suffix (division-public-gcd-body-steps b world))))
           :in-theory (disable division-public-prefix-count division-public-body
                               division-public-dispatch-layout-p division-public-instructions
                               division-public-target division-public-route
                               proof-immediate-integer-p proof-integer-word proof-gcd-p
                               division-instruction-sequence division-gcd-word-loop-entry-p
                               division-gcd-immediate-loop-start division-gcd-immediate-loop-end
                               division-gcd-immediate-count)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm division-return-one-effects
   (let ((after (division-instruction-sequence *division-return-one-instructions* world)))
     (implies (division-ordinary-world-p world)
              (and (equal (proof-world-reg 0 after) (proof-integer-word 1))
                   (equal (proof-world-pc after) (proof-world-reg 30 world))
                   (equal (proof-world-stop after) (proof-world-stop world))
                   (equal (boymoo-model::a64-memory (proof-world-machine after))
                          (boymoo-model::a64-memory (proof-world-machine world))))))
   :rule-classes nil))

(local
 (defthm division-one-operand-gcd
   (implies (and (integerp a) (posp b) (or (equal a 1) (equal b 1)))
            (proof-gcd-p a b 1))
   :hints (("Goal"
            :cases ((equal b 1))
            :use (:instance division-gcd-witness-gives-contract (g 1)
                            (left (if (equal b 1) 0 1)) (right (if (equal b 1) 1 0)))
            :in-theory (disable proof-gcd-p)))
   :rule-classes nil))

(defthm division-public-gcd-by-one-returns
  (let* ((body (division-public-body t world))
         (cuts (list (proof-world-reg 30 world)))
         (steps (+ (division-public-prefix-count t world) 2))
         (after (proof-advance steps world)))
    (implies (and (integerp a) (posp b)
                  (or (and (equal a 1) (equal (proof-world-reg 0 world) (proof-integer-word 1)))
                      (and (equal b 1) (equal (proof-world-reg 1 world) (proof-integer-word 1))))
                  (division-public-prefix-ready-p t world)
                  (division-instruction-sequence-ready-p *division-return-one-instructions* cuts body))
             (and (proof-segment-p steps cuts world :cut after)
                  (proof-gcd-p a b 1)
                  (equal (proof-world-reg 0 after) (proof-integer-word 1)))))
  :hints (("Goal"
           :use ((:instance division-public-prefix-passes-arguments (gcd t))
                 (:instance division-one-operand-gcd)
                 (:instance division-return-one-effects (world (division-public-body t world)))
                 (:instance division-instruction-sequence-advances
                            (instructions *division-return-one-instructions*)
                            (cuts (list (proof-world-reg 30 world))) (world (division-public-body t world)))
                 (:instance division-instruction-sequence-runs-to-cut
                            (instructions *division-return-one-instructions*)
                            (cuts (list (proof-world-reg 30 world))) (world (division-public-body t world)))
                 (:instance division-public-body-segment-composes (gcd t) (suffix 2)))
           :in-theory (disable division-public-prefix-count division-public-body division-public-prefix-ready-p
                               division-public-target division-public-route proof-gcd-p division-instruction-sequence)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)
