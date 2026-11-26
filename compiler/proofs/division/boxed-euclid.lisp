(in-package "BOYMOO-PROOFS")

(include-book "boxed-divide")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable abs floor mod proof-step proof-advance proof-world-reg proof-world-pc
                     proof-world-machine proof-world-stop proof-load-word proof-segment-p
                     division-before-cuts-p division-instruction-sequence-ready-p
                     division-unsigned-ready-p division-unsigned-steps division-result-view-count
                     proof-gcd-p proof-integer-view-p proof-memory-span-agrees-p
                     boymoo-model::a64-sp boymoo-model::a64-memory)))

(defun division-gcd-magnitude (a b)
  (mv-let (g left right)
    (division-euclid (abs a) b)
    (declare (ignore left right))
    g))

(defthm division-gcd-magnitude-satisfies-contract
  (implies (and (integerp a) (natp b))
           (proof-gcd-p a b (division-gcd-magnitude a b)))
  :hints (("Goal" :use (:instance division-euclid-gcd-contract)
                  :in-theory (disable division-euclid)))
  :rule-classes nil)

(local
 (defthm division-absolute-word-is-natural
   (implies (integerp value) (natp (abs value)))
   :hints (("Goal" :in-theory (enable abs)))))

(local
 (defthm division-remainder-keeps-gcd-magnitude
   (implies (and (integerp a) (posp b))
            (equal (division-gcd-magnitude a b) (division-gcd-magnitude b (mod (abs a) b))))
   :hints (("Goal"
            :expand ((division-euclid (abs a) b))
            :in-theory (disable division-euclid)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-gcd-magnitude-at-base
   (implies (and (integerp a) (or (equal b 0) (equal b 1)))
            (equal (division-gcd-magnitude a b) (if (equal b 1) 1 (abs a))))
   :hints (("Goal"
            :cases ((equal b 0))
            :use ((:instance division-remainder-keeps-gcd-magnitude (b 1))
                  (:instance division-remainder-unique (a (abs a)) (b 1) (q (abs a)) (r 0)))
            :in-theory (enable abs)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-unstopped-cut-is-at-cut-address
   (implies (and (eq (mv-nth 0 (proof-run count cuts world)) :cut)
                 (not (proof-world-stop (mv-nth 1 (proof-run count cuts world)))))
            (member-equal (proof-world-pc (mv-nth 1 (proof-run count cuts world))) cuts))
   :hints (("Goal" :induct (proof-run count cuts world)))
   :rule-classes nil))

(local
 (defthm division-unstopped-segment-returns-to-cut-pc
   (implies (and (proof-segment-p count (list target) world :cut after)
                 (not (proof-world-stop after)))
            (equal (proof-world-pc after) target))
   :hints (("Goal"
            :use (:instance division-unstopped-cut-is-at-cut-address (cuts (list target)))
            :in-theory (e/d (proof-segment-p) (proof-run))
            :do-not-induct t))
   :rule-classes nil))

(defun division-boxed-gcd-count (register world)
  (division-result-view-count (proof-world-reg register world) world))

(defun division-boxed-gcd-select-steps (world)
  (len (division-boxed-gcd-select-instructions (division-boxed-gcd-count 22 world))))

(defun division-boxed-gcd-selected (world)
  (proof-advance (division-boxed-gcd-select-steps world) world))

(defun division-boxed-gcd-entered (world)
  (proof-advance 7 (division-boxed-gcd-selected world)))

(defun division-boxed-gcd-divide-steps (plan world)
  (division-unsigned-steps (division-boxed-gcd-count 21 world) (division-boxed-gcd-count 22 world)
                           (car plan) (cdr plan) (division-boxed-gcd-entered world)))

(defun division-boxed-gcd-divided (plan world)
  (proof-advance (division-boxed-gcd-divide-steps plan world) (division-boxed-gcd-entered world)))

(defun division-boxed-gcd-iteration-steps (plan world)
  (+ (division-boxed-gcd-select-steps world) 12 (division-boxed-gcd-divide-steps plan world)))

(defun division-boxed-gcd-next (plan world)
  (proof-advance (division-boxed-gcd-iteration-steps plan world) world))

(defun division-boxed-gcd-select-ready-p (b world)
  (let ((count (division-boxed-gcd-count 22 world)))
    (and (division-boxed-gcd-select-inputs-p b count world)
         (division-instruction-sequence-ready-p
          (division-boxed-gcd-select-instructions count)
          (list (+ (division-boxed-gcd-select-offset b) (proof-world-pc world))) world))))

(defun division-boxed-gcd-iteration-ready-p (a b plan world)
  (let* ((a-count (division-boxed-gcd-count 21 world))
         (b-count (division-boxed-gcd-count 22 world))
         (selected (division-boxed-gcd-selected world))
         (entered (division-boxed-gcd-entered world))
         (divided (division-boxed-gcd-divided plan world))
         (b-address (proof-world-reg 22 world))
         (r-address (proof-world-reg 3 entered))
         (slot (division-boxed-remainder-slot divided))
         (b-size (division-view-bytes b-count))
         (r-size (division-view-bytes (division-result-view-count r-address divided))))
    (and (integerp a) (posp b) (< 1 b)
         (proof-integer-view-p a (proof-world-reg 21 world) a-count world)
         (division-boxed-gcd-select-ready-p b world)
         (division-boxed-inner-call-inputs-p t selected)
         (division-instruction-sequence-ready-p (division-boxed-inner-call-instructions t)
                                                (list (division-boxed-inner-target t selected)) selected)
         (division-unsigned-ready-p a b a-count b-count (car plan) (cdr plan) entered)
         (not (proof-world-stop divided))
         (equal (proof-load-word slot (proof-world-machine divided)) r-address)
         (proof-span-p b-address b-size) (proof-span-p r-address r-size)
         (proof-memory-span-agrees-p b-address (+ b-address b-size) world divided)
         (proof-disjoint-p b-address (+ b-address b-size) slot (+ slot 8))
         (proof-disjoint-p r-address (+ r-address r-size) slot (+ slot 8))
         (division-boxed-gcd-rotate-inputs-p divided)
         (division-instruction-sequence-ready-p
          *division-boxed-gcd-rotate-instructions*
          (list (+ *division-gcd-rotate-to-loop-offset* (proof-world-pc divided))) divided))))

(local
 (defthm division-boxed-gcd-divide-returns-remainder
   (let* ((divided (division-boxed-gcd-divided plan world))
          (r (mod (abs a) b))
          (slot (division-boxed-remainder-slot divided))
          (r-address (proof-load-word slot (proof-world-machine divided))))
     (implies (division-boxed-gcd-iteration-ready-p a b plan world)
              (and (proof-integer-view-p b (proof-world-reg 22 divided) (division-boxed-gcd-count 22 world) divided)
                   (proof-integer-view-p r r-address (division-result-view-count r-address divided) divided)
                   (equal (proof-world-reg 21 divided) (proof-world-reg 21 world))
                   (equal (proof-world-reg 22 divided) (proof-world-reg 22 world))
                   (equal (proof-world-pc divided)
                          (+ 4 *division-gcd-to-divide-offset* (proof-world-pc world))))))
   :hints (("Goal"
            :use ((:instance division-boxed-gcd-select-runs (value b) (count (division-boxed-gcd-count 22 world)))
                  (:instance division-boxed-call-enters-divider (gcd t) (world (division-boxed-gcd-selected world)))
                  (:instance division-unsigned-entry-to-return
                             (a-count (division-boxed-gcd-count 21 world)) (b-count (division-boxed-gcd-count 22 world))
                             (q-steps (car plan)) (r-steps (cdr plan)) (world (division-boxed-gcd-entered world)))
                  (:instance division-unstopped-segment-returns-to-cut-pc
                             (count (division-boxed-gcd-divide-steps plan world))
                             (target (proof-world-reg 30 (division-boxed-gcd-entered world)))
                             (after (division-boxed-gcd-divided plan world)) (world (division-boxed-gcd-entered world)))
                  (:instance division-integer-view-after-span-agreement
                             (value b) (count (division-boxed-gcd-count 22 world))
                             (address (proof-world-reg 22 world)) (start (proof-world-reg 22 world))
                             (end (+ (proof-world-reg 22 world)
                                     (division-view-bytes (division-boxed-gcd-count 22 world))))
                             (before world) (after (division-boxed-gcd-divided plan world))))
            :in-theory (disable division-boxed-gcd-rotate-inputs-p
                                division-boxed-inner-call-inputs-p division-boxed-inner-target
                                division-boxed-inner-call-instructions division-boxed-gcd-count
                                division-view-bytes division-boxed-remainder-slot)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-boxed-gcd-next-is-rotation
   (equal (division-boxed-gcd-next plan world)
          (proof-advance 5 (division-boxed-gcd-divided plan world)))
   :hints (("Goal"
            :use (:instance division-advance-chain-sum
                            (counts (list (division-boxed-gcd-select-steps world)
                                          7 (division-boxed-gcd-divide-steps plan world) 5)))
            :in-theory (disable division-boxed-gcd-select-steps proof-advance-append)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-boxed-gcd-iteration-executes
  (let* ((after (division-boxed-gcd-next plan world))
         (divided (division-boxed-gcd-divided plan world))
         (slot (division-boxed-remainder-slot divided))
         (r-address (proof-load-word slot (proof-world-machine divided)))
         (r (mod (abs a) b)))
    (implies (division-boxed-gcd-iteration-ready-p a b plan world)
             (and (proof-integer-view-p b (proof-world-reg 21 after) (division-boxed-gcd-count 22 world) after)
                  (proof-integer-view-p r (proof-world-reg 22 after) (division-result-view-count r-address divided) after)
                  (equal (proof-world-pc after) (proof-world-pc world))
                  (equal (proof-load-word slot (proof-world-machine after)) (proof-world-reg 21 world))
                  (natp r) (< r b))))
  :hints (("Goal"
           :use ((:instance division-boxed-gcd-divide-returns-remainder)
                 (:instance division-boxed-gcd-next-is-rotation)
                 (:instance division-boxed-gcd-euclidean-step
                            (b-count (division-boxed-gcd-count 22 world))
                            (r-count (division-result-view-count
                                      (proof-load-word (division-boxed-remainder-slot (division-boxed-gcd-divided plan world))
                                                       (proof-world-machine (division-boxed-gcd-divided plan world)))
                                      (division-boxed-gcd-divided plan world)))
                            (world (division-boxed-gcd-divided plan world)))
                 (:instance division-boxed-gcd-rotates-views
                            (world (division-boxed-gcd-divided plan world))))
           :in-theory (disable division-boxed-gcd-divided division-boxed-gcd-next division-boxed-gcd-select-ready-p
                               division-boxed-inner-call-inputs-p division-boxed-inner-call-instructions
                               division-boxed-inner-target division-boxed-gcd-rotate-inputs-p division-view-bytes)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defconst *division-gcd-loop-to-epilogue*
  (- (division-runtime-offset "rt:z-division-return") (division-runtime-offset "rt:z-gcd-loop")))

(defun division-boxed-gcd-base-count (b world)
  (division-boxed-gcd-count (if (equal b 1) 22 21) world))

(defun division-boxed-gcd-base-steps (b world)
  (+ (division-boxed-gcd-select-steps world) (if (equal b 1) 2 3)))

(defun division-boxed-gcd-base-ready-p (a b world)
  (let* ((one (equal b 1))
         (selected (division-boxed-gcd-selected world))
         (instructions (division-boxed-gcd-finish-instructions one))
         (target (division-boxed-gcd-finish-target one selected))
         (address (proof-world-reg (if one 22 21) world)))
    (and (integerp a) (or (equal b 0) one)
         (proof-integer-view-p a (proof-world-reg 21 world) (division-boxed-gcd-count 21 world) world)
         (division-boxed-gcd-select-ready-p b world)
         (proof-span-p address (division-view-bytes (division-boxed-gcd-base-count b world)))
         (unsigned-byte-p 64 target)
         (division-instruction-sequence-ready-p instructions (list target) selected))))

(local
 (defthm division-boxed-gcd-base-has-current-view
   (let* ((one (equal b 1))
          (selected (division-boxed-gcd-selected world))
          (address (division-boxed-gcd-finish-address one selected)))
     (implies (division-boxed-gcd-base-ready-p a b world)
              (and (proof-integer-view-p (if one 1 a) address (division-boxed-gcd-base-count b world) selected)
                   (proof-span-p address (division-view-bytes (division-boxed-gcd-base-count b world)))
                   (division-ordinary-world-p selected)
                   (equal (proof-world-pc selected) (+ (division-boxed-gcd-select-offset b) (proof-world-pc world))))))
   :hints (("Goal"
            :cases ((equal b 1))
            :use ((:instance division-boxed-gcd-select-runs (value b) (count (division-boxed-gcd-count 22 world)))
                  (:instance division-integer-view-after-equal-memory
                             (value (if (equal b 1) 1 a)) (count (division-boxed-gcd-base-count b world))
                             (address (proof-world-reg (if (equal b 1) 22 21) world))
                             (before world) (after (division-boxed-gcd-selected world))))
            :in-theory (disable division-boxed-gcd-select-instructions division-boxed-gcd-finish-instructions
                                division-boxed-gcd-select-offset)
            :do-not '(generalize fertilize)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm division-boxed-gcd-base-advance
   (equal (proof-advance (division-boxed-gcd-base-steps b world) world)
          (proof-advance (if (equal b 1) 2 3) (division-boxed-gcd-selected world)))
   :hints (("Goal"
            :use (:instance proof-advance-append
                            (prefix (division-boxed-gcd-select-steps world)) (suffix (if (equal b 1) 2 3)))
            :in-theory (disable division-boxed-gcd-select-steps proof-advance-append)))))

(defthm division-boxed-gcd-base-reaches-epilogue
  (let* ((after (proof-advance (division-boxed-gcd-base-steps b world) world))
         (value (division-gcd-magnitude a b)))
    (implies (division-boxed-gcd-base-ready-p a b world)
             (and (natp b)
                  (proof-integer-view-p value (proof-world-reg 0 after)
                                        (division-result-view-count (proof-world-reg 0 after) after) after)
                  (equal (proof-world-pc after) (+ *division-gcd-loop-to-epilogue* (proof-world-pc world))))))
  :hints (("Goal"
           :cases ((equal b 1))
           :use ((:instance division-boxed-gcd-base-has-current-view)
                 (:instance division-gcd-magnitude-at-base)
                 (:instance division-boxed-gcd-base-advance)
                 (:instance division-boxed-gcd-finishes-with-natural-view
                            (one (equal b 1)) (count (division-boxed-gcd-base-count b world))
                            (world (division-boxed-gcd-selected world)))
                 (:instance division-boxed-gcd-finish-effects (one (equal b 1)) (world (division-boxed-gcd-selected world)))
                 (:instance division-instruction-sequence-advances
                            (instructions (division-boxed-gcd-finish-instructions (equal b 1)))
                            (cuts (list (division-boxed-gcd-finish-target (equal b 1) (division-boxed-gcd-selected world))))
                            (world (division-boxed-gcd-selected world)))
                 (:instance division-view-count-after-header
                            (value (division-gcd-magnitude a b)) (count (division-boxed-gcd-base-count b world))
                            (address (proof-world-reg 0 (proof-advance (division-boxed-gcd-base-steps b world) world)))
                            (world (proof-advance (division-boxed-gcd-base-steps b world) world))))
           :in-theory (disable division-gcd-magnitude division-boxed-gcd-select-ready-p
                               division-boxed-gcd-base-steps division-boxed-gcd-base-advance
                               division-boxed-gcd-selected division-boxed-gcd-select-steps division-instruction-sequence)
           :do-not '(generalize fertilize)
           :do-not-induct t))
  :rule-classes nil)

(defun division-boxed-gcd-loop-ready-p (plans a b world)
  (if (atom plans)
      (and (null plans) (division-boxed-gcd-base-ready-p a b world))
    (and (division-boxed-gcd-iteration-ready-p a b (car plans) world)
         (division-boxed-gcd-loop-ready-p (cdr plans) b (mod (abs a) b)
                                          (division-boxed-gcd-next (car plans) world)))))

(defun division-boxed-gcd-loop-steps (plans a b world)
  (if (atom plans)
      (division-boxed-gcd-base-steps b world)
    (+ (division-boxed-gcd-iteration-steps (car plans) world)
       (division-boxed-gcd-loop-steps (cdr plans) b (mod (abs a) b)
                                      (division-boxed-gcd-next (car plans) world)))))

(local
 (defthm division-boxed-gcd-iteration-steps-natural
   (natp (division-boxed-gcd-iteration-steps plan world))
   :rule-classes :type-prescription))

(local
 (defthm division-boxed-gcd-loop-steps-natural
   (natp (division-boxed-gcd-loop-steps plans a b world))
   :hints (("Goal" :induct (division-boxed-gcd-loop-steps plans a b world)))
   :rule-classes :type-prescription))

(local
 (defthm division-boxed-gcd-loop-advance-past-first
   (implies (consp plans)
            (let ((next (division-boxed-gcd-next (car plans) world)))
              (equal (proof-advance (division-boxed-gcd-loop-steps plans a b world) world)
                     (proof-advance (division-boxed-gcd-loop-steps (cdr plans) b (mod (abs a) b) next) next))))
   :hints (("Goal"
            :use (:instance proof-advance-append
                            (prefix (division-boxed-gcd-iteration-steps (car plans) world))
                            (suffix (division-boxed-gcd-loop-steps (cdr plans) b (mod (abs a) b)
                                                                   (division-boxed-gcd-next (car plans) world))))
            :in-theory (disable division-boxed-gcd-iteration-steps proof-advance-append)
            :do-not-induct t))
   :rule-classes nil))

(defthm division-boxed-gcd-loop-computes-natural-view
  (let ((after (proof-advance (division-boxed-gcd-loop-steps plans a b world) world)))
    (implies (division-boxed-gcd-loop-ready-p plans a b world)
             (and (proof-integer-view-p (division-gcd-magnitude a b) (proof-world-reg 0 after)
                                        (division-result-view-count (proof-world-reg 0 after) after) after)
                  (equal (proof-world-pc after) (+ *division-gcd-loop-to-epilogue* (proof-world-pc world)))
                  (<= (len plans) b))))
  :hints (("Goal"
           :induct (division-boxed-gcd-loop-steps plans a b world)
           :in-theory (disable division-gcd-magnitude division-boxed-gcd-base-ready-p
                               division-boxed-gcd-iteration-ready-p division-boxed-gcd-select-steps
                               division-boxed-gcd-base-steps division-boxed-gcd-iteration-steps division-boxed-gcd-next))
          ("Subgoal *1/1"
           :use (:instance division-boxed-gcd-base-reaches-epilogue))
          ("Subgoal *1/2"
           :use ((:instance division-boxed-gcd-loop-advance-past-first)
                 (:instance division-boxed-gcd-iteration-executes (plan (car plans)))
                 (:instance division-remainder-keeps-gcd-magnitude))
           :in-theory (disable division-gcd-magnitude division-boxed-gcd-base-ready-p
                               division-boxed-gcd-select-ready-p division-boxed-gcd-select-steps
                               division-boxed-gcd-base-steps division-boxed-gcd-iteration-steps
                               division-boxed-gcd-next division-boxed-gcd-divided
                               division-boxed-inner-call-inputs-p division-boxed-gcd-rotate-inputs-p)))
  :rule-classes nil)
