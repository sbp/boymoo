(in-package "BOYMOO-PROOFS")

(include-book "returns")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-number-execute-block proof-segment-p
                     proof-number-checked-block-p proof-number-exact-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-reg-value-p proof-machine-value-p proof-heap-base proof-load-word
                     proof-number-classifier-path proof-number-datum-class
                     boymoo-model::a64-sp boymoo-model::a64-memory)))

(defund proof-number-classifier-after (world)
  (proof-number-execute-block (proof-number-classifier-path world) world))

(defund proof-number-classifier-trace-p (cuts world)
  (let ((path (proof-number-classifier-path world)))
    (and (not (eq (car (proof-world-machine world)) :svc))
         (unsigned-byte-p 64 (+ 52 (proof-world-pc world)))
         (proof-number-checked-block-p path (list (proof-world-reg 30 world)) world)
         (proof-number-checked-block-p path cuts world))))

(defthm proof-number-classification-keeps-values
  (let* ((after (proof-number-classifier-after world))
         (first (proof-world-machine world))
         (last (proof-world-machine after)))
    (implies (proof-number-classifier-trace-p cuts world)
             (and (proof-number-exact-prefix-p (len (proof-number-classifier-path world))
                                               cuts world after)
                  (equal (proof-world-pc after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp first))
                  (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory first))
                  (implies (proof-reg-value-p 0 value world objects packages)
                           (equal (proof-world-reg 3 after) (proof-number-datum-class value)))
                  (implies (not (member-equal register '(3 4 5)))
                           (and (equal (proof-world-reg register after) (proof-world-reg register world))
                                (equal (proof-reg-value-p register operand after objects packages)
                                       (proof-reg-value-p register operand world objects packages)))))))
  :hints (("Goal"
           :use (proof-number-classifier-returns proof-number-classifier-returns-datum-class
                 (:instance proof-number-classifier-returns (register 28))
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-classifier-path world)))
                 (:instance proof-number-reg-value-with-same-memory
                            (before world) (after (proof-number-classifier-after world))
                            (word (proof-world-reg register world)) (value operand)))
           :in-theory (e/d (proof-number-classifier-trace-p proof-number-classifier-after
                            proof-reg-value-p proof-heap-base)
                           (proof-number-word-class))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-types-second-ready (rational-only classifier world)
  (proof-number-execute-block
   (proof-number-types-second-code rational-only (proof-world-pc world) classifier) world))

(defund proof-number-types-second-trace-p (rational-only classifier cuts world)
  (let* ((code (proof-number-types-second-code rational-only (proof-world-pc world) classifier))
         (ready (proof-number-types-second-ready rational-only classifier world)))
    (and (not (eq (car (proof-world-machine world)) :svc))
         (unsigned-byte-p 64 (+ (proof-world-pc world) (if rational-only 28 24)))
         (unsigned-byte-p 64 classifier)
         (proof-number-checked-block-p code (list classifier) world)
         (proof-number-checked-block-p code cuts world)
         (proof-number-classifier-trace-p cuts ready))))

(defthm proof-number-types-classifies-second-value
  (let* ((code (proof-number-types-second-code rational-only (proof-world-pc world) classifier))
         (ready (proof-number-types-second-ready rational-only classifier world))
         (after (proof-number-classifier-after ready))
         (count (+ (len code) (len (proof-number-classifier-path ready))))
         (first (proof-world-machine world))
         (last (proof-world-machine after)))
    (implies (and (proof-number-types-second-trace-p rational-only classifier cuts world)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (equal (proof-world-reg 3 world) (proof-number-datum-class a)))
             (and (proof-number-exact-prefix-p count cuts world after)
                  (proof-reg-value-p 6 (if rational-only (rfix a) (fix a)) after objects packages)
                  (proof-reg-value-p 0 b after objects packages)
                  (equal (proof-world-reg 3 after) (proof-number-datum-class b))
                  (equal (proof-world-pc after) (+ (proof-world-pc world) (if rational-only 28 24)))
                  (implies (not rational-only)
                           (equal (proof-world-reg 7 after) (proof-number-datum-class a)))
                  (equal (boymoo-model::a64-sp last) (boymoo-model::a64-sp first))
                  (equal (boymoo-model::a64-memory last) (boymoo-model::a64-memory first)))))
  :hints (("Goal"
           :use (proof-number-types-call-second-classifier proof-number-types-save-first-value
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-types-second-code rational-only
                                           (proof-world-pc world) classifier)))
                 (:instance proof-number-classification-keeps-values
                            (world (proof-number-types-second-ready rational-only classifier world))
                            (register 0) (value b) (operand b))
                 (:instance proof-number-classification-keeps-values
                            (world (proof-number-types-second-ready rational-only classifier world))
                            (register 6) (value b) (operand (if rational-only (rfix a) (fix a))))
                 (:instance proof-number-classification-keeps-values
                            (world (proof-number-types-second-ready rational-only classifier world))
                            (register 7) (value b) (operand nil))
                 (:instance proof-number-exact-prefix-append
                            (prefix (len (proof-number-types-second-code rational-only
                                          (proof-world-pc world) classifier)))
                            (suffix (len (proof-number-classifier-path
                                          (proof-number-types-second-ready rational-only classifier world))))
                            (before world) (middle (proof-number-types-second-ready rational-only classifier world))
                            (after (proof-number-classifier-after
                                    (proof-number-types-second-ready rational-only classifier world)))))
           :in-theory (e/d (proof-number-types-second-trace-p proof-number-types-second-ready)
                           (proof-number-binary-types-p))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-types-first-ready (classifier world)
  (proof-number-execute-block
   (proof-number-types-first-code (proof-world-pc world) classifier) world))

(defund proof-number-types-first-trace-p (classifier cuts world)
  (let* ((machine (proof-world-machine world))
         (pc (proof-world-pc world))
         (code (proof-number-types-first-code pc classifier))
         (ready (proof-number-types-first-ready classifier world)))
    (and (not (eq (car machine) :svc))
         (proof-span-p (- (boymoo-model::a64-sp machine) 16) 16)
         (unsigned-byte-p 64 (+ 8 pc)) (unsigned-byte-p 64 classifier)
         (proof-number-checked-block-p code (list classifier) world)
         (proof-number-checked-block-p code cuts world)
         (proof-number-classifier-trace-p cuts ready))))

(local
 (defthm word-kept-with-memory
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (equal (proof-load-word address last) (proof-load-word address first)))
   :hints (("Goal"
            :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                            (boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(defthm proof-number-types-classifies-first-value
  (let* ((ready (proof-number-types-first-ready classifier world))
         (after (proof-number-classifier-after ready))
         (count (+ 2 (len (proof-number-classifier-path ready))))
         (saved (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
         (machine (proof-world-machine after)))
    (implies (and (proof-number-types-first-trace-p classifier cuts world)
                  (proof-reg-value-p 0 a ready objects packages)
                  (proof-reg-value-p 1 b ready objects packages))
             (and (proof-number-exact-prefix-p count cuts world after)
                  (equal (proof-world-pc after) (+ 8 (proof-world-pc world)))
                  (proof-reg-value-p 0 a after objects packages)
                  (proof-reg-value-p 1 b after objects packages)
                  (equal (proof-world-reg 3 after) (proof-number-datum-class a))
                  (equal (boymoo-model::a64-sp machine) saved)
                  (equal (proof-load-word saved machine) (proof-world-reg 29 world))
                  (equal (proof-load-word (+ 8 saved) machine) (proof-world-reg 30 world)))))
  :hints (("Goal"
           :use (proof-number-types-call-first-classifier
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-types-first-code (proof-world-pc world) classifier)))
                 (:instance proof-number-classification-keeps-values
                            (world (proof-number-types-first-ready classifier world))
                            (register 0) (value a) (operand a))
                 (:instance proof-number-classification-keeps-values
                            (world (proof-number-types-first-ready classifier world))
                            (register 1) (value a) (operand b))
                 (:instance proof-number-exact-prefix-append
                            (prefix 2)
                            (suffix (len (proof-number-classifier-path
                                          (proof-number-types-first-ready classifier world))))
                            (before world) (middle (proof-number-types-first-ready classifier world))
                            (after (proof-number-classifier-after
                                    (proof-number-types-first-ready classifier world))))
                 (:instance word-kept-with-memory
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (first (proof-world-machine (proof-number-types-first-ready classifier world)))
                            (last (proof-world-machine
                                   (proof-number-classifier-after
                                    (proof-number-types-first-ready classifier world)))))
                 (:instance word-kept-with-memory
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 8))
                            (first (proof-world-machine (proof-number-types-first-ready classifier world)))
                            (last (proof-world-machine
                                   (proof-number-classifier-after
                                    (proof-number-types-first-ready classifier world))))))
           :in-theory (e/d (proof-number-types-first-trace-p proof-number-types-first-ready
                            proof-number-types-first-code)
                           (proof-view proof-view-step))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-types-classified (rational-only classifier world)
  (proof-number-classifier-after
   (proof-number-types-second-ready rational-only classifier
                                    (proof-number-classifier-after
                                     (proof-number-types-first-ready classifier world)))))

(defund proof-number-types-classification-steps (rational-only classifier world)
  (let* ((first (proof-number-types-first-ready classifier world))
         (first-return (proof-number-classifier-after first))
         (second (proof-number-types-second-ready rational-only classifier first-return)))
    (+ 2 (len (proof-number-classifier-path first))
       (len (proof-number-types-second-code rational-only (proof-world-pc first-return) classifier))
       (len (proof-number-classifier-path second)))))

(defthm proof-number-types-classifies-operands
  (let* ((ready (proof-number-types-first-ready classifier world))
         (first (proof-number-classifier-after ready))
         (after (proof-number-types-classified rational-only classifier world))
         (machine (proof-world-machine after))
         (saved (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
         (steps (proof-number-types-classification-steps rational-only classifier world)))
    (implies (and (proof-number-types-first-trace-p classifier cuts world)
                  (proof-number-types-second-trace-p rational-only classifier cuts first)
                  (proof-reg-value-p 0 a ready objects packages)
                  (proof-reg-value-p 1 b ready objects packages))
             (and (proof-number-exact-prefix-p steps cuts world after)
                  (equal (proof-world-pc after) (+ (proof-world-pc world) (if rational-only 36 32)))
                  (proof-reg-value-p 6 (if rational-only (rfix a) (fix a)) after objects packages)
                  (proof-reg-value-p 0 b after objects packages)
                  (equal (proof-world-reg 3 after) (proof-number-datum-class b))
                  (implies (not rational-only)
                           (equal (proof-world-reg 7 after) (proof-number-datum-class a)))
                  (equal (boymoo-model::a64-sp machine) saved)
                  (equal (proof-load-word saved machine) (proof-world-reg 29 world))
                  (equal (proof-load-word (+ 8 saved) machine) (proof-world-reg 30 world)))))
  :hints (("Goal"
           :use (proof-number-types-classifies-first-value
                 (:instance proof-number-types-classifies-second-value
                            (world (proof-number-classifier-after
                                    (proof-number-types-first-ready classifier world))))
                 (:instance proof-number-exact-prefix-append
                            (prefix (+ 2 (len (proof-number-classifier-path
                                               (proof-number-types-first-ready classifier world)))))
                            (suffix (+ (len (proof-number-types-second-code
                                             rational-only
                                             (proof-world-pc (proof-number-classifier-after
                                                              (proof-number-types-first-ready classifier world)))
                                             classifier))
                                       (len (proof-number-classifier-path
                                             (proof-number-types-second-ready
                                              rational-only classifier (proof-number-classifier-after
                                                                        (proof-number-types-first-ready
                                                                         classifier world)))))))
                            (before world)
                            (middle (proof-number-classifier-after (proof-number-types-first-ready classifier world)))
                            (after (proof-number-types-classified rational-only classifier world)))
                 (:instance word-kept-with-memory
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (first (proof-world-machine
                                    (proof-number-classifier-after (proof-number-types-first-ready classifier world))))
                            (last (proof-world-machine (proof-number-types-classified rational-only classifier world))))
                 (:instance word-kept-with-memory
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 8))
                            (first (proof-world-machine
                                    (proof-number-classifier-after (proof-number-types-first-ready classifier world))))
                            (last (proof-world-machine (proof-number-types-classified rational-only classifier world)))))
           :in-theory (enable proof-number-types-classified proof-number-types-classification-steps)
           :cases ((not rational-only))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-types-completion-steps (rational-only classifier world)
  (+ (proof-number-types-classification-steps rational-only classifier world)
     (len (proof-number-types-finish-code rational-only))))

(defund proof-number-types-completion-after (rational-only classifier world)
  (proof-number-execute-block (proof-number-types-finish-code rational-only)
                              (proof-number-types-classified rational-only classifier world)))

(local
 (defthm completion-instruction-count
   (equal (len (proof-number-types-finish-code rational-only)) (if rational-only 7 8))
   :hints (("Goal" :in-theory (enable proof-number-types-finish-code)))))

(defund proof-number-types-completion-trace-p (rational-only classifier cuts a b world objects packages)
  (let* ((ready (proof-number-types-first-ready classifier world))
         (first (proof-number-classifier-after ready))
         (classified (proof-number-types-classified rational-only classifier world))
         (machine (proof-world-machine classified))
         (code (proof-number-types-finish-code rational-only))
         (target (proof-number-types-finish-target rational-only classified)))
    (and (proof-number-types-first-trace-p classifier cuts world)
         (proof-number-types-second-trace-p rational-only classifier cuts first)
         (proof-reg-value-p 0 a ready objects packages)
         (proof-reg-value-p 1 b ready objects packages)
         (not (eq (car machine) :svc))
         (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp machine)))
         (unsigned-byte-p 64 (+ (* 4 (len code)) (proof-world-pc classified)))
         (proof-number-checked-block-p code (list target) classified)
         (proof-number-checked-block-p code cuts classified))))

(defthm proof-number-types-return-or-fallthrough
  (let* ((steps (proof-number-types-completion-steps rational-only classifier world))
         (after (proof-number-types-completion-after rational-only classifier world))
         (link (proof-world-reg 30 world))
         (target (if rational-only (+ 64 (proof-world-pc world)) link)))
    (implies (proof-number-types-completion-trace-p rational-only classifier cuts a b world objects packages)
             (and (proof-number-exact-prefix-p steps cuts world after)
                  (implies (equal cuts (list target))
                           (proof-segment-p steps (list target) world :cut after))
                  (equal (proof-world-pc after) target)
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 world))
                  (equal (proof-world-reg 30 after) link)
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (if rational-only
                      (proof-register-arguments-p (list (rfix a) (rfix b)) 0 after objects packages)
                    (proof-number-binary-types-p a b after objects packages)))))
  :hints (("Goal"
           :use (proof-number-types-classifies-operands
                 (:instance proof-number-types-finish
                            (world (proof-number-types-classified rational-only classifier world)))
                 (:instance proof-number-types-return-completed-values
                            (world (proof-number-types-classified rational-only classifier world)))
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-types-finish-code rational-only))
                            (world (proof-number-types-classified rational-only classifier world)))
                 (:instance proof-number-exact-prefix-append
                            (prefix (proof-number-types-classification-steps rational-only classifier world))
                            (suffix (len (proof-number-types-finish-code rational-only)))
                            (before world) (middle (proof-number-types-classified rational-only classifier world))
                            (after (proof-number-types-completion-after rational-only classifier world)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (proof-number-types-classification-steps rational-only classifier world))
                            (suffix (len (proof-number-types-finish-code rational-only)))
                            (cuts (list (if rational-only (+ 64 (proof-world-pc world)) (proof-world-reg 30 world))))
                            (before world) (middle (proof-number-types-classified rational-only classifier world))
                            (reason :cut) (after (proof-number-types-completion-after rational-only classifier world))))
           :in-theory (e/d (proof-number-types-completion-trace-p proof-number-types-completion-steps
                            proof-number-types-completion-after proof-number-types-finish-target)
                           (proof-number-binary-types-p proof-register-arguments-p))
           :cases ((not rational-only))
           :do-not-induct t))
  :rule-classes nil)
