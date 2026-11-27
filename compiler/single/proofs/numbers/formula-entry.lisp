(in-package "BOYMOO-PROOFS")

(include-book "formula-trace")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-number-execute-block proof-segment-p
                     proof-number-checked-block-p proof-number-cut-free-prefix-p
                     proof-number-exact-prefix-p proof-number-frame-p proof-stack-prefix
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-stack-base proof-stack-top proof-heap-base proof-load-word
                     proof-prefix-preserved-p proof-machine-value-p proof-reg-value-p
                     proof-heap-p proof-number-formula-argument-store-instructions
                     proof-grow-return-p boymoo-model::a64-sp)))

(defund proof-number-formula-arguments-after (args world)
  (proof-number-execute-block (proof-number-formula-argument-store-instructions (len args)) world))

(defund proof-number-formula-argument-trace-p (args link world objects packages)
  (let* ((arity (len args))
         (machine (proof-world-machine world))
         (top (proof-stack-top world))
         (end (+ top (* 8 arity)))
         (pc (+ 8 (proof-world-pc world)))
         (code (proof-number-formula-argument-store-instructions arity))
         (after (proof-number-formula-arguments-after args world)))
    (and (proof-number-argument-list-p args)
         (not (eq (car machine) :svc))
         (proof-span-p top (* 8 arity))
         (unsigned-byte-p 64 end) (unsigned-byte-p 64 pc)
         (proof-number-checked-block-p code (list pc) world)
         (proof-number-checked-block-p code (list link) world)
         (proof-prefix-preserved-p top world after objects objects packages)
         (equal (proof-world-reg 19 world) top)
         (proof-machine-value-p (proof-world-reg 0 world) (car args) after objects packages)
         (implies (equal arity 2)
                  (proof-machine-value-p (proof-world-reg 1 world) (cadr args)
                                         after objects packages)))))

(defthm proof-number-formula-arguments-initialize-frame
  (let* ((top (proof-stack-top world))
         (start (len (cdr (proof-stack-prefix top world objects packages))))
         (after (proof-number-formula-arguments-after args world)))
    (implies (proof-number-formula-argument-trace-p args link world objects packages)
             (and (proof-number-exact-prefix-p 2 (list link) world after)
                  (proof-number-frame-p start args after objects packages)
                  (equal (proof-world-reg 19 after) (proof-number-frame-address start after)))))
  :hints (("Goal"
           :use ((:instance proof-number-formula-writes-arguments (arity (len args)))
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-formula-argument-store-instructions (len args)))
                            (cuts (list link)))
                 (:instance proof-number-frame-initialized-with-arguments
                            (before world) (old-objects objects)
                            (after (proof-number-formula-arguments-after args world)))
                 (:instance proof-number-prefix-end-is-frame-address
                            (top (proof-stack-top world))
                            (world (proof-number-formula-arguments-after args world))))
           :in-theory (e/d (proof-number-formula-argument-trace-p proof-number-formula-arguments-after
                            proof-number-formula-argument-store-instructions proof-prefix-preserved-p
                            proof-number-argument-list-p)
                           (proof-number-frame-address))
           :expand ((len (cdr args)))
           :cases ((equal (len args) 1))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-formula-frame-bytes (name)
  (* 8 (+ (proof-number-formula-arity name) (1- (len (proof-number-formula-calls name))))))

(defund proof-number-formula-grow-ready (name grow world)
  (proof-number-execute-block
   (proof-number-formula-grow-instructions (proof-world-pc world) grow
                                           (proof-number-formula-frame-bytes name))
   world))

(defund proof-number-formula-growth-trace-p (name grow steps world grown objects new-objects packages)
  (let* ((machine (proof-world-machine world))
         (pc (proof-world-pc world))
         (continuation (+ 16 pc))
         (link (proof-world-reg 30 world))
         (bytes (proof-number-formula-frame-bytes name))
         (code (proof-number-formula-grow-instructions pc grow bytes))
         (required (+ (proof-stack-top world) bytes))
         (ready (proof-number-formula-grow-ready name grow world)))
    (and (proof-span-p (- (boymoo-model::a64-sp machine) 16) 16)
         (unsigned-byte-p 64 continuation) (unsigned-byte-p 64 grow)
         (unsigned-byte-p 64 required) (not (eq (car machine) :svc))
         (proof-number-checked-block-p code (list grow) world)
         (proof-number-checked-block-p code (list link) world)
         (natp steps)
         (proof-segment-p steps (list continuation) ready :cut grown)
         (proof-number-cut-free-prefix-p steps (list continuation link) ready)
         (proof-grow-return-p "rt:ensure-stack" required ready grown
                              objects new-objects packages))))

(defthm proof-number-formula-growth-prefix
  (let* ((entry (proof-world-pc world))
         (link (proof-world-reg 30 world))
         (ready (proof-number-formula-grow-ready name grow world))
         (required (+ (proof-stack-top world) (proof-number-formula-frame-bytes name))))
    (implies (proof-number-formula-growth-trace-p name grow steps world grown objects new-objects packages)
             (and (proof-number-exact-prefix-p (+ 4 steps) (list link) world grown)
                  (equal (proof-world-pc ready) grow)
                  (equal (proof-world-pc grown) (+ 16 entry))
                  (equal (proof-world-reg 8 ready) required))))
  :hints (("Goal"
           :use ((:instance proof-number-formula-calls-growth
                            (bytes (proof-number-formula-frame-bytes name)))
                 (:instance proof-number-checked-block-exact-prefix
                            (cuts (list (proof-world-reg 30 world)))
                            (instructions (proof-number-formula-grow-instructions
                                           (proof-world-pc world) grow
                                           (proof-number-formula-frame-bytes name))))
                 (:instance proof-number-segment-exact-prefix
                            (count steps) (cuts (list (proof-world-reg 30 world)))
                            (local-cuts (list (+ 16 (proof-world-pc world))))
                            (before (proof-number-formula-grow-ready name grow world))
                            (reason :cut) (after grown))
                 (:instance proof-number-exact-prefix-append
                            (prefix 4) (suffix steps) (cuts (list (proof-world-reg 30 world)))
                            (before world) (middle (proof-number-formula-grow-ready name grow world))
                            (after grown)))
           :in-theory (e/d (proof-number-formula-growth-trace-p proof-number-formula-grow-ready
                            proof-number-formula-grow-instructions proof-grow-return-p
                            proof-frame-return-p)
                           (proof-preserved-heap-p proof-fixed-heap-p proof-grow-limit
                            proof-register-frame-p proof-stack-limit))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-formula-entry-initializes-frame
  (let* ((link (proof-world-reg 30 world))
         (prefix (proof-stack-prefix (proof-stack-top grown) grown new-objects packages))
         (start (len (cdr prefix)))
         (body (proof-number-formula-arguments-after args grown)))
    (implies (and (proof-number-formula-growth-trace-p name grow steps world grown
                                                       objects new-objects packages)
                  (proof-number-formula-argument-trace-p args link grown new-objects packages)
                  (natp steps))
             (and (proof-number-exact-prefix-p (+ 6 steps) (list link) world body)
                  (proof-number-frame-p start args body new-objects packages)
                  (equal (proof-world-reg 19 body) (proof-number-frame-address start body)))))
  :hints (("Goal"
           :use (proof-number-formula-growth-prefix
                 (:instance proof-number-formula-arguments-initialize-frame
                            (world grown) (objects new-objects) (link (proof-world-reg 30 world)))
                 (:instance proof-number-exact-prefix-append
                            (prefix (+ 4 steps)) (suffix 2) (cuts (list (proof-world-reg 30 world)))
                            (before world) (middle grown)
                            (after (proof-number-formula-arguments-after args grown))))
           :in-theory (disable proof-number-frame-address)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-formula-trace-after (trace)
  (proof-number-execute-block *proof-number-formula-return-instructions* (cadar (last trace))))

(defund proof-number-formula-trace-p
    (name args gcd grow growth-steps targets trace world grown objects grown-objects packages)
  (let* ((link (proof-world-reg 30 world))
         (start (len (cdr (proof-stack-prefix (proof-stack-top grown) grown grown-objects packages))))
         (calls (proof-number-formula-calls name))
         (body (proof-number-formula-arguments-after args grown))
         (returned (cadar (last trace)))
         (machine (proof-world-machine returned))
         (sp (boymoo-model::a64-sp machine)))
    (and (natp growth-steps)
         (proof-number-formula-growth-trace-p name grow growth-steps world grown
                                              objects grown-objects packages)
         (proof-number-formula-argument-trace-p args link grown grown-objects packages)
         (proof-number-formula-body-trace-p calls trace args gcd start targets link
                                            body grown-objects packages)
         (proof-number-checked-block-p *proof-number-formula-return-instructions* (list link) returned)
         (not (eq (car machine) :svc))
         (unsigned-byte-p 64 (+ 16 sp))
         (equal (proof-load-word (+ 8 sp) machine) link))))

(defthm proof-number-generated-formula-return
  (let* ((link (proof-world-reg 30 world))
         (calls (proof-number-formula-calls name))
         (count (+ 9 growth-steps (proof-number-formula-trace-steps calls trace)))
         (after (proof-number-formula-trace-after trace)))
    (implies (and (proof-number-formula-result-p name args gcd result)
                  (proof-number-formula-trace-p name args gcd grow growth-steps targets trace
                                                 world grown objects grown-objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (proof-reg-value-p 0 result after (caddar (last trace)) packages))))
  :hints (("Goal"
           :use ((:instance proof-number-formula-entry-initializes-frame
                            (steps growth-steps) (new-objects grown-objects))
                 (:instance proof-number-formula-body-returns-result
                            (start (len (cdr (proof-stack-prefix (proof-stack-top grown)
                                                                 grown grown-objects packages))))
                            (world (proof-number-formula-arguments-after args grown))
                            (objects grown-objects) (link (proof-world-reg 30 world)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (+ 6 growth-steps))
                            (suffix (+ 3 (proof-number-formula-trace-steps
                                          (proof-number-formula-calls name) trace)))
                            (cuts (list (proof-world-reg 30 world))) (before world)
                            (middle (proof-number-formula-arguments-after args grown)) (reason :cut)
                            (after (proof-number-formula-trace-after trace))))
           :in-theory (e/d (proof-number-formula-trace-p proof-number-formula-trace-after)
                           (proof-number-formula-calls proof-number-formula-body-trace-p
                            proof-number-formula-result-p proof-number-formula-trace-steps last))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-q-normalize-reduction-return
  (let* ((middle (proof-number-q-normalize-after zero unchanged reduce world))
         (link (proof-world-reg 30 world))
         (name "rt:q-reduce")
         (args (list a b))
         (count (+ 14 growth-steps
                   (proof-number-formula-trace-steps (proof-number-formula-calls name) trace)))
         (after (proof-number-formula-trace-after trace)))
    (implies (and (integerp a) (not (equal a 0)) (posp b) (< 1 b)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-q-normalize-pre-p zero unchanged reduce world)
                  (proof-number-cut-free-prefix-p 5 (list reduce link) world)
                  (proof-gcd-p a b gcd)
                  (natp growth-steps)
                  (proof-number-formula-trace-p name args gcd grow growth-steps targets trace
                                                 middle grown objects grown-objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (proof-reg-value-p 0 (/ a b) after (caddar (last trace)) packages))))
  :hints (("Goal"
           :use ((:instance proof-number-q-normalize-dispatch-by-value (register 30))
                 proof-number-q-reduce-formula
                 (:instance proof-number-generated-formula-return
                            (name "rt:q-reduce") (args (list a b)) (result (/ a b))
                            (world (proof-number-q-normalize-after zero unchanged reduce world)))
                 (:instance proof-number-compose-segments
                            (prefix 5) (suffix (+ 9 growth-steps
                                                 (proof-number-formula-trace-steps
                                                  (proof-number-formula-calls "rt:q-reduce") trace)))
                            (first-cuts (list reduce)) (last-cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut) (after (proof-number-formula-trace-after trace))
                            (middle (proof-number-q-normalize-after zero unchanged reduce world))))
           :in-theory (disable proof-number-formula-calls proof-number-formula-result-p proof-gcd-p
                               proof-number-cut-free-prefix-p proof-number-formula-trace-steps
                               proof-number-q-normalize-pre-p last)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-negative-inversion-return
  (let* ((path (proof-number-invert-path a zero negative box world))
         (middle (proof-number-execute-block path world))
         (link (proof-world-reg 30 world))
         (name "rt:q-invert-negative")
         (args (list a b))
         (count (+ (len path) 9 growth-steps
                   (proof-number-formula-trace-steps (proof-number-formula-calls name) trace)))
         (after (proof-number-formula-trace-after trace)))
    (implies (and (proof-number-reduced-p a b) (< a 0)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-checked-block-p path (list negative) world)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 (+ 56 (proof-world-pc world)))
                  (unsigned-byte-p 64 negative)
                  (proof-number-cut-free-prefix-p (len path) (list negative link) world)
                  (natp growth-steps)
                  (proof-number-formula-trace-p name args gcd grow growth-steps targets trace
                                                 middle grown objects grown-objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (proof-reg-value-p 0 (/ (/ a b)) after (caddar (last trace)) packages))))
  :hints (("Goal"
           :use (proof-number-invert-dispatch proof-number-q-invert-negative-formula
                 (:instance proof-number-generated-formula-return
                            (name "rt:q-invert-negative") (args (list a b)) (result (/ (/ a b)))
                            (world (proof-number-execute-block
                                    (proof-number-invert-path a zero negative box world) world)))
                 (:instance proof-number-compose-segments
                            (prefix (len (proof-number-invert-path a zero negative box world)))
                            (suffix (+ 9 growth-steps
                                       (proof-number-formula-trace-steps
                                        (proof-number-formula-calls "rt:q-invert-negative") trace)))
                            (first-cuts (list negative)) (last-cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut) (after (proof-number-formula-trace-after trace))
                            (middle (proof-number-execute-block
                                     (proof-number-invert-path a zero negative box world) world))))
           :in-theory (e/d (proof-number-invert-target)
                           (proof-number-formula-calls proof-number-formula-result-p
                            proof-number-formula-trace-steps last))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-zero-inversion-return
  (let* ((path (proof-number-invert-path 0 zero negative box world))
         (middle (proof-number-execute-block path world))
         (link (proof-world-reg 30 world))
         (code (cdr (assoc-equal "rt:zero" *proof-number-leaf-returns*)))
         (after (proof-number-execute-block code middle)))
    (implies (and (proof-number-reduced-p 0 b)
                  (proof-reg-value-p 0 0 world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-checked-block-p path (list zero) world)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 (+ 56 (proof-world-pc world)))
                  (unsigned-byte-p 64 (+ 4 zero)) (unsigned-byte-p 64 zero)
                  (proof-number-cut-free-prefix-p 2 (list zero link) world)
                  (proof-number-checked-block-p code (list link) middle)
                  (not (eq (car (proof-world-machine middle)) :svc)))
             (and (proof-segment-p 4 (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (proof-reg-value-p 0 0 after objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-invert-dispatch (a 0))
                 (:instance proof-number-leaf-returns-word
                            (name "rt:zero") (register 30)
                            (world (proof-number-execute-block
                                    (proof-number-invert-path 0 zero negative box world) world)))
                 (:instance proof-number-compose-segments
                            (prefix 2) (suffix 2) (first-cuts (list zero))
                            (last-cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut)
                            (middle (proof-number-execute-block
                                     (proof-number-invert-path 0 zero negative box world) world))
                            (after (proof-number-execute-block
                                    (cdr (assoc-equal "rt:zero" *proof-number-leaf-returns*))
                                    (proof-number-execute-block
                                     (proof-number-invert-path 0 zero negative box world) world))))
                 (:instance proof-number-immediate-word-view
                            (value 0) (base (proof-heap-base world)) (machine (proof-world-machine world)))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (word 1) (value 0) (before world)
                            (after (proof-number-execute-block
                                    (cdr (assoc-equal "rt:zero" *proof-number-leaf-returns*))
                                    (proof-number-execute-block
                                     (proof-number-invert-path 0 zero negative box world) world)))))
           :in-theory (e/d (proof-number-invert-path proof-number-invert-instructions proof-number-invert-target
                            proof-number-leaf-result-word proof-reg-value-p proof-machine-value-p)
                           (proof-value-p proof-integer-word boymoo-model::a64-memory))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-positive-inversion-passes-reduced-parts
  (let* ((path (proof-number-invert-path a zero negative box world))
         (after (proof-number-execute-block path world)))
    (implies (and (proof-number-reduced-p a b) (< 0 a)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (proof-number-checked-block-p path (list box) world)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 (+ 56 (proof-world-pc world)))
                  (unsigned-byte-p 64 box))
             (and (proof-segment-p (len path) (list box) world :cut after)
                  (equal (proof-world-pc after) box)
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (proof-reg-value-p 0 b after objects packages)
                  (proof-reg-value-p 1 a after objects packages)
                  (proof-number-reduced-p b a)
                  (equal (/ (/ a b)) (/ b a)))))
  :hints (("Goal"
           :use (proof-number-invert-dispatch proof-number-inverted-parts-are-reduced
                 proof-number-reciprocal-from-parts
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (value b) (word (proof-world-reg 1 world)) (before world)
                            (after (proof-number-execute-block
                                    (proof-number-invert-path a zero negative box world) world)))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 1) (value a) (word (proof-world-reg 0 world)) (before world)
                            (after (proof-number-execute-block
                                    (proof-number-invert-path a zero negative box world) world))))
           :in-theory (enable proof-number-invert-target proof-number-reduced-p proof-reg-value-p)
           :do-not-induct t))
  :rule-classes nil)
