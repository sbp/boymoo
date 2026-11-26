(in-package "BOYMOO-PROOFS")

(include-book "multiplication")
(include-book "register-effects")
(include-book "heap-frame")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-advance proof-segment-p
                     proof-number-checked-block-p proof-number-exact-prefix-p
                     proof-number-execute-block proof-instruction-effect proof-execute
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-reg-value-p proof-machine-value-p proof-runtime-value
                     proof-register-frame-p proof-runtime-pre-p proof-runtime-return-p
                     proof-datum-return-p proof-frame-return-p proof-preserved-heap-p
                     proof-register-arguments-p proof-heap-p proof-heap-base
                     proof-number-integer-parity proof-integer-word
                     proof-number-immediate-word-bits proof-immediate-integer-p
                     boymoo-model::a64-sp boymoo-model::a64-memory
                     boymoo-model::a64-unsigned mod floor ash)))

(local
 (defthm world-pc-range
   (unsigned-byte-p 64 (proof-world-pc world))
   :hints (("Goal" :in-theory (e/d (proof-world-pc)
                                  (boymoo-model::a64-pc unsigned-byte-p))))
   :rule-classes ((:type-prescription :corollary (natp (proof-world-pc world)))
                  (:linear :corollary (< (proof-world-pc world) (expt 2 64))))))

(defund proof-number-immediate-arity (name)
  (if (member-eq name '(acl2::unary-- acl2::unary-/)) 1 2))

(defund proof-number-immediate-returns-here-p (name a b)
  (and (proof-immediate-integer-p a)
       (or (equal (proof-number-immediate-arity name) 1)
           (proof-immediate-integer-p b))
       (case name
         (acl2::binary-+ (proof-immediate-integer-p (+ a b)))
         (acl2::binary-* (proof-immediate-integer-p (* a b)))
         (acl2::unary-- (proof-immediate-integer-p (- a)))
         (acl2::unary-/ (member-equal a '(-1 0 1)))
         (< t)
         (otherwise nil))))

(defund proof-number-immediate-result (name a b)
  (case name
    (acl2::binary-+ (+ a b))
    (acl2::binary-* (* a b))
    (acl2::unary-- (- a))
    (acl2::unary-/ (/ a))
    (otherwise (< a b))))

(defund proof-number-immediate-result-word (name a b)
  (if (eq name '<)
      (if (< a b) *proof-t* *proof-nil*)
    (proof-integer-word (proof-number-immediate-result name a b))))

(defund proof-number-immediate-body-code (name a b pc slow yes no)
  (case name
    (acl2::binary-+ (proof-number-add-negate-instructions nil pc slow))
    (acl2::binary-* (proof-number-immediate-multiply-instructions pc slow))
    (acl2::unary-- (proof-number-add-negate-instructions t pc slow))
    (acl2::unary-/ (proof-number-immediate-reciprocal-instructions pc slow))
    (< (append (take (if (< a b) 2 3) (proof-number-immediate-less-instructions pc yes no))
               (cdr (assoc-equal (if (< a b) "rt:true" "rt:nil") *proof-number-leaf-returns*))))
    (otherwise nil)))

(defund proof-number-immediate-body-trace-p (name a b slow yes no world)
  (let ((pc (proof-world-pc world))
        (link (proof-world-reg 30 world))
        (machine (proof-world-machine world)))
    (and (not (eq (car machine) :svc))
         (unsigned-byte-p 64 (+ 32 pc))
         (unsigned-byte-p 64 slow)
         (if (eq name '<)
             (proof-number-immediate-less-body-pre-p a b yes no world)
           (proof-number-checked-block-p
            (proof-number-immediate-body-code name a b pc slow yes no)
            (list link) world)))))

(local
 (defthm less-body-is-selected-code
   (equal (proof-number-immediate-less-after a b yes no world)
          (proof-number-execute-block
           (proof-number-immediate-body-code '< a b (proof-world-pc world) slow yes no)
           world))
   :hints (("Goal"
            :in-theory (enable proof-number-immediate-body-code proof-number-immediate-less-after
                               proof-number-immediate-less-selection)
            :cases ((< a b))))
   :rule-classes nil))

(local
 (defmacro immediate-body-case (event operation &rest laws)
   `(defthm ,event
      (let* ((pc (proof-world-pc world))
             (link (proof-world-reg 30 world))
             (code (proof-number-immediate-body-code ',operation a b pc slow yes no))
             (after (proof-number-execute-block code world)))
        (implies (and (proof-number-immediate-returns-here-p ',operation a b)
                      (equal (proof-world-reg 0 world) (proof-integer-word a))
                      (implies (equal (proof-number-immediate-arity ',operation) 2)
                               (equal (proof-world-reg 1 world) (proof-integer-word b)))
                      (proof-number-immediate-body-trace-p ',operation a b slow yes no world))
                 (and (proof-segment-p (len code) (list link) world :cut after)
                      (equal (proof-world-pc after) link)
                      (equal (proof-world-reg 0 after)
                             (proof-number-immediate-result-word ',operation a b)))))
      :hints (("Goal"
               :use ,laws
               :in-theory (enable proof-number-immediate-returns-here-p proof-number-immediate-arity
                                  proof-number-immediate-body-trace-p proof-number-immediate-body-code
                                  proof-number-immediate-result-word proof-number-immediate-result
                                  proof-number-add-negate-instructions
                                  proof-number-immediate-multiply-instructions
                                  proof-number-immediate-reciprocal-instructions
                                  proof-number-immediate-less-instructions
                                  (:executable-counterpart proof-immediate-integer-p))
               :do-not-induct t))
      :rule-classes nil)))

(local
 (immediate-body-case immediate-add-body acl2::binary-+
                      (:instance proof-number-immediate-add-negate-returns-or-delegates
                                 (negate nil) (overflow slow))))

(local
 (immediate-body-case immediate-negate-body acl2::unary--
                      (:instance proof-number-immediate-add-negate-returns-or-delegates
                                 (negate t) (overflow slow))))

(local
 (immediate-body-case immediate-multiply-body acl2::binary-*
                      (:instance proof-number-immediate-multiply-returns-or-delegates (overflow slow))))

(local
 (immediate-body-case immediate-reciprocal-body acl2::unary-/
                      (:instance proof-number-immediate-reciprocal-returns-or-delegates
                                 (general slow) (register 0))))

(local
 (immediate-body-case immediate-less-body <
                      proof-number-immediate-less-body-returns-word less-body-is-selected-code))

(local
 (defthm immediate-returns-here-name
   (implies (proof-number-immediate-returns-here-p name a b)
            (member-eq name '(acl2::binary-+ acl2::binary-* acl2::unary-- acl2::unary-/ <)))
   :hints (("Goal" :in-theory (enable proof-number-immediate-returns-here-p)))
   :rule-classes nil))

(defthm proof-number-immediate-body-returns
  (let* ((pc (proof-world-pc world))
         (link (proof-world-reg 30 world))
         (code (proof-number-immediate-body-code name a b pc slow yes no))
         (after (proof-number-execute-block code world)))
    (implies (and (proof-number-immediate-returns-here-p name a b)
                  (equal (proof-world-reg 0 world) (proof-integer-word a))
                  (implies (equal (proof-number-immediate-arity name) 2)
                           (equal (proof-world-reg 1 world) (proof-integer-word b)))
                  (proof-number-immediate-body-trace-p name a b slow yes no world))
             (and (proof-segment-p (len code) (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 0 after) (proof-number-immediate-result-word name a b)))))
  :hints (("Goal"
           :use (immediate-returns-here-name immediate-add-body immediate-multiply-body
                 immediate-negate-body immediate-reciprocal-body immediate-less-body)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-immediate-entry-code (name a b entry general slow yes no)
  (let* ((arity (proof-number-immediate-arity name))
         (body (+ entry (* 4 (1+ arity)))))
    (append (proof-number-tag-gate-instructions arity entry general)
            (proof-number-immediate-body-code name a b body slow yes no))))

(local
 (defthm immediate-entry-executes-gate-then-body
   (let* ((entry (proof-world-pc world))
          (arity (proof-number-immediate-arity name))
          (gate (proof-number-tag-gate-instructions arity entry general))
          (body (proof-number-immediate-body-code
                 name a b (+ entry (* 4 (1+ arity))) slow yes no)))
     (equal (proof-number-execute-block
             (proof-number-immediate-entry-code name a b entry general slow yes no) world)
            (proof-number-execute-block body (proof-number-execute-block gate world))))
   :hints (("Goal" :in-theory (enable proof-number-immediate-entry-code)))
   :rule-classes nil))

(defund proof-number-immediate-entry-trace-p (name a b general slow yes no world)
  (let* ((arity (proof-number-immediate-arity name))
         (entry (proof-world-pc world))
         (gate (proof-number-tag-gate-instructions arity entry general))
         (body (proof-number-execute-block gate world)))
    (and (not (eq (car (proof-world-machine world)) :svc))
         (unsigned-byte-p 64 (+ entry (* 4 (1+ arity))))
         (unsigned-byte-p 64 general)
         (proof-number-checked-block-p gate (list (+ entry (* 4 (1+ arity)))) world)
         (proof-number-checked-block-p gate (list (proof-world-reg 30 world)) world)
         (proof-number-immediate-body-trace-p name a b slow yes no body))))

(defthm proof-number-immediate-entry-returns
  (let* ((entry (proof-world-pc world))
         (link (proof-world-reg 30 world))
         (code (proof-number-immediate-entry-code name a b entry general slow yes no))
         (after (proof-number-execute-block code world)))
    (implies (and (proof-number-immediate-returns-here-p name a b)
                  (equal (proof-world-reg 0 world) (proof-integer-word a))
                  (implies (equal (proof-number-immediate-arity name) 2)
                           (equal (proof-world-reg 1 world) (proof-integer-word b)))
                  (proof-number-immediate-entry-trace-p name a b general slow yes no world))
             (and (proof-segment-p (len code) (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 0 after) (proof-number-immediate-result-word name a b)))))
  :hints (("Goal"
           :use ((:instance proof-number-public-tag-gate
                            (arity (proof-number-immediate-arity name)))
                 immediate-entry-executes-gate-then-body
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-tag-gate-instructions
                                           (proof-number-immediate-arity name) (proof-world-pc world) general))
                            (cuts (list (proof-world-reg 30 world))))
                 (:instance proof-number-immediate-body-returns
                            (world (proof-number-execute-block
                                    (proof-number-tag-gate-instructions
                                     (proof-number-immediate-arity name) (proof-world-pc world) general)
                                    world)))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (len (proof-number-tag-gate-instructions
                                          (proof-number-immediate-arity name) (proof-world-pc world) general)))
                            (suffix (len (proof-number-immediate-body-code
                                          name a b (+ (proof-world-pc world)
                                                      (* 4 (1+ (proof-number-immediate-arity name))))
                                          slow yes no)))
                            (before world) (reason :cut) (cuts (list (proof-world-reg 30 world)))
                            (middle (proof-number-execute-block
                                     (proof-number-tag-gate-instructions
                                      (proof-number-immediate-arity name) (proof-world-pc world) general)
                                     world))
                            (after (proof-number-execute-block
                                    (proof-number-immediate-entry-code
                                     name a b (proof-world-pc world) general slow yes no) world))))
           :in-theory (e/d (proof-number-immediate-entry-code proof-number-immediate-entry-trace-p
                            proof-number-immediate-arity proof-number-immediate-returns-here-p
                            proof-number-tag-gate-instructions)
                           (proof-number-immediate-result-word proof-number-immediate-body-code
                            proof-number-immediate-body-trace-p oddp))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm immediate-entry-register-only
   (proof-number-register-only-code-p
    (proof-number-immediate-entry-code name a b entry general slow yes no)
    *proof-volatile-registers*)
   :hints (("Goal"
            :in-theory (enable proof-number-immediate-entry-code proof-number-immediate-body-code
                               proof-number-immediate-arity proof-number-tag-gate-instructions
                               proof-number-add-negate-instructions proof-number-immediate-multiply-instructions
                               proof-number-immediate-reciprocal-instructions
                               proof-number-immediate-less-instructions
                               proof-number-register-only-instruction-p)
            :cases ((< a b))))
   :rule-classes nil))

(local
 (defthm unchanged-tail-keeps-world-fields
   (implies (equal (cdr before) (cdr after))
            (and (proof-streams-preserved-p before after)
                 (equal (proof-world-regions before) (proof-world-regions after))
                 (equal (proof-world-page-size before) (proof-world-page-size after))))
   :hints (("Goal" :cases ((consp before) (consp after))))
   :rule-classes nil))

(local
 (defthm volatile-frame-covers-runtime-frame
   (implies (proof-register-frame-p 30 *proof-volatile-registers* before after)
            (and (proof-register-frame-p 30 (append *proof-volatile-registers* '(24 26 27)) before after)
                 (equal (proof-world-reg 23 before) (proof-world-reg 23 after))
                 (equal (proof-world-reg 24 before) (proof-world-reg 24 after))
                 (equal (proof-world-reg 25 before) (proof-world-reg 25 after))
                 (equal (proof-world-reg 26 before) (proof-world-reg 26 after))
                 (equal (proof-world-reg 27 before) (proof-world-reg 27 after))
                 (equal (proof-world-reg 28 before) (proof-world-reg 28 after))))
   :hints (("Goal"
            :use ((:instance proof-number-register-frame-keeps
                             (limit 30) (clobbers *proof-volatile-registers*) (register 23))
                  (:instance proof-number-register-frame-keeps
                             (limit 30) (clobbers *proof-volatile-registers*) (register 24))
                  (:instance proof-number-register-frame-keeps
                             (limit 30) (clobbers *proof-volatile-registers*) (register 25))
                  (:instance proof-number-register-frame-keeps
                             (limit 30) (clobbers *proof-volatile-registers*) (register 26))
                  (:instance proof-number-register-frame-keeps
                             (limit 30) (clobbers *proof-volatile-registers*) (register 27))
                  (:instance proof-number-register-frame-keeps
                             (limit 30) (clobbers *proof-volatile-registers*) (register 28))
                  (:instance proof-number-register-frame-allows-more-clobbers
                             (limit 30) (clobbers *proof-volatile-registers*)
                             (extended (append *proof-volatile-registers* '(24 26 27)))))))
   :rule-classes nil))

(defthm proof-number-immediate-path-keeps-heap-and-register-frame
  (let* ((code (proof-number-immediate-entry-code
                name a b (proof-world-pc world) general slow yes no))
         (after (proof-number-execute-block code world)))
    (implies (and (not (eq (car (proof-world-machine world)) :svc))
                  (proof-heap-p world objects packages))
             (and (proof-preserved-heap-p nil world after objects objects packages)
                  (proof-heap-p after objects packages)
                  (proof-register-frame-p 30 (append *proof-volatile-registers* '(24 26 27)) world after)
                  (equal (boymoo-model::a64-sp (proof-world-machine world))
                         (boymoo-model::a64-sp (proof-world-machine after)))
                  (equal (proof-world-stop after) (proof-world-stop world)))))
  :hints (("Goal"
           :use ((:instance immediate-entry-register-only (entry (proof-world-pc world)))
                 (:instance proof-number-register-only-block-keeps-register-frame
                            (limit 30) (clobbers *proof-volatile-registers*)
                            (instructions (proof-number-immediate-entry-code
                                           name a b (proof-world-pc world) general slow yes no)))
                 (:instance proof-number-register-only-block-effects
                            (register 30) (clobbers *proof-volatile-registers*)
                            (instructions (proof-number-immediate-entry-code
                                           name a b (proof-world-pc world) general slow yes no)))
                 (:instance unchanged-tail-keeps-world-fields
                            (before world)
                            (after (proof-number-execute-block
                                    (proof-number-immediate-entry-code
                                     name a b (proof-world-pc world) general slow yes no) world)))
                 (:instance volatile-frame-covers-runtime-frame
                            (before world)
                            (after (proof-number-execute-block
                                    (proof-number-immediate-entry-code
                                     name a b (proof-world-pc world) general slow yes no) world)))
                 (:instance proof-number-same-state-preserves-heap
                            (before world)
                            (after (proof-number-execute-block
                                    (proof-number-immediate-entry-code
                                     name a b (proof-world-pc world) general slow yes no) world)))
                 (:instance proof-number-same-state-keeps-heap
                            (before world)
                            (after (proof-number-execute-block
                                    (proof-number-immediate-entry-code
                                     name a b (proof-world-pc world) general slow yes no) world))))
           :in-theory (e/d (proof-number-same-heap-state-p)
                           (proof-number-register-only-block-keeps-register-frame
                            proof-dynamic-view proof-streams-preserved-p proof-world-page-size
                            proof-world-regions))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-immediate-source-args (name a b)
  (if (equal (proof-number-immediate-arity name) 1) (list a) (list a b)))

(local
 (defthm immediate-source-result
   (implies (proof-number-immediate-returns-here-p name a b)
            (and (equal (proof-runtime-value
                         name (proof-number-immediate-source-args name a b) program)
                        (boymoo-model::core-value (proof-number-immediate-result name a b)))
                 (implies (not (eq name '<))
                          (proof-immediate-integer-p (proof-number-immediate-result name a b)))
                 (equal (proof-runtime-clobbers name) (append *proof-volatile-registers* '(24 26 27)))
                 (proof-runtime-allocates-p name (proof-number-immediate-source-args name a b))))
   :hints (("Goal"
            :use proof-number-public-value-completions
            :in-theory (enable proof-number-immediate-arity proof-number-immediate-result
                               proof-number-immediate-returns-here-p proof-number-immediate-source-args
                               proof-immediate-integer-p)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm word-of-represented-immediate
   (implies (and (proof-immediate-integer-p value)
                 (proof-reg-value-p register value world objects packages))
            (equal (proof-world-reg register world) (proof-integer-word value)))
   :hints (("Goal"
            :use ((:instance proof-number-value-has-immediate-word
                             (word (proof-world-reg register world))
                             (base (proof-heap-base world)) (machine (proof-world-machine world))))
            :in-theory (enable proof-reg-value-p proof-machine-value-p)))
   :rule-classes nil))

(local
 (defthm heap-world-is-running
   (implies (proof-heap-p world objects packages)
            (not (proof-world-stop world)))
   :hints (("Goal"
            :expand ((proof-heap-p world objects packages) (proof-heap-layout-p world))
            :in-theory (disable proof-covered-p proof-static-p proof-heap-object-spans-p
                                proof-heap-layout-p proof-object-map-p proof-external-objects
                                proof-dynamic-entries proof-dynamic-symbol-objects-p)))
   :rule-classes nil))

(local
 (defthm immediate-entry-arguments
   (implies (and (proof-number-immediate-returns-here-p name a b)
                 (proof-runtime-pre-p name (proof-number-immediate-source-args name a b)
                                      program labels base world objects packages))
            (and (proof-heap-p world objects packages)
                 (not (proof-world-stop world))
                 (equal (proof-world-reg 0 world) (proof-integer-word a))
                 (implies (equal (proof-number-immediate-arity name) 2)
                          (equal (proof-world-reg 1 world) (proof-integer-word b)))))
   :hints (("Goal"
            :use (heap-world-is-running
                  (:instance word-of-represented-immediate (register 0) (value a))
                  (:instance word-of-represented-immediate (register 1) (value b)))
            :in-theory (e/d (proof-runtime-pre-p proof-number-immediate-source-args
                             proof-register-arguments-p proof-number-immediate-returns-here-p)
                            (proof-program-packages-p proof-runtime-entry proof-label-address
                             proof-argument-views))
            :cases ((equal (proof-number-immediate-arity name) 1))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm immediate-result-word-represents-source
   (implies (and (proof-number-immediate-returns-here-p name a b)
                 (proof-heap-p after objects packages)
                 (equal (proof-world-reg 0 after) (proof-number-immediate-result-word name a b)))
            (proof-reg-value-p 0 (proof-number-immediate-result name a b) after objects packages))
   :hints (("Goal"
            :use ((:instance immediate-source-result (program nil))
                  (:instance proof-number-boolean-words-have-views (world after))
                  (:instance proof-number-immediate-word-view
                             (value (proof-number-immediate-result name a b))
                             (base (proof-heap-base after)) (machine (proof-world-machine after))))
            :in-theory (e/d (proof-number-immediate-result-word proof-reg-value-p proof-machine-value-p)
                            (proof-view proof-value-p proof-runtime-allocates-p proof-runtime-clobbers))
            :cases ((eq name '<))
            :do-not-induct t)
           ("Subgoal 1"
            :in-theory (enable proof-number-immediate-result proof-number-immediate-result-word
                               proof-reg-value-p)))
   :rule-classes nil))

(defthm proof-number-public-immediate-runtime-return
  (let* ((args (proof-number-immediate-source-args name a b))
         (code (proof-number-immediate-entry-code
                name a b (proof-world-pc world) general slow yes no))
         (after (proof-number-execute-block code world)))
    (implies (and (proof-number-immediate-returns-here-p name a b)
                  (proof-runtime-pre-p name args program labels base world objects packages)
                  (proof-number-immediate-entry-trace-p name a b general slow yes no world))
             (and (proof-segment-p (len code) (list (proof-world-reg 30 world)) world :cut after)
                  (proof-runtime-return-p name args program world after objects objects packages))))
  :hints (("Goal"
           :use (immediate-entry-arguments immediate-source-result immediate-returns-here-name
                 proof-number-immediate-entry-returns proof-number-immediate-path-keeps-heap-and-register-frame
                 (:instance immediate-result-word-represents-source
                            (after (proof-number-execute-block
                                    (proof-number-immediate-entry-code
                                     name a b (proof-world-pc world) general slow yes no) world))))
           :in-theory (e/d (proof-number-immediate-entry-trace-p proof-runtime-return-p
                            proof-datum-return-p proof-frame-return-p)
                           (proof-runtime-entry proof-runtime-clobbers proof-runtime-allocates-p
                            proof-fixed-heap-p proof-dynamic-table-preserved-p))
           :do-not-induct t))
  :rule-classes nil)
