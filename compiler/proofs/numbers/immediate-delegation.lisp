(in-package "BOYMOO-PROOFS")

(include-book "immediate-contracts")
(include-book "arithmetic-dispatch")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-number-execute-block
                     proof-number-checked-block-p proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-reg proof-world-pc proof-world-stop
                     proof-heap-p proof-heap-layout-p proof-preserved-heap-p proof-machine-limit
                     proof-runtime-pre-p proof-runtime-return-p proof-runtime-value proof-datum-return-p
                     proof-number-immediate-returns-here-p proof-immediate-integer-p
                     proof-integer-word proof-number-immediate-word-bits
                     boymoo-model::a64-sp boymoo-model::a64-memory mod floor ash)))

(defund proof-number-immediate-delegates-p (name a b)
  (and (proof-number-arithmetic-dispatch-entry name)
       (proof-immediate-integer-p a)
       (or (equal (proof-number-immediate-arity name) 1) (proof-immediate-integer-p b))
       (not (proof-number-immediate-returns-here-p name a b))))

(defund proof-number-immediate-delegation-count (name a)
  (case name
    (acl2::binary-* 7)
    (acl2::unary-/ (if (< a -1) 2 4))
    (otherwise 3)))

(defund proof-number-immediate-delegation-code (name a pc slow)
  (take (proof-number-immediate-delegation-count name a)
        (proof-number-immediate-body-code name a nil pc slow 0 0)))

(defund proof-number-immediate-delegation-body-trace-p (name a slow world)
  (let* ((pc (proof-world-pc world))
         (code (proof-number-immediate-delegation-code name a pc slow)))
    (and (not (eq (car (proof-world-machine world)) :svc))
         (unsigned-byte-p 64 (+ pc (if (eq name 'acl2::binary-*) 32 16)))
         (unsigned-byte-p 64 slow)
         (proof-number-checked-block-p code (list slow) world)
         (proof-number-checked-block-p code (list (proof-world-reg 30 world)) world))))

(local
 (defthm immediate-operand-is-integer
   (implies (proof-immediate-integer-p value) (integerp value))
   :hints (("Goal" :in-theory (enable proof-immediate-integer-p)))
   :rule-classes :forward-chaining))

(defthm proof-number-immediate-body-reaches-helper
  (let* ((pc (proof-world-pc world))
         (binary (equal (proof-number-immediate-arity name) 2))
         (code (proof-number-immediate-delegation-code name a pc slow))
         (after (proof-number-execute-block code world)))
    (implies (and (proof-number-immediate-delegates-p name a b)
                  (equal (proof-world-reg 0 world) (proof-integer-word a))
                  (implies binary (equal (proof-world-reg 1 world) (proof-integer-word b)))
                  (proof-number-immediate-delegation-body-trace-p name a slow world))
             (and (proof-segment-p (proof-number-immediate-delegation-count name a) (list slow) world :cut after)
                  (equal (proof-world-pc after) slow)
                  (equal (proof-world-reg 0 after) (proof-integer-word a))
                  (implies binary (equal (proof-world-reg 1 after) (proof-integer-word b)))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world)))))
  :hints (("Goal"
           :use ((:instance proof-number-immediate-add-negate-returns-or-delegates (negate nil) (overflow slow))
                 (:instance proof-number-immediate-add-negate-returns-or-delegates (negate t) (overflow slow))
                 (:instance proof-number-immediate-multiply-returns-or-delegates (overflow slow))
                 (:instance proof-number-immediate-reciprocal-returns-or-delegates (general slow) (register 0))
                 (:instance proof-number-immediate-reciprocal-returns-or-delegates (general slow) (register 30)))
           :in-theory (e/d (proof-number-immediate-delegates-p proof-number-immediate-delegation-body-trace-p
                            proof-number-immediate-delegation-code proof-number-immediate-delegation-count
                            proof-number-immediate-returns-here-p proof-number-immediate-arity
                            proof-number-immediate-body-code proof-number-arithmetic-dispatch-entry)
                           (proof-number-immediate-reciprocal-instructions
                            proof-number-add-negate-instructions proof-number-immediate-multiply-instructions))
           :cases ((eq name 'acl2::binary-+) (eq name 'acl2::binary-*)
                   (eq name 'acl2::unary--) (eq name 'acl2::unary-/))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-immediate-delegation-entry-code (name a pc general slow)
  (let ((arity (proof-number-immediate-arity name)))
    (append (proof-number-tag-gate-instructions arity pc general)
            (proof-number-immediate-delegation-code name a (+ pc (* 4 (1+ arity))) slow))))

(defund proof-number-immediate-delegation-after (name a general slow world)
  (proof-number-execute-block
   (proof-number-immediate-delegation-entry-code name a (proof-world-pc world) general slow) world))

(defund proof-number-immediate-delegation-trace-p (name a b general slow world)
  (let* ((arity (proof-number-immediate-arity name))
         (pc (proof-world-pc world))
         (entry (+ pc (* 4 (1+ arity))))
         (gate (proof-number-tag-gate-instructions arity pc general))
         (body (proof-number-execute-block gate world)))
    (and (proof-number-immediate-delegates-p name a b)
         (not (eq (car (proof-world-machine world)) :svc))
         (unsigned-byte-p 64 entry)
         (unsigned-byte-p 64 general)
         (proof-number-checked-block-p gate (list entry) world)
         (proof-number-checked-block-p gate (list (proof-world-reg 30 world)) world)
         (proof-number-immediate-delegation-body-trace-p name a slow body))))

(local
 (defthm immediate-tag-gate-length
   (implies (member-equal arity '(1 2))
            (equal (len (proof-number-tag-gate-instructions arity pc general)) (1+ arity)))
   :hints (("Goal" :in-theory (enable proof-number-tag-gate-instructions)))))

(local
 (defthm appending-keeps-instruction-counts
   (equal (len (append first rest)) (+ (len first) (len rest)))
   :hints (("Goal" :induct (len first)))))

(local
 (defthm immediate-delegation-entry-splits
   (let* ((arity (proof-number-immediate-arity name))
          (pc (proof-world-pc world))
          (gate (proof-number-tag-gate-instructions arity pc general))
          (body (proof-number-immediate-delegation-code name a (+ pc (* 4 (1+ arity))) slow)))
     (and (equal (proof-number-immediate-delegation-after name a general slow world)
                 (proof-number-execute-block body (proof-number-execute-block gate world)))
          (equal (len (proof-number-immediate-delegation-entry-code name a pc general slow))
                 (+ (1+ arity) (len body)))))
   :hints (("Goal"
            :in-theory (enable proof-number-immediate-delegation-after proof-number-immediate-delegation-entry-code
                               proof-number-immediate-arity)))
   :rule-classes nil))

(local
 (defthm immediate-delegation-address-and-operands
   (let* ((arity (proof-number-immediate-arity name))
          (code (proof-number-immediate-delegation-entry-code name a (proof-world-pc world) general slow))
          (link (proof-world-reg 30 world))
          (after (proof-number-immediate-delegation-after name a general slow world)))
     (implies (and (proof-number-immediate-delegation-trace-p name a b general slow world)
                   (equal (proof-world-reg 0 world) (proof-integer-word a))
                   (implies (equal arity 2) (equal (proof-world-reg 1 world) (proof-integer-word b))))
              (and (proof-number-exact-prefix-p (len code) (list link) world after)
                   (equal (proof-world-pc after) slow)
                   (equal (proof-world-reg 30 after) link)
                   (equal (proof-world-reg 0 after) (proof-integer-word a))
                   (implies (equal arity 2)
                            (equal (proof-world-reg 1 after) (proof-integer-word b))))))
   :hints (("Goal"
            :use (immediate-delegation-entry-splits
                  (:instance proof-number-public-tag-gate (arity (proof-number-immediate-arity name)))
                  (:instance proof-number-immediate-word-is-odd (value a))
                  (:instance proof-number-immediate-word-is-odd (value b))
                  (:instance proof-number-immediate-body-reaches-helper
                             (world (proof-number-execute-block
                                     (proof-number-tag-gate-instructions
                                      (proof-number-immediate-arity name) (proof-world-pc world) general) world)))
                  (:instance proof-number-checked-block-exact-prefix
                             (instructions (proof-number-tag-gate-instructions
                                            (proof-number-immediate-arity name) (proof-world-pc world) general))
                             (cuts (list (proof-world-reg 30 world))))
                  (:instance proof-number-checked-block-exact-prefix
                             (instructions (proof-number-immediate-delegation-code
                                            name a (+ (proof-world-pc world)
                                                      (* 4 (1+ (proof-number-immediate-arity name)))) slow))
                             (cuts (list (proof-world-reg 30 world)))
                             (world (proof-number-execute-block
                                     (proof-number-tag-gate-instructions
                                      (proof-number-immediate-arity name) (proof-world-pc world) general) world)))
                  (:instance proof-number-exact-prefix-append
                             (prefix (1+ (proof-number-immediate-arity name)))
                             (suffix (len (proof-number-immediate-delegation-code
                                           name a (+ (proof-world-pc world)
                                                     (* 4 (1+ (proof-number-immediate-arity name)))) slow)))
                             (before world)
                             (middle (proof-number-execute-block
                                      (proof-number-tag-gate-instructions
                                       (proof-number-immediate-arity name) (proof-world-pc world) general) world))
                             (after (proof-number-immediate-delegation-after name a general slow world))
                             (cuts (list (proof-world-reg 30 world)))))
            :in-theory (e/d (proof-number-immediate-delegation-trace-p proof-number-immediate-delegates-p
                             proof-number-immediate-delegation-body-trace-p proof-number-immediate-arity)
                            (proof-number-immediate-delegation-code proof-number-tag-gate-instructions
                             oddp proof-number-immediate-returns-here-p))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm sequence-of-scratch-register-instructions
   (implies (and (proof-number-register-only-code-p first clobbers)
                 (proof-number-register-only-code-p second clobbers))
            (proof-number-register-only-code-p (append first second) clobbers))
   :hints (("Goal" :induct (len first)))))

(local
 (defthm immediate-delegation-is-register-only
   (implies (proof-number-arithmetic-dispatch-entry name)
            (proof-number-register-only-code-p
             (proof-number-immediate-delegation-entry-code name a pc general slow) '(2 3 4)))
   :hints (("Goal"
            :in-theory (enable proof-number-arithmetic-dispatch-entry proof-number-immediate-arity
                               proof-number-immediate-delegation-entry-code proof-number-tag-gate-instructions
                               proof-number-immediate-delegation-code proof-number-immediate-delegation-count
                               proof-number-immediate-body-code proof-number-add-negate-instructions
                               proof-number-immediate-multiply-instructions proof-number-immediate-reciprocal-instructions
                               proof-number-register-only-instruction-p)
            :do-not-induct t))))

(local
 (defthm immediate-delegation-start-requirements
   (implies (proof-number-immediate-delegation-trace-p name a b general slow world)
            (and (proof-number-arithmetic-dispatch-entry name)
                 (proof-immediate-integer-p a)
                 (or (equal (proof-number-immediate-arity name) 1) (proof-immediate-integer-p b))
                 (not (eq (car (proof-world-machine world)) :svc))))
   :hints (("Goal"
            :in-theory (enable proof-number-immediate-delegation-trace-p proof-number-immediate-delegates-p)))
   :rule-classes nil))

(local
 (defthm represented-immediate-gives-tagged-word
   (implies (and (proof-immediate-integer-p value)
                 (proof-reg-value-p reg value world objects packages))
            (equal (proof-world-reg reg world) (proof-integer-word value)))
   :hints (("Goal"
            :use ((:instance proof-number-value-has-immediate-word
                             (word (proof-world-reg reg world))
                             (base (proof-heap-base world)) (machine (proof-world-machine world))))
            :in-theory (e/d (proof-reg-value-p proof-machine-value-p) (proof-value-p))))
   :rule-classes nil))

(local
 (defthm immediate-delegation-precondition-gives-operands
   (let ((args (proof-number-immediate-source-args name a b)))
     (implies (and (proof-runtime-pre-p name args program labels base world objects packages)
                   (proof-number-immediate-delegation-trace-p name a b general slow world))
              (and (proof-heap-p world objects packages)
                   (equal (proof-world-reg 0 world) (proof-integer-word a))
                   (implies (equal (proof-number-immediate-arity name) 2)
                            (equal (proof-world-reg 1 world) (proof-integer-word b))))))
   :hints (("Goal"
            :use (immediate-delegation-start-requirements
                  (:instance represented-immediate-gives-tagged-word (reg 0) (value a))
                  (:instance represented-immediate-gives-tagged-word (reg 1) (value b)))
            :in-theory (e/d (proof-runtime-pre-p proof-number-immediate-source-args proof-number-immediate-arity)
                            (proof-runtime-entry proof-program-packages-p proof-label-address))
            :do-not-induct t))
   :rule-classes nil))

(defthm proof-number-public-immediate-reaches-helper
  (let* ((args (proof-number-immediate-source-args name a b))
         (code (proof-number-immediate-delegation-entry-code name a (proof-world-pc world) general slow))
         (entered (proof-number-immediate-delegation-after name a general slow world))
         (link (proof-world-reg 30 world)))
    (implies (and (proof-runtime-pre-p name args program labels base world objects packages)
                  (proof-number-immediate-delegation-trace-p name a b general slow world))
             (and (proof-number-exact-prefix-p (len code) (list link) world entered)
                  (proof-preserved-heap-p nil world entered objects objects packages)
                  (proof-register-frame-p 30 '(2 3 4) world entered)
                  (equal (proof-machine-limit entered) (proof-machine-limit world))
                  (equal (boymoo-model::a64-sp (proof-world-machine entered))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (equal (proof-world-pc entered) slow)
                  (equal (proof-world-reg 30 entered) link)
                  (equal (proof-world-reg 0 entered) (proof-integer-word a))
                  (implies (equal (proof-number-immediate-arity name) 2)
                           (equal (proof-world-reg 1 entered) (proof-integer-word b))))))
  :hints (("Goal"
           :use (immediate-delegation-precondition-gives-operands immediate-delegation-start-requirements
                 immediate-delegation-address-and-operands
                 (:instance proof-number-register-only-execution-preserves-heap
                            (clobbers '(2 3 4))
                            (instructions
                             (proof-number-immediate-delegation-entry-code name a (proof-world-pc world) general slow))))
           :in-theory (e/d (proof-number-immediate-delegation-after)
                           (proof-number-register-only-code-p proof-register-frame-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-public-delegated-immediate-runtime-return
  (let* ((args (proof-number-immediate-source-args name a b))
         (code (proof-number-immediate-delegation-entry-code name a (proof-world-pc world) general slow))
         (entered (proof-number-immediate-delegation-after name a general slow world))
         (link (proof-world-reg 30 world)))
    (implies (and (proof-runtime-pre-p name args program labels base world objects packages)
                  (proof-number-immediate-delegation-trace-p name a b general slow world)
                  (proof-number-world-byte-keys-p world)
                  (natp steps)
                  (proof-segment-p steps (list link) entered :cut after)
                  (proof-runtime-return-p name args program entered after objects new-objects packages))
             (and (proof-segment-p (+ (len code) steps) (list link) world :cut after)
                  (proof-runtime-return-p name args program world after objects new-objects packages))))
  :hints (("Goal"
           :use (immediate-delegation-start-requirements immediate-delegation-precondition-gives-operands
                 proof-number-public-immediate-reaches-helper
                 (:instance proof-number-arithmetic-primitive-and-source-result (primitive name))
                 (:instance proof-number-segment-after-exact-prefix
                            (prefix (len (proof-number-immediate-delegation-entry-code
                                          name a (proof-world-pc world) general slow)))
                            (suffix steps) (cuts (list (proof-world-reg 30 world))) (before world)
                            (middle (proof-number-immediate-delegation-after name a general slow world)) (reason :cut))
                 (:instance proof-number-segment-preserves-byte-keys
                            (count (+ (len (proof-number-immediate-delegation-entry-code
                                            name a (proof-world-pc world) general slow)) steps))
                            (cuts (list (proof-world-reg 30 world))) (before world) (reason :cut))
                 (:instance proof-number-numeric-runtime-return-contract
                            (args (proof-number-immediate-source-args name a b)) (before world)
                            (old-objects objects) (objects new-objects))
                 (:instance proof-number-numeric-runtime-return-contract
                            (args (proof-number-immediate-source-args name a b))
                            (before (proof-number-immediate-delegation-after name a general slow world))
                            (old-objects objects) (objects new-objects))
                 (:instance proof-number-numeric-tail-transfer-returns
                            (datum (boymoo-model::core-datum
                                    (proof-runtime-value name (proof-number-immediate-source-args name a b) program)))
                            (before world) (middle (proof-number-immediate-delegation-after name a general slow world))
                            (clobbers '(2 3 4))
                            (old-objects objects) (middle-objects objects) (objects new-objects)))
           :in-theory (enable proof-number-numeric-clobbers)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-immediate-tag-agrees-with-datum
  (implies (proof-reg-value-p reg value world objects packages)
           (equal (oddp (proof-world-reg reg world)) (proof-immediate-integer-p value)))
  :hints (("Goal"
           :use (represented-immediate-gives-tagged-word
                 (:instance proof-number-immediate-word-is-odd (value value))
                 (:instance proof-number-odd-word-view
                            (word (proof-world-reg reg world)) (base (proof-heap-base world))
                            (machine (proof-world-machine world)))
                 (:instance proof-number-odd-word-round-trip (word (proof-world-reg reg world)))
                 (:instance proof-number-reg-range (register reg) (machine (proof-world-machine world))))
           :in-theory (e/d (proof-world-reg proof-reg-value-p proof-machine-value-p proof-value-p)
                           (proof-view proof-view-step proof-reg oddp))
           :do-not-induct t))
  :rule-classes nil)
