(in-package "BOYMOO-PROOFS")

(include-book "formula-entry")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-runtime-value proof-number-formula-result-p
                     proof-number-datum-class proof-number-binary-types-p
                     proof-step proof-run proof-segment-p proof-number-checked-block-p
                     proof-number-cut-free-prefix-p proof-number-execute-block
                     proof-world-pc proof-world-reg proof-world-machine proof-reg-value-p
                     boymoo-model::a64-sp boymoo-model::a64-unsigned boymoo-model::a64-signed
                     acl2::binary-logand logbitp mod floor ash)))

(defund proof-number-arithmetic-dispatch-entry (primitive)
  (case primitive
    (acl2::binary-+ "rt:n-add")
    (acl2::binary-* "rt:n-multiply")
    (acl2::unary-- "rt:n-negate")
    (acl2::unary-/ "rt:n-reciprocal")
    (otherwise nil)))

(defund proof-number-arithmetic-formula-labels (primitive)
  (case primitive
    (acl2::binary-+ '("rt:q-add" "rt:c-add"))
    (acl2::binary-* '("rt:q-multiply" "rt:c-multiply"))
    (acl2::unary-- '("rt:q-negate" "rt:c-negate"))
    (acl2::unary-/ '("rt:q-reciprocal" "rt:c-reciprocal"))
    (otherwise nil)))

(defund proof-number-arithmetic-binary-p (primitive)
  (member-eq primitive '(acl2::binary-+ acl2::binary-*)))

(defund proof-number-arithmetic-dispatch-args (primitive a b)
  (if (proof-number-arithmetic-binary-p primitive) (list (fix a) (fix b)) (list (fix a))))

(defund proof-number-arithmetic-source-args (primitive a b)
  (if (proof-number-arithmetic-binary-p primitive) (list a b) (list a)))

(defund proof-number-arithmetic-dispatch-input-p (primitive a b world objects packages)
  (if (proof-number-arithmetic-binary-p primitive)
      (proof-number-binary-types-p a b world objects packages)
    (and (proof-reg-value-p 0 a world objects packages)
         (equal (proof-world-reg 3 world) (proof-number-datum-class a)))))

(defthm proof-number-selected-formula-refines-source
  (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
         (label (proof-number-selected-label entry world))
         (args (proof-number-arithmetic-dispatch-args primitive a b))
         (source (proof-number-arithmetic-source-args primitive a b))
         (result (boymoo-model::core-datum (proof-runtime-value primitive source program))))
    (implies (and (proof-number-arithmetic-dispatch-input-p primitive a b world objects packages)
                  (member-equal label (proof-number-arithmetic-formula-labels primitive)))
             (proof-number-formula-result-p label args gcd result)))
  :hints (("Goal"
           :use (proof-number-add-dispatch-by-value proof-number-multiply-dispatch-by-value
                 proof-number-negation-dispatch-by-value proof-number-reciprocal-dispatch-by-value
                 proof-number-public-value-completions
                 (:instance proof-number-q-add-formula (x (fix a)) (y (fix b)))
                 (:instance proof-number-q-multiply-formula (x (fix a)) (y (fix b)))
                 (:instance proof-number-q-negate-formula (x a))
                 (:instance proof-number-q-reciprocal-formula (x a))
                 (:instance proof-number-c-add-formula (x (fix a)) (y (fix b)))
                 (:instance proof-number-c-multiply-formula (x (fix a)) (y (fix b)))
                 (:instance proof-number-c-negate-formula (x a))
                 (:instance proof-number-c-reciprocal-formula (x a)))
           :in-theory (e/d (proof-number-arithmetic-dispatch-entry proof-number-arithmetic-formula-labels
                            proof-number-arithmetic-dispatch-input-p proof-number-arithmetic-binary-p
                            proof-number-arithmetic-dispatch-args proof-number-arithmetic-source-args)
                           (proof-number-selected-label))
           :cases ((eq primitive 'acl2::binary-+) (eq primitive 'acl2::binary-*)
                   (eq primitive 'acl2::unary--) (eq primitive 'acl2::unary-/))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-arithmetic-dispatch-path (primitive addresses world)
  (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
         (row (assoc-equal entry *proof-number-dispatch-rows*)))
    (proof-number-dispatch-path (cadr row) (caddr row) (proof-world-pc world) addresses world)))

(defthm proof-number-dispatched-formula-returns-source-value
  (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
         (row (assoc-equal entry *proof-number-dispatch-rows*))
         (tests (cadr row))
         (label (proof-number-selected-label entry world))
         (target (cdr (assoc-equal label addresses)))
         (link (proof-world-reg 30 world))
         (path (proof-number-arithmetic-dispatch-path primitive addresses world))
         (middle (proof-number-execute-block path world))
         (args (proof-number-arithmetic-dispatch-args primitive a b))
         (source (proof-number-arithmetic-source-args primitive a b))
         (result (boymoo-model::core-datum (proof-runtime-value primitive source program)))
         (count (+ (len path) 9 growth-steps
                   (proof-number-formula-trace-steps (proof-number-formula-calls label) trace)))
         (after (proof-number-formula-trace-after trace)))
    (implies (and row (member-equal label (proof-number-arithmetic-formula-labels primitive))
                  (proof-number-arithmetic-dispatch-input-p primitive a b world objects packages)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 (+ (proof-world-pc world) (* 8 (len tests))))
                  (unsigned-byte-p 64 target)
                  (proof-number-checked-block-p path (list target) world)
                  (proof-number-cut-free-prefix-p (len path) (list target link) world)
                  (natp growth-steps)
                  (proof-number-formula-trace-p label args gcd grow growth-steps targets trace
                                                 middle grown objects grown-objects packages))
             (and (proof-segment-p count (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (proof-reg-value-p 0 result after (caddar (last trace)) packages))))
  :hints (("Goal"
           :use (proof-number-selected-formula-refines-source
                 (:instance proof-number-dispatch-reaches-selected-label
                            (name (proof-number-arithmetic-dispatch-entry primitive)) (register 30))
                 (:instance proof-number-generated-formula-return
                            (name (proof-number-selected-label
                                   (proof-number-arithmetic-dispatch-entry primitive) world))
                            (args (proof-number-arithmetic-dispatch-args primitive a b))
                            (result (boymoo-model::core-datum
                                     (proof-runtime-value
                                      primitive (proof-number-arithmetic-source-args primitive a b) program)))
                            (world (proof-number-execute-block
                                    (proof-number-arithmetic-dispatch-path primitive addresses world) world)))
                 (:instance proof-number-compose-segments
                            (prefix (len (proof-number-arithmetic-dispatch-path primitive addresses world)))
                            (suffix (+ 9 growth-steps
                                       (proof-number-formula-trace-steps
                                        (proof-number-formula-calls
                                         (proof-number-selected-label
                                          (proof-number-arithmetic-dispatch-entry primitive) world)) trace)))
                            (first-cuts (list (cdr (assoc-equal
                                                    (proof-number-selected-label
                                                     (proof-number-arithmetic-dispatch-entry primitive) world)
                                                    addresses))))
                            (last-cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut) (after (proof-number-formula-trace-after trace))
                            (middle (proof-number-execute-block
                                     (proof-number-arithmetic-dispatch-path primitive addresses world) world))))
           :in-theory (e/d (proof-number-arithmetic-dispatch-path proof-number-selected-label)
                           (proof-number-dispatch-path proof-number-dispatch-label proof-number-formula-calls
                            proof-number-formula-trace-steps last assoc-equal))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm number-times-zero
   (implies (acl2-numberp value)
            (and (equal (* 0 value) 0) (equal (* value 0) 0)))
   :hints (("Goal"
            :use ((:instance acl2::distributivity (acl2::x value) (acl2::y 0) (acl2::z 0)))
            :in-theory (disable acl2::distributivity)))))

(defthm proof-number-selected-arithmetic-leaf-refines-source
  (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
         (label (proof-number-selected-label entry world))
         (word (proof-number-leaf-result-word label world))
         (source (proof-number-arithmetic-source-args primitive a b))
         (result (boymoo-model::core-datum (proof-runtime-value primitive source program))))
    (implies (and entry
                  (proof-number-arithmetic-dispatch-input-p primitive a b world objects packages)
                  (member-equal label '("rt:zero" "rt:num-type-return" "rt:num-return-second")))
             (proof-machine-value-p word result world objects packages)))
  :hints (("Goal"
           :use (proof-number-add-dispatch-by-value proof-number-multiply-dispatch-by-value
                 proof-number-negation-dispatch-by-value proof-number-reciprocal-dispatch-by-value
                 proof-number-public-value-completions
                 (:instance proof-number-immediate-word-view
                            (value 0) (base (proof-heap-base world)) (machine (proof-world-machine world))))
           :in-theory (e/d (proof-number-arithmetic-dispatch-entry proof-number-binary-types-p
                            proof-number-arithmetic-dispatch-input-p proof-number-arithmetic-binary-p
                            proof-number-arithmetic-source-args proof-number-leaf-result-word
                            proof-reg-value-p proof-machine-value-p)
                           (proof-number-selected-label proof-value-p))
           :cases ((eq primitive 'acl2::binary-+) (eq primitive 'acl2::binary-*)
                   (eq primitive 'acl2::unary--) (eq primitive 'acl2::unary-/))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-arithmetic-leaf-code (primitive world)
  (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
         (label (proof-number-selected-label entry world)))
    (cdr (assoc-equal label *proof-number-leaf-returns*))))

(defthm proof-number-dispatched-leaf-returns-source-value
  (let* ((entry (proof-number-arithmetic-dispatch-entry primitive))
         (row (assoc-equal entry *proof-number-dispatch-rows*))
         (label (proof-number-selected-label entry world))
         (target (cdr (assoc-equal label addresses)))
         (link (proof-world-reg 30 world))
         (path (proof-number-arithmetic-dispatch-path primitive addresses world))
         (middle (proof-number-execute-block path world))
         (code (proof-number-arithmetic-leaf-code primitive world))
         (after (proof-number-execute-block code middle))
         (source (proof-number-arithmetic-source-args primitive a b))
         (result (boymoo-model::core-datum (proof-runtime-value primitive source program))))
    (implies (and entry row
                  (member-equal label '("rt:zero" "rt:num-type-return" "rt:num-return-second"))
                  (proof-number-arithmetic-dispatch-input-p primitive a b world objects packages)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (not (eq (car (proof-world-machine middle)) :svc))
                  (unsigned-byte-p 64 (+ (proof-world-pc world) (* 8 (len (cadr row)))))
                  (unsigned-byte-p 64 target) (unsigned-byte-p 64 (+ 4 target))
                  (proof-number-checked-block-p path (list target) world)
                  (proof-number-checked-block-p code (list link) middle)
                  (proof-number-cut-free-prefix-p (len path) (list target link) world))
             (and (proof-segment-p (+ (len path) (len code)) (list link) world :cut after)
                  (equal (proof-world-pc after) link)
                  (proof-reg-value-p 0 result after objects packages))))
  :hints (("Goal"
           :use (proof-number-selected-arithmetic-leaf-refines-source
                 (:instance proof-number-dispatch-reaches-selected-label
                            (name (proof-number-arithmetic-dispatch-entry primitive)) (register 0))
                 (:instance proof-number-dispatch-reaches-selected-label
                            (name (proof-number-arithmetic-dispatch-entry primitive)) (register 1))
                 (:instance proof-number-dispatch-reaches-selected-label
                            (name (proof-number-arithmetic-dispatch-entry primitive)) (register 28))
                 (:instance proof-number-dispatch-reaches-selected-label
                            (name (proof-number-arithmetic-dispatch-entry primitive)) (register 30))
                 (:instance proof-number-leaf-returns-word
                            (name (proof-number-selected-label
                                   (proof-number-arithmetic-dispatch-entry primitive) world))
                            (world (proof-number-execute-block
                                    (proof-number-arithmetic-dispatch-path primitive addresses world) world))
                            (register 0))
                 (:instance proof-number-compose-segments
                            (prefix (len (proof-number-arithmetic-dispatch-path primitive addresses world)))
                            (suffix (len (proof-number-arithmetic-leaf-code primitive world)))
                            (first-cuts (list (cdr (assoc-equal
                                                    (proof-number-selected-label
                                                     (proof-number-arithmetic-dispatch-entry primitive) world)
                                                    addresses))))
                            (last-cuts (list (proof-world-reg 30 world)))
                            (before world) (reason :cut)
                            (middle (proof-number-execute-block
                                     (proof-number-arithmetic-dispatch-path primitive addresses world) world))
                            (after (proof-number-execute-block
                                    (proof-number-arithmetic-leaf-code primitive world)
                                    (proof-number-execute-block
                                     (proof-number-arithmetic-dispatch-path primitive addresses world) world))))
                 (:instance proof-number-reg-value-with-same-memory
                            (register 0) (before world)
                            (word (proof-number-leaf-result-word
                                   (proof-number-selected-label
                                    (proof-number-arithmetic-dispatch-entry primitive) world) world))
                            (value (boymoo-model::core-datum
                                    (proof-runtime-value primitive
                                                         (proof-number-arithmetic-source-args primitive a b)
                                                         program)))
                            (after (proof-number-execute-block
                                    (proof-number-arithmetic-leaf-code primitive world)
                                    (proof-number-execute-block
                                     (proof-number-arithmetic-dispatch-path primitive addresses world) world)))))
           :in-theory (e/d (proof-number-arithmetic-dispatch-path proof-number-selected-label
                            proof-number-arithmetic-leaf-code proof-number-leaf-result-word proof-heap-base)
                           (proof-number-dispatch-path proof-number-dispatch-label
                            proof-machine-value-p proof-value-p proof-view proof-view-step
                            boymoo-model::a64-memory (:definition assoc-equal)))
           :cases ((equal (proof-number-selected-label (proof-number-arithmetic-dispatch-entry primitive) world)
                          "rt:zero")
                   (equal (proof-number-selected-label (proof-number-arithmetic-dispatch-entry primitive) world)
                          "rt:num-return-second"))
           :do-not-induct t))
  :rule-classes nil)
