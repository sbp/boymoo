(in-package "BOYMOO-PROOFS")

(include-book "store-traces")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-advance
                     proof-execute proof-instruction-effect
                     proof-number-checked-block-p proof-number-execute-block
                     proof-number-exact-prefix-p proof-number-cut-free-prefix-p
                     proof-world-machine proof-world-pc proof-world-reg proof-world-stop
                     proof-load-word proof-reg-value-p proof-machine-value-p proof-heap-base
                     proof-number-binary-types-p proof-number-classifier-path
                     boymoo-model::a64-sp boymoo-model::a64-pc boymoo-model::a64-memory
                     boymoo-model::a64-unsigned boymoo-model::a64-read-reg
                     boymoo-model::a64-write-reg boymoo-model::a64-set-pc
                     (:definition update-nth) (:definition nth))))

(defconst *proof-number-classification-wrappers*
  '(("rt:n-add" "rt:n-types" t)
    ("rt:n-multiply" "rt:n-types" t)
    ("rt:n-negate" "rt:num-type" t)
    ("rt:n-reciprocal" "rt:num-type" t)
    ("rt:n-less" "rt:n-types" nil)
    ("rt:q-compare" "rt:n-types" t)))

(defconst *proof-number-pop-link-code*
  '((:pair t 31 29 30 :post 16)))

(defun proof-number-classification-wrapper-decoding-p (rows labels)
  (if (endp rows)
      t
    (let* ((row (car rows))
           (name (car row))
           (entry (boymoo-compiler::a64-offset name labels))
           (target (boymoo-compiler::a64-offset (cadr row) labels))
           (instructions (append (proof-number-types-first-code entry target)
                                 (if (caddr row) *proof-number-pop-link-code* nil)))
           (items (cdr (proof-number-code-at-label
                        name (boymoo-compiler::runtime-primitive-code)))))
      (and (equal (proof-number-decode-items (take (len instructions) items) entry labels)
                  instructions)
           (proof-number-classification-wrapper-decoding-p (cdr rows) labels)))))

(defthm proof-number-classification-wrappers-decode
  (mv-let (end labels reverse-items)
    (boymoo-compiler::a64-layout (boymoo-compiler::runtime-code) 0 nil nil)
    (declare (ignore end reverse-items))
    (proof-number-classification-wrapper-decoding-p *proof-number-classification-wrappers* labels))
  :rule-classes nil)

(defund proof-number-save-and-call-trace-p (target cuts world)
  (let* ((machine (proof-world-machine world))
         (pc (proof-world-pc world))
         (saved (- (boymoo-model::a64-sp machine) 16))
         (code (proof-number-types-first-code pc target)))
    (and (not (eq (car machine) :svc))
         (proof-span-p saved 16)
         (unsigned-byte-p 64 target)
         (unsigned-byte-p 64 (+ 8 pc))
         (proof-number-checked-block-p code (list target) world)
         (proof-number-checked-block-p code cuts world))))

(defthm proof-number-checked-save-and-call
  (let* ((ready (proof-number-types-first-ready target world))
         (machine (proof-world-machine ready))
         (saved (- (boymoo-model::a64-sp (proof-world-machine world)) 16)))
    (implies (proof-number-save-and-call-trace-p target cuts world)
             (and (proof-number-exact-prefix-p 2 cuts world ready)
                  (proof-segment-p 2 (list target) world :cut ready)
                  (equal (proof-world-pc ready) target)
                  (equal (proof-world-reg 30 ready) (+ 8 (proof-world-pc world)))
                  (equal (boymoo-model::a64-sp machine) saved)
                  (equal (proof-load-word saved machine) (proof-world-reg 29 world))
                  (equal (proof-load-word (+ 8 saved) machine) (proof-world-reg 30 world)))))
  :hints (("Goal"
           :use ((:instance proof-number-types-call-first-classifier (classifier target))
                 (:instance proof-number-checked-block-exact-prefix
                            (instructions (proof-number-types-first-code (proof-world-pc world) target))))
           :in-theory (enable proof-number-save-and-call-trace-p
                              proof-number-types-first-ready proof-number-types-first-code)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-type-completion-memory-from-save
  (let* ((ready (proof-number-types-first-ready classifier world))
         (after (proof-number-types-completion-after rational-only classifier world)))
    (implies (proof-number-types-completion-trace-p rational-only classifier cuts a b world objects packages)
             (and (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory (proof-world-machine ready)))
                  (equal (proof-heap-base after) (proof-heap-base world)))))
  :hints (("Goal"
           :use ((:instance proof-number-save-and-call-effects (target classifier) (register 28))
                 (:instance proof-number-classification-keeps-values
                            (world (proof-number-types-first-ready classifier world))
                            (value a) (register 28) (operand nil))
                 (:instance proof-number-classification-keeps-values
                            (world (proof-number-types-second-ready
                                    rational-only classifier
                                    (proof-number-classifier-after
                                     (proof-number-types-first-ready classifier world))))
                            (value b) (register 28) (operand nil))
                 (:instance proof-number-types-call-second-classifier
                            (world (proof-number-classifier-after
                                    (proof-number-types-first-ready classifier world))))
                 (:instance proof-number-types-finish
                            (world (proof-number-types-classified rational-only classifier world))))
           :in-theory (enable proof-number-types-completion-trace-p
                              proof-number-types-first-trace-p proof-number-types-second-trace-p
                              proof-number-types-second-ready proof-number-types-classified
                              proof-number-types-completion-after proof-heap-base)
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm word-with-same-memory
   (implies (equal (boymoo-model::a64-memory first) (boymoo-model::a64-memory last))
            (equal (proof-load-word address last) (proof-load-word address first)))
   :hints (("Goal" :in-theory (e/d (proof-load-word boymoo-model::a64-load)
                                  (boymoo-model::a64-read-bytes))))
   :rule-classes nil))

(defthm proof-number-type-completion-keeps-disjoint-word
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (after (proof-number-types-completion-after rational-only classifier world)))
    (implies (and (proof-number-types-completion-trace-p rational-only classifier cuts a b world objects packages)
                  (proof-span-p (- sp 16) 16)
                  (proof-span-p address 8)
                  (proof-disjoint-p address (+ 8 address) (- sp 16) sp))
             (equal (proof-load-word address (proof-world-machine after))
                    (proof-load-word address machine))))
  :hints (("Goal"
           :use (proof-number-type-completion-memory-from-save
                 (:instance proof-number-save-and-call-effects (target classifier) (register 28))
                 (:instance proof-number-load-after-disjoint-store
                            (dest (- (boymoo-model::a64-sp (proof-world-machine world)) 16)) (size 8)
                            (value (proof-world-reg 29 world)) (machine (proof-world-machine world)))
                 (:instance proof-number-load-after-disjoint-store
                            (dest (- (boymoo-model::a64-sp (proof-world-machine world)) 8)) (size 8)
                            (value (proof-world-reg 30 world))
                            (machine (boymoo-model::a64-store
                                      8 (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                      (proof-world-reg 29 world) (proof-world-machine world))))
                 (:instance word-with-same-memory
                            (last (proof-world-machine
                                   (proof-number-types-completion-after rational-only classifier world)))
                            (first (boymoo-model::a64-store
                                    8 (- (boymoo-model::a64-sp (proof-world-machine world)) 8)
                                    (proof-world-reg 30 world)
                                    (boymoo-model::a64-store
                                     8 (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                     (proof-world-reg 29 world) (proof-world-machine world))))))
           :in-theory (enable proof-number-types-completion-trace-p proof-number-types-first-trace-p)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-pop-link-after (world)
  (proof-number-execute-block *proof-number-pop-link-code* world))

(defthm proof-number-pop-link-effects
  (let* ((machine (proof-world-machine world))
         (sp (boymoo-model::a64-sp machine))
         (after (proof-number-pop-link-after world)))
    (implies (and (not (eq (car machine) :svc))
                  (unsigned-byte-p 64 (+ 16 sp))
                  (unsigned-byte-p 64 (+ 4 (proof-world-pc world))))
             (and (equal (proof-world-pc after) (+ 4 (proof-world-pc world)))
                  (equal (proof-world-reg 29 after) (proof-load-word sp machine))
                  (equal (proof-world-reg 30 after) (proof-load-word (+ 8 sp) machine))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (implies (not (member-equal register '(29 30)))
                           (equal (proof-world-reg register after) (proof-world-reg register world)))
                  (equal (cdr after) (cdr world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after)) (+ 16 sp))
                  (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory machine)))))
  :hints (("Goal"
           :in-theory (e/d (proof-number-pop-link-after proof-number-execute-block
                            proof-world-reg proof-world-pc proof-heap-base)
                           (proof-reg))
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-binary-types-call-after (types classifier world)
  (proof-number-types-completion-after nil classifier (proof-number-types-first-ready types world)))

(defund proof-number-binary-types-call-trace-p (types classifier cuts a b world objects packages)
  (and (proof-number-save-and-call-trace-p types cuts world)
       (proof-number-types-completion-trace-p nil classifier cuts a b
                                              (proof-number-types-first-ready types world)
                                              objects packages)))

(defthm proof-number-binary-wrapper-completes
  (let* ((ready (proof-number-types-first-ready types world))
         (after (proof-number-binary-types-call-after types classifier world))
         (count (+ 2 (proof-number-types-completion-steps nil classifier ready)))
         (saved (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
         (machine (proof-world-machine after)))
    (implies (proof-number-binary-types-call-trace-p types classifier cuts a b world objects packages)
             (and (proof-number-exact-prefix-p count cuts world after)
                  (equal (proof-world-pc after) (+ 8 (proof-world-pc world)))
                  (equal (boymoo-model::a64-sp machine) saved)
                  (equal (proof-load-word saved machine) (proof-world-reg 29 world))
                  (equal (proof-load-word (+ 8 saved) machine) (proof-world-reg 30 world))
                  (proof-number-binary-types-p a b after objects packages))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-save-and-call (target types))
                 (:instance proof-number-types-return-or-fallthrough
                            (rational-only nil) (world (proof-number-types-first-ready types world)))
                 (:instance proof-number-type-completion-keeps-disjoint-word
                            (rational-only nil) (world (proof-number-types-first-ready types world))
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16)))
                 (:instance proof-number-type-completion-keeps-disjoint-word
                            (rational-only nil) (world (proof-number-types-first-ready types world))
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 8)))
                 (:instance proof-number-exact-prefix-append
                            (prefix 2)
                            (suffix (proof-number-types-completion-steps
                                     nil classifier (proof-number-types-first-ready types world)))
                            (before world) (middle (proof-number-types-first-ready types world))
                            (after (proof-number-binary-types-call-after types classifier world))))
           :in-theory (enable proof-number-binary-types-call-trace-p proof-number-binary-types-call-after
                              proof-number-save-and-call-trace-p proof-number-types-completion-trace-p
                              proof-number-types-first-trace-p)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-pop-link-trace-p (cuts world)
  (and (not (eq (car (proof-world-machine world)) :svc))
       (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp (proof-world-machine world))))
       (unsigned-byte-p 64 (+ 4 (proof-world-pc world)))
       (proof-number-checked-block-p *proof-number-pop-link-code* cuts world)))

(defthm proof-number-checked-pop-link
  (implies (proof-number-pop-link-trace-p cuts world)
           (proof-number-exact-prefix-p 1 cuts world (proof-number-pop-link-after world)))
  :hints (("Goal"
           :use ((:instance proof-number-checked-block-exact-prefix
                            (instructions *proof-number-pop-link-code*)))
           :in-theory (enable proof-number-pop-link-trace-p proof-number-pop-link-after)))
  :rule-classes nil)

(defthm proof-number-pop-link-keeps-value
  (implies (and (proof-number-pop-link-trace-p cuts world)
                (not (member-equal register '(29 30)))
                (proof-reg-value-p register value world objects packages))
           (proof-reg-value-p register value (proof-number-pop-link-after world) objects packages))
  :hints (("Goal"
           :use (proof-number-pop-link-effects
                 (:instance proof-number-reg-value-with-same-memory
                            (word (proof-world-reg register world))
                            (before world) (after (proof-number-pop-link-after world))))
           :in-theory (enable proof-number-pop-link-trace-p proof-reg-value-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-binary-wrapper-reaches-dispatch
  (let* ((ready (proof-number-types-first-ready types world))
         (called (proof-number-binary-types-call-after types classifier world))
         (after (proof-number-pop-link-after called))
         (count (+ 3 (proof-number-types-completion-steps nil classifier ready))))
    (implies (and (proof-number-binary-types-call-trace-p types classifier cuts a b world objects packages)
                  (proof-number-pop-link-trace-p cuts called))
             (and (proof-number-exact-prefix-p count cuts world after)
                  (equal (proof-world-pc after) (+ 12 (proof-world-pc world)))
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (proof-number-binary-types-p a b after objects packages))))
  :hints (("Goal"
           :use (proof-number-binary-wrapper-completes
                 (:instance proof-number-checked-pop-link
                            (world (proof-number-binary-types-call-after types classifier world)))
                 (:instance proof-number-pop-link-effects (register 3)
                            (world (proof-number-binary-types-call-after types classifier world)))
                 (:instance proof-number-pop-link-keeps-value
                            (register 0) (value (fix a))
                            (world (proof-number-binary-types-call-after types classifier world)))
                 (:instance proof-number-pop-link-keeps-value
                            (register 1) (value (fix b))
                            (world (proof-number-binary-types-call-after types classifier world)))
                 (:instance proof-number-exact-prefix-append
                            (prefix (+ 2 (proof-number-types-completion-steps
                                          nil classifier (proof-number-types-first-ready types world))))
                            (suffix 1) (before world)
                            (middle (proof-number-binary-types-call-after types classifier world))
                            (after (proof-number-pop-link-after
                                    (proof-number-binary-types-call-after types classifier world)))))
           :in-theory (enable proof-number-binary-types-p proof-number-pop-link-trace-p)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-unary-wrapper-reaches-dispatch
  (let* ((ready (proof-number-types-first-ready classifier world))
         (called (proof-number-classifier-after ready))
         (after (proof-number-pop-link-after called))
         (count (+ 3 (len (proof-number-classifier-path ready)))))
    (implies (and (proof-number-save-and-call-trace-p classifier cuts world)
                  (proof-number-classifier-trace-p cuts ready)
                  (proof-reg-value-p 0 a ready objects packages)
                  (proof-number-pop-link-trace-p cuts called))
             (and (proof-number-exact-prefix-p count cuts world after)
                  (equal (proof-world-pc after) (+ 12 (proof-world-pc world)))
                  (equal (proof-world-reg 29 after) (proof-world-reg 29 world))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp (proof-world-machine world)))
                  (proof-reg-value-p 0 a after objects packages)
                  (equal (proof-world-reg 3 after) (proof-number-datum-class a)))))
  :hints (("Goal"
           :use ((:instance proof-number-checked-save-and-call (target classifier))
                 (:instance proof-number-classification-keeps-values
                            (world (proof-number-types-first-ready classifier world))
                            (register 0) (value a) (operand a))
                 (:instance proof-number-checked-pop-link
                            (world (proof-number-classifier-after (proof-number-types-first-ready classifier world))))
                 (:instance proof-number-pop-link-effects
                            (register 3)
                            (world (proof-number-classifier-after (proof-number-types-first-ready classifier world))))
                 (:instance proof-number-pop-link-keeps-value
                            (register 0) (value a)
                            (world (proof-number-classifier-after (proof-number-types-first-ready classifier world))))
                 (:instance word-with-same-memory
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (first (proof-world-machine (proof-number-types-first-ready classifier world)))
                            (last (proof-world-machine
                                   (proof-number-classifier-after (proof-number-types-first-ready classifier world)))))
                 (:instance word-with-same-memory
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 8))
                            (first (proof-world-machine (proof-number-types-first-ready classifier world)))
                            (last (proof-world-machine
                                   (proof-number-classifier-after (proof-number-types-first-ready classifier world)))))
                 (:instance proof-number-exact-prefix-append
                            (prefix 2) (suffix (len (proof-number-classifier-path
                                                     (proof-number-types-first-ready classifier world))))
                            (before world) (middle (proof-number-types-first-ready classifier world))
                            (after (proof-number-classifier-after (proof-number-types-first-ready classifier world))))
                 (:instance proof-number-exact-prefix-append
                            (prefix (+ 2 (len (proof-number-classifier-path
                                               (proof-number-types-first-ready classifier world)))))
                            (suffix 1) (before world)
                            (middle (proof-number-classifier-after (proof-number-types-first-ready classifier world)))
                            (after (proof-number-pop-link-after
                                    (proof-number-classifier-after (proof-number-types-first-ready classifier world))))))
           :in-theory (enable proof-number-pop-link-trace-p)
           :do-not-induct t))
  :rule-classes nil)
