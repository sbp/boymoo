(in-package "BOYMOO-PROOFS")

(include-book "memory-footprint")
(include-book "formula-entry")
(include-book "completion-return")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (disable proof-step proof-run proof-segment-p proof-execute
                     proof-instruction-effect proof-number-checked-block-p
                     proof-reg proof-world-reg proof-world-pc proof-world-machine
                     proof-load-word proof-heap-base proof-stack-top proof-stack-base
                     proof-view proof-machine-value-p proof-reg-value-p
                     proof-object-map-p proof-object-disjoint-p proof-stack-prefix
                     proof-prefix-preserved-p proof-number-memory-change-p
                     boymoo-model::a64-unsigned boymoo-model::a64-sp
                     boymoo-model::a64-read-reg boymoo-model::a64-write-reg
                     boymoo-model::a64-set-pc boymoo-model::a64-pc
                     boymoo-model::a64-store boymoo-model::a64-memory
                     boymoo-model::a64-write-bytes
                     (:definition update-nth) (:definition nth))))

(local
 (defthm memory-of-store
   (equal (boymoo-model::a64-memory (boymoo-model::a64-store size address value machine))
          (boymoo-model::a64-write-bytes size address value (boymoo-model::a64-memory machine)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-store boymoo-model::a64-memory)))))

(defthm proof-number-world-tail-of-machine-update
  (equal (cdr (update-nth 0 machine world)) (cdr world))
  :hints (("Goal" :in-theory (enable (:definition update-nth)))))

(defthm proof-number-pair-store-changes-only-footprint
  (implies (and (proof-span-p address 16) (<= start address) (<= (+ address 16) end))
           (proof-number-memory-change-p
            start end machine
            (boymoo-model::a64-store
             8 (+ 8 address) right (boymoo-model::a64-store 8 address left machine))))
  :hints (("Goal"
           :use ((:instance proof-number-store-changes-only-footprint
                            (dest address) (size 8) (value left))
                 (:instance proof-number-store-changes-only-footprint
                            (dest (+ 8 address)) (size 8) (value right)
                            (machine (boymoo-model::a64-store 8 address left machine)))
                 (:instance proof-number-memory-change-composes
                            (first machine)
                            (middle (boymoo-model::a64-store 8 address left machine))
                            (last (boymoo-model::a64-store
                                   8 (+ 8 address) right
                                   (boymoo-model::a64-store 8 address left machine)))))))
  :rule-classes nil)

(defthm proof-number-save-and-call-effects
  (let* ((machine (proof-world-machine world))
         (saved (- (boymoo-model::a64-sp machine) 16))
         (after (proof-number-types-first-ready target world)))
    (implies (not (eq (car machine) :svc))
             (and (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory
                          (boymoo-model::a64-store
                           8 (+ 8 saved) (proof-world-reg 30 world)
                           (boymoo-model::a64-store 8 saved (proof-world-reg 29 world) machine))))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (implies (not (equal register 30))
                           (equal (proof-world-reg register after)
                                  (proof-world-reg register world)))
                  (equal (cdr after) (cdr world)))))
  :hints (("Goal"
           :in-theory (enable proof-number-types-first-ready proof-number-types-first-code
                              proof-world-reg proof-heap-base)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-save-and-call-keeps-arguments
  (let* ((machine (proof-world-machine world))
         (saved (- (boymoo-model::a64-sp machine) 16))
         (after (proof-number-types-first-ready target world)))
    (implies (and (not (eq (car machine) :svc))
                  (proof-span-p saved 16)
                  (posp saved)
                  (proof-object-map-p objects objects nil (proof-heap-base world) packages machine)
                  (proof-object-disjoint-p saved (+ saved 16) objects machine)
                  (not (equal register 30))
                  (proof-reg-value-p register value world objects packages))
             (proof-reg-value-p register value after objects packages)))
  :hints (("Goal"
           :use (proof-number-save-and-call-effects
                 (:instance proof-number-pair-store-changes-only-footprint
                            (address (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (end (boymoo-model::a64-sp (proof-world-machine world)))
                            (machine (proof-world-machine world))
                            (left (proof-world-reg 29 world)) (right (proof-world-reg 30 world)))
                 (:instance proof-number-memory-change-with-same-final-memory
                            (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (end (boymoo-model::a64-sp (proof-world-machine world)))
                            (first (proof-world-machine world))
                            (last (proof-world-machine (proof-number-types-first-ready target world)))
                            (other (boymoo-model::a64-store
                                    8 (- (boymoo-model::a64-sp (proof-world-machine world)) 8)
                                    (proof-world-reg 30 world)
                                    (boymoo-model::a64-store
                                     8 (- (boymoo-model::a64-sp (proof-world-machine world)) 16)
                                     (proof-world-reg 29 world) (proof-world-machine world)))))
                 (:instance proof-number-disjoint-footprint-keeps-old-values
                            (before world) (after (proof-number-types-first-ready target world))
                            (start (- (boymoo-model::a64-sp (proof-world-machine world)) 16))
                            (end (boymoo-model::a64-sp (proof-world-machine world)))
                            (old-objects objects) (extra nil) (word (proof-world-reg register world))))
           :in-theory (enable proof-reg-value-p)
           :do-not-induct t))
  :rule-classes nil)

(defund proof-number-append-storage-p (size world objects packages)
  (let* ((machine (proof-world-machine world))
         (base (proof-heap-base world))
         (top (proof-stack-top world))
         (metadata (- base 88)))
    (and (posp top)
         (proof-span-p top size)
         (proof-span-p metadata 8)
         (proof-disjoint-p metadata (+ metadata 8) top (+ top size))
         (proof-object-map-p objects objects nil base packages machine)
         (proof-object-disjoint-p top (+ top size) objects machine)
         (proof-stack-prefix top world objects packages))))

(defthm proof-number-value-store-effects
  (let* ((machine (proof-world-machine world))
         (top (proof-stack-top world))
         (after (proof-number-execute-block
                 (proof-number-formula-argument-store-instructions arity) world))
         (first (boymoo-model::a64-store 8 top (proof-world-reg 0 world) machine))
         (last (if (equal arity 1)
                   first
                 (boymoo-model::a64-store 8 (+ 8 top) (proof-world-reg 1 world) first))))
    (implies (and (not (eq (car machine) :svc))
                  (member-equal arity '(1 2))
                  (unsigned-byte-p 64 (+ top (* 8 arity))))
             (and (equal (boymoo-model::a64-memory (proof-world-machine after))
                         (boymoo-model::a64-memory last))
                  (equal (proof-heap-base after) (proof-heap-base world))
                  (equal (proof-stack-top after) (+ top (* 8 arity)))
                  (equal (cdr after) (cdr world))
                  (equal (boymoo-model::a64-sp (proof-world-machine after))
                         (boymoo-model::a64-sp machine))
                  (implies (not (equal register 25))
                           (equal (proof-world-reg register after)
                                  (proof-world-reg register world))))))
  :hints (("Goal" :in-theory (enable proof-number-formula-argument-store-instructions
                                     proof-world-reg proof-heap-base proof-stack-top)
                  :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-value-store-keeps-frame-memory
  (let* ((machine (proof-world-machine world))
         (top (proof-stack-top world))
         (end (+ top (* 8 arity)))
         (after (proof-number-execute-block
                 (proof-number-formula-argument-store-instructions arity) world)))
    (implies (and (not (eq (car machine) :svc))
                  (member-equal arity '(1 2))
                  (proof-span-p top (* 8 arity))
                  (unsigned-byte-p 64 end))
             (proof-number-memory-change-p top end machine (proof-world-machine after))))
  :hints (("Goal"
           :use ((:instance proof-number-value-store-effects (register 0))
                 (:instance proof-number-store-changes-only-footprint
                            (dest (proof-stack-top world)) (size 8) (start (proof-stack-top world))
                            (end (+ 8 (proof-stack-top world))) (value (proof-world-reg 0 world))
                            (machine (proof-world-machine world)))
                 (:instance proof-number-pair-store-changes-only-footprint
                            (address (proof-stack-top world)) (start (proof-stack-top world))
                            (end (+ 16 (proof-stack-top world)))
                            (left (proof-world-reg 0 world)) (right (proof-world-reg 1 world))
                            (machine (proof-world-machine world)))
                 (:instance proof-number-memory-change-with-same-final-memory
                            (start (proof-stack-top world)) (end (+ (proof-stack-top world) (* 8 arity)))
                            (first (proof-world-machine world))
                            (last (proof-world-machine
                                   (proof-number-execute-block
                                    (proof-number-formula-argument-store-instructions arity) world)))
                            (other (if (equal arity 1)
                                       (boymoo-model::a64-store
                                        8 (proof-stack-top world) (proof-world-reg 0 world)
                                        (proof-world-machine world))
                                     (boymoo-model::a64-store
                                      8 (+ 8 (proof-stack-top world)) (proof-world-reg 1 world)
                                      (boymoo-model::a64-store
                                       8 (proof-stack-top world) (proof-world-reg 0 world)
                                       (proof-world-machine world)))))))
           :in-theory (disable proof-number-execute-block)
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-value-store-preserves-views
  (let* ((top (proof-stack-top world))
         (size (* 8 arity))
         (after (proof-number-execute-block
                 (proof-number-formula-argument-store-instructions arity) world)))
    (implies (and (member-equal arity '(1 2))
                  (not (eq (car (proof-world-machine world)) :svc))
                  (unsigned-byte-p 64 (+ top size))
                  (proof-number-append-storage-p size world objects packages))
             (and (proof-prefix-preserved-p top world after objects objects packages)
                  (implies (proof-machine-value-p word value world objects packages)
                           (proof-machine-value-p word value after objects packages)))))
  :hints (("Goal"
           :use (proof-number-value-store-keeps-frame-memory
                 (:instance proof-number-value-store-effects (register 0))
                 (:instance proof-number-disjoint-footprint-keeps-old-values
                            (old-objects objects) (extra nil) (before world)
                            (start (proof-stack-top world)) (end (+ (proof-stack-top world) (* 8 arity)))
                            (after (proof-number-execute-block
                                    (proof-number-formula-argument-store-instructions arity) world)))
                 (:instance proof-number-footprint-keeps-disjoint-span
                            (lower (- (proof-heap-base world) 88))
                            (upper (- (proof-heap-base world) 80))
                            (start (proof-stack-top world)) (end (+ (proof-stack-top world) (* 8 arity)))
                            (first (proof-world-machine world))
                            (last (proof-world-machine
                                   (proof-number-execute-block
                                    (proof-number-formula-argument-store-instructions arity) world))))
                 (:instance proof-number-word-agrees-in-machine-span
                            (address (- (proof-heap-base world) 88))
                            (lower (- (proof-heap-base world) 88))
                            (upper (- (proof-heap-base world) 80))
                            (first (proof-world-machine world))
                            (last (proof-world-machine
                                   (proof-number-execute-block
                                    (proof-number-formula-argument-store-instructions arity) world))))
                 (:instance proof-number-disjoint-footprint-keeps-prefix
                            (top (proof-stack-top world)) (old-objects objects) (before world)
                            (start (proof-stack-top world)) (end (+ (proof-stack-top world) (* 8 arity)))
                            (after (proof-number-execute-block
                                    (proof-number-formula-argument-store-instructions arity) world))))
           :in-theory (e/d (proof-number-append-storage-p proof-stack-base proof-runtime-word)
                           (proof-number-execute-block proof-number-objects-memory-p))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-argument-trace-from-disjoint-store
  (let* ((arity (len args))
         (size (* 8 arity))
         (code (proof-number-formula-argument-store-instructions arity))
         (pc (+ 8 (proof-world-pc world))))
    (implies (and (proof-number-argument-list-p args)
                  (proof-register-arguments-p args 0 world objects packages)
                  (not (eq (car (proof-world-machine world)) :svc))
                  (proof-number-append-storage-p size world objects packages)
                  (unsigned-byte-p 64 (+ (proof-stack-top world) size))
                  (unsigned-byte-p 64 pc)
                  (equal (proof-world-reg 19 world) (proof-stack-top world))
                  (proof-number-checked-block-p code (list pc) world)
                  (proof-number-checked-block-p code (list link) world))
             (proof-number-formula-argument-trace-p args link world objects packages)))
  :hints (("Goal"
           :use ((:instance proof-number-value-store-preserves-views
                            (arity (len args)) (word (proof-world-reg 0 world)) (value (car args)))
                 (:instance proof-number-value-store-preserves-views
                            (arity (len args)) (word (proof-world-reg 1 world)) (value (cadr args))))
           :in-theory (e/d (proof-number-argument-list-p proof-number-formula-argument-trace-p
                            proof-number-formula-arguments-after proof-reg-value-p
                            proof-number-append-storage-p)
                           (proof-number-execute-block proof-object-disjoint-p))
           :expand ((len (cdr args))
                    (proof-register-arguments-p (cdr args) 1 world objects packages))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-spill-trace-from-disjoint-store
  (let* ((size 8)
         (top (proof-stack-top world))
         (pc (+ 8 (proof-world-pc world))))
    (implies (and (not (eq (car (proof-world-machine world)) :svc))
                  (proof-number-append-storage-p size world objects packages)
                  (unsigned-byte-p 64 (+ top size))
                  (unsigned-byte-p 64 pc)
                  (proof-reg-value-p 0 value world objects packages)
                  (proof-number-checked-block-p *proof-number-formula-spill-instructions* (list pc) world)
                  (proof-number-checked-block-p *proof-number-formula-spill-instructions* (list link) world))
             (proof-number-formula-spill-trace-p value link world objects packages)))
  :hints (("Goal"
           :use ((:instance proof-number-value-store-preserves-views
                            (arity 1) (word (proof-world-reg 0 world))))
           :in-theory (e/d (proof-number-formula-spill-trace-p proof-number-formula-spill-after
                            proof-number-formula-argument-store-instructions
                            proof-number-append-storage-p proof-reg-value-p)
                           (proof-number-execute-block))
           :do-not-induct t))
  :rule-classes nil)

(defthm proof-number-type-completion-trace-from-disjoint-save
  (let* ((machine (proof-world-machine world))
         (saved (- (boymoo-model::a64-sp machine) 16))
         (ready (proof-number-types-first-ready classifier world))
         (first (proof-number-classifier-after ready))
         (classified (proof-number-types-classified rational-only classifier world))
         (code (proof-number-types-finish-code rational-only)))
    (implies (and (proof-number-types-first-trace-p classifier cuts world)
                  (proof-number-types-second-trace-p rational-only classifier cuts first)
                  (posp saved)
                  (proof-object-map-p objects objects nil (proof-heap-base world) packages machine)
                  (proof-object-disjoint-p saved (+ 16 saved) objects machine)
                  (proof-reg-value-p 0 a world objects packages)
                  (proof-reg-value-p 1 b world objects packages)
                  (not (eq (car (proof-world-machine classified)) :svc))
                  (unsigned-byte-p 64 (+ 16 (boymoo-model::a64-sp (proof-world-machine classified))))
                  (unsigned-byte-p 64 (+ (* 4 (len code)) (proof-world-pc classified)))
                  (proof-number-checked-block-p
                   code (list (proof-number-types-finish-target rational-only classified)) classified)
                  (proof-number-checked-block-p code cuts classified))
             (proof-number-types-completion-trace-p rational-only classifier cuts a b world objects packages)))
  :hints (("Goal"
           :use ((:instance proof-number-save-and-call-keeps-arguments
                            (target classifier) (register 0) (value a))
                 (:instance proof-number-save-and-call-keeps-arguments
                            (target classifier) (register 1) (value b)))
           :in-theory (enable proof-number-types-first-trace-p proof-number-types-completion-trace-p)
           :do-not-induct t))
  :rule-classes nil)
