(in-package "BOYMOO-PROOFS")

(include-book "large-entry")
(include-book "stack-writes")
(include-book "cons-heap")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defund allocation-large-save-room-p (caller)
  (let* ((save (- (allocation-sp caller) 32))
         (floor (- (proof-machine-limit caller) *proof-machine-margin*)))
    (and (posp save)
         (proof-subspan-p save 32 floor (+ floor *proof-machine-reservation*)))))

(local
 (defthm allocation-large-layout-keeps-stacks-separate
   (let ((floor (- (proof-machine-limit caller) *proof-machine-margin*)))
     (implies (proof-heap-layout-p caller)
              (proof-disjoint-p (proof-stack-base caller) (proof-stack-end caller)
                                floor (+ floor *proof-machine-reservation*))))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-align-up proof-covered-p proof-regions-p proof-disjoint-p
                                      proof-runtime-word mod)))))

(local
 (defthm allocation-large-save-words-are-in-machine-reservation
   (implies (allocation-large-save-room-p caller)
            (allocation-stack-word-writes-p (allocation-large-save-writes caller) caller))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (allocation-large-save-room-p)
                                   (proof-stack-base proof-stack-end proof-machine-limit))))))

(local
 (defthm allocation-large-four-save-words-avoid-a-span
   (let ((sp (allocation-sp caller))
         (save (- (allocation-sp caller) 32)))
     (implies (and (posp save) (proof-span-p save 32)
                   (proof-disjoint-p save sp lower upper))
              (allocation-word-writes-avoid-span-p (allocation-large-save-writes caller) lower upper)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable allocation-word-register-range)))))

(local
 (defthm allocation-large-save-interval-geometry
   (let* ((sp (allocation-sp caller))
          (save (- sp 32))
          (end (+ (- (proof-machine-limit caller) *proof-machine-margin*) *proof-machine-reservation*)))
     (implies (and (proof-heap-layout-p caller) (allocation-large-save-room-p caller))
              (and (<= 32 sp) (posp save) (proof-span-p save 32)
                   (proof-disjoint-p save sp (proof-stack-base caller) (proof-stack-top caller))
                   (proof-disjoint-p save sp sp end))))
   :rule-classes nil
   :hints (("Goal" :use (allocation-large-layout-keeps-stacks-separate
                         (:instance allocation-layout-storage-spans (world caller)))
            :in-theory (e/d (allocation-large-save-room-p)
                            (proof-heap-layout-p proof-stack-base proof-stack-end proof-stack-top proof-machine-limit
                             proof-runtime-word allocation-runtime-word-as-load))))))

(defthm allocation-large-saves-within-unused-machine-stack
  (let* ((sp (allocation-sp caller))
         (stack (proof-stack-base caller))
         (top (proof-stack-top caller))
         (end (+ (- (proof-machine-limit caller) *proof-machine-margin*) *proof-machine-reservation*))
         (writes (allocation-large-save-writes caller)))
    (implies (and (proof-heap-layout-p caller)
                  (allocation-large-save-room-p caller))
             (and (<= 32 sp)
                  (allocation-stack-word-writes-p writes caller)
                  (allocation-word-writes-avoid-span-p writes stack top)
                  (allocation-word-writes-avoid-span-p writes sp end))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-save-words-are-in-machine-reservation allocation-large-save-interval-geometry
                 (:instance allocation-large-four-save-words-avoid-a-span
                  (lower (proof-stack-base caller)) (upper (proof-stack-top caller)))
                 (:instance allocation-large-four-save-words-avoid-a-span
                  (lower (allocation-sp caller))
                  (upper (+ (- (proof-machine-limit caller) *proof-machine-margin*) *proof-machine-reservation*))))
           :in-theory (disable proof-heap-layout-p allocation-large-save-writes allocation-stack-word-writes-p
                               allocation-word-writes-avoid-span-p proof-span-p proof-disjoint-p
                               proof-stack-base proof-stack-end proof-stack-top proof-machine-limit))))

(defthm allocation-large-constructor-prefix-controls
  (let ((length (proof-world-reg 0 caller)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p caller)
                  (not (proof-world-stop caller))
                  (equal (proof-world-pc caller) (allocation-large-string-address origin 0))
                  (<= 32 (allocation-sp caller))
                  (<= 128 (proof-heap-base caller))
                  (< length *proof-space-size*)
                  (equal sized (allocation-path-end *allocation-large-size-path* caller))
                  (equal rounded (allocation-path-end *allocation-large-round-path* sized))
                  (equal budget (allocation-path-end *allocation-large-accounting-load-path* rounded)))
             (and (proof-register-frame-p 30 '(1 2 19 20 21) caller budget)
                  (equal (allocation-sp budget) (- (allocation-sp caller) 32))
                  (equal (allocation-memory budget)
                         (allocation-memory (allocation-write-words (allocation-large-save-writes caller) caller)))
                  (equal (proof-world-pc budget) (allocation-large-string-address origin 12))
                  (equal (proof-world-reg 19 budget) length)
                  (equal (proof-world-reg 20 budget) (allocation-large-mapping-size length))
                  (equal (proof-world-reg 21 budget) (- (proof-heap-base caller) 128))
                  (equal (proof-world-reg 1 budget) (proof-string-bytes-since-collection budget))
                  (equal (proof-world-reg 2 budget) (proof-string-budget budget))
                  (allocation-machine-state-p budget) (not (proof-world-stop budget))
                  (equal (proof-world-regions budget) (proof-world-regions caller))
                  (equal (proof-world-replies budget) (proof-world-replies caller))
                  (proof-streams-preserved-p caller budget))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-size-prefix-saves-caller (before sized))
                 (:instance allocation-large-size-machine-edge (before caller) (cut sized))
                 allocation-large-save-prefix-footprint
                 (:instance allocation-large-round-and-load-budget (before sized) (after budget))
                 (:instance allocation-register-frame-member
                  (register 28) (upper 30) (clobbers '(1 19)) (before caller) (after sized))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small '(1 19)) (large '(1 2 19 20 21)) (before caller) (after sized))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small '(1 2 20 21)) (large '(1 2 19 20 21)) (before sized) (after budget))
                 (:instance allocation-register-frame-transitive
                  (register 30) (clobbers '(1 2 19 20 21)) (before caller) (middle sized) (after budget))
                 (:instance allocation-equal-memory-is-model-equivalence (first sized) (last budget)))
           :in-theory (disable allocation-path-end proof-register-frame-p allocation-large-save-writes
                               allocation-write-words allocation-code-origin-p allocation-large-string-address
                               allocation-large-mapping-size allocation-runtime-word-as-load proof-load-word
                               allocation-equal-memory-is-model-equivalence))))

(local
 (defthm allocation-large-constructor-stack-save-aligned
   (implies (and (integerp sp) (equal (mod sp 16) 0))
            (equal (mod (- sp 32) 16) 0))))

(defthm allocation-large-entry-stack-state
  (let* ((clobbers '(1 2 19 20 21))
         (writes (allocation-large-save-writes caller)))
    (implies (and (proof-heap-layout-p caller)
                  (allocation-large-save-room-p caller)
                  (proof-register-frame-p 30 clobbers caller budget)
                  (equal (allocation-sp budget) (- (allocation-sp caller) 32))
                  (equal (allocation-memory budget) (allocation-memory (allocation-write-words writes caller)))
                  (not (proof-world-stop budget))
                  (equal (proof-world-regions budget) (proof-world-regions caller))
                  (proof-streams-preserved-p caller budget))
             (and (allocation-stack-write-state-p writes caller budget)
                  (equal (proof-stack-top budget) (proof-stack-top caller))
                  (allocation-stack-pointers-in-original-reservations-p caller budget))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-saves-within-unused-machine-stack
                 (:instance allocation-word-register-range (register 0) (world caller))
                 (:instance allocation-register-frame-member
                  (register 23) (upper 30) (clobbers '(1 2 19 20 21)) (before caller) (after budget))
                 (:instance allocation-register-frame-member
                  (register 24) (upper 30) (clobbers '(1 2 19 20 21)) (before caller) (after budget))
                 (:instance allocation-register-frame-member
                  (register 25) (upper 30) (clobbers '(1 2 19 20 21)) (before caller) (after budget))
                 (:instance allocation-register-frame-member
                  (register 26) (upper 30) (clobbers '(1 2 19 20 21)) (before caller) (after budget))
                 (:instance allocation-register-frame-member
                  (register 27) (upper 30) (clobbers '(1 2 19 20 21)) (before caller) (after budget))
                 (:instance allocation-register-frame-member
                  (register 28) (upper 30) (clobbers '(1 2 19 20 21)) (before caller) (after budget)))
           :in-theory (e/d (allocation-stack-write-state-p allocation-stack-pointers-in-original-reservations-p
                            allocation-large-save-room-p unsigned-byte-p acl2::integer-range-p)
                           (proof-register-frame-p allocation-word-register-range allocation-stack-word-writes-p
                            allocation-large-save-writes allocation-write-words proof-covered-p proof-regions-p
                            proof-disjoint-p proof-align-up proof-static-size proof-page-size-p
                            proof-world-regions proof-runtime-word allocation-runtime-word-as-load mod)))))

(defthm allocation-large-entry-preserves-caller-heap
  (let* ((top (proof-stack-top caller))
         (clobbers '(1 2 19 20 21))
         (writes (allocation-large-save-writes caller)))
    (implies (and (proof-heap-p caller objects packages)
                  (allocation-large-save-room-p caller)
                  (natp index) (equal top (+ (proof-stack-base caller) (* 8 index)))
                  (proof-register-frame-p 30 clobbers caller budget)
                  (equal (allocation-sp budget) (- (allocation-sp caller) 32))
                  (equal (allocation-memory budget) (allocation-memory (allocation-write-words writes caller)))
                  (not (proof-world-stop budget))
                  (equal (proof-world-regions budget) (proof-world-regions caller))
                  (proof-streams-preserved-p caller budget))
             (proof-preserved-heap-p nil caller budget objects objects packages)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world caller))
                 allocation-large-entry-stack-state allocation-large-saves-within-unused-machine-stack
                 (:instance allocation-stack-write-state-keeps-existing-heap
                  (before caller) (after budget) (writes (allocation-large-save-writes caller))))
           :in-theory (disable proof-heap-p proof-heap-layout-p proof-preserved-heap-p proof-register-frame-p
                               allocation-stack-write-state-p allocation-stack-pointers-in-original-reservations-p
                               allocation-write-words allocation-large-save-writes allocation-stack-word-writes-p
                               allocation-word-writes-avoid-span-p proof-stack-base proof-stack-top proof-machine-limit))))

(local
 (defthm allocation-large-entry-old-layout-flags
   (implies (proof-heap-layout-p world)
            (and (not (proof-world-stop world)) (<= 128 (proof-heap-base world))))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (disable proof-align-up proof-regions-p proof-covered-p proof-disjoint-p mod)))))

(defthm allocation-large-checked-entry-preserves-heap-to-budget
  (let* ((length (proof-world-reg 0 caller))
         (base (proof-heap-base caller))
         (path *allocation-large-entry-to-budget-path*)
         (cuts (list (allocation-large-string-address origin 12))))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p caller)
                  (equal (proof-world-pc caller) (allocation-large-string-address origin 0))
                  (proof-heap-p caller objects packages)
                  (allocation-large-save-room-p caller)
                  (natp index) (equal (proof-stack-top caller) (+ (proof-stack-base caller) (* 8 index)))
                  (< length *proof-space-size*)
                  (equal sized (allocation-path-end *allocation-large-size-path* caller))
                  (equal rounded (allocation-path-end *allocation-large-round-path* sized))
                  (equal budget (allocation-path-end *allocation-large-accounting-load-path* rounded))
                  (allocation-path-ready-p path cuts caller))
             (and (proof-segment-p (len path) cuts caller :cut budget)
                  (proof-preserved-heap-p nil caller budget objects objects packages)
                  (allocation-large-caller-saves-p caller budget)
                  (allocation-machine-state-p budget) (not (proof-world-stop budget))
                  (equal (proof-world-reg 19 budget) length)
                  (equal (proof-world-reg 20 budget) (allocation-large-mapping-size length))
                  (equal (proof-world-reg 21 budget) (- base 128))
                  (equal (proof-heap-base budget) base)
                  (equal (proof-world-reg 1 budget) (proof-string-bytes-since-collection budget))
                  (equal (proof-world-reg 2 budget) (proof-string-budget budget)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world caller))
                 allocation-large-saves-within-unused-machine-stack allocation-large-constructor-prefix-controls
                 allocation-large-checked-entry-to-budget allocation-large-entry-preserves-caller-heap
                 (:instance allocation-register-frame-member
                  (register 28) (upper 30) (clobbers '(1 2 19 20 21)) (before caller) (after budget)))
           :in-theory (disable allocation-path-end allocation-path-ready-p allocation-code-origin-p
                               allocation-large-string-address proof-segment-p proof-register-frame-p
                               proof-heap-p proof-heap-layout-p proof-preserved-heap-p
                               allocation-large-mapping-size allocation-large-save-writes allocation-write-words
                               allocation-stack-word-writes-p allocation-word-writes-avoid-span-p
                               proof-heap-base proof-runtime-word allocation-runtime-word-as-load))))

(defthm allocation-large-budget-addition-exact-on-heap
  (let* ((length (proof-world-reg 19 before))
         (size (proof-world-reg 20 before))
         (counter (proof-world-reg 1 before)))
    (implies (and (proof-heap-p before objects packages)
                  (< length *proof-space-size*)
                  (equal size (allocation-large-mapping-size length))
                  (equal counter (proof-string-bytes-since-collection before)))
             (< (+ counter size) *allocation-word-modulus*)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-budget-sum-fits
                  (world before) (length (proof-world-reg 19 before))
                  (headers (cdr (proof-external-objects (proof-external-head before) (len objects) before objects)))))
           :in-theory (disable allocation-large-mapping-size proof-heap-layout-p proof-static-p proof-object-map-p
                               proof-string-accounting-p proof-external-objects proof-heap-object-spans-p proof-stack-prefix
                               proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p))))

(defthm allocation-large-budget-edge-keeps-heap
  (implies (and (proof-heap-p before objects packages)
                (allocation-machine-state-p before)
                (allocation-code-origin-p origin)
                (equal (proof-world-pc before) (allocation-large-string-address origin 12))
                (< (+ (proof-world-reg 1 before) (proof-world-reg 20 before)) *allocation-word-modulus*)
                (equal cut (allocation-path-end (allocation-large-budget-path before) before)))
           (proof-preserved-heap-p nil before cut objects objects packages))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-budget-machine-edge
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-large-budget-path-keeps-frame (after cut))
                 (:instance allocation-context-from-register-frame (after cut) (clobbers '(0 1 30)))
                 (:instance allocation-register-frame-member (after cut) (register 24) (upper 30) (clobbers '(0 1 30)))
                 (:instance allocation-register-frame-member (after cut) (register 26) (upper 30) (clobbers '(0 1 30)))
                 (:instance allocation-register-frame-member (after cut) (register 27) (upper 30) (clobbers '(0 1 30)))
                 (:instance allocation-heap-under-same-context-and-frontiers (after cut))
                 (:instance allocation-preserved-heap-under-same-context (after cut)))
           :in-theory (disable allocation-path-end allocation-large-budget-path allocation-large-string-address
                               allocation-large-budget-target proof-heap-p proof-heap-layout-p
                               proof-preserved-heap-p proof-register-frame-p proof-streams-preserved-p))))

(defthm allocation-large-checked-budget-branches-with-heap-and-saves
  (let* ((path (allocation-large-budget-path before))
         (target (allocation-large-budget-target before origin))
         (cuts (list target)))
    (implies (and (proof-heap-p before objects packages)
                  (allocation-large-caller-saves-p caller before)
                  (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (equal (proof-world-pc before) (allocation-large-string-address origin 12))
                  (< (proof-world-reg 19 before) *proof-space-size*)
                  (equal (proof-world-reg 20 before) (allocation-large-mapping-size (proof-world-reg 19 before)))
                  (equal (proof-world-reg 1 before) (proof-string-bytes-since-collection before))
                  (equal (proof-world-reg 2 before) (proof-string-budget before))
                  (allocation-path-ready-p path cuts before)
                  (equal cut (allocation-path-end path before)))
             (and (proof-segment-p (len path) cuts before :cut cut)
                  (equal (proof-world-pc cut) target)
                  (proof-preserved-heap-p nil before cut objects objects packages)
                  (allocation-large-caller-saves-p caller cut)
                  (allocation-machine-state-p cut)
                  (not (proof-world-stop cut))
                  (equal (proof-world-reg 19 cut) (proof-world-reg 19 before))
                  (equal (proof-world-reg 20 cut) (proof-world-reg 20 before))
                  (equal (proof-world-reg 21 cut) (proof-world-reg 21 before))
                  (equal (proof-heap-base cut) (proof-heap-base before))
                  (implies (allocation-large-collect-p (proof-world-reg 1 before) (proof-world-reg 20 before)
                                                       (proof-world-reg 2 before))
                           (and (equal (proof-world-reg 0 cut) 0)
                                (equal (proof-world-reg 1 cut) 0)
                                (equal (proof-world-reg 30 cut) (allocation-code-address "rt:map-string" origin)))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world before))
                 allocation-large-budget-addition-exact-on-heap allocation-large-budget-edge-keeps-heap
                 allocation-large-budget-checked-edge allocation-large-budget-machine-edge
                 (:instance allocation-large-budget-path-keeps-frame (after cut))
                 (:instance allocation-large-budget-check-preserves-caller-saves (after cut)))
           :in-theory (disable allocation-path-end allocation-path-ready-p allocation-large-budget-path
                               allocation-large-budget-target allocation-large-collect-p proof-segment-p
                               allocation-code-origin-p allocation-large-string-address allocation-large-mapping-size
                               proof-heap-p proof-heap-layout-p proof-preserved-heap-p
                               proof-register-frame-p proof-streams-preserved-p))))
