(in-package "BOYMOO-PROOFS")

(include-book "large-entry-heap")
(include-book "large-composition")
(include-book "external-bounds")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defund allocation-large-budget-inputs-p (origin world)
  (let ((length (proof-world-reg 19 world)))
    (and (allocation-code-origin-p origin)
         (allocation-machine-state-p world)
         (equal (proof-world-pc world) (allocation-large-string-address origin 12))
         (< length *proof-space-size*)
         (equal (proof-world-reg 20 world) (allocation-large-mapping-size length))
         (equal (proof-world-reg 21 world) (- (proof-heap-base world) 128))
         (equal (proof-world-reg 1 world) (proof-string-bytes-since-collection world))
         (equal (proof-world-reg 2 world) (proof-string-budget world)))))

(defthm allocation-large-budget-without-collection-to-map
  (let* ((path (allocation-large-budget-path budget))
         (cuts (list (allocation-code-address "rt:map-string" origin))))
    (implies (and (allocation-large-budget-inputs-p origin budget)
                  (proof-heap-p budget objects packages)
                  (allocation-large-caller-saves-p caller budget)
                  (not (allocation-large-collect-p (proof-world-reg 1 budget)
                                                    (proof-world-reg 20 budget)
                                                    (proof-world-reg 2 budget)))
                  (allocation-path-ready-p path cuts budget)
                  (equal mapped (allocation-path-end path budget)))
             (and (proof-segment-p (len path) cuts budget :cut mapped)
                  (allocation-large-map-entry-p origin mapped)
                  (allocation-large-caller-saves-p caller mapped)
                  (proof-preserved-heap-p nil budget mapped objects objects packages)
                  (equal (proof-world-reg 20 mapped) (allocation-large-mapping-size (proof-world-reg 19 mapped)))
                  (equal (proof-world-reg 21 mapped) (- (proof-heap-base mapped) 128))
                  (< (proof-world-reg 19 mapped) *proof-space-size*))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-checked-budget-branches-with-heap-and-saves (before budget) (cut mapped)))
           :in-theory (e/d (allocation-large-budget-inputs-p allocation-large-map-entry-p)
                           (allocation-path-ready-p allocation-path-end allocation-large-budget-path
                            allocation-large-collect-p allocation-code-origin-p allocation-code-address
                            allocation-large-string-address allocation-large-mapping-size proof-segment-p
                            proof-heap-p proof-preserved-heap-p proof-heap-base proof-runtime-word
                            allocation-runtime-word-as-load)))))

(local
 (defthm allocation-large-layout-is-running
   (implies (proof-heap-layout-p world)
            (not (proof-world-stop world)))
   :rule-classes :forward-chaining
   :hints (("Goal" :in-theory (disable proof-align-up proof-regions-p proof-covered-p proof-disjoint-p mod)))))

(local
 (defthm allocation-layout-has-ordinary-machine-state
   (implies (proof-heap-layout-p world)
            (allocation-machine-state-p world))
   :rule-classes :forward-chaining
   :hints (("Goal"
            :use ((:instance allocation-growth-layout-facts (before world)))
            :in-theory (e/d (allocation-machine-state-p proof-world-reg proof-reg boymoo-model::a64-read-reg)
                            (proof-heap-layout-p proof-world-machine boymoo-model::a64-unsigned))))))

(defthm allocation-large-collector-restores-map-entry
  (let* ((sp (allocation-sp cut))
         (end (+ (- (proof-machine-limit cut) *proof-machine-margin*) *proof-machine-reservation*)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-large-caller-saves-p caller cut)
                  (proof-subspan-p sp 32 sp end)
                  (equal (proof-world-reg 30 cut) (allocation-code-address "rt:map-string" origin))
                  (equal (proof-world-reg 21 cut) (- (proof-heap-base cut) 128))
                  (proof-collector-return-p :header 0 cut before-map objects map-objects packages))
             (and (allocation-large-map-entry-p origin before-map)
                  (allocation-large-caller-saves-p caller before-map)
                  (proof-preserved-heap-p nil cut before-map objects map-objects packages)
                  (equal (proof-world-reg 20 before-map) (proof-world-reg 20 cut))
                  (equal (proof-world-reg 19 before-map) (proof-world-reg 19 cut))
                  (equal (proof-world-reg 21 before-map) (- (proof-heap-base before-map) 128)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-collector-return-keeps-map-arguments
                  (before cut) (after before-map) (old-objects objects) (new-objects map-objects))
                 (:instance allocation-large-collector-return-preserves-caller-saves
                  (before cut) (after before-map) (old-objects objects) (new-objects map-objects))
                 (:instance allocation-layout-of-heap (world before-map) (objects map-objects)))
           :in-theory (e/d (allocation-large-map-entry-p)
                           (allocation-code-origin-p allocation-code-address proof-heap-p proof-heap-layout-p
                            proof-prefix-preserved-p proof-dynamic-table-preserved-p proof-memory-span-agrees-p
                            proof-stack-prefix proof-reserved-span-p proof-subspan-p
                            proof-active-floor proof-inactive-floor proof-heap-base)))))

(local
 (defthm allocation-large-member-of-subset-is-member
   (implies (and (subsetp-equal subset superset) (member-equal item subset))
            (member-equal item superset))
   :hints (("Goal" :induct (subsetp-equal subset superset)))))

(local
 (defthm allocation-no-path-is-ready
   (allocation-path-ready-p nil cuts world)
   :hints (("Goal" :expand ((allocation-path-ready-p nil cuts world))))))

(local
 (defthm allocation-large-path-ready-with-fewer-cuts
   (implies (and (subsetp-equal smaller larger) (allocation-path-ready-p path larger world))
            (allocation-path-ready-p path smaller world))
   :rule-classes nil
   :hints (("Goal" :induct (allocation-path-ready-p path larger world)
            :expand ((:free (cuts) (allocation-path-ready-p path cuts world)))
            :in-theory (disable (:definition allocation-path-ready-p) proof-step proof-instruction-at-p
                                proof-instruction-access-p)))))

(local
 (defthm allocation-large-budget-and-collector-heap-frame
   (implies (and (proof-preserved-heap-p nil budget cut objects objects packages)
                 (proof-preserved-heap-p nil cut before-map objects map-objects packages)
                 (proof-register-frame-p 30 '(0 1 30) budget cut)
                 (equal (allocation-sp cut) (allocation-sp budget))
                 (proof-span-p (proof-heap-base budget) 8)
                 (allocation-memory-addresses-are-words-p (allocation-memory budget))
                 (allocation-memory-addresses-are-words-p (allocation-memory before-map)))
            (proof-preserved-heap-p nil budget before-map objects map-objects packages))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-register-frame-member
                   (before budget) (after cut) (register 23) (upper 30) (clobbers '(0 1 30)))
                  (:instance allocation-register-frame-member
                   (before budget) (after cut) (register 25) (upper 30) (clobbers '(0 1 30)))
                  (:instance allocation-heap-preservation-compose-at-same-stack-top
                   (before budget) (middle cut) (after before-map) (old-objects objects)
                   (middle-objects objects) (new-objects map-objects)))
            :in-theory (disable proof-register-frame-p proof-preserved-heap-p proof-span-p proof-heap-base
                                allocation-memory-addresses-are-words-p)))))

(local
 (defthm allocation-large-budget-cut-state
   (let* ((path (allocation-large-budget-path budget))
          (target (allocation-large-budget-target budget origin))
          (cuts (list (proof-world-reg 30 caller)))
          (collect (allocation-large-collect-p (proof-world-reg 1 budget) (proof-world-reg 20 budget)
                                              (proof-world-reg 2 budget))))
     (implies (and (allocation-large-budget-inputs-p origin budget)
                   (proof-heap-p budget objects packages)
                   (allocation-large-caller-saves-p caller budget)
                   (allocation-path-ready-p path (cons target cuts) budget)
                   (equal cut (allocation-path-end path budget)))
              (and (allocation-prefix-p (len path) cuts budget cut)
                   (proof-preserved-heap-p nil budget cut objects objects packages)
                   (allocation-large-caller-saves-p caller cut)
                   (proof-register-frame-p 30 '(0 1 30) budget cut)
                   (equal (allocation-sp cut) (allocation-sp budget))
                   (equal (proof-world-reg 19 cut) (proof-world-reg 19 budget))
                   (equal (proof-world-reg 20 cut) (allocation-large-mapping-size (proof-world-reg 19 cut)))
                   (equal (proof-world-reg 21 cut) (- (proof-heap-base cut) 128))
                   (< (proof-world-reg 19 cut) *proof-space-size*)
                   (allocation-code-origin-p origin)
                   (allocation-machine-state-p cut)
                   (not (proof-world-stop cut))
                   (equal (proof-world-pc cut) target)
                   (implies collect (equal (proof-world-reg 30 cut) (allocation-code-address "rt:map-string" origin))))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-large-path-ready-with-fewer-cuts
                   (world budget) (path (allocation-large-budget-path budget))
                   (smaller (list (proof-world-reg 30 caller)))
                   (larger (list (allocation-large-budget-target budget origin) (proof-world-reg 30 caller))))
                  (:instance allocation-large-path-ready-with-fewer-cuts
                   (world budget) (path (allocation-large-budget-path budget))
                   (smaller (list (allocation-large-budget-target budget origin)))
                   (larger (list (allocation-large-budget-target budget origin) (proof-world-reg 30 caller))))
                  (:instance allocation-large-budget-path-keeps-frame (before budget) (after cut))
                  (:instance allocation-large-checked-budget-branches-with-heap-and-saves (before budget))
                  (:instance allocation-prefix-from-path
                   (before budget) (path (allocation-large-budget-path budget)) (cuts (list (proof-world-reg 30 caller)))))
            :in-theory (e/d (allocation-large-budget-inputs-p)
                            (allocation-path-ready-p allocation-path-end allocation-prefix-p allocation-prefix-from-path
                             allocation-large-budget-path allocation-large-budget-target allocation-large-collect-p
                             allocation-code-origin-p allocation-code-address allocation-large-string-address
                             proof-segment-p proof-heap-p proof-preserved-heap-p proof-register-frame-p
                             proof-streams-preserved-p allocation-large-mapping-size proof-heap-base
                             proof-runtime-word allocation-runtime-word-as-load))))))

(defthm allocation-large-budget-executes-to-map-entry
  (let* ((collect (allocation-large-collect-p (proof-world-reg 1 budget)
                                             (proof-world-reg 20 budget)
                                             (proof-world-reg 2 budget)))
         (path (allocation-large-budget-path budget))
         (target (allocation-large-budget-target budget origin))
         (cuts (list (proof-world-reg 30 caller))))
    (implies (and (allocation-large-budget-inputs-p origin budget)
                  (proof-heap-p budget objects packages)
                  (allocation-large-caller-saves-p caller budget)
                  (proof-span-p (proof-heap-base budget) 8)
                  (allocation-memory-addresses-are-words-p (allocation-memory budget))
                  (allocation-memory-addresses-are-words-p (allocation-memory before-map))
                  (natp collector-steps)
                  (allocation-path-ready-p path (cons target cuts) budget)
                  (equal cut (allocation-path-end path budget))
                  (if collect
                      (and (proof-subspan-p (allocation-sp cut) 32 (allocation-sp cut)
                                            (+ (- (proof-machine-limit cut) *proof-machine-margin*) *proof-machine-reservation*))
                           (allocation-prefix-p collector-steps cuts cut before-map)
                           (proof-collector-return-p :header 0 cut before-map objects map-objects packages))
                    (and (equal collector-steps 0) (equal before-map cut) (equal map-objects objects))))
             (and (allocation-large-map-entry-p origin before-map)
                  (allocation-large-caller-saves-p caller before-map)
                  (proof-preserved-heap-p nil budget before-map objects map-objects packages)
                  (allocation-prefix-p (+ (len path) collector-steps) cuts budget before-map)
                  (equal (proof-world-reg 19 before-map) (proof-world-reg 19 budget))
                  (equal (proof-world-reg 20 before-map) (allocation-large-mapping-size (proof-world-reg 19 before-map)))
                  (equal (proof-world-reg 21 before-map) (- (proof-heap-base before-map) 128))
                  (< (proof-world-reg 19 before-map) *proof-space-size*))))
  :rule-classes nil
  :hints (("Goal"
           :cases ((allocation-large-collect-p (proof-world-reg 1 budget) (proof-world-reg 20 budget)
                                                (proof-world-reg 2 budget)))
           :use (allocation-large-budget-cut-state allocation-large-collector-restores-map-entry
                 allocation-large-budget-and-collector-heap-frame
                 (:instance allocation-prefix-after-prefix
                  (before budget) (middle cut) (after before-map) (first-steps (len (allocation-large-budget-path budget)))
                  (last-steps collector-steps) (cuts (list (proof-world-reg 30 caller)))))
           :in-theory (e/d (allocation-large-map-entry-p)
                           (allocation-large-collect-p allocation-path-ready-p allocation-path-end
                            allocation-prefix-p allocation-large-budget-path
                            allocation-code-origin-p allocation-code-address allocation-large-string-address
                            allocation-large-mapping-size proof-heap-p proof-preserved-heap-p proof-collector-return-p
                            proof-register-frame-p proof-span-p proof-subspan-p proof-heap-base proof-runtime-word
                            allocation-memory-addresses-are-words-p allocation-runtime-word-as-load)))))

(defund allocation-large-collector-route-p (caller budget cut before-map steps objects map-objects packages)
  (and (natp steps)
       (if (allocation-large-collect-p (proof-world-reg 1 budget) (proof-world-reg 20 budget)
                                       (proof-world-reg 2 budget))
           (and (allocation-prefix-p steps (list (proof-world-reg 30 caller)) cut before-map)
                (proof-collector-return-p :header 0 cut before-map objects map-objects packages))
         (and (equal steps 0) (equal before-map cut) (equal map-objects objects)))))

(defthm allocation-large-caller-save-room-at-cut
  (let* ((save (allocation-sp world))
         (floor (- (proof-machine-limit world) *proof-machine-margin*))
         (end (+ floor *proof-machine-reservation*)))
    (implies (and (allocation-large-save-room-p caller)
                  (allocation-large-caller-saves-p caller world))
             (and (proof-subspan-p save 32 floor end)
                  (proof-subspan-p save 32 save end))))
  :rule-classes nil
  :hints (("Goal"
           :in-theory (e/d (allocation-large-save-room-p allocation-large-caller-saves-p)
                           (proof-register-frame-p)))))

(local
 (defthm allocation-large-entry-path-executes-three-stages
   (implies (and (equal sized (allocation-path-end *allocation-large-size-path* caller))
                 (equal rounded (allocation-path-end *allocation-large-round-path* sized))
                 (equal budget (allocation-path-end *allocation-large-accounting-load-path* rounded)))
            (equal budget (allocation-path-end *allocation-large-entry-to-budget-path* caller)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-path-end-of-append
                   (first *allocation-large-size-path*)
                   (last (append *allocation-large-round-path* *allocation-large-accounting-load-path*))
                   (world caller))
                  (:instance allocation-path-end-of-append
                   (first *allocation-large-round-path*) (last *allocation-large-accounting-load-path*) (world sized)))
            :in-theory (disable allocation-path-end allocation-path-end-of-append)))))

(local
 (defthm allocation-large-entry-preserves-word-address-keys
   (implies (and (allocation-memory-addresses-are-words-p (allocation-memory caller))
                 (equal (allocation-memory budget)
                        (allocation-memory (allocation-write-words (allocation-large-save-writes caller) caller))))
            (allocation-memory-addresses-are-words-p (allocation-memory budget)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-word-writes-preserve-memory-keys
                   (before caller) (writes (allocation-large-save-writes caller))))
            :in-theory (disable allocation-memory-addresses-are-words-p allocation-write-words allocation-large-save-writes)))))

(local
 (defthm allocation-large-entry-budget-preserves-heap-base-span
   (implies (and (proof-preserved-heap-p nil caller budget objects objects packages)
                 (proof-span-p (proof-heap-base caller) 8))
            (and (proof-heap-p budget objects packages)
                 (proof-span-p (proof-heap-base budget) 8)))
   :rule-classes nil
   :hints (("Goal"
            :in-theory (disable proof-heap-p proof-span-p proof-heap-base proof-stack-base proof-stack-end
                                proof-spaces-end proof-memory-span-agrees-p proof-dynamic-table-preserved-p
                                proof-prefix-preserved-p proof-streams-preserved-p)))))

(defthm allocation-large-entry-executes-to-budget
  (let* ((entry *allocation-large-entry-to-budget-path*)
         (target (allocation-large-string-address origin 12))
         (cuts (list (proof-world-reg 30 caller))))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p caller)
                  (equal (proof-world-pc caller) (allocation-large-string-address origin 0))
                  (proof-heap-p caller objects packages)
                  (allocation-large-save-room-p caller)
                  (natp index) (equal (proof-stack-top caller) (+ (proof-stack-base caller) (* 8 index)))
                  (< (proof-world-reg 0 caller) *proof-space-size*)
                  (proof-span-p (proof-heap-base caller) 8)
                  (allocation-memory-addresses-are-words-p (allocation-memory caller))
                  (equal sized (allocation-path-end *allocation-large-size-path* caller))
                  (equal rounded (allocation-path-end *allocation-large-round-path* sized))
                  (equal budget (allocation-path-end *allocation-large-accounting-load-path* rounded))
                  (allocation-path-ready-p entry (cons target cuts) caller))
             (and (allocation-prefix-p (len entry) cuts caller budget)
                  (allocation-large-budget-inputs-p origin budget)
                  (allocation-large-caller-saves-p caller budget)
                  (proof-preserved-heap-p nil caller budget objects objects packages)
                  (proof-heap-p budget objects packages)
                  (proof-span-p (proof-heap-base budget) 8)
                  (allocation-memory-addresses-are-words-p (allocation-memory budget)))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-layout-of-heap (world caller))
                 (:instance allocation-growth-layout-facts (before caller))
                 allocation-large-entry-path-executes-three-stages allocation-large-entry-budget-preserves-heap-base-span
                 allocation-large-saves-within-unused-machine-stack allocation-large-constructor-prefix-controls
                 allocation-large-entry-preserves-word-address-keys allocation-large-checked-entry-preserves-heap-to-budget
                 (:instance allocation-large-path-ready-with-fewer-cuts
                  (path *allocation-large-entry-to-budget-path*) (world caller)
                  (smaller (list (proof-world-reg 30 caller)))
                  (larger (list (allocation-large-string-address origin 12) (proof-world-reg 30 caller))))
                 (:instance allocation-large-path-ready-with-fewer-cuts
                  (path *allocation-large-entry-to-budget-path*) (world caller)
                  (smaller (list (allocation-large-string-address origin 12)))
                  (larger (list (allocation-large-string-address origin 12) (proof-world-reg 30 caller))))
                 (:instance allocation-prefix-from-path
                  (path *allocation-large-entry-to-budget-path*) (before caller) (cuts (list (proof-world-reg 30 caller)))))
           :in-theory (e/d (allocation-large-budget-inputs-p)
                           (allocation-path-end allocation-path-ready-p allocation-prefix-p allocation-prefix-from-path
                            allocation-code-origin-p allocation-large-string-address allocation-large-mapping-size
                            proof-segment-p proof-heap-p proof-heap-layout-p proof-preserved-heap-p
                            proof-stack-base proof-stack-top proof-heap-base proof-span-p
                            allocation-large-save-writes allocation-write-words allocation-memory-addresses-are-words-p mod)))))

(local
 (defthm allocation-large-budget-route-keeps-word-address-keys
   (let* ((path (allocation-large-budget-path budget))
          (link (proof-world-reg 30 caller))
          (target (allocation-large-budget-target budget origin)))
     (implies (and (allocation-memory-addresses-are-words-p (allocation-memory budget))
                   (allocation-path-ready-p path (list target link) budget)
                   (equal cut (allocation-path-end path budget))
                   (allocation-large-collector-route-p caller budget cut before-map collector-steps
                                                       objects map-objects packages))
              (allocation-memory-addresses-are-words-p (allocation-memory before-map))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-checked-path-preserves-word-address-keys
                   (before budget) (path (allocation-large-budget-path budget))
                   (cuts (list (allocation-large-budget-target budget origin) (proof-world-reg 30 caller))))
                  (:instance allocation-executed-prefix-preserves-word-address-keys
                   (before cut) (after before-map) (steps collector-steps) (cuts (list (proof-world-reg 30 caller)))))
            :in-theory (e/d (allocation-large-collector-route-p)
                            (allocation-path-end allocation-path-ready-p allocation-prefix-p allocation-large-budget-path
                             allocation-large-budget-target allocation-large-collect-p proof-collector-return-p
                             allocation-memory-addresses-are-words-p))))))

(defthm allocation-large-checked-entry-to-map
  (let* ((entry *allocation-large-entry-to-budget-path*)
         (budget-path (allocation-large-budget-path budget))
         (budget-target (allocation-large-string-address origin 12))
         (dispatch-target (allocation-large-budget-target budget origin))
         (cuts (list (proof-world-reg 30 caller)))
         (prefix-steps (+ (len entry) (len budget-path) collector-steps)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p caller)
                  (equal (proof-world-pc caller) (allocation-large-string-address origin 0))
                  (proof-heap-p caller objects packages)
                  (allocation-large-save-room-p caller)
                  (natp index) (equal (proof-stack-top caller) (+ (proof-stack-base caller) (* 8 index)))
                  (< (proof-world-reg 0 caller) *proof-space-size*)
                  (proof-span-p (proof-heap-base caller) 8)
                  (allocation-memory-addresses-are-words-p (allocation-memory caller))
                  (equal sized (allocation-path-end *allocation-large-size-path* caller))
                  (equal rounded (allocation-path-end *allocation-large-round-path* sized))
                  (equal budget (allocation-path-end *allocation-large-accounting-load-path* rounded))
                  (allocation-path-ready-p entry (cons budget-target cuts) caller)
                  (equal cut (allocation-path-end budget-path budget))
                  (allocation-path-ready-p budget-path (cons dispatch-target cuts) budget)
                  (allocation-large-collector-route-p caller budget cut before-map collector-steps
                                                      objects map-objects packages))
             (and (allocation-prefix-p prefix-steps cuts caller before-map)
                  (allocation-large-map-entry-p origin before-map)
                  (allocation-large-caller-saves-p caller before-map)
                  (allocation-memory-addresses-are-words-p (allocation-memory before-map))
                  (proof-preserved-heap-p nil caller before-map objects map-objects packages)
                  (equal (proof-world-reg 20 before-map) (allocation-large-mapping-size (proof-world-reg 19 before-map)))
                  (equal (proof-world-reg 21 before-map) (- (proof-heap-base before-map) 128))
                  (< (proof-world-reg 19 before-map) *proof-space-size*))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-entry-executes-to-budget allocation-large-budget-executes-to-map-entry
                 allocation-large-budget-cut-state allocation-large-budget-route-keeps-word-address-keys
                 (:instance allocation-large-caller-save-room-at-cut (world cut))
                 (:instance allocation-prefix-after-prefix
                  (first-steps (len *allocation-large-entry-to-budget-path*))
                  (last-steps (+ (len (allocation-large-budget-path budget)) collector-steps))
                  (before caller) (middle budget) (after before-map) (cuts (list (proof-world-reg 30 caller))))
                 (:instance allocation-large-call-heap-after-suffix
                  (before budget) (after before-map) (old-objects objects) (new-objects map-objects)))
           :in-theory (e/d (allocation-large-collector-route-p)
                           (allocation-path-end allocation-path-ready-p allocation-prefix-p
                            allocation-large-budget-path allocation-large-collect-p allocation-large-budget-target
                            allocation-large-budget-inputs-p
                            allocation-large-mapping-size proof-heap-p proof-preserved-heap-p proof-collector-return-p
                            proof-register-frame-p proof-span-p proof-subspan-p proof-heap-base
                            proof-stack-base proof-stack-top proof-runtime-word allocation-runtime-word-as-load
                            allocation-memory-addresses-are-words-p)))))

(local
 (defthm allocation-large-map-preserved-data-keeps-external-head
   (implies (allocation-mapping-preserves-heap-data-p before after)
            (equal (proof-external-head after) (proof-external-head before)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (allocation-mapping-preserves-heap-data-p
                                   proof-external-head proof-runtime-word)
                                  (allocation-runtime-word-as-load allocation-same-memory-p
                                   allocation-equal-memory-is-model-equivalence))))))

(local
 (defthm allocation-large-map-preserved-data-keeps-external-total
   (let* ((head (proof-external-head before))
          (external (proof-external-objects head fuel before objects))
          (mapped (proof-external-objects (proof-external-head after) fuel after objects)))
     (implies (and (allocation-mapping-preserves-heap-data-p before after)
                   (equal (proof-world-regions after) (cons region (proof-world-regions before)))
                   external)
              (equal (proof-external-bytes (cdr mapped) (proof-world-machine after))
                     (proof-external-bytes (cdr external) (proof-world-machine before)))))
   :rule-classes nil
   :hints (("Goal"
            :use (allocation-large-map-preserved-data-keeps-external-head
                  (:instance allocation-external-list-with-appended-region
                   (head (proof-external-head before))))
            :in-theory (e/d (allocation-mapping-preserves-heap-data-p)
                            (allocation-same-memory-p allocation-equal-memory-is-model-equivalence
                             proof-external-objects proof-external-bytes
                             proof-external-head proof-runtime-word))))))

(local
 (defthm allocation-large-layout-provides-mapping-page-size
   (implies (proof-heap-layout-p world)
            (proof-page-size-p (proof-world-page-size world)))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-page-size-p proof-regions-p proof-align-up
                                      proof-covered-p proof-disjoint-p mod)))))

(local
 (defthm allocation-large-heap-has-external-list
   (implies (proof-heap-p world objects packages)
            (proof-external-objects (proof-external-head world) (len objects) world objects))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-heap-layout-p proof-static-p proof-object-map-p
                                      proof-external-objects proof-heap-object-spans-p proof-string-accounting-p
                                      proof-dynamic-view proof-dynamic-entries proof-dynamic-symbol-objects-p
                                      proof-stack-prefix)))))

(defthm allocation-large-mapped-total-fits-linux-range
  (let* ((reply (car (proof-world-replies before)))
         (size (proof-world-reg 20 before))
         (external (proof-external-objects (proof-external-head mapped) (len objects) mapped objects))
         (mapped-total (proof-external-bytes (cdr external) (proof-world-machine mapped))))
    (implies (and (allocation-large-map-entry-p origin before)
                  (proof-heap-p before objects packages)
                  (allocation-linux-writable-regions-p (proof-world-regions before))
                  (allocation-memory-in-readable-regions-p (allocation-memory before) (proof-world-regions before))
                  (consp (proof-world-replies before))
                  (posp size) (equal (mod size *proof-runtime-page*) 0)
                  (allocation-map-admissible-success-p reply size before)
                  (equal mapped (allocation-path-end *allocation-large-map-call* before)))
             (< (+ mapped-total size) (expt 2 63))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-map-path-effects (after mapped))
                 (:instance allocation-large-map-success-keeps-old-data (after mapped))
                 (:instance allocation-large-map-preserved-data-keeps-external-total
                  (after mapped) (fuel (len objects))
                  (region (proof-region (car (proof-world-replies before))
                                        (+ (car (proof-world-replies before)) (proof-world-reg 20 before)) :rw)))
                 (:instance allocation-adding-fresh-region-bounds-external-byte-total
                  (world before) (head (proof-external-head before)) (fuel (len objects))
                  (start (car (proof-world-replies before)))
                  (end (+ (car (proof-world-replies before)) (proof-world-reg 20 before))))
                 (:instance allocation-layout-of-heap (world before))
                 (:instance allocation-large-layout-provides-mapping-page-size (world before))
                 (:instance allocation-layout-storage-spans (world before))
                 (:instance allocation-large-heap-has-external-list (world before)))
           :in-theory (e/d (allocation-large-map-entry-p allocation-large-map-reply-p
                           proof-external-head proof-runtime-word)
                           (allocation-path-end proof-heap-p proof-heap-layout-p proof-page-size-p proof-regions-p
                            proof-region-disjoint-p proof-clear-memory proof-external-objects proof-external-bytes
                            allocation-mapping-preserves-heap-data-p allocation-runtime-word-as-load
                            allocation-large-map-call-result-p allocation-code-origin-p allocation-code-address
                            allocation-memory-in-readable-regions-p allocation-linux-writable-regions-p
                            proof-linux-errno-p mod)))))

(local
 (defthm allocation-large-preserved-heap-includes-result-heap
   (implies (proof-preserved-heap-p nil before after old-objects new-objects packages)
            (proof-heap-p after new-objects packages))
   :rule-classes nil
   :hints (("Goal" :in-theory (disable proof-heap-p proof-heap-frame-p
                                      proof-prefix-preserved-p proof-dynamic-table-preserved-p)))))

(local
 (defthm allocation-large-map-and-initializer-keep-word-address-keys
   (implies (and (allocation-memory-addresses-are-words-p (allocation-memory before-map))
                 (allocation-path-ready-p *allocation-large-map-call* cuts before-map)
                 (equal mapped (allocation-path-end *allocation-large-map-call* before-map))
                 (allocation-path-ready-p (allocation-large-postmap-path) cuts mapped)
                 (equal inserted (allocation-path-end *allocation-large-insertion-path* mapped))
                 (equal initialized (allocation-path-end *allocation-large-header-path* inserted))
                 (equal after (allocation-path-end *allocation-large-restore-path* initialized)))
            (allocation-memory-addresses-are-words-p (allocation-memory after)))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance allocation-checked-path-preserves-word-address-keys
                   (path *allocation-large-map-call*) (before before-map))
                  (:instance allocation-checked-path-preserves-word-address-keys
                   (path (allocation-large-postmap-path)) (before mapped))
                  (:instance allocation-path-end-of-append
                   (first *allocation-large-insertion-path*)
                   (last (append *allocation-large-header-path* *allocation-large-restore-path*)) (world mapped))
                  (:instance allocation-path-end-of-append
                   (first *allocation-large-header-path*) (last *allocation-large-restore-path*) (world inserted)))
            :in-theory (disable allocation-path-end allocation-path-ready-p allocation-path-end-of-append
                                allocation-memory-addresses-are-words-p)))))

(defthm allocation-large-constructor-checked-return-from-entry
  (let* ((entry *allocation-large-entry-to-budget-path*)
         (budget-path (allocation-large-budget-path budget))
         (budget-target (allocation-large-string-address origin 12))
         (dispatch-target (allocation-large-budget-target budget origin))
         (cuts (list (proof-world-reg 30 caller)))
         (prefix-steps (+ (len entry) (len budget-path) collector-steps))
         (reply (car (proof-world-replies before-map)))
         (size (proof-world-reg 20 before-map))
         (published (cons (proof-object (+ reply 24) :external :header 0) map-objects)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p caller)
                  (equal (proof-world-pc caller) (allocation-large-string-address origin 0))
                  (proof-heap-p caller objects packages)
                  (allocation-linux-writable-regions-p (proof-world-regions caller))
                  (allocation-large-save-room-p caller)
                  (natp index) (equal (proof-stack-top caller) (+ (proof-stack-base caller) (* 8 index)))
                  (< (proof-world-reg 0 caller) *proof-space-size*)
                  (proof-span-p (proof-heap-base caller) 8)
                  (allocation-memory-addresses-are-words-p (allocation-memory caller))
                  (equal sized (allocation-path-end *allocation-large-size-path* caller))
                  (equal rounded (allocation-path-end *allocation-large-round-path* sized))
                  (equal budget (allocation-path-end *allocation-large-accounting-load-path* rounded))
                  (allocation-path-ready-p entry (cons budget-target cuts) caller)
                  (equal cut (allocation-path-end budget-path budget))
                  (allocation-path-ready-p budget-path (cons dispatch-target cuts) budget)
                  (allocation-large-collector-route-p caller budget cut before-map collector-steps
                                                      objects map-objects packages)
                  (allocation-memory-in-readable-regions-p (allocation-memory before-map) (proof-world-regions before-map))
                  (consp (proof-world-replies before-map))
                  (allocation-map-admissible-success-p reply size before-map)
                  (allocation-path-ready-p *allocation-large-map-call* cuts before-map)
                  (equal mapped (allocation-path-end *allocation-large-map-call* before-map))
                  (allocation-path-ready-p (allocation-large-postmap-path) cuts mapped)
                  (equal inserted (allocation-path-end *allocation-large-insertion-path* mapped))
                  (equal initialized (allocation-path-end *allocation-large-header-path* inserted))
                  (equal after (allocation-path-end *allocation-large-restore-path* initialized)))
             (and (proof-segment-p (+ prefix-steps (len *allocation-large-map-call*) (len (allocation-large-postmap-path)))
                                   cuts caller :cut after)
                  (proof-string-constructor-return-p (proof-world-reg 0 caller) caller after objects published packages))))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-checked-entry-to-map
                 (:instance allocation-large-caller-save-room-at-cut (world before-map))
                 (:instance allocation-linux-writable-regions-preserved-by-prefix
                  (before caller) (after before-map) (cuts (list (proof-world-reg 30 caller)))
                  (steps (+ (len *allocation-large-entry-to-budget-path*)
                            (len (allocation-large-budget-path budget)) collector-steps)))
                 (:instance allocation-large-preserved-heap-includes-result-heap
                  (before caller) (after before-map) (old-objects objects) (new-objects map-objects))
                 (:instance allocation-large-rounded-size-is-mappable (length (proof-world-reg 19 before-map)))
                 (:instance allocation-large-mapped-total-fits-linux-range (before before-map) (objects map-objects))
                 (:instance allocation-large-map-and-initializer-keep-word-address-keys
                  (cuts (list (proof-world-reg 30 caller))))
                 (:instance allocation-large-constructor-checked-return-through-map
                  (before before-map) (old-objects objects) (objects map-objects)
                  (prefix-steps (+ (len *allocation-large-entry-to-budget-path*)
                                   (len (allocation-large-budget-path budget)) collector-steps))))
           :in-theory (e/d (allocation-large-collector-route-p)
                           (allocation-path-end allocation-path-ready-p allocation-prefix-p
                            allocation-large-budget-path allocation-large-collect-p allocation-large-budget-target
                            allocation-large-mapping-size allocation-large-postmap-path
                            allocation-large-map-entry-p proof-heap-p proof-preserved-heap-p proof-collector-return-p
                            proof-string-constructor-return-p proof-segment-p proof-span-p proof-subspan-p proof-heap-base
                            proof-stack-base proof-stack-top proof-external-objects proof-external-bytes proof-external-head
                            allocation-memory-addresses-are-words-p allocation-memory-in-readable-regions-p
                            allocation-linux-writable-regions-p allocation-map-admissible-success-p mod)))))

(local
 (defthm allocation-prefix-without-cuts
   (implies (allocation-prefix-p steps cuts before after)
            (allocation-prefix-p steps nil before after))
   :rule-classes nil
   :hints (("Goal" :induct (allocation-prefix-p steps cuts before after)
            :in-theory (disable proof-step)))))

(defthm allocation-large-constructor-checked-refusal-from-entry
  (let* ((entry *allocation-large-entry-to-budget-path*)
         (budget-path (allocation-large-budget-path budget))
         (budget-target (allocation-large-string-address origin 12))
         (dispatch-target (allocation-large-budget-target budget origin))
         (cuts (list (proof-world-reg 30 caller)))
         (prefix-steps (+ (len entry) (len budget-path) collector-steps))
         (stop (allocation-code-address (proof-resource-label :mapping) origin))
         (stop-cuts (list stop))
         (test (list *allocation-large-map-test*))
         (refusal-steps (+ (len (append *allocation-large-map-call* test)) stop-steps)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p caller)
                  (equal (proof-world-pc caller) (allocation-large-string-address origin 0))
                  (proof-heap-p caller objects packages)
                  (allocation-large-save-room-p caller)
                  (natp index) (equal (proof-stack-top caller) (+ (proof-stack-base caller) (* 8 index)))
                  (< (proof-world-reg 0 caller) *proof-space-size*)
                  (proof-span-p (proof-heap-base caller) 8)
                  (allocation-memory-addresses-are-words-p (allocation-memory caller))
                  (equal sized (allocation-path-end *allocation-large-size-path* caller))
                  (equal rounded (allocation-path-end *allocation-large-round-path* sized))
                  (equal budget (allocation-path-end *allocation-large-accounting-load-path* rounded))
                  (allocation-path-ready-p entry (cons budget-target cuts) caller)
                  (equal dispatch (allocation-path-end budget-path budget))
                  (allocation-path-ready-p budget-path (cons dispatch-target cuts) budget)
                  (allocation-large-collector-route-p caller budget dispatch before-map collector-steps
                                                      objects map-objects packages)
                  (consp (proof-world-replies before-map))
                  (proof-linux-errno-p (car (proof-world-replies before-map)))
                  (allocation-path-ready-p *allocation-large-map-call* stop-cuts before-map)
                  (equal returned (allocation-path-end *allocation-large-map-call* before-map))
                  (allocation-path-ready-p test stop-cuts returned)
                  (equal refused (allocation-path-end test returned))
                  (natp stop-steps)
                  (proof-segment-p stop-steps nil refused '(:exit . 3) after)
                  (null (proof-world-stdout after)))
             (and (equal (proof-world-pc refused) stop)
                  (proof-segment-p (+ prefix-steps refusal-steps) nil caller '(:exit . 3) after)
                  (proof-resource-observation-p after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-checked-entry-to-map (cut dispatch))
                 (:instance allocation-layout-of-heap (world before-map) (objects map-objects))
                 (:instance allocation-large-layout-provides-mapping-page-size (world before-map))
                 (:instance allocation-large-rounded-size-is-mappable (length (proof-world-reg 19 before-map)))
                 (:instance allocation-large-checked-map-refusal-exits (before before-map) (cut refused))
                 (:instance allocation-prefix-without-cuts (before caller) (after before-map)
                  (steps (+ (len *allocation-large-entry-to-budget-path*)
                            (len (allocation-large-budget-path budget)) collector-steps))
                  (cuts (list (proof-world-reg 30 caller))))
                 (:instance allocation-segment-after-prefix
                  (count (+ (len *allocation-large-entry-to-budget-path*)
                            (len (allocation-large-budget-path budget)) collector-steps))
                  (cuts nil) (before caller) (middle before-map) (reason '(:exit . 3))
                  (remaining (+ (len (append *allocation-large-map-call* (list *allocation-large-map-test*))) stop-steps))))
           :in-theory (e/d (allocation-large-collector-route-p proof-preserved-heap-p)
                           (allocation-path-end allocation-path-ready-p allocation-prefix-p
                            allocation-large-budget-path allocation-large-budget-target allocation-large-collect-p
                            allocation-large-map-entry-p allocation-large-mapping-size
                            allocation-memory-addresses-are-words-p proof-collector-return-p proof-heap-p
                            proof-heap-layout-p proof-heap-frame-p proof-prefix-preserved-p
                            proof-dynamic-table-preserved-p proof-linux-errno-p proof-page-size-p
                            proof-resource-observation-p proof-segment-p proof-span-p mod)))))
