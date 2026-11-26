(in-package "BOYMOO-PROOFS")

(include-book "large-caller")

(local (include-book "arithmetic/top" :dir :system))

(logic)
(set-verify-guards-eagerness 0)

(defconst *allocation-large-entry-to-budget-path*
  (append *allocation-large-size-path* *allocation-large-round-path* *allocation-large-accounting-load-path*))

(defun allocation-large-save-writes (caller)
  (let ((save (- (allocation-sp caller) 32)))
    (list (cons (+ 16 save) (proof-world-reg 19 caller))
          (cons (+ 24 save) (proof-world-reg 20 caller))
          (cons save (proof-world-reg 21 caller))
          (cons (+ 8 save) (proof-world-reg 30 caller)))))

(defthm allocation-large-save-prefix-footprint
  (implies (and (allocation-code-origin-p origin)
                (allocation-machine-state-p caller)
                (not (proof-world-stop caller))
                (equal (proof-world-pc caller) (allocation-large-string-address origin 0))
                (<= 32 (allocation-sp caller))
                (equal sized (allocation-path-end *allocation-large-size-path* caller)))
           (and (allocation-machine-state-p sized)
                (equal (allocation-memory sized)
                       (allocation-memory (allocation-write-words (allocation-large-save-writes caller) caller)))
                (equal (proof-world-regions sized) (proof-world-regions caller))
                (equal (proof-world-replies sized) (proof-world-replies caller))
                (proof-streams-preserved-p caller sized)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-word-register-range (register 0) (world caller)))
           :in-theory (e/d (unsigned-byte-p acl2::integer-range-p)
                           (allocation-word-register-range allocation-unsigned-64-of-sum
                            allocation-unsigned-64-of-difference)))))

(defthm allocation-large-size-cut-has-caller-saves
  (implies (and (allocation-code-origin-p origin)
                (allocation-machine-state-p caller)
                (not (proof-world-stop caller))
                (equal (proof-world-pc caller) (allocation-large-string-address origin 0))
                (<= 32 (allocation-sp caller))
                (equal sized (allocation-path-end *allocation-large-size-path* caller)))
           (allocation-large-caller-saves-p caller sized))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-size-prefix-saves-caller (before sized))
                 (:instance allocation-register-frame-member (register 23) (upper 30) (clobbers '(1 19))
                            (before caller) (after sized))
                 (:instance allocation-register-frame-member (register 25) (upper 30) (clobbers '(1 19))
                            (before caller) (after sized))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small '(1 19)) (before caller) (after sized)
                  (large (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*))))
           :in-theory (e/d (allocation-large-caller-saves-p)
                           (allocation-path-end proof-register-frame-p allocation-code-origin-p
                            allocation-large-string-address)))))

(defthm allocation-large-rounding-keeps-frame
  (implies (and (allocation-machine-state-p before)
                (equal after (allocation-path-end *allocation-large-round-path* before)))
           (and (allocation-machine-state-p after)
                (equal (allocation-sp after) (allocation-sp before))
                (equal (allocation-memory after) (allocation-memory before))
                (equal (proof-world-replies after) (proof-world-replies before))
                (equal (proof-world-regions after) (proof-world-regions before))
                (proof-streams-preserved-p before after)
                (proof-register-frame-p 30 '(1 20) before after)))
  :rule-classes nil)

(defthm allocation-large-accounting-load-keeps-frame
  (implies (and (allocation-machine-state-p before)
                (equal after (allocation-path-end *allocation-large-accounting-load-path* before)))
           (and (allocation-machine-state-p after)
                (equal (allocation-sp after) (allocation-sp before))
                (equal (allocation-memory after) (allocation-memory before))
                (equal (proof-world-replies after) (proof-world-replies before))
                (equal (proof-world-regions after) (proof-world-regions before))
                (proof-streams-preserved-p before after)
                (proof-register-frame-p 30 '(1 2 21) before after)))
  :rule-classes nil)

(local
 (defthm allocation-large-load-saved-word-with-unchanged-memory
   (implies (equal (allocation-memory before) (allocation-memory after))
            (equal (allocation-load-word address after) (allocation-load-word address before)))
   :rule-classes nil
   :hints (("Goal" :in-theory (e/d (allocation-load-word proof-load-word)
                                   (boymoo-model::a64-read-bytes))))))

(defthm allocation-large-call-saves-across-register-update
  (let* ((sp (allocation-sp before))
         (clobbers (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*)))
    (implies (and (allocation-large-caller-saves-p caller before)
                  (equal (allocation-sp after) sp)
                  (equal (allocation-memory after) (allocation-memory before))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (proof-register-frame-p 30 clobbers before after))
             (allocation-large-caller-saves-p caller after)))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-load-saved-word-with-unchanged-memory (address (allocation-sp before)))
                 (:instance allocation-large-load-saved-word-with-unchanged-memory (address (+ (allocation-sp before) 8)))
                 (:instance allocation-large-load-saved-word-with-unchanged-memory (address (+ (allocation-sp before) 16)))
                 (:instance allocation-large-load-saved-word-with-unchanged-memory (address (+ (allocation-sp before) 24)))
                 (:instance allocation-register-frame-member
                  (register 23) (upper 30)
                  (clobbers (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*)))
                 (:instance allocation-register-frame-member
                  (register 25) (upper 30)
                  (clobbers (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*)))
                 (:instance allocation-register-frame-transitive
                  (register 30) (before caller) (middle before)
                  (clobbers (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*))))
           :in-theory (e/d (allocation-large-caller-saves-p) (proof-register-frame-p)))))

(defthm allocation-large-round-and-load-budget
  (let ((length (proof-world-reg 19 before))
        (base (proof-heap-base before)))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p before)
                  (not (proof-world-stop before))
                  (equal (proof-world-pc before) (allocation-large-string-address origin 5))
                  (< length *proof-space-size*) (<= 128 base)
                  (equal rounded (allocation-path-end *allocation-large-round-path* before))
                  (equal after (allocation-path-end *allocation-large-accounting-load-path* rounded)))
             (and (allocation-machine-state-p after)
                  (not (proof-world-stop after))
                  (equal (proof-world-pc after) (allocation-large-string-address origin 12))
                  (equal (proof-world-reg 19 after) length)
                  (equal (proof-world-reg 20 after) (allocation-large-mapping-size length))
                  (equal (proof-world-reg 21 after) (- base 128))
                  (equal (proof-heap-base after) base)
                  (equal (proof-world-reg 1 after) (proof-string-bytes-since-collection before))
                  (equal (proof-world-reg 2 after) (proof-string-budget before))
                  (equal (allocation-sp after) (allocation-sp before))
                  (equal (allocation-memory after) (allocation-memory before))
                  (equal (proof-world-replies after) (proof-world-replies before))
                  (equal (proof-world-regions after) (proof-world-regions before))
                  (proof-streams-preserved-p before after)
                  (proof-register-frame-p 30 '(1 2 20 21) before after))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-rounding-machine-edge (cut rounded))
                 (:instance allocation-large-rounding-keeps-frame (after rounded))
                 (:instance allocation-large-load-accounting (before rounded) (cut after))
                 (:instance allocation-large-accounting-load-keeps-frame (before rounded))
                 (:instance allocation-register-frame-member
                  (register 28) (upper 30) (clobbers '(1 20)) (after rounded))
                 (:instance allocation-register-frame-member
                  (register 28) (upper 30) (clobbers '(1 2 21)) (before rounded))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small '(1 20)) (large '(1 2 20 21)) (after rounded))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small '(1 2 21)) (large '(1 2 20 21)) (before rounded))
                 (:instance allocation-register-frame-transitive
                  (register 30) (clobbers '(1 2 20 21)) (middle rounded))
                 (:instance allocation-large-load-saved-word-with-unchanged-memory
                  (address (+ -56 (proof-heap-base before))) (after rounded))
                 (:instance allocation-large-load-saved-word-with-unchanged-memory
                  (address (+ -48 (proof-heap-base before))) (after rounded)))
           :in-theory (disable allocation-path-end proof-register-frame-p allocation-code-origin-p
                               allocation-large-string-address allocation-large-mapping-size))))

(defthm allocation-large-checked-entry-to-budget
  (let* ((length (proof-world-reg 0 caller))
         (base (proof-heap-base caller))
         (path *allocation-large-entry-to-budget-path*)
         (cuts (list (allocation-large-string-address origin 12))))
    (implies (and (allocation-code-origin-p origin)
                  (allocation-machine-state-p caller)
                  (not (proof-world-stop caller))
                  (equal (proof-world-pc caller) (allocation-large-string-address origin 0))
                  (< length *proof-space-size*)
                  (<= 32 (allocation-sp caller)) (<= 128 base)
                  (equal sized (allocation-path-end *allocation-large-size-path* caller))
                  (equal rounded (allocation-path-end *allocation-large-round-path* sized))
                  (equal budget (allocation-path-end *allocation-large-accounting-load-path* rounded))
                  (allocation-path-ready-p path cuts caller))
             (and (proof-segment-p (len path) cuts caller :cut budget)
                  (allocation-large-caller-saves-p caller budget)
                  (allocation-machine-state-p budget)
                  (equal (proof-world-reg 19 budget) length)
                  (equal (proof-world-reg 20 budget) (allocation-large-mapping-size length))
                  (equal (proof-world-reg 21 budget) (- base 128))
                  (equal (proof-heap-base budget) base)
                  (equal (proof-world-reg 1 budget) (proof-string-bytes-since-collection sized))
                  (equal (proof-world-reg 2 budget) (proof-string-budget sized))
                  (equal (allocation-memory budget)
                         (allocation-memory (allocation-write-words (allocation-large-save-writes caller) caller))))))
  :rule-classes nil
  :hints (("Goal"
           :use ((:instance allocation-large-size-machine-edge (before caller) (cut sized))
                 (:instance allocation-large-size-prefix-saves-caller (before sized))
                 allocation-large-save-prefix-footprint allocation-large-size-cut-has-caller-saves
                 (:instance allocation-register-frame-member
                  (register 28) (upper 30) (clobbers '(1 19)) (before caller) (after sized))
                 (:instance allocation-large-round-and-load-budget (before sized) (after budget))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small '(1 2 20 21)) (before sized) (after budget)
                  (large (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*)))
                 (:instance allocation-large-call-saves-across-register-update (before sized) (after budget))
                 (:instance allocation-path-end-of-append
                  (first *allocation-large-size-path*)
                  (last (append *allocation-large-round-path* *allocation-large-accounting-load-path*))
                  (world caller))
                 (:instance allocation-path-end-of-append
                  (first *allocation-large-round-path*) (last *allocation-large-accounting-load-path*) (world sized))
                 (:instance allocation-checked-cut
                  (instructions *allocation-large-entry-to-budget-path*) (world caller) (after budget)
                  (cuts (list (allocation-large-string-address origin 12)))))
           :in-theory (disable allocation-path-end allocation-path-end-of-append allocation-path-ready-p
                               allocation-checked-cut proof-segment-p allocation-write-words allocation-large-save-writes
                               allocation-large-mapping-size proof-register-frame-p allocation-code-origin-p
                               allocation-large-string-address))))

(defthm allocation-large-budget-path-keeps-frame
  (implies (and (allocation-machine-state-p before)
                (equal after (allocation-path-end (allocation-large-budget-path before) before)))
           (and (allocation-machine-state-p after)
                (equal (allocation-sp after) (allocation-sp before))
                (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                (equal (proof-world-reg 20 after) (proof-world-reg 20 before))
                (equal (proof-world-reg 21 after) (proof-world-reg 21 before))
                (equal (proof-heap-base after) (proof-heap-base before))
                (equal (allocation-memory after) (allocation-memory before))
                (equal (proof-world-regions after) (proof-world-regions before))
                (equal (proof-world-replies after) (proof-world-replies before))
                (proof-streams-preserved-p before after)
                (proof-register-frame-p 30 '(0 1 30) before after)))
  :rule-classes nil
  :hints (("Goal" :in-theory (disable allocation-unsigned-64-of-sum allocation-unsigned-64-of-difference))))

(defthm allocation-large-budget-check-preserves-caller-saves
  (implies (and (allocation-large-caller-saves-p caller before)
                (allocation-machine-state-p before)
                (equal after (allocation-path-end (allocation-large-budget-path before) before)))
           (allocation-large-caller-saves-p caller after))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-budget-path-keeps-frame allocation-large-call-saves-across-register-update
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small '(0 1 30))
                  (large (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*))))
           :in-theory (disable allocation-path-end allocation-large-budget-path proof-register-frame-p))))

(defthm allocation-large-collector-return-preserves-caller-saves
  (let* ((sp (allocation-sp before))
         (end (+ (- (proof-machine-limit before) *proof-machine-margin*) *proof-machine-reservation*)))
    (implies (and (allocation-large-caller-saves-p caller before)
                  (proof-collector-return-p :header 0 before after old-objects new-objects packages)
                  (proof-subspan-p sp 32 sp end))
             (allocation-large-caller-saves-p caller after)))
  :rule-classes nil
  :hints (("Goal"
           :use (allocation-large-collector-return-keeps-map-arguments
                 (:instance allocation-large-collector-keeps-save-record (offset 0))
                 (:instance allocation-large-collector-keeps-save-record (offset 8))
                 (:instance allocation-large-collector-keeps-save-record (offset 16))
                 (:instance allocation-large-collector-keeps-save-record (offset 24))
                 (:instance allocation-register-frame-member
                  (register 23) (upper 30) (clobbers *allocation-large-constructor-clobbers*))
                 (:instance allocation-register-frame-member
                  (register 25) (upper 30) (clobbers *allocation-large-constructor-clobbers*))
                 (:instance allocation-register-frame-under-more-clobbers
                  (register 30) (small *allocation-large-constructor-clobbers*)
                  (large (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*)))
                 (:instance allocation-register-frame-transitive
                  (register 30) (before caller) (middle before)
                  (clobbers (append *allocation-large-saved-registers* *allocation-large-constructor-clobbers*))))
           :in-theory (e/d (allocation-large-caller-saves-p)
                           (proof-heap-p proof-preserved-heap-p proof-reserved-span-p proof-register-frame-p
                            proof-active-floor proof-inactive-floor proof-subspan-p)))))
