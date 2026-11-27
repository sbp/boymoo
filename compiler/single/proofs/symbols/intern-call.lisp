(in-package "BOYMOO-PROOFS")

(include-book "lookup")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                    (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg proof-heap-base
                     proof-advance proof-register-frame-p proof-runtime-pre-p
                     boymoo-model::a64-unsigned boymoo-model::a64-sp
                     symbols-runtime-offset symbols-path-ready-p symbols-intern-saved-world
                     symbols-stack-word symbols-load-register-word symbols-symbol-view-result
                     symbols-intern-designator-target symbols-intern-name-target)))

(defconst *symbols-intern-call-clobbers* (append *proof-volatile-registers* '(24 26 27)))
(defconst *symbols-intern-temporary-clobbers*
  (append *symbols-intern-call-clobbers* '(19 20 21 22 29 30)))

(defun symbols-intern-save-writes (before)
  (let ((sp (boymoo-model::a64-sp (proof-world-machine before))))
    (list (cons (- sp 16) (proof-world-reg 19 before))
          (cons (- sp 8) (proof-world-reg 20 before))
          (cons (- sp 32) (proof-world-reg 21 before))
          (cons (- sp 24) (proof-world-reg 22 before))
          (cons (- sp 48) (proof-world-reg 29 before))
          (cons (- sp 40) (proof-world-reg 30 before)))))

(local
 (defthm symbols-intern-saves-are-word-writes
   (equal (symbols-write-words (symbols-intern-save-writes before) before)
          (symbols-intern-saved-world before))
   :hints (("Goal" :in-theory (e/d (symbols-intern-saved-world proof-world-machine)
                                   (boymoo-model::a64-store update-nth))))))

(local
 (defthm symbols-intern-saves-keep-registers
   (equal (proof-world-reg register (symbols-intern-saved-world before))
          (proof-world-reg register before))
   :hints (("Goal" :use ((:instance symbols-write-words-preserve-registers-and-mappings
                                    (writes (symbols-intern-save-writes before))))
                   :in-theory (disable symbols-intern-save-writes symbols-write-words
                                       symbols-write-words-preserve-registers-and-mappings)))))

(defun symbols-intern-saved-frame-p (before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (- (boymoo-model::a64-sp (proof-world-machine before)) 48))
       (proof-register-frame-p 30 *symbols-intern-temporary-clobbers* before after)
       (symbols-no-memory-or-kernel-change-p (symbols-intern-saved-world before) after)))

(local
 (defthm symbols-intern-saved-frame-survives-read-only-path
   (implies (and (symbols-intern-saved-frame-p before middle)
                 (not (proof-world-stop after))
                 (not (eq (car (proof-world-machine after)) :svc))
                 (equal (boymoo-model::a64-sp (proof-world-machine after))
                        (boymoo-model::a64-sp (proof-world-machine middle)))
                 (proof-register-frame-p 30 clobbers middle after)
                 (subsetp-equal clobbers *symbols-intern-temporary-clobbers*)
                 (symbols-no-memory-or-kernel-change-p middle after))
            (symbols-intern-saved-frame-p before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers
                             (highest 30) (before middle) (allowed *symbols-intern-temporary-clobbers*))
                  (:instance symbols-frame-is-transitive
                             (highest 30) (clobbers *symbols-intern-temporary-clobbers*)
                             (first before) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-intern-saved-world before)) (last after)))))
   :rule-classes nil))

(local
 (defthm symbols-intern-setup-establishes-saved-frame
   (implies (symbols-intern-setup-frame-p base before setup)
            (symbols-intern-saved-frame-p before setup))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(0 19 30))
                             (allowed *symbols-intern-temporary-clobbers*) (after setup)))
            :in-theory (disable symbols-no-memory-or-kernel-change-p proof-world-stop)))
   :rule-classes nil))

(defthm symbols-intern-front-preserves-saved-frame
  (implies (symbols-intern-front-frames-p base before setup designator call view after)
           (symbols-intern-saved-frame-p before after))
  :hints (("Goal"
           :use ((:instance symbols-intern-setup-establishes-saved-frame)
                 (:instance symbols-intern-saved-frame-survives-read-only-path
                            (clobbers '(1 2)) (middle setup) (after designator))
                 (:instance symbols-intern-saved-frame-survives-read-only-path
                            (clobbers '(0 20 30)) (middle designator) (after call))
                 (:instance symbols-intern-saved-frame-survives-read-only-path
                            (clobbers '(1 2 3)) (middle call) (after view))
                 (:instance symbols-intern-saved-frame-survives-read-only-path
                            (clobbers '(3 4 8 21)) (middle view)))
           :in-theory (disable symbols-string-hit-p symbols-string-header-word symbols-string-payload
                               symbols-intern-saved-frame-p symbols-no-memory-or-kernel-change-p
                               proof-world-stop symbols-logical-right-shift-bits)))
  :rule-classes nil)

; The data bounds keep zero available as the failed view result.
(defun symbols-intern-saved-input-p (name designator before objects packages)
  (let* ((saved (symbols-intern-saved-world before))
         (base (proof-heap-base before))
         (name-address (proof-pointer-address (proof-world-reg 0 before) base))
         (package-address (proof-pointer-address (proof-world-reg 1 before) base)))
    (and (proof-reg-value-p 0 name saved objects packages)
         (proof-reg-value-p 1 designator saved objects packages)
         (implies (symbolp designator) (not (equal package-address 0)))
         (implies (stringp name) (< (+ name-address 8) (expt 2 64))))))

(local
 (defthm symbols-intern-designator-view-has-source-type
   (implies (and (symbols-intern-saved-input-p name designator before objects packages)
                 (symbols-intern-setup-frame-p base before setup)
                 (equal (proof-world-reg 1 view) (symbols-symbol-view-result setup)))
            (and (iff (equal (proof-world-reg 1 view) 0) (not (symbolp designator)))
                 (implies (symbolp designator)
                          (equal (proof-world-reg 1 view)
                                 (proof-pointer-address (proof-world-reg 1 before) (proof-heap-base before))))))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers '(0 19 30)) (after setup))
                  (:instance symbols-view-depends-on-memory
                             (word (proof-world-reg 1 before)) (base (proof-heap-base before))
                             (first (proof-world-machine (symbols-intern-saved-world before)))
                             (last (proof-world-machine setup)))
                  (:instance symbols-symbol-view-agrees-with-value (datum designator) (world setup)))
            :in-theory (e/d (proof-heap-base symbols-no-memory-or-kernel-change-p)
                            (proof-view proof-pointer-address
                             symbols-symbol-view-agrees-with-value))))
   :rule-classes nil))

(local
 (defthm symbols-intern-front-string-call-reloads-name
   (implies (and (symbols-intern-saved-input-p name designator before objects packages)
                 (symbols-intern-front-frames-p base before setup designator-view call string-view after)
                 (not (equal (proof-world-reg 1 designator-view) 0)))
            (and (proof-reg-value-p 0 name call objects packages)
                 (implies (stringp name)
                          (< (+ 8 (proof-pointer-address (proof-world-reg 0 call) (proof-heap-base call)))
                             (expt 2 64)))))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers '(0 19 30)) (after setup))
                  (:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers '(1 2)) (before setup) (after designator-view))
                  (:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers '(0 20 30)) (before designator-view) (after call))
                  (:instance symbols-frame-gives-register (highest 30) (register 19)
                             (clobbers '(1 2)) (before setup) (after designator-view))
                  (:instance symbols-view-depends-on-memory
                             (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                             (first (proof-world-machine (symbols-intern-saved-world before)))
                             (last (proof-world-machine call))))
            :in-theory (e/d (proof-heap-base symbols-no-memory-or-kernel-change-p)
                            (proof-view proof-pointer-address symbols-symbol-view-agrees-with-value
                             symbols-string-view-frame-p symbols-intern-name-frame-p symbols-load-register-word))))
   :rule-classes nil))

(defun symbols-intern-default-p (name designator)
  (or (not (stringp name)) (not (symbolp designator))))

(defthm symbols-intern-front-selects-argument-path
  (implies (and (symbols-intern-saved-input-p name designator before objects packages)
                (symbols-intern-front-frames-p base before setup designator-view call string-view after))
           (equal (proof-world-pc after)
                  (symbols-runtime-address (if (symbols-intern-default-p name designator)
                                               "rt:intern-nil" "rt:intern-hash") base)))
  :hints (("Goal"
           :use ((:instance symbols-intern-designator-view-has-source-type (view designator-view))
                 (:instance symbols-intern-front-string-call-reloads-name)
                 (:instance symbols-string-view-agrees-with-value (datum name) (before call) (after string-view)))
           :in-theory (e/d (symbols-intern-designator-target symbols-intern-name-target)
                           (symbols-intern-saved-input-p symbols-string-view-frame-p
                            symbols-intern-setup-frame-p proof-value-p proof-reg-value-p
                            proof-load-word proof-pointer-address proof-string-bytes proof-byte-list))))
  :rule-classes nil)

(local
 (defthm symbols-intern-designator-view-is-nonzero
   (implies (and (symbols-intern-saved-input-p name designator before objects packages)
                 (symbolp designator))
            (not (equal (proof-pointer-address (proof-world-reg 1 before) (proof-heap-base before)) 0)))
   :hints (("Goal" :in-theory (disable proof-reg-value-p proof-pointer-address)))
   :rule-classes nil))

(defthm symbols-intern-accepted-name-feeds-hash
  (implies (and (symbols-runtime-base-p base) (stringp name) (symbolp designator)
                (symbols-intern-saved-input-p name designator before objects packages)
                (symbols-intern-front-frames-p base before setup designator-view call string-view after))
           (and (symbols-hash-input-p (coerce name 'list) base after)
                (equal (proof-world-reg 3 after) 0)))
  :hints (("Goal"
           :use ((:instance symbols-intern-designator-view-has-source-type (view designator-view))
                 (:instance symbols-intern-designator-view-is-nonzero)
                 (:instance symbols-intern-front-string-call-reloads-name)
                 (:instance symbols-string-view-agrees-with-value (datum name) (before call) (after string-view))
                 (:instance symbols-byte-list-depends-on-memory
                            (size (len (coerce name 'list)))
                            (address (proof-world-reg 1 string-view))
                            (first (proof-world-machine call)) (last (proof-world-machine after))))
           :in-theory (e/d (symbols-intern-name-target symbols-no-memory-or-kernel-change-p)
                           (symbols-intern-saved-input-p symbols-intern-setup-frame-p
                            symbols-intern-designator-frame-p symbols-intern-designator-target
                            proof-value-p proof-reg-value-p proof-load-word proof-pointer-address
                            proof-string-bytes proof-byte-list symbols-string-payload
                            symbols-string-hit-p symbols-string-header-word symbols-logical-right-shift-bits
                            proof-header-size ash floor))))
  :rule-classes nil)

(local
 (defthm symbols-intern-call-stack-pointer-fits
   (< (boymoo-model::a64-sp machine) (expt 2 64))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :linear))

(local
 (defthm symbols-intern-call-stack-pointer-is-natural
   (natp (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-intern-call-register-fits
   (equal (boymoo-model::a64-unsigned 64 (proof-world-reg register world))
          (proof-world-reg register world))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))))

(local
 (defthm symbols-intern-saved-words
   (let ((sp (boymoo-model::a64-sp (proof-world-machine before)))
         (saved (symbols-intern-saved-world before)))
     (implies (<= 48 sp)
              (and (equal (symbols-load-register-word (- sp 48) saved) (proof-world-reg 29 before))
                   (equal (symbols-load-register-word (- sp 40) saved) (proof-world-reg 30 before))
                   (equal (symbols-load-register-word (- sp 32) saved) (proof-world-reg 21 before))
                   (equal (symbols-load-register-word (- sp 24) saved) (proof-world-reg 22 before))
                   (equal (symbols-load-register-word (- sp 16) saved) (proof-world-reg 19 before))
                   (equal (symbols-load-register-word (- sp 8) saved) (proof-world-reg 20 before)))))
   :hints (("Goal"
            :in-theory (e/d (symbols-intern-saved-world symbols-load-register-word)
                            (proof-load-word boymoo-model::a64-store update-nth))))))

(local
 (defthm symbols-intern-read-of-same-memory
   (implies (equal (symbols-machine-memory first) (symbols-machine-memory last))
            (equal (symbols-load-register-word address first)
                   (symbols-load-register-word address last)))
   :hints (("Goal" :in-theory (enable symbols-load-register-word boymoo-model::a64-load)))
   :rule-classes nil))

(defthm symbols-intern-saved-frame-has-caller-words
  (implies (and (<= 48 (boymoo-model::a64-sp (proof-world-machine before)))
                (symbols-intern-saved-frame-p before middle))
           (and (equal (symbols-stack-word 0 middle) (proof-world-reg 29 before))
                (equal (symbols-stack-word 8 middle) (proof-world-reg 30 before))
                (equal (symbols-stack-word 16 middle) (proof-world-reg 21 before))
                (equal (symbols-stack-word 24 middle) (proof-world-reg 22 before))
                (equal (symbols-stack-word 32 middle) (proof-world-reg 19 before))
                (equal (symbols-stack-word 40 middle) (proof-world-reg 20 before))))
  :hints (("Goal"
           :use ((:instance symbols-intern-saved-words)
                  (:instance symbols-intern-read-of-same-memory
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 48))
                             (first (symbols-intern-saved-world before)) (last middle))
                  (:instance symbols-intern-read-of-same-memory
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 40))
                             (first (symbols-intern-saved-world before)) (last middle))
                  (:instance symbols-intern-read-of-same-memory
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                             (first (symbols-intern-saved-world before)) (last middle))
                  (:instance symbols-intern-read-of-same-memory
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 24))
                             (first (symbols-intern-saved-world before)) (last middle))
                  (:instance symbols-intern-read-of-same-memory
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                             (first (symbols-intern-saved-world before)) (last middle))
                  (:instance symbols-intern-read-of-same-memory
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 8))
                             (first (symbols-intern-saved-world before)) (last middle)))
           :in-theory (e/d (symbols-stack-word symbols-no-memory-or-kernel-change-p)
                           (symbols-intern-saved-words))))
  :rule-classes nil)

(defun symbols-intern-caller-save-slots-p (before middle)
  (and (equal (boymoo-model::a64-sp (proof-world-machine middle))
              (- (boymoo-model::a64-sp (proof-world-machine before)) 48))
       (equal (symbols-stack-word 0 middle) (proof-world-reg 29 before))
       (equal (symbols-stack-word 8 middle) (proof-world-reg 30 before))
       (equal (symbols-stack-word 16 middle) (proof-world-reg 21 before))
       (equal (symbols-stack-word 24 middle) (proof-world-reg 22 before))
       (equal (symbols-stack-word 32 middle) (proof-world-reg 19 before))
       (equal (symbols-stack-word 40 middle) (proof-world-reg 20 before))))

(local
 (defthm symbols-intern-span-agrees-on-register-word
   (implies (and (proof-memory-span-agrees-p start end before after)
                 (natp address) (<= start address)
                 (<= (+ address 8) end) (<= end (expt 2 64)))
            (equal (symbols-load-register-word address before)
                   (symbols-load-register-word address after)))
   :hints (("Goal"
            :use ((:instance symbols-agreeing-memory-span-gives-word))
            :in-theory (enable symbols-load-register-word)))
   :rule-classes nil))

(defthm symbols-intern-caller-save-slots-survive-writes
  (let ((sp (boymoo-model::a64-sp (proof-world-machine before))))
    (implies (and (<= 48 sp)
                  (equal (boymoo-model::a64-sp (proof-world-machine middle)) (- sp 48))
                  (proof-memory-span-agrees-p (- sp 48) sp (symbols-intern-saved-world before) middle))
             (symbols-intern-caller-save-slots-p before middle)))
  :hints (("Goal"
           :use ((:instance symbols-intern-saved-words)
                 (:instance symbols-intern-span-agrees-on-register-word
                            (start (- (boymoo-model::a64-sp (proof-world-machine before)) 48))
                            (end (boymoo-model::a64-sp (proof-world-machine before)))
                            (address (- (boymoo-model::a64-sp (proof-world-machine before)) 48))
                            (before (symbols-intern-saved-world before)) (after middle))
                 (:instance symbols-intern-span-agrees-on-register-word
                            (start (- (boymoo-model::a64-sp (proof-world-machine before)) 48))
                            (end (boymoo-model::a64-sp (proof-world-machine before)))
                            (address (- (boymoo-model::a64-sp (proof-world-machine before)) 40))
                            (before (symbols-intern-saved-world before)) (after middle))
                 (:instance symbols-intern-span-agrees-on-register-word
                            (start (- (boymoo-model::a64-sp (proof-world-machine before)) 48))
                            (end (boymoo-model::a64-sp (proof-world-machine before)))
                            (address (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
                            (before (symbols-intern-saved-world before)) (after middle))
                 (:instance symbols-intern-span-agrees-on-register-word
                            (start (- (boymoo-model::a64-sp (proof-world-machine before)) 48))
                            (end (boymoo-model::a64-sp (proof-world-machine before)))
                            (address (- (boymoo-model::a64-sp (proof-world-machine before)) 24))
                            (before (symbols-intern-saved-world before)) (after middle))
                 (:instance symbols-intern-span-agrees-on-register-word
                            (start (- (boymoo-model::a64-sp (proof-world-machine before)) 48))
                            (end (boymoo-model::a64-sp (proof-world-machine before)))
                            (address (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
                            (before (symbols-intern-saved-world before)) (after middle))
                 (:instance symbols-intern-span-agrees-on-register-word
                            (start (- (boymoo-model::a64-sp (proof-world-machine before)) 48))
                            (end (boymoo-model::a64-sp (proof-world-machine before)))
                            (address (- (boymoo-model::a64-sp (proof-world-machine before)) 8))
                            (before (symbols-intern-saved-world before)) (after middle)))
           :in-theory (e/d (symbols-stack-word)
                           (proof-memory-span-agrees-p symbols-intern-saved-words))))
  :rule-classes nil)

(defthm symbols-intern-restore-caller-registers
  (implies (and (not (proof-world-stop before))
                (symbols-intern-caller-save-slots-p before middle)
                (proof-register-frame-p 30 *symbols-intern-temporary-clobbers* before middle)
                (symbols-intern-restore-frame-p result middle after))
           (and (proof-frame-return-p *symbols-intern-call-clobbers* t before after)
                (equal (proof-world-reg 0 after) result)))
  :hints (("Goal"
           :use ((:instance symbols-frame-allows-more-clobbers
                            (highest 30) (clobbers '(0 19 20 21 22 29 30)) (before middle)
                            (allowed *symbols-intern-temporary-clobbers*))
                 (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-intern-temporary-clobbers*)
                            (first before) (last after))
                 (:instance symbols-frame-keeps-restored-register (highest 30) (register 19)
                            (clobbers *symbols-intern-temporary-clobbers*))
                 (:instance symbols-frame-keeps-restored-register (highest 30) (register 20)
                            (clobbers (append *symbols-intern-call-clobbers* '(20 21 22 29 30))))
                 (:instance symbols-frame-keeps-restored-register (highest 30) (register 21)
                            (clobbers (append *symbols-intern-call-clobbers* '(21 22 29 30))))
                 (:instance symbols-frame-keeps-restored-register (highest 30) (register 22)
                            (clobbers (append *symbols-intern-call-clobbers* '(22 29 30))))
                 (:instance symbols-frame-keeps-restored-register (highest 30) (register 29)
                            (clobbers (append *symbols-intern-call-clobbers* '(29 30))))
                 (:instance symbols-frame-keeps-restored-register (highest 30) (register 30)
                            (clobbers (append *symbols-intern-call-clobbers* '(30)))))
           :in-theory (disable symbols-no-memory-or-kernel-change-p)))
  :rule-classes nil)

(defthm symbols-intern-restore-returns-to-caller
  (implies (and (not (proof-world-stop before))
                (<= 48 (boymoo-model::a64-sp (proof-world-machine before)))
                (symbols-intern-saved-frame-p before middle)
                (symbols-intern-restore-frame-p result middle after))
           (and (proof-frame-return-p *symbols-intern-call-clobbers* t before after)
                (equal (proof-world-reg 0 after) result)
                (symbols-no-memory-or-kernel-change-p (symbols-intern-saved-world before) after)))
  :hints (("Goal"
           :use ((:instance symbols-intern-saved-frame-has-caller-words)
                 (:instance symbols-intern-restore-caller-registers)
                 (:instance symbols-memory-and-kernel-frame-is-transitive
                            (first (symbols-intern-saved-world before)) (last after)))
           :in-theory (disable proof-frame-return-p symbols-no-memory-or-kernel-change-p)))
  :rule-classes nil)

(defun symbols-intern-rejection-finish (before)
  (proof-advance (len *symbols-intern-reject-path*) (symbols-intern-front-state before)))

(local
 (defthm symbols-intern-saved-frame-can-pop
   (implies (symbols-intern-saved-frame-p before after)
            (< (+ 48 (boymoo-model::a64-sp (proof-world-machine after))) (expt 2 64)))
   :hints (("Goal" :in-theory (disable symbols-no-memory-or-kernel-change-p)))))

(defthm symbols-run-intern-default
  (let ((front (symbols-intern-front-state before))
        (after (symbols-intern-rejection-finish before)))
    (implies (and (symbols-intern-at-p 0 code-base before)
                  (<= 48 (boymoo-model::a64-sp (proof-world-machine before)))
                  (symbols-intern-front-ready-p code-base before)
                  (symbols-intern-saved-input-p name designator before objects packages)
                  (symbols-intern-default-p name designator)
                  (symbols-path-ready-p *symbols-intern-reject-path* code-base
                                        (proof-world-reg 30 before) front))
             (and (proof-frame-return-p *symbols-intern-call-clobbers* t before after)
                  (equal (proof-world-reg 0 after) *proof-nil*)
                  (symbols-no-memory-or-kernel-change-p (symbols-intern-saved-world before) after))))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-front)
                 (:instance symbols-intern-front-preserves-saved-frame (base code-base)
                            (setup (symbols-intern-setup-state before))
                            (designator (symbols-intern-designator-view before))
                            (call (symbols-intern-name-call before))
                            (view (symbols-intern-name-view before)) (after (symbols-intern-front-state before)))
                 (:instance symbols-intern-front-selects-argument-path (base code-base)
                            (setup (symbols-intern-setup-state before))
                            (designator-view (symbols-intern-designator-view before))
                            (call (symbols-intern-name-call before))
                            (string-view (symbols-intern-name-view before)) (after (symbols-intern-front-state before)))
                 (:instance symbols-intern-saved-frame-has-caller-words (middle (symbols-intern-front-state before)))
                 (:instance symbols-run-intern-reject (before (symbols-intern-front-state before)))
                 (:instance symbols-intern-restore-returns-to-caller (middle (symbols-intern-front-state before))
                            (result *proof-nil*) (after (symbols-intern-rejection-finish before))))
           :in-theory (disable symbols-intern-front-frames-p symbols-intern-restore-frame-p
                               symbols-intern-setup-state symbols-intern-designator-view symbols-intern-name-call
                               symbols-intern-name-view symbols-intern-front-state symbols-intern-front-ready-p
                               symbols-intern-saved-input-p symbols-intern-default-p proof-segment-p
                               symbols-replay symbols-run-intern-reject
                               proof-frame-return-p symbols-no-memory-or-kernel-change-p)))
  :rule-classes nil)

(defun symbols-intern-saved-package-address (before)
  (+ 16 (proof-pointer-address (proof-world-reg 1 before) (proof-heap-base before))))

(defun symbols-intern-saved-package-word (before)
  (proof-load-word (symbols-intern-saved-package-address before)
                   (proof-world-machine (symbols-intern-saved-world before))))

(local
 (defthm symbols-intern-name-setup-keeps-package-word
   (implies (and (symbolp designator)
                 (symbols-intern-saved-input-p name designator before objects packages)
                 (symbols-intern-front-frames-p base before setup designator-view call string-view after))
            (equal (proof-world-reg 20 after) (symbols-intern-saved-package-word before)))
   :hints (("Goal"
            :use ((:instance symbols-intern-designator-view-has-source-type (view designator-view))
                  (:instance symbols-frame-gives-register (highest 30) (register 20)
                             (clobbers '(1 2 3)) (before call) (after string-view))
                  (:instance symbols-frame-gives-register (highest 30) (register 20) (clobbers '(3 4 8 21))
                             (before string-view))
                  (:instance symbols-intern-read-of-same-memory
                             (address (symbols-intern-saved-package-address before))
                             (first (symbols-intern-saved-world before)) (last designator-view)))
            :in-theory (e/d (symbols-load-register-word symbols-word-load-fits
                             symbols-no-memory-or-kernel-change-p)
                            (symbols-intern-saved-input-p symbols-string-hit-p symbols-string-header-word
                             symbols-logical-right-shift-bits symbols-string-payload proof-pointer-address
                             boymoo-model::a64-load))))
   :rule-classes nil))

(local
 (defthm symbols-intern-saved-package-word-gives-number
   (let ((number (proof-package-number (acl2::symbol-package-name designator) packages 0)))
     (implies (and (symbolp designator)
                   (proof-packages-p packages)
                   (symbols-intern-saved-input-p name designator before objects packages))
              (and (natp number) (< number (expt 2 62))
                   (equal (symbols-intern-saved-package-word before) (+ 1 (* 2 number))))))
   :hints (("Goal"
            :use ((:instance symbols-published-symbol-fields
                             (symbol designator) (word (proof-world-reg 1 before)) (base (proof-heap-base before))
                             (machine (proof-world-machine (symbols-intern-saved-world before))))
                  (:instance symbols-package-number-of-indexed-row
                             (first 0)
                             (number (proof-view-value
                                      (proof-view (symbols-intern-saved-package-word before) (proof-heap-base before)
                                                  objects packages
                                                  (proof-world-machine (symbols-intern-saved-world before))))))
                  (:instance symbols-canonical-immediate-integer-word
                             (word (symbols-intern-saved-package-word before)) (base (proof-heap-base before))
                             (machine (proof-world-machine (symbols-intern-saved-world before)))
                             (number (proof-view-value
                                      (proof-view (symbols-intern-saved-package-word before) (proof-heap-base before)
                                                  objects packages
                                                  (proof-world-machine (symbols-intern-saved-world before)))))))
            :in-theory (e/d (proof-heap-base)
                            (proof-package-number proof-packages-p proof-pointer-address
                             proof-value-p proof-view proof-load-word))))
   :rule-classes nil))

(defthm symbols-intern-accepted-package-feeds-hash
  (let ((number (proof-package-number (acl2::symbol-package-name designator) packages 0)))
    (implies (and (symbolp designator) (proof-packages-p packages)
                  (symbols-intern-saved-input-p name designator before objects packages)
                  (symbols-intern-front-frames-p base before setup designator-view call string-view after))
             (and (natp number) (< number (expt 2 62))
                  (equal (proof-world-reg 20 after) (+ 1 (* 2 number))))))
  :hints (("Goal"
           :use ((:instance symbols-intern-name-setup-keeps-package-word)
                 (:instance symbols-intern-saved-package-word-gives-number))
           :in-theory (disable symbols-intern-saved-package-word symbols-intern-saved-input-p
                               proof-package-number proof-packages-p symbols-intern-front-frames-p)))
  :rule-classes nil)

(defun symbols-intern-lookup-start (name before)
  (symbols-intern-static-entry name (symbols-intern-front-state before)))

(defun symbols-intern-lookup-ready-p (name static-count static-fuels dynamic-count dynamic-fuels base before)
  (and (symbols-intern-front-ready-p base before)
       (symbols-intern-static-entry-ready-p name base (symbols-intern-front-state before))
       (symbols-intern-probes-ready-p static-count static-fuels dynamic-count dynamic-fuels
                                     base (symbols-intern-lookup-start name before))))

(defun symbols-intern-lookup-state (name static-count static-fuels dynamic-count dynamic-fuels before)
  (symbols-intern-probes-finish static-count static-fuels dynamic-count dynamic-fuels
                               (symbols-intern-lookup-start name before)))

(defun symbols-intern-lookup-binding (name static-count static-fuels dynamic-count before)
  (symbols-intern-probes-binding static-count static-fuels dynamic-count
                                (symbols-intern-lookup-start name before)))

(local
 (defthm symbols-intern-hash-and-probes-keep-saves
   (implies (and (symbols-intern-saved-frame-p before front)
                 (symbols-intern-selected-static-frame-p number name base front selected)
                 (symbols-intern-probes-frame-p binding base selected after))
            (symbols-intern-saved-frame-p before after))
   :hints (("Goal"
            :use ((:instance symbols-intern-saved-frame-survives-read-only-path
                             (clobbers '(3 4 5 9 22)) (middle front) (after selected))
                  (:instance symbols-intern-saved-frame-survives-read-only-path
                             (clobbers *symbols-intern-scan-clobbers*) (middle selected)))
            :in-theory (disable symbols-intern-static-slot symbols-intern-hashed proof-symbol-hash
                                proof-integer-word symbols-no-memory-or-kernel-change-p
                                symbols-intern-saved-frame-p)))
   :rule-classes nil))

(defthm symbols-run-intern-lookup
  (let* ((after (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels before))
         (binding (symbols-intern-lookup-binding name static-count static-fuels dynamic-count before)))
    (implies (and (symbols-intern-at-p 0 code-base before)
                  (<= 48 (boymoo-model::a64-sp (proof-world-machine before)))
                  (stringp name) (symbolp designator) (proof-packages-p packages)
                  (symbols-intern-saved-input-p name designator before objects packages)
                  (symbols-intern-lookup-ready-p name static-count static-fuels dynamic-count dynamic-fuels
                                                 code-base before))
             (and (symbols-intern-saved-frame-p before after)
                  (equal (proof-world-pc after)
                         (symbols-runtime-address (if binding "rt:intern-return" "rt:intern-create") code-base))
                  (implies binding (equal (proof-world-reg 0 after) (cdr binding))))))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-front)
                 (:instance symbols-intern-front-preserves-saved-frame (base code-base)
                            (setup (symbols-intern-setup-state before)) (designator (symbols-intern-designator-view before))
                            (call (symbols-intern-name-call before)) (view (symbols-intern-name-view before))
                            (after (symbols-intern-front-state before)))
                 (:instance symbols-intern-accepted-name-feeds-hash (base code-base)
                            (setup (symbols-intern-setup-state before)) (designator-view (symbols-intern-designator-view before))
                            (call (symbols-intern-name-call before)) (string-view (symbols-intern-name-view before))
                            (after (symbols-intern-front-state before)))
                 (:instance symbols-intern-accepted-package-feeds-hash (base code-base)
                            (setup (symbols-intern-setup-state before)) (designator-view (symbols-intern-designator-view before))
                            (call (symbols-intern-name-call before)) (string-view (symbols-intern-name-view before))
                            (after (symbols-intern-front-state before)))
                 (:instance symbols-run-intern-select-static-bucket
                            (number (proof-package-number (acl2::symbol-package-name designator) packages 0))
                            (before (symbols-intern-front-state before)))
                 (:instance symbols-run-intern-probes (before (symbols-intern-lookup-start name before)))
                 (:instance symbols-intern-hash-and-probes-keep-saves (base code-base)
                            (number (proof-package-number (acl2::symbol-package-name designator) packages 0))
                            (front (symbols-intern-front-state before)) (selected (symbols-intern-lookup-start name before))
                            (binding (symbols-intern-lookup-binding name static-count static-fuels dynamic-count before))
                            (after (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels before))))
           :in-theory (disable symbols-intern-front-frames-p symbols-intern-front-ready-p
                               symbols-intern-front-state symbols-intern-setup-state symbols-intern-designator-view
                               symbols-intern-name-call symbols-intern-name-view symbols-hash-input-p
                               symbols-intern-static-entry-ready-p symbols-intern-hashed symbols-intern-static-slot
                               proof-symbol-hash proof-integer-word boymoo-model::a64-signed
                               symbols-intern-probes-ready-p symbols-intern-probes-finish symbols-intern-probes-binding
                               symbols-intern-static-entry symbols-intern-saved-frame-p symbols-intern-saved-input-p
                               symbols-no-memory-or-kernel-change-p proof-packages-p proof-package-number
                               symbols-runtime-base-p)))
  :rule-classes nil)

(defun symbols-intern-existing-finish (name static-count static-fuels dynamic-count dynamic-fuels before)
  (proof-advance (len *symbols-intern-return-path*)
                 (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels before)))

(defthm symbols-run-intern-existing
  (let* ((middle (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels before))
         (after (symbols-intern-existing-finish name static-count static-fuels dynamic-count dynamic-fuels before))
         (binding (symbols-intern-lookup-binding name static-count static-fuels dynamic-count before)))
    (implies (and (symbols-intern-at-p 0 code-base before)
                  (<= 48 (boymoo-model::a64-sp (proof-world-machine before)))
                  (stringp name) (symbolp designator) (proof-packages-p packages)
                  (symbols-intern-saved-input-p name designator before objects packages)
                  (symbols-intern-lookup-ready-p name static-count static-fuels dynamic-count dynamic-fuels
                                                 code-base before)
                  binding
                  (symbols-path-ready-p *symbols-intern-return-path* code-base (proof-world-reg 30 before) middle))
             (and (proof-frame-return-p *symbols-intern-call-clobbers* t before after)
                  (equal (proof-world-reg 0 after) (cdr binding))
                  (symbols-no-memory-or-kernel-change-p (symbols-intern-saved-world before) after))))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-lookup)
                 (:instance symbols-intern-saved-frame-has-caller-words
                            (middle (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels before)))
                 (:instance symbols-run-intern-return
                            (before (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels before)))
                 (:instance symbols-intern-restore-returns-to-caller
                            (middle (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels before))
                            (result (cdr (symbols-intern-lookup-binding name static-count static-fuels dynamic-count before)))
                            (after (symbols-intern-existing-finish name static-count static-fuels dynamic-count dynamic-fuels before))))
           :in-theory (disable symbols-intern-lookup-ready-p symbols-intern-lookup-state symbols-intern-lookup-binding
                               symbols-intern-restore-frame-p proof-frame-return-p proof-packages-p
                               symbols-intern-saved-input-p symbols-no-memory-or-kernel-change-p)))
  :rule-classes nil)

(local
 (defthm symbols-intern-result-value-survives-return
   (let ((saved (symbols-intern-saved-world before)))
     (implies (and (proof-frame-return-p *symbols-intern-call-clobbers* t before after)
                   (symbols-no-memory-or-kernel-change-p saved after)
                   (proof-machine-value-p (proof-world-reg 0 after) value saved objects packages))
              (proof-reg-value-p 0 value after objects packages)))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers *symbols-intern-call-clobbers*))
                  (:instance symbols-view-depends-on-memory
                             (word (proof-world-reg 0 after)) (base (proof-heap-base before))
                             (first (proof-world-machine (symbols-intern-saved-world before)))
                             (last (proof-world-machine after))))
            :in-theory (e/d (proof-heap-base symbols-no-memory-or-kernel-change-p)
                            (proof-view))))
   :rule-classes nil))

(defthm symbols-intern-default-runtime-contract
  (let* ((primitive 'acl2::intern-in-package-of-symbol)
         (args (list name designator))
         (front (symbols-intern-front-state before))
         (after (symbols-intern-rejection-finish before)))
    (implies (and (proof-runtime-pre-p primitive args program *symbols-runtime-labels*
                                       code-base before objects packages)
                  (symbols-intern-at-p 0 code-base before)
                  (<= 48 (boymoo-model::a64-sp (proof-world-machine before)))
                  (symbols-intern-front-ready-p code-base before)
                  (symbols-intern-saved-input-p name designator before objects packages)
                  (symbols-intern-default-p name designator)
                  (symbols-path-ready-p *symbols-intern-reject-path* code-base
                                        (proof-world-reg 30 before) front)
                  (proof-machine-value-p *proof-nil* nil (symbols-intern-saved-world before) objects packages)
                  (proof-preserved-heap-p t before after objects objects packages))
             (proof-runtime-return-p primitive args program before after objects objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-default)
                 (:instance symbols-intern-result-value-survives-return
                            (value nil) (after (symbols-intern-rejection-finish before)))
                 (:instance symbols-intern-default-implements-core))
           :in-theory (disable proof-frame-return-p proof-machine-value-p proof-reg-value-p proof-preserved-heap-p
                               boymoo-model::core-primitive symbols-intern-default-implements-core
                               symbols-intern-front-ready-p symbols-intern-front-state symbols-intern-at-p
                               symbols-intern-saved-input-p symbols-intern-rejection-finish
                               symbols-no-memory-or-kernel-change-p)))
  :rule-classes nil)

; The static data agreement pairs a word found in the physical chain
; with the decoded binding. The dynamic data agreement supplies the
; represented resident symbol and its home key.
(defun symbols-intern-existing-agreement-p (name designator static-count static-fuels dynamic-count
                                                 buckets resident before objects packages)
  (let* ((number (proof-package-number (acl2::symbol-package-name designator) packages 0))
         (start (symbols-intern-lookup-start name before))
         (physical (symbols-intern-binding static-count nil start))
         (static (proof-static-binding number name buckets))
         (binding (symbols-intern-lookup-binding name static-count static-fuels dynamic-count before))
         (saved (symbols-intern-saved-world before)))
    (and (natp number)
         (iff physical static)
         (if physical
             (and (proof-static-bucket-p
                   (proof-view-value (nth (proof-symbol-hash number name 12) buckets))
                   (proof-symbol-hash number name 12) packages)
                  (proof-machine-value-p (cdr physical) (cdr static) saved objects packages))
           (and (proof-package-bindings-p packages 0 buckets)
                (implies binding
                         (and (symbolp resident) (equal (symbol-name resident) name)
                              (equal (acl2::symbol-package-name resident) (acl2::symbol-package-name designator))
                              (proof-machine-value-p (cdr binding) resident saved objects packages))))))))

(defthm symbols-intern-existing-value-implements-core
  (let* ((binding (symbols-intern-lookup-binding name static-count static-fuels dynamic-count before))
         (source (boymoo-model::core-primitive 'acl2::intern-in-package-of-symbol (list name designator) program)))
    (implies (and (stringp name) (symbolp designator) (proof-packages-p packages) binding
                  (symbols-intern-existing-agreement-p name designator static-count static-fuels dynamic-count
                                                       buckets resident before objects packages))
             (and (boymoo-model::core-value-p source)
                  (proof-machine-value-p (cdr binding) (boymoo-model::core-datum source)
                                         (symbols-intern-saved-world before) objects packages))))
  :hints (("Goal"
           :use ((:instance symbols-intern-on-static-hit-implements-core)
                 (:instance symbols-intern-on-dynamic-hit-implements-core))
           :in-theory (disable symbols-intern-lookup-start symbols-intern-binding
                               symbols-intern-dynamic-entry symbols-intern-dynamic-root-nil-p
                               symbols-intern-static-probed proof-static-binding proof-static-bucket-p
                               proof-symbol-hash proof-package-number proof-package-bindings-p proof-packages-p
                               proof-machine-value-p boymoo-model::core-primitive
                               symbols-intern-on-static-hit-implements-core)))
  :rule-classes nil)

(defthm symbols-intern-existing-runtime-contract
  (let* ((primitive 'acl2::intern-in-package-of-symbol)
         (args (list name designator))
         (middle (symbols-intern-lookup-state name static-count static-fuels dynamic-count dynamic-fuels before))
         (binding (symbols-intern-lookup-binding name static-count static-fuels dynamic-count before))
         (after (symbols-intern-existing-finish name static-count static-fuels dynamic-count dynamic-fuels before)))
    (implies (and (proof-runtime-pre-p primitive args program *symbols-runtime-labels*
                                       code-base before objects packages)
                  (symbols-intern-at-p 0 code-base before)
                  (<= 48 (boymoo-model::a64-sp (proof-world-machine before)))
                  (stringp name) (symbolp designator) (proof-packages-p packages)
                  (symbols-intern-saved-input-p name designator before objects packages)
                  (symbols-intern-lookup-ready-p name static-count static-fuels dynamic-count dynamic-fuels
                                                 code-base before)
                  binding
                  (symbols-path-ready-p *symbols-intern-return-path* code-base (proof-world-reg 30 before) middle)
                  (symbols-intern-existing-agreement-p name designator static-count static-fuels dynamic-count
                                                       buckets resident before objects packages)
                  (proof-preserved-heap-p t before after objects objects packages))
             (proof-runtime-return-p primitive args program before after objects objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-existing)
                 (:instance symbols-intern-existing-value-implements-core)
                 (:instance symbols-intern-result-value-survives-return
                            (after (symbols-intern-existing-finish name static-count static-fuels
                                                                 dynamic-count dynamic-fuels before))
                            (value (boymoo-model::core-datum
                                    (boymoo-model::core-primitive 'acl2::intern-in-package-of-symbol
                                                                 (list name designator) program)))))
           :in-theory (disable proof-frame-return-p proof-machine-value-p proof-reg-value-p proof-preserved-heap-p
                               proof-packages-p symbols-intern-at-p symbols-intern-saved-input-p
                               symbols-intern-lookup-ready-p symbols-intern-lookup-state symbols-intern-lookup-binding
                               symbols-intern-existing-finish symbols-intern-existing-agreement-p
                               symbols-no-memory-or-kernel-change-p boymoo-model::core-primitive)))
  :rule-classes nil)

(local
 (defthm symbols-valid-heap-has-object-map
   (implies (proof-heap-p world objects packages)
            (proof-object-map-p objects objects nil (proof-heap-base world) packages (proof-world-machine world)))
   :hints (("Goal"
            :in-theory (disable proof-heap-layout-p proof-static-p proof-object-map-p proof-dynamic-entries
                                proof-dynamic-view proof-external-objects proof-heap-object-spans-p
                                proof-string-accounting-p proof-dynamic-symbol-objects-p proof-stack-prefix)))))

(defthm symbols-intern-return-word-is-canonical
  (let* ((primitive 'acl2::intern-in-package-of-symbol)
         (args (list name designator))
         (result (boymoo-model::core-datum (boymoo-model::core-primitive primitive args program))))
    (implies (and (proof-runtime-return-p primitive args program before after old-objects new-objects packages)
                  (proof-machine-value-p represented result after new-objects packages))
             (equal (proof-world-reg 0 after) represented)))
  :hints (("Goal"
           :use ((:instance symbols-valid-heap-has-object-map (world after) (objects new-objects))
                 (:instance symbols-canonical-symbol-word
                            (base (proof-heap-base after)) (first (proof-world-reg 0 after)) (second represented)
                            (symbol (boymoo-model::core-datum
                                     (boymoo-model::core-primitive 'acl2::intern-in-package-of-symbol
                                                                  (list name designator) program)))
                            (objects new-objects) (machine (proof-world-machine after))))
           :in-theory (e/d (proof-heap-base boymoo-model::core-primitive)
                           (proof-value-p proof-heap-p proof-object-map-p proof-frame-return-p
                            proof-fixed-heap-p proof-heap-frame-p proof-prefix-preserved-p
                            proof-dynamic-table-preserved-p symbols-valid-heap-has-object-map))))
  :rule-classes nil)

