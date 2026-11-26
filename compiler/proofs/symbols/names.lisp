(in-package "BOYMOO-PROOFS")

(include-book "contracts")
(include-book "loops")
(include-book "memory")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                     (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg proof-heap-base
                     proof-advance proof-advance-append proof-segment-p
                     boymoo-model::a64-unsigned symbols-runtime-offset
                     symbols-no-memory-or-kernel-change-p symbols-path-ready-p
                     symbols-load-register-word symbols-stack-word symbols-saved-link-world
                     symbols-symbol-view-result symbols-name-setup-path symbols-symbol-view-path
                     symbols-name-continuation-path symbols-package-name-dispatch-path
                     symbols-package-name-continuation-path)))

(defun symbols-name-view-call (package-name before)
  (proof-advance (len (symbols-name-setup-path package-name)) before))

(defun symbols-name-viewed (package-name before)
  (let ((call (symbols-name-view-call package-name before)))
    (proof-advance (len (symbols-symbol-view-path call)) call)))

(defun symbols-name-header (before)
  (symbols-symbol-view-result (symbols-saved-link-world before)))

(defun symbols-name-view-ready-p (package-name base before)
  (let ((call (symbols-name-view-call package-name before)))
    (and (symbols-path-ready-p (symbols-name-setup-path package-name) base
                               (symbols-runtime-address "rt:symbol-view" base) before)
         (symbols-path-ready-p (symbols-symbol-view-path call) base (proof-world-reg 30 call) call))))

(defun symbols-name-viewed-frame-p (package-name base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after)
              (+ 8 (symbols-runtime-address (symbols-name-entry-label package-name) base)))
       (equal (proof-world-reg 1 after) (symbols-name-header before))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
       (proof-register-frame-p 30 '(1 2 30) before after)
       (symbols-no-memory-or-kernel-change-p (symbols-saved-link-world before) after)))

(local
 (defthm symbols-name-save-preserves-registers
   (equal (proof-world-reg register (symbols-saved-link-world before))
          (proof-world-reg register before))
   :hints (("Goal" :in-theory (enable symbols-saved-link-world proof-world-reg proof-reg)))))

(local
 (defthm symbols-name-view-result-of-equal-inputs
   (implies (and (symbols-no-memory-or-kernel-change-p first last)
                 (equal (proof-world-reg 0 first) (proof-world-reg 0 last))
                 (equal (proof-world-reg 28 first) (proof-world-reg 28 last)))
            (equal (symbols-symbol-view-result first) (symbols-symbol-view-result last)))
   :hints (("Goal" :in-theory (enable symbols-symbol-view-result proof-heap-base
                                     boymoo-model::a64-load symbols-no-memory-or-kernel-change-p)))
   :rule-classes nil))

(local
 (defthm symbols-name-viewed-frame-composition
   (implies (and (symbols-name-setup-frame-p package-name base before call)
                 (proof-frame-return-p '(1 2) t call after)
                 (not (eq (car (proof-world-machine after)) :svc))
                 (equal (proof-world-reg 1 after) (symbols-symbol-view-result call))
                 (symbols-no-memory-or-kernel-change-p call after))
            (symbols-name-viewed-frame-p package-name base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 0)
                             (clobbers '(30)) (after call))
                  (:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers '(30)) (after call))
                  (:instance symbols-name-view-result-of-equal-inputs
                             (first (symbols-saved-link-world before)) (last call))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(30)) (allowed '(1 2 30)) (after call))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(1 2)) (allowed '(1 2 30)) (before call))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers '(1 2 30))
                             (first before) (middle call) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-saved-link-world before)) (middle call) (last after)))))
   :rule-classes nil))

(defthm symbols-run-name-view
  (implies (and (symbols-name-setup-pre-p package-name code-base before)
                (symbols-name-view-ready-p package-name code-base before))
           (symbols-name-viewed-frame-p package-name code-base before
                                       (symbols-name-viewed package-name before)))
  :hints (("Goal"
           :use ((:instance symbols-run-name-setup)
                 (:instance symbols-run-symbol-view (before (symbols-name-view-call package-name before)))
                 (:instance symbols-name-viewed-frame-composition (base code-base)
                            (call (symbols-name-view-call package-name before))
                            (after (symbols-name-viewed package-name before))))
           :in-theory (disable symbols-name-viewed-frame-p symbols-run-symbol-view)))
  :rule-classes nil)

(local
 (defthm symbols-name-sp-is-natural
   (natp (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-name-sp-fits-word
   (< (boymoo-model::a64-sp machine) (expt 2 64))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :linear))

(local
 (defthm symbols-name-read-saved-words
   (let ((sp (boymoo-model::a64-sp (proof-world-machine before)))
         (saved (symbols-saved-link-world before)))
     (implies (<= 16 sp)
              (and (equal (symbols-load-register-word (- sp 16) saved) (proof-world-reg 29 before))
                   (equal (symbols-load-register-word (- sp 8) saved) (proof-world-reg 30 before)))))
   :hints (("Goal" :in-theory (e/d (symbols-saved-link-world symbols-load-register-word
                                    proof-world-reg proof-reg boymoo-model::a64-read-reg)
                                   (proof-load-word))))))

(local
 (defthm symbols-name-load-word-of-equal-memory
   (implies (equal (symbols-machine-memory first) (symbols-machine-memory last))
            (equal (symbols-load-register-word address first)
                   (symbols-load-register-word address last)))
   :hints (("Goal" :in-theory (enable symbols-load-register-word boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm symbols-name-stack-words-from-saves
   (let ((sp (boymoo-model::a64-sp (proof-world-machine before))))
     (implies (and (<= 16 sp)
                   (equal (boymoo-model::a64-sp (proof-world-machine viewed)) (- sp 16))
                   (symbols-no-memory-or-kernel-change-p (symbols-saved-link-world before) viewed))
              (and (equal (symbols-stack-word 0 viewed) (proof-world-reg 29 before))
                   (equal (symbols-stack-word 8 viewed) (proof-world-reg 30 before)))))
   :hints (("Goal"
            :use ((:instance symbols-name-read-saved-words)
                  (:instance symbols-name-load-word-of-equal-memory
                             (first (symbols-saved-link-world before)) (last viewed)
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 16)))
                  (:instance symbols-name-load-word-of-equal-memory
                             (first (symbols-saved-link-world before)) (last viewed)
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 8))))
            :in-theory (e/d (symbols-stack-word symbols-no-memory-or-kernel-change-p)
                            (symbols-name-read-saved-words))))
   :rule-classes nil))

(defconst *symbols-name-clobbers* '(0 1 2 5))
(defconst *symbols-name-link-clobbers* '(0 1 2 5 29 30))

(defun symbols-name-transfer-p (address word before after)
  (and (not (proof-world-stop after))
       (equal (proof-world-pc after) address)
       (equal (proof-world-reg 0 after) word)
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-register-frame-p 30 *symbols-name-clobbers* before after)
       (symbols-no-memory-or-kernel-change-p (symbols-saved-link-world before) after)))

(local
 (defthm symbols-name-restored-register-frame
   (implies (and (proof-register-frame-p 30 *symbols-name-link-clobbers* before after)
                 (equal (proof-world-reg 29 before) (proof-world-reg 29 after))
                 (equal (proof-world-reg 30 before) (proof-world-reg 30 after)))
            (proof-register-frame-p 30 *symbols-name-clobbers* before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-keeps-restored-register
                             (highest 30) (register 29) (clobbers *symbols-name-link-clobbers*))
                  (:instance symbols-frame-keeps-restored-register
                             (highest 30) (register 30) (clobbers '(0 1 2 5 30))))))
   :rule-classes nil))

(defun symbols-symbol-name-ready-p (base before)
  (let ((viewed (symbols-name-viewed nil before)))
    (and (symbols-name-view-ready-p nil base before)
         (symbols-path-ready-p (symbols-name-continuation-path viewed) base
                               (symbols-name-continuation-target base viewed) viewed))))

(defun symbols-symbol-name-finish (before)
  (let ((viewed (symbols-name-viewed nil before)))
    (proof-advance (len (symbols-name-continuation-path viewed)) viewed)))

(defun symbols-symbol-name-transfer-target (base before)
  (if (equal (symbols-name-header before) 0) (symbols-runtime-address "rt:empty-string" base)
    (proof-world-reg 30 before)))

(defun symbols-symbol-name-word (before)
  (let ((header (symbols-name-header before)))
    (if (equal header 0) (proof-world-reg 0 before)
      (symbols-load-register-word (+ header 8) (symbols-saved-link-world before)))))

(local
 (defthm symbols-symbol-name-frames-compose
   (implies (and (symbols-name-setup-pre-p nil base before)
                 (symbols-name-viewed-frame-p nil base before viewed)
                 (symbols-name-continuation-frame-p base viewed after))
            (symbols-name-transfer-p (symbols-symbol-name-transfer-target base before)
                                      (symbols-symbol-name-word before) before after))
   :hints (("Goal"
            :use ((:instance symbols-name-stack-words-from-saves)
                  (:instance symbols-name-load-word-of-equal-memory
                             (first (symbols-saved-link-world before)) (last viewed)
                             (address (+ (symbols-name-header before) 8)))
                  (:instance symbols-frame-gives-register (highest 30) (register 0)
                             (clobbers '(1 2 30)) (after viewed))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(1 2 30)) (allowed *symbols-name-link-clobbers*) (after viewed))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0 29 30)) (allowed *symbols-name-link-clobbers*) (before viewed))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-name-link-clobbers*)
                             (first before) (middle viewed) (last after))
                  (:instance symbols-name-restored-register-frame)
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-saved-link-world before)) (middle viewed) (last after)))
            :in-theory (enable symbols-no-memory-or-kernel-change-p)))
   :rule-classes nil))

(defthm symbols-run-symbol-name
  (implies (and (symbols-name-setup-pre-p nil code-base before)
                (symbols-symbol-name-ready-p code-base before))
           (symbols-name-transfer-p (symbols-symbol-name-transfer-target code-base before)
                                     (symbols-symbol-name-word before) before
                                     (symbols-symbol-name-finish before)))
  :hints (("Goal"
           :use ((:instance symbols-run-name-view (package-name nil))
                 (:instance symbols-run-name-continuation (before (symbols-name-viewed nil before)))
                 (:instance symbols-name-sp-fits-word (machine (proof-world-machine before)))
                 (:instance symbols-symbol-name-frames-compose (base code-base)
                            (viewed (symbols-name-viewed nil before))
                            (after (symbols-symbol-name-finish before))))
           :in-theory (disable symbols-name-viewed symbols-name-view-ready-p
                               symbols-name-continuation-frame-p symbols-name-transfer-p
                               symbols-run-name-continuation)))
  :rule-classes nil)

(defun symbols-package-name-dispatched (before)
  (let ((viewed (symbols-name-viewed t before)))
    (proof-advance (len (symbols-package-name-dispatch-path viewed)) viewed)))

(defun symbols-package-name-row-state (before)
  (proof-advance (len *symbols-package-row-path*) (symbols-package-name-dispatched before)))

(defun symbols-package-name-ready-p (base before)
  (let ((viewed (symbols-name-viewed t before)))
    (and (symbols-name-view-ready-p t base before)
         (symbols-path-ready-p (symbols-package-name-dispatch-path viewed) base
                               (symbols-package-name-dispatch-target base viewed) viewed)
         (implies (not (equal (symbols-name-header before) 0))
                  (let ((call (symbols-package-name-dispatched before))
                        (row (symbols-package-name-row-state before)))
                    (and (symbols-path-ready-p *symbols-package-row-path* base (proof-world-reg 30 call) call)
                         (symbols-path-ready-p (symbols-package-name-continuation-path row) base
                                               (symbols-package-name-continuation-target base row) row)))))))

(defun symbols-package-name-finish (before)
  (if (equal (symbols-name-header before) 0)
      (symbols-package-name-dispatched before)
    (let ((row (symbols-package-name-row-state before)))
      (proof-advance (len (symbols-package-name-continuation-path row)) row))))

(defun symbols-package-name-row-frame-p (base before call row)
  (and (not (proof-world-stop row))
       (not (eq (car (proof-world-machine row)) :svc))
       (equal (proof-world-pc row) (+ 24 (symbols-runtime-address *symbols-package-name-entry* base)))
       (equal (proof-world-reg 0 row) (symbols-package-row-address call))
       (equal (proof-world-reg 5 row) (proof-world-reg 0 before))
       (equal (proof-world-reg 0 call)
              (symbols-load-register-word (+ (symbols-name-header before) 16)
                                          (symbols-saved-link-world before)))
       (equal (proof-heap-base call) (proof-heap-base before))
       (equal (boymoo-model::a64-sp (proof-world-machine row))
              (- (boymoo-model::a64-sp (proof-world-machine before)) 16))
       (proof-register-frame-p 30 *symbols-name-link-clobbers* before row)
       (symbols-no-memory-or-kernel-change-p (symbols-saved-link-world before) call)
       (symbols-no-memory-or-kernel-change-p (symbols-saved-link-world before) row)))

(local
 (defthm symbols-package-name-row-frames-compose
   (implies (and (symbols-name-viewed-frame-p t base before viewed)
                 (not (equal (symbols-name-header before) 0))
                 (symbols-package-name-dispatch-frame-p base viewed call)
                 (proof-frame-return-p '(0 1) nil call row)
                 (not (eq (car (proof-world-machine row)) :svc))
                 (equal (proof-world-reg 0 row) (symbols-package-row-address call))
                 (symbols-no-memory-or-kernel-change-p call row))
            (symbols-package-name-row-frame-p base before call row))
   :hints (("Goal"
            :use ((:instance symbols-name-load-word-of-equal-memory
                             (first (symbols-saved-link-world before)) (last viewed)
                             (address (+ (symbols-name-header before) 16)))
                  (:instance symbols-frame-gives-register (highest 30) (register 0)
                             (clobbers '(1 2 30)) (after viewed))
                  (:instance symbols-frame-gives-register (highest 30) (register 5)
                             (clobbers '(0 1)) (before call) (after row))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(1 2 30)) (allowed *symbols-name-link-clobbers*) (after viewed))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0 5 29 30)) (allowed *symbols-name-link-clobbers*)
                             (before viewed) (after call))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0 1)) (allowed *symbols-name-link-clobbers*) (before call) (after row))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-name-link-clobbers*)
                             (first before) (middle viewed) (last call))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-name-link-clobbers*)
                             (first before) (middle call) (last row))
                  (:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers *symbols-name-link-clobbers*) (after call))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-saved-link-world before)) (middle viewed) (last call))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-saved-link-world before)) (middle call) (last row)))
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p proof-heap-base) (symbols-package-row-address))))
   :rule-classes nil))

(local
 (defthm symbols-package-name-empty-frames-compose
   (implies (and (symbols-name-setup-pre-p t base before)
                 (symbols-name-viewed-frame-p t base before viewed)
                 (equal (symbols-name-header before) 0)
                 (symbols-package-name-dispatch-frame-p base viewed after))
            (symbols-name-transfer-p (symbols-runtime-address "rt:empty-string" base)
                                      (proof-world-reg 0 before) before after))
   :hints (("Goal"
            :use ((:instance symbols-name-stack-words-from-saves)
                  (:instance symbols-frame-gives-register (highest 30) (register 0)
                             (clobbers '(1 2 30)) (after viewed))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(1 2 30)) (allowed *symbols-name-link-clobbers*) (after viewed))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0 5 29 30)) (allowed *symbols-name-link-clobbers*) (before viewed))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-name-link-clobbers*)
                             (first before) (middle viewed) (last after))
                  (:instance symbols-name-restored-register-frame)
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-saved-link-world before)) (middle viewed) (last after)))))
   :rule-classes nil))

(defthm symbols-run-package-name-to-row
  (let ((call (symbols-package-name-dispatched before))
        (row (symbols-package-name-row-state before)))
    (implies (and (symbols-name-setup-pre-p t code-base before)
                  (symbols-package-name-ready-p code-base before))
             (if (equal (symbols-name-header before) 0)
                 (symbols-name-transfer-p (symbols-runtime-address "rt:empty-string" code-base)
                                           (proof-world-reg 0 before) before call)
               (symbols-package-name-row-frame-p code-base before call row))))
  :hints (("Goal"
           :use ((:instance symbols-run-name-view (package-name t))
                 (:instance symbols-run-package-name-dispatch (before (symbols-name-viewed t before)))
                 (:instance symbols-run-package-row (before (symbols-package-name-dispatched before)))
                 (:instance symbols-name-sp-fits-word (machine (proof-world-machine before)))
                 (:instance symbols-package-name-row-frames-compose (base code-base)
                            (viewed (symbols-name-viewed t before))
                            (call (symbols-package-name-dispatched before))
                            (row (symbols-package-name-row-state before)))
                 (:instance symbols-package-name-empty-frames-compose (base code-base)
                            (viewed (symbols-name-viewed t before))
                            (after (symbols-package-name-dispatched before))))
           :in-theory (disable symbols-name-viewed symbols-name-view-ready-p
                               symbols-package-row-address symbols-package-row-slot
                               symbols-run-package-row symbols-package-name-row-frame-p
                               symbols-name-transfer-p symbols-package-name-continuation-target)))
  :rule-classes nil)

(defun symbols-package-name-target (row base before)
  (cond ((equal (symbols-name-header before) 0) (symbols-runtime-address "rt:empty-string" base))
        ((equal (symbols-load-register-word (+ row 24) (symbols-saved-link-world before)) *proof-nil*)
         (symbols-runtime-address "rt:hidden-symbol" base))
        (t (proof-world-reg 30 before))))

(defun symbols-package-name-word (row before)
  (if (or (equal (symbols-name-header before) 0)
          (equal (symbols-load-register-word (+ row 24) (symbols-saved-link-world before)) *proof-nil*))
      (proof-world-reg 0 before)
    (symbols-load-register-word (+ row 8) (symbols-saved-link-world before))))

(local
 (defthm symbols-package-name-return-frames-compose
   (let ((address (symbols-package-row-address call)))
     (implies (and (symbols-name-setup-pre-p t base before)
                   (not (equal (symbols-name-header before) 0))
                   (symbols-package-name-row-frame-p base before call row)
                   (symbols-package-name-continuation-frame-p base row after))
              (symbols-name-transfer-p (symbols-package-name-target address base before)
                                        (symbols-package-name-word address before) before after)))
   :hints (("Goal"
            :use ((:instance symbols-name-stack-words-from-saves (viewed row))
                  (:instance symbols-name-load-word-of-equal-memory
                             (first (symbols-saved-link-world before)) (last row)
                             (address (+ (symbols-package-row-address call) 8)))
                  (:instance symbols-name-load-word-of-equal-memory
                             (first (symbols-saved-link-world before)) (last row)
                             (address (+ (symbols-package-row-address call) 24)))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0 1 29 30)) (allowed *symbols-name-link-clobbers*) (before row))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-name-link-clobbers*)
                             (first before) (middle row) (last after))
                  (:instance symbols-name-restored-register-frame)
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-saved-link-world before)) (middle row) (last after)))
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p) (symbols-package-row-address))))
   :rule-classes nil))

(defthm symbols-run-symbol-package-name
  (let* ((call (symbols-package-name-dispatched before))
         (address (symbols-package-row-address call)))
    (implies (and (symbols-name-setup-pre-p t code-base before)
                  (symbols-package-name-ready-p code-base before))
             (symbols-name-transfer-p (symbols-package-name-target address code-base before)
                                       (symbols-package-name-word address before) before
                                       (symbols-package-name-finish before))))
  :hints (("Goal"
           :use ((:instance symbols-run-package-name-to-row)
                 (:instance symbols-run-package-name-continuation (before (symbols-package-name-row-state before)))
                 (:instance symbols-name-sp-fits-word (machine (proof-world-machine before)))
                 (:instance symbols-package-name-return-frames-compose (base code-base)
                            (call (symbols-package-name-dispatched before))
                            (row (symbols-package-name-row-state before))
                            (after (symbols-package-name-finish before))))
           :in-theory (disable symbols-package-name-dispatched symbols-package-name-row-state
                               symbols-package-name-continuation-frame-p symbols-name-transfer-p
                               symbols-run-package-name-continuation symbols-package-row-address)))
  :rule-classes nil)

(defun symbols-name-saved-input-p (datum before objects packages)
  (let ((saved (symbols-saved-link-world before)))
    (and (proof-reg-value-p 0 datum saved objects packages)
         (implies (symbolp datum)
                  (not (equal (proof-pointer-address (proof-world-reg 0 saved)
                                                     (proof-heap-base saved))
                              0))))))

(defthm symbols-name-header-agrees-with-input
  (implies (symbols-name-saved-input-p datum before objects packages)
           (equal (symbols-name-header before)
                  (if (symbolp datum)
                      (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before))
                    0)))
  :hints (("Goal"
           :use ((:instance symbols-symbol-view-agrees-with-value
                            (world (symbols-saved-link-world before))))
           :in-theory (e/d (proof-heap-base)
                           (symbols-symbol-view-agrees-with-value proof-value-p proof-view
                            proof-pointer-address))))
  :rule-classes nil)

(local
 (defthm symbols-name-value-in-returned-world
   (implies (and (symbols-name-transfer-p target word before after)
                 (proof-machine-value-p word value (symbols-saved-link-world before) objects packages))
            (proof-reg-value-p 0 value after objects packages))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers *symbols-name-clobbers*))
                  (:instance symbols-view-depends-on-memory
                             (base (proof-heap-base before))
                             (first (proof-world-machine (symbols-saved-link-world before)))
                             (last (proof-world-machine after))))
            :in-theory (e/d (proof-heap-base symbols-no-memory-or-kernel-change-p)
                            (proof-view proof-pointer-address))))
   :rule-classes nil))

(local
 (defthm symbols-name-transfer-to-link-is-return
   (implies (and (not (proof-world-stop before))
                 (symbols-name-transfer-p (proof-world-reg 30 before) word before after))
            (proof-frame-return-p (append *proof-volatile-registers* '(26 27)) t before after))
   :hints (("Goal" :use ((:instance symbols-frame-allows-more-clobbers (highest 30)
                                    (clobbers *symbols-name-clobbers*)
                                    (allowed (append *proof-volatile-registers* '(26 27)))))))
   :rule-classes nil))

(defthm symbols-symbol-name-result-implements-core
  (let* ((after (symbols-symbol-name-finish before))
         (result (boymoo-model::core-primitive 'symbol-name (list datum) program)))
    (implies (and (symbols-name-setup-pre-p nil code-base before)
                  (symbols-symbol-name-ready-p code-base before)
                  (symbolp datum) (symbols-name-saved-input-p datum before objects packages))
             (and (boymoo-model::core-value-p result)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after objects packages)
                  (proof-frame-return-p (append *proof-volatile-registers* '(26 27)) t before after))))
  :hints (("Goal"
           :use ((:instance symbols-run-symbol-name)
                 (:instance symbols-name-header-agrees-with-input)
                 (:instance symbols-published-symbol-fields
                            (symbol datum)
                            (word (proof-world-reg 0 (symbols-saved-link-world before)))
                            (base (proof-heap-base (symbols-saved-link-world before)))
                            (machine (proof-world-machine (symbols-saved-link-world before))))
                 (:instance symbols-name-value-in-returned-world
                            (target (symbols-symbol-name-transfer-target code-base before))
                            (word (symbols-symbol-name-word before)) (value (symbol-name datum))
                            (after (symbols-symbol-name-finish before)))
                 (:instance symbols-name-transfer-to-link-is-return
                            (word (symbols-symbol-name-word before)) (after (symbols-symbol-name-finish before))))
           :in-theory (e/d (boymoo-model::core-primitive symbols-load-register-word symbols-word-load-fits
                            proof-heap-base)
                           (symbols-name-transfer-p proof-frame-return-p proof-value-p proof-view
                            proof-pointer-address boymoo-model::a64-load
                            symbols-symbol-name-ready-p symbols-symbol-name-finish))))
  :rule-classes nil)

(defun symbols-symbol-package-data-agreement-p (datum address before objects packages)
  (let* ((saved (symbols-saved-link-world before))
         (name (acl2::symbol-package-name datum))
         (row (assoc-equal name packages)))
    (and row
         (iff (equal (symbols-load-register-word (+ address 24) saved) *proof-nil*)
              (not (proof-package-visible row)))
         (implies (proof-package-visible row)
                  (proof-machine-value-p (symbols-load-register-word (+ address 8) saved)
                                         name saved objects packages)))))

(defthm symbols-symbol-package-name-result-implements-core
  (let* ((after (symbols-package-name-finish before))
         (address (symbols-package-row-address (symbols-package-name-dispatched before)))
         (result (boymoo-model::core-primitive 'acl2::symbol-package-name (list datum) program)))
    (implies (and (symbols-name-setup-pre-p t code-base before)
                  (symbols-package-name-ready-p code-base before)
                  (symbolp datum) (symbols-name-saved-input-p datum before objects packages)
                  (proof-program-packages-p program packages)
                  (symbols-symbol-package-data-agreement-p datum address before objects packages))
             (if (boymoo-model::core-value-p result)
                 (and (proof-reg-value-p 0 (boymoo-model::core-datum result) after objects packages)
                      (proof-frame-return-p (append *proof-volatile-registers* '(26 27)) t before after))
               (and (equal result :no-value)
                    (equal (proof-world-pc after) (symbols-runtime-address "rt:hidden-symbol" code-base))
                    (equal (proof-world-reg 0 after) (proof-world-reg 0 before))))))
  :hints (("Goal"
           :use ((:instance symbols-run-symbol-package-name)
                 (:instance symbols-name-header-agrees-with-input)
                 (:instance symbols-package-name-implements-core)
                 (:instance symbols-name-value-in-returned-world
                            (target (symbols-package-name-target
                                     (symbols-package-row-address (symbols-package-name-dispatched before))
                                     code-base before))
                            (word (symbols-package-name-word
                                   (symbols-package-row-address (symbols-package-name-dispatched before)) before))
                            (value (acl2::symbol-package-name datum)) (after (symbols-package-name-finish before)))
                 (:instance symbols-name-transfer-to-link-is-return
                            (word (symbols-package-name-word
                                   (symbols-package-row-address (symbols-package-name-dispatched before)) before))
                            (after (symbols-package-name-finish before))))
           :in-theory (e/d (proof-heap-base)
                           (symbols-package-row-address symbols-package-name-dispatched
                            symbols-package-name-ready-p symbols-package-name-finish
                            symbols-package-name-implements-core proof-program-packages-p
                            proof-frame-return-p proof-value-p proof-view proof-machine-value-p
                            proof-pointer-address assoc-equal))))
  :rule-classes nil)

(local
 (defthm symbols-empty-string-has-no-characters
   (implies (and (stringp value) (equal (length value) 0))
            (equal value ""))
   :hints (("Goal"
            :use ((:instance acl2::coerce-inverse-2 (acl2::x value)))
            :expand ((len (coerce value 'list)))
            :in-theory (disable acl2::coerce-inverse-2)))
   :rule-classes nil))

(local
 (defthm symbols-value-view-reconstruct
   (implies (proof-value-view-p view)
            (equal view (proof-value-view (proof-view-value view))))
   :rule-classes nil))

(local
 (defthm symbols-empty-constructor-returns-value
   (implies (proof-string-constructor-return-p 0 entry after old-objects new-objects packages)
            (proof-reg-value-p 0 "" after new-objects packages))
   :hints (("Goal"
            :use ((:instance symbols-empty-string-has-no-characters
                             (value (proof-view-value
                                     (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                                                 new-objects packages (proof-world-machine after)))))
                  (:instance symbols-value-view-reconstruct
                             (view (proof-view (proof-world-reg 0 after) (proof-heap-base after)
                                               new-objects packages (proof-world-machine after)))))
            :in-theory (disable proof-frame-return-p proof-preserved-heap-p
                                proof-view proof-pointer-address proof-covered-p)))))

(local
 (defthm symbols-name-constructor-frame-composition
   (let ((clobbers (append *proof-volatile-registers* '(26 27))))
     (implies (and (not (proof-world-stop before))
                   (symbols-name-transfer-p target word before entry)
                   (proof-frame-return-p clobbers t entry after))
              (proof-frame-return-p clobbers t before after)))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 30)
                             (clobbers *symbols-name-clobbers*) (after entry))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers *symbols-name-clobbers*) (after entry)
                             (allowed (append *proof-volatile-registers* '(26 27))))
                  (:instance symbols-frame-is-transitive (highest 30)
                             (clobbers (append *proof-volatile-registers* '(26 27)))
                             (first before) (middle entry) (last after)))))
   :rule-classes nil))

(defun symbols-name-primitive (package-name)
  (if package-name 'acl2::symbol-package-name 'symbol-name))

(defun symbols-name-ready-p (package-name base before)
  (if package-name (symbols-package-name-ready-p base before)
    (symbols-symbol-name-ready-p base before)))

(defun symbols-name-finish (package-name before)
  (if package-name (symbols-package-name-finish before)
    (symbols-symbol-name-finish before)))

(defthm symbols-nonsymbol-name-implements-core
  (let* ((entry (symbols-name-finish package-name before))
         (after (proof-advance (nfix empty-fuel) entry))
         (primitive (symbols-name-primitive package-name))
         (result (boymoo-model::core-primitive primitive (list datum) program)))
    (implies (and (symbols-name-setup-pre-p package-name code-base before)
                  (symbols-name-ready-p package-name code-base before)
                  (not (symbolp datum))
                  (proof-program-packages-p program packages)
                  (symbols-name-saved-input-p datum before old-objects packages)
                  (proof-string-constructor-return-p 0 entry after old-objects new-objects packages))
             (and (equal result (boymoo-model::core-value ""))
                  (equal (proof-world-pc entry) (symbols-runtime-address "rt:empty-string" code-base))
                  (proof-reg-value-p 0 "" after new-objects packages)
                  (proof-frame-return-p (append *proof-volatile-registers* '(26 27)) t before after))))
  :hints (("Goal"
           :use ((:instance symbols-run-symbol-name)
                 (:instance symbols-run-symbol-package-name)
                 (:instance symbols-name-header-agrees-with-input (objects old-objects))
                 (:instance symbols-name-of-nonsymbol-implements-core)
                 (:instance symbols-package-name-implements-core)
                 (:instance symbols-empty-constructor-returns-value
                            (entry (symbols-name-finish package-name before))
                            (after (proof-advance (nfix empty-fuel) (symbols-name-finish package-name before))))
                 (:instance symbols-name-constructor-frame-composition
                            (word (proof-world-reg 0 before))
                            (target (symbols-runtime-address "rt:empty-string" code-base))
                            (entry (symbols-name-finish package-name before))
                            (after (proof-advance (nfix empty-fuel) (symbols-name-finish package-name before)))))
           :in-theory (disable symbols-symbol-name-finish symbols-package-name-finish
                               symbols-package-row-address symbols-name-header
                               symbols-name-saved-input-p proof-reg-value-p proof-frame-return-p
                               proof-program-packages-p boymoo-model::core-primitive
                               symbols-name-of-nonsymbol-implements-core symbols-package-name-implements-core
                               proof-preserved-heap-p)))
  :rule-classes nil)

(defthm symbols-name-of-symbol-runtime-contract
  (let* ((primitive (symbols-name-primitive package-name))
         (address (symbols-package-row-address (symbols-package-name-dispatched before)))
         (after (symbols-name-finish package-name before)))
    (implies (and (proof-runtime-pre-p primitive (list datum) program *symbols-runtime-labels*
                                       code-base before objects packages)
                  (symbols-name-setup-pre-p package-name code-base before)
                  (symbols-name-ready-p package-name code-base before)
                  (symbolp datum) (symbols-name-saved-input-p datum before objects packages)
                  (proof-program-packages-p program packages)
                  (implies package-name
                           (symbols-symbol-package-data-agreement-p datum address before objects packages))
                  (boymoo-model::core-value-p (boymoo-model::core-primitive primitive (list datum) program))
                  (proof-preserved-heap-p nil before after objects objects packages)
                  (proof-fixed-heap-p before after objects))
             (proof-runtime-return-p primitive (list datum) program before after objects objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-symbol-name-result-implements-core)
                 (:instance symbols-symbol-package-name-result-implements-core))
           :in-theory (disable proof-runtime-pre-p proof-frame-return-p proof-reg-value-p
                               proof-program-packages-p proof-preserved-heap-p proof-fixed-heap-p
                               boymoo-model::core-primitive symbols-symbol-name-ready-p
                               symbols-package-name-ready-p symbols-package-row-address
                               symbols-symbol-name-finish symbols-package-name-finish)))
  :rule-classes nil)

(defthm symbols-name-of-nonsymbol-runtime-contract
  (let* ((primitive (symbols-name-primitive package-name))
         (entry (symbols-name-finish package-name before))
         (after (proof-advance (nfix empty-fuel) entry)))
    (implies (and (proof-runtime-pre-p primitive (list datum) program *symbols-runtime-labels*
                                       code-base before old-objects packages)
                  (symbols-name-setup-pre-p package-name code-base before)
                  (symbols-name-ready-p package-name code-base before)
                  (not (symbolp datum))
                  (proof-program-packages-p program packages)
                  (symbols-name-saved-input-p datum before old-objects packages)
                  (proof-string-constructor-return-p 0 entry after old-objects new-objects packages)
                  (proof-preserved-heap-p nil before after old-objects new-objects packages))
             (proof-runtime-return-p primitive (list datum) program before after old-objects new-objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-nonsymbol-name-implements-core))
           :in-theory (disable proof-runtime-pre-p proof-frame-return-p proof-reg-value-p
                               proof-program-packages-p proof-preserved-heap-p proof-string-constructor-return-p
                               boymoo-model::core-primitive symbols-name-ready-p symbols-name-finish)))
  :rule-classes nil)

(local (include-book "row-data"))

(local
 (defthm symbols-package-name-field-encodes-home-number
   (let* ((saved (symbols-saved-link-world before))
          (number (proof-package-number (acl2::symbol-package-name datum) packages 0))
          (field (symbols-load-register-word (+ 16 (symbols-name-header before)) saved)))
     (implies (and (symbolp datum) (symbols-name-saved-input-p datum before objects packages)
                   (proof-packages-p packages))
              (and (not (equal (symbols-name-header before) 0))
                   (natp number) (< number (len packages)) (< number (expt 2 62))
                   (equal field (+ 1 (* 2 number))))))
   :hints (("Goal"
            :use ((:instance symbols-name-header-agrees-with-input)
                  (:instance symbols-published-symbol-fields (symbol datum)
                             (word (proof-world-reg 0 (symbols-saved-link-world before)))
                             (base (proof-heap-base (symbols-saved-link-world before)))
                             (machine (proof-world-machine (symbols-saved-link-world before))))
                  (:instance symbols-package-number-of-indexed-row (first 0)
                             (number (proof-view-value
                                      (proof-view
                                       (proof-load-word (+ 16 (proof-pointer-address
                                                              (proof-world-reg 0 (symbols-saved-link-world before))
                                                              (proof-heap-base (symbols-saved-link-world before))))
                                                        (proof-world-machine (symbols-saved-link-world before)))
                                       (proof-heap-base (symbols-saved-link-world before))
                                       objects packages (proof-world-machine (symbols-saved-link-world before))))))
                  (:instance symbols-canonical-immediate-integer-word
                             (word (proof-load-word (+ 16 (proof-pointer-address
                                                           (proof-world-reg 0 (symbols-saved-link-world before))
                                                           (proof-heap-base (symbols-saved-link-world before))))
                                                    (proof-world-machine (symbols-saved-link-world before))))
                             (base (proof-heap-base (symbols-saved-link-world before)))
                             (machine (proof-world-machine (symbols-saved-link-world before)))
                             (number (proof-view-value
                                      (proof-view
                                       (proof-load-word (+ 16 (proof-pointer-address
                                                              (proof-world-reg 0 (symbols-saved-link-world before))
                                                              (proof-heap-base (symbols-saved-link-world before))))
                                                        (proof-world-machine (symbols-saved-link-world before)))
                                       (proof-heap-base (symbols-saved-link-world before))
                                       objects packages (proof-world-machine (symbols-saved-link-world before)))))))
            :in-theory (e/d (proof-heap-base symbols-load-register-word symbols-word-load-fits)
                            (proof-load-word boymoo-model::a64-load proof-package-number proof-packages-p
                             proof-view proof-value-p proof-view-value proof-package-name
                             proof-pointer-address symbols-name-header))))
   :rule-classes nil))

(local
 (defthm symbols-name-row-word-keeps-value-across-call
   (implies (and (symbols-no-memory-or-kernel-change-p first last)
                 (equal (proof-heap-base first) (proof-heap-base last))
                 (proof-machine-value-p (symbols-load-register-word address first) value first objects packages))
            (proof-machine-value-p (symbols-load-register-word address last) value last objects packages))
   :hints (("Goal"
            :use ((:instance symbols-name-load-word-of-equal-memory)
                  (:instance symbols-view-depends-on-memory
                             (base (proof-heap-base first))
                             (word (symbols-load-register-word address first))
                             (first (proof-world-machine first)) (last (proof-world-machine last))))
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p)
                            (proof-view))))
   :rule-classes nil))

(local
 (defthm symbols-package-name-load-is-model-word
   (equal (symbols-load-register-word address world)
          (proof-load-word address (proof-world-machine world)))
   :hints (("Goal" :in-theory (e/d (symbols-load-register-word proof-load-word symbols-word-load-fits)
                                   (boymoo-model::a64-load))))))

(local
 (defthm symbols-package-name-from-associated-row
   (implies (assoc-equal name packages)
            (equal (proof-package-name (assoc-equal name packages)) name))
   :hints (("Goal" :induct (assoc-equal name packages)))))

(defthm symbols-package-name-data-from-static-map
  (let* ((call (symbols-package-name-dispatched before))
         (base (proof-heap-base call))
         (machine (proof-world-machine call))
         (address (symbols-package-row-address call)))
    (implies (and (symbols-name-setup-pre-p t code-base before)
                  (symbols-package-name-ready-p code-base before)
                  (symbolp datum) (symbols-name-saved-input-p datum before objects packages)
                  (proof-static-p base objects packages machine)
                  (proof-object-map-p objects objects nil base packages machine)
                  (proof-packages-p packages))
             (symbols-symbol-package-data-agreement-p datum address before objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-run-package-name-to-row)
                 (:instance symbols-package-name-field-encodes-home-number)
                 (:instance symbols-package-row-slot-agrees-with-static-vector
                            (number (proof-package-number (acl2::symbol-package-name datum) packages 0))
                            (world (symbols-package-name-dispatched before)))
                 (:instance symbols-package-number-selects-row (first 0) (name (acl2::symbol-package-name datum)))
                 (:instance symbols-package-number-present (first 0) (name (acl2::symbol-package-name datum)))
                 (:instance symbols-static-package-row-fields-in-live-objects
                            (number (proof-package-number (acl2::symbol-package-name datum) packages 0))
                            (base (proof-heap-base (symbols-package-name-dispatched before)))
                            (machine (proof-world-machine (symbols-package-name-dispatched before))))
                 (:instance symbols-static-package-row-witness-tests-visibility
                            (number (proof-package-number (acl2::symbol-package-name datum) packages 0))
                            (base (proof-heap-base (symbols-package-name-dispatched before)))
                            (machine (proof-world-machine (symbols-package-name-dispatched before))))
                 (:instance symbols-name-load-word-of-equal-memory
                            (address (+ 24 (symbols-package-row-address (symbols-package-name-dispatched before))))
                            (first (symbols-package-name-dispatched before))
                            (last (symbols-saved-link-world before)))
                 (:instance symbols-name-row-word-keeps-value-across-call
                            (address (+ 8 (symbols-package-row-address (symbols-package-name-dispatched before))))
                            (first (symbols-package-name-dispatched before))
                            (last (symbols-saved-link-world before))
                            (value (acl2::symbol-package-name datum))))
           :in-theory (e/d (proof-heap-base symbols-no-memory-or-kernel-change-p)
                           (symbols-package-name-dispatched symbols-package-name-row-state symbols-name-saved-input-p
                            symbols-package-name-ready-p symbols-name-header symbols-package-row-address
                            symbols-package-row-slot symbols-load-register-word symbols-logical-right-shift-bits
                            proof-register-frame-p symbols-name-transfer-p symbols-runtime-address
                            proof-package-number proof-package-name proof-package-visible
                            proof-static-p proof-object-map-p proof-value-p proof-pointer-address
                            proof-packages-p proof-package-imports proof-package-witness
                            symbols-package-number-selects-row symbols-package-number-present
                            proof-load-word boymoo-model::a64-load assoc-equal))))
  :rule-classes nil)
