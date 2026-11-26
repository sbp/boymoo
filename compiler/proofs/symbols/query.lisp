(in-package "BOYMOO-PROOFS")

(include-book "find")
(include-book "contracts")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                     (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg proof-heap-base
                     proof-advance proof-advance-append proof-byte-list proof-segment-p
                     boymoo-model::a64-unsigned symbols-runtime-offset
                     symbols-no-memory-or-kernel-change-p symbols-path-ready-p
                     symbols-query-saved-world symbols-load-register-word symbols-stack-word
                     symbols-logical-right-shift-bits symbols-string-view-path
                     symbols-query-dispatch-path symbols-query-string-continuation
                     symbols-query-default-path)))

(defun symbols-query-view-entry (before)
  (proof-advance (len *symbols-query-setup-path*) before))

(defun symbols-query-dispatch-entry (before)
  (let ((view (symbols-query-view-entry before)))
    (proof-advance (len (symbols-string-view-path view)) view)))

(defun symbols-query-dispatched (before)
  (let ((dispatch (symbols-query-dispatch-entry before)))
    (proof-advance (len (symbols-query-dispatch-path dispatch)) dispatch)))

(defun symbols-query-setup-ready-p (base before)
  (let ((view (symbols-query-view-entry before))
        (dispatch (symbols-query-dispatch-entry before)))
    (and (symbols-path-ready-p *symbols-query-setup-path* base
                               (symbols-runtime-address "rt:string-view" base) before)
         (symbols-path-ready-p (symbols-string-view-path view) base (proof-world-reg 30 view) view)
         (symbols-path-ready-p (symbols-query-dispatch-path dispatch) base
                               (symbols-query-dispatch-target base dispatch) dispatch))))

(defun symbols-query-string-argument-p (before)
  (let ((saved (symbols-query-saved-world before)))
    (and (symbols-string-hit-p saved)
         (not (equal (symbols-string-payload saved) 0)))))

(defun symbols-query-calls-finder-p (before)
  (or (symbols-query-string-argument-p before) (equal (proof-world-reg 6 before) 24)))

(defun symbols-query-dispatched-frame-p (base before after)
  (let* ((string-arg (symbols-query-string-argument-p before))
         (find (symbols-query-calls-finder-p before))
         (saved (symbols-query-saved-world before))
         (query (symbols-runtime-address "rt:package-query" base)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after)
                (symbols-runtime-address (if find "rt:find-package" "rt:package-query-nil") base))
         (equal (proof-world-reg 1 after)
                (cond (string-arg (symbols-string-payload saved))
                      (find (symbols-runtime-address "rt:acl2-name" base))
                      (t 0)))
         (implies find
                  (and (equal (proof-world-reg 2 after)
                              (if string-arg
                                  (symbols-logical-right-shift-bits (symbols-string-header-word saved) 8)
                                4))
                       (equal (proof-world-reg 30 after) (+ query (if string-arg 60 36)))))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
         (proof-register-frame-p 30 '(1 2 3 30) before after)
         (symbols-no-memory-or-kernel-change-p saved after))))

(local
 (defthm symbols-saves-preserve-registers
   (equal (proof-world-reg register (symbols-query-saved-world before))
          (proof-world-reg register before))
   :hints (("Goal" :in-theory (enable symbols-query-saved-world proof-world-reg proof-reg)))))

(local
 (defthm symbols-read-only-frame-preserves-string-view-data
   (implies (and (symbols-no-memory-or-kernel-change-p first last)
                 (equal (proof-world-reg 0 first) (proof-world-reg 0 last))
                 (equal (proof-world-reg 28 first) (proof-world-reg 28 last)))
            (and (equal (symbols-string-hit-p first) (symbols-string-hit-p last))
                 (equal (symbols-string-payload first) (symbols-string-payload last))
                 (equal (symbols-string-header-word first) (symbols-string-header-word last))))
   :hints (("Goal" :in-theory (enable symbols-no-memory-or-kernel-change-p proof-heap-base
                                     symbols-load-register-word boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm symbols-query-view-and-dispatch-preconditions
   (implies (and (symbols-runtime-base-p base)
                 (member-equal (proof-world-reg 6 before) '(16 24))
                 (symbols-query-setup-frame-p base before view))
            (and (symbols-string-view-pre-p base view)
                 (implies (symbols-string-view-frame-p view dispatch)
                          (symbols-query-dispatch-pre-p base dispatch))))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register
                             (highest 30) (register 6) (clobbers '(30)) (after view))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 6) (clobbers '(1 2 3))
                             (before view) (after dispatch)))
            :in-theory (disable symbols-string-payload symbols-string-hit-p
                                symbols-string-header-word)))
   :rule-classes nil))

(local
 (defthm symbols-query-prefix-frames-compose
   (implies (and (member-equal (proof-world-reg 6 before) '(16 24))
                 (symbols-query-setup-frame-p base before view)
                 (symbols-string-view-frame-p view dispatch)
                 (symbols-query-dispatch-frame-p base dispatch after))
            (symbols-query-dispatched-frame-p base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register
                             (highest 30) (register 0) (clobbers '(30)) (after view))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 28) (clobbers '(30)) (after view))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 6) (clobbers '(30)) (after view))
                  (:instance symbols-frame-gives-register
                             (highest 30) (register 6) (clobbers '(1 2 3))
                             (before view) (after dispatch))
                  (:instance symbols-read-only-frame-preserves-string-view-data
                             (first (symbols-query-saved-world before)) (last view))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(30)) (allowed '(1 2 3 30)) (after view))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(1 2 3)) (allowed '(1 2 3 30))
                             (before view) (after dispatch))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(1 2 30)) (allowed '(1 2 3 30)) (before dispatch))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers '(1 2 3 30))
                             (first before) (middle view) (last dispatch))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers '(1 2 3 30))
                             (first before) (middle dispatch) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-query-saved-world before)) (middle view) (last dispatch))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-query-saved-world before)) (middle dispatch) (last after)))
            :in-theory (disable symbols-string-payload symbols-string-hit-p
                                symbols-string-header-word)))
   :rule-classes nil))

(defthm symbols-run-query-prefix
  (implies (and (symbols-query-setup-pre-p code-base before)
                (member-equal (proof-world-reg 6 before) '(16 24))
                (symbols-query-setup-ready-p code-base before))
           (symbols-query-dispatched-frame-p code-base before (symbols-query-dispatched before)))
  :hints (("Goal"
           :use ((:instance symbols-run-query-setup)
                 (:instance symbols-run-string-view (before (symbols-query-view-entry before)))
                 (:instance symbols-run-query-dispatch (before (symbols-query-dispatch-entry before)))
                 (:instance symbols-query-view-and-dispatch-preconditions
                            (base code-base) (view (symbols-query-view-entry before))
                            (dispatch (symbols-query-dispatch-entry before)))
                 (:instance symbols-query-prefix-frames-compose
                            (base code-base) (view (symbols-query-view-entry before))
                            (dispatch (symbols-query-dispatch-entry before))
                            (after (symbols-query-dispatched before))))
           :in-theory (disable symbols-query-setup-frame-p symbols-string-view-frame-p
                               symbols-query-dispatch-frame-p symbols-query-dispatched-frame-p
                               symbols-query-dispatch-target symbols-run-query-setup
                               symbols-run-query-dispatch)))
  :rule-classes nil)

(defun symbols-query-lookup-bytes (name before)
  (if (symbols-query-string-argument-p before) name '(65 67 76 50)))

(defun symbols-query-search-fuel (rows byte-fuels before)
  (if (symbols-query-calls-finder-p before)
      (symbols-find-package-fuel rows byte-fuels (symbols-query-dispatched before))
    0))

(defun symbols-query-search-result (rows byte-fuels before)
  (proof-advance (symbols-query-search-fuel rows byte-fuels before)
                 (symbols-query-dispatched before)))

(defun symbols-query-search-ready-p (rows name byte-fuels base before)
  (let ((entry (symbols-query-dispatched before)))
    (implies (symbols-query-calls-finder-p before)
             (and (symbols-find-package-input-p rows (symbols-query-lookup-bytes name before) base entry)
                  (symbols-path-ready-p *symbols-find-setup-path* base
                                        (symbols-runtime-address "rt:find-package-loop" base) entry)
                  (symbols-find-scan-ready-p rows byte-fuels base
                                             (proof-advance (len *symbols-find-setup-path*) entry))))))

(defun symbols-query-row (rows name before)
  (let ((binding (assoc-equal (symbols-query-lookup-bytes name before) rows)))
    (if binding (cdr binding) 0)))

(defun symbols-query-after-search-p (rows name before entry after)
  (if (symbols-query-calls-finder-p before)
      (symbols-find-package-return-p rows (symbols-query-lookup-bytes name before) entry after)
    (equal after entry)))

(local
 (defthm symbols-query-zero-steps
   (equal (proof-advance 0 world) world)
   :hints (("Goal" :in-theory (enable proof-advance)))))

(defthm symbols-run-query-search
  (implies (symbols-query-search-ready-p rows name byte-fuels code-base before)
           (symbols-query-after-search-p rows name before (symbols-query-dispatched before)
                                         (symbols-query-search-result rows byte-fuels before)))
  :hints (("Goal"
           :use ((:instance symbols-run-find-package (before (symbols-query-dispatched before))
                            (query (symbols-query-lookup-bytes name before))))
           :in-theory (disable symbols-query-dispatched symbols-query-calls-finder-p
                               symbols-query-lookup-bytes symbols-find-package-input-p
                               symbols-find-package-fuel symbols-find-scan-ready-p
                               symbols-find-package-return-p)))
  :rule-classes nil)

(local
 (defthm symbols-query-sp-is-natural
   (natp (boymoo-model::a64-sp machine))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :type-prescription))

(local
 (defthm symbols-query-sp-fits-word
   (< (boymoo-model::a64-sp machine) (expt 2 64))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-sp)))
   :rule-classes :linear))

(defun symbols-query-saves-p (before after)
  (and (equal (symbols-stack-word 0 after) (proof-world-reg 0 before))
       (equal (symbols-stack-word 8 after) (proof-world-reg 6 before))
       (equal (symbols-stack-word 16 after) (proof-world-reg 29 before))
       (equal (symbols-stack-word 24 after) (proof-world-reg 30 before))))

(local
 (defthm symbols-query-saved-words
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine before)))
          (saved (symbols-query-saved-world before)))
     (implies (<= 32 sp)
              (and (equal (symbols-load-register-word (- sp 32) saved) (proof-world-reg 0 before))
                   (equal (symbols-load-register-word (- sp 24) saved) (proof-world-reg 6 before))
                   (equal (symbols-load-register-word (- sp 16) saved) (proof-world-reg 29 before))
                   (equal (symbols-load-register-word (- sp 8) saved) (proof-world-reg 30 before)))))
   :hints (("Goal" :in-theory (e/d (symbols-query-saved-world symbols-load-register-word
                                    proof-world-reg proof-reg boymoo-model::a64-read-reg)
                                   (proof-load-word))))))

(local
 (defthm symbols-query-register-word-from-same-memory
   (implies (equal (symbols-machine-memory first) (symbols-machine-memory last))
            (equal (symbols-load-register-word address first)
                   (symbols-load-register-word address last)))
   :hints (("Goal" :in-theory (enable symbols-load-register-word boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm symbols-query-dispatch-keeps-saves
   (implies (and (symbols-query-setup-pre-p base before)
                 (symbols-query-dispatched-frame-p base before dispatch))
            (symbols-query-saves-p before dispatch))
   :hints (("Goal"
            :use ((:instance symbols-query-saved-words)
                  (:instance symbols-query-register-word-from-same-memory
                             (first (symbols-query-saved-world before)) (last dispatch)
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 32)))
                  (:instance symbols-query-register-word-from-same-memory
                             (first (symbols-query-saved-world before)) (last dispatch)
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 24)))
                  (:instance symbols-query-register-word-from-same-memory
                             (first (symbols-query-saved-world before)) (last dispatch)
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 16)))
                  (:instance symbols-query-register-word-from-same-memory
                             (first (symbols-query-saved-world before)) (last dispatch)
                             (address (- (boymoo-model::a64-sp (proof-world-machine before)) 8))))
            :in-theory (e/d (symbols-stack-word symbols-no-memory-or-kernel-change-p)
                            (symbols-query-saved-words symbols-string-hit-p
                             symbols-string-header-word symbols-string-payload))))
   :rule-classes nil))

(local
 (defthm symbols-query-read-above-finder-saves
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine entry)))
          (address (+ sp offset)))
     (implies (and (<= 16 sp) (natp offset) (<= (+ address 8) (expt 2 64)))
              (equal (symbols-load-register-word address (symbols-saved-link-world entry))
                     (symbols-load-register-word address entry))))
   :hints (("Goal" :in-theory (e/d (symbols-load-register-word) (proof-load-word))))
   :rule-classes nil))

(local
 (defthm symbols-query-finder-retains-save
   (let* ((sp (boymoo-model::a64-sp (proof-world-machine entry)))
          (address (+ sp offset)))
     (implies (and (<= 16 sp) (natp offset) (<= (+ address 8) (expt 2 64))
                   (symbols-find-package-return-p rows bytes entry after))
              (equal (symbols-stack-word offset after) (symbols-stack-word offset entry))))
   :hints (("Goal"
            :use ((:instance symbols-query-read-above-finder-saves)
                  (:instance symbols-query-register-word-from-same-memory
                             (first (symbols-saved-link-world entry)) (last after)
                             (address (+ (boymoo-model::a64-sp (proof-world-machine entry)) offset))))
            :in-theory (e/d (symbols-stack-word symbols-no-memory-or-kernel-change-p)
                            (symbols-saved-link-world assoc-equal))))
   :rule-classes nil))

(local
 (defthm symbols-query-search-keeps-saves
   (implies (and (symbols-query-setup-pre-p base before)
                 (symbols-query-dispatched-frame-p base before entry)
                 (symbols-query-after-search-p rows name before entry found)
                 (implies (symbols-query-calls-finder-p before)
                          (<= 16 (boymoo-model::a64-sp (proof-world-machine entry)))))
            (symbols-query-saves-p before found))
   :hints (("Goal"
            :use ((:instance symbols-query-dispatch-keeps-saves (dispatch entry))
                  (:instance symbols-query-sp-fits-word (machine (proof-world-machine before)))
                  (:instance symbols-query-finder-retains-save (after found) (offset 0)
                             (bytes (symbols-query-lookup-bytes name before)))
                  (:instance symbols-query-finder-retains-save (after found) (offset 8)
                             (bytes (symbols-query-lookup-bytes name before)))
                  (:instance symbols-query-finder-retains-save (after found) (offset 16)
                             (bytes (symbols-query-lookup-bytes name before)))
                  (:instance symbols-query-finder-retains-save (after found) (offset 24)
                             (bytes (symbols-query-lookup-bytes name before))))
            :in-theory (disable symbols-query-calls-finder-p symbols-query-string-argument-p
                                symbols-query-lookup-bytes symbols-find-package-return-p)))
   :rule-classes nil))

(defconst *symbols-query-clobbers* '(0 1 2 3 4 5 6 7 8 9))
(defconst *symbols-query-link-clobbers* '(0 1 2 3 4 5 6 7 8 9 30))

(defun symbols-query-stack-effects (before entry)
  (if (symbols-query-calls-finder-p before)
      (symbols-saved-link-world entry)
    (symbols-query-saved-world before)))

(defun symbols-query-search-frame-p (rows name base before entry found)
  (let* ((string-arg (symbols-query-string-argument-p before))
         (witness (equal (proof-world-reg 6 before) 24))
         (query (symbols-runtime-address "rt:package-query" base)))
    (and (not (proof-world-stop found))
         (not (eq (car (proof-world-machine found)) :svc))
         (equal (proof-world-pc found) (+ query (cond (string-arg 60) (witness 36) (t 48))))
         (implies (symbols-query-calls-finder-p before)
                  (equal (proof-world-reg 0 found) (symbols-query-row rows name before)))
         (equal (boymoo-model::a64-sp (proof-world-machine found))
                (- (boymoo-model::a64-sp (proof-world-machine before)) 32))
         (proof-register-frame-p 30 *symbols-query-link-clobbers* before found)
         (symbols-no-memory-or-kernel-change-p (symbols-query-stack-effects before entry) found))))

(local
 (defthm symbols-query-combine-search-frames
   (implies (and (member-equal (proof-world-reg 6 before) '(16 24))
                 (symbols-query-dispatched-frame-p base before entry)
                 (symbols-query-after-search-p rows name before entry found))
            (symbols-query-search-frame-p rows name base before entry found))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(1 2 3 30)) (allowed *symbols-query-link-clobbers*) (after entry))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers *symbols-find-package-clobbers*) (allowed *symbols-query-link-clobbers*)
                             (before entry) (after found))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-query-link-clobbers*)
                             (first before) (middle entry) (last found)))
            :in-theory (disable symbols-query-string-argument-p symbols-query-lookup-bytes
                                symbols-saved-link-world assoc-equal)))
   :rule-classes nil))

(defun symbols-query-tail-path (before found)
  (if (symbols-query-string-argument-p before)
      (symbols-query-string-continuation found)
    (symbols-query-default-path (equal (proof-world-reg 6 before) 24) found)))

(defun symbols-query-tail-target (base before found)
  (if (symbols-query-string-argument-p before)
      (symbols-query-string-target base found)
    (symbols-query-default-target (equal (proof-world-reg 6 before) 24) base found)))

(defun symbols-query-tail-frame-p (base before found after)
  (if (symbols-query-string-argument-p before)
      (symbols-query-string-frame-p base found after)
    (symbols-query-default-frame-p (equal (proof-world-reg 6 before) 24) base found after)))

(defthm symbols-run-query-tail
  (implies (and (symbols-runtime-base-p code-base)
                (member-equal (proof-world-reg 6 before) '(16 24))
                (symbols-query-search-frame-p rows name code-base before entry found)
                (symbols-query-saves-p before found)
                (symbols-path-ready-p (symbols-query-tail-path before found) code-base
                                      (symbols-query-tail-target code-base before found) found))
           (symbols-query-tail-frame-p code-base before found
                                       (proof-advance (len (symbols-query-tail-path before found))
                                                      found)))
  :hints (("Goal"
           :use ((:instance symbols-query-sp-fits-word (machine (proof-world-machine before)))
                 (:instance symbols-run-query-string-continuation (before found))
                 (:instance symbols-run-query-default (before found)
                            (witness (equal (proof-world-reg 6 before) 24))))
           :in-theory (disable symbols-query-string-argument-p symbols-query-lookup-bytes
                               symbols-saved-link-world assoc-equal
                               symbols-run-query-string-continuation symbols-run-query-default
                               symbols-query-string-frame-p symbols-query-default-frame-p
                               symbols-query-string-target symbols-query-default-target)))
  :rule-classes nil)

(defun symbols-query-outcome (row before memory)
  (let ((offset (proof-world-reg 6 before)))
    (cond ((symbols-query-string-argument-p before)
           (if (and (not (equal row 0))
                    (not (equal (symbols-load-register-word (+ row 24) memory) *proof-nil*)))
               (mv nil (symbols-load-register-word (+ row offset) memory))
             (mv (if (equal offset 16) "rt:imports-absent" "rt:witness-absent")
                 (proof-world-reg 0 before))))
          ((equal offset 16) (mv nil *proof-nil*))
          ((equal row 0) (mv "rt:missing-acl2" 0))
          (t (mv nil (symbols-load-register-word (+ row 24) memory))))))

(defun symbols-package-query-frame-p (rows name base before entry after)
  (let ((memory (symbols-query-stack-effects before entry)))
    (mv-let (diagnostic word)
      (symbols-query-outcome (symbols-query-row rows name before) before memory)
      (and (not (proof-world-stop after))
           (equal (proof-world-reg 0 after) word)
           (if diagnostic
               (and (equal (proof-world-pc after) (symbols-runtime-address diagnostic base))
                    (equal (boymoo-model::a64-sp (proof-world-machine after))
                           (- (boymoo-model::a64-sp (proof-world-machine before)) 32)))
             (proof-frame-return-p *symbols-query-clobbers* t before after))
           (symbols-no-memory-or-kernel-change-p memory after)))))

(local
 (defthm symbols-query-finished-registers
   (implies (and (proof-register-frame-p 30 *symbols-query-link-clobbers* before found)
                 (if string-arg
                     (proof-register-frame-p 30 '(0 1 5 6 29 30) found after)
                   (proof-register-frame-p 30 '(0 29 30) found after))
                 (equal (proof-world-reg 29 before) (proof-world-reg 29 after))
                 (equal (proof-world-reg 30 before) (proof-world-reg 30 after)))
            (proof-register-frame-p 30 *symbols-query-clobbers* before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers *symbols-query-link-clobbers*)
                             (allowed '(0 1 2 3 4 5 6 7 8 9 29 30)) (after found))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0 1 5 6 29 30))
                             (allowed '(0 1 2 3 4 5 6 7 8 9 29 30)) (before found))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0 29 30))
                             (allowed '(0 1 2 3 4 5 6 7 8 9 29 30)) (before found))
                  (:instance symbols-frame-is-transitive (highest 30)
                             (clobbers '(0 1 2 3 4 5 6 7 8 9 29 30))
                             (first before) (middle found) (last after))
                  (:instance symbols-frame-keeps-restored-register (highest 30) (register 29)
                             (clobbers '(0 1 2 3 4 5 6 7 8 9 29 30)))
                  (:instance symbols-frame-keeps-restored-register (highest 30) (register 30)
                             (clobbers *symbols-query-link-clobbers*)))))
   :rule-classes nil))

(local
 (defthm symbols-query-tail-returns-expected-word
   (implies (and (symbols-query-setup-pre-p base before)
                 (member-equal (proof-world-reg 6 before) '(16 24))
                 (symbols-query-search-frame-p rows name base before entry found)
                 (symbols-query-saves-p before found)
                 (symbols-query-tail-frame-p base before found after))
            (symbols-package-query-frame-p rows name base before entry after))
   :hints (("Goal"
            :use ((:instance symbols-query-register-word-from-same-memory
                             (first (symbols-query-stack-effects before entry)) (last found)
                             (address (+ (symbols-query-row rows name before) 24)))
                  (:instance symbols-query-register-word-from-same-memory
                             (first (symbols-query-stack-effects before entry)) (last found)
                             (address (+ (symbols-query-row rows name before) 16)))
                  (:instance symbols-query-finished-registers
                             (string-arg (symbols-query-string-argument-p before)))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first (symbols-query-stack-effects before entry))
                             (middle found) (last after)))
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p)
                            (symbols-query-stack-effects symbols-query-string-argument-p
                             symbols-query-row assoc-equal))))
   :rule-classes nil))

(defthm symbols-run-package-query
  (let* ((entry (symbols-query-dispatched before))
         (found (symbols-query-search-result rows byte-fuels before))
         (path (symbols-query-tail-path before found))
         (after (proof-advance (len path) found)))
    (implies (and (symbols-query-setup-pre-p code-base before)
                  (member-equal (proof-world-reg 6 before) '(16 24))
                  (symbols-query-setup-ready-p code-base before)
                  (symbols-query-search-ready-p rows name byte-fuels code-base before)
                  (symbols-path-ready-p path code-base
                                        (symbols-query-tail-target code-base before found) found))
             (symbols-package-query-frame-p rows name code-base before entry after)))
  :hints (("Goal"
           :use ((:instance symbols-run-query-prefix)
                 (:instance symbols-run-query-search)
                 (:instance symbols-query-search-keeps-saves (base code-base)
                            (entry (symbols-query-dispatched before))
                            (found (symbols-query-search-result rows byte-fuels before)))
                 (:instance symbols-query-combine-search-frames (base code-base)
                            (entry (symbols-query-dispatched before))
                            (found (symbols-query-search-result rows byte-fuels before)))
                 (:instance symbols-run-query-tail (entry (symbols-query-dispatched before))
                            (found (symbols-query-search-result rows byte-fuels before)))
                 (:instance symbols-query-tail-returns-expected-word (base code-base)
                            (entry (symbols-query-dispatched before))
                            (found (symbols-query-search-result rows byte-fuels before))
                            (after (proof-advance
                                    (len (symbols-query-tail-path
                                          before (symbols-query-search-result rows byte-fuels before)))
                                    (symbols-query-search-result rows byte-fuels before)))))
           :in-theory (disable symbols-query-dispatched symbols-query-search-result
                               symbols-query-dispatched-frame-p symbols-query-setup-ready-p
                               symbols-query-after-search-p symbols-query-saves-p
                               symbols-query-tail-path symbols-query-tail-target symbols-query-tail-frame-p
                               symbols-query-search-frame-p symbols-package-query-frame-p
                               symbols-query-string-argument-p symbols-query-calls-finder-p
                               symbols-find-scan-ready-p symbols-find-rows-p)))
  :rule-classes nil)

(defun symbols-package-query-finish (rows byte-fuels before)
  (let ((found (symbols-query-search-result rows byte-fuels before)))
    (proof-advance (len (symbols-query-tail-path before found)) found)))

(defun symbols-package-query-ready-p (rows name byte-fuels base before)
  (let ((found (symbols-query-search-result rows byte-fuels before)))
    (and (symbols-query-setup-ready-p base before)
         (symbols-query-search-ready-p rows name byte-fuels base before)
         (symbols-path-ready-p (symbols-query-tail-path before found) base
                               (symbols-query-tail-target base before found) found))))

(defun symbols-public-query-body (witness before)
  (proof-advance (len (symbols-query-wrapper-path witness)) before))

(defun symbols-query-diagnostic (rows name before entry)
  (mv-let (diagnostic word)
    (symbols-query-outcome (symbols-query-row rows name before) before
                           (symbols-query-stack-effects before entry))
    (declare (ignore word))
    diagnostic))

(local
 (defthm symbols-query-wrapper-enters-body
   (implies (and (symbols-query-wrapper-pre-p witness base before)
                 (symbols-query-wrapper-frame-p witness base before body)
                 (<= 32 (boymoo-model::a64-sp (proof-world-machine before))))
            (and (symbols-query-setup-pre-p base body)
                 (member-equal (proof-world-reg 6 body) '(16 24))))))

(local
 (defthm symbols-query-wrapper-and-body-return-frame
   (implies (and (symbols-query-wrapper-pre-p witness base before)
                 (symbols-query-wrapper-frame-p witness base before body)
                 (symbols-package-query-frame-p rows name base body entry after)
                 (not (symbols-query-diagnostic rows name body entry)))
            (proof-frame-return-p *symbols-query-clobbers* t before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register
                             (highest 30) (register 30) (clobbers '(6)) (after body))
                  (:instance symbols-frame-allows-more-clobbers
                             (highest 30) (clobbers '(6))
                             (allowed *symbols-query-clobbers*) (after body))
                  (:instance symbols-frame-is-transitive
                             (highest 30) (clobbers *symbols-query-clobbers*)
                             (first before) (middle body) (last after)))
            :in-theory (disable symbols-query-outcome symbols-query-stack-effects
                                symbols-query-row)))
   :rule-classes nil))

(defthm symbols-run-public-package-query
  (let* ((path (symbols-query-wrapper-path witness))
         (body (symbols-public-query-body witness before))
         (entry (symbols-query-dispatched body))
         (after (symbols-package-query-finish rows byte-fuels body)))
    (implies (and (symbols-query-wrapper-pre-p witness code-base before)
                  (<= 32 (boymoo-model::a64-sp (proof-world-machine before)))
                  (symbols-path-ready-p path code-base
                                        (symbols-runtime-address "rt:package-query" code-base)
                                        before)
                  (symbols-package-query-ready-p rows name byte-fuels code-base body))
             (and (symbols-package-query-frame-p rows name code-base body entry after)
                  (equal (proof-world-reg 6 body) (if witness 24 16))
                  (equal (proof-world-reg 0 body) (proof-world-reg 0 before))
                  (symbols-no-memory-or-kernel-change-p before body)
                  (implies (not (symbols-query-diagnostic rows name body entry))
                           (proof-frame-return-p *symbols-query-clobbers* t before after)))))
  :hints (("Goal"
           :use ((:instance symbols-run-query-wrapper)
                 (:instance symbols-query-wrapper-enters-body
                            (base code-base) (body (symbols-public-query-body witness before)))
                 (:instance symbols-run-package-query
                            (before (symbols-public-query-body witness before)))
                 (:instance symbols-frame-gives-register
                            (highest 30) (register 0) (clobbers '(6))
                            (after (symbols-public-query-body witness before)))
                 (:instance symbols-query-wrapper-and-body-return-frame
                            (base code-base) (body (symbols-public-query-body witness before))
                            (entry (symbols-query-dispatched (symbols-public-query-body witness before)))
                            (after (symbols-package-query-finish
                                    rows byte-fuels (symbols-public-query-body witness before)))))
           :in-theory (disable symbols-run-query-wrapper symbols-query-wrapper-path
                               symbols-query-outcome symbols-query-diagnostic
                               symbols-query-stack-effects symbols-query-row
                               symbols-package-query-frame-p symbols-query-setup-pre-p
                               symbols-query-wrapper-pre-p symbols-query-dispatched
                               symbols-query-search-result symbols-query-tail-path
                               symbols-query-tail-target)))
  :rule-classes nil)

; A package row is located by its name bytes. A visible row stores
; words for its imports and witness. A hidden row has a NIL witness
; word, and an absent name has row address zero.
(defun symbols-query-data-agreement-p (primitive datum packages rows name before entry objects)
  (let* ((memory (symbols-query-stack-effects before entry))
         (address (symbols-query-row rows name before))
         (offset (symbols-query-field primitive))
         (row (assoc-equal (if (stringp datum) datum "ACL2") packages)))
    (and (equal (proof-world-reg 6 before) offset)
         (equal (proof-heap-base memory) (proof-heap-base before))
         (iff (symbols-query-string-argument-p before) (stringp datum))
         (cond ((stringp datum)
                (and (iff (equal address 0) (not row))
                     (implies row
                              (iff (equal (symbols-load-register-word (+ address 24) memory)
                                          *proof-nil*)
                                   (not (proof-package-visible row))))
                     (implies (proof-package-visible row)
                              (proof-machine-value-p
                               (symbols-load-register-word (+ address offset) memory)
                               (symbols-query-row-value primitive row) memory objects packages))))
               ((eq primitive 'acl2::pkg-imports)
                (proof-machine-value-p *proof-nil* nil memory objects packages))
               (t (and (not (equal address 0))
                       (proof-machine-value-p
                        (symbols-load-register-word (+ address 24) memory)
                        (proof-package-witness row) memory objects packages)))))))

(defthm symbols-package-query-result-implements-core
  (let* ((result (boymoo-model::core-primitive primitive (list datum) program))
         (memory (symbols-query-stack-effects before entry)))
    (implies (and (member-eq primitive '(acl2::pkg-imports acl2::pkg-witness))
                  (proof-program-packages-p program packages)
                  (symbols-query-data-agreement-p primitive datum packages
                                                  rows name before entry objects)
                  (symbols-package-query-frame-p rows name code-base before entry after))
             (if (boymoo-model::core-value-p result)
                 (and (not (symbols-query-diagnostic rows name before entry))
                      (proof-frame-return-p *symbols-query-clobbers* t before after)
                      (proof-machine-value-p (proof-world-reg 0 after)
                                             (boymoo-model::core-datum result)
                                             memory objects packages))
               (and (equal result :no-value)
                    (equal (proof-world-pc after)
                           (symbols-runtime-address
                            (if (eq primitive 'acl2::pkg-imports)
                                "rt:imports-absent" "rt:witness-absent")
                            code-base))
                    (equal (proof-world-reg 0 after) (proof-world-reg 0 before))))))
  :hints (("Goal"
           :use ((:instance symbols-package-query-implements-core))
           :in-theory (disable symbols-package-query-implements-core
                               proof-program-packages-p proof-machine-value-p proof-frame-return-p
                               symbols-query-stack-effects symbols-query-row
                               symbols-query-string-argument-p assoc-equal)))
  :rule-classes nil)

(local
 (defthm symbols-query-value-in-returned-world
   (implies (and (proof-frame-return-p *symbols-query-clobbers* t before after)
                 (equal (proof-heap-base memory) (proof-heap-base before))
                 (symbols-no-memory-or-kernel-change-p memory after)
                 (proof-machine-value-p (proof-world-reg 0 after) value memory objects packages))
            (proof-reg-value-p 0 value after objects packages))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers *symbols-query-clobbers*))
                  (:instance symbols-view-depends-on-memory
                             (word (proof-world-reg 0 after)) (base (proof-heap-base before))
                             (first (proof-world-machine memory)) (last (proof-world-machine after))))
            :in-theory (e/d (proof-heap-base symbols-no-memory-or-kernel-change-p)
                            (proof-view))))
   :rule-classes nil))

(defthm symbols-query-core-value-in-returned-world
  (let ((result (boymoo-model::core-primitive primitive (list datum) program)))
    (implies (and (member-eq primitive '(acl2::pkg-imports acl2::pkg-witness))
                  (boymoo-model::core-value-p result)
                  (proof-program-packages-p program packages)
                  (symbols-query-data-agreement-p primitive datum packages rows name before entry objects)
                  (symbols-package-query-frame-p rows name code-base before entry after))
             (and (not (symbols-query-diagnostic rows name before entry))
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after objects packages))))
  :hints (("Goal"
           :use ((:instance symbols-package-query-result-implements-core)
                 (:instance symbols-query-value-in-returned-world
                            (value (boymoo-model::core-datum
                                    (boymoo-model::core-primitive primitive (list datum) program)))
                            (memory (symbols-query-stack-effects before entry))))
           :in-theory (disable proof-frame-return-p proof-reg-value-p proof-machine-value-p
                               proof-program-packages-p symbols-query-diagnostic symbols-query-outcome
                               symbols-query-stack-effects symbols-query-row symbols-query-string-argument-p
                               assoc-equal)))
  :rule-classes nil)

(defthm symbols-public-package-query-contract
  (let* ((caller-path (symbols-query-wrapper-path witness))
         (primitive (if witness 'acl2::pkg-witness 'acl2::pkg-imports))
         (body (symbols-public-query-body witness before))
         (entry (symbols-query-dispatched body))
         (after (symbols-package-query-finish rows byte-fuels body))
         (result (boymoo-model::core-primitive primitive (list datum) program)))
    (implies (and (symbols-query-wrapper-pre-p witness code-base before)
                  (<= 32 (boymoo-model::a64-sp (proof-world-machine before)))
                  (symbols-path-ready-p caller-path code-base
                                        (symbols-runtime-address "rt:package-query" code-base) before)
                  (symbols-package-query-ready-p rows name byte-fuels code-base body)
                  (proof-runtime-pre-p primitive (list datum) program *symbols-runtime-labels*
                                       code-base before objects packages)
                  (proof-program-packages-p program packages)
                  (symbols-query-data-agreement-p primitive datum packages rows name body entry objects)
                  (boymoo-model::core-value-p result)
                  (proof-preserved-heap-p nil before after objects objects packages)
                  (proof-fixed-heap-p before after objects))
             (proof-runtime-return-p primitive (list datum) program before after objects objects packages)))
  :hints (("Goal"
           :use ((:instance symbols-run-public-package-query)
                 (:instance symbols-query-core-value-in-returned-world
                            (primitive (if witness 'acl2::pkg-witness 'acl2::pkg-imports))
                            (before (symbols-public-query-body witness before))
                            (entry (symbols-query-dispatched (symbols-public-query-body witness before)))
                            (after (symbols-package-query-finish
                                    rows byte-fuels (symbols-public-query-body witness before)))))
           :in-theory (disable boymoo-model::core-primitive proof-reg-value-p proof-machine-value-p
                               proof-runtime-pre-p proof-program-packages-p proof-preserved-heap-p proof-fixed-heap-p
                               proof-frame-return-p symbols-query-diagnostic symbols-package-query-frame-p
                               symbols-query-data-agreement-p symbols-package-query-ready-p
                               symbols-package-query-finish symbols-query-dispatched
                               symbols-query-wrapper-path symbols-query-wrapper-pre-p)))
  :rule-classes nil)
