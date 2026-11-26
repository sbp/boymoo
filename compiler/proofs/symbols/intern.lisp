(in-package "BOYMOO-PROOFS")

(include-book "loops")
(include-book "memory")
(include-book "table")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                     (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg proof-heap-base
                     proof-advance proof-advance-append proof-segment-p proof-byte-list
                     boymoo-model::a64-unsigned symbols-runtime-offset
                     symbols-no-memory-or-kernel-change-p symbols-path-ready-p
                     symbols-load-register-word symbols-stack-word
                     symbols-logical-right-shift-bits symbols-intern-name-equality-path
                     symbols-intern-scan-path symbols-intern-match-path)))

(local
 (defthm symbols-intern-word-register-bound
   (< (proof-world-reg register world) (expt 2 64))
   :hints (("Goal" :in-theory (enable proof-world-reg proof-reg boymoo-model::a64-read-reg)))
   :rule-classes :linear))

(defthm symbols-intern-combined-hash-agrees
  (implies (and (natp number) (< number (expt 2 63))
                (equal (proof-world-reg 20 before) (+ 1 (* 2 number)))
                (equal (proof-world-reg 3 before)
                       (symbols-machine-name-hash (coerce name 'list) 0)))
           (equal (symbols-intern-combined-hash before) (symbols-machine-key-hash number name)))
  :hints (("Goal"
           :use ((:instance symbols-logical-right-shift-correct (word (proof-world-reg 20 before))
                            (amount 1))
                 (:instance symbols-floor-of-decomposition (q number) (r 1) (divisor 2))
                 (:instance symbols-intern-word-register-bound (register 20) (world before)))
           :in-theory (disable symbols-machine-key-hash-agrees symbols-machine-name-hash-agrees
                               symbols-floor-of-decomposition floor symbols-machine-name-hash)))
  :rule-classes nil)

(defthm symbols-intern-bucket-frame-agrees-with-key
  (implies (and (natp number) (< number (expt 2 63))
                (equal (proof-world-reg 20 before) (+ 1 (* 2 number)))
                (equal (proof-world-reg 3 before)
                       (symbols-machine-name-hash (coerce name 'list) 0))
                (symbols-intern-bucket-frame-p code-base before after))
           (and (equal (proof-world-reg 3 after) (proof-symbol-hash number name 12))
                (equal (proof-world-reg 9 after)
                       (proof-integer-word
                        (boymoo-model::a64-signed 63 (proof-symbol-hash number name 63))))))
  :hints (("Goal"
           :use ((:instance symbols-intern-combined-hash-agrees)
                 (:instance symbols-machine-static-hash)
                 (:instance symbols-machine-tagged-hash))
           :in-theory (disable symbols-machine-key-hash symbols-machine-key-hash-agrees
                               symbols-machine-name-hash symbols-intern-combined-hash
                               symbols-intern-static-slot symbols-machine-static-hash
                               symbols-machine-tagged-hash proof-hash-characters proof-integer-word
                               boymoo-model::a64-signed acl2::binary-logand)))
  :rule-classes nil)

(defun symbols-intern-name-key-matches-p (word address size world)
  (let* ((header (symbols-box-address word (proof-heap-base world)))
         (length (symbols-logical-right-shift-bits (symbols-load-register-word header world) 8))
         (payload (boymoo-model::a64-unsigned 64 (+ header 8)))
         (machine (proof-world-machine world)))
    (and (equal length size)
         (equal (proof-byte-list size payload machine) (proof-byte-list size address machine)))))

(defun symbols-intern-comparison-entry (before)
  (proof-advance (len (symbols-intern-name-equality-path before)) before))

(defun symbols-intern-compared (byte-fuel before)
  (let ((steps (if (symbols-intern-name-length-miss-p before) (len *symbols-bytes-differ-path*)
                 (nfix byte-fuel))))
    (proof-advance steps (symbols-intern-comparison-entry before))))

(defun symbols-intern-compare-ready-p (byte-fuel base before)
  (let ((entry (symbols-intern-comparison-entry before)))
    (and (symbols-path-ready-p (symbols-intern-name-equality-path before) base
                               (symbols-intern-name-equality-target base before) before)
         (if (symbols-intern-name-length-miss-p before)
             (symbols-path-ready-p *symbols-bytes-differ-path* base (proof-world-reg 30 entry) entry)
           (symbols-byte-equality-return-p entry (symbols-intern-compared byte-fuel before))))))

(defun symbols-intern-compare-return-p (before after)
  (and (proof-frame-return-p '(0 1 2 3 4) t before after)
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-reg 0 after)
              (if (symbols-intern-name-key-matches-p (proof-world-reg 0 before) (proof-world-reg 8 before)
                                                     (proof-world-reg 21 before) before)
                  1
                0))
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-intern-compare-bytes-of-same-memory
   (implies (and (symbols-intern-name-equality-frame-p base before entry)
                 (not (symbols-intern-name-length-miss-p before))
                 (symbols-byte-equality-return-p entry after))
            (equal (proof-world-reg 0 after)
                   (if (symbols-intern-name-key-matches-p (proof-world-reg 0 before) (proof-world-reg 8 before)
                                                          (proof-world-reg 21 before) before)
                       1
                     0)))
   :hints (("Goal"
            :use ((:instance symbols-byte-list-depends-on-memory
                             (size (proof-world-reg 21 before)) (address (proof-world-reg 8 before))
                             (first (proof-world-machine entry)) (last (proof-world-machine before)))
                  (:instance symbols-byte-list-depends-on-memory
                             (size (proof-world-reg 21 before))
                             (address (boymoo-model::a64-unsigned 64
                                        (+ 8 (symbols-intern-candidate-string before))))
                             (first (proof-world-machine entry)) (last (proof-world-machine before))))
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p) (proof-frame-return-p))))
   :rule-classes nil))

(local
 (defthm symbols-intern-compare-frames-compose
   (implies (and (not (proof-world-stop before))
                 (symbols-intern-name-equality-frame-p base before entry)
                 (if (symbols-intern-name-length-miss-p before)
                     (and (proof-frame-return-p '(0) nil entry after)
                          (not (eq (car (proof-world-machine after)) :svc))
                          (equal (proof-world-reg 0 after) 0)
                          (symbols-no-memory-or-kernel-change-p entry after))
                   (symbols-byte-equality-return-p entry after)))
            (symbols-intern-compare-return-p before after))
   :hints (("Goal"
            :use ((:instance symbols-intern-compare-bytes-of-same-memory)
                  (:instance symbols-frame-gives-register (highest 30) (register 30)
                             (clobbers '(0 1 2)) (after entry))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0 1 2)) (allowed '(0 1 2 3 4)) (after entry))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0)) (allowed '(0 1 2 3 4)) (before entry))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers '(0 1 2 3 4))
                             (first before) (middle entry) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first before) (middle entry) (last after)))))
   :rule-classes nil))

(defthm symbols-run-intern-name-check
  (implies (and (symbols-intern-name-equality-pre-p code-base before)
                (symbols-intern-compare-ready-p byte-fuel code-base before))
           (symbols-intern-compare-return-p before (symbols-intern-compared byte-fuel before)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-name-equality)
                 (:instance symbols-run-bytes-differ (before (symbols-intern-comparison-entry before)))
                 (:instance symbols-intern-compare-frames-compose (base code-base)
                            (entry (symbols-intern-comparison-entry before))
                            (after (symbols-intern-compared byte-fuel before))))
           :in-theory (disable symbols-intern-name-length-miss-p symbols-intern-compare-return-p
                               symbols-byte-equality-return-p
                               symbols-intern-candidate-length)))
  :rule-classes nil)

(defun symbols-intern-scanned-key-matches-p (dynamic world)
  (and (symbols-intern-scan-calls-compare-p dynamic world)
       (symbols-intern-name-key-matches-p
        (car (cddddr (symbols-intern-scan-fields dynamic world)))
        (proof-world-reg 8 world) (proof-world-reg 21 world) world)))

(defun symbols-intern-scan-probe (dynamic before)
  (proof-advance (len (symbols-intern-scan-path dynamic before)) before))

(defun symbols-intern-scan-checked (dynamic byte-fuel before)
  (symbols-intern-compared byte-fuel (symbols-intern-scan-probe dynamic before)))

(defun symbols-intern-scan-step-finish (dynamic byte-fuel before)
  (if (symbols-intern-scan-calls-compare-p dynamic before)
      (let ((compared (symbols-intern-scan-checked dynamic byte-fuel before)))
        (proof-advance (len (symbols-intern-match-path dynamic compared)) compared))
    (symbols-intern-scan-probe dynamic before)))

(defun symbols-intern-scan-step-ready-p (dynamic byte-fuel base before)
  (and (symbols-path-ready-p (symbols-intern-scan-path dynamic before) base nil before)
       (implies (symbols-intern-scan-calls-compare-p dynamic before)
                (let ((probe (symbols-intern-scan-probe dynamic before))
                      (compared (symbols-intern-scan-checked dynamic byte-fuel before)))
                  (and (symbols-intern-compare-ready-p byte-fuel base probe)
                       (symbols-path-ready-p (symbols-intern-match-path dynamic compared) base
                                             (symbols-intern-match-target dynamic base compared)
                                             compared))))))

(defconst *symbols-intern-scan-clobbers* '(0 1 2 3 4 5 6 22 30))

(defun symbols-intern-scan-step-frame-p (dynamic base before after)
  (let ((end (symbols-intern-scan-empty-p before))
        (match (symbols-intern-scanned-key-matches-p dynamic before))
        (fields (symbols-intern-scan-fields dynamic before)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after)
                (symbols-runtime-address
                 (cond (end (if dynamic "rt:intern-create" "rt:intern-dynamic-start"))
                       (match "rt:intern-return")
                       (t (symbols-intern-scan-label dynamic)))
                 base))
         (equal (proof-world-reg 22 after) (if end *proof-nil* (car fields)))
         (implies match (equal (proof-world-reg 0 after) (cadr fields)))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 *symbols-intern-scan-clobbers* before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-intern-name-key-of-same-memory
   (implies (and (equal (symbols-machine-memory first) (symbols-machine-memory last))
                 (equal (proof-heap-base first) (proof-heap-base last)))
            (equal (symbols-intern-name-key-matches-p word address size first)
                   (symbols-intern-name-key-matches-p word address size last)))
   :hints (("Goal"
            :use ((:instance symbols-byte-list-depends-on-memory
                             (first (proof-world-machine first)) (last (proof-world-machine last)))
                  (:instance symbols-byte-list-depends-on-memory
                             (address (boymoo-model::a64-unsigned
                                        64 (+ 8 (symbols-box-address word (proof-heap-base first)))))
                             (first (proof-world-machine first)) (last (proof-world-machine last))))
            :in-theory (enable symbols-load-register-word boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm symbols-intern-checked-key-matches-probe
   (implies (and (symbols-intern-scan-calls-compare-p dynamic before)
                 (symbols-intern-scan-frame-p dynamic base before probe)
                 (symbols-intern-compare-return-p probe compared))
            (equal (proof-world-reg 0 compared)
                   (if (symbols-intern-scanned-key-matches-p dynamic before) 1 0)))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 8)
                             (clobbers '(0 4 5 6 22 30)) (after probe))
                  (:instance symbols-frame-gives-register (highest 30) (register 21)
                             (clobbers '(0 4 5 6 22 30)) (after probe))
                  (:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers '(0 4 5 6 22 30)) (after probe))
                  (:instance symbols-intern-name-key-of-same-memory
                             (word (car (cddddr (symbols-intern-scan-fields dynamic before))))
                             (address (proof-world-reg 8 before)) (size (proof-world-reg 21 before))
                             (first before) (last probe)))
            :in-theory (e/d (proof-heap-base symbols-no-memory-or-kernel-change-p)
                            (symbols-intern-scan-fields symbols-intern-name-key-matches-p
                             symbols-intern-scan-calls-compare-p proof-frame-return-p))))
   :rule-classes nil))

(local
 (defthm symbols-intern-scan-match-frames
   (implies (and (symbols-intern-scan-calls-compare-p dynamic before)
                 (symbols-intern-scan-frame-p dynamic base before probe)
                 (symbols-intern-compare-return-p probe compared)
                 (symbols-intern-match-frame-p dynamic base compared after))
            (symbols-intern-scan-step-frame-p dynamic base before after))
   :hints (("Goal"
            :use ((:instance symbols-intern-checked-key-matches-probe)
                  (:instance symbols-frame-gives-register (highest 30) (register 22)
                             (clobbers '(0 1 2 3 4)) (before probe) (after compared))
                  (:instance symbols-frame-gives-register (highest 30) (register 5)
                             (clobbers '(0 1 2 3 4)) (before probe) (after compared))
                  (:instance symbols-frame-gives-register (highest 30) (register 22)
                             (clobbers '(0)) (before compared))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0 4 5 6 22 30)) (allowed *symbols-intern-scan-clobbers*) (after probe))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0 1 2 3 4)) (allowed *symbols-intern-scan-clobbers*)
                             (before probe) (after compared))
                  (:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0)) (allowed *symbols-intern-scan-clobbers*) (before compared))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-intern-scan-clobbers*)
                             (first before) (middle probe) (last compared))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-intern-scan-clobbers*)
                             (first before) (middle compared) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first before) (middle probe) (last compared))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first before) (middle compared) (last after)))
            :in-theory (disable symbols-intern-scan-fields symbols-intern-name-key-matches-p
                                symbols-intern-scan-package-match-p symbols-intern-scan-hash-mismatch-p)))
   :rule-classes nil))

(local
 (defthm symbols-intern-scan-skip-frames
   (implies (and (not (symbols-intern-scan-calls-compare-p dynamic before))
                 (symbols-intern-scan-frame-p dynamic base before after))
            (symbols-intern-scan-step-frame-p dynamic base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers (highest 30)
                             (clobbers '(0 4 5 6 22 30)) (allowed *symbols-intern-scan-clobbers*)))
            :in-theory (disable symbols-intern-scan-fields symbols-intern-scan-calls-compare-p)))
   :rule-classes nil))

(local
 (defthm symbols-intern-check-and-match
   (let* ((compared (symbols-intern-compared byte-fuel probe))
          (path (symbols-intern-match-path dynamic compared)))
     (implies (and (symbols-runtime-base-p base)
                   (symbols-intern-scan-calls-compare-p dynamic before)
                   (symbols-intern-scan-frame-p dynamic base before probe)
                   (symbols-intern-compare-ready-p byte-fuel base probe)
                   (symbols-path-ready-p path base (symbols-intern-match-target dynamic base compared) compared))
              (and (symbols-intern-compare-return-p probe compared)
                   (symbols-intern-match-frame-p dynamic base compared
                                                 (proof-advance (len path) compared)))))
   :hints (("Goal"
            :use ((:instance symbols-run-intern-name-check (code-base base) (before probe))
                  (:instance symbols-run-intern-match (code-base base) (before (symbols-intern-compared byte-fuel probe))))
            :in-theory (disable symbols-intern-scan-fields symbols-intern-name-key-matches-p
                                symbols-intern-compare-ready-p symbols-intern-compared
                                symbols-intern-match-frame-p symbols-intern-match-target
                                symbols-intern-scan-package-match-p symbols-intern-scan-hash-mismatch-p)))
   :rule-classes nil))

(defthm symbols-run-intern-scan-step
  (implies (and (symbols-intern-scan-start-p dynamic code-base before)
                (symbols-intern-scan-step-ready-p dynamic byte-fuel code-base before))
           (symbols-intern-scan-step-frame-p dynamic code-base before
                                             (symbols-intern-scan-step-finish dynamic byte-fuel before)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-scan-iteration)
                 (:instance symbols-intern-check-and-match (base code-base)
                            (probe (symbols-intern-scan-probe dynamic before)))
                 (:instance symbols-intern-scan-match-frames (base code-base)
                            (probe (symbols-intern-scan-probe dynamic before))
                            (compared (symbols-intern-scan-checked dynamic byte-fuel before))
                            (after (symbols-intern-scan-step-finish dynamic byte-fuel before)))
                 (:instance symbols-intern-scan-skip-frames (base code-base)
                            (after (symbols-intern-scan-probe dynamic before))))
           :in-theory (disable symbols-intern-scan-frame-p symbols-intern-scan-step-frame-p
                               symbols-intern-compare-ready-p symbols-intern-compared
                               symbols-intern-match-frame-p symbols-intern-match-target
                               symbols-intern-compare-return-p symbols-intern-scan-calls-compare-p)))
  :rule-classes nil)

(defun symbols-intern-key-matches-fields-p (dynamic fields world)
  (and (or (not dynamic) (equal (caddr fields) (proof-world-reg 9 world)))
       (equal (cadddr fields) (proof-world-reg 20 world))
       (symbols-intern-name-key-matches-p (car (cddddr fields))
                                          (proof-world-reg 8 world) (proof-world-reg 21 world) world)))

(local
 (defthm symbols-scanned-entry-agrees-with-fields
   (equal (symbols-intern-scanned-key-matches-p dynamic world)
          (and (not (symbols-intern-scan-empty-p world))
               (symbols-intern-key-matches-fields-p
                dynamic (symbols-intern-fields-at dynamic (proof-world-reg 22 world) world) world)))
   :hints (("Goal" :in-theory (disable symbols-intern-fields-at symbols-intern-name-key-matches-p)))))

(defun symbols-intern-chain-length-p (count dynamic link world)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (equal link *proof-nil*)
    (and (not (equal link *proof-nil*))
         (symbols-intern-chain-length-p
          (1- count) dynamic (car (symbols-intern-fields-at dynamic link world)) world))))

(defun symbols-intern-chain-binding (count dynamic link world)
  (declare (xargs :measure (nfix count)))
  (if (or (zp count) (equal link *proof-nil*))
      nil
    (let ((fields (symbols-intern-fields-at dynamic link world)))
      (if (symbols-intern-key-matches-fields-p dynamic fields world)
          (cons :binding (cadr fields))
        (symbols-intern-chain-binding (1- count) dynamic (car fields) world)))))

(defun symbols-intern-loop-ready-p (count dynamic byte-fuels base before)
  (declare (xargs :measure (nfix count)))
  (and (symbols-intern-scan-step-ready-p dynamic (car byte-fuels) base before)
       (or (zp count) (symbols-intern-scanned-key-matches-p dynamic before)
           (symbols-intern-loop-ready-p
            (1- count) dynamic (cdr byte-fuels) base
            (symbols-intern-scan-step-finish dynamic (car byte-fuels) before)))))

(defun symbols-intern-loop-finish (count dynamic byte-fuels before)
  (declare (xargs :measure (nfix count)))
  (let ((after (symbols-intern-scan-step-finish dynamic (car byte-fuels) before)))
    (if (or (zp count) (symbols-intern-scanned-key-matches-p dynamic before))
        after
      (symbols-intern-loop-finish (1- count) dynamic (cdr byte-fuels) after))))

(defun symbols-intern-chain-return-p (count dynamic base before after)
  (let ((binding (symbols-intern-chain-binding count dynamic (proof-world-reg 22 before) before)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after)
                (symbols-runtime-address
                 (cond (binding "rt:intern-return")
                       (dynamic "rt:intern-create")
                       (t "rt:intern-dynamic-start"))
                 base))
         (if binding (equal (proof-world-reg 0 after) (cdr binding))
           (equal (proof-world-reg 22 after) *proof-nil*))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 *symbols-intern-scan-clobbers* before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defun symbols-intern-key-frame-p (first last)
   (and (equal (symbols-machine-memory first) (symbols-machine-memory last))
        (equal (proof-heap-base first) (proof-heap-base last))
        (equal (proof-world-reg 8 first) (proof-world-reg 8 last))
        (equal (proof-world-reg 9 first) (proof-world-reg 9 last))
        (equal (proof-world-reg 20 first) (proof-world-reg 20 last))
        (equal (proof-world-reg 21 first) (proof-world-reg 21 last)))))

(local
 (defthm symbols-intern-fields-use-only-memory-and-base
   (implies (and (equal (symbols-machine-memory first) (symbols-machine-memory last))
                 (equal (proof-heap-base first) (proof-heap-base last)))
            (equal (symbols-intern-fields-at dynamic link first)
                   (symbols-intern-fields-at dynamic link last)))
   :hints (("Goal" :in-theory (enable symbols-load-register-word boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm symbols-intern-keys-agree-on-fields
   (implies (symbols-intern-key-frame-p first last)
            (and (equal (symbols-intern-fields-at dynamic link first)
                        (symbols-intern-fields-at dynamic link last))
                 (equal (symbols-intern-key-matches-fields-p dynamic fields first)
                        (symbols-intern-key-matches-fields-p dynamic fields last))))
   :hints (("Goal"
            :use ((:instance symbols-intern-fields-use-only-memory-and-base)
                  (:instance symbols-intern-name-key-of-same-memory
                             (word (car (cddddr fields)))
                             (size (proof-world-reg 21 first)) (address (proof-world-reg 8 first))))
            :in-theory (disable symbols-intern-fields-at symbols-intern-name-key-matches-p)))
   :rule-classes nil))

(local
 (defthm symbols-intern-chain-length-preserved-by-key-frame
   (implies (symbols-intern-key-frame-p first last)
            (equal (symbols-intern-chain-length-p count dynamic link first)
                   (symbols-intern-chain-length-p count dynamic link last)))
   :hints (("Goal" :induct (symbols-intern-chain-length-p count dynamic link first)
                   :in-theory (disable symbols-intern-key-frame-p symbols-intern-fields-at))
           ("Subgoal *1/2"
            :use ((:instance symbols-intern-keys-agree-on-fields))
            :in-theory (disable symbols-intern-key-frame-p symbols-intern-fields-at)))
   :rule-classes nil))

(local
 (defthm symbols-intern-binding-preserved-by-key-frame
   (implies (symbols-intern-key-frame-p first last)
            (equal (symbols-intern-chain-binding count dynamic link first)
                   (symbols-intern-chain-binding count dynamic link last)))
   :hints (("Goal" :induct (symbols-intern-chain-length-p count dynamic link first)
                   :in-theory (disable symbols-intern-key-frame-p symbols-intern-fields-at
                                       symbols-intern-key-matches-fields-p))
           ("Subgoal *1/2"
            :use ((:instance symbols-intern-keys-agree-on-fields
                             (fields (symbols-intern-fields-at dynamic link first))))
            :in-theory (disable symbols-intern-key-frame-p symbols-intern-fields-at
                                symbols-intern-key-matches-fields-p)))
   :rule-classes nil))

(local
 (defthm symbols-intern-scan-step-preserves-key
   (implies (symbols-intern-scan-step-frame-p dynamic base first last)
            (symbols-intern-key-frame-p first last))
   :hints (("Goal"
            :use ((:instance symbols-frame-gives-register (highest 30) (register 8)
                             (clobbers *symbols-intern-scan-clobbers*) (before first) (after last))
                  (:instance symbols-frame-gives-register (highest 30) (register 9)
                             (clobbers *symbols-intern-scan-clobbers*) (before first) (after last))
                  (:instance symbols-frame-gives-register (highest 30) (register 20)
                             (clobbers *symbols-intern-scan-clobbers*) (before first) (after last))
                  (:instance symbols-frame-gives-register (highest 30) (register 21)
                             (clobbers *symbols-intern-scan-clobbers*) (before first) (after last))
                  (:instance symbols-frame-gives-register (highest 30) (register 28)
                             (clobbers *symbols-intern-scan-clobbers*) (before first) (after last)))
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p proof-heap-base)
                            (symbols-intern-scanned-key-matches-p symbols-intern-fields-at))))
   :rule-classes nil))

(local
 (defthm symbols-intern-completed-step-gives-binding
   (implies (and (natp count)
                 (symbols-intern-chain-length-p count dynamic (proof-world-reg 22 before) before)
                 (or (zp count) (symbols-intern-scanned-key-matches-p dynamic before))
                 (symbols-intern-scan-step-frame-p dynamic base before after))
            (symbols-intern-chain-return-p count dynamic base before after))
   :hints (("Goal" :cases ((zp count))
                   :in-theory (disable symbols-intern-fields-at symbols-intern-key-matches-fields-p)))
   :rule-classes nil))

(local
 (defthm symbols-intern-chain-continues-at-next-link
   (let ((link (proof-world-reg 22 before)))
     (implies (and (posp count) (symbols-runtime-base-p base)
                   (symbols-intern-chain-length-p count dynamic link before)
                   (not (symbols-intern-scanned-key-matches-p dynamic before))
                   (symbols-intern-scan-step-frame-p dynamic base before middle))
              (and (symbols-intern-scan-start-p dynamic base middle)
                   (symbols-intern-chain-length-p (1- count) dynamic (proof-world-reg 22 middle) middle))))
   :hints (("Goal"
            :use ((:instance symbols-intern-scan-step-preserves-key (first before) (last middle))
                  (:instance symbols-intern-chain-length-preserved-by-key-frame
                             (count (1- count))
                             (link (car (symbols-intern-fields-at dynamic (proof-world-reg 22 before) before)))
                             (first before) (last middle)))
            :expand ((symbols-intern-chain-length-p count dynamic (proof-world-reg 22 before) before))
            :in-theory (disable symbols-intern-key-frame-p symbols-intern-fields-at
                                symbols-intern-key-matches-fields-p)))
   :rule-classes nil))

(local
 (defthm symbols-intern-missed-head-binds-tail
   (implies (and (posp count) (not (equal link *proof-nil*))
                 (not (symbols-intern-key-matches-fields-p dynamic (symbols-intern-fields-at dynamic link before)
                                                           before)))
            (equal (symbols-intern-chain-binding count dynamic link before)
                   (symbols-intern-chain-binding (1- count) dynamic
                                                  (car (symbols-intern-fields-at dynamic link before))
                                                  before)))
   :hints (("Goal" :expand ((symbols-intern-chain-binding count dynamic link before))
                   :in-theory (disable symbols-intern-fields-at symbols-intern-key-matches-fields-p)))
   :rule-classes nil))

(local
 (defthm symbols-intern-chain-return-composition
   (let ((link (proof-world-reg 22 before)))
     (implies (and (posp count)
                   (symbols-intern-chain-length-p count dynamic link before)
                   (not (symbols-intern-scanned-key-matches-p dynamic before))
                   (symbols-intern-scan-step-frame-p dynamic base before middle)
                   (symbols-intern-chain-return-p (1- count) dynamic base middle after))
              (symbols-intern-chain-return-p count dynamic base before after)))
   :hints (("Goal"
            :use ((:instance symbols-intern-scan-step-preserves-key (first before) (last middle))
                  (:instance symbols-intern-missed-head-binds-tail (link (proof-world-reg 22 before)))
                  (:instance symbols-intern-binding-preserved-by-key-frame
                             (count (1- count))
                             (link (car (symbols-intern-fields-at dynamic (proof-world-reg 22 before) before)))
                             (first before) (last middle))
                  (:instance symbols-frame-is-transitive
                             (highest 30) (clobbers *symbols-intern-scan-clobbers*)
                             (first before) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive (first before) (last after)))
            :expand ((symbols-intern-chain-length-p count dynamic (proof-world-reg 22 before) before))
            :in-theory (disable symbols-intern-key-frame-p symbols-intern-fields-at
                                symbols-intern-chain-binding symbols-intern-key-matches-fields-p)))
   :rule-classes nil))

(defthm symbols-run-intern-chain
  (implies (and (natp count) (symbols-intern-scan-start-p dynamic code-base before)
                (symbols-intern-chain-length-p count dynamic (proof-world-reg 22 before) before)
                (symbols-intern-loop-ready-p count dynamic byte-fuels code-base before))
           (symbols-intern-chain-return-p count dynamic code-base before
                                           (symbols-intern-loop-finish count dynamic byte-fuels before)))
  :hints (("Goal"
           :induct (symbols-intern-loop-ready-p count dynamic byte-fuels code-base before)
           :in-theory (disable symbols-intern-scan-step-ready-p symbols-intern-scan-step-finish
                               symbols-intern-scan-step-frame-p symbols-intern-chain-return-p
                               symbols-intern-scanned-key-matches-p symbols-scanned-entry-agrees-with-fields
                               symbols-intern-chain-length-p))
          ("Subgoal *1/3"
           :use ((:instance symbols-run-intern-scan-step (byte-fuel (car byte-fuels)))
                 (:instance symbols-intern-chain-continues-at-next-link (base code-base)
                            (middle (symbols-intern-scan-step-finish dynamic (car byte-fuels) before)))
                 (:instance symbols-intern-chain-return-composition (base code-base)
                            (middle (symbols-intern-scan-step-finish dynamic (car byte-fuels) before))
                            (after (symbols-intern-loop-finish count dynamic byte-fuels before))))
           :in-theory (disable symbols-intern-scan-step-ready-p symbols-intern-scan-step-finish
                               symbols-intern-scan-step-frame-p symbols-intern-chain-return-p
                               symbols-intern-scanned-key-matches-p symbols-scanned-entry-agrees-with-fields
                               symbols-intern-chain-length-p))
          ("Subgoal *1/2"
           :use ((:instance symbols-run-intern-scan-step (byte-fuel (car byte-fuels)))
                 (:instance symbols-intern-completed-step-gives-binding (base code-base)
                            (after (symbols-intern-scan-step-finish dynamic (car byte-fuels) before)))))
          ("Subgoal *1/1"
           :use ((:instance symbols-run-intern-scan-step (byte-fuel (car byte-fuels)))
                 (:instance symbols-intern-completed-step-gives-binding (base code-base)
                            (after (symbols-intern-scan-step-finish dynamic (car byte-fuels) before))))))
  :rule-classes nil)

(defun symbols-intern-setup-state (before)
  (proof-advance (len *symbols-intern-setup-path*) before))

(defun symbols-intern-designator-view (before)
  (let ((setup (symbols-intern-setup-state before)))
    (proof-advance (len (symbols-symbol-view-path setup)) setup)))

(defun symbols-intern-name-call (before)
  (let ((view (symbols-intern-designator-view before)))
    (proof-advance (len (symbols-intern-designator-path view)) view)))

(defun symbols-intern-name-view (before)
  (let ((call (symbols-intern-name-call before)))
    (proof-advance (len (symbols-string-view-path call)) call)))

(defun symbols-intern-front-state (before)
  (if (equal (proof-world-reg 1 (symbols-intern-designator-view before)) 0)
      (symbols-intern-name-call before)
    (let ((view (symbols-intern-name-view before)))
      (proof-advance (len (symbols-intern-name-path view)) view))))

(defun symbols-intern-front-ready-p (base before)
  (let ((setup (symbols-intern-setup-state before))
        (designator (symbols-intern-designator-view before)))
    (and (symbols-path-ready-p *symbols-intern-setup-path* base
                               (symbols-runtime-address "rt:symbol-view" base) before)
         (symbols-path-ready-p (symbols-symbol-view-path setup) base (proof-world-reg 30 setup) setup)
         (symbols-path-ready-p (symbols-intern-designator-path designator) base
                               (symbols-intern-designator-target base designator) designator)
         (implies (not (equal (proof-world-reg 1 designator) 0))
                  (let ((call (symbols-intern-name-call before)) (view (symbols-intern-name-view before)))
                    (and (symbols-path-ready-p (symbols-string-view-path call) base
                                               (proof-world-reg 30 call) call)
                         (symbols-path-ready-p (symbols-intern-name-path view) base
                                               (symbols-intern-name-target base view) view)))))))

(defun symbols-intern-front-frames-p (base before setup designator call view after)
  (and (symbols-intern-setup-frame-p base before setup)
       (proof-frame-return-p '(1 2) t setup designator)
       (not (eq (car (proof-world-machine designator)) :svc))
       (equal (proof-world-reg 1 designator) (symbols-symbol-view-result setup))
       (symbols-no-memory-or-kernel-change-p setup designator)
       (symbols-intern-designator-frame-p base designator call)
       (if (equal (proof-world-reg 1 designator) 0)
           (equal after call)
         (and (symbols-string-view-frame-p call view)
              (symbols-intern-name-frame-p base view after)))))

(defthm symbols-run-intern-front
  (implies (and (symbols-intern-at-p 0 code-base before)
                (<= 48 (boymoo-model::a64-sp (proof-world-machine before)))
                (symbols-intern-front-ready-p code-base before))
           (symbols-intern-front-frames-p code-base before
                                          (symbols-intern-setup-state before)
                                          (symbols-intern-designator-view before)
                                          (symbols-intern-name-call before)
                                          (symbols-intern-name-view before)
                                          (symbols-intern-front-state before)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-setup)
                 (:instance symbols-run-symbol-view (before (symbols-intern-setup-state before)))
                 (:instance symbols-run-intern-designator-test (before (symbols-intern-designator-view before)))
                 (:instance symbols-run-string-view (before (symbols-intern-name-call before)))
                 (:instance symbols-run-intern-name-test (before (symbols-intern-name-view before))))
           :in-theory (disable symbols-run-symbol-view symbols-symbol-view-path
                               symbols-intern-designator-path symbols-intern-name-path
                               symbols-string-view-path symbols-string-hit-p
                               symbols-string-header-word symbols-string-payload
                               symbols-symbol-view-result symbols-intern-name-equality-target
                               symbols-intern-saved-world)))
  :rule-classes nil)

(defun symbols-intern-dynamic-call (before)
  (proof-advance (len (symbols-intern-dynamic-start-path before)) before))

(defun symbols-intern-dynamic-bucket (before)
  (proof-advance (len *symbols-bucket-address-path*) (symbols-intern-dynamic-call before)))

(defun symbols-intern-dynamic-entry (before)
  (if (symbols-intern-dynamic-root-nil-p before)
      (symbols-intern-dynamic-call before)
    (proof-advance (len *symbols-intern-dynamic-head-path*) (symbols-intern-dynamic-bucket before))))

(defun symbols-intern-dynamic-entry-ready-p (base before)
  (and (symbols-path-ready-p (symbols-intern-dynamic-start-path before) base
                             (symbols-intern-dynamic-start-target base before) before)
       (implies (not (symbols-intern-dynamic-root-nil-p before))
                (let ((call (symbols-intern-dynamic-call before))
                      (bucket (symbols-intern-dynamic-bucket before)))
                  (and (symbols-path-ready-p *symbols-bucket-address-path* base
                                             (proof-world-reg 30 call) call)
                       (symbols-path-ready-p *symbols-intern-dynamic-head-path* base
                                             (symbols-runtime-address "rt:intern-dynamic" base) bucket))))))

(defun symbols-intern-dynamic-selected-bucket (before)
  (symbols-dynamic-bucket-at
   (symbols-box-address (symbols-intern-dynamic-root-word before) (proof-heap-base before))
   (proof-world-reg 9 before) before))

(defun symbols-intern-dynamic-entry-frame-p (base before after)
  (let ((nil-root (symbols-intern-dynamic-root-nil-p before)))
    (and (not (proof-world-stop after))
         (not (eq (car (proof-world-machine after)) :svc))
         (equal (proof-world-pc after)
                (symbols-runtime-address (if nil-root "rt:intern-create" "rt:intern-dynamic") base))
         (implies (not nil-root)
                  (equal (proof-world-reg 22 after)
                         (symbols-load-register-word (symbols-intern-dynamic-selected-bucket before) before)))
         (equal (boymoo-model::a64-sp (proof-world-machine after))
                (boymoo-model::a64-sp (proof-world-machine before)))
         (proof-register-frame-p 30 '(1 3 4 22 30) before after)
         (symbols-no-memory-or-kernel-change-p before after))))

(local
 (defthm symbols-intern-load-register-word-of-same-memory
   (implies (equal (symbols-machine-memory first) (symbols-machine-memory last))
            (equal (symbols-load-register-word address first)
                   (symbols-load-register-word address last)))
   :hints (("Goal" :in-theory (enable symbols-load-register-word boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm symbols-intern-dynamic-bucket-of-same-memory
   (implies (equal (symbols-machine-memory first) (symbols-machine-memory last))
            (equal (symbols-dynamic-bucket-at table key first)
                   (symbols-dynamic-bucket-at table key last)))
   :hints (("Goal" :in-theory (enable boymoo-model::a64-load)))
   :rule-classes nil))

(local
 (defthm symbols-intern-dynamic-bucket-and-head-segments
   (let* ((bucket (proof-advance (len *symbols-bucket-address-path*) call))
          (after (proof-advance (len *symbols-intern-dynamic-head-path*) bucket)))
     (implies (and (symbols-runtime-base-p base)
                   (not (symbols-intern-dynamic-root-nil-p before))
                   (symbols-intern-dynamic-start-frame-p base before call)
                   (symbols-path-ready-p *symbols-bucket-address-path* base (proof-world-reg 30 call) call)
                   (symbols-path-ready-p *symbols-intern-dynamic-head-path* base
                                         (symbols-runtime-address "rt:intern-dynamic" base) bucket))
              (and (proof-frame-return-p '(3 4) nil call bucket)
                   (equal (proof-world-reg 4 bucket) (symbols-intern-dynamic-selected-bucket before))
                   (symbols-no-memory-or-kernel-change-p call bucket)
                   (not (proof-world-stop after))
                   (not (eq (car (proof-world-machine after)) :svc))
                   (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-dynamic" base))
                   (equal (proof-world-reg 22 after)
                          (symbols-load-register-word (proof-world-reg 4 bucket) bucket))
                   (equal (boymoo-model::a64-sp (proof-world-machine after))
                          (boymoo-model::a64-sp (proof-world-machine bucket)))
                   (proof-register-frame-p 30 '(22) bucket after)
                   (symbols-no-memory-or-kernel-change-p bucket after))))
   :hints (("Goal"
            :use ((:instance symbols-run-bucket-address (code-base base) (before call))
                  (:instance symbols-run-intern-dynamic-head (code-base base)
                             (before (proof-advance (len *symbols-bucket-address-path*) call)))
                  (:instance symbols-frame-gives-register (highest 30) (register 9)
                             (clobbers '(1 30)) (after call))
                  (:instance symbols-intern-dynamic-bucket-of-same-memory
                             (table (symbols-box-address (symbols-intern-dynamic-root-word before)
                                                         (proof-heap-base before)))
                             (key (proof-world-reg 9 before)) (first before) (last call)))
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p)
                            (symbols-dynamic-mask-at symbols-dynamic-bucket-at
                             symbols-intern-dynamic-root-word symbols-box-address
                             symbols-run-bucket-address))))
   :rule-classes nil))

(local
 (defthm symbols-intern-dynamic-present-frames
   (implies (and (not (symbols-intern-dynamic-root-nil-p before))
                 (symbols-intern-dynamic-start-frame-p base before call)
                 (proof-frame-return-p '(3 4) nil call bucket)
                 (equal (proof-world-reg 4 bucket) (symbols-intern-dynamic-selected-bucket before))
                 (symbols-no-memory-or-kernel-change-p call bucket)
                 (not (proof-world-stop after))
                 (not (eq (car (proof-world-machine after)) :svc))
                 (equal (proof-world-pc after) (symbols-runtime-address "rt:intern-dynamic" base))
                 (equal (proof-world-reg 22 after) (symbols-load-register-word (proof-world-reg 4 bucket) bucket))
                 (equal (boymoo-model::a64-sp (proof-world-machine after))
                        (boymoo-model::a64-sp (proof-world-machine bucket)))
                 (proof-register-frame-p 30 '(22) bucket after)
                 (symbols-no-memory-or-kernel-change-p bucket after))
            (symbols-intern-dynamic-entry-frame-p base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(1 30))
                             (allowed '(1 3 4 22 30)) (after call))
                  (:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(3 4))
                             (allowed '(1 3 4 22 30)) (before call) (after bucket))
                  (:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(22))
                             (allowed '(1 3 4 22 30)) (before bucket))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers '(1 3 4 22 30))
                             (first before) (middle call) (last bucket))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers '(1 3 4 22 30))
                             (first before) (middle bucket) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first before) (middle call) (last bucket))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first before) (middle bucket) (last after))
                  (:instance symbols-intern-load-register-word-of-same-memory
                             (address (symbols-intern-dynamic-selected-bucket before))
                             (first before) (last bucket)))
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p)
                            (symbols-intern-dynamic-selected-bucket symbols-intern-dynamic-root-word))))
   :rule-classes nil))

(local
 (defthm symbols-intern-dynamic-absent-frame
   (implies (and (symbols-intern-dynamic-root-nil-p before)
                 (symbols-intern-dynamic-start-frame-p base before after))
            (symbols-intern-dynamic-entry-frame-p base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(1 30))
                             (allowed '(1 3 4 22 30))))
            :in-theory (disable symbols-intern-dynamic-selected-bucket symbols-intern-dynamic-root-word)))
   :rule-classes nil))

(defthm symbols-run-intern-dynamic-entry
  (implies (and (symbols-intern-dynamic-start-pre-p code-base before)
                (symbols-intern-dynamic-entry-ready-p code-base before))
           (symbols-intern-dynamic-entry-frame-p code-base before (symbols-intern-dynamic-entry before)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-dynamic-start)
                 (:instance symbols-intern-dynamic-absent-frame
                            (base code-base) (after (symbols-intern-dynamic-call before)))
                 (:instance symbols-intern-dynamic-bucket-and-head-segments
                            (base code-base) (call (symbols-intern-dynamic-call before)))
                 (:instance symbols-intern-dynamic-present-frames
                            (base code-base) (call (symbols-intern-dynamic-call before))
                            (bucket (symbols-intern-dynamic-bucket before))
                            (after (symbols-intern-dynamic-entry before))))
           :in-theory (disable symbols-intern-dynamic-root-word symbols-intern-dynamic-start-frame-p
                               symbols-intern-dynamic-entry-frame-p symbols-intern-dynamic-selected-bucket
                               symbols-intern-dynamic-start-path symbols-intern-dynamic-start-target)))
  :rule-classes nil)

(local
 (defthm symbols-intern-word-load-is-header
   (equal (symbols-load-register-word address world)
          (proof-load-word address (proof-world-machine world)))
   :hints (("Goal" :in-theory (e/d (symbols-load-register-word symbols-word-load-fits proof-load-word)
                                   (boymoo-model::a64-load))))))

(local
 (defthm symbols-intern-string-header-is-pointer
   (implies (equal (proof-word-tag (proof-world-reg 0 world)) 2)
            (equal (symbols-symbol-header world)
                   (proof-pointer-address (proof-world-reg 0 world) (proof-heap-base world))))
   :hints (("Goal"
            :use ((:instance symbols-unsigned-sum-right
                             (width 64) (x (- (proof-world-reg 0 world) 2)) (y (proof-heap-base world))))
            :in-theory (disable symbols-unsigned-sum-right)))))

(local
 (defthm symbols-intern-string-header-size
   (let ((header (proof-load-word address (proof-world-machine world))))
     (and (equal (symbols-logical-right-shift-bits header 8) (proof-header-size header))
          (natp (proof-header-size header))))
   :hints (("Goal"
            :use ((:instance symbols-logical-right-shift-correct
                             (word (proof-load-word address (proof-world-machine world))) (amount 8))
                  (:instance symbols-load-width (count 8) (machine (proof-world-machine world))))
            :in-theory (e/d (ash proof-load-word)
                            (boymoo-model::a64-load symbols-logical-right-shift-bits))))))

(local
 (defthm symbols-intern-character-count-is-byte-count
   (equal (len (proof-string-bytes characters)) (len characters))
   :hints (("Goal" :induct (proof-string-bytes characters)))))

(local
 (defthm symbols-intern-loaded-header-size-is-natural
   (natp (proof-header-size (proof-load-word address machine)))
   :hints (("Goal" :use ((:instance symbols-load-width (count 8)))
                   :in-theory (e/d (ash) (boymoo-model::a64-load))))
   :rule-classes :type-prescription))

(defthm symbols-string-view-agrees-with-value
  (let* ((word (proof-world-reg 0 before))
         (base (proof-heap-base before))
         (address (proof-pointer-address word base))
         (machine (proof-world-machine before)))
    (implies (and (proof-reg-value-p 0 datum before objects packages)
                  (symbols-string-view-frame-p before after)
                  (implies (stringp datum) (< (+ address 8) (expt 2 64))))
             (if (stringp datum)
                 (and (not (equal (proof-world-reg 1 after) 0))
                      (equal (proof-world-reg 1 after) (+ address 8))
                      (equal (proof-world-reg 2 after) (len (coerce datum 'list)))
                      (equal (proof-byte-list (len (coerce datum 'list)) (+ address 8) machine)
                             (proof-string-bytes (coerce datum 'list))))
               (and (equal (proof-world-reg 1 after) 0)
                    (equal (proof-world-reg 2 after) 0)))))
  :hints (("Goal"
           :use ((:instance symbols-represented-string-layout
                            (word (proof-world-reg 0 before)) (base (proof-heap-base before))
                            (machine (proof-world-machine before)))
                 (:instance symbols-loaded-string-has-span-bytes
                            (count (proof-header-size (proof-load-word
                                     (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before))
                                     (proof-world-machine before))))
                            (address (+ 8 (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before))))
                            (machine (proof-world-machine before)))
                 (:instance symbols-byte-list-length
                            (count (proof-header-size (proof-load-word
                                     (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before))
                                     (proof-world-machine before))))
                            (address (+ 8 (proof-pointer-address (proof-world-reg 0 before) (proof-heap-base before))))
                            (machine (proof-world-machine before))))
           :in-theory (e/d (symbols-string-hit-p symbols-string-header-word symbols-string-payload
                            symbols-symbol-tag-p)
                           (proof-frame-return-p proof-load-word proof-value-p proof-view
                            proof-load-string proof-pointer-address symbols-symbol-header
                            proof-byte-list proof-string-bytes symbols-loaded-string-has-span-bytes
                            symbols-byte-list-length proof-header-size))))
  :rule-classes nil)
