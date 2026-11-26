(in-package "BOYMOO-PROOFS")

(include-book "intern")

(logic)
(set-verify-guards-eagerness 0)

(local
 (in-theory (set-difference-theories (current-theory :here)
                                    (theory 'symbols-state-operations))))

(local
 (in-theory (disable proof-world-reg proof-world-pc proof-reg proof-heap-base
                     proof-advance proof-advance-append proof-register-frame-p
                     symbols-runtime-offset symbols-path-ready-p symbols-intern-static-slot
                     symbols-intern-loop-ready-p symbols-intern-loop-finish symbols-intern-chain-binding
                     symbols-intern-dynamic-entry symbols-intern-dynamic-root-nil-p
                     symbols-intern-dynamic-entry-ready-p symbols-intern-chain-length-p)))

(defun symbols-intern-hashed (name before)
  (proof-advance (symbols-hash-iterations-fuel (coerce name 'list)) before))

(defun symbols-intern-static-entry (name before)
  (proof-advance (len *symbols-intern-bucket-path*) (symbols-intern-hashed name before)))

(defun symbols-intern-static-entry-ready-p (name base before)
  (let ((hashed (symbols-intern-hashed name before)))
    (and (symbols-hash-iterations-ready-p (coerce name 'list) base before)
         (symbols-path-ready-p *symbols-intern-bucket-path* base
                               (symbols-runtime-address "rt:intern-static" base) hashed))))

(defun symbols-intern-selected-static-frame-p (number name base before after)
  (and (symbols-intern-scan-start-p nil base after)
       (equal (proof-world-reg 3 after) (proof-symbol-hash number name 12))
       (equal (proof-world-reg 9 after)
              (proof-integer-word (boymoo-model::a64-signed 63 (proof-symbol-hash number name 63))))
       (equal (proof-world-reg 22 after)
              (symbols-load-register-word
               (symbols-intern-static-slot (symbols-intern-hashed name before)) before))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-register-frame-p 30 '(3 4 5 9 22) before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-intern-static-entry-frames-compose
   (implies (and (symbols-runtime-base-p base)
                 (not (proof-world-stop hashed))
                 (equal (proof-world-pc hashed) (symbols-runtime-address "rt:intern-bucket" base))
                 (equal (boymoo-model::a64-sp (proof-world-machine hashed))
                        (boymoo-model::a64-sp (proof-world-machine before)))
                 (proof-register-frame-p 30 '(3 4 5) before hashed)
                 (symbols-no-memory-or-kernel-change-p before hashed)
                 (symbols-intern-bucket-frame-p base hashed after)
                 (equal hashed (symbols-intern-hashed name before))
                 (equal (proof-world-reg 3 after) (proof-symbol-hash number name 12))
                 (equal (proof-world-reg 9 after)
                        (proof-integer-word (boymoo-model::a64-signed 63 (proof-symbol-hash number name 63)))))
            (symbols-intern-selected-static-frame-p number name base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(3 4 5))
                             (allowed '(3 4 5 9 22)) (after hashed))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers '(3 4 5 9 22))
                             (first before) (middle hashed) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive
                             (first before) (middle hashed) (last after)))
            :in-theory (e/d (symbols-no-memory-or-kernel-change-p symbols-load-register-word boymoo-model::a64-load)
                            (symbols-intern-hashed proof-integer-word proof-hash-characters))))
   :rule-classes nil))

(defthm symbols-run-intern-select-static-bucket
  (let ((after (symbols-intern-static-entry name before)))
    (implies (and (stringp name) (natp number) (< number (expt 2 63))
                  (equal (proof-world-reg 20 before) (+ 1 (* 2 number)))
                  (equal (proof-world-reg 3 before) 0)
                  (symbols-hash-input-p (coerce name 'list) code-base before)
                  (symbols-intern-static-entry-ready-p name code-base before))
             (symbols-intern-selected-static-frame-p number name code-base before after)))
  :hints (("Goal"
           :use ((:instance symbols-run-hash-iterations (characters (coerce name 'list)))
                 (:instance symbols-run-intern-bucket (before (symbols-intern-hashed name before)))
                 (:instance symbols-intern-static-entry-frames-compose (base code-base)
                            (hashed (symbols-intern-hashed name before)) (after (symbols-intern-static-entry name before)))
                 (:instance symbols-frame-gives-register (highest 30) (clobbers '(3 4 5)) (register 20)
                            (after (symbols-intern-hashed name before)))
                 (:instance symbols-machine-name-hash-agrees (characters (coerce name 'list)) (hash 0))
                 (:instance symbols-intern-bucket-frame-agrees-with-key
                            (before (symbols-intern-hashed name before))
                            (after (symbols-intern-static-entry name before))))
           :in-theory (e/d (symbols-intern-bucket-pre-p symbols-hash-input-p symbols-hash-loop-pre-p)
                           (proof-symbol-hash proof-integer-word symbols-intern-selected-static-frame-p
                            symbols-intern-bucket-frame-p proof-hash-characters symbols-machine-name-hash-agrees
                            symbols-machine-name-hash symbols-hash-iterations-fuel))))
  :rule-classes nil)

(defun symbols-intern-binding (count dynamic world)
  (symbols-intern-chain-binding count dynamic (proof-world-reg 22 world) world))

(defun symbols-intern-static-probed (count byte-fuels before)
  (symbols-intern-loop-finish count nil byte-fuels before))

(defun symbols-intern-probe-ready-p (count dynamic byte-fuels base world)
  (and (natp count)
       (symbols-intern-chain-length-p count dynamic (proof-world-reg 22 world) world)
       (symbols-intern-loop-ready-p count dynamic byte-fuels base world)))

(defun symbols-intern-probes-ready-p (static-count static-fuels dynamic-count dynamic-fuels base before)
  (and (symbols-intern-probe-ready-p static-count nil static-fuels base before)
       (or (symbols-intern-binding static-count nil before)
           (let ((probed (symbols-intern-static-probed static-count static-fuels before)))
             (and (symbols-intern-dynamic-entry-ready-p base probed)
                  (or (symbols-intern-dynamic-root-nil-p probed)
                      (symbols-intern-probe-ready-p
                       dynamic-count t dynamic-fuels base (symbols-intern-dynamic-entry probed))))))))

(defun symbols-intern-probes-finish (static-count static-fuels dynamic-count dynamic-fuels before)
  (let ((probed (symbols-intern-static-probed static-count static-fuels before)))
    (if (symbols-intern-binding static-count nil before)
        probed
      (let ((dynamic (symbols-intern-dynamic-entry probed)))
        (if (symbols-intern-dynamic-root-nil-p probed) dynamic
          (symbols-intern-loop-finish dynamic-count t dynamic-fuels dynamic))))))

(defun symbols-intern-probes-binding (static-count static-fuels dynamic-count before)
  (or (symbols-intern-binding static-count nil before)
      (let ((probed (symbols-intern-static-probed static-count static-fuels before)))
        (and (not (symbols-intern-dynamic-root-nil-p probed))
             (symbols-intern-binding dynamic-count t (symbols-intern-dynamic-entry probed))))))

(defun symbols-intern-probes-frame-p (binding base before after)
  (and (not (proof-world-stop after))
       (not (eq (car (proof-world-machine after)) :svc))
       (equal (proof-world-pc after)
              (symbols-runtime-address (if binding "rt:intern-return" "rt:intern-create") base))
       (implies binding (equal (proof-world-reg 0 after) (cdr binding)))
       (equal (boymoo-model::a64-sp (proof-world-machine after))
              (boymoo-model::a64-sp (proof-world-machine before)))
       (proof-register-frame-p 30 *symbols-intern-scan-clobbers* before after)
       (symbols-no-memory-or-kernel-change-p before after)))

(local
 (defthm symbols-intern-dynamic-readiness
   (implies (and (symbols-runtime-base-p base)
                 (symbols-intern-chain-return-p static-count nil base before probed)
                 (not (symbols-intern-binding static-count nil before))
                 (symbols-intern-dynamic-entry-ready-p base probed))
            (let ((dynamic (symbols-intern-dynamic-entry probed)))
              (and (symbols-intern-dynamic-entry-frame-p base probed dynamic)
                   (implies (not (symbols-intern-dynamic-root-nil-p probed))
                            (symbols-intern-scan-start-p t base dynamic)))))
   :hints (("Goal"
            :use ((:instance symbols-run-intern-dynamic-entry (code-base base) (before probed)))
            :in-theory (disable symbols-intern-dynamic-selected-bucket)))
   :rule-classes nil))

(local
 (defthm symbols-intern-dynamic-probes-compose
   (implies (and (symbols-intern-chain-return-p static-count nil base before static)
                 (not (symbols-intern-binding static-count nil before))
                 (symbols-intern-dynamic-entry-frame-p base static dynamic)
                 (if (symbols-intern-dynamic-root-nil-p static)
                     (and (not binding) (equal after dynamic))
                   (and (equal binding (symbols-intern-binding dynamic-count t dynamic))
                        (symbols-intern-chain-return-p dynamic-count t base dynamic after))))
            (symbols-intern-probes-frame-p binding base before after))
   :hints (("Goal"
            :use ((:instance symbols-frame-allows-more-clobbers (highest 30) (clobbers '(1 3 4 22 30))
                             (allowed *symbols-intern-scan-clobbers*) (before static) (after dynamic))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-intern-scan-clobbers*)
                             (first before) (middle static) (last dynamic))
                  (:instance symbols-frame-is-transitive (highest 30) (clobbers *symbols-intern-scan-clobbers*)
                             (first before) (middle dynamic) (last after))
                  (:instance symbols-memory-and-kernel-frame-is-transitive (first before) (middle static) (last dynamic))
                  (:instance symbols-memory-and-kernel-frame-is-transitive (first before) (middle dynamic) (last after)))
            :in-theory (disable symbols-intern-dynamic-selected-bucket)))
   :rule-classes nil))

(defthm symbols-run-intern-probes
  (let* ((binding (symbols-intern-probes-binding static-count static-fuels dynamic-count before))
         (after (symbols-intern-probes-finish static-count static-fuels dynamic-count dynamic-fuels before)))
    (implies (and (symbols-intern-scan-start-p nil code-base before)
                  (symbols-intern-probes-ready-p static-count static-fuels dynamic-count dynamic-fuels code-base before))
             (symbols-intern-probes-frame-p binding code-base before after)))
  :hints (("Goal"
           :use ((:instance symbols-run-intern-chain (count static-count) (dynamic nil) (byte-fuels static-fuels))
                 (:instance symbols-intern-dynamic-readiness (base code-base)
                            (probed (symbols-intern-static-probed static-count static-fuels before)))
                 (:instance symbols-run-intern-chain (count dynamic-count) (dynamic t) (byte-fuels dynamic-fuels)
                            (before (symbols-intern-dynamic-entry
                                     (symbols-intern-static-probed static-count static-fuels before))))
                 (:instance symbols-intern-dynamic-probes-compose (base code-base)
                            (static (symbols-intern-static-probed static-count static-fuels before))
                            (dynamic (symbols-intern-dynamic-entry
                                      (symbols-intern-static-probed static-count static-fuels before)))
                            (binding (symbols-intern-probes-binding static-count static-fuels dynamic-count before))
                            (after (symbols-intern-probes-finish static-count static-fuels dynamic-count dynamic-fuels before))))
           :in-theory (disable symbols-intern-dynamic-entry-frame-p symbols-intern-dynamic-selected-bucket
                               symbols-no-memory-or-kernel-change-p)))
  :rule-classes nil)
