(in-package "BOYMOO-PROOFS")

(include-book "object-views")
(include-book "pair-access")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-stop proof-world-machine
                    proof-step proof-run proof-segment-p proof-advance proof-heap-p
                    generated-path-p generated-if-path generated-pair-access-path
                    generated-heap-world-equiv proof-stack-prefix proof-reg-value-p
                    proof-prefix-preserved-p proof-machine-value-p proof-value-p
                    boymoo-model::core-eval-step boymoo-compiler::gen-term expt))

(defthm generated-if-dispatch-in-published-heap
  (let* ((pc (proof-world-pc before))
         (path (generated-if-path yes no before))
         (after (generated-path-after path before))
         (truth (boymoo-model::core-datum test-result)))
    (implies (and (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no)
                  (< (+ pc 8) (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before))
                  (boymoo-model::core-value-p test-result)
                  (proof-heap-p before objects packages)
                  (proof-reg-value-p 0 truth before objects packages)
                  (generated-path-p path (list yes no) before))
             (and (proof-segment-p (len path) (list yes no) before :cut after)
                  (equal (proof-world-pc after) (if truth yes no))
                  (generated-heap-world-equiv after before)
                  (equal (proof-world-reg 0 after) (proof-world-reg 0 before)))))
  :hints (("Goal"
           :use (generated-if-dispatch-selects-source-arm
                 (:instance generated-nil-has-canonical-word-in-heap
                            (world before) (word (proof-world-reg 0 before))
                            (value (boymoo-model::core-datum test-result))))
           :in-theory (enable proof-reg-value-p)))
  :rule-classes nil)

(defthm generated-pair-access-in-published-heap
  (let* ((pc (proof-world-pc before))
         (path (generated-pair-access-path cdr-p before))
         (after (generated-path-after path before)))
    (implies (and (< (+ pc 24) (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before)) (proof-heap-p before objects packages)
                  (proof-reg-value-p 0 input before objects packages)
                  (generated-path-p path (list (+ pc 24)) before))
             (and (proof-segment-p (if (consp input) 6 4) (list (+ pc 24)) before :cut after)
                  (proof-reg-value-p 0 (if cdr-p (cdr input) (car input)) after objects packages)
                  (generated-heap-world-equiv after before))))
  :hints (("Goal"
           :use (generated-pair-access-checked-path
                 (:instance generated-static-booleans-in-published-heap (world before))
                 (:instance generated-published-cons-field-addresses-fit
                            (world before) (word (proof-world-reg 0 before)) (value input)))
           :in-theory (e/d (proof-reg-value-p proof-machine-value-p)
                           ((:congruence generated-heap-world-equiv-implies-equal-proof-heap-base-1)
                            (:congruence generated-heap-world-equiv-implies-equal-proof-machine-value-p-3)))))
  :rule-classes nil)

(defthm generated-if-dispatch-and-selected-arm-return
  (let* ((next (1- fuel))
         (pc (proof-world-pc before))
         (path (generated-if-path yes no before))
         (arm (generated-path-after path before))
         (test-result (boymoo-model::core-eval-step :term test env program next))
         (truth (boymoo-model::core-datum test-result))
         (arm-result (boymoo-model::core-eval-step :term (if truth yes-term no-term) env program next))
         (source-result (boymoo-model::core-eval-step :term
                                                     (list 'if test yes-term no-term) env program fuel)))
    (implies (and (posp fuel) (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no)
                  (< (+ pc 8) (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before))
                  (boymoo-model::core-value-p test-result)
                  (proof-heap-p before objects packages)
                  (proof-reg-value-p 0 truth before objects packages)
                  (generated-path-p path (list yes no continuation) before)
                  (proof-segment-p arm-steps (list continuation) arm :cut after)
                  (boymoo-model::core-value-p arm-result)
                  (proof-reg-value-p 0 (boymoo-model::core-datum arm-result) after new-objects packages)
                  (proof-prefix-preserved-p (proof-stack-top arm) arm after objects new-objects packages))
             (and (equal (proof-world-pc arm) (if truth yes no))
                  (proof-segment-p (+ (len path) (nfix arm-steps)) (list continuation) before :cut after)
                  (boymoo-model::core-value-p source-result)
                  (proof-reg-value-p 0 (boymoo-model::core-datum source-result) after new-objects packages)
                  (proof-prefix-preserved-p (proof-stack-top before) before after
                                            objects new-objects packages))))
  :hints (("Goal" :use ((:instance generated-if-dispatch-in-published-heap
                                  (test-result (boymoo-model::core-eval-step :term test env program
                                                                             (1- fuel))))
                        (:instance generated-placed-path-allows-fewer-cuts
                                   (path (generated-if-path yes no before)) (cuts (list yes no))
                                   (all-cuts (list yes no continuation)))
                        (:instance generated-placed-path-allows-fewer-cuts
                                   (path (generated-if-path yes no before)) (cuts (list continuation))
                                   (all-cuts (list yes no continuation)))
                        (:instance generated-prefix-then-segment
                                   (prefix (len (generated-if-path yes no before))) (suffix arm-steps)
                                   (cuts (list continuation)) (reason :cut)
                                   (middle (generated-path-after (generated-if-path yes no before) before))))
                  :in-theory (enable proof-prefix-preserved-p)))
  :rule-classes nil)

(defthm generated-if-nontail-emission
  (equal (boymoo-compiler::gen-term (list boymoo-compiler::*if-name* test yes-term no-term)
                                   scope depth nil context code high serial)
         (mv-let (test-code test-high test-serial)
           (boymoo-compiler::gen-term test scope depth nil context code high serial)
           (let* ((yes (boymoo-compiler::gen-local test-serial))
                  (no (boymoo-compiler::gen-local (+ 1 test-serial)))
                  (done (boymoo-compiler::gen-local (+ 2 test-serial)))
                  (dispatch (boymoo-compiler::reverse-onto
                             (list '(:cmp 0 34) (list :b-cond :ne yes)
                                   (list :b no) (list :label yes)) test-code)))
             (mv-let (yes-code yes-high yes-serial)
               (boymoo-compiler::gen-term yes-term scope depth nil context
                                            dispatch test-high (+ 3 test-serial))
               (mv-let (no-code no-high no-serial)
                 (boymoo-compiler::gen-term no-term scope depth nil context
                                              (cons (list :label no) (cons (list :b done) yes-code))
                                              yes-high yes-serial)
                 (mv (cons (list :label done) no-code) no-high no-serial))))))
  :hints (("Goal" :expand (boymoo-compiler::gen-term
                           (list boymoo-compiler::*if-name* test yes-term no-term)
                           scope depth nil context code high serial)
                  :in-theory (enable length boymoo-compiler::gen-simple-p boymoo-compiler::gen-emit))))
