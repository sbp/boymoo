(in-package "BOYMOO-PROOFS")

(include-book "conditional-flow")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-stop proof-heap-p proof-segment-p proof-instruction-effect
                    generated-path-p generated-path-after generated-if-path generated-nontail-value-result-p
                    boymoo-model::core-eval-step unsigned-byte-p expt))

(local
 (defthm generated-selected-arm-segment-reaches-final-continuation
   (let* ((arm-end (if truth jump continuation)) (arm-cuts (if truth (cons jump cuts) cuts))
          (branch (list :branch (- continuation jump) nil)))
     (implies (and (natp arm-steps) (unsigned-byte-p 64 continuation) (member-equal continuation cuts)
                   (proof-segment-p arm-steps arm-cuts entered :cut returned)
                   (generated-nontail-value-result-p datum arm-end entered returned old-objects objects packages)
                   (if truth
                       (and (generated-ordinary-machine-p returned) (generated-path-p (list branch) cuts returned)
                            (equal after (proof-instruction-effect branch returned)))
                     (equal after returned)))
              (and (proof-segment-p (+ arm-steps (if truth 1 0)) cuts entered :cut after)
                   (generated-nontail-value-result-p datum continuation entered after old-objects objects packages))))
   :hints (("Goal" :use (:instance generated-if-true-arm-jump-composes
                                    (arm-start entered) (arm-end jump) (arm-exit returned))))
   :rule-classes nil))

(defthm generated-conditional-evaluation-selects-and-returns-source-value
  (let* ((test-result (boymoo-model::core-eval-step :term test env program (1- fuel)))
         (truth (boymoo-model::core-datum test-result)) (selected (if truth yes no))
         (selected-term (if truth yes-term no-term))
         (arm-result (boymoo-model::core-eval-step :term selected-term env program (1- fuel)))
         (result (boymoo-model::core-eval-step :term (list 'if test yes-term no-term) env program fuel))
         (test-end (proof-world-pc tested)) (dispatch (generated-if-path yes no tested))
         (entered (generated-path-after dispatch tested)) (arm-end (if truth jump continuation))
         (arm-cuts (if truth (cons jump cuts) cuts)) (branch (list :branch (- continuation jump) nil)))
    (implies (and (posp fuel) (boymoo-model::core-value-p test-result) (boymoo-model::core-value-p arm-result)
                  (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no) (unsigned-byte-p 64 continuation)
                  (natp test-steps) (natp arm-steps) (member-equal continuation cuts)
                  (< (+ test-end 8) (expt 2 64)) (generated-ordinary-machine-p tested) (not (proof-world-stop tested))
                  (proof-segment-p test-steps (list* test-end selected cuts) before :cut tested)
                  (generated-nontail-value-result-p truth test-end before tested old-objects objects packages)
                  (generated-path-p dispatch (list* yes no selected cuts) tested)
                  (proof-segment-p arm-steps arm-cuts entered :cut returned)
                  (generated-nontail-value-result-p (boymoo-model::core-datum arm-result) arm-end
                                                    entered returned objects new-objects packages)
                  (if truth
                      (and (generated-ordinary-machine-p returned) (generated-path-p (list branch) cuts returned)
                           (equal after (proof-instruction-effect branch returned)))
                    (equal after returned)))
             (and (proof-segment-p (+ test-steps (len dispatch) arm-steps (if truth 1 0)) cuts before :cut after)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                    before after old-objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-if-test-and-dispatch-compose (test-end (proof-world-pc tested))
                            (test-result (boymoo-model::core-eval-step :term test env program (1- fuel)))
                            (cuts (cons (if (boymoo-model::core-datum (boymoo-model::core-eval-step :term test env program (1- fuel)))
                                            yes no) cuts)))
                 (:instance generated-selected-arm-segment-reaches-final-continuation
                            (old-objects objects) (objects new-objects)
                            (truth (boymoo-model::core-datum (boymoo-model::core-eval-step :term test env program (1- fuel))))
                            (datum (boymoo-model::core-datum
                                    (boymoo-model::core-eval-step :term (if (boymoo-model::core-datum
                                                                            (boymoo-model::core-eval-step :term test env program (1- fuel)))
                                                                           yes-term no-term) env program (1- fuel))))
                            (entered (generated-path-after (generated-if-path yes no tested) tested)))
                 (:instance generated-nontail-segments-compose
                            (prefix-steps (+ test-steps (len (generated-if-path yes no tested))))
                            (suffix-steps (+ arm-steps (if (boymoo-model::core-datum
                                                           (boymoo-model::core-eval-step :term test env program (1- fuel))) 1 0)))
                            (middle-pc (if (boymoo-model::core-datum (boymoo-model::core-eval-step :term test env program (1- fuel))) yes no))
                            (middle (generated-path-after (generated-if-path yes no tested) tested))
                            (prefix-datum (boymoo-model::core-datum (boymoo-model::core-eval-step :term test env program (1- fuel))))
                            (middle-objects objects)
                            (datum (boymoo-model::core-datum
                                    (boymoo-model::core-eval-step :term (list 'if test yes-term no-term) env program fuel)))))))
  :rule-classes nil)
