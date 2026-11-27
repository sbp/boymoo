(in-package "BOYMOO-PROOFS")

(include-book "term-flow")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-stop proof-world-reg proof-heap-p proof-reg-value-p
                    proof-instruction-effect proof-segment-p
                    generated-path-p generated-path-after generated-if-path
                    generated-heap-world-equiv generated-nontail-value-result-p
                    boymoo-model::core-eval-step expt))

(defthm generated-if-dispatch-preserves-heap-and-frame-observations
  (let ((after (generated-path-after (generated-if-path yes no before) before)))
    (implies (and (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no)
                  (< (+ (proof-world-pc before) 8) (expt 2 64))
                  (generated-ordinary-machine-p before))
             (and (generated-heap-world-equiv after before)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before)))))
  :hints (("Goal" :in-theory (enable generated-path-after generated-if-path)))
  :rule-classes nil)

(defthm generated-heap-equivalent-state-keeps-nontail-context
  (implies (and (generated-heap-world-equiv after before)
                (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                (proof-heap-p before objects packages)
                (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                (proof-constant-map-p quoted constants (proof-heap-base before) objects packages
                                      (proof-world-machine before)))
           (and (proof-heap-p after objects packages)
                (proof-environment-p slots env (proof-world-reg 19 after) after objects packages)
                (proof-constant-map-p quoted constants (proof-heap-base after) objects packages
                                      (proof-world-machine after))))
  :rule-classes nil)

(defthm generated-nontail-segments-compose
  (implies (and (proof-segment-p prefix-steps (cons middle-pc cuts) before :cut middle)
                (generated-nontail-value-result-p prefix-datum middle-pc
                                                  before middle old-objects middle-objects packages)
                (proof-segment-p suffix-steps cuts middle :cut after)
                (generated-nontail-value-result-p datum continuation
                                                  middle after middle-objects new-objects packages))
           (and (proof-segment-p (+ (nfix prefix-steps) (nfix suffix-steps)) cuts before :cut after)
                (generated-nontail-value-result-p datum continuation
                                                  before after old-objects new-objects packages)))
  :hints (("Goal"
           :use (generated-nontail-value-results-compose
                 (:instance generated-segment-composes-with-final-segment
                            (prefix-cuts (cons middle-pc cuts)) (reason :cut)))))
  :rule-classes nil)

(defthm generated-if-test-and-dispatch-compose
  (let* ((datum (boymoo-model::core-datum test-result))
         (selected (if datum yes no))
         (path (generated-if-path yes no tested))
         (after (generated-path-after path tested)))
    (implies (and (boymoo-model::core-value-p test-result)
                  (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no)
                  (< (+ (proof-world-pc tested) 8) (expt 2 64))
                  (generated-ordinary-machine-p tested) (not (proof-world-stop tested))
                  (member-equal selected cuts)
                  (proof-segment-p test-steps (cons test-end cuts) before :cut tested)
                  (generated-nontail-value-result-p datum test-end
                                                    before tested old-objects objects packages)
                  (generated-path-p path (list* yes no cuts) tested))
             (and (proof-segment-p (+ (nfix test-steps) (len path)) cuts before :cut after)
                  (generated-nontail-value-result-p datum selected before after old-objects objects packages)
                  (generated-heap-world-equiv after tested)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 tested)))))
  :hints (("Goal"
           :use ((:instance generated-if-dispatch-provides-nontail-result (before tested))
                 (:instance generated-nontail-segments-compose (prefix-steps test-steps) (middle-pc test-end)
                            (middle tested) (prefix-datum (boymoo-model::core-datum test-result))
                            (middle-objects objects) (new-objects objects)
                            (suffix-steps (len (generated-if-path yes no tested)))
                            (continuation (if (boymoo-model::core-datum test-result) yes no))
                            (datum (boymoo-model::core-datum test-result))
                            (after (generated-path-after (generated-if-path yes no tested) tested))))
           :in-theory (enable generated-nontail-value-result-p)))
  :rule-classes nil)

(defthm generated-if-true-arm-jump-composes
  (let ((after (proof-instruction-effect (list :branch (- continuation arm-end) nil) arm-exit)))
    (implies (and (proof-segment-p arm-steps (cons arm-end cuts) arm-start :cut arm-exit)
                  (generated-nontail-value-result-p datum arm-end arm-start arm-exit old-objects objects packages)
                  (unsigned-byte-p 64 continuation) (member-equal continuation cuts)
                  (generated-ordinary-machine-p arm-exit)
                  (generated-path-p (list (list :branch (- continuation arm-end) nil)) cuts arm-exit))
             (and (proof-segment-p (+ (nfix arm-steps) 1) cuts arm-start :cut after)
                  (generated-nontail-value-result-p datum continuation arm-start after old-objects objects packages)
                  (generated-heap-world-equiv after arm-exit)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 arm-exit)))))
  :hints (("Goal"
           :use ((:instance generated-branch-keeps-nontail-value (before arm-exit))
                 (:instance generated-nontail-segments-compose (prefix-steps arm-steps) (suffix-steps 1)
                            (middle-pc arm-end) (before arm-start) (middle arm-exit)
                            (prefix-datum datum) (middle-objects objects) (new-objects objects)
                            (after (proof-instruction-effect (list :branch (- continuation arm-end) nil) arm-exit))))
           :in-theory (enable generated-nontail-value-result-p)))
  :rule-classes nil)
