(in-package "BOYMOO-PROOFS")

(include-book "argument-flow")
(include-book "compound-terms")
(include-book "simple-registers")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-stop proof-world-machine
                    proof-instruction-effect proof-segment-p proof-heap-p proof-stack-top
                    proof-stack-base proof-stack-prefix proof-prefix-preserved-p proof-reg-value-p
                    proof-machine-value-p generated-heap-world-equiv
                    generated-sp generated-path-after generated-path-p generated-if-path
                    generated-simple-operand-path boymoo-model::core-eval-step expt))

(defthm generated-heap-equivalent-state-provides-value-result
  (implies (and (proof-heap-p before objects packages)
                (generated-heap-world-equiv after before)
                (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                (proof-reg-value-p 0 datum after objects packages))
           (generated-nontail-value-result-p datum (proof-world-pc after)
                                             before after objects objects packages))
  :hints (("Goal" :use (:instance generated-heap-has-layout-and-roots (world before))
                  :in-theory (enable generated-nontail-value-result-p generated-same-stack-frame-p
                                     proof-prefix-preserved-p)))
  :rule-classes nil)

(defthm generated-nontail-value-results-compose
  (implies (and (generated-nontail-value-result-p prefix-datum middle-pc
                                                 before middle old-objects middle-objects packages)
                (generated-nontail-value-result-p datum continuation
                                                 middle after middle-objects new-objects packages))
           (generated-nontail-value-result-p datum continuation
                                             before after old-objects new-objects packages))
  :hints (("Goal"
           :use ((:instance generated-prefix-preserved-transitive (top (proof-stack-top before))
                            (first before) (last after) (first-objects old-objects) (last-objects new-objects)))
           :in-theory (enable generated-nontail-value-result-p generated-same-stack-frame-p)))
  :rule-classes nil)

(local
 (defthm generated-source-simple-term-has-loaded-value
   (let ((result (boymoo-model::core-eval-step :term source env program fuel)))
     (implies (and (boymoo-model::core-value-p result)
                   (generated-simple-operand-agrees-p term source scope slots quoted))
              (equal result (boymoo-model::core-value (generated-simple-source-value source env)))))
   :hints (("Goal"
            :expand (boymoo-model::core-eval-step :term source env program fuel)
            :in-theory (enable generated-simple-operand-agrees-p generated-variable-text-p)))
   :rule-classes nil))

(defthm generated-simple-term-emits-linked-operand-items
  (let ((constants (caddr context)))
    (implies (and (generated-simple-operand-agrees-p term source scope slots quoted)
                  (proof-constant-map-p quoted constants base objects packages machine))
             (equal (boymoo-compiler::gen-term term scope depth nil context code high serial)
                    (mv (boymoo-compiler::reverse-onto (generated-simple-operand-items term 0 scope constants) code)
                        high serial))))
  :hints (("Goal"
           :use ((:instance generated-simple-operand-emission (register 0) (constants (caddr context))))
           :expand (boymoo-compiler::gen-term term scope depth nil context code high serial)
           :in-theory (e/d (generated-simple-operand-agrees-p generated-variable-text-p
                            boymoo-compiler::gen-simple-p boymoo-compiler::gen-finish)
                           (boymoo-compiler::gen-simple generated-simple-operand-items))))
  :rule-classes nil)

(defthm generated-simple-term-provides-nontail-result
  (let* ((path (generated-simple-operand-path term 0 scope constants))
         (after (generated-path-after path before))
         (continuation (+ (proof-world-pc before) (* 4 (len path))))
         (result (boymoo-model::core-eval-step :term source env program fuel)))
    (implies (and (boymoo-model::core-value-p result)
                  (generated-simple-operand-agrees-p term source scope slots quoted)
                  (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                  (proof-constant-map-p quoted constants (proof-heap-base before) objects packages
                                        (proof-world-machine before))
                  (proof-heap-p before objects packages) (not (proof-world-stop before))
                  (< continuation (expt 2 64)) (member-equal continuation cuts)
                  (generated-path-p path cuts before))
             (and (proof-segment-p (len path) cuts before :cut after)
                  (generated-heap-world-equiv after before)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                    before after objects objects packages))))
  :hints (("Goal"
           :use (generated-source-simple-term-has-loaded-value
                 (:instance generated-simple-operand-loads-value (register 0) (other 19))
                 (:instance generated-heap-equivalent-state-provides-value-result
                            (datum (generated-simple-source-value source env))
                            (after (generated-path-after (generated-simple-operand-path term 0 scope constants) before)))
                 (:instance generated-placed-path-to-cut
                            (instructions (generated-simple-operand-path term 0 scope constants))))
           :in-theory (e/d (generated-heap-world-equiv) (generated-simple-source-value))))
  :rule-classes nil)

(local
 (defthm generated-if-dispatch-keeps-frame-register
   (implies (and (generated-ordinary-machine-p before) (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no)
                 (< (+ (proof-world-pc before) 8) (expt 2 64)))
            (equal (proof-world-reg 19 (generated-path-after (generated-if-path yes no before) before))
                   (proof-world-reg 19 before)))
   :hints (("Goal" :in-theory (enable generated-path-after generated-if-path)))))

(defthm generated-if-dispatch-provides-nontail-result
  (let* ((path (generated-if-path yes no before)) (after (generated-path-after path before))
         (datum (boymoo-model::core-datum test-result)) (selected (if datum yes no)))
    (implies (and (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no) (boymoo-model::core-value-p test-result)
                  (< (+ (proof-world-pc before) 8) (expt 2 64)) (generated-ordinary-machine-p before)
                  (not (proof-world-stop before)) (proof-heap-p before objects packages)
                  (proof-reg-value-p 0 datum before objects packages)
                  (member-equal selected cuts) (generated-path-p path (list* yes no cuts) before))
             (and (proof-segment-p (len path) cuts before :cut after)
                  (generated-heap-world-equiv after before)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (generated-nontail-value-result-p datum selected before after objects objects packages))))
  :hints (("Goal"
           :use (generated-if-dispatch-in-published-heap
                 (:instance generated-placed-path-allows-fewer-cuts
                            (path (generated-if-path yes no before)) (all-cuts (list* yes no cuts)) (cuts (list yes no)))
                 (:instance generated-placed-path-allows-fewer-cuts
                            (path (generated-if-path yes no before)) (all-cuts (list* yes no cuts)))
                 (:instance generated-placed-path-to-cut (instructions (generated-if-path yes no before)))
                 (:instance generated-heap-equivalent-state-provides-value-result
                            (datum (boymoo-model::core-datum test-result))
                            (after (generated-path-after (generated-if-path yes no before) before))))
           :in-theory (enable proof-reg-value-p)))
  :rule-classes nil)

(defthm generated-branch-keeps-nontail-value
  (let* ((pc (proof-world-pc before)) (instruction (list :branch (- continuation pc) nil))
         (after (proof-instruction-effect instruction before)))
    (implies (and (unsigned-byte-p 64 continuation) (generated-ordinary-machine-p before)
                  (proof-heap-p before objects packages) (proof-reg-value-p 0 datum before objects packages)
                  (member-equal continuation cuts) (generated-path-p (list instruction) cuts before))
             (and (proof-segment-p 1 cuts before :cut after)
                  (generated-heap-world-equiv after before)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before))
                  (generated-nontail-value-result-p datum continuation before after objects objects packages))))
  :hints (("Goal"
           :use ((:instance generated-placed-path-to-cut
                            (instructions (list (list :branch (- continuation (proof-world-pc before)) nil))))
                 (:instance generated-heap-equivalent-state-provides-value-result (datum datum)
                            (after (proof-instruction-effect (list :branch (- continuation (proof-world-pc before)) nil) before))))
           :in-theory (enable generated-path-p generated-path-after proof-reg-value-p)))
  :rule-classes nil)
