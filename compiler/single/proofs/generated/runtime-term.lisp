(in-package "BOYMOO-PROOFS")

(include-book "prepared-calls")
(include-book "resolved-calls")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-model::core-eval-step boymoo-model::core-attachment boymoo-model::core-mbe-call-p
                    generated-attachment-chain-p generated-simple-register-path generated-argument-register-path
                    proof-runtime-value proof-world-pc proof-world-reg proof-world-stop proof-world-machine
                    proof-segment-p proof-heap-p proof-heap-base proof-constant-map-p proof-environment-p
                    proof-stack-top generated-path-p generated-path-after generated-address-path expt))

(defund generated-runtime-application-source-p (chain terms env program fuel)
  (let* ((name (car (last chain))) (term (cons (car chain) terms))
         (arguments (boymoo-model::core-eval-step :terms terms env program (1- fuel)))
         (args (boymoo-model::core-datum arguments)))
    (and (posp fuel) (<= (len chain) (1- fuel))
         (symbolp (car chain)) (not (member-eq (car chain) '(quote if)))
         (not (boymoo-model::core-mbe-call-p term)) (boymoo-model::core-value-p arguments)
         (generated-attachment-chain-p chain args program)
         (not (boymoo-model::core-attachment name program))
         (boymoo-model::core-value-p (proof-runtime-value name args program)))))

(defthm generated-resolved-runtime-application-evaluates-source-result
  (let* ((name (car (last chain))) (term (cons (car chain) terms))
         (arguments (boymoo-model::core-eval-step :terms terms env program (1- fuel)))
         (args (boymoo-model::core-datum arguments)) (result (proof-runtime-value name args program)))
    (implies (generated-runtime-application-source-p chain terms env program fuel)
             (equal (boymoo-model::core-eval-step :term term env program fuel) result)))
  :hints (("Goal"
           :use ((:instance generated-source-named-term-evaluates-arguments-before-call (name (car chain)))
                 (:instance generated-resolved-source-call-evaluates-runtime-value (fuel (1- fuel))
                            (args (boymoo-model::core-datum (boymoo-model::core-eval-step :terms terms env program (1- fuel))))))
           :in-theory (enable generated-runtime-application-source-p boymoo-model::core-value-p)))
  :rule-classes nil)

(defthm generated-simple-runtime-application-returns-source-result
  (let* ((name (car (last chain))) (source (cons (car chain) sources))
         (arguments (boymoo-model::core-eval-step :terms sources env program (1- fuel)))
         (args (boymoo-model::core-datum arguments)) (routine-value (proof-runtime-value name args program))
         (result (boymoo-model::core-eval-step :term source env program fuel))
         (path (generated-simple-register-path terms 0 scope constants)) (ready (generated-path-after path before))
         (ready-pc (+ (proof-world-pc before) (* 4 (len path)))))
    (implies (and (generated-runtime-application-source-p chain sources env program fuel)
                  (generated-simple-operands-agree-p terms sources scope slots quoted) (<= (len terms) 17)
                  (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                  (proof-constant-map-p quoted constants (proof-heap-base before) objects packages (proof-world-machine before))
                  (proof-heap-p before objects packages) (< ready-pc (expt 2 64)) (not (proof-world-stop before))
                  (generated-path-p path (cons ready-pc cuts) before)
                  (proof-segment-p routine-steps cuts ready :cut after)
                  (generated-nontail-value-result-p (boymoo-model::core-datum routine-value) continuation
                                                    ready after objects new-objects packages))
             (and (proof-register-arguments-p args 0 ready objects packages)
                  (proof-segment-p (+ (len path) (nfix routine-steps)) cuts before :cut after)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                    before after objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-resolved-runtime-application-evaluates-source-result (terms sources))
                 (:instance generated-simple-evaluated-arguments-and-routine-compose (fuel (1- fuel)) (name (car (last chain)))))
           :in-theory (enable generated-runtime-application-source-p)))
  :rule-classes nil)

(defthm generated-computed-runtime-application-returns-source-result
  (let* ((name (car (last chain))) (source (cons (car chain) sources))
         (arguments (boymoo-model::core-eval-step :terms sources env program (1- fuel)))
         (args (boymoo-model::core-datum arguments)) (routine-value (proof-runtime-value name args program))
         (result (boymoo-model::core-eval-step :term source env program fuel))
         (count (len args)) (prepare (generated-argument-register-path count depth 0))
         (loaded (generated-path-after prepare ready)) (ready-pc (proof-world-pc ready))
         (routine-pc (+ ready-pc (* 4 (len prepare))))
         (drop-pc (proof-world-pc returned)) (drop-path (generated-address-path 25 25 (* 8 count) t))
         (continuation (+ drop-pc (* 4 (len drop-path)))) (after (generated-path-after drop-path returned)))
    (implies (and (generated-runtime-application-source-p chain sources env program fuel)
                  (proof-heap-p before old-objects packages) (proof-heap-p ready objects packages)
                  (generated-argument-trace-p terms sources nil env program (1- fuel) before old-objects
                                               ready objects packages (list* ready-pc drop-pc cuts) trace)
                  (not (proof-world-stop ready)) (equal (proof-stack-top before) (+ (proof-world-reg 19 ready) (* 8 depth)))
                  (natp depth) (natp routine-steps) (<= count 17) (< (* 8 (+ depth count)) (expt 2 64))
                  (< routine-pc (expt 2 64)) (generated-path-p prepare (list* routine-pc drop-pc cuts) ready)
                  (proof-segment-p routine-steps (cons drop-pc cuts) loaded :cut returned)
                  (generated-nontail-value-result-p (boymoo-model::core-datum routine-value) drop-pc
                                                    loaded returned objects new-objects packages)
                  (unsigned-byte-p 64 (* 8 count)) (< continuation (expt 2 64)) (member-equal continuation cuts)
                  (not (proof-world-stop returned)) (generated-path-p drop-path cuts returned))
             (and (proof-register-arguments-p args 0 loaded objects packages)
                  (proof-segment-p (+ (generated-argument-trace-budget trace) (len prepare) (nfix routine-steps) (len drop-path))
                                   cuts before :cut after)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                    before after old-objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-resolved-runtime-application-evaluates-source-result (terms sources))
                 (:instance generated-argument-trace-evaluates-in-source-order
                            (alias-p nil) (actuals terms) (fuel (1- fuel)) (objects old-objects) (after ready) (new-objects objects)
                            (cuts (list* (proof-world-pc ready) (proof-world-pc returned) cuts)))
                 (:instance generated-computed-arguments-routine-and-drop-compose
                            (name (car (last chain))) (argument-steps (generated-argument-trace-budget trace))
                            (args (boymoo-model::core-datum (boymoo-model::core-eval-step :terms sources env program (1- fuel))))))
           :in-theory (enable generated-runtime-application-source-p)))
  :rule-classes nil)
