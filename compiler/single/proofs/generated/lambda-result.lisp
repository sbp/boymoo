(in-package "BOYMOO-PROOFS")

(include-book "lambda-flow")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-model::core-eval-step boymoo-compiler::gen-term boymoo-compiler::gen-lambda-args
                    proof-world-pc proof-world-reg proof-world-stop proof-heap-p proof-stack-top proof-stack-base
                    proof-environment-p proof-segment-p generated-address-path generated-path-after generated-path-p expt))

(defthm generated-lambda-pushed-values-have-emitted-slot-count
  (equal (len (generated-lambda-pushed-values actuals values)) (generated-lambda-push-count actuals))
  :hints (("Goal" :induct (generated-lambda-pushed-values actuals values))))

(defthm generated-lambda-drop-matches-number-of-pushed-actuals
  (let* ((argument-code (boymoo-compiler::gen-lambda-args
                        actuals formals scope nil depth context code high serial))
         (top (mv-nth 4 argument-code)))
    (implies (and (natp depth) (equal (len formals) (len actuals)))
             (equal (- top depth) (len (generated-lambda-pushed-values actuals values)))))
  :hints (("Goal"
           :use (:instance generated-lambda-arguments-install-aliased-and-pushed-slots
                           (args actuals) (body-scope nil))
           :in-theory (disable generated-lambda-arguments-install-aliased-and-pushed-slots)))
  :rule-classes nil)

(defthm generated-lambda-argument-and-body-traces-return-source-value
  (let* ((argument-fuel (1- fuel))
         (arg-result (boymoo-model::core-eval-step :terms sources caller-env program argument-fuel))
         (values (boymoo-model::core-datum arg-result))
         (pushed (generated-lambda-pushed-values actuals values))
         (slots (generated-lambda-slots actuals scope depth))
         (body-env (pairlis$ formals values))
         (body-result (boymoo-model::core-eval-step :term body body-env program argument-fuel))
         (source (cons (list 'lambda formals body) sources))
         (result (boymoo-model::core-eval-step :term source caller-env program fuel))
         (body-pc (proof-world-pc ready)) (drop-pc (proof-world-pc returned))
         (drop-bytes (* 8 (len pushed))) (drop-path (generated-address-path 25 25 drop-bytes t))
         (continuation (+ drop-pc (* 4 (len drop-path)))) (after (generated-path-after drop-path returned)))
    (implies (and (posp fuel) (boymoo-model::core-value-p arg-result) (boymoo-model::core-value-p body-result)
                  (generated-lambda-actuals-agree-p actuals sources scope caller-bindings)
                  (symbol-listp formals) (no-duplicatesp-equal formals) (equal (len formals) (len actuals))
                  (natp offset) (equal (proof-world-reg 19 before) (+ (proof-stack-base before) (* 8 offset)))
                  (natp depth) (equal (proof-stack-top before) (+ (proof-world-reg 19 before) (* 8 depth)))
                  (proof-heap-p before old-objects packages)
                  (proof-environment-p caller-bindings caller-env (proof-world-reg 19 before) before old-objects packages)
                  (generated-argument-trace-p actuals sources t caller-env program argument-fuel
                                               before old-objects ready middle-objects packages (list* body-pc drop-pc cuts) trace)
                  (generated-nontail-value-result-p (boymoo-model::core-datum body-result) drop-pc
                                                    ready returned middle-objects objects packages)
                  (proof-segment-p body-steps (cons drop-pc cuts) ready :cut returned)
                  (unsigned-byte-p 64 drop-bytes) (< continuation (expt 2 64)) (member-equal continuation cuts)
                  (not (proof-world-stop returned)) (generated-path-p drop-path cuts returned))
             (and (proof-environment-p (pairlis$ formals slots) body-env (proof-world-reg 19 ready)
                                       ready middle-objects packages)
                  (proof-segment-p (+ (generated-argument-trace-budget trace) (nfix body-steps) (len drop-path))
                                   cuts before :cut after)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                    before after old-objects objects packages))))
  :hints (("Goal"
           :use ((:instance generated-argument-trace-evaluates-in-source-order (alias-p t) (fuel (1- fuel))
                            (env caller-env) (objects old-objects) (after ready) (new-objects middle-objects)
                            (cuts (list* (proof-world-pc ready) (proof-world-pc returned) cuts)))
                 (:instance generated-lambda-argument-stage-provides-body-environment (fuel (1- fuel))
                            (after ready) (new-objects middle-objects))
                 (:instance generated-arguments-body-and-drop-provide-nontail-result
                            (args (generated-lambda-pushed-values actuals
                                   (boymoo-model::core-datum (boymoo-model::core-eval-step :terms sources caller-env program (1- fuel)))))
                            (datum (boymoo-model::core-datum
                                    (boymoo-model::core-eval-step :term body
                                     (pairlis$ formals (boymoo-model::core-datum
                                                       (boymoo-model::core-eval-step :terms sources caller-env program (1- fuel))))
                                     program (1- fuel))))
                            (argument-steps (generated-argument-trace-budget trace)))
                 (:instance generated-source-lambda (actuals sources) (env caller-env)))
           :in-theory (disable generated-lambda-pushed-values generated-lambda-slots generated-lambda-push-count)))
  :rule-classes nil)
