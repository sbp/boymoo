(in-package "BOYMOO-PROOFS")

(include-book "resolved-calls")
(include-book "argument-evaluation")
(include-book "tail-return")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-model::core-eval-step boymoo-model::core-attachment boymoo-model::core-definition
                    boymoo-model::core-primitive boymoo-model::core-prelude boymoo-model::core-mbe-call-p
                    proof-world-pc proof-world-reg proof-world-stop proof-label-address proof-compiled-entry-p
                    proof-compiled-return-p proof-heap-p proof-segment-p generated-link-to generated-sp
                    generated-attachment-chain-p boymoo-compiler::gen-defined-call expt))

(defthm generated-resolved-ordinary-call-returns-source-value
  (let* ((source-name (car chain)) (target-name (car (last chain)))
         (source (cons source-name sources)) (def (boymoo-model::core-definition target-name program))
         (arg-result (boymoo-model::core-eval-step :terms sources env program (1- fuel)))
         (args (boymoo-model::core-datum arg-result)) (body-fuel (- (1- fuel) (len chain)))
         (body-result (boymoo-model::core-eval-step :term (caddr def) (pairlis$ (cadr def) args) program body-fuel))
         (result (boymoo-model::core-eval-step :term source env program fuel))
         (pc (proof-world-pc ready)) (target (proof-label-address (list :fn name) base labels))
         (return-pc (+ pc 4)) (entered (generated-link-to target ready))
         (item (car (boymoo-compiler::gen-defined-call name (len args) nil nil))))
    (implies (and (posp fuel) (<= (len chain) (1- fuel)) (symbolp source-name)
                  (not (member-eq source-name '(quote if))) (not (boymoo-model::core-mbe-call-p source))
                  (boymoo-model::core-value-p arg-result) (generated-attachment-chain-p chain args program)
                  (not (boymoo-model::core-attachment target-name program)) def
                  (not (boymoo-model::core-primitive target-name args program))
                  (not (boymoo-model::core-prelude target-name args))
                  (generated-variable-text-p name target-name) (equal (len args) (len (cadr def)))
                  (proof-heap-p before old-objects packages)
                  (generated-argument-trace-p actuals sources nil env program (1- fuel)
                                               before old-objects ready objects packages (cons pc cuts) trace)
                  (unsigned-byte-p 64 target) (< return-pc (expt 2 64))
                  (generated-ordinary-machine-p ready) (not (proof-world-stop ready))
                  (not (equal pc target)) (not (member-equal pc cuts)) (member-equal return-pc cuts)
                  (generated-linked-item-p item (list :branch (- target pc) t) pc base labels ready)
                  (proof-segment-p callee-steps cuts entered :cut after)
                  (proof-compiled-return-p (len args) body-result entered after objects new-objects packages))
             (and (natp body-fuel) (< body-fuel fuel)
                  (proof-compiled-entry-p target args entered objects packages)
                  (proof-segment-p (+ (generated-argument-trace-budget trace) 1 (nfix callee-steps)) cuts before :cut after)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) return-pc
                                                    before after old-objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-resolved-named-term-evaluates-defined-body-at-smaller-fuel (terms sources))
                 (:instance generated-argument-trace-evaluates-in-source-order (alias-p nil) (fuel (1- fuel))
                            (objects old-objects) (after ready) (new-objects objects) (cuts (cons (proof-world-pc ready) cuts)))
                 (:instance generated-ordinary-call-composes-arguments-link-and-return
                            (args (boymoo-model::core-datum (boymoo-model::core-eval-step :terms sources env program (1- fuel))))
                            (result (boymoo-model::core-eval-step :term (caddr (boymoo-model::core-definition (car (last chain)) program))
                                     (pairlis$ (cadr (boymoo-model::core-definition (car (last chain)) program))
                                               (boymoo-model::core-datum (boymoo-model::core-eval-step :terms sources env program (1- fuel))))
                                     program (- (1- fuel) (len chain))))
                            (argument-steps (generated-argument-trace-budget trace))))))
  :rule-classes nil)
