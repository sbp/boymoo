(in-package "BOYMOO-PROOFS")

(include-book "frame-cuts")
(include-book "named-calls")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-stop proof-world-reg proof-label-address proof-compiled-entry-p
                    proof-compiled-return-p proof-segment-p generated-before-frame-cuts-p generated-frame-segment-p
                    generated-sp generated-link-to boymoo-compiler::gen-defined-call
                    boymoo-model::core-eval-step boymoo-model::core-definition boymoo-model::core-attachment
                    boymoo-model::core-prelude boymoo-model::core-primitive boymoo-model::core-mbe-call-p
                    generated-attachment-chain-p expt))

(local
 (defthm generated-active-single-step-has-count-one
   (implies (and (not (proof-world-stop world)) (not (member-equal (proof-world-pc world) cuts)))
            (equal (generated-run-step-count 1 cuts world) 1))
   :hints (("Goal"
            :expand (generated-run-step-count 1 cuts world)
            :in-theory (enable generated-run-step-count)))))

(defthm generated-frame-cut-call-restores-the-original-caller
  (let* ((pc (proof-world-pc ready)) (target (proof-label-address (list :fn name) base labels))
         (entered (generated-link-to target ready)) (continuation (+ pc 4))
         (return-cut (list (cons continuation (generated-sp ready))))
         (item (car (boymoo-compiler::gen-defined-call name (len args) nil nil))))
    (implies (and (generated-arguments-result-p args before ready old-objects objects packages)
                  (unsigned-byte-p 64 target) (< continuation (expt 2 64))
                  (generated-ordinary-machine-p ready) (not (proof-world-stop ready)) (not (equal pc target))
                  (generated-linked-item-p item (list :branch (- target pc) t) pc base labels ready)
                  (generated-frame-segment-p callee-steps return-cut entered :cut after)
                  (proof-compiled-return-p (len args) result entered after objects new-objects packages))
             (and (proof-compiled-entry-p target args entered objects packages)
                  (generated-frame-segment-p (+ 1 (nfix callee-steps)) return-cut ready :cut after)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                    before after old-objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-collected-arguments-establish-compiled-entry (after ready) (new-objects objects))
                 (:instance generated-defined-call-establishes-entry (before ready))
                 (:instance generated-defined-return-consumes-argument-suffix
                            (target (proof-label-address (list :fn name) base labels)))
                 (:instance generated-address-prefix-composes-with-frame-segment (prefix-steps 1) (frame-steps callee-steps)
                            (address-cuts (list (proof-label-address (list :fn name) base labels) (+ 4 (proof-world-pc ready))))
                            (before ready) (middle (generated-link-to (proof-label-address (list :fn name) base labels) ready))
                            (frames (list (cons (+ 4 (proof-world-pc ready)) (generated-sp ready)))) (reason :cut))
                 (:instance generated-branch-with-link-transfer (address 0) (before ready)
                            (target (proof-label-address (list :fn name) base labels))
                            (cuts (list (proof-label-address (list :fn name) base labels) (+ 4 (proof-world-pc ready))))))
           :in-theory (disable generated-run-step-count)))
  :rule-classes nil)

(defthm generated-frame-cut-call-composes-with-argument-collection
  (let* ((pc (proof-world-pc ready)) (target (proof-label-address (list :fn name) base labels))
         (entered (generated-link-to target ready)) (continuation (+ pc 4))
         (return-cut (list (cons continuation (generated-sp ready))))
         (item (car (boymoo-compiler::gen-defined-call name (len args) nil nil))))
    (implies (and (generated-arguments-result-p args before ready old-objects objects packages)
                  (generated-frame-segment-p argument-steps (cons (generated-frame-key ready) return-cut) before :cut ready)
                  (unsigned-byte-p 64 target) (< continuation (expt 2 64))
                  (generated-ordinary-machine-p ready) (not (proof-world-stop ready)) (not (equal pc target))
                  (generated-linked-item-p item (list :branch (- target pc) t) pc base labels ready)
                  (generated-frame-segment-p callee-steps return-cut entered :cut after)
                  (proof-compiled-return-p (len args) result entered after objects new-objects packages))
             (and (proof-compiled-entry-p target args entered objects packages)
                  (generated-frame-segment-p (+ (nfix argument-steps) 1 (nfix callee-steps)) return-cut before :cut after)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                    before after old-objects new-objects packages))))
  :hints (("Goal"
           :use (generated-frame-cut-call-restores-the-original-caller
                 (:instance generated-frame-segments-compose-under-step-budgets (prefix-steps argument-steps)
                            (suffix-steps (+ 1 (nfix callee-steps)))
                            (cuts (list (cons (+ 4 (proof-world-pc ready)) (generated-sp ready))))
                            (prefix-cuts (list (generated-frame-key ready) (cons (+ 4 (proof-world-pc ready)) (generated-sp ready))))
                            (middle ready) (reason :cut)))))
  :rule-classes nil)

(defthm generated-resolved-call-with-frame-cut-returns-source-value
  (let* ((source-name (car chain)) (target-name (car (last chain)))
         (source (cons source-name terms)) (def (boymoo-model::core-definition target-name program))
         (arg-result (boymoo-model::core-eval-step :terms terms env program (1- fuel)))
         (args (boymoo-model::core-datum arg-result)) (body-fuel (- (1- fuel) (len chain)))
         (body-result (boymoo-model::core-eval-step :term (caddr def) (pairlis$ (cadr def) args) program body-fuel))
         (result (boymoo-model::core-eval-step :term source env program fuel))
         (pc (proof-world-pc ready)) (continuation (+ pc 4)) (return-cut (list (cons continuation (generated-sp ready))))
         (target (proof-label-address (list :fn name) base labels)) (entered (generated-link-to target ready))
         (item (car (boymoo-compiler::gen-defined-call name (len args) nil nil))))
    (implies (and (posp fuel) (<= (len chain) (1- fuel)) (symbolp source-name)
                  (not (member-eq source-name '(quote if))) (not (boymoo-model::core-mbe-call-p source))
                  (boymoo-model::core-value-p arg-result) (generated-attachment-chain-p chain args program)
                  (not (boymoo-model::core-attachment target-name program)) def
                  (not (boymoo-model::core-primitive target-name args program)) (not (boymoo-model::core-prelude target-name args))
                  (generated-variable-text-p name target-name) (equal (len args) (len (cadr def)))
                  (generated-arguments-result-p args before ready old-objects objects packages)
                  (generated-frame-segment-p argument-steps (cons (generated-frame-key ready) return-cut) before :cut ready)
                  (unsigned-byte-p 64 target) (< continuation (expt 2 64))
                  (generated-ordinary-machine-p ready) (not (proof-world-stop ready)) (not (equal pc target))
                  (generated-linked-item-p item (list :branch (- target pc) t) pc base labels ready)
                  (generated-frame-segment-p callee-steps return-cut entered :cut after)
                  (proof-compiled-return-p (len args) body-result entered after objects new-objects packages))
             (and (natp body-fuel) (< body-fuel fuel)
                  (proof-compiled-entry-p target args entered objects packages)
                  (generated-frame-segment-p (+ (nfix argument-steps) 1 (nfix callee-steps)) return-cut before :cut after)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                    before after old-objects new-objects packages))))
  :hints (("Goal"
           :use (generated-resolved-named-term-evaluates-defined-body-at-smaller-fuel
                 (:instance generated-frame-cut-call-composes-with-argument-collection
                            (args (boymoo-model::core-datum (boymoo-model::core-eval-step :terms terms env program (1- fuel))))
                            (result (boymoo-model::core-eval-step :term (caddr (boymoo-model::core-definition (car (last chain)) program))
                                     (pairlis$ (cadr (boymoo-model::core-definition (car (last chain)) program))
                                               (boymoo-model::core-datum (boymoo-model::core-eval-step :terms terms env program (1- fuel))))
                                     program (- (1- fuel) (len chain))))))))
  :rule-classes nil)
