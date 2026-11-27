(in-package "BOYMOO-PROOFS")

(include-book "argument-flow")
(include-book "calls")
(include-book "growth")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-stop proof-world-machine proof-stack-base
                    proof-stack-top proof-stack-prefix proof-label-address proof-heap-p proof-compiled-entry-p
                    proof-compiled-return-p proof-frame-return-p proof-heap-frame-p proof-register-frame-p
                    proof-prefix-preserved-p proof-segment-p proof-reg-value-p generated-link-to generated-sp
                    generated-path-p generated-path-after generated-value-top-is-x25 boymoo-model::a64-unsigned expt))

(local
 (defthm generated-argument-count-recovers-old-top
   (implies (generated-arguments-result-p args before after old-objects new-objects packages)
            (equal (- (proof-stack-top after) (* 8 (len args))) (proof-stack-top before)))
   :hints (("Goal" :in-theory (enable generated-arguments-result-p)))
   :rule-classes nil))

(defthm generated-collected-arguments-establish-compiled-entry
  (implies (generated-arguments-result-p args before after old-objects new-objects packages)
           (proof-compiled-entry-p (proof-world-pc after) args after new-objects packages))
  :hints (("Goal"
           :use (generated-argument-count-recovers-old-top
                 (:instance generated-stack-prefix-has-aligned-slot-count
                            (world before) (objects old-objects) (top (proof-stack-top before))))
           :in-theory (enable generated-arguments-result-p generated-same-stack-frame-p
                              proof-compiled-entry-p proof-prefix-preserved-p)))
  :rule-classes nil)

(defthm generated-defined-return-consumes-argument-suffix
  (let* ((arity (len args)) (entry (generated-link-to target ready))
         (continuation (+ 4 (proof-world-pc ready))))
    (implies (and (generated-arguments-result-p args before ready old-objects objects packages)
                  (< continuation (expt 2 64))
                  (proof-compiled-return-p arity result entry after objects new-objects packages))
             (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                               before after old-objects new-objects packages)))
  :hints (("Goal"
           :use ((:instance generated-argument-count-recovers-old-top (after ready) (new-objects objects))
                 (:instance generated-defined-call-returns-to-continuation
                            (before ready) (arity (len args)) (old-objects objects))
                 (:instance generated-register-in-preserved-frame (register 19) (last 30)
                            (before (generated-link-to target ready))
                            (clobbers (append *proof-volatile-registers* '(24 25 26 27))))
                 (:instance generated-prefix-preserved-transitive (top (proof-stack-top before))
                            (first before) (middle ready) (last after)
                            (first-objects old-objects) (middle-objects objects) (last-objects new-objects)))
           :in-theory (e/d (proof-compiled-return-p proof-frame-return-p proof-heap-frame-p generated-link-to
                                                  generated-nontail-value-result-p generated-arguments-result-p
                                                  generated-same-stack-frame-p proof-prefix-preserved-p)
                           (proof-dynamic-table-preserved-p proof-stack-views))))
  :rule-classes nil)

(defthm generated-ordinary-call-composes-arguments-link-and-return
  (let* ((pc (proof-world-pc ready)) (target (proof-label-address (list :fn name) base labels))
         (entered (generated-link-to target ready))
         (continuation (+ pc 4)) (item (car (boymoo-compiler::gen-defined-call name (len args) nil nil))))
    (implies (and (generated-arguments-result-p args before ready old-objects objects packages)
                  (proof-segment-p argument-steps (cons pc cuts) before :cut ready)
                  (unsigned-byte-p 64 target) (< continuation (expt 2 64))
                  (generated-ordinary-machine-p ready) (not (proof-world-stop ready))
                  (not (equal pc target)) (not (member-equal pc cuts)) (member-equal continuation cuts)
                  (generated-linked-item-p item (list :branch (- target pc) t) pc base labels ready)
                  (proof-segment-p callee-steps cuts entered :cut after)
                  (proof-compiled-return-p (len args) result entered after objects new-objects packages))
             (and (proof-compiled-entry-p target args entered objects packages)
                  (proof-segment-p (+ (nfix argument-steps) 1 (nfix callee-steps)) cuts before :cut after)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                    before after old-objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-collected-arguments-establish-compiled-entry (after ready) (new-objects objects))
                 (:instance generated-defined-call-establishes-entry (before ready))
                 (:instance generated-defined-return-consumes-argument-suffix
                            (target (proof-label-address (list :fn name) base labels)))
                 (:instance generated-branch-with-link-transfer (address 0) (before ready)
                            (target (proof-label-address (list :fn name) base labels))
                            (cuts (cons (proof-label-address (list :fn name) base labels) cuts)))
                 (:instance generated-segment-composes-with-final-segment (prefix-steps 1) (suffix-steps callee-steps)
                            (prefix-cuts (cons (proof-label-address (list :fn name) base labels) cuts))
                            (before ready) (middle (generated-link-to (proof-label-address (list :fn name) base labels) ready))
                            (reason :cut))
                 (:instance generated-segment-composes-with-final-segment (prefix-steps argument-steps)
                            (suffix-steps (+ 1 (nfix callee-steps))) (prefix-cuts (cons (proof-world-pc ready) cuts))
                            (middle ready) (reason :cut)))
           :in-theory (disable boymoo-compiler::gen-defined-call)))
  :rule-classes nil)
