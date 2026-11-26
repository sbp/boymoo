(in-package "BOYMOO-PROOFS")

(include-book "defined-flow")
(include-book "tail-return")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-stop proof-label-address proof-heap-p
                    proof-compiled-entry-p proof-compiled-return-p proof-reg-value-p proof-prefix-preserved-p
                    proof-stack-base proof-stack-top proof-segment-p proof-subspan-p generated-load-word
                    generated-indexed-tail-path generated-path-after generated-path-p generated-sp expt))

(local
 (defthm generated-tail-argument-preparation-keeps-retained-prefix
   (let ((frame (proof-world-reg 19 ready)))
     (implies (and (generated-arguments-result-p args before ready old-objects objects packages)
                   (natp keep) (equal frame (+ (proof-stack-base ready) (* 8 keep)))
                   (<= frame (proof-stack-top before)))
              (and (<= (+ frame (* 8 (len args))) (proof-stack-top ready))
                   (proof-prefix-preserved-p frame before ready old-objects objects packages))))
   :hints (("Goal"
            :use (:instance generated-prefix-preserved-at-smaller-top (after ready) (new-objects objects)
                             (top (proof-world-reg 19 ready)) (retained (proof-stack-top before)) (count keep))
            :in-theory (enable generated-arguments-result-p generated-same-stack-frame-p)))
   :rule-classes nil))

(defthm generated-tail-call-composes-argument-collection-and-callee-return
  (let* ((arity (len args)) (frame (proof-world-reg 19 ready)) (sp (generated-sp ready))
         (link (generated-load-word (+ sp 8) ready)) (pc (proof-world-pc ready))
         (target (proof-label-address (list :fn name) base labels))
         (path (generated-indexed-tail-path arity target ready)) (entered (generated-path-after path ready)))
    (implies (and (generated-arguments-result-p args before ready old-objects objects packages)
                  (proof-segment-p argument-steps (list pc link) before :cut ready)
                  (natp keep) (equal frame (+ (proof-stack-base ready) (* 8 keep))) (<= frame (proof-stack-top before))
                  (proof-subspan-p sp 16 (generated-machine-stack-base ready) (generated-machine-stack-end ready))
                  (< (+ sp 16) (expt 2 64)) (< (+ pc (* 4 (len path))) (expt 2 64))
                  (unsigned-byte-p 64 target) (generated-ordinary-machine-p ready)
                  (generated-path-p path (list target link) ready)
                  (proof-segment-p callee-steps (list link) entered :cut after)
                  (proof-compiled-return-p arity result entered after objects new-objects packages))
             (and (proof-segment-p (+ (nfix argument-steps) (len path) (nfix callee-steps)) (list link) before :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 19 after) (generated-load-word sp ready))
                  (equal (proof-world-reg 30 after) link)
                  (equal (generated-sp after) (+ sp 16))
                  (equal (proof-stack-top after) frame)
                  (proof-heap-p after new-objects packages)
                  (proof-prefix-preserved-p frame before after old-objects new-objects packages)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after new-objects packages))))
  :hints (("Goal"
           :use (generated-tail-argument-preparation-keeps-retained-prefix
                 (:instance generated-collected-arguments-establish-compiled-entry (after ready) (new-objects objects))
                 (:instance generated-tail-callee-return-is-outer-return
                            (before ready) (target (proof-label-address (list :fn name) base labels)))
                 (:instance generated-prefix-preserved-transitive (top (proof-world-reg 19 ready))
                            (first before) (middle ready) (last after)
                            (first-objects old-objects) (middle-objects objects) (last-objects new-objects))
                 (:instance generated-segment-composes-with-final-segment
                            (prefix-steps argument-steps)
                            (suffix-steps (+ (len (generated-indexed-tail-path (len args)
                                                  (proof-label-address (list :fn name) base labels) ready)) (nfix callee-steps)))
                            (cuts (list (generated-load-word (+ (generated-sp ready) 8) ready)))
                            (prefix-cuts (list (proof-world-pc ready) (generated-load-word (+ (generated-sp ready) 8) ready)))
                            (middle ready) (reason :cut)))))
  :rule-classes nil)
