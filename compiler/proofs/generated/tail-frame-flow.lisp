(in-package "BOYMOO-PROOFS")

(include-book "frame-cuts")
(include-book "tail-return")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-compiled-entry-p proof-compiled-return-p proof-reg-value-p proof-prefix-preserved-p
                    proof-heap-p proof-world-pc proof-world-reg proof-world-machine proof-stack-top proof-stack-base
                    proof-subspan-p proof-advance proof-segment-p generated-before-cuts-p generated-before-frame-cuts-p
                    generated-frame-segment-p generated-indexed-tail-path generated-path-after generated-path-p
                    generated-sp generated-load-word expt))

(defthm generated-tail-transfer-reaches-original-return-frame
  (let* ((arity (len args)) (bytes (* 8 arity))
         (frame (proof-world-reg 19 before)) (sp (generated-sp before))
         (saved-frame (generated-load-word sp before)) (link (generated-load-word (+ sp 8) before))
         (path (generated-indexed-tail-path arity target before)) (entry (generated-path-after path before))
         (cuts (list target link)) (return-cut (list (cons link (+ sp 16)))))
    (implies (and (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
                  (natp keep) (equal frame (+ (proof-stack-base before) (* 8 keep)))
                  (<= (+ frame bytes) (proof-stack-top before))
                  (proof-subspan-p sp 16 (generated-machine-stack-base before) (generated-machine-stack-end before))
                  (< (+ sp 16) (expt 2 64)) (< (+ (proof-world-pc before) (* 4 (len path))) (expt 2 64))
                  (unsigned-byte-p 64 target) (generated-ordinary-machine-p before)
                  (generated-path-p path cuts before)
                  (generated-frame-segment-p callee-steps return-cut entry :cut after)
                  (proof-compiled-return-p arity result entry after objects new-objects packages))
             (and (proof-compiled-entry-p target args entry objects packages)
                  (generated-frame-segment-p (+ (len path) (nfix callee-steps)) return-cut before :cut after)
                  (equal (generated-frame-key after) (car return-cut))
                  (equal (proof-world-reg 19 after) saved-frame)
                  (equal (proof-world-reg 30 after) link)
                  (equal (proof-stack-top after) frame)
                  (proof-heap-p after new-objects packages)
                  (proof-prefix-preserved-p frame before after objects new-objects packages)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-placed-path-allows-fewer-cuts
                            (path (generated-indexed-tail-path (len args) target before)) (cuts (list target))
                            (all-cuts (list target (generated-load-word (+ (generated-sp before) 8) before))))
                 generated-indexed-tail-establishes-entry-and-preserves-heap
                 (:instance generated-compiled-return-observes-inherited-frame
                            (arity (len args)) (old-objects objects)
                            (entry (generated-path-after (generated-indexed-tail-path (len args) target before) before)))
                 (:instance generated-advance-of-placed-path
                            (instructions (generated-indexed-tail-path (len args) target before)) (world before)
                            (cuts (list target (generated-load-word (+ (generated-sp before) 8) before))))
                 (:instance generated-clear-address-prefix-is-clear-of-frame-cuts
                            (count (len (generated-indexed-tail-path (len args) target before)))
                            (cuts (list target (generated-load-word (+ (generated-sp before) 8) before)))
                            (frames (list (cons (generated-load-word (+ (generated-sp before) 8) before) (+ (generated-sp before) 16)))))
                 (:instance generated-frame-prefix-and-segment-compose
                            (prefix (len (generated-indexed-tail-path (len args) target before))) (suffix callee-steps)
                            (middle (generated-path-after (generated-indexed-tail-path (len args) target before) before))
                            (cuts (list (cons (generated-load-word (+ (generated-sp before) 8) before) (+ (generated-sp before) 16))))
                            (reason :cut))
                 (:instance generated-prefix-preserved-transitive
                            (top (proof-world-reg 19 before)) (first before) (last after)
                            (middle (generated-path-after (generated-indexed-tail-path (len args) target before) before))
                            (first-objects objects) (middle-objects objects) (last-objects new-objects)))
           :in-theory (disable generated-advance-of-placed-path generated-cut-is-segment)))
  :rule-classes nil)
