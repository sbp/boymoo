(in-package "BOYMOO-PROOFS")

(include-book "tail-frame")
(include-book "growth")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-compiled-entry-p proof-compiled-return-p proof-register-frame-p proof-frame-return-p
                    proof-reg-value-p proof-prefix-preserved-p proof-heap-p proof-world-pc proof-world-reg
                    proof-world-stop proof-world-machine proof-stack-top proof-stack-base
                    proof-segment-p proof-advance proof-subspan-p generated-before-cuts-p
                    generated-indexed-tail-path generated-indexed-tail-prefix generated-path-after generated-path-p
                    generated-sp generated-load-word expt))

(defthm generated-compiled-return-observes-inherited-frame
  (let ((top (- (proof-stack-top entry) (* 8 arity))))
    (implies (proof-compiled-return-p arity result entry after old-objects new-objects packages)
             (and (equal (proof-world-pc after) (proof-world-reg 30 entry))
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 entry))
                  (equal (proof-world-reg 30 after) (proof-world-reg 30 entry))
                  (equal (generated-sp after) (generated-sp entry))
                  (equal (proof-stack-top after) top)
                  (proof-heap-p after new-objects packages)
                  (proof-prefix-preserved-p top entry after old-objects new-objects packages)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-register-in-preserved-frame
                            (register 19) (last 30) (before entry)
                            (clobbers (append *proof-volatile-registers* '(24 25 26 27))))
                 (:instance generated-register-in-preserved-frame
                            (register 30) (last 30) (before entry)
                            (clobbers (append *proof-volatile-registers* '(24 25 26 27)))))
           :in-theory (enable proof-compiled-return-p proof-frame-return-p generated-heap-machine-sp)))
  :rule-classes nil)

(defthm generated-tail-callee-return-is-outer-return
  (let* ((arity (len args)) (bytes (* 8 arity))
         (frame (proof-world-reg 19 before)) (sp (generated-sp before))
         (saved-frame (generated-load-word sp before))
         (link (generated-load-word (+ sp 8) before))
         (path (generated-indexed-tail-path arity target before))
         (entry (generated-path-after path before)))
    (implies (and (proof-compiled-entry-p (proof-world-pc before) args before objects packages)
                  (natp keep) (equal frame (+ (proof-stack-base before) (* 8 keep)))
                  (<= (+ frame bytes) (proof-stack-top before))
                  (proof-subspan-p sp 16 (generated-machine-stack-base before) (generated-machine-stack-end before))
                  (< (+ sp 16) (expt 2 64)) (< (+ (proof-world-pc before) (* 4 (len path))) (expt 2 64))
                  (unsigned-byte-p 64 target) (generated-ordinary-machine-p before)
                  (generated-path-p path (list target link) before)
                  (proof-segment-p callee-steps (list link) entry :cut after)
                  (proof-compiled-return-p arity result entry after objects new-objects packages))
             (and (proof-segment-p (+ (len path) (nfix callee-steps)) (list link) before :cut after)
                  (equal (proof-world-pc after) link)
                  (equal (proof-world-reg 19 after) saved-frame)
                  (equal (proof-world-reg 30 after) link)
                  (equal (generated-sp after) (+ sp 16))
                  (equal (proof-stack-top after) frame)
                  (proof-heap-p after new-objects packages)
                  (proof-prefix-preserved-p frame before after objects new-objects packages)
                  (proof-reg-value-p 0 (boymoo-model::core-datum result) after new-objects packages))))
  :hints (("Goal"
           :use (generated-indexed-tail-establishes-entry-and-preserves-heap
                 (:instance generated-compiled-return-observes-inherited-frame
                            (arity (len args)) (old-objects objects)
                            (entry (generated-path-after (generated-indexed-tail-path (len args) target before) before)))
                 (:instance generated-placed-path-allows-fewer-cuts
                            (path (generated-indexed-tail-path (len args) target before)) (cuts (list target))
                            (all-cuts (list target (generated-load-word (+ (generated-sp before) 8) before))))
                 (:instance generated-placed-path-allows-fewer-cuts
                            (path (generated-indexed-tail-path (len args) target before))
                            (cuts (list (generated-load-word (+ (generated-sp before) 8) before)))
                            (all-cuts (list target (generated-load-word (+ (generated-sp before) 8) before))))
                 (:instance generated-prefix-then-segment
                            (prefix (len (generated-indexed-tail-path (len args) target before))) (suffix callee-steps)
                            (middle (generated-path-after (generated-indexed-tail-path (len args) target before) before))
                            (cuts (list (generated-load-word (+ (generated-sp before) 8) before))) (reason :cut))
                 (:instance generated-prefix-preserved-transitive
                            (top (proof-world-reg 19 before)) (first before) (last after)
                            (middle (generated-path-after (generated-indexed-tail-path (len args) target before) before))
                            (first-objects objects) (middle-objects objects) (last-objects new-objects)))
           :in-theory (disable generated-cut-is-segment)))
  :rule-classes nil)
