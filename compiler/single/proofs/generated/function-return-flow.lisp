(in-package "BOYMOO-PROOFS")

(include-book "function-body-entry")
(include-book "compiled-return")
(include-book "frame-cuts")
(include-book "tail-return")
(include-book "argument-flow")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-compiled-entry-p proof-compiled-return-p proof-world-pc proof-world-reg proof-world-stop
                    proof-heap-p proof-stack-base proof-stack-top proof-stack-limit proof-machine-limit
                    proof-prefix-preserved-p proof-dynamic-table-preserved-p proof-heap-frame-p proof-reg-value-p
                    proof-environment-p proof-register-frame-p proof-segment-p proof-subspan-p proof-advance generated-before-cuts-p
                    generated-before-frame-cuts-p generated-frame-segment-p generated-at-saved-compiled-frame-p
                    generated-path-after generated-path-p generated-full-prologue-fits-path generated-sp generated-load-word
                    boymoo-compiler::gen-term boymoo-compiler::declaration-list boymoo-compiler::bind-formals
                    boymoo-model::core-eval-step expt))

(local
 (defthm generated-finish-path-with-return-contract-cuts-at-caller-frame
   (let* ((link (proof-world-reg 30 entry)) (cut (list (generated-frame-key after))))
     (implies (and (generated-path-p *generated-return-path* (list link) before)
                   (equal after (generated-path-after *generated-return-path* before))
                   (proof-compiled-return-p arity result entry after old-objects new-objects packages))
              (and (equal cut (list (cons link (generated-sp entry))))
                   (generated-frame-segment-p 3 cut before :cut after))))
   :hints (("Goal"
            :use (generated-compiled-return-observes-inherited-frame
                  (:instance generated-advance-of-placed-path (instructions *generated-return-path*)
                             (world before) (cuts (list (proof-world-reg 30 entry))))
                  (:instance generated-clear-address-prefix-is-clear-of-frame-cuts (count 3)
                             (cuts (list (proof-world-reg 30 entry)))
                             (frames (list (cons (proof-world-reg 30 entry) (generated-sp entry)))))
                  (:instance generated-frame-cut-at-exact-instruction-count (count 3)
                             (cuts (list (cons (proof-world-reg 30 entry) (generated-sp entry))))))
            :in-theory (enable proof-compiled-return-p proof-frame-return-p)))
   :rule-classes nil))

(defthm generated-body-value-and-finish-establish-frame-aware-return
  (let* ((frame (- (proof-stack-top before) (* 8 arity)))
         (link (proof-world-reg 30 before)) (return-cut (list (cons link (generated-sp before))))
         (sp (generated-sp finished)) (after (generated-path-after *generated-return-path* finished)))
    (implies (and (natp arity)
                  (boymoo-model::core-value-p result)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) (proof-world-pc finished)
                                                    ready finished old-objects new-objects packages)
                  (generated-at-saved-compiled-frame-p arity before finished)
                  (natp keep) (equal frame (+ (proof-stack-base finished) (* 8 keep))) (<= frame (proof-stack-top finished))
                  (proof-subspan-p sp 16 (generated-machine-stack-base finished) (generated-machine-stack-end finished))
                  (generated-ordinary-machine-p finished) (< (+ sp 16) (expt 2 64))
                  (generated-path-p *generated-return-path* (list link) finished)
                  (proof-prefix-preserved-p frame before finished old-objects new-objects packages)
                  (proof-dynamic-table-preserved-p t before finished old-objects new-objects packages))
             (and (generated-frame-segment-p 3 return-cut finished :cut after)
                  (proof-compiled-return-p arity result before after old-objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-finish-establishes-compiled-return-contract
                            (entry before) (before finished) (objects new-objects))
                 (:instance generated-finish-path-with-return-contract-cuts-at-caller-frame
                            (entry before) (before finished) (after (generated-path-after *generated-return-path* finished))))
           :in-theory (enable generated-at-saved-compiled-frame-p generated-nontail-value-result-p)))
  :rule-classes nil)

(local
 (defthm generated-positioned-prologue-composes-with-frame-segments
   (implies (and (generated-path-p path address-cuts before)
                 (equal ready (generated-path-after path before))
                 (subsetp-equal (strip-cars return-cuts) address-cuts)
                 (generated-frame-segment-p body-steps (cons (generated-frame-key finished) return-cuts) ready :cut finished)
                 (generated-frame-segment-p finish-steps return-cuts finished :cut after))
            (generated-frame-segment-p (+ (len path) (nfix body-steps) (nfix finish-steps)) return-cuts before :cut after))
   :hints (("Goal"
            :use ((:instance generated-advance-of-placed-path (instructions path) (world before) (cuts address-cuts))
                  (:instance generated-clear-address-prefix-is-clear-of-frame-cuts
                             (count (len path)) (cuts address-cuts) (frames return-cuts))
                  (:instance generated-frame-segments-compose-under-step-budgets
                             (before ready) (middle finished) (prefix-steps body-steps) (suffix-steps finish-steps)
                             (reason :cut) (cuts return-cuts) (prefix-cuts (cons (generated-frame-key finished) return-cuts)))
                  (:instance generated-frame-prefix-and-segment-compose
                             (prefix (len path)) (suffix (+ (nfix body-steps) (nfix finish-steps)))
                             (middle ready) (reason :cut) (cuts return-cuts)))
            :in-theory (disable generated-advance-of-placed-path)))
   :rule-classes nil))

(defthm generated-fitting-function-path-returns-to-caller-frame
  (let* ((link (proof-world-reg 30 before)) (return-cut (list (cons link (generated-sp before))))
         (frame (- (proof-stack-top before) (* 8 arity))) (sp (generated-sp finished))
         (path (generated-full-prologue-fits-path arity high)) (ready (generated-path-after path before))
         (body (+ (proof-world-pc before) (* 4 (len path)) (if (< arity high) 8 4)))
         (after (generated-path-after *generated-return-path* finished)))
    (implies (and (natp arity) (boymoo-model::core-value-p result)
                  (generated-path-p path (list body link) before)
                  (generated-frame-segment-p body-steps (cons (generated-frame-key finished) return-cut) ready :cut finished)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) (proof-world-pc finished)
                                                    ready finished old-objects new-objects packages)
                  (generated-at-saved-compiled-frame-p arity before finished)
                  (natp keep) (equal frame (+ (proof-stack-base finished) (* 8 keep))) (<= frame (proof-stack-top finished))
                  (proof-subspan-p sp 16 (generated-machine-stack-base finished) (generated-machine-stack-end finished))
                  (generated-ordinary-machine-p finished) (< (+ sp 16) (expt 2 64))
                  (generated-path-p *generated-return-path* (list link) finished)
                  (proof-prefix-preserved-p frame before finished old-objects new-objects packages)
                  (proof-dynamic-table-preserved-p t before finished old-objects new-objects packages))
             (and (generated-frame-segment-p (+ (len path) (nfix body-steps) 3) return-cut before :cut after)
                  (proof-compiled-return-p arity result before after old-objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-body-value-and-finish-establish-frame-aware-return
                            (ready (generated-path-after (generated-full-prologue-fits-path arity high) before)))
                 (:instance generated-positioned-prologue-composes-with-frame-segments
                            (path (generated-full-prologue-fits-path arity high))
                            (ready (generated-path-after (generated-full-prologue-fits-path arity high) before))
                            (address-cuts (list (+ (proof-world-pc before) (* 4 (len (generated-full-prologue-fits-path arity high)))
                                                   (if (< arity high) 8 4)) (proof-world-reg 30 before)))
                            (return-cuts (list (cons (proof-world-reg 30 before) (generated-sp before))))
                            (finish-steps 3) (after (generated-path-after *generated-return-path* finished))))))
  :rule-classes nil)

(defthm generated-fitting-definition-returns-checked-source-body
  (let* ((compiler-formals (boymoo-compiler::declaration-list (cadr definition)))
         (scope (boymoo-compiler::bind-formals compiler-formals 0 nil))
         (extra (* 8 (- high arity))) (frame (- (proof-stack-top before) (* 8 arity)))
         (link (proof-world-reg 30 before)) (return-cut (list (cons link (generated-sp before))))
         (sp (generated-sp finished)) (after (generated-path-after *generated-return-path* finished)))
    (implies (and (equal arity (len compiler-formals))
                  (equal high (mv-nth 1 (boymoo-compiler::gen-term (caddr definition) scope arity t context nil arity (+ serial 2))))
                  (equal path (generated-full-prologue-fits-path arity high))
                  (equal ready (generated-path-after path before))
                  (equal body (+ (proof-world-pc before) (* 4 (len path)) (if (< arity high) 8 4)))
                  (equal result (boymoo-model::core-eval-step :term source-body (pairlis$ formals args) program fuel))
                  (equal (len args) arity) (symbol-listp formals) (no-duplicatesp-equal formals)
                  (equal (len formals) arity) (natp high) (<= arity high)
                  (proof-compiled-entry-p (proof-world-pc before) args before old-objects packages)
                  (unsigned-byte-p 64 (* 8 arity)) (unsigned-byte-p 64 extra)
                  (<= (+ (proof-stack-top before) extra) (proof-stack-limit before))
                  (<= (proof-machine-limit before) (- (generated-sp before) 16)) (< body (expt 2 64))
                  (generated-ordinary-machine-p before) (generated-path-p path (list body link) before)
                  (boymoo-model::core-value-p result)
                  (generated-frame-segment-p body-steps (cons (generated-frame-key finished) return-cut) ready :cut finished)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) (proof-world-pc finished)
                                                    ready finished old-objects new-objects packages)
                  (generated-at-saved-compiled-frame-p arity before finished)
                  (natp keep) (equal frame (+ (proof-stack-base finished) (* 8 keep))) (<= frame (proof-stack-top finished))
                  (proof-subspan-p sp 16 (generated-machine-stack-base finished) (generated-machine-stack-end finished))
                  (generated-ordinary-machine-p finished) (< (+ sp 16) (expt 2 64))
                  (generated-path-p *generated-return-path* (list link) finished)
                  (proof-prefix-preserved-p frame before finished old-objects new-objects packages)
                  (proof-dynamic-table-preserved-p t before finished old-objects new-objects packages))
             (and (proof-environment-p (pairlis$ formals (generated-consecutive-slots arity 0))
                                       (pairlis$ formals args) frame ready old-objects packages)
                  (<= (+ frame (* 8 high)) (proof-stack-limit ready))
                  (generated-frame-segment-p (+ (len path) (nfix body-steps) 3) return-cut before :cut after)
                  (proof-compiled-return-p arity result before after old-objects new-objects packages))))
  :hints (("Goal"
           :use (generated-fitting-function-path-returns-to-caller-frame
                 (:instance generated-fitting-definition-prologue-establishes-body-bindings-and-reservation (objects old-objects))
                 (:instance generated-placed-path-allows-fewer-cuts (all-cuts (list body (proof-world-reg 30 before))) (cuts (list body))))
           :in-theory (disable generated-nontail-value-result-p)))
  :rule-classes nil)
