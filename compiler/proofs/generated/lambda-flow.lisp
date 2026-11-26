(in-package "BOYMOO-PROOFS")

(include-book "argument-evaluation")
(include-book "conditional-flow")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-stack-top proof-stack-base proof-environment-p proof-stack-views
                    proof-heap-base proof-world-pc proof-world-reg proof-world-machine proof-world-stop
                    proof-subspan-p proof-span-p proof-reg-value-p proof-prefix-preserved-p proof-segment-p
                    boymoo-model::core-eval-step boymoo-compiler::gen-term boymoo-compiler::gen-lambda-args
                    generated-address-path generated-path-after generated-path-p
                    generated-heap-world-equiv expt))

(defthm generated-lambda-term-emits-arguments-body-and-drop
  (let* ((head (car term)) (formals (boymoo-compiler::declaration-list (cadr head))))
    (implies (and (equal head (list "COMMON-LISP::LAMBDA" (cadr head) (caddr head)))
                  (or (consp (cadr head)) (equal (cadr head) boymoo-compiler::*nil-name*)))
             (equal (boymoo-compiler::gen-term term scope depth nil context code high serial)
                    (mv-let (arguments next-high next-serial body-scope top)
                      (boymoo-compiler::gen-lambda-args (cdr term) formals scope nil depth context code high serial)
                      (mv-let (body final-high final-serial)
                        (boymoo-compiler::gen-term (caddr head) body-scope top nil context arguments next-high next-serial)
                        (mv (boymoo-compiler::gen-drop (- top depth) body) final-high final-serial))))))
  :hints (("Goal"
           :expand (boymoo-compiler::gen-term term scope depth nil context code high serial)
           :in-theory (enable boymoo-compiler::gen-simple-p boymoo-compiler::gen-mbe-p)))
  :rule-classes nil)

(local
 (defthm generated-argument-result-keeps-caller-environment
   (let ((frame (proof-world-reg 19 before)))
     (implies (and (natp offset) (equal frame (+ (proof-stack-base before) (* 8 offset)))
                   (proof-environment-p bindings env frame before old-objects packages)
                   (generated-arguments-result-p values before after old-objects new-objects packages))
              (proof-environment-p bindings env (proof-world-reg 19 after) after new-objects packages)))
   :hints (("Goal"
            :use (:instance generated-prefix-preserves-aligned-environment (frame (proof-world-reg 19 before)))
            :in-theory (enable generated-arguments-result-p generated-same-stack-frame-p)))
   :rule-classes nil))

(defthm generated-lambda-argument-stage-provides-body-environment
  (let* ((frame (proof-world-reg 19 before))
         (result (boymoo-model::core-eval-step :terms sources caller-env program fuel))
         (values (boymoo-model::core-datum result))
         (pushed (generated-lambda-pushed-values actuals values))
         (slots (generated-lambda-slots actuals scope depth)))
    (implies (and (generated-lambda-actuals-agree-p actuals sources scope caller-bindings)
                  (symbol-listp formals) (no-duplicatesp-equal formals) (equal (len formals) (len actuals))
                  (natp offset) (equal frame (+ (proof-stack-base before) (* 8 offset)))
                  (natp depth) (equal (proof-stack-top before) (+ frame (* 8 depth)))
                  (boymoo-model::core-value-p result)
                  (proof-environment-p caller-bindings caller-env frame before old-objects packages)
                  (generated-arguments-result-p pushed before after old-objects new-objects packages))
             (proof-environment-p (pairlis$ formals slots) (pairlis$ formals values)
                                  (proof-world-reg 19 after) after new-objects packages)))
  :hints (("Goal"
           :use ((:instance generated-argument-result-keeps-caller-environment
                            (values (generated-lambda-pushed-values actuals
                                     (boymoo-model::core-datum (boymoo-model::core-eval-step :terms sources caller-env program fuel))))
                            (bindings caller-bindings) (env caller-env))
                 (:instance generated-lambda-body-environment-from-evaluated-actuals
                            (world after) (frame (proof-world-reg 19 after)) (objects new-objects)))
           :in-theory (enable generated-arguments-result-p generated-same-stack-frame-p proof-subspan-p proof-span-p
                              proof-stack-top)))
  :rule-classes nil)

(local
 (defthm generated-changing-value-top-keeps-datum-view
   (implies (generated-heap-world-equiv after (generated-set-reg 25 top before))
            (equal (proof-machine-value-p word datum after objects packages)
                   (proof-machine-value-p word datum before objects packages)))
   :hints (("Goal" :in-theory (enable generated-heap-world-equiv proof-machine-value-p proof-value-p proof-heap-base)))
   :rule-classes nil))

(defthm generated-drop-preserves-result-datum
  (let* ((bytes (* 8 drop)) (top (- (proof-stack-top before) bytes))
         (path (generated-address-path 25 25 bytes t))
         (end (+ (proof-world-pc before) (* 4 (len path)))) (after (generated-path-after path before)))
    (implies (and (natp drop) (natp keep) (unsigned-byte-p 64 bytes)
                  (equal top (+ (proof-stack-base before) (* 8 keep)))
                  (< end (expt 2 64)) (not (proof-world-stop before))
                  (proof-heap-p before objects packages) (proof-reg-value-p 0 datum before objects packages)
                  (member-equal end cuts) (generated-path-p path cuts before))
             (and (proof-segment-p (len path) cuts before :cut after)
                  (equal (proof-world-pc after) end)
                  (proof-heap-p after objects packages)
                  (generated-same-stack-frame-p before after)
                  (equal (proof-stack-top after) top)
                  (proof-prefix-preserved-p top before after objects objects packages)
                  (proof-reg-value-p 0 datum after objects packages))))
  :hints (("Goal"
           :use (generated-drop-keeps-valid-stack-prefix
                 (:instance generated-changing-value-top-keeps-datum-view
                            (word (proof-world-reg 0 before)) (top (- (proof-stack-top before) (* 8 drop)))
                            (after (generated-path-after (generated-address-path 25 25 (* 8 drop) t) before)))
                 (:instance generated-placed-path-allows-fewer-cuts
                            (path (generated-address-path 25 25 (* 8 drop) t)) (all-cuts cuts)
                            (cuts (list (+ (proof-world-pc before) (* 4 (len (generated-address-path 25 25 (* 8 drop) t)))))))
                 (:instance generated-placed-path-to-cut (instructions (generated-address-path 25 25 (* 8 drop) t))))
           :in-theory (enable generated-same-stack-frame-p proof-reg-value-p)))
  :rule-classes nil)

(local
 (defthm generated-returning-body-has-expected-drop-top
   (implies (and (generated-arguments-result-p args before ready old-objects middle-objects packages)
                 (generated-nontail-value-result-p datum body-end ready returned middle-objects objects packages))
            (equal (- (proof-stack-top returned) (* 8 (len args))) (proof-stack-top before)))
   :hints (("Goal" :in-theory (enable generated-arguments-result-p generated-nontail-value-result-p)))
   :rule-classes nil))

(local
 (defthm generated-argument-result-starts-at-valid-prefix
   (implies (generated-arguments-result-p args before ready old-objects new-objects packages)
            (proof-stack-prefix (proof-stack-top before) before old-objects packages))
   :hints (("Goal" :in-theory (enable generated-arguments-result-p proof-prefix-preserved-p)))
   :rule-classes nil))

(local
 (defthm generated-arguments-and-body-establish-drop-state
   (let* ((target-top (proof-stack-top before))
          (keep (ash (- target-top (proof-stack-base before)) -3)))
     (implies (and (generated-arguments-result-p args before ready old-objects middle-objects packages)
                   (generated-nontail-value-result-p datum (proof-world-pc returned)
                                                     ready returned middle-objects objects packages))
              (and (natp keep) (equal target-top (+ (proof-stack-base returned) (* 8 keep)))
                   (equal (- (proof-stack-top returned) (* 8 (len args))) target-top)
                   (generated-same-stack-frame-p before returned)
                   (proof-heap-p returned objects packages)
                   (proof-reg-value-p 0 datum returned objects packages)
                   (proof-prefix-preserved-p target-top before returned old-objects objects packages))))
   :hints (("Goal"
            :use ((:instance generated-stack-prefix-has-aligned-slot-count
                             (top (proof-stack-top before)) (world before) (objects old-objects))
                  (:instance generated-argument-result-starts-at-valid-prefix (new-objects middle-objects))
                  (:instance generated-returning-body-has-expected-drop-top (body-end (proof-world-pc returned)))
                  (:instance generated-prefix-preserved-at-smaller-top (before ready) (after returned)
                             (old-objects middle-objects) (new-objects objects)
                             (top (proof-stack-top before)) (retained (proof-stack-top ready))
                             (count (ash (- (proof-stack-top before) (proof-stack-base before)) -3)))
                  (:instance generated-prefix-preserved-transitive (top (proof-stack-top before))
                             (first before) (middle ready) (last returned) (first-objects old-objects) (last-objects objects)))
            :in-theory (enable generated-arguments-result-p generated-same-stack-frame-p generated-nontail-value-result-p)))
   :rule-classes nil))

(local
 (defthm generated-argument-body-and-drop-segments-compose
   (let ((ready-pc (proof-world-pc ready)) (drop-pc (proof-world-pc returned)))
     (implies (and (proof-segment-p argument-steps (list* ready-pc drop-pc cuts) before :cut ready)
                   (proof-segment-p body-steps (cons drop-pc cuts) ready :cut returned)
                   (proof-segment-p drop-steps cuts returned :cut after))
              (proof-segment-p (+ (nfix argument-steps) (nfix body-steps) (nfix drop-steps)) cuts before :cut after)))
   :hints (("Goal"
            :use ((:instance generated-segment-composes-with-final-segment (prefix-steps argument-steps) (suffix-steps body-steps)
                             (cuts (cons (proof-world-pc returned) cuts))
                             (prefix-cuts (list* (proof-world-pc ready) (proof-world-pc returned) cuts))
                             (middle ready) (after returned) (reason :cut))
                  (:instance generated-segment-composes-with-final-segment (prefix-steps (+ (nfix argument-steps) (nfix body-steps)))
                             (suffix-steps drop-steps) (prefix-cuts (cons (proof-world-pc returned) cuts))
                             (middle returned) (reason :cut)))))
   :rule-classes nil))

(defthm generated-arguments-body-and-drop-provide-nontail-result
  (let* ((ready-pc (proof-world-pc ready)) (body-end (proof-world-pc returned))
         (path (generated-address-path 25 25 (* 8 (len args)) t))
         (continuation (+ body-end (* 4 (len path)))) (after (generated-path-after path returned)))
    (implies (and (generated-arguments-result-p args before ready old-objects middle-objects packages)
                  (generated-nontail-value-result-p datum body-end ready returned middle-objects objects packages)
                  (proof-segment-p argument-steps (list* ready-pc body-end cuts) before :cut ready)
                  (proof-segment-p body-steps (cons body-end cuts) ready :cut returned)
                  (unsigned-byte-p 64 (* 8 (len args))) (< continuation (expt 2 64))
                  (not (proof-world-stop returned)) (member-equal continuation cuts)
                  (generated-path-p path cuts returned))
             (and (proof-segment-p (+ (nfix argument-steps) (nfix body-steps) (len path)) cuts before :cut after)
                  (generated-nontail-value-result-p datum continuation before after old-objects objects packages))))
  :hints (("Goal"
           :use (generated-arguments-and-body-establish-drop-state
                 (:instance generated-drop-preserves-result-datum (before returned) (drop (len args))
                            (keep (ash (- (proof-stack-top before) (proof-stack-base before)) -3)))
                 (:instance generated-prefix-preserved-transitive (top (proof-stack-top before))
                            (first before) (middle returned)
                            (last (generated-path-after (generated-address-path 25 25 (* 8 (len args)) t) returned))
                            (first-objects old-objects) (middle-objects objects) (last-objects objects))
                 (:instance generated-argument-body-and-drop-segments-compose
                            (drop-steps (len (generated-address-path 25 25 (* 8 (len args)) t)))
                            (after (generated-path-after (generated-address-path 25 25 (* 8 (len args)) t) returned))))
           :in-theory (enable generated-same-stack-frame-p generated-nontail-value-result-p)))
  :rule-classes nil)
