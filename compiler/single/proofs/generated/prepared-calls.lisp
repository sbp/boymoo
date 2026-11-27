(in-package "BOYMOO-PROOFS")

(include-book "runtime-flow")
(include-book "simple-registers")
(include-book "lambda-flow")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-stack-base proof-stack-top proof-stack-prefix proof-prefix-preserved-p
                    proof-stack-views proof-heap-base proof-reg-value-p proof-register-arguments-p
                    proof-world-pc proof-world-reg proof-world-stop proof-world-machine proof-segment-p
                    generated-path-after generated-path-p generated-heap-world-equiv generated-value-top-is-x25
                    generated-argument-register-path generated-simple-register-path
                    proof-runtime-value proof-runtime-entry proof-runtime-return-p
                    proof-label-address generated-link-to boymoo-model::core-eval-step expt))

(defthm generated-collected-arguments-load-runtime-registers
  (let* ((count (len args)) (path (generated-argument-register-path count depth 0))
         (after (generated-path-after path ready)) (end (+ (proof-world-pc ready) (* 4 (len path)))))
    (implies (and (generated-arguments-result-p args before ready old-objects objects packages)
                  (equal (proof-stack-top before) (+ (proof-world-reg 19 ready) (* 8 depth)))
                  (natp depth) (<= count 17) (< (* 8 (+ depth count)) (expt 2 64)) (< end (expt 2 64))
                  (not (proof-world-stop ready)) (member-equal end cuts) (generated-path-p path cuts ready))
             (and (proof-segment-p (len path) cuts ready :cut after)
                  (equal (proof-world-pc after) end)
                  (proof-register-arguments-p args 0 after objects packages)
                  (generated-heap-world-equiv after ready)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 ready)))))
  :hints (("Goal"
           :use ((:instance generated-argument-registers-load-views (register 0) (slot depth) (before ready))
                 (:instance generated-argument-register-path-preserves-fields
                            (count (len args)) (register 0) (slot depth) (before ready) (other 19))
                 (:instance generated-placed-path-allows-fewer-cuts (all-cuts cuts) (before ready)
                            (path (generated-argument-register-path (len args) depth 0))
                            (cuts (list (+ (proof-world-pc ready) (* 4 (len (generated-argument-register-path (len args) depth 0)))))))
                 (:instance generated-placed-path-to-cut
                            (instructions (generated-argument-register-path (len args) depth 0)) (before ready)))
           :in-theory (enable generated-arguments-result-p)))
  :rule-classes nil)

(defthm generated-heap-equivalent-prefix-and-runtime-value-segment-compose
  (implies (and (proof-heap-p before old-objects packages)
                (generated-heap-world-equiv ready before)
                (equal (proof-world-reg 19 ready) (proof-world-reg 19 before))
                (proof-segment-p preparation-steps (cons (proof-world-pc ready) cuts) before :cut ready)
                (proof-segment-p routine-steps cuts ready :cut after)
                (generated-nontail-value-result-p datum continuation ready after old-objects new-objects packages))
           (and (proof-segment-p (+ (nfix preparation-steps) (nfix routine-steps)) cuts before :cut after)
                (generated-nontail-value-result-p datum continuation before after old-objects new-objects packages)))
  :hints (("Goal"
           :use ((:instance generated-segment-composes-with-final-segment
                            (prefix-steps preparation-steps) (suffix-steps routine-steps)
                            (middle ready) (prefix-cuts (cons (proof-world-pc ready) cuts)) (reason :cut))
                 (:instance generated-heap-has-layout-and-roots (world before) (objects old-objects))
                 (:instance generated-prefix-preserved-transitive
                            (first before) (middle ready) (last after) (top (proof-stack-top before))
                            (first-objects old-objects) (middle-objects old-objects) (last-objects new-objects)))
           :in-theory (enable generated-nontail-value-result-p generated-same-stack-frame-p proof-prefix-preserved-p)))
  :rule-classes nil)

(defthm generated-simple-evaluated-arguments-and-routine-compose
  (let* ((args-result (boymoo-model::core-eval-step :terms sources env program fuel))
         (args (boymoo-model::core-datum args-result))
         (path (generated-simple-register-path terms 0 scope constants))
         (ready (generated-path-after path before))
         (ready-pc (+ (proof-world-pc before) (* 4 (len path))))
         (datum (boymoo-model::core-datum (proof-runtime-value name args program))))
    (implies (and (generated-simple-operands-agree-p terms sources scope slots quoted) (<= (len terms) 17)
                  (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                  (proof-constant-map-p quoted constants (proof-heap-base before) objects packages (proof-world-machine before))
                  (boymoo-model::core-value-p args-result) (proof-heap-p before objects packages)
                  (< ready-pc (expt 2 64)) (not (proof-world-stop before))
                  (generated-path-p path (cons ready-pc cuts) before)
                  (proof-segment-p routine-steps cuts ready :cut after)
                  (generated-nontail-value-result-p datum continuation ready after objects new-objects packages))
             (and (proof-register-arguments-p args 0 ready objects packages)
                  (proof-segment-p (+ (len path) (nfix routine-steps)) cuts before :cut after)
                  (generated-nontail-value-result-p datum continuation before after objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-simple-registers-load-source-arguments (register 0))
                 (:instance generated-placed-path-allows-fewer-cuts
                            (path (generated-simple-register-path terms 0 scope constants))
                            (all-cuts (cons (+ (proof-world-pc before)
                                             (* 4 (len (generated-simple-register-path terms 0 scope constants)))) cuts))
                            (cuts (list (+ (proof-world-pc before)
                                           (* 4 (len (generated-simple-register-path terms 0 scope constants)))))))
                 (:instance generated-placed-path-to-cut (instructions (generated-simple-register-path terms 0 scope constants))
                            (cuts (cons (+ (proof-world-pc before)
                                           (* 4 (len (generated-simple-register-path terms 0 scope constants)))) cuts)))
                 (:instance generated-heap-equivalent-prefix-and-runtime-value-segment-compose
                            (ready (generated-path-after (generated-simple-register-path terms 0 scope constants) before))
                            (preparation-steps (len (generated-simple-register-path terms 0 scope constants))) (old-objects objects)
                            (datum (boymoo-model::core-datum
                                    (proof-runtime-value name (boymoo-model::core-datum
                                                               (boymoo-model::core-eval-step :terms sources env program fuel)) program)))))))
  :rule-classes nil)

(defthm generated-computed-runtime-term-emits-arguments-registers-and-drop
  (let* ((arity (length terms)) (info (boymoo-compiler::gen-call-info head context))
         (name (mv-nth 0 info)) (label (mv-nth 2 info)))
    (implies (and (stringp head) (not (equal head boymoo-compiler::*quote-name*))
                  (not (equal head boymoo-compiler::*if-name*)) (not (boymoo-compiler::gen-mbe-p head terms))
                  (equal (mv-nth 1 info) arity) label (not (boymoo-compiler::gen-simple-args-p terms)))
             (equal (boymoo-compiler::gen-term (cons head terms) scope depth nil context code high serial)
                    (mv-let (args-code arg-high arg-serial)
                      (boymoo-compiler::gen-args terms scope depth context code high serial)
                      (mv-let (routine-code next-serial)
                        (boymoo-compiler::gen-routine name label arg-serial
                                                      (boymoo-compiler::gen-argument-registers arity depth 0 args-code))
                        (mv (boymoo-compiler::gen-drop arity routine-code) arg-high next-serial))))))
  :hints (("Goal"
           :expand (boymoo-compiler::gen-term (cons head terms) scope depth nil context code high serial)
           :in-theory (e/d (boymoo-compiler::gen-simple-p length)
                           (boymoo-compiler::gen-call-info boymoo-compiler::gen-routine boymoo-compiler::gen-args
                            boymoo-compiler::gen-simple-args-p boymoo-compiler::gen-mbe-p))))
  :rule-classes nil)

(local
 (defthm generated-computed-argument-registers-and-routine-compose
   (let* ((count (len args)) (prepare (generated-argument-register-path count depth 0))
          (loaded (generated-path-after prepare ready))
          (entry (+ (proof-world-pc ready) (* 4 (len prepare))))
          (continuation (proof-world-pc returned)))
     (implies (and (generated-arguments-result-p args before ready old-objects objects packages)
                   (proof-heap-p ready objects packages) (not (proof-world-stop ready))
                   (equal (proof-stack-top before) (+ (proof-world-reg 19 ready) (* 8 depth)))
                   (natp depth) (natp routine-steps) (<= count 17)
                   (< (* 8 (+ depth count)) (expt 2 64)) (< entry (expt 2 64))
                   (generated-path-p prepare (cons entry cuts) ready)
                   (proof-segment-p routine-steps cuts loaded :cut returned)
                   (generated-nontail-value-result-p datum continuation loaded returned objects new-objects packages))
              (and (proof-register-arguments-p args 0 loaded objects packages)
                   (proof-segment-p (+ (len prepare) (nfix routine-steps)) cuts ready :cut returned)
                   (generated-nontail-value-result-p datum continuation ready returned objects new-objects packages))))
   :hints (("Goal"
            :use ((:instance generated-collected-arguments-load-runtime-registers
                             (cuts (cons (+ (proof-world-pc ready) (* 4 (len (generated-argument-register-path (len args) depth 0)))) cuts)))
                  (:instance generated-argument-register-path-preserves-fields
                             (count (len args)) (slot depth) (register 0) (before ready) (other 19))
                  (:instance generated-placed-path-to-cut
                             (instructions (generated-argument-register-path (len args) depth 0)) (before ready)
                             (cuts (cons (+ (proof-world-pc ready) (* 4 (len (generated-argument-register-path (len args) depth 0)))) cuts)))
                  (:instance generated-heap-equivalent-prefix-and-runtime-value-segment-compose
                             (preparation-steps (len (generated-argument-register-path (len args) depth 0)))
                             (before ready) (ready (generated-path-after (generated-argument-register-path (len args) depth 0) ready))
                             (after returned) (continuation (proof-world-pc returned)) (old-objects objects)))
            :do-not-induct t))
   :rule-classes nil))

(defthm generated-computed-arguments-routine-and-drop-compose
  (let* ((count (len args)) (prepare (generated-argument-register-path count depth 0))
         (loaded (generated-path-after prepare ready))
         (routine-pc (+ (proof-world-pc ready) (* 4 (len prepare))))
         (drop-pc (proof-world-pc returned)) (drop-path (generated-address-path 25 25 (* 8 count) t))
         (continuation (+ drop-pc (* 4 (len drop-path)))) (after (generated-path-after drop-path returned))
         (datum (boymoo-model::core-datum (proof-runtime-value name args program))))
    (implies (and (generated-arguments-result-p args before ready old-objects objects packages)
                  (proof-heap-p ready objects packages) (not (proof-world-stop ready))
                  (proof-segment-p argument-steps (list* (proof-world-pc ready) drop-pc cuts) before :cut ready)
                  (equal (proof-stack-top before) (+ (proof-world-reg 19 ready) (* 8 depth)))
                  (natp depth) (natp routine-steps) (<= count 17)
                  (< (* 8 (+ depth count)) (expt 2 64)) (< routine-pc (expt 2 64))
                  (generated-path-p prepare (list* routine-pc drop-pc cuts) ready)
                  (proof-segment-p routine-steps (cons drop-pc cuts) loaded :cut returned)
                  (generated-nontail-value-result-p datum drop-pc loaded returned objects new-objects packages)
                  (unsigned-byte-p 64 (* 8 count)) (< continuation (expt 2 64)) (member-equal continuation cuts)
                  (not (proof-world-stop returned)) (generated-path-p drop-path cuts returned))
             (and (proof-register-arguments-p args 0 loaded objects packages)
                  (proof-segment-p (+ (nfix argument-steps) (len prepare) (nfix routine-steps) (len drop-path))
                                   cuts before :cut after)
                  (generated-nontail-value-result-p datum continuation before after old-objects new-objects packages))))
  :hints (("Goal"
           :use ((:instance generated-computed-argument-registers-and-routine-compose
                            (datum (boymoo-model::core-datum (proof-runtime-value name args program)))
                            (cuts (cons (proof-world-pc returned) cuts)))
                 (:instance generated-arguments-body-and-drop-provide-nontail-result
                            (datum (boymoo-model::core-datum (proof-runtime-value name args program)))
                            (middle-objects objects) (objects new-objects)
                            (body-steps (+ (len (generated-argument-register-path (len args) depth 0)) (nfix routine-steps)))))
           :in-theory (disable generated-address-path)
           :do-not-induct t))
  :rule-classes nil)
