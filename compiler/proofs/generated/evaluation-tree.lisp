(in-package "BOYMOO-PROOFS")

(include-book "noncall-terms")
(include-book "lambda-result")
(include-book "conditional-result")
(include-book "named-calls")
(include-book "runtime-term")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-model::core-eval-step boymoo-model::core-mbe-call-p
                    boymoo-compiler::gen-simple-p boymoo-compiler::gen-mbe-p boymoo-compiler::declaration-list
                    proof-world-pc proof-world-reg proof-world-stop proof-world-machine proof-heap-p proof-heap-base
                    proof-stack-top proof-stack-base proof-stack-limit proof-environment-p proof-constant-map-p
                    proof-compiled-return-p proof-label-address generated-link-to generated-attachment-chain-p
                    proof-runtime-value generated-simple-register-path generated-argument-register-path
                    boymoo-model::core-definition boymoo-model::core-attachment boymoo-model::core-prelude
                    boymoo-model::core-primitive boymoo-compiler::gen-defined-call
                    proof-segment-p proof-instruction-effect generated-path-p generated-path-after generated-if-path generated-address-path
                    generated-lambda-pushed-values generated-lambda-slots generated-bind-slots expt))

; A lambda node gives the argument state, its object map, an argument tree,
; and the corresponding operand records. It also gives the body state, its
; object map, its step bound, and its term tree. A computed operand uses one
; term tree and one operand record. A variable alias consumes neither.
; A conditional gives the arm and jump addresses and two evaluation records.
; An ordinary call gives the resolution chain, linked target, argument
; records, and the named callee's return segment.
; A routine takes direct register operands or an argument tree followed by
; register loads. The routine segment supplies its result at the continuation
; or at the drop instruction that removes the computed arguments.
(defund generated-evaluation-tree-p (kind tree operands term source scope slots quoted constants
                                           env program fuel before objects after new-objects packages
                                           continuation cuts steps)
  (declare (xargs :measure (nfix fuel) :ruler-extenders :all))
  (and
   (posp fuel)
   (case kind
     (:term
      (and
       (boymoo-model::core-value-p (boymoo-model::core-eval-step :term source env program fuel))
       (case (car tree)
         (:pure
          (let ((path (cadr tree)))
            (and (equal objects new-objects) (proof-heap-p before objects packages)
                 (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                 (proof-constant-map-p quoted constants (proof-heap-base before) objects packages
                                       (proof-world-machine before))
                 (generated-noncall-context-agrees-p path term source scope slots quoted env program fuel)
                 (generated-noncall-trace-p path term source scope constants env program fuel before after
                                            continuation cuts steps))))
         (:mbe
          (and (not (boymoo-compiler::gen-simple-p term))
               (boymoo-compiler::gen-mbe-p (car term) (cdr term)) (equal (length (cdr term)) 3)
               (boymoo-model::core-mbe-call-p source)
               (generated-evaluation-tree-p :term (cadr tree) nil (cadddr term) (cadddr source)
                                            scope slots quoted constants env program (1- fuel)
                                            before objects after new-objects packages continuation cuts steps)))
         (:lambda
          (let* ((bindings (cadr tree)) (argument-data (caddr tree)) (body-data (cadddr tree))
                 (offset (car bindings)) (depth (cadr bindings))
                 (ready (car argument-data)) (argument-objects (cadr argument-data))
                 (argument-tree (caddr argument-data)) (argument-records (cadddr argument-data))
                 (returned (car body-data)) (body-objects (cadr body-data))
                 (body-steps (caddr body-data)) (body-tree (cadddr body-data))
                 (actuals (cdr term)) (sources (cdr source)) (formals (cadar source)) (body (caddar source))
                 (compiler-formals (boymoo-compiler::declaration-list (cadar term)))
                 (body-slots (generated-lambda-slots actuals scope depth))
                 (body-scope (generated-bind-slots compiler-formals body-slots nil))
                 (args-result (boymoo-model::core-eval-step :terms sources env program (1- fuel)))
                 (values (boymoo-model::core-datum args-result)) (body-env (pairlis$ formals values))
                 (pushed (generated-lambda-pushed-values actuals values))
                 (frame (proof-world-reg 19 before)) (drop-bytes (* 8 (len pushed)))
                 (drop-path (generated-address-path 25 25 drop-bytes t))
                 (body-pc (proof-world-pc ready)) (drop-pc (proof-world-pc returned)))
            (and (equal (car term) (list "COMMON-LISP::LAMBDA" (cadar term) (caddar term)))
                 (or (consp (cadar term)) (equal (cadar term) boymoo-compiler::*nil-name*))
                 (equal (car source) (list 'lambda formals body))
                 (symbol-listp formals) (no-duplicatesp-equal formals)
                 (equal (len formals) (len actuals)) (equal (len compiler-formals) (len actuals))
                 (generated-lambda-actuals-agree-p actuals sources scope slots)
                 (natp offset) (equal frame (+ (proof-stack-base before) (* 8 offset)))
                 (natp depth) (equal (proof-stack-top before) (+ frame (* 8 depth)))
                 (proof-heap-p before objects packages)
                 (proof-environment-p slots env frame before objects packages)
                 (boymoo-model::core-value-p args-result)
                 (boymoo-model::core-value-p (boymoo-model::core-eval-step :term body body-env program (1- fuel)))
                 (generated-evaluation-tree-p :lambda-args argument-tree argument-records actuals sources
                                               scope slots quoted constants env program (1- fuel)
                                               before objects ready argument-objects packages body-pc
                                               (list* body-pc drop-pc cuts) (generated-argument-trace-budget argument-records))
                 (generated-evaluation-tree-p :term body-tree nil (caddar term) body body-scope
                                               (pairlis$ formals body-slots) quoted constants body-env program (1- fuel)
                                               ready argument-objects returned body-objects packages drop-pc
                                               (cons drop-pc cuts) body-steps)
                 (unsigned-byte-p 64 drop-bytes) (not (proof-world-stop returned))
                 (equal continuation (+ drop-pc (* 4 (len drop-path))))
                 (< continuation (expt 2 64)) (member-equal continuation cuts)
                 (generated-path-p drop-path cuts returned) (equal after (generated-path-after drop-path returned))
                 (equal new-objects body-objects)
                 (equal steps (+ (generated-argument-trace-budget argument-records) (nfix body-steps) (len drop-path))))))
         (:if
          (let* ((addresses (cadr tree)) (test-data (caddr tree)) (arm-data (cadddr tree))
                 (yes (car addresses)) (no (cadr addresses)) (jump (caddr addresses))
                 (tested (car test-data)) (test-objects (cadr test-data)) (test-steps (caddr test-data))
                 (returned (car arm-data)) (arm-steps (cadr arm-data))
                 (test-result (boymoo-model::core-eval-step :term (cadr source) env program (1- fuel)))
                 (truth (boymoo-model::core-datum test-result)) (selected (if truth yes no))
                 (test-end (proof-world-pc tested)) (dispatch (generated-if-path yes no tested))
                 (entered (generated-path-after dispatch tested))
                 (arm-term (if truth (caddr term) (cadddr term)))
                 (arm-source (if truth (caddr source) (cadddr source)))
                 (arm-end (if truth jump continuation)) (arm-cuts (if truth (cons jump cuts) cuts))
                 (branch (list :branch (- continuation jump) nil)))
            (and (equal term (list boymoo-compiler::*if-name* (cadr term) (caddr term) (cadddr term)))
                 (equal source (list 'if (cadr source) (caddr source) (cadddr source)))
                 (boymoo-model::core-value-p test-result)
                 (boymoo-model::core-value-p (boymoo-model::core-eval-step :term arm-source env program (1- fuel)))
                 (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no) (unsigned-byte-p 64 continuation)
                 (natp test-steps) (natp arm-steps) (member-equal continuation cuts)
                 (< (+ 8 test-end) (expt 2 64)) (generated-ordinary-machine-p tested) (not (proof-world-stop tested))
                 (generated-evaluation-tree-p :term (cadddr test-data) nil (cadr term) (cadr source)
                                               scope slots quoted constants env program (1- fuel) before objects
                                               tested test-objects packages test-end (list* test-end selected cuts) test-steps)
                 (generated-path-p dispatch (list* yes no selected cuts) tested)
                 (generated-evaluation-tree-p :term (caddr arm-data) nil arm-term arm-source scope slots quoted constants
                                               env program (1- fuel) entered test-objects returned new-objects packages
                                               arm-end arm-cuts arm-steps)
                 (if truth
                     (and (generated-ordinary-machine-p returned) (generated-path-p (list branch) cuts returned)
                          (equal after (proof-instruction-effect branch returned)))
                   (equal after returned))
                 (equal steps (+ test-steps (len dispatch) arm-steps (if truth 1 0))))))
         (:ordinary-call
          (let* ((route (cadr tree)) (argument-data (caddr tree))
                 (chain (car route)) (name (cadr route)) (base (caddr route)) (labels (cadddr route))
                 (ready (car argument-data)) (argument-objects (cadr argument-data))
                 (argument-records (cadddr argument-data)) (callee-steps (cadddr tree))
                 (pc (proof-world-pc ready)) (target (proof-label-address (list :fn name) base labels))
                 (entered (generated-link-to target ready))
                 (resolved (car (last chain))) (definition (boymoo-model::core-definition resolved program))
                 (arg-result (boymoo-model::core-eval-step :terms (cdr source) env program (1- fuel)))
                 (args (boymoo-model::core-datum arg-result))
                 (body-fuel (- (1- fuel) (len chain)))
                 (body-result (boymoo-model::core-eval-step :term (caddr definition)
                               (pairlis$ (cadr definition) args) program body-fuel))
                 (item (car (boymoo-compiler::gen-defined-call name (len args) nil nil))))
            (and (consp term) (consp source) (equal (car source) (car chain))
                 (generated-variable-text-p (car term) (car source))
                 (symbolp (car source)) (not (member-eq (car source) '(quote if)))
                 (not (boymoo-model::core-mbe-call-p source))
                 (<= (len chain) (1- fuel)) (boymoo-model::core-value-p arg-result)
                 (generated-attachment-chain-p chain args program) definition
                 (not (boymoo-model::core-attachment resolved program))
                 (not (boymoo-model::core-primitive resolved args program))
                 (not (boymoo-model::core-prelude resolved args))
                 (generated-variable-text-p name resolved) (equal (len args) (len (cadr definition)))
                 (proof-heap-p before objects packages)
                 (generated-evaluation-tree-p :args (caddr argument-data) argument-records (cdr term) (cdr source)
                                               scope slots quoted constants env program (1- fuel)
                                               before objects ready argument-objects packages pc (cons pc cuts)
                                               (generated-argument-trace-budget argument-records))
                 (unsigned-byte-p 64 target) (equal continuation (+ 4 pc)) (< continuation (expt 2 64))
                 (generated-ordinary-machine-p ready) (not (proof-world-stop ready))
                 (not (equal pc target)) (not (member-equal pc cuts)) (member-equal continuation cuts)
                 (generated-linked-item-p item (list :branch (- target pc) t) pc base labels ready)
                 (proof-segment-p callee-steps cuts entered :cut after)
                 (proof-compiled-return-p (len args) body-result entered after argument-objects new-objects packages)
                 (equal steps (+ (generated-argument-trace-budget argument-records) 1 (nfix callee-steps))))))
         (:simple-routine
          (let* ((chain (cadr tree)) (routine-steps (caddr tree))
                 (args (boymoo-model::core-datum (boymoo-model::core-eval-step :terms (cdr source) env program (1- fuel))))
                 (result (proof-runtime-value (car (last chain)) args program))
                 (path (generated-simple-register-path (cdr term) 0 scope constants))
                 (ready (generated-path-after path before))
                 (ready-pc (+ (proof-world-pc before) (* 4 (len path)))))
            (and (consp term) (consp source) (equal (car source) (car chain))
                 (generated-variable-text-p (car term) (car source))
                 (generated-runtime-application-source-p chain (cdr source) env program fuel)
                 (generated-simple-operands-agree-p (cdr term) (cdr source) scope slots quoted) (<= (len (cdr term)) 17)
                 (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                 (proof-constant-map-p quoted constants (proof-heap-base before) objects packages (proof-world-machine before))
                 (proof-heap-p before objects packages) (< ready-pc (expt 2 64)) (not (proof-world-stop before))
                 (generated-path-p path (cons ready-pc cuts) before)
                 (proof-segment-p routine-steps cuts ready :cut after)
                 (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation ready after
                                                   objects new-objects packages)
                 (equal steps (+ (len path) (nfix routine-steps))))))
         (:computed-routine
          (let* ((route (cadr tree)) (argument-data (caddr tree)) (result-data (cadddr tree))
                 (chain (car route)) (depth (cadr route))
                 (ready (car argument-data)) (argument-objects (cadr argument-data)) (argument-records (cadddr argument-data))
                 (returned (car result-data)) (routine-steps (cadr result-data))
                 (args (boymoo-model::core-datum (boymoo-model::core-eval-step :terms (cdr source) env program (1- fuel))))
                 (result (proof-runtime-value (car (last chain)) args program))
                 (count (len args)) (prepare (generated-argument-register-path count depth 0))
                 (loaded (generated-path-after prepare ready)) (ready-pc (proof-world-pc ready))
                 (routine-pc (+ ready-pc (* 4 (len prepare))))
                 (drop-pc (proof-world-pc returned)) (drop-path (generated-address-path 25 25 (* 8 count) t)))
            (and (consp term) (consp source) (equal (car source) (car chain))
                 (generated-variable-text-p (car term) (car source))
                 (generated-runtime-application-source-p chain (cdr source) env program fuel)
                 (not (boymoo-compiler::gen-simple-args-p (cdr term)))
                 (proof-heap-p before objects packages) (proof-heap-p ready argument-objects packages)
                 (generated-evaluation-tree-p :args (caddr argument-data) argument-records (cdr term) (cdr source)
                                               scope slots quoted constants env program (1- fuel)
                                               before objects ready argument-objects packages ready-pc
                                               (list* ready-pc drop-pc cuts) (generated-argument-trace-budget argument-records))
                 (not (proof-world-stop ready)) (equal (proof-stack-top before) (+ (proof-world-reg 19 ready) (* 8 depth)))
                 (natp depth) (natp routine-steps) (<= count 17) (< (* 8 (+ depth count)) (expt 2 64))
                 (< routine-pc (expt 2 64)) (generated-path-p prepare (list* routine-pc drop-pc cuts) ready)
                 (proof-segment-p routine-steps (cons drop-pc cuts) loaded :cut returned)
                 (generated-nontail-value-result-p (boymoo-model::core-datum result) drop-pc loaded returned
                                                   argument-objects new-objects packages)
                 (unsigned-byte-p 64 (* 8 count)) (equal continuation (+ drop-pc (* 4 (len drop-path))))
                 (< continuation (expt 2 64)) (member-equal continuation cuts) (not (proof-world-stop returned))
                 (generated-path-p drop-path cuts returned) (equal after (generated-path-after drop-path returned))
                 (equal steps (+ (generated-argument-trace-budget argument-records) (len prepare) routine-steps (len drop-path))))))
         (otherwise nil))))
     ((:args :lambda-args)
      (cond
       ((atom term)
        (and (null term) (null source) (null operands) (null tree)
             (equal after before) (equal new-objects objects)
             (member-equal (proof-world-pc before) cuts) (not (proof-world-stop before))))
       ((atom source) nil)
       ((and (eq kind :lambda-args) (atom (car term)))
        (and (generated-variable-text-p (car term) (car source))
             (generated-evaluation-tree-p kind tree operands (cdr term) (cdr source)
                                           scope slots quoted constants env program (1- fuel)
                                           before objects after new-objects packages continuation cuts steps)))
       (t
        (let* ((record (car operands)) (operand-steps (car record))
               (evaluated (cadr record)) (operand-objects (caddr record))
               (operand-end (proof-world-pc evaluated)) (push-end (+ operand-end 8))
               (push-cuts (cons push-end cuts)) (pushed (generated-path-after *generated-push-path* evaluated)))
          (and (consp operands) (consp tree) (true-listp record) (equal (len record) 3) (natp operand-steps)
               (generated-evaluation-tree-p :term (car tree) nil (car term) (car source) scope slots quoted constants
                                             env program (1- fuel) before objects evaluated operand-objects packages
                                             operand-end (cons operand-end push-cuts) operand-steps)
               (<= (+ (proof-stack-top evaluated) 8) (proof-stack-limit evaluated))
               (< push-end (expt 2 64)) (generated-ordinary-machine-p evaluated)
               (generated-path-p *generated-push-path* push-cuts evaluated)
               (generated-evaluation-tree-p kind (cdr tree) (cdr operands) (cdr term) (cdr source)
                                             scope slots quoted constants env program (1- fuel)
                                             pushed operand-objects after new-objects packages continuation cuts steps))))))
     (otherwise nil))))

(local
 (defun generated-evaluation-tree-induction (kind tree operands term source scope slots env program fuel
                                                  before objects after new-objects continuation cuts steps)
   (declare (xargs :measure (nfix fuel) :ruler-extenders :all))
   (cond
    ((zp fuel) (list tree operands term source scope slots env program before objects after new-objects continuation cuts steps))
    ((eq kind :term)
     (case (car tree)
       (:mbe
        (generated-evaluation-tree-induction :term (cadr tree) nil (cadddr term) (cadddr source)
                                              scope slots env program (1- fuel) before objects after new-objects
                                              continuation cuts steps))
       (:lambda
        (let* ((depth (cadadr tree)) (argument-data (caddr tree)) (body-data (cadddr tree))
               (ready (car argument-data)) (argument-objects (cadr argument-data))
               (returned (car body-data)) (body-pc (proof-world-pc ready)) (drop-pc (proof-world-pc returned))
               (actuals (cdr term)) (sources (cdr source)) (formals (cadar source))
               (body-slots (generated-lambda-slots actuals scope depth))
               (body-scope (generated-bind-slots (boymoo-compiler::declaration-list (cadar term)) body-slots nil))
               (values (boymoo-model::core-datum (boymoo-model::core-eval-step :terms sources env program (1- fuel)))))
          (list (generated-evaluation-tree-induction
                 :lambda-args (caddr argument-data) (cadddr argument-data) actuals sources scope slots env program (1- fuel)
                 before objects ready argument-objects body-pc (list* body-pc drop-pc cuts)
                 (generated-argument-trace-budget (cadddr argument-data)))
                (generated-evaluation-tree-induction
                 :term (cadddr body-data) nil (caddar term) (caddar source) body-scope
                 (pairlis$ formals body-slots) (pairlis$ formals values) program (1- fuel)
                 ready argument-objects returned (cadr body-data) drop-pc (cons drop-pc cuts) (caddr body-data)))))
       (:if
        (let* ((addresses (cadr tree)) (test-data (caddr tree)) (arm-data (cadddr tree))
               (yes (car addresses)) (no (cadr addresses)) (jump (caddr addresses))
               (tested (car test-data)) (test-objects (cadr test-data)) (test-end (proof-world-pc tested))
               (returned (car arm-data))
               (truth (boymoo-model::core-datum (boymoo-model::core-eval-step :term (cadr source) env program (1- fuel))))
               (entered (generated-path-after (generated-if-path yes no tested) tested)))
          (list (generated-evaluation-tree-induction
                 :term (cadddr test-data) nil (cadr term) (cadr source) scope slots env program (1- fuel)
                 before objects tested test-objects test-end (list* test-end (if truth yes no) cuts) (caddr test-data))
                (generated-evaluation-tree-induction
                 :term (caddr arm-data) nil (if truth (caddr term) (cadddr term)) (if truth (caddr source) (cadddr source))
                 scope slots env program (1- fuel) entered test-objects returned new-objects
                 (if truth jump continuation) (if truth (cons jump cuts) cuts) (cadr arm-data)))))
       (:ordinary-call
        (let* ((argument-data (caddr tree)) (ready (car argument-data)) (pc (proof-world-pc ready))
               (argument-records (cadddr argument-data)))
          (generated-evaluation-tree-induction :args (caddr argument-data) argument-records (cdr term) (cdr source)
                                                scope slots env program (1- fuel)
                                                before objects ready (cadr argument-data) pc (cons pc cuts)
                                                (generated-argument-trace-budget argument-records))))
       (:computed-routine
        (let* ((argument-data (caddr tree)) (ready (car argument-data)) (pc (proof-world-pc ready))
               (argument-records (cadddr argument-data)) (returned (car (cadddr tree))))
          (generated-evaluation-tree-induction :args (caddr argument-data) argument-records (cdr term) (cdr source)
                                               scope slots env program (1- fuel) before objects ready (cadr argument-data)
                                               pc (list* pc (proof-world-pc returned) cuts)
                                               (generated-argument-trace-budget argument-records))))
       (otherwise (list tree term source before after continuation cuts steps))))
    ((not (member-eq kind '(:args :lambda-args))) (list kind term source))
    ((or (atom term) (atom source)) (list term source tree operands before after objects new-objects continuation cuts steps))
    ((and (eq kind :lambda-args) (atom (car term)))
     (generated-evaluation-tree-induction kind tree operands (cdr term) (cdr source)
                                           scope slots env program (1- fuel) before objects after new-objects
                                           continuation cuts steps))
    (t
     (let* ((record (car operands)) (evaluated (cadr record)) (operand-objects (caddr record))
            (operand-end (proof-world-pc evaluated)) (push-cuts (cons (+ operand-end 8) cuts))
            (pushed (generated-path-after *generated-push-path* evaluated)))
       (list (generated-evaluation-tree-induction
              :term (car tree) nil (car term) (car source) scope slots env program (1- fuel)
              before objects evaluated operand-objects operand-end (cons operand-end push-cuts) (car record))
             (generated-evaluation-tree-induction
              kind (cdr tree) (cdr operands) (cdr term) (cdr source) scope slots env program (1- fuel)
              pushed operand-objects after new-objects continuation cuts steps)))))))

(defthm generated-term-and-argument-evaluation-tree-sound
  (implies (generated-evaluation-tree-p kind tree operands term source scope slots quoted constants
                                          env program fuel before objects after new-objects packages continuation cuts steps)
           (if (eq kind :term)
               (and (proof-segment-p steps cuts before :cut after)
                    (generated-nontail-value-result-p
                     (boymoo-model::core-datum (boymoo-model::core-eval-step :term source env program fuel))
                     continuation before after objects new-objects packages))
             (generated-argument-trace-p term source (eq kind :lambda-args) env program fuel
                                          before objects after new-objects packages cuts operands)))
  :hints (("Goal"
           :induct (generated-evaluation-tree-induction kind tree operands term source scope slots env program fuel
                                                       before objects after new-objects continuation cuts steps)
           :in-theory (enable generated-evaluation-tree-p generated-argument-trace-p))
          ("Subgoal *1/7"
           :use ((:instance generated-noncall-trace-returns-source-value (trace (cadr tree)))
                 (:instance generated-simple-runtime-application-returns-source-result
                            (chain (cadr tree)) (terms (cdr term)) (sources (cdr source)) (routine-steps (caddr tree))))
           :in-theory (e/d (generated-evaluation-tree-p) (generated-argument-trace-p))
           :do-not-induct t)
          ("Subgoal *1/6"
           :expand (generated-evaluation-tree-p :term tree operands term source scope slots quoted constants
                                                env program fuel before objects after new-objects packages continuation cuts steps)
           :use (:instance generated-computed-runtime-application-returns-source-result
                           (chain (caadr tree)) (depth (cadadr tree)) (terms (cdr term)) (sources (cdr source))
                           (ready (car (caddr tree))) (old-objects objects) (objects (cadr (caddr tree)))
                           (trace (cadddr (caddr tree))) (returned (car (cadddr tree))) (routine-steps (cadr (cadddr tree))))
           :in-theory (e/d (generated-evaluation-tree-p) (generated-argument-trace-p))
           :do-not-induct t)
          ("Subgoal *1/5"
           :expand (generated-evaluation-tree-p :term tree operands term source scope slots quoted constants
                                                env program fuel before objects after new-objects packages continuation cuts steps)
           :use (:instance generated-resolved-ordinary-call-returns-source-value
                           (chain (caadr tree)) (name (cadadr tree)) (base (caddr (cadr tree))) (labels (cadddr (cadr tree)))
                           (actuals (cdr term)) (sources (cdr source)) (ready (car (caddr tree)))
                           (old-objects objects) (objects (cadr (caddr tree)))
                           (trace (cadddr (caddr tree))) (callee-steps (cadddr tree)))
           :in-theory (e/d (generated-evaluation-tree-p) (generated-argument-trace-p))
           :do-not-induct t)
          ("Subgoal *1/4"
           :expand (generated-evaluation-tree-p :term tree operands term source scope slots quoted constants
                                                env program fuel before objects after new-objects packages continuation cuts steps)
           :use (:instance generated-conditional-evaluation-selects-and-returns-source-value
                           (test (cadr source)) (yes-term (caddr source)) (no-term (cadddr source))
                           (yes (caadr tree)) (no (cadadr tree)) (jump (caddr (cadr tree)))
                           (old-objects objects) (objects (cadr (caddr tree)))
                           (tested (car (caddr tree))) (returned (car (cadddr tree)))
                           (test-steps (caddr (caddr tree))) (arm-steps (cadr (cadddr tree))))
           :in-theory (e/d (generated-evaluation-tree-p) (generated-argument-trace-p))
           :do-not-induct t)
          ("Subgoal *1/3"
           :use (:instance generated-lambda-argument-and-body-traces-return-source-value
                           (actuals (cdr term)) (sources (cdr source)) (formals (cadar source)) (body (caddar source))
                           (caller-bindings slots) (caller-env env) (offset (caadr tree)) (depth (cadadr tree))
                           (old-objects objects) (middle-objects (cadr (caddr tree))) (objects (cadr (cadddr tree)))
                           (ready (car (caddr tree))) (returned (car (cadddr tree)))
                           (body-steps (caddr (cadddr tree))) (trace (cadddr (caddr tree))))
           :in-theory (e/d (generated-evaluation-tree-p) (generated-argument-trace-p))
           :do-not-induct t)
          ("Subgoal *1/2" :in-theory (enable generated-evaluation-tree-p generated-source-mbe) :do-not-induct t)
          ("Subgoal *1/1" :do-not-induct t))
  :rule-classes nil)
