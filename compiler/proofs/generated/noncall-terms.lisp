(in-package "BOYMOO-PROOFS")

(include-book "conditional-flow")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-world-pc proof-world-reg proof-world-stop proof-world-machine
                    proof-heap-p proof-environment-p proof-constant-map-p proof-heap-base proof-segment-p
                    proof-instruction-effect generated-path-p generated-path-after generated-if-path
                    generated-simple-operand-path generated-heap-world-equiv generated-nontail-value-result-p
                    boymoo-compiler::gen-simple-p boymoo-compiler::gen-mbe-p boymoo-model::core-mbe-call-p
                    boymoo-model::core-eval-step unsigned-byte-p expt))

; The conditional supplies three addresses and two subsidiary traces. Each
; subsidiary record contains its trace, output world, and instruction budget.
; The addresses give the true arm, false arm, and jump after the true arm.
(defund generated-noncall-trace-p (trace term source scope constants env program fuel
                                        before after continuation cuts steps)
  (declare (xargs :measure (acl2-count trace) :ruler-extenders :all))
  (case (car trace)
    (:simple
     (let* ((path (generated-simple-operand-path term 0 scope constants))
            (end (+ (proof-world-pc before) (* 4 (len path)))))
       (and (equal continuation end) (< end (expt 2 64)) (member-equal end cuts)
            (not (proof-world-stop before)) (generated-path-p path cuts before)
            (equal after (generated-path-after path before)) (equal steps (len path)))))
    (:mbe
     (and (posp fuel)
          (not (boymoo-compiler::gen-simple-p term))
          (boymoo-compiler::gen-mbe-p (car term) (cdr term)) (equal (length (cdr term)) 3)
          (boymoo-model::core-mbe-call-p source)
          (generated-noncall-trace-p (cadr trace) (cadddr term) (cadddr source)
                                     scope constants env program (1- fuel) before after continuation cuts steps)))
    (:if
     (let* ((addresses (cadr trace)) (test-record (caddr trace)) (arm-record (cadddr trace))
            (yes (car addresses)) (no (cadr addresses)) (jump (caddr addresses))
            (tested (cadr test-record)) (returned (cadr arm-record))
            (test-steps (caddr test-record)) (arm-steps (caddr arm-record))
            (test-end (proof-world-pc tested))
            (test-result (boymoo-model::core-eval-step :term (cadr source) env program (1- fuel)))
            (truth (boymoo-model::core-datum test-result))
            (selected (if truth yes no)) (dispatch (generated-if-path yes no tested))
            (entered (generated-path-after dispatch tested))
            (arm-end (if truth jump continuation))
            (arm-cuts (if truth (cons jump cuts) cuts))
            (branch (list :branch (- continuation jump) nil)))
       (and (posp fuel)
            (equal term (list boymoo-compiler::*if-name* (cadr term) (caddr term) (cadddr term)))
            (equal source (list 'if (cadr source) (caddr source) (cadddr source)))
            (boymoo-model::core-value-p test-result)
            (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no) (unsigned-byte-p 64 continuation)
            (< (+ test-end 8) (expt 2 64)) (member-equal continuation cuts)
            (natp test-steps) (natp arm-steps)
            (generated-ordinary-machine-p tested) (not (proof-world-stop tested))
            (generated-noncall-trace-p (car test-record) (cadr term) (cadr source) scope constants env program
                                       (1- fuel) before tested test-end (list* test-end selected cuts) test-steps)
            (generated-path-p dispatch (list* yes no selected cuts) tested)
            (generated-noncall-trace-p (car arm-record) (if truth (caddr term) (cadddr term))
                                       (if truth (caddr source) (cadddr source))
                                       scope constants env program (1- fuel) entered returned arm-end arm-cuts arm-steps)
            (if truth
                (and (generated-ordinary-machine-p returned)
                     (generated-path-p (list branch) cuts returned)
                     (equal after (proof-instruction-effect branch returned)))
              (equal after returned))
            (equal steps (+ (nfix test-steps) (len dispatch) (nfix arm-steps) (if truth 1 0))))))
    (otherwise nil)))

(local
 (defthm generated-heap-equivalence-and-frame-register-compose
   (implies (and (generated-heap-world-equiv middle before)
                 (equal (proof-world-reg 19 middle) (proof-world-reg 19 before))
                 (generated-heap-world-equiv after middle)
                 (equal (proof-world-reg 19 after) (proof-world-reg 19 middle)))
            (and (generated-heap-world-equiv after before)
                 (equal (proof-world-reg 19 after) (proof-world-reg 19 before))))
   :hints (("Goal" :in-theory (enable generated-heap-world-equiv)))
   :rule-classes nil))

(local
 (defthm generated-conditional-arm-finishes-at-continuation
   (let* ((arm-end (if truth jump continuation))
          (arm-cuts (if truth (cons jump cuts) cuts))
          (branch (list :branch (- continuation jump) nil)))
     (implies (and (natp arm-steps) (unsigned-byte-p 64 continuation) (member-equal continuation cuts)
                   (proof-segment-p arm-steps arm-cuts entered :cut returned)
                   (generated-nontail-value-result-p datum arm-end entered returned objects objects packages)
                   (if truth
                       (and (generated-ordinary-machine-p returned)
                            (generated-path-p (list branch) cuts returned)
                            (equal after (proof-instruction-effect branch returned)))
                     (equal after returned)))
              (and (proof-segment-p (+ arm-steps (if truth 1 0)) cuts entered :cut after)
                   (generated-nontail-value-result-p datum continuation entered after objects objects packages)
                   (generated-heap-world-equiv after returned)
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 returned)))))
   :hints (("Goal" :use (:instance generated-if-true-arm-jump-composes (arm-start entered)
                                    (arm-end jump) (arm-exit returned) (old-objects objects))))
   :rule-classes nil))

(local
 (defthm generated-checked-conditional-segments-compose
   (let* ((truth (boymoo-model::core-datum test-result))
          (selected (if truth yes no)) (test-end (proof-world-pc tested))
          (dispatch (generated-if-path yes no tested)) (entered (generated-path-after dispatch tested))
          (arm-end (if truth jump continuation)) (arm-cuts (if truth (cons jump cuts) cuts))
          (branch (list :branch (- continuation jump) nil)))
     (implies (and (boymoo-model::core-value-p test-result) (unsigned-byte-p 64 yes) (unsigned-byte-p 64 no)
                   (< (+ test-end 8) (expt 2 64)) (generated-ordinary-machine-p tested) (not (proof-world-stop tested))
                   (unsigned-byte-p 64 continuation) (member-equal continuation cuts)
                   (natp test-steps) (natp arm-steps)
                   (proof-segment-p test-steps (list* test-end selected cuts) before :cut tested)
                   (generated-nontail-value-result-p truth test-end before tested objects objects packages)
                   (generated-heap-world-equiv tested before)
                   (equal (proof-world-reg 19 tested) (proof-world-reg 19 before))
                   (generated-path-p dispatch (list* yes no selected cuts) tested)
                   (proof-segment-p arm-steps arm-cuts entered :cut returned)
                   (generated-nontail-value-result-p datum arm-end entered returned objects objects packages)
                   (generated-heap-world-equiv returned entered)
                   (equal (proof-world-reg 19 returned) (proof-world-reg 19 entered))
                   (if truth
                       (and (generated-ordinary-machine-p returned)
                            (generated-path-p (list branch) cuts returned)
                            (equal after (proof-instruction-effect branch returned)))
                     (equal after returned)))
              (and (proof-segment-p (+ (nfix test-steps) (len dispatch) (nfix arm-steps) (if truth 1 0))
                                    cuts before :cut after)
                   (generated-nontail-value-result-p datum continuation before after objects objects packages)
                   (generated-heap-world-equiv after before)
                   (equal (proof-world-reg 19 after) (proof-world-reg 19 before)))))
   :hints (("Goal"
            :use ((:instance generated-if-test-and-dispatch-compose
                             (test-end (proof-world-pc tested)) (old-objects objects)
                             (cuts (cons (if (boymoo-model::core-datum test-result) yes no) cuts)))
                  (:instance generated-conditional-arm-finishes-at-continuation
                             (truth (boymoo-model::core-datum test-result))
                             (entered (generated-path-after (generated-if-path yes no tested) tested)))
                  (:instance generated-nontail-segments-compose
                             (prefix-steps (+ (nfix test-steps) (len (generated-if-path yes no tested))))
                             (suffix-steps (+ (nfix arm-steps) (if (boymoo-model::core-datum test-result) 1 0)))
                             (middle-pc (if (boymoo-model::core-datum test-result) yes no))
                             (middle (generated-path-after (generated-if-path yes no tested) tested))
                             (prefix-datum (boymoo-model::core-datum test-result))
                             (old-objects objects) (middle-objects objects) (new-objects objects))
                  (:instance generated-heap-equivalence-and-frame-register-compose (middle tested)
                             (after (generated-path-after (generated-if-path yes no tested) tested)))
                  (:instance generated-heap-equivalence-and-frame-register-compose (middle returned)
                             (before (generated-path-after (generated-if-path yes no tested) tested)))
                  (:instance generated-heap-equivalence-and-frame-register-compose
                             (middle (generated-path-after (generated-if-path yes no tested) tested))))))
   :rule-classes nil))

(defund generated-noncall-context-agrees-p (trace term source scope slots quoted env program fuel)
  (declare (xargs :measure (acl2-count trace) :ruler-extenders :all))
  (case (car trace)
    (:simple (generated-simple-operand-agrees-p term source scope slots quoted))
    (:mbe (generated-noncall-context-agrees-p (cadr trace) (cadddr term) (cadddr source)
                                             scope slots quoted env program (1- fuel)))
    (:if
     (let* ((truth (boymoo-model::core-datum
                   (boymoo-model::core-eval-step :term (cadr source) env program (1- fuel)))))
       (and (generated-noncall-context-agrees-p (car (caddr trace)) (cadr term) (cadr source)
                                                scope slots quoted env program (1- fuel))
            (generated-noncall-context-agrees-p (car (cadddr trace)) (if truth (caddr term) (cadddr term))
                                                (if truth (caddr source) (cadddr source))
                                                scope slots quoted env program (1- fuel)))))
    (otherwise nil)))

(local
 (defun generated-noncall-trace-induction (trace term source env program fuel before after continuation cuts steps)
   (declare (xargs :measure (acl2-count trace) :ruler-extenders :all))
   (cond
    ((not (member-eq (car trace) '(:mbe :if))) (list term source before after continuation cuts steps))
    ((eq (car trace) :mbe)
     (generated-noncall-trace-induction (cadr trace) (cadddr term) (cadddr source) env program
                                        (1- fuel) before after continuation cuts steps))
    (t
     (let* ((addresses (cadr trace)) (test-record (caddr trace)) (arm-record (cadddr trace))
            (yes (car addresses)) (no (cadr addresses)) (jump (caddr addresses))
            (tested (cadr test-record)) (test-end (proof-world-pc tested))
            (truth (boymoo-model::core-datum (boymoo-model::core-eval-step :term (cadr source) env program (1- fuel))))
            (entered (generated-path-after (generated-if-path yes no tested) tested)))
       (list (generated-noncall-trace-induction
              (car test-record) (cadr term) (cadr source) env program
              (1- fuel) before tested test-end (list* test-end (if truth yes no) cuts) (caddr test-record))
             (generated-noncall-trace-induction
              (car arm-record) (if truth (caddr term) (cadddr term)) (if truth (caddr source) (cadddr source))
              env program (1- fuel) entered (cadr arm-record) (if truth jump continuation)
              (if truth (cons jump cuts) cuts) (caddr arm-record))))))))

(defthm generated-noncall-trace-returns-source-value
  (let ((result (boymoo-model::core-eval-step :term source env program fuel)))
    (implies (and (boymoo-model::core-value-p result)
                  (proof-heap-p before objects packages)
                  (proof-environment-p slots env (proof-world-reg 19 before) before objects packages)
                  (proof-constant-map-p quoted constants (proof-heap-base before) objects packages
                                        (proof-world-machine before))
                  (generated-noncall-context-agrees-p trace term source scope slots quoted env program fuel)
                  (generated-noncall-trace-p trace term source scope constants env program fuel
                                             before after continuation cuts steps))
             (and (proof-segment-p steps cuts before :cut after)
                  (generated-nontail-value-result-p (boymoo-model::core-datum result) continuation
                                                    before after objects objects packages)
                  (generated-heap-world-equiv after before)
                  (equal (proof-world-reg 19 after) (proof-world-reg 19 before)))))
  :hints (("Goal" :induct (generated-noncall-trace-induction trace term source env program fuel
                                                           before after continuation cuts steps)
                  :in-theory (enable generated-noncall-trace-p generated-noncall-context-agrees-p))
          ("Subgoal *1/3"
           :use ((:instance generated-if-dispatch-preserves-heap-and-frame-observations
                            (before (cadr (caddr trace))) (yes (caadr trace)) (no (cadadr trace)))
                 (:instance generated-heap-equivalent-state-keeps-nontail-context (after (cadr (caddr trace))))
                 (:instance generated-heap-equivalent-state-keeps-nontail-context (before (cadr (caddr trace)))
                            (after (generated-path-after (generated-if-path (caadr trace) (cadadr trace) (cadr (caddr trace)))
                                                         (cadr (caddr trace)))))
                 (:instance generated-checked-conditional-segments-compose
                            (test-result (boymoo-model::core-eval-step :term (cadr source) env program (1- fuel)))
                            (datum (boymoo-model::core-datum (boymoo-model::core-eval-step :term source env program fuel)))
                            (yes (caadr trace)) (no (cadadr trace)) (jump (caddr (cadr trace)))
                            (tested (cadr (caddr trace))) (returned (cadr (cadddr trace)))
                            (test-steps (caddr (caddr trace))) (arm-steps (caddr (cadddr trace)))))
           :do-not-induct t)
          ("Subgoal *1/2" :in-theory (enable generated-noncall-trace-p generated-noncall-context-agrees-p generated-source-mbe)
                           :do-not-induct t)
          ("Subgoal *1/1" :use generated-simple-term-provides-nontail-result :do-not-induct t))
  :rule-classes nil)
