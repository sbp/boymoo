(in-package "BOYMOO-PROOFS")

(include-book "argument-flow")
(include-book "lambda-environment")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-model::core-eval-step proof-heap-p proof-segment-p proof-run
                    proof-world-pc proof-world-stop proof-stack-top proof-stack-limit
                    generated-path-after generated-path-p expt))

(defun generated-argument-values-to-push (alias-p actuals args)
  (if alias-p (generated-lambda-pushed-values actuals args) args))

; Each record gives the operand step bound, the state at its continuation,
; and the published objects at that state. The following push is fixed code.
(defun generated-argument-trace-budget (trace)
  (if (atom trace)
      0
    (+ (nfix (caar trace)) 2 (generated-argument-trace-budget (cdr trace)))))

(defund generated-argument-trace-p (actuals sources alias-p env program fuel before objects after new-objects
                                            packages cuts trace)
  (cond
   ((atom actuals)
    (and (null actuals) (null sources) (null trace) (equal after before) (equal new-objects objects)
         (member-equal (proof-world-pc before) cuts) (not (proof-world-stop before))))
   ((atom sources) nil)
   ((and alias-p (atom (car actuals)))
    (and (generated-variable-text-p (car actuals) (car sources))
         (generated-argument-trace-p (cdr actuals) (cdr sources) alias-p env program (1- fuel)
                                      before objects after new-objects packages cuts trace)))
   (t
    (let* ((record (car trace))
           (operand-steps (car record))
           (evaluated (cadr record))
           (operand-objects (caddr record))
           (operand-end (proof-world-pc evaluated))
           (push-end (+ operand-end 8))
           (push-cuts (cons push-end cuts))
           (pushed (generated-path-after *generated-push-path* evaluated))
           (source (boymoo-model::core-eval-step :term (car sources) env program (1- fuel))))
      (and (consp trace) (true-listp record) (equal (len record) 3) (natp operand-steps)
           (proof-segment-p operand-steps (cons operand-end push-cuts) before :cut evaluated)
           (generated-nontail-value-result-p (boymoo-model::core-datum source) operand-end
                                              before evaluated objects operand-objects packages)
           (<= (+ (proof-stack-top evaluated) 8) (proof-stack-limit evaluated))
           (< push-end (expt 2 64)) (generated-ordinary-machine-p evaluated)
           (generated-path-p *generated-push-path* push-cuts evaluated)
           (generated-argument-trace-p (cdr actuals) (cdr sources) alias-p env program (1- fuel)
                                        pushed operand-objects after new-objects packages cuts (cdr trace)))))))

(local
 (defun generated-argument-trace-induction (actuals sources alias-p fuel before objects trace)
   (cond
    ((atom actuals) (list sources fuel before objects trace))
    ((and alias-p (atom (car actuals)))
     (generated-argument-trace-induction (cdr actuals) (cdr sources) alias-p (1- fuel) before objects trace))
    (t
     (generated-argument-trace-induction
      (cdr actuals) (cdr sources) alias-p (1- fuel)
      (generated-path-after *generated-push-path* (cadar trace)) (caddar trace) (cdr trace))))))

(local
 (defthm generated-argument-stage-has-resulting-heap
   (implies (generated-arguments-result-p args before after old-objects new-objects packages)
            (proof-heap-p after new-objects packages))
   :hints (("Goal" :in-theory (enable generated-arguments-result-p)))
   :rule-classes :forward-chaining))

(local
 (defthm generated-argument-values-to-push-step
   (equal (generated-argument-values-to-push alias-p (cons actual actuals) (cons first rest))
          (if (and alias-p (atom actual))
              (generated-argument-values-to-push alias-p actuals rest)
            (cons first (generated-argument-values-to-push alias-p actuals rest))))))

(defthm generated-argument-trace-evaluates-in-source-order
  (let* ((result (boymoo-model::core-eval-step :terms sources env program fuel))
         (args (generated-argument-values-to-push alias-p actuals (boymoo-model::core-datum result))))
    (implies (and (boymoo-model::core-value-p result) (proof-heap-p before objects packages)
                  (generated-argument-trace-p actuals sources alias-p env program fuel before objects
                                               after new-objects packages cuts trace))
             (and (proof-segment-p (generated-argument-trace-budget trace) cuts before :cut after)
                  (generated-arguments-result-p args before after objects new-objects packages))))
  :hints (("Goal" :induct (generated-argument-trace-induction actuals sources alias-p fuel before objects trace)
                  :in-theory (e/d (generated-argument-trace-p)
                                  (generated-argument-values-to-push generated-lambda-pushed-values)))
          ("Subgoal *1/3"
           :use ((:instance generated-successful-argument-evaluation-splits (terms sources))
                 (:instance generated-evaluated-operand-and-push-compose
                            (evaluated (cadar trace)) (objects (caddar trace)) (old-objects objects)
                            (operand-end (proof-world-pc (cadar trace))) (operand-steps (caar trace))
                            (cuts (cons (+ 8 (proof-world-pc (cadar trace))) cuts))
                            (datum (boymoo-model::core-datum
                                    (boymoo-model::core-eval-step :term (car sources) env program (1- fuel)))))
                 (:instance generated-argument-stages-compose
                            (first-args (list (boymoo-model::core-datum
                                               (boymoo-model::core-eval-step :term (car sources) env program (1- fuel)))))
                            (rest-args (generated-argument-values-to-push
                                        alias-p (cdr actuals)
                                        (boymoo-model::core-datum
                                         (boymoo-model::core-eval-step :terms (cdr sources) env program (1- fuel)))))
                            (middle (generated-path-after *generated-push-path* (cadar trace)))
                            (old-objects objects) (middle-objects (caddar trace)))
                 (:instance generated-segment-composes-with-final-segment
                            (prefix-cuts (cons (+ 8 (proof-world-pc (cadar trace))) cuts))
                            (prefix-steps (+ (nfix (caar trace)) 2))
                            (suffix-steps (generated-argument-trace-budget (cdr trace)))
                            (middle (generated-path-after *generated-push-path* (cadar trace))) (reason :cut)))
           :in-theory (e/d (generated-argument-trace-p)
                           (generated-argument-values-to-push generated-lambda-pushed-values)))
          ("Subgoal *1/2"
           :use (:instance generated-successful-argument-evaluation-splits (terms sources))
           :in-theory (e/d (generated-argument-trace-p)
                           (generated-argument-values-to-push generated-lambda-pushed-values)))
          ("Subgoal *1/1"
           :use ((:instance generated-no-arguments-preserve-the-frame (world before)))
           :expand (boymoo-model::core-eval-step :terms nil env program fuel)
           :in-theory (enable generated-argument-trace-p proof-run proof-segment-p)))
  :rule-classes nil)
