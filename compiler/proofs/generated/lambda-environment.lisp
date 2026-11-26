(in-package "BOYMOO-PROOFS")

(include-book "lambda-slots")
(include-book "simple-registers")
(include-book "stack-write")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-model::core-eval-step boymoo-compiler::gen-slot
                    proof-environment-p proof-subspan-p proof-span-p proof-stack-views
                    proof-stack-top proof-stack-base proof-heap-base proof-world-machine
                    proof-machine-value-p proof-value-p proof-load-word generated-load-word
                    generated-stack-views-are-word-views generated-stack-views-of-one-slot expt))

(defthm generated-successful-argument-evaluation-splits
  (let* ((first (boymoo-model::core-eval-step :term (car terms) env program (1- fuel)))
         (rest (boymoo-model::core-eval-step :terms (cdr terms) env program (1- fuel)))
         (result (boymoo-model::core-eval-step :terms terms env program fuel)))
    (implies (and (consp terms) (boymoo-model::core-value-p result))
             (and (posp fuel) (boymoo-model::core-value-p first) (boymoo-model::core-value-p rest)
                  (equal result (boymoo-model::core-value
                                 (cons (boymoo-model::core-datum first) (boymoo-model::core-datum rest)))))))
  :hints (("Goal" :expand (boymoo-model::core-eval-step :terms terms env program fuel)))
  :rule-classes nil)

(defun generated-lambda-actuals-agree-p (actuals sources scope bindings)
  (if (atom actuals)
      (and (null actuals) (null sources))
    (and (consp sources)
         (or (consp (car actuals))
             (and (generated-variable-text-p (car actuals) (car sources))
                  (member-equal (cons (car sources) (boymoo-compiler::gen-slot (car actuals) scope)) bindings)))
         (generated-lambda-actuals-agree-p (cdr actuals) (cdr sources) scope bindings))))

(defun generated-lambda-pushed-values (actuals values)
  (if (atom actuals)
      nil
    (let ((rest (generated-lambda-pushed-values (cdr actuals) (cdr values))))
      (if (atom (car actuals)) rest (cons (car values) rest)))))

(local
 (defthm generated-unreferenced-binding-can-be-added
   (implies (not (assoc-equal name bindings))
            (equal (proof-environment-p bindings (cons (cons name datum) env) frame world objects packages)
                   (proof-environment-p bindings env frame world objects packages)))
   :hints (("Goal" :induct (len bindings) :in-theory (enable proof-environment-p)))))

(defthm generated-environment-extends-by-fresh-slot
  (let ((address (+ frame (* 8 slot))))
    (implies (and (not (assoc-equal name bindings)) (natp slot)
                  (proof-environment-p bindings env frame world objects packages)
                  (proof-subspan-p address 8 (proof-stack-base world) (proof-stack-top world))
                  (proof-machine-value-p (proof-load-word address (proof-world-machine world))
                                         datum world objects packages))
             (proof-environment-p (cons (cons name slot) bindings) (cons (cons name datum) env) frame world objects packages)))
  :hints (("Goal" :expand (proof-environment-p (cons (cons name slot) bindings) (cons (cons name datum) env)
                                              frame world objects packages)))
  :rule-classes nil)

(local
 (defthm generated-successful-variable-argument-uses-binding
   (let ((result (boymoo-model::core-eval-step :term name env program fuel)))
     (implies (and (symbolp name) (boymoo-model::core-value-p result))
              (and (assoc-eq name env) (equal (boymoo-model::core-datum result) (cdr (assoc-eq name env))))))
   :hints (("Goal" :expand (boymoo-model::core-eval-step :term name env program fuel)))
   :rule-classes nil))

(defthm generated-stack-views-separate-first-argument
   (let ((machine (proof-world-machine world)) (base (proof-heap-base world)))
     (implies (and (natp count)
                   (equal (proof-stack-views (1+ count) address base objects packages machine)
                          (cons :slots (proof-argument-views (cons first rest)))))
              (and (proof-machine-value-p (proof-load-word address machine) first world objects packages)
                   (equal (proof-stack-views count (+ address 8) base objects packages machine)
                          (cons :slots (proof-argument-views rest))))))
   :hints (("Goal"
            :expand ((proof-stack-views (1+ count) address (proof-heap-base world) objects packages
                                        (proof-world-machine world))
                     (proof-argument-views (cons first rest)))
            :in-theory (enable proof-machine-value-p proof-value-p)))
   :rule-classes nil)

(defthm generated-stack-slot-and-suffix-are-within-span
   (let ((base (proof-stack-base world)) (top (proof-stack-top world)))
     (implies (and (natp count) (proof-subspan-p address (* 8 (1+ count)) base top))
              (and (proof-subspan-p address 8 base top)
                   (proof-subspan-p (+ address 8) (* 8 count) base top))))
   :hints (("Goal" :in-theory (enable proof-subspan-p proof-span-p proof-stack-top)))
   :rule-classes nil)

(local
 (defun generated-lambda-environment-induction (actuals sources formals depth fuel)
   (cond ((atom actuals) (list sources formals depth fuel))
         ((atom (car actuals))
          (generated-lambda-environment-induction (cdr actuals) (cdr sources) (cdr formals) depth (1- fuel)))
         (t
          (generated-lambda-environment-induction (cdr actuals) (cdr sources) (cdr formals) (1+ depth) (1- fuel))))))

(defthm generated-lambda-body-environment-from-evaluated-actuals
  (let* ((result (boymoo-model::core-eval-step :terms sources caller-env program fuel))
         (values (boymoo-model::core-datum result))
         (pushed (generated-lambda-pushed-values actuals values))
         (address (+ frame (* 8 depth)))
         (slots (generated-lambda-slots actuals scope depth)))
    (implies (and (generated-lambda-actuals-agree-p actuals sources scope caller-bindings)
                  (symbol-listp formals) (no-duplicatesp-equal formals) (equal (len formals) (len actuals))
                  (natp depth) (integerp frame) (boymoo-model::core-value-p result)
                  (proof-environment-p caller-bindings caller-env frame world objects packages)
                  (proof-subspan-p address (* 8 (len pushed)) (proof-stack-base world) (proof-stack-top world))
                  (equal (proof-stack-views (len pushed) address (proof-heap-base world) objects packages
                                           (proof-world-machine world))
                         (cons :slots (proof-argument-views pushed))))
             (proof-environment-p (pairlis$ formals slots) (pairlis$ formals values) frame world objects packages)))
  :hints (("Goal" :induct (generated-lambda-environment-induction actuals sources formals depth fuel))
          ("Subgoal *1/3"
           :use ((:instance generated-successful-argument-evaluation-splits (terms sources) (env caller-env))
                 (:instance generated-stack-views-separate-first-argument (address (+ frame (* 8 depth)))
                            (count (len (generated-lambda-pushed-values
                                         (cdr actuals) (boymoo-model::core-datum
                                                        (boymoo-model::core-eval-step :terms (cdr sources) caller-env program (1- fuel))))))
                            (first (boymoo-model::core-datum
                                    (boymoo-model::core-eval-step :term (car sources) caller-env program (1- fuel))))
                            (rest (generated-lambda-pushed-values
                                   (cdr actuals) (boymoo-model::core-datum
                                                  (boymoo-model::core-eval-step :terms (cdr sources) caller-env program (1- fuel))))))
                 (:instance generated-stack-slot-and-suffix-are-within-span (address (+ frame (* 8 depth)))
                            (count (len (generated-lambda-pushed-values
                                         (cdr actuals) (boymoo-model::core-datum
                                                        (boymoo-model::core-eval-step :terms (cdr sources) caller-env program (1- fuel))))))))
           :in-theory (enable proof-environment-p))
          ("Subgoal *1/2"
           :use ((:instance generated-successful-argument-evaluation-splits (terms sources) (env caller-env))
                 (:instance generated-successful-variable-argument-uses-binding
                            (name (car sources)) (env caller-env) (fuel (1- fuel)))
                 (:instance generated-environment-binding (variable (car sources)) (env caller-env)
                            (slot (boymoo-compiler::gen-slot (car actuals) scope)) (bindings caller-bindings)))
           :in-theory (enable proof-environment-p generated-variable-text-p generated-load-word))
          ("Subgoal *1/1" :in-theory (enable proof-environment-p)))
  :rule-classes nil)
