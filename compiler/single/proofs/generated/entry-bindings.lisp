(in-package "BOYMOO-PROOFS")

(include-book "lambda-environment")
(include-book "prologue-state")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable proof-heap-p proof-world-pc proof-world-reg proof-world-machine proof-compiled-entry-p
                    proof-environment-p proof-stack-views proof-stack-base proof-stack-top proof-heap-base
                    proof-load-word proof-machine-value-p proof-subspan-p proof-span-p
                    generated-stack-views-are-word-views expt))

(local
 (defun generated-consecutive-binding-induction (formals args slot)
   (if (atom formals)
       (list args slot)
     (generated-consecutive-binding-induction (cdr formals) (cdr args) (1+ slot)))))

(local
 (defthm generated-absent-formal-has-no-slot-binding
   (implies (not (member-equal name formals))
            (not (assoc-equal name (pairlis$ formals slots))))
   :hints (("Goal" :induct (pairlis$ formals slots)))))

(defthm generated-consecutive-argument-views-establish-environment
  (let* ((count (len args)) (address (+ frame (* 8 slot)))
         (slots (generated-consecutive-slots count slot)))
    (implies (and (symbol-listp formals) (no-duplicatesp-equal formals) (true-listp args)
                  (equal (len formals) count) (natp slot) (integerp frame)
                  (proof-subspan-p address (* 8 count) (proof-stack-base world) (proof-stack-top world))
                  (equal (proof-stack-views count address (proof-heap-base world) objects packages
                                           (proof-world-machine world))
                         (cons :slots (proof-argument-views args))))
             (proof-environment-p (pairlis$ formals slots) (pairlis$ formals args) frame world objects packages)))
  :hints (("Goal" :induct (generated-consecutive-binding-induction formals args slot))
          ("Subgoal *1/2"
           :use ((:instance generated-stack-slot-and-suffix-are-within-span
                            (count (len (cdr args))) (address (+ frame (* 8 slot))))
                 (:instance generated-stack-views-separate-first-argument
                            (count (len (cdr args))) (address (+ frame (* 8 slot))) (first (car args)) (rest (cdr args)))
                 (:instance generated-environment-extends-by-fresh-slot
                            (name (car formals)) (datum (car args))
                            (bindings (pairlis$ (cdr formals) (generated-consecutive-slots (len (cdr args)) (1+ slot))))
                            (env (pairlis$ (cdr formals) (cdr args))))))
          ("Subgoal *1/1" :in-theory (enable proof-environment-p)))
  :rule-classes nil)

(defthm generated-function-entry-provides-body-environment
  (let* ((frame (proof-world-reg 19 world)) (count (len args))
         (slots (generated-consecutive-slots count 0)))
    (implies (and (proof-compiled-entry-p (proof-world-pc world) args world objects packages)
                  (equal frame (- (proof-stack-top world) (* 8 count)))
                  (symbol-listp formals) (no-duplicatesp-equal formals) (equal (len formals) count))
             (proof-environment-p (pairlis$ formals slots) (pairlis$ formals args) frame world objects packages)))
  :hints (("Goal"
           :use ((:instance generated-consecutive-argument-views-establish-environment (slot 0)
                            (frame (proof-world-reg 19 world)))
                 (:instance generated-heap-has-layout-and-roots (world world))
                 (:instance generated-heap-layout-value-stack-bounds (world world)))
           :in-theory (enable proof-compiled-entry-p proof-subspan-p proof-span-p proof-stack-top)))
  :rule-classes nil)
