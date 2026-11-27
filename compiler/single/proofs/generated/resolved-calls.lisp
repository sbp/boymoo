(in-package "BOYMOO-PROOFS")

(include-book "defined-flow")
(include-book "source")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-model::core-eval-step boymoo-model::core-call boymoo-model::core-definition
                    boymoo-model::core-attachment boymoo-model::core-primitive boymoo-model::core-prelude
                    boymoo-model::core-mbe-call-p boymoo-compiler::gen-mbe-p boymoo-compiler::gen-call-info
                    boymoo-compiler::gen-term boymoo-compiler::gen-args boymoo-compiler::gen-defined-call
                    proof-runtime-value proof-index-agrees-p generated-attachment-chain-p))

(defthm generated-source-named-term-evaluates-arguments-before-call
  (let* ((term (cons name terms))
         (args (boymoo-model::core-eval-step :terms terms env program (1- fuel))))
    (implies (and (posp fuel) (symbolp name) (not (member-eq name '(quote if)))
                  (not (boymoo-model::core-mbe-call-p term)) (boymoo-model::core-value-p args))
             (equal (boymoo-model::core-eval-step :term term env program fuel)
                    (boymoo-model::core-eval-step :call name (boymoo-model::core-datum args) program (1- fuel)))))
  :hints (("Goal" :expand (boymoo-model::core-eval-step :term (cons name terms) env program fuel)))
  :rule-classes nil)

(defthm generated-resolved-source-call-evaluates-defined-body-at-smaller-fuel
  (let* ((target (car (last chain)))
         (definition (boymoo-model::core-definition target program))
         (body-fuel (- fuel (len chain)))
         (body (boymoo-model::core-eval-step :term (caddr definition) (pairlis$ (cadr definition) args)
                                             program body-fuel)))
    (implies (and (generated-attachment-chain-p chain args program) (natp fuel) (<= (len chain) fuel)
                  (not (boymoo-model::core-attachment target program))
                  (not (boymoo-model::core-primitive target args program))
                  (not (boymoo-model::core-prelude target args)) definition)
             (and (natp body-fuel) (< body-fuel fuel)
                  (equal (boymoo-model::core-eval-step :call (car chain) args program fuel) body))))
  :hints (("Goal"
           :use (generated-source-call-follows-chain
                 (:instance generated-source-defined-call (name (car (last chain)))
                            (fuel (- (1+ fuel) (len chain)))))
           :in-theory (enable generated-attachment-chain-p)))
  :rule-classes nil)

(local
 (defthm generated-source-runtime-terminal
   (implies (and (posp fuel) (not (boymoo-model::core-attachment name program))
                 (proof-runtime-value name args program))
            (equal (boymoo-model::core-eval-step :call name args program fuel)
                   (proof-runtime-value name args program)))
   :hints (("Goal" :expand (boymoo-model::core-eval-step :call name args program fuel)
                   :in-theory (enable proof-runtime-value)))
   :rule-classes nil))

(defthm generated-resolved-source-call-evaluates-runtime-value
  (let* ((target (car (last chain)))
         (result (proof-runtime-value target args program)))
    (implies (and (generated-attachment-chain-p chain args program) (natp fuel) (<= (len chain) fuel)
                  (not (boymoo-model::core-attachment target program)) result)
             (equal (boymoo-model::core-eval-step :call (car chain) args program fuel) result)))
  :hints (("Goal"
           :use (generated-source-call-follows-chain
                 (:instance generated-source-runtime-terminal (name (car (last chain))) (fuel (- (1+ fuel) (len chain)))))))
  :rule-classes nil)

(defthm generated-resolved-defined-term-emits-arguments-and-call
  (let ((arity (length terms)))
    (implies (and (stringp head) (not (equal head boymoo-compiler::*quote-name*))
                  (not (equal head boymoo-compiler::*if-name*)) (not (boymoo-compiler::gen-mbe-p head terms))
                  (stringp target)
                  (proof-index-agrees-p (list (cons head target)) (cadr context))
                  (proof-index-agrees-p (list (cons target arity)) (car context))
                  (not (assoc-equal target boymoo-compiler::*jets*))
                  (not (assoc-equal target boymoo-compiler::*primitives*)))
             (equal (boymoo-compiler::gen-term (cons head terms) scope depth tail context code high serial)
                    (mv-let (arguments next-high next-serial)
                      (boymoo-compiler::gen-args terms scope depth context code high serial)
                      (mv (boymoo-compiler::gen-defined-call target arity tail arguments) next-high next-serial)))))
  :hints (("Goal"
           :use (:instance generated-defined-call-info-from-agreeing-indexes (resolved target) (arity (length terms)))
           :expand (boymoo-compiler::gen-term (cons head terms) scope depth tail context code high serial)
           :in-theory (enable boymoo-compiler::gen-simple-p length)))
  :rule-classes nil)

(defthm generated-ordinary-defined-term-emits-arguments-and-call
  (let ((arity (length terms)))
    (implies (and (stringp head) (not (equal head boymoo-compiler::*quote-name*))
                  (not (equal head boymoo-compiler::*if-name*)) (not (boymoo-compiler::gen-mbe-p head terms))
                  (proof-index-agrees-p (list (cons head nil)) (cadr context))
                  (proof-index-agrees-p (list (cons head arity)) (car context))
                  (not (assoc-equal head boymoo-compiler::*jets*))
                  (not (assoc-equal head boymoo-compiler::*primitives*)))
             (equal (boymoo-compiler::gen-term (cons head terms) scope depth tail context code high serial)
                    (mv-let (arguments next-high next-serial)
                      (boymoo-compiler::gen-args terms scope depth context code high serial)
                      (mv (boymoo-compiler::gen-defined-call head arity tail arguments) next-high next-serial)))))
  :hints (("Goal"
           :expand (boymoo-compiler::gen-term (cons head terms) scope depth tail context code high serial)
           :in-theory (e/d (boymoo-compiler::gen-simple-p boymoo-compiler::gen-call-info proof-index-agrees-p length)
                           (assoc-equal))))
  :rule-classes nil)

(defthm generated-resolved-named-term-evaluates-defined-body-at-smaller-fuel
  (let* ((head (car chain)) (target (car (last chain)))
         (args-result (boymoo-model::core-eval-step :terms terms env program (1- fuel)))
         (args (boymoo-model::core-datum args-result))
         (definition (boymoo-model::core-definition target program))
         (body-fuel (- (1- fuel) (len chain)))
         (result (boymoo-model::core-eval-step :term (caddr definition)
                                               (pairlis$ (cadr definition) args) program body-fuel)))
    (implies (and (posp fuel) (<= (len chain) (1- fuel)) (symbolp head) (not (member-eq head '(quote if)))
                  (not (boymoo-model::core-mbe-call-p (cons head terms))) (boymoo-model::core-value-p args-result)
                  (generated-attachment-chain-p chain args program)
                  (not (boymoo-model::core-attachment target program)) definition
                  (not (boymoo-model::core-primitive target args program)) (not (boymoo-model::core-prelude target args)))
             (and (natp body-fuel) (< body-fuel fuel)
                  (equal (boymoo-model::core-eval-step :term (cons head terms) env program fuel) result))))
  :hints (("Goal"
           :use ((:instance generated-source-named-term-evaluates-arguments-before-call (name (car chain)))
                 (:instance generated-resolved-source-call-evaluates-defined-body-at-smaller-fuel (fuel (1- fuel))
                            (args (boymoo-model::core-datum (boymoo-model::core-eval-step :terms terms env program (1- fuel))))))))
  :rule-classes nil)
