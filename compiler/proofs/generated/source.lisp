(in-package "BOYMOO-PROOFS")

(include-book "emission")

(logic)
(set-verify-guards-eagerness 0)

(in-theory (disable boymoo-model::core-eval-step boymoo-model::core-call
                    boymoo-model::core-attachment boymoo-model::core-definition
                    boymoo-model::core-mbe-call-p boymoo-compiler::gen-term
                    boymoo-compiler::gen-lambda-args boymoo-compiler::gen-call-info
                    boymoo-compiler::gen-slot boymoo-compiler::bind-formal
                    boymoo-compiler::index-get boymoo-compiler::gen-simple-p))

(defthm generated-source-variable
  (implies (and (symbolp name) (posp fuel))
           (equal (boymoo-model::core-eval-step :term name env program fuel)
                  (let ((binding (assoc-eq name env)))
                    (if binding (boymoo-model::core-value (cdr binding)) :no-value))))
  :hints (("Goal" :expand (boymoo-model::core-eval-step :term name env program fuel))))

(defthm generated-source-quote
  (implies (posp fuel)
           (equal (boymoo-model::core-eval-step :term (list 'quote datum) env program fuel)
                  (boymoo-model::core-value datum)))
  :hints (("Goal" :expand (boymoo-model::core-eval-step :term (list 'quote datum)
                                                       env program fuel))))

(defthm generated-source-if
  (implies (posp fuel)
           (equal (boymoo-model::core-eval-step :term (list 'if test yes no) env program fuel)
                  (let ((result (boymoo-model::core-eval-step :term test env program (1- fuel))))
                    (if (boymoo-model::core-value-p result)
                        (boymoo-model::core-eval-step :term
                                                     (if (boymoo-model::core-datum result) yes no)
                                                     env program (1- fuel))
                      result))))
  :hints (("Goal" :expand (boymoo-model::core-eval-step :term (list 'if test yes no)
                                                       env program fuel))))

(defthm generated-source-mbe
  (implies (and (posp fuel) (boymoo-model::core-mbe-call-p term))
           (equal (boymoo-model::core-eval-step :term term env program fuel)
                  (boymoo-model::core-eval-step :term (cadddr term) env program (1- fuel))))
  :hints (("Goal" :expand (boymoo-model::core-eval-step :term term env program fuel)
                  :in-theory (enable boymoo-model::core-mbe-call-p))))

(defthm generated-source-lambda
  (implies (posp fuel)
           (equal (boymoo-model::core-eval-step
                   :term (cons (list 'lambda formals body) actuals) env program fuel)
                  (let ((args (boymoo-model::core-eval-step
                               :terms actuals env program (1- fuel))))
                    (if (boymoo-model::core-value-p args)
                        (boymoo-model::core-eval-step
                         :term body (pairlis$ formals (boymoo-model::core-datum args))
                         program (1- fuel))
                      args))))
  :hints (("Goal" :expand (boymoo-model::core-eval-step
                            :term (cons (list 'lambda formals body) actuals) env program fuel)
                  :in-theory (enable boymoo-model::core-mbe-call-p))))

(defthm generated-source-arguments-first-then-rest
  (implies (posp fuel)
           (equal (boymoo-model::core-eval-step :terms (cons first rest) env program fuel)
                  (let ((value (boymoo-model::core-eval-step :term first env program (1- fuel))))
                    (if (boymoo-model::core-value-p value)
                        (let ((values (boymoo-model::core-eval-step :terms rest env program (1- fuel))))
                          (if (boymoo-model::core-value-p values)
                              (boymoo-model::core-value
                               (cons (boymoo-model::core-datum value) (boymoo-model::core-datum values)))
                            values))
                      value))))
  :hints (("Goal" :expand (boymoo-model::core-eval-step :terms (cons first rest) env program fuel)))
  :rule-classes nil)

(defthm generated-variable-actual-uses-existing-slot
  (implies (and (consp args) (consp formals) (atom (car args)))
           (equal (boymoo-compiler::gen-lambda-args
                   args formals scope body-scope depth context code high serial)
                  (boymoo-compiler::gen-lambda-args
                   (cdr args) (cdr formals) scope
                   (boymoo-compiler::bind-formal
                    (car formals) (boymoo-compiler::gen-slot (car args) scope) body-scope)
                   depth context code high serial)))
  :hints (("Goal" :expand (boymoo-compiler::gen-lambda-args
                            args formals scope body-scope depth context code high serial)))
  :rule-classes nil)

(defun generated-attachment-chain-p (chain args program)
  (and (consp chain)
       (symbolp (car chain))
       (if (consp (cdr chain))
           (let ((attachment (boymoo-model::core-attachment (car chain) program)))
             (and (not (boymoo-model::core-primitive (car chain) args program))
                  attachment (equal (cadr attachment) (cadr chain))
                  (generated-attachment-chain-p (cdr chain) args program)))
         (null (cdr chain)))))

(local
 (defun generated-attachment-induction (chain fuel)
   (if (or (zp fuel) (atom (cdr chain)))
       chain
     (generated-attachment-induction (cdr chain) (1- fuel)))))

(defthm generated-source-call-follows-chain
  (implies (and (generated-attachment-chain-p chain args program)
                (natp fuel) (<= (len chain) fuel))
           (equal (boymoo-model::core-eval-step :call (car chain) args program fuel)
                  (boymoo-model::core-eval-step
                   :call (car (last chain)) args program (- (1+ fuel) (len chain)))))
  :hints (("Goal" :induct (generated-attachment-induction chain fuel)
                  :expand (boymoo-model::core-eval-step :call (car chain) args program fuel)))
  :rule-classes nil)

(defthm generated-source-defined-call
  (implies (and (posp fuel) (boymoo-model::core-definition name program)
                (not (boymoo-model::core-attachment name program))
                (not (boymoo-model::core-primitive name args program))
                (not (boymoo-model::core-prelude name args)))
           (let ((definition (boymoo-model::core-definition name program)))
             (equal (boymoo-model::core-eval-step :call name args program fuel)
                    (boymoo-model::core-eval-step :term (caddr definition)
                                                 (pairlis$ (cadr definition) args)
                                                 program (1- fuel)))))
  :hints (("Goal" :expand (boymoo-model::core-eval-step :call name args program fuel)))
  :rule-classes nil)

(defthm generated-defined-call-info-from-agreeing-indexes
  (implies (and (stringp resolved) (natp arity)
                (proof-index-agrees-p (list (cons head resolved)) (cadr context))
                (proof-index-agrees-p (list (cons resolved arity)) (car context))
                (not (assoc-equal resolved boymoo-compiler::*jets*))
                (not (assoc-equal resolved boymoo-compiler::*primitives*)))
           (equal (boymoo-compiler::gen-call-info head context) (list resolved arity nil)))
  :hints (("Goal" :in-theory (e/d (boymoo-compiler::gen-call-info) (assoc-equal))))
  :rule-classes nil)

(defthm generated-runtime-call-info-from-agreeing-index
  (implies (and (stringp resolved) (natp arity) (stringp label)
                (proof-index-agrees-p (list (cons head resolved)) (cadr context))
                (equal (or (assoc-equal resolved boymoo-compiler::*jets*)
                           (assoc-equal resolved boymoo-compiler::*primitives*))
                       (list* resolved arity label)))
           (equal (boymoo-compiler::gen-call-info head context) (list resolved arity label)))
  :hints (("Goal" :in-theory (e/d (boymoo-compiler::gen-call-info) (assoc-equal))))
  :rule-classes nil)
