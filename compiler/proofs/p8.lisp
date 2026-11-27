(in-package "BOYMOO-COMPILER")

(include-book "rega-check")
(include-book "mir-semantics")

(logic)
(set-verify-guards-eagerness 0)

(defund rega-agreement (live except homes virtual physical)
  (if (endp live)
      t
    (let* ((number (car live))
           (value (assoc-equal number virtual))
           (stored (assoc-equal (ntab-get number homes) physical)))
      (and (or (equal number except) (and value stored (equal (cdr value) (cdr stored))))
           (rega-agreement (cdr live) except homes virtual physical)))))

; Apply an arbitrary sequence of writes allowed by a calling convention.
(defund rega-clobber (kind writes physical)
  (if (endp writes)
      physical
    (let* ((write (car writes))
           (physical (if (rega-surviving-home-p kind (car write))
                         physical
                       (put-assoc-equal (car write) (cdr write) physical))))
      (rega-clobber kind (cdr writes) physical))))

(in-theory (disable ntab-get rega-surviving-home-p rega-home-p))

(defthmd p8-checked-block-has-consistent-live-in
  (implies (mv-nth 0 (rega-check-instructions reversed live homes nspill))
           (equal (mv-nth 1 (rega-check-instructions reversed live homes nspill))
                  (mir-insts-live reversed live)))
  :hints (("Goal" :induct (rega-check-instructions reversed live homes nspill)
           :in-theory (disable rega-instruction-safe-p mir-inst-live))))

(defthmd p8-preserved-home-after-clobber
  (implies (rega-surviving-home-p kind place)
           (equal (assoc-equal place (rega-clobber kind writes physical))
                  (assoc-equal place physical)))
  :hints (("Goal" :induct (rega-clobber kind writes physical)
           :in-theory (enable rega-clobber))))

(defthmd p8-live-values-survive-call-clobbers
  (implies (and (rega-live-safe-p live dest home kind homes nspill)
                (rega-agreement live dest homes virtual physical))
           (rega-agreement live dest homes virtual (rega-clobber kind writes physical)))
  :hints (("Goal" :induct (rega-live-safe-p live dest home kind homes nspill)
           :in-theory (enable p8-preserved-home-after-clobber rega-agreement))))

(defthmd p8-live-values-survive-definition
  (let ((home (ntab-get dest homes)))
    (implies (and (nat-listp live) (natp dest)
                  (rega-live-safe-p live dest home kind homes nspill)
                  (rega-agreement live dest homes virtual physical))
             (rega-agreement live nil homes (put-assoc-equal dest value virtual)
                                (put-assoc-equal home value physical))))
  :hints (("Goal" :induct (rega-live-safe-p live dest (ntab-get dest homes) kind homes nspill)
           :in-theory (enable rega-agreement))))

(defthmd p8-checked-instruction-result-stays-in-agreement
  (let* ((dest (mir-dest inst))
         (number (cdr dest))
         (home (ntab-get number homes))
         (kind (car inst)))
    (implies (and (rega-instruction-safe-p inst live homes nspill)
                  (qir-temp-p dest) (nat-listp live)
                  (rega-agreement live number homes virtual physical))
             (rega-agreement live nil homes (put-assoc-equal number value virtual)
                                (put-assoc-equal home value (rega-clobber kind writes physical)))))
  :hints (("Goal" :use ((:instance p8-live-values-survive-call-clobbers
                                    (dest (cdr (mir-dest inst))) (kind (car inst))
                                    (home (ntab-get (cdr (mir-dest inst)) homes)))
                         (:instance p8-live-values-survive-definition
                                    (dest (cdr (mir-dest inst))) (kind (car inst))
                                    (physical (rega-clobber (car inst) writes physical))))
           :in-theory (disable mir-dest rega-live-safe-p))))

(defthmd p8-live-temp-agrees-with-home
  (let ((virtual-value (assoc-equal number virtual))
        (physical-value (assoc-equal (ntab-get number homes) physical)))
    (implies (and (rega-agreement live except homes virtual physical)
                  (member-equal number live) (not (equal number except)))
             (and virtual-value physical-value (equal (cdr virtual-value) (cdr physical-value)))))
  :hints (("Goal" :induct (rega-agreement live except homes virtual physical)
           :in-theory (enable rega-agreement))))

(defthmd p8-rewriting-a-live-operand-preserves-value
  (implies (and (qir-temp-p operand) (member-equal (cdr operand) live)
                (rega-home-p (ntab-get (cdr operand) homes) nspill)
                (rega-agreement live nil homes virtual physical))
           (equal (mir-operand (rega-operand operand homes) physical)
                  (mir-operand operand virtual)))
  :hints (("Goal" :use (:instance p8-live-temp-agrees-with-home (number (cdr operand)) (except nil))
           :in-theory (enable rega-home-p mir-operand))))

(defun p8-all-allocations-valid-p (functions)
  (if (endp functions)
      t
    (and (rega-allocation-valid-p (car functions) (rega-allocation (car functions)))
         (p8-all-allocations-valid-p (cdr functions)))))

(defthmd p8-validated-program-is-assigned-program
  (implies (p8-all-allocations-valid-p functions)
           (equal (rega-validated-program functions) (rega-program functions)))
  :hints (("Goal" :induct (rega-program functions)
           :in-theory (disable rega-allocation-valid-p rega-allocation rega-apply))))

(defun p8-sources-live-p (operands live)
  (if (endp operands)
      t
    (and (or (not (qir-temp-p (car operands))) (member-equal (cdar operands) live))
         (p8-sources-live-p (cdr operands) live))))

(defthmd p8-rewriting-a-constant-preserves-value
  (implies (qir-const-p operand)
           (equal (mir-operand (rega-operand operand homes) physical)
                  (mir-operand operand virtual)))
  :hints (("Goal" :in-theory (enable mir-operand))))

(defthmd p8-rewriting-live-operands-preserves-values
  (implies (and (rega-operands-have-homes-p operands homes nspill)
                (p8-sources-live-p operands live)
                (rega-agreement live nil homes virtual physical))
           (equal (mir-arguments (rega-operands operands homes) physical)
                  (mir-arguments operands virtual)))
  :hints (("Goal" :induct (rega-operands operands homes)
           :in-theory (e/d (mir-arguments p8-rewriting-a-constant-preserves-value
                            p8-rewriting-a-live-operand-preserves-value)
                           (rega-operand qir-const-p qir-temp-p)))))

; This predicate supplies the syntax needed by the pure MIR evaluator.
(defund p8-pure-instruction-p (inst)
  (and (qir-temp-p (mir-dest inst))
       (case (car inst)
         (:li (integerp (caddr inst)))
         (:mov (qir-temp-p (caddr inst)))
         (:rrr (and (mir-register-op (cadr inst))
                    (qir-temp-p (cadddr inst))
                    (qir-temp-p (car (cddddr inst)))))
         (:rri (and (mir-immediate-op (cadr inst))
                    (qir-temp-p (cadddr inst))
                    (integerp (car (cddddr inst)))))
         (otherwise nil))))

(defthmd p8-pure-destination-is-temporary
  (implies (p8-pure-instruction-p inst)
           (and (qir-temp-p (mir-dest inst)) (consp (mir-dest inst))
                (natp (cdr (mir-dest inst)))))
  :hints (("Goal" :in-theory (enable p8-pure-instruction-p))))

(defthmd p8-placed-destination
  (let ((home (ntab-get (cdr dest) homes)))
    (implies (and (qir-temp-p dest) (rega-home-p home nspill))
             (and (equal (rega-operand dest homes) home)
                  (not (qir-temp-p home)))))
  :hints (("Goal" :in-theory (enable rega-home-p))))

(defthmd p8-pure-rewrite-sources
  (implies (p8-pure-instruction-p inst)
           (equal (mir-sources (rega-fields inst homes))
                  (rega-operands (mir-sources inst) homes)))
  :hints (("Goal" :in-theory (enable p8-pure-instruction-p))))

(defthmd p8-pure-rewrite-destination
  (implies (p8-pure-instruction-p inst)
           (equal (mir-dest (rega-fields inst homes))
                  (rega-operand (mir-dest inst) homes)))
  :hints (("Goal" :in-theory (enable p8-pure-instruction-p))))

(defthmd p8-pure-rewrite-operation
  (implies (p8-pure-instruction-p inst)
           (equal (mir-pure-result (rega-fields inst homes) args)
                  (mir-pure-result inst args)))
  :hints (("Goal" :in-theory (enable p8-pure-instruction-p mir-pure-result))))

(defund p8-step-pure (instruction env)
  (let* ((operands (mir-arguments (mir-sources instruction) env))
         (result (mir-pure-result instruction (boymoo-model::core-datum operands)))
         (dest (mir-dest instruction)))
    (if (and (boymoo-model::core-value-p operands) (boymoo-model::core-value-p result))
        (boymoo-model::core-value
         (put-assoc-equal (if (qir-temp-p dest) (cdr dest) dest)
                          (boymoo-model::core-datum result) env))
      :malformed)))

(defthmd p8-checked-pure-rewrite-preserves-agreement
  (let* ((source-result (p8-step-pure inst virtual))
         (target-result (p8-step-pure (rega-fields inst homes) physical))
         (dest (cdr (mir-dest inst))))
    (implies (and (p8-pure-instruction-p inst)
                  (rega-instruction-safe-p inst after homes nspill)
                  (p8-sources-live-p (mir-sources inst) before)
                  (rega-agreement before nil homes virtual physical)
                  (rega-agreement after dest homes virtual physical)
                  (nat-listp after)
                  (boymoo-model::core-value-p source-result))
             (and (boymoo-model::core-value-p target-result)
                  (rega-agreement after nil homes (boymoo-model::core-datum source-result)
                                     (boymoo-model::core-datum target-result)))))
  :hints (("Goal"
           :use (p8-pure-destination-is-temporary
                 (:instance p8-placed-destination (dest (mir-dest inst)))
                 (:instance p8-rewriting-live-operands-preserves-values
                            (operands (mir-sources inst)) (live before))
                 (:instance p8-live-values-survive-definition
                            (live after) (dest (cdr (mir-dest inst))) (kind (car inst))
                            (value (boymoo-model::core-datum
                                    (mir-pure-result inst (boymoo-model::core-datum
                                                             (mir-arguments (mir-sources inst) virtual)))))))
           :in-theory (e/d (p8-step-pure p8-pure-rewrite-sources
                            p8-pure-rewrite-destination p8-pure-rewrite-operation)
                           (mir-dest mir-sources rega-fields rega-agreement rega-live-safe-p
                            rega-operands-have-homes-p rega-operand qir-temp-p))
           :do-not-induct t)))

(assert-event
 (let* ((function '(:mfn "ACL2::MOVE" ((:d . 0) (:d . 1)) 0
                    ((0 ((:mov (:d . 2) (:d . 0)) (:li (:w . 3) 7)) (:ret (:d . 2))))))
        (allocation (rega-allocation function))
        (homes (car allocation))
        (overlap (ntab-put 3 (ntab-get 2 homes) homes)))
   (and (rega-allocation-valid-p function allocation)
        (equal (rega-validated-program (list function)) (list (rega-function function)))
        (not (rega-validate function overlap (cadr allocation) (caddr allocation))))))

(local
 (defun p8-call-fixture (kind label)
   (list :mfn "ACL2::CROSS" '((:d . 0)) 0
         (list (list 0 (list '(:li (:w . 1) 7)
                            (list kind label '((:d . 0)) nil)
                            '(:mov (:d . 2) (:w . 1)))
                     '(:ret (:d . 2)))) 3)))

(assert-event
 (let* ((function (p8-call-fixture :call "ACL2::CALLEE"))
        (allocation (rega-allocation function))
        (homes (car allocation))
        (clobbered (ntab-put 1 '(:x . 19) homes))
        (incorrect-live (ntab-put 0 nil (caddr allocation))))
   (and (rega-allocation-valid-p function allocation)
        (equal (car (ntab-get 1 homes)) :m)
        (not (rega-validate function clobbered (cadr allocation) (caddr allocation)))
        (not (rega-validate function homes (cadr allocation) incorrect-live)))))

(assert-event
 (let* ((function (p8-call-fixture :rt "prim:COMMON-LISP::CONSP"))
        (allocation (rega-allocation function))
        (homes (car allocation))
        (clobbered (ntab-put 1 '(:x . 1) homes)))
   (and (rega-allocation-valid-p function allocation)
        (rega-surviving-home-p :rt (ntab-get 1 homes))
        (not (rega-validate function clobbered (cadr allocation) (caddr allocation))))))
