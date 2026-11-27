(in-package "BOYMOO-COMPILER")

(include-book "../qir")
(include-book "word-ops")

(logic)
(set-verify-guards-eagerness 0)

; A virtual environment is keyed by temporary number. After assignment
; the same operations read an environment keyed by register or slot.
(defund mir-operand (operand env)
  (if (qir-const-p operand)
      (boymoo-model::core-value (model-word (cdr operand)))
    (let ((entry (assoc-equal (if (qir-temp-p operand) (cdr operand) operand) env)))
      (if entry (boymoo-model::core-value (cdr entry)) :malformed))))

(defund mir-arguments (operands env)
  (if (endp operands)
      (boymoo-model::core-value nil)
    (let ((first (mir-operand (car operands) env)))
      (if (not (boymoo-model::core-value-p first))
          first
        (let ((rest (mir-arguments (cdr operands) env)))
          (if (boymoo-model::core-value-p rest)
              (boymoo-model::core-value (cons (boymoo-model::core-datum first)
                                              (boymoo-model::core-datum rest)))
            rest))))))

(defun mir-register-op (op)
  (case op
    (:add-reg :add) (:sub-reg :sub) (:mul :mul)
    (:and-reg :and) (:orr-reg :or) (:eor-reg :xor)
    (:lslv :shl) (:lsrv :shr) (:asrv :sar)
    (otherwise nil)))

(defun mir-immediate-op (op)
  (case op
    (:add :add) (:sub :sub) (:and-mask :and)
    (:lsl :shl) (:lsr :shr) (:asr :sar)
    (otherwise nil)))

; This fragment consists of instructions that produce a result from
; their operands and do not use flags, memory, or calling conventions.
(defund mir-pure-result (inst args)
  (case (car inst)
    (:li (boymoo-model::core-value (model-word (caddr inst))))
    (:mov (boymoo-model::core-value (car args)))
    (:rrr (let ((op (mir-register-op (cadr inst))))
            (if op (boymoo-model::core-value (model-word-op op (car args) (cadr args)))
              :malformed)))
    (:rri (let* ((op (mir-immediate-op (cadr inst)))
                 (imm (car (cddddr inst)))
                 (b (if (eq (cadr inst) :and-mask) (1- (ash 1 imm)) imm)))
            (if op (boymoo-model::core-value (model-word-op op (car args) b))
              :malformed)))
    (otherwise :malformed)))
