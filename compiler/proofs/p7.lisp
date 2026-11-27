(in-package "BOYMOO-COMPILER")

(include-book "../isel")
(include-book "qir-semantics")
(include-book "mir-semantics")
(include-book "word-properties")

(logic)
(set-verify-guards-eagerness 0)

(defthm p7-isel-word-is-model-word
  (equal (isel-word x) (model-word x)))

(defthm p7-isel-signed-is-model-signed
  (equal (isel-signed x) (model-signed x)))

(in-theory (disable isel-word model-word low-bits))

(defthmd p7-copy-of-constant-preserves-value
  (implies (and dest (unsigned-byte-p 64 value))
           (let* ((operand (cons :k value))
                  (code (isel-copy dest operand out)))
             (and (equal code (cons (list :li dest (model-word value)) out))
                  (equal (mir-pure-result (car code) nil)
                         (qir-operand operand env :l heap)))))
  :hints (("Goal" :in-theory (enable mir-pure-result qir-operand))))

(defthmd p7-copy-of-temporary-preserves-value
  (implies (and (qir-temp-p source) dest (not (equal dest source))
                (equal (assoc-equal (cdr source) mir-env)
                       (cons (cdr source) (cdr (assoc-equal source qir-env))))
                (assoc-equal source qir-env))
           (let* ((code (isel-copy dest source out))
                  (operand (mir-operand source mir-env)))
             (and (equal code (cons (list :mov dest source) out))
                  (equal (mir-pure-result (car code) (list (boymoo-model::core-datum operand)))
                         (qir-operand source qir-env :l heap)))))
  :hints (("Goal" :in-theory (enable mir-pure-result mir-operand qir-operand))))

(defthmd p7-add-immediate-preserves-value
  (implies (and (qir-temp-p source) (unsigned-byte-p 12 imm))
           (let ((code (mv-nth 1 (isel-binop dest :add source (cons :k imm) fresh out))))
             (and (equal code (cons (list :rri :add dest source imm) out))
                  (equal (mir-pure-result (car code) (list a))
                         (boymoo-model::core-value (model-word-op :add a imm))))))
  :hints (("Goal" :in-theory (e/d (mir-pure-result unsigned-byte-p integer-range-p)
                                   (model-word low-bits))
           :use (:instance model-word-in-range (x imm))
           :do-not-induct t)))

(defthmd p7-add-register-preserves-value
  (implies (and (qir-temp-p left) (qir-temp-p right))
           (let ((code (mv-nth 1 (isel-binop dest :add left right fresh out))))
             (and (equal code (cons (list :rrr :add-reg dest left right) out))
                  (equal (mir-pure-result (car code) (list a b))
                         (boymoo-model::core-value (model-word-op :add a b))))))
  :hints (("Goal" :in-theory (enable mir-pure-result)
           :do-not-induct t)))
