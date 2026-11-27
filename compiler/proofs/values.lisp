(in-package "BOYMOO-COMPILER")

(include-book "../index")
(include-book "../../compiler/model/core")
(include-book "../../compiler/model/a64-state")

(logic)
(set-verify-guards-eagerness 0)

(defconst *model-nil-word* 34)
(defconst *model-t-word* 58)

(defun model-word (x)
  (low-bits (ifix x) 64))

(defun model-signed (x)
  (let ((bits (model-word x)))
    (if (< bits #x8000000000000000) bits (- bits #x10000000000000000))))

(defun model-immediate-integer-p (x)
  (signed-byte-p 63 x))

(defun model-integer-word (x)
  (model-word (+ 1 (* 2 (ifix x)))))

(defun model-character-word (x)
  (+ 4 (* 8 (char-code x))))

; Boxed constants are supplied by an association list from words to data.
; The interpretation of the immediate words does not depend on that list.
(defund model-constant (word constants)
  (if (not (integerp word))
      :malformed
    (let* ((word (model-word word))
           (tag (logand word 7)))
      (cond ((logbitp 0 word)
             (boymoo-model::core-value (ash (model-signed word) -1)))
            ((equal word *model-nil-word*) (boymoo-model::core-value nil))
            ((equal word *model-t-word*) (boymoo-model::core-value t))
            ((and (equal tag 4) (< word 2048))
             (boymoo-model::core-value (code-char (ash word -3))))
            (t (let ((entry (assoc-equal word constants)))
                 (if entry (boymoo-model::core-value (cdr entry)) :malformed)))))))

(defun model-routine-symbol (name)
  (if (equal (subseq name 0 6) "ACL2::")
      (acl2::intern-in-package-of-symbol (subseq name 6 nil) 'acl2::acl2-numberp)
    (acl2::intern-in-package-of-symbol (subseq name 13 nil) 'common-lisp::nil)))

(defund model-routine (name args program)
  (let ((primitive (assoc-equal name *primitives*))
        (prelude (assoc-equal name *jets*)))
    (cond ((and primitive (equal (len args) (cadr primitive)))
           (boymoo-model::core-primitive (model-routine-symbol name) args program))
          ((and prelude (equal (len args) (cadr prelude)))
           (boymoo-model::core-prelude (model-routine-symbol name) args))
          (t :malformed))))

(defthm model-constant-of-nil
  (equal (model-constant *model-nil-word* constants)
         (boymoo-model::core-value nil))
  :hints (("Goal" :in-theory (enable model-constant))))

(defthm model-constant-of-t
  (equal (model-constant *model-t-word* constants)
         (boymoo-model::core-value t))
  :hints (("Goal" :in-theory (enable model-constant))))

(defthm model-lookup-of-alist-update
  (equal (assoc-equal key (put-assoc-equal dest value env))
         (if (equal key dest) (cons key value) (assoc-equal key env)))
  :hints (("Goal" :induct (put-assoc-equal dest value env))))

(assert-event
 (equal (model-routine "COMMON-LISP::CAR" '((1 . 2)) nil)
        (boymoo-model::core-value 1)))

(assert-event
 (equal (model-routine "ACL2::BINARY-+" '(9 -11) nil)
        (boymoo-model::core-value -2)))
