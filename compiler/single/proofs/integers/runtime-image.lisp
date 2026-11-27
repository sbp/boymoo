(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

(defconst *integer-runtime-items*
  (append (boymoo-compiler::linux-system-code)
          (boymoo-compiler::runtime-code)
          '((:label "rt:entry") (:ret)
            (:label "data:static") (:quad 8))))

(defconst *integer-runtime-labels*
  (mv-let (end labels reversed)
    (boymoo-compiler::a64-layout *integer-runtime-items* 0 nil nil)
    (declare (ignore end reversed))
    labels))

(defconst *integer-runtime-bytes*
  (boymoo-compiler::a64-bytes *integer-runtime-items*))

(defun integer-runtime-address (label base)
  (proof-label-address label base *integer-runtime-labels*))

(defun integer-decode-runtime-instructions (count offset)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (let* ((text *integer-runtime-bytes*)
           (word (+ (char-code (char text offset))
                    (* 256 (char-code (char text (+ offset 1))))
                    (* 65536 (char-code (char text (+ offset 2))))
                    (* 16777216 (char-code (char text (+ offset 3)))))))
      (cons (proof-decode word)
            (integer-decode-runtime-instructions (1- count) (+ offset 4))))))

(defun integer-runtime-instructions (label displacement count)
  (integer-decode-runtime-instructions
   count (+ (integer-runtime-address label 0) displacement)))

