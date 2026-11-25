(in-package "BOYMOO")

(include-book "check")

; A field begins with four bytes giving its length in big-endian order.
(defun checker-field-size (text pos)
  (+ (* 16777216 (char-code (char text pos)))
     (* 65536 (char-code (char text (+ pos 1))))
     (* 256 (char-code (char text (+ pos 2))))
     (char-code (char text (+ pos 3)))))

; A successful read returns the remaining fields as conses ending in T.
; NIL indicates a malformed frame.
(defun checker-fields (text pos end fields)
  (declare (xargs :measure (nfix fields)))
  (if (zp fields)
      (equal pos end)
    (let ((start (+ pos 4)))
      (if (< end start)
          nil
        (let ((stop (+ start (checker-field-size text pos))))
          (if (< end stop)
              nil
            (let ((rest (checker-fields text stop end (- fields 1))))
              (and rest (cons (subseq text start stop) rest)))))))))

(defun checker-verdict (ground library statements proofs library-proofs)
  (let ((result (check-four ground library statements proofs library-proofs)))
    (coerce (app (coerce (car result) 'list) (list #\Newline)) 'string)))

(defun checker-entry (text)
  (let ((fields (checker-fields text 0 (length text) 5)))
    (if (consp fields)
        (checker-verdict (first fields) (second fields) (third fields)
                         (fourth fields) (fifth fields))
      "invalid checker input frame
")))
