(in-package "BOYMOO-PROVER")

(include-book "driver")

; Each field begins with its byte length as a four-byte unsigned integer.
(defun prover-field-size (text pos)
  (+ (* 16777216 (char-code (char text pos)))
     (* 65536 (char-code (char text (+ pos 1))))
     (* 256 (char-code (char text (+ pos 2))))
     (char-code (char text (+ pos 3)))))

(defun prover-fields (text pos end fields)
  (declare (xargs :measure (nfix fields)))
  (if (zp fields)
      (equal pos end)
    (let ((start (+ pos 4)))
      (if (< end start)
          nil
        (let ((stop (+ start (prover-field-size text pos))))
          (if (< end stop)
              nil
            (let ((rest (prover-fields text stop end (- fields 1))))
              (and rest (cons (subseq text start stop) rest)))))))))

(defun prover-entry-options (sets ranks)
  (let* ((names (and (not (equal sets "")) (text-split sets ",")))
         (digits (coerce ranks 'list)))
    (if (and (subsetp-equal names *prove-sets*)
             (no-duplicatesp-equal names)
             (reader-all-digits-p digits))
        (cons t (append (and names (list (cons :sets names)))
                        (and digits (list (cons :ranks (reader-decimal digits 0))))))
      nil)))

(defun prover-entry-result (ground library statements aids options)
  (if (equal ground "")
      (let ((proof (driver-prove library statements aids options)))
        (and (stringp proof) proof))
    (let* ((result (driver-prove-checked ground library statements aids options))
           (proof (car result))
           (verdict (cadr result)))
      (and (stringp proof)
           (or (equal verdict "accepted") (prove-provisional verdict))
           proof))))

(defun prover-entry (text)
  (let* ((fields (prover-fields text 0 (length text) 6))
         (options (and fields (prover-entry-options (fifth fields) (sixth fields)))))
    (and options
         (prover-entry-result (first fields) (second fields) (third fields)
                              (fourth fields) (cdr options)))))
