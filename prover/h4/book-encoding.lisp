(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(mutual-recursion
 (defun h4-book-encoding-proof-lines-encode (value)
   (declare (xargs :measure (1+ (* 2 (acl2-count value)))))
   (if (and (consp value) (proof-compound value))
       (proof-with-checked-results
        ((parts (h4-book-encoding-encode-compound value t)))
        (text-join "" (cons "(" parts)))
     (proof-write value)))
 (defun h4-book-encoding-encode-compound (values firstp)
   (declare (xargs :measure (* 2 (acl2-count values))))
   (cond
    ((endp values) (list ")"))
    ((and (endp (cdr values)) (consp (car values)) (equal (caar values) "dot"))
     (proof-with-checked-results
      ((tail (proof-term-at (car values) 1))
       (encoded (h4-book-encoding-proof-lines-encode tail)))
      (list " . " encoded ")")))
    (t
     (proof-with-checked-results
      ((encoded (h4-book-encoding-proof-lines-encode (car values)))
       (more (h4-book-encoding-encode-compound (cdr values) nil)))
      (if firstp (cons encoded more) (list* " " encoded more)))))))

(defun h4-book-encoding-encode-items (items)
  (if (endp items)
      nil
    (proof-with-checked-results
     ((first (h4-book-encoding-proof-lines-encode (car items)))
      (rest (h4-book-encoding-encode-items (cdr items))))
     (cons first rest))))

; A visit returns the line number, the number and source tables, and
; the next line number. The source table has the newest entry first.
(mutual-recursion
 (defun h4-book-encoding-visit (step numbers emitted next)
   (declare (xargs :measure (acl2-count step)))
   (if (not (proof-step-p step))
       '(:failure "failure" "")
     (let ((prior (assoc-equal step numbers)))
       (if prior
           (list (cdr prior) numbers emitted next)
         (proof-with-checked-results
          ((arguments (h4-book-encoding-number-arguments
                       (proof-step-data step) numbers emitted next))
           (items (h4-book-encoding-encode-items (car arguments)))
           (word (h4-api-encoding-ascii-text (proof-step-word step))))
          (let* ((source (concatenate 'string "("
                                      (text-join " " (cons word items)) ")"
                                      (coerce (list #\Newline) 'string)))
                 (numbers (cadr arguments))
                 (emitted (caddr arguments))
                 (next (cadddr arguments))
                 (duplicate (assoc-equal source emitted)))
            (if duplicate
                (list (cdr duplicate) (acons step (cdr duplicate) numbers) emitted next)
              (list next (acons step next numbers) (acons source next emitted) (1+ next)))))))))
 (defun h4-book-encoding-number-arguments (data numbers emitted next)
   (declare (xargs :measure (acl2-count data)))
   (if (endp data)
       (list nil numbers emitted next)
     (proof-with-checked-results
      ((first (if (proof-step-p (car data))
                  (h4-book-encoding-visit (car data) numbers emitted next)
                (list (car data) numbers emitted next)))
       (rest (h4-book-encoding-number-arguments
              (cdr data) (cadr first) (caddr first) (cadddr first))))
      (cons (cons (car first) (car rest)) (cdr rest))))))

(defun h4-book-encoding-proof-lines (last)
  (proof-with-checked-results
   ((visited (h4-book-encoding-visit last nil nil 1)))
   (proof-emitted-lines (caddr visited) nil)))

(defun h4-book-encoding-entry-proofs (proofs count reversed)
  (if (endp proofs)
      (list count (text-join "" (reverse reversed)))
    (proof-with-checked-results
     ((steps (h4-book-encoding-proof-lines (car proofs)))
      (qed (proof-line "qed" nil)))
     (h4-book-encoding-entry-proofs (cdr proofs) (+ count (len steps))
                                   (cons qed (revappend steps reversed))))))

(defun h4-book-encoding-book-entry (kind name arguments proofs)
  (proof-with-checked-results
   ((kind (h4-api-encoding-ascii-text kind))
    (header (proof-line kind (cons name arguments))))
   (h4-book-encoding-entry-proofs proofs 0 (list header))))
