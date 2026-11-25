(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-reuse-fact* '("(fact " 1 ")"))

(defun b2-reuse-parse (raw)
  (proof-with-checked-results
   ((line (reader-reader-line (reader-reader raw))))
   (list (caar line) (proof-freeze (cadar line)))))

(defun b2-reuse-head (entry)
  (proof-with-checked-results
   ((source (proof-term-at entry 3)))
   (let ((newline (text-find source (coerce (list #\Newline) 'string))))
     (if (< newline 0)
         source
       (seq-slice source 0 newline)))))

(defun b2-reuse-definition-names (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((name (proof-term-at (car definitions) 0))
      (rest (b2-reuse-definition-names (cdr definitions))))
     (cons name rest))))

(defun b2-reuse-declares (entry)
  (proof-with-checked-results
   ((kind (proof-term-at entry 0)))
   (cond
    ((equal kind "define")
     (proof-with-checked-results
      ((header (b2-reuse-head entry))
       (line (b2-reuse-parse header)))
      (b2-reuse-definition-names (cdr (cadr line)))))
    ((equal kind "lemma")
     (proof-with-checked-results
      ((name (proof-term-at entry 1)))
      (list name)))
    (t nil))))

