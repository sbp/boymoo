(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-generate-default-reasons*
  '(("STATE-P1-UPDATE-MAIN-TIMER" . "global-table update invariant")
    ("STATE-P1-UPDATE-PRINT-BASE" . "global-table update invariant")
    ("STATE-P1-UPDATE-NTH-2-WORLD" . "global-table update invariant")
    ("DEFAULT-<-1" . "numeric comparison completion")
    ("DEFAULT-<-2" . "numeric comparison completion")
    ("ADD-DEF-COMPLEX" . "componentwise complex addition")
    ("TRUE-LISTP-MERGE-SORT-LEXORDER" . "two-list induction")
    ("RESIZE-LIST-EXEC-IS-RESIZE-LIST" . "countdown with changing accumulator")
    ("EQLABLEP-NTH" . "list and index induction")
    ("FN-COUNT-EVG-REC-TYPE-PRESCRIPTION" . "event-count induction")
    ("FN-COUNT-EVG-REC-BOUND" . "event-count induction and bound")
    ("FN-COUNT-1-TYPE" . "induction with changing accumulators")
    ("SYMBOL-LISTP-CDR-ASSOC-EQUAL" . "association-list induction")
    ("ANCESTORS-CHECK-BUILTIN-PROPERTY" . "ancestor membership invariant")
    ("D-POS-LISTP-FORWARD-TO-TRUE-LISTP" . "list-recognizer induction")
    ("POS-LISTP-FORWARD-TO-INTEGER-LISTP" . "list-recognizer induction")
    ("TRUE-LISTP-CHARS-FOR-TILDE-@-CLAUSE-ID-PHRASE/PERIODS" . "list construction")
    ("TRUE-LISTP-EXPLODE-ATOM" . "result types of print helpers")
    ("SYMBOL-LISTP-STRICT-MERGE-SORT-SYMBOL<" . "merge and split invariants")))

(defun h3-generate-reason (name)
  (cond ((text-starts-with name "ALPHORDER-") "order on atomic types")
        ((text-starts-with name "LEXORDER-") "lexicographic induction")
        ((text-starts-with name "INTEGERP-NTH-") "count accumulator induction")
        (t (table-get *h3-generate-default-reasons* name
                        "conditional rewrite unresolved"))))

(defun h3-generate-admit-definitions (proof definitions)
  (if (endp definitions)
      proof
    (let* ((definition (car definitions))
           (size (len definition))
           (formals (cadr definition)))
      (cond
       ((integerp definition)
        '(:failure "failure" ""))
       ((/= size 3) '(:failure "failure" ""))
       ((integerp formals)
        '(:failure "failure" ""))
       ((stringp formals)
        '(:failure "failure" ""))
       (t (h3-generate-admit-definitions
           (proof-proof-add-definition proof (car definition) formals (caddr definition))
           (cdr definitions)))))))

(defun h3-generate-admit-constraints (facts constraints)
  (if (endp constraints)
      facts
    (proof-with-checked-results
     ((constraint (proof-list-of-length (car constraints) 2)))
     (h3-generate-admit-constraints
      (table-put facts (car constraint) (list (cadr constraint)))
      (cdr constraints)))))

(defun h3-generate-admit (library kind fields)
  (let ((proof (library-library-proof library)))
    (cond
     ((equal kind "define")
      (if (integerp fields)
          '(:failure "failure" "")
        (proof-with-checked-results
         ((proof (h3-generate-admit-definitions proof (cdr fields))))
         (library-library-with-proof library proof))))
     ((equal kind "constrain")
      (proof-with-checked-results
       ((constraints (proof-term-at fields 1)))
       (cond ((equal constraints *proof-nil*) library)
             ((integerp constraints) '(:failure "failure" ""))
             (t (proof-with-checked-results
                 ((facts (h3-generate-admit-constraints
                          (proof-proof-facts proof) constraints)))
                 (library-library-with-proof library (proof-proof-with-facts proof facts)))))))
     ((or (equal kind "theorem") (equal kind "axiom"))
      (proof-with-checked-results
       ((name (proof-term-at fields 0))
        (formula (proof-term-at fields 1)))
       (let ((facts (table-put (proof-proof-facts proof) name (list formula))))
         (library-library-with-proof library (proof-proof-with-facts proof facts)))))
     (t library))))

(defun h3-generate-entry-index (entries index)
  (if (endp entries)
      index
    (h3-generate-entry-index (cdr entries)
                             (table-put index (cadar entries) (car entries)))))

(defun h3-generate-fact-lines (entries fact-lines)
  (if (endp entries)
      fact-lines
    (let ((name (caar entries)))
      (proof-with-checked-results
       ((line (proof-line "fact" (list name))))
       (h3-generate-fact-lines (cdr entries) (table-put fact-lines line name))))))

(defun h3-generate-lines-with-endings (chars reversed)
  (if (endp chars)
      (and (consp reversed) (list (coerce (reverse reversed) 'string)))
    (let ((ch (car chars)))
      (cond ((and (eql ch #\Return) (eql (cadr chars) #\Newline))
             (cons (coerce (reverse (list* #\Newline ch reversed)) 'string)
                   (h3-generate-lines-with-endings (cddr chars) nil)))
            ((or (eql ch #\Return) (eql ch #\Newline))
             (cons (coerce (reverse (cons ch reversed)) 'string)
                   (h3-generate-lines-with-endings (cdr chars) nil)))
            (t (h3-generate-lines-with-endings (cdr chars) (cons ch reversed)))))))

(defun h3-generate-citations (lines fact-lines)
  (if (endp lines)
      nil
    (let ((fact (assoc-equal (car lines) fact-lines)))
      (if fact
          (cons (cdr fact) (h3-generate-citations (cdr lines) fact-lines))
        (h3-generate-citations (cdr lines) fact-lines)))))

(defun h3-generate-entry-citations (entry fact-lines)
  (h3-generate-citations
   (h3-generate-lines-with-endings (coerce (cadddr entry) 'list) nil)
   fact-lines))

(defun h3-generate-visit-citations (n pending entries fact-lines needed)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "Fuel" "h3-generate-visit-citations"))
   ((endp pending) needed)
   ((member-equal (car pending) needed)
    (h3-generate-visit-citations
     (1- n) (cdr pending) entries fact-lines needed))
   (t (let* ((name (car pending))
             (entry (assoc-equal name entries)))
        (if (not entry)
            (table-delete nil name)
          (let ((citations (h3-generate-entry-citations (cdr entry) fact-lines)))
            (h3-generate-visit-citations
             (1- n) (append citations (cdr pending)) entries fact-lines (cons name needed))))))))

(defun h3-generate-serialize-theorem-visit (n entry entries fact-lines needed)
  (proof-with-checked-results
   ((reversed (h3-generate-visit-citations
               n (h3-generate-entry-citations entry fact-lines) entries fact-lines (reverse needed))))
   (reverse reversed)))

(defun h3-generate-count-steps (counts total)
  (if (endp counts)
      total
    (h3-generate-count-steps (cdr counts) (+ total (car counts)))))

(defun h3-generate-selected-entries (entries needed)
  (cond ((endp entries) nil)
        ((member-equal (cadar entries) needed)
         (cons (car entries) (h3-generate-selected-entries (cdr entries) needed)))
        (t (h3-generate-selected-entries (cdr entries) needed))))

(defun h3-generate-total-step-count (entries total)
  (if (endp entries)
      total
    (h3-generate-total-step-count
     (cdr entries) (+ total (h3-generate-count-steps (caddar entries) 0)))))

(defun h3-generate-entry-texts (entries)
  (if (endp entries)
      nil
    (cons (cadddr (car entries)) (h3-generate-entry-texts (cdr entries)))))

(defun h3-generate-serialize-theorem (library name result)
  (let* ((entries (library-library-entries library))
         (index (h3-generate-entry-index entries nil)))
    (proof-with-checked-results
     ((fact-lines (h3-generate-fact-lines index nil))
      (theorem (proof-proof-entry "theorem" name (list name) (list result)))
      (needed (h3-generate-serialize-theorem-visit 1000000 theorem index fact-lines nil)))
     (let* ((selected (append (h3-generate-selected-entries entries needed) (list theorem)))
            (total (h3-generate-total-step-count selected 0)))
       (list total (text-join "" (h3-generate-entry-texts selected)))))))

(defun h3-generate-quote-input (contents)
  (concatenate 'string "(COMMON-LISP::QUOTE \"" (reader-escape contents 34) "\")"))
