(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

; Consume a sorted list of raw-line and parse pairs, returning the tree and
; the unused tail.
(defun b1-open-line-tree (size lines)
  (declare (xargs :measure (nfix size)))
  (if (zp size)
      (cons nil lines)
    (let* ((left-size (floor size 2))
           (right-size (- (1- size) left-size)))
      (if (or (not (< left-size size)) (not (< right-size size)))
          (cons nil lines)
        (let* ((left (b1-open-line-tree left-size lines))
               (rest (cdr left))
               (right (b1-open-line-tree right-size (cdr rest))))
          (cons (list (car rest) (car left) (car right)) (cdr right)))))))

(defun b1-open-line-lookup (raw tree)
  (cond ((endp tree) nil)
        ((equal raw (caar tree)) (car tree))
        ((string< raw (caar tree)) (b1-open-line-lookup raw (cadr tree)))
        (t (b1-open-line-lookup raw (caddr tree)))))

(defun b1-open-make-session (given library-lines prefixes measures history statement)
  (list :b1-session given library-lines prefixes measures history statement))

(defun b1-open-given (session)
  (cadr session))

(defun b1-open-library-lines (session)
  (caddr session))

(defun b1-open-prefixes (session)
  (cadddr session))

(defun b1-open-measures (session)
  (nth 4 session))

(defun b1-open-history (session)
  (nth 5 session))

(defun b1-open-statement (session)
  (nth 6 session))

(defun b1-open-parse-line (raw previous-line previous-statement)
  (cond ((and previous-line (equal raw (car previous-line))) (cdr previous-line))
        ((and previous-statement (equal raw (car previous-statement))) (cdr previous-statement))
        (t (b1-api-parse raw))))

(defun b1-open-context-add-line (line library-lines previous-line previous-statement updated)
  (proof-with-checked-results ((raw (b1-api-raw line)))
    (let ((seen (car updated)))
      (if (or (b1-open-line-lookup raw library-lines) (member-equal raw seen))
          (cons updated nil)
        (proof-with-checked-results
         ((fields (b1-open-parse-line raw previous-line previous-statement))
          (result (b1-api-context-add-statement (car fields) (cadr fields)
                                               (cadr updated) (caddr updated)
                                               (cadddr updated) (nth 4 updated))))
         (cons (cons (cons raw seen) result) (cons raw fields)))))))

; The second part of the result has one parse or an empty slot per line.
(defun b1-open-context-add-lines (lines library-lines previous previous-statement updated parsed)
  (if (endp lines)
      (cons updated (reverse parsed))
    (proof-with-checked-results
     ((result (b1-open-context-add-line (car lines) library-lines
                                        (car previous) previous-statement updated)))
     (b1-open-context-add-lines (cdr lines) library-lines (cdr previous) previous-statement
                                (car result) (cons (cdr result) parsed)))))

(defun b1-open-context-extend (context lines library-lines previous previous-statement)
  (if (endp lines)
      (cons context nil)
    (let ((inputs (list (b1-api-context-seen context)
                        (b1-api-context-world context)
                        (b1-api-context-formulas context)
                        (b1-api-context-names context)
                        nil)))
      (proof-with-checked-results
       ((admitted (b1-open-context-add-lines lines library-lines previous previous-statement inputs nil))
        (extended (b1-api-context-finish context (car admitted))))
       (cons extended (cdr admitted))))))

(defun b1-open-prepare-library (library)
  (if (or (true-listp library) (equal library ""))
      (proof-with-checked-results ((ground (b1-api-ground)))
        (b1-open-context-extend ground library nil nil nil))
    '(:failure "failure" "")))

(defun b1-api-open (library)
  (let ((prepared (b1-open-prepare-library library)))
    (if (failure-p prepared)
        (b1-open-make-session prepared nil nil nil nil nil)
      (let* ((context (car prepared))
             (sorted (acl2::merge-sort-lexorder (remove-equal nil (cdr prepared))))
             (tree (car (b1-open-line-tree (len sorted) sorted)))
             (given (b1-api-make-context (b1-api-context-world context) nil
                                         (b1-api-context-formulas context)
                                         (b1-api-context-facts context)
                                         (b1-api-context-names context))))
        (b1-open-make-session given tree nil nil nil nil)))))

(defun b1-open-cache-record (key value cache size)
  (if (and (consp cache) (equal key (caar cache)))
      cache
    (let ((others (remove-assoc-equal key cache)))
      (cons (cons key value) (take (min (1- size) (len others)) others)))))

; Each prefix is admitted as one group. Its fact index has a single
; addition per name, even if the name occurs on several distinct lines.
(defun b1-open-context-for (session earlier)
  (let* ((given (b1-open-given session))
         (library-lines (b1-open-library-lines session))
         (prefixes (b1-open-prefixes session))
         (history (b1-open-history session))
         (statement (b1-open-statement session))
         (boundary (* 64 (floor (len earlier) 64)))
         (lines (take boundary earlier))
         (hit (assoc-equal lines prefixes))
         (same-boundary (equal boundary (car history)))
         (previous (if (and hit same-boundary) nil (append (cadr history) (caddr history))))
         (prefix (if hit (cdr hit)
                   (b1-open-context-extend given lines library-lines previous statement))))
    (if (failure-p prefix)
        (cons prefix session)
      (let* ((suffix (nthcdr boundary earlier))
             (previous-suffix (if same-boundary (caddr history) (nthcdr boundary previous)))
             (extended (b1-open-context-extend (car prefix) suffix library-lines
                                                previous-suffix statement))
             (prefixes (if lines (b1-open-cache-record lines prefix prefixes 16) prefixes))
             (failed (failure-p extended))
             (history (if failed history (list boundary (cdr prefix) (cdr extended)))))
        (cons (if failed extended (car extended))
              (b1-open-make-session given library-lines prefixes (b1-open-measures session)
                                    history statement))))))

(defun b1-open-prove-prepared (session context parsed obligation aids)
  (let* ((word (car parsed))
         (definition (equal word "define"))
         (cache (b1-open-measures session))
         (hit (and definition (assoc-equal aids cache)))
         (measures (cond (hit (cdr hit))
                         (definition (b1-api-measures aids))
                         (t nil))))
    (if (failure-p measures)
        (cons nil session)
      (let* ((answer (b1-api-prove-prepared context word (cadr parsed)
                                            (car obligation) (cadr obligation) measures))
             (cache (if definition (b1-open-cache-record aids measures cache 12) cache)))
        (cons (if (failure-p answer) nil answer)
              (b1-open-make-session (b1-open-given session) (b1-open-library-lines session)
                                    (b1-open-prefixes session) cache
                                    (b1-open-history session) (b1-open-statement session)))))))

(defun b1-open-prove (session raw parsed earlier aids library-line)
  (let ((obligation (b1-generate-obligations (car parsed) (cadr parsed))))
    (if (or (failure-p obligation)
            (not (car obligation))
            (failure-p (b1-open-given session))
            (not (or (true-listp earlier) (equal earlier ""))))
        (cons nil session)
      (let* ((prepared (b1-open-context-for session earlier))
             (context (car prepared))
             (session (cdr prepared)))
        (if (or (failure-p context)
                library-line
                (member-equal raw (b1-api-context-seen context)))
            (cons nil session)
          (b1-open-prove-prepared session context parsed obligation aids))))))

(defun b1-api-prove-open (session statement earlier aids)
  (let ((raw (b1-api-raw statement)))
    (if (failure-p raw)
        (cons nil session)
      (let* ((library-line (b1-open-line-lookup raw (b1-open-library-lines session)))
             (parsed (b1-open-parse-line raw library-line (b1-open-statement session))))
        (if (failure-p parsed)
            (cons nil session)
          (let* ((result (b1-open-prove session raw parsed earlier aids library-line))
                 (session (cdr result)))
            (cons (car result)
                  (b1-open-make-session (b1-open-given session) (b1-open-library-lines session)
                                        (b1-open-prefixes session) (b1-open-measures session)
                                        (b1-open-history session) (cons raw parsed)))))))))

(defun b1-open-prove-all-reversed (session cases answers)
  (if (endp cases)
      answers
    (let* ((case (car cases))
           (result (b1-api-prove-open session (car case) (cadr case) (caddr case))))
      (b1-open-prove-all-reversed (cdr result) (cdr cases) (cons (car result) answers)))))

(defun b1-api-prove-all-loop (session cases)
  (reverse (b1-open-prove-all-reversed session cases nil)))

(defun b1-api-prove-all (library cases)
  (b1-api-prove-all-loop (b1-api-open library) cases))
