(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-reference-plan* (proof-sym "PLAN" "ACL2"))
(defconst *l1-reference-lines* (proof-sym "LINES" "ACL2"))
(defconst *l1-reference-previous* (proof-sym "PREVIOUS" "ACL2"))
(defconst *l1-reference-current* (proof-sym "CURRENT" "ACL2"))
(defconst *l1-reference-n* (proof-sym "N" "ACL2"))
(defconst *l1-reference-tail* (proof-sym "TAIL" "ACL2"))
(defconst *l1-reference-ground* (proof-sym "GROUND" "ACL2"))
(defconst *l1-reference-library* (proof-sym "LIBRARY" "ACL2"))
(defconst *l1-reference-statements* (proof-sym "STATEMENTS" "ACL2"))
(defconst *l1-reference-w* (proof-sym "W" "ACL2"))
(defconst *l1-reference-drop* (proof-sym "L1-REFERENCE-DROP" "ACL2"))
(defconst *l1-reference-decode* (proof-sym "L1-REFERENCE-DECODE" "ACL2"))
(defconst *l1-reference-verdict* (proof-sym "L1-REFERENCE-VERDICT" "ACL2"))
(defconst *l1-reference-check* (proof-sym "L1-REFERENCE-CHECK" "ACL2"))
(defconst *l1-reference-lambda* (proof-cl "LAMBDA"))
(defconst *l1-reference-coerce* (proof-cl "COERCE"))
(defconst *l1-reference-stringp* (proof-cl "STRINGP"))
(defconst *l1-reference-list* (proof-quote (proof-cl "LIST")))
(defconst *l1-reference-string-empty* (proof-quote '("str" "")))

(defun l1-reference-boymoo (name)
  (proof-sym name "BOYMOO"))

(defund l1-reference-definition-line (group)
  (proof-line "define" (list *proof-nil* group)))

(defun l1-reference-definition-lines (groups)
  (if (endp groups)
      nil
    (proof-with-checked-results
        ((line (l1-reference-definition-line (car groups)))
         (rest (l1-reference-definition-lines (cdr groups))))
      (cons line rest))))

(defun l1-reference-program ()
  (let* ((drop (proof-ite (list *proof-less* *proof-zero* *l1-reference-n*)
                          (list *l1-reference-drop*
                                (library-plus *proof-neg-one* *l1-reference-n*)
                                (list *library-cdr* *l1-reference-tail*))
                          *l1-reference-tail*))
         (row (list *library-car* *l1-reference-plan*))
         (count (list *library-car* row))
         (text (list *library-car* (list *library-cdr* row)))
         (join (list (l1-reference-boymoo "APP")
                     (list *l1-reference-coerce* text *l1-reference-list*)
                     (proof-ite (list *proof-less* count *proof-zero*) *proof-false*
                                (list *l1-reference-drop* count *l1-reference-previous*))))
         (push (list *l1-reference-decode* (list *library-cdr* *l1-reference-plan*)
                     (list *proof-cons* *l1-reference-current* *l1-reference-lines*)
                     *l1-reference-current*))
         (restore (list (list *l1-reference-lambda*
                              (list *l1-reference-current* *l1-reference-plan* *l1-reference-lines*)
                              push)
                        join *l1-reference-plan* *l1-reference-lines*))
         (plain (list *l1-reference-decode* (list *library-cdr* *l1-reference-plan*)
                      (list *proof-cons* (list *l1-reference-coerce* row *l1-reference-list*)
                            *l1-reference-lines*)
                      *l1-reference-previous*))
         (decode (proof-ite (list *proof-consp* *l1-reference-plan*)
                            (proof-ite (list *l1-reference-stringp* row) plain restore)
                            *l1-reference-lines*))
         (bad (list (l1-reference-boymoo "REJECTED-P") *l1-reference-w*))
         (reject (list (l1-reference-boymoo "REJECTION-VERDICT") *l1-reference-w*))
         (verdict (proof-ite bad reject
                             (list *proof-cons*
                                   (list (l1-reference-boymoo "VERDICT") *l1-reference-w*)
                                   (list *proof-cons* *l1-reference-string-empty* *proof-false*))))
         (ground (list (l1-reference-boymoo "LOAD-GROUND")
                       (list (l1-reference-boymoo "LINES-OF") *l1-reference-ground*)
                       (list (l1-reference-boymoo "INITIAL-WORLD"))))
         (library (list (l1-reference-boymoo "CHECK-LIBRARY")
                        (list (l1-reference-boymoo "LINES-OF") *l1-reference-library*)
                        *proof-zero* *l1-reference-ground*))
         (check (list *l1-reference-verdict*
                      (list (l1-reference-boymoo "RUN")
                            (list (l1-reference-boymoo "LINES-OF") *l1-reference-statements*)
                            *proof-zero*
                            (list *l1-reference-decode* *l1-reference-plan* *proof-false* *proof-false*)
                            *proof-zero* *proof-false* *l1-reference-w*)))
         (check-library (list (list *l1-reference-lambda*
                                    (list *l1-reference-w* *l1-reference-statements* *l1-reference-plan*)
                                    (proof-ite bad reject check))
                              library *l1-reference-statements* *l1-reference-plan*))
         (bad-ground (proof-quote '(("str" "the ground theory could not be read") ("str" ""))))
         (load (proof-ite (proof-eq *l1-reference-ground* (proof-quote (proof-sym "BAD" "KEYWORD")))
                          bad-ground check-library))
         (start (list (list *l1-reference-lambda*
                            (list *l1-reference-ground* *l1-reference-library*
                                  *l1-reference-statements* *l1-reference-plan*)
                            load)
                      ground *l1-reference-library* *l1-reference-statements* *l1-reference-plan*))
         (groups (list (list *l1-reference-drop* (list *l1-reference-n* *l1-reference-tail*) drop)
                       (list *l1-reference-decode*
                             (list *l1-reference-plan* *l1-reference-lines* *l1-reference-previous*)
                             decode)
                       (list *l1-reference-verdict* (list *l1-reference-w*) verdict)
                       (list *l1-reference-check*
                             (list *l1-reference-ground* *l1-reference-library*
                                   *l1-reference-statements* *l1-reference-plan*)
                             start))))
    (proof-with-checked-results ((lines (l1-reference-definition-lines groups)))
      (text-join "" lines))))

(defun l1-reference-suffix-length-search (n line-bytes previous low high)
  (declare (xargs :measure (nfix n)))
  (cond ((>= low high) low)
        ((zp n) '(:failure "Fuel" "l1-reference-suffix-length-search"))
        (t (let ((middle (floor (+ low high 1) 2)))
             (if (text-ends-with line-bytes (seq-slice previous (- middle) :none))
                 (l1-reference-suffix-length-search (1- n) line-bytes previous middle high)
               (l1-reference-suffix-length-search (1- n) line-bytes previous low (1- middle)))))))

(defund l1-reference-suffix-length (line-bytes previous)
  (l1-reference-suffix-length-search 1000000 line-bytes previous
                                     0 (min (length line-bytes) (length previous))))

(defun l1-reference-complete-lines (parts newline)
  (cond ((endp parts) nil)
        ((endp (cdr parts)) (and (not (equal (car parts) "")) (list (car parts))))
        (t (cons (string-append (car parts) newline)
                 (l1-reference-complete-lines (cdr parts) newline)))))

(defun l1-reference-encode-rows (rows previous)
  (if (endp rows)
      nil
    (let ((row (car rows)))
      (if (and (<= 1024 (length row)) (text-starts-with row "(compute (COMMON-LISP::CONS "))
          (proof-with-checked-results
              ((suffix (l1-reference-suffix-length row previous))
               (drop (if (= suffix 0) -1 (- (length previous) suffix)))
               (prefix (seq-slice row 0 (- (length row) suffix)))
               (rest (l1-reference-encode-rows (cdr rows) row)))
            (cons (list drop (list "str" prefix)) rest))
        (proof-with-checked-results ((rest (l1-reference-encode-rows (cdr rows) previous)))
          (cons (list "str" row) rest))))))

(defun l1-reference-encoded-lines (source)
  (if (equal source "")
      (proof-write *proof-false*)
    (proof-with-checked-results
        ((newline (coerce (list #\Newline) 'string))
         (parts (text-split source newline))
         (rows (reverse (l1-reference-complete-lines parts newline)))
         (items (l1-reference-encode-rows rows "")))
      (proof-write (proof-quote items)))))
