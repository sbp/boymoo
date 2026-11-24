(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *worklist-nil* '("sym" "COMMON-LISP" "NIL"))
(defconst *worklist-quote* '("sym" "COMMON-LISP" "QUOTE"))
(defconst *worklist-return-last* '("sym" "ACL2" "RETURN-LAST"))
(defconst *worklist-mbe* (list *worklist-quote* '("sym" "ACL2" "MBE1-RAW")))

(defun worklist-statement (kind obligation names package)
  (list kind obligation names package))

(defun worklist-statement-kind (statement)
  (first statement))

(defun worklist-statement-obligation (statement)
  (second statement))

(defun worklist-statement-names (statement)
  (third statement))

(defun worklist-statement-package (statement)
  (fourth statement))

(defun worklist-name-text (symbol)
  (reader-write symbol))

(defun worklist-list-datum-p (datum)
  (and (consp datum) (not (stringp (car datum)))))

(mutual-recursion
 (defun worklist-recursive-term (term names)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (let ((head (car term)))
     (cond
      ((or (not (worklist-list-datum-p term)) (equal head *worklist-quote*)) nil)
      ((worklist-list-datum-p head)
       (if (consp (cddr head))
           (or (worklist-recursive-terms (cdr term) names)
               (worklist-recursive-term (caddr head) names))
         '(:failure "failure" "")))
      ((member-equal head names) t)
      ((and (equal head *worklist-return-last*) (equal (len term) 4)
            (equal (cadr term) *worklist-mbe*))
       (worklist-recursive-term (cadddr term) names))
      (t (worklist-recursive-terms (cdr term) names)))))
 (defun worklist-recursive-terms (terms names)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (and (consp terms)
        (or (worklist-recursive-terms (cdr terms) names)
            (worklist-recursive-term (car terms) names)))))

(defun worklist-definition-bodies (definitions)
  (if (endp definitions)
      nil
    (let ((definition (car definitions)))
      (if (consp (cddr definition))
          (let ((bodies (worklist-definition-bodies (cdr definitions))))
            (if (failure-p bodies) bodies (cons (caddr definition) bodies)))
        '(:failure "failure" "")))))

(defun worklist-definition-symbols (definitions)
  (if (endp definitions)
      nil
    (let* ((definition (car definitions))
           (name (car definition)))
      (if (or (not (consp definition)) (worklist-list-datum-p name))
          '(:failure "failure" "")
        (let ((names (worklist-definition-symbols (cdr definitions))))
          (if (failure-p names) names (cons name names)))))))

(defun worklist-recursive (definitions)
  (let ((names (worklist-definition-symbols definitions)))
    (if (failure-p names)
        names
      (let ((bodies (worklist-definition-bodies definitions)))
        (if (failure-p bodies) bodies (worklist-recursive-terms bodies names))))))

(defun worklist-statement-word (line)
  (let ((space (text-find line " ")))
    (seq-slice line 1 (if (< space 0) :none space))))

(defun worklist-statement-leading-datum (kind line)
  (let ((reader (reader-reader-take (reader-reader line)
                                   (text-join "" (list "(" kind " ")))))
    (if (failure-p reader)
        reader
      (let ((parsed (reader-reader-datum reader)))
        (if (failure-p parsed) parsed (car parsed))))))

(defun worklist-statement-arguments (line)
  (let* ((newline (string (code-char 10)))
         (text (if (text-ends-with line newline) (seq-slice line 0 -1) line))
         (parsed (reader-reader-line (reader-reader text))))
    (if (failure-p parsed) parsed (cadar parsed))))

(defun worklist-declared-names (rows)
  (cond
   ((integerp rows) '(:failure "failure" ""))
   ((endp rows) nil)
   ((not (worklist-list-datum-p (car rows))) '(:failure "failure" ""))
   (t (let ((name (worklist-name-text (caar rows))))
        (if (failure-p name)
            name
          (let ((names (worklist-declared-names (cdr rows))))
            (if (failure-p names) names (cons name names))))))))

(defun worklist-defined-statement (kind definitions)
  (let ((names (worklist-declared-names definitions)))
    (if (failure-p names)
        names
      (let ((recursivep (worklist-recursive definitions)))
        (if (failure-p recursivep)
            recursivep
          (worklist-statement kind (and recursivep (car names)) names nil))))))

(defun worklist-constrained-statement (kind args)
  (if (not (equal (len args) 2))
      '(:failure "failure" "")
    (let* ((functions (first args))
           (formulas (second args))
           (names (worklist-declared-names functions)))
      (cond ((failure-p names) names)
            ((equal formulas *worklist-nil*) (worklist-statement kind nil names nil))
            ((endp names) '(:failure "failure" ""))
            (t (let ((facts (worklist-declared-names formulas)))
                 (if (failure-p facts)
                     facts
                   (worklist-statement kind (car names) (append names facts) nil))))))))

(defun worklist-statement-info (line)
  (let ((kind (worklist-statement-word line)))
    (cond
     ((member-equal kind '("theorem" "axiom" "choose" "reserve"))
      (let ((datum (worklist-statement-leading-datum kind line)))
        (if (failure-p datum)
            datum
          (let ((name (worklist-name-text datum)))
            (if (failure-p name)
                name
              (worklist-statement kind (and (equal kind "theorem") name)
                                  (list name) nil))))))
     ((member-equal kind '("package" "hidden-package"))
      (let ((datum (worklist-statement-leading-datum kind line)))
        (cond ((failure-p datum) datum)
              ((not (consp (cdr datum))) '(:failure "failure" ""))
              (t (worklist-statement kind nil nil (cadr datum))))))
     ((or (equal kind "define") (equal kind "constrain"))
      (let ((args (worklist-statement-arguments line)))
        (cond ((failure-p args) args)
              ((equal kind "define") (worklist-defined-statement kind (cdr args)))
              (t (worklist-constrained-statement kind args)))))
     (t (worklist-statement kind nil nil nil)))))
