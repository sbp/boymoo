(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t4-bookrun-proof-heads* '("define" "lemma" "measure" "theorem" "witness" "skip"))

(defun t4-bookrun-make-entry (name source steps reason)
  (list :entry name source steps reason))

(defun t4-bookrun-entry-name (entry)
  (cadr entry))

(defun t4-bookrun-entry-source (entry)
  (caddr entry))

(defun t4-bookrun-entry-steps (entry)
  (cadddr entry))

(defun t4-bookrun-entry-reason (entry)
  (car (cddddr entry)))

(defun t4-bookrun-skipped (name reason)
  (proof-with-checked-results
   ((source (proof-line "skip" (list name))))
   (t4-bookrun-make-entry name source 0 reason)))

(defun t4-bookrun-definition-names (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((name (proof-term-at (car definitions) 0))
      (rest (t4-bookrun-definition-names (cdr definitions))))
     (cons name rest))))

(defun t4-bookrun-subst-actuals (args env)
  (if (endp args)
      nil
    (proof-with-checked-results
     ((actual (proof-subst (car args) env))
      (rest (t4-bookrun-subst-actuals (cdr args) env)))
     (cons actual rest))))

(defun t4-bookrun-lambda-bindings (formals args env bindings)
  (if (or (endp formals) (endp args))
      bindings
    (proof-with-checked-results
     ((actual (proof-subst (car args) env)))
     (t4-bookrun-lambda-bindings
      (cdr formals) (cdr args) env
      (table-put bindings (car formals) actual)))))

(defun t4-bookrun-extends (rulers name)
  (or (equal rulers *termination-all*)
      (and (proof-compound rulers) (member-equal name rulers))))

(mutual-recursion
 (defun t4-bookrun-first-call-in-term (term env ruled rulers names)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (proof-compound term)) nil)
    ((endp term) '(:failure "failure" ""))
    ((equal (car term) *proof-quote*) nil)
    (t
     (let ((head (car term))
           (args (cdr term)))
       (cond
        ((proof-compound head)
         (proof-with-checked-results
          ((lambda-fields (proof-list-of-length head 3))
           (actual-call
            (t4-bookrun-first-call-in-args
             args env (and ruled (t4-bookrun-extends rulers *termination-lambdas*))
             rulers names)))
          (or actual-call
              (proof-with-checked-results
               ((bindings (t4-bookrun-lambda-bindings (cadr lambda-fields) args env nil)))
               (t4-bookrun-first-call-in-term
                (caddar term) bindings ruled rulers names)))))
        ((and (equal head *termination-return-last*) (endp args))
         '(:failure "failure" ""))
        ((and (equal head *termination-return-last*) (equal (car args) *termination-mbe*))
         (if (consp (cddr args))
             (t4-bookrun-first-call-in-term (caddr args) env ruled rulers names)
           '(:failure "failure" "")))
        ((and (equal head *proof-if*) ruled)
         (proof-with-checked-results
          ((if-fields (proof-list-of-length args 3))
           (test-call
            (t4-bookrun-first-call-in-term
             (cadr term) env (t4-bookrun-extends rulers *proof-if*) rulers names)))
          (or test-call
              (proof-with-checked-results
               ((literal (proof-subst (cadr term) env)))
               (let ((yes-call (t4-bookrun-first-call-in-term
                                (caddr term) env t rulers names)))
                 (or yes-call
                     (t4-bookrun-first-call-in-term
                      (cadddr term) env t rulers names)))))))
        ((member-equal head names)
         (proof-with-checked-results
          ((actuals (t4-bookrun-subst-actuals args env)))
          t))
        (t
         (t4-bookrun-first-call-in-args
          args env (and ruled (t4-bookrun-extends rulers head)) rulers names)))))))
 (defun t4-bookrun-first-call-in-args (args env ruled rulers names)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (let ((found (t4-bookrun-first-call-in-term (car args) env ruled rulers names)))
       (or found
           (t4-bookrun-first-call-in-args (cdr args) env ruled rulers names))))))

(defun t4-bookrun-first-call (definitions rulers names)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3)))
     (let ((found (t4-bookrun-first-call-in-term (caddr definition) nil t rulers names)))
       (or found
           (t4-bookrun-first-call (cdr definitions) rulers names))))))

(defun t4-bookrun-obligation (kind data)
  (cond
   ((equal kind "theorem") (proof-term-at data 0))
   ((equal kind "define")
    (proof-with-checked-results
     ((rulers (proof-term-at data 0))
      (names (t4-bookrun-definition-names (cdr data)))
      (recursive (t4-bookrun-first-call (cdr data) rulers names)))
     (and recursive (car names))))
   ((equal kind "constrain")
    (proof-with-checked-results
     ((formulas (proof-term-at data 1)))
     (if (proof-compound formulas)
         (proof-with-checked-results
          ((functions (proof-term-at data 0))
           (function (proof-term-at functions 0)))
          (proof-term-at function 0))
       nil)))
   (t nil)))

(defun t4-bookrun-byte-lines (chars keepend reversed)
  (declare (xargs :measure (acl2-count chars)))
  (cond
   ((endp chars)
    (and reversed (list (coerce (reverse reversed) 'string))))
   ((equal (char-code (car chars)) 10)
    (cons (coerce (reverse (if keepend (cons (car chars) reversed) reversed)) 'string)
          (t4-bookrun-byte-lines (cdr chars) keepend nil)))
   ((equal (char-code (car chars)) 13)
    (if (and (consp (cdr chars)) (equal (char-code (cadr chars)) 10))
        (cons (coerce (reverse (if keepend (list* (cadr chars) (car chars) reversed)
                                 reversed)) 'string)
              (t4-bookrun-byte-lines (cddr chars) keepend nil))
      (cons (coerce (reverse (if keepend (cons (car chars) reversed) reversed)) 'string)
            (t4-bookrun-byte-lines (cdr chars) keepend nil))))
   (t
    (t4-bookrun-byte-lines (cdr chars) keepend (cons (car chars) reversed)))))

(defun t4-bookrun-splitlines (source keepend)
  (t4-bookrun-byte-lines (coerce source 'list) keepend nil))

(defun t4-bookrun-byte-whitespace (char)
  (member-equal (char-code char) '(9 10 11 12 13 32)))

(defun t4-bookrun-word-chars (chars)
  (if (or (endp chars) (t4-bookrun-byte-whitespace (car chars)))
      nil
    (cons (car chars) (t4-bookrun-word-chars (cdr chars)))))

(defun t4-bookrun-first-word (chars)
  (cond
   ((endp chars) '(:failure "failure" ""))
   ((t4-bookrun-byte-whitespace (car chars))
    (t4-bookrun-first-word (cdr chars)))
   (t (coerce (t4-bookrun-word-chars chars) 'string))))

(defun t4-bookrun-sections-in (lines current reversed)
  (if (endp lines)
      (list (reverse (if current (cons (reverse current) reversed) reversed)) nil)
    (let* ((raw (car lines))
           (word (t4-bookrun-first-word (cdr (coerce raw 'list)))))
      (cond
       ((failure-p word) (list (reverse reversed) word))
       ((and (member-equal word *t4-bookrun-proof-heads*) current)
        (t4-bookrun-sections-in (cdr lines) (list raw) (cons (reverse current) reversed)))
       (t (t4-bookrun-sections-in (cdr lines) (cons raw current) reversed))))))

(defun t4-bookrun-section-scan (source)
  (t4-bookrun-sections-in (t4-bookrun-splitlines source t) nil nil))

(defun t4-bookrun-sections (source)
  (let ((scan (t4-bookrun-section-scan source)))
    (or (cadr scan) (car scan))))

(defun t4-bookrun-read-line (raw)
  (proof-with-checked-results
   ((parsed (reader-reader-line (reader-reader raw))))
   (list (caar parsed) (proof-freeze (cadar parsed)))))

(defun t4-bookrun-declaration-name (kind data)
  (if (equal kind "define")
      (proof-with-checked-results
       ((definition (proof-term-at data 1)))
       (proof-term-at definition 0))
    (proof-term-at data 0)))

(defun t4-bookrun-count-line (line lines)
  (if (endp lines)
      0
    (+ (if (equal line (car lines)) 1 0)
       (t4-bookrun-count-line line (cdr lines)))))

(defun t4-bookrun-assemble-sections (blocks declarations chunks steps size offset)
  (if (endp blocks)
      (list declarations chunks steps size offset)
    (let* ((block (car blocks))
           (head (car block)))
      (proof-with-checked-results
       ((parsed (t4-bookrun-read-line (seq-slice head 0 -1)))
        (name (and (member-equal (car parsed) '("define" "lemma"))
                   (t4-bookrun-declaration-name (car parsed) (cadr parsed)))))
       (let* ((declaration (member-equal (car parsed) '("define" "lemma")))
              (prior (and declaration (assoc-equal name declarations))))
         (cond
          ((and prior (equal (cdr prior) head))
           (t4-bookrun-assemble-sections (cdr blocks) declarations chunks steps size offset))
          (prior
           (proof-with-checked-results
            ((written (proof-write name)))
            '(:failure "failure" "")))
          (t
           (let* ((contents (text-join "" block))
                  (lines (len block))
                  (qeds (t4-bookrun-count-line (proof-line "qed" nil) block)))
             (t4-bookrun-assemble-sections
              (cdr blocks) (if declaration (table-put declarations name head) declarations)
              (cons contents chunks) (+ steps (- (- lines 1) qeds)) (+ size (length contents))
              (+ offset lines))))))))))

(defun t4-bookrun-assemble-entries (entries declarations chunks offsets offset)
  (if (endp entries)
      (list (text-join "" (reverse chunks)) (reverse offsets))
    (let ((scan (t4-bookrun-section-scan (t4-bookrun-entry-source (car entries)))))
      (proof-with-checked-results
       ((assembled (t4-bookrun-assemble-sections (car scan) declarations chunks 0 0 offset)))
       (let ((end (car (cddddr assembled))))
         (or (cadr scan)
             (t4-bookrun-assemble-entries
              (cdr entries) (car assembled) (cadr assembled)
              (cons (list offset end (caddr assembled) (cadddr assembled)) offsets) end)))))))

(defun t4-bookrun-assemble (entries)
  (t4-bookrun-assemble-entries entries nil nil nil 0))

(defun t4-bookrun-proof-dependencies-in (lines facts names)
  (cond
   ((endp lines) names)
   ((text-starts-with (car lines) "(fact ")
    (proof-with-checked-results
     ((parsed (t4-bookrun-read-line (car lines)))
      (name (proof-term-at (cadr parsed) 0)))
     (let ((fact (assoc-equal name facts)))
       (t4-bookrun-proof-dependencies-in
        (cdr lines) facts (if fact (table-put names name (cdr fact)) names)))))
   (t
    (t4-bookrun-proof-dependencies-in (cdr lines) facts names))))

(defun t4-bookrun-proof-dependencies (source facts)
  (t4-bookrun-proof-dependencies-in (t4-bookrun-splitlines source nil) facts nil))

(mutual-recursion
 (defun t4-bookrun-enabled-functions (hints)
   (declare (xargs :measure (acl2-count hints)))
   (cond
    ((or (not (proof-compound hints)) (endp hints)) nil)
    ((equal (car hints) (proof-sym "ENABLE" "ACL2")) (cdr hints))
    (t (append (t4-bookrun-enabled-functions (car hints))
               (t4-bookrun-enabled-functions-in (cdr hints))))))
 (defun t4-bookrun-enabled-functions-in (children)
   (declare (xargs :measure (acl2-count children)))
   (if (endp children)
       nil
     (append (t4-bookrun-enabled-functions (car children))
             (t4-bookrun-enabled-functions-in (cdr children))))))

(defun t4-bookrun-witness-suffix (raw)
  (text-upper (seq-slice (siphash-hexdigest raw) 0 12)))

(defun t4-bookrun-suffix-witness-names (source raw)
  (let* ((suffix (concatenate 'string "-" (t4-bookrun-witness-suffix raw)))
         (counterexample "ACL2::T4-COUNTEREXAMPLE")
         (predicate "ACL2::T4-CHOSEN-PREDICATE"))
    (text-replace
     (text-replace source counterexample (concatenate 'string counterexample suffix))
     predicate (concatenate 'string predicate suffix))))

(defun t4-bookrun-failed-reason (kind)
  (cond ((equal kind "theorem") "needs a theorem proof")
        ((equal kind "define") "needs a measure proof")
        ((equal kind "constrain") "needs a witness")
        (t '(:failure "failure" ""))))

(defun t4-bookrun-book-entry (name kind raw generated evaluator simple)
  (cond
   ((not (failure-p generated))
    (let ((source (cadr generated)))
      (t4-bookrun-make-entry
       name (if (equal kind "constrain") (t4-bookrun-suffix-witness-names source raw) source)
       (car generated) "")))
   ((and (equal kind "constrain") (equal (cadr generated) "Unproved"))
    (let ((candidate (or evaluator simple)))
      (cond ((failure-p candidate) candidate)
            (candidate (t4-bookrun-make-entry name (cadr candidate) (car candidate) ""))
            (t (t4-bookrun-skipped name "needs a constructive witness")))))
   ((member-equal (cadr generated)
                  '("Unproved" "SearchMiss" "InferenceMismatch" "MissingProofInput"
                    "value" "assertion" "key" "recursion"))
    (proof-with-checked-results
     ((reason (t4-bookrun-failed-reason kind)))
     (t4-bookrun-skipped name reason)))
   (t generated)))
