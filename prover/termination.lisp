(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *termination-all* '("sym" "KEYWORD" "ALL"))
(defconst *termination-lambdas* '("sym" "KEYWORD" "LAMBDAS"))
(defconst *termination-return-last* '("sym" "ACL2" "RETURN-LAST"))
(defconst *termination-mbe* '(("sym" "COMMON-LISP" "QUOTE") ("sym" "ACL2" "MBE1-RAW")))
(defconst *termination-selectors* '(("sym" "COMMON-LISP" "CAR") ("sym" "COMMON-LISP" "CDR")))

(defun termination-make-call (caller callee actuals tests)
  (list caller callee actuals tests))

(defun termination-call-caller (call)
  (car call))

(defun termination-call-callee (call)
  (cadr call))

(defun termination-call-actuals (call)
  (caddr call))

(defun termination-call-tests (call)
  (cadddr call))

(defconst *termination-index-error* '(:failure "index" ""))

(defmacro termination-bind (name expr body)
  `(let ((,name ,expr))
     (if (failure-p ,name) ,name ,body)))

(mutual-recursion
 (defun termination-logical-body (term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (proof-compound term)) term)
    ((endp term) *termination-index-error*)
    ((equal (car term) *proof-quote*) term)
    ((and (equal (car term) *termination-return-last*) (endp (cdr term)))
     *termination-index-error*)
    ((and (equal (car term) *termination-return-last*)
          (equal (cadr term) *termination-mbe*))
     (if (consp (cdddr term))
         (termination-logical-body (cadddr term))
       *termination-index-error*))
    ((proof-compound (car term))
     (if (consp (cddar term))
         (termination-bind body (termination-logical-body (caddar term))
           (termination-bind actuals (termination-logical-body-args (cdr term))
             (cons (list (caar term) (cadar term) body) actuals)))
       *termination-index-error*))
    (t
     (termination-bind actuals (termination-logical-body-args (cdr term))
       (cons (car term) actuals)))))
 (defun termination-logical-body-args (args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (termination-bind first (termination-logical-body (car args))
       (termination-bind rest (termination-logical-body-args (cdr args))
         (cons first rest))))))

(defun termination-recursive-calls-extends (name rulers)
  (or (equal rulers *termination-all*)
      (and (proof-compound rulers) (if (member-equal name rulers) t nil))))

(defun termination-subst-actuals (args env)
  (if (endp args)
      nil
    (termination-bind actual (proof-subst (car args) env)
      (termination-bind rest (termination-subst-actuals (cdr args) env)
        (cons actual rest)))))

(defun termination-lambda-bindings (formals args env bindings)
  (if (or (endp formals) (endp args))
      bindings
    (termination-bind actual (proof-subst (car args) env)
      (termination-lambda-bindings (cdr formals) (cdr args) env
                                   (table-put bindings (car formals) actual)))))

(mutual-recursion
 (defun termination-recursive-calls-walk (caller term tests env ruled rulers names)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (proof-compound term)) nil)
    ((endp term) *termination-index-error*)
    ((equal (car term) *proof-quote*) nil)
    (t
     (let ((head (car term))
           (args (cdr term)))
       (cond
        ((proof-compound head)
         (if (equal (len head) 3)
             (termination-bind actual-calls
                 (termination-recursive-calls-walk-args
                  caller args tests env
                  (and ruled (termination-recursive-calls-extends *termination-lambdas* rulers))
                  rulers names)
               (termination-bind bindings (termination-lambda-bindings (cadr head) args env nil)
                 (termination-bind body-calls
                     (termination-recursive-calls-walk caller (caddr head) tests bindings ruled rulers names)
                   (append actual-calls body-calls))))
           (proof-list-of-length head 3)))
        ((and (equal head *termination-return-last*) (endp args))
         *termination-index-error*)
        ((and (equal head *termination-return-last*) (equal (car args) *termination-mbe*))
         (if (consp (cddr args))
             (termination-recursive-calls-walk caller (caddr args) tests env ruled rulers names)
           *termination-index-error*))
        ((and (equal head *proof-if*) ruled)
         (if (equal (len args) 3)
             (termination-bind test-calls
                 (termination-recursive-calls-walk
                  caller (car args) tests env
                  (termination-recursive-calls-extends *proof-if* rulers) rulers names)
               (termination-bind literal (proof-subst (car args) env)
                 (termination-bind yes-calls
                     (termination-recursive-calls-walk
                      caller (cadr args) (append tests (list (list literal t))) env t rulers names)
                   (termination-bind no-calls
                       (termination-recursive-calls-walk
                        caller (caddr args) (append tests (list (list literal nil))) env t rulers names)
                     (append test-calls yes-calls no-calls)))))
           (proof-list-of-length args 3)))
        (t
         (let ((recursive (member-equal head names)))
           (termination-bind actuals (if recursive (termination-subst-actuals args env) nil)
             (termination-bind inner-calls
                 (termination-recursive-calls-walk-args
                  caller args tests env
                  (and ruled (termination-recursive-calls-extends head rulers)) rulers names)
               (if recursive
                   (cons (termination-make-call caller head actuals tests) inner-calls)
                 inner-calls))))))))))
 (defun termination-recursive-calls-walk-args (caller args tests env ruled rulers names)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (termination-bind first
         (termination-recursive-calls-walk caller (car args) tests env ruled rulers names)
       (termination-bind rest
           (termination-recursive-calls-walk-args caller (cdr args) tests env ruled rulers names)
         (append first rest))))))

(defun termination-definition-names (definitions)
  (if (endp definitions)
      nil
    (termination-bind name (proof-term-at (car definitions) 0)
      (termination-bind rest (termination-definition-names (cdr definitions))
        (cons name rest)))))

(defun termination-recursive-definitions (definitions rulers names)
  (if (endp definitions)
      nil
    (termination-bind definition (proof-list-of-length (car definitions) 3)
      (termination-bind calls
          (termination-recursive-calls-walk
           (car definition) (caddr definition) nil nil t rulers names)
        (termination-bind rest (termination-recursive-definitions (cdr definitions) rulers names)
          (append calls rest))))))

(defun termination-recursive-calls (rulers definitions)
  (termination-bind names (termination-definition-names definitions)
    (termination-recursive-definitions definitions rulers names)))

(defun termination-formals (definitions normalize formals)
  (if (endp definitions)
      formals
    (termination-bind definition (proof-list-of-length (car definitions) 3)
      (let ((args (cadr definition)))
        (termination-formals
         (cdr definitions) normalize
         (table-put formals (car definition)
                      (if (and normalize (equal args *proof-nil*)) nil args)))))))

(defun termination-name-key-error (name)
  (declare (ignore name))
  (list :failure "key" ""))

(defun termination-ordinality-cases (definitions measures)
  (if (endp definitions)
      nil
    (let* ((name (caar definitions))
           (measure (assoc-equal name measures)))
      (if measure
          (termination-bind rest (termination-ordinality-cases (cdr definitions) measures)
            (cons (list (list (list *proof-ordinalp* (cdr measure))) nil) rest))
        (termination-name-key-error name)))))

(defun termination-clause-tests (tests)
  (if (endp tests)
      nil
    (termination-bind signed (proof-list-of-length (car tests) 2)
      (let* ((term (car signed))
             (literal (if (cadr signed) (proof-neg term) term)))
        (termination-bind rest (termination-clause-tests (cdr tests))
          (cons literal rest))))))

(defun termination-bindings (formals actuals bindings)
  (if (or (endp formals) (endp actuals))
      bindings
    (termination-bindings (cdr formals) (cdr actuals)
                          (table-put bindings (car formals) (car actuals)))))

(defun termination-call-cases (calls measures formals)
  (if (endp calls)
      nil
    (let ((call (car calls)))
      (termination-bind tests (termination-clause-tests (termination-call-tests call))
        (let* ((callee (termination-call-callee call))
               (before (assoc-equal callee measures))
               (variables (assoc-equal callee formals))
               (caller (termination-call-caller call))
               (parent (assoc-equal caller measures)))
          (cond
           ((not before) (termination-name-key-error callee))
           ((not variables) (termination-name-key-error callee))
           (t
            (termination-bind smaller
                (proof-subst (cdr before) (termination-bindings (cdr variables)
                                                               (termination-call-actuals call) nil))
              (if parent
                  (let ((clause (append tests (list (list *proof-ordinal-less* smaller (cdr parent))))))
                    (termination-bind rest (termination-call-cases (cdr calls) measures formals)
                      (cons (list clause call) rest)))
                (termination-name-key-error caller))))))))))

(defun termination-obligation-cases (definitions measures calls)
  (termination-bind formals (termination-formals definitions nil nil)
    (termination-bind ordinalities (termination-ordinality-cases definitions measures)
      (termination-bind decreases (termination-call-cases calls measures formals)
        (append ordinalities decreases)))))

(defun termination-case-clauses (cases)
  (if (endp cases)
      nil
    (cons (caar cases) (termination-case-clauses (cdr cases)))))

(defun termination-obligations (definitions measures calls)
  (termination-bind cases (termination-obligation-cases definitions measures calls)
    (proof-unique (termination-case-clauses cases))))

(defun termination-selector-plan-selector-path-end (term variable)
  (cond
   ((not (proof-compound term)) (equal term variable))
   ((endp term) *termination-index-error*)
   ((member-equal (car term) *termination-selectors*)
    (if (consp (cdr term))
        (termination-selector-plan-selector-path-end (cadr term) variable)
      *termination-index-error*))
   (t (equal term variable))))

(defun termination-selector-plan-selector-path (term variable)
  (cond
   ((not (proof-compound term)) nil)
   ((endp term) *termination-index-error*)
   ((member-equal (car term) *termination-selectors*)
    (termination-selector-plan-selector-path-end term variable))
   (t nil)))

(defun termination-selector-actuals (calls)
  (if (endp calls)
      nil
    (termination-bind actuals (termination-logical-body-args (termination-call-actuals (car calls)))
      (termination-bind rest (termination-selector-actuals (cdr calls))
        (cons actuals rest)))))

(defun termination-selector-axes (definitions formals)
  (if (endp definitions)
      nil
    (let ((name (caar definitions)))
      (cons (cons name (len (cdr (assoc-equal name formals))))
            (termination-selector-axes (cdr definitions) formals)))))

(defun termination-selector-positive-axes-p (axes)
  (if (endp axes)
      t
    (and (posp (cdar axes)) (termination-selector-positive-axes-p (cdr axes)))))

(defun termination-selector-plan-check (calls actuals formals selected)
  (if (endp calls)
      t
    (let* ((call (car calls))
           (callee (termination-call-callee call))
           (caller (termination-call-caller call))
           (callee-index (assoc-equal callee selected))
           (caller-formals (assoc-equal caller formals))
           (caller-index (assoc-equal caller selected)))
      (cond
       ((not callee-index) (termination-name-key-error callee))
       ((<= (len (car actuals)) (cdr callee-index))
        *termination-index-error*)
       ((or (not caller-formals) (not caller-index))
        (termination-name-key-error caller))
       ((<= (len (cdr caller-formals)) (cdr caller-index))
        *termination-index-error*)
       (t
        (termination-bind valid
            (termination-selector-plan-selector-path
             (nth (cdr callee-index) (car actuals))
             (nth (cdr caller-index) (cdr caller-formals)))
          (and valid (termination-selector-plan-check
                      (cdr calls) (cdr actuals) formals selected))))))))

(defun termination-selector-selected-formals (selected formals)
  (if (endp selected)
      nil
    (let* ((name (caar selected))
           (index (cdar selected))
           (variables (cdr (assoc-equal name formals))))
      (cons (cons name (nth index variables))
            (termination-selector-selected-formals (cdr selected) formals)))))

(mutual-recursion
 (defun termination-selector-product (n axes formals calls actuals selected)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "termination-selector-product")
     (if (endp axes)
         (termination-bind valid (termination-selector-plan-check calls actuals formals selected)
           (and valid (termination-selector-selected-formals selected formals)))
       (termination-selector-indices (1- n) 0 axes formals calls actuals selected))))
 (defun termination-selector-indices (n index axes formals calls actuals selected)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "termination-selector-indices")
     (if (< index (cdar axes))
         (let ((result (termination-selector-product
                        (1- n) (cdr axes) formals calls actuals
                        (table-put selected (caar axes) index))))
           (or result
               (termination-selector-indices (1- n) (+ 1 index) axes formals calls actuals selected)))
       nil))))

(defun termination-selector-plan (definitions calls)
  (termination-bind formals (termination-formals definitions t nil)
    (termination-bind actuals (termination-selector-actuals calls)
      (let ((axes (termination-selector-axes definitions formals)))
        (and (termination-selector-positive-axes-p axes)
             (termination-selector-product 1000000 axes formals calls actuals nil))))))
