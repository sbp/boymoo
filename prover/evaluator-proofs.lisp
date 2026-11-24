(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *evaluator-proofs-a* (proof-sym "A" "ACL2"))
(defconst *evaluator-proofs-b* (proof-sym "B" "ACL2"))
(defconst *evaluator-proofs-symbolp* (proof-cl "SYMBOLP"))
(defconst *evaluator-proofs-quoted* (proof-quote *proof-quote*))
(defconst *evaluator-proofs-kwote* (proof-sym "KWOTE" "ACL2"))
(defconst *evaluator-proofs-kwote-list* (proof-sym "KWOTE-LST" "ACL2"))
(defconst *evaluator-proofs-pairlis* (proof-sym "PAIRLIS$" "ACL2"))
(defconst *evaluator-proofs-function* (list *library-car* *library-x*))

(defmacro evaluator-proofs-let* (bindings body)
  (if (endp bindings)
      body
    (let ((binding (car bindings)))
      `(let (,binding)
         (if (failure-p ,(car binding))
             ,(car binding)
           (evaluator-proofs-let* ,(cdr bindings) ,body))))))

(defun evaluator-proofs-fields-of-size (fields size)
  (proof-list-of-length fields size))

(defun evaluator-proofs-argument-cdrs (term index)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (list *library-car* term)
    (evaluator-proofs-argument-cdrs (list *library-cdr* term) (1- index))))

(defun evaluator-proofs-argument-index (index)
  (cond ((integerp index) index)
        ((eq index t) 1)
        ((null index) 0)
        (t '(:failure "failure" ""))))

(defun evaluator-proofs-argument (term index)
  (evaluator-proofs-let* ((index (evaluator-proofs-argument-index index)))
    (evaluator-proofs-argument-cdrs term index)))

(defun evaluator-proofs-argument-number-tail (tail number)
  (declare (xargs :measure (acl2-count tail)))
  (cond ((and (consp tail) (proof-is-call tail *library-cdr*))
         (if (consp (cdr tail))
             (evaluator-proofs-argument-number-tail (cadr tail) (1+ number))
           '(:failure "failure" "")))
        ((equal tail *library-x*) (1- number))
        (t *terms-unproved*)))

(defun evaluator-proofs-argument-number (term)
  (cond ((not (proof-is-call term *library-car*))
         *terms-unproved*)
        ((not (consp (cdr term))) '(:failure "failure" ""))
        (t (evaluator-proofs-argument-number-tail (cadr term) 0))))

(defun evaluator-proofs-used-add (number used)
  (cond ((endp used) (list number))
        ((equal number (car used)) used)
        ((string< (decimal-text number) (decimal-text (car used))) (cons number used))
        (t (cons (car used) (evaluator-proofs-used-add number (cdr used))))))

(defun evaluator-proofs-operations-abstract-selector (term used)
  (if (not (consp (cdr term)))
      '(:failure "failure" "")
    (evaluator-proofs-let* ((number (evaluator-proofs-argument-number (cadr term))))
      (cond ((not (consp (cddr term))) '(:failure "failure" ""))
            ((or (not (equal (caddr term) *evaluator-proofs-a*)) (< number 0))
             *terms-unproved*)
            (t (cons (evaluator-proofs-argument *library-y* number)
                     (evaluator-proofs-used-add number used)))))))

(mutual-recursion
 (defun evaluator-proofs-operations-abstract (term used eval-term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((proof-is-call term eval-term)
          (evaluator-proofs-operations-abstract-selector term used))
         ((proof-is-call term *proof-quote*) (cons term used))
         ((not (proof-compound term))
          *terms-unproved*)
         ((atom term) '(:failure "failure" ""))
         ((proof-compound (car term))
          *terms-unproved*)
         (t (evaluator-proofs-let*
             ((result (evaluator-proofs-operations-abstract-arguments
                       (cdr term) used eval-term)))
             (cons (cons (car term) (car result)) (cdr result))))))
 (defun evaluator-proofs-operations-abstract-arguments (args used eval-term)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       (cons nil used)
     (evaluator-proofs-let*
      ((first (evaluator-proofs-operations-abstract (car args) used eval-term))
       (rest (evaluator-proofs-operations-abstract-arguments (cdr args) (cdr first) eval-term)))
      (cons (cons (car first) (car rest)) (cdr rest))))))

(defun evaluator-proofs-operation-equations (formulas)
  (if (endp formulas)
      t
    (let ((formula (car formulas)))
      (cond ((not (proof-is-call formula *library-implies*))
             *terms-unproved*)
            ((not (consp (cddr formula))) '(:failure "failure" ""))
            ((not (proof-is-call (caddr formula) *proof-equal*))
             *terms-unproved*)
            (t (evaluator-proofs-operation-equations (cdr formulas)))))))

(defun evaluator-proofs-primitive-case (guard equality eval-term)
  (let ((test (caddr guard)))
    (cond ((not (proof-is-call guard *proof-if*)) nil)
          ((not (consp (cdr guard))) '(:failure "failure" ""))
          ((not (equal (cadr guard) (list *proof-consp* *library-x*))) nil)
          ((not (consp (cdddr guard))) '(:failure "failure" ""))
          ((not (equal (cadddr guard) *proof-false*)) nil)
          ((not (proof-is-call test *proof-equal*)) nil)
          ((not (consp (cdr test))) '(:failure "failure" ""))
          ((not (equal (cadr test) *evaluator-proofs-function*)) nil)
          ((not (consp (cddr test))) '(:failure "failure" ""))
          ((not (proof-is-call (caddr test) *proof-quote*)) nil)
          ((not (consp (cdr equality))) '(:failure "failure" ""))
          (t (equal (cadr equality) (list eval-term *library-x* *evaluator-proofs-a*))))))

(defun evaluator-proofs-primitive-operations (formulas eval-term)
  (if (endp formulas)
      nil
    (evaluator-proofs-let*
     ((case-pair (evaluator-proofs-fields-of-size (cdar formulas) 2))
      (guard (car case-pair))
      (equality (cadr case-pair))
      (valid (evaluator-proofs-primitive-case guard equality eval-term)))
     (cond ((not valid) *terms-unproved*)
           ((not (consp (cddr equality))) '(:failure "failure" ""))
           (t (evaluator-proofs-let*
               ((operation (evaluator-proofs-operations-abstract
                            (caddr equality) nil eval-term))
                (rest (evaluator-proofs-primitive-operations (cdr formulas) eval-term)))
               (cons (list (caddr (caddr guard)) (car operation) (seq-sorted (cdr operation))) rest)))))))

(defun evaluator-proofs-operations (functions formulas)
  (evaluator-proofs-let*
   ((functions (evaluator-proofs-fields-of-size functions 2))
    (term-function (evaluator-proofs-fields-of-size (car functions) 2))
    (list-function (evaluator-proofs-fields-of-size (cadr functions) 2))
    (equation-shape (evaluator-proofs-operation-equations formulas)))
   (if (and equation-shape (consp formulas) (consp (cddr (caddar formulas))))
       (let* ((eval-term (car term-function))
              (eval-list (car list-function))
              (replay (caddr (caddar formulas)))
              (args (list eval-list (list *library-cdr* *library-x*) *evaluator-proofs-a*))
              (call (list *proof-cons* *evaluator-proofs-function*
                          (list *evaluator-proofs-kwote-list* args))))
         (if (equal replay (list eval-term call *proof-false*))
             (evaluator-proofs-primitive-operations (nthcdr 8 formulas) eval-term)
           *terms-unproved*))
     '(:failure "failure" ""))))

(defun evaluator-proofs-evaluator-make (lib ops name eval-fn eval-list apply-fn formulas)
  (list :evaluator lib ops name eval-fn eval-list apply-fn formulas))

(defun evaluator-proofs-evaluator-lib (evaluator) (cadr evaluator))
(defun evaluator-proofs-evaluator-ops (evaluator) (caddr evaluator))
(defun evaluator-proofs-evaluator-name (evaluator) (cadddr evaluator))
(defun evaluator-proofs-evaluator-eval (evaluator) (nth 4 evaluator))
(defun evaluator-proofs-evaluator-eval-list (evaluator) (nth 5 evaluator))
(defun evaluator-proofs-evaluator-apply (evaluator) (nth 6 evaluator))
(defun evaluator-proofs-evaluator-formulas (evaluator) (nth 7 evaluator))

(defun evaluator-proofs-evaluator-with-lib (evaluator lib)
  (evaluator-proofs-evaluator-make lib (evaluator-proofs-evaluator-ops evaluator)
                                  (evaluator-proofs-evaluator-name evaluator)
                                  (evaluator-proofs-evaluator-eval evaluator)
                                  (evaluator-proofs-evaluator-eval-list evaluator)
                                  (evaluator-proofs-evaluator-apply evaluator)
                                  (evaluator-proofs-evaluator-formulas evaluator)))

(defun evaluator-proofs-formulas (named-formulas)
  (if (endp named-formulas)
      nil
    (evaluator-proofs-let*
     ((named (evaluator-proofs-fields-of-size (car named-formulas) 2))
      (rest (evaluator-proofs-formulas (cdr named-formulas))))
     (cons (cadr named) rest))))

(defun evaluator-proofs-substitute-formulas (formulas names)
  (if (endp formulas)
      nil
    (evaluator-proofs-let*
     ((formula (terms-replace-calls (car formulas) names))
      (rest (evaluator-proofs-substitute-formulas (cdr formulas) names)))
     (cons formula rest))))

(defun evaluator-proofs-evaluator-init (lib data)
  (evaluator-proofs-let*
   ((data (evaluator-proofs-fields-of-size data 2))
    (functions (car data))
    (formulas (evaluator-proofs-formulas (cadr data)))
    (ops (evaluator-proofs-operations functions formulas))
    (source (proof-write data)))
   (let* ((digest (text-upper (seq-slice (siphash-hexdigest source) 0 16)))
          (name (concatenate 'string "EVALUATOR-" digest))
          (prefix (concatenate 'string "T1-" name "-"))
          (eval-fn (proof-sym (concatenate 'string prefix "TERM") "ACL2"))
          (eval-list (proof-sym (concatenate 'string prefix "LIST") "ACL2"))
          (apply-fn (proof-sym (concatenate 'string prefix "APPLY") "ACL2"))
          (names (table-put (list (cons (caar functions) eval-fn))
                              (caadr functions) eval-list)))
     (evaluator-proofs-let* ((formulas (evaluator-proofs-substitute-formulas formulas names)))
       (evaluator-proofs-evaluator-make lib ops name eval-fn eval-list apply-fn formulas)))))

(defun evaluator-proofs-apply-body (reversed-ops apply-body)
  (if (endp reversed-ops)
      apply-body
    (let* ((operation (car reversed-ops))
           (test (proof-eq *library-z* (car operation)))
           (body (proof-ite test (cadr operation) apply-body)))
      (evaluator-proofs-apply-body (cdr reversed-ops) body))))

(defun evaluator-proofs-definitions (evaluator)
  (let* ((eval-fn (evaluator-proofs-evaluator-eval evaluator))
         (eval-list (evaluator-proofs-evaluator-eval-list evaluator))
         (apply-fn (evaluator-proofs-evaluator-apply evaluator))
         (function *evaluator-proofs-function*)
         (environment *evaluator-proofs-a*)
         (args (list eval-list (list *library-cdr* *library-x*) environment))
         (names (evaluator-proofs-argument function 1))
         (lambda-body (evaluator-proofs-argument function 2))
         (lambda-value (list eval-fn lambda-body
                             (list *evaluator-proofs-pairlis* names args)))
         (dispatch (proof-ite (list *proof-consp* function) lambda-value
                              (proof-ite (list *evaluator-proofs-symbolp* function)
                                         (list apply-fn function args) *proof-false*)))
         (application (proof-ite (proof-eq function *evaluator-proofs-quoted*)
                                 (evaluator-proofs-argument *library-x* 1) dispatch))
         (assoc-term (list (proof-sym "ASSOC-EQUAL" "ACL2") *library-x* environment))
         (variable (proof-ite (list *evaluator-proofs-symbolp* *library-x*)
                              (proof-ite *library-x* (list *library-cdr* assoc-term) *proof-false*)
                              *proof-false*))
         (cons-test (list *proof-consp* *library-x*))
         (value (proof-ite cons-test application variable))
         (head-value (list eval-fn (list *library-car* *library-x*) environment))
         (values (proof-ite cons-test (list *proof-cons* head-value args) *proof-false*))
         (formals (list *library-x* environment)))
    (list (list eval-fn formals value) (list eval-list formals values))))

(defun evaluator-proofs-add-definitions (proof definitions)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      proof
    (let ((definition (car definitions)))
      (evaluator-proofs-let*
       ((proof (proof-proof-add-definition proof (car definition)
                                            (cadr definition) (caddr definition))))
       (evaluator-proofs-add-definitions proof (cdr definitions))))))

(defun evaluator-proofs-evaluator-add-pair (evaluator)
  (let* ((lib (evaluator-proofs-evaluator-lib evaluator))
         (definitions (evaluator-proofs-definitions evaluator))
         (eval-fn (evaluator-proofs-evaluator-eval evaluator))
         (eval-list (evaluator-proofs-evaluator-eval-list evaluator))
         (data (cons *termination-all* definitions))
         (measure (list (list *library-count* *library-x*) *proof-ordinal-less*))
         (measures (table-put (list (cons eval-fn measure)) eval-list measure))
         (result (termination-proofs-termination-proofs lib data measures nil nil)))
    (if (failure-p result)
        (cons result evaluator)
      (let* ((value (car result))
             (lib (cdr result))
             (evaluator (evaluator-proofs-evaluator-with-lib evaluator lib)))
        (if (failure-p value)
            (cons value evaluator)
          (let ((source (proof-line "define" data))
                (entry (car value)))
            (if (failure-p source)
                (cons source evaluator)
              (let* ((entry (list "define" eval-fn (caddr entry)
                                  (concatenate 'string source (cadddr entry))))
                     (lib (library-library-with-entries
                           lib (append (library-library-entries lib) (list entry))))
                     (proof (evaluator-proofs-add-definitions
                             (library-library-proof lib) definitions)))
                (if (failure-p proof)
                    (cons proof (evaluator-proofs-evaluator-with-lib evaluator lib))
                  (cons nil (evaluator-proofs-evaluator-with-lib
                             evaluator (library-library-with-proof lib proof))))))))))))

(defun evaluator-proofs-evaluator-define-result (evaluator)
  (let* ((lib (evaluator-proofs-evaluator-lib evaluator))
         (apply-body (evaluator-proofs-apply-body
                      (reverse (evaluator-proofs-evaluator-ops evaluator)) *proof-false*))
         (result (library-library-definition lib (evaluator-proofs-evaluator-apply evaluator)
                                             (list *library-z* *library-y*) apply-body)))
    (if (failure-p result)
        (cons result evaluator)
      (evaluator-proofs-evaluator-add-pair
       (evaluator-proofs-evaluator-with-lib evaluator result)))))

(defun evaluator-proofs-evaluator-define (evaluator)
  (let ((result (evaluator-proofs-evaluator-define-result evaluator)))
    (or (car result) (cdr result))))

(defun evaluator-proofs-evaluator-opened (evaluator call evidence definitions logical)
  (let* ((lib (evaluator-proofs-evaluator-lib evaluator))
         (proof (library-library-proof lib)))
    (evaluator-proofs-let*
     ((equation (proof-proof-unfold proof call))
      (reducer (book-logic-reducer-init lib evidence definitions t 80 230 nil logical))
      (literal (proof-step-first equation))
      (reduced (book-logic-reducer-reduce reducer (caddr literal) nil))
      (reduction (car reduced)))
     (proof-proof-chain proof equation (list reduction)))))

(defun evaluator-proofs-evaluator-list-equation (evaluator term env evidence)
  (evaluator-proofs-evaluator-opened
   evaluator (list (evaluator-proofs-evaluator-eval-list evaluator) term env) evidence nil nil))

(defun evaluator-proofs-projection-fact (evaluator index)
  (let* ((lib (evaluator-proofs-evaluator-lib evaluator))
         (label (concatenate 'string "SELF-" (evaluator-proofs-evaluator-name evaluator)
                             "-ARG-" (decimal-text index))))
    (proof-proof-fact (library-library-proof lib) (proof-sym label "ACL2")
                      (list (list *library-x* (list *library-cdr* *library-x*))))))

(defun evaluator-proofs-evaluator-projection (evaluator index)
  (let* ((lib (evaluator-proofs-evaluator-lib evaluator))
         (proof (library-library-proof lib))
         (eval-fn (evaluator-proofs-evaluator-eval evaluator))
         (values (list (evaluator-proofs-evaluator-eval-list evaluator)
                       *library-x* *evaluator-proofs-a*))
         (cons-test (list *proof-consp* *library-x*)))
    (evaluator-proofs-let*
     ((left (evaluator-proofs-argument values index))
      (argument (evaluator-proofs-argument *library-x* index))
      (right (list eval-fn argument *evaluator-proofs-a*))
      (goal (proof-eq left right))
      (when-cons (proof-proof-assume proof cons-test t))
      (when-atom (proof-proof-assume proof cons-test nil))
      (unfolded (evaluator-proofs-evaluator-list-equation
                 evaluator *library-x* *evaluator-proofs-a* (list when-cons)))
      (reducer (book-logic-reducer-init lib (list unfolded) nil nil 32 95 nil nil))
      (reduced (book-logic-reducer-reduce reducer left nil))
      (yes (car reduced))
      (yes (if (equal index 0)
               yes
             (evaluator-proofs-let*
              ((previous (evaluator-proofs-projection-fact evaluator (1- index))))
              (proof-proof-chain proof yes (list previous)))))
      (unfolded (evaluator-proofs-evaluator-list-equation
                 evaluator *library-x* *evaluator-proofs-a* (list when-atom)))
      (reducer (book-logic-reducer-init lib (list unfolded when-atom) (list eval-fn)
                                        t 48 95 nil t))
      (reduced (book-logic-reducer-reduce reducer left nil))
      (left-step (car reduced))
      (reduced (book-logic-reducer-reduce (cdr reduced) right nil))
      (right-step (car reduced))
      (reverse (proof-proof-symmetric proof right-step))
      (no (proof-proof-chain proof left-step (list reverse)))
      (step (proof-proof-cases proof cons-test yes no))
      (name (concatenate 'string (evaluator-proofs-evaluator-name evaluator)
                         "-ARG-" (decimal-text index)))
      (lib (library-library-lemma lib name goal step nil)))
     (evaluator-proofs-evaluator-with-lib evaluator lib))))

(defun evaluator-proofs-evaluator-list-replay (evaluator)
  (let* ((lib (evaluator-proofs-evaluator-lib evaluator))
         (proof (library-library-proof lib))
         (eval-list (evaluator-proofs-evaluator-eval-list evaluator))
         (values (list eval-list *library-x* *evaluator-proofs-a*))
         (replay (list eval-list (list *evaluator-proofs-kwote-list* values) *evaluator-proofs-b*))
         (goal (proof-eq replay values))
         (cons-test (list *proof-consp* *library-x*)))
    (evaluator-proofs-let*
     ((induction (book-logic-tree-induction-init lib goal *library-x*))
      (yes (proof-proof-assume proof cons-test t))
      (no (proof-proof-assume proof cons-test nil))
      (builtin (library-library-builtin lib 3 *library-x*))
      (smaller (proof-proof-discharge proof builtin yes))
      (induction-result (book-logic-tree-induction-at
                         induction (list *library-cdr* *library-x*) smaller nil))
      (hypothesis (car induction-result))
      (select (evaluator-proofs-evaluator-list-equation
               evaluator *library-x* *evaluator-proofs-a* (list yes)))
      (literal (proof-step-first select))
      (items (caddr literal))
      (quoted (evaluator-proofs-evaluator-opened
               evaluator (list *evaluator-proofs-kwote-list* items) nil
               (list *rulers-endp* *rulers-atom* *proof-not* *evaluator-proofs-kwote*
                     *termination-return-last*) nil))
      (literal (proof-step-first quoted))
      (joined (evaluator-proofs-evaluator-list-equation
               evaluator (caddr literal) *evaluator-proofs-b* nil))
      (literal (proof-step-first joined))
      (replay-head (evaluator-proofs-evaluator-opened
                    evaluator (cadr (caddr literal)) nil nil nil))
      (reflexive (lemmas-slice-library-reflexive lib replay))
      (when-cons (proof-proof-rewrite proof reflexive select '(1 2 1 1)))
      (when-cons (proof-proof-rewrite proof when-cons quoted '(1 2 1)))
      (when-cons (proof-proof-chain proof when-cons (list joined)))
      (when-cons (proof-proof-rewrite proof when-cons replay-head '(1 2 1)))
      (when-cons (proof-proof-rewrite proof when-cons hypothesis '(1 2 2)))
      (reverse (proof-proof-symmetric proof select))
      (when-cons (proof-proof-chain proof when-cons (list reverse)))
      (select (evaluator-proofs-evaluator-list-equation
               evaluator *library-x* *evaluator-proofs-a* (list no)))
      (reducer (book-logic-reducer-init
                lib (list select)
                (list eval-list *evaluator-proofs-kwote-list* *rulers-endp* *rulers-atom* *proof-not*)
                nil 70 160 nil nil))
      (reduced (book-logic-reducer-reduce reducer replay nil))
      (replay-step (car reduced))
      (reverse (proof-proof-symmetric proof select))
      (when-atom (proof-proof-chain proof replay-step (list reverse)))
      (cases (proof-proof-cases proof cons-test when-cons when-atom))
      (step (book-logic-tree-induction-finish (cdr induction-result) cases))
      (name (concatenate 'string (evaluator-proofs-evaluator-name evaluator) "-QUOTED-VALUES"))
      (lib (library-library-lemma lib name goal step nil)))
     (evaluator-proofs-evaluator-with-lib evaluator lib))))

(defun evaluator-proofs-evaluator-replay (evaluator goal evidence)
  (let* ((lib (evaluator-proofs-evaluator-lib evaluator))
         (proof (library-library-proof lib)))
    (evaluator-proofs-let*
     ((operands (evaluator-proofs-fields-of-size (cdr goal) 2))
      (left (car operands))
      (right (cadr operands))
      (opened (evaluator-proofs-evaluator-opened evaluator left evidence nil nil))
      (encoded (evaluator-proofs-evaluator-opened evaluator right evidence nil nil))
      (args (cdadr right))
      (car-cons (library-library-axiom lib "CAR-CONS" args))
      (encoded (proof-proof-rewrite-first proof encoded car-cons))
      (cdr-cons (library-library-axiom lib "CDR-CONS" args))
      (encoded (proof-proof-rewrite-first proof encoded cdr-cons))
      (name (proof-sym (concatenate 'string "SELF-" (evaluator-proofs-evaluator-name evaluator)
                                   "-QUOTED-VALUES") "ACL2"))
      (identity (proof-proof-fact proof name
                                  (list (list *library-x* (list *library-cdr* *library-x*))
                                        (list *evaluator-proofs-b* *proof-false*))))
      (encoded (proof-proof-rewrite-first proof encoded identity))
      (reverse (proof-proof-symmetric proof encoded)))
     (proof-proof-chain proof opened (list reverse)))))

(defun evaluator-proofs-shape-symbol (lib evidence)
  (let ((symbol-step (assoc-equal (list *evaluator-proofs-symbolp* *library-x*) evidence)))
    (if (not symbol-step)
        evidence
      (let* ((proof (library-library-proof lib))
             (test (list *proof-consp* *library-x*)))
        (evaluator-proofs-let*
         ((rule (proof-proof-fact proof "consp-not-symbolp" nil))
          (assume (proof-proof-assume proof test t))
          (atom-step (proof-proof-modus-ponens proof rule assume))
          (step (proof-proof-cut proof (cdr symbol-step) atom-step))
          (step (proof-proof-front proof step (proof-neg test))))
         (table-put evidence (proof-neg test) step))))))

(defun evaluator-proofs-shape-literal (lib evidence quoted test holds)
  (let ((premise (cdr (assoc-equal (if holds test (proof-neg test)) evidence))))
    (if (not premise)
        evidence
      (let ((proof (library-library-proof lib)))
        (evaluator-proofs-let*
         ((assume (proof-proof-assume proof quoted t))
          (literal (proof-proof-rewrite proof premise assume (if holds '(1 1) '(1 1 1))))
          (reducer (book-logic-reducer-init lib nil (list (proof-cl "NOT")) nil 800 400 nil nil))
          (term (proof-step-first literal))
          (reduced (book-logic-reducer-reduce reducer term nil))
          (contradiction (car reduced))
          (ruled-out (proof-proof-rewrite proof literal contradiction '(1)))
          (ruled-out (proof-proof-tidy proof ruled-out))
          (ruled-out (proof-proof-front proof ruled-out (proof-neg quoted))))
         (table-put evidence (proof-neg quoted) ruled-out))))))

(defun evaluator-proofs-evaluator-add-shape-facts (evaluator evidence)
  (let* ((lib (evaluator-proofs-evaluator-lib evaluator))
         (function *evaluator-proofs-function*)
         (quoted (proof-eq function *evaluator-proofs-quoted*)))
    (evaluator-proofs-let*
     ((evidence (evaluator-proofs-shape-symbol lib evidence))
      (evidence (evaluator-proofs-shape-literal
                 lib evidence quoted (list *proof-consp* function) t)))
     (evaluator-proofs-shape-literal lib evidence quoted
                                    (list *evaluator-proofs-symbolp* function) nil))))

(defun evaluator-proofs-index-evidence (steps evidence)
  (if (endp steps)
      evidence
    (evaluator-proofs-let* ((term (proof-step-first (car steps))))
      (evaluator-proofs-index-evidence (cdr steps) (table-put evidence term (car steps))))))

(defun evaluator-proofs-operator-fact (lib evidence operator equality predicate truth)
  (let* ((proof (library-library-proof lib))
         (literal (list predicate operator)))
    (evaluator-proofs-let*
     ((ground (proof-proof-prove proof (if truth literal (proof-neg literal)) nil
                                 (list (proof-cl "NOT"))))
      (reverse (proof-proof-symmetric proof equality))
      (fact (proof-proof-rewrite proof ground reverse (if truth '(1 1) '(1 1 1))))
      (fact (proof-proof-tidy proof fact))
      (term (proof-step-first fact)))
     (table-put evidence term fact))))

(defun evaluator-proofs-rewrite-projections (evaluator consequence numbers)
  (declare (xargs :measure (acl2-count numbers)))
  (if (endp numbers)
      consequence
    (let ((proof (library-library-proof (evaluator-proofs-evaluator-lib evaluator))))
      (evaluator-proofs-let*
       ((project (evaluator-proofs-projection-fact evaluator (car numbers)))
        (consequence (proof-proof-rewrite-first proof consequence project)))
       (evaluator-proofs-rewrite-projections evaluator consequence (cdr numbers))))))

(defun evaluator-proofs-primitive-constraint (evaluator position equality evidence)
  (let* ((lib (evaluator-proofs-evaluator-lib evaluator))
         (ops (evaluator-proofs-evaluator-ops evaluator))
         (index (- position 8)))
    (if (<= (len ops) index)
        '(:failure "failure" "")
      (let* ((op (nth index ops))
             (operator (car op))
             (numbers (caddr op))
             (key (proof-eq *evaluator-proofs-function* operator))
             (operators (assoc-equal key evidence)))
        (if (not operators)
            '(:failure "failure" "")
          (evaluator-proofs-let*
           ((operators (cdr operators))
            (evidence (evaluator-proofs-operator-fact
                       lib evidence operator operators *proof-consp* nil))
            (evidence (evaluator-proofs-operator-fact
                       lib evidence operator operators *evaluator-proofs-symbolp* t))
            (consequence (evaluator-proofs-evaluator-opened
                          evaluator (cadr equality) (table-values evidence)
                          (list (evaluator-proofs-evaluator-apply evaluator)) nil)))
           (evaluator-proofs-rewrite-projections evaluator consequence numbers)))))))

(defun evaluator-proofs-evaluator-constraint (evaluator position formula)
  (let* ((lib (evaluator-proofs-evaluator-lib evaluator))
         (proof (library-library-proof lib)))
    (evaluator-proofs-let*
     ((formula (evaluator-proofs-fields-of-size formula 3))
      (condition (cadr formula))
      (equality (caddr formula))
      (premise (proof-proof-assume proof condition t))
      (rulers (rulers-rulers-init lib nil nil))
      (steps (rulers-rulers-expand 1000000 rulers condition t premise))
      (evidence (evaluator-proofs-index-evidence steps nil))
      (evidence (if (< position 8)
                    (evaluator-proofs-evaluator-add-shape-facts evaluator evidence)
                  evidence))
      (consequence (cond ((equal position 0)
                          (evaluator-proofs-evaluator-replay evaluator equality (table-values evidence)))
                         ((< position 8)
                          (if (consp (cdr equality))
                              (evaluator-proofs-evaluator-opened
                               evaluator (cadr equality) (table-values evidence) nil nil)
                            '(:failure "failure" "")))
                         (t (evaluator-proofs-primitive-constraint
                             evaluator position equality evidence))))
      (term (proof-step-first consequence)))
     (if (equal term equality)
         (witnesses-prove-implication lib formula premise consequence)
       *terms-unproved*))))

(defun evaluator-proofs-max-number (numbers maximum)
  (if (endp numbers)
      maximum
    (evaluator-proofs-max-number (cdr numbers) (max (car numbers) maximum))))

(defun evaluator-proofs-argument-bound (ops maximum)
  (if (endp ops)
      maximum
    (evaluator-proofs-argument-bound
     (cdr ops) (evaluator-proofs-max-number (caddar ops) maximum))))

(defun evaluator-proofs-projections (evaluator index remaining)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (cons nil evaluator)
    (let ((result (evaluator-proofs-evaluator-projection evaluator index)))
      (if (failure-p result)
          (cons result evaluator)
        (evaluator-proofs-projections result (1+ index) (1- remaining))))))

(defun evaluator-proofs-constraint-steps (evaluator index formulas)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      nil
    (evaluator-proofs-let*
     ((step (evaluator-proofs-evaluator-constraint evaluator index (car formulas)))
      (rest (evaluator-proofs-constraint-steps evaluator (1+ index) (cdr formulas))))
     (cons step rest))))

(defun evaluator-proofs-evaluator-witness-entry (evaluator first)
  (evaluator-proofs-let*
   ((proofs (evaluator-proofs-constraint-steps
             evaluator 0 (evaluator-proofs-evaluator-formulas evaluator))))
   (proof-proof-entry "witness" first
                      (list first (evaluator-proofs-evaluator-eval evaluator)
                            (evaluator-proofs-evaluator-eval-list evaluator))
                      proofs)))

(defun evaluator-proofs-evaluator-witness (evaluator first)
  (let ((defined (evaluator-proofs-evaluator-define-result evaluator)))
    (if (car defined)
        defined
      (let* ((evaluator (cdr defined))
             (replayed (evaluator-proofs-evaluator-list-replay evaluator)))
        (if (failure-p replayed)
            (cons replayed evaluator)
          (let* ((bound (evaluator-proofs-argument-bound
                         (evaluator-proofs-evaluator-ops replayed) -1))
                 (projected (evaluator-proofs-projections replayed 0 (1+ bound))))
            (if (car projected)
                projected
              (let ((evaluator (cdr projected)))
                (cons (evaluator-proofs-evaluator-witness-entry evaluator first)
                      evaluator)))))))))

(defun evaluator-proofs-evaluator-witnesses (lib data)
  (let ((evaluator (evaluator-proofs-evaluator-init lib data)))
    (if (failure-p evaluator)
        (cons evaluator lib)
      (let ((witness (evaluator-proofs-evaluator-witness evaluator (caaar data))))
        (cons (car witness) (evaluator-proofs-evaluator-lib (cdr witness)))))))
