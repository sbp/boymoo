(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-evaluators-a* (proof-sym "A" "ACL2"))
(defconst *b1-evaluators-mode* (proof-sym "LIST-MODE" "ACL2"))
(defconst *b1-evaluators-kwote* (proof-sym "KWOTE" "ACL2"))
(defconst *b1-evaluators-kwote-list* (proof-sym "KWOTE-LST" "ACL2"))
(defconst *b1-evaluators-pairlis* (proof-sym "PAIRLIS$" "ACL2"))
(defconst *b1-evaluators-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *b1-evaluators-quote-name* (proof-quote *proof-quote*))

(defun b1-evaluators-range-bound (count)
  (cond ((integerp count) count)
        ((eq count t) 1)
        ((null count) 0)
        (t '(:failure "failure" ""))))

(defun b1-evaluators-after-cdrs-count (term count)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      term
    (b1-evaluators-after-cdrs-count (list *library-cdr* term) (1- count))))

(defun b1-evaluators-after-cdrs (term count)
  (proof-with-checked-results ((count (b1-evaluators-range-bound count)))
    (b1-evaluators-after-cdrs-count term count)))

(defun b1-evaluators-argument (term index)
  (proof-with-checked-results ((tail (b1-evaluators-after-cdrs term index)))
    (list *library-car* tail)))

(defun b1-evaluators-evaluator-lib (evaluator)
  (cadr evaluator))

(defun b1-evaluators-evaluator-tag (evaluator)
  (caddr evaluator))

(defun b1-evaluators-evaluator-engine (evaluator)
  (cadddr evaluator))

(defun b1-evaluators-evaluator-term-fn (evaluator)
  (nth 4 evaluator))

(defun b1-evaluators-evaluator-list-fn (evaluator)
  (nth 5 evaluator))

(defun b1-evaluators-evaluator-functions (evaluator)
  (nth 6 evaluator))

(defun b1-evaluators-evaluator-table (evaluator)
  (nth 7 evaluator))

(defun b1-evaluators-evaluator-with-lib (evaluator lib)
  (list* :b1-evaluator lib (cddr evaluator)))

(defun b1-evaluators-evaluator-evaluate (evaluator term environment)
  (list (b1-evaluators-evaluator-engine evaluator) *proof-false* term environment))

(defun b1-evaluators-evaluator-evaluate-list (evaluator terms environment)
  (list (b1-evaluators-evaluator-engine evaluator) *proof-true* terms environment))

(defun b1-evaluators-evaluator-init-table (constraints)
  (if (endp constraints)
      nil
    (proof-with-checked-results
        ((pair (proof-list-of-length (car constraints) 2))
         (guard (proof-term-at (cadr pair) 1))
         (test (proof-term-at guard 2))
         (operator (proof-term-at test 2))
         (claim (proof-term-at (cadr pair) 2))
         (body (proof-term-at claim 2))
         (rest (b1-evaluators-evaluator-init-table (cdr constraints))))
      (cons (list operator body) rest))))

(defun b1-evaluators-evaluator-install-path-index (suffix args index)
  (declare (xargs :measure (acl2-count suffix)))
  (cond ((equal suffix args) index)
        ((not (proof-is-call suffix *library-cdr*)) '(:failure "failure" ""))
        ((not (consp (cdr suffix))) '(:failure "failure" ""))
        (t (b1-evaluators-evaluator-install-path-index (cadr suffix) args (1+ index)))))

(mutual-recursion
 (defun b1-evaluators-evaluator-install-mapped (term constrained-term args values)
   (declare (xargs :measure (acl2-count term)))
   (cond ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) term)
         ((proof-is-call term constrained-term)
          (proof-with-checked-results ((parts (proof-list-of-length term 3)))
            (let ((path (cadr parts)) (env (caddr parts)))
              (if (and (equal env *b1-evaluators-a*) (proof-is-call path *library-car*))
                  (proof-with-checked-results
                      ((suffix (proof-term-at path 1))
                       (index (b1-evaluators-evaluator-install-path-index suffix args 0)))
                    (b1-evaluators-argument values index))
                '(:failure "failure" "")))))
         ((endp term) '(:failure "failure" ""))
         (t (proof-with-checked-results
                ((mapped (b1-evaluators-evaluator-install-map-arguments
                          (cdr term) constrained-term args values)))
              (cons (car term) mapped)))))
 (defun b1-evaluators-evaluator-install-map-arguments (terms constrained-term args values)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (proof-with-checked-results
         ((term (b1-evaluators-evaluator-install-mapped (car terms) constrained-term args values))
          (rest (b1-evaluators-evaluator-install-map-arguments
                 (cdr terms) constrained-term args values)))
       (cons term rest)))))

(defun b1-evaluators-evaluator-install-application
    (operators constrained-term head args values application)
  (if (endp operators)
      application
    (proof-with-checked-results
        ((pair (proof-list-of-length (car operators) 2))
         (mapped (b1-evaluators-evaluator-install-mapped (cadr pair) constrained-term args values)))
      (b1-evaluators-evaluator-install-application
       (cdr operators) constrained-term head args values
       (proof-ite (proof-eq head (car pair)) mapped application)))))

(defun b1-evaluators-evaluator-install (evaluator constrained-term)
  (let* ((lib (b1-evaluators-evaluator-lib evaluator))
         (proof (library-library-proof lib))
         (engine (b1-evaluators-evaluator-engine evaluator)))
    (if (assoc-equal engine (proof-proof-definitions proof))
        evaluator
      (let* ((head (list *library-car* *library-x*))
             (args (list *library-cdr* *library-x*))
             (values (b1-evaluators-evaluator-evaluate-list evaluator args *b1-evaluators-a*)))
        (proof-with-checked-results
            ((application (b1-evaluators-evaluator-install-application
                           (reverse (b1-evaluators-evaluator-table evaluator))
                           constrained-term head args values *proof-false*))
             (application (proof-ite (list *b1-logic-symbolp* head) application *proof-false*))
             (parameters (b1-evaluators-argument head 1))
             (body (b1-evaluators-argument head 2))
             (lambda-value (b1-evaluators-evaluator-evaluate
                            evaluator body (list *b1-evaluators-pairlis* parameters values)))
             (quoted-value (b1-evaluators-argument *library-x* 1))
             (compound-value (proof-ite (proof-eq head *b1-evaluators-quote-name*) quoted-value
                                        (proof-ite (list *proof-consp* head) lambda-value application)))
             (variable (proof-ite *library-x*
                                  (list *library-cdr* (list *b1-evaluators-assoc*
                                                           *library-x* *b1-evaluators-a*))
                                  *proof-false*))
             (atom-value (proof-ite (list *b1-logic-symbolp* *library-x*) variable *proof-false*))
             (term-value (proof-ite (list *proof-consp* *library-x*) compound-value atom-value))
             (list-value (proof-ite (list *proof-consp* *library-x*)
                                    (list *proof-cons* (b1-evaluators-evaluator-evaluate
                                                       evaluator head *b1-evaluators-a*) values)
                                    *proof-false*))
             (formals (list *b1-evaluators-mode* *library-x* *b1-evaluators-a*))
             (body (proof-ite *b1-evaluators-mode* list-value term-value))
             (definition (list engine formals body))
             (rulers (list *proof-if*))
             (measure (list *library-count* *library-x*))
             (calls (termination-recursive-calls rulers (list definition)))
             (measured (b1-measures-proof-for-measures
                        lib (list definition) calls (list (cons engine measure))))
             (lib (cdr measured))
             (measure-entry (proof-proof-entry "measure" engine (list engine measure)
                                               (cadar measured)))
             (header (proof-line "define" (list rulers definition)))
             (source (concatenate 'string header (cadddr measure-entry)))
             (lib (library-library-with-entries
                   lib (append (library-library-entries lib)
                               (list (list "define" engine (caddr measure-entry) source)))))
             (new-proof (proof-proof-add-definition (library-library-proof lib) engine formals body))
             (lib (library-library-with-proof lib new-proof))
             (wrapper-formals (list *library-x* *b1-evaluators-a*))
             (lib (library-library-definition
                   lib (b1-evaluators-evaluator-term-fn evaluator) wrapper-formals
                   (b1-evaluators-evaluator-evaluate evaluator *library-x* *b1-evaluators-a*)))
             (lib (library-library-definition
                   lib (b1-evaluators-evaluator-list-fn evaluator) wrapper-formals
                   (b1-evaluators-evaluator-evaluate-list evaluator *library-x* *b1-evaluators-a*))))
          (b1-evaluators-evaluator-with-lib evaluator lib))))))

(defun b1-evaluators-evaluator-init (lib functions constraints)
  (proof-with-checked-results
      ((constrained-term (proof-term-at functions 0))
       (written (proof-write constrained-term))
       (tag (concatenate 'string "EVAL-" (text-upper (seq-slice (siphash-hexdigest written) 0 12))))
       (name (concatenate 'string "B1-" tag))
       (engine (proof-sym name "ACL2"))
       (term-fn (proof-sym (concatenate 'string name "-TERM") "ACL2"))
       (list-fn (proof-sym (concatenate 'string name "-LIST") "ACL2"))
       (table (b1-evaluators-evaluator-init-table (seq-slice constraints 8 :none))))
    (b1-evaluators-evaluator-install
     (list :b1-evaluator lib tag engine term-fn list-fn (list term-fn list-fn) table)
     constrained-term)))

(defun b1-evaluators-evaluator-open (evaluator call evidence rules wrappers)
  (b1-logic-bookproof-normalize
   (b1-evaluators-evaluator-lib evaluator) call evidence
   (append wrappers (list (b1-evaluators-evaluator-engine evaluator))) rules nil nil t))

(defun b1-evaluators-selector-place (count)
  (declare (xargs :measure (nfix count)))
  (if (zp count) nil (cons 1 (b1-evaluators-selector-place (1- count)))))

(defun b1-evaluators-evaluator-selector-law-left (cell evaluator evaluated selected index)
  (let* ((lib (b1-evaluators-evaluator-lib evaluator))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equation (b1-evaluators-evaluator-open evaluator evaluated (list cell) nil nil))
         (reflexive (proof-proof-reflexive proof selected))
         (place (list* 1 2 (b1-evaluators-selector-place (1+ index))))
         (replaced (proof-proof-rewrite proof reflexive equation place))
         (result (proof-rewritten-term replaced))
         (normalized (b1-logic-bookproof-normalize lib result nil nil nil nil nil nil)))
      (proof-proof-chain proof replaced (list normalized)))))

(defun b1-evaluators-evaluator-selector-law-lemma
    (evaluator index tag test atom evaluated selected syntax right in-cons)
  (let* ((lib (b1-evaluators-evaluator-lib evaluator))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((in-atom (b1-evaluators-evaluator-selector-law-left atom evaluator evaluated selected index))
         (selector (if (equal index 0) *library-car* *library-cdr*))
         (absent (b1-structures-noncons-selector lib selector atom))
         (reduced (b1-logic-bookproof-normalize lib syntax nil nil
                                              (list (b1-logic-equal-to absent)) nil nil nil))
         (opened (b1-revappend-lift-argument lib right reduced 2))
         (result (proof-rewritten-term opened))
         (normalized (b1-evaluators-evaluator-open evaluator result nil nil nil))
         (opened (proof-proof-chain proof opened (list normalized)))
         (reversed (proof-proof-symmetric proof opened))
         (in-atom (proof-proof-chain proof in-atom (list reversed)))
         (cases (proof-proof-cases proof test in-cons in-atom))
         (lib (library-library-lemma lib tag (proof-eq selected right) cases nil)))
      (b1-evaluators-evaluator-with-lib evaluator lib))))

(defun b1-evaluators-selector-tag (evaluator index)
  (concatenate 'string (b1-evaluators-evaluator-tag evaluator) "-ARGUMENT-"
               (cond ((eq index t) "True")
                     ((null index) "False")
                     ((eq index :none) "None")
                     ((integerp index) (decimal-text index))
                     ((rationalp index) (concatenate 'string (decimal-text (numerator index))
                                                     "/" (decimal-text (denominator index))))
                     ((stringp index) index)
                     (t (proof-datum-text index)))))

(defun b1-evaluators-evaluator-selector-law-rec (n evaluator index terms environment)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "b1-evaluators-evaluator-selector-law-rec")
    (let* ((lib (b1-evaluators-evaluator-lib evaluator))
           (proof (library-library-proof lib))
           (tag (b1-evaluators-selector-tag evaluator index))
           (name (proof-sym (concatenate 'string "SELF-" tag) "ACL2")))
      (proof-with-checked-results
          ((evaluator
            (if (assoc-equal name (proof-proof-facts proof))
                evaluator
              (proof-with-checked-results
                  ((test (list *proof-consp* *library-x*))
                   (cons (proof-proof-assume proof test t))
                   (atom (proof-proof-assume proof test nil))
                   (evaluated (b1-evaluators-evaluator-evaluate-list
                               evaluator *library-x* *b1-evaluators-a*))
                   (selected (b1-evaluators-argument evaluated index))
                   (syntax (b1-evaluators-argument *library-x* index))
                   (right (b1-evaluators-evaluator-evaluate evaluator syntax *b1-evaluators-a*))
                   (index (b1-evaluators-range-bound index))
                   (in-cons (b1-evaluators-evaluator-selector-law-left
                             cons evaluator evaluated selected index))
                   (child (if (equal index 0)
                              (cons nil evaluator)
                            (b1-evaluators-evaluator-selector-law-rec
                             (1- n) evaluator (1- index) (list *library-cdr* *library-x*)
                             *b1-evaluators-a*)))
                   (evaluator (cdr child))
                   (updated-proof (library-library-proof (b1-evaluators-evaluator-lib evaluator)))
                   (in-cons (if (equal index 0) in-cons
                              (proof-proof-chain updated-proof in-cons (list (car child))))))
                (b1-evaluators-evaluator-selector-law-lemma
                 evaluator index tag test atom evaluated selected syntax right in-cons))))
           (proof (library-library-proof (b1-evaluators-evaluator-lib evaluator)))
           (step (proof-proof-fact proof name (list (list *library-x* terms)
                                                    (list *b1-evaluators-a* environment)))))
        (cons step evaluator)))))

(defun b1-evaluators-evaluator-selector-law (evaluator index terms environment)
  (b1-evaluators-evaluator-selector-law-rec 1000000 evaluator index terms environment))

(defun b1-evaluators-evaluator-quote-arguments-reduce-inputs
    (cell evaluator values quoted again)
  (let* ((lib (b1-evaluators-evaluator-lib evaluator))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((result (b1-evaluators-evaluator-open evaluator values (list cell) nil nil))
         (packaged (b1-revappend-lift-argument lib quoted result 1))
         (right (proof-rewritten-term packaged))
         (reduced (b1-revappend-open-list lib right nil))
         (packaged (proof-proof-chain proof packaged (list reduced)))
         (opened (b1-revappend-lift-argument lib again packaged 2))
         (right (proof-rewritten-term opened))
         (reduced (b1-evaluators-evaluator-open evaluator right nil nil nil))
         (opened (proof-proof-chain proof opened (list reduced))))
      (list result opened))))

(defun b1-evaluators-evaluator-quote-arguments-base (atom evaluator values quoted again)
  (let ((proof (library-library-proof (b1-evaluators-evaluator-lib evaluator))))
    (proof-with-checked-results
        ((inputs (b1-evaluators-evaluator-quote-arguments-reduce-inputs
                  atom evaluator values quoted again))
         (reversed (proof-proof-symmetric proof (car inputs))))
      (proof-proof-chain proof (cadr inputs) (list reversed)))))

(defun b1-evaluators-evaluator-quote-arguments-step (cons induction evaluator values quoted again)
  (let* ((lib (b1-evaluators-evaluator-lib evaluator))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((inputs (b1-evaluators-evaluator-quote-arguments-reduce-inputs
                  cons evaluator values quoted again))
         (opened (cadr inputs))
         (right (proof-rewritten-term opened))
         (head (proof-term-at right 1))
         (syntax (proof-term-at head 2))
         (exact (b1-revappend-open-list lib syntax nil))
         (quotation (b1-revappend-lift-argument lib head exact 2))
         (right (proof-rewritten-term quotation))
         (reduced (b1-evaluators-evaluator-open evaluator right nil nil nil))
         (quotation (proof-proof-chain proof quotation (list reduced)))
         (opened (proof-proof-rewrite proof opened quotation '(1 2 1)))
         (opened (proof-proof-rewrite proof opened induction '(1 2 2)))
         (reversed (proof-proof-symmetric proof (car inputs))))
      (proof-proof-chain proof opened (list reversed)))))

(defun b1-evaluators-evaluator-quote-arguments-lemma (evaluator tag)
  (let* ((lib (b1-evaluators-evaluator-lib evaluator))
         (proof (library-library-proof lib))
         (values (b1-evaluators-evaluator-evaluate-list evaluator *library-x* *b1-evaluators-a*))
         (quoted (list *b1-evaluators-kwote-list* values))
         (again (b1-evaluators-evaluator-evaluate-list evaluator quoted *proof-false*))
         (formula (proof-eq again values)))
    (proof-with-checked-results
        ((prep (b1-revappend-list-induction-prepare lib formula *library-x* nil))
         (step (b1-evaluators-evaluator-quote-arguments-step
                (caddr prep) (cadddr prep) evaluator values quoted again))
         (atom (proof-proof-assume proof (cadr prep) nil))
         (base (b1-evaluators-evaluator-quote-arguments-base atom evaluator values quoted again))
         (done (b1-revappend-list-induction lib prep base step))
         (lib (library-library-lemma lib tag formula done nil)))
      (b1-evaluators-evaluator-with-lib evaluator lib))))

(defun b1-evaluators-evaluator-quote-arguments (evaluator)
  (let* ((lib (b1-evaluators-evaluator-lib evaluator))
         (tag (concatenate 'string (b1-evaluators-evaluator-tag evaluator) "-QUOTED-ARGUMENTS"))
         (name (proof-sym (concatenate 'string "SELF-" tag) "ACL2")))
    (proof-with-checked-results
        ((evaluator (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                        evaluator
                      (b1-evaluators-evaluator-quote-arguments-lemma evaluator tag)))
         (rule (b1-logic-bookproof-rewrite-rule (b1-evaluators-evaluator-lib evaluator) name)))
      (cons rule evaluator))))

(defun b1-evaluators-evaluator-constraint-common-expressions (premise lib number)
  (if (member-equal number '(1 4 5))
      (list premise)
    (b1-logic-bookproof-split-conjuncts lib premise)))

(defun b1-evaluators-evaluator-constraint-lambda-is-not-quote (cons-head lib)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first cons-head))
         (head (proof-term-at literal 1))
         (test (proof-eq head *b1-evaluators-quote-name*))
         (assumed (proof-proof-assume proof test t))
         (impossible (proof-proof-rewrite proof cons-head assumed '(1 1)))
         (simplified (proof-proof-simplify-first proof impossible nil nil)))
      (proof-proof-front proof simplified (proof-neg test)))))

(defun b1-evaluators-evaluator-constraint-branch-proof (lib number premise call fields)
  (let ((proof (library-library-proof lib)))
    (cond
     ((equal number 1)
      (proof-with-checked-results
          ((term (proof-term-at call 1))
           (cons (list *proof-consp* term))
           (law (proof-proof-fact proof "consp-not-symbolp" (list (list *library-x* term))))
           (assumed (proof-proof-assume proof cons t))
           (impossible (proof-proof-modus-ponens proof law assumed))
           (cut (proof-proof-cut proof premise impossible)))
        (proof-proof-front proof cut (proof-neg cons))))
     ((equal number 3)
      (proof-with-checked-results ((cons-head (proof-term-at fields 1)))
        (b1-evaluators-evaluator-constraint-lambda-is-not-quote cons-head lib)))
     ((equal number 7)
      (proof-with-checked-results
          ((term (proof-term-at call 1))
           (test (proof-eq (list *library-car* term) *b1-evaluators-quote-name*))
           (false-syntax (car (last fields)))
           (quote-symbol (b1-logic-bookproof-normalize-proof
                          lib (list *b1-logic-symbolp* *b1-evaluators-quote-name*) nil nil nil nil))
           (same (proof-proof-assume proof test t))
           (different (proof-proof-symmetric proof same))
           (witnessed (proof-proof-rewrite proof quote-symbol different '(1 1)))
           (cut (proof-proof-cut proof witnessed false-syntax)))
        (proof-proof-front proof cut (proof-neg test))))
     (t nil))))

(defun b1-evaluators-evaluator-constraint-selector (index result args env)
  (proof-with-checked-results
      ((law (b1-evaluators-evaluator-selector-law (cdr result) index args env))
       (evaluator (cdr law))
       (proof (library-library-proof (b1-evaluators-evaluator-lib evaluator)))
       (before (proof-proof-rewrite-first proof (car result) (car law))))
    (cons before evaluator)))

(defun b1-evaluators-evaluator-constraint-selectors (remaining index result args env)
  (declare (xargs :measure (nfix remaining)))
  (if (or (failure-p result) (zp remaining))
      result
    (b1-evaluators-evaluator-constraint-selectors
     (1- remaining) (1+ index)
     (b1-evaluators-evaluator-constraint-selector index result args env) args env)))

(defun b1-evaluators-constraint-operator-p (number)
  (if (rationalp number)
      (<= 8 number)
    '(:failure "failure" "")))

(defun b1-evaluators-evaluator-constraint-consequence (premise evaluator number call expected wrappers)
  (let ((lib (b1-evaluators-evaluator-lib evaluator)))
    (proof-with-checked-results
        ((fields (b1-evaluators-evaluator-constraint-common-expressions premise lib number))
         (extra (b1-evaluators-evaluator-constraint-branch-proof lib number premise call fields))
         (known (if extra (append fields (list extra)) fields))
         (operator-p (b1-evaluators-constraint-operator-p number))
         (rules (if operator-p
                    (proof-with-checked-results ((step (proof-term-at fields 1)))
                      (list (b1-logic-equal-to step)))
                  nil))
         (before (b1-evaluators-evaluator-open evaluator call known rules wrappers))
         (quoted (if (equal number 0) (b1-evaluators-evaluator-quote-arguments evaluator)
                   (cons nil evaluator)))
         (evaluator (cdr quoted))
         (after (if (equal number 0)
                    (b1-evaluators-evaluator-open evaluator expected known (list (car quoted)) wrappers)
                  (b1-logic-bookproof-normalize lib expected nil wrappers nil nil nil t)))
         (selected (if operator-p
                       (proof-with-checked-results ((parts (proof-list-of-length (cdr call) 2)))
                         (b1-evaluators-evaluator-constraint-selectors
                          (1- (len expected)) 0 (cons before evaluator) (list *library-cdr* (car parts))
                          (cadr parts)))
                     (cons before evaluator)))
         (evaluator (cdr selected))
         (proof (library-library-proof (b1-evaluators-evaluator-lib evaluator)))
         (reversed (proof-proof-symmetric proof after))
         (step (proof-proof-chain proof (car selected) (list reversed))))
      (cons step evaluator))))

(defun b1-evaluators-evaluator-constraint (evaluator number formula)
  (let* ((lib (b1-evaluators-evaluator-lib evaluator))
         (number (cond ((eq number t) 1) ((null number) 0) (t number))))
    (proof-with-checked-results
        ((implication (proof-list-of-length formula 3))
         (claim (proof-list-of-length (caddr implication) 3))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-evaluators-evaluator-constraint-consequence
                       premise evaluator number (cadr claim) (caddr claim)
                       (b1-evaluators-evaluator-functions evaluator)))
         (evaluator (cdr consequence))
         (lib (b1-evaluators-evaluator-lib evaluator))
         (step (b1-logic-bookproof-prove-implication-with-premise
                lib formula premise (car consequence))))
      (cons step evaluator))))
