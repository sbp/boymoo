(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-clause-processors-a* '("sym" "ACL2" "A"))
(defconst *b1-clause-processors-n* '("sym" "ACL2" "N"))
(defconst *b1-clause-processors-mv-nth* '("sym" "ACL2" "MV-NTH"))
(defconst *b1-clause-processors-rec* '("sym" "ACL2" "MV-NTH-EVAL-REC"))
(defconst *b1-clause-processors-disjoin* '("sym" "ACL2" "DISJOIN"))
(defconst *b1-clause-processors-disjoin2* '("sym" "ACL2" "DISJOIN2"))
(defconst *b1-clause-processors-nth* '("sym" "COMMON-LISP" "NTH"))
(defconst *b1-clause-processors-mv-eval* '("sym" "ACL2" "EVAL-FOR-MV-NTH"))
(defconst *b1-clause-processors-flag-eval* '("sym" "FLAG" "FLAG-IS-CP-EV"))
(defconst *b1-clause-processors-termp* '("sym" "ACL2" "TERMP"))
(defconst *b1-clause-processors-term-listp* '("sym" "ACL2" "TERM-LISTP"))
(defconst *b1-clause-processors-term-list-listp* '("sym" "ACL2" "TERM-LIST-LISTP"))
(defconst *b1-clause-processors-logic-fnsp* '("sym" "ACL2" "LOGIC-FNSP"))
(defconst *b1-clause-processors-logic-fns-listp* '("sym" "ACL2" "LOGIC-FNS-LISTP"))
(defconst *b1-clause-processors-logic-fns-list-listp*
  '("sym" "ACL2" "LOGIC-FNS-LIST-LISTP"))
(defconst *b1-clause-processors-arities* '("sym" "ACL2" "ARITIES-OKP"))

(defun b1-clause-processors-literal-field (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b1-clause-processors-evaluator-equation
    (lib evaluator number syntax environment evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length evaluator 3))
         (rule (proof-sym (concatenate 'string (caddr parts) "-CONSTRAINT-" (decimal-text number))
                          (cadr parts)))
         (conditional (proof-proof-fact proof rule
                                        (list (list *library-x* syntax)
                                              (list *b1-clause-processors-a* environment))))
         (condition (b1-clause-processors-literal-field conditional 1))
         (guard (b1-logic-bookproof-normalize-proof lib condition evidence nil nil nil))
         (value (proof-proof-modus-ponens proof conditional guard))
         (right (b1-clause-processors-literal-field value 2))
         (reduced (b1-logic-bookproof-normalize lib right nil nil nil nil nil nil)))
      (proof-proof-chain proof value (list reduced)))))

(defun b1-clause-processors-mv-nth-equals-nth-align (cell extra using lib left right)
  (let ((proof (library-library-proof lib))
        (evidence (cons cell extra)))
    (proof-with-checked-results
        ((a (b1-revappend-open-list lib left evidence))
         (b (b1-revappend-open-list lib right evidence))
         (back (proof-proof-symmetric proof b)))
      (proof-proof-chain proof a (list using back)))))

(defun b1-clause-processors-mv-nth-equals-nth-install (lib)
  (let* ((proof (library-library-proof lib))
         (n *b1-clause-processors-n*)
         (x *library-x*)
         (left (list *b1-clause-processors-mv-nth* n x))
         (right (list *b1-clause-processors-nth* n x))
         (formula (proof-eq left right))
         (test (list *proof-consp* x))
         (zero (list *b1-logic-zp* n)))
    (proof-with-checked-results
        ((cons (proof-proof-assume proof test t))
         (atom (proof-proof-assume proof test nil))
         (induction (b1-induction-tree-induction-init lib formula x))
         (child (b1-induction-tree-induction-hypothesis
                 induction (list (cons x (list *library-cdr* x))
                                 (cons n (library-plus *proof-neg-one* n)))
                 (list (list test t))))
         (base (b1-clause-processors-mv-nth-equals-nth-align atom nil nil lib left right))
         (zero-true (proof-proof-assume proof zero t))
         (yes (b1-clause-processors-mv-nth-equals-nth-align
               cons (list zero-true) nil lib left right))
         (zero-false (proof-proof-assume proof zero nil))
         (no (b1-clause-processors-mv-nth-equals-nth-align
              cons (list zero-false) (car child) lib left right))
         (nonempty (proof-proof-cases proof zero yes no))
         (cases (proof-proof-cases proof test nonempty base))
         (step (b1-induction-tree-induction-finish (cdr child) cases)))
      (library-library-lemma lib "MV-NTH-IS-NTH" formula step nil))))

(defun b1-clause-processors-mv-nth-equals-nth (lib index items)
  (let ((name (proof-sym "SELF-MV-NTH-IS-NTH" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (library-inherited proof-proof-facts lib))
                  lib
                (b1-clause-processors-mv-nth-equals-nth-install lib)))
         (step (library-inherited proof-proof-fact lib name
                                  (list (list *b1-clause-processors-n* index)
                                        (list *library-x* items)))))
      (cons step lib))))

(defun b1-clause-processors-branch-facts-field (lib field)
  (proof-with-checked-results
      ((literal (proof-step-first field))
       (normalized (b1-logic-bookproof-normalize
                    lib literal nil (list *b1-logic-eq*) nil nil nil nil)))
    (library-inherited proof-proof-rewrite lib field normalized '(1))))

(defun b1-clause-processors-branch-facts-fields (n lib evidence)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "b1-clause-processors-branch-facts-fields")
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((literal (proof-step-first evidence))
           (otherwise (if (proof-is-call literal *proof-if*)
                          (proof-term-at literal 3)
                        nil)))
        (if (equal otherwise *proof-false*)
            (proof-with-checked-results
                ((fields (proof-proof-conjunct proof evidence))
                 (left (b1-clause-processors-branch-facts-field lib (car fields)))
                 (rest (b1-clause-processors-branch-facts-fields (1- n) lib (cadr fields))))
              (cons left rest))
          (proof-with-checked-results
              ((last (b1-clause-processors-branch-facts-field lib evidence)))
            (list last)))))))

(defun b1-clause-processors-branch-facts (lib tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((test (proof-list-of-length (car tests) 2))
         (evidence (library-inherited proof-proof-assume lib (car test) (cadr test)))
         (fields (if (cadr test)
                     (b1-clause-processors-branch-facts-fields 1000000 lib evidence)
                   (proof-with-checked-results
                       ((field (b1-clause-processors-branch-facts-field lib evidence)))
                     (list field))))
         (rest (b1-clause-processors-branch-facts lib (cdr tests))))
      (append fields rest))))

(defun b1-clause-processors-evidence-find (literal evidence)
  (if (endp evidence)
      nil
    (proof-with-checked-results ((first (proof-step-first (car evidence))))
      (if (equal literal first)
          (car evidence)
        (b1-clause-processors-evidence-find literal (cdr evidence))))))

(defun b1-clause-processors-mv-nth-evaluation-recursion-quoted
    (lib result output evaluation environment index evidence)
  (proof-with-checked-results
      ((exact (b1-clause-processors-evaluator-equation
               lib *b1-clause-processors-mv-eval* 2 result environment nil))
       (has-zp (b1-clause-processors-evidence-find (list *b1-logic-zp* index) evidence))
       (reduced (if has-zp
                    (proof-with-checked-results
                        ((opened (b1-revappend-open-list lib output evidence)))
                      (cons opened lib))
                  (proof-with-checked-results
                      ((args (proof-list-of-length (cdr output) 2)))
                    (b1-clause-processors-mv-nth-equals-nth lib (car args) (cadr args)))))
       (lib (cdr reduced))
       (proof (library-library-proof lib))
       (same (proof-proof-chain proof evaluation (list (car reduced))))
       (back (proof-proof-symmetric proof same))
       (step (proof-proof-chain proof exact (list back))))
    (cons step lib)))

(defun b1-clause-processors-mv-nth-evaluation-recursion-other
    (lib result output evaluation evidence induction driver prior syntax index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-list lib output evidence))
         (reduced (proof-proof-chain proof evaluation (list opened))))
      (if (proof-is-call result *b1-clause-processors-rec*)
          (proof-with-checked-results
              ((args (proof-list-of-length (take (min 2 (len (cdr result))) (cdr result)) 2))
               (hypothesis (b1-induction-tree-induction-hypothesis
                            induction
                            (table-put (list (cons syntax (cadr args))) index (car args))
                            (list (list driver t))))
               (cons (b1-clause-processors-evidence-find driver evidence)))
            (if (not cons)
                '(:failure "failure" "")
              (proof-with-checked-results
                  ((discharged (proof-proof-discharge proof (car hypothesis) cons))
                   (guard (proof-proof-chain proof prior (list reduced)))
                   (claim (proof-proof-modus-ponens proof discharged guard))
                   (back (proof-proof-symmetric proof reduced))
                   (step (proof-proof-chain proof claim (list back))))
                (cons step (cdr hypothesis)))))
        (proof-with-checked-results ((step (proof-proof-symmetric proof reduced)))
          (cons step induction))))))

(defun b1-clause-processors-mv-nth-evaluation-recursion-leaf-proof
    (lib result original prior syntax index environment expected evidence induction driver)
  (if (equal result original)
      (list prior induction lib)
    (proof-with-checked-results
        ((first (if (proof-is-call result *proof-cons*) (proof-term-at result 1) nil))
         (quoted (equal first *b1-evaluators-quote-name*))
         (equation (b1-clause-processors-evaluator-equation
                    lib *b1-clause-processors-mv-eval* (if quoted 2 9)
                    syntax environment evidence))
         (evaluation (b1-revappend-lift-argument lib expected equation 2))
         (output (b1-clause-processors-literal-field evaluation 2)))
      (if quoted
          (proof-with-checked-results
              ((quoted-proof (b1-clause-processors-mv-nth-evaluation-recursion-quoted
                              lib result output evaluation environment index evidence)))
            (list (car quoted-proof)
                  (b1-induction-tree-induction-with-lib induction (cdr quoted-proof))
                  (cdr quoted-proof)))
        (proof-with-checked-results
            ((other (b1-clause-processors-mv-nth-evaluation-recursion-other
                     lib result output evaluation evidence induction driver prior syntax index)))
          (list (car other) (cdr other) lib))))))

(defun b1-clause-processors-mv-nth-evaluation-recursion-consequence-leaf
    (value tests lib original prior syntax index environment expected induction driver template)
  (proof-with-checked-results
      ((evidence (b1-clause-processors-branch-facts lib tests))
       (normalized (b1-logic-bookproof-normalize lib value nil nil nil nil nil nil))
       (result (b1-clause-processors-literal-field normalized 2))
       (answer (b1-clause-processors-mv-nth-evaluation-recursion-leaf-proof
                lib result original prior syntax index environment expected evidence induction driver))
       (lib (caddr answer))
       (proof (library-library-proof lib))
       (back (proof-proof-symmetric proof normalized))
       (step (proof-proof-rewrite-result proof (car answer) back template *proof-result*)))
    (list step (cadr answer) lib)))

(defun b1-clause-processors-mv-nth-evaluation-recursion-leaves
    (requests lib original prior syntax index environment expected induction driver template)
  (if (endp requests)
      (list nil induction lib)
    (proof-with-checked-results
        ((request (car requests))
         (answer (b1-clause-processors-mv-nth-evaluation-recursion-consequence-leaf
                  (car request) (cadr request) lib original prior syntax index environment
                  expected induction driver template))
         (rest (b1-clause-processors-mv-nth-evaluation-recursion-leaves
                (cdr requests) (caddr answer) original prior syntax index environment
                expected (cadr answer) driver template)))
      (list (cons (cons request (car answer)) (car rest)) (cadr rest) (caddr rest)))))

(defun b1-clause-processors-mv-nth-evaluation-recursion-consequence
    (prior lib original syntax index environment expected induction driver template opened)
  (proof-with-checked-results
      ((value (b1-clause-processors-literal-field opened 2))
       (requests (library-inherited proof-proof-by-value-leaves lib value nil))
       (answers (b1-clause-processors-mv-nth-evaluation-recursion-leaves
                 requests lib original prior syntax index environment expected induction driver template))
       (lib (caddr answers))
       (proof (library-library-proof lib))
       (chosen (proof-proof-by-value proof value template (car answers) nil))
       (back (proof-proof-symmetric proof opened))
       (step (proof-proof-rewrite-result proof chosen back template *proof-result*)))
    (list step (cadr answers) lib)))

(defun b1-clause-processors-mv-nth-evaluation-recursion (lib formula)
  (proof-with-checked-results
      ((formula-fields (proof-list-of-length formula 3))
       (conclusion (proof-list-of-length (caddr formula-fields) 3))
       (transformed (proof-list-of-length (cadr conclusion) 3))
       (call (cadr transformed))
       (arguments (proof-list-of-length call 4)))
    (let* ((index (cadr arguments))
           (syntax (caddr arguments))
           (original (cadddr arguments))
           (expected (caddr conclusion))
           (environment (caddr transformed))
           (driver (list *proof-consp* syntax))
           (induction (b1-induction-tree-induction-init lib formula syntax))
           (template (proof-eq (list *b1-clause-processors-mv-eval* *proof-result* environment)
                               expected)))
      (proof-with-checked-results
          ((opened (library-inherited proof-proof-unfold lib call))
           (prior (b1-logic-bookproof-prove-implication-premise lib formula))
           (answer (b1-clause-processors-mv-nth-evaluation-recursion-consequence
                    prior lib original syntax index environment expected induction driver template opened))
           (lib (caddr answer))
           (case (b1-logic-bookproof-prove-implication-with-premise lib formula prior (car answer)))
           (step (b1-induction-tree-induction-finish (cadr answer) case)))
        (cons step lib)))))

(defun b1-clause-processors-mv-nth-evaluation-meta-leaf
    (value tests lib original original-eval environment)
  (let ((proof (library-library-proof lib)))
    (if (equal value original)
        (proof-proof-reflexive proof original-eval)
      (proof-with-checked-results
          ((evidence (b1-clause-processors-branch-facts lib tests))
           (evaluated (b1-clause-processors-evaluator-equation
                       lib *b1-clause-processors-mv-eval* 8 original environment evidence))
           (index (b1-evaluators-argument original 1))
           (quoted-index (b1-clause-processors-evaluator-equation
                          lib *b1-clause-processors-mv-eval* 2 index environment evidence))
           (actual (proof-proof-rewrite proof evaluated quoted-index '(1 2 1)))
           (literal (proof-step-first actual))
           (right (proof-term-at literal 2))
           (expected (proof-eq (list *b1-clause-processors-mv-eval* value environment) right))
           (lemma (b1-logic-bookproof-from-fact
                   lib (proof-sym "EVAL-FOR-MV-NTH-REC-THM" "ACL2")
                   (list *library-implies* literal expected)))
           (known (proof-proof-modus-ponens proof lemma actual))
           (back (proof-proof-symmetric proof known)))
        (proof-proof-chain proof actual (list back))))))

(defun b1-clause-processors-mv-nth-evaluation-meta-leaves
    (requests lib original original-eval environment)
  (if (endp requests)
      nil
    (proof-with-checked-results
        ((request (car requests))
         (step (b1-clause-processors-mv-nth-evaluation-meta-leaf
                (car request) (cadr request) lib original original-eval environment))
         (rest (b1-clause-processors-mv-nth-evaluation-meta-leaves
                (cdr requests) lib original original-eval environment)))
      (cons (cons request step) rest))))

(defun b1-clause-processors-mv-nth-evaluation-meta (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((formula-fields (proof-list-of-length formula 3))
         (original-eval (cadr formula-fields))
         (original-fields (proof-list-of-length original-eval 3))
         (original (cadr original-fields))
         (environment (caddr original-fields))
         (call (proof-term-at (caddr formula-fields) 1))
         (view (proof-proof-unfold proof call))
         (value (b1-clause-processors-literal-field view 2))
         (template (proof-eq original-eval
                             (list *b1-clause-processors-mv-eval* *proof-result* environment)))
         (requests (proof-proof-by-value-leaves proof value nil))
         (leaves (b1-clause-processors-mv-nth-evaluation-meta-leaves
                  requests lib original original-eval environment))
         (result (proof-proof-by-value proof value template leaves nil))
         (back (proof-proof-symmetric proof view)))
      (proof-proof-rewrite-result proof result back template *proof-result*))))

(defun b1-clause-processors-one-clause-conjunction-empty (term lib map-clauses)
  (if (proof-is-call term map-clauses)
      (proof-with-checked-results ((items (proof-term-at term 1)))
        (if (equal items *proof-false*)
            (b1-revappend-open-list lib term nil)
          nil))
    nil))

(defun b1-clause-processors-flag-processor-wellformed-consequence-quoted-arity (term lib)
  (if (proof-is-call term *b1-clause-processors-arities*)
      (proof-with-checked-results ((table (proof-term-at term 1)))
        (if (proof-is-call table *proof-quote*)
            (library-inherited proof-proof-unfold lib term)
          nil))
    nil))

(defun b1-clause-processors-normalize-with-rule-visit
    (n result lib term unfold id inspect-branches replies)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "b1-clause-processors-normalize-with-rule-visit"))
        ((failure-p result) result)
        ((not (b1-logic-call-p result)) (car result))
        (t (let* ((callback-term (b1-logic-call-term result))
                  (callback-lib (b1-logic-call-library result))
                  (step (if (eq id :quoted-arity)
                            (b1-clause-processors-flag-processor-wellformed-consequence-quoted-arity
                             callback-term callback-lib)
                          (b1-clause-processors-one-clause-conjunction-empty
                           callback-term callback-lib id)))
                  (reply (if (failure-p step) step (cons step callback-lib)))
                  (replies (append replies (list reply))))
             (if (equal n 1)
                 '(:failure "Fuel" "b1-clause-processors-normalize-with-rule-visit")
               (b1-clause-processors-normalize-with-rule-visit
                (1- n)
                (b1-logic-bookproof-normalize-with-library
                 lib term nil unfold (list (list :callback id)) nil nil inspect-branches replies)
                lib term unfold id inspect-branches replies))))))

(defun b1-clause-processors-normalize-with-rule (n lib term unfold id inspect-branches replies)
  (if (zp n)
      '(:failure "Fuel" "b1-clause-processors-normalize-with-rule")
    (b1-clause-processors-normalize-with-rule-visit
     n (b1-logic-bookproof-normalize-with-library
        lib term nil unfold (list (list :callback id)) nil nil inspect-branches replies)
     lib term unfold id inspect-branches replies)))

(defun b1-clause-processors-one-clause-conjunction (lib call)
  (let ((proof (library-library-proof lib))
        (map-clauses (proof-sym "DISJOIN-LST" "ACL2"))
        (conjoin (proof-sym "CONJOIN" "ACL2"))
        (reducers (list *b1-logic-endp* *b1-logic-atom* *proof-not*)))
    (proof-with-checked-results
        ((mapped (proof-proof-unfold proof call))
         (right (b1-clause-processors-literal-field mapped 2))
         (subcall (proof-term-at right 1))
         (mapping (b1-clause-processors-normalize-with-rule
                   1000000 lib subcall (cons map-clauses reducers) map-clauses nil nil))
         (conjoined (proof-proof-rewrite proof mapped mapping '(1 2 1)))
         (value (b1-clause-processors-literal-field conjoined 2))
         (normalized (b1-logic-bookproof-normalize
                      lib value nil (cons conjoin reducers) nil nil nil nil)))
      (proof-proof-chain proof conjoined (list normalized)))))

(defun b1-clause-processors-flag-clause-equation-disjunction-different
    (quoted lib negative-flag)
  (let ((proof (library-library-proof lib))
        (same (proof-eq negative-flag quoted)))
    (proof-with-checked-results
        ((left (b1-logic-bookproof-normalize lib (list *library-car* negative-flag)
                                            nil nil nil nil nil nil))
         (assumed (proof-proof-assume proof same t))
         (left (proof-proof-rewrite proof left assumed '(1 1 1)))
         (term (b1-clause-processors-literal-field left 1))
         (reduced (b1-logic-bookproof-normalize lib term nil nil nil nil nil nil))
         (left (proof-proof-rewrite proof left reduced '(1 1)))
         (simplified (proof-proof-simplify-first proof left nil nil)))
      (proof-proof-front proof simplified (proof-neg same)))))

(defun b1-clause-processors-flag-clause-equation-disjunction-leaf
    (value tests lib tail right negative-flag truth-quote empty-quote never environment)
  (declare (ignore tests))
  (let ((proof (library-library-proof lib))
        (evaluator *b1-clause-processors-flag-eval*))
    (cond
     ((equal value tail) (proof-proof-reflexive proof right))
     ((or (equal value negative-flag) (equal value truth-quote))
      (let ((quoted (if (equal value negative-flag) empty-quote truth-quote)))
        (proof-with-checked-results
            ((same (proof-proof-assume proof (proof-eq tail quoted) t))
             (reflexive (proof-proof-reflexive proof right))
             (target (proof-proof-rewrite proof reflexive same '(1 2 1)))
             (right (b1-clause-processors-literal-field target 2))
             (syntax (proof-term-at right 1))
             (evaluated (b1-clause-processors-evaluator-equation
                         lib evaluator 2 syntax environment nil))
             (target (proof-proof-chain proof target (list evaluated)))
             (given (if (equal value negative-flag)
                        never
                      (b1-clause-processors-evaluator-equation
                       lib evaluator 2 value environment nil)))
             (back (proof-proof-symmetric proof target)))
          (proof-proof-chain proof given (list back)))))
     (t (proof-with-checked-results
            ((reduced (b1-clause-processors-evaluator-equation
                       lib evaluator 8 value environment nil))
             (right (b1-clause-processors-literal-field reduced 2))
             (normalized (b1-logic-bookproof-normalize
                          lib right nil nil (list (b1-logic-equal-to never)) nil nil nil)))
          (proof-proof-chain proof reduced (list normalized)))))))

(defun b1-clause-processors-flag-clause-equation-disjunction-leaves
    (requests lib tail right negative-flag truth-quote empty-quote never environment)
  (if (endp requests)
      nil
    (proof-with-checked-results
        ((request (car requests))
         (step (b1-clause-processors-flag-clause-equation-disjunction-leaf
                (car request) (cadr request) lib tail right negative-flag
                truth-quote empty-quote never environment))
         (rest (b1-clause-processors-flag-clause-equation-disjunction-leaves
                (cdr requests) lib tail right negative-flag truth-quote empty-quote never environment)))
      (cons (cons request step) rest))))

(defun b1-clause-processors-flag-clause-equation-disjunction
    (tail lib negative-flag truth-quote empty-quote never environment)
  (let* ((proof (library-library-proof lib))
         (evaluator *b1-clause-processors-flag-eval*)
         (call (list *b1-clause-processors-disjoin2* negative-flag tail))
         (right (list evaluator tail environment))
         (template (proof-eq (list evaluator *proof-result* environment) right)))
    (proof-with-checked-results
        ((view (proof-proof-unfold proof call))
         (different-true (b1-clause-processors-flag-clause-equation-disjunction-different
                          truth-quote lib negative-flag))
         (different-nil (b1-clause-processors-flag-clause-equation-disjunction-different
                         empty-quote lib negative-flag))
         (left (b1-clause-processors-literal-field view 1))
         (opened (b1-logic-bookproof-normalize lib left (list different-true different-nil)
                                              (list *b1-clause-processors-disjoin2*)
                                              nil nil nil nil))
         (value (b1-clause-processors-literal-field opened 2))
         (requests (proof-proof-by-value-leaves proof value nil))
         (leaves (b1-clause-processors-flag-clause-equation-disjunction-leaves
                  requests lib tail right negative-flag truth-quote empty-quote never environment))
         (result (proof-proof-by-value proof value template leaves nil))
         (back (proof-proof-symmetric proof opened)))
      (proof-proof-rewrite-result proof result back template *proof-result*))))

(defun b1-clause-processors-flag-clause-equation-expose (cell lib left environment)
  (proof-with-checked-results
      ((have (b1-logic-bookproof-normalize
              lib left (list cell) (list *b1-clause-processors-disjoin* *b1-logic-endp*
                                         *b1-logic-atom* *proof-not*) nil nil nil nil)))
    (b1-revappend-lift-argument lib (list *b1-clause-processors-flag-eval* left environment) have 1)))

(defun b1-clause-processors-flag-clause-equation (lib selected original environment)
  (let ((proof (library-library-proof lib))
        (evaluator *b1-clause-processors-flag-eval*))
    (proof-with-checked-results
        ((parts (proof-list-of-length selected 3))
         (negative-flag (cadr parts))
         (clause (caddr parts))
         (operands (proof-term-at negative-flag 2))
         (flag (proof-term-at operands 1))
         (never (b1-clause-processors-evaluator-equation lib evaluator 10 negative-flag environment nil))
         (defined (b1-clause-processors-evaluator-equation lib evaluator 9 flag environment nil))
         (definition (b1-clause-processors-literal-field defined 2))
         (definition (proof-proof-unfold proof definition))
         (defined (proof-proof-chain proof defined (list definition)))
         (value (b1-clause-processors-literal-field never 2))
         (reduced (b1-logic-bookproof-normalize
                   lib value nil (list *proof-not*) (list (b1-logic-equal-to defined)) nil nil nil))
         (never (proof-proof-chain proof never (list reduced)))
         (empty-quote (proof-quote (list *proof-quote* *proof-nil*)))
         (truth-quote (proof-quote (list *proof-quote* *proof-t*)))
         (right (list evaluator original environment))
         (left (list *b1-clause-processors-disjoin* selected))
         (is-cons (list *proof-consp* clause))
         (cons (proof-proof-assume proof is-cons t))
         (atom (proof-proof-assume proof is-cons nil))
         (left-cons (b1-clause-processors-flag-clause-equation-expose cons lib left environment))
         (disjunction (b1-clause-processors-flag-clause-equation-disjunction
                       original lib negative-flag truth-quote empty-quote never environment))
         (yes (proof-proof-chain proof left-cons (list disjunction)))
         (missing (b1-revappend-open-list lib original (list atom)))
         (target (b1-revappend-lift-argument lib right missing 1))
         (right (b1-clause-processors-literal-field target 2))
         (syntax (proof-term-at right 1))
         (evaluated (b1-clause-processors-evaluator-equation lib evaluator 2 syntax environment nil))
         (target (proof-proof-chain proof target (list evaluated)))
         (left-atom (b1-clause-processors-flag-clause-equation-expose atom lib left environment))
         (back (proof-proof-symmetric proof target))
         (no (proof-proof-chain proof left-atom (list never back))))
      (proof-proof-cases proof is-cons yes no))))

(defun b1-clause-processors-flag-processor-correct-consequence (premise lib flattened equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fields (b1-logic-bookproof-split-conjuncts lib premise))
         (fields (proof-list-of-length fields 3))
         (reduced (proof-proof-rewrite proof (caddr fields) flattened '(1 1))))
      (proof-proof-rewrite proof reduced equation '(1)))))

(defun b1-clause-processors-flag-processor-correct (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (guard (proof-term-at (cadr parts) 2))
         (call (proof-term-at guard 2))
         (call (proof-list-of-length call 3))
         (conjunction (cadr call))
         (processor-call (proof-term-at conjunction 1))
         (processor (proof-proof-unfold proof processor-call))
         (reflexive (proof-proof-reflexive proof conjunction))
         (normalized (proof-proof-rewrite proof reflexive processor '(1 2 1)))
         (flatten-call (b1-clause-processors-literal-field normalized 2))
         (flattening (b1-clause-processors-one-clause-conjunction lib flatten-call))
         (flattened (proof-proof-chain proof normalized (list flattening)))
         (right (b1-clause-processors-literal-field flattened 2))
         (selected (proof-term-at right 1))
         (original (proof-term-at (caddr parts) 1))
         (equation (b1-clause-processors-flag-clause-equation lib selected original (caddr call)))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (step (b1-clause-processors-flag-processor-correct-consequence premise lib flattened equation)))
      (b1-logic-bookproof-prove-implication-with-premise lib formula premise step))))

(defun b1-clause-processors-recognised-list (lib predicate items world head tail)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((branch (b1-revappend-open-list lib (list predicate items world) (list head)))
         (tail (if tail
                   tail
                 (proof-with-checked-results
                     ((right (b1-clause-processors-literal-field branch 2)))
                   (b1-logic-bookproof-normalize-proof
                    lib right nil (list predicate *b1-logic-atom* *b1-logic-endp* *proof-not*)
                    nil nil)))))
      (proof-proof-transport proof tail branch))))

(defun b1-clause-processors-unary-application-type
    (lib term world arity logical argument-term argument-logic)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((operands (proof-term-at term 2))
         (type-list (b1-clause-processors-recognised-list
                     lib *b1-clause-processors-term-listp* operands world argument-term nil))
         (logical-list (b1-clause-processors-recognised-list
                        lib *b1-clause-processors-logic-fns-listp* operands world argument-logic nil))
         (is-cons (b1-revappend-cons-value lib operands))
         (rule (proof-proof-fact proof "consp-not-stringp" (list (list *library-x* operands))))
         (not-string (proof-proof-modus-ponens proof rule is-cons))
         (length (proof-cl "LENGTH"))
         (empty-length (b1-revappend-open-list lib (list *library-len* *proof-false*) nil))
         (unit (b1-logic-bookproof-normalize
                lib (list length operands) (list not-string)
                (list length *library-len* *b1-logic-atom* *b1-logic-endp* *proof-not*)
                (list (b1-logic-equal-to empty-length)) nil nil nil))
         (size (b1-clause-processors-literal-field unit 2)))
      (if (not (equal size *proof-one*))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((termp *b1-clause-processors-termp*)
             (logic-fnsp *b1-clause-processors-logic-fnsp*)
             (term-type (b1-logic-bookproof-normalize-proof
                         lib (list termp term world) (list type-list)
                         (list termp *b1-logic-atom* *b1-logic-eq* *b1-logic-eql* *proof-not*)
                         (list (b1-logic-equal-to arity) (b1-logic-equal-to unit)) nil))
             (logic-type (b1-logic-bookproof-normalize-proof
                          lib (list logic-fnsp term world) (list logical-list logical)
                          (list logic-fnsp *b1-logic-atom* *b1-logic-eq* *proof-not*) nil nil)))
          (list term-type logic-type))))))

(defun b1-clause-processors-flag-processor-wellformed-consequence
    (premise lib quoted-name world flag flag-literal sole-clause value claim transformed)
  (let ((proof (library-library-proof lib))
        (termp *b1-clause-processors-termp*)
        (logic-fnsp *b1-clause-processors-logic-fnsp*)
        (term-listp *b1-clause-processors-term-listp*)
        (logic-listp *b1-clause-processors-logic-fns-listp*))
    (proof-with-checked-results
        ((original-and-available (proof-proof-conjunct proof premise))
         (original (car original-and-available))
         (available (cadr original-and-available))
         (original-term (proof-step-first original))
         (opened (proof-proof-unfold proof original-term))
         (original (proof-proof-rewrite proof original opened '(1)))
         (terms-and-logical (proof-proof-conjunct proof original))
         (available-term (proof-step-first available))
         (known (b1-clause-processors-normalize-with-rule
                 1000000 lib available-term (list *b1-logic-atom* *b1-logic-endp* *proof-not*)
                 :quoted-arity t nil))
         (available (proof-proof-rewrite proof available known '(1)))
         (facts (b1-logic-bookproof-split-conjuncts lib available))
         (facts (proof-list-of-length (take (min 4 (len facts)) facts) 4))
         (quote-term (b1-logic-bookproof-normalize-proof
                      lib (list termp quoted-name world) nil
                      (list termp *b1-logic-eq* (proof-cl "NULL") *b1-logic-atom* *proof-not*) nil nil))
         (quote-logic (b1-logic-bookproof-normalize-proof
                       lib (list logic-fnsp quoted-name world) nil
                       (list logic-fnsp *b1-logic-atom* *b1-logic-eq* *proof-not*) nil nil))
         (inner (b1-clause-processors-unary-application-type
                 lib flag world (caddr facts) (cadddr facts) quote-term quote-logic))
         (outer (b1-clause-processors-unary-application-type
                 lib flag-literal world (car facts) (cadr facts) (car inner) (cadr inner)))
         (new-terms (b1-clause-processors-recognised-list
                     lib term-listp sole-clause world (car outer) (car terms-and-logical)))
         (new-logic (b1-clause-processors-recognised-list
                     lib logic-listp sole-clause world (cadr outer) (cadr terms-and-logical)))
         (nested-terms (b1-clause-processors-recognised-list
                        lib *b1-clause-processors-term-list-listp* value world new-terms nil))
         (nested-logic (b1-clause-processors-recognised-list
                        lib *b1-clause-processors-logic-fns-list-listp* value world new-logic nil))
         (target (proof-proof-unfold proof (list (car claim) value world)))
         (right (b1-clause-processors-literal-field target 2))
         (supported (b1-logic-bookproof-normalize-proof
                     lib right (list nested-terms nested-logic) nil nil nil))
         (transported (proof-proof-transport proof supported target)))
      (library-library-transport-argument lib transported transformed 1))))

(defun b1-clause-processors-flag-processor-wellformed (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr parts) 3))
       (transformed (library-inherited proof-proof-unfold lib (cadr claim)))
       (value (b1-clause-processors-literal-field transformed 2))
       (sole-clause (proof-term-at value 1))
       (flag-literal (proof-term-at sole-clause 1))
       (operands (proof-term-at flag-literal 2))
       (flag (proof-term-at operands 1))
       (operands (proof-term-at flag 2))
       (quoted-name (proof-term-at operands 1))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (step (b1-clause-processors-flag-processor-wellformed-consequence
              premise lib quoted-name (caddr claim) flag flag-literal sole-clause value claim transformed)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise step)))
