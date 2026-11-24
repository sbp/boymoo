(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-clause-processors-process* (proof-sym "FLAG-IS-CP" "FLAG"))
(defconst *t3-book-clause-processors-ev* (proof-sym "FLAG-IS-CP-EV" "FLAG"))
(defconst *t3-book-clause-processors-flag-is* (proof-sym "FLAG-IS" "ACL2"))
(defconst *t3-book-clause-processors-conjoin-clauses* (proof-sym "CONJOIN-CLAUSES" "ACL2"))
(defconst *t3-book-clause-processors-conjoin* (proof-sym "CONJOIN" "ACL2"))
(defconst *t3-book-clause-processors-disjoin* (proof-sym "DISJOIN" "ACL2"))
(defconst *t3-book-clause-processors-disjoin2* (proof-sym "DISJOIN2" "ACL2"))
(defconst *t3-book-clause-processors-disjoin-list* (proof-sym "DISJOIN-LST" "ACL2"))
(defconst *t3-book-clause-processors-logic-nested* (proof-sym "LOGIC-TERM-LIST-LISTP" "ACL2"))
(defconst *t3-book-clause-processors-real-nested* (proof-sym "TERM-LIST-LISTP" "ACL2"))
(defconst *t3-book-clause-processors-functions-nested* (proof-sym "LOGIC-FNS-LIST-LISTP" "ACL2"))
(defconst *t3-book-clause-processors-logicp* (proof-sym "LOGICP" "ACL2"))
(defconst *t3-book-clause-processors-arities* (proof-sym "ARITIES-OKP" "ACL2"))
(defconst *t3-book-clause-processors-qtrue* (proof-quote (proof-quote *proof-t*)))
(defconst *t3-book-clause-processors-qfalse* (proof-quote (proof-quote *proof-nil*)))

(defun t3-book-clause-processors-empty-type (lib predicate world)
  (proof-with-checked-results
      ((normal (t3-book-spines-shallow lib (list predicate *proof-false* world) nil)))
    (proof-proof-true-from-eq (library-library-proof lib) normal)))

(defun t3-book-clause-processors-pair-type (lib predicate value world head tail)
  (proof-with-checked-results
      ((pair (t3-scan-typed-pair lib head tail))
       (normal (t3-book-spines-shallow lib (list predicate value world) nil)))
    (proof-proof-transport (library-library-proof lib) pair normal)))

(defun t3-book-clause-processors-symbol-proof (lib head)
  (let* ((proof (library-library-proof lib))
         (term (list *t3-book-lambdas-symbolp* head)))
    (if (not (member-eq (proof-proof-kind proof) '(:t3-book :book)))
        (t3-logic-libraryproofs-prove-formula lib term nil nil)
      (proof-with-checked-results
          ((equation (t3-book-values-book-proofs-normalize
                      (t3-book-values-make-book-proofs lib nil nil) term nil nil))
           (right (if equation (proof-rewritten-term equation) term))
           (result (t3-logic-libraryproofs-prove-formula lib right nil nil)))
        (if (and equation (not (equal right term)))
            (proof-proof-transport proof result equation)
          result)))))

(defun t3-book-clause-processors-marker-types-visit (n lib term world facts)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib))
        (target (list *t3-book-lambdas-real-term* term world))
        (logic (list *t3-book-lambdas-logic-fns* term world)))
    (cond
     ((zp n) '(:failure "Fuel" "t3-book-clause-processors-marker-types"))
     ((integerp term) '(:failure "failure" ""))
     (t
      (proof-with-checked-results ((parts (proof-list-of-length (cdr term) 2)))
        (let ((head (car parts))
              (arguments (cadr parts)))
          (if (equal head (proof-quote *proof-quote*))
              (proof-with-checked-results
                  ((first (t3-book-spines-shallow lib target nil))
                   (typed (proof-proof-true-from-eq proof first))
                   (second (t3-book-spines-shallow lib logic nil))
                   (allowed (proof-proof-true-from-eq proof second)))
                (list typed allowed))
            (proof-with-checked-results
                ((argument (proof-term-at arguments 1))
                 (types (t3-book-clause-processors-marker-types-visit (1- n) lib argument world facts))
                 (empty (t3-book-clause-processors-empty-type lib *t3-book-lambdas-real-list* world))
                 (typed (t3-book-clause-processors-pair-type
                         lib *t3-book-lambdas-real-list* arguments world (car types) empty))
                 (empty (t3-book-clause-processors-empty-type lib *t3-book-lambdas-logic-list* world))
                 (calls (t3-book-clause-processors-pair-type
                         lib *t3-book-lambdas-logic-list* arguments world (cadr types) empty))
                 (count (t3-logic-libraryproofs-normalize lib (list *library-len* arguments) nil
                                                         (list *library-len*)))
                 (arity (t3-book-function-terms-fact-at
                         facts (proof-eq (list *t3-book-function-terms-arity* head world) *proof-one*)))
                 (reversed (proof-proof-symmetric proof arity))
                 (arity (proof-proof-chain proof count (list reversed)))
                 (symbol (t3-book-clause-processors-symbol-proof lib head))
                 (not-quote (t3-logic-libraryproofs-prove-formula
                             lib (proof-neg (proof-eq head (proof-quote *proof-quote*))) (list *proof-not*) nil))
                 (result (t3-book-function-terms-symbol-application lib target symbol typed not-quote arity))
                 (known (t3-book-function-terms-fact-at
                         facts (list *t3-book-clause-processors-logicp* head world)))
                 (inspected (t3-book-spines-shallow lib logic (list known)))
                 (allowed (proof-proof-transport proof calls inspected)))
              (list result allowed)))))))))

(defun t3-book-clause-processors-marker-types (lib term world facts)
  (t3-book-clause-processors-marker-types-visit 1000000 lib term world facts))

(defun t3-book-clause-processors-wellformed-marker (lib parts clause world original)
  (let ((proof (library-library-proof lib))
        (typed (cadr parts)))
    (proof-with-checked-results
        ((literal (proof-step-first typed))
         (normalized (t3-book-spines-constructor-form
                      lib literal nil
                      (append *t3-book-spines-guards* (list *t3-book-clause-processors-arities*))))
         (rewritten (if normalized
                        (proof-proof-rewrite proof typed normalized '(1))
                      '(:failure "failure" "")))
         (components (t3-book-associations-components lib rewritten))
         (facts (t3-book-function-terms-fact-table components nil))
         (term (proof-term-at clause 1))
         (marker (t3-book-clause-processors-marker-types lib term world facts))
         (real (t3-book-clause-processors-pair-type
                lib *t3-book-lambdas-real-list* clause world (car marker) (car original)))
         (logic (t3-book-clause-processors-pair-type
                 lib *t3-book-lambdas-logic-list* clause world (cadr marker) (cadr original))))
      (list real logic))))

(defun t3-book-clause-processors-wellformed (lib name formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((target (proof-term-at formula 2))
         (args (if (integerp target)
                   '(:failure "failure" "")
                 (proof-list-of-length (cdr target) 2)))
         (guard (proof-term-at formula 1))
         (accepted (proof-proof-assume proof guard t)))
      (let* ((call (car args))
             (world (cadr args))
             (marker-added (proof-is-call call *t3-book-clause-processors-process*)))
        (proof-with-checked-results
            ((parts (if marker-added (proof-proof-conjunct proof accepted) (list accepted)))
             (source (proof-step-first (car parts)))
             (shallow (t3-book-spines-shallow lib source nil))
             (rewritten (proof-proof-rewrite proof (car parts) shallow '(1)))
             (original (proof-proof-conjunct proof rewritten))
             (cp (proof-proof-unfold proof call))
             (value (proof-rewritten-term cp))
             (clause (proof-term-at value 1))
             (lib (if marker-added (t3-book-lambdas-proper-length lib) lib))
             (original (if marker-added
                           (t3-book-clause-processors-wellformed-marker lib parts clause world original)
                         original)))
          (let ((proof (library-library-proof lib))
                (real *t3-book-clause-processors-real-nested*)
                (functions *t3-book-clause-processors-functions-nested*))
            (proof-with-checked-results
                ((empty (t3-book-clause-processors-empty-type lib real world))
                 (real (t3-book-clause-processors-pair-type lib real value world (car original) empty))
                 (empty (t3-book-clause-processors-empty-type lib functions world))
                 (functions (t3-book-clause-processors-pair-type lib functions value world (cadr original) empty))
                 (pair (t3-scan-typed-pair lib real functions))
                 (needed (t3-book-spines-shallow lib (list *t3-book-clause-processors-logic-nested* value world) nil))
                 (expanded (proof-proof-transport proof pair needed))
                 (reversed (proof-proof-symmetric proof cp))
                 (result (proof-proof-rewrite proof expanded reversed '(1 1)))
                 (entry (t3-book-function-terms-finish lib name formula result)))
              (cons entry lib))))))))

(defun t3-book-clause-processors-eval-application (lib term environment operator)
  (let ((number (cond ((equal operator *proof-quote*) 2)
                      ((equal operator *proof-if*) 8)
                      ((equal operator *t3-book-clause-processors-flag-is*) 9)
                      ((equal operator *proof-not*) 10)
                      (t nil)))
        (proof (library-library-proof lib)))
    (if (not number)
        '(:failure "MissingProofInput" "")
      (let ((rule (proof-sym (concatenate 'string "FLAG-IS-CP-EV-CONSTRAINT-" (decimal-text number)) "FLAG")))
        (proof-with-checked-results
            ((facts (proof-proof-fact proof rule (list (list *library-x* term)
                                                       (list (proof-sym "A" "ACL2") environment))))
             (present (t3-logic-libraryproofs-prove-formula lib (list *proof-consp* term) nil nil))
             (head (t3-logic-libraryproofs-prove-formula
                    lib (proof-eq (list *library-car* term) (proof-quote operator)) nil nil))
             (guard (t3-scan-typed-pair lib present head))
             (equation (proof-proof-modus-ponens proof facts guard))
             (value (proof-rewritten-term equation))
             (reduced (t3-logic-libraryproofs-normalize lib value nil nil)))
          (proof-proof-chain proof equation (list reduced)))))))

(defun t3-book-clause-processors-evaluated (lib equation environment)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first equation))
         (left (proof-term-at literal 1))
         (original (proof-proof-reflexive proof (list *t3-book-clause-processors-ev* left environment))))
      (proof-proof-rewrite proof original equation '(1 2 1)))))

(defun t3-book-clause-processors-false-disjunction-true (lib value right hypothesis evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((example (t3-logic-evidence-find evidence (proof-eq *library-y* *t3-book-clause-processors-qtrue*))))
      (if (car example)
          (proof-with-checked-results ((equation (t3-book-clause-processors-evaluated lib (car example) *library-z*)))
            (proof-proof-symmetric proof equation))
        (proof-with-checked-results
            ((known (t3-logic-evidence-require (cdr example)
                                               (proof-eq *library-x* *t3-book-clause-processors-qtrue*)))
             (quoted (t3-book-clause-processors-evaluated lib (car known) *library-z*))
             (evaluated (t3-book-clause-processors-eval-application
                         lib *t3-book-clause-processors-qtrue* *library-z* *proof-quote*))
             (yes (proof-proof-chain proof quoted (list evaluated)))
             (reversed (proof-proof-symmetric proof hypothesis))
             (clash (proof-proof-chain proof reversed (list yes)))
             (clash (t3-logic-libraryproofs-simplify-first lib clash nil nil)))
          (proof-proof-subsume proof clash
                               (proof-unique
                                (cons (proof-eq (list *t3-book-clause-processors-ev* value *library-z*) right)
                                      (proof-step-clause clash)))))))))

(defun t3-book-clause-processors-false-disjunction-branch (value tests lib right hypothesis)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((evidence (t3-logic-evidence-init lib tests nil nil)))
      (cond
       ((equal value *library-y*) (proof-proof-reflexive proof right))
       ((equal value *library-x*)
        (proof-with-checked-results
            ((known (t3-logic-evidence-require evidence (proof-eq *library-y* *t3-book-clause-processors-qfalse*)))
             (quoted (t3-book-clause-processors-evaluated lib (car known) *library-z*))
             (evaluated (t3-book-clause-processors-eval-application
                         lib *t3-book-clause-processors-qfalse* *library-z* *proof-quote*))
             (output (proof-proof-chain proof quoted (list evaluated)))
             (reversed (proof-proof-symmetric proof output)))
          (proof-proof-chain proof hypothesis (list reversed))))
       ((equal value *t3-book-clause-processors-qtrue*)
        (t3-book-clause-processors-false-disjunction-true lib value right hypothesis evidence))
       (t
        (proof-with-checked-results
            ((equation (t3-book-clause-processors-eval-application lib value *library-z* *proof-if*))
             (reduced (t3-book-spines-replace-value lib equation (list hypothesis)))
             (right (proof-rewritten-term reduced))
             (normalized (t3-logic-libraryproofs-normalize lib right nil nil)))
          (proof-proof-chain proof reduced (list normalized))))))))

(defund t3-book-clause-processors-false-disjunction-advance (request lib right hypothesis template)
  (proof-with-checked-results
      ((branch (t3-book-clause-processors-false-disjunction-branch
                (cadr request) (caddr request) lib right hypothesis)))
    (t3-book-term-collections-by-value-resume lib template request branch)))

(defun t3-book-clause-processors-false-disjunction-visit
    (n request lib right hypothesis template)
  (declare (xargs :measure (nfix n)))
  (cond
   ((failure-p request) request)
   ((not (eq (car request) :t3-book-term-collections-leaf)) request)
   ((zp n) '(:failure "Fuel" "t3-book-clause-processors-false-disjunction"))
   (t
    (t3-book-clause-processors-false-disjunction-visit
     (1- n) (t3-book-clause-processors-false-disjunction-advance request lib right hypothesis template)
     lib right hypothesis template))))

(defun t3-book-clause-processors-false-prefix (lib hypothesis)
  (let ((proof (library-library-proof lib))
        (whole (list *t3-book-clause-processors-disjoin* (list *proof-cons* *library-x* *library-y*)))
        (rest (list *t3-book-clause-processors-disjoin* *library-y*))
        (test (list *proof-consp* *library-y*)))
    (proof-with-checked-results
        ((present (proof-proof-assume proof test t))
         (atom (proof-proof-assume proof test nil))
         (shallow (t3-book-spines-shallow lib whole (list present)))
         (more (t3-book-clause-processors-evaluated lib shallow *library-z*))
         (law (library-library-cite lib "T3-EVAL-DISJOIN2-FALSE" (list *library-x* rest *library-z*)
                                   (list hypothesis)))
         (yes (proof-proof-chain proof more (list law)))
         (shallow (t3-book-spines-shallow lib whole (list atom)))
         (one (t3-book-clause-processors-evaluated lib shallow *library-z*))
         (shallow (t3-book-spines-shallow lib rest (list atom)))
         (empty (t3-book-clause-processors-evaluated lib shallow *library-z*))
         (false (t3-book-clause-processors-eval-application
                 lib *t3-book-clause-processors-qfalse* *library-z* *proof-quote*))
         (empty (proof-proof-chain proof empty (list false)))
         (reversed (proof-proof-symmetric proof empty))
         (no (proof-proof-chain proof one (list hypothesis reversed)))
         (result (proof-proof-cases proof test yes no))
         (claim (proof-step-first result))
         (assumption (proof-step-first hypothesis)))
      (library-library-lemma lib "T3-EVAL-DISJOIN-FALSE-PREFIX" claim result (list (proof-neg assumption))))))

(defun t3-book-clause-processors-false-disjunction (lib)
  (let* ((proof (library-library-proof lib))
         (left (list *t3-book-clause-processors-ev* *library-x* *library-z*))
         (right (list *t3-book-clause-processors-ev* *library-y* *library-z*))
         (template (proof-eq (list *t3-book-clause-processors-ev* *proof-result* *library-z*) right)))
    (proof-with-checked-results
        ((hypothesis (proof-proof-assume proof (proof-eq left *proof-false*) t))
         (source (proof-proof-unfold proof (list *t3-book-clause-processors-disjoin2* *library-x* *library-y*)))
         (value (proof-rewritten-term source))
         (request (t3-book-term-collections-by-value-start lib value nil))
         (result (t3-book-clause-processors-false-disjunction-visit
                  1000000 request lib right hypothesis template))
         (reversed (proof-proof-symmetric proof source))
         (result (proof-proof-rewrite-result proof result reversed template *proof-result*))
         (claim (proof-step-first result))
         (assumption (proof-step-first hypothesis))
         (lib (library-library-lemma lib "T3-EVAL-DISJOIN2-FALSE" claim result (list (proof-neg assumption)))))
      (t3-book-clause-processors-false-prefix lib hypothesis))))

(defun t3-book-clause-processors-marker-false (lib marker environment)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((logic (t3-book-clause-processors-eval-application lib marker environment *proof-not*))
         (result (proof-rewritten-term logic))
         (argument (proof-term-at result 1))
         (inside (proof-term-at argument 1))
         (gate (t3-book-clause-processors-eval-application lib inside environment *t3-book-clause-processors-flag-is*))
         (value (proof-rewritten-term gate))
         (normalized (t3-logic-libraryproofs-normalize lib value nil (list *t3-book-clause-processors-flag-is*)))
         (gate (proof-proof-chain proof gate (list normalized)))
         (logic (t3-book-spines-replace-value lib logic (list gate)))
         (result (proof-rewritten-term logic))
         (normalized (t3-logic-libraryproofs-normalize lib result nil (list *proof-not*))))
      (proof-proof-chain proof logic (list normalized)))))

(defun t3-book-clause-processors-erase-marker (lib opened environment evaluated-clause)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (proof-rewritten-term opened))
         (clause (proof-term-at value 1))
         (parts (if (integerp clause)
                    '(:failure "failure" "")
                  (proof-list-of-length (cdr clause) 2)))
         (false (t3-book-clause-processors-marker-false lib (car parts) environment))
         (law (library-library-cite lib "T3-EVAL-DISJOIN-FALSE-PREFIX"
                                   (list (car parts) (cadr parts) environment) (list false)))
         (rewritten (proof-proof-rewrite proof evaluated-clause law '(1))))
      (proof-proof-tidy proof rewritten))))

(defun t3-book-clause-processors-processor-correct (lib name formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((guard (proof-term-at formula 1))
         (assumption (proof-proof-assume proof guard t))
         (parts (proof-proof-conjunct proof assumption))
         (rest (proof-proof-conjunct proof (cadr parts)))
         (given (cadr rest))
         (literal (proof-step-first given))
         (environment (proof-term-at literal 2))
         (clauses (proof-term-at literal 1))
         (processor (proof-term-at clauses 1))
         (opened (proof-proof-unfold proof processor))
         (reflexive (proof-proof-reflexive proof clauses))
         (single (proof-proof-rewrite proof reflexive opened '(1 2 1)))
         (right (proof-rewritten-term single))
         (normalized (t3-logic-libraryproofs-normalize
                      lib right nil (list *t3-book-clause-processors-conjoin-clauses*
                                          *t3-book-clause-processors-disjoin-list* *t3-book-clause-processors-conjoin*
                                          *t3-logic-endp* *t3-logic-atom* *proof-not*)))
         (equation (proof-proof-chain proof single (list normalized)))
         (rewritten (proof-proof-rewrite proof given equation '(1 1)))
         (evaluated-clause (proof-proof-tidy proof rewritten)))
      (let ((marker-added (proof-is-call processor *t3-book-clause-processors-process*)))
        (proof-with-checked-results
            ((lib (if marker-added (t3-book-clause-processors-false-disjunction lib) lib))
             (evaluated-clause (if marker-added
                                   (t3-book-clause-processors-erase-marker lib opened environment evaluated-clause)
                                 evaluated-clause))
             (claim (proof-step-first evaluated-clause))
             (target (proof-term-at formula 2)))
          (if (equal claim target)
              (proof-with-checked-results
                  ((entry (t3-book-function-terms-finish lib name formula evaluated-clause)))
                (cons entry lib))
            '(:failure "Unsupported" "")))))))
