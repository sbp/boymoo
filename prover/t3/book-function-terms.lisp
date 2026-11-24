(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-function-terms-arity* (proof-sym "ARITY" "ACL2"))

(defun t3-book-function-terms-fact-table (steps facts)
  (if (endp steps)
      facts
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (t3-book-function-terms-fact-table
       (cdr steps) (table-put facts literal (car steps))))))

(defun t3-book-function-terms-fact-at (facts term)
  (let ((entry (assoc-equal term facts)))
    (if entry
        (cdr entry)
      '(:failure "MissingProofInput" ""))))

(defun t3-book-function-terms-theorem-from (lib name target facts)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((clause (t3-book-function-terms-fact-at (proof-proof-facts proof) name))
         (literal (proof-term-at clause 0))
         (pattern (proof-term-at literal 2))
         (matched (t3-book-theorems-match pattern target nil)))
      (if (not (car matched))
          '(:failure "Unsupported" "")
        (proof-with-checked-results
            ((theorem (proof-proof-fact proof name (table-items (cdr matched))))
             (source (proof-step-first theorem))
             (condition (proof-term-at source 1))
             (known (t3-book-function-terms-fact-table facts nil))
             (guard (t3-book-lambdas-required lib condition known)))
          (proof-proof-modus-ponens proof theorem guard))))))

(defun t3-book-function-terms-finish (lib name formula proof)
  (proof-with-checked-results ((result (t3-book-lemmas-implication lib formula proof)))
    (proof-proof-entry "theorem" name (list name) (list result))))

(defun t3-book-function-terms-fn-from-term (lib name formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((guard (proof-term-at formula 1))
         (assumption (proof-proof-assume proof guard t))
         (parts (t3-book-associations-components lib assumption))
         (parts (proof-list-of-length parts 3))
         (target (proof-term-at formula 2))
         (denied (t3-book-lambdas-not-symbol lib (caddr parts)))
         (equation (t3-book-lambdas-inspect lib target (list denied)))
         (meaning (proof-rewritten-term equation))
         (lambda-type (t3-book-function-terms-theorem-from
                       lib *t3-book-lambdas-extract-real* meaning parts))
         (result (proof-proof-transport proof lambda-type equation)))
      (t3-book-function-terms-finish lib name formula result))))

(defun t3-book-function-terms-lambda-components (lib typed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((recognizer (proof-step-first typed))
         (equation (t3-book-lambdas-inspect lib recognizer nil))
         (rewritten (proof-proof-rewrite proof typed equation '(1)))
         (clauses (proof-proof-tidy proof rewritten))
         (parts (t3-book-associations-components lib clauses)))
      (t3-book-function-terms-fact-table parts nil))))

(defun t3-book-function-terms-fn-from-lambda (lib name formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((guard (proof-term-at formula 1))
         (typed (proof-proof-assume proof guard t))
         (fields (t3-book-function-terms-lambda-components lib typed))
         (literal (proof-step-first typed))
         (operator (proof-term-at literal 1))
         (head (t3-book-lambdas-present-operator lib operator fields))
         (target (proof-term-at formula 2))
         (denied (t3-book-lambdas-not-symbol lib head))
         (equation (t3-book-lambdas-inspect lib target (list denied)))
         (result (proof-proof-transport proof typed equation)))
      (t3-book-function-terms-finish lib name formula result))))

(defun t3-book-function-terms-pseudo-fn-from-term (lib name formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((guard (proof-term-at formula 1))
         (assumption (proof-proof-assume proof guard t))
         (parts (proof-proof-conjunct proof assumption))
         (target (proof-term-at formula 2))
         (term (proof-term-at target 1)))
      (let ((test (list *t3-book-lambdas-symbolp* term)))
        (proof-with-checked-results
            ((positive (proof-proof-assume proof test t))
             (negative (proof-proof-assume proof test nil))
             (positive-equation (t3-book-lambdas-inspect lib target (list positive)))
             (yes (proof-proof-transport proof positive positive-equation))
             (equation (t3-book-lambdas-inspect lib target (list negative)))
             (excluded (t3-book-evaluators-quote-excluded lib term negative))
             (meaning (proof-rewritten-term equation))
             (recognized (t3-book-lambdas-pseudo-lambda-from-term
                          lib (car parts) (cadr parts) excluded negative meaning))
             (no (proof-proof-transport proof recognized equation))
             (result (proof-proof-cases proof test yes no)))
          (t3-book-function-terms-finish lib name formula result))))))

(defun t3-book-function-terms-nonnil-integer (lib typed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first typed))
         (value (proof-term-at literal 1))
         (denied (proof-proof-assume proof value nil))
         (missing (t3-book-lemmas-nil-value lib denied))
         (rewritten (proof-proof-rewrite proof typed missing '(1 1)))
         (contradiction (t3-logic-libraryproofs-simplify-first lib rewritten nil nil)))
      (proof-proof-front proof contradiction value))))

(defund t3-book-function-terms-book-check (book value evidence)
  (t3-book-values-book-proofs-normalize book value evidence *t3-book-lambdas-definitions*))

(defund t3-book-function-terms-finish-book-checks (book equation evidence)
  (let ((proof (library-library-proof (t3-book-values-book-proofs-library book))))
    (if (not equation)
        nil
      (proof-with-checked-results
          ((right (proof-rewritten-term equation))
           (normalized (t3-book-function-terms-book-check book right evidence)))
        (proof-proof-chain proof equation (list normalized))))))

(defund t3-book-function-terms-rewrite-check (book value equation branch position)
  (if (not branch)
      equation
    (let ((proof (library-library-proof (t3-book-values-book-proofs-library book))))
      (proof-with-checked-results ((previous (or equation (proof-proof-reflexive proof value))))
        (proof-proof-rewrite proof previous branch (list 1 2 position))))))

(mutual-recursion
 (defun t3-book-function-terms-book-checks (n book value evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "t3-book-function-terms-book-checks")
     (proof-with-checked-results
         ((equation (t3-book-function-terms-book-check book value evidence))
          (current (if equation (proof-rewritten-term equation) value)))
       (if (not (proof-is-call current *proof-if*))
           equation
         (proof-with-checked-results
             ((rewritten (t3-book-function-terms-book-checks-branches
                          (1- n) book value current evidence '(1 2 3) equation)))
           (t3-book-function-terms-finish-book-checks book rewritten evidence))))))

 (defun t3-book-function-terms-book-checks-branches (n book value current evidence positions equation)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t3-book-function-terms-book-checks"))
    ((endp positions) equation)
    (t
     (proof-with-checked-results
         ((branch (proof-term-at current (car positions)))
          (branch (t3-book-function-terms-book-checks (1- n) book branch evidence))
          (equation (t3-book-function-terms-rewrite-check
                     book value equation branch (car positions))))
       (t3-book-function-terms-book-checks-branches
        (1- n) book value current evidence (cdr positions) equation))))))

(defun t3-book-function-terms-normalize-checks (lib value evidence)
  (if (member-eq (proof-proof-kind (library-library-proof lib)) '(:t3-book :book))
      (t3-book-function-terms-book-checks
       1000000 (t3-book-values-make-book-proofs lib nil nil) value evidence)
    (t3-book-lambdas-normalize-checks lib value evidence)))

(defun t3-book-function-terms-symbol-application-check (lib raw known facts count)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((source (proof-rewritten-term raw))
         (normalized (t3-book-function-terms-normalize-checks lib source known))
         (equation (proof-proof-chain proof raw (list normalized)))
         (equation (if count
                       (t3-book-spines-replace-value lib equation (list count))
                     equation))
         (meaning (proof-rewritten-term equation))
         (required (t3-book-lambdas-required lib meaning facts)))
      (proof-proof-transport proof required equation))))

(defun t3-book-function-terms-symbol-application (lib target symbol arguments not-quote arity)
  (let ((proof (library-library-proof lib))
        (known (list symbol arguments not-quote)))
    (proof-with-checked-results
        ((raw (t3-book-lambdas-open-application lib target))
         (facts (t3-book-function-terms-fact-table known nil))
         (operator (proof-term-at target 0)))
      (if (not (equal operator *t3-book-lambdas-real-term*))
          (t3-book-function-terms-symbol-application-check lib raw known facts nil)
        (proof-with-checked-results
            ((literal (proof-step-first arguments))
             (values (proof-term-at literal 1))
             (arity-literal (proof-step-first arity))
             (actual-arity (proof-term-at arity-literal 2))
             (length-type (t3-logic-libraryproofs-type-of lib (list *library-len* values) nil))
             (typed (proof-proof-rewrite proof length-type arity '(1 1)))
             (nonnil (t3-book-function-terms-nonnil-integer lib typed))
             (proper (t3-book-lambdas-term-list-proper lib arguments))
             (count (library-library-cite lib *t3-book-lambdas-proper-length*
                                          (list values) (list proper))))
          (t3-book-function-terms-symbol-application-check
           lib raw (append known (list nonnil))
           (table-put (table-put facts arity-literal arity) actual-arity nonnil)
           count))))))

(defun t3-book-function-terms-real-arity (lib head fields function head-present arity)
  (let ((proof (library-library-proof lib))
        (lengths (list *library-car* (list *library-cdr* head))))
    (proof-with-checked-results
        ((length-type (t3-book-function-terms-fact-at fields (list *t3-book-lambdas-arglist* lengths)))
         (proper (t3-book-lambdas-arglist-proper lib length-type))
         (literal (proof-step-first function))
         (world (proof-term-at literal 2))
         (actual (t3-book-spines-shallow lib (list *t3-book-function-terms-arity* head world)
                                       (list head-present)))
         (exact (library-library-cite lib *t3-book-lambdas-proper-length* (list lengths) (list proper)))
         (equation (proof-proof-chain proof actual (list exact))))
      (proof-proof-rewrite proof arity equation '(1 2)))))

(defun t3-book-function-terms-pseudo-arity (lib arity head-present)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first arity))
         (expanded (t3-logic-libraryproofs-normalize
                    lib literal (list head-present) (list *t3-logic-atom* *proof-not*)))
         (rewritten (if expanded
                        (proof-proof-rewrite proof arity expanded '(1))
                      '(:failure "failure" ""))))
      (proof-proof-tidy proof rewritten))))

(defun t3-book-function-terms-expand-not-quote (proof not-quote)
  (proof-with-checked-results
      ((literal (proof-step-first not-quote))
       (explicit (proof-term-at literal 1)))
    (if (proof-is-call explicit (proof-cl "EQ"))
        (proof-with-checked-results ((opened (proof-proof-unfold proof explicit)))
          (proof-proof-rewrite proof not-quote opened '(1 1)))
      not-quote)))

(defun t3-book-function-terms-from-function (lib name formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((target (proof-term-at formula 2))
         (guard (proof-term-at formula 1))
         (assumption (proof-proof-assume proof guard t))
         (parts (t3-book-associations-components lib assumption))
         (parts (proof-list-of-length parts 4))
         (function (proof-step-first (car parts)))
         (head (proof-term-at function 1)))
      (let* ((pseudo (not (proof-is-call target *t3-book-lambdas-real-term*)))
             (test (list *t3-book-lambdas-symbolp* head))
             (arguments (cadr parts))
             (arity (caddr parts)))
        (proof-with-checked-results
            ((symbol (proof-proof-assume proof test t))
             (nonsymbol (proof-proof-assume proof test nil))
             (not-quote (t3-book-function-terms-expand-not-quote proof (cadddr parts)))
             (lib (if pseudo lib (t3-book-lambdas-proper-length lib))))
          (let ((proof (library-library-proof lib)))
            (proof-with-checked-results
                ((yes (t3-book-function-terms-symbol-application lib target symbol arguments not-quote arity))
                 (parsed (t3-book-lambdas-inspect lib function (list nonsymbol)))
                 (rewritten (proof-proof-rewrite proof (car parts) parsed '(1)))
                 (typed (proof-proof-tidy proof rewritten))
                 (fields (t3-book-function-terms-lambda-components lib typed))
                 (head-present (t3-book-lambdas-present-operator lib head fields))
                 (arity (if pseudo
                            (t3-book-function-terms-pseudo-arity lib arity head-present)
                          (t3-book-function-terms-real-arity lib head fields (car parts) head-present arity)))
                 (no (t3-book-function-terms-theorem-from
                      lib (if pseudo *t3-book-lambdas-construct* *t3-book-lambdas-construct-real*)
                      target (list typed arguments arity)))
                 (result (proof-proof-cases proof test yes no))
                 (entry (t3-book-function-terms-finish lib name formula result)))
              (cons entry lib))))))))
