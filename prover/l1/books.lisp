(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-books-simple-definitions*
  (list *library-implies* *proof-not* *termination-return-last*
        (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "EQ")
        (proof-cl "EQL") (proof-cl "NULL")))

(defun l1-books-make-certificate (source steps reason helpers)
  (list :l1-certificate source steps reason helpers))

(defun l1-books-certificate-sources (certificate)
  (let ((source (cadr certificate)))
    (if (stringp source) (list source) source)))

(defun l1-books-certificate-source (certificate)
  (l1-warrant-join-sources 1000000 (l1-books-certificate-sources certificate)))

(defun l1-books-certificate-steps (certificate)
  (caddr certificate))

(defun l1-books-certificate-reason (certificate)
  (cadddr certificate))

(defun l1-books-certificate-helpers (certificate)
  (car (cddddr certificate)))

(defun l1-books-missing-warrant-dependency-p (result)
  (and (failure-p result)
       (or (equal (cadr result) "missing-warrant-dependency")
           (equal (cadr result) "key"))))

(defun l1-books-add-counts (counts count)
  (if (endp counts)
      count
    (l1-books-add-counts (cdr counts) (+ count (car counts)))))

(defun l1-books-entry (kind name fields steps)
  (proof-with-checked-results
      ((entry (proof-proof-entry kind name fields steps)))
    (l1-books-make-certificate
     (cadddr entry) (l1-books-add-counts (caddr entry) 0) "" nil)))

(defun l1-books-obligation (kind data)
  (cond
   ((equal kind "theorem")
    (proof-with-checked-results ((name (proof-term-at data 0)))
      (list name nil)))
   ((equal kind "define")
    (proof-with-checked-results
        ((rulers (proof-term-at data 0))
         (calls (termination-recursive-calls rulers (cdr data))))
      (if (endp calls)
          (list nil nil)
        (proof-with-checked-results ((name (proof-term-at (cadr data) 0)))
          (list name calls)))))
   ((equal kind "constrain")
    (proof-with-checked-results ((formulas (proof-term-at data 1)))
      (if (equal formulas *proof-nil*)
          (list nil nil)
        (proof-with-checked-results
            ((function (proof-term-at (car data) 0))
             (name (proof-term-at function 0)))
          (list name nil)))))
   (t (list nil nil))))

(mutual-recursion
 (defun l1-books-replace-calls (term names)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
     term)
    ((endp term)
     '(:failure "unproved" ""))
    (t
     (let ((head (car term)))
       (proof-with-checked-results
           ((new-head
             (if (proof-compound head)
                 (if (< (len head) 3)
                     '(:failure "failure" "")
                   (proof-with-checked-results
                       ((body (l1-books-replace-calls (caddr head) names)))
                     (list (car head) (cadr head) body)))
               (table-get names head head)))
            (actuals (l1-books-replace-actuals (cdr term) names)))
         (cons new-head actuals))))))
 (defun l1-books-replace-actuals (actuals names)
   (declare (xargs :measure (* 2 (acl2-count actuals))))
   (if (endp actuals)
       nil
     (proof-with-checked-results
         ((first (l1-books-replace-calls (car actuals) names))
          (rest (l1-books-replace-actuals (cdr actuals) names)))
       (cons first rest)))))

(defun l1-books-byte-lines (input line lines)
  (cond
   ((endp input)
    (reverse (if line
                 (cons (coerce (reverse line) 'string) lines)
               lines)))
   ((or (eql (car input) #\Return) (eql (car input) #\Newline))
    (l1-books-byte-lines
     (if (and (eql (car input) #\Return) (eql (cadr input) #\Newline))
         (cddr input)
       (cdr input))
     nil (cons (coerce (reverse line) 'string) lines)))
   (t (l1-books-byte-lines (cdr input) (cons (car input) line) lines))))

(mutual-recursion
 (defun l1-books-datum-text (datum)
   (declare (xargs :measure (1+ (* 2 (acl2-count datum)))))
   (cond ((stringp datum)
          (concatenate 'string
                       "\""
                       (text-replace (text-replace datum "\\" "\\\\") "\"" "\\\"")
                       "\""))
         ((integerp datum) (decimal-text datum))
         (t (concatenate 'string "("
                         (text-join " " (l1-books-datum-items-text datum))
                         ")"))))
 (defun l1-books-datum-items-text (items)
   (declare (xargs :measure (* 2 (acl2-count items))))
   (if (endp items)
       nil
     (cons (l1-books-datum-text (car items))
           (l1-books-datum-items-text (cdr items))))))

(defun l1-books-fact-keys (lines keys)
  (if (endp lines)
      keys
    (if (text-starts-with (car lines) "(fact ")
        (proof-with-checked-results
            ((line (reader-reader-line (reader-reader (car lines))))
             (name (proof-term-at (cadar line) 0)))
          (let ((name (proof-freeze name)))
            (l1-books-fact-keys
             (cdr lines)
             (table-put keys (l1-books-datum-text name) name))))
      (l1-books-fact-keys (cdr lines) keys))))

(defun l1-books-fact-names (source)
  (proof-with-checked-results
      ((keys (l1-books-fact-keys
              (l1-books-byte-lines (coerce source 'list) nil nil) nil)))
    (table-values (seq-sorted keys))))

(defun l1-books-select-helpers (entries needed helpers)
  (if (endp entries)
      helpers
    (proof-with-checked-results ((name (proof-term-at (car entries) 1)))
      (if (member-equal name needed)
          (proof-with-checked-results
              ((source (proof-term-at (car entries) 3))
               (names (l1-books-fact-names source)))
            (l1-books-select-helpers (cdr entries) (union-equal names needed)
                                     (cons (car entries) helpers)))
        (l1-books-select-helpers (cdr entries) needed helpers)))))

(defun l1-books-arithmetic-helpers (source entries)
  (proof-with-checked-results ((needed (l1-books-fact-names source)))
    (l1-books-select-helpers (reverse entries) needed nil)))

(defun l1-books-helper-fact-names (helpers names)
  (if (endp helpers)
      names
    (proof-with-checked-results
        ((entry (proof-list-of-length (car helpers) 4))
         (found (l1-books-fact-names (cadddr entry))))
      (l1-books-helper-fact-names (cdr helpers) (union-equal found names)))))

(defun l1-books-referenced-facts (names facts)
  (if (endp names)
      nil
    (let ((fact (assoc-equal (car names) facts)))
      (if fact
          (cons fact (l1-books-referenced-facts (cdr names) facts))
        (l1-books-referenced-facts (cdr names) facts)))))

(defun l1-books-fact-dependencies (certificate facts)
  (proof-with-checked-results
      ((names (l1-books-fact-names (l1-books-certificate-source certificate)))
       (all (l1-books-helper-fact-names
             (l1-books-certificate-helpers certificate) names)))
    (l1-books-referenced-facts
     (table-values (seq-sorted (pairlis$ (l1-books-datum-items-text all) all)))
     facts)))

(defun l1-books-simplified-value (step term)
  (if step
      (proof-with-checked-results ((literal (proof-step-first step)))
        (proof-term-at literal 2))
    term))

(defun l1-books-matching-fact (proof facts formula)
  (if (endp facts)
      nil
    (let ((clause (cdar facts)))
      (if (and (equal (len clause) 1) (proof-compound (car clause)))
          (proof-with-checked-results
              ((matched (l1-rewriting-match (car clause) formula nil)))
            (if (car matched)
                (proof-proof-fact proof (caar facts) (table-items (cdr matched)))
              (l1-books-matching-fact proof (cdr facts) formula)))
        (l1-books-matching-fact proof (cdr facts) formula)))))

(defund l1-books-formula-plan-prepared (proof formula evidence definitions rewriting rewriter)
  (let ((direct (l1-warrant-prove proof formula evidence definitions)))
    (if (not (l1-rewriting-retry-proof-p direct))
        direct
      (proof-with-checked-results
          ((fact (l1-books-matching-fact proof (proof-proof-facts proof) formula)))
        (cond
         (fact fact)
         ((proof-is-call formula *library-implies*)
          (proof-with-checked-results
              ((parts (proof-list-of-length (cdr formula) 2))
               (positive (proof-proof-assume proof (car parts) t)))
            (list :implication (car parts) (append evidence (list positive)))))
         (rewriting
          (proof-with-checked-results ((rewriter (or rewriter (l1-rewriting-rewriter-init proof))))
            (l1-rewriting-rewriter-prove rewriter formula evidence 0)))
         (t (proof-with-checked-results ((written (proof-write formula)))
              '(:failure "unproved" ""))))))))

(defund l1-books-formula-plan (proof formula evidence definitions rewriting)
  (l1-books-formula-plan-prepared proof formula evidence definitions rewriting nil))

(defun l1-books-prove-formula-prepared (proof formula evidence definitions rewriting rewriter)
  (declare (xargs :measure (acl2-count formula)))
  (proof-with-checked-results
      ((plan (l1-books-formula-plan-prepared proof formula evidence definitions rewriting rewriter)))
    (if (and (consp formula) (eq (car plan) :implication))
        (let ((hypothesis (cadr plan))
              (yes-evidence (caddr plan))
              (implies (list *library-implies*)))
          (proof-with-checked-results
              ((conclusion (l1-books-prove-formula-prepared
                            proof (caddr formula) yes-evidence definitions rewriting rewriter))
               (yes (l1-warrant-prove proof formula (append yes-evidence (list conclusion))
                                      implies))
               (negative (proof-proof-assume proof hypothesis nil))
               (no (l1-warrant-prove proof formula (list negative) implies)))
            (proof-proof-cases proof hypothesis yes no)))
      plan)))

(defun l1-books-prove-formula (proof formula evidence definitions rewriting)
  (l1-books-prove-formula-prepared proof formula evidence definitions rewriting nil))

(defun l1-books-arithmetic-library ()
  (library-library-build (library-library-init (proof-proof-init))))

(defun l1-books-arithmetic-or-build (arithmetic)
  (or arithmetic (l1-books-arithmetic-library)))

(defun l1-books-selector-case-prepared (proof goal hypotheses arithmetic)
  (if (or (not hypotheses) (not (proof-is-call goal *proof-ordinal-less*)))
      (cons nil hypotheses)
    (proof-with-checked-results ((parts (proof-list-of-length goal 3)))
      (let ((child (cadr parts))
            (parent (caddr parts)))
        (if (not (and (proof-is-call child *library-count*)
                      (proof-is-call parent *library-count*)))
            (cons nil hypotheses)
          (proof-with-checked-results
              ((argument (proof-term-at child 1))
               (opened (l1-warrant-simplify proof argument nil (list *termination-return-last*)))
               (actual (l1-books-simplified-value opened argument))
               (root (proof-term-at parent 1))
               (scope (l1-structural-measures-selector-hypotheses proof actual root hypotheses)))
            (if (not (car scope))
                (cons nil (cdr scope))
              (proof-with-checked-results
                  ((lib (l1-books-arithmetic-or-build arithmetic))
                   (result (descent-selector-decrease lib goal (car scope))))
                (cons (car result) (cdr scope))))))))))

(defun l1-books-length-arguments-p (arguments)
  (if (endp arguments)
      t
    (and (proof-is-call (car arguments) *library-len*)
         (l1-books-length-arguments-p (cdr arguments)))))

(defun l1-books-length-sum-p (term)
  (and (proof-is-call term *proof-plus*)
       (l1-books-length-arguments-p (cdr term))))

(defun l1-books-length-sum-changing-prepared
    (proof goal child parent changing fixed hypotheses arithmetic)
  (proof-with-checked-results
      ((old-length (proof-term-at parent changing))
       (old (proof-term-at old-length 1))
       (child-fixed (proof-term-at child fixed))
       (parent-fixed (proof-term-at parent fixed)))
    (if (not (equal child-fixed parent-fixed))
        (cons nil hypotheses)
      (proof-with-checked-results ((new-length (proof-term-at child changing)))
        (if (not (equal new-length (list *library-len* (list *library-cdr* old))))
            (cons nil hypotheses)
          (proof-with-checked-results
              ((evidence (l1-structural-measures-cons-evidence proof old hypotheses)))
            (if (not (car evidence))
                evidence
              (proof-with-checked-results
                  ((lib (l1-books-arithmetic-or-build arithmetic))
                   (scope (descent-hypotheses-init proof
                           (descent-hypotheses-tests (cdr evidence)) (list (car evidence))))
                   (result (descent-run-decrease lib goal scope)))
                (cons (car result) (cdr evidence))))))))))

(defun l1-books-length-sum-case-prepared (proof goal hypotheses arithmetic)
  (if (or (not hypotheses) (not (proof-is-call goal *proof-ordinal-less*)))
      (cons nil hypotheses)
    (proof-with-checked-results ((parts (proof-list-of-length goal 3)))
      (let ((child (cadr parts))
            (parent (caddr parts)))
        (if (not (and (l1-books-length-sum-p child) (l1-books-length-sum-p parent)))
            (cons nil hypotheses)
          (proof-with-checked-results
              ((first (l1-books-length-sum-changing-prepared
                       proof goal child parent 1 2 hypotheses arithmetic)))
            (if (car first)
                first
              (l1-books-length-sum-changing-prepared
               proof goal child parent 2 1 (cdr first) arithmetic))))))))

(defun l1-books-lexer-arithmetic (entries context arithmetic)
  (if (endp entries)
      context
    (let* ((name (cadar entries))
           (facts (proof-proof-facts context))
           (definitions (proof-proof-definitions context))
           (fact (assoc-equal name (proof-proof-facts arithmetic)))
           (definition (assoc-equal name (proof-proof-definitions arithmetic))))
      (l1-books-lexer-arithmetic
       (cdr entries)
       (proof-make-proof
        (table-put facts name (cdr fact))
        (if definition (table-put definitions name (cdr definition)) definitions)
        (proof-proof-primitives context))
       arithmetic))))

(defun l1-books-lexer-proofs-prepared (proof arithmetic)
  (let* ((ground (proof-proof-init))
         (context (proof-make-proof
                   (table-update (proof-proof-facts ground) (proof-proof-facts proof))
                   (table-update (proof-proof-definitions ground) (proof-proof-definitions proof))
                   (proof-proof-primitives ground))))
    (proof-with-checked-results ((arithmetic (l1-books-arithmetic-or-build arithmetic)))
      (let* ((entries (library-library-entries arithmetic))
             (context (l1-books-lexer-arithmetic
                       entries context (library-library-proof arithmetic)))
             (lib (library-make-library context entries)))
        (lexer-lexer-proofs-build (lexer-lexer-proofs-init lib))))))

(defun l1-books-cdr-root (term)
  (if (not (proof-is-call term *library-cdr*))
      term
    (if (endp (cdr term))
        '(:failure "failure" "")
      (l1-books-cdr-root (cadr term)))))

(defun l1-books-has-lexer-definitions-p (fields definitions)
  (if (endp fields)
      t
    (and (assoc-equal (caar fields) definitions)
         (l1-books-has-lexer-definitions-p (cdr fields) definitions))))

(defun l1-books-length-selector-prepared (proof goal argument root hypotheses lexer arithmetic)
  (proof-with-checked-results
      ((scope (l1-structural-measures-selector-hypotheses proof argument root hypotheses)))
    (if (not (car scope))
        (cons (list nil lexer) (cdr scope))
      (proof-with-checked-results
          ((arithmetic (l1-books-arithmetic-or-build arithmetic))
           (result (lexer-lexer-proofs-decrease
                    (lexer-lexer-proofs-init arithmetic) goal (car scope))))
        (cons (list (car result) lexer) (cdr scope))))))

(defun l1-books-length-lexer-prepared (proof goal root hypotheses lexer arithmetic)
  (if (not (proof-compound root))
      (cons (list nil lexer) hypotheses)
    (proof-with-checked-results ((head (proof-term-at root 0)))
      (if (and (assoc-equal head *lexer-fields*)
               (l1-books-has-lexer-definitions-p *lexer-fields* (proof-proof-definitions proof)))
          (proof-with-checked-results
              ((active (or lexer (l1-books-lexer-proofs-prepared proof arithmetic)))
               (result (lexer-lexer-proofs-decrease active goal hypotheses)))
            (cons (list (car result) (cadr result)) (caddr result)))
        (cons (list nil lexer) hypotheses)))))

(defun l1-books-length-case-prepared (proof goal hypotheses lexer arithmetic)
  (proof-with-checked-results ((parts (proof-list-of-length goal 3)))
    (let ((child (cadr parts))
          (parent (caddr parts)))
      (if (not (and (proof-is-call child *library-len*)
                    (proof-is-call parent *library-len*)))
          (cons (list nil lexer) hypotheses)
        (proof-with-checked-results
            ((argument (proof-term-at child 1))
             (root (l1-books-cdr-root argument))
             (source (proof-term-at parent 1)))
          (if (equal root source)
              (l1-books-length-selector-prepared proof goal argument root hypotheses lexer arithmetic)
            (l1-books-length-lexer-prepared proof goal root hypotheses lexer arithmetic)))))))

(defun l1-books-arithmetic-descent-prepared (proof goal hypotheses lexer arithmetic)
  (proof-with-checked-results
      ((selector (l1-books-selector-case-prepared proof goal hypotheses arithmetic))
       (length-sum (if (car selector)
                       selector
                     (l1-books-length-sum-case-prepared proof goal (cdr selector) arithmetic))))
    (if (car length-sum)
        (list (car length-sum) lexer)
      (proof-with-checked-results
          ((parent (proof-term-at goal 2))
           (counter
            (if (proof-is-call parent *library-gap*)
                (proof-with-checked-results ((lib (l1-books-arithmetic-or-build arithmetic)))
                  (l1-counters-counter-decrease lib goal (cdr length-sum)))
              length-sum))
           (phase
            (if (car counter)
                counter
              (proof-with-checked-results ((lib (l1-books-arithmetic-or-build arithmetic)))
                (l1-structural-measures-phase-decrease proof lib goal (cdr counter))))))
        (if (car phase)
            (list (car phase) lexer)
          (proof-with-checked-results
              ((result (l1-books-length-case-prepared proof goal (cdr phase) lexer arithmetic)))
            (car result)))))))

(defun l1-books-ordinal-case-prepared (clause lexer arithmetic)
  (proof-with-checked-results
      ((lib (l1-books-arithmetic-or-build arithmetic))
       (literal (proof-term-at clause 0))
       (measure (proof-term-at literal 1))
       (step (descent-measure-ordinal lib measure)))
    (list step lexer)))

(defun l1-books-prove-measure-case-prepared (proof clause call lexer arithmetic)
  (proof-with-checked-results
      ((hypotheses (and call (descent-hypotheses-init proof (termination-call-tests call) nil)))
       (direct (descent-direct-builtin proof clause hypotheses)))
    (if (car direct)
        (list (car direct) nil lexer)
      (let ((result (if call
                        (l1-books-arithmetic-descent-prepared
                         proof (car (last clause)) (cdr direct) lexer arithmetic)
                      (l1-books-ordinal-case-prepared clause lexer arithmetic))))
        (cond ((l1-rewriting-retry-proof-p result) nil)
              ((failure-p result) result)
              ((car result) (list (car result) t (cadr result)))
              (t nil))))))

; Progress records the seen clauses, reversed Steps, arithmetic use, and LexerProofs.
(defund l1-books-measure-record-prepared (proof obligation progress arithmetic)
  (let ((clause (car obligation))
        (call (cadr obligation))
        (seen (car progress)))
    (if (member-equal clause seen)
        progress
      (proof-with-checked-results
          ((result (l1-books-prove-measure-case-prepared
                    proof clause call (cadddr progress) arithmetic)))
        (and result
             (proof-with-checked-results ((step (proof-proof-subsume proof (car result) clause)))
               (list (cons clause seen) (cons step (cadr progress))
                     (or (cadr result) (caddr progress)) (caddr result))))))))

(defund l1-books-measure-record (proof obligation progress)
  (l1-books-measure-record-prepared proof obligation progress nil))

(defun l1-books-measure-ordinalities-prepared (definitions proof measures progress arithmetic)
  (if (endp definitions)
      progress
    (proof-with-checked-results
        ((cases (termination-ordinality-cases (list (car definitions)) measures))
         (next (l1-books-measure-record-prepared proof (car cases) progress arithmetic)))
      (and next (l1-books-measure-ordinalities-prepared
                 (cdr definitions) proof measures next arithmetic)))))

(defun l1-books-measure-decreases-prepared (calls proof formals measures progress arithmetic)
  (if (endp calls)
      progress
    (proof-with-checked-results
        ((cases (termination-call-cases (list (car calls)) measures formals))
         (next (l1-books-measure-record-prepared proof (car cases) progress arithmetic)))
      (and next (l1-books-measure-decreases-prepared
                 (cdr calls) proof formals measures next arithmetic)))))

(defun l1-books-measure-fields (definitions measures)
  (if (endp definitions)
      nil
    (let ((measure (assoc-equal (caar definitions) measures)))
      (if measure
          (proof-with-checked-results
              ((rest (l1-books-measure-fields (cdr definitions) measures)))
            (cons (cdr measure) rest))
        '(:failure "failure" "")))))

(defun l1-books-helpers-occupied-p (helpers facts)
  (and (consp helpers)
       (or (assoc-equal (cadar helpers) facts)
           (l1-books-helpers-occupied-p (cdr helpers) facts))))

(defun l1-books-measure-helpers-prepared (proof certificate lexer arithmetic)
  (proof-with-checked-results
      ((lib (if lexer (lexer-lexer-proofs-lib lexer) (l1-books-arithmetic-or-build arithmetic)))
       (helpers (l1-books-arithmetic-helpers (l1-books-certificate-source certificate)
                                            (library-library-entries lib))))
    (if (l1-books-helpers-occupied-p helpers (proof-proof-facts proof))
        nil
      (l1-books-make-certificate (l1-books-certificate-source certificate)
                                 (l1-books-certificate-steps certificate) "" helpers))))

(defun l1-books-measure-proof-prepared (proof name definitions calls measures arithmetic)
  (proof-with-checked-results
      ((formals (termination-formals definitions nil nil))
       (ordinalities (l1-books-measure-ordinalities-prepared
                      definitions proof measures '(nil nil nil nil) arithmetic))
       (progress (and ordinalities
                      (l1-books-measure-decreases-prepared
                       calls proof formals measures ordinalities arithmetic))))
    (and progress
         (proof-with-checked-results
             ((fields (l1-books-measure-fields definitions measures))
              (certificate (l1-books-entry "measure" name (cons name fields)
                                            (reverse (cadr progress)))))
           (if (caddr progress)
               (l1-books-measure-helpers-prepared proof certificate (cadddr progress) arithmetic)
             certificate)))))

(defun l1-books-witness-names (functions tag index names)
  (if (endp functions)
      names
    (proof-with-checked-results ((function (proof-list-of-length (car functions) 2)))
      (let ((helper (proof-sym (concatenate 'string "L1-WITNESS-" tag "-" (decimal-text index))
                               "ACL2")))
        (l1-books-witness-names (cdr functions) tag (1+ index)
                                (table-put names (car function) helper))))))

(defun l1-books-witness-formals (remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons (proof-sym (concatenate 'string "L1-ARGUMENT-" (decimal-text index)) "ACL2")
          (l1-books-witness-formals (1- remaining) (1+ index)))))

(defun l1-books-witness-definitions (functions names proof value sources)
  (if (endp functions)
      (cons proof (reverse sources))
    (let* ((function (caar functions))
           (arity (cadar functions))
           (helper (cdr (assoc-equal function names)))
           (formals (or (l1-books-witness-formals arity 0) *proof-nil*))
           (extended (proof-proof-add-definition proof helper formals value)))
      (proof-with-checked-results
          ((source (proof-line "define" (list *proof-nil* (list helper formals value)))))
        (l1-books-witness-definitions (cdr functions) names extended value (cons source sources))))))

(defun l1-books-witness-steps (formulas names proof definitions)
  (if (endp formulas)
      nil
    (proof-with-checked-results
        ((formula (proof-list-of-length (car formulas) 2))
         (term (l1-books-replace-calls (cadr formula) names))
         (step (l1-books-prove-formula proof term nil definitions nil))
         (rest (l1-books-witness-steps (cdr formulas) names proof definitions)))
      (cons step rest))))

(defund l1-books-witness-certificate (proof name formulas names helpers sources)
  (proof-with-checked-results
      ((steps (l1-books-witness-steps formulas names proof
                                      (append *l1-books-simple-definitions* helpers)))
       (witness (l1-books-entry "witness" name (cons name helpers) steps)))
    (l1-books-make-certificate
     (text-join "" (append sources (list (l1-books-certificate-source witness))))
     (l1-books-certificate-steps witness) "" nil)))

(defun l1-books-constant-values (values proof name functions formulas names helpers)
  (if (endp values)
      nil
    (proof-with-checked-results
        ((extended (l1-books-witness-definitions functions names proof (car values) nil)))
      (let ((witness (l1-books-witness-certificate
                      (car extended) name formulas names helpers (cdr extended))))
        (if (l1-rewriting-retry-proof-p witness)
            (l1-books-constant-values (cdr values) proof name functions formulas names helpers)
          witness)))))

(defun l1-books-any-named-fact-p (names facts)
  (and (consp names)
       (or (assoc-equal (car names) facts)
           (l1-books-any-named-fact-p (cdr names) facts))))

(defun l1-books-constant-witness (proof name data tag)
  (proof-with-checked-results
      ((parts (proof-list-of-length data 2))
       (names (l1-books-witness-names (car parts) tag 0 nil)))
    (let ((helpers (table-values names)))
      (if (l1-books-any-named-fact-p helpers (proof-proof-facts proof))
          nil
        (l1-books-constant-values (list *proof-false* *proof-true* *proof-zero*)
                                  proof name (car parts) (cadr parts) names helpers)))))

(defun l1-books-choice-terms-p (comparison functions)
  (let* ((argument (l1-witness-comparison-argument comparison))
         (parameters (l1-witness-comparison-parameters comparison))
         (counterexample (l1-witness-comparison-counterexample comparison))
         (application (l1-witness-comparison-application comparison))
         (forbidden (pairlis$ (strip-cars functions) '(nil nil))))
    (and (subsetp-equal (l1-rewriting-variable-set counterexample)
                        (cons argument parameters))
         (proof-with-checked-results
             ((body (proof-term-at (car application) 2))
              (marked-body (l1-books-replace-calls body forbidden))
              (marked-counterexample (l1-books-replace-calls counterexample forbidden)))
           (and (equal marked-body body)
                (equal marked-counterexample counterexample))))))

(defun l1-books-choice-witness (proof data tag)
  (proof-with-checked-results
      ((comparison (l1-witness-comparison-read data))
       (admissible (and comparison (l1-books-choice-terms-p comparison (car data)))))
    (and admissible
         (let* ((name (proof-sym (concatenate 'string "L1-CHOICE-" tag) "ACL2"))
                (argument (l1-witness-comparison-argument comparison))
                (parameters (l1-witness-comparison-parameters comparison))
                (counterexample (l1-witness-comparison-counterexample comparison))
                (choice (list name (list argument) (or parameters *proof-nil*)
                              counterexample *proof-nil*)))
           (and (not (assoc-equal name (proof-proof-facts proof)))
                (proof-with-checked-results
                    ((registered (l1-witness-available-choice proof "choose" choice))
                     (witness (l1-witness-prove-witness
                               (cdr registered) data (list (car registered)) tag)))
                  (and witness
                       (proof-with-checked-results ((source (proof-line "choose" choice)))
                         (l1-books-make-certificate
                          (concatenate 'string source (cadr witness))
                          (car witness) "" nil)))))))))

(defun l1-books-skip (name reason)
  (proof-with-checked-results ((source (proof-line "skip" (list name))))
    (l1-books-make-certificate source 0 reason nil)))

(defun l1-books-theorem-direct-prepared (proof name formula rewriter)
  (proof-with-checked-results
      ((step (l1-books-prove-formula-prepared
              proof formula nil *l1-books-simple-definitions* t rewriter)))
    (l1-books-entry "theorem" name (list name) (list step))))

(defun l1-books-theorem-induction-prepared (proof name formula rewriter)
  (proof-with-checked-results
      ((rewriter (or rewriter (l1-rewriting-rewriter-init proof)))
       (step (l1-rewriting-rewriter-induct rewriter formula)))
    (l1-books-entry "theorem" name (list name) (list step))))

(defun l1-books-generate-theorem-prepared (proof choices data name rewriter)
  (proof-with-checked-results ((formula (proof-term-at data 1)))
    (let ((specialized (l1-warrant-theorem-prove-fragments proof name formula choices)))
      (cond
       ((and (failure-p specialized)
             (not (or (l1-books-missing-warrant-dependency-p specialized)
                      (l1-rewriting-retry-proof-p specialized))))
        specialized)
       ((and specialized (not (failure-p specialized)))
        (l1-books-make-certificate (cadr specialized) (car specialized) "" nil))
       (t
        (let ((direct (l1-books-theorem-direct-prepared proof name formula rewriter)))
          (if (l1-rewriting-retry-proof-p direct)
              (let ((induction (l1-books-theorem-induction-prepared proof name formula rewriter)))
                (if (l1-rewriting-retry-proof-p induction)
                    (l1-books-skip name "needs a theorem proof")
                  induction))
            direct)))))))

(defun l1-books-with-stored-ordinal-p (definitions stored)
  (if (endp definitions)
      t
    (proof-with-checked-results ((name (proof-term-at (car definitions) 0)))
      (let ((binding (assoc-equal name stored)))
        (and binding
             (proof-with-checked-results ((relation (proof-term-at (cdr binding) 1)))
               (and (equal relation *proof-ordinal-less*)
                    (l1-books-with-stored-ordinal-p (cdr definitions) stored))))))))

(defun l1-books-stored-measures (definitions stored measures)
  (if (endp definitions)
      measures
    (let* ((name (caar definitions))
           (binding (assoc-equal name stored)))
      (proof-with-checked-results ((measure (proof-term-at (cdr binding) 0)))
        (l1-books-stored-measures (cdr definitions) stored (table-put measures name measure))))))

(defun l1-books-counter-measures (definitions measures gaps)
  (if (endp definitions)
      gaps
    (proof-with-checked-results
        ((definition (proof-list-of-length (car definitions) 3))
         (term (cdr (assoc-equal (car definition) measures)))
         (gap (l1-counters-counter-measure term (cadr definition))))
      (l1-books-counter-measures (cdr definitions) measures
                                 (table-put gaps (car definition) gap)))))

(defun l1-books-all-measures-p (measures)
  (if (endp measures)
      t
    (and (cdar measures) (l1-books-all-measures-p (cdr measures)))))

(defun l1-books-stored-certificate-prepared (proof name definitions calls stored arithmetic)
  (proof-with-checked-results ((available (l1-books-with-stored-ordinal-p definitions stored)))
    (and available
         (proof-with-checked-results
             ((measures (l1-books-stored-measures definitions stored nil))
              (certificate (l1-books-measure-proof-prepared
                            proof name definitions calls measures arithmetic)))
           (or certificate
               (proof-with-checked-results ((gaps (l1-books-counter-measures definitions measures nil)))
                 (and (l1-books-all-measures-p gaps)
                      (l1-books-measure-proof-prepared proof name definitions calls gaps arithmetic))))))))

(defun l1-books-count-measures (plan)
  (if (endp plan)
      nil
    (cons (cons (caar plan) (list *library-count* (cdar plan)))
          (l1-books-count-measures (cdr plan)))))

(defun l1-books-selector-certificate-prepared (proof name definitions calls arithmetic)
  (proof-with-checked-results ((plan (termination-selector-plan definitions calls)))
    (and plan
         (l1-books-measure-proof-prepared proof name definitions calls
                                          (l1-books-count-measures plan) arithmetic))))

(defun l1-books-phase-certificate-prepared (proof name definitions calls arithmetic)
  (proof-with-checked-results ((phases (l1-structural-measures-phase-measures definitions calls)))
    (and phases (l1-books-measure-proof-prepared proof name definitions calls phases arithmetic))))

(defun l1-books-generate-definition-prepared (proof name definitions calls stored arithmetic)
  (proof-with-checked-results
      ((certificate (l1-books-stored-certificate-prepared
                     proof name definitions calls stored arithmetic))
       (selector (or certificate (l1-books-selector-certificate-prepared
                                  proof name definitions calls arithmetic)))
       (phase (or selector (l1-books-phase-certificate-prepared
                            proof name definitions calls arithmetic))))
    (or phase (l1-books-skip name "needs ordinal descent"))))

(defun l1-books-generate-constraint (proof choices raw data name)
  (let ((tag (text-upper (siphash-hexdigest raw))))
    (proof-with-checked-results ((witness (l1-witness-prove-witness proof data choices tag)))
      (if witness
          (l1-books-make-certificate (cadr witness) (car witness) "" nil)
        (proof-with-checked-results
            ((certificate (l1-books-constant-witness proof name data tag))
             (choice (and (not certificate) (l1-warrant-choice-witness proof data))))
          (cond (certificate certificate)
                (choice (l1-books-make-certificate (cadr choice) (car choice) "" nil))
                (t (l1-books-skip name "needs constrained witness"))))))))

(defund l1-books-generate-prepared (proof choices raw kind data name calls stored preparation)
  (cond ((equal kind "theorem") (l1-books-generate-theorem-prepared
                                proof choices data name (cadr preparation)))
        ((equal kind "define") (l1-books-generate-definition-prepared
                                proof name (cdr data) calls stored (car preparation)))
        (t (l1-books-generate-constraint proof choices raw data name))))

(defund l1-books-generate (proof choices raw kind data name calls stored)
  (l1-books-generate-prepared proof choices raw kind data name calls stored nil))

(defund l1-books-remember-certificate (cache raw certificate facts)
  (proof-with-checked-results ((dependencies (l1-books-fact-dependencies certificate facts)))
    (table-put cache raw
                 (append (table-get cache raw nil)
                         (list (list certificate dependencies))))))

