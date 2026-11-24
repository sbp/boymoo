(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-books-books* "build/export/books")
(defconst *t3-books-fact-line* "^\\(fact .+\\)$")
(defconst *t3-books-compute-line* "^\\(compute .+\\)$")

; Selecting a definition obligation stops at the first recursive call.
(defund t3-books-obligation-action (term ruled names)
  (cond
   ((not (proof-compound term)) nil)
   ((endp term) '(:failure "failure" ""))
   ((equal (car term) *proof-quote*) nil)
   ((proof-compound (car term))
    (proof-with-checked-results ((parts (proof-list-of-length (car term) 3)))
      (list :lambda (cadr parts))))
   ((and (equal (car term) *termination-return-last*) (endp (cdr term)))
    '(:failure "failure" ""))
   ((and (equal (car term) *termination-return-last*)
         (equal (cadr term) *termination-mbe*))
    (if (consp (cdddr term))
        :mbe
      '(:failure "failure" "")))
   ((and (equal (car term) *proof-if*) ruled)
    (if (equal (len (cdr term)) 3)
        :if
      (proof-list-of-length (cdr term) 3)))
   ((member-equal (car term) names) :call)
   (t :arguments)))

(mutual-recursion
 (defun t3-books-obligation-walk (n term env ruled rulers names)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "t3-books-obligation")
     (proof-with-checked-results ((action (t3-books-obligation-action term ruled names)))
       (cond
        ((not action) nil)
        ((consp action)
         (let ((found (t3-books-obligation-walk-args
                       (1- n) (cdr term) env
                       (and ruled (termination-recursive-calls-extends
                                   *termination-lambdas* rulers))
                       rulers names)))
           (if found
               found
             (proof-with-checked-results
                 ((formals (cadr action))
                  (bindings (if (integerp formals)
                                '(:failure "failure" "")
                              (termination-lambda-bindings formals (cdr term) env nil))))
               (t3-books-obligation-walk (1- n) (caddar term) bindings ruled rulers names)))))
        ((eq action :mbe)
         (t3-books-obligation-walk (1- n) (cadddr term) env ruled rulers names))
        ((eq action :if)
         (let ((found (t3-books-obligation-walk
                       (1- n) (cadr term) env (termination-recursive-calls-extends *proof-if* rulers)
                       rulers names)))
           (if found
               found
             (let ((literal (proof-subst (cadr term) env)))
               (if (failure-p literal)
                   literal
                 (or (t3-books-obligation-walk (1- n) (caddr term) env t rulers names)
                     (t3-books-obligation-walk (1- n) (cadddr term) env t rulers names)))))))
        ((eq action :call)
         (let ((actuals (termination-subst-actuals (cdr term) env)))
           (if (failure-p actuals) actuals t)))
        (t (t3-books-obligation-walk-args
            (1- n) (cdr term) env
            (and ruled (termination-recursive-calls-extends (car term) rulers))
            rulers names))))))
 (defun t3-books-obligation-walk-args (n args env ruled rulers names)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "t3-books-obligation"))
         ((endp args) nil)
         (t (or (t3-books-obligation-walk (1- n) (car args) env ruled rulers names)
                (t3-books-obligation-walk-args (1- n) (cdr args) env ruled rulers names))))))

(defun t3-books-obligation-definitions (definitions rulers names)
  (if (endp definitions)
      nil
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (or (t3-books-obligation-walk 1000000 (caddr definition) nil t rulers names)
          (t3-books-obligation-definitions (cdr definitions) rulers names)))))

(defun t3-books-obligation (kind data)
  (cond
   ((equal kind "theorem") (proof-term-at data 0))
   ((equal kind "constrain")
    (proof-with-checked-results ((constraints (proof-term-at data 1)))
      (if (equal constraints *proof-nil*)
          nil
        (proof-with-checked-results ((declarations (proof-term-at data 0))
                                     (first (proof-term-at declarations 0)))
          (proof-term-at first 0)))))
   ((equal kind "define")
    (proof-with-checked-results ((rulers (proof-term-at data 0))
                                 (names (termination-definition-names (cdr data)))
                                 (found (t3-books-obligation-definitions (cdr data) rulers names)))
      (and found (proof-term-at (cadr data) 0))))
   (t nil)))

(defun t3-books-read-measures-collect (records measures)
  (if (endp records)
      measures
    (proof-with-checked-results ((record (proof-list-of-length (car records) 3)))
      (let ((kind (cadr record))
            (data (caddr record)))
        (if (equal kind "measure")
            (proof-with-checked-results ((relation (proof-term-at data 2)))
              (if (equal relation *proof-ordinal-less*)
                  (t3-books-read-measures-collect
                   (cdr records) (table-put measures (car data) (cadr data)))
                (t3-books-read-measures-collect (cdr records) measures)))
          (t3-books-read-measures-collect (cdr records) measures))))))

(defun t3-books-read-measures (records)
  (t3-books-read-measures-collect records nil))

(defun t3-books-zip-bindings (keys values bindings)
  (if (or (endp keys) (endp values))
      bindings
    (t3-books-zip-bindings (cdr keys) (cdr values)
                          (table-put bindings (car keys) (car values)))))

(defun t3-books-choice-results (bound index value)
  (if (endp bound)
      nil
    (cons (list (proof-sym "MV-NTH" "ACL2") (proof-quote index) value)
          (t3-books-choice-results (cdr bound) (1+ index) value))))

(defun t3-books-choice-bindings (value bound)
  (if (integerp bound)
      '(:failure "failure" "")
    (t3-books-zip-bindings
     bound (if (equal (len bound) 1)
               (list value)
             (t3-books-choice-results bound 0 value))
     nil)))

(defun t3-books-choice-call (name free)
  (cond ((equal free *proof-nil*) (list name))
        ((integerp free) '(:failure "failure" ""))
        (t (cons name free))))

(defun t3-books-choice (data)
  (proof-with-checked-results ((fields (proof-list-of-length data 5)))
    (let ((name (car fields))
          (bound (cadr fields))
          (free (caddr fields))
          (body (cadddr fields))
          (free-again (nth 4 fields)))
      (proof-with-checked-results
          ((call (t3-books-choice-call name free))
           (first-bindings (t3-books-choice-bindings call bound))
           (chosen (proof-subst body first-bindings)))
        (let* ((implication (list (proof-sym "IMPLIES" "ACL2") body chosen))
               (basic (if (> (len bound) 1)
                          (proof-ite (list (proof-sym "TRUE-LISTP" "ACL2") call)
                                     implication *proof-false*)
                        implication)))
          (if (equal free-again *proof-nil*)
              basic
            (proof-with-checked-results
                ((other-call (t3-books-choice-call name free-again))
                 (other-body (proof-subst body (t3-books-zip-bindings free free-again nil)))
                 (same (proof-eq call other-call))
                 (other-at-first (proof-subst other-body first-bindings))
                 (only-first (proof-ite chosen (proof-neg other-at-first) *proof-false*))
                 (second-bindings (t3-books-choice-bindings other-call bound))
                 (other-at-second (proof-subst other-body second-bindings))
                 (body-at-second (proof-subst body second-bindings)))
              (let ((only-second (proof-ite other-at-second (proof-neg body-at-second) *proof-false*)))
                (proof-ite basic
                           (proof-ite same same (proof-ite only-first only-first only-second))
                           *proof-false*)))))))))

(defun t3-books-step-line-argument (line)
  (proof-with-checked-results ((parsed (reader-reader-line (reader-reader-init line)))
                               (argument (proof-term-at (cadar parsed) 0)))
    (proof-freeze argument)))

(defun t3-books-computation-package (term)
  (proof-with-checked-results ((function (proof-term-at term 0)))
    (let ((package-arg
           (cond ((or (equal function (proof-sym "PKG-IMPORTS" "ACL2"))
                      (equal function (proof-sym "PKG-WITNESS" "ACL2")))
                  '(1 "str"))
                 ((equal function (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2")) '(1 "sym"))
                 ((equal function (proof-sym "INTERN-IN-PACKAGE-OF-SYMBOL" "ACL2")) '(2 "sym"))
                 (t nil))))
      (if (endp package-arg)
          :none
        (proof-with-checked-results ((arg (proof-term-at term (car package-arg)))
                                     (datum (proof-term-at arg 1)))
          (if (and (consp datum) (equal (car datum) (cadr package-arg)))
              (proof-term-at datum 1)
            :none))))))

; The patterns match a complete line ending in a close parenthesis.
; Only a line feed is a line boundary in the byte patterns.
(defun t3-books-step-line-matches-p (line prefix)
  (and (> (length line) (1+ (length prefix)))
       (text-starts-with line prefix)
       (text-ends-with line ")")))

(defun t3-books-step-arguments-lines (lines prefix packages-p reversed)
  (if (endp lines)
      reversed
    (if (t3-books-step-line-matches-p (car lines) prefix)
        (proof-with-checked-results
            ((argument (t3-books-step-line-argument (car lines)))
             (value (if packages-p (t3-books-computation-package argument) argument)))
          (t3-books-step-arguments-lines (cdr lines) prefix packages-p
                                        (if (eq value :none) reversed (cons value reversed))))
      (t3-books-step-arguments-lines (cdr lines) prefix packages-p reversed))))

(defun t3-books-step-arguments-entries (entries prefix packages-p reversed)
  (if (endp entries)
      (reverse reversed)
    (proof-with-checked-results
        ((entry (proof-list-of-length (car entries) 4))
         (source (cadddr entry))
         (lines (if (integerp source)
                    '(:failure "failure" "")
                  (text-split source (coerce (list #\Newline) 'string))))
         (arguments (t3-books-step-arguments-lines lines prefix packages-p reversed)))
      (t3-books-step-arguments-entries (cdr entries) prefix packages-p arguments))))

(defun t3-books-step-arguments (entries pattern)
  (cond ((endp entries) nil)
        ((equal pattern *t3-books-fact-line*)
         (t3-books-step-arguments-entries entries "(fact " nil nil))
        ((equal pattern *t3-books-compute-line*)
         (t3-books-step-arguments-entries entries "(compute " nil nil))
        (t (proof-with-checked-results ((entry (proof-list-of-length (car entries) 4)))
             '(:failure "failure" "")))))

(defun t3-books-used-packages (entries)
  (t3-books-step-arguments-entries entries "(compute " t nil))

(defun t3-books-fragment-init (entries facts packages reason)
  (list :t3-fragment entries facts packages reason))

(defun t3-books-fragment-entries (fragment)
  (cadr fragment))

(defun t3-books-fragment-facts (fragment)
  (caddr fragment))

(defun t3-books-fragment-packages (fragment)
  (cadddr fragment))

(defun t3-books-fragment-reason (fragment)
  (nth 4 fragment))

(defun t3-books-admit-definitions (definitions proof)
  (if (endp definitions)
      proof
    (proof-with-checked-results ((name (proof-term-at (car definitions) 0)))
      (if (assoc-equal name (proof-proof-definitions proof))
          (t3-books-admit-definitions (cdr definitions) proof)
        (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
          (if (integerp (cadr definition))
              '(:failure "failure" "")
            (t3-books-admit-definitions
             (cdr definitions)
             (proof-proof-add-definition proof name (cadr definition) (caddr definition)))))))))

(defun t3-books-admit-formulas (formulas facts)
  (if (endp formulas)
      facts
    (proof-with-checked-results ((formula (proof-list-of-length (car formulas) 2)))
      (let ((name (car formula)))
        (t3-books-admit-formulas
         (cdr formulas)
         (if (assoc-equal name facts)
             facts
           (table-put facts name (list (cadr formula)))))))))

(defun t3-books-admit-add-statement (proof kind data)
  (cond
   ((equal kind "define")
    (if (integerp data)
        '(:failure "failure" "")
      (t3-books-admit-definitions (cdr data) proof)))
   ((or (equal kind "theorem") (equal kind "axiom"))
    (proof-with-checked-results ((facts (t3-books-admit-formulas (list data) (proof-proof-facts proof))))
      (proof-proof-with-facts proof facts)))
   ((equal kind "constrain")
    (proof-with-checked-results ((formulas (proof-term-at data 1)))
      (cond ((equal formulas *proof-nil*) proof)
            ((integerp formulas) '(:failure "failure" ""))
            (t (proof-with-checked-results
                   ((facts (t3-books-admit-formulas formulas (proof-proof-facts proof))))
                 (proof-proof-with-facts proof facts))))))
   (t proof)))

(defun t3-books-admit (lib kind data)
  (proof-with-checked-results
      ((declared (t3-book-values-book-proofs-declaration lib kind data)))
    (let ((library (t3-book-values-book-proofs-library declared)))
      (proof-with-checked-results
          ((proof (t3-books-admit-add-statement (library-library-proof library) kind data))
           (updated (if (equal kind "choose")
                        (proof-with-checked-results ((formula (t3-books-choice data)))
                          (proof-proof-with-facts
                           proof (table-put (proof-proof-facts proof) (car data) (list formula))))
                      proof)))
        (t3-book-values-book-proofs-with-library
         declared (library-library-with-proof library updated))))))

(defun t3-books-package-state (lib package)
  (let ((exports (t3-book-values-book-proofs-packages lib))
        (visible (t3-book-values-book-proofs-visible lib)))
    (list (if (member-equal package visible) t nil)
          (table-values (table-get exports package nil)))))

(defun t3-books-fragment-facts-available-p (needed facts)
  (if (endp needed)
      t
    (and (equal (table-get facts (caar needed) nil) (cdar needed))
         (t3-books-fragment-facts-available-p (cdr needed) facts))))

(defun t3-books-fragment-packages-available-p (needed lib)
  (if (endp needed)
      t
    (and (equal (t3-books-package-state lib (caar needed)) (cdar needed))
         (t3-books-fragment-packages-available-p (cdr needed) lib))))

(defun t3-books-fragment-available (fragment lib)
  (let* ((library (t3-book-values-book-proofs-library lib))
         (proof (library-library-proof library)))
    (and (t3-books-fragment-facts-available-p (t3-books-fragment-facts fragment)
                                             (proof-proof-facts proof))
         (t3-books-fragment-packages-available-p (t3-books-fragment-packages fragment) lib))))

(defun t3-books-failure-kind-p (result kinds)
  (and (failure-p result) (member-equal (cadr result) kinds)))

(defun t3-books-recoverable-proof-failure-p (result)
  (t3-books-failure-kind-p
   result '("Unproved" "Unsupported" "MissingProofInput" "ProofMismatch"
            "value" "index" "key" "assertion")))

(defun t3-books-theorem-search (lib search name formula)
  (proof-with-checked-results ((found (t3-book-theorems-theorems-theorem search name formula)))
    (cons (car found) lib)))

(defun t3-books-theorem-proof (lib search name formula)
  (let* ((selected (t3-book-recipes-theorem-tactic formula))
         (tactic (if (t3-books-failure-kind-p selected
                     '("MalformedLambdaFormals" "Unsupported" "index" "type" "value"))
                     nil
                   selected)))
    (cond
     ((failure-p tactic) tactic)
     ((not tactic) (t3-books-theorem-search lib search name formula))
     (t
      (let ((proved (t3-book-recipes-apply tactic (t3-book-values-book-proofs-library lib) name formula)))
        (cond
         ((t3-books-recoverable-proof-failure-p proved)
          (let ((found (t3-books-theorem-search lib search name formula)))
            (if (t3-books-failure-kind-p found '("Unsupported"))
                '(:failure "Unsupported" "")
              found)))
         ((failure-p proved) proved)
         (t (cons (car proved) (t3-book-values-book-proofs-with-library lib (cdr proved))))))))))

(defun t3-books-constrain-proof (lib search declarations formulas)
  (proof-with-checked-results ((evaluator (t3-book-evaluators-evaluator-shape declarations formulas)))
    (let* ((library (t3-book-values-book-proofs-library lib))
           (evaluation (and evaluator (t3-book-evaluators-witness library declarations formulas)))
           (witness (if (or (not evaluator) (t3-books-recoverable-proof-failure-p evaluation))
                        (t3-tactics-witnesses library declarations formulas)
                      evaluation)))
      (cond
       ((not (failure-p witness))
        (cons (car witness) (t3-book-values-book-proofs-with-library lib (cdr witness))))
       ((t3-books-recoverable-proof-failure-p witness)
        (proof-with-checked-results
            ((proved (t3-book-witnesses-witness-proof library search declarations formulas)))
          (cons (car proved) (t3-book-values-book-proofs-with-library lib (cadr proved)))))
       (t witness)))))

(defun t3-books-generate-proof (lib search kind data measures)
  (cond
   ((equal kind "define")
    (proof-with-checked-results
        ((rulers (proof-term-at data 0))
         (proved (t3-book-measures-measure-proof
                  (t3-book-values-book-proofs-library lib) search rulers (cdr data) measures)))
      (cons (car proved) (t3-book-values-book-proofs-with-library lib (cadr proved)))))
   ((integerp data) '(:failure "failure" ""))
   ((equal kind "constrain")
    (if (equal (len data) 2)
        (t3-books-constrain-proof lib search (car data) (cadr data))
      '(:failure "failure" "")))
   (t
    (if (equal (len data) 2)
        (t3-books-theorem-proof lib search (car data) (cadr data))
      '(:failure "failure" "")))))

(defun t3-books-generate-supplied (entries)
  (if (endp entries)
      nil
    (proof-with-checked-results ((name (proof-term-at (car entries) 1))
                                 (names (t3-books-generate-supplied (cdr entries))))
      (cons name names))))

(defun t3-books-generate-facts (names supplied facts reversed)
  (if (endp names)
      (reverse reversed)
    (let ((name (car names)))
      (if (or (member-equal name supplied) (assoc-equal name reversed))
          (t3-books-generate-facts (cdr names) supplied facts reversed)
        (let ((found (assoc-equal name facts)))
          (if found
              (t3-books-generate-facts (cdr names) supplied facts (cons found reversed))
            '(:failure "failure" "")))))))

(defun t3-books-generate-packages (names lib reversed)
  (if (endp names)
      (reverse reversed)
    (let ((package (car names)))
      (t3-books-generate-packages
       (cdr names) lib
       (if (assoc-equal package reversed)
           reversed
         (acons package (t3-books-package-state lib package) reversed))))))

(defun t3-books-generate-fragment (entry lib)
  (let* ((library (t3-book-values-book-proofs-library lib))
         (proof (library-library-proof library)))
    (proof-with-checked-results
        ((source (proof-term-at entry 3))
         (auxiliary (t3-logic-libraryproofs-required-entries library source))
         (supplied (t3-books-generate-supplied auxiliary)))
      (let ((entries (append auxiliary (list entry))))
        (proof-with-checked-results
            ((fact-names (t3-books-step-arguments entries *t3-books-fact-line*))
             (facts (t3-books-generate-facts fact-names supplied (proof-proof-facts proof) nil))
             (package-names (t3-books-used-packages entries)))
          (t3-books-fragment-init entries facts (t3-books-generate-packages package-names lib nil) ""))))))

(defun t3-books-generate-result (result name)
  (if (t3-books-failure-kind-p result '("Unproved" "Unsupported" "value"))
      (proof-with-checked-results ((source (proof-line "skip" (list name))))
        (t3-books-fragment-init (list (list "skip" name nil source)) nil nil "unproved"))
    result))

(defun t3-books-generate (lib search kind name data measures)
  (let* ((library (t3-book-values-book-proofs-library lib))
         (start (len (library-library-entries library)))
         (proved (t3-books-generate-proof lib search kind data measures))
         (failed (failure-p proved))
         (extended (if failed library (t3-book-values-book-proofs-library (cdr proved))))
         (fragment (if failed proved (t3-books-generate-fragment (car proved) (cdr proved))))
         (result (t3-books-generate-result fragment name))
         (discarded (t3-logic-libraryproofs-discard-entries extended start)))
    (if (failure-p discarded) discarded result)))

; The prefix stores admitted source lines in reverse admission order.
(defun t3-books-prefix-digest (prefix)
  (siphash-hexdigest (text-join "" (reverse prefix))))

(defun t3-books-book-proofs-available (fragments lib)
  (if (endp fragments)
      nil
    (if (t3-books-fragment-available (car fragments) lib)
        (car fragments)
      (t3-books-book-proofs-available (cdr fragments) lib))))

(defun t3-books-book-proofs-fragment (raw kind name data lib search measures prefix cache failures)
  (let* ((candidates (table-get cache raw nil))
         (available (t3-books-book-proofs-available candidates lib)))
    (if available
        (list available cache failures)
      (let* ((key (list raw (t3-books-prefix-digest prefix) (table-get measures name nil)))
             (failed (table-get failures key nil)))
        (if failed
            (list failed cache failures)
          (proof-with-checked-results ((fragment (t3-books-generate lib search kind name data measures)))
            (if (equal (t3-books-fragment-reason fragment) "")
                (list fragment (table-put cache raw (append candidates (list fragment))) failures)
              (list fragment cache (table-put failures key fragment)))))))))

(defun t3-books-book-proofs-step-count (counts)
  (if (endp counts)
      0
    (+ (car counts) (t3-books-book-proofs-step-count (cdr counts)))))

(defun t3-books-book-proofs-emit (entries emitted chunks steps bytes)
  (if (endp entries)
      (list emitted chunks steps bytes)
    (proof-with-checked-results ((entry (proof-list-of-length (car entries) 4)))
      (let* ((kind (car entry))
             (name (cadr entry))
             (counts (caddr entry))
             (chunk (cadddr entry))
             (auxiliary (member-equal kind '("lemma" "define")))
             (retained (and auxiliary (assoc-equal name emitted))))
        (cond
         ((not retained)
          (t3-books-book-proofs-emit
           (cdr entries) (if auxiliary (table-put emitted name chunk) emitted)
           (cons chunk chunks) (+ steps (t3-books-book-proofs-step-count counts)) (+ bytes (length chunk))))
         ((equal (cdr retained) chunk)
          (t3-books-book-proofs-emit (cdr entries) emitted chunks steps bytes))
         (t (proof-with-checked-results ((symbol-text (proof-write name)))
              '(:failure "failure" ""))))))))

(defun t3-books-book-proofs-helpers (lib kind data)
  (if (not (equal kind "define"))
      lib
    (proof-with-checked-results ((names (termination-definition-names (cdr data))))
      (let ((library (t3-book-values-book-proofs-library lib)))
        (proof-with-checked-results
            ((library (if (member-equal *t3-book-lemmas-set-tail* names)
                          (t3-book-lemmas-set-tail library)
                        library))
             (library (if (member-equal *t3-book-halves-halve* names)
                          (t3-book-halves-halves library)
                        library)))
          (t3-book-values-book-proofs-with-library lib library))))))

(defun t3-books-book-proofs-index (search lib kind data)
  (let ((search (t3-book-theorems-theorems-with-lib search lib)))
    (if (equal kind "choose")
        (let* ((name (car data))
               (library (t3-book-values-book-proofs-library lib))
               (proof (library-library-proof library))
               (fact (assoc-equal name (proof-proof-facts proof))))
          (if fact
              (proof-with-checked-results ((formula (proof-term-at (cdr fact) 0)))
                (t3-book-theorems-theorems-index-fact search name formula))
            '(:failure "failure" "")))
      (t3-book-theorems-theorems-add search kind data))))

(defun t3-books-book-proofs-row (fragment book name emitted chunks rows distinct raw)
  (let* ((reason (t3-books-fragment-reason fragment))
         (proved (equal reason ""))
         (distinct (table-put distinct raw proved)))
    (proof-with-checked-results
        ((result (t3-books-book-proofs-emit (t3-books-fragment-entries fragment) emitted chunks 0 0))
         (written (proof-write name)))
      (let ((row (text-join (coerce (list #\Tab) 'string)
                          (list book written (if proved "proved" "skipped")
                                (decimal-text (caddr result)) (decimal-text (cadddr result)) reason))))
        (list (car result) (cadr result) (cons row rows) distinct)))))

(defun t3-books-book-proofs-statements (records book lib search measures seen prefix cache failures
                                              emitted chunks rows distinct)
  (declare (xargs :measure (acl2-count records)))
  (if (endp records)
      (list chunks rows distinct cache failures)
    (proof-with-checked-results ((record (proof-list-of-length (car records) 3)))
      (let ((raw (car record)) (kind (cadr record)) (data (caddr record)))
        (if (member-equal raw seen)
            (t3-books-book-proofs-statements (cdr records) book lib search measures seen prefix cache failures
                                             emitted chunks rows distinct)
          (proof-with-checked-results
              ((name (t3-books-obligation kind data))
               (candidate (if name
                              (t3-books-book-proofs-fragment
                               raw kind name data lib search measures prefix cache failures)
                            (list nil cache failures)))
               (output (if name
                           (t3-books-book-proofs-row (car candidate) book name emitted chunks rows distinct raw)
                         (list emitted chunks rows distinct)))
               (lib (t3-books-admit lib kind data))
               (lib (t3-books-book-proofs-helpers lib kind data))
               (search (t3-books-book-proofs-index search lib kind data)))
            (t3-books-book-proofs-statements
             (cdr records) book lib search measures (cons raw seen) (cons raw prefix)
             (cadr candidate) (caddr candidate)
             (car output) (cadr output) (caddr output) (cadddr output))))))))

(defun t3-books-book-proofs (book expected base library-lines library-measures cache failures statements aids)
  (proof-with-checked-results
      ((book-measures (t3-books-read-measures aids))
       (search (t3-book-theorems-theorems-init base))
       (result (t3-books-book-proofs-statements
                statements book base search (table-update library-measures book-measures)
                library-lines nil cache failures nil nil nil nil)))
    (let ((rows (cadr result)))
      (if (equal (len rows) expected)
          (list (list (concatenate 'string *t3-books-books* "/" book ".statements")
                      (text-join "" (reverse (car result))) (reverse rows) (caddr result))
                (cadddr result) (nth 4 result))
        '(:failure "failure" "")))))
