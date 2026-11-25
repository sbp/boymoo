(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-tactics-exported-nfix* (proof-sym "NFIX" "ACL2"))
(defconst *t3-tactics-components*
  (list (proof-cl "REALPART") (proof-cl "IMAGPART")
        (proof-cl "NUMERATOR") (proof-cl "DENOMINATOR")))
(defconst *t3-tactics-divisions* (list (proof-cl "TRUNCATE") (proof-cl "FLOOR")))
(defconst *t3-tactics-abs* (proof-cl "ABS"))

(mutual-recursion
 (defun t3-tactics-replace-functions (term mapping)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) term)
    ((endp term) '(:failure "unproved" ""))
    ((proof-compound (car term))
     (if (not (consp (cddar term)))
         '(:failure "missing-proof-input" "")
       (proof-with-checked-results
           ((body (t3-tactics-replace-functions (caddar term) mapping))
            (args (t3-tactics-replace-functions-args (cdr term) mapping)))
         (cons (list (caar term) (cadar term) body) args))))
    (t (let ((head (table-get mapping (car term) (car term))))
         (proof-with-checked-results
             ((args (t3-tactics-replace-functions-args (cdr term) mapping)))
           (cons head args))))))
 (defun t3-tactics-replace-functions-args (args mapping)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((arg (t3-tactics-replace-functions (car args) mapping))
          (rest (t3-tactics-replace-functions-args (cdr args) mapping)))
       (cons arg rest)))))

(defun t3-tactics-witness-names-collect (declarations names)
  (if (endp declarations)
      names
    (proof-with-checked-results
        ((parts (proof-list-of-length (car declarations) 2))
         (printed (proof-write (car parts)))
         (name (proof-sym (concatenate 'string "T3-WITNESS-"
                                       (text-upper (siphash-hexdigest printed))) "ACL2")))
      (t3-tactics-witness-names-collect (cdr declarations) (table-put names (car parts) name)))))

(defun t3-tactics-witness-names (declarations)
  (t3-tactics-witness-names-collect declarations nil))

(defun t3-tactics-witness-formals (indices)
  (if (endp indices)
      nil
    (cons (proof-sym (concatenate 'string "T3-ARG-" (decimal-text (car indices))) "ACL2")
          (t3-tactics-witness-formals (cdr indices)))))

(defun t3-tactics-witness-definition-loop (lib declarations names)
  (declare (xargs :measure (acl2-count declarations)))
  (if (endp declarations)
      lib
    (proof-with-checked-results
        ((parts (proof-list-of-length (car declarations) 2))
         (formals (t3-tactics-witness-formals (seq-range 0 (cadr parts) 1)))
         (lib (library-library-definition lib (table-get names (car parts) nil)
                                          formals *proof-false*)))
      (t3-tactics-witness-definition-loop lib (cdr declarations) names))))

(defun t3-tactics-witness-proof-loop (lib formulas names definitions)
  (if (endp formulas)
      nil
    (proof-with-checked-results
        ((parts (proof-list-of-length (car formulas) 2))
         (goal (t3-tactics-replace-functions (cadr parts) names))
         (step (t3-logic-libraryproofs-prove-formula lib goal definitions nil))
         (rest (t3-tactics-witness-proof-loop lib (cdr formulas) names definitions)))
      (cons step rest))))

(defun t3-tactics-witnesses (lib declarations formulas)
  (proof-with-checked-results
      ((names (t3-tactics-witness-names declarations))
       (lib (t3-tactics-witness-definition-loop lib declarations names))
       (symbols (table-values names))
       (definitions (append (list *library-implies* *proof-not* (proof-cl "ATOM")
                                  (proof-sym "MV-NTH" "ACL2") (proof-sym "SYNP" "ACL2"))
                            symbols))
       (proofs (t3-tactics-witness-proof-loop lib formulas names definitions))
       (declaration (proof-term-at declarations 0))
       (first (proof-term-at declaration 0))
       (entry (proof-proof-entry "witness" first (cons first symbols) proofs)))
    (cons entry lib)))

(defund t3-tactics-actual-value-opening (term)
  (cond
   ((or (endp term) (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
   ((member-equal (car term) *t3-logic-wrappers*)
    (proof-with-checked-results ((body (proof-term-at term 3)))
      (list body)))
   ((proof-compound (car term))
    (proof-with-checked-results
        ((parts (proof-list-of-length (car term) 3))
         (formals (if (equal (cadr parts) *proof-nil*) nil (cadr parts)))
         (bindings (proof-bindings-table (seq-zip formals (cdr term)) nil))
         (body (proof-subst (caddr parts) bindings)))
      (list body)))
   (t nil)))

(defun t3-tactics-actual-value-visit (n term)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t3-tactics-actual-value-visit")
    (proof-with-checked-results ((opening (t3-tactics-actual-value-opening term)))
      (if opening
          (t3-tactics-actual-value-visit (1- n) (car opening))
        term))))

(defun t3-tactics-actual-value (term)
  (t3-tactics-actual-value-visit 1000000 term))

(defun t3-tactics-actual-values (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((value (t3-tactics-actual-value (car terms)))
         (rest (t3-tactics-actual-values (cdr terms))))
      (cons value rest))))

(defun t3-tactics-clock-edges (calls name)
  (cond ((endp calls) nil)
        ((equal (termination-call-caller (car calls)) name)
         (cons (car calls) (t3-tactics-clock-edges (cdr calls) name)))
        (t (t3-tactics-clock-edges (cdr calls) name))))

(defun t3-tactics-clock-guard-p (edges test)
  (if (endp edges)
      t
    (and (member-equal test (termination-call-tests (car edges)))
         (t3-tactics-clock-guard-p (cdr edges) test))))

(defun t3-tactics-clock-candidates (formals edges index)
  (if (endp formals)
      nil
    (let ((guard (list (list *t3-logic-zp* (car formals)) nil)))
      (if (and edges (t3-tactics-clock-guard-p edges guard))
          (cons (list index (car formals))
                (t3-tactics-clock-candidates (cdr formals) edges (1+ index)))
        (t3-tactics-clock-candidates (cdr formals) edges (1+ index))))))

(defun t3-tactics-clock-collect (definitions calls clocks)
  (if (endp definitions)
      clocks
    (proof-with-checked-results ((parts (proof-list-of-length (car definitions) 3)))
      (if (equal (cadr parts) *proof-nil*)
          nil
        (let* ((edges (t3-tactics-clock-edges calls (car parts)))
               (candidates (t3-tactics-clock-candidates (cadr parts) edges 0)))
          (and (equal (len candidates) 1)
               (t3-tactics-clock-collect
                (cdr definitions) calls (table-put clocks (car parts) (car candidates)))))))))

(defun t3-tactics-map-lookup (mapping key)
  (let ((entry (assoc-equal key mapping)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun t3-tactics-clock-edges-valid-p (calls clocks)
  (if (endp calls)
      t
    (let ((call (car calls)))
      (proof-with-checked-results
          ((callee (t3-tactics-map-lookup clocks (termination-call-callee call)))
           (caller (t3-tactics-map-lookup clocks (termination-call-caller call)))
           (actual (proof-term-at (termination-call-actuals call) (car callee)))
           (smaller (t3-tactics-actual-value actual)))
        (if (not (proof-is-call smaller *proof-plus*))
            nil
          (proof-with-checked-results ((values (t3-tactics-actual-values (cdr smaller))))
            (and (or (equal values (list *proof-neg-one* (cadr caller)))
                     (equal values (list (cadr caller) *proof-neg-one*)))
                 (t3-tactics-clock-edges-valid-p (cdr calls) clocks))))))))

(defun t3-tactics-clock-measures (clocks)
  (if (endp clocks)
      nil
    (cons (cons (caar clocks) (list *library-count* (caddar clocks)))
          (t3-tactics-clock-measures (cdr clocks)))))

(defun t3-tactics-clock-plan (definitions calls)
  (proof-with-checked-results ((clocks (t3-tactics-clock-collect definitions calls nil)))
    (if (and definitions (not clocks))
        nil
      (proof-with-checked-results ((valid (t3-tactics-clock-edges-valid-p calls clocks)))
        (and valid (t3-tactics-clock-measures clocks))))))

(defun t3-tactics-numeric-actuals (calls index)
  (if (endp calls)
      nil
    (proof-with-checked-results
        ((actual (proof-term-at (termination-call-actuals (car calls)) index))
         (value (t3-tactics-actual-value actual))
         (rest (t3-tactics-numeric-actuals (cdr calls) index)))
      (cons value rest))))

(defun t3-tactics-numeric-values-p (values variable)
  (or (endp values)
      (and (proof-compound (car values))
           (consp (cdar values))
           (equal (cadar values) variable)
           (t3-tactics-numeric-values-p (cdr values) variable))))

(defun t3-tactics-numeric-plan-visit (name formals calls index)
  (if (endp formals)
      nil
    (proof-with-checked-results ((values (t3-tactics-numeric-actuals calls index)))
      (let ((variable (car formals)))
        (if (and values (t3-tactics-numeric-values-p values variable))
            (let ((heads (strip-cars values)))
              (cond ((subsetp-equal heads *t3-tactics-components*)
                     (list (cons name (list *library-count* variable))))
                    ((and (intersectp-equal heads *t3-tactics-divisions*)
                          (subsetp-equal heads (append *t3-tactics-divisions*
                                                      (list *t3-tactics-abs* *proof-minus*))))
                     (list (cons name (t3-quotient-digit-measure variable))))
                    (t (t3-tactics-numeric-plan-visit name (cdr formals) calls (1+ index)))))
          (t3-tactics-numeric-plan-visit name (cdr formals) calls (1+ index)))))))

(defun t3-tactics-numeric-plan (definition calls)
  (proof-with-checked-results ((parts (proof-list-of-length definition 3)))
    (t3-tactics-numeric-plan-visit (car parts)
                                   (if (equal (cadr parts) *proof-nil*) nil (cadr parts))
                                   calls 0)))

(defun t3-tactics-gap-unclip (measure)
  (if (proof-is-call measure *proof-if*)
      (proof-with-checked-results ((yes (proof-term-at measure 2)))
        (if (equal yes *proof-zero*) (proof-term-at measure 3) measure))
    measure))

(defun t3-tactics-gap-endpoints (measure)
  (proof-with-checked-results ((measure (t3-tactics-gap-unclip measure)))
    (and (proof-is-call measure *t3-tactics-exported-nfix*)
         (proof-with-checked-results ((delta (proof-term-at measure 1)))
           (and (proof-is-call delta *proof-plus*)
                (proof-with-checked-results ((minus (proof-term-at delta 2)))
                  (and (proof-is-call minus *proof-minus*)
                       (proof-with-checked-results
                           ((upper (proof-term-at delta 1))
                            (lower (proof-term-at minus 1)))
                         (list upper lower)))))))))

(defun t3-tactics-selector-measures (selectors)
  (if (endp selectors)
      nil
    (cons (cons (caar selectors) (list *library-count* (cdar selectors)))
          (t3-tactics-selector-measures (cdr selectors)))))

(defun t3-tactics-heuristic-plan (definitions calls)
  (proof-with-checked-results ((selectors (termination-selector-plan definitions calls)))
    (if selectors
        (t3-tactics-selector-measures selectors)
      (proof-with-checked-results ((clocks (t3-tactics-clock-plan definitions calls)))
        (or clocks
            (and (equal (len definitions) 1)
                 (t3-tactics-numeric-plan (car definitions) calls)))))))

(defun t3-tactics-exported-measures (definitions stored measures)
  (if (endp definitions)
      measures
    (proof-with-checked-results ((parts (proof-list-of-length (car definitions) 3)))
      (let ((entry (assoc-equal (car parts) stored)))
        (t3-tactics-exported-measures
         (cdr definitions) stored (if entry (table-put measures (car entry) (cdr entry)) measures))))))

(defun t3-tactics-exported-endpoints (measures)
  (if (endp measures)
      nil
    (proof-with-checked-results
        ((endpoints (t3-tactics-gap-endpoints (cdar measures)))
         (rest (t3-tactics-exported-endpoints (cdr measures))))
      (cons (cons (caar measures) endpoints) rest))))

(defun t3-tactics-all-endpoints-p (endpoints)
  (or (endp endpoints)
      (and (cdar endpoints) (t3-tactics-all-endpoints-p (cdr endpoints)))))

(defun t3-tactics-gap-measures (endpoints advance)
  (if (endp endpoints)
      nil
    (let ((upper (cadar endpoints))
          (lower (caddar endpoints)))
      (cons (cons (caar endpoints)
                  (list *library-gap* (if advance (library-plus *proof-one* upper) upper) lower))
            (t3-tactics-gap-measures (cdr endpoints) advance)))))

(defun t3-tactics-prefixed-measures (measures)
  (if (endp measures)
      nil
    (proof-with-checked-results
        ((measure (t3-tactics-replace-functions
                   (cdar measures) (list (cons *t3-tactics-exported-nfix* *library-nfix*))))
         (rest (t3-tactics-prefixed-measures (cdr measures))))
      (cons (cons (caar measures) measure) rest))))

(defun t3-tactics-exported-plan (definitions stored)
  (proof-with-checked-results ((measures (t3-tactics-exported-measures definitions stored nil)))
    (if (not (equal (len measures) (len definitions)))
        nil
      (proof-with-checked-results ((endpoints (t3-tactics-exported-endpoints measures)))
        (if (t3-tactics-all-endpoints-p endpoints)
            (cons (t3-tactics-gap-measures endpoints nil) (list :advance endpoints measures))
          (proof-with-checked-results ((plan (t3-tactics-prefixed-measures measures)))
            (cons plan :done)))))))

(defun t3-tactics-heuristic-or-exported-plan (definitions calls stored)
  (proof-with-checked-results ((heuristic (t3-tactics-heuristic-plan definitions calls)))
    (if heuristic
        (cons heuristic :exported)
      (t3-tactics-exported-plan definitions stored))))

(defun t3-tactics-formatting-or-heuristic-plan (first definitions calls stored)
  (if (equal first *t3-formatting-fmt-tilde*)
      (cons (list (cons first (t3-formatting-formatting-measure
                              (proof-sym "I" "ACL2") (proof-sym "MAXIMUM" "ACL2")
                              (proof-sym "COL" "ACL2"))))
            :heuristic)
    (t3-tactics-heuristic-or-exported-plan definitions calls stored)))

(defund t3-tactics-measure-plan-next (definitions calls stored phase)
  (cond
   ((eq phase :start)
    (proof-with-checked-results
        ((definition (proof-term-at definitions 0))
         (parts (proof-list-of-length definition 3)))
      (let ((first (car parts)))
        (if (equal first *t3-genvar-genvar*)
            (proof-with-checked-results ((measure (t3-genvar-genvar-measure (cadr parts))))
              (cons (list (cons first measure)) :formatting))
          (t3-tactics-formatting-or-heuristic-plan first definitions calls stored)))))
   ((eq phase :formatting)
    (t3-tactics-formatting-or-heuristic-plan (caar definitions) definitions calls stored))
   ((eq phase :heuristic) (t3-tactics-heuristic-or-exported-plan definitions calls stored))
   ((eq phase :exported) (t3-tactics-exported-plan definitions stored))
   ((eq (car phase) :advance)
    (cons (t3-tactics-gap-measures (cadr phase) t) (list :prefix (caddr phase))))
   ((eq (car phase) :prefix)
    (proof-with-checked-results ((plan (t3-tactics-prefixed-measures (cadr phase))))
      (cons plan :done)))
   (t nil)))

(defun t3-tactics-ordinal (lib measure)
  (proof-with-checked-results
      ((direct (descent-direct-builtin lib (list (list *proof-ordinalp* measure)) nil)))
    (cond
     ((car direct) (cons (car direct) lib))
     ((proof-is-call measure *library-gap*)
      (proof-with-checked-results ((step (library-library-cite lib "GAP-ORDINAL" (cdr measure) nil)))
        (cons step lib)))
     ((proof-is-call measure *library-nfix*)
      (proof-with-checked-results ((step (library-library-cite lib "NFIX-ORDINAL" (cdr measure) nil)))
        (cons step lib)))
     ((proof-is-call measure *t3-size-make-ord*) (t3-size-ordinal-phase lib measure))
     (t (proof-with-checked-results ((phase (t3-size-phase-count measure)))
          (proof-with-checked-results
              ((step (if phase
                         (t3-size-ordinal-doubled lib measure)
                       (proof-with-checked-results
                           ((natural (t3-logic-libraryproofs-natural lib measure)))
                         (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural))))))
            (cons step lib)))))))

(defun t3-tactics-list-tail-descent (lib smaller larger evidence)
  (if (proof-is-call larger *library-len*)
      (proof-with-checked-results ((term (proof-term-at larger 1)))
        (if (equal smaller (list *library-len* (list *library-cdr* term)))
            (t3-size-length-tail lib term evidence)
          '(:failure "unsupported" "")))
    '(:failure "unsupported" "")))

(defun t3-tactics-shifted-tail (lib smaller larger offset prefix evidence)
  (proof-with-checked-results
      ((step (t3-tactics-list-tail-descent lib smaller larger evidence))
       (shifted (t3-size-shift lib (car step) offset prefix nil)))
    (cons shifted (cdr step))))

(defun t3-tactics-length-sum-descent (lib smaller larger evidence)
  (proof-with-checked-results
      ((first-left (proof-term-at smaller 1))
       (first-right (proof-term-at larger 1))
       (second-left (proof-term-at smaller 2))
       (second-right (proof-term-at larger 2)))
    (cond
     ((equal first-left first-right)
      (t3-tactics-shifted-tail lib second-left second-right first-right t evidence))
     ((equal second-left second-right)
      (t3-tactics-shifted-tail lib first-left first-right second-right nil evidence))
     (t
      (proof-with-checked-results
          ((left-arguments (proof-list-of-length (cdr smaller) 2))
           (right-arguments (proof-list-of-length (cdr larger) 2))
           (first (t3-tactics-shifted-tail lib (car left-arguments) (car right-arguments)
                                           (cadr left-arguments) nil evidence))
           (second (t3-tactics-shifted-tail lib (cadr left-arguments) (cadr right-arguments)
                                            (car right-arguments) t (cdr first)))
           (result (t3-size-chain lib (car first) (car second) nil)))
        (cons result (cdr second)))))))

(defun t3-tactics-alternating-projection-p (smaller)
  (and (proof-is-call smaller *library-len*)
       (proof-with-checked-results
           ((part (proof-term-at smaller 1))
            (head (proof-term-at part 0)))
         (member-equal head (list *t3-size-evens* *t3-size-odds*)))))

(defun t3-tactics-length-descent (lib smaller larger evidence)
  (proof-with-checked-results ((alternating (t3-tactics-alternating-projection-p smaller)))
    (if alternating
        (t3-size-alternating-length lib smaller larger evidence)
      (proof-with-checked-results
          ((result (if (and (proof-is-call larger *proof-plus*) (proof-is-call smaller *proof-plus*))
                       (t3-tactics-length-sum-descent lib smaller larger evidence)
                     (t3-tactics-list-tail-descent lib smaller larger evidence))))
        (list (car result) lib (cdr result))))))

(defun t3-tactics-descent-result (step method lib)
  (if (failure-p step)
      step
    (cons (list step method) lib)))

(defun t3-tactics-descent-constructed (lib smaller larger evidence)
  (proof-with-checked-results
      ((negated (t3-trees-negated-literal-descent lib smaller larger evidence))
       (result (if (caar negated)
                   negated
                 (t3-trees-parsed-guard-descent (cdr negated) smaller larger (cadar negated)))))
    (if (caar result)
        (t3-tactics-descent-result (caar result) "constructed terms" (cdr result))
      (proof-with-checked-results
          ((selector (t3-size-count-descent (cdr result) smaller larger (cadar result))))
        (t3-tactics-descent-result (car selector) "selector paths" (cdr result))))))

(defun t3-tactics-descent-count (lib smaller larger evidence)
  (proof-with-checked-results ((rational (t3-rational-rational-descent lib smaller larger evidence)))
    (if (car rational)
        (t3-tactics-descent-result (car rational) "rational components" (cadr rational))
      (t3-tactics-descent-constructed (cadr rational) smaller larger (cddr rational)))))

(defun t3-tactics-descent-gap (lib main smaller larger call evidence)
  (if (equal (termination-call-caller call) *t3-genvar-genvar*)
      (proof-with-checked-results ((result (t3-genvar-descent lib main call)))
        (t3-tactics-descent-result (car result) "finite name bounds" (cdr result)))
    (proof-with-checked-results
        ((argument (proof-term-at smaller 2))
         (inferred (t3-scan-infer-scan-result lib argument evidence))
         (result (t3-arithmetic-gap-descent (car inferred) smaller larger (cdr inferred))))
      (t3-tactics-descent-result (car result) "integer gaps" (car inferred)))))

(defun t3-tactics-descent-with-phase (lib smaller larger evidence)
  (proof-with-checked-results ((result (t3-size-doubled-descent lib smaller larger evidence t)))
    (if (not (eq (car result) :t3-size-transformed))
        (t3-tactics-descent-result (car result) "integer phases" (cadr result))
      (proof-with-checked-results
          ((bound (t3-printing-printing-count-with-evidence
                   lib (cadr result) (caddr result) (cadddr result)))
           (result (t3-size-doubled-descent-from-bound
                    (cdr bound) smaller larger (cadar bound) (caar bound))))
        (t3-tactics-descent-result (car result) "integer phases" (cadr result))))))

(defun t3-tactics-descent-length (lib smaller larger evidence)
  (proof-with-checked-results
      ((result (t3-tactics-length-descent lib smaller larger evidence))
       (lib (cadr result))
       (order (t3-size-ordinal-comparison lib smaller larger))
       (step (proof-proof-transport (library-library-proof lib) (car result) order)))
    (t3-tactics-descent-result step "list lengths" lib)))

(defun t3-tactics-descent-other (lib main smaller larger evidence)
  (proof-with-checked-results ((phase (t3-size-phase-count larger)))
    (if phase
        (t3-tactics-descent-with-phase lib smaller larger evidence)
      (proof-with-checked-results ((digit (t3-quotient-is-digit-measure larger)))
        (cond
         (digit
          (proof-with-checked-results ((result (t3-quotient-digit-descent lib smaller larger evidence)))
            (t3-tactics-descent-result (caar result) "integer quotient bounds" (cdr result))))
         ((or (proof-is-call larger *library-len*) (proof-is-call larger *proof-plus*))
          (t3-tactics-descent-length lib smaller larger evidence))
         (t (proof-with-checked-results ((printed (proof-write main)))
              '(:failure "unsupported" ""))))))))

(defun t3-tactics-descent-measures (lib main smaller larger call evidence)
  (cond
   ((and (proof-is-call larger *library-count*) (proof-is-call smaller *library-count*))
    (t3-tactics-descent-count lib smaller larger evidence))
   ((proof-is-call larger *library-gap*)
    (t3-tactics-descent-gap lib main smaller larger call evidence))
   ((proof-is-call larger *library-nfix*)
    (proof-with-checked-results ((result (t3-arithmetic-clipped-descent lib smaller larger evidence)))
      (t3-tactics-descent-result (car result) "integer countdowns" lib)))
   ((proof-is-call larger *t3-size-make-ord*)
    (if (equal (termination-call-caller call) *t3-formatting-fmt-tilde*)
        (proof-with-checked-results
            ((result (t3-formatting-formatting-descent lib smaller larger evidence)))
          (t3-tactics-descent-result (car result) "index and column phases" (cadr result)))
      (proof-with-checked-results ((result (t3-size-ordinal-descent lib smaller larger evidence)))
        (t3-tactics-descent-result (car result) "ordinal phases" (cadr result)))))
   (t (t3-tactics-descent-other lib main smaller larger evidence))))

(defconst *t3-tactics-descent-definitions*
  (list *t3-logic-zp* *t3-logic-zpf* (proof-sym "WEAK-BRR-DATA-P" "ACL2")
        (proof-sym "FIXNAT-GUARD" "ACL2") (proof-sym "UNSIGNED-BYTE-P" "ACL2")
        (proof-sym "INTEGER-RANGE-P" "ACL2")))

(defun t3-tactics-descent-call (lib clause goal call)
  (proof-with-checked-results
      ((evidence (t3-logic-evidence-init lib (termination-call-tests call) nil
                                        *t3-tactics-descent-definitions*))
       (opened (t3-logic-libraryproofs-normalize lib goal nil nil))
       (main (if opened (proof-rewritten-term opened) goal))
       (parts (proof-list-of-length main 3))
       (structural (t3-size-direct-builtin lib (append (butlast clause 1) (list main)) evidence))
       (result (if (car structural)
                   (t3-tactics-descent-result (car structural) "ground clauses" lib)
                 (t3-tactics-descent-measures lib main (cadr parts) (caddr parts) call (cdr structural)))))
    (if (not opened)
        result
      (let ((lib (cdr result)))
        (t3-tactics-descent-result
         (proof-proof-transport (library-library-proof lib) (caar result) opened)
         (cadar result) lib)))))

(defun t3-tactics-descent (lib clause call)
  (proof-with-checked-results ((direct (descent-direct-builtin lib clause nil)))
    (cond ((car direct) (t3-tactics-descent-result (car direct) "ground clauses" lib))
          ((not call)
           (proof-with-checked-results
               ((measure (proof-term-at (car (last clause)) 1))
                (result (t3-tactics-ordinal lib measure)))
             (t3-tactics-descent-result (car result) "" (cdr result))))
          (t (t3-tactics-descent-call lib clause (car (last clause)) call)))))

(defun t3-tactics-measure-failed-p (result)
  (eq (car result) :t3-tactics-measure-failed))

(defun t3-tactics-measure-failure (error lib)
  (list :t3-tactics-measure-failed error lib))

(defund t3-tactics-prove-measure-case (case-result progress)
  (let ((lib (car progress)))
    (cond
     ((failure-p case-result) (t3-tactics-measure-failure case-result lib))
     ((member-equal (car case-result) (cadddr progress)) progress)
     (t
      (let* ((clause (car case-result))
             (call (cadr case-result))
             (result (t3-tactics-descent lib clause call)))
        (if (failure-p result)
            (t3-tactics-measure-failure result lib)
          (let* ((lib (cdr result))
                 (step (proof-proof-subsume (library-library-proof lib) (caar result) clause)))
            (if (failure-p step)
                (t3-tactics-measure-failure step lib)
              (list lib
                    (cons step (cadr progress))
                    (if call (add-to-set-equal (cadar result) (caddr progress)) (caddr progress))
                    (cons clause (cadddr progress)))))))))))

(defun t3-tactics-prove-measure-ordinalities (definitions measures progress)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      progress
    (let* ((cases (termination-ordinality-cases (list (car definitions)) measures))
           (result (t3-tactics-prove-measure-case (if (failure-p cases) cases (car cases)) progress)))
      (if (t3-tactics-measure-failed-p result)
          result
        (t3-tactics-prove-measure-ordinalities (cdr definitions) measures result)))))

(defun t3-tactics-prove-measure-calls (calls measures formals progress)
  (declare (xargs :measure (acl2-count calls)))
  (if (endp calls)
      progress
    (let* ((cases (termination-call-cases (list (car calls)) measures formals))
           (result (t3-tactics-prove-measure-case (if (failure-p cases) cases (car cases)) progress)))
      (if (t3-tactics-measure-failed-p result)
          result
        (t3-tactics-prove-measure-calls (cdr calls) measures formals result)))))

(defun t3-tactics-measure-fields (definitions measures)
  (if (endp definitions)
      nil
    (proof-with-checked-results
        ((measure (t3-tactics-map-lookup measures (caar definitions)))
         (rest (t3-tactics-measure-fields (cdr definitions) measures)))
      (cons measure rest))))

(defun t3-tactics-measure-entry (definitions measures progress)
  (proof-with-checked-results
      ((definition (proof-term-at definitions 0))
       (first (proof-term-at definition 0))
       (fields (t3-tactics-measure-fields definitions measures))
       (entry (proof-proof-entry "measure" first (cons first fields) (reverse (cadr progress)))))
    (list entry (text-join ", " (seq-sorted (caddr progress))))))

(defun t3-tactics-prove-measure-attempt (lib definitions calls measures)
  (let ((formals (termination-formals definitions nil nil)))
    (if (failure-p formals)
        (t3-tactics-measure-failure formals lib)
      (let ((progress (t3-tactics-prove-measure-ordinalities definitions measures (list lib nil nil nil))))
        (if (t3-tactics-measure-failed-p progress)
            progress
          (let ((progress (t3-tactics-prove-measure-calls calls measures formals progress)))
            (if (t3-tactics-measure-failed-p progress)
                progress
              (let ((entry (t3-tactics-measure-entry definitions measures progress)))
                (if (failure-p entry)
                    (t3-tactics-measure-failure entry (car progress))
                  (cons entry (car progress)))))))))))

(defund t3-tactics-plan-attempt (lib definitions calls stored phase start error)
  (proof-with-checked-results ((next (t3-tactics-measure-plan-next definitions calls stored phase)))
    (if (not next)
        error
      (let ((result (t3-tactics-prove-measure-attempt lib definitions calls (car next))))
        (if (not (t3-tactics-measure-failed-p result))
            result
          (let ((error (cadr result)))
            (if (not (member-equal (cadr error) '("unproved" "unsupported" "value")))
                error
              (proof-with-checked-results
                  ((lib (t3-logic-libraryproofs-discard-entries (caddr result) start)))
                (list :retry lib (cdr next) error)))))))))

(defun t3-tactics-try-plans (n lib definitions calls stored phase start error)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t3-tactics-try-plans")
    (let ((result (t3-tactics-plan-attempt lib definitions calls stored phase start error)))
      (if (eq (car result) :retry)
          (t3-tactics-try-plans (1- n) (cadr result) definitions calls stored
                               (caddr result) start (cadddr result))
        result))))

(defun t3-tactics-termination (lib rulers definitions stored)
  (proof-with-checked-results
      ((calls (termination-recursive-calls rulers definitions))
       (definition (proof-term-at definitions 0))
       (first (proof-term-at definition 0))
       (lib (if (equal first *t3-genvar-genvar*) (t3-genvar-build lib) lib)))
    (t3-tactics-try-plans 1000000 lib definitions calls stored :start
                         (len (library-library-entries lib))
                         '(:failure "unsupported" ""))))
