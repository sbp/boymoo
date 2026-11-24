(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h3-book-tactics-iff* (proof-sym "IFF" "ACL2"))

(defconst *h3-book-tactics-definitions*
  (append *h3-book-descent-transparent*
          (list *h3-book-tactics-iff*
                (proof-sym "HIDE" "ACL2")
                (proof-sym "THE-CHECK" "ACL2")
                (proof-sym "FIX" "ACL2"))))

(defconst *h3-book-tactics-boolean-rules*
  (list "booleanp-consp" "booleanp-integerp" "booleanp-rationalp"
        "booleanp-complex-rationalp" "booleanp-acl2-numberp" "booleanp-stringp"
        "booleanp-symbolp" "booleanp-<" (proof-sym "BOOLEANP-CHARACTERP" "ACL2")))

(defun h3-book-tactics-support-names (names)
  (if (endp names)
      nil
    (cons (if (equal (car names) "consp-cons")
              (car names)
            (proof-sym (car names) "ACL2"))
          (h3-book-tactics-support-names (cdr names)))))

(defconst *h3-book-tactics-fixed-rules*
  (append (h3-book-tactics-support-names *h3-book-descent-support*)
          (list "integerp-binary-+" "integerp-binary-*" "integerp-unary--"
                "rationalp-binary-+" "rationalp-binary-*" "rationalp-unary--"
                "rationalp-unary-/" "rationalp-acl2-numberp"
                (proof-sym "INTEGER-IMPLIES-RATIONAL" "ACL2"))
          *h3-book-tactics-boolean-rules*))

(defconst *h3-book-tactics-clause-types*
  '("PSEUDO-TERM-LISTP-DISJOIN-LST" "PSEUDO-TERMP-CONJOIN"
    "PSEUDO-TERMP-CONJOIN-CLAUSES" "PSEUDO-TERMP-DISJOIN"))

(defconst *h3-book-tactics-set-count-theorems*
  '("HEAD-COUNT" "HEAD-COUNT-BUILT-IN" "TAIL-COUNT" "TAIL-COUNT-BUILT-IN"))

(defconst *h3-book-tactics-term* (proof-sym "PSEUDO-TERMP" "ACL2"))
(defconst *h3-book-tactics-terms* (proof-sym "PSEUDO-TERM-LISTP" "ACL2"))

(mutual-recursion
 (defun h3-book-tactics-subterms (term)
   (declare (xargs :measure (acl2-count term)))
   (if (and (consp term) (proof-compound term)
            (not (proof-is-call term *proof-quote*)))
       (cons term (h3-book-tactics-subterm-list (cdr term)))
     (list term)))
 (defun h3-book-tactics-subterm-list (terms)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (append (h3-book-tactics-subterms (car terms))
             (h3-book-tactics-subterm-list (cdr terms))))))

; Count at most LIMIT subterms, visiting the arguments in order.
(mutual-recursion
 (defun h3-book-tactics-subterm-count (term limit)
   (declare (xargs :measure (acl2-count term)))
   (if (zp limit)
       0
     (if (and (consp term) (proof-compound term)
              (not (proof-is-call term *proof-quote*)))
         (1+ (h3-book-tactics-subterm-count-list (cdr term) (1- limit)))
       1)))
 (defun h3-book-tactics-subterm-count-list (terms limit)
   (declare (xargs :measure (acl2-count terms)))
   (if (or (endp terms) (zp limit))
       0
     (let ((count (h3-book-tactics-subterm-count (car terms) limit)))
       (+ count (h3-book-tactics-subterm-count-list (cdr terms) (- limit count)))))))

(defun h3-book-tactics-book-search-init
    (lib definitions calls rules budget inference-budget deep inside-first)
  (h3-rewrite-search-with-book-options
   (h3-rewrite-search-init lib definitions calls rules budget deep)
   inference-budget inside-first))

(defun h3-book-tactics-book-search-arguments-first (search term)
  (h3-rewrite-search-arguments-first search term))

(defun h3-book-tactics-book-search-rewrite-atom (search value evidence)
  (h3-rewrite-search-rewrite-atom search value evidence))

(defun h3-book-tactics-book-search-visit-term (search)
  (h3-rewrite-search-visit-term search))

(defun h3-book-tactics-book-search-evaluate (search term)
  (h3-rewrite-search-evaluate search term))

(defun h3-book-tactics-book-search-should-unfold (search term)
  (h3-rewrite-search-should-unfold search term))

(defun h3-book-tactics-book-search-reduce (search term evidence tests active)
  (h3-rewrite-search-reduce search term evidence tests active))

(defun h3-book-tactics-book-search-derive (search term evidence active tests)
  (h3-rewrite-search-derive search term evidence active tests))

(defun h3-book-tactics-fact-index-count (index)
  (cadr index))

(defun h3-book-tactics-fact-index-formulas (index)
  (caddr index))

(defun h3-book-tactics-fact-index-conclusions (index)
  (cadddr index))

(defun h3-book-tactics-fact-index-equations (index)
  (car (cddddr index)))

(defun h3-book-tactics-make-fact-index (count formulas conclusions equations)
  (list :h3-book-tactics-fact-index count formulas conclusions equations))

(defun h3-book-tactics-fact-index-init ()
  (h3-book-tactics-make-fact-index 0 nil nil nil))

(defun h3-book-tactics-select-present (names table keep-strings)
  (if (endp names)
      nil
    (if (or (assoc-equal (car names) table)
            (and keep-strings (stringp (car names))))
        (cons (car names)
              (h3-book-tactics-select-present (cdr names) table keep-strings))
      (h3-book-tactics-select-present (cdr names) table keep-strings))))

(defun h3-book-tactics-available-rules (lib)
  (h3-book-tactics-select-present
   *h3-book-tactics-fixed-rules*
   (proof-proof-facts (library-library-proof lib)) t))

(defun h3-book-tactics-conclusion (formula)
  (if (proof-is-call formula *library-implies*)
      (proof-term-at formula 2)
    formula))

(defun h3-book-tactics-index-append (table head pattern name)
  (table-put table head
               (append (table-get table head nil) (list (list pattern name)))))

(defun h3-book-tactics-index-access (table head)
  (if (assoc-equal head table) table (table-put table head nil)))

(defun h3-book-tactics-index-fact (fact proof index)
  (let ((name (car fact))
        (clause (cdr fact))
        (count (h3-book-tactics-fact-index-count index))
        (formulas (h3-book-tactics-fact-index-formulas index))
        (conclusions (h3-book-tactics-fact-index-conclusions index))
        (equations (h3-book-tactics-fact-index-equations index)))
    (if (endp clause)
        index
      (let ((formula (car clause)))
        (proof-with-checked-results
            ((formulas
              (if (endp (cdr clause))
                  (proof-with-checked-results ((head (h3-rewrite-head-of formula)))
                    (h3-book-tactics-index-append formulas head formula name))
                formulas)))
          (if (or (assoc-equal name (proof-proof-definitions proof))
                  (member-equal name (proof-proof-primitives proof)))
              (h3-book-tactics-make-fact-index count formulas conclusions equations)
            (proof-with-checked-results
                ((conclusion (h3-book-tactics-conclusion formula))
                 (head (h3-rewrite-head-of conclusion)))
              (let ((conclusions
                     (if head
                         (h3-book-tactics-index-append conclusions head conclusion name)
                       conclusions)))
                (if (proof-is-call conclusion *proof-equal*)
                    (proof-with-checked-results
                        ((parts (proof-list-of-length (cdr conclusion) 2))
                         (left-head (h3-rewrite-head-of (car parts))))
                      (h3-book-tactics-make-fact-index
                       count formulas conclusions
                       (if left-head
                           (h3-book-tactics-index-append equations left-head (car parts) name)
                         equations)))
                  (h3-book-tactics-make-fact-index
                   count formulas conclusions equations))))))))))

(defun h3-book-tactics-index-facts (facts proof index)
  (if (endp facts)
      index
    (proof-with-checked-results
        ((next (h3-book-tactics-index-fact (car facts) proof index)))
      (h3-book-tactics-index-facts (cdr facts) proof next))))

(defun h3-book-tactics-fact-index-extend (index lib)
  (let* ((proof (library-library-proof lib))
         (facts (proof-proof-facts proof)))
    (proof-with-checked-results
        ((updated (h3-book-tactics-index-facts
                   (nthcdr (h3-book-tactics-fact-index-count index) facts)
                   proof index)))
      (h3-book-tactics-make-fact-index (len facts)
                                      (h3-book-tactics-fact-index-formulas updated)
                                      (h3-book-tactics-fact-index-conclusions updated)
                                      (h3-book-tactics-fact-index-equations updated)))))

; Each fact has an insertion position and an index contribution.
; Replacing a fact can update its indexed terms or resolve an indexing failure.
(defun h3-book-tactics-fact-contribution (fact proof)
  (h3-book-tactics-index-fact fact proof (h3-book-tactics-fact-index-init)))

(defun h3-book-tactics-prepared-fact-names (prepared)
  (cadddr prepared))

(defun h3-book-tactics-append-index-item (table contribution)
  (if (endp contribution)
      table
    (let ((item (cadar contribution)))
      (h3-book-tactics-index-append table (caar contribution) (car item) (cadr item)))))

(defun h3-book-tactics-append-prepared-fact (fact proof prepared)
  (let* ((index (car prepared))
         (position (h3-book-tactics-fact-index-count index))
         (contribution (h3-book-tactics-fact-contribution fact proof))
         (failed (failure-p contribution))
         (items (if failed nil contribution)))
    (list (h3-book-tactics-make-fact-index
           (1+ position)
           (h3-book-tactics-append-index-item
            (h3-book-tactics-fact-index-formulas index)
            (h3-book-tactics-fact-index-formulas items))
           (h3-book-tactics-append-index-item
            (h3-book-tactics-fact-index-conclusions index)
            (h3-book-tactics-fact-index-conclusions items))
           (h3-book-tactics-append-index-item
            (h3-book-tactics-fact-index-equations index)
            (h3-book-tactics-fact-index-equations items)))
          (acons (car fact) (cons position contribution) (cadr prepared))
          (if failed (acons position contribution (caddr prepared)) (caddr prepared))
          (cons (car fact) (h3-book-tactics-prepared-fact-names prepared)))))

(defun h3-book-tactics-prepare-facts-loop (facts proof prepared)
  (if (endp facts)
      prepared
    (h3-book-tactics-prepare-facts-loop
     (cdr facts) proof (h3-book-tactics-append-prepared-fact (car facts) proof prepared))))

(defun h3-book-tactics-prepare-facts (proof)
  (h3-book-tactics-prepare-facts-loop
   (proof-proof-facts proof) proof (list (h3-book-tactics-fact-index-init) nil nil nil)))

(defun h3-book-tactics-replace-index-item (items old new)
  (cond ((endp items) nil)
        ((equal (car items) old)
         (if new (cons new (cdr items)) (cdr items)))
        (t (cons (car items) (h3-book-tactics-replace-index-item (cdr items) old new)))))

(defun h3-book-tactics-insert-index-item (items item position positions)
  (if (or (endp items) (< position (cadr (assoc-equal (cadar items) positions))))
      (cons item items)
    (cons (car items) (h3-book-tactics-insert-index-item (cdr items) item position positions))))

(defun h3-book-tactics-update-index-table (table old new position positions)
  (cond ((equal old new) table)
        ((and old new (equal (caar old) (caar new)))
         (let* ((head (caar old))
                (items (table-get table head nil)))
           (table-put table head
                        (h3-book-tactics-replace-index-item items (cadar old) (cadar new)))))
        (t
         (let ((table (if old
                          (let* ((head (caar old))
                                 (items (table-get table head nil))
                                 (rest (h3-book-tactics-replace-index-item items (cadar old) nil)))
                            (if rest (table-put table head rest) (table-without table head)))
                        table)))
           (if new
               (let* ((head (caar new))
                      (items (table-get table head nil)))
                 (table-put table head
                              (h3-book-tactics-insert-index-item items (cadar new) position positions)))
             table)))))

(defun h3-book-tactics-replace-prepared-fact (fact proof prepared entry)
  (let* ((index (car prepared))
         (positions (cadr prepared))
         (errors (caddr prepared))
         (position (cadr entry))
         (old (cddr entry))
         (new (h3-book-tactics-fact-contribution fact proof)))
    (if (equal old new)
        prepared
      (let* ((errors (cond ((failure-p new) (table-put errors position new))
                           ((failure-p old) (table-without errors position))
                           (t errors)))
             (old-items (if (failure-p old) nil old))
             (new-items (if (failure-p new) nil new)))
        (list (h3-book-tactics-make-fact-index
               (h3-book-tactics-fact-index-count index)
               (h3-book-tactics-update-index-table
                (h3-book-tactics-fact-index-formulas index)
                (h3-book-tactics-fact-index-formulas old-items)
                (h3-book-tactics-fact-index-formulas new-items) position positions)
               (h3-book-tactics-update-index-table
                (h3-book-tactics-fact-index-conclusions index)
                (h3-book-tactics-fact-index-conclusions old-items)
                (h3-book-tactics-fact-index-conclusions new-items) position positions)
               (h3-book-tactics-update-index-table
                (h3-book-tactics-fact-index-equations index)
                (h3-book-tactics-fact-index-equations old-items)
                (h3-book-tactics-fact-index-equations new-items) position positions))
              (table-put positions (car fact) (cons position new)) errors
              (h3-book-tactics-prepared-fact-names prepared))))))

(defun h3-book-tactics-update-fact-names (prepared old-proof proof names)
  (if (endp names)
      prepared
    (let* ((name (car names))
           (entry (assoc-equal name (cadr prepared)))
           (fact (assoc-equal name (proof-proof-facts proof)))
           (next (cond ((not entry) (h3-book-tactics-append-prepared-fact fact proof prepared))
                       ((and (equal fact (assoc-equal name (proof-proof-facts old-proof)))
                             (equal (consp (assoc-equal name (proof-proof-definitions proof)))
                                    (consp (assoc-equal name (proof-proof-definitions old-proof)))))
                        prepared)
                       (t (h3-book-tactics-replace-prepared-fact fact proof prepared entry)))))
      (h3-book-tactics-update-fact-names next old-proof proof (cdr names)))))

(defun h3-book-tactics-update-prepared-facts (prepared old-proof proof names)
  (h3-book-tactics-update-fact-names prepared old-proof proof (proof-unique names)))

(defun h3-book-tactics-first-index-failure (errors first)
  (if (endp errors)
      (cdr first)
    (h3-book-tactics-first-index-failure
     (cdr errors) (if (or (not first) (< (caar errors) (car first))) (car errors) first))))

(defun h3-book-tactics-current-fact-index (lib prepared)
  (if prepared
      (or (h3-book-tactics-first-index-failure (caddr prepared) nil) (car prepared))
    (h3-book-tactics-fact-index-extend (h3-book-tactics-fact-index-init) lib)))

(defun h3-book-tactics-exact-candidates (candidates proof formula)
  (if (endp candidates)
      nil
    (proof-with-checked-results
        ((matched (h3-rewrite-match (caar candidates) formula nil)))
      (if (car matched)
          (proof-proof-fact proof (cadar candidates) (table-items (cdr matched)))
        (h3-book-tactics-exact-candidates (cdr candidates) proof formula)))))

(defun h3-book-tactics-fact-index-exact (index lib formula)
  (let ((head (h3-rewrite-head-of formula)))
    (if (failure-p head)
        (cons head index)
      (let* ((formulas (h3-book-tactics-index-access
                        (h3-book-tactics-fact-index-formulas index) head))
             (proof (library-library-proof lib))
             (result (h3-book-tactics-exact-candidates
                      (table-get formulas head nil) proof formula)))
        (cons result
              (h3-book-tactics-make-fact-index
               (h3-book-tactics-fact-index-count index) formulas
               (h3-book-tactics-fact-index-conclusions index)
               (h3-book-tactics-fact-index-equations index)))))))

(defun h3-book-tactics-decreasing-equation (term)
  (if (not (proof-is-call term *proof-equal*))
      nil
    (proof-with-checked-results ((parts (proof-list-of-length (cdr term) 2)))
      (let ((lhs (car parts))
            (rhs (cadr parts)))
        (cond ((or (not (h3-rewrite-arguments lhs))
                   (equal (h3-rewrite-head-of lhs) *proof-quote*))
               nil)
              ((or (not (proof-compound rhs)) (proof-is-call rhs *proof-quote*)) t)
              (t (> (len (h3-book-tactics-subterms lhs))
                    (len (h3-book-tactics-subterms rhs)))))))))

(defun h3-book-tactics-match-rule (candidate term equations facts names)
  (let ((pattern (car candidate))
        (name (cadr candidate)))
    (if (member-equal name names)
        nil
      (proof-with-checked-results ((matched (h3-rewrite-match pattern term nil)))
        (cond ((not (car matched)) nil)
              ((or (proof-is-call pattern *proof-equal*)
                   (member-equal candidate equations))
               (let ((fact (assoc-equal name facts)))
                 (if (not fact)
                     '(:failure "failure" "")
                   (proof-with-checked-results
                       ((formula (proof-term-at (cdr fact) 0))
                        (equation (h3-book-tactics-conclusion formula)))
                     (h3-book-tactics-decreasing-equation equation)))))
              (t t))))))

(defun h3-book-tactics-select-rules (candidates term equations facts names)
  (if (endp candidates)
      (cons names nil)
    (proof-with-checked-results
        ((match-p (h3-book-tactics-match-rule (car candidates) term equations facts names)))
      (if match-p
          (let ((names (append names (list (cadar candidates)))))
            (if (>= (len names) 65)
                (cons names t)
              (h3-book-tactics-select-rules (cdr candidates) term equations facts names)))
        (h3-book-tactics-select-rules (cdr candidates) term equations facts names)))))

(defun h3-book-tactics-rules-for-terms (terms lib index names)
  (if (endp terms)
      (cons names index)
    (let* ((term (car terms))
           (head (h3-rewrite-head-of term)))
      (cond
       ((failure-p head) (cons head index))
       ((or (not head) (equal head *proof-quote*))
        (h3-book-tactics-rules-for-terms (cdr terms) lib index names))
       (t
        (let* ((conclusions (h3-book-tactics-index-access
                             (h3-book-tactics-fact-index-conclusions index) head))
               (equations (h3-book-tactics-fact-index-equations index))
               (equality-p (proof-is-call term *proof-equal*))
               (equations (if equality-p equations
                            (h3-book-tactics-index-access equations head)))
               (index (h3-book-tactics-make-fact-index
                       (h3-book-tactics-fact-index-count index)
                       (h3-book-tactics-fact-index-formulas index)
                       conclusions equations))
               (equations (table-get equations head nil))
               (propositions (table-get conclusions head nil))
               (candidates (if equality-p propositions (append propositions equations)))
               (facts (proof-proof-facts (library-library-proof lib)))
               (selected (h3-book-tactics-select-rules
                          (reverse candidates) term equations facts names)))
          (cond ((failure-p selected) (cons selected index))
                ((cdr selected) (cons (car selected) index))
                (t (h3-book-tactics-rules-for-terms (cdr terms) lib index
                                                  (car selected))))))))))

(defun h3-book-tactics-fact-index-rules-for (index lib terms)
  (h3-book-tactics-rules-for-terms terms lib index
                                 (proof-unique (h3-book-tactics-available-rules lib))))

(defun h3-book-tactics-small-definitions-loop (definitions terms count)
  (if (endp terms)
      nil
    (let ((term (car terms)))
      (proof-with-checked-results ((name (h3-rewrite-head-of term)))
        (let ((entry (assoc-equal name definitions)))
          (if (or (not entry) (member-equal name *h3-book-tactics-definitions*)
                  (proof-is-call term *proof-quote*))
              (h3-book-tactics-small-definitions-loop definitions (cdr terms) count)
            (proof-with-checked-results
                ((parts (proof-list-of-length (cdr entry) 2))
                 (body (termination-logical-body (cadr parts))))
              (if (< (h3-book-tactics-subterm-count body 130) 130)
                  (proof-with-checked-results
                      ((rest (h3-book-tactics-small-definitions-loop
                              definitions (cdr terms) (1+ count))))
                    (if (< count 35) (cons term rest) rest))
                (h3-book-tactics-small-definitions-loop definitions (cdr terms) count)))))))))

(defun h3-book-tactics-small-definitions (lib terms)
  (h3-book-tactics-small-definitions-loop
   (proof-proof-definitions (library-library-proof lib)) (proof-unique terms) 0))

; Build the simultaneous substitution in formal argument order.
(defun h3-book-tactics-induction-mapping (formals actuals children bindings mapping)
  (declare (xargs :measure (acl2-count formals)))
  (if (or (endp formals) (endp actuals) (endp children))
      mapping
    (proof-with-checked-results
        ((next (if (or (proof-compound (car actuals)) (equal (car children) (car formals)))
                   mapping
                 (proof-with-checked-results ((value (proof-subst (car children) bindings)))
                   (table-put mapping (car actuals) value)))))
      (h3-book-tactics-induction-mapping
       (cdr formals) (cdr actuals) (cdr children) bindings next))))

(defun h3-book-tactics-induction-reason (lib head actual)
  (cond
   ((equal head *library-cdr*) 3)
   ((equal head *library-car*) 2)
   (t
    (let* ((proof (library-library-proof lib))
           (name (table-get *h3-book-descent-set-selectors* head nil)))
      (if (and name (assoc-equal name (proof-proof-facts proof)))
          (proof-with-checked-results
              ((axiom (proof-proof-fact proof name (list (list *library-x* actual))))
               (guard (proof-proof-assume
                       proof (proof-neg (list *h3-book-descent-set-empty* actual)) t)))
            (h3-rewrite-apply-implication lib axiom guard))
        nil)))))

(defun h3-book-tactics-record-induction
    (lib formal actual child mapping proposed alternatives)
  (let ((args (h3-rewrite-arguments child))
        (head (car child)))
    (if (or (proof-compound actual)
            (not (equal args (list formal)))
            (not (equal (table-get mapping actual nil) (list head actual))))
        (cons proposed alternatives)
      (proof-with-checked-results ((reason (h3-book-tactics-induction-reason lib head actual)))
        (if (not reason)
            (cons proposed alternatives)
          (let ((proposed (if (integerp reason)
                              (table-put proposed actual
                                           (add-to-set-equal head (table-get proposed actual nil)))
                            proposed))
                (substitutions (table-get alternatives actual nil)))
            (cons proposed
                  (table-put alternatives actual
                               (table-put substitutions mapping (list mapping reason))))))))))

(defun h3-book-tactics-induction-alternatives
    (lib formals actuals children mapping state-pair)
  (declare (xargs :measure (acl2-count formals)))
  (if (or (endp formals) (endp actuals) (endp children) (failure-p state-pair))
      state-pair
    (h3-book-tactics-induction-alternatives
     lib (cdr formals) (cdr actuals) (cdr children) mapping
     (h3-book-tactics-record-induction lib (car formals) (car actuals) (car children)
                                       mapping (car state-pair) (cdr state-pair)))))

(defun h3-book-tactics-induction-recursive-call (lib formals actuals bindings call state-pair)
  (let ((children (termination-call-actuals call)))
    (proof-with-checked-results
        ((mapping (h3-book-tactics-induction-mapping formals actuals children bindings nil)))
      (h3-book-tactics-induction-alternatives lib formals actuals children mapping state-pair))))

(defun h3-book-tactics-induction-recursive
    (lib formals actuals bindings calls state-pair)
  (declare (xargs :measure (acl2-count calls)))
  (if (or (endp calls) (failure-p state-pair))
      state-pair
    (h3-book-tactics-induction-recursive
     lib formals actuals bindings (cdr calls)
     (h3-book-tactics-induction-recursive-call lib formals actuals bindings (car calls) state-pair))))

(defun h3-book-tactics-induction-general (alternatives general)
  (if (endp alternatives)
      general
    (let ((variable (caar alternatives))
          (substitutions (cdar alternatives)))
      (h3-book-tactics-induction-general
       (cdr alternatives)
       (if (<= (len substitutions) 2)
           (table-put general (list variable (table-keys substitutions))
                        (list variable (table-values substitutions)))
         general)))))

(defun h3-book-tactics-induction-call (lib call proposed general)
  (proof-with-checked-results ((head (proof-term-at call 0)))
    (let ((definition (assoc-equal head (proof-proof-definitions
                                         (library-library-proof lib)))))
      (if (not definition)
          '(:failure "failure" "")
        (proof-with-checked-results ((parts (proof-list-of-length (cdr definition) 2)))
          (let* ((formals (car parts))
                 (actuals (cdr call))
                 (bindings (termination-bindings formals actuals nil)))
            (proof-with-checked-results
                ((recursive (termination-recursive-calls *termination-all* (list (cons head parts))))
                 (updated (h3-book-tactics-induction-recursive
                           lib formals actuals bindings recursive (cons proposed nil))))
              (cons (car updated) (h3-book-tactics-induction-general (cdr updated) general)))))))))

(defun h3-book-tactics-induction-calls (lib calls plans)
  (declare (xargs :measure (acl2-count calls)))
  (if (or (endp calls) (failure-p plans))
      plans
    (h3-book-tactics-induction-calls
     lib (cdr calls) (h3-book-tactics-induction-call lib (car calls) (car plans) (cdr plans)))))

(defun h3-book-tactics-basic-inductions (proposed)
  (if (endp proposed)
      nil
    (let ((variable (caar proposed))
          (selectors (cdar proposed)))
      (cons (list variable
                  (append (if (member-equal *library-cdr* selectors)
                              (list (list (list (cons variable (list *library-cdr* variable))) 3))
                            nil)
                          (if (member-equal *library-car* selectors)
                              (list (list (list (cons variable (list *library-car* variable))) 2))
                            nil)))
            (h3-book-tactics-basic-inductions (cdr proposed))))))

(defun h3-book-tactics-add-inductions (general candidates)
  (if (endp general)
      candidates
    (let ((candidate (cdar general)))
      (h3-book-tactics-add-inductions
       (cdr general)
       (if (member-equal candidate candidates)
           candidates
         (append candidates (list candidate)))))))

(defun h3-book-tactics-induction-candidates (lib calls)
  (proof-with-checked-results ((plans (h3-book-tactics-induction-calls lib calls nil)))
    (h3-book-tactics-add-inductions (cdr plans) (h3-book-tactics-basic-inductions (car plans)))))

(defun h3-book-tactics-available-definitions (lib)
  (h3-book-tactics-select-present
   *h3-book-tactics-definitions*
   (proof-proof-definitions (library-library-proof lib)) nil))

(defun h3-book-tactics-match-reverse (lib formula index)
  (if (not (proof-is-call formula *proof-equal*))
      (cons nil index)
    (let ((right (proof-term-at formula 2)))
      (if (failure-p right)
          (cons right index)
        (let* ((reverse (proof-eq right (cadr formula)))
               (matched (h3-book-tactics-fact-index-exact index lib reverse))
               (step (car matched)))
          (if (or (not step) (failure-p step))
              matched
            (cons (proof-proof-symmetric (library-library-proof lib) step) (cdr matched))))))))

(defun h3-book-tactics-match-reduced (lib formula index)
  (let* ((definitions (h3-book-tactics-available-definitions lib))
         (search (h3-book-tactics-book-search-init lib definitions nil nil 14 130 t nil))
         (equality (car (h3-book-tactics-book-search-reduce search formula nil nil nil))))
    (cond ((h3-rewrite-unproved-p equality) (cons nil index))
          ((or (failure-p equality) (not equality)) (cons equality index))
          (t
           (let ((reduced (proof-with-checked-results ((literal (proof-step-first equality)))
                            (proof-term-at literal 2))))
             (if (failure-p reduced)
                 (cons reduced index)
               (let* ((exact (h3-book-tactics-fact-index-exact index lib reduced))
                      (step (car exact)))
                 (if (or (not step) (failure-p step))
                     exact
                   (cons (proof-proof-transport (library-library-proof lib) step equality)
                         (cdr exact))))))))))

(defun h3-book-tactics-matching-theorem-with-index (lib formula index)
  (let ((exact (h3-book-tactics-fact-index-exact index lib formula)))
    (if (car exact)
        exact
      (let ((reverse (h3-book-tactics-match-reverse lib formula (cdr exact))))
        (if (car reverse)
            reverse
          (h3-book-tactics-match-reduced lib formula (cdr reverse)))))))

(defun h3-book-tactics-matching-theorem (lib formula index)
  (car (h3-book-tactics-matching-theorem-with-index lib formula index)))

(defun h3-book-tactics-failure-kind-p (value kinds)
  (and (failure-p value) (if (member-equal (cadr value) kinds) t nil)))

(defun h3-book-tactics-guarded-candidate (candidate lib guard conclusion given rules boolean)
  (let ((proof (library-library-proof lib))
        (pattern (car candidate))
        (name (cadr candidate)))
    (proof-with-checked-results
        ((matched (h3-rewrite-match pattern conclusion nil))
         (fact (and (car matched) (proof-proof-fact proof name (table-items (cdr matched)))))
         (literal (and fact (equal (len (proof-step-clause fact)) 1) (proof-step-first fact))))
      (if (not (proof-is-call literal *library-implies*))
          :skip
        (let* ((search (h3-book-tactics-book-search-init
                        lib *h3-book-tactics-definitions* nil rules 6 40 nil nil))
               (hypothesis (proof-term-at literal 1))
               (premise (if (failure-p hypothesis)
                            hypothesis
                          (car (h3-rewrite-search-prove search hypothesis (list given))))))
          (cond ((h3-book-tactics-failure-kind-p premise '("Unproved" "assertion")) :decline)
                ((failure-p premise) premise)
                (t
                 (proof-with-checked-results
                     ((result (h3-rewrite-apply-implication lib fact premise))
                      (goal (if boolean (h3-book-arithmetic-truth-value lib result) result)))
                   (h3-rewrite-implication lib guard goal)))))))))

(defun h3-book-tactics-guarded-candidates
    (candidates lib guard conclusion given rules boolean attempts value)
  (declare (xargs :measure (acl2-count candidates)))
  (cond ((not (member-eq value '(:skip :decline))) value)
        ((or (endp candidates) (and (eq value :decline) (<= attempts 1))) nil)
        (t
         (h3-book-tactics-guarded-candidates
          (cdr candidates) lib guard conclusion given rules boolean
          (if (eq value :decline) (1- attempts) attempts)
          (h3-book-tactics-guarded-candidate (car candidates) lib guard conclusion given rules boolean)))))

(defun h3-book-tactics-guarded-instance (lib formula index)
  (if (not (proof-is-call formula *library-implies*))
      nil
    (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2)))
      (let ((guard (car parts))
            (goal (cadr parts)))
        (proof-with-checked-results
            ((right (and (proof-is-call goal *proof-equal*) (proof-term-at goal 2))))
          (let* ((boolean (and (equal right *proof-true*)
                               (proof-is-call (cadr goal) *proof-equal*)))
                 (conclusion (if boolean (cadr goal) goal)))
            (proof-with-checked-results
                ((head (h3-rewrite-head-of conclusion))
                 (given (proof-proof-assume (library-library-proof lib) guard t))
                 (rules (h3-rewrite-rules-init lib (h3-book-tactics-available-rules lib) nil)))
              (h3-book-tactics-guarded-candidates
               (reverse (table-get (h3-book-tactics-fact-index-conclusions index) head nil))
               lib guard conclusion given rules boolean 12 :skip))))))))

(defun h3-book-tactics-lookup-on-cons (lib formula)
  (if (not (proof-is-call formula *library-implies*))
      nil
    (proof-with-checked-results ((goal (proof-term-at formula 2)))
      (if (not (proof-is-call goal *proof-equal*))
          nil
        (proof-with-checked-results ((call (proof-term-at goal 1)))
          (if (not (proof-is-call call (proof-sym "ASSOC-EQUAL" "ACL2")))
              nil
            (proof-with-checked-results ((pairs (proof-term-at call 2)))
              (if (not (proof-is-call pairs *proof-cons*))
                  nil
                (proof-with-checked-results
                    ((rules (h3-rewrite-rules-init lib (h3-book-tactics-available-rules lib) nil)))
                  (let ((search (h3-rewrite-search-init lib *h3-book-descent-transparent*
                                                        (list call) rules 24 t)))
                    (car (h3-rewrite-search-prove search formula nil))))))))))))

(defun h3-book-tactics-structural-label (guard goal)
  (cond
   ((proof-is-call guard *proof-consp*)
    (proof-with-checked-results ((value (proof-term-at guard 1)))
      (and (equal goal (library-lt (list *library-len* (list *library-cdr* value))
                                   (list *library-len* value)))
           "LEN-CDR-LESS")))
   ((proof-is-call guard *library-natp*)
    (proof-with-checked-results ((value (proof-term-at guard 1)))
      (and (equal goal (list *proof-ordinalp* value)) "NATURAL-ORDINAL")))
   (t nil)))

(defun h3-book-tactics-structural-arithmetic (lib formula)
  (if (not (proof-is-call formula *library-implies*))
      (cons nil lib)
    (let* ((parts (proof-list-of-length (cdr formula) 2))
           (guard (car parts))
           (label (if (failure-p parts)
                      parts
                    (h3-book-tactics-structural-label guard (cadr parts)))))
      (if (or (not label) (failure-p label))
          (cons label lib)
        (let ((updated (h3-merges-arithmetic lib)))
          (if (failure-p updated)
              (cons updated lib)
            (cons (proof-with-checked-results
                       ((given (proof-proof-assume (library-library-proof updated) guard t))
                        (goal (library-library-cite updated label (list (cadr guard)) (list given))))
                     (h3-rewrite-implication updated guard goal))
                  updated)))))))

(defun h3-book-tactics-prove-with-search
    (lib definitions calls rules budget inference-budget deep inside-first formula evidence)
  (car (h3-rewrite-search-prove
        (h3-book-tactics-book-search-init
         lib definitions calls rules budget inference-budget deep inside-first)
        formula evidence)))

(defun h3-book-tactics-solve-theorem-prove-case
    (evidence lib available calls rules inside-first formula)
  (h3-book-tactics-prove-with-search
   lib available calls rules 18 130 t inside-first formula evidence))

(defun h3-book-tactics-prove-clause-type-prove-case
    (evidence lib calls rules formula)
  (h3-book-tactics-prove-with-search
   lib *h3-book-tactics-definitions* calls rules 45 1500 nil nil formula evidence))

(defun h3-book-tactics-run-induction
    (n lib formula variable replacements available calls rules inside-first clause-type replies result)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "h3-book-tactics-run-induction"))
        ((not (h3-induction-request-p result)) result)
        (t
         (let* ((evidence (h3-induction-request-evidence result))
                (reply (if clause-type
                           (h3-book-tactics-prove-clause-type-prove-case
                            evidence lib calls rules formula)
                         (h3-book-tactics-solve-theorem-prove-case
                          evidence lib available calls rules inside-first formula)))
                (replies (append replies (list reply))))
           (h3-book-tactics-run-induction
            (1- n) lib formula variable replacements available calls rules inside-first clause-type
            replies (h3-induction-structural-induction lib formula variable replacements replies))))))

(defun h3-book-tactics-induct
    (lib formula variable replacements available calls rules inside-first clause-type)
  (h3-book-tactics-run-induction
   1000000 lib formula variable replacements available calls rules inside-first clause-type nil
   (h3-induction-structural-induction lib formula variable replacements nil)))

(defun h3-book-tactics-pseudo-term-constructors (lib)
  (let* ((a *library-x*)
         (d *library-y*)
         (source (list *h3-book-tactics-terms* (list *proof-cons* a d)))
         (body (proof-ite (list *h3-book-tactics-term* a)
                          (list *h3-book-tactics-terms* d) *proof-false*))
         (label "H3-BOOK-PSEUDO-TERM-LIST-CONS")
         (name (proof-sym "SELF-H3-BOOK-PSEUDO-TERM-LIST-CONS" "ACL2")))
    (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
        (cons name lib)
      (let* ((formula (proof-eq source body))
             (updated
              (proof-with-checked-results
                  ((rules (h3-rewrite-rules-init lib *h3-book-tactics-fixed-rules* nil))
                   (step (h3-book-tactics-prove-with-search
                          lib *h3-book-tactics-definitions* (list source) rules
                          14 130 t nil formula nil)))
                (library-library-lemma lib label formula step nil))))
        (if (failure-p updated) (cons updated lib) (cons name updated))))))

(defun h3-book-tactics-clause-pair (lib fn list-cons)
  (if (not (member-equal fn '(("sym" "ACL2" "DISJOIN") ("sym" "ACL2" "CONJOIN"))))
      (cons nil lib)
    (let* ((pair (proof-sym (string-append (caddr fn) "2") "ACL2"))
           (label (string-append "H3-BOOK-PSEUDO-TERM-" (caddr pair)))
           (name (proof-sym (string-append "SELF-" label) "ACL2")))
      (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
          (cons name lib)
        (let* ((call (list pair *library-x* *library-y*))
               (target (list *h3-book-tactics-term* call))
               (guard (proof-ite (list *h3-book-tactics-term* *library-x*)
                                 (list *h3-book-tactics-term* *library-y*) *proof-false*))
               (lemma (list *library-implies* guard target))
               (updated
                (proof-with-checked-results
                    ((rules (h3-rewrite-rules-init
                             lib (append *h3-book-tactics-fixed-rules* (list list-cons)) nil))
                     (step (h3-book-tactics-prove-with-search
                            lib (append *h3-book-tactics-definitions* (list pair))
                            (list call) rules 65 2200 nil nil lemma nil)))
                  (library-library-lemma lib label lemma step nil))))
          (if (failure-p updated) (cons updated lib) (cons name updated)))))))

(defun h3-book-tactics-prove-clause-type-finish (lib formula list-cons pair-name call fn)
  (let* ((before '(("sym" "ACL2" "PSEUDO-TERMP-DISJOIN")
                   ("sym" "ACL2" "PSEUDO-TERMP-CONJOIN")
                   ("sym" "ACL2" "PSEUDO-TERM-LISTP-DISJOIN-LST")))
         (names (append *h3-book-tactics-fixed-rules* (list list-cons)
                        (and pair-name (list pair-name))
                        (h3-book-tactics-select-present
                         before (proof-proof-facts (library-library-proof lib)) nil))))
    (proof-with-checked-results
        ((rules (h3-rewrite-rules-init lib names nil))
         (guard (proof-term-at formula 1)))
      (let ((calls (list guard call (list *h3-book-tactics-terms* *proof-false*))))
        (if (equal fn (proof-sym "CONJOIN-CLAUSES" "ACL2"))
            (h3-book-tactics-prove-clause-type-prove-case nil lib calls rules formula)
          (proof-with-checked-results ((variable (proof-term-at guard 1)))
            (let* ((mapping (list (cons variable (list *library-cdr* variable))))
                   (replacements (list (list mapping 3))))
              (h3-book-tactics-induct
               lib formula variable replacements *h3-book-tactics-definitions*
               calls rules nil t))))))))

(defun h3-book-tactics-prove-clause-type (lib formula)
  (let* ((constructors (h3-book-tactics-pseudo-term-constructors lib))
         (list-cons (car constructors))
         (lib (cdr constructors)))
    (if (failure-p list-cons)
        constructors
      (let ((fields (proof-with-checked-results
                        ((goal (proof-term-at formula 2))
                         (call (proof-term-at goal 1))
                         (fn (proof-term-at call 0)))
                      (list call fn))))
        (if (failure-p fields)
            (cons fields lib)
          (let* ((call (car fields))
                 (fn (cadr fields))
                 (pair (h3-book-tactics-clause-pair lib fn list-cons))
                 (pair-name (car pair))
                 (lib (cdr pair)))
            (if (failure-p pair-name)
                pair
              (cons (h3-book-tactics-prove-clause-type-finish
                     lib formula list-cons pair-name call fn) lib))))))))

(defun h3-book-tactics-library-result (value lib)
  (if (failure-p value) (cons value lib) value))

(defun h3-book-tactics-special-theorem (lib name package local-name formula)
  (cond
   ((and (equal package "SET") (member-equal local-name *h3-book-tactics-set-count-theorems*))
    (let* ((result (h3-book-descent-set-selector-theorem-with-library lib formula))
           (value (car result)))
      (if (h3-book-tactics-failure-kind-p value '("value" "Unproved" "assertion"))
          (cons :continue (cdr result))
        result)))
   ((equal name (proof-sym "SFIX-PRODUCES-SET" "SET"))
    (let ((value (h3-book-descent-set-fix-type lib formula)))
      (cons (if (h3-book-tactics-failure-kind-p value '("value" "Unproved" "assertion"))
                :continue
              value)
            lib)))
   ((and (equal package "ACL2") (member-equal local-name *h3-book-tactics-clause-types*))
    (let ((result (h3-book-tactics-prove-clause-type lib formula)))
      (if (h3-rewrite-unproved-p (car result))
          (cons :continue (cdr result))
        result)))
   (t (cons :continue lib))))

(defun h3-book-tactics-call-tactic (tactic lib name formula)
  (h3-book-tactics-library-result
   (case tactic
     (:product-sign (h3-book-signs-product-sign-theorem-with-library lib name formula))
     (:exponent (h3-book-exponent-exponent-theorem lib name formula))
     (:floor (h3-book-floor-floor-theorem-with-library lib name formula))
     (:mod (h3-book-mod-mod-theorem-with-library lib name formula))
     (:remainder-interval
      (h3-book-mod-interval-remainder-interval-theorem-with-library lib name formula))
     (:numerator (h3-book-numerator-numerator-theorem-with-library lib name formula))
     (:parity (h3-book-parity-parity-theorem-with-library lib name formula))
     (:quotient (h3-book-quotient-quotient-theorem-with-library lib name formula))
     (:arithmetic (cons (h3-book-arithmetic-arithmetic-theorem lib name formula) lib))
     (:power-identities (h3-book-power-identities-power-identities-theorem lib formula))
     (:power-products (h3-book-power-products-power-products-theorem-with-library lib formula))
     (:power-order (h3-book-power-order-power-order-theorem-with-library lib formula))
     (:boolean-comparison (h3-book-signs-boolean-comparison-equality-with-library lib formula))
     (:rounding (h3-book-rounding-rounding-theorem-with-library lib formula))
     (:modulus-translation (h3-book-translation-modulus-translation-with-library lib formula))
     (:modulus-scaling (h3-book-translation-modulus-scaling-with-library lib formula))
     (:conditional-product-sign (h3-book-signs-conditional-product-sign-with-library lib formula))
     (:factor-order (h3-book-quotient-factor-order-with-library lib formula))
     (:nonlinear (h3-book-order-nonlinear-theorem-with-library lib formula))
     (otherwise (cons nil lib)))
   lib))

(defun h3-book-tactics-try-tactics (tactics name formula result)
  (declare (xargs :measure (acl2-count tactics)))
  (cond ((and (car result) (not (h3-rewrite-unproved-p (car result)))) result)
        ((endp tactics) (cons nil (cdr result)))
        (t (h3-book-tactics-try-tactics
            (cdr tactics) name formula
            (h3-book-tactics-call-tactic (car tactics) (cdr result) name formula)))))

(defun h3-book-tactics-rewrite-attempts (openings lib formula definitions rules result)
  (declare (xargs :measure (acl2-count openings)))
  (cond ((not (or (eq result :start)
                  (h3-book-tactics-failure-kind-p result '("Unproved" "value" "assertion"))))
         result)
        ((endp openings) nil)
        (t (h3-book-tactics-rewrite-attempts
            (cdr openings) lib formula definitions rules
            (h3-book-tactics-prove-with-search
             lib definitions (caar openings) rules 14 130 t (cadar openings) formula nil)))))

(defun h3-book-tactics-induction-attempt (options lib formula candidate definitions calls rules result)
  (declare (xargs :measure (acl2-count options)))
  (cond ((not (or (eq result :start)
                  (h3-book-tactics-failure-kind-p result '("Unproved" "ProofMismatch" "assertion"))))
         result)
        ((endp options) nil)
        (t (h3-book-tactics-induction-attempt
            (cdr options) lib formula candidate definitions calls rules
            (h3-book-tactics-induct lib formula (car candidate) (cadr candidate)
                                    definitions calls rules (car options) nil)))))

(defun h3-book-tactics-induction-attempts (candidates lib formula definitions calls rules result)
  (declare (xargs :measure (acl2-count candidates)))
  (if (or result (endp candidates))
      result
    (h3-book-tactics-induction-attempts
     (cdr candidates) lib formula definitions calls rules
     (h3-book-tactics-induction-attempt '(t nil) lib formula (car candidates) definitions calls rules :start))))

(defun h3-book-tactics-rewrite-theorem (lib formula terms index)
  (proof-with-checked-results
      ((names (car (h3-book-tactics-fact-index-rules-for index lib terms)))
       (rules (h3-rewrite-rules-init lib names nil))
       (calls (h3-book-tactics-small-definitions lib terms)))
    (let* ((definitions (h3-book-tactics-available-definitions lib))
           (openings (list (list nil nil) (list calls t) (list calls nil)))
           (rewritten (h3-book-tactics-rewrite-attempts openings lib formula definitions rules :start)))
      (if (or rewritten (> (len terms) 80))
          rewritten
        (proof-with-checked-results ((candidates (h3-book-tactics-induction-candidates lib calls)))
          (h3-book-tactics-induction-attempts (take (min 3 (len candidates)) candidates)
                                             lib formula definitions calls rules nil))))))

(defun h3-book-tactics-retry-theorem (lib formula index)
  (let ((guarded (h3-book-tactics-guarded-instance lib formula index)))
    (if (and guarded (not (h3-rewrite-unproved-p guarded)))
        (cons guarded lib)
      (let ((lookup (h3-book-tactics-lookup-on-cons lib formula)))
        (if (and lookup (not (h3-rewrite-unproved-p lookup)))
            (cons lookup lib)
          (let* ((result (h3-book-tactics-structural-arithmetic lib formula))
                 (value (car result)))
            (if (and value (not (h3-rewrite-unproved-p value)))
                result
              (cons *h3-rewrite-unproved* (cdr result)))))))))

(defun h3-book-tactics-solve-theorem-search (lib formula terms index)
  (let* ((result (if (<= (len terms) 45)
                     (h3-book-sums-additive-theorem-with-library lib formula)
                   (cons nil lib)))
         (value (car result))
         (lib (cdr result)))
    (if (and value (not (h3-book-tactics-failure-kind-p
                         value '("Unproved" "DifferentNormalForms" "value" "assertion"))))
        result
      (let ((step (h3-book-tactics-rewrite-theorem lib formula terms index)))
        (if step
            (cons step lib)
          (h3-book-tactics-retry-theorem lib formula index))))))

(defun h3-book-tactics-solve-theorem-tactics (lib local-name package formula terms index)
  (let* ((named '(:exponent :floor :mod :remainder-interval :numerator :parity :quotient :arithmetic))
         (named (if (member-equal local-name *h3-book-signs-product-signs*)
                    (cons :product-sign named)
                  named))
         (general '(:power-identities :power-products :power-order :boolean-comparison
                    :rounding :modulus-translation :modulus-scaling
                    :conditional-product-sign :factor-order :nonlinear))
         (tactics (if (equal package "ACL2") (append named general) general))
         (result (h3-book-tactics-try-tactics tactics local-name formula (cons nil lib))))
    (if (car result)
        result
      (h3-book-tactics-solve-theorem-search (cdr result) formula terms index))))

(defun h3-book-tactics-solve-theorem-unmatched (lib name formula index)
  (let* ((package (proof-term-at name 1))
         (local-name (and (member-equal package '("SET" "ACL2")) (proof-term-at name 2))))
    (cond ((failure-p package) (cons package lib))
          ((failure-p local-name) (cons local-name lib))
          (t
           (let ((result (h3-book-tactics-special-theorem lib name package local-name formula)))
             (if (not (eq (car result) :continue))
                 result
               (let ((terms (proof-unique (h3-book-tactics-subterms formula)))
                     (lib (cdr result)))
                 (if (> (len terms) 250)
                     (cons '(:failure "Unproved" "") lib)
                   (h3-book-tactics-solve-theorem-tactics lib local-name package formula terms index)))))))))

(defun h3-book-tactics-solve-theorem-prepared (lib name formula prepared)
  (let ((index (h3-book-tactics-current-fact-index lib prepared)))
    (if (failure-p index)
        (cons index lib)
      (let* ((matched (h3-book-tactics-matching-theorem-with-index lib formula index))
             (fact (car matched)))
        (if fact
            (cons fact lib)
          (h3-book-tactics-solve-theorem-unmatched lib name formula (cdr matched)))))))

(defun h3-book-tactics-solve-theorem (lib name formula aids)
  (declare (ignore aids))
  (h3-book-tactics-solve-theorem-prepared lib name formula nil))

(defun h3-book-tactics-solve-witness-prepared (instance witnesses lib prepared)
  (let* ((definitions (proof-proof-definitions (library-library-proof lib)))
         (names (h3-book-tactics-select-present witnesses definitions nil))
         (terms (proof-unique (h3-book-tactics-subterms instance))))
    (proof-with-checked-results
        ((index (h3-book-tactics-current-fact-index lib prepared))
         (rules (car (h3-book-tactics-fact-index-rules-for index lib terms)))
         (rules (h3-rewrite-rules-init lib rules nil))
         (calls (h3-book-tactics-small-definitions lib terms)))
      (h3-book-tactics-prove-with-search
       lib (append *h3-book-tactics-definitions* names) calls rules 20 130 t nil instance nil))))

(defun h3-book-tactics-solve-book-statement-prove (instance witnesses lib)
  (h3-book-tactics-solve-witness-prepared instance witnesses lib nil))

(defun h3-book-tactics-run-witness-prepared (n lib function-names formulas candidates
                                               replies result prepared)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons '(:failure "Fuel" "h3-book-tactics-run-witness-prepared") lib)
    (let ((value (car result)))
      (if (and (consp value) (eq (car value) :request))
          (let* ((updated (cdr result))
                 (proof (h3-book-tactics-solve-witness-prepared
                         (cadr value) (caddr value) updated prepared))
                 (replies (append replies (list (cons proof updated)))))
            (h3-book-tactics-run-witness-prepared
             (1- n) lib function-names formulas candidates replies
             (h3-book-witness-try-options lib function-names formulas candidates replies)
             prepared))
        result))))

(defun h3-book-tactics-run-witness (n lib function-names formulas candidates replies result)
  (h3-book-tactics-run-witness-prepared n lib function-names formulas candidates replies result nil))

(defun h3-book-tactics-local-fact-names (entries)
  (if (endp entries)
      nil
    (cons (cadar entries) (h3-book-tactics-local-fact-names (cdr entries)))))

(defun h3-book-tactics-constraint-entry-prepared (lib fields prepared)
  (let* ((witnesses (h3-book-witness-prepare lib fields))
         (plan (car witnesses)))
    (if (failure-p plan)
        witnesses
      (let* ((world (cdr witnesses))
             (names (car plan))
             (formulas (cadr plan))
             (candidates (caddr plan))
             (prepared (and prepared
                            (h3-book-tactics-update-prepared-facts
                             prepared (library-library-proof lib) (library-library-proof world)
                             (h3-book-tactics-local-fact-names (library-library-entries world))))))
        (h3-book-tactics-run-witness-prepared
         1000000 world names formulas candidates nil
         (h3-book-witness-try-options world names formulas candidates nil) prepared)))))

(defun h3-book-tactics-constraint-entry (lib fields)
  (h3-book-tactics-constraint-entry-prepared lib fields nil))

(defun h3-book-tactics-theorem-entry-prepared (lib fields prepared)
  (let ((parts (proof-list-of-length fields 2)))
    (if (failure-p parts)
        (cons parts lib)
      (let* ((name (car parts))
             (formula (cadr parts))
             (result (h3-book-tactics-solve-theorem-prepared lib name formula prepared))
             (step (car result)))
        (cond ((failure-p step) result)
              ((not step)
               (cons '(:failure "failure" "")
                     (cdr result)))
              ((not (equal (proof-step-clause step) (list formula)))
               (cons '(:failure "failure" "") (cdr result)))
              (t (cons (proof-proof-entry "theorem" name (list name) (list step)) (cdr result))))))))

(defun h3-book-tactics-theorem-entry (lib fields aids)
  (declare (ignore aids))
  (h3-book-tactics-theorem-entry-prepared lib fields nil))

(defun h3-book-tactics-solve-book-statement-prepared (lib kind fields aids prepared)
  (cond ((equal kind "define")
         (h3-book-descent-termination-proof-with-library lib fields aids :proof-entry))
        ((equal kind "theorem") (h3-book-tactics-theorem-entry-prepared lib fields prepared))
        ((equal kind "constrain") (h3-book-tactics-constraint-entry-prepared lib fields prepared))
        (t (cons '(:failure "Unproved" "") lib))))

(defun h3-book-tactics-solve-book-statement (lib kind fields aids)
  (h3-book-tactics-solve-book-statement-prepared lib kind fields aids nil))
