(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-theorems-guard-words*
  (list (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "NULL")
        (proof-cl "EQ") (proof-cl "EQL") *proof-not*))

(defconst *t3-book-theorems-constructor-equality*
  (proof-sym "SELF-T3-EQUAL-CONS" "ACL2"))

(defun t3-book-theorems-escape-sexp-string (chars)
  (if (endp chars)
      nil
    (let* ((char (car chars))
           (rest (t3-book-theorems-escape-sexp-string (cdr chars))))
      (if (or (eql char #\\) (eql char #\"))
          (list* #\\ char rest)
        (cons char rest)))))

(mutual-recursion
 (defun t3-book-theorems-sexp-text (value)
   (declare (xargs :measure (1+ (* 2 (acl2-count value)))))
   (cond ((consp value)
          (concatenate 'string
                       "(" (text-join " " (t3-book-theorems-sexp-items value)) ")"))
         ((null value) "()")
         ((eq value t) "t")
         ((integerp value) (decimal-text value))
         ((rationalp value)
          (concatenate 'string (decimal-text (numerator value)) "/"
                       (decimal-text (denominator value))))
         ((stringp value)
          (concatenate
           'string "\""
           (coerce (t3-book-theorems-escape-sexp-string (coerce value 'list))
                   'string)
           "\""))
         (t "")))
 (defun t3-book-theorems-sexp-items (items)
   (declare (xargs :measure (* 2 (acl2-count items))))
   (if (endp items)
       nil
     (cons (t3-book-theorems-sexp-text (car items))
           (t3-book-theorems-sexp-items (cdr items))))))

(defun t3-book-theorems-set-sort-keys (items)
  (if (endp items)
      nil
    (cons (list (t3-book-theorems-sexp-text (car items)) (car items))
          (t3-book-theorems-set-sort-keys (cdr items)))))

(defun t3-book-theorems-set-values (entries)
  (if (endp entries)
      nil
    (cons (cadar entries) (t3-book-theorems-set-values (cdr entries)))))

(defun t3-book-theorems-sort-set (items)
  (t3-book-theorems-set-values
   (seq-sorted (t3-book-theorems-set-sort-keys (proof-unique items)))))

(defconst *t3-book-theorems-predicates*
  (t3-book-theorems-sort-set
   (list *proof-consp* *proof-equal* *proof-not* (proof-sym "BOOLEANP" "ACL2")
         (proof-cl "CHARACTERP") *proof-integerp* *library-rationalp*
         (proof-cl "STRINGP") (proof-cl "SYMBOLP") *proof-less*
         *library-numberp* *library-natp*)))

(defun t3-book-theorems-head (term)
  (if (proof-compound term)
      (proof-term-at term 0)
    nil))

(defun t3-book-theorems-fingerprint (term)
  (if (not (proof-compound term))
      nil
    (proof-with-checked-results ((function (t3-book-theorems-head term)))
      (if (proof-compound function)
          (proof-cl "LAMBDA")
        function))))

(defun t3-book-theorems-fingerprints (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((first (t3-book-theorems-fingerprint (car terms)))
         (rest (t3-book-theorems-fingerprints (cdr terms))))
      (cons first rest))))

(defun t3-book-theorems-rule-key (term)
  (proof-with-checked-results ((function (t3-book-theorems-fingerprint term)))
    (cond ((consp term)
           (proof-with-checked-results
               ((args (t3-book-theorems-fingerprints (seq-slice term 1 3))))
             (list function args)))
          ((stringp term)
           (list function (take (max 0 (1- (min (length term) 3))) nil)))
          (t (proof-term-at term 0)))))

(defun t3-book-theorems-candidate-keys (args)
  (cond ((consp (cdr args))
         (proof-unique (list args (list (car args) nil)
                             (list nil (cadr args)) '(nil nil))))
        ((consp args) (proof-unique (list args '(nil))))
        (t (list nil))))

(defun t3-book-theorems-candidates-at-keys (index function keys)
  (if (endp keys)
      nil
    (append (table-get index (list function (car keys)) nil)
            (t3-book-theorems-candidates-at-keys index function (cdr keys)))))

(defun t3-book-theorems-candidates (index term)
  (proof-with-checked-results ((key (t3-book-theorems-rule-key term)))
    (t3-book-theorems-candidates-at-keys
     index (car key) (t3-book-theorems-candidate-keys (cadr key)))))

(mutual-recursion
 (defun t3-book-theorems-terms (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) (list term))
         ((endp term) '(:failure "MissingProofInput" ""))
         ((equal (car term) *proof-quote*) (list term))
         (t (proof-with-checked-results
                 ((args (t3-book-theorems-argument-terms (cdr term))))
               (cons term args)))))
 (defun t3-book-theorems-argument-terms (args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((first (t3-book-theorems-terms (car args)))
          (rest (t3-book-theorems-argument-terms (cdr args))))
       (append first rest)))))

(defun t3-book-theorems-noncompound-terms (terms)
  (cond ((endp terms) nil)
        ((proof-compound (car terms))
         (t3-book-theorems-noncompound-terms (cdr terms)))
        (t (cons (car terms) (t3-book-theorems-noncompound-terms (cdr terms))))))

(defun t3-book-theorems-variables (term)
  (proof-with-checked-results ((terms (t3-book-theorems-terms term)))
    (t3-book-theorems-sort-set (t3-book-theorems-noncompound-terms terms))))

(mutual-recursion
 (defun t3-book-theorems-match (pattern term bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (cond ((not (proof-compound pattern))
          (let ((bound (assoc-equal pattern bindings)))
            (if bound
                (cons (equal (cdr bound) term) bindings)
              (cons t (table-put bindings pattern term)))))
         ((proof-is-call pattern *proof-quote*)
          (cons (equal pattern term) bindings))
         ((or (not (proof-compound term)) (not (equal (len pattern) (len term))))
          (cons nil bindings))
         ((endp pattern) '(:failure "MissingProofInput" ""))
         ((not (equal (car pattern) (car term))) (cons nil bindings))
         (t (t3-book-theorems-match-arguments (cdr pattern) (cdr term) bindings))))
 (defun t3-book-theorems-match-arguments (patterns terms bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (endp patterns)
       (cons t bindings)
     (proof-with-checked-results
         ((first (t3-book-theorems-match (car patterns) (car terms) bindings)))
       (if (car first)
           (t3-book-theorems-match-arguments (cdr patterns) (cdr terms) (cdr first))
         first)))))

(defun t3-book-theorems-projection-traversal (n term path guards)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t3-book-theorems-projections")
    (let ((recipe (list term path guards)))
      (cond
       ((proof-is-call term *library-implies*)
        (proof-with-checked-results
            ((conclusion (proof-term-at term 2))
             (test (proof-term-at term 1))
             (rest (t3-book-theorems-projection-traversal
                    (1- n) conclusion (append path '(2)) (append guards (list test)))))
          (cons recipe rest)))
       ((proof-is-call term *proof-if*)
        (proof-with-checked-results ((otherwise (proof-term-at term 3)))
          (if (equal otherwise *proof-false*)
              (proof-with-checked-results
                  ((first (t3-book-theorems-projection-traversal
                           (1- n) (cadr term) (append path '(0)) guards))
                   (second (t3-book-theorems-projection-traversal
                            (1- n) (caddr term) (append path '(1)) guards)))
                (cons recipe (append first second)))
            (list recipe))))
       ((proof-is-call term (proof-sym "IFF" "ACL2"))
        (proof-with-checked-results
            ((left (proof-term-at term 1))
             (right (proof-term-at term 2)))
          (list recipe
                (list left (append path '(3)) (append guards (list right)))
                (list right (append path '(4)) (append guards (list left))))))
       (t (list recipe))))))

(defun t3-book-theorems-projections (term path guards)
  (t3-book-theorems-projection-traversal 1000000 term path guards))

(defun t3-book-theorems-conjunct-traversal (n term)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "t3-book-theorems-conjuncts"))
        ((proof-is-call term *proof-if*)
         (proof-with-checked-results ((otherwise (proof-term-at term 3)))
           (if (equal otherwise *proof-false*)
               (proof-with-checked-results
                   ((first (t3-book-theorems-conjunct-traversal (1- n) (cadr term)))
                    (second (t3-book-theorems-conjunct-traversal (1- n) (caddr term))))
                 (append first second))
             (list term))))
        (t (list term))))

(defun t3-book-theorems-conjuncts (term)
  (t3-book-theorems-conjunct-traversal 1000000 term))

(defun t3-book-theorems-project (lib step path guards)
  (declare (xargs :measure (acl2-count path)))
  (if (endp path)
      step
    (let* ((proof (library-library-proof lib))
           (index (car path)))
      (cond
       ((equal index 2)
        (if (endp guards)
            '(:failure "failure" "")
          (proof-with-checked-results
              ((next (proof-proof-modus-ponens proof step (car guards))))
            (t3-book-theorems-project lib next (cdr path) (cdr guards)))))
       ((or (equal index 3) (equal index 4))
        (proof-with-checked-results ((literal (proof-step-first step)))
          (if (endp guards)
              '(:failure "failure" "")
            (proof-with-checked-results
                ((next (library-library-cite
                        lib (if (= index 3) "T3-IFF-LEFT" "T3-IFF-RIGHT")
                        (cdr literal) (list step (car guards)))))
              (t3-book-theorems-project lib next (cdr path) (cdr guards))))))
       (t
        (proof-with-checked-results
            ((parts (proof-proof-conjunct proof step))
             (next (if (integerp index)
                       (let ((offset (if (< index 0) (+ index 2) index)))
                         (if (< offset 0)
                             '(:failure "failure" "")
                           (proof-term-at parts offset)))
                     '(:failure "failure" ""))))
          (t3-book-theorems-project lib next (cdr path) guards)))))))

(defun t3-book-theorems-recurrences (name formals body)
  (if (equal formals *proof-nil*)
      nil
    (termination-recursive-calls *termination-all* (list (list name formals body)))))

(defun t3-book-theorems-changed-indices (formals actuals index)
  (if (or (endp formals) (endp actuals))
      nil
    (let ((rest (t3-book-theorems-changed-indices (cdr formals) (cdr actuals) (1+ index))))
      (if (equal (car formals) (car actuals))
          rest
        (cons index rest)))))

(defun t3-book-theorems-recurrence-drivers (formals calls)
  (if (endp calls)
      nil
    (append (t3-book-theorems-changed-indices
             formals (termination-call-actuals (car calls)) 1)
            (t3-book-theorems-recurrence-drivers formals (cdr calls)))))

(defun t3-book-theorems-drivers-from-calls (formals calls)
  (if (failure-p calls)
      calls
    (seq-sorted (proof-unique (t3-book-theorems-recurrence-drivers formals calls)))))

(defun t3-book-theorems-drivers (name formals body)
  (t3-book-theorems-drivers-from-calls formals (t3-book-theorems-recurrences name formals body)))

(defun t3-book-theorems-definition-summary (definition)
  (let* ((name (car definition))
         (formals (cadr definition))
         (body (caddr definition))
         (calls (t3-book-theorems-recurrences name formals body)))
    (list name formals body calls (t3-book-theorems-drivers-from-calls formals calls))))

(defun t3-book-theorems-find-definition-summary (summaries name formals body)
  (let ((summary (assoc-equal name summaries)))
    (and summary (equal formals (cadr summary)) (equal body (caddr summary)) summary)))

(defun t3-book-theorems-definition-recurrences (summaries name formals body)
  (let ((summary (t3-book-theorems-find-definition-summary summaries name formals body)))
    (if summary (cadddr summary) (t3-book-theorems-recurrences name formals body))))

(defun t3-book-theorems-definition-drivers (summaries name formals body)
  (let ((summary (t3-book-theorems-find-definition-summary summaries name formals body)))
    (if summary (car (cddddr summary)) (t3-book-theorems-drivers name formals body))))

(defun t3-book-theorems-term-present-p (term)
  (cond ((acl2-numberp term) (not (equal term 0)))
        ((stringp term) (not (equal term "")))
        (t (if term t nil))))

(mutual-recursion
 (defun t3-book-theorems-pending-test (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) nil)
         ((endp term) '(:failure "failure" ""))
         ((equal (car term) *proof-quote*) nil)
         ((equal (car term) *proof-if*)
          (if (endp (cdr term))
              '(:failure "failure" "")
            (proof-with-checked-results ((pending (t3-book-theorems-pending-test (cadr term))))
              (if (t3-book-theorems-term-present-p pending) pending (cadr term)))))
         (t (t3-book-theorems-pending-test-arguments (cdr term)))))
 (defun t3-book-theorems-pending-test-arguments (args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results ((first (t3-book-theorems-pending-test (car args))))
       (if (t3-book-theorems-term-present-p first)
           first
         (t3-book-theorems-pending-test-arguments (cdr args)))))))

(defun t3-book-theorems-quoted-cost (term)
  (if (proof-is-call term *proof-quote*)
      (proof-with-checked-results ((datum (proof-term-at term 1)))
        (if (proof-compound datum) (floor (len datum) 4) 0))
    0))

(mutual-recursion
 (defun t3-book-theorems-count-term (term count limit)
   (declare (xargs :measure (acl2-count term)))
   (proof-with-checked-results ((quoted (t3-book-theorems-quoted-cost term)))
     (let ((next (+ 1 count quoted)))
       (cond ((> next limit) next)
             ((not (proof-compound term)) next)
             ((endp term) '(:failure "failure" ""))
             ((equal (car term) *proof-quote*) next)
             (t (t3-book-theorems-count-term-args (cdr term) next limit))))))
 (defun t3-book-theorems-count-term-args (args count limit)
   (declare (xargs :measure (acl2-count args)))
   (if (or (endp args) (> count limit))
       count
     (proof-with-checked-results
         ((next (t3-book-theorems-count-term (car args) count limit)))
       (t3-book-theorems-count-term-args (cdr args) next limit)))))

(defund t3-book-theorems-term-cost (term limit)
  (t3-book-theorems-count-term term 0 limit))

(defun t3-book-theorems-make-context
    (lib facts equalities projections rewrites contradiction frozen)
  (list :t3-book-theorems-context
        lib facts equalities projections rewrites contradiction frozen))

(defun t3-book-theorems-context-init (lib frozen)
  (t3-book-theorems-make-context
   lib nil nil nil nil nil (t3-book-theorems-sort-set frozen)))

(defun t3-book-theorems-context-lib (context)
  (nth 1 context))

(defun t3-book-theorems-context-facts (context)
  (nth 2 context))

(defun t3-book-theorems-context-equalities (context)
  (nth 3 context))

(defun t3-book-theorems-context-projections (context)
  (nth 4 context))

(defun t3-book-theorems-context-rewrites (context)
  (nth 5 context))

(defun t3-book-theorems-context-contradiction (context)
  (nth 6 context))

(defun t3-book-theorems-context-frozen (context)
  (nth 7 context))

(defun t3-book-theorems-context-with-facts (context facts contradiction)
  (t3-book-theorems-make-context
   (t3-book-theorems-context-lib context) facts
   (t3-book-theorems-context-equalities context)
   (t3-book-theorems-context-projections context)
   (t3-book-theorems-context-rewrites context)
   contradiction
   (t3-book-theorems-context-frozen context)))

(defun t3-book-theorems-context-with-recipes (context projections rewrites)
  (t3-book-theorems-make-context
   (t3-book-theorems-context-lib context)
   (t3-book-theorems-context-facts context)
   (t3-book-theorems-context-equalities context)
   projections rewrites
   (t3-book-theorems-context-contradiction context)
   (t3-book-theorems-context-frozen context)))

(defun t3-book-theorems-table-put-if-absent (table key value)
  (if (assoc-equal key table)
      table
    (table-put table key value)))

(defun t3-book-theorems-table-append (table key value)
  (table-put table key (append (table-get table key nil) (list value))))

(defun t3-book-theorems-context-set-equality (context term step)
  (t3-book-theorems-make-context
   (t3-book-theorems-context-lib context)
   (t3-book-theorems-context-facts context)
   (t3-book-theorems-table-put-if-absent
    (t3-book-theorems-context-equalities context) term step)
   (t3-book-theorems-context-projections context)
   (t3-book-theorems-context-rewrites context)
   (t3-book-theorems-context-contradiction context)
   (t3-book-theorems-context-frozen context)))

(defun t3-book-theorems-context-record-recipes (context step recipes)
  (declare (xargs :measure (acl2-count recipes)))
  (if (endp recipes)
      context
    (let* ((claim (caar recipes))
           (path (cadar recipes))
           (guards (caddar recipes))
           (recipe (list step path guards))
           (projections (t3-book-theorems-context-projections context))
           (rewrites (t3-book-theorems-context-rewrites context))
           (next-projections (if (and path guards)
                                 (t3-book-theorems-table-append projections claim recipe)
                               projections)))
      (proof-with-checked-results
          ((next-rewrites
            (if (proof-is-call claim *proof-equal*)
                (proof-with-checked-results
                    ((left (proof-term-at claim 1))
                     (right (proof-term-at claim 2)))
                  (if (equal left right)
                      rewrites
                    (t3-book-theorems-table-append rewrites left recipe)))
              rewrites)))
        (t3-book-theorems-context-record-recipes
         (t3-book-theorems-context-with-recipes context next-projections next-rewrites)
         step (cdr recipes))))))

(defun t3-book-theorems-context-record-equality (context step term)
  (if (not (proof-is-call term *proof-equal*))
      context
    (proof-with-checked-results ((parts (proof-list-of-length (cdr term) 2)))
      (let ((left (car parts))
            (right (cadr parts))
            (proof (library-library-proof (t3-book-theorems-context-lib context))))
        (cond
         ((and (not (equal left right))
               (not (proof-is-call left *proof-quote*))
               (or (not (proof-compound left)) (proof-is-call right *proof-quote*)))
          (proof-with-checked-results ((variables (t3-book-theorems-variables right)))
            (if (member-equal left variables)
                context
              (t3-book-theorems-context-set-equality context left step))))
         ((not (proof-compound right))
          (proof-with-checked-results ((variables (t3-book-theorems-variables left)))
            (if (member-equal right variables)
                context
              (proof-with-checked-results ((reversed (proof-proof-symmetric proof step)))
                (t3-book-theorems-context-set-equality context right reversed)))))
         (t context))))))

(defun t3-book-theorems-context-opposite (context step term)
  (let* ((proof (library-library-proof (t3-book-theorems-context-lib context)))
         (facts (t3-book-theorems-context-facts context))
         (denied (assoc-equal (proof-neg term) facts)))
    (cond (denied (proof-proof-cut proof step (cdr denied)))
          ((proof-is-call term *proof-not*)
           (proof-with-checked-results ((positive (proof-term-at term 1)))
             (let ((held (assoc-equal positive facts)))
               (if held
                   (proof-proof-cut proof (cdr held) step)
                 (t3-book-theorems-context-contradiction context)))))
          (t (t3-book-theorems-context-contradiction context)))))

(defund t3-book-theorems-context-step-consequences (context step)
  (proof-with-checked-results ((term (proof-step-first step)))
    (let ((facts (t3-book-theorems-context-facts context)))
      (cond
       ((or (assoc-equal term facts) (equal term *proof-true*)) (cons context nil))
       ((equal term *proof-false*)
        (cons (t3-book-theorems-context-with-facts context (table-put facts term step) step) nil))
       (t
        (let ((context (t3-book-theorems-context-with-facts
                        context (table-put facts term step)
                        (t3-book-theorems-context-contradiction context))))
          (proof-with-checked-results
              ((contradiction (t3-book-theorems-context-opposite context step term))
               (recipes (t3-book-theorems-projections term nil nil))
               (context
                (t3-book-theorems-context-record-recipes
                 (t3-book-theorems-context-with-facts
                  context (t3-book-theorems-context-facts context) contradiction)
                 step recipes))
               (context (t3-book-theorems-context-record-equality context step term))
               (parts (and (proof-is-call term *proof-if*) (equal (cadddr term) *proof-false*)
                           (proof-proof-conjunct
                            (library-library-proof (t3-book-theorems-context-lib context)) step))))
            (cons context parts))))))))

(defund t3-book-theorems-context-note-steps (n context steps)
  (declare (xargs :measure (nfix n)))
  (cond ((endp steps) context)
        ((zp n) '(:failure "Fuel" "t3-book-theorems-context-note"))
        (t
         (proof-with-checked-results ((noted (t3-book-theorems-context-step-consequences context (car steps))))
           (t3-book-theorems-context-note-steps
            (1- n) (car noted) (append (cdr noted) (cdr steps)))))))

(defund t3-book-theorems-context-note (context step)
  (t3-book-theorems-context-note-steps 1000000 context (list step)))

(defund t3-book-theorems-context-branch (context test holds)
  (proof-with-checked-results
      ((step (proof-proof-assume
              (library-library-proof (t3-book-theorems-context-lib context)) test holds)))
    (t3-book-theorems-context-note context step)))

(defun t3-book-theorems-context-nil-value (context term)
  (let ((denied (table-get (t3-book-theorems-context-facts context)
                            (proof-neg term) nil))
        (proof (library-library-proof (t3-book-theorems-context-lib context))))
    (if denied
        (proof-with-checked-results
            ((nil-or-true (proof-proof-nil-or-true proof term))
             (positive (proof-proof-front proof nil-or-true term)))
          (proof-proof-cut proof positive denied))
      nil)))

(defun t3-book-theorems-make-theorems (lib constructor-cases index rewrites fuel)
  (list :t3-book-theorems-theorems lib constructor-cases index rewrites fuel))

(defun t3-book-theorems-theorems-lib (search)
  (nth 1 search))

(defun t3-book-theorems-theorems-constructor-cases (search)
  (nth 2 search))

(defun t3-book-theorems-theorems-index (search)
  (nth 3 search))

(defun t3-book-theorems-theorems-rewrites (search)
  (nth 4 search))

(defun t3-book-theorems-theorems-fuel (search)
  (nth 5 search))

(defun t3-book-theorems-prepared-p (search)
  (eq (car search) :t3-book-theorems-prepared))

(defun t3-book-theorems-definition-summaries (search)
  (and (t3-book-theorems-prepared-p search) (nth 6 search)))

(defun t3-book-theorems-make-prepared-search (lib constructor-cases index rewrites fuel summaries)
  (list :t3-book-theorems-prepared lib constructor-cases index rewrites fuel summaries))

(defun t3-book-theorems-rebuild-search (search lib constructor-cases index rewrites fuel)
  (if (t3-book-theorems-prepared-p search)
      (t3-book-theorems-make-prepared-search
       lib constructor-cases index rewrites fuel (t3-book-theorems-definition-summaries search))
    (t3-book-theorems-make-theorems lib constructor-cases index rewrites fuel)))

(defun t3-book-theorems-with-definition-summaries (search summaries)
  (t3-book-theorems-make-prepared-search
   (t3-book-theorems-theorems-lib search)
   (t3-book-theorems-theorems-constructor-cases search)
   (t3-book-theorems-theorems-index search)
   (t3-book-theorems-theorems-rewrites search)
   (t3-book-theorems-theorems-fuel search)
   summaries))

(defun t3-book-theorems-theorems-with-lib (search lib)
  (t3-book-theorems-rebuild-search
   search lib (t3-book-theorems-theorems-constructor-cases search)
   (t3-book-theorems-theorems-index search)
   (t3-book-theorems-theorems-rewrites search)
   (t3-book-theorems-theorems-fuel search)))

(defun t3-book-theorems-theorems-with-fuel (search allowance)
  (t3-book-theorems-rebuild-search
   search
   (t3-book-theorems-theorems-lib search)
   (t3-book-theorems-theorems-constructor-cases search)
   (t3-book-theorems-theorems-index search)
   (t3-book-theorems-theorems-rewrites search)
   allowance))

(defun t3-book-theorems-theorems-with-constructor-cases (search enabled)
  (t3-book-theorems-rebuild-search
   search
   (t3-book-theorems-theorems-lib search)
   enabled
   (t3-book-theorems-theorems-index search)
   (t3-book-theorems-theorems-rewrites search)
   (t3-book-theorems-theorems-fuel search)))

(defun t3-book-theorems-theorems-with-indexes (search index rewrites)
  (t3-book-theorems-rebuild-search
   search
   (t3-book-theorems-theorems-lib search)
   (t3-book-theorems-theorems-constructor-cases search)
   index rewrites
   (t3-book-theorems-theorems-fuel search)))

(defun t3-book-theorems-set-included-p (items candidates)
  (or (endp items)
      (and (member-equal (car items) candidates)
           (t3-book-theorems-set-included-p (cdr items) candidates))))

(defun t3-book-theorems-guard-variables (guards)
  (if (endp guards)
      nil
    (proof-with-checked-results
        ((first (t3-book-theorems-variables (car guards)))
         (rest (t3-book-theorems-guard-variables (cdr guards))))
      (append first rest))))

(defun t3-book-theorems-index-rewrite-p (left right)
  (proof-with-checked-results ((right-terms (t3-book-theorems-terms right)))
    (if (member-equal left right-terms)
        nil
      (proof-with-checked-results
          ((right-variables (t3-book-theorems-variables right))
           (left-variables (t3-book-theorems-variables left)))
        (if (not (t3-book-theorems-set-included-p right-variables left-variables))
            nil
          (proof-with-checked-results
              ((left-head (t3-book-theorems-head left))
               (right-head (t3-book-theorems-head right)))
            (if (not (equal left-head right-head))
                t
              (proof-with-checked-results
                  ((right-terms (t3-book-theorems-terms right))
                   (left-terms (t3-book-theorems-terms left)))
                (< (len right-terms) (len left-terms))))))))))

(defund t3-book-theorems-index-rewrites (rewrites term recipe)
  (if (not (proof-is-call term *proof-equal*))
      rewrites
    (proof-with-checked-results ((left (proof-term-at term 1)))
      (if (and (proof-compound left) (not (proof-is-call left *proof-quote*)))
          (proof-with-checked-results
              ((parts (proof-list-of-length (cdr term) 2))
               (index-p (t3-book-theorems-index-rewrite-p left (cadr parts))))
            (if index-p
                (proof-with-checked-results ((key (t3-book-theorems-rule-key left)))
                  (t3-book-theorems-table-append rewrites key recipe))
              rewrites))
        rewrites))))

(defun t3-book-theorems-index-projections (search name projections)
  (declare (xargs :measure (acl2-count projections)))
  (if (endp projections)
      search
    (let* ((term (caar projections))
           (path (cadar projections))
           (guards (caddar projections)))
      (if (or (not (proof-compound term)) (proof-is-call term *proof-quote*))
          (t3-book-theorems-index-projections search name (cdr projections))
        (proof-with-checked-results
            ((variables (t3-book-theorems-guard-variables guards))
             (key (t3-book-theorems-rule-key term)))
          (let* ((recipe (list name term path guards (t3-book-theorems-sort-set variables)))
                 (index (t3-book-theorems-table-append
                         (t3-book-theorems-theorems-index search) key recipe)))
            (proof-with-checked-results
                ((rewrites (t3-book-theorems-index-rewrites
                            (t3-book-theorems-theorems-rewrites search) term recipe)))
              (t3-book-theorems-index-projections
               (t3-book-theorems-theorems-with-indexes search index rewrites)
               name (cdr projections)))))))))

(defun t3-book-theorems-theorems-index-fact (search name formula)
  (proof-with-checked-results
      ((projections (t3-book-theorems-projections formula nil nil)))
    (t3-book-theorems-index-projections search name projections)))

(defun t3-book-theorems-admit-library-facts (facts definitions search)
  (declare (xargs :measure (acl2-count facts)))
  (if (endp facts)
      search
    (let ((name (caar facts))
          (clause (cdar facts)))
      (proof-with-checked-results
          ((next (if (and (equal (len clause) 1) (not (assoc-equal name definitions)))
                     (t3-book-theorems-theorems-index-fact search name (car clause))
                   search)))
        (t3-book-theorems-admit-library-facts (cdr facts) definitions next)))))

(defun t3-book-theorems-index-statement (search data)
  (proof-with-checked-results ((parts (proof-list-of-length data 2)))
    (t3-book-theorems-theorems-index-fact search (car parts) (cadr parts))))

(defun t3-book-theorems-index-statements (search statements)
  (declare (xargs :measure (acl2-count statements)))
  (if (endp statements)
      search
    (proof-with-checked-results ((next (t3-book-theorems-index-statement search (car statements))))
      (t3-book-theorems-index-statements next (cdr statements)))))

(defun t3-book-theorems-theorems-add (search kind data)
  (cond ((member-equal kind '("theorem" "axiom"))
         (t3-book-theorems-index-statement search data))
        ((equal kind "constrain")
         (proof-with-checked-results ((facts (proof-term-at data 1)))
           (if (equal facts *proof-nil*)
               search
             (t3-book-theorems-index-statements search facts))))
        (t search)))

(defun t3-book-theorems-library (search)
  (t3-book-values-book-proofs-library (t3-book-theorems-theorems-lib search)))

(defun t3-book-theorems-proof (search)
  (library-library-proof (t3-book-theorems-library search)))

(defun t3-book-theorems-with-library (search lib)
  (t3-book-theorems-theorems-with-lib
   search (t3-book-values-book-proofs-with-library
           (t3-book-theorems-theorems-lib search) lib)))

(defun t3-book-theorems-new-context (search frozen)
  (t3-book-theorems-context-init (t3-book-theorems-library search) frozen))

(defun t3-book-theorems-theorems-init (lib)
  (let* ((search (t3-book-theorems-make-theorems lib nil nil nil :none))
         (proof (t3-book-theorems-proof search)))
    (t3-book-theorems-admit-library-facts
     (proof-proof-facts proof) (proof-proof-definitions proof) search)))

(defun t3-book-theorems-summarize-definitions (definitions)
  (if (endp definitions)
      nil
    (cons (t3-book-theorems-definition-summary (car definitions))
          (t3-book-theorems-summarize-definitions (cdr definitions)))))

(defun t3-book-theorems-prepare-definitions (search)
  (t3-book-theorems-with-definition-summaries
   search (t3-book-theorems-summarize-definitions
           (proof-proof-definitions (t3-book-theorems-proof search)))))

(defun t3-book-theorems-prefix-summaries (names definitions summaries)
  (if (endp names)
      summaries
    (let* ((name (car names))
           (definition (assoc-equal name definitions))
           (known (and definition
                       (t3-book-theorems-find-definition-summary
                        summaries name (cadr definition) (caddr definition)))))
      (t3-book-theorems-prefix-summaries
       (cdr names) definitions
       (if (and definition (not known))
           (cons (t3-book-theorems-definition-summary definition) summaries)
         summaries)))))

(defun t3-book-theorems-prepare-prefix-definitions (search names)
  (if (t3-book-theorems-prepared-p search)
      (t3-book-theorems-with-definition-summaries
       search (t3-book-theorems-prefix-summaries
               names (proof-proof-definitions (t3-book-theorems-proof search))
               (t3-book-theorems-definition-summaries search)))
    search))

(defun t3-book-theorems-variables-bound-p (variables bindings)
  (or (endp variables)
      (and (assoc-equal (car variables) bindings)
           (t3-book-theorems-variables-bound-p (cdr variables) bindings))))

(defun t3-book-theorems-match-guard (part head facts bindings)
  (declare (xargs :measure (acl2-count facts)))
  (if (endp facts)
      bindings
    (proof-with-checked-results ((known-head (t3-book-theorems-head (caar facts))))
      (if (not (equal head known-head))
          (t3-book-theorems-match-guard part head (cdr facts) bindings)
        (proof-with-checked-results ((trial (t3-book-theorems-match part (caar facts) bindings)))
          (if (car trial)
              (cdr trial)
            (t3-book-theorems-match-guard part head (cdr facts) bindings)))))))

(defun t3-book-theorems-bind-guard-parts (parts required bindings facts)
  (declare (xargs :measure (acl2-count parts)))
  (cond ((endp parts) (cons nil bindings))
        ((not (proof-compound (car parts)))
         (t3-book-theorems-bind-guard-parts (cdr parts) required bindings facts))
        (t (let ((part (car parts)))
             (proof-with-checked-results ((variables (t3-book-theorems-variables part)))
               (if (t3-book-theorems-variables-bound-p variables bindings)
                   (t3-book-theorems-bind-guard-parts (cdr parts) required bindings facts)
                 (proof-with-checked-results
                     ((head (t3-book-theorems-head part))
                      (trial (t3-book-theorems-match-guard part head facts bindings)))
                   (if (t3-book-theorems-variables-bound-p required trial)
                       (cons t trial)
                     (t3-book-theorems-bind-guard-parts (cdr parts) required trial facts)))))))))

(defun t3-book-theorems-theorems-bind-guards (guards required bindings context)
  (declare (xargs :measure (acl2-count guards)))
  (if (endp guards)
      :none
    (proof-with-checked-results
        ((parts (t3-book-theorems-conjuncts (car guards)))
         (bound (t3-book-theorems-bind-guard-parts
                 parts required bindings (t3-book-theorems-context-facts context))))
      (if (car bound)
          (cdr bound)
        (t3-book-theorems-theorems-bind-guards (cdr guards) required (cdr bound) context)))))

; Search calls carry the current allowance through successes and failures.
; Entry points return a failure as the full result.
(defund t3-book-theorems-search-failure-p (value)
  (failure-p value))

(defmacro t3-book-theorems-with-steps (search bindings result)
  (if (endp bindings)
      result
    (let ((name (caar bindings))
          (form (cadar bindings)))
      (list 'let (list (list 'checked-result form))
            (list 'if '(t3-book-theorems-search-failure-p checked-result)
                  (list 'cons 'checked-result search)
                  (list 'let (list (list name 'checked-result))
                        (list 't3-book-theorems-with-steps search (cdr bindings) result)))))))

(defmacro t3-book-theorems-with-search (binding result)
  (let ((value (car binding))
        (search (cadr binding))
        (form (caddr binding)))
    (list 'let* (list (list 'search-result form)
                     (list value '(car search-result))
                     (list search '(cdr search-result)))
          (list 'if (list 't3-book-theorems-search-failure-p value) 'search-result result))))

(defun t3-book-theorems-search-answer (result)
  (if (failure-p (car result))
      (car result)
    result))

(defun t3-book-theorems-allowance (search)
  (let ((allowance (t3-book-theorems-theorems-fuel search)))
    (if (eq allowance :none)
        '(:failure "failure" "")
      allowance)))

(defun t3-book-theorems-spend (search cost)
  (proof-with-checked-results ((allowance (t3-book-theorems-allowance search)))
    (t3-book-theorems-theorems-with-fuel search (- allowance cost))))

(defun t3-book-theorems-theorems-truth (search term)
  (if (or (not (proof-is-call term *proof-quote*)) (equal term *proof-false*))
      nil
    (let ((proof (t3-book-theorems-proof search)))
      (proof-with-checked-results
          ((step (proof-proof-nil-or-true proof term))
           (computed (proof-proof-compute proof (proof-eq term *proof-false*) *proof-nil*))
           (rewritten (proof-proof-rewrite proof step computed '(1))))
        (proof-proof-tidy proof rewritten)))))

(defun t3-book-theorems-constant (search term)
  (t3-book-values-book-proofs-constant (t3-book-theorems-theorems-lib search) term))

(defun t3-book-theorems-simplify-first (search step evidence definitions)
  (let ((proof (t3-book-theorems-proof search)))
    (proof-with-checked-results
        ((term (proof-step-first step))
         (equality (t3-book-values-book-proofs-simplify
                    (t3-book-theorems-theorems-lib search) term evidence definitions)))
      (if equality
          (proof-with-checked-results ((rewritten (proof-proof-rewrite proof step equality '(1))))
            (proof-proof-tidy proof rewritten))
        step))))

(defun t3-book-theorems-atomic-cons (search term)
  (let* ((lib (t3-book-theorems-library search))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((nonempty (proof-proof-fact
                    proof "consp-cons" (seq-zip (list *library-x* *library-y*) (cdr term))))
         (denied (proof-proof-assume proof term nil))
         (equation (t3-book-lemmas-nil-value lib denied))
         (contradiction (proof-proof-rewrite proof nonempty equation '(1 1)))
         (simplified (t3-book-theorems-simplify-first search contradiction nil nil)))
      (proof-proof-front proof simplified term))))

(defun t3-book-theorems-atomic-negation (search term)
  (if (not (proof-is-call term *proof-not*))
      nil
    (proof-with-checked-results ((value (proof-term-at term 1)))
      (if (and (proof-compound value) (not (proof-is-call value *proof-quote*)))
          (let ((proof (t3-book-theorems-proof search)))
            (proof-with-checked-results
                ((function (proof-term-at value 0))
                 (equation (and (member-equal function (proof-proof-primitives proof))
                                (t3-book-theorems-constant search value)))
                 (right (and equation (proof-rewritten-term equation))))
              (if (and equation (equal right *proof-false*))
                  (proof-with-checked-results
                      ((not-nil (proof-proof-not-nil proof))
                       (reverse (proof-proof-symmetric proof equation)))
                    (proof-proof-rewrite-result
                     proof not-nil reverse (proof-neg *proof-false*) *proof-false*))
                nil)))
        nil))))

(defun t3-book-theorems-atomic-primitive (search term)
  (let ((proof (t3-book-theorems-proof search)))
    (proof-with-checked-results ((function (proof-term-at term 0)))
      (if (or (equal function *proof-if*)
              (not (member-equal function (proof-proof-primitives proof))))
          nil
        (proof-with-checked-results ((equality (t3-book-theorems-constant search term)))
          (if (not equality)
              nil
            (proof-with-checked-results
                ((right (proof-rewritten-term equality))
                 (positive (t3-book-theorems-theorems-truth search right)))
              (and positive (proof-proof-transport proof positive equality)))))))))

(defun t3-book-theorems-theorems-atomic-value (search term)
  (cond
   ((and (t3-book-theorems-theorems-constructor-cases search)
         (proof-is-call term *proof-cons*))
    (t3-book-theorems-atomic-cons search term))
   (t
    (proof-with-checked-results
        ((boolean-value (and (proof-is-call term *t3-book-lemmas-booleanp*)
                             (proof-term-at term 1))))
      (if (member-equal boolean-value (list *proof-true* *proof-false*))
          (t3-book-values-book-proofs-prove
           (t3-book-theorems-theorems-lib search) term nil
           (list *t3-book-lemmas-booleanp* (proof-cl "EQ")))
        (proof-with-checked-results ((negative (t3-book-theorems-atomic-negation search term)))
          (or negative (t3-book-theorems-atomic-primitive search term))))))))

(defun t3-book-theorems-match-recipe (pattern term rewriting)
  (if (not rewriting)
      (t3-book-theorems-match pattern term nil)
    (proof-with-checked-results
        ((left (proof-term-at pattern 1))
         (matched (t3-book-theorems-match left term nil)))
      (if (not (car matched))
          matched
        (proof-with-checked-results
            ((right (proof-term-at pattern 2))
             (value (proof-subst right (cdr matched))))
          (cons (not (equal value term)) (cdr matched)))))))

(mutual-recursion
 (defun t3-book-theorems-quick-search (n search term context depth)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-quick") search)
     (t3-book-theorems-with-steps search
         ((known (or (table-get (t3-book-theorems-context-facts context) term nil)
                     (t3-book-theorems-theorems-truth search term))))
       (if (or known (< depth 0) (not (proof-compound term)))
           (cons known search)
         (t3-book-theorems-with-steps search
             ((atomic (t3-book-theorems-theorems-atomic-value search term)))
           (if atomic
               (cons atomic search)
             (t3-book-theorems-rule-search (1- n) search term context depth nil)))))))
 (defun t3-book-theorems-rule-search (n search term context depth rewriting)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-rule-search") search)
     (let* ((local-map (if rewriting (t3-book-theorems-context-rewrites context)
                         (t3-book-theorems-context-projections context)))
            (local (table-get local-map term nil)))
       (t3-book-theorems-with-search
        (step search (t3-book-theorems-try-local-rules (1- n) search local context depth))
        (if step
            (cons step search)
          (let ((index (if rewriting (t3-book-theorems-theorems-rewrites search)
                         (t3-book-theorems-theorems-index search))))
            (t3-book-theorems-with-steps search
                ((recipes (t3-book-theorems-candidates index term)))
              (t3-book-theorems-try-index-rules
               (1- n) search recipes term context depth rewriting))))))))
 (defun t3-book-theorems-try-local-rules (n search recipes context depth)
   (declare (xargs :measure (nfix n)))
   (cond
    ((endp recipes) (cons nil search))
    ((zp n) (cons '(:failure "Fuel" "t3-book-theorems-try-local-rules") search))
    (t (let* ((recipe (car recipes))
              (step (car recipe))
              (path (cadr recipe))
              (guards (caddr recipe)))
         (t3-book-theorems-with-search
          (premises search (t3-book-theorems-premises-search
                            (1- n) search guards nil context depth))
          (if (eq premises :none)
              (t3-book-theorems-try-local-rules (1- n) search (cdr recipes) context depth)
            (cons (t3-book-theorems-project
                   (t3-book-theorems-library search) step path premises)
                  search)))))))
 (defun t3-book-theorems-try-index-rules (n search recipes term context depth rewriting)
   (declare (xargs :measure (nfix n)))
   (cond
    ((endp recipes) (cons nil search))
    ((zp n) (cons '(:failure "Fuel" "t3-book-theorems-try-index-rules") search))
    (t
     (let* ((recipe (car recipes))
            (name (car recipe)))
       (if (and rewriting (t3-book-theorems-theorems-constructor-cases search)
                (not (equal name *t3-book-theorems-constructor-equality*)))
           (t3-book-theorems-try-index-rules (1- n) search (cdr recipes)
                                            term context depth rewriting)
         (t3-book-theorems-with-steps search ((search (t3-book-theorems-spend search 1)))
           (if (< (t3-book-theorems-theorems-fuel search) 0)
               (cons nil search)
             (t3-book-theorems-with-steps search
                 ((matched (t3-book-theorems-match-recipe (cadr recipe) term rewriting)))
               (t3-book-theorems-with-search
                (step search
                 (if (car matched)
                     (t3-book-theorems-apply-rule-search
                      (1- n) search name (caddr recipe) (cadddr recipe)
                      (nth 4 recipe) (cdr matched) context depth)
                   (cons nil search)))
                (if step
                    (cons step search)
                  (t3-book-theorems-try-index-rules (1- n) search (cdr recipes)
                                                   term context depth rewriting)))))))))))
 (defun t3-book-theorems-apply-rule-search
     (n search name path guards required bindings context depth)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-apply-rule") search)
     (t3-book-theorems-with-steps search
         ((bindings (if (t3-book-theorems-variables-bound-p required bindings)
                        bindings
                      (t3-book-theorems-theorems-bind-guards guards required bindings context))))
       (if (eq bindings :none)
           (cons nil search)
         (t3-book-theorems-with-search
          (premises search (t3-book-theorems-premises-search
                            (1- n) search guards bindings context depth))
          (if (eq premises :none)
              (cons nil search)
            (t3-book-theorems-with-steps search
                ((step (proof-proof-fact (t3-book-theorems-proof search)
                                         name (table-items bindings))))
              (cons (t3-book-theorems-project
                     (t3-book-theorems-library search) step path premises)
                    search))))))))
 (defun t3-book-theorems-premises-search (n search guards bindings context depth)
   (declare (xargs :measure (nfix n)))
   (cond
    ((endp guards) (cons nil search))
    ((< depth 0) (cons :none search))
    ((zp n) (cons '(:failure "Fuel" "t3-book-theorems-theorems-premises") search))
    (t
     (t3-book-theorems-with-steps search ((target (proof-subst (car guards) bindings)))
       (t3-book-theorems-with-search
        (step search (t3-book-theorems-quick-search (1- n) search target context (1- depth)))
        (t3-book-theorems-with-search
         (step search
          (if (or step (not (proof-is-call target *proof-if*)))
              (cons step search)
            (t3-book-theorems-premise-conjunct (1- n) search target context (1- depth))))
         (if (not step)
             (cons :none search)
           (t3-book-theorems-with-search
            (remaining search (t3-book-theorems-premises-search
                               (1- n) search (cdr guards) bindings context depth))
            (cons (if (eq remaining :none) :none (cons step remaining)) search)))))))))
 (defun t3-book-theorems-premise-conjunct (n search target context depth)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-premises") search)
     (t3-book-theorems-with-steps search ((otherwise (proof-term-at target 3)))
       (if (not (equal otherwise *proof-false*))
           (cons nil search)
         (t3-book-theorems-with-search
          (first search (t3-book-theorems-quick-search (1- n) search (cadr target) context depth))
          (t3-book-theorems-with-search
           (second search (t3-book-theorems-quick-search (1- n) search (caddr target) context depth))
           (let ((proof (t3-book-theorems-proof search)))
             (if (and first second)
                 (t3-book-theorems-with-steps search
                     ((selected (proof-proof-select proof target first)))
                   (cons (proof-proof-transport proof second selected) search))
               (cons nil search))))))))))

(defund t3-book-theorems-quick-result (search term context depth)
  (t3-book-theorems-quick-search 1000000 search term context depth))

(defund t3-book-theorems-rule-result (search term context depth rewriting)
  (t3-book-theorems-rule-search 1000000 search term context depth rewriting))

(defun t3-book-theorems-theorems-quick (search term context depth)
  (t3-book-theorems-search-answer
   (t3-book-theorems-quick-result search term context depth)))

(defun t3-book-theorems-theorems-instance (search term context depth)
  (t3-book-theorems-search-answer
   (t3-book-theorems-rule-result search term context depth nil)))

(defun t3-book-theorems-theorems-premises (search guards bindings context depth)
  (t3-book-theorems-search-answer
   (t3-book-theorems-premises-search 1000000 search guards bindings context depth)))

(defun t3-book-theorems-theorems-apply-rule
    (search name path guards required bindings context depth)
  (t3-book-theorems-search-answer
   (t3-book-theorems-apply-rule-search
    1000000 search name path guards required bindings context depth)))

(defun t3-book-theorems-theorems-rewriting (search term context)
  (t3-book-theorems-search-answer
   (t3-book-theorems-rule-result search term context 0 t)))

(defund t3-book-theorems-quick-test (search test context)
  (t3-book-theorems-with-search
   (held search (t3-book-theorems-quick-result search test context 0))
   (if held
       (cons held search)
     (t3-book-theorems-quick-result search (proof-neg test) context 0))))

(defun t3-book-theorems-test-known-value (search term context ignore)
  (t3-book-theorems-with-steps search ((head (t3-book-theorems-head term)))
    (if (or (not (member-equal head *t3-book-theorems-predicates*)) (equal term ignore))
        (cons nil search)
      (t3-book-theorems-with-search
       (positive search (t3-book-theorems-quick-result search term context 0))
       (cond ((not positive) (cons nil search))
             ((proof-is-call term *proof-equal*)
              (cons (t3-book-lemmas-true-equality
                     (t3-book-theorems-library search) positive)
                    search))
             (t
              (t3-book-theorems-with-search
               (boolean search (t3-book-theorems-quick-result search (list *t3-book-lemmas-booleanp* term) context 0))
               (cons (and boolean
                          (library-library-cite
                           (t3-book-theorems-library search) "T3-BOOLEAN-TRUE"
                           (list term) (list boolean positive)))
                     search))))))))

(defun t3-book-theorems-theorems-known-value (search term context ignore)
  (t3-book-theorems-search-answer
   (t3-book-theorems-test-known-value search term context ignore)))

(defun t3-book-theorems-theorems-constructor-equation-reconstruction (value lib context)
  (let ((cells (table-get (t3-book-theorems-context-facts context)
                           (list *proof-consp* value) nil)))
    (and cells
         (proof-with-checked-results
             ((elim (library-library-axiom lib "CAR-CDR-ELIM" (list value))))
           (proof-proof-modus-ponens (library-library-proof lib) elim cells)))))

(defun t3-book-theorems-count-calls-p (terms)
  (or (endp terms)
      (and (proof-is-call (car terms) *library-count*)
           (t3-book-theorems-count-calls-p (cdr terms)))))

(defun t3-book-theorems-constructor-count-equation (search term)
  (let* ((lib (t3-book-theorems-library search))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((args (proof-list-of-length (cdr term) 2))
         (whole (car args))
         (part (cadr args))
         (cell (proof-term-at whole 1))
         (value (proof-term-at part 1)))
      (cond
       ((equal whole part)
        (proof-with-checked-results
            ((integer (library-library-type-of lib whole nil))
             (weak (library-library-cite lib "WEAK-REFLEXIVE" (list whole) (list integer))))
          (t3-book-lemmas-nil-value lib weak)))
       ((and (proof-is-call cell *proof-cons*) (member-equal value (cdr cell)))
        (proof-with-checked-results
            ((cells (proof-proof-fact
                     proof "consp-cons" (seq-zip (list *library-x* *library-y*) (cdr cell))))
             (clause (library-library-builtin lib (if (equal value (cadr cell)) 2 3) cell))
             (discharged (proof-proof-discharge proof clause cells))
             (descent (t3-book-theorems-simplify-first search discharged nil nil))
             (order (library-library-ordinal-comparison lib part whole))
             (strict (proof-proof-rewrite proof descent order '(1)))
             (weak (library-library-as-weak lib strict)))
          (t3-book-lemmas-nil-value lib weak)))
       (t nil)))))

(defun t3-book-theorems-constructor-false-equation (search term context)
  (let* ((lib (t3-book-theorems-library search))
         (proof (library-library-proof lib))
         (facts (t3-book-theorems-context-facts context)))
    (proof-with-checked-results
        ((right (proof-term-at term 2))
         (value (if (equal right *proof-false*) (cadr term) right))
         (claimed (proof-proof-assume proof term t))
         (oriented (if (equal right *proof-false*)
                       claimed
                     (proof-proof-symmetric proof claimed))))
      (let ((positive (table-get facts value nil)))
        (if positive
            (proof-with-checked-results
                ((rewritten (proof-proof-rewrite proof positive oriented '(1)))
                 (tidied (proof-proof-tidy proof rewritten))
                 (denied (proof-proof-front proof tidied (proof-neg term))))
              (t3-book-lemmas-nil-value lib denied))
          (let ((cells (table-get facts (list *proof-consp* value) nil)))
            (and cells
                 (proof-with-checked-results
                     ((rewritten (proof-proof-rewrite proof cells oriented '(1 1)))
                      (impossible (t3-book-theorems-simplify-first search rewritten nil nil))
                      (denied (proof-proof-front proof impossible (proof-neg term))))
                   (t3-book-lemmas-nil-value lib denied)))))))))

(defun t3-book-theorems-constructor-expand-equality (proof term index reconstructed)
  (proof-with-checked-results
      ((reflexive (proof-proof-reflexive proof term))
       (reverse (proof-proof-symmetric proof reconstructed))
       (expanded (proof-proof-rewrite proof reflexive reverse (list 1 2 index)))
       (right (proof-rewritten-term expanded))
       (parts (proof-list-of-length (cdr right) 2))
       (fields (seq-zip (list *library-x* *library-y* *library-z* (proof-sym "U" "ACL2"))
                       (append (cdar parts) (cdadr parts))))
       (equality (proof-proof-fact proof *t3-book-theorems-constructor-equality* fields)))
    (proof-proof-chain proof expanded (list equality))))

(defun t3-book-theorems-constructor-side-equation (search term context index)
  (let* ((lib (t3-book-theorems-library search))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (proof-term-at term index))
         (other (proof-term-at term (- 3 index))))
      (if (or (not (proof-is-call other *proof-cons*))
              (proof-is-call value *proof-cons*))
          nil
        (proof-with-checked-results
            ((reconstructed (t3-book-theorems-theorems-constructor-equation-reconstruction
                             value lib context)))
          (if reconstructed
              (t3-book-theorems-constructor-expand-equality proof term index reconstructed)
            (let ((non-cell (proof-neg (list *proof-consp* value))))
              (proof-with-checked-results
                  ((atom-step (or (table-get (t3-book-theorems-context-facts context)
                                              non-cell nil)
                                  (t3-book-theorems-theorems-atomic-value search non-cell))))
                (and atom-step
                     (proof-with-checked-results
                         ((claimed (proof-proof-assume proof term t))
                          (oriented (if (= index 1) (proof-proof-symmetric proof claimed) claimed))
                          (other-cells (proof-proof-fact
                                        proof "consp-cons"
                                        (seq-zip (list *library-x* *library-y*) (cdr other))))
                          (cells (proof-proof-rewrite proof other-cells oriented '(1 1)))
                          (cut (proof-proof-cut proof cells atom-step))
                          (denied (proof-proof-front proof cut (proof-neg term))))
                       (t3-book-lemmas-nil-value lib denied)))))))))))

(defun t3-book-theorems-theorems-constructor-equation (search term context)
  (cond
   ((proof-is-call term *proof-cons*)
    (proof-with-checked-results ((left (proof-term-at term 1)))
      (and (proof-is-call left *library-car*)
           (proof-with-checked-results
               ((value (proof-term-at left 1))
                (right (proof-term-at term 2)))
             (and (equal right (list *library-cdr* value))
                  (t3-book-theorems-theorems-constructor-equation-reconstruction
                   value (t3-book-theorems-library search) context))))))
   ((and (proof-is-call term *proof-less*) (t3-book-theorems-count-calls-p (cdr term)))
    (t3-book-theorems-constructor-count-equation search term))
   ((proof-is-call term *proof-equal*)
    (proof-with-checked-results
        ((false-equality (and (member-equal *proof-false* (cdr term))
                              (t3-book-theorems-constructor-false-equation search term context))))
      (if false-equality
          false-equality
        (proof-with-checked-results
            ((left (t3-book-theorems-constructor-side-equation search term context 1)))
          (or left (t3-book-theorems-constructor-side-equation search term context 2))))))
   (t nil)))

(defun t3-book-theorems-trail-head-p (trail function)
  (if (endp trail)
      nil
    (proof-with-checked-results ((head (t3-book-theorems-head (car trail))))
      (or (equal head function) (t3-book-theorems-trail-head-p (cdr trail) function)))))

(defun t3-book-theorems-driver-arguments-p (indices term quoted frozen)
  (if (endp indices)
      t
    (proof-with-checked-results ((arg (proof-term-at term (car indices))))
      (if (if quoted (proof-is-call arg *proof-quote*) (not (member-equal arg frozen)))
          (t3-book-theorems-driver-arguments-p (cdr indices) term quoted frozen)
        nil))))

(defun t3-book-theorems-complete-selector (search term context function)
  (if (not (member-equal function (list *library-car* *library-cdr*)))
      (cons nil search)
    (t3-book-theorems-with-steps search ((value (proof-term-at term 1)))
      (t3-book-theorems-with-search
       (absent search (t3-book-theorems-quick-result search (proof-neg (list *proof-consp* value)) context 0))
       (if (not absent)
           (cons nil search)
         (let* ((lib (t3-book-theorems-library search))
                (proof (library-library-proof lib)))
           (t3-book-theorems-with-steps search
               ((first (library-library-axiom
                        lib (concatenate 'string "COMPLETION-OF-" (caddr function)) (list value)))
                (right (proof-rewritten-term first))
                (selected (proof-proof-select proof right absent)))
             (cons (proof-proof-chain proof first (list selected)) search))))))))

(defun t3-book-theorems-unfold-definition (search term context function definition)
  (if (not definition)
      (t3-book-theorems-complete-selector search term context function)
    (let ((body (caddr definition)))
      (t3-book-theorems-with-steps search
          ((drivers (t3-book-theorems-definition-drivers
                     (t3-book-theorems-definition-summaries search)
                     function (cadr definition) body))
           (long-body
            (and (t3-book-theorems-theorems-constructor-cases search)
                 (or drivers
                     (proof-with-checked-results ((cost (t3-book-theorems-term-cost body 65)))
                       (> cost 65))))))
        (if long-body
            (cons nil search)
          (t3-book-theorems-with-steps search
              ((unfrozen (t3-book-theorems-driver-arguments-p
                          drivers term nil (t3-book-theorems-context-frozen context))))
            (if unfrozen
                (cons (proof-proof-unfold (t3-book-theorems-proof search) term) search)
              (t3-book-theorems-complete-selector search term context function))))))))

(defund t3-book-theorems-open-term (search term context trail)
  (t3-book-theorems-with-steps search
      ((function (proof-term-at term 0))
       (constructor (and (t3-book-theorems-theorems-constructor-cases search)
                         (t3-book-theorems-theorems-constructor-equation search term context))))
    (if constructor
        (cons constructor search)
      (let ((definition (assoc-equal function (proof-proof-definitions (t3-book-theorems-proof search)))))
        (t3-book-theorems-with-steps search
            ((repeated (t3-book-theorems-trail-head-p trail function))
             (drivers (and repeated definition
                           (t3-book-theorems-definition-drivers
                            (t3-book-theorems-definition-summaries search)
                            function (cadr definition) (caddr definition))))
             (quoted (and drivers (t3-book-theorems-driver-arguments-p drivers term t nil))))
          (if (and repeated (not quoted))
              (cons nil search)
            (t3-book-theorems-unfold-definition search term context function definition)))))))

(defun t3-book-theorems-theorems-open-definition (search term context trail)
  (t3-book-theorems-search-answer (t3-book-theorems-open-term search term context trail)))

(defun t3-book-theorems-context-equation (term context ignore)
  (and (not (equal term ignore))
       (or (table-get (t3-book-theorems-context-equalities context) term nil)
           (t3-book-theorems-context-nil-value context term))))

(defun t3-book-theorems-book-normalize (search term evidence definitions)
  (t3-book-values-book-proofs-normalize
   (t3-book-theorems-theorems-lib search) term evidence definitions))

(mutual-recursion
 (defun t3-book-theorems-normalize-term (n search term context trail ignore)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-normalize") search)
     (t3-book-theorems-with-steps search ((search (t3-book-theorems-spend search 1)))
       (if (or (< (t3-book-theorems-theorems-fuel search) 0)
               (> (len trail) 24) (member-equal term trail)
               (proof-is-call term *proof-quote*))
           (cons nil search)
         (t3-book-theorems-with-steps search ((cost (t3-book-theorems-term-cost term 1000)))
           (if (> cost 1000)
               (cons nil search)
             (t3-book-theorems-with-steps search
                 ((search (t3-book-theorems-spend search (floor cost 40)))
                  (equation (t3-book-theorems-context-equation term context ignore)))
               (cond (equation
                      (t3-book-theorems-normalize-right
                       (1- n) search equation context (append trail (list term))))
                     ((not (proof-compound term)) (cons nil search))
                     (t (t3-book-theorems-normalize-call
                         (1- n) search term context trail ignore))))))))))
 (defun t3-book-theorems-normalize-call (n search term context trail ignore)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-normalize") search)
     (t3-book-theorems-with-steps search ((function (proof-term-at term 0)))
       (let ((proof (t3-book-theorems-proof search)))
         (cond
          ((or (proof-compound function) (member-equal function *t3-logic-wrappers*))
           (t3-book-theorems-with-steps search
               ((step (if (proof-compound function)
                          (proof-proof-beta proof term)
                        (proof-proof-unfold proof term))))
             (t3-book-theorems-normalize-right
              (1- n) search step context (append trail (list term)))))
          ((equal function *proof-if*)
           (t3-book-theorems-normalize-conditional (1- n) search term context trail))
          (t (t3-book-theorems-normalize-nonconditional
              (1- n) search term context trail ignore)))))))
 (defun t3-book-theorems-normalize-to (n search step value context trail)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-normalize") search)
     (t3-book-theorems-with-search
      (tail search (t3-book-theorems-normalize-term (1- n) search value context trail nil))
      (cons (proof-proof-chain (t3-book-theorems-proof search) step (list tail)) search))))
 (defun t3-book-theorems-normalize-right (n search step context trail)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-normalize") search)
     (t3-book-theorems-with-steps search ((value (proof-rewritten-term step)))
       (t3-book-theorems-normalize-to (1- n) search step value context trail))))
 (defun t3-book-theorems-normalize-conditional (n search term context trail)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-conditional") search)
     (t3-book-theorems-with-steps search ((parts (proof-list-of-length (cdr term) 3)))
       (let ((test (car parts))
             (yes (cadr parts))
             (no (caddr parts))
             (proof (t3-book-theorems-proof search)))
         (t3-book-theorems-with-search
          (held search (t3-book-theorems-quick-test search test context))
          (cond
           (held
            (t3-book-theorems-with-steps search ((selected (proof-proof-select proof term held)))
              (t3-book-theorems-normalize-right (1- n) search selected context trail)))
           ((equal test *proof-false*)
            (t3-book-theorems-with-steps search
                ((selected (proof-proof-fact
                            proof "if-nil" (seq-zip (list *library-y* *library-z*) (cdr parts)))))
              (t3-book-theorems-normalize-to (1- n) search selected no context trail)))
           ((equal yes no)
            (t3-book-theorems-with-steps search
                ((first (proof-proof-if-true proof term))
                 (second (proof-proof-if-false proof term))
                 (same (proof-proof-cases proof test first second)))
              (t3-book-theorems-normalize-to (1- n) search same yes context trail)))
           (t
            (t3-book-theorems-with-search
             (opened search (t3-book-theorems-normalize-term (1- n) search test context trail nil))
             (t3-book-theorems-with-steps search ((right (and opened (proof-rewritten-term opened))))
               (if (and opened (not (equal right test)))
                   (t3-book-theorems-with-steps search
                       ((reflexive (proof-proof-reflexive proof term))
                        (reduced (proof-proof-rewrite proof reflexive opened '(1 2 1))))
                     (t3-book-theorems-normalize-right (1- n) search reduced context trail))
                 (cons nil search)))))))))))
 (defun t3-book-theorems-normalize-nonconditional (n search term context trail ignore)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-normalize") search)
     (t3-book-theorems-with-steps search ((constant (t3-book-theorems-constant search term)))
       (if constant
           (cons constant search)
         (t3-book-theorems-with-search
          (known search (t3-book-theorems-test-known-value search term context ignore))
          (if known
              (cons known search)
            (t3-book-theorems-with-search
             (early search (t3-book-theorems-rule-result search term context 0 t))
             (if early
                 (t3-book-theorems-normalize-right
                  (1- n) search early context (append trail (list term)))
               (t3-book-theorems-with-search
                (equation search (t3-book-theorems-normalize-arguments
                                  (1- n) search term (cdr term) 1 context trail nil))
                (t3-book-theorems-normalize-current
                 (1- n) search term context trail ignore equation))))))))))
 (defun t3-book-theorems-normalize-arguments (n search term args index context trail equation)
   (declare (xargs :measure (nfix n)))
   (cond
    ((endp args) (cons equation search))
    ((zp n) (cons '(:failure "Fuel" "t3-book-theorems-theorems-normalize") search))
    (t
     (t3-book-theorems-with-search
      (changed search (t3-book-theorems-normalize-term (1- n) search (car args) context trail nil))
      (let ((proof (t3-book-theorems-proof search)))
        (t3-book-theorems-with-steps search
            ((next (if (not changed)
                       equation
                     (proof-with-checked-results
                         ((previous (or equation (proof-proof-reflexive proof term))))
                       (proof-proof-rewrite proof previous changed (list 1 2 index))))))
          (t3-book-theorems-normalize-arguments
           (1- n) search term (cdr args) (1+ index) context trail next)))))))
 (defun t3-book-theorems-normalize-current (n search term context trail ignore equation)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-normalize") search)
     (let ((proof (t3-book-theorems-proof search)))
       (t3-book-theorems-with-steps search
           ((current (if equation (proof-rewritten-term equation) term))
            (leaf (t3-book-theorems-constant search current)))
         (if leaf
             (cons (if equation (proof-proof-chain proof equation (list leaf)) leaf) search)
           (t3-book-theorems-with-steps search
               ((local (t3-book-theorems-context-equation current context ignore)))
             (t3-book-theorems-with-search
              (next search (if local
                               (cons local search)
                             (t3-book-theorems-rule-result search current context 0 t)))
              (t3-book-theorems-with-search
               (next search (if next
                                (cons next search)
                              (t3-book-theorems-open-term search current context trail)))
               (if next
                   (t3-book-theorems-with-search
                    (step search (t3-book-theorems-normalize-right
                                  (1- n) search next context (append trail (list current))))
                    (cons (if equation (proof-proof-chain proof equation (list step)) step) search))
                 (cons (and equation (proof-proof-tidy proof equation)) search)))))))))))

(defund t3-book-theorems-normalization-result (search term context trail ignore)
  (t3-book-theorems-normalize-term 1000000 search term context trail ignore))

(defun t3-book-theorems-theorems-normalize (search term context trail ignore)
  (t3-book-theorems-search-answer
   (t3-book-theorems-normalization-result search term context trail ignore)))

(defun t3-book-theorems-theorems-conditional (search term context trail)
  (t3-book-theorems-search-answer
   (t3-book-theorems-normalize-conditional 1000000 search term context trail)))

(defun t3-book-theorems-congruence-arguments (search left right context index result)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      (cons (proof-proof-tidy (t3-book-theorems-proof search) result) search)
    (if (equal (car left) (car right))
        (t3-book-theorems-congruence-arguments
         search (cdr left) (cdr right) context (1+ index) result)
      (t3-book-theorems-with-search
       (step search (t3-book-theorems-quick-result search (proof-eq (car left) (car right)) context 0))
       (if (not step)
           (cons nil search)
         (t3-book-theorems-with-steps search
             ((next (proof-proof-rewrite
                     (t3-book-theorems-proof search) result step (list 1 2 index))))
           (t3-book-theorems-congruence-arguments
            search (cdr left) (cdr right) context (1+ index) next)))))))

(defun t3-book-theorems-match-congruence (search term context)
  (if (not (proof-is-call term *proof-equal*))
      (cons nil search)
    (t3-book-theorems-with-steps search ((parts (proof-list-of-length (cdr term) 2)))
      (let* ((left (car parts))
             (right (cadr parts))
             (proof (t3-book-theorems-proof search)))
        (if (equal left right)
            (cons (proof-proof-reflexive proof left) search)
          (let ((reverse-step (table-get (t3-book-theorems-context-facts context)
                                          (proof-eq right left) nil)))
            (if reverse-step
                (cons (proof-proof-symmetric proof reverse-step) search)
              (t3-book-theorems-with-steps search
                  ((left-head (t3-book-theorems-head left))
                   (right-head (t3-book-theorems-head right)))
                (if (or (not (equal left-head right-head))
                        (not left-head) (equal left-head *proof-quote*)
                        (not (equal (len left) (len right))))
                    (cons nil search)
                  (t3-book-theorems-with-steps search
                      ((initial (proof-proof-reflexive proof left)))
                    (t3-book-theorems-congruence-arguments
                     search (cdr left) (cdr right) context 1 initial)))))))))))

(defun t3-book-theorems-theorems-congruence (search term context)
  (t3-book-theorems-search-answer (t3-book-theorems-match-congruence search term context)))

(defun t3-book-theorems-quick-or-congruence (search term context)
  (t3-book-theorems-with-search
   (known search (t3-book-theorems-quick-result search term context 1))
   (if known
       (cons known search)
     (t3-book-theorems-match-congruence search term context))))

(defund t3-book-theorems-reduce (search term context)
  (t3-book-theorems-with-search
   (known search (t3-book-theorems-quick-or-congruence search term context))
   (if known
       (cons (list known nil) search)
     (t3-book-theorems-with-search
      (reduced search (t3-book-theorems-normalization-result search term context nil nil))
      (if (not reduced)
          (cons '(nil nil) search)
        (t3-book-theorems-with-steps search ((normal (proof-rewritten-term reduced)))
          (t3-book-theorems-with-search
           (result search (t3-book-theorems-quick-or-congruence search normal context))
           (if (not result)
               (cons (list nil reduced) search)
             (t3-book-theorems-with-steps search
                 ((transported (proof-proof-transport (t3-book-theorems-proof search) result reduced)))
               (cons (list transported nil) search))))))))))

(defun t3-book-theorems-theorems-reduce-goal (search term context)
  (t3-book-theorems-search-answer (t3-book-theorems-reduce search term context)))

(defun t3-book-theorems-saturation-note (search premise equality denied context)
  (let ((proof (t3-book-theorems-proof search)))
    (proof-with-checked-results
        ((derived (proof-proof-rewrite proof premise equality (if denied '(1 1) '(1))))
         (right (proof-rewritten-term equality))
         (derived
          (if (and denied (member-equal right (list *proof-true* *proof-false*)))
              (proof-with-checked-results
                  ((term (proof-step-first derived))
                   (reduced (t3-book-theorems-book-normalize search term nil (list *proof-not*))))
                (proof-proof-rewrite proof derived reduced '(1)))
            derived))
         (literal (proof-step-first derived))
         (derived (if (equal literal *proof-false*)
                      derived
                    (proof-proof-tidy proof derived)))
         (context (t3-book-theorems-context-note context derived))
         (literal (proof-step-first derived))
         (test (t3-book-theorems-pending-test literal)))
      (cons test context))))

(defund t3-book-theorems-saturation-pass (search premises context choices)
  (declare (xargs :measure (acl2-count premises)))
  (if (endp premises)
      (cons (list choices context nil) search)
    (t3-book-theorems-with-steps search ((literal (proof-step-first (car premises))))
      (if (equal literal *proof-false*)
          (cons (list choices context t) search)
        (let* ((denied (and (t3-book-theorems-theorems-constructor-cases search)
                            (proof-is-call literal *proof-not*)))
               (premise (car premises)))
          (t3-book-theorems-with-steps search
              ((subject (if denied (proof-term-at literal 1) literal)))
            (t3-book-theorems-with-search
             (equation search
              (t3-book-theorems-normalization-result search subject context nil subject))
             (t3-book-theorems-with-steps search
                 ((right (and equation (proof-rewritten-term equation)))
                  (noted (if (and equation (not (equal right subject)))
                             (t3-book-theorems-saturation-note search premise equation denied context)
                           (cons nil context))))
               (let* ((test (car noted))
                      (context (cdr noted))
                      (choices (if (t3-book-theorems-term-present-p test)
                                   (cons test choices)
                                 choices)))
                 (if (or (< (t3-book-theorems-theorems-fuel search) 0)
                         (t3-book-theorems-context-contradiction context))
                     (cons (list choices context t) search)
                   (t3-book-theorems-saturation-pass
                    search (cdr premises) context choices)))))))))))

(defund t3-book-theorems-saturate-context (passes search context choices)
  (declare (xargs :measure (nfix passes)))
  (if (zp passes)
      (cons (cons (reverse choices) context) search)
    (let ((facts (t3-book-theorems-context-facts context)))
      (t3-book-theorems-with-search
       (pass search (t3-book-theorems-saturation-pass search (table-values facts) context choices))
       (let ((choices (car pass))
             (context (cadr pass))
             (stopped (caddr pass)))
         (if (or stopped (equal (len (t3-book-theorems-context-facts context)) (len facts)))
             (cons (cons (reverse choices) context) search)
           (t3-book-theorems-saturate-context (1- passes) search context choices)))))))

(defun t3-book-theorems-theorems-saturate (search context)
  (let ((result (t3-book-theorems-saturate-context 3 search context nil)))
    (if (failure-p (car result))
        (car result)
      (cons (caar result) (cons (cdr result) (cdar result))))))

(defund t3-book-theorems-result-true-branch (search value test step)
  (let ((lib (t3-book-theorems-library search)))
    (proof-with-checked-results
        ((selected (proof-proof-if-true (library-library-proof lib) value))
         (result (library-library-transport-argument lib step selected 1)))
      (cons result (member-equal (proof-neg test) (proof-step-clause result))))))

(mutual-recursion
 (defun t3-book-theorems-result-search (n search formula context trail)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-result-cases") search)
     (t3-book-theorems-with-steps search ((allowance (t3-book-theorems-allowance search)))
       (if (or (< allowance 0) (> (len trail) 10))
           (cons nil search)
         (let ((search (t3-book-theorems-theorems-with-fuel search (- allowance 3))))
           (t3-book-theorems-with-search
            (known search (t3-book-theorems-quick-result search formula context 1))
            (if known
                (cons known search)
              (t3-book-theorems-with-steps search
                  ((parts (proof-list-of-length formula 2))
                   (function (t3-book-theorems-head (cadr parts))))
                (t3-book-theorems-result-value
                 (1- n) search formula (car parts) (cadr parts) function context trail)))))))))
 (defun t3-book-theorems-result-value (n search formula predicate value function context trail)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "Fuel" "t3-book-theorems-theorems-result-cases") search))
    ((equal function *proof-quote*)
     (t3-book-theorems-with-search
      (result search (t3-book-theorems-reduce search formula context))
      (cons (car result) search)))
    ((not function) (cons nil search))
    (t
     (t3-book-theorems-with-steps search ((cost (t3-book-theorems-term-cost value 1000)))
       (cond
        ((> cost 400) (cons nil search))
        ((equal function *proof-if*)
         (t3-book-theorems-result-conditional (1- n) search predicate value context trail))
        ((proof-compound function)
         (t3-book-theorems-with-steps search ((opened (proof-proof-beta (t3-book-theorems-proof search) value)))
           (t3-book-theorems-result-opened
            (1- n) search predicate opened context (append trail (list function)))))
        ((or (member-equal function trail) (member-equal function (list *library-car* *library-cdr*)))
         (cons nil search))
        (t
         (t3-book-theorems-with-search
          (opened search (t3-book-theorems-open-term search value context nil))
          (if opened
              (t3-book-theorems-result-opened
               (1- n) search predicate opened context (append trail (list function)))
            (cons nil search)))))))))
 (defun t3-book-theorems-result-opened (n search predicate opened context trail)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-result-cases") search)
     (t3-book-theorems-with-steps search ((right (proof-rewritten-term opened)))
       (t3-book-theorems-with-search
        (step search (t3-book-theorems-result-search (1- n) search (list predicate right) context trail))
        (cons (and step (library-library-transport-argument
                         (t3-book-theorems-library search) step opened 1))
              search)))))
 (defun t3-book-theorems-result-conditional (n search predicate value context trail)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-result-cases") search)
     (t3-book-theorems-with-steps search ((parts (proof-list-of-length (cdr value) 3)))
       (let ((test (car parts))
             (yes (cadr parts))
             (no (caddr parts))
             (proof (t3-book-theorems-proof search)))
         (t3-book-theorems-with-search
          (decided search (t3-book-theorems-quick-test search test context))
          (if decided
              (t3-book-theorems-with-steps search ((selected (proof-proof-select proof value decided)))
                (t3-book-theorems-result-opened (1- n) search predicate selected context trail))
            (t3-book-theorems-with-steps search
                ((true-context (t3-book-theorems-context-branch context test t)))
              (t3-book-theorems-with-search
               (first search (t3-book-theorems-result-search
                              (1- n) search (list predicate yes) true-context trail))
               (if (not first)
                   (cons nil search)
                 (t3-book-theorems-with-steps search
                     ((branch (t3-book-theorems-result-true-branch search value test first))
                      (first (car branch)))
                   (if (not (cdr branch))
                       (cons first search)
                     (t3-book-theorems-with-steps search
                         ((false-context (t3-book-theorems-context-branch context test nil)))
                       (t3-book-theorems-with-search
                        (second search (t3-book-theorems-result-search
                                        (1- n) search (list predicate no) false-context trail))
                        (if (not second)
                            (cons nil search)
                          (t3-book-theorems-with-steps search
                              ((selected (proof-proof-if-false proof value))
                               (second (library-library-transport-argument
                                        (t3-book-theorems-library search) second selected 1)))
                            (cons (proof-proof-cases proof test first second) search)))))))))))))))))

(defund t3-book-theorems-result-proof (search formula context trail)
  (t3-book-theorems-result-search 1000000 search formula context trail))

(defun t3-book-theorems-theorems-result-cases (search formula context trail)
  (t3-book-theorems-search-answer
   (t3-book-theorems-result-proof search formula context trail)))

(defun t3-book-theorems-theorems-definition-equation (search term)
  (if (not (proof-is-call term *proof-equal*))
      nil
    (proof-with-checked-results ((cost (t3-book-theorems-term-cost term 140)))
      (if (> cost 140)
          nil
        (proof-with-checked-results
            ((sides (proof-list-of-length (cdr term) 2))
             (left (car sides))
             (right (cadr sides))
             (function (t3-book-theorems-head left)))
          (let* ((proof (t3-book-theorems-proof search))
                 (definition (assoc-equal function (proof-proof-definitions proof))))
            (if (not definition)
                nil
              (proof-with-checked-results
                  ((body (proof-term-at (cdr definition) 1))
                   (cost (t3-book-theorems-term-cost body 140)))
                (if (> cost 140)
                    nil
                  (proof-with-checked-results
                      ((opened (proof-proof-unfold proof left))
                       (value (proof-rewritten-term opened))
                       (reduced (t3-book-theorems-book-normalize
                                 search value nil *t3-book-theorems-guard-words*))
                       (lhs (proof-proof-chain proof opened (list reduced)))
                       (left-value (proof-rewritten-term lhs)))
                    (if (equal left-value right)
                        lhs
                      (proof-with-checked-results
                          ((rhs (t3-book-theorems-book-normalize
                                 search right nil *t3-book-theorems-guard-words*))
                           (right-value (and rhs (proof-rewritten-term rhs))))
                        (if (and rhs (equal left-value right-value))
                            (proof-with-checked-results ((reverse (proof-proof-symmetric proof rhs)))
                              (proof-proof-chain proof lhs (list reverse)))
                          nil)))))))))))))

(defun t3-book-theorems-alias-arguments-p (args formals)
  (or (endp args)
      (and (or (proof-is-call (car args) *proof-quote*) (member-equal (car args) formals))
           (t3-book-theorems-alias-arguments-p (cdr args) formals))))

(defun t3-book-theorems-alias-body-p (proof function)
  (let ((definition (assoc-equal function (proof-proof-definitions proof))))
    (and definition
         (proof-with-checked-results
             ((parts (proof-list-of-length (cdr definition) 2))
              (body (cadr parts)))
           (and (proof-compound body)
                (proof-with-checked-results ((operator (t3-book-theorems-head body)))
                  (and (not (member-equal operator (list *proof-if* *proof-quote* function)))
                       (not (proof-compound operator))
                       (t3-book-theorems-alias-arguments-p (cdr body) (car parts)))))))))

(mutual-recursion
 (defun t3-book-theorems-theorems-reveal-alias (search term place)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) nil)
         ((endp term) '(:failure "failure" ""))
         ((equal (car term) *proof-quote*) nil)
         (t
          (let ((proof (t3-book-theorems-proof search)))
            (proof-with-checked-results ((alias (t3-book-theorems-alias-body-p proof (car term))))
              (if alias
                  (proof-with-checked-results ((opened (proof-proof-unfold proof term)))
                    (list opened place))
                (t3-book-theorems-reveal-alias-arguments search (cdr term) place 1)))))))
 (defun t3-book-theorems-reveal-alias-arguments (search args place index)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((found (t3-book-theorems-theorems-reveal-alias
                  search (car args) (append place (list index)))))
       (or found (t3-book-theorems-reveal-alias-arguments search (cdr args) place (1+ index)))))))

(defund t3-book-theorems-alias-equation (search term equation)
  (let ((proof (t3-book-theorems-proof search)))
    (proof-with-checked-results
        ((current (if equation (proof-rewritten-term equation) term))
         (revealed (t3-book-theorems-theorems-reveal-alias search current nil)))
      (and revealed
           (proof-with-checked-results
               ((previous (or equation (proof-proof-reflexive proof term)))
                (replaced (proof-proof-rewrite
                           proof previous (car revealed) (append '(1 2) (cadr revealed)))))
             (proof-proof-tidy proof replaced))))))

(defun t3-book-theorems-alias-consequence-loop (attempts search term context equation)
  (declare (xargs :measure (nfix attempts)))
  (if (zp attempts)
      (cons nil search)
    (t3-book-theorems-with-steps search ((equation (t3-book-theorems-alias-equation search term equation)))
      (if (not equation)
          (cons nil search)
        (t3-book-theorems-with-steps search ((right (proof-rewritten-term equation)))
          (t3-book-theorems-with-search
           (found search (t3-book-theorems-quick-result search right context 0))
           (if found
               (cons (proof-proof-transport (t3-book-theorems-proof search) found equation) search)
             (t3-book-theorems-alias-consequence-loop
              (1- attempts) search term context equation))))))))

(defun t3-book-theorems-theorems-alias-consequence (search term context)
  (t3-book-theorems-search-answer
   (t3-book-theorems-alias-consequence-loop 4 search term context nil)))

(defun t3-book-theorems-proved (step search context)
  (if (failure-p step)
      (cons step search)
    (cons (cons step context) search)))

(defun t3-book-theorems-remove-false (clause)
  (cond ((endp clause) nil)
        ((equal (car clause) *proof-false*) (t3-book-theorems-remove-false (cdr clause)))
        (t (cons (car clause) (t3-book-theorems-remove-false (cdr clause))))))

(defun t3-book-theorems-denied-implication (search term denied)
  (let ((proof (t3-book-theorems-proof search)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof term))
         (body (proof-rewritten-term opened))
         (true (proof-proof-prove proof *proof-true* nil nil))
         (selection (proof-proof-if-false proof body))
         (false (proof-proof-transport proof true selection))
         (discharged (proof-proof-discharge proof false denied)))
      (proof-proof-transport proof discharged opened))))

(defun t3-book-theorems-undecided-test-p (test facts)
  (and (not (assoc-equal test facts)) (not (assoc-equal (proof-neg test) facts))))

(defun t3-book-theorems-first-undecided-test (choices facts)
  (cond ((endp choices) nil)
        ((t3-book-theorems-undecided-test-p (car choices) facts) (car choices))
        (t (t3-book-theorems-first-undecided-test (cdr choices) facts))))

(defund t3-book-theorems-goal-test (search current choices facts)
  (proof-with-checked-results ((pending (t3-book-theorems-pending-test current)))
    (let* ((constructors (t3-book-theorems-theorems-constructor-cases search))
           (premise (and (or (null pending) constructors)
                         (t3-book-theorems-first-undecided-test choices facts)))
           (test (if (t3-book-theorems-term-present-p premise) premise pending)))
      (if (and (null test) constructors (proof-is-call current *proof-consp*))
          current
        test))))

(mutual-recursion
 (defun t3-book-theorems-prove-term (n search term context depth)
   (declare (xargs :measure (nfix n)))
   (let ((contradiction (t3-book-theorems-context-contradiction context)))
     (cond
      ((zp n) (cons '(:failure "Fuel" "t3-book-theorems-theorems-prove") search))
      (contradiction
       (t3-book-theorems-proved
        (proof-proof-subsume
         (t3-book-theorems-proof search) contradiction
         (proof-unique (cons term (t3-book-theorems-remove-false (proof-step-clause contradiction)))))
        search context))
      ((< depth 0) (cons '(:failure "Unsupported" "") search))
      (t
       (t3-book-theorems-with-steps search ((allowance (t3-book-theorems-allowance search)))
         (if (< allowance 0)
             (cons '(:failure "Unsupported" "") search)
           (t3-book-theorems-with-search
            (known search (t3-book-theorems-quick-result search term context 0))
            (cond
             (known (t3-book-theorems-proved known search context))
             ((proof-is-call term *library-implies*)
              (t3-book-theorems-prove-implication (1- n) search term context depth))
             (t
              (t3-book-theorems-with-search
               (step search
                (if (and (proof-compound term) (equal (len term) 2)
                         (not (member-equal (car term) (list *proof-not* *proof-quote*))))
                    (t3-book-theorems-result-proof search term context nil)
                  (cons nil search)))
               (if step
                   (t3-book-theorems-proved step search context)
                 (t3-book-theorems-prove-reduced (1- n) search term context depth))))))))))))
 (defun t3-book-theorems-prove-implication (n search term context depth)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-prove") search)
     (t3-book-theorems-with-steps search ((parts (proof-list-of-length (cdr term) 2)))
       (let* ((test (car parts))
              (conclusion (cadr parts))
              (denied (table-get (t3-book-theorems-context-facts context) (proof-neg test) nil)))
         (if denied
             (t3-book-theorems-proved (t3-book-theorems-denied-implication search term denied) search context)
           (t3-book-theorems-with-steps search
               ((branch (t3-book-theorems-context-branch context test t)))
             (t3-book-theorems-with-search
              (yes search (t3-book-theorems-prove-term (1- n) search conclusion branch (1- depth)))
              (t3-book-theorems-proved
               (t3-book-lemmas-implication (t3-book-theorems-library search) term (car yes))
               search context))))))))
 (defun t3-book-theorems-prove-reduced (n search term context depth)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-prove") search)
     (t3-book-theorems-with-search
      (result search (t3-book-theorems-reduce search term context))
      (if (car result)
          (t3-book-theorems-proved (car result) search context)
        (t3-book-theorems-with-steps search
            ((otherwise (and (proof-is-call term *proof-if*) (proof-term-at term 3))))
          (if (equal otherwise *proof-false*)
              (t3-book-theorems-prove-conjunct (1- n) search term context depth)
            (t3-book-theorems-prove-saturated (1- n) search term context depth)))))))
 (defun t3-book-theorems-prove-conjunct (n search term context depth)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-prove") search)
     (t3-book-theorems-with-search
      (guard search (t3-book-theorems-prove-term (1- n) search (cadr term) context (1- depth)))
      (t3-book-theorems-with-steps search ((context (t3-book-theorems-context-note (cdr guard) (car guard))))
        (t3-book-theorems-with-search
         (consequent search (t3-book-theorems-prove-term
                             (1- n) search (caddr term) context (1- depth)))
         (let ((proof (t3-book-theorems-proof search)))
           (t3-book-theorems-with-steps search ((selected (proof-proof-select proof term (car guard))))
             (t3-book-theorems-proved
              (proof-proof-transport proof (car consequent) selected) search (cdr consequent)))))))))
 (defun t3-book-theorems-prove-saturated (n search term context depth)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-prove") search)
     (t3-book-theorems-with-search
      (saturated search (t3-book-theorems-saturate-context 3 search context nil))
      (let ((choices (car saturated))
            (context (cdr saturated)))
        (if (t3-book-theorems-context-contradiction context)
            (t3-book-theorems-prove-term (1- n) search term context depth)
          (t3-book-theorems-with-search
           (result search (t3-book-theorems-reduce search term context))
           (if (car result)
               (t3-book-theorems-proved (car result) search context)
             (t3-book-theorems-with-steps search
                 ((current (if (cadr result) (proof-rewritten-term (cadr result)) term))
                  (test (t3-book-theorems-goal-test
                         search current choices (t3-book-theorems-context-facts context))))
               (if (and test (t3-book-theorems-undecided-test-p test (t3-book-theorems-context-facts context)))
                   (t3-book-theorems-prove-cases (1- n) search term test context depth)
                 (cons '(:failure "Unsupported" "") search))))))))))
 (defun t3-book-theorems-prove-cases (n search term test context depth)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-theorems-prove") search)
     (t3-book-theorems-with-steps search ((branch (t3-book-theorems-context-branch context test t)))
       (t3-book-theorems-with-search
        (yes search (t3-book-theorems-prove-term (1- n) search term branch (1- depth)))
        (t3-book-theorems-with-steps search ((branch (t3-book-theorems-context-branch context test nil)))
          (t3-book-theorems-with-search
           (no search (t3-book-theorems-prove-term (1- n) search term branch (1- depth)))
           (t3-book-theorems-proved
            (proof-proof-cases (t3-book-theorems-proof search) test (car yes) (car no))
            search context))))))))

(defun t3-book-theorems-theorems-prove (search term context depth)
  (let ((result (t3-book-theorems-prove-term 1000000 search term context depth)))
    (if (failure-p (car result))
        (car result)
      (cons (caar result) (cons (cdr result) (cdar result))))))

(defun t3-book-theorems-binding-values (bindings)
  (if (endp bindings)
      nil
    (proof-with-checked-results
        ((pair (proof-list-of-length (car bindings) 2))
         (rest (t3-book-theorems-binding-values (cdr bindings))))
      (cons (cadr pair) rest))))

(defun t3-book-theorems-induction-values (substitutions)
  (if (endp substitutions)
      nil
    (proof-with-checked-results
        ((values (t3-book-theorems-binding-values (car substitutions)))
         (rest (t3-book-theorems-induction-values (cdr substitutions))))
      (append values rest))))

(defun t3-book-theorems-bindings-from-pairs (pairs bindings)
  (declare (xargs :measure (acl2-count pairs)))
  (if (endp pairs)
      bindings
    (proof-with-checked-results ((pair (proof-list-of-length (car pairs) 2)))
      (t3-book-theorems-bindings-from-pairs
       (cdr pairs) (table-put bindings (car pair) (cadr pair))))))

(defun t3-book-theorems-induction-notes (lib formula measure substitutions context evidence)
  (declare (xargs :measure (acl2-count substitutions)))
  (if (endp substitutions)
      context
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((bindings (t3-book-theorems-bindings-from-pairs (car substitutions) nil))
           (child (proof-subst measure bindings))
           (smaller (list *proof-ordinal-less* child measure))
           (direct (t3-size-direct-builtin lib (list smaller) evidence))
           (descent (if (car direct)
                        direct
                      (t3-size-count-descent lib child measure (cdr direct))))
           (claim (proof-subst formula bindings))
           (hypothesis (proof-ite smaller claim *proof-true*))
           (assumption (proof-proof-assume proof hypothesis t))
           (step (proof-proof-prove-if proof assumption (car descent)))
           (context (t3-book-theorems-context-note context step)))
        (t3-book-theorems-induction-notes
         lib formula measure (cdr substitutions) context (cdr descent))))))

(defund t3-book-theorems-induct-on (search formula variable test recurs-on-true substitutions)
  (let* ((lib (t3-book-theorems-library search))
         (proof (library-library-proof lib))
         (measure (list *library-count* variable)))
    (t3-book-theorems-with-steps search
        ((frozen (t3-book-theorems-induction-values substitutions))
         (recursive (t3-book-theorems-context-branch
                     (t3-book-theorems-new-context search frozen) test recurs-on-true))
         (evidence (t3-logic-evidence-init lib (list (list test recurs-on-true)) nil nil))
         (recursive (t3-book-theorems-induction-notes
                     lib formula measure substitutions recursive evidence)))
      (t3-book-theorems-with-search
       (step search (t3-book-theorems-prove-term 1000000 search formula recursive 12))
       (t3-book-theorems-with-steps search
           ((base-context (t3-book-theorems-context-branch
                           (t3-book-theorems-new-context search nil) test (not recurs-on-true))))
         (t3-book-theorems-with-search
          (base search (t3-book-theorems-prove-term 1000000 search formula base-context 12))
          (t3-book-theorems-with-steps search
              ((ordinal (library-library-builtin lib 1 variable))
               (cases (if recurs-on-true
                          (proof-proof-cases proof test (car step) (car base))
                        (proof-proof-cases proof test (car base) (car step)))))
            (cons (proof-proof-induct proof ordinal cases formula measure substitutions)
                  search))))))))

(defun t3-book-theorems-theorems-induction
    (search formula variable test recurs-on-true substitutions)
  (t3-book-theorems-search-answer
   (t3-book-theorems-induct-on search formula variable test recurs-on-true substitutions)))

(defun t3-book-theorems-count-driver-uses (term indices candidates)
  (declare (xargs :measure (acl2-count indices)))
  (if (endp indices)
      candidates
    (proof-with-checked-results ((argument (proof-term-at term (car indices))))
      (t3-book-theorems-count-driver-uses
       term (cdr indices)
       (if (proof-compound argument)
           candidates
         (table-put candidates argument (1+ (table-get candidates argument 0))))))))

(defun t3-book-theorems-candidate-counts-with-summaries (terms definitions candidates summaries)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      candidates
    (let ((term (car terms)))
      (if (not (proof-compound term))
          (t3-book-theorems-candidate-counts-with-summaries
           (cdr terms) definitions candidates summaries)
        (proof-with-checked-results ((head (proof-term-at term 0)))
          (let ((definition (assoc-equal head definitions)))
            (proof-with-checked-results
                ((candidates
                  (if definition
                      (proof-with-checked-results
                          ((fields (proof-list-of-length (cdr definition) 2))
                           (indices (t3-book-theorems-definition-drivers
                                     summaries head (car fields) (cadr fields))))
                        (t3-book-theorems-count-driver-uses term indices candidates))
                    candidates)))
              (t3-book-theorems-candidate-counts-with-summaries
               (cdr terms) definitions candidates summaries))))))))

(defun t3-book-theorems-induction-candidate-counts (terms definitions candidates)
  (t3-book-theorems-candidate-counts-with-summaries terms definitions candidates nil))

(defun t3-book-theorems-induction-sort-keys (candidates position)
  (if (endp candidates)
      nil
    (cons (list (- (cdar candidates)) position (caar candidates))
          (t3-book-theorems-induction-sort-keys (cdr candidates) (1+ position)))))

(defun t3-book-theorems-theorems-induction-candidates (search formula)
  (proof-with-checked-results
      ((terms (t3-book-theorems-terms formula))
       (counts (t3-book-theorems-candidate-counts-with-summaries
                terms (proof-proof-definitions (t3-book-theorems-proof search))
                nil (t3-book-theorems-definition-summaries search))))
    (let ((ranked (seq-sorted (t3-book-theorems-induction-sort-keys counts 0))))
      (cond ((consp (cdr ranked)) (list (caddar ranked) (caddr (cadr ranked))))
            (ranked (list (caddar ranked)))
            (t nil)))))

(defun t3-book-theorems-default-schemes (candidates)
  (if (endp candidates)
      nil
    (let ((variable (car candidates)))
      (cons (list variable (list *proof-consp* variable) t
                  (list (list (list variable (list *library-cdr* variable)))))
            (t3-book-theorems-default-schemes (cdr candidates))))))

(defun t3-book-theorems-substitute-actuals (actuals bindings)
  (if (endp actuals)
      nil
    (proof-with-checked-results
        ((value (proof-subst (car actuals) bindings))
         (rest (t3-book-theorems-substitute-actuals (cdr actuals) bindings)))
      (cons value rest))))

(defun t3-book-theorems-substitute-calls (calls bindings)
  (if (endp calls)
      nil
    (proof-with-checked-results
        ((values (t3-book-theorems-substitute-actuals
                  (termination-call-actuals (car calls)) bindings))
         (rest (t3-book-theorems-substitute-calls (cdr calls) bindings)))
      (cons values rest))))

(defun t3-book-theorems-changed-arguments (arguments actuals)
  (cond ((or (endp arguments) (endp actuals)) nil)
        ((equal (car arguments) (car actuals))
         (t3-book-theorems-changed-arguments (cdr arguments) (cdr actuals)))
        (t (cons (list (car arguments) (car actuals))
                 (t3-book-theorems-changed-arguments (cdr arguments) (cdr actuals))))))

(defun t3-book-theorems-substitution-lists (arguments actuals)
  (declare (xargs :measure (acl2-count actuals)))
  (if (endp actuals)
      nil
    (cons (t3-book-theorems-changed-arguments arguments (car actuals))
          (t3-book-theorems-substitution-lists arguments (cdr actuals)))))

(defun t3-book-theorems-count-argument (argument args)
  (if (endp args)
      0
    (+ (if (equal argument (car args)) 1 0)
       (t3-book-theorems-count-argument argument (cdr args)))))

(defun t3-book-theorems-distinct-binding-arguments-p (pairs arguments)
  (or (endp pairs)
      (and (not (proof-compound (caar pairs)))
           (equal (t3-book-theorems-count-argument (caar pairs) arguments) 1)
           (t3-book-theorems-distinct-binding-arguments-p (cdr pairs) arguments))))

(defun t3-book-theorems-distinct-substitutions-p (substitutions arguments)
  (or (endp substitutions)
      (and (t3-book-theorems-distinct-binding-arguments-p (car substitutions) arguments)
           (t3-book-theorems-distinct-substitutions-p (cdr substitutions) arguments))))

(defund t3-book-theorems-induction-data-with-summaries (term definitions summaries)
  (if (not (proof-compound term))
      nil
    (proof-with-checked-results ((function (proof-term-at term 0)))
      (let ((definition (assoc-equal function definitions)))
        (and definition
             (proof-with-checked-results
                 ((fields (proof-list-of-length (cdr definition) 2))
                  (formals (car fields))
                  (calls (t3-book-theorems-definition-recurrences
                          summaries function formals (cadr fields))))
               (if (or (endp calls) (> (len calls) 3))
                   nil
                 (let ((arguments (cdr term)))
                   (proof-with-checked-results
                       ((bindings (t3-book-theorems-bindings-from-pairs (seq-zip formals arguments) nil))
                        (actuals (t3-book-theorems-substitute-calls calls bindings)))
                     (let ((substitutions
                            (proof-unique (t3-book-theorems-substitution-lists arguments actuals))))
                       (and (t3-book-theorems-distinct-substitutions-p substitutions arguments)
                            (list arguments actuals substitutions))))))))))))

(defund t3-book-theorems-induction-scheme-data (term definitions)
  (t3-book-theorems-induction-data-with-summaries term definitions nil))

(defun t3-book-theorems-recursive-argument-values (actuals index)
  (if (endp actuals)
      nil
    (proof-with-checked-results
        ((first (proof-term-at (car actuals) index))
         (rest (t3-book-theorems-recursive-argument-values (cdr actuals) index)))
      (cons first rest))))

(defun t3-book-theorems-all-selector-paths-p (smaller variable)
  (if (endp smaller)
      t
    (proof-with-checked-results ((path (t3-size-selector-path (car smaller) variable)))
      (and path (not (eq path :none))
           (t3-book-theorems-all-selector-paths-p (cdr smaller) variable)))))

(defun t3-book-theorems-all-predecessors-p (smaller variable)
  (or (endp smaller)
      (and (member-equal (car smaller) (list (list *proof-plus* *proof-neg-one* variable)
                                            (list *proof-plus* variable *proof-neg-one*)))
           (t3-book-theorems-all-predecessors-p (cdr smaller) variable))))

(defund t3-book-theorems-argument-scheme (variable actuals index substitutions)
  (if (proof-compound variable)
      nil
    (proof-with-checked-results
        ((smaller (t3-book-theorems-recursive-argument-values actuals index))
         (selectors (t3-book-theorems-all-selector-paths-p smaller variable)))
      (cond (selectors (list variable (list *proof-consp* variable) t substitutions))
            ((t3-book-theorems-all-predecessors-p smaller variable)
             (list variable (list *t3-logic-zp* variable) nil substitutions))
            (t nil)))))

; Save the unused arguments of the current call and the unused formula terms
; after selecting a scheme so induction can stop at the first success.
(defun t3-book-theorems-next-scheme-with-summaries
    (n terms args index actuals substitutions seen definitions summaries)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "Fuel" "t3-book-theorems-theorems-induction-schemes"))
   ((consp args)
    (proof-with-checked-results
        ((scheme (t3-book-theorems-argument-scheme (car args) actuals index substitutions)))
      (if (and scheme (not (member-equal scheme seen)))
          (list scheme (list terms (cdr args) (1+ index) actuals substitutions (cons scheme seen)))
        (t3-book-theorems-next-scheme-with-summaries
         (1- n) terms (cdr args) (1+ index) actuals substitutions seen definitions summaries))))
   ((consp terms)
    (proof-with-checked-results
        ((data (t3-book-theorems-induction-data-with-summaries (car terms) definitions summaries)))
      (t3-book-theorems-next-scheme-with-summaries
       (1- n) (cdr terms) (car data) 0 (cadr data) (caddr data) seen definitions summaries)))
   (t nil)))

(defun t3-book-theorems-next-structural-scheme
    (n terms args index actuals substitutions seen definitions)
  (t3-book-theorems-next-scheme-with-summaries
   n terms args index actuals substitutions seen definitions nil))

(defund t3-book-theorems-scheme-from-cursor (cursor definitions summaries)
  (t3-book-theorems-next-scheme-with-summaries
   1000000 (nth 0 cursor) (nth 1 cursor) (nth 2 cursor) (nth 3 cursor)
   (nth 4 cursor) (nth 5 cursor) definitions summaries))

(defund t3-book-theorems-next-from-cursor (cursor definitions)
  (t3-book-theorems-scheme-from-cursor cursor definitions nil))

(defun t3-book-theorems-collect-schemes-with-summaries (n cursor definitions summaries)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t3-book-theorems-theorems-induction-schemes")
    (proof-with-checked-results ((next (t3-book-theorems-scheme-from-cursor cursor definitions summaries)))
      (and next
           (proof-with-checked-results
               ((rest (t3-book-theorems-collect-schemes-with-summaries
                       (1- n) (cadr next) definitions summaries)))
             (cons (car next) rest))))))

(defun t3-book-theorems-collect-structural-schemes (n cursor definitions)
  (t3-book-theorems-collect-schemes-with-summaries n cursor definitions nil))

(defun t3-book-theorems-theorems-induction-schemes (search formula)
  (proof-with-checked-results
      ((candidates (t3-book-theorems-theorems-induction-candidates search formula))
       (terms (t3-book-theorems-terms formula))
       (defaults (t3-book-theorems-default-schemes candidates))
       (structural (t3-book-theorems-collect-schemes-with-summaries
                    1000000 (list terms nil 0 nil nil defaults)
                    (proof-proof-definitions (t3-book-theorems-proof search))
                    (t3-book-theorems-definition-summaries search))))
    (append defaults structural)))

(defun t3-book-theorems-unsupported-p (value)
  (and (failure-p value) (equal (cadr value) "Unsupported")))

(defund t3-book-theorems-next-induction-attempt (search formula defaults remaining cursor)
  (if remaining
      (list (car remaining) (cdr remaining) cursor)
    (proof-with-checked-results
        ((cursor (if (eq cursor :none)
                     (proof-with-checked-results ((terms (t3-book-theorems-terms formula)))
                       (list terms nil 0 nil nil defaults))
                   cursor))
         (next (t3-book-theorems-scheme-from-cursor
                cursor (proof-proof-definitions (t3-book-theorems-proof search))
                (t3-book-theorems-definition-summaries search))))
      (and next (list (car next) nil (cadr next))))))

(defun t3-book-theorems-try-induction-schemes
    (attempts search formula allowance direct defaults remaining cursor)
  (declare (xargs :measure (nfix attempts)))
  (if (zp attempts)
      (cons direct search)
    (t3-book-theorems-with-steps search
        ((next (t3-book-theorems-next-induction-attempt search formula defaults remaining cursor)))
      (if (not next)
          (cons direct search)
        (let* ((scheme (car next))
               (search (t3-book-theorems-theorems-with-fuel search (+ allowance 700)))
               (result (t3-book-theorems-induct-on
                        search formula (car scheme) (cadr scheme) (caddr scheme) (cadddr scheme))))
          (if (t3-book-theorems-unsupported-p (car result))
              (t3-book-theorems-try-induction-schemes
               (1- attempts) (cdr result) formula allowance direct defaults (cadr next) (caddr next))
            result))))))

(defun t3-book-theorems-prove-formula (search formula allowance induct)
  (let ((search (t3-book-theorems-theorems-with-fuel search allowance)))
    (t3-book-theorems-with-search
     (known search (t3-book-theorems-quick-result search formula (t3-book-theorems-new-context search nil) 0))
     (if known
         (cons known search)
       (let* ((attempt (t3-book-theorems-prove-term
                        1000000 search formula (t3-book-theorems-new-context search nil) 12))
              (direct (car attempt))
              (search (cdr attempt)))
         (cond
          ((not (failure-p direct)) (cons (car direct) search))
          ((and induct (t3-book-theorems-unsupported-p direct))
           (t3-book-theorems-with-steps search
               ((candidates (t3-book-theorems-theorems-induction-candidates search formula)))
             (let ((defaults (t3-book-theorems-default-schemes candidates)))
               (t3-book-theorems-try-induction-schemes
                4 search formula allowance direct defaults defaults :none))))
          (t attempt)))))))

(defun t3-book-theorems-theorems-formula (search formula allowance induct)
  (t3-book-theorems-search-answer
   (t3-book-theorems-prove-formula search formula allowance induct)))

(defund t3-book-theorems-guard-simplification (book value evidence)
  (t3-book-values-book-proofs-normalize book value evidence *t3-book-spines-guards*))

(defund t3-book-theorems-constructor-normalization (n book value evidence)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t3-book-theorems-constructor-normalization")
    (let ((proof (library-library-proof (t3-book-values-book-proofs-library book))))
      (proof-with-checked-results
          ((equation (t3-book-theorems-guard-simplification book value evidence))
           (current (if equation (proof-rewritten-term equation) value))
           (equation
            (if (not (proof-is-call current *proof-if*))
                equation
              (proof-with-checked-results
                  ((yes (proof-term-at current 2))
                   (branch (t3-book-theorems-constructor-normalization (1- n) book yes evidence))
                   (equation
                    (t3-book-spines-constructor-form-rewrite proof value equation branch 2))
                   (no (proof-term-at current 3))
                   (branch (t3-book-theorems-constructor-normalization (1- n) book no evidence)))
                (t3-book-spines-constructor-form-rewrite proof value equation branch 3)))))
        (and equation (proof-proof-tidy proof equation))))))

(defun t3-book-theorems-theorems-guarded-equation-forms (value book evidence)
  (let ((proof (library-library-proof (t3-book-values-book-proofs-library book))))
    (proof-with-checked-results
        ((constructor (t3-book-theorems-constructor-normalization 1000000 book value evidence))
         (first (or constructor (proof-proof-reflexive proof value)))
         (current (proof-rewritten-term first))
         (name (t3-book-theorems-head current)))
      (let ((definition (assoc-equal name (proof-proof-definitions proof))))
        (proof-with-checked-results
            ((cost (and definition (t3-book-theorems-term-cost (caddr definition) 100))))
          (if (and definition (<= cost 100))
              (proof-with-checked-results
                  ((opened (proof-proof-unfold proof current))
                   (body (proof-rewritten-term opened))
                   (constructor (t3-book-theorems-constructor-normalization 1000000 book body evidence))
                   (shallow (proof-proof-chain proof opened (list constructor)))
                   (next (proof-proof-chain proof first (list shallow))))
                (list first next))
            (list first)))))))

(defun t3-book-theorems-equation-with-result (steps value)
  (if (endp steps)
      nil
    (proof-with-checked-results ((right (proof-rewritten-term (car steps))))
      (if (equal value right)
          (car steps)
        (t3-book-theorems-equation-with-result (cdr steps) value)))))

(defun t3-book-theorems-join-constructor-forms (lib left right guarded formula)
  (declare (xargs :measure (acl2-count left)))
  (if (endp left)
      nil
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((value (proof-rewritten-term (car left)))
           (match (t3-book-theorems-equation-with-result right value)))
        (if match
            (proof-with-checked-results
                ((reverse (proof-proof-symmetric proof match))
                 (equality (proof-proof-chain proof (car left) (list reverse))))
              (if guarded (t3-book-lemmas-implication lib formula equality) equality))
          (t3-book-theorems-join-constructor-forms lib (cdr left) right guarded formula))))))

(defun t3-book-theorems-guarded-forms-of-sides (sides book evidence)
  (if (endp sides)
      nil
    (proof-with-checked-results
        ((first (t3-book-theorems-theorems-guarded-equation-forms (car sides) book evidence))
         (rest (t3-book-theorems-guarded-forms-of-sides (cdr sides) book evidence)))
      (cons first rest))))

(defun t3-book-theorems-theorems-guarded-equation (search formula)
  (let* ((lib (t3-book-theorems-library search))
         (proof (library-library-proof lib))
         (guarded (proof-is-call formula *library-implies*)))
    (proof-with-checked-results ((goal (if guarded (proof-term-at formula 2) formula)))
      (if (not (proof-is-call goal *proof-equal*))
          nil
        (proof-with-checked-results ((cost (t3-book-theorems-term-cost goal 100)))
          (if (> cost 100)
              nil
            (proof-with-checked-results
                ((context (if guarded
                              (proof-with-checked-results
                                  ((test (proof-term-at formula 1))
                                   (assumed (proof-proof-assume proof test t)))
                                (t3-book-theorems-context-note
                                 (t3-book-theorems-new-context search nil) assumed))
                            (t3-book-theorems-new-context search nil)))
                 (evidence (table-values (t3-book-theorems-context-facts context)))
                 (sides (t3-book-theorems-guarded-forms-of-sides
                         (seq-slice (cdr goal) 0 3) (t3-book-theorems-theorems-lib search) evidence))
                 (forms (proof-list-of-length sides 2)))
              (t3-book-theorems-join-constructor-forms lib (car forms) (cadr forms) guarded formula))))))))

(defun t3-book-theorems-boolean-value-term (formula)
  (if (not (proof-is-call formula *proof-if*))
      nil
    (proof-with-checked-results
        ((true-case (proof-term-at formula 1))
         (yes (proof-term-at formula 2)))
      (if (or (not (equal true-case yes)) (not (proof-is-call true-case *proof-equal*)))
          nil
        (proof-with-checked-results ((right (proof-term-at true-case 2)))
          (if (not (equal right *proof-true*))
              nil
            (proof-with-checked-results ((otherwise (proof-term-at formula 3)))
              (and (equal otherwise (proof-eq (cadr true-case) *proof-false*))
                   (list (cadr true-case))))))))))

(defun t3-book-theorems-prove-boolean-result (search formula)
  (t3-book-theorems-with-steps search ((value (t3-book-theorems-boolean-value-term formula)))
    (if (not value)
        (cons nil search)
      (let ((search (t3-book-theorems-theorems-with-fuel search 1100))
            (value (car value)))
        (t3-book-theorems-with-search
         (step search (t3-book-theorems-result-proof search (list *t3-book-lemmas-booleanp* value)
                       (t3-book-theorems-new-context search nil) nil))
         (if (not step)
             (cons nil search)
           (let* ((lib (t3-book-theorems-library search))
                  (proof (library-library-proof lib)))
             (t3-book-theorems-with-steps search
                 ((equivalent (library-library-axiom
                               lib "BOOLEANP-COMPOUND-RECOGNIZER" (list value)))
                  (rewritten (proof-proof-rewrite proof step equivalent '(1))))
               (cons (proof-proof-tidy proof rewritten) search)))))))))

(defun t3-book-theorems-theorems-boolean-result (search formula)
  (t3-book-theorems-search-answer (t3-book-theorems-prove-boolean-result search formula)))

(defun t3-book-theorems-constructor-head-p (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results ((head (t3-book-theorems-head (car terms))))
      (or (member-equal head (list *proof-consp* *library-car* *library-cdr* *library-count*))
          (t3-book-theorems-constructor-head-p (cdr terms))))))

(defun t3-book-theorems-prove-constructor (search formula)
  (t3-book-theorems-with-steps search ((cost (t3-book-theorems-term-cost formula 52)))
    (if (> cost 52)
        (cons nil search)
      (t3-book-theorems-with-steps search
          ((terms (t3-book-theorems-terms formula))
           (constructor (t3-book-theorems-constructor-head-p terms)))
        (if (not constructor)
            (cons nil search)
          (let* ((search (t3-book-theorems-theorems-with-constructor-cases search t))
                 (search (t3-book-theorems-theorems-with-fuel search 4600))
                 (attempt (t3-book-theorems-prove-term
                           1000000 search formula (t3-book-theorems-new-context search nil) 8))
                 (result (car attempt))
                 (search (t3-book-theorems-theorems-with-constructor-cases (cdr attempt) nil)))
            (cons (if (failure-p result) result (car result)) search)))))))

(defun t3-book-theorems-theorems-prove-constructor-cases (search formula)
  (t3-book-theorems-search-answer (t3-book-theorems-prove-constructor search formula)))

(defund t3-book-theorems-shape-solve (target evidence search)
  (t3-book-theorems-with-steps search
      ((context (t3-book-theorems-context-note-steps
                 1000000 (t3-book-theorems-new-context search nil) evidence)))
    (let ((search (t3-book-theorems-theorems-with-fuel search 600)))
      (t3-book-theorems-with-steps search
          ((otherwise (and (proof-is-call target *proof-if*) (proof-term-at target 3))))
        (t3-book-theorems-with-search
         (result search
          (if (equal otherwise *proof-false*)
              (t3-book-theorems-prove-conjunct 1000000 search target context 13)
            (t3-book-theorems-prove-term 1000000 search target context 12)))
         (cons (car result) search))))))

(defund t3-book-theorems-shape-earlier-proof (target search)
  (let ((search (t3-book-theorems-theorems-with-fuel search 220)))
    (t3-book-theorems-quick-result search target (t3-book-theorems-new-context search nil) 0)))

(defund t3-book-theorems-shape-rewrite-proof (target search)
  (let ((search (t3-book-theorems-theorems-with-fuel search 160)))
    (t3-book-theorems-rule-result search target (t3-book-theorems-new-context search nil) 0 t)))

(defun t3-book-theorems-theorems-shape-proof-solve (target evidence search)
  (t3-book-theorems-search-answer (t3-book-theorems-shape-solve target evidence search)))

(defun t3-book-theorems-theorems-shape-proof-earlier (target search)
  (t3-book-theorems-search-answer (t3-book-theorems-shape-earlier-proof target search)))

(defun t3-book-theorems-theorems-shape-proof-by-equality (target search)
  (t3-book-theorems-search-answer (t3-book-theorems-shape-rewrite-proof target search)))

(defund t3-book-theorems-spines-attempt (lib goal mapped replies)
  (if mapped
      (t3-book-spines-mapped-list lib goal replies)
    (t3-book-spines-commuting-list-fix lib goal replies)))

(defun t3-book-theorems-shape-spines (n search goal mapped replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons '(:failure "Fuel" "t3-book-theorems-shape-spines") search)
    (let ((result (t3-book-theorems-spines-attempt
                   (t3-book-theorems-library search) goal mapped replies)))
      (if (not (t3-book-spines-callback-p result))
          (cons result search)
        (let ((args (t3-book-spines-callback-args result)))
          (t3-book-theorems-with-search
           (reply search
            (if (eq (t3-book-spines-callback-kind result) :solve)
                (t3-book-theorems-shape-solve (car args) (cadr args) search)
              (t3-book-theorems-shape-rewrite-proof (car args) search)))
           (t3-book-theorems-shape-spines
            (1- n) search goal mapped (append replies (list reply)))))))))

(defund t3-book-theorems-shape-after-removal (search goal)
  (let* ((lib (t3-book-theorems-library search))
         (result (t3-book-occurrences-after-removal lib goal nil)))
    (if (not (t3-book-occurrences-solve-request-p result))
        (cons result search)
      (let ((target (t3-book-occurrences-solve-request-goal result)))
        (t3-book-theorems-with-search
         (reply search (t3-book-theorems-shape-earlier-proof target search))
         (cons (t3-book-occurrences-after-removal lib goal (list (cons target reply)))
               search))))))

(defun t3-book-theorems-string-results (search earlier)
  (t3-book-strings-string-results-init (t3-book-theorems-library search) earlier))

(defund t3-book-theorems-string-action (search value tests trail)
  (t3-book-strings-string-action
   (t3-book-theorems-string-results search nil) value tests trail))

(defund t3-book-theorems-string-call-action (search value target trail)
  (t3-book-strings-call-action
   (t3-book-theorems-string-results search (list (cons target nil))) value target trail))

; Each returned value receives its own earlier-proof invocation. The allowance
; follows evaluation order through both branches even when a target occurs twice.
(mutual-recursion
 (defun t3-book-theorems-string-value (n search value tests trail)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-string-value") search)
     (let ((action (t3-book-theorems-string-action search value tests trail)))
       (if (not (t3-book-strings-earlier-request-p action))
           (cons action search)
         (let ((target (cadr action)))
           (t3-book-theorems-with-search
            (earlier search (t3-book-theorems-shape-earlier-proof target search))
            (if earlier
                (cons earlier search)
              (t3-book-theorems-string-dispatch
               (1- n) search value tests trail
               (t3-book-theorems-string-call-action search value target trail)))))))))
 (defun t3-book-theorems-string-dispatch (n search value tests trail action)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-string-value") search)
     (let ((lib (t3-book-theorems-library search)))
       (case (car action)
         (:project
          (t3-book-theorems-with-steps search
              ((projection (t3-book-strings-projection
                            (t3-book-theorems-string-results search nil) value trail)))
            (let ((template (cadr projection)))
              (t3-book-theorems-with-search
               (step search (t3-book-theorems-string-visit
                             (1- n) search (car projection) template tests
                             (caddr projection) (cadddr projection)))
               (cons (t3-book-strings-rewrite-branch
                      (library-library-proof lib) step (nth 4 projection) template)
                     search)))))
         (:cases
          (t3-book-theorems-with-search
           (step search (t3-book-theorems-string-visit
                         (1- n) search (cadr action) (t3-book-strings-string-template)
                         tests (caddr action) nil))
           (cons (if (cadddr action)
                     (library-library-transport-argument lib step (cadddr action) 1)
                   step)
                 search)))
         (otherwise (cons action search))))))
 (defun t3-book-theorems-string-visit (n search value template tests trail index)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-string-value") search)
     (let* ((proof (t3-book-theorems-proof search))
            (branch (t3-book-strings-branch proof value)))
       (case (car branch)
         (:if
          (let ((test (cadr branch)))
            (t3-book-theorems-with-search
             (yes search (t3-book-theorems-string-visit
                          (1- n) search (caddr branch) template
                          (append tests (list (list test t))) trail index))
             (t3-book-theorems-with-search
              (no search (t3-book-theorems-string-visit
                           (1- n) search (cadddr branch) template
                           (append tests (list (list test nil))) trail index))
              (cons (proof-by-value-join proof value template yes no) search)))))
         (:opened
          (t3-book-theorems-with-search
           (step search (t3-book-theorems-string-visit
                         (1- n) search (cadr branch) template tests trail index))
           (cons (t3-book-strings-rewrite-branch proof step (caddr branch) template) search)))
         (:leaf
          (t3-book-theorems-with-search
           (step search (if (integerp index)
                            (t3-book-theorems-string-project-leaf
                             (1- n) search value tests trail index)
                          (t3-book-theorems-string-value (1- n) search value tests trail)))
           (cons (t3-logic-by-value-check-leaf step value template) search)))
         (otherwise (cons branch search))))))
 (defun t3-book-theorems-string-project-leaf (n search term tests trail index)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "Fuel" "t3-book-theorems-string-value") search)
     (t3-book-theorems-with-steps search
         ((selected (t3-book-strings-projected-leaf-selection
                     (t3-book-theorems-string-results search nil) index term)))
       (t3-book-theorems-with-search
        (step search (t3-book-theorems-string-value (1- n) search (car selected) tests trail))
        (cons (library-library-transport-argument
               (t3-book-theorems-library search) step (cdr selected) 1)
              search))))))

(defund t3-book-theorems-shape-string-result (search formula)
  (cond
   ((proof-is-call formula *library-implies*)
    (t3-book-theorems-with-steps search ((goal (proof-term-at formula 2)))
      (if (not (proof-is-call goal *t3-list-bounds-stringp*))
          (cons nil search)
        (t3-book-theorems-with-steps search ((value (proof-term-at goal 1)))
          (t3-book-theorems-with-search
           (step search (t3-book-theorems-string-value
                         1000000 search value (list (list (cadr formula) t)) nil))
           (cons (t3-book-lemmas-implication (t3-book-theorems-library search) formula step)
                 search))))))
   ((proof-is-call formula *t3-list-bounds-stringp*)
    (t3-book-theorems-with-steps search ((value (proof-term-at formula 1)))
      (t3-book-theorems-string-value 1000000 search value nil nil)))
   (t (cons nil search))))

(defconst *t3-book-theorems-shape-recipes*
  '(:projected-list :preserving-elements :rendered-tree :event-cons :mapped-list
    :fold-over-list-fix :commuting-list-fix :removal-over-list-fix :absence :different-key
    :after-removal :equality-relation :guarded-equation :boolean-result :string-result))

(defun t3-book-theorems-shape-accept-library (search result)
  (if (failure-p result)
      (cons result search)
    (cons (car result) (t3-book-theorems-with-library search (cdr result)))))

(defund t3-book-theorems-try-shape-recipe (search goal recipe)
  (let ((lib (t3-book-theorems-library search)))
    (case recipe
      (:projected-list (cons (t3-book-projections-projected-list lib goal) search))
      (:preserving-elements
       (t3-book-theorems-shape-accept-library search (t3-book-character-lists-preserving-elements lib goal)))
      (:rendered-tree (cons (t3-book-tree-results-rendered-tree lib goal) search))
      (:event-cons
       (t3-book-theorems-shape-accept-library search (t3-book-tree-results-event-cons lib goal)))
      (:mapped-list (t3-book-theorems-shape-spines 1000000 search goal t nil))
      (:fold-over-list-fix (cons (t3-book-spines-fold-over-list-fix lib goal) search))
      (:commuting-list-fix (t3-book-theorems-shape-spines 1000000 search goal nil nil))
      (:removal-over-list-fix (cons (t3-book-spines-removal-over-list-fix lib goal) search))
      (:absence (cons (t3-book-spines-absence lib goal) search))
      (:different-key (cons (t3-book-spines-different-key lib goal) search))
      (:after-removal (t3-book-theorems-shape-after-removal search goal))
      (:equality-relation (cons (t3-book-equivalence-equality-relation lib goal) search))
      (:guarded-equation (cons (t3-book-theorems-theorems-guarded-equation search goal) search))
      (:boolean-result (t3-book-theorems-prove-boolean-result search goal))
      (otherwise (t3-book-theorems-shape-string-result search goal)))))

(defun t3-book-theorems-try-shape-recipes (search goal recipes)
  (declare (xargs :measure (acl2-count recipes)))
  (if (endp recipes)
      (cons nil search)
    (t3-book-theorems-with-search
     (step search (t3-book-theorems-try-shape-recipe search goal (car recipes)))
     (if step
         (cons step search)
       (t3-book-theorems-try-shape-recipes search goal (cdr recipes))))))

(defun t3-book-theorems-shape-reduced-goal (search goal opened)
  (t3-book-theorems-with-search
   (step search (t3-book-theorems-try-shape-recipes search goal *t3-book-theorems-shape-recipes*))
   (if step
       (cons step search)
     (let* ((attempt (if opened (t3-book-theorems-prove-formula search goal 700 t) (cons nil search)))
            (result (car attempt))
            (search (cdr attempt)))
       (cond ((and result (not (t3-book-theorems-unsupported-p result))) attempt)
             (t (t3-book-theorems-prove-constructor search goal)))))))

(defun t3-book-theorems-shape-search (search formula)
  (t3-book-theorems-with-steps search
      ((head (and (proof-compound formula) (proof-term-at formula 0)))
       (opened (and (proof-compound formula) (proof-compound head)
                    (proof-proof-beta (t3-book-theorems-proof search) formula)))
       (goal (if opened (proof-rewritten-term opened) formula)))
    (let* ((attempt (t3-book-theorems-shape-reduced-goal search goal opened))
           (step (car attempt))
           (search (cdr attempt)))
      (cond ((t3-book-theorems-unsupported-p step) (cons nil search))
            ((failure-p step) attempt)
            ((and step opened)
             (cons (proof-proof-transport (t3-book-theorems-proof search) step opened) search))
            (t attempt)))))

(defun t3-book-theorems-theorems-shape-proof (search formula)
  (t3-book-theorems-search-answer (t3-book-theorems-shape-search search formula)))

(defun t3-book-theorems-conclude (search formula)
  (let ((search (t3-book-theorems-theorems-with-fuel search 400)))
    (t3-book-theorems-with-steps search
        ((concluded (or (t3-book-lemmas-implies-proper-list
                         (t3-book-theorems-library search) formula nil)
                        (t3-book-theorems-theorems-definition-equation search formula))))
      (if concluded
          (cons concluded search)
        (t3-book-theorems-with-search
         (alias search (t3-book-theorems-alias-consequence-loop
                        4 search formula (t3-book-theorems-new-context search nil) nil))
         (if alias
             (cons alias search)
           (let* ((attempt (t3-book-theorems-prove-formula search formula 1100 t))
                  (initial (car attempt)))
             (if (not (t3-book-theorems-unsupported-p initial))
                 attempt
               (t3-book-theorems-with-search
                (shape search (t3-book-theorems-shape-search (cdr attempt) formula))
                (cons (or shape initial) search))))))))))

(defun t3-book-theorems-theorems-theorem (search name formula)
  (t3-book-theorems-search-answer
   (t3-book-theorems-with-search
    (concluded search (t3-book-theorems-conclude search formula))
    (cons (proof-proof-entry "theorem" name (list name) (list concluded)) search))))
