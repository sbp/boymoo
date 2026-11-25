(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defmacro proof-search-let (bindings body)
  (if (endp bindings)
      body
    (let ((binding (car bindings)))
      `(let (,binding)
         (if (failure-p ,(car binding))
             ,(car binding)
           (proof-search-let ,(cdr bindings) ,body))))))

(defun proof-search-present-p (value)
  (and value (not (equal value 0)) (not (equal value ""))))

(defun proof-search-zip-bindings (names values bindings)
  (if (and (consp names) (consp values))
      (proof-search-zip-bindings
       (cdr names) (cdr values)
       (table-put bindings (car names) (car values)))
    bindings))

(defun proof-search-head (term)
  (cond ((not (proof-compound term)) nil)
        ((endp term) '(:failure "failure" ""))
        ((proof-compound (car term)) nil)
        (t (car term))))

(defun proof-search-key (term)
  (proof-search-let ((operator (proof-search-head term)))
    (if (member-equal operator
                      (list *proof-equal* *proof-not* *library-implies*))
        (if (consp (cdr term))
            (proof-search-let ((argument-head (proof-search-head (cadr term))))
              (list operator argument-head))
          '(:failure "failure" ""))
      (list operator nil))))

(defun proof-search-conclusion-loop (fuel term)
  (declare (xargs :measure (nfix fuel)))
  (cond
    ((zp fuel) '(:failure "fuel" "proof-search-conclusion-loop"))
    ((not (proof-compound term)) term)
    ((endp term) '(:failure "failure" ""))
    ((proof-compound (car term))
     (let ((operator (car term)))
       (if (equal (len operator) 3)
           (proof-search-let
             ((body (proof-subst
                     (caddr operator)
                     (proof-search-zip-bindings (cadr operator) (cdr term) nil))))
             (proof-search-conclusion-loop (1- fuel) body))
         *terms-invalid-proof-arity*)))
    ((proof-is-call term *library-implies*)
     (if (consp (cddr term))
         (proof-search-conclusion-loop (1- fuel) (caddr term))
       '(:failure "failure" "")))
    (t term)))

(defun proof-search-conclusion (term)
  (proof-search-conclusion-loop 1000000 term))

(defun proof-search-make-rule (name pattern expose)
  (list :rule name pattern expose))

(defun proof-search-rule-name (rule)
  (cadr rule))

(defun proof-search-rule-pattern (rule)
  (caddr rule))

(defun proof-search-rule-expose (rule)
  (cadddr rule))

(mutual-recursion
 (defun proof-search-can-shorten (term size)
   (declare (xargs :measure (acl2-count term)))
   (let ((actual (book-logic-term-size term size)))
     (cond ((failure-p actual) actual)
           ((< actual size) t)
           ((proof-is-call term *proof-if*)
            (proof-search-can-shorten-branches (cddr term) size))
           (t nil))))
 (defun proof-search-can-shorten-branches (branches size)
   (declare (xargs :measure (acl2-count branches)))
   (and (consp branches)
        (or (proof-search-can-shorten (car branches) size)
            (proof-search-can-shorten-branches (cdr branches) size)))))

(defun proof-search-make-fact-index (lib rules equations)
  (list :fact-index lib rules equations))

(defun proof-search-fact-index-lib (index)
  (cadr index))

(defun proof-search-fact-index-rules (index)
  (caddr index))

(defun proof-search-fact-index-equations (index)
  (cadddr index))

(defun proof-search-fact-index-with-lib (index lib)
  (proof-search-make-fact-index lib
                               (proof-search-fact-index-rules index)
                               (proof-search-fact-index-equations index)))

(defun proof-search-index-rule (rules qualified rule)
  (table-put rules qualified
               (append (cdr (assoc-equal qualified rules)) (list rule))))

(defun proof-search-index-formula (rules name formula exposed)
  (proof-search-let ((operator (proof-search-head formula)))
    (if (or operator (equal formula exposed))
        (proof-search-let ((qualified (proof-search-key formula)))
          (proof-search-index-rule
           rules qualified (proof-search-make-rule name formula nil)))
      rules)))

(defun proof-search-index-conclusion (rules name formula exposed)
  (if (equal exposed formula)
      rules
    (proof-search-let ((operator (proof-search-head exposed)))
      (if operator
          (proof-search-let ((qualified (proof-search-key exposed)))
            (proof-search-index-rule
             rules qualified (proof-search-make-rule name exposed t)))
        rules))))

(defun proof-search-index-equation (equations definitions name formula exposed)
  (if (or (assoc-equal name definitions)
          (not (proof-is-call exposed *proof-equal*)))
      equations
    (if (endp (cdr exposed))
        '(:failure "failure" "")
      (proof-search-let ((operator (proof-search-head (cadr exposed))))
        (cond
          ((not (proof-search-present-p operator)) equations)
          ((not (equal (len (cdr exposed)) 2))
           *terms-invalid-proof-arity*)
          (t
           (proof-search-let
             ((size (book-logic-term-size (cadr exposed) 120))
              (shorter (proof-search-can-shorten (caddr exposed) size)))
             (if shorter
                 (proof-search-let
                   ((qualified (proof-search-key (cadr exposed))))
                   (proof-search-index-rule
                    equations qualified
                    (proof-search-make-rule name exposed
                                            (not (equal exposed formula)))))
               equations))))))))

(defun proof-search-fact-index-add (index name)
  (let* ((lib (proof-search-fact-index-lib index))
         (proof (library-library-proof lib))
         (entry (assoc-equal name (proof-proof-facts proof))))
    (cond
      ((not entry) '(:failure "failure" ""))
      ((endp (cdr entry)) '(:failure "failure" ""))
      (t
       (let ((formula (cadr entry)))
         (proof-search-let
           ((exposed (proof-search-conclusion formula))
            (rules (proof-search-index-formula
                    (proof-search-fact-index-rules index) name formula exposed))
            (rules (proof-search-index-conclusion rules name formula exposed))
            (equations (proof-search-index-equation
                        (proof-search-fact-index-equations index)
                        (proof-proof-definitions proof) name formula exposed)))
           (proof-search-make-fact-index lib rules equations)))))))

(defun proof-search-index-facts (facts index)
  (if (endp facts)
      index
    (proof-search-let
      ((updated (proof-search-fact-index-add index (caar facts))))
      (proof-search-index-facts (cdr facts) updated))))

(defun proof-search-fact-index-init (lib)
  (proof-search-index-facts (proof-proof-facts (library-library-proof lib))
                            (proof-search-make-fact-index lib nil nil)))

(defun proof-search-fact-index-candidates (index goal)
  (proof-search-let ((qualified (proof-search-key goal)))
    (let* ((rules (proof-search-fact-index-rules index))
           (specific (reverse (cdr (assoc-equal qualified rules)))))
      (if (cadr qualified)
          (append specific
                  (reverse (cdr (assoc-equal (list (car qualified) nil)
                                             rules))))
        specific))))

(defun proof-search-request-p (value)
  (and (consp value) (eq (car value) :request)))

(defun proof-search-interrupted-p (value)
  (or (failure-p value) (proof-search-request-p value)))

(defun proof-search-condition (term condition)
  (if (eq condition :none)
      *terms-unproved*
    (let ((answer (assoc-equal term condition)))
      (if answer (cdr answer) (list :request term)))))

(defun proof-search-expose-fact (fuel proof step condition)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      '(:failure "fuel" "proof-search-expose-fact")
    (proof-search-let ((formula (proof-step-first step)))
      (cond
        ((not (proof-compound formula)) step)
        ((endp formula) '(:failure "failure" ""))
        ((proof-compound (car formula))
         (proof-search-let
           ((beta (proof-proof-beta proof formula))
            (rewritten (proof-proof-rewrite proof step beta (list 1)))
            (tidied (proof-proof-tidy proof rewritten)))
           (proof-search-expose-fact (1- fuel) proof tidied condition)))
        ((proof-is-call formula *library-implies*)
         (if (eq condition :none)
             *terms-unproved*
           (if (endp (cdr formula))
               '(:failure "failure" "")
             (let ((premise (proof-search-condition (cadr formula) condition)))
               (if (proof-search-interrupted-p premise)
                   premise
                 (proof-search-let
                   ((conclusion (proof-proof-modus-ponens proof step premise)))
                   (proof-search-expose-fact (1- fuel) proof conclusion condition)))))))
        (t step)))))

(defun proof-search-discharge-fact (proof step sides condition)
  (if (endp sides)
      (proof-proof-tidy proof step)
    (let ((side (car sides)))
      (cond
        ((or (equal side *proof-false*)
             (not (member-equal side (cdr (proof-step-clause step)))))
         (proof-search-discharge-fact proof step (cdr sides) condition))
        ((eq condition :none)
         *terms-unproved*)
        ((and (proof-is-call side *proof-not*) (endp (cdr side)))
         '(:failure "failure" ""))
        (t
         (let* ((need (if (proof-is-call side *proof-not*)
                          (cadr side)
                        (proof-neg side)))
                (premise (proof-search-condition need condition)))
           (if (proof-search-interrupted-p premise)
               premise
             (proof-search-let
               ((updated (proof-proof-discharge proof step premise)))
               (proof-search-discharge-fact proof updated (cdr sides)
                                            condition)))))))))

(defun proof-search-fact-index-apply (index rule bindings condition)
  (let* ((proof (library-library-proof (proof-search-fact-index-lib index)))
         (step (proof-proof-fact proof (proof-search-rule-name rule)
                                 (table-items bindings))))
    (if (failure-p step)
        step
      (let ((opened (if (proof-search-rule-expose rule)
                        (proof-search-expose-fact 1000000 proof step condition)
                      step)))
        (if (proof-search-interrupted-p opened)
            opened
          (proof-search-discharge-fact proof opened
                                       (cdr (proof-step-clause opened))
                                       condition))))))

(defun proof-search-prove-fact (index candidates goal condition)
  (if (endp candidates)
      *terms-unproved*
    (let* ((rule (car candidates))
           (matched (book-logic-match (proof-search-rule-pattern rule) goal nil)))
      (cond
        ((failure-p matched) matched)
        ((failure-p (car matched)) (car matched))
        ((not (car matched))
         (proof-search-prove-fact index (cdr candidates) goal condition))
        (t
         (let ((step (proof-search-fact-index-apply index rule (cdr matched)
                                                   condition)))
           (cond
             ((terms-unproved-p step)
              (proof-search-prove-fact index (cdr candidates) goal condition))
             ((proof-search-interrupted-p step) step)
             (t
              (proof-search-let ((first (proof-step-first step)))
                (if (equal first goal)
                    step
                  (proof-search-prove-fact index (cdr candidates) goal
                                           condition)))))))))))

(defund proof-search-fact-index-prove (index goal condition)
  (proof-search-let ((candidates (proof-search-fact-index-candidates index goal)))
    (proof-search-prove-fact index candidates goal condition)))

(defund proof-search-equality-right (step)
  (proof-search-let ((first (proof-step-first step)))
    (if (and (consp first) (consp (cdr first)) (consp (cddr first)))
        (caddr first)
      '(:failure "failure" ""))))

(defun proof-search-shorten-fact-step (proof step size condition)
  (proof-search-let
    ((right (proof-search-equality-right step))
     (actual (book-logic-term-size right size)))
    (cond
      ((< actual size) step)
      ((not (proof-is-call right *proof-if*)) nil)
      ((endp (cdr right)) '(:failure "failure" ""))
      ((eq condition :none) '(:failure "failure" ""))
      (t
       (let* ((positive (proof-search-condition (cadr right) condition))
              (test (if (terms-unproved-p positive)
                        (proof-search-condition (proof-neg (cadr right))
                                                condition)
                      positive)))
         (if (proof-search-interrupted-p test)
             test
           (proof-search-let
             ((selected (proof-proof-select proof right test))
              (shortened (proof-proof-chain proof step (list selected))))
             (cons :shorten shortened))))))))

(defun proof-search-shorten-fact (fuel proof next size condition)
  (declare (xargs :measure (nfix fuel)))
  (cond
    ((not (eq (car next) :shorten)) next)
    ((zp fuel) '(:failure "fuel" "proof-search-shorten-fact"))
    (t
     (proof-search-shorten-fact
      (1- fuel) proof (proof-search-shorten-fact-step proof (cdr next) size condition)
      size condition))))

(defun proof-search-match-rewrite (index rule term size condition)
  (let ((pattern (proof-search-rule-pattern rule)))
    (if (endp (cdr pattern))
        '(:failure "failure" "")
      (let ((matched (book-logic-match (cadr pattern) term nil)))
        (cond
          ((failure-p matched) matched)
          ((failure-p (car matched)) (car matched))
          ((not (car matched)) nil)
          ((endp (cddr pattern)) '(:failure "failure" ""))
          (t
           (proof-search-let
             ((right (proof-subst (caddr pattern) (cdr matched)))
              (shorter (proof-search-can-shorten right size)))
             (if shorter
                 (let ((step (proof-search-fact-index-apply index rule (cdr matched)
                                                           condition)))
                   (if (proof-search-interrupted-p step)
                       step
                     (proof-search-shorten-fact
                      1000000 (library-library-proof (proof-search-fact-index-lib index))
                      (cons :shorten step) size condition)))
               nil))))))))

(defun proof-search-rewrite-fact (index candidates term size condition)
  (if (endp candidates)
      nil
    (let ((step (proof-search-match-rewrite index (car candidates) term size
                                            condition)))
      (if (or (not step) (terms-unproved-p step))
          (proof-search-rewrite-fact index (cdr candidates) term size condition)
        step))))

(defund proof-search-fact-index-rewrite (index term condition)
  (proof-search-let ((qualified (proof-search-key term)))
    (let ((candidates (cdr (assoc-equal qualified
                                       (proof-search-fact-index-equations index)))))
      (if candidates
          (proof-search-let ((size (book-logic-term-size term 120)))
            (proof-search-rewrite-fact index (reverse candidates) term size
                                       condition))
        nil))))

(defun proof-search-fact-index-recursive-invocations (index name)
  (let* ((proof (library-library-proof (proof-search-fact-index-lib index)))
         (definition (assoc-equal name (proof-proof-definitions proof))))
    (if definition
        (if (equal (len (cdr definition)) 2)
            (termination-recursive-calls *termination-all* (list definition))
          *terms-invalid-proof-arity*)
      '(:failure "failure" ""))))

(defun proof-search-recursive-actuals (calls)
  (if (endp calls)
      nil
    (cons (termination-call-actuals (car calls))
          (proof-search-recursive-actuals (cdr calls)))))

(defun proof-search-fact-index-recursive-arguments (index name)
  (proof-search-let
    ((calls (proof-search-fact-index-recursive-invocations index name)))
    (proof-search-recursive-actuals calls)))

(mutual-recursion
 (defun proof-search-find-conditional-test (term)
   (declare (xargs :measure (acl2-count term)))
   (cond
     ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
     ((proof-is-call term *proof-if*)
      (if (endp (cdr term))
          '(:failure "failure" "")
        (proof-search-let ((inner (proof-search-find-conditional-test (cadr term))))
          (if (and inner (proof-search-present-p (cdr inner)))
              inner
            (cons :test (cadr term))))))
     ((consp (cdr term)) (proof-search-conditional-test-arguments (cdr term)))
     (t nil)))
 (defun proof-search-conditional-test-arguments (arguments)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (let ((test (proof-search-find-conditional-test (car arguments))))
       (if test test (proof-search-conditional-test-arguments (cdr arguments)))))))

(defmacro proof-search-let-in (object bindings body)
  (if (endp bindings)
      body
    (let ((binding (car bindings)))
      `(let (,binding)
         (if (failure-p ,(car binding))
             (cons ,(car binding) ,object)
           (proof-search-let-in ,object ,(cdr bindings) ,body))))))

(defmacro proof-search-with-result (value object form body)
  `(let* ((proof-search-reply ,form)
          (,value (car proof-search-reply))
          (,object (cdr proof-search-reply)))
     ,body))

(defun proof-search-make-search (lib index budget rewriting logical pending)
  (list :search lib index budget rewriting logical pending))

(defun proof-search-search-init (lib index budget rewriting logical)
  (proof-search-make-search lib index budget (or rewriting logical) logical nil))

(defun proof-search-search-lib (search)
  (cadr search))

(defun proof-search-search-index (search)
  (caddr search))

(defun proof-search-search-budget (search)
  (cadddr search))

(defun proof-search-search-rewriting (search)
  (nth 4 search))

(defun proof-search-search-logical (search)
  (nth 5 search))

(defun proof-search-search-pending (search)
  (nth 6 search))

(defun proof-search-search-with-lib (search lib)
  (let* ((index (proof-search-search-index search))
         (index (if (equal (proof-search-fact-index-lib index)
                           (proof-search-search-lib search))
                    (proof-search-fact-index-with-lib index lib)
                  index)))
    (proof-search-make-search lib index (proof-search-search-budget search)
                              (proof-search-search-rewriting search)
                              (proof-search-search-logical search)
                              (proof-search-search-pending search))))

(defun proof-search-search-with-budget (search budget)
  (proof-search-make-search (proof-search-search-lib search)
                            (proof-search-search-index search) budget
                            (proof-search-search-rewriting search)
                            (proof-search-search-logical search)
                            (proof-search-search-pending search)))

(defun proof-search-search-with-pending (search pending)
  (proof-search-make-search (proof-search-search-lib search)
                            (proof-search-search-index search)
                            (proof-search-search-budget search)
                            (proof-search-search-rewriting search)
                            (proof-search-search-logical search) pending))

(defund proof-search-library-result (result search)
  (if (failure-p result)
      (cons result search)
    (cons (car result) (proof-search-search-with-lib search (cdr result)))))

(defun proof-search-proof (search)
  (library-library-proof (proof-search-search-lib search)))

(defun proof-search-reduce (lib evidence definitions expose budget size logical term)
  (proof-search-let
    ((reducer (book-logic-reducer-init lib evidence definitions expose
                                      budget size nil logical)))
    (car (book-logic-reducer-reduce reducer term nil))))

(defun proof-search-reducer-prove (lib evidence definitions budget size logical term)
  (proof-search-let
    ((reducer (book-logic-reducer-init lib evidence definitions nil
                                      budget size nil logical)))
    (car (book-logic-reducer-prove reducer term))))

(defund proof-search-evidence-index (steps evidence replacep)
  (if (endp steps)
      evidence
    (proof-search-let ((term (proof-step-first (car steps))))
      (proof-search-evidence-index
       (cdr steps)
       (if (or replacep (not (assoc-equal term evidence)))
           (table-put evidence term (car steps))
         evidence)
       replacep))))

(defun proof-search-search-evidence-add (step rules expanded)
  (proof-search-let ((term (proof-step-first step)))
    (let ((negative (proof-is-call term *proof-not*)))
      (if (and negative (endp (cdr term)))
          '(:failure "failure" "")
        (proof-search-let
          ((parts (rulers-rulers-expand 1000000 rules
                                       (if negative (cadr term) term)
                                       (not negative) step)))
          (proof-search-evidence-index parts expanded nil))))))

(defun proof-search-expand-evidence (steps rules expanded)
  (if (endp steps)
      expanded
    (proof-search-let
      ((expanded (proof-search-search-evidence-add (car steps) rules expanded)))
      (proof-search-expand-evidence (cdr steps) rules expanded))))

(defun proof-search-cons-argument-p (arguments expanded)
  (and (consp arguments)
       (or (and (assoc-equal (list *proof-consp* (car arguments)) expanded) t)
           (proof-search-cons-argument-p (cdr arguments) expanded))))

(defun proof-search-open-evidence-step (step search rules expanded base)
  (proof-search-let
    ((term (proof-step-first step))
     (function (proof-search-head term)))
    (let* ((lib (proof-search-search-lib search))
           (proof (library-library-proof lib))
           (logical (proof-search-search-logical search))
           (definition (assoc-equal function (proof-proof-definitions proof))))
      (if (or (not definition)
              (member-equal function (list *proof-if* *library-implies* *proof-not*)))
          expanded
        (let* ((body (caddr definition))
               (has-cons (proof-search-cons-argument-p (cdr term) expanded))
               (equal-heads (if logical
                                (list *proof-equal* (proof-cl "EQL")
                                      (proof-cl "EQ") *termination-return-last*)
                              (list *proof-equal*))))
          (proof-search-let
            ((eligible (if has-cons
                           t
                         (proof-search-let ((operator (proof-search-head body)))
                           (member-equal operator equal-heads))))
             (small (and eligible
                         (book-logic-within-size body (if logical 80 60)))))
            (if (not small)
                expanded
              (let ((definitions (append (list (proof-cl "ATOM")
                                               (proof-cl "ENDP") *proof-not*)
                                         (if logical
                                             (list (proof-cl "EQL") (proof-cl "EQ"))
                                           nil))))
                (proof-search-let
                  ((opened (proof-proof-unfold proof term))
                   (value (proof-search-equality-right opened))
                   (reduced (proof-search-reduce lib base definitions nil
                                                 25 100 logical value))
                   (equation (proof-proof-chain proof opened (list reduced)))
                   (result (proof-search-equality-right equation))
                   (small (book-logic-within-size result 120)))
                  (if small
                      (proof-search-let
                        ((rewritten (proof-proof-rewrite proof step equation (list 1)))
                         (tidied (proof-proof-tidy proof rewritten)))
                        (proof-search-search-evidence-add tidied rules expanded))
                    expanded))))))))))

(defun proof-search-open-evidence (steps search rules expanded base)
  (if (endp steps)
      expanded
    (proof-search-let
      ((updated (proof-search-open-evidence-step (car steps) search rules expanded base)))
      (proof-search-open-evidence (cdr steps) search rules updated base))))

(defund proof-search-search-evidence (search steps)
  (proof-search-let
    ((rules (rulers-rulers-init (proof-search-search-lib search) nil nil))
     (expanded (proof-search-expand-evidence steps rules nil))
     (expanded (if (proof-search-search-rewriting search)
                   (proof-search-open-evidence steps search rules expanded
                                               (table-values expanded))
                 expanded)))
    (table-values expanded)))

(defund proof-search-conjunction-p (term)
  (if (proof-is-call term *proof-if*)
      (if (consp (cdddr term))
          (equal (cadddr term) *proof-false*)
        '(:failure "failure" ""))
    nil))

(defun proof-search-transport-selected (proof term test branch)
  (proof-search-let ((selected (proof-proof-select proof term test)))
    (proof-proof-transport proof branch selected)))

(defund proof-search-search-computed-premise (search term known)
  (proof-search-with-result value search
    (proof-search-library-result
     (remainder-proofs-remainder-premise (proof-search-search-lib search) term known)
     search)
    (if value
        (cons value search)
      (proof-search-library-result
       (finite-tables-finite-table-predicate (proof-search-search-lib search) term known)
       search))))

(defun proof-search-search-context-premise-loop (fuel search term evidence known)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      '(:failure "fuel" "proof-search-search-context-premise-loop")
    (let ((entry (assoc-equal term known)))
      (if entry
          (cdr entry)
        (proof-search-let ((conditional (proof-search-conjunction-p term)))
          (if conditional
              (proof-search-let
                ((test (proof-search-search-context-premise-loop
                        (1- fuel) search (cadr term) evidence known))
                 (branch (proof-search-search-context-premise-loop
                          (1- fuel) search (caddr term) evidence known)))
                (proof-search-transport-selected (proof-search-proof search)
                                                 term test branch))
            (proof-search-reducer-prove
             (proof-search-search-lib search) evidence
             (list (proof-cl "EQ") (proof-cl "EQL") *proof-not*)
             18 100 t term)))))))

(defun proof-search-search-context-premise (search term evidence known)
  (proof-search-search-context-premise-loop 1000000 search term evidence known))

(defun proof-search-search-prove-premise-context (premise search evidence known)
  (proof-search-search-context-premise search premise evidence known))

(defun proof-search-context-index-prove (fuel search goal evidence known answers)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      '(:failure "fuel" "proof-search-context-index-prove")
    (let ((step (proof-search-fact-index-prove (proof-search-search-index search)
                                               goal answers)))
      (if (proof-search-request-p step)
          (let* ((term (cadr step))
                 (proof (proof-search-search-prove-premise-context
                         term search evidence known)))
            (proof-search-context-index-prove
             (1- fuel) search goal evidence known (table-put answers term proof)))
        step))))

(defun proof-search-proper-list-search (fuel result evidence known search)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (cons '(:failure "fuel" "proof-search-proper-list-search") search)
    (proof-search-with-result value search
      (proof-search-library-result result search)
      (if (and (consp value) (eq (car value) :call))
          (let ((answer (proof-search-context-index-prove 1000000 search
                                                          (cadr value) evidence known nil)))
            (proof-search-proper-list-search
             (1- fuel)
             (proper-lists-proper-list-search-resume
              (proof-search-search-lib search) (cadddr value) answer)
             evidence known search))
        (cons value search)))))

(defun proof-search-logical-premise (search term evidence known)
  (proof-search-with-result computed search
    (proof-search-search-computed-premise search term known)
    (if computed
        (cons computed search)
      (let ((indexed (and evidence
                          (proof-search-context-index-prove
                           1000000 search term evidence known nil))))
        (cond
          ((and indexed (not (terms-unproved-p indexed)))
           (cons indexed search))
          ((proof-is-call term *proper-lists-true-list*)
           (if (consp (cdr term))
               (proof-search-proper-list-search
                1000000 (proper-lists-proper-list-search
                         (proof-search-search-lib search) (cadr term) evidence)
                evidence known search)
             (cons '(:failure "failure" "") search)))
          (t (cons nil search)))))))

(defun proof-search-reduce-premise (search term evidence known)
  (let ((indexed (proof-search-fact-index-prove (proof-search-search-index search)
                                                  term :none)))
    (if (terms-unproved-p indexed)
        (proof-search-with-result logical search
          (if (proof-search-search-logical search)
              (proof-search-logical-premise search term evidence known)
            (cons nil search))
          (if logical
              (cons logical search)
            (cons (proof-search-reducer-prove
                   (proof-search-search-lib search) evidence :none 35 120
                   (proof-search-search-logical search) term)
                  search)))
      (cons indexed search))))

(mutual-recursion
 (defun proof-search-search-premise-loop (fuel search term evidence known)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-search-premise-loop") search)
     (proof-search-let-in search ((small (book-logic-within-size term 160)))
       (if (not small)
           (cons *terms-unproved*
                 search)
         (let ((entry (assoc-equal term known)))
           (if entry
               (cons (cdr entry) search)
             (proof-search-with-result value search
               (proof-search-search-prove-premise-loop
                (1- fuel) search term evidence known)
               (cons (if (or (not value) (terms-unproved-p value))
                         *terms-unproved*
                       value)
                     search))))))))
 (defun proof-search-search-prove-premise-loop (fuel search term evidence known)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-search-prove-premise-loop") search)
     (proof-search-let-in search ((conditional (proof-search-conjunction-p term)))
       (if conditional
           (proof-search-with-result left search
             (proof-search-search-premise-loop (1- fuel) search (cadr term) evidence known)
             (if (failure-p left)
                 (cons left search)
               (proof-search-with-result right search
                 (proof-search-search-premise-loop (1- fuel) search (caddr term) evidence known)
                 (if (failure-p right)
                     (cons right search)
                   (cons (proof-search-transport-selected (proof-search-proof search)
                                                          term left right)
                         search)))))
         (proof-search-reduce-premise search term evidence known))))))

(defund proof-search-search-premise (search term evidence known)
  (proof-search-search-premise-loop 1000000 search term evidence known))

; Each requested premise is proved against the current library and evidence.
(defund proof-search-index-with-premise (fuel search term evidence known answers rewritep)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (cons '(:failure "fuel" "proof-search-index-with-premise") search)
    (let* ((index (proof-search-search-index search))
           (step (if rewritep
                     (proof-search-fact-index-rewrite index term answers)
                   (proof-search-fact-index-prove index term answers))))
      (if (proof-search-request-p step)
          (let ((test (cadr step)))
            (proof-search-with-result answer search
              (proof-search-search-premise search test evidence known)
              (proof-search-index-with-premise (1- fuel) search term evidence known
                                               (table-put answers test answer)
                                               rewritep)))
        (cons step search)))))

(defun proof-search-integer-evidence (steps)
  (if (endp steps)
      nil
    (proof-search-let
      ((first (proof-step-first (car steps)))
       (rest (proof-search-integer-evidence (cdr steps))))
      (if (proof-is-call first *proof-integerp*)
          (cons (car steps) rest)
        rest))))

(defund proof-search-evidence-literals (evidence)
  (if (endp evidence)
      nil
    (proof-search-let
      ((first (proof-step-first (car evidence)))
       (rest (proof-search-evidence-literals (cdr evidence))))
      (cons first rest))))

(defun proof-search-contradiction (proof formula entries known)
  (if (endp entries)
      nil
    (let* ((entry (car entries))
           (opposite (assoc-equal (proof-neg (car entry)) known)))
      (if opposite
          (proof-search-let ((cut (proof-proof-cut proof (cdr entry) (cdr opposite))))
            (proof-proof-subsume proof cut (cons formula (proof-step-clause cut))))
        (proof-search-contradiction proof formula (cdr entries) known)))))

(defund proof-search-known-formula (search formula known)
  (let* ((proof (proof-search-proof search))
         (found (assoc-equal formula known))
         (false (assoc-equal *proof-false* known)))
    (cond
      (found (cdr found))
      (false
       (proof-proof-subsume proof (cdr false)
                            (cons formula (cdr (proof-step-clause (cdr false))))))
      (t (proof-search-contradiction proof formula known known)))))

(defund proof-search-search-evidence-implication (search formula steps evidence known)
  (if (endp steps)
      (cons nil search)
    (let ((premise (car steps)))
      (proof-search-let-in search ((first (proof-step-first premise)))
        (if (proof-is-call first *library-implies*)
            (cond
              ((endp (cddr first)) (cons '(:failure "failure" "") search))
              ((equal (caddr first) formula)
               (proof-search-with-result required search
                 (proof-search-search-premise search (cadr first) evidence known)
                 (let ((proof (if (failure-p required)
                                  required
                                (proof-proof-modus-ponens
                                 (proof-search-proof search) premise required))))
                   (if (terms-unproved-p proof)
                       (proof-search-search-evidence-implication
                        search formula (cdr steps) evidence known)
                     (cons proof search)))))
              (t (proof-search-search-evidence-implication
                  search formula (cdr steps) evidence known)))
          (proof-search-search-evidence-implication
           search formula (cdr steps) evidence known))))))

; Replaying the replies preserves the reducer's traversal, memo and budget.
(defund proof-search-rewrite-reduction (fuel reducer term replies evidence known search)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (cons '(:failure "fuel" "proof-search-rewrite-reduction") search)
    (let* ((working (book-logic-reducer-with-rewrite reducer (cons t replies)))
           (reduced (book-logic-reducer-reduce working term nil))
           (value (car reduced)))
      (if (and (consp value) (eq (car value) :call) (eq (cadr value) :rewrite))
          (let ((search (proof-search-search-with-lib search (caddr value))))
            (proof-search-with-result step search
              (proof-search-index-with-premise
               1000000 search (cadddr value) evidence known nil t)
              (proof-search-rewrite-reduction
               (1- fuel) reducer term
               (append replies (list (cons step (proof-search-search-lib search))))
               evidence known search)))
        (cons value search)))))

(defun proof-search-arithmetic-head-p (terms)
  (if (endp terms)
      nil
    (proof-search-let ((operator (proof-search-head (car terms))))
      (if (member-equal operator (list *proof-plus* *proof-minus*))
          t
        (proof-search-arithmetic-head-p (cdr terms))))))

; Sum normalization uses the integer rules of the current proof theory.
; The slice and book theories can add auxiliary lemmas during type inference.

(defund proof-search-slice-leaf-integer (lib term evidence)
  (let ((answer (lemmas-slice-library-type-of lib term evidence)))
    (if (failure-p answer) (cons answer lib) answer)))

(defun proof-search-integer-constructor (term)
  (and (proof-compound term)
       (cond
         ((equal (car term) *proof-plus*) "INTEGER-SUM")
         ((equal (car term) *proof-times*) "INTEGER-PRODUCT")
         ((equal (car term) *proof-minus*) "INTEGER-NEGATION")
         (t nil))))

(mutual-recursion
 (defun proof-search-slice-integer-in (fuel lib term evidence)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-slice-integer-in") lib)
     (let ((name (proof-search-integer-constructor term)))
       (if (not name)
           (proof-search-slice-leaf-integer lib term evidence)
         (proof-search-let-in lib
           ((supplied (library-type-evidence (library-integer term) evidence)))
           (if supplied
               (cons supplied lib)
             (let ((negative (proof-is-call term *proof-minus*)))
               (if (and negative (endp (cdr term)))
                   (cons '(:failure "failure" "") lib)
                 (let ((arguments (if negative (list (cadr term)) (cdr term))))
                   (proof-search-with-result types lib
                     (proof-search-slice-integers-in (1- fuel) lib arguments evidence)
                     (cons (if (failure-p types)
                               types
                             (library-library-cite lib name (cdr term) types))
                           lib)))))))))))

 (defun proof-search-slice-integers-in (fuel lib terms evidence)
   (declare (xargs :measure (nfix fuel)))
   (cond
     ((zp fuel) (cons '(:failure "fuel" "proof-search-slice-integers-in") lib))
     ((endp terms) (cons nil lib))
     (t
      (proof-search-with-result step lib
        (proof-search-slice-integer-in (1- fuel) lib (car terms) evidence)
        (if (failure-p step)
            (cons step lib)
          (proof-search-with-result rest lib
            (proof-search-slice-integers-in (1- fuel) lib (cdr terms) evidence)
            (cons (if (failure-p rest) rest (cons step rest)) lib))))))))

(defund proof-search-slice-integer (lib term evidence)
  (proof-search-slice-integer-in 1000000 lib term evidence))

(defun proof-search-slice-integers (lib terms evidence)
  (proof-search-slice-integers-in 1000000 lib terms evidence))

(defund proof-search-slice-negation-rule (lib argument evidence)
  (let ((facts (proof-proof-facts (library-library-proof lib))))
    (cond
      ((and (proof-is-call argument *proof-minus*)
            (assoc-equal (proof-sym "SELF-DOUBLE-NEGATION" "ACL2") facts))
       (proof-search-let-in lib ((term (proof-term-at argument 1)))
         (proof-search-with-result integral lib
           (proof-search-slice-integer lib term evidence)
           (cons (if (failure-p integral)
                     integral
                   (library-library-cite lib "DOUBLE-NEGATION"
                                         (list term) (list integral)))
                 lib))))
      ((and (proof-is-call argument *proof-plus*)
            (assoc-equal (proof-sym "SELF-NEGATE-SUM" "ACL2") facts))
       (proof-search-with-result types lib
         (proof-search-slice-integers lib (cdr argument) evidence)
         (cons (if (failure-p types)
                   types
                 (library-library-cite lib "NEGATE-SUM" (cdr argument) types))
               lib)))
      (t (cons nil lib)))))

(defund proof-search-linear-identity (lib term)
  (proof-proof-reflexive (library-library-proof lib) term))

(defund proof-search-linear-rewrite (lib step equality place)
  (if equality
      (proof-proof-rewrite (library-library-proof lib) step equality place)
    step))

(defund proof-search-push-slice-minus (fuel lib term evidence)
  (declare (xargs :measure (nfix fuel)))
  (cond
    ((zp fuel) (cons '(:failure "fuel" "proof-search-push-slice-minus") lib))
    ((proof-is-call term *proof-plus*)
     (proof-search-let-in lib
       ((identity (proof-search-linear-identity lib term))
        (left (proof-term-at term 1)))
       (proof-search-with-result left-step lib
         (proof-search-push-slice-minus (1- fuel) lib left evidence)
         (proof-search-let-in lib
           ((left-step left-step)
            (result (proof-search-linear-rewrite lib identity left-step '(1 2 1)))
            (right (proof-term-at term 2)))
           (proof-search-with-result right-step lib
             (proof-search-push-slice-minus (1- fuel) lib right evidence)
             (proof-search-let-in lib
               ((right-step right-step)
                (result (proof-search-linear-rewrite lib result right-step '(1 2 2)))
                (normal (proof-search-equality-right result)))
               (cons (if (equal normal term) nil result) lib)))))))
    ((proof-is-call term *proof-minus*)
     (proof-search-let-in lib ((argument (proof-term-at term 1)))
       (if (proof-is-call argument *proof-quote*)
           (cons (proof-proof-constant (library-library-proof lib) term) lib)
         (proof-search-with-result step lib
           (proof-search-slice-negation-rule lib argument evidence)
           (if (or (not step) (failure-p step))
               (cons step lib)
             (proof-search-let-in lib ((right (proof-search-equality-right step)))
               (proof-search-with-result rest lib
                 (proof-search-push-slice-minus (1- fuel) lib right evidence)
                 (cons (if (failure-p rest)
                           rest
                         (proof-proof-chain (library-library-proof lib) step (list rest)))
                       lib))))))))
    (t (cons nil lib))))

(defun proof-search-remove-slice-zero (lib step name term place evidence)
  (proof-search-with-result integral lib
    (proof-search-slice-integer lib term evidence)
    (proof-search-let-in lib
      ((integral integral)
       (identity (library-library-cite lib name (list term) (list integral)))
       (rewritten (proof-search-linear-rewrite lib step identity place)))
      (cons (list :combine rewritten place) lib))))

(defun proof-search-associate-slice-pair (lib step a b rest place)
  (let ((proof (library-library-proof lib)))
    (proof-search-let
      ((tail (proof-term-at rest 2))
       (assoc (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list a b tail)))
       (reverse (proof-proof-symmetric proof assoc)))
      (proof-search-linear-rewrite lib step reverse place))))

(defun proof-search-combine-slice-pair (lib step a b rest suffix place)
  (proof-search-let-in lib
    ((combine (library-linear-combine-pair lib a b)))
    (if (not combine)
        (cons (list :combine step (append place '(2))) lib)
      (proof-search-let-in lib
        ((step (if suffix
                   (proof-search-associate-slice-pair lib step a b rest place)
                 step))
         (rewritten (proof-search-linear-rewrite
                     lib step combine (if suffix (append place '(1)) place))))
        (cons (list :combine rewritten '(1 2)) lib)))))

(defun proof-search-combine-slice-step (lib step place evidence)
  (proof-search-let-in lib
    ((first (proof-step-first step))
     (node (library-linear-form-get first (cdr place))))
    (if (not (proof-is-call node *proof-plus*))
        (cons (proof-proof-tidy (library-library-proof lib) step) lib)
      (proof-search-let-in lib ((pair (proof-list-of-length (cdr node) 2)))
        (let* ((a (car pair))
               (rest (cadr pair))
               (suffix (proof-is-call rest *proof-plus*)))
          (proof-search-let-in lib ((b (if suffix (proof-term-at rest 1) rest)))
            (cond
              ((equal a *proof-zero*)
               (proof-search-remove-slice-zero lib step "ADD-ZERO-LEFT"
                                                rest place evidence))
              ((and (equal b *proof-zero*) (not suffix))
               (proof-search-remove-slice-zero lib step "ADD-ZERO-RIGHT"
                                                a place evidence))
              (t (proof-search-combine-slice-pair lib step a b rest suffix place)))))))))

(defun proof-search-combine-slice-sum (fuel result evidence)
  (declare (xargs :measure (nfix fuel)))
  (let ((value (car result))
        (lib (cdr result)))
    (cond
      ((not (eq (car value) :combine)) result)
      ((zp fuel) (cons '(:failure "fuel" "proof-search-combine-slice-sum") lib))
      (t
       (proof-search-combine-slice-sum
        (1- fuel)
        (proof-search-combine-slice-step lib (cadr value) (caddr value) evidence)
        evidence)))))

(defun proof-search-slice-linear-form (lib term evidence)
  (proof-search-with-result step lib
    (proof-search-push-slice-minus 1000000 lib term evidence)
    (proof-search-let-in lib
      ((step (if step step (proof-search-linear-identity lib term)))
       (step (library-linear-reassociate 1000000 lib step '(1 2)))
       (step (library-linear-sort 1000000 lib step '(1 2) nil)))
      (proof-search-combine-slice-sum
       1000000 (cons (list :combine step '(1 2)) lib) evidence))))

(defun proof-search-slice-linear-equal (lib left right integers)
  (proof-search-with-result a lib
    (proof-search-slice-linear-form lib left integers)
    (proof-search-let-in lib ((a a))
      (proof-search-with-result b lib
        (proof-search-slice-linear-form lib right integers)
        (proof-search-let-in lib
          ((b b)
           (a-normal (proof-search-equality-right a))
           (b-normal (proof-search-equality-right b)))
          (if (equal a-normal b-normal)
              (let ((proof (library-library-proof lib)))
                (proof-search-let-in lib ((reverse (proof-proof-symmetric proof b)))
                  (cons (proof-proof-chain proof a (list reverse)) lib)))
            (let ((checked (proof-write-list (list a-normal b-normal))))
              (cons (if (failure-p checked) checked *terms-different-normal-forms*)
                    lib))))))))

(defun proof-search-linear-equal-call (lib target integers)
  (let ((arguments (cdr target)))
    (case (len arguments)
      (2 (if (member-eq (proof-proof-kind (library-library-proof lib)) '(:slice :book))
             (proof-search-slice-linear-equal lib (car arguments) (cadr arguments) integers)
           (cons (library-library-linear-equal lib (car arguments) (cadr arguments) integers)
                 lib)))
      (otherwise (cons '(:failure "failure" "") lib)))))

(defun proof-search-reduced-equality (search target reduced evidence)
  (proof-search-let-in search
    ((arithmetic (and (proof-is-call target *proof-equal*)
                      (proof-search-arithmetic-head-p (cdr target)))))
    (if (not arithmetic)
        (cons nil search)
      (proof-search-let-in search ((integers (proof-search-integer-evidence evidence)))
        (proof-search-with-result equality search
          (proof-search-library-result
           (proof-search-linear-equal-call (proof-search-search-lib search)
                                           target integers)
           search)
          (let ((result (cond
                          ((or (failure-p equality) (not reduced)) equality)
                          (t (proof-proof-transport
                              (proof-search-proof search) equality reduced)))))
            (cons (if (terms-proof-fallback-p result) nil result) search)))))))

(defund proof-search-reduced-formula (search target reduced known evidence)
  (let ((proof (proof-search-proof search))
        (known-step (assoc-equal target known)))
    (cond
      ((equal target *proof-true*)
       (cons (if reduced
                 (proof-proof-true-from-eq proof reduced)
               (proof-proof-prove proof *proof-true* nil nil))
             search))
      (known-step
       (cons (if reduced
                 (proof-proof-transport proof (cdr known-step) reduced)
               (cdr known-step))
             search))
      (t (proof-search-reduced-equality search target reduced evidence)))))

(defund proof-search-splitting-test (search target formula evidence)
  (proof-search-let ((test (proof-search-find-conditional-test target)))
    (if (or test (not (proof-search-search-rewriting search)))
        test
      (proof-search-let
        ((view (proof-search-reduce (proof-search-search-lib search) evidence :none t
                                     65 160 (proof-search-search-logical search)
                                     formula)))
        (if view
            (proof-search-let ((value (proof-search-equality-right view)))
              (proof-search-find-conditional-test value))
          nil)))))

(defund proof-search-search-invariance (search call fixed-call fixed position require)
  (let ((step (proof-search-fact-index-prove (proof-search-search-index search)
                                              (proof-eq fixed-call call) require)))
    (if (terms-unproved-p step)
        (if (equal position 1)
            (proof-search-library-result
             (fixer-proofs-fixer-invariance (proof-search-search-lib search) call fixed)
             search)
          (cons nil search))
      (cons step search))))

(defun proof-search-search-fixed-arguments-require (term search evidence known)
  (proof-search-search-premise search term evidence known))

(defun proof-search-invariance (fuel search call fixed-call fixed position
                                     evidence known answers)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (cons '(:failure "fuel" "proof-search-invariance") search)
    (proof-search-with-result step search
      (proof-search-search-invariance search call fixed-call fixed position answers)
      (if (proof-search-request-p step)
          (let ((term (cadr step)))
            (proof-search-with-result answer search
              (proof-search-search-fixed-arguments-require term search evidence known)
              (proof-search-invariance (1- fuel) search call fixed-call fixed position
                                        evidence known (table-put answers term answer))))
        (cons step search)))))

(defun proof-search-fixed-argument-pair (search first second left right position
                                               premise evidence known)
  (let ((left-fixed (append (seq-slice left :none position) (list first)
                            (seq-slice left (1+ position) :none)))
        (right-fixed (append (seq-slice right :none position) (list second)
                             (seq-slice right (1+ position) :none))))
    (proof-search-with-result fix-left search
      (proof-search-invariance 1000000 search left left-fixed first position
                               evidence known nil)
      (if (or (not fix-left) (failure-p fix-left))
          (cons fix-left search)
        (proof-search-with-result fix-right search
          (proof-search-invariance 1000000 search right right-fixed second position
                                   evidence known nil)
          (if (or (not fix-right) (failure-p fix-right))
              (cons fix-right search)
            (let ((proof (proof-search-proof search)))
              (proof-search-let-in search
                ((reverse (proof-proof-symmetric proof fix-left))
                 (initial (proof-proof-rewrite proof reverse premise (list 1 2 position))))
                (cons (proof-proof-chain proof initial (list fix-right)) search)))))))))

(defund proof-search-fixed-argument-premise (search left right position before after
                                                  premise evidence known)
  (proof-search-let-in search ((literal (proof-step-first premise)))
    (cond
      ((not (proof-is-call literal *proof-equal*)) (cons nil search))
      ((not (equal (len (cdr literal)) 2))
       (cons *terms-invalid-proof-arity* search))
      (t
       (let ((first (cadr literal))
             (second (caddr literal)))
         (proof-search-let-in search
           ((first-head (proof-search-head first))
            (second-head (proof-search-head second)))
           (if (or (not (equal first-head second-head))
                   (not (proof-search-present-p first-head)))
               (cons nil search)
             (let* ((swap (and (member-equal after (cdr first))
                               (member-equal before (cdr second))))
                    (ordered-first (if swap second first))
                    (ordered-second (if swap first second))
                    (premise (if swap
                                 (proof-proof-symmetric (proof-search-proof search)
                                                       premise)
                               premise)))
               (cond
                 ((failure-p premise) (cons premise search))
                 ((and (member-equal before (cdr ordered-first))
                       (member-equal after (cdr ordered-second)))
                  (proof-search-fixed-argument-pair
                   search ordered-first ordered-second left right position
                   premise evidence known))
                 (t (cons nil search)))))))))))

(defun proof-search-fixed-arguments-loop (search left right position before after
                                                steps evidence known)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      (cons nil search)
    (proof-search-with-result proof search
      (proof-search-fixed-argument-premise search left right position before after
                                            (car steps) evidence known)
      (if proof
          (cons proof search)
        (proof-search-fixed-arguments-loop search left right position before after
                                            (cdr steps) evidence known)))))

(defund proof-search-search-fixed-arguments (search left right position before after
                                                   evidence known)
  (proof-search-fixed-arguments-loop search left right position before after
                                     evidence evidence known))

(defun proof-search-boolean (lib term)
  (let ((kind (proof-proof-kind (library-library-proof lib))))
    (case kind
      (:book (book-library-book-library-boolean lib term))
      (:slice '(:failure "failure" ""))
      (otherwise '(:failure "failure" "")))))

(defund proof-search-boolean-formula (search formula evidence)
  (if (not (proof-is-call formula *book-library-booleanp*))
      nil
    (if (endp (cdr formula))
        '(:failure "failure" "")
      (let* ((lib (proof-search-search-lib search))
             (value (cadr formula))
             (typed (proof-search-boolean lib value)))
        (if typed
            typed
          (proof-search-let ((opened (proof-search-reduce lib evidence :none t
                                                          50 145 nil value)))
            (if (not opened)
                nil
              (proof-search-let
                ((expanded (proof-search-equality-right opened))
                 (typed (proof-search-boolean lib expanded)))
                (if typed
                    (library-library-transport-argument lib typed opened 1)
                  nil)))))))))

(defun proof-search-argument-differences (left right position)
  (if (or (endp left) (endp right))
      nil
    (let ((rest (proof-search-argument-differences (cdr left) (cdr right)
                                                  (1+ position))))
      (if (equal (car left) (car right))
          rest
        (cons (list position (car left) (car right)) rest)))))

(defund proof-search-argument-assumptions (proof tests)
  (if (endp tests)
      nil
    (proof-search-let
      ((assumption (proof-proof-assume proof (caar tests) (cadar tests)))
       (rest (proof-search-argument-assumptions proof (cdr tests))))
      (cons assumption rest))))

(defun proof-search-rewrite-value-branch (proof step equality template)
  (proof-search-let ((reverse (proof-proof-symmetric proof equality)))
    (proof-proof-rewrite-result proof step reverse template *proof-result*)))

(defun proof-search-missing-to-nil (result)
  (let ((value (car result)))
    (if (terms-unproved-p value)
        (cons nil (cdr result))
      result)))

(defund proof-search-assume (search term holds)
  (proof-proof-assume (proof-search-proof search) term holds))

(defund proof-search-beta (search term)
  (proof-proof-beta (proof-search-proof search) term))

(defund proof-search-start-reduction (search evidence)
  (let ((rewriting (proof-search-search-rewriting search)))
    (book-logic-reducer-init
     (proof-search-search-lib search) evidence :none (not rewriting)
     100 160 (if rewriting (list t) nil) (proof-search-search-logical search))))

(defund proof-search-primitive (reducer term)
  (book-logic-reducer-known reducer term))

(defund proof-search-main-reduction (search reducer term evidence known)
  (if (proof-search-search-rewriting search)
      (proof-search-rewrite-reduction 1000000 reducer term nil evidence known search)
    (cons (car (book-logic-reducer-reduce reducer term nil)) search)))

(defund proof-search-expose-cons-type (search formula evidence)
  (proof-search-library-result
   (proper-lists-expose-cons-type (proof-search-search-lib search) formula evidence)
   search))

(defund proof-search-reflexive (search term)
  (proof-proof-reflexive (proof-search-proof search) term))

(defund proof-search-rewrite-argument (search chain change position)
  (proof-proof-rewrite (proof-search-proof search) chain change (list 1 2 position)))

(defun proof-search-number-if-p (search template)
  (let ((proof (proof-search-proof search)))
    (and (equal template (list *library-numberp* *proof-result*))
         (member-eq (proof-proof-kind proof) (list :slice :book))
         (assoc-equal *lemmas-number-if* (proof-proof-facts proof)))))

(defun proof-search-join-value-branches (search value template yes no number-if)
  (let ((proof (proof-search-proof search))
        (lib (proof-search-search-lib search))
        (test (cadr value)))
    (cond
      ((not number-if)
       (proof-search-let
         ((true-eq (proof-proof-if-true proof value))
          (yes (proof-search-rewrite-value-branch proof yes true-eq template))
          (false-eq (proof-proof-if-false proof value))
          (no (proof-search-rewrite-value-branch proof no false-eq template)))
         (proof-proof-cases proof test yes no)))
      ((and (not (member-equal (proof-neg test) (proof-step-clause yes)))
            (not (member-equal test (proof-step-clause no))))
       (library-library-cite lib "NUMBER-IF" (cdr value) (list yes no)))
      (t
       (proof-search-let
         ((true-eq (proof-proof-if-true proof value))
          (yes (library-library-transport-argument lib yes true-eq 1))
          (false-eq (proof-proof-if-false proof value))
          (no (library-library-transport-argument lib no false-eq 1)))
         (proof-proof-cases proof test yes no))))))

(mutual-recursion
 (defun proof-search-search-prove-loop (fuel search formula evidence splits)
   (declare (xargs :measure (nfix fuel)))
   (cond
     ((zp fuel) (cons '(:failure "fuel" "proof-search-search-prove-loop") search))
     ((<= (proof-search-search-budget search) 0)
      (cons *terms-unproved* search))
     (t
      (let ((search (proof-search-search-with-budget
                     search (1- (proof-search-search-budget search)))))
        (proof-search-let-in search ((small (book-logic-within-size formula 300)))
          (if (not small)
              (cons *terms-unproved* search)
            (proof-search-let-in search
              ((literals (proof-search-evidence-literals evidence)))
              (let ((pending (proof-search-search-pending search))
                    (key (list formula literals splits)))
                (if (member-equal key pending)
                    (cons *terms-unproved*
                          search)
                  (proof-search-with-result step search
                    (proof-search-search-loop
                     (1- fuel) (proof-search-search-with-pending
                                search (cons key pending))
                     formula evidence splits)
                    (cons step (proof-search-search-with-pending search pending))))))))))))

 (defun proof-search-search-loop (fuel search formula evidence splits)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-search-loop") search)
     (proof-search-let-in search
       ((evidence (proof-search-search-evidence search evidence))
        (known (proof-search-evidence-index evidence nil t))
        (found (proof-search-known-formula search formula known)))
       (if found
           (cons found search)
         (proof-search-with-result opened search
           (proof-search-search-lambda (1- fuel) search formula evidence splits)
           (if opened
               (cons opened search)
             (proof-search-with-result implied search
               (proof-search-search-implication (1- fuel) search formula evidence splits)
               (if implied
                   (cons implied search)
                 (proof-search-search-after-implication
                  (1- fuel) search formula evidence known splits)))))))))

 (defun proof-search-search-lambda (fuel search formula evidence splits)
   (declare (xargs :measure (nfix fuel)))
   (cond
     ((zp fuel) (cons '(:failure "fuel" "proof-search-search-lambda") search))
     ((or (not (proof-search-search-logical search))
          (not (proof-compound formula))) (cons nil search))
     ((endp formula) (cons '(:failure "failure" "") search))
     ((not (proof-compound (car formula))) (cons nil search))
     (t
      (proof-search-let-in search
        ((opened (proof-search-beta search formula))
         (target (proof-search-equality-right opened)))
        (proof-search-missing-to-nil
         (proof-search-with-result step search
           (proof-search-search-prove-loop (1- fuel) search target evidence splits)
           (cons (if (failure-p step)
                     step
                   (proof-proof-transport (proof-search-proof search) step opened))
                 search)))))))

 (defun proof-search-search-implication (fuel search formula evidence splits)
   (declare (xargs :measure (nfix fuel)))
   (cond
     ((zp fuel) (cons '(:failure "fuel" "proof-search-search-implication") search))
     ((not (proof-is-call formula *library-implies*)) (cons nil search))
     ((endp (cdr formula)) (cons '(:failure "failure" "") search))
     (t
      (proof-search-let-in search
        ((premise (proof-search-assume search (cadr formula) t)))
        (if (endp (cddr formula))
            (cons '(:failure "failure" "") search)
          (proof-search-missing-to-nil
           (proof-search-with-result consequence search
             (proof-search-search-prove-loop (1- fuel) search (caddr formula)
                                             (append evidence (list premise)) splits)
             (cons (if (failure-p consequence)
                       consequence
                     (witnesses-prove-implication (proof-search-search-lib search)
                                                   formula premise consequence))
                   search))))))))

 (defun proof-search-search-after-implication (fuel search formula evidence known splits)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-search-after-implication") search)
     (proof-search-let-in search ((conditional (proof-search-conjunction-p formula)))
       (if conditional
           (proof-search-with-result test search
             (proof-search-search-prove-loop (1- fuel) search (cadr formula) evidence splits)
             (if (failure-p test)
                 (cons test search)
               (proof-search-with-result branch search
                 (proof-search-search-prove-loop (1- fuel) search (caddr formula)
                                                 (append evidence (list test)) splits)
                 (cons (if (failure-p branch)
                           branch
                         (proof-search-transport-selected
                          (proof-search-proof search) formula test branch))
                       search))))
         (proof-search-with-result proof search
           (proof-search-search-evidence-implication search formula evidence evidence known)
           (if proof
               (cons proof search)
             (proof-search-with-result indexed search
               (proof-search-index-with-premise
                1000000 search formula evidence known nil nil)
               (if (terms-unproved-p indexed)
                   (proof-search-search-after-index
                    (1- fuel) search formula evidence known splits)
                 (cons indexed search)))))))))

 (defun proof-search-search-after-index (fuel search formula evidence known splits)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-search-after-index") search)
     (proof-search-with-result direct search
       (if (proof-search-search-logical search)
           (proof-search-search-logical-formula-loop
            (1- fuel) search formula evidence known)
         (cons nil search))
       (if direct
           (cons direct search)
         (proof-search-with-result proper search
           (if (and (proof-search-search-logical search)
                    (proof-is-call formula *proper-lists-true-list*))
               (proof-search-missing-to-nil
                (proof-search-search-premise search formula evidence known))
             (cons nil search))
           (if proper
               (cons proper search)
             (proof-search-search-reduction
              (1- fuel) search formula evidence known splits)))))))

 (defun proof-search-search-reduction (fuel search formula evidence known splits)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-search-reduction") search)
     (proof-search-let-in search
       ((reducer (proof-search-start-reduction search evidence))
        (primitive (proof-search-primitive reducer formula)))
       (if primitive
           (cons primitive search)
         (proof-search-with-result reduced search
           (proof-search-main-reduction search reducer formula evidence known)
           (proof-search-let-in search
             ((target (cond ((failure-p reduced) reduced)
                            (reduced (proof-search-equality-right reduced))
                            (t formula))))
             (proof-search-with-result direct search
               (proof-search-reduced-formula search target reduced known evidence)
               (if direct
                   (cons direct search)
                 (proof-search-search-after-reduction
                  (1- fuel) search formula target reduced evidence known splits)))))))))

 (defun proof-search-search-after-reduction
     (fuel search formula target reduced evidence known splits)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-search-after-reduction") search)
     (proof-search-with-result recovered search
       (if (equal target formula)
           (cons nil search)
         (proof-search-missing-to-nil
          (proof-search-with-result step search
            (proof-search-search-prove-loop (1- fuel) search target evidence 0)
            (cons (if (failure-p step)
                      step
                    (proof-proof-transport (proof-search-proof search) step reduced))
                  search))))
       (if recovered
           (cons recovered search)
         (proof-search-search-split (1- fuel) search formula target evidence known splits)))))

 (defun proof-search-search-split (fuel search formula target evidence known splits)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-search-split") search)
     (proof-search-let-in search
       ((selected (and (< 0 splits)
                       (proof-search-splitting-test search target formula evidence))))
       (let ((test (cdr selected)))
         (if (and selected (not (assoc-equal test known))
                  (not (assoc-equal (proof-neg test) known)))
             (proof-search-let-in search
               ((assumption (proof-search-assume search test t)))
               (proof-search-with-result yes search
                 (proof-search-search-prove-loop (1- fuel) search formula
                                                 (append evidence (list assumption))
                                                 (1- splits))
                 (if (failure-p yes)
                     (cons yes search)
                   (proof-search-let-in search
                     ((assumption (proof-search-assume search test nil)))
                     (proof-search-with-result no search
                       (proof-search-search-prove-loop (1- fuel) search formula
                                                       (append evidence (list assumption))
                                                       (1- splits))
                       (cons (if (failure-p no)
                                 no
                               (proof-proof-cases (proof-search-proof search) test yes no))
                             search))))))
           (cons *terms-unproved*
                 search))))))

 (defun proof-search-search-logical-formula-loop (fuel search formula evidence known)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-search-logical-formula-loop") search)
     (proof-search-with-result computed search
       (proof-search-search-computed-premise search formula known)
       (if computed
           (cons computed search)
         (proof-search-with-result preserved search
           (if (and (proof-compound formula) (equal (len formula) 2)
                    (proof-compound (cadr formula)))
               (proof-search-preserve-type
                (1- fuel) search
                (list-preservation-preserve-list-type
                 (proof-search-search-lib search) formula)
                evidence)
             (cons nil search))
           (if preserved
               (cons preserved search)
             (proof-search-with-result exposed search
               (proof-search-expose-cons-type search formula evidence)
               (cond
                 ((failure-p exposed) (cons exposed search))
                 (t
                  (proof-search-with-result lifted search
                    (if exposed
                        (proof-search-missing-to-nil
                         (proof-search-search-exposed-formula
                          (1- fuel) search formula evidence exposed))
                      (cons nil search))
                    (if lifted
                        (cons lifted search)
                      (let ((typed (proof-search-boolean-formula search formula evidence)))
                        (if typed
                            (cons typed search)
                          (proof-search-logical-equality
                           (1- fuel) search formula evidence known))))))))))))))

 (defun proof-search-preserve-type (fuel search result evidence)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-preserve-type") search)
     (proof-search-with-result value search
       (proof-search-library-result result search)
       (if (and (consp value) (eq (car value) :call))
           (proof-search-with-result answer search
             (proof-search-search-prove-loop (1- fuel) search (cadr value) evidence 0)
             (proof-search-preserve-type
              (1- fuel) search
              (list-preservation-preserve-list-type-resume
               (proof-search-search-lib search) (cadddr value) answer)
              evidence))
         (cons value search)))))

 (defun proof-search-search-exposed-formula (fuel search formula evidence exposed)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-search-exposed-formula") search)
     (proof-search-let-in search ((target (proof-search-equality-right exposed)))
       (let ((same (proof-is-call target (car formula))))
         (if (and same (endp (cdr target)))
             (cons '(:failure "failure" "") search)
           (proof-search-with-result proof search
             (if (and same (proof-is-call (cadr target) *proof-if*))
                 (proof-search-search-by-value
                  (1- fuel) search (cadr target) (list (car target) *proof-result*)
                  evidence nil)
               (proof-search-search-prove-loop (1- fuel) search target evidence 0))
             (cons (if (failure-p proof)
                       proof
                     (proof-proof-transport (proof-search-proof search) proof exposed))
                   search)))))))

 (defun proof-search-search-by-value (fuel search value template evidence tests)
   (declare (xargs :measure (nfix fuel)))
   (cond
     ((zp fuel) (cons '(:failure "fuel" "proof-search-search-by-value") search))
     ((proof-is-call value *proof-if*)
      (if (not (equal (len (cdr value)) 3))
          (cons *terms-invalid-proof-arity* search)
        (let ((test (cadr value))
              (number-if (proof-search-number-if-p search template)))
          (proof-search-with-result yes search
            (proof-search-search-by-value
             (1- fuel) search (caddr value) template evidence
             (append tests (list (list test t))))
            (if (failure-p yes)
                (cons yes search)
              (proof-search-with-result no search
                (proof-search-search-by-value
                 (1- fuel) search (cadddr value) template evidence
                 (append tests (list (list test nil))))
                (if (failure-p no)
                    (cons no search)
                  (cons (proof-search-join-value-branches search value template
                                                         yes no number-if)
                        search))))))))
     ((and (proof-compound value) (endp value))
      (cons '(:failure "failure" "") search))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-search-let-in search
        ((equality (proof-search-beta search value))
         (opened (proof-search-equality-right equality)))
        (proof-search-with-result step search
          (proof-search-search-by-value (1- fuel) search opened template evidence tests)
          (cons (if (failure-p step)
                    step
                  (proof-search-rewrite-value-branch (proof-search-proof search)
                                                      step equality template))
                search))))
     (t
      (proof-search-with-result step search
        (proof-search-search-logical-formula-branch-in
         (1- fuel) value tests search (car template) evidence)
        (if (failure-p step)
            (cons step search)
          (proof-search-let-in search
            ((actual (proof-step-first step))
             (expected (proof-subst template (list (cons *proof-result* value)))))
            (cons (if (equal actual expected) step '(:failure "failure" ""))
                  search)))))))

 (defun proof-search-search-logical-formula-branch-in
     (fuel value tests search predicate evidence)
   (declare (xargs :measure (nfix fuel)))
   (if (zp fuel)
       (cons '(:failure "fuel" "proof-search-search-logical-formula-branch-in") search)
     (proof-search-let-in search
       ((rulers (proof-search-argument-assumptions (proof-search-proof search) tests)))
       (proof-search-search-prove-loop (1- fuel) search (list predicate value)
                                       (append evidence rulers) 0))))

 (defun proof-search-logical-equality (fuel search formula evidence known)
   (declare (xargs :measure (nfix fuel)))
   (cond
     ((zp fuel) (cons '(:failure "fuel" "proof-search-logical-equality") search))
     ((not (proof-is-call formula *proof-equal*)) (cons nil search))
     ((not (equal (len (cdr formula)) 2))
      (cons *terms-invalid-proof-arity* search))
     (t
      (let* ((left (cadr formula))
             (right (caddr formula))
             (reverse (cdr (assoc-equal (proof-eq right left) known))))
        (cond
          (reverse (cons (proof-proof-symmetric (proof-search-proof search) reverse) search))
          ((or (not (proof-compound left)) (proof-is-call left *proof-quote*)
               (not (proof-compound right))) (cons nil search))
          ((or (endp left) (endp right)) (cons '(:failure "failure" "") search))
          ((or (not (equal (car left) (car right)))
               (not (equal (len left) (len right)))) (cons nil search))
          (t
           (let ((differences (proof-search-argument-differences (cdr left) (cdr right) 1)))
             (proof-search-with-result fixed search
               (if (and (consp differences) (endp (cdr differences)))
                   (let ((argument (car differences)))
                     (proof-search-search-fixed-arguments
                      search left right (car argument) (cadr argument) (caddr argument)
                      evidence known))
                 (cons nil search))
               (if fixed
                   (cons fixed search)
                 (proof-search-let-in search
                   ((chain (proof-search-reflexive search left)))
                   (proof-search-logical-rewrite
                    (1- fuel) search chain differences evidence)))))))))))

 (defun proof-search-logical-rewrite (fuel search chain differences evidence)
   (declare (xargs :measure (nfix fuel)))
   (cond
     ((zp fuel) (cons '(:failure "fuel" "proof-search-logical-rewrite") search))
     ((endp differences) (cons (proof-proof-tidy (proof-search-proof search) chain) search))
     (t
      (let ((argument (car differences)))
        (proof-search-with-result change search
          (proof-search-search-prove-loop (1- fuel) search
                                          (proof-eq (cadr argument) (caddr argument))
                                          evidence 0)
          (cond
            ((terms-unproved-p change) (cons nil search))
            ((failure-p change) (cons change search))
            (t
             (proof-search-let-in search
               ((rewritten (proof-search-rewrite-argument
                            search chain change (car argument))))
               (proof-search-logical-rewrite
                (1- fuel) search rewritten (cdr differences) evidence))))))))))

(defun proof-search-search-prove (search formula evidence splits)
  (proof-search-search-prove-loop 1000000 search formula evidence splits))

(defun proof-search-selector-substitution (actuals next-args environment)
  (if (or (endp actuals) (endp next-args))
      nil
    (let ((old (car actuals)))
      (if (proof-compound old)
          (proof-search-selector-substitution (cdr actuals) (cdr next-args) environment)
        (proof-search-let
          ((new (proof-subst (car next-args) environment))
           (rest (proof-search-selector-substitution
                  (cdr actuals) (cdr next-args) environment)))
          (if (equal old new) rest (cons (list old new) rest)))))))

(defun proof-search-record-selector-plan (changes substitution plans)
  (if (endp changes)
      plans
    (let* ((variable (caar changes))
           (smaller (cadar changes)))
      (proof-search-record-selector-plan
       (cdr changes) substitution
       (if (or (equal smaller (list *library-car* variable))
               (equal smaller (list *library-cdr* variable)))
           (table-put plans variable
                        (table-put (cdr (assoc-equal variable plans))
                                     substitution smaller))
         plans)))))

(defun proof-search-invocation-plans (calls actuals environment plans)
  (if (endp calls)
      plans
    (proof-search-let
      ((substitution (proof-search-selector-substitution actuals (car calls) environment)))
      (proof-search-invocation-plans
       (cdr calls) actuals environment
       (proof-search-record-selector-plan substitution substitution plans)))))

(defun proof-search-term-plans (index term plans)
  (proof-search-let ((function (proof-search-head term)))
    (let* ((proof (library-library-proof (proof-search-fact-index-lib index)))
           (definition (assoc-equal function (proof-proof-definitions proof)))
           (actuals (cdr term)))
      (cond
        ((not definition) plans)
        ((not (equal (len (cdr definition)) 2))
         *terms-invalid-proof-arity*)
        ((not (no-duplicatesp-equal actuals)) plans)
        (t
         (let ((environment (proof-search-zip-bindings (cadr definition) actuals nil)))
           (proof-search-let
             ((calls (proof-search-fact-index-recursive-arguments index function)))
             (proof-search-invocation-plans calls actuals environment plans))))))))

(defun proof-search-induction-plans-loop (fuel index terms plans)
  (declare (xargs :measure (nfix fuel)))
  (cond
    ((zp fuel) '(:failure "fuel" "proof-search-induction-plans-loop"))
    ((endp terms) plans)
    (t
     (let ((term (car terms)))
       (if (or (not (proof-compound term)) (proof-is-call term *proof-quote*))
           (proof-search-induction-plans-loop (1- fuel) index (cdr terms) plans)
         (proof-search-let ((updated (proof-search-term-plans index term plans)))
           (proof-search-induction-plans-loop
            (1- fuel) index (append (cdr term) (cdr terms)) updated)))))))

(defun proof-search-induction-plans (index formula)
  (proof-search-induction-plans-loop 1000000 index (list formula) nil))

(defun proof-search-logical-selector-goal (formula variable)
  (proof-search-let ((goal (proof-search-conclusion formula)))
    (if (proof-is-call goal *proof-equal*)
        (if (not (equal (len (cdr goal)) 2))
            *terms-invalid-proof-arity*
          (let ((left (cadr goal))
                (right (caddr goal)))
            (cond ((or (equal variable left) (equal variable right)) t)
                  ((or (not (proof-compound left)) (not (proof-compound right))) nil)
                  ((or (endp left) (endp right)) '(:failure "failure" ""))
                  (t (and (equal (car left) (car right))
                          (equal (len left) 2) (equal (len right) 2)
                          (or (equal variable (cadr left))
                              (equal variable (cadr right))))))))
      (proof-search-let ((operator (proof-search-head goal)))
        (and operator (equal (len goal) 2) (proof-compound (cadr goal)))))))

(defun proof-search-new-attempt (search budget rewriting logical)
  (proof-search-search-init (proof-search-search-lib search)
                            (proof-search-search-index search)
                            budget rewriting logical))

(defun proof-search-run-attempt (search formula evidence splits budget rewriting logical)
  (proof-search-search-prove (proof-search-new-attempt search budget rewriting logical)
                             formula evidence splits))

(defun proof-search-search-result-library (result)
  (cons (car result) (proof-search-search-lib (cdr result))))

(defun proof-search-selector-extras (bindings variable)
  (if (endp bindings)
      nil
    (let ((binding (car bindings)))
      (if (not (equal (len binding) 2))
          *terms-invalid-proof-arity*
        (proof-search-let ((rest (proof-search-selector-extras (cdr bindings) variable)))
          (if (equal (car binding) variable)
              rest
            (cons binding rest)))))))

(defund proof-search-selector-hypothesis (lib induction variable cons-step substitution)
  (let ((bindings (car substitution))
        (smaller (cdr substitution))
        (proof (library-library-proof lib)))
    (if (endp smaller)
        '(:failure "failure" "")
      (proof-search-let
        ((natural (library-library-builtin lib
                                           (if (equal (car smaller) *library-car*) 2 3)
                                           variable))
         (descends (proof-proof-discharge proof natural cons-step))
         (extras (proof-search-selector-extras bindings variable)))
        (book-logic-tree-induction-at induction smaller descends extras)))))

(defun proof-search-selector-hypotheses (lib induction variable cons-step substitutions)
  (declare (xargs :measure (acl2-count substitutions)))
  (if (endp substitutions)
      (cons induction nil)
    (proof-search-let
      ((instance (proof-search-selector-hypothesis lib induction variable cons-step
                                                   (car substitutions)))
       (step (car instance))
       (rest (proof-search-selector-hypotheses lib (cdr instance) variable
                                               cons-step (cdr substitutions))))
      (cons (car rest) (cons step (cdr rest))))))

(defun proof-search-selector-initial-hypotheses (lib formula variable cons-step logical)
  (proof-search-let ((goal (proof-search-conclusion formula)))
    (if (and logical (proof-is-call goal *proof-equal*)
             (member-equal variable (cdr goal)))
        (let ((proof (library-library-proof lib)))
          (proof-search-let
            ((law (library-library-axiom lib "CAR-CDR-ELIM" (list variable)))
             (rebuilt (proof-proof-modus-ponens proof law cons-step))
             (symmetric (proof-proof-symmetric proof rebuilt)))
            (list cons-step symmetric)))
      (list cons-step))))

(defun proof-search-selector-induction-step (search formula variable substitutions
                                                   logical splits cons-test base)
  (let ((lib (proof-search-search-lib search)))
    (proof-search-let-in search
      ((cons-step (proof-proof-assume (library-library-proof lib) cons-test t))
       (induction (book-logic-tree-induction-init lib formula variable))
       (initial (proof-search-selector-initial-hypotheses lib formula variable
                                                         cons-step logical))
       (hypotheses (proof-search-selector-hypotheses lib induction variable
                                                     cons-step substitutions)))
      (proof-search-with-result step search
        (proof-search-run-attempt search formula (append initial (cdr hypotheses))
                                  splits (if logical 58 48) t logical)
        (proof-search-let-in search
          ((branch step)
           (cases (proof-proof-cases (proof-search-proof search) cons-test branch base)))
          (cons (book-logic-tree-induction-finish (car hypotheses) cases) search))))))

(defund proof-search-selector-induction-candidate (search formula variable substitutions
                                                        logical)
  (let ((cons-test (list *proof-consp* variable))
        (splits (if logical 3 1)))
    (proof-search-let-in search
      ((atom-step (proof-proof-assume (proof-search-proof search) cons-test nil)))
      (proof-search-with-result base search
        (proof-search-run-attempt search formula (list atom-step)
                                  splits (if logical 44 48) t logical)
        (if (failure-p base)
            (cons base search)
          (proof-search-selector-induction-step search formula variable substitutions
                                                logical splits cons-test base))))))

(defun proof-search-selector-induction (search formula plans logical)
  (declare (xargs :measure (acl2-count plans)))
  (if (endp plans)
      (cons *terms-unproved* search)
    (let ((variable (caar plans)))
      (proof-search-let-in search
        ((eligible (if logical (proof-search-logical-selector-goal formula variable) t)))
        (if (not eligible)
            (proof-search-selector-induction search formula (cdr plans) logical)
          (proof-search-with-result value search
            (proof-search-selector-induction-candidate search formula variable
                                                       (cdar plans) logical)
            (if (terms-unproved-p value)
                (proof-search-selector-induction search formula (cdr plans) logical)
              (cons value search))))))))

(defun proof-search-theorem-tactic (fuel search result tactic)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (cons '(:failure "fuel" "proof-search-theorem-tactic") search)
    (proof-search-with-result value search
      (proof-search-library-result result search)
      (if (and (consp value) (eq (car value) :call))
          (proof-search-with-result answer search
            (proof-search-run-attempt search (cadr value) (caddr value)
                                      (if (eq tactic :algebra) 3 2)
                                      (if (eq tactic :algebra) 52 38) nil t)
            (let* ((lib (proof-search-search-lib search))
                   (continuation (cadddr value))
                   (resumed (if (eq tactic :algebra)
                                (list-algebra-list-algebra-resume lib continuation answer)
                              (list-equivalence-prove-list-equivalence-resume
                               lib continuation answer))))
              (proof-search-theorem-tactic (1- fuel) search resumed tactic)))
        (cons value search)))))

(defun proof-search-theorem-list-equivalence (search formula)
  (proof-search-theorem-tactic
   1000000 search
   (list-equivalence-prove-list-equivalence (proof-search-search-lib search) formula)
   :equivalence))

(defun proof-search-theorem-list-algebra (search formula)
  (proof-search-theorem-tactic
   1000000 search
   (list-algebra-list-algebra (proof-search-search-lib search) formula) :algebra))

(defun proof-search-radix-induction-step (search formula candidate base)
  (proof-search-with-result prepared search
    (proof-search-library-result
     (quotient-proofs-prove-radix-induction (proof-search-search-lib search)
                                           formula candidate)
     search)
    (if (or (not prepared) (failure-p prepared))
        (cons prepared search)
      (proof-search-with-result step search
        (proof-search-run-attempt search formula (cadr prepared) 2 38 nil t)
        (cons (if (failure-p step)
                  step
                (quotient-proofs-prove-radix-induction-finish
                 (proof-search-search-lib search) candidate (car prepared) base step))
              search)))))

(defund proof-search-radix-induction-candidate (search formula candidate)
  (proof-search-let-in search
    ((evidence (quotient-proofs-prove-radix-induction-base
                (proof-search-search-lib search) candidate)))
    (proof-search-with-result base search
      (proof-search-run-attempt search formula evidence 2 38 nil t)
      (if (failure-p base)
          (cons base search)
        (proof-search-radix-induction-step search formula candidate base)))))

(defund proof-search-next-radix-candidate (search cursor)
  (quotient-proofs-radix-calls-next (proof-search-search-lib search) cursor))

(defun proof-search-radix-induction (fuel search formula cursor)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      (cons '(:failure "fuel" "proof-search-radix-induction") search)
    (proof-search-let-in search
      ((next (proof-search-next-radix-candidate search cursor)))
      (if (not next)
          (cons *terms-unproved* search)
        (proof-search-with-result step search
          (proof-search-radix-induction-candidate search formula (car next))
          (if (or (not step) (terms-unproved-p step))
              (proof-search-radix-induction (1- fuel) search formula (cdr next))
            (cons step search)))))))

(defun proof-search-theorem-induction (search formula)
  (proof-search-let-in search
    ((plans (proof-search-induction-plans (proof-search-search-index search) formula)))
    (proof-search-with-result selected search
      (proof-search-missing-to-nil
       (proof-search-selector-induction search formula plans nil))
      (if selected
          (cons selected search)
        (proof-search-let-in search ((small (book-logic-within-size formula 90)))
          (proof-search-with-result logical search
            (if small
                (proof-search-missing-to-nil
                 (proof-search-selector-induction search formula plans t))
              (cons nil search))
            (if logical
                (cons logical search)
              (proof-search-with-result radix search
                (proof-search-radix-induction 1000000 search formula
                                              (quotient-proofs-radix-calls-start formula))
                (cons (if (terms-unproved-p radix)
                          *terms-unproved*
                        radix)
                      search)))))))))

(defun proof-search-theorem-after-algebra (search formula)
  (proof-search-let-in search ((small (book-logic-within-size formula 110)))
    (proof-search-with-result direct search
      (if small
          (proof-search-missing-to-nil
           (proof-search-run-attempt search formula nil 3 42 nil t))
        (cons nil search))
      (if direct
          (cons direct search)
        (proof-search-with-result equivalent search
          (proof-search-missing-to-nil (proof-search-theorem-list-equivalence search formula))
          (if equivalent
              (cons equivalent search)
            (proof-search-theorem-induction search formula)))))))

(defun proof-search-theorem-list-tactics (search formula)
  (proof-search-with-result combined search
    (proof-search-missing-to-nil
     (proof-search-library-result
      (list-preservation-combine-list-equation (proof-search-search-lib search) formula)
      search))
    (if combined
        (cons combined search)
      (proof-search-with-result algebra search
        (proof-search-missing-to-nil (proof-search-theorem-list-algebra search formula))
        (if algebra
            (cons algebra search)
          (proof-search-theorem-after-algebra search formula))))))

(defun proof-search-theorem-after-basic (search formula)
  (proof-search-with-result rewritten search
    (proof-search-missing-to-nil
     (proof-search-run-attempt search formula nil 2 48 t nil))
    (if rewritten
        (cons rewritten search)
      (proof-search-with-result ordinal search
        (proof-search-library-result
         (lexicographic-ordinal-constructor-equation-with-library
          (proof-search-search-lib search) formula)
         search)
        (if ordinal
            (cons ordinal search)
          (proof-search-with-result half-order search
            (proof-search-library-result
             (halved-counters-halved-counter-comparison
              (proof-search-search-lib search) formula)
             search)
            (if half-order
                (cons half-order search)
              (proof-search-theorem-list-tactics search formula))))))))

(defun proof-search-theorem (search formula)
  (proof-search-with-result basic search
    (proof-search-run-attempt search formula nil 2 48 nil nil)
    (if (not (terms-unproved-p basic))
        (cons basic search)
      (proof-search-let-in search ((small (book-logic-within-size formula 140)))
        (if small
            (proof-search-theorem-after-basic search formula)
          (proof-search-with-result equivalent search
            (proof-search-theorem-list-equivalence search formula)
            (cons (if (terms-unproved-p equivalent)
                      basic
                    equivalent)
                  search)))))))

(defun proof-search-prove-theorem (lib index formula)
  (proof-search-search-result-library
   (proof-search-theorem (proof-search-search-init lib index 48 nil nil) formula)))
