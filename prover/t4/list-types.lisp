(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-list-types-eq* (proof-cl "EQ"))
(defconst *t4-list-types-endp* (proof-cl "ENDP"))
(defconst *t4-list-types-acons* (proof-cl "ACONS"))
(defconst *t4-list-types-append* (proof-sym "BINARY-APPEND" "ACL2"))
(defconst *t4-list-types-double* (proof-sym "DOUBLE-REWRITE" "ACL2"))

(defun t4-list-types-request-p (value)
  (eq (car value) :t4-list-types-request))

(defun t4-list-types-request-operation (request)
  (cadr request))

(defun t4-list-types-request-library (request)
  (caddr request))

(defun t4-list-types-request-arguments (request)
  (cadddr request))

(defund t4-list-types-library (context)
  (car context))

(defund t4-list-types-evidence (context)
  (cadr context))

(defund t4-list-types-proof (context)
  (library-library-proof (t4-list-types-library context)))

(defund t4-list-types-with-evidence (context evidence)
  (list (t4-list-types-library context) evidence (caddr context) (cadddr context)))

(defund t4-list-types-with-library (context lib)
  (let ((evidence (t4-list-types-evidence context))
        (previous (t4-list-types-library context)))
    (list lib (if (and evidence (not (equal previous lib))
                       (equal (t4-structural-evidence-proof evidence) previous))
                  (t4-structural-evidence-with-proof evidence lib)
                evidence)
          (caddr context) (cadddr context))))

(defund t4-list-types-reply (context reply)
  (let* ((evidence (or (caddr reply) (t4-list-types-evidence context)))
         (context (t4-list-types-with-evidence context evidence))
         (context (t4-list-types-with-library context (cadr reply))))
    (cons (car reply) context)))

(defund t4-list-types-ask (context operation arguments)
  (let* ((lib (t4-list-types-library context))
         (request (list :t4-list-types-request operation lib arguments))
         (replies (cadddr context)))
    (if (eq (caddr context) :ordered)
        (if (endp replies)
            (cons request context)
          (let ((context (list lib (t4-list-types-evidence context) :ordered (cdr replies)))
                (reply (car replies)))
            (cond ((failure-p reply) (cons reply context))
                  ((member-eq operation '(:use-arithmetic :prove))
                   (t4-list-types-reply context (list (car reply) (cdr reply) nil)))
                  ((failure-p (car reply))
                   (t4-list-types-reply context (list (car reply) (cdr reply) nil)))
                  (t (t4-list-types-reply context (list (caar reply) (cdr reply) (cdar reply)))))))
      (let ((answer (assoc-equal request replies)))
        (if answer
            (t4-list-types-reply context (cdr answer))
          (cons request context))))))

; A result carries the Library, Evidence, and unused replies.
; Failures and requests retain those fields for the next proof operation.
(defmacro t4-list-types-let (bindings body)
  (if (endp bindings)
      body
    (let* ((binding (car bindings))
           (name (car binding))
           (form (cadr binding))
           (kind (caddr binding))
           (next `(t4-list-types-let ,(cdr bindings) ,body)))
      (case kind
        (:result
         `(let* ((,name ,form)
                 (context (cdr ,name))
                 (,name (car ,name)))
            (if (or (failure-p ,name) (t4-list-types-request-p ,name))
                (cons ,name context)
              ,next)))
        (:library
         `(let ((,name ,form))
            (if (failure-p ,name)
                (cons ,name context)
              (let* ((context (t4-list-types-with-library context (cdr ,name)))
                     (,name (car ,name)))
                (if (failure-p ,name) (cons ,name context) ,next)))))
        (:evidence
         `(let ((,name ,form))
            (if (failure-p ,name)
                (cons ,name context)
              (let* ((context (t4-list-types-with-evidence context (caddr ,name)))
                     (context (t4-list-types-with-library context (cadr ,name)))
                     (,name (car ,name)))
                (if (failure-p ,name) (cons ,name context) ,next)))))
        (otherwise
         `(let ((,name ,form))
            (if (failure-p ,name) (cons ,name context) ,next)))))))

(defun t4-list-types-search-miss-p (value)
  (and (failure-p value) (member-equal (cadr value) '("SearchMiss" "value"))))

(defund t4-list-types-lookup (context operation term)
  (t4-list-types-ask context operation (list term (t4-list-types-evidence context))))

(defund t4-list-types-prove (context term evidence definitions)
  (t4-list-types-ask context :prove (list term evidence definitions)))

(defund t4-list-types-definitions (context)
  (proof-proof-definitions (t4-list-types-proof context)))

(defund t4-list-types-reverse-argument (context step equality)
  (let ((proof (t4-list-types-proof context)))
    (t4-list-types-let
     ((reversed (proof-proof-symmetric proof equality)))
     (cons (proof-proof-rewrite proof step reversed '(1 1)) context))))

(defun t4-list-types-cdr-path-tail (arguments obj)
  (declare (xargs :measure (acl2-count arguments)))
  (if (endp arguments)
      '(:failure "failure" "")
    (let ((value (car arguments)))
      (if (proof-is-call value *library-cdr*)
          (t4-list-types-cdr-path-tail (cdr value) obj)
        (equal value obj)))))

(defun t4-list-types-cdr-path (value obj)
  (and (proof-is-call value *library-cdr*)
       (t4-list-types-cdr-path-tail (cdr value) obj)))

(mutual-recursion
 (defun t4-list-types-type-value (n context predicate value mode active projection)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t4-list-types-type-value") context)
     (let ((expected (list predicate value)))
       (t4-list-types-let
        ((known (t4-list-types-lookup context :known expected) :result)
         (known (if known (cons known context)
                  (t4-list-types-lookup context :fact-proof expected)) :result))
        (let* ((lib (t4-list-types-library context))
               (proof (t4-list-types-proof context))
               (definitions (t4-list-types-definitions context))
               (defined (assoc-equal predicate definitions)))
          (cond
           (known (cons known context))
           ((proof-is-call value *proof-quote*)
            (t4-list-types-prove context expected nil
              (and defined (list predicate *t4-structural-atom* *t4-list-types-endp*
                                 *t4-list-types-eq* *proof-not*))))
           ((and (proof-is-call value *t4-list-types-acons*)
                 (assoc-equal (car value) definitions))
            (t4-list-types-let
             ((equation (proof-proof-unfold proof value))
              (body (proof-rewritten-term equation))
              (step (t4-list-types-nested (1- n) predicate body context mode active projection)
                    :result))
             (t4-list-types-reverse-argument context step equation)))
           (t
            (t4-list-types-let
             ((equation (if (and (proof-is-call value *proof-cons*) defined)
                            (let ((result (t4-syntax-lists-constructed-view lib expected value)))
                              (if (failure-p result) (cons result context)
                                (cons (car result) (t4-list-types-with-library context (cdr result)))))
                          (t4-list-types-lookup context :equation expected)) :result))
             (if (not equation)
                 (cons '(:failure "SearchMiss" "")
                       context)
               (t4-list-types-let
                ((body (proof-rewritten-term equation))
                 (empty (and (proof-is-call body *proof-if*) (proof-term-at body 3)))
                 (step
                  (if (equal empty *proof-false*)
                      (t4-list-types-let
                       ((first (t4-list-types-type-of-value-prove (1- n) (cadr body) context
                                                                  mode active projection) :result)
                        (rest (t4-list-types-type-of-value-prove (1- n) (caddr body) context
                                                                 mode active projection) :result))
                       (cons (t4-division-combine (t4-list-types-library context) (list first rest))
                             context))
                    (t4-list-types-type-of-value-prove (1- n) body context mode active projection))
                  :result))
                (cons (proof-proof-transport (t4-list-types-proof context) step equation) context)))))))))))

 (defun t4-list-types-type-of-value-prove (n term context mode active projection)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n)))
     (cons '(:failure "Fuel" "t4-list-types-type-of-value-prove") context))
    ((and (proof-compound term) (equal (len term) 2))
     (t4-list-types-nested (1- n) (car term) (cadr term) context mode active projection))
    (t
     (t4-list-types-let
      ((known (t4-list-types-lookup context :known term) :result))
      (if known (cons known context)
        (t4-list-types-prove context term nil (list *proof-not*)))))))

 (defun t4-list-types-nested (n operator term context mode active projection)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t4-list-types-nested") context)
     (case mode
       (:transform
        (t4-list-types-typed-list-transform-branch-leaf-typing (1- n) operator term context active))
       (:projected
        (t4-list-types-projected-list-type-leaf-typing (1- n) operator term context projection))
       (:constructor
        (t4-list-types-type-value (1- n) context operator term :constructor nil nil))
       (otherwise
        (t4-list-types-ask context :nested (list operator term (t4-list-types-evidence context)))))))

 (defun t4-list-types-typed-list-transform-branch-leaf-typing (n operator term context active)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t4-list-types-typed-list-transform-branch-leaf-typing") context)
     (if (proof-is-call term *termination-return-last*)
         (t4-list-types-let
          ((reduced (proof-proof-unfold (t4-list-types-proof context) term))
           (body (proof-rewritten-term reduced))
           (step (t4-list-types-typed-list-transform-branch-leaf-typing
                  (1- n) operator body context active) :result))
          (t4-list-types-reverse-argument context step reduced))
       (let ((goal (list operator term)))
         (if (member-equal goal active)
             (cons '(:failure "SearchMiss" "") context)
           (t4-list-types-type-value (1- n) context operator term :transform (cons goal active) nil))))))

 (defun t4-list-types-projected-list-type-leaf-typing (n operator term context projection)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t4-list-types-projected-list-type-leaf-typing") context)
     (t4-list-types-let
      ((index-term (and (proof-is-call term *t4-results-mv-nth*) (proof-term-at term 1))))
      (if (not (proof-is-call index-term *proof-quote*))
          (t4-list-types-type-value (1- n) context operator term :projected nil projection)
        (t4-list-types-let
         ((definition (proof-term-at term 2)))
         (let* ((formula (car projection))
                (predicate (cadr projection))
                (index (caddr projection))
                (position (cadddr projection))
                (size (car (cddddr projection)))
                (changed (cadr (cddddr projection)))
                (updates (and (equal index-term index) (assoc-equal definition changed))))
           (if (and updates (equal operator predicate))
               (t4-list-types-let
                ((actual (proof-term-at definition position))
                 (comparison (list *proof-ordinal-less* (t4-structural-count actual) size))
                 (decrease (t4-structural-structural-count-descent
                            (t4-list-types-library context) comparison (t4-list-types-evidence context))
                           :evidence)
                 (instantiated (proof-subst formula (proof-bindings-table (cdr updates) nil)))
                 (condition (proof-ite comparison instantiated *proof-true*))
                 (proof (t4-list-types-proof context))
                 (assumed (proof-proof-assume proof condition t)))
                (cons (proof-proof-prove-if proof assumed decrease) context))
             (t4-list-types-let
              ((reduction (t4-results-projection (t4-list-types-library context) term) :library)
               (reduction
                (if (and (not reduction) (proof-is-call definition *termination-return-last*))
                    (let ((proof (t4-list-types-proof context)))
                      (proof-with-checked-results
                       ((reflexive (proof-proof-reflexive proof term))
                        (opened (proof-proof-unfold proof definition)))
                       (proof-proof-rewrite proof reflexive opened '(1 2 2))))
                  reduction)))
              (if reduction
                  (t4-list-types-let
                   ((body (proof-rewritten-term reduction))
                    (step (t4-list-types-projected-list-type-leaf-typing
                           (1- n) operator body context projection) :result))
                   (t4-list-types-reverse-argument context step reduction))
                (t4-list-types-type-value (1- n) context operator term :projected nil projection)))))))))))

(defun t4-list-types-typed-list-transform-branch-leaf (value tests context predicate premises)
  (t4-list-types-let
   ((evidence (t4-structural-evidence-init (t4-list-types-library context) tests premises))
    (context (t4-list-types-with-evidence context evidence)))
   (t4-list-types-typed-list-transform-branch-leaf-typing 1000000 predicate value context nil)))

(defun t4-list-types-projected-list-type-leaf (value tests context projection)
  (t4-list-types-let
   ((evidence (t4-structural-evidence-init (t4-list-types-library context) tests nil))
    (context (t4-list-types-with-evidence context evidence)))
   (t4-list-types-projected-list-type-leaf-typing
    1000000 (cadr projection) (list *t4-results-mv-nth* (caddr projection) value) context projection)))

(defun t4-list-types-by-value-leaf (context value template tests mode predicate data)
  (t4-list-types-let
   ((step (if (eq mode :transform)
              (t4-list-types-typed-list-transform-branch-leaf value tests context predicate data)
            (t4-list-types-projected-list-type-leaf value tests context data))
          :result)
    (literal (proof-step-first step))
    (target (proof-subst template (list (cons *proof-result* value)))))
   (cons (if (equal literal target) step '(:failure "InferenceMismatch" "")) context)))

(defun t4-list-types-by-value (n context value template tests mode predicate data)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) (cons '(:failure "Fuel" "t4-list-types-by-value") context))
   ((proof-is-call value *proof-if*)
    (t4-list-types-let
     ((branches (proof-list-of-length (cdr value) 3))
      (test (car branches))
      (yes (t4-list-types-by-value (1- n) context (cadr branches) template
                                   (append tests (list (list test t))) mode predicate data) :result)
      (no (t4-list-types-by-value (1- n) context (caddr branches) template
                                  (append tests (list (list test nil))) mode predicate data) :result))
     (cons (proof-by-value-join (t4-list-types-proof context) value template yes no) context)))
   ((proof-compound value)
    (t4-list-types-let
     ((head (proof-term-at value 0)))
     (if (proof-compound head)
         (t4-list-types-let
          ((equality (proof-proof-beta (t4-list-types-proof context) value))
           (body (proof-rewritten-term equality))
           (step (t4-list-types-by-value (1- n) context body template tests mode predicate data) :result)
           (proof (t4-list-types-proof context))
           (reversed (proof-proof-symmetric proof equality)))
          (cons (proof-proof-rewrite-result proof step reversed template *proof-result*) context))
       (t4-list-types-by-value-leaf context value template tests mode predicate data))))
   (t (t4-list-types-by-value-leaf context value template tests mode predicate data))))

(defun t4-list-types-typed-list-transform-branch (shape-premise premises context root predicate template)
  (t4-list-types-let
   ((equation (t4-syntax-lists-spine (t4-list-types-library context) root shape-premise) :library)
    (body (proof-rewritten-term equation))
    (result (t4-list-types-by-value 1000000 context body template nil :transform predicate premises)
            :result)
    (proof (t4-list-types-proof context))
    (reversed (proof-proof-symmetric proof equation)))
   (cons (proof-proof-rewrite-result proof result reversed template *proof-result*) context)))

(defun t4-list-types-typed-list-transform-proof (context formula guard predicate obj root)
  (let ((shape (list *proof-consp* obj))
        (template (list predicate *proof-result*))
        (tail (list *library-cdr* obj)))
    (t4-list-types-let
     ((arithmetic (t4-list-types-ask context :use-arithmetic nil) :result)
      (proof (t4-list-types-proof context))
      (cons-proof (proof-proof-assume proof shape t))
      (atom (proof-proof-assume proof shape nil))
      (deeper (proof-subst root (list (cons obj tail))))
      (recur (t4-syntax-lists-recur (t4-list-types-library context) formula obj *library-cdr* 3))
      (view (t4-syntax-lists-spine (t4-list-types-library context) guard cons-proof) :library)
      (proof (t4-list-types-proof context))
      (assumed (proof-proof-assume proof guard t))
      (source (proof-proof-rewrite proof assumed view '(1)))
      (literal (proof-step-first source))
      (empty (and (proof-is-call literal *proof-if*) (proof-term-at literal 3)))
      (fields (if (equal empty *proof-false*)
                  (proof-proof-conjunct proof source)
                (list nil source)))
      (tail-type (proof-step-first (cadr fields))))
     (if (not (equal tail-type (list predicate tail)))
         (cons nil context)
       (t4-list-types-let
        ((tail-proof (proof-proof-modus-ponens proof (car recur) (cadr fields)))
         (supports (if (car fields) (list (car fields) tail-proof) (list tail-proof)))
         (tail-result (proof-step-first tail-proof)))
        (if (not (equal tail-result (list predicate deeper)))
            (cons '(:failure "InferenceMismatch" "") context)
          (t4-list-types-let
           ((yes (t4-list-types-typed-list-transform-branch cons-proof supports context root
                                                            predicate template) :result)
            (no (t4-list-types-typed-list-transform-branch atom nil context root predicate template)
                :result)
            (proof (t4-list-types-proof context))
            (cases (proof-proof-cases proof shape yes no))
            (cases (t4-ordinals-ordinals-imply (t4-list-types-library context) guard cases))
            (ordinal (library-library-builtin (t4-list-types-library context) 1 obj)))
           (cons (proof-proof-induct proof ordinal cases formula (t4-structural-count obj)
                                     (list (cadr recur)))
                 context))))))))

(defun t4-list-types-count-item (item terms)
  (if (endp terms)
      0
    (+ (if (equal item (car terms)) 1 0)
       (t4-list-types-count-item item (cdr terms)))))

(defun t4-list-types-typed-list-transform-run (context formula recursive)
  (if (not (proof-is-call formula *library-implies*))
      (cons nil context)
    (t4-list-types-let
     ((arguments (proof-list-of-length (cdr formula) 2)))
     (let ((guard (car arguments))
           (claim (cadr arguments)))
       (if (not (and (proof-compound guard) (equal (len guard) 2)
                     (proof-is-call claim (car guard)) (equal (len claim) 2)
                     (member-equal (car guard) recursive)
                     (not (proof-compound (cadr guard)))
                     (proof-compound (cadr claim))))
           (cons nil context)
         (let ((predicate (car guard))
               (obj (cadr guard))
               (root (cadr claim)))
           (t4-list-types-let
            ((head (proof-term-at root 0)))
            (if (not (and (member-equal head recursive)
                          (equal (t4-list-types-count-item obj (cdr root)) 1)))
                (cons nil context)
              (t4-list-types-let
               ((opened (t4-syntax-lists-open-body (t4-list-types-library context) root))
                (body (proof-rewritten-term opened)))
               (if (proof-is-call body *proof-if*)
                   (t4-list-types-typed-list-transform-proof context formula guard predicate obj root)
                 (cons nil context)))))))))))

(defun t4-list-types-compound-member-p (terms)
  (and (consp terms)
       (or (proof-compound (car terms)) (t4-list-types-compound-member-p (cdr terms)))))

(defun t4-list-types-instantiate-calls (name calls bindings)
  (if (endp calls)
      nil
    (proof-with-checked-results
     ((call (proof-subst (cons name (termination-call-actuals (car calls))) bindings))
      (rest (t4-list-types-instantiate-calls name (cdr calls) bindings)))
     (cons call rest))))

(defun t4-list-types-changed-pairs (arguments actuals)
  (cond ((or (endp arguments) (endp actuals)) nil)
        ((equal (car arguments) (car actuals))
         (t4-list-types-changed-pairs (cdr arguments) (cdr actuals)))
        (t (cons (list (car arguments) (car actuals))
                 (t4-list-types-changed-pairs (cdr arguments) (cdr actuals))))))

(defun t4-list-types-changed-calls (arguments applications)
  (if (endp applications)
      nil
    (let ((app (car applications)))
      (cons (cons app (t4-list-types-changed-pairs arguments (cdr app)))
            (t4-list-types-changed-calls arguments (cdr applications))))))

(defun t4-list-types-all-cdr-paths (calls index obj)
  (if (endp calls)
      t
    (proof-with-checked-results
     ((actual (proof-term-at (car calls) index))
      (path (t4-list-types-cdr-path actual obj)))
     (and path (t4-list-types-all-cdr-paths (cdr calls) index obj)))))

(defun t4-list-types-cdr-argument (arguments calls index)
  (if (endp arguments)
      nil
    (let ((obj (car arguments)))
      (proof-with-checked-results
       ((found (t4-list-types-all-cdr-paths calls index obj)))
       (if found (list index obj)
         (t4-list-types-cdr-argument (cdr arguments) calls (1+ index)))))))

(defun t4-list-types-projected-list-type-proof (context formula predicate index root changed position obj)
  (let* ((template (list predicate (list *t4-results-mv-nth* index *proof-result*)))
         (size (t4-structural-count obj))
         (projection (list formula predicate index position size changed)))
    (t4-list-types-let
     ((arithmetic (t4-list-types-ask context :use-arithmetic nil) :result)
      (opened (proof-proof-unfold (t4-list-types-proof context) root))
      (body (proof-rewritten-term opened))
      (result (t4-list-types-by-value 1000000 context body template nil :projected predicate projection)
              :result)
      (proof (t4-list-types-proof context))
      (closed (proof-proof-symmetric proof opened))
      (result (proof-proof-rewrite-result proof result closed template *proof-result*))
      (ordinal (library-library-builtin (t4-list-types-library context) 1 obj)))
     (cons (proof-proof-induct proof ordinal result formula size (table-values changed)) context))))

(defun t4-list-types-projected-list-type-root (context formula predicate index root recursive)
  (if (not (proof-compound root))
      (cons nil context)
    (t4-list-types-let
     ((name (proof-term-at root 0)))
     (let ((arguments (cdr root)))
       (if (or (not (member-equal name recursive))
               (t4-list-types-compound-member-p arguments)
               (not (equal (len (proof-unique arguments)) (len arguments))))
           (cons nil context)
         (let ((definition (assoc-equal name (t4-list-types-definitions context))))
           (if (not definition)
               (cons '(:failure "MissingProofInput" "") context)
             (t4-list-types-let
              ((parts (proof-list-of-length (cdr definition) 2))
               (formals (car parts))
               (body (cadr parts))
               (calls (termination-recursive-calls *termination-all* (list (list name formals body)))))
              (if (endp calls)
                  (cons nil context)
                (t4-list-types-let
                 ((bindings (proof-bindings-table (seq-zip formals arguments) nil))
                  (instantiated (t4-list-types-instantiate-calls name calls bindings))
                  (instantiated (proof-unique instantiated))
                  (changed (t4-list-types-changed-calls arguments instantiated))
                  (match (t4-list-types-cdr-argument arguments instantiated 1)))
                 (if match
                     (t4-list-types-projected-list-type-proof context formula predicate index root changed
                                                              (car match) (cadr match))
                   (cons nil context))))))))))))

(defun t4-list-types-projected-list-type-run (context formula recursive)
  (if (not (and (proof-compound formula) (equal (len formula) 2)
                (member-equal (car formula) *t4-results-result-predicates*)))
      (cons nil context)
    (let ((predicate (car formula))
          (field (cadr formula)))
      (t4-list-types-let
       ((index (and (proof-is-call field *t4-results-mv-nth*) (proof-term-at field 1))))
       (if (not (proof-is-call index *proof-quote*))
           (cons nil context)
         (t4-list-types-let
          ((parts (proof-list-of-length field 3)))
          (t4-list-types-projected-list-type-root context formula predicate index (caddr parts)
                                                 recursive)))))))

(defun t4-list-types-cons-recognizer-with-library (lib predicate pair)
  (t4-syntax-lists-constructed-view lib (list predicate pair) pair))

(defun t4-list-types-cons-recognizer (lib predicate pair)
  (proof-with-checked-results
   ((result (t4-list-types-cons-recognizer-with-library lib predicate pair)))
   (car result)))

(defun t4-list-types-in-first (lib step equality)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((rewritten (proof-proof-rewrite proof step equality '(1 1))))
     (proof-proof-tidy proof rewritten))))

(defun t4-list-types-selector-types (lib clauses obj recursive)
  (if (endp clauses)
      nil
    (let ((step (car clauses)))
      (proof-with-checked-results
       ((literal (proof-step-first step)))
       (if (not (and (proof-compound literal) (equal (len literal) 2)
                     (member-equal (car literal) recursive)))
           (t4-list-types-selector-types lib (cdr clauses) obj recursive)
         (let ((argument (cadr literal)))
           (proof-with-checked-results
            ((wrapped (and (proof-is-call argument *t4-list-types-double*)
                           (proof-term-at argument 1)))
             (step (if (and (proof-is-call argument *t4-list-types-double*) (equal wrapped obj))
                       (proof-with-checked-results
                        ((opened (proof-proof-unfold (library-library-proof lib) argument)))
                        (t4-list-types-in-first lib step opened))
                     step))
             (literal (proof-step-first step))
             (rest (t4-list-types-selector-types lib (cdr clauses) obj recursive)))
            (if (equal (cdr literal) (list obj))
                (cons step rest)
              rest))))))))

(defun t4-list-types-first-piece (n lib step goal)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-list-types-first-piece")
    (proof-with-checked-results
     ((literal (proof-step-first step))
      (head (and (proof-compound literal) (proof-term-at literal 0)))
      (empty (and (equal head *proof-if*) (proof-term-at literal 3))))
     (if (equal empty *proof-false*)
         (proof-with-checked-results
          ((pieces (proof-proof-conjunct (library-library-proof lib) step))
           (first (proof-step-first (car pieces))))
          (if (equal first goal)
              (car pieces)
            (t4-list-types-first-piece (1- n) lib (cadr pieces) goal)))
       (and (equal literal goal) step)))))

(defun t4-list-types-selector-absence-proof (context predicate-at-nil clauses residual selecting)
  (t4-list-types-let
   ((absent (t4-list-types-prove context predicate-at-nil
                (append clauses (list residual))
                (list (car predicate-at-nil) *t4-list-types-eq* *t4-structural-atom* *proof-not*))
            :result))
   (cons (library-library-transport-argument (t4-list-types-library context) absent selecting 1)
         context)))

(defun t4-list-types-selector-contradiction (context obj goal clauses residual)
  (let ((proof (t4-list-types-proof context)))
    (t4-list-types-let
     ((nonempty (proof-find-evidence clauses (list obj)))
      (literal (proof-step-first residual))
      (zero (if (proof-is-call literal *t4-list-types-eq*)
                (proof-with-checked-results ((opened (proof-proof-unfold proof literal)))
                  (proof-proof-rewrite proof residual opened '(1)))
              residual)))
     (if (not nonempty)
         (cons nil context)
       (t4-list-types-let
        ((literal (proof-step-first zero)))
        (if (not (equal literal (proof-eq obj *proof-false*)))
            (cons nil context)
          (t4-list-types-let
           ((impossible (proof-proof-rewrite proof nonempty zero '(1)))
            (impossible (proof-proof-tidy proof impossible)))
           (cons (proof-proof-subsume proof impossible (cons goal (proof-step-clause impossible)))
                 context))))))))

(defun t4-list-types-selector-absence (context selector obj goal atom clauses residual)
  (let ((predicate-at-nil (list (car goal) *proof-false*)))
    (t4-list-types-let
     ((selector-name (concatenate 'string "COMPLETION-OF-" (caddr selector)))
      (lib (t4-list-types-library context))
      (raw-selector (library-library-axiom lib selector-name (list obj)))
      (selecting (t4-syntax-lists-choose lib raw-selector atom))
      (evidence (t4-structural-evidence-init lib nil (append clauses (list atom residual))))
      (context (t4-list-types-with-evidence context evidence))
      (absent (t4-list-types-lookup context :fact-proof predicate-at-nil) :result))
     (if absent
         (cons (library-library-transport-argument (t4-list-types-library context) absent selecting 1)
               context)
       (let ((attempt (t4-list-types-selector-absence-proof context predicate-at-nil clauses residual
                                                           selecting)))
         (if (t4-list-types-search-miss-p (car attempt))
             (t4-list-types-selector-contradiction (cdr attempt) obj goal clauses residual)
           attempt))))))

(defun t4-list-types-selector-try-types (context types guard goal selector obj clauses cons-proof atom)
  (declare (xargs :measure (acl2-count types)))
  (if (endp types)
      (cons nil context)
    (let ((typed (car types)))
      (t4-list-types-let
       ((arithmetic (t4-list-types-ask context :use-arithmetic nil) :result)
        (literal (proof-step-first typed))
        (view (t4-syntax-lists-spine (t4-list-types-library context) literal cons-proof) :library)
        (unfolded (proof-proof-rewrite (t4-list-types-proof context) typed view '(1)))
        (known (t4-list-types-first-piece 1000000 (t4-list-types-library context) unfolded goal)))
       (if (not known)
           (t4-list-types-selector-try-types context (cdr types) guard goal selector obj clauses
                                             cons-proof atom)
         (t4-list-types-let
          ((empty (t4-syntax-lists-spine (t4-list-types-library context) literal atom) :library)
           (residual (proof-proof-rewrite (t4-list-types-proof context) typed empty '(1)))
           (no (t4-list-types-selector-absence context selector obj goal atom clauses residual) :result))
          (if (not no)
              (t4-list-types-selector-try-types context (cdr types) guard goal selector obj clauses
                                                cons-proof atom)
            (t4-list-types-let
             ((cases (proof-proof-cases (t4-list-types-proof context) (list *proof-consp* obj) known no)))
             (cons (t4-ordinals-ordinals-imply (t4-list-types-library context) guard cases)
                   context)))))))))

(defun t4-list-types-list-selector-type-run (context formula recursive)
  (if (not (proof-is-call formula *library-implies*))
      (cons nil context)
    (t4-list-types-let
     ((arguments (proof-list-of-length (cdr formula) 2)))
     (let ((guard (car arguments))
           (goal (cadr arguments)))
       (if (not (and (proof-compound goal) (equal (len goal) 2) (proof-compound (cadr goal))))
           (cons nil context)
         (t4-list-types-let
          ((head (proof-term-at (cadr goal) 0)))
          (if (not (member-equal head (list *library-car* *library-cdr*)))
              (cons nil context)
            (t4-list-types-let
             ((selection (proof-list-of-length (cadr goal) 2)))
             (let ((obj (cadr selection)))
               (if (proof-compound obj)
                   (cons nil context)
                 (let ((lib (t4-list-types-library context))
                       (proof (t4-list-types-proof context))
                       (shape (list *proof-consp* obj)))
                   (t4-list-types-let
                    ((assumed (proof-proof-assume proof guard t))
                     (clauses (t4-division-pieces lib assumed))
                     (types (t4-list-types-selector-types lib clauses obj recursive))
                     (cons-proof (proof-proof-assume proof shape t))
                     (atom (proof-proof-assume proof shape nil)))
                    (t4-list-types-selector-try-types context types guard goal head obj clauses
                                                      cons-proof atom)))))))))))))

(defun t4-list-types-append-type-branch (sign context test shown opened right exact)
  (let ((lib (t4-list-types-library context))
        (proof (t4-list-types-proof context)))
    (t4-list-types-let
     ((head (proof-proof-assume proof test sign))
      (a (t4-syntax-lists-choose lib shown head))
      (right-test (proof-proof-select proof opened head))
      (b (proof-proof-rewrite proof right right-test '(1 2 1))))
     (if sign
         (t4-list-types-let
          ((reversed (proof-proof-symmetric proof b)))
          (cons (proof-proof-chain proof a (list exact reversed)) context))
       (t4-list-types-let
        ((not-nil (proof-proof-not-nil proof))
         (b (t4-syntax-lists-choose lib b not-nil))
         (reversed (proof-proof-symmetric proof b)))
        (cons (proof-proof-chain proof a (list reversed)) context))))))

(defun t4-list-types-append-unchanged-guard (context assumed atom front)
  (t4-list-types-let
   ((evidence (t4-structural-evidence-init (t4-list-types-library context) nil (list assumed atom)))
    (context (t4-list-types-with-evidence context evidence))
    (atom-type (t4-list-types-lookup context :fact-proof front) :result))
   (cons (and atom-type (list assumed atom-type)) context)))

(defun t4-list-types-append-proper-guard (context assumed cons-proof atom guard predicate front)
  (t4-list-types-let
   ((guard-cons (t4-syntax-lists-spine (t4-list-types-library context) guard cons-proof) :library)
    (smaller-guard (proof-proof-rewrite (t4-list-types-proof context) assumed guard-cons '(1)))
    (guard-atom (t4-syntax-lists-spine (t4-list-types-library context) guard atom) :library)
    (proof (t4-list-types-proof context))
    (empty (proof-proof-rewrite proof assumed guard-atom '(1)))
    (literal (proof-step-first empty))
    (empty (if (proof-is-call literal *t4-list-types-eq*)
               (proof-with-checked-results ((opened (proof-proof-unfold proof literal)))
                 (proof-proof-rewrite proof empty opened '(1)))
             empty))
    (evaluated (proof-proof-reflexive proof front))
    (evaluated (proof-proof-rewrite proof evaluated empty '(1 2 1)))
    (term (proof-rewritten-term evaluated))
    (typed-nil (t4-list-types-prove context term nil
                 (list predicate *t4-list-types-eq* *t4-structural-atom* *proof-not*)) :result)
    (atom-type (proof-proof-transport (t4-list-types-proof context) typed-nil evaluated)))
   (cons (list smaller-guard atom-type) context)))

(defun t4-list-types-append-equality-branches
    (context guard combined predicate obj front cons-proof atom head-view opened shown atom-view recur)
  (t4-list-types-let
   ((assumed (proof-proof-assume (t4-list-types-proof context) guard t))
    (guard-tail (proof-subst guard (proof-bindings-table (cadr recur) nil)))
    (guards
     (cond ((equal guard-tail guard) (t4-list-types-append-unchanged-guard context assumed atom front))
           ((equal guard (list *t4-results-true-list* obj))
            (t4-list-types-append-proper-guard context assumed cons-proof atom guard predicate front))
           (t (cons nil context)))
     :result))
   (if (not guards)
       (cons nil context)
     (t4-list-types-let
      ((proof (t4-list-types-proof context))
       (exact (proof-proof-modus-ponens proof (car recur) (car guards)))
       (right (proof-proof-reflexive proof combined))
       (right (proof-proof-rewrite proof right head-view '(1 2 1)))
       (test (proof-term-at opened 1))
       (yes (t4-list-types-append-type-branch t context test shown opened right exact) :result)
       (no (t4-list-types-append-type-branch nil context test shown opened right exact) :result)
       (yes (proof-proof-cases proof test yes no))
       (selected (proof-proof-select proof combined (cadr guards)))
       (reversed (proof-proof-symmetric proof selected))
       (no (proof-proof-chain proof atom-view (list reversed))))
      (cons (list yes no) context)))))

(defun t4-list-types-append-preservation-branches (context guard head-view shown atom-view recur)
  (let ((proof (t4-list-types-proof context))
        (lib (t4-list-types-library context)))
    (t4-list-types-let
     ((assumed (proof-proof-assume proof guard t))
      (typed (t4-division-pieces lib assumed))
      (typed (proof-list-of-length typed 2))
      (opened (proof-proof-rewrite proof (car typed) head-view '(1)))
      (parts (proof-proof-conjunct proof opened))
      (conditions (t4-division-combine lib (list (cadr parts) (cadr typed))))
      (recursively (proof-proof-modus-ponens proof (car recur) conditions))
      (yes (t4-division-combine lib (list (car parts) recursively)))
      (yes (proof-proof-transport proof yes shown))
      (no (proof-proof-transport proof (cadr typed) atom-view)))
     (cons (list yes no) context))))

(defun t4-list-types-append-proof
    (context formula guard call root predicate obj suffix front combined equality)
  (let ((shape (list *proof-consp* obj))
        (tail (list *library-cdr* obj)))
    (t4-list-types-let
     ((arithmetic (t4-list-types-ask context :use-arithmetic nil) :result)
      (proof (t4-list-types-proof context))
      (cons-proof (proof-proof-assume proof shape t))
      (atom (proof-proof-assume proof shape nil))
      (head-view (t4-syntax-lists-spine (t4-list-types-library context) front cons-proof) :library)
      (opened (proof-rewritten-term head-view)))
     (if (not (and (proof-is-call opened *proof-if*)
                   (equal (cddr opened) (list (list predicate tail) *proof-false*))))
         (cons nil context)
       (t4-list-types-let
        ((recur (t4-syntax-lists-recur (t4-list-types-library context) formula obj *library-cdr* 3))
         (joined (t4-syntax-lists-spine (t4-list-types-library context) root cons-proof) :library)
         (pair (proof-rewritten-term joined)))
        (if (not (equal pair (list *proof-cons* (list *library-car* obj)
                                   (list *t4-list-types-append* tail suffix))))
            (cons '(:failure "InferenceMismatch" "") context)
          (t4-list-types-let
           ((proof (t4-list-types-proof context))
            (shown (proof-proof-reflexive proof call))
            (shown (proof-proof-rewrite proof shown joined '(1 2 1)))
            (view (t4-list-types-cons-recognizer-with-library (t4-list-types-library context)
                                                              predicate pair) :library)
            (shown (proof-proof-chain (t4-list-types-proof context) shown (list view)))
            (empty (t4-syntax-lists-spine (t4-list-types-library context) root atom) :library)
            (proof (t4-list-types-proof context))
            (atom-view (proof-proof-reflexive proof call))
            (atom-view (proof-proof-rewrite proof atom-view empty '(1 2 1)))
            (branches (if equality
                          (t4-list-types-append-equality-branches
                           context guard combined predicate obj front cons-proof atom head-view opened
                           shown atom-view recur)
                        (t4-list-types-append-preservation-branches context guard head-view shown atom-view recur))
                      :result))
           (if (not branches)
               (cons nil context)
             (t4-list-types-let
              ((proof (t4-list-types-proof context))
               (cases (proof-proof-cases proof shape (car branches) (cadr branches)))
               (step (t4-ordinals-ordinals-imply (t4-list-types-library context) guard cases))
               (ordinal (library-library-builtin (t4-list-types-library context) 1 obj)))
              (cons (proof-proof-induct proof ordinal step formula (t4-structural-count obj)
                                        (list (cadr recur)))
                    context))))))))))

(defun t4-list-types-append-type-run (context formula recursive)
  (if (not (proof-is-call formula *library-implies*))
      (cons nil context)
    (t4-list-types-let
     ((arguments (proof-list-of-length (cdr formula) 2)))
     (let* ((guard (car arguments))
            (goal (cadr arguments))
            (equality (proof-is-call goal *proof-equal*)))
       (t4-list-types-let
        ((call (if equality (proof-term-at goal 1) goal)))
        (if (not (and (proof-compound call) (equal (len call) 2) (member-equal (car call) recursive)
                      (proof-is-call (cadr call) *t4-list-types-append*)))
            (cons nil context)
          (let ((predicate (car call))
                (root (cadr call)))
            (t4-list-types-let
             ((operands (proof-list-of-length (cdr root) 2)))
             (let ((obj (car operands))
                   (suffix (cadr operands)))
               (if (or (proof-compound obj) (proof-compound suffix) (equal obj suffix))
                   (cons nil context)
                 (let* ((front (list predicate obj))
                        (rest (list predicate suffix))
                        (combined (proof-ite front rest *proof-false*)))
                   (t4-list-types-let
                    ((target (if equality (proof-term-at goal 2) guard)))
                    (if (not (equal target combined))
                        (cons nil context)
                      (t4-list-types-append-proof context formula guard call root predicate obj suffix
                                                  front combined equality))))))))))))))

(defun t4-list-types-query-run (recipe context arguments)
  (case recipe
    (:typed-list-transform
     (t4-list-types-typed-list-transform-run context (car arguments) (cadr arguments)))
    (:projected-list-type
     (t4-list-types-projected-list-type-run context (car arguments) (cadr arguments)))
    (:list-selector-type
     (t4-list-types-list-selector-type-run context (car arguments) (cadr arguments)))
    (:append-type
     (t4-list-types-append-type-run context (car arguments) (cadr arguments)))
    ((:type-of-value :constructor-type)
     (let ((context (t4-list-types-with-evidence context (caddr arguments))))
       (t4-list-types-type-value 1000000 context (car arguments) (cadr arguments)
                                 (if (eq recipe :constructor-type) :constructor :external) nil nil)))
    (otherwise (cons '(:failure "SearchMiss" "") context))))

(defun t4-list-types-finish (recipe result named-requests keep-library)
  (let* ((value (car result))
         (context (cdr result))
         (lib (t4-list-types-library context)))
    (cond ((t4-list-types-request-p value)
           (if named-requests
               value
             (list :t4-request (t4-list-types-request-operation value)
                   (t4-list-types-request-arguments value) lib)))
          ((and (failure-p value) (not keep-library)) value)
          ((member-eq recipe '(:type-of-value :constructor-type))
           (list value lib (t4-list-types-evidence context)))
          (t (cons value lib)))))

(defun t4-list-types-keyed-query (recipe lib arguments replies)
  (t4-list-types-finish recipe (t4-list-types-query-run recipe (list lib nil :keyed replies) arguments)
                         t nil))

(defun t4-list-types-query (recipe lib arguments replies)
  (t4-list-types-finish recipe (t4-list-types-query-run recipe (list lib nil :ordered replies) arguments)
                         nil nil))

(defun t4-list-types-query-with-library (recipe lib arguments replies)
  (t4-list-types-finish recipe (t4-list-types-query-run recipe (list lib nil :ordered replies) arguments)
                         nil t))

(defun t4-list-types-type-of-value (lib predicate value evidence replies)
  (t4-list-types-keyed-query :type-of-value lib (list predicate value evidence) replies))

(defun t4-list-types-constructor-type (lib predicate value evidence replies)
  (t4-list-types-keyed-query :constructor-type lib (list predicate value evidence) replies))

(defun t4-list-types-typed-list-transform (lib formula recursive replies)
  (t4-list-types-keyed-query :typed-list-transform lib (list formula recursive) replies))

(defun t4-list-types-projected-list-type (lib formula recursive replies)
  (t4-list-types-keyed-query :projected-list-type lib (list formula recursive) replies))

(defun t4-list-types-list-selector-type (lib formula recursive replies)
  (t4-list-types-keyed-query :list-selector-type lib (list formula recursive) replies))

(defun t4-list-types-append-type (lib formula recursive replies)
  (t4-list-types-keyed-query :append-type lib (list formula recursive) replies))
