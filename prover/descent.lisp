(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defun descent-request-p (value)
  (and (consp value) (eq (car value) :descent-request)))

(defun descent-request-term (request)
  (cadr request))

(defun descent-request-hypotheses (request)
  (caddr request))

(defmacro descent-let* (bindings body)
  (if (endp bindings)
      body
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (or (failure-p ,name) (descent-request-p ,name))
             ,name
           (descent-let* ,(cdr bindings) ,body))))))

(defun descent-proof (object)
  (let ((proof (library-library-proof object)))
    (if (equal object (library-make-library proof (library-library-entries object)))
        proof
      object)))

(defun descent-hypotheses-proof (hypotheses)
  (cadr hypotheses))

(defun descent-hypotheses-tests (hypotheses)
  (caddr hypotheses))

(defun descent-hypotheses-extra (hypotheses)
  (cadddr hypotheses))

(defun descent-hypotheses-found (hypotheses)
  (car (cddddr hypotheses)))

(defun descent-hypotheses-with-found (hypotheses found)
  (list :hypotheses (descent-hypotheses-proof hypotheses)
        (descent-hypotheses-tests hypotheses) (descent-hypotheses-extra hypotheses) found))

(defun descent-hypotheses-with-proof (hypotheses proof)
  (list :hypotheses proof (descent-hypotheses-tests hypotheses)
        (descent-hypotheses-extra hypotheses) (descent-hypotheses-found hypotheses)))

(defun descent-extra-by-term (steps extra)
  (if (endp steps)
      extra
    (descent-let* ((term (proof-step-first (car steps))))
      (descent-extra-by-term (cdr steps) (table-put extra term (car steps))))))

(defun descent-hypotheses-init (proof tests extra-steps)
  (descent-let* ((extra (descent-extra-by-term extra-steps nil)))
    (list :hypotheses proof tests extra nil)))

(defun descent-hypotheses-remember (hypotheses term step)
  (descent-hypotheses-with-found
   hypotheses (table-put (descent-hypotheses-found hypotheses) term step)))

(defun descent-hypotheses-put-new (hypotheses term step)
  (if (assoc-equal term (descent-hypotheses-found hypotheses))
      hypotheses
    (descent-hypotheses-remember hypotheses term step)))

(defun descent-conjuncts (tail prefix)
  (cond
   ((not (proof-is-call tail *proof-if*)) (cons (reverse prefix) tail))
   ((endp (cdddr tail)) '(:failure "index" ""))
   ((not (equal (cadddr tail) *proof-false*)) (cons (reverse prefix) tail))
   (t (descent-conjuncts (caddr tail) (cons (cadr tail) prefix)))))

(defun descent-find-conjunct (prefix tail term step proof hypotheses)
  (if (endp prefix)
      (let ((next (descent-hypotheses-put-new hypotheses tail step)))
        (cons (table-get (descent-hypotheses-found next) term nil) next))
    (descent-let* ((parts (proof-proof-conjunct proof step)))
      (let* ((conjunct (car prefix))
             (next (descent-hypotheses-put-new hypotheses conjunct (car parts))))
        (if (equal term conjunct)
            (cons (table-get (descent-hypotheses-found next) term nil) next)
          (descent-find-conjunct (cdr prefix) tail term (cadr parts) proof next))))))

(defun descent-find-tests (tests term proof hypotheses)
  (if (endp tests)
      (cons nil hypotheses)
    (descent-let* ((test (proof-list-of-length (car tests) 2)))
      (let ((literal (car test))
            (holds (cadr test)))
        (cond
         ((equal (if holds literal (proof-neg literal)) term)
          (descent-let* ((step (proof-proof-assume proof literal holds)))
            (cons step (descent-hypotheses-remember hypotheses term step))))
         ((not holds)
          (descent-find-tests (cdr tests) term proof hypotheses))
         (t
          (descent-let* ((parts (descent-conjuncts literal nil)))
            (let ((prefix (car parts))
                  (tail (cdr parts)))
              (if (or (member-equal term prefix) (equal term tail))
                  (descent-let* ((step (proof-proof-assume proof literal t)))
                    (descent-find-conjunct prefix tail term step proof hypotheses))
                (descent-find-tests (cdr tests) term proof hypotheses))))))))))

(defun descent-hypotheses-find (hypotheses term)
  (let ((existing (or (assoc-equal term (descent-hypotheses-extra hypotheses))
                      (assoc-equal term (descent-hypotheses-found hypotheses)))))
    (if existing
        (cons (cdr existing) hypotheses)
      (descent-find-tests (descent-hypotheses-tests hypotheses) term
                          (descent-proof (descent-hypotheses-proof hypotheses)) hypotheses))))

(defun descent-lookup (hypotheses term replies)
  (descent-let* ((result (descent-hypotheses-find hypotheses term)))
    (if (or (car result) (eq replies :plain))
        result
      (let ((hypotheses (cdr result))
            (reply (assoc-equal term replies)))
        (if (not reply)
            (list :descent-request term hypotheses)
          (let ((step (cadr reply)))
            (cons step (if (cddr reply)
                           (descent-hypotheses-remember hypotheses term step)
                         hypotheses))))))))

(defun descent-missing-hypothesis (term)
  (descent-let* ((text (proof-write term)))
    (list :failure "value" (concatenate 'string "Missing hypothesis " text))))

(defun descent-require (hypotheses term replies)
  (descent-let* ((result (descent-lookup hypotheses term replies)))
    (if (car result) result (descent-missing-hypothesis term))))

(defun descent-hypotheses-require (hypotheses term)
  (descent-require hypotheses term :plain))

(mutual-recursion
 (defun descent-match-argument (pattern term bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (cond
    ((equal pattern *library-x*)
     (let ((existing (assoc-equal *library-x* bindings)))
       (if existing
           (cons (equal (cdr existing) term) bindings)
         (cons t (table-put bindings *library-x* term)))))
    ((not (proof-compound pattern)) (cons (equal pattern term) bindings))
    ((endp pattern) '(:failure "index" ""))
    ((equal (car pattern) *proof-quote*) (cons (equal pattern term) bindings))
    ((and (proof-compound term)
          (equal (len pattern) (len term))
          (equal (car pattern) (car term)))
     (descent-match-arguments (cdr pattern) (cdr term) bindings))
    (t (cons nil bindings))))
 (defun descent-match-arguments (patterns terms bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (or (endp patterns) (endp terms))
       (cons t bindings)
     (descent-let* ((matched (descent-match-argument (car patterns) (car terms) bindings)))
       (if (car matched)
           (descent-match-arguments (cdr patterns) (cdr terms) (cdr matched))
         matched)))))

(defun descent-builtin-matches (indices proof clause goal matches)
  (if (endp indices)
      (cons nil (reverse matches))
    (descent-let*
     ((name (concatenate 'string "built-in-clause-" (decimal-text (car indices))))
      (fact (proof-proof-fact proof name nil))
      (first (proof-step-first fact))
      (matched (descent-match-argument first goal nil)))
     (if (not (car matched))
         (descent-builtin-matches (cdr indices) proof clause goal matches)
       (descent-let* ((step (proof-proof-instantiate proof fact (table-items (cdr matched)))))
         (if (subsetp-equal (proof-step-clause step) clause)
             (cons step nil)
           (descent-builtin-matches (cdr indices) proof clause goal (cons step matches))))))))

(defun descent-discharge-tests (tests proof clause step hypotheses replies)
  (cond
   ((endp tests) (cons step hypotheses))
   ((member-equal (car tests) clause)
    (descent-discharge-tests (cdr tests) proof clause step hypotheses replies))
   (t
    (let ((test (car tests)))
      (descent-let*
       ((negative (if (proof-is-call test *proof-not*)
                      (descent-let* ((inner (proof-term-at test 1)))
                        (descent-lookup hypotheses inner replies))
                    (cons nil hypotheses)))
        (evidence (if (car negative)
                      negative
                    (descent-lookup (cdr negative) (proof-neg test) replies))))
       (if (not (car evidence))
           (cons nil (cdr evidence))
         (descent-let* ((result (proof-proof-discharge proof step (car evidence))))
           (descent-discharge-tests (cdr tests) proof clause result (cdr evidence) replies))))))))

(defun descent-discharge-matches (matches proof clause hypotheses replies)
  (if (endp matches)
      (cons nil hypotheses)
    (let ((step (car matches)))
      (descent-let*
       ((result (descent-discharge-tests (cdr (proof-step-clause step))
                                         proof clause step hypotheses replies)))
       (if (car result)
           result
         (descent-discharge-matches (cdr matches) proof clause (cdr result) replies))))))

(defun descent-direct-builtin-query (lib clause hypotheses replies)
  (if (endp clause)
      '(:failure "index" "")
    (let ((proof (descent-proof lib))
          (goal (car (last clause))))
      (descent-let* ((matches (descent-builtin-matches (seq-range 1 24 1) proof clause goal nil)))
        (if (or (car matches) (not hypotheses))
            (cons (car matches) hypotheses)
          (descent-discharge-matches (cdr matches) proof clause hypotheses replies))))))

(defun descent-direct-builtin (lib clause hypotheses)
  (descent-direct-builtin-query lib clause hypotheses :plain))

(defconst *descent-nfix* (proof-sym "NFIX" "ACL2"))
(defconst *descent-length* (proof-cl "LENGTH"))
(defconst *descent-min* (proof-cl "MIN"))
(defconst *descent-natural-template* (list *library-natp* *proof-result*))

(defun descent-slice-library-p (lib)
  (let ((kind (proof-proof-kind (library-library-proof lib))))
    (or (eq kind :slice) (eq kind :book))))

(defun descent-library-has-fact (lib name)
  (assoc-equal (proof-sym (concatenate 'string "SELF-" name) "ACL2")
               (proof-proof-facts (library-library-proof lib))))

(defun descent-library-has-definition (lib head)
  (assoc-equal head (proof-proof-definitions (library-library-proof lib))))

(defun descent-nfix-equation-library (lib)
  (if (descent-library-has-fact lib "LIBRARY-NFIX")
      lib
    (let ((proof (library-library-proof lib)))
      (descent-let*
       ((nfix (proof-proof-unfold proof (list *descent-nfix* *library-x*)))
        (helper (proof-proof-simplify proof (list *library-nfix* *library-x*)
                                      nil (list *library-nfix* *library-natp*)))
        (back (proof-proof-symmetric proof helper))
        (identity (proof-proof-chain proof nfix (list back)))
        (claim (proof-step-first identity)))
       (library-library-lemma lib "LIBRARY-NFIX" claim identity nil)))))

(defun descent-natural-nfix (lib term)
  (descent-let*
   ((natural (library-library-cite lib "NFIX-NATURAL" (cdr term) nil))
    (arg (proof-term-at term 1))
    (lib (descent-nfix-equation-library lib))
    (equation (library-library-cite lib "LIBRARY-NFIX" (list arg) nil))
    (step (library-library-transport-argument lib natural equation 1)))
   (cons step lib)))

(defun descent-minimum-leaves (requests bounds)
  (if (endp requests)
      nil
    (let* ((request (car requests))
           (bound (assoc-equal (car request) bounds))
           (step (if bound (cdr bound) (list :failure "key" ""))))
      (cons (cons request step) (descent-minimum-leaves (cdr requests) bounds)))))

(defun descent-minimum-natural-library (lib)
  (if (descent-library-has-fact lib "MINIMUM-NATURAL")
      lib
    (let ((proof (library-library-proof lib))
          (nx (list *library-natp* *library-x*))
          (ny (list *library-natp* *library-y*)))
      (descent-let*
       ((equation (proof-proof-unfold proof (list *descent-min* *library-x* *library-y*)))
        (first (proof-step-first equation))
        (value (proof-term-at first 2))
        (x-bound (proof-proof-assume proof nx t))
        (y-bound (proof-proof-assume proof ny t))
        (requests (proof-proof-by-value-leaves proof value nil))
        (leaves (descent-minimum-leaves requests
                                        (list (cons *library-x* x-bound) (cons *library-y* y-bound))))
        (step (proof-proof-by-value proof value *descent-natural-template* leaves nil))
        (step (library-library-transport-argument lib step equation 1))
        (claim (proof-step-first step)))
       (library-library-lemma lib "MINIMUM-NATURAL" claim step (list (proof-neg nx) (proof-neg ny)))))))

(defun descent-natural-prepare (lib term)
  (let ((proof (library-library-proof lib)))
    (cond
     ((and (proof-is-call term *descent-nfix*) (descent-library-has-definition lib *descent-nfix*))
      (descent-let* ((result (descent-natural-nfix lib term)))
        (list :value result)))
     ((and (proof-is-call term *descent-min*) (descent-library-has-definition lib *descent-min*))
      (descent-let* ((lib (descent-minimum-natural-library lib)))
        (list :arguments lib "MINIMUM-NATURAL" (cdr term))))
     ((proof-is-call term *descent-length*)
      (if (descent-library-has-fact lib "LENGTH-NATURAL")
          (descent-let* ((step (library-library-cite lib "LENGTH-NATURAL" (cdr term) nil)))
            (list :value (cons step lib)))
        (let ((length (list *descent-length* *library-x*)))
          (descent-let*
           ((equation (proof-proof-unfold proof length))
            (first (proof-step-first equation))
            (value (proof-term-at first 2))
            (requests (proof-proof-by-value-leaves proof value nil)))
           (list :length lib (cdr term) length equation value requests)))))
     ((proof-is-call term *proof-plus*)
      (list :arguments lib "NATURAL-SUM" (cdr term)))
     (t
      (descent-let* ((step (library-library-natural lib term)))
        (list :value (cons step lib)))))))

(defun descent-natural-finish-length (task leaves)
  (let* ((lib (cdr leaves))
         (proof (library-library-proof lib))
         (args (caddr task))
         (length (cadddr task))
         (equation (car (cddddr task)))
         (value (cadr (cddddr task))))
    (descent-let*
     ((step (proof-proof-by-value proof value *descent-natural-template* (car leaves) nil))
      (back (proof-proof-symmetric proof equation))
      (step (proof-proof-rewrite-result proof step back *descent-natural-template* *proof-result*))
      (lib (library-library-lemma lib "LENGTH-NATURAL" (list *library-natp* length) step nil))
      (step (library-library-cite lib "LENGTH-NATURAL" args nil)))
     (cons step lib))))

(mutual-recursion
 (defun descent-slice-natural (n lib term)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "descent-library-natural")
     (descent-natural-task (1- n) (descent-natural-prepare lib term))))
 (defun descent-natural-task (n task)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "descent-library-natural"))
    ((failure-p task) task)
    ((eq (car task) :value) (cadr task))
    ((eq (car task) :length)
     (descent-let*
      ((leaves (descent-natural-leaves (1- n) (cadr task) (caddr (cddddr task)))))
      (descent-natural-finish-length task leaves)))
    (t
     (let ((args (cadddr task)))
       (descent-let*
        ((result (descent-natural-arguments (1- n) (cadr task) args))
         (step (library-library-cite (cdr result) (caddr task) args (car result))))
        (cons step (cdr result)))))))
 (defun descent-natural-arguments (n lib args)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "descent-library-natural"))
    ((endp args) (cons nil lib))
    (t
     (descent-let* ((first (descent-slice-natural (1- n) lib (car args)))
                    (rest (descent-natural-arguments (1- n) (cdr first) (cdr args))))
       (cons (cons (car first) (car rest)) (cdr rest))))))
 (defun descent-natural-leaves (n lib requests)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "descent-library-natural"))
    ((endp requests) (cons nil lib))
    (t
     (descent-let* ((first (descent-slice-natural (1- n) lib (caar requests)))
                    (rest (descent-natural-leaves (1- n) (cdr first) (cdr requests))))
       (cons (cons (cons (car requests) (car first)) (car rest)) (cdr rest)))))))

(defun descent-library-natural (lib term)
  (if (descent-slice-library-p lib)
      (descent-slice-natural 1000000 lib term)
    (descent-let* ((step (library-library-natural lib term)))
      (cons step lib))))

(defun descent-slice-natural-type-p (lib term)
  (or (proof-is-call term *descent-length*)
      (and (or (proof-is-call term *descent-nfix*) (proof-is-call term *descent-min*))
           (descent-library-has-definition lib (car term)))))

(defun descent-natural-integer (lib term)
  (descent-let*
   ((natural (descent-library-natural lib term))
    (step (library-library-cite (cdr natural) "NATURAL-INTEGER" (list term) (list (car natural)))))
   (cons step (cdr natural))))

(mutual-recursion
 (defun descent-slice-type-of (term lib evidence)
   (declare (xargs :measure (acl2-count term)))
   (descent-let* ((known (library-type-evidence (library-integer term) evidence)))
     (cond
      (known (cons known lib))
      ((descent-slice-natural-type-p lib term)
       (descent-natural-integer lib term))
      ((and (consp term)
            (or (proof-is-call term *proof-plus*) (proof-is-call term *proof-times*)))
       (descent-let*
        ((types (descent-slice-types (cdr term) lib evidence))
         (name (if (equal (car term) *proof-plus*) "INTEGER-SUM" "INTEGER-PRODUCT"))
         (step (library-library-cite (cdr types) name (cdr term) (car types))))
        (cons step (cdr types))))
      ((and (consp term) (proof-is-call term *proof-minus*))
       (if (endp (cdr term))
           '(:failure "index" "")
         (descent-let*
          ((arg-type (descent-slice-type-of (cadr term) lib evidence))
           (step (library-library-cite (cdr arg-type) "INTEGER-NEGATION" (cdr term) (list (car arg-type)))))
          (cons step (cdr arg-type)))))
      (t
       (descent-let* ((step (library-library-type-of lib term evidence)))
         (cons step lib))))))
 (defun descent-slice-types (terms lib evidence)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       (cons nil lib)
     (descent-let* ((first (descent-slice-type-of (car terms) lib evidence))
                    (rest (descent-slice-types (cdr terms) (cdr first) evidence)))
       (cons (cons (car first) (car rest)) (cdr rest))))))

(defun descent-library-type-of (lib term evidence)
  (if (descent-slice-library-p lib)
      (descent-slice-type-of term lib evidence)
    (descent-let* ((step (library-library-type-of lib term evidence)))
      (cons step lib))))

(defun descent-ordinal-comparison (lib child parent)
  (descent-let*
   ((a-type (descent-library-type-of lib child nil))
    (b-type (descent-library-type-of (cdr a-type) parent nil))
    (step (library-library-cite (cdr b-type) "FINITE-ORDER" (list child parent)
                                (list (car a-type) (car b-type)))))
   (cons step (cdr b-type))))

(defun descent-hypotheses-after-library (hypotheses initial lib)
  (if (and (not (equal initial lib)) (equal (descent-hypotheses-proof hypotheses) initial))
      (descent-hypotheses-with-proof hypotheses lib)
    hypotheses))

(defun descent-measure-ordinal-with-library (lib measure)
  (descent-let* ((builtin (descent-direct-builtin lib (list (list *proof-ordinalp* measure)) nil)))
    (if (car builtin)
        (cons (car builtin) lib)
      (descent-let* ((head (proof-term-at measure 0)))
        (if (equal head *library-gap*)
            (descent-let* ((step (library-library-cite lib "GAP-ORDINAL" (cdr measure) nil)))
              (cons step lib))
          (descent-let*
           ((natural (descent-library-natural lib measure))
            (step (library-library-cite (cdr natural) "NATURAL-ORDINAL" (list measure) (list (car natural)))))
           (cons step (cdr natural))))))))

(defun descent-measure-ordinal (lib measure)
  (descent-let* ((result (descent-measure-ordinal-with-library lib measure)))
    (car result)))

(defun descent-selector-chain-edges (child parent edges)
  (cond
   ((equal child parent) edges)
   ((not (proof-compound child)) nil)
   ((endp child) '(:failure "index" ""))
   ((member-equal (car child) (list *library-car* *library-cdr*))
    (if (consp (cdr child))
        (descent-selector-chain-edges (cadr child) parent
                                      (cons (list (car child) (cadr child)) edges))
      '(:failure "index" "")))
   (t nil)))

(defun descent-selector-edge (lib head base evidence)
  (let ((proof (descent-proof lib))
        (is-car (equal head *library-car*)))
    (if evidence
        (descent-let*
         ((builtin (library-library-builtin lib (if is-car 2 3) base))
          (strict (proof-proof-discharge proof builtin evidence))
          (current (list *library-count* (list head base)))
          (previous (list *library-count* base))
          (ordinal (library-library-ordinal-comparison lib current previous)))
         (proof-proof-rewrite proof strict ordinal '(1)))
      (library-library-cite lib (if is-car "COUNT-CAR-WEAK" "COUNT-CDR-WEAK") (list base) nil))))

(defun descent-selector-chain-steps (edges lib step hypotheses replies)
  (if (endp edges)
      (descent-let* ((first (proof-step-first step))
                     (head (proof-term-at first 0)))
        (if (equal head *proof-less*)
            (cons step hypotheses)
          (list :failure "assertion" "")))
    (let* ((edge (car edges))
           (head (car edge))
           (base (cadr edge)))
      (descent-let*
       ((evidence (descent-lookup hypotheses (list *proof-consp* base) replies))
        (bound (descent-selector-edge lib head base (car evidence)))
        (combined (if step (library-library-compare-chain lib bound step) bound)))
       (descent-selector-chain-steps (cdr edges) lib combined (cdr evidence) replies)))))

(defun descent-selector-chain-query (lib child parent hypotheses replies)
  (descent-let* ((edges (descent-selector-chain-edges child parent nil)))
    (if edges
        (descent-selector-chain-steps edges lib nil hypotheses replies)
      (descent-let* ((text (proof-write parent)))
        (list :failure "value" (concatenate 'string "Expected a selector path from " text))))))

(defun descent-selector-chain (lib child parent hypotheses)
  (descent-selector-chain-query lib child parent hypotheses :plain))

(defun descent-selector-step (lib actual parent hypotheses replies)
  (let ((proof (descent-proof lib)))
    (descent-let*
     ((head (proof-term-at actual 0))
      (selector (member-equal head (list *library-car* *library-cdr*)))
      (arg (if selector (proof-term-at actual 1) nil))
      (base (proof-term-at parent 1)))
     (if (and selector (equal arg base))
         (descent-let*
          ((structural (library-library-builtin lib (if (equal head *library-car*) 2 3) base))
           (evidence (descent-require hypotheses (list *proof-consp* base) replies))
           (step (proof-proof-discharge proof structural (car evidence))))
          (cons step (cdr evidence)))
       (descent-let*
        ((decrease (descent-selector-chain-query lib actual base hypotheses replies))
         (order (library-library-ordinal-comparison lib (list *library-count* actual) parent))
         (step (proof-proof-transport proof (car decrease) order)))
        (cons step (cdr decrease)))))))

(defun descent-selector-decrease-query (lib goal hypotheses replies)
  (let ((proof (descent-proof lib)))
    (descent-let*
     ((parts (proof-list-of-length goal 3))
      (child-head (proof-term-at (cadr parts) 0))
      (parent-head (proof-term-at (caddr parts) 0)))
     (if (not (and (equal child-head *library-count*) (equal parent-head *library-count*)))
         '(:failure "assertion" "")
       (descent-let*
        ((parent (caddr parts))
         (raw (proof-term-at (cadr parts) 1))
         (opened (proof-proof-simplify proof raw nil (list *termination-return-last*)))
         (actual (if opened
                     (descent-let* ((equation (proof-step-first opened)))
                       (proof-term-at equation 2))
                   raw))
         (result (descent-selector-step lib actual parent hypotheses replies)))
        (if (not opened)
            result
          (descent-let*
           ((reverse (proof-proof-symmetric proof opened))
            (rewritten (proof-proof-rewrite proof (car result) reverse '(1 1 1)))
            (step (proof-proof-tidy proof rewritten)))
           (cons step (cdr result)))))))))

(defun descent-selector-decrease (lib goal hypotheses)
  (descent-selector-decrease-query lib goal hypotheses :plain))

(defun descent-gap-finish (lib bound old new integers inside advance hypotheses)
  (descent-let*
   ((bound-type (descent-library-type-of lib bound integers))
    (old-type (descent-library-type-of (cdr bound-type) old integers))
    (new-type (descent-library-type-of (cdr old-type) new integers))
    (extended (cdr new-type))
    (step (library-library-cite extended "GAP-DECREASE" (list bound old new)
                                (list (car bound-type) (car old-type) (car new-type) inside advance))))
   (cons step (descent-hypotheses-after-library hypotheses lib extended))))

(defun descent-gap-integer-bound (lib bound old new hypotheses replies)
  (descent-let*
   ((natural (descent-require hypotheses (list *library-natp* old) replies))
    (int-old (library-library-cite lib "NATURAL-INTEGER" (list old) (list (car natural))))
    (inside (descent-require (cdr natural) (library-lt old bound) replies))
    (advance (library-library-cite lib "SUCCESSOR-LARGER" (list old) (list int-old))))
   (descent-gap-finish lib bound old new (list int-old) (car inside) advance (cdr inside))))

(defun descent-gap-other-bound (lib bound p new hypotheses replies)
  (descent-let*
   ((n (proof-term-at bound 2))
    (int-n (descent-require hypotheses (library-integer n) replies))
    (int-p (descent-require (cdr int-n) (library-integer p) replies))
    (positive (descent-require (cdr int-p) (library-positive p) replies))
    (at-least (descent-require (cdr positive) (proof-neg (library-lt n p)) replies))
    (inside (library-library-cite lib "LESS-THAN-NEXT" (list n p)
                                  (list (car int-n) (car int-p) (car at-least))))
    (advance (library-library-cite lib "TENFOLD-LARGER" (list p)
                                   (list (car int-p) (car positive)))))
   (descent-gap-finish lib bound p new (list (car int-n) (car int-p))
                       inside advance (cdr at-least))))

(defun descent-gap-decrease-query (lib goal hypotheses replies)
  (descent-let*
   ((parts (proof-list-of-length goal 3))
    (measure (proof-list-of-length (caddr parts) 3))
    (smaller (proof-list-of-length (cadr parts) 3)))
   (let ((bound (cadr measure))
         (old (caddr measure))
         (new (caddr smaller)))
     (cond
      ((not (equal bound (cadr smaller))) '(:failure "assertion" ""))
      ((proof-is-call bound *proof-quote*)
       (descent-gap-integer-bound lib bound old new hypotheses replies))
      (t (descent-gap-other-bound lib bound old new hypotheses replies))))))

(defun descent-shift-left (lib step a b offset)
  (let ((proof (descent-proof lib)))
    (descent-let*
     ((swap-a (library-library-axiom lib "COMMUTATIVITY-OF-+" (list a offset)))
      (step (proof-proof-rewrite proof step swap-a '(1 1)))
      (swap-b (library-library-axiom lib "COMMUTATIVITY-OF-+" (list b offset))))
     (proof-proof-rewrite proof step swap-b '(1 2)))))

(defun descent-shift-with-library (lib step offset left-offset)
  (descent-let*
   ((first (proof-step-first step))
    (parts (proof-list-of-length first 3))
    (a (cadr parts))
    (b (caddr parts))
    (a-type (descent-library-type-of lib a nil))
    (b-type (descent-library-type-of (cdr a-type) b nil))
    (offset-type (descent-library-type-of (cdr b-type) offset nil))
    (lib (cdr offset-type))
    (result (library-library-cite lib "LESS-SHIFT" (list a b offset)
                                  (list (car a-type) (car b-type) (car offset-type) step)))
    (result (if left-offset (descent-shift-left lib result a b offset) result))
    (step (proof-proof-tidy (descent-proof lib) result)))
   (cons step lib)))

(defun descent-shift (lib step offset left-offset)
  (descent-let* ((result (descent-shift-with-library lib step offset left-offset)))
    (car result)))

(defun descent-walk-successor (lib before)
  (descent-let*
   ((type (descent-library-type-of lib before nil))
    (step (library-library-cite (cdr type) "SUCCESSOR-LARGER" (list before) (list (car type)))))
   (cons step (cdr type))))

(defun descent-walk-step (lib after before caller-walks callee-walks hypotheses replies)
  (if (equal after before)
      (if (and caller-walks (not callee-walks))
          (descent-let* ((result (descent-walk-successor lib before)))
            (list (car result) hypotheses (cdr result)))
        '(:failure "assertion" ""))
    (descent-let*
     ((child (proof-term-at after 1))
      (parent (proof-term-at before 1))
      (decrease (descent-selector-chain-query lib child parent hypotheses replies))
      (step (car decrease))
      (result (cond
               (callee-walks (descent-shift-with-library lib step *proof-one* t))
               (caller-walks
                (descent-let* ((growth (descent-walk-successor lib before))
                               (extended (cdr growth))
                               (combined (library-library-compare-chain extended step (car growth))))
                  (cons combined extended)))
               (t (cons step lib)))))
     (list (car result) (cdr decrease) (cdr result)))))

(defun descent-walk-decrease-query (lib goal hypotheses replies)
  (descent-let*
   ((parts (proof-list-of-length goal 3))
    (child (cadr parts))
    (parent (caddr parts))
    (parent-head (proof-term-at parent 0))
    (child-head (proof-term-at child 0))
    (caller-walks (not (equal parent-head *library-count*)))
    (callee-walks (not (equal child-head *library-count*)))
    (before (if caller-walks (proof-term-at parent 2) parent))
    (raw-after (if callee-walks (proof-term-at child 2) child)))
   (if (and (not caller-walks) callee-walks)
       '(:failure "assertion" "")
     (let ((proof (descent-proof lib)))
       (descent-let*
        ((opened (proof-proof-simplify proof raw-after nil (list *termination-return-last*)))
         (after (if opened
                    (descent-let* ((equation (proof-step-first opened)))
                      (proof-term-at equation 2))
                  raw-after))
         (result (descent-walk-step lib after before caller-walks callee-walks hypotheses replies))
         (extended (caddr result))
         (proof (descent-proof extended))
         (step (if opened
                   (descent-let* ((reverse (proof-proof-symmetric proof opened)))
                     (proof-proof-rewrite-first proof (car result) reverse))
                 (car result)))
         (order (descent-ordinal-comparison extended child parent))
         (transported (proof-proof-transport (descent-proof (cdr order)) step (car order))))
        (cons transported (descent-hypotheses-after-library (cadr result) lib (cdr order))))))))

(defun descent-run-unchanged (lib child parent old changed unchanged hypotheses replies)
  (descent-let*
   ((offset (proof-term-at parent unchanged))
    (child-offset (proof-term-at child unchanged)))
   (if (not (equal offset child-offset))
       '(:failure "assertion" "")
     (descent-let*
      ((cons-proof (descent-require hypotheses (list *proof-consp* old) replies))
       (less (library-library-cite lib "LEN-CDR-LESS" (list old) (list (car cons-proof))))
       (step (descent-shift-with-library lib less offset (equal changed 2)))
       (order (descent-ordinal-comparison (cdr step) child parent))
       (result (proof-proof-transport (descent-proof (cdr order)) (car step) (car order))))
      (cons result (descent-hypotheses-after-library (cdr cons-proof) lib (cdr order)))))))

(defun descent-run-decrease-query (lib goal hypotheses replies)
  (descent-let*
   ((parts (proof-list-of-length goal 3))
    (child (cadr parts))
    (parent (caddr parts))
    (child-left (proof-term-at child 1))
    (parent-left (proof-term-at parent 1))
    (changed (if (equal child-left parent-left) 2 1))
    (unchanged (- 3 changed))
    (old-length (proof-term-at parent changed))
    (old (proof-term-at old-length 1))
    (new-length (proof-term-at child changed)))
   (if (equal new-length (list *library-len* (list *library-cdr* old)))
       (descent-run-unchanged lib child parent old changed unchanged hypotheses replies)
     '(:failure "assertion" ""))))

(defun descent-run-decrease (lib goal hypotheses)
  (descent-run-decrease-query lib goal hypotheses :plain))

(defun descent-query-recipe (recipe lib args hypotheses replies)
  (case recipe
    (:direct-builtin (descent-direct-builtin-query lib (car args) hypotheses replies))
    (:selector-chain (descent-selector-chain-query lib (car args) (cadr args) hypotheses replies))
    (:selector-decrease (descent-selector-decrease-query lib (car args) hypotheses replies))
    (:gap-decrease (descent-gap-decrease-query lib (car args) hypotheses replies))
    (:walk-decrease (descent-walk-decrease-query lib (car args) hypotheses replies))
    (:run-decrease (descent-run-decrease-query lib (car args) hypotheses replies))
    (otherwise '(:failure "value" ""))))
