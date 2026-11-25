(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-term-collections-if-leaves*
  (proof-sym "IF-TREE-LEAF-TERMS" "ACL2"))
(defconst *t3-book-term-collections-append-type* "T3-APPEND-PSEUDO-TERM-LISTS")
(defconst *t3-book-term-collections-conjoin* (proof-sym "CONJOIN" "ACL2"))
(defconst *t3-book-term-collections-conjoin2* (proof-sym "CONJOIN2" "ACL2"))
(defconst *t3-book-term-collections-equalities*
  (proof-sym "CONJOIN-EQUALITIES-AUX" "ACL2"))

(defun t3-book-term-collections-step-term-at (step index)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defund t3-book-term-collections-by-value-open-frame (proof value)
  (if (proof-is-call value *proof-if*)
      (proof-with-checked-results ((parts (proof-list-of-length (cdr value) 3)))
        (cons :if-true parts))
    (proof-with-checked-results ((equation (t3-logic-by-value-unfold proof value)))
      (and equation
           (proof-with-checked-results
               ((opened (t3-book-term-collections-step-term-at equation 2)))
             (list :rewrite equation opened))))))

; The stack records the proof operations to perform after each leaf returns.
(defun t3-book-term-collections-by-value-open (n proof value tests stack)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t3-book-term-collections-by-value-open")
    (let ((frame (t3-book-term-collections-by-value-open-frame proof value)))
      (case (car frame)
        (:failure frame)
        (:if-true
         (t3-book-term-collections-by-value-open
          (1- n) proof (caddr frame) (append tests (list (list (cadr frame) t)))
          (cons (list :if-true value tests) stack)))
        (:rewrite
         (t3-book-term-collections-by-value-open
          (1- n) proof (caddr frame) tests (cons (list :rewrite (cadr frame)) stack)))
        (otherwise (list :t3-book-term-collections-leaf value tests stack))))))

(defund t3-book-term-collections-by-value-close-frame (proof template step frame)
  (let ((value (cadr frame)))
    (if (eq (car frame) :rewrite)
        (proof-with-checked-results ((back (proof-proof-symmetric proof value)))
          (proof-proof-rewrite-result proof step back template *proof-result*))
      (proof-by-value-join proof value template (caddr frame) step))))

(defun t3-book-term-collections-by-value-return (proof template step stack)
  (declare (xargs :measure (acl2-count stack)))
  (cond
   ((or (failure-p step) (endp stack)) step)
   ((eq (caar stack) :if-true)
    (let* ((frame (car stack))
           (value (cadr frame)))
      (t3-book-term-collections-by-value-open
       1000000 proof (cadddr value) (append (caddr frame) (list (list (cadr value) nil)))
       (cons (list :if-false value step) (cdr stack)))))
   (t (t3-book-term-collections-by-value-return
       proof template (t3-book-term-collections-by-value-close-frame proof template step (car stack))
       (cdr stack)))))

(defun t3-book-term-collections-by-value-start (lib value tests)
  (t3-book-term-collections-by-value-open
   1000000 (library-library-proof lib) value tests nil))

(defund t3-book-term-collections-by-value-resume (lib template request step)
  (proof-with-checked-results
      ((step step)
       (literal (proof-step-first step))
       (target (proof-subst template (list (cons *proof-result* (cadr request))))))
    (if (equal literal target)
        (t3-book-term-collections-by-value-return
         (library-library-proof lib) template step (cadddr request))
      '(:failure "proof-mismatch" ""))))

(defund t3-book-term-collections-constructor-form-plan (lib value evidence)
  (proof-with-checked-results
      ((equation (t3-book-associations-normalize lib value evidence *t3-book-spines-guards*))
       (current (if equation (t3-book-term-collections-step-term-at equation 2) value)))
    (list current equation)))

(defund t3-book-term-collections-constructor-form-after-yes (proof value current equation branch)
  (proof-with-checked-results
      ((branch branch)
       (equation (t3-book-spines-constructor-form-rewrite proof value equation branch 2))
       (no (proof-term-at current 3)))
    (list no equation)))

(defun t3-book-term-collections-constructor-form (n lib value evidence)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t3-book-term-collections-constructor-form")
    (let* ((proof (library-library-proof lib))
           (plan (t3-book-term-collections-constructor-form-plan lib value evidence)))
      (if (failure-p plan)
          plan
        (let ((current (car plan))
              (equation (cadr plan)))
          (proof-with-checked-results
              ((equation
                (if (proof-is-call current *proof-if*)
                    (proof-with-checked-results
                        ((yes (proof-term-at current 2))
                         (branch (t3-book-term-collections-constructor-form (1- n) lib yes evidence))
                         (next (t3-book-term-collections-constructor-form-after-yes
                                proof value current equation branch))
                         (branch (t3-book-term-collections-constructor-form
                                  (1- n) lib (car next) evidence)))
                      (t3-book-spines-constructor-form-rewrite proof value (cadr next) branch 3))
                  equation)))
            (and equation (proof-proof-tidy proof equation))))))))

(defun t3-book-term-collections-shallow (lib term evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof term))
         (value (t3-book-term-collections-step-term-at opened 2))
         (constructor (t3-book-term-collections-constructor-form 1000000 lib value evidence)))
      (proof-proof-chain proof opened (list constructor)))))

(defun t3-book-term-collections-append-lists (lib)
  (let* ((proof (library-library-proof lib))
         (call (list *t3-list-bounds-append* *library-x* *library-y*)))
    (proof-with-checked-results
        ((first (proof-proof-assume proof (list *t3-book-substitution-list* *library-x*) t))
         (second (proof-proof-assume proof (list *t3-book-substitution-list* *library-y*) t))
         (left-type (proof-step-first first))
         (right-type (proof-step-first second))
         (inner (proof-ite right-type (list *t3-book-substitution-list* call) *proof-true*))
         (formula (proof-ite left-type inner *proof-true*))
         (cell-proof (proof-proof-assume proof (list *proof-consp* *library-x*) t))
         (parts (t3-book-substitution-list-components lib first cell-proof))
         (remaining (t3-list-bounds-tail-hypothesis lib formula cell-proof))
         (joined (proof-proof-prove-if proof remaining (cadr parts)))
         (joined (proof-proof-prove-if proof joined second))
         (cell (t3-list-bounds-append-branch lib *library-x* *library-y* cell-proof))
         (pair (t3-scan-typed-pair lib (car parts) joined))
         (body (t3-book-term-collections-step-term-at cell 2))
         (opened (t3-book-term-collections-shallow lib (list *t3-book-substitution-list* body) nil))
         (yes (proof-proof-transport proof pair opened))
         (yes (library-library-transport-argument lib yes cell 1))
         (atom-proof (proof-proof-assume proof (list *proof-consp* *library-x*) nil))
         (atom (t3-list-bounds-append-branch lib *library-x* *library-y* atom-proof))
         (no (library-library-transport-argument lib second atom 1))
         (yes (t3-scan-conclusion lib inner yes))
         (yes (t3-scan-conclusion lib formula yes))
         (no (t3-scan-conclusion lib inner no))
         (no (t3-scan-conclusion lib formula no))
         (step (t3-list-bounds-tail-induction lib formula yes no)))
      (library-library-lemma lib *t3-book-term-collections-append-type* formula step nil))))

(defun t3-book-term-collections-known-type (target known)
  (if (endp known)
      nil
    (proof-with-checked-results ((literal (proof-step-first (car known))))
      (if (equal literal target)
          (car known)
        (t3-book-term-collections-known-type target (cdr known))))))

(defund t3-book-term-collections-constructed-type-plan (lib predicate value known)
  (proof-with-checked-results ((found (t3-book-term-collections-known-type (list predicate value) known)))
    (if found
        (list :known found)
      (proof-with-checked-results
          ((normalized (t3-book-associations-normalize lib value nil nil))
           (normal (if normalized (t3-book-term-collections-step-term-at normalized 2) value)))
        (cond
         ((not (equal normal value)) (list :normalized normal normalized))
         ((proof-is-call value *proof-quote*) (list :quote))
         ((not (proof-is-call value *proof-cons*))
          '(:failure "unsupported" ""))
         (t
          (proof-with-checked-results ((head (proof-term-at value 1)))
            (cond ((equal predicate *t3-book-substitution-list*) (list :list head))
                  ((equal head (proof-quote *proof-quote*)) (list :quote))
                  (t (proof-with-checked-results ((args (proof-term-at value 2)))
                       (list :application args)))))))))))

(defund t3-book-term-collections-constructed-type-tail (value step)
  (if (failure-p step) step (proof-term-at value 2)))

(defun t3-book-term-collections-constructed-type (n lib predicate value known)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t3-book-term-collections-constructed-type")
    (let ((target (list predicate value))
          (proof (library-library-proof lib))
          (plan (t3-book-term-collections-constructed-type-plan lib predicate value known)))
      (case (car plan)
        (:known (cadr plan))
        (:normalized
         (proof-with-checked-results
             ((typed (t3-book-term-collections-constructed-type (1- n) lib predicate (cadr plan) known)))
           (library-library-transport-argument lib typed (caddr plan) 1)))
        (:quote (t3-book-substitution-quoted-base lib target))
        (:list
         (let* ((head-type (t3-book-term-collections-constructed-type
                            (1- n) lib *t3-book-substitution-term* (cadr plan) known))
                (tail (t3-book-term-collections-constructed-type-tail value head-type)))
           (if (failure-p tail)
               tail
             (proof-with-checked-results
                 ((tail-type (t3-book-term-collections-constructed-type
                              (1- n) lib *t3-book-substitution-list* tail known))
                  (pair (t3-scan-typed-pair lib head-type tail-type))
                  (opened (t3-book-term-collections-shallow lib target nil)))
               (proof-proof-transport proof pair opened)))))
        (:application
         (proof-with-checked-results
             ((args-type (t3-book-term-collections-constructed-type
                          (1- n) lib *t3-book-substitution-list* (cadr plan) known))
              (opened (t3-book-term-collections-shallow lib target (list args-type))))
           (proof-proof-true-from-eq proof opened)))
        (otherwise plan)))))

(defun t3-book-term-collections-leaf-types-selected-list (lib tails typed)
  (cond ((endp tails) (t3-book-substitution-total-list-components lib typed))
        ((not (proof-is-call (car tails) *library-cdr*))
         '(:failure "unsupported" ""))
        (t (proof-with-checked-results
               ((parts (t3-book-substitution-total-list-components lib typed)))
             (t3-book-term-collections-leaf-types-selected-list lib (cdr tails) (cadr parts))))))

(defun t3-book-term-collections-leaf-types-leaf-smaller
    (call lib variable measure expanded evidence arguments substitutions)
  (if (not (proof-is-call call *t3-book-term-collections-if-leaves*))
      '(:failure "unsupported" "")
    (proof-with-checked-results ((item (proof-term-at call 1))
                                 (path (t3-size-selector-path item variable)))
      (if (or (eq path :none) (< (len path) 2))
          '(:failure "unsupported" "")
        (let* ((proof (library-library-proof lib))
               (existing (assoc-equal item substitutions))
               (key (if existing (cdr existing) (list (list variable item))))
               (substitutions (if existing substitutions (table-put substitutions item key)))
               (child-rank (list *library-count* item)))
          (proof-with-checked-results
              ((descents (t3-size-count-descent lib child-rank measure evidence))
               (claim (proof-subst expanded (proof-bindings-table key nil)))
               (hypothesis (proof-ite (list *proof-ordinal-less* child-rank measure)
                                      claim *proof-true*))
               (assumed (proof-proof-assume proof hypothesis t))
               (step (proof-proof-prove-if proof assumed (car descents)))
               (parts (t3-book-term-collections-leaf-types-selected-list
                       lib (reverse (seq-slice path 1 -1)) arguments))
               (proved (proof-proof-modus-ponens proof step (car parts))))
            (list proved (cdr descents) substitutions)))))))

(defun t3-book-term-collections-leaf-types-leaf-append
    (value tests lib accepted variable measure expanded substitutions)
  (let ((proof (library-library-proof lib))
        (children (cdr value)))
    (proof-with-checked-results
        ((evidence (t3-logic-evidence-init lib tests nil nil))
         (original (t3-book-substitution-original-arguments lib accepted evidence)))
      (let ((arguments (cadar original))
            (evidence (cdr original)))
        (if (endp children)
            '(:failure "unproved" "")
          (proof-with-checked-results
              ((left (t3-book-term-collections-leaf-types-leaf-smaller
                      (car children) lib variable measure expanded evidence arguments substitutions)))
            (if (endp (cdr children))
                '(:failure "unproved" "")
              (proof-with-checked-results
                  ((right (t3-book-term-collections-leaf-types-leaf-smaller
                           (cadr children) lib variable measure expanded (cadr left)
                           arguments (caddr left))))
                (if (consp (cddr children))
                    (proof-with-checked-results
                        ((extra (t3-book-term-collections-leaf-types-leaf-smaller
                                 (caddr children) lib variable measure expanded (cadr right)
                                 arguments (caddr right))))
                      '(:failure "unproved" ""))
                  (proof-with-checked-results
                      ((append-step (library-library-cite
                                     lib *t3-book-term-collections-append-type* children nil))
                       (without-left (proof-proof-prove-if proof append-step (car left)))
                       (proved (proof-proof-prove-if proof without-left (car right))))
                    (cons proved (caddr right))))))))))))

(defun t3-book-term-collections-leaf-types-leaf
    (value tests lib accepted variable measure expanded substitutions)
  (cond
   ((equal value (list *proof-cons* variable *proof-false*))
    (proof-with-checked-results
        ((nil-type (t3-book-substitution-quoted-base
                    lib (list *t3-book-substitution-list* *proof-false*)))
         (head (t3-scan-typed-pair lib accepted nil-type))
         (opened (t3-book-term-collections-shallow lib (list *t3-book-substitution-list* value) nil))
         (proved (proof-proof-transport (library-library-proof lib) head opened)))
      (cons proved substitutions)))
   ((not (proof-is-call value *t3-list-bounds-append*))
    '(:failure "unsupported" ""))
   (t (t3-book-term-collections-leaf-types-leaf-append
       value tests lib accepted variable measure expanded substitutions))))

(defun t3-book-term-collections-aligned-types-leaf
    (value tests lib left formula pairs right-head right-rest)
  (if (equal value *proof-false*)
      (t3-book-substitution-quoted-base lib (list *t3-book-substitution-list* *proof-false*))
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((evidence (t3-logic-evidence-init lib tests nil nil))
           (cons-found (t3-logic-evidence-require evidence (list *proof-consp* *library-x*)))
           (parts (t3-book-substitution-list-components lib left (car cons-found)))
           (builtin (library-library-builtin lib 3 *library-x*))
           (descent (proof-proof-discharge proof builtin (car cons-found)))
           (decrease (proof-step-first descent))
           (child (proof-subst formula (proof-bindings-table pairs nil)))
           (assumed (proof-proof-assume proof (proof-ite decrease child *proof-true*) t))
           (ih (proof-proof-prove-if proof assumed descent))
           (ih (proof-proof-prove-if proof ih (cadr parts)))
           (ih (proof-proof-prove-if proof ih right-rest)))
        (t3-book-term-collections-constructed-type
         1000000 lib *t3-book-substitution-list* value (list (car parts) right-head ih))))))

(defun t3-book-term-collections-typed-conjunction-leaf (value tests lib first second)
  (declare (ignore tests))
  (t3-book-term-collections-constructed-type
   1000000 lib *t3-book-substitution-term* value (list first second)))

(defund t3-book-term-collections-by-value-answer (lib request recipe context substitutions)
  (let ((value (cadr request))
        (tests (caddr request)))
    (if (eq recipe :collect)
        (t3-book-term-collections-leaf-types-leaf
         value tests lib (car context) (cadr context) (caddr context)
         (cadddr context) substitutions)
      (proof-with-checked-results
          ((step (if (eq recipe :aligned)
                     (t3-book-term-collections-aligned-types-leaf
                      value tests lib (car context) (cadr context) (caddr context)
                      (cadddr context) (car (cddddr context)))
                   (t3-book-term-collections-typed-conjunction-leaf
                    value tests lib (car context) (cadr context)))))
        (cons step substitutions)))))

(defun t3-book-term-collections-by-value
    (n lib template request recipe context substitutions)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "t3-book-term-collections-by-value"))
   ((failure-p request) request)
   ((not (eq (car request) :t3-book-term-collections-leaf)) (cons request substitutions))
   (t
    (proof-with-checked-results
        ((answer (t3-book-term-collections-by-value-answer lib request recipe context substitutions)))
      (t3-book-term-collections-by-value
       (1- n) lib template
       (t3-book-term-collections-by-value-resume lib template request (car answer))
       recipe context (cdr answer))))))

(defun t3-book-term-collections-leaf-types (lib name formula)
  (proof-with-checked-results
      ((lib (t3-book-term-collections-append-lists lib))
       (parts (proof-list-of-length formula 3))
       (head (proof-term-at (caddr parts) 0)))
    (let ((proof (library-library-proof lib))
          (input-type (cadr parts))
          (output (caddr parts))
          (template (list *t3-book-substitution-list* *proof-result*)))
      (proof-with-checked-results
          ((equation (and (proof-compound head) (proof-proof-beta proof output)))
           (goal (if equation (t3-book-term-collections-step-term-at equation 2) output))
           (expanded (list *library-implies* input-type goal))
           (accepted (proof-proof-assume proof input-type t))
           (variable (proof-term-at input-type 1))
           (measure (list *library-count* variable))
           (call (proof-term-at goal 1))
           (opened (proof-proof-unfold proof call))
           (body (t3-book-term-collections-step-term-at opened 2))
           (first (t3-book-term-collections-by-value-start lib body nil))
           (result (t3-book-term-collections-by-value
                    1000000 lib template first :collect
                    (list accepted variable measure expanded) nil))
           (proved (library-library-transport-argument lib (car result) opened 1))
           (step (t3-book-lemmas-implication lib expanded proved))
           (rank (library-library-builtin lib 1 variable))
           (induction (proof-proof-induct proof rank step expanded measure
                                          (table-values (cdr result))))
           (finished (if equation
                         (proof-with-checked-results
                             ((reflexive (proof-proof-reflexive proof formula))
                              (unfolded (proof-proof-rewrite proof reflexive equation '(1 2 2))))
                           (proof-proof-transport proof induction unfolded))
                       induction))
           (entry (proof-proof-entry "theorem" name (list name) (list finished))))
        (cons entry lib)))))

(defun t3-book-term-collections-aligned-types (lib operation)
  (let* ((proof (library-library-proof lib))
         (call (list operation *library-x* *library-y*))
         (measure (list *library-count* *library-x*))
         (pairs (list (list *library-x* (list *library-cdr* *library-x*))
                      (list *library-y* (list *library-cdr* *library-y*)))))
    (proof-with-checked-results
        ((left (proof-proof-assume proof (list *t3-book-substitution-list* *library-x*) t))
         (right (proof-proof-assume proof (list *t3-book-substitution-list* *library-y*) t))
         (left-type (proof-step-first left))
         (right-type (proof-step-first right))
         (inner (proof-ite right-type (list *t3-book-substitution-list* call) *proof-true*))
         (formula (proof-ite left-type inner *proof-true*))
         (right-parts (t3-book-substitution-total-list-components lib right))
         (opened (proof-proof-unfold proof call))
         (body (t3-book-term-collections-step-term-at opened 2))
         (request (t3-book-term-collections-by-value-start lib body nil))
         (result (t3-book-term-collections-by-value
                  1000000 lib (list *t3-book-substitution-list* *proof-result*) request :aligned
                  (list left formula pairs (car right-parts) (cadr right-parts)) nil))
         (step (library-library-transport-argument lib (car result) opened 1))
         (inner-case (t3-scan-conclusion lib inner step))
         (case-step (t3-scan-conclusion lib formula inner-case))
         (rank (library-library-builtin lib 1 *library-x*)))
      (proof-proof-induct proof rank case-step formula measure (list pairs)))))

(defun t3-book-term-collections-typed-conjunction (lib)
  (let* ((proof (library-library-proof lib))
         (call (list *t3-book-term-collections-conjoin2* *library-x* *library-y*))
         (joined (list *t3-book-substitution-term* call)))
    (proof-with-checked-results
        ((first (proof-proof-assume proof (list *t3-book-substitution-term* *library-x*) t))
         (second (proof-proof-assume proof (list *t3-book-substitution-term* *library-y*) t))
         (equation (proof-proof-unfold proof call))
         (value (t3-book-term-collections-step-term-at equation 2))
         (request (t3-book-term-collections-by-value-start lib value nil))
         (result (t3-book-term-collections-by-value
                  1000000 lib (list *t3-book-substitution-term* *proof-result*) request
                  :conjoin (list first second) nil))
         (lemma (library-library-transport-argument lib (car result) equation 1))
         (first-type (proof-step-first first))
         (second-type (proof-step-first second))
         (lib (library-library-lemma lib "T3-CONJOIN2-TERM" joined lemma
                                     (list (proof-neg first-type) (proof-neg second-type))))
         (proof (library-library-proof lib))
         (typed (proof-proof-assume proof (list *t3-book-substitution-list* *library-x*) t))
         (goal (list *t3-book-substitution-term*
                     (list *t3-book-term-collections-conjoin* *library-x*)))
         (typed-literal (proof-step-first typed))
         (formula (proof-ite typed-literal goal *proof-true*))
         (cells (list *proof-consp* *library-x*))
         (present (proof-proof-assume proof cells t))
         (parts (t3-book-substitution-list-components lib typed present))
         (tail (t3-list-bounds-tail-hypothesis lib formula present))
         (ih (proof-proof-prove-if proof tail (cadr parts)))
         (source (t3-book-term-collections-shallow lib (cadr goal) (list present)))
         (body (t3-book-term-collections-step-term-at source 2))
         (body-no (proof-term-at body 3))
         (result (library-library-cite lib "T3-CONJOIN2-TERM" (cdr body-no) (list (car parts) ih)))
         (if-true (proof-proof-if-true proof body))
         (yes (library-library-transport-argument lib (car parts) if-true 1))
         (if-false (proof-proof-if-false proof body))
         (no (library-library-transport-argument lib result if-false 1))
         (test (proof-term-at body 1))
         (cases (proof-proof-cases proof test yes no))
         (step (library-library-transport-argument lib cases source 1))
         (absent (proof-proof-assume proof cells nil))
         (base (t3-book-term-collections-shallow lib (cadr goal) (list absent)))
         (base-body (t3-book-term-collections-step-term-at base 2))
         (empty (t3-book-substitution-quoted-base lib (list *t3-book-substitution-term* base-body)))
         (start (library-library-transport-argument lib empty base 1))
         (case-step (t3-scan-conclusion lib formula step))
         (case-base (t3-scan-conclusion lib formula start))
         (proved (t3-list-bounds-tail-induction lib formula case-step case-base)))
      (library-library-lemma lib "T3-CONJOIN-TERM" formula proved nil))))

(defun t3-book-term-collections-equality-types-conjoin (lib goal step)
  (proof-with-checked-results
      ((lib (t3-book-term-collections-typed-conjunction lib))
       (call (proof-term-at goal 1))
       (equation (t3-book-term-collections-shallow lib call nil))
       (body (t3-book-term-collections-step-term-at equation 2))
       (conjunction (library-library-cite lib "T3-CONJOIN-TERM" (cdr body) nil))
       (result (proof-proof-prove-if (library-library-proof lib) conjunction step))
       (proved (library-library-transport-argument lib result equation 1)))
    (cons proved lib)))

(defund t3-book-term-collections-equality-types-component-parts (proof step)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (no (and (proof-is-call literal *proof-if*) (proof-term-at literal 3))))
    (and (equal no *proof-false*) (proof-proof-conjunct proof step))))

; Inspect the next component for a failure before checking the limit.
(defun t3-book-term-collections-equality-types-components (remaining proof step)
  (declare (xargs :measure (nfix remaining)))
  (proof-with-checked-results
      ((parts (t3-book-term-collections-equality-types-component-parts proof step)))
    (cond ((zp remaining) '(:failure "unproved" ""))
          (parts
           (proof-with-checked-results
               ((rest (t3-book-term-collections-equality-types-components
                       (1- remaining) proof (cadr parts))))
             (cons (car parts) rest)))
          (t (list step)))))

(defun t3-book-term-collections-equality-types (lib name formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((formula-arg (proof-term-at formula 2))
         (head (proof-term-at formula-arg 0))
         (opened (and (proof-compound head) (proof-proof-beta proof formula-arg)))
         (goal (if opened (t3-book-term-collections-step-term-at opened 2) formula-arg))
         (recognized (t3-book-term-collections-aligned-types lib *t3-book-term-collections-equalities*))
         (recognized-type (proof-step-first recognized))
         (lib (library-library-lemma lib "T3-ALIGNED-EQUALITY-TERMS" recognized-type recognized nil))
         (proof (library-library-proof lib))
         (guard (proof-term-at formula 1))
         (accepted (proof-proof-assume proof guard t))
         (parts (t3-book-term-collections-equality-types-components 3 proof accepted))
         (parts (proof-list-of-length parts 3))
         (left (t3-book-term-collections-step-term-at (car parts) 1))
         (right (t3-book-term-collections-step-term-at (cadr parts) 1))
         (rule (library-library-cite lib "T3-ALIGNED-EQUALITY-TERMS" (list left right) nil))
         (step (proof-proof-prove-if proof rule (car parts)))
         (step (proof-proof-prove-if proof step (cadr parts)))
         (predicate (proof-term-at goal 0))
         (result (if (equal predicate *t3-book-substitution-term*)
                     (t3-book-term-collections-equality-types-conjoin lib goal step)
                   (cons step lib)))
         (lib (cdr result))
         (step (if opened (proof-proof-transport (library-library-proof lib) (car result) opened)
                 (car result)))
         (proved (t3-book-lemmas-implication lib formula step))
         (entry (proof-proof-entry "theorem" name (list name) (list proved))))
      (cons entry lib))))
