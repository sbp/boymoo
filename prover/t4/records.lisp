(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-records-record* (proof-sym "RCDP" "ACL2"))
(defconst *t4-records-wrapped* (proof-sym "LSP" "ACL2"))
(defconst *t4-records-before* (proof-sym "<<" "ACL2"))
(defconst *t4-records-insert* (proof-sym "S-AUX" "ACL2"))
(defconst *t4-records-delete* (proof-sym "DELETE-KEY" "ACL2"))
(defconst *t4-records-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *t4-records-get* (proof-sym "G" "ACL2"))
(defconst *t4-records-set* (proof-sym "S" "ACL2"))
(defconst *t4-records-atom* (proof-cl "ATOM"))
(defconst *t4-records-endp* (proof-cl "ENDP"))
(defconst *t4-records-null* (proof-cl "NULL"))
(defconst *t4-records-w* (proof-sym "W" "ACL2"))
(defconst *t4-records-fields* (proof-sym "SELF-RECORD-FIELDS" "ACL2"))
(defconst *t4-records-backing* (proof-sym "SELF-RECORD-BACKING" "ACL2"))
(defconst *t4-records-pack* (proof-sym "SELF-RECORD-PACK" "ACL2"))
(defconst *t4-records-update* (proof-sym "SELF-RECORD-UPDATE" "ACL2"))

(defun t4-records-first-key (record)
  (list *library-car* (list *library-car* record)))

(defun t4-records-above (lower record)
  (proof-ite (list *t4-records-atom* record) *proof-true*
             (list *t4-records-before* lower (t4-records-first-key record))))

(defun t4-records-field (key record)
  (list *library-cdr* (list *t4-records-assoc* key record)))

(defun t4-records-valid-backing (backing)
  (proof-ite backing (proof-neg (list *t4-records-wrapped* backing)) *proof-true*))

(defun t4-records-records-init (lib)
  (list :t4-records lib))

(defun t4-records-records-lib (records)
  (cadr records))

(defun t4-records-proof (records)
  (library-library-proof (t4-records-records-lib records)))

; A :WITH binding takes its value and the resulting Records object.
(defmacro t4-records-let (records bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings)))
      (if (eq (car binding) :with)
          (let ((name (cadr binding))
                (form (caddr binding)))
            `(proof-with-checked-results ((,name ,form))
               (let ((,records (cdr ,name))
                     (,name (car ,name)))
                 (t4-records-let ,records ,(cdr bindings) ,result))))
        `(proof-with-checked-results (,binding)
           (t4-records-let ,records ,(cdr bindings) ,result))))))

(defun t4-records-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun t4-records-slice-arguments (term)
  (if (integerp term)
      '(:failure "failure" "")
    (cdr term)))

(defun t4-records-step-arguments (step size)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (arguments (t4-records-slice-arguments literal)))
    (proof-list-of-length arguments size)))

(defun t4-records-records-has (records name)
  (if (assoc-equal (library-lemma-name name)
                   (proof-proof-facts (t4-records-proof records)))
      t
    nil))

(defun t4-records-records-use (records name values premises)
  (proof-proof-use (t4-records-proof records) (library-lemma-name name)
                   (seq-zip (list *library-x* *library-y* *library-z* *t4-records-w*)
                           values)
                   premises))

(defun t4-records-add-lemma (records name literal step conditions)
  (proof-with-checked-results
      ((lib (library-library-lemma (t4-records-records-lib records)
                                   name literal step conditions)))
    (t4-records-records-init lib)))

(defun t4-records-simplify (records term evidence definitions)
  (proof-with-checked-results
      ((result (t4-ordinals-ordinals-simplify (t4-records-records-lib records)
                                             term evidence definitions)))
    (cons (car result) (t4-records-records-init (cdr result)))))

(defun t4-records-prove (records term evidence definitions)
  (proof-with-checked-results
      ((result (t4-ordinals-ordinals-prove (t4-records-records-lib records)
                                          term evidence definitions)))
    (cons (car result) (t4-records-records-init (cdr result)))))

(defun t4-records-records-choose (records equation condition)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((rhs (t4-records-step-at equation 2))
         (chosen (proof-proof-select proof rhs condition)))
      (proof-proof-chain proof equation (list chosen)))))

(defun t4-records-records-unfold-side (records call shape positive)
  (t4-records-let records
      ((equation (proof-proof-unfold (t4-records-proof records) call))
       (rhs (t4-records-step-at equation 2))
       (test (proof-term-at rhs 1))
       (:with condition (t4-records-prove records (if positive (proof-neg test) test)
                                         (list shape)
                                         (list *t4-records-endp* *t4-records-atom* *proof-not*)))
       (step (t4-records-records-choose records equation condition)))
    (cons step records)))

(defun t4-records-records-cons (records term)
  (proof-with-checked-results ((arguments (t4-records-slice-arguments term)))
    (proof-proof-fact (t4-records-proof records) "consp-cons"
                      (seq-zip (list *library-x* *library-y*) arguments))))

(defun t4-records-records-projections (records step pair)
  (let ((lib (t4-records-records-lib records))
        (proof (t4-records-proof records)))
    (proof-with-checked-results
        ((args (t4-records-slice-arguments pair))
         (car-equation (library-library-axiom lib "CAR-CONS" args))
         (step (proof-proof-rewrite-first proof step car-equation))
         (cdr-equation (library-library-axiom lib "CDR-CONS" args)))
      (proof-proof-rewrite-first proof step cdr-equation))))

(defun t4-records-records-lift (records step equation template)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results ((reversed (proof-proof-symmetric proof equation)))
      (proof-proof-rewrite-result proof step reversed template *proof-result*))))

(defun t4-records-records-nil-from-denial (records denied)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((obj (t4-records-step-at denied 1))
         (either (proof-proof-nil-or-true proof obj))
         (positive (proof-proof-front proof either obj)))
      (proof-proof-cut proof positive denied))))

(defun t4-records-records-denial-from-nil (records equation)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results ((rhs (t4-records-step-at equation 2)))
      (if (not (equal rhs *proof-false*))
          '(:failure "inference-mismatch" "")
        (proof-with-checked-results
            ((not-nil (proof-proof-not-nil proof))
             (reversed (proof-proof-symmetric proof equation)))
          (proof-proof-rewrite proof not-nil reversed '(1 1)))))))

(defun t4-records-records-nonempty (records cons-step)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((obj (t4-records-step-at cons-step 1))
         (denied (proof-proof-assume proof obj nil))
         (equation (t4-records-records-nil-from-denial records denied))
         (contradicted (proof-proof-rewrite proof cons-step equation '(1 1)))
         (atomic (t4-records-prove records (proof-neg (list *proof-consp* *proof-false*))
                                   nil (list *proof-not*)))
         (joined (proof-proof-cut (t4-records-proof (cdr atomic))
                                  contradicted (car atomic))))
      (proof-proof-front (t4-records-proof (cdr atomic)) joined obj))))

(defund t4-records-record-atom-step (records value)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results ((literal (proof-step-first value)))
      (cond ((proof-is-call literal *proof-equal*) value)
            ((proof-is-call literal *proof-not*)
             (t4-records-records-nil-from-denial records value))
            (t (proof-with-checked-results
                   ((opened (proof-proof-unfold proof literal))
                    (value (proof-proof-rewrite proof value opened '(1))))
                 (list :rewrite value)))))))

(defun t4-records-record-atom-unfold (n records value)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t4-records-record-atom-unfold")
    (let ((next (t4-records-record-atom-step records value)))
      (if (eq (car next) :rewrite)
          (t4-records-record-atom-unfold (1- n) records (cadr next))
        next))))

(defun t4-records-records-record-atom (records record atom-step)
  (t4-records-let records
      ((obj (t4-records-step-at record 1))
       (literal (proof-step-first record))
       (:with view (t4-records-records-unfold-side records literal atom-step nil))
       (value (proof-proof-rewrite (t4-records-proof records) record view '(1)))
       (step (t4-records-record-atom-unfold 1000000 records value)))
    (cons step records)))

(defun t4-records-records-nonempty-record (records typed nonzero)
  (t4-records-let records
      ((obj (t4-records-step-at typed 1))
       (shape (list *proof-consp* obj))
       (assumed-atom (proof-proof-assume (t4-records-proof records) shape nil))
       (:with empty (t4-records-records-record-atom records typed assumed-atom))
       (denial (t4-records-records-denial-from-nil records empty))
       (joined (proof-proof-cut (t4-records-proof records) nonzero denial))
       (step (proof-proof-front (t4-records-proof records) joined shape)))
    (cons step records)))

(defun t4-records-records-null-test (records step positive)
  (t4-records-let records
      ((obj (if positive (proof-step-first step) (t4-records-step-at step 1)))
       (equals-nil (proof-eq obj *proof-false*))
       (:with testing (t4-records-simplify records (list *t4-records-null* obj)
                                           nil (list *t4-records-null* (proof-cl "EQ")))))
    (let ((proof (t4-records-proof records)))
      (proof-with-checked-results
          ((result
            (if positive
                (proof-with-checked-results
                    ((same (proof-proof-assume proof equals-nil t))
                     (rewritten (proof-proof-rewrite proof step same '(1)))
                     (impossible (proof-proof-tidy proof rewritten))
                     (front (proof-proof-front proof impossible (proof-neg equals-nil)))
                     (reversed (proof-proof-symmetric proof testing)))
                  (proof-proof-rewrite proof front reversed '(1 1)))
              (proof-with-checked-results
                  ((nil-equation (t4-records-records-nil-from-denial records step)))
                (proof-proof-transport proof nil-equation testing)))))
        (cons result records)))))

(defun t4-records-records-denied-null (records hypothesis)
  (t4-records-let records
      ((test (t4-records-step-at hypothesis 1))
       (obj (proof-term-at test 1))
       (:with equality (t4-records-simplify records test nil
                                             (list *t4-records-null* (proof-cl "EQ"))))
       (reduced (proof-proof-rewrite (t4-records-proof records) hypothesis equality '(1 1)))
       (either (proof-proof-nil-or-true (t4-records-proof records) obj))
       (step (proof-proof-cut (t4-records-proof records) either reduced)))
    (cons step records)))

(defund t4-records-change-arg (proof step change)
  (proof-with-checked-results ((pair (proof-list-of-length change 2)))
    (proof-proof-rewrite proof step (cadr pair) (list 1 2 (car pair)))))

(defun t4-records-change-args-visit (proof step changes)
  (declare (xargs :measure (acl2-count changes)))
  (if (endp changes)
      (proof-proof-tidy proof step)
    (proof-with-checked-results ((step (t4-records-change-arg proof step (car changes))))
      (t4-records-change-args-visit proof step (cdr changes)))))

(defun t4-records-records-change-args (records term changes)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results ((step (proof-proof-reflexive proof term)))
      (t4-records-change-args-visit proof step changes))))

(defun t4-records-records-transitive (records left right)
  (let ((lib (t4-records-records-lib records)))
    (proof-with-checked-results
        ((parts (t4-records-step-arguments left 2))
         (c (t4-records-step-at right 2))
         (axiom (library-library-axiom lib "<<-TRANSITIVE" (append parts (list c))))
         (joined (t4-division-combine lib (list left right))))
      (proof-proof-modus-ponens (t4-records-proof records) axiom joined))))

(defun t4-records-records-reversed-distinct (records difference)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((equality (t4-records-step-at difference 1))
         (arguments (t4-records-slice-arguments equality))
         (parts (proof-list-of-length arguments 2))
         (same (proof-eq (cadr parts) (car parts)))
         (assumed (proof-proof-assume proof same t))
         (symmetric (proof-proof-symmetric proof assumed))
         (joined (proof-proof-cut proof symmetric difference)))
      (proof-proof-front proof joined (proof-neg same)))))

(defun t4-records-records-reverse-order (records not-before unequal)
  (let ((lib (t4-records-records-lib records)))
    (proof-with-checked-results
        ((ordering (t4-records-step-at not-before 1))
         (arguments (t4-records-slice-arguments ordering))
         (parts (proof-list-of-length arguments 2))
         (axiom (library-library-axiom lib "<<-TRICHOTOMY"
                                     (list (cadr parts) (car parts))))
         (distinct (t4-records-records-reversed-distinct records unequal))
         (joined (t4-division-combine lib (list not-before distinct))))
      (proof-proof-modus-ponens (t4-records-proof records) axiom joined))))

(defun t4-records-cons-record-lemma (records name)
  (let ((pair (list *proof-cons* *library-x* *library-y*)))
    (t4-records-let records
        ((shape (t4-records-records-cons records pair))
         (:with step (t4-records-records-unfold-side records
                       (list *t4-records-record* pair) shape t))
         (step (t4-records-records-projections records step pair))
         (claim (proof-step-first step)))
      (t4-records-add-lemma records name claim step nil))))

(defun t4-records-records-cons-record (records head tail)
  (let ((name "RECORD-CONS-EQUATION"))
    (proof-with-checked-results
        ((records (if (t4-records-records-has records name)
                      records
                    (t4-records-cons-record-lemma records name)))
         (step (t4-records-records-use records name (list head tail) nil)))
      (cons step records))))

(defun t4-records-records-components (records record cons-step)
  (t4-records-let records
      ((obj (t4-records-step-at record 1))
       (head (list *library-car* obj))
       (tail (list *library-cdr* obj))
       (axiom (library-library-axiom (t4-records-records-lib records)
                                  "CAR-CDR-ELIM" (list obj)))
       (decomposition (proof-proof-modus-ponens (t4-records-proof records) axiom cons-step))
       (reversed (proof-proof-symmetric (t4-records-proof records) decomposition))
       (known (proof-proof-rewrite (t4-records-proof records) record reversed '(1 1)))
       (:with equation (t4-records-records-cons-record records head tail))
       (known (proof-proof-rewrite (t4-records-proof records) known equation '(1))))
    (let ((proof (t4-records-proof records))
          (test (list *t4-records-atom* tail)))
      (proof-with-checked-results
          ((head-parts (proof-proof-conjunct proof known))
           (rest (proof-proof-conjunct proof (cadr head-parts)))
           (tail-test (cadr rest))
           (yes (proof-proof-assume proof test t))
           (no (proof-proof-assume proof test nil))
           (selected (proof-proof-prove-if proof tail-test no))
           (nonempty-parts (proof-proof-conjunct proof selected))
           (opened (proof-proof-unfold proof (list *t4-records-record* tail)))
           (atom-record (t4-records-records-choose records opened yes))
           (empty-branch (proof-proof-prove-if proof tail-test yes))
           (empty-record (proof-proof-transport proof empty-branch atom-record))
           (typed (proof-proof-cases proof test empty-record (car nonempty-parts)))
           (order (t4-records-above (list *library-car* head) tail))
           (truth (proof-proof-prove proof *proof-true* nil nil))
           (if-true (proof-proof-if-true proof order))
           (empty-order (proof-proof-transport proof truth if-true))
           (if-false (proof-proof-if-false proof order))
           (tail-order (proof-proof-transport proof (cadr nonempty-parts) if-false))
           (ordered (proof-proof-cases proof test empty-order tail-order)))
        (cons (list (car head-parts) (car rest) typed ordered) records)))))

(defun t4-records-records-ordered-record (records head-cons value tail-record lower)
  (let ((proof (t4-records-proof records)))
    (t4-records-let records
        ((head (t4-records-step-at head-cons 1))
         (tail (t4-records-step-at tail-record 1))
         (test (list *t4-records-atom* tail))
         (empty-assumed (proof-proof-assume proof test t))
         (solid (proof-proof-assume proof test nil))
         (tail-literal (proof-step-first tail-record))
         (opened (proof-proof-unfold proof tail-literal))
         (selected (t4-records-records-choose records opened empty-assumed))
         (empty (proof-proof-rewrite proof tail-record selected '(1)))
         (ordering (proof-proof-prove-if proof lower solid))
         (typed (t4-division-combine (t4-records-records-lib records) (list tail-record ordering)))
         (empty-literal (proof-step-first empty))
         (typed-literal (proof-step-first typed))
         (tail-formula (proof-ite test empty-literal typed-literal))
         (if-true (proof-proof-if-true proof tail-formula))
         (yes (proof-proof-transport proof empty if-true))
         (if-false (proof-proof-if-false proof tail-formula))
         (no (proof-proof-transport proof typed if-false))
         (tail-proof (proof-proof-cases proof test yes no))
         (joined (t4-division-combine (t4-records-records-lib records)
                                      (list head-cons value tail-proof)))
         (:with equation (t4-records-records-cons-record records head tail))
         (step (proof-proof-transport (t4-records-proof records) joined equation)))
      (cons step records))))

(defun t4-records-records-weaken-order (records bound tail)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((lower (t4-records-step-at bound 1))
         (result (t4-records-above lower tail))
         (truth (proof-proof-prove proof *proof-true* nil nil))
         (if-true (proof-proof-if-true proof result))
         (yes (proof-proof-transport proof truth if-true))
         (if-false (proof-proof-if-false proof result))
         (no (proof-proof-transport proof bound if-false)))
      (proof-proof-cases proof (cadr result) yes no))))

(defun t4-records-records-empty-order (records lower)
  (proof-with-checked-results
      ((proof (t4-records-prove records (t4-records-above lower *proof-false*)
                               nil (list *t4-records-atom* *proof-not*))))
    (car proof)))

(defun t4-records-records-record-nil (records)
  (proof-with-checked-results
      ((proof (t4-records-prove records (list *t4-records-record* *proof-false*) nil
                               (list *t4-records-record* *t4-records-atom*
                                     *t4-records-null* (proof-cl "EQ") *proof-not*))))
    (car proof)))

(defun t4-records-records-assoc-cons (records key pair)
  (t4-records-let records
      ((shape (t4-records-records-cons records pair))
       (:with view (t4-records-records-unfold-side records (list *t4-records-assoc* key pair)
                                                  shape t))
       (view (t4-records-records-projections records view pair))
       (head (proof-term-at pair 1))
       (step (if (proof-is-call head *proof-cons*)
                 (t4-records-records-projections records view head)
               view)))
    (cons step records)))

(defun t4-records-records-assoc-nil (records key)
  (t4-records-let records
      ((:with atomic (t4-records-prove records (proof-neg (list *proof-consp* *proof-false*))
                                       nil (list *proof-not*)))
       (view (t4-records-records-unfold-side records
                (list *t4-records-assoc* key *proof-false*) atomic nil)))
    (car view)))

(defun t4-records-records-before-distinct (records ordered)
  (let ((lib (t4-records-records-lib records))
        (proof (t4-records-proof records)))
    (proof-with-checked-results
        ((parts (t4-records-step-arguments ordered 2))
         (test (proof-eq (car parts) (cadr parts)))
         (assumed (proof-proof-assume proof test t))
         (same (proof-proof-rewrite proof ordered assumed '(1 1)))
         (irreflexive (library-library-axiom lib "<<-IRREFLEXIVE" (list (cadr parts))))
         (joined (proof-proof-cut proof same irreflexive)))
      (proof-proof-front proof joined (proof-neg test)))))

(defun t4-records-by-value-join (records value template yes no)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((if-true (proof-proof-if-true proof value))
         (yes (t4-records-records-lift records yes if-true template))
         (if-false (proof-proof-if-false proof value))
         (no (t4-records-records-lift records no if-false template)))
      (proof-proof-cases proof (cadr value) yes no))))

(defund t4-records-by-value-open (records value)
  (proof-with-checked-results
      ((equation (proof-proof-beta (t4-records-proof records) value))
       (opened (t4-records-step-at equation 2)))
    (cons opened equation)))

; Each traversal calls its leaf proof in place, with the library from the
; preceding branch. The leaf receives the values captured by its recipe.
(defmacro t4-records-define-by-value (name leaf captures)
  `(defun ,name (n records value template tests ,@captures)
     (declare (xargs :measure (nfix n)))
     (cond
      ((not (o< (nfix (1- n)) (nfix n)))
       (list :failure "fuel" ,(string-downcase (symbol-name name))))
      ((proof-is-call value *proof-if*)
       (t4-records-let records
           ((branches (proof-list-of-length (cdr value) 3))
            (:with yes (,name (1- n) records (cadr branches) template
                        (append tests (list (list (car branches) t))) ,@captures))
            (:with no (,name (1- n) records (caddr branches) template
                       (append tests (list (list (car branches) nil))) ,@captures))
            (step (t4-records-by-value-join records value template yes no)))
         (cons step records)))
      ((and (proof-compound value) (endp value))
       '(:failure "failure" ""))
      ((and (proof-compound value) (proof-compound (car value)))
       (t4-records-let records
           ((opened (t4-records-by-value-open records value))
            (:with step (,name (1- n) records (car opened) template tests ,@captures))
            (step (t4-records-records-lift records step (cdr opened) template)))
         (cons step records)))
      (t (t4-records-let records
             ((:with step (,leaf value tests records ,@captures))
              (literal (proof-step-first step))
              (target (proof-subst template (list (cons *proof-result* value)))))
           (if (equal literal target)
               (cons step records)
             '(:failure "failure" "")))))))

(defun t4-records-records-insert-order-leaf (pair tests records key-bound old bound-template)
  (let ((lib (t4-records-records-lib records))
        (proof (t4-records-proof records)))
    (proof-with-checked-results
        ((head (proof-term-at pair 1))
         (step
          (cond
           ((equal head (list *proof-cons* *library-x* *library-y*))
            (proof-proof-assume proof key-bound t))
           ((not (equal head (list *library-car* *library-z*)))
            '(:failure "failure" ""))
           (t
            (proof-with-checked-results
                ((evidence (t4-structural-evidence-init lib tests nil))
                 (shape (t4-structural-evidence-require
                         evidence (proof-neg (list *t4-records-atom* *library-z*)))))
              (proof-proof-prove-if proof old (car shape))))))
         (goal (proof-subst bound-template (list (cons *proof-result* pair))))
         (reflexive (proof-proof-reflexive proof goal))
         (car-equation (library-library-axiom lib "CAR-CONS" (cdr pair)))
         (goal-view (proof-proof-rewrite-result proof reflexive car-equation
                                                (proof-eq *proof-true* goal)
                                                (list *library-car* pair)))
         (goal-view
          (if (proof-is-call head *proof-cons*)
              (proof-with-checked-results
                  ((car-equation (library-library-axiom lib "CAR-CONS" (cdr head))))
                (proof-proof-rewrite proof goal-view car-equation '(1 2 2)))
            goal-view))
         (result (proof-proof-transport proof step goal-view)))
      (cons result records))))

(t4-records-define-by-value t4-records-insert-order-by-value
  t4-records-records-insert-order-leaf (key-bound old bound-template))

(defun t4-records-insert-order-lemma (records name)
  (let* ((call (list *t4-records-insert* *library-x* *library-y* *library-z*))
         (key-bound (list *t4-records-before* *t4-records-w* *library-x*))
         (old-bound (t4-records-above *t4-records-w* *library-z*))
         (template (list *t4-records-before* *t4-records-w*
                         (t4-records-first-key *proof-result*))))
    (t4-records-let records
        ((old (proof-proof-assume (t4-records-proof records) old-bound t))
         (equation (proof-proof-unfold (t4-records-proof records) call))
         (value (t4-records-step-at equation 2))
         (:with proof (t4-records-insert-order-by-value
                       1000000 records value template nil key-bound old template))
         (proof (t4-records-records-lift records proof equation template))
         (claim (proof-step-first proof)))
      (t4-records-add-lemma records name claim proof
                            (list (proof-neg key-bound) (proof-neg old-bound))))))

(defun t4-records-records-insert-order
    (records key value record lower before-key before-record)
  (let ((name "RECORD-INSERT-LOWER-BOUND"))
    (proof-with-checked-results
        ((records (if (t4-records-records-has records name)
                      records
                    (t4-records-insert-order-lemma records name)))
         (step (t4-records-records-use records name (list key value record lower)
                                      (list before-key before-record))))
      (cons step records))))

(defun t4-records-records-delete-order-leaf (result tests records guard base-bound)
  (if (equal result *library-y*)
      (cons base-bound records)
    (t4-records-let records
        ((evidence (t4-structural-evidence-init (t4-records-records-lib records) tests nil))
         (answer (t4-structural-evidence-require evidence (list *proof-consp* *library-y*)))
         (shape (car answer))
         (:with nonatom
           (t4-records-prove records (proof-neg (list *t4-records-atom* *library-y*))
                             (list shape) (list *t4-records-atom* *proof-not*)))
         (bound (proof-proof-prove-if (t4-records-proof records) base-bound nonatom)))
      (cond
       ((proof-is-call result *proof-cons*)
        (proof-with-checked-results
            ((eq-key (library-library-axiom (t4-records-records-lib records)
                                            "CAR-CONS" (cdr result)))
             (reversed (proof-proof-symmetric (t4-records-proof records) eq-key))
             (changed (proof-proof-rewrite (t4-records-proof records) bound reversed '(1 2 1)))
             (step (t4-records-records-weaken-order records changed result)))
          (cons step records)))
       ((not (equal result (list *library-cdr* *library-y*)))
        '(:failure "failure" ""))
       (t
        (t4-records-let records
            ((record (proof-proof-assume (t4-records-proof records) guard t))
             (:with parts (t4-records-records-components records record shape)))
          (let ((proof (t4-records-proof records))
                (test (list *t4-records-atom* result))
                (order (t4-records-above *library-z* result)))
            (proof-with-checked-results
                ((solid (proof-proof-assume proof test nil))
                 (selection (proof-proof-prove-if proof (cadddr parts) solid))
                 (bigger (t4-records-records-transitive records bound selection))
                 (true-proof (proof-proof-prove proof *proof-true* nil nil))
                 (if-true (proof-proof-if-true proof order))
                 (yes (proof-proof-transport proof true-proof if-true))
                 (if-false (proof-proof-if-false proof order))
                 (no (proof-proof-transport proof bigger if-false))
                 (step (proof-proof-cases proof test yes no)))
              (cons step records)))))))))

(t4-records-define-by-value t4-records-delete-order-by-value
  t4-records-records-delete-order-leaf (guard base-bound))

(defun t4-records-delete-order-lemma (records name)
  (let* ((guard (list *t4-records-record* *library-y*))
         (old-bound (t4-records-above *library-z* *library-y*))
         (template (t4-records-above *library-z* *proof-result*)))
    (t4-records-let records
        ((base-bound (proof-proof-assume (t4-records-proof records) old-bound t))
         (equation (proof-proof-unfold (t4-records-proof records)
                                      (list *t4-records-delete* *library-x* *library-y*)))
         (value (t4-records-step-at equation 2))
         (:with proof (t4-records-delete-order-by-value
                       1000000 records value template nil guard base-bound))
         (proof (t4-records-records-lift records proof equation template))
         (claim (proof-step-first proof)))
      (t4-records-add-lemma records name claim proof
                            (list (proof-neg guard) (proof-neg old-bound))))))

(defun t4-records-records-delete-order (records key record lower typed old)
  (let ((name "RECORD-DELETE-LOWER-BOUND"))
    (proof-with-checked-results
        ((records (if (t4-records-records-has records name)
                      records
                    (t4-records-delete-order-lemma records name)))
         (step (t4-records-records-use records name (list key record lower) (list typed old))))
      (cons step records))))

(defun t4-records-typed-insert-empty (records head val)
  (let ((proof (t4-records-proof records))
        (lib (t4-records-records-lib records)))
    (proof-with-checked-results
        ((shape (t4-records-records-cons records head))
         (args (t4-records-slice-arguments head))
         (cdr-equation (library-library-axiom lib "CDR-CONS" args))
         (reversed (proof-proof-symmetric proof cdr-equation))
         (value (proof-proof-rewrite proof val reversed '(1)))
         (typed (t4-records-records-record-nil records))
         (bound (t4-records-records-empty-order records (list *library-car* head))))
      (t4-records-records-ordered-record records shape value typed bound))))

(defun t4-records-typed-insert-head
    (records head remainder evidence arg original val typed-tail ordered)
  (let ((proof (t4-records-proof records))
        (lib (t4-records-records-lib records)))
    (proof-with-checked-results
        ((cdr-equation (library-library-axiom lib "CDR-CONS" (cdr head)))
         (reversed (proof-proof-symmetric proof cdr-equation))
         (act (proof-proof-rewrite proof val reversed '(1)))
         (head-key (library-library-axiom lib "CAR-CONS" (cdr head)))
         (type-and-bound
          (if (equal remainder arg)
              (proof-with-checked-results
                  ((answer (t4-structural-evidence-require
                            evidence (list *t4-records-before* *library-x*
                                           (t4-records-first-key arg))))
                   (bound (t4-records-records-weaken-order records (car answer) remainder)))
                (cons original bound))
            (proof-with-checked-results
                ((answer (t4-structural-evidence-require
                          evidence (proof-eq *library-x* (t4-records-first-key arg))))
                 (reversed (proof-proof-symmetric proof (car answer)))
                 (bound (proof-proof-rewrite proof ordered reversed '(1 3 1))))
              (cons typed-tail bound))))
         (reversed (proof-proof-symmetric proof head-key))
         (bound (proof-proof-rewrite proof (cdr type-and-bound) reversed '(1 3 1)))
         (shape (t4-records-records-cons records head)))
      (t4-records-records-ordered-record records shape act (car type-and-bound) bound))))

(defun t4-records-typed-insert-tail
    (records remainder evidence shape parts arg val tail hypothesis decreases)
  (let ((proof (t4-records-proof records))
        (lib (t4-records-records-lib records)))
    (t4-records-let records
        ((assumed (proof-proof-assume proof hypothesis t))
         (discharged (proof-proof-discharge proof decreases shape))
         (ih (proof-proof-prove-if proof assumed discharged))
         (typed-tail (caddr parts))
         (ordered (cadddr parts))
         (joined (t4-division-combine lib (list typed-tail val)))
         (tail-valid (proof-proof-modus-ponens proof ih joined))
         (key (t4-records-first-key arg))
         (not-before (t4-structural-evidence-require
                      evidence (proof-neg (list *t4-records-before* *library-x* key))))
         (not-equal (t4-structural-evidence-require
                     (cdr not-before) (proof-neg (proof-eq *library-x* key))))
         (next-key (t4-records-records-reverse-order records (car not-before) (car not-equal)))
         (:with minimum (t4-records-records-insert-order
                         records *library-x* *library-y* tail key next-key ordered))
         (bound (t4-records-records-weaken-order records minimum remainder)))
      (t4-records-records-ordered-record records (car parts) (cadr parts) tail-valid bound))))

(defun t4-records-records-typed-insert-leaf
    (result tests records arg original val tail hypothesis decreases)
  (t4-records-let records
      ((args (t4-records-slice-arguments result))
       (args (proof-list-of-length args 2))
       (head (car args))
       (remainder (cadr args))
       (evidence (t4-structural-evidence-init (t4-records-records-lib records) tests nil)))
    (if (equal remainder *proof-false*)
        (t4-records-typed-insert-empty records head val)
      (t4-records-let records
          ((answer (t4-structural-evidence-require evidence (list *proof-consp* arg)))
           (shape (car answer))
           (:with parts (t4-records-records-components records original shape))
           (evidence (t4-structural-evidence-with-proof
                      (cdr answer) (t4-records-records-lib records))))
        (if (proof-is-call head *proof-cons*)
            (t4-records-typed-insert-head
             records head remainder evidence arg original val (caddr parts) (cadddr parts))
          (t4-records-typed-insert-tail
           records remainder evidence shape parts arg val tail hypothesis decreases))))))

(t4-records-define-by-value t4-records-typed-insert-by-value
  t4-records-records-typed-insert-leaf (arg original val tail hypothesis decreases))

(defun t4-records-typed-insert-lemma (records name)
  (let* ((arg *library-z*)
         (call (list *t4-records-insert* *library-x* *library-y* arg))
         (guard (proof-ite (list *t4-records-record* arg) *library-y* *proof-false*))
         (claim (list *library-implies* guard (list *t4-records-record* call)))
         (proof (t4-records-proof records)))
    (t4-records-let records
        ((assumption (proof-proof-assume proof guard t))
         (parts (proof-proof-conjunct proof assumption))
         (tail (list *library-cdr* arg))
         (decreases (library-library-builtin (t4-records-records-lib records) 3 arg))
         (binding (list (list arg tail)))
         (decrease (proof-step-first decreases))
         (substituted (proof-subst claim (list (cons arg tail))))
         (hypothesis (proof-ite decrease substituted *proof-true*))
         (template (list *t4-records-record* *proof-result*))
         (saved (proof-proof-unfold proof call))
         (result (t4-records-step-at saved 2))
         (:with proved
           (t4-records-typed-insert-by-value
            1000000 records result template nil arg (car parts) (cadr parts) tail
            hypothesis decreases))
         (proved (t4-records-records-lift records proved saved template))
         (cases (t4-ordinals-ordinals-imply (t4-records-records-lib records) guard proved))
         (ordinal (library-library-builtin (t4-records-records-lib records) 1 arg))
         (induction (proof-proof-induct (t4-records-proof records) ordinal cases
                                        claim (t4-structural-count arg) (list binding))))
      (t4-records-add-lemma records name claim induction nil))))

(defun t4-records-records-typed-insert (records key value record typed nonzero)
  (let ((name "RECORD-VALID-INSERT"))
    (proof-with-checked-results
        ((records (if (t4-records-records-has records name)
                      records
                    (t4-records-typed-insert-lemma records name)))
         (fact (t4-records-records-use records name (list key value record) nil))
         (premise (t4-division-combine (t4-records-records-lib records) (list typed nonzero)))
         (step (proof-proof-modus-ponens (t4-records-proof records) fact premise)))
      (cons step records))))

(defun t4-records-records-typed-delete-leaf
    (value tests records original decreases hypothesis)
  (if (equal value *library-y*)
      (cons original records)
    (t4-records-let records
        ((evidence (t4-structural-evidence-init (t4-records-records-lib records) tests nil))
         (answer (t4-structural-evidence-require evidence (list *proof-consp* *library-y*)))
         (shape (car answer))
         (:with parts (t4-records-records-components records original shape))
         (tail (caddr parts))
         (tail-term (list *library-cdr* *library-y*)))
      (if (equal value tail-term)
          (cons tail records)
        (let ((proof (t4-records-proof records)))
          (t4-records-let records
              ((assumed (proof-proof-assume proof hypothesis t))
               (discharged (proof-proof-discharge proof decreases shape))
               (smaller (proof-proof-prove-if proof assumed discharged))
               (tail-valid (proof-proof-modus-ponens proof smaller tail))
               (:with tail-order (t4-records-records-delete-order
                                  records *library-x* tail-term (t4-records-first-key *library-y*)
                                  tail (cadddr parts))))
            (t4-records-records-ordered-record records (car parts) (cadr parts)
                                               tail-valid tail-order)))))))

(t4-records-define-by-value t4-records-typed-delete-by-value
  t4-records-records-typed-delete-leaf (original decreases hypothesis))

(defun t4-records-typed-delete-lemma (records name)
  (let* ((guard (list *t4-records-record* *library-y*))
         (call (list *t4-records-delete* *library-x* *library-y*))
         (claim (list *library-implies* guard (list *t4-records-record* call)))
         (proof (t4-records-proof records)))
    (t4-records-let records
        ((equation (proof-proof-unfold proof call))
         (template (list *t4-records-record* *proof-result*))
         (original (proof-proof-assume proof guard t))
         (decreases (library-library-builtin (t4-records-records-lib records) 3 *library-y*))
         (tail (list *library-cdr* *library-y*))
         (binding (list (list *library-y* tail)))
         (decrease (proof-step-first decreases))
         (substituted (proof-subst claim (list (cons *library-y* tail))))
         (hypothesis (proof-ite decrease substituted *proof-true*))
         (value (t4-records-step-at equation 2))
         (:with proof (t4-records-typed-delete-by-value
                       1000000 records value template nil original decreases hypothesis))
         (proof (t4-records-records-lift records proof equation template))
         (cases (t4-ordinals-ordinals-imply (t4-records-records-lib records) guard proof))
         (ordinal (library-library-builtin (t4-records-records-lib records) 1 *library-y*))
         (proof (proof-proof-induct (t4-records-proof records) ordinal cases claim
                                    (t4-structural-count *library-y*) (list binding))))
      (t4-records-add-lemma records name claim proof nil))))

(defun t4-records-records-typed-delete (records key record typed)
  (let ((name "RECORD-VALID-DELETE"))
    (proof-with-checked-results
        ((records (if (t4-records-records-has records name)
                      records
                    (t4-records-typed-delete-lemma records name)))
         (fact (t4-records-records-use records name (list key record) nil))
         (step (proof-proof-modus-ponens (t4-records-proof records) fact typed)))
      (cons step records))))

(defun t4-records-missing-below-lemma (records name)
  (let* ((guard (proof-ite (list *t4-records-record* *library-y*)
                          (t4-records-above *library-x* *library-y*) *proof-false*))
         (lookup (list *t4-records-assoc* *library-x* *library-y*))
         (claim (list *library-implies* guard (proof-eq lookup *proof-false*)))
         (proof (t4-records-proof records)))
    (t4-records-let records
        ((assumed (proof-proof-assume proof guard t))
         (premise (proof-proof-conjunct proof assumed))
         (shape (list *proof-consp* *library-y*))
         (solid (proof-proof-assume proof shape t))
         (atomic (proof-proof-assume proof shape nil))
         (tail (list *library-cdr* *library-y*))
         (:with parts (t4-records-records-components records (car premise) solid))
         (:with has-head (t4-records-prove records
                            (proof-neg (list *t4-records-atom* *library-y*))
                            (list solid) (list *t4-records-atom* *proof-not*)))
         (smaller-key (proof-proof-prove-if (t4-records-proof records) (cadr premise) has-head))
         (different (t4-records-records-before-distinct records smaller-key))
         (decreases (library-library-builtin (t4-records-records-lib records) 3 *library-y*))
         (binding (list (list *library-y* tail))))
      (let ((proof (t4-records-proof records))
            (lib (t4-records-records-lib records))
            (new-bound (t4-records-above *library-x* tail)))
        (t4-records-let records
            ((decrease (proof-step-first decreases))
             (substituted (proof-subst claim (list (cons *library-y* tail))))
             (assumed (proof-proof-assume proof (proof-ite decrease substituted *proof-true*) t))
             (discharged (proof-proof-discharge proof decreases solid))
             (ih (proof-proof-prove-if proof assumed discharged))
             (test (cadr new-bound))
             (nonatom (proof-proof-assume proof test nil))
             (larger-key (proof-proof-prove-if proof (cadddr parts) nonatom))
             (transitive (t4-records-records-transitive records smaller-key larger-key))
             (truth (proof-proof-prove proof *proof-true* nil nil))
             (if-true (proof-proof-if-true proof new-bound))
             (when-atom (proof-proof-transport proof truth if-true))
             (if-false (proof-proof-if-false proof new-bound))
             (when-pair (proof-proof-transport proof transitive if-false))
             (later (proof-proof-cases proof test when-atom when-pair))
             (joined (t4-division-combine lib (list (caddr parts) later)))
             (tail-missing (proof-proof-modus-ponens proof ih joined))
             (:with opened (t4-records-records-unfold-side records lookup solid t))
             (chosen (t4-records-records-choose records opened different))
             (yes (proof-proof-chain (t4-records-proof records) chosen (list tail-missing)))
             (:with no (t4-records-records-unfold-side records lookup atomic nil))
             (cases (proof-proof-cases (t4-records-proof records) shape yes no))
             (cases (t4-ordinals-ordinals-imply (t4-records-records-lib records) guard cases))
             (ordinal (library-library-builtin (t4-records-records-lib records) 1 *library-y*))
             (proof (proof-proof-induct (t4-records-proof records) ordinal cases claim
                                        (t4-structural-count *library-y*) (list binding))))
          (t4-records-add-lemma records name claim proof nil))))))

(defun t4-records-records-missing-below (records key record typed order)
  (let ((name "RECORD-LOOKUP-BELOW-HEAD"))
    (proof-with-checked-results
        ((records (if (t4-records-records-has records name)
                      records
                    (t4-records-missing-below-lemma records name)))
         (fact (t4-records-records-use records name (list key record) nil))
         (premise (t4-division-combine (t4-records-records-lib records) (list typed order)))
         (step (proof-proof-modus-ponens (t4-records-proof records) fact premise)))
      (cons step records))))

(defun t4-records-updated-lookup-new-entry
    (records result evidence original tail same-key same-head)
  (t4-records-let records
      ((:with opened (t4-records-records-assoc-cons records *library-x* result))
       (proof (t4-records-proof records))
       (matched (proof-proof-assume proof same-key t))
       (yes (t4-records-records-choose records opened matched))
       (unmatched (proof-proof-assume proof same-key nil))
       (no (t4-records-records-choose records opened unmatched))
       (remainder (proof-term-at result 2))
       (evidence (t4-structural-evidence-with-proof
                  evidence (t4-records-records-lib records))))
    (cond
     ((equal remainder *proof-false*)
      (t4-records-let records
          ((atomic (t4-structural-evidence-require
                    evidence (proof-neg (list *proof-consp* *t4-records-w*))))
           (:with old-nil (t4-records-records-unfold-side records original (car atomic) nil))
           (absent (t4-records-records-assoc-nil records *library-x*))
           (proof (t4-records-proof records))
           (reversed (proof-proof-symmetric proof old-nil))
           (no (proof-proof-chain proof no (list absent reversed))))
        (cons (list yes no) records)))
     ((equal remainder tail)
      (t4-records-let records
          ((assumed (proof-proof-assume proof same-key nil))
           (same (t4-structural-evidence-require evidence same-head))
           (changed (proof-proof-rewrite proof assumed (car same) '(1 1 2)))
           (solid (t4-structural-evidence-require (cdr same) (list *proof-consp* *t4-records-w*)))
           (:with old-view (t4-records-records-unfold-side records original (car solid) t))
           (chosen (t4-records-records-choose records old-view changed))
           (proof (t4-records-proof records))
           (reversed (proof-proof-symmetric proof chosen))
           (no (proof-proof-chain proof no (list reversed))))
        (cons (list yes no) records)))
     ((equal remainder *t4-records-w*) (cons (list yes no) records))
     (t '(:failure "failure" "")))))

(defun t4-records-updated-lookup-drop-head
    (records evidence parts tail same-key same-head old-view)
  (if (not parts)
      '(:failure "failure" "")
    (let ((proof (t4-records-proof records))
          (tail-valid (caddr parts))
          (order (cadddr parts)))
      (t4-records-let records
          ((answer (t4-structural-evidence-require evidence same-head))
           (same (car answer))
           (assumed (proof-proof-assume proof same-key t))
           (same-as-head (proof-proof-chain proof assumed (list same)))
           (reversed (proof-proof-symmetric proof same-as-head))
           (order (proof-proof-rewrite proof order reversed '(1 3 1)))
           (:with yes (t4-records-records-missing-below records *library-x* tail tail-valid order))
           (proof (t4-records-proof records))
           (assumed (proof-proof-assume proof same-key nil))
           (changed (proof-proof-rewrite proof assumed same '(1 1 2)))
           (selected (t4-records-records-choose records old-view changed))
           (no (proof-proof-symmetric proof selected)))
        (cons (list yes no) records)))))

(defun t4-records-updated-lookup-keep-head
    (records result evidence shape old-view insert parts same-key same-head
             lookup-head induction-step decreases)
  (proof-with-checked-results ((head (proof-term-at result 1)))
    (if (not (equal head (list *library-car* *t4-records-w*)))
        '(:failure "failure" "")
      (t4-records-let records
          ((:with lhs (t4-records-records-assoc-cons records *library-x* result))
           (proof (t4-records-proof records))
           (induction (proof-proof-assume proof induction-step t))
           (discharged (proof-proof-discharge proof decreases shape))
           (ih (proof-proof-prove-if proof induction discharged))
           (ih (if insert ih (proof-proof-modus-ponens proof ih (caddr parts))))
           (match-key (proof-proof-assume proof same-key t))
           (evidence (t4-structural-evidence-with-proof
                      evidence (t4-records-records-lib records)))
           (old-test (t4-structural-evidence-require evidence (proof-neg same-head)))
           (reversed (proof-proof-symmetric proof match-key))
           (old-miss (proof-proof-rewrite proof (car old-test) reversed '(1 1 1)))
           (selected (t4-records-records-choose records lhs old-miss))
           (tail-hit (t4-records-records-choose records ih match-key))
           (yes (proof-proof-chain proof selected (list tail-hit)))
           (matched (proof-proof-assume proof lookup-head t))
           (unmatched (proof-proof-assume proof lookup-head nil))
           (selected (t4-records-records-choose records lhs matched))
           (old-hit (t4-records-records-choose records old-view matched))
           (reversed (proof-proof-symmetric proof old-hit))
           (if-match (proof-proof-chain proof selected (list reversed)))
           (assumed (proof-proof-assume proof same-key nil))
           (tail-read (t4-records-records-choose records ih assumed))
           (selected (t4-records-records-choose records lhs unmatched))
           (old-miss (t4-records-records-choose records old-view unmatched))
           (reversed (proof-proof-symmetric proof old-miss))
           (if-miss (proof-proof-chain proof selected (list tail-read reversed)))
           (no (proof-proof-cases proof lookup-head if-match if-miss)))
        (cons (list yes no) records)))))

(defun t4-records-updated-lookup-old-entry
    (records result evidence insert original tail same-key same-head lookup-head
             guard induction-step decreases)
  (t4-records-let records
      ((answer (t4-structural-evidence-require evidence (list *proof-consp* *t4-records-w*)))
       (shape (car answer))
       (:with old-view (t4-records-records-unfold-side records original shape t))
       (:with parts
         (if insert
             (cons nil records)
           (proof-with-checked-results
               ((typed (proof-proof-assume (t4-records-proof records) guard t)))
             (t4-records-records-components records typed shape))))
       (evidence (t4-structural-evidence-with-proof
                  (cdr answer) (t4-records-records-lib records))))
    (if (equal result tail)
        (t4-records-updated-lookup-drop-head
         records evidence parts tail same-key same-head old-view)
      (t4-records-updated-lookup-keep-head
       records result evidence shape old-view insert parts same-key same-head
       lookup-head induction-step decreases))))

(defun t4-records-updated-lookup-branches
    (records result evidence insert original tail same-key same-head lookup-head
             entry guard induction-step decreases)
  (if (equal result *t4-records-w*)
      (t4-records-let records
          ((answer (t4-structural-evidence-require
                    evidence (proof-neg (list *proof-consp* *t4-records-w*))))
           (:with yes (t4-records-records-unfold-side records original (car answer) nil))
           (no (proof-proof-reflexive (t4-records-proof records) original)))
        (cons (list yes no) records))
    (proof-with-checked-results
        ((new-entry (and (proof-is-call result *proof-cons*) (proof-term-at result 1))))
      (if (and (proof-is-call result *proof-cons*) (equal new-entry entry))
          (t4-records-updated-lookup-new-entry records result evidence original tail
                                              same-key same-head)
        (t4-records-updated-lookup-old-entry
         records result evidence insert original tail same-key same-head lookup-head
         guard induction-step decreases)))))

(defun t4-records-records-updated-lookup-leaf
    (result tests records insert original tail same-key same-head lookup-head
            entry rhs guard induction-step decreases)
  (t4-records-let records
      ((evidence (t4-structural-evidence-init (t4-records-records-lib records) tests nil))
       (:with branches
         (t4-records-updated-lookup-branches
          records result evidence insert original tail same-key same-head lookup-head
          entry guard induction-step decreases))
       (proof (t4-records-proof records))
       (if-true (proof-proof-if-true proof rhs))
       (reversed (proof-proof-symmetric proof if-true))
       (yes (proof-proof-chain proof (car branches) (list reversed)))
       (if-false (proof-proof-if-false proof rhs))
       (reversed (proof-proof-symmetric proof if-false))
       (no (proof-proof-chain proof (cadr branches) (list reversed)))
       (step (proof-proof-cases proof same-key yes no)))
    (cons step records)))

(t4-records-define-by-value t4-records-updated-lookup-by-value
  t4-records-records-updated-lookup-leaf
  (insert original tail same-key same-head lookup-head entry rhs guard induction-step decreases))

(defun t4-records-updated-lookup-lemma (records name insert)
  (let* ((original (list *t4-records-assoc* *library-x* *t4-records-w*))
         (tail (list *library-cdr* *t4-records-w*))
         (head (t4-records-first-key *t4-records-w*))
         (same-key (proof-eq *library-x* *library-y*))
         (same-head (proof-eq *library-y* head))
         (lookup-head (proof-eq *library-x* head))
         (entry (if insert (list *proof-cons* *library-y* *library-z*) *proof-false*))
         (call (if insert
                   (list *t4-records-insert* *library-y* *library-z* *t4-records-w*)
                 (list *t4-records-delete* *library-y* *t4-records-w*)))
         (rhs (proof-ite same-key entry original))
         (claim (proof-eq (list *t4-records-assoc* *library-x* call) rhs))
         (guard (list *t4-records-record* *t4-records-w*))
         (formula (if insert claim (list *library-implies* guard claim))))
    (t4-records-let records
        ((decreases (library-library-builtin (t4-records-records-lib records) 3 *t4-records-w*))
         (bindings (list (list *t4-records-w* tail)))
         (decrease (proof-step-first decreases))
         (substituted (proof-subst formula (list (cons *t4-records-w* tail))))
         (induction-step (proof-ite decrease substituted *proof-true*))
         (template (proof-eq (list *t4-records-assoc* *library-x* *proof-result*) rhs))
         (equation (proof-proof-unfold (t4-records-proof records) call))
         (result (t4-records-step-at equation 2))
         (:with branches
          (t4-records-updated-lookup-by-value
           1000000 records result template nil insert original tail same-key same-head
           lookup-head entry rhs guard induction-step decreases))
         (branches (t4-records-records-lift records branches equation template))
         (cases (if insert branches
                  (t4-ordinals-ordinals-imply (t4-records-records-lib records) guard branches)))
         (ordinal (library-library-builtin (t4-records-records-lib records) 1 *t4-records-w*))
         (proof (proof-proof-induct (t4-records-proof records) ordinal cases formula
                                    (t4-structural-count *t4-records-w*) (list bindings))))
      (t4-records-add-lemma records name formula proof nil))))

(defun t4-records-records-updated-lookup (records query key value record typed)
  (let* ((insert (not (eq value :none)))
         (name (if insert "RECORD-LOOKUP-AFTER-INSERT" "RECORD-LOOKUP-AFTER-DELETE")))
    (proof-with-checked-results
        ((records (if (t4-records-records-has records name)
                      records
                    (t4-records-updated-lookup-lemma records name insert)))
         (derived (t4-records-records-use records name
                        (list query key (if insert value *proof-false*) record) nil))
         (step (cond (insert derived)
                     ((null typed) '(:failure "failure" ""))
                     (t (proof-proof-modus-ponens (t4-records-proof records) derived typed)))))
      (cons step records))))

(defun t4-records-records-represent (records)
  (if (assoc-equal *t4-records-fields* (proof-proof-definitions (t4-records-proof records)))
      records
    (let ((lib (t4-records-records-lib records))
          (record (list *t4-records-record* *library-x*))
          (wrapped (list *t4-records-wrapped* *library-x*)))
      (proof-with-checked-results
          ((lib (library-library-definition
                 lib *t4-records-fields* (list *library-x*)
                 (proof-ite record *library-x*
                            (proof-ite wrapped (list *library-car* *library-x*) *proof-false*))))
           (lib (library-library-definition
                 lib *t4-records-backing* (list *library-x*)
                 (proof-ite record *proof-false*
                            (proof-ite wrapped (list *library-cdr* *library-x*) *library-x*))))
           (lib (library-library-definition
                 lib *t4-records-pack* (list *library-x* *library-y*)
                 (proof-ite *library-y*
                            (proof-ite *library-x* (list *proof-cons* *library-x* *library-y*)
                                       *library-y*)
                            *library-x*)))
           (lib (library-library-definition
                 lib *t4-records-update* (list *library-x* *library-y* *library-z*)
                 (proof-ite *library-y* (list *t4-records-insert* *library-x* *library-y* *library-z*)
                            (list *t4-records-delete* *library-x* *library-z*)))))
        (t4-records-records-init lib)))))

(defun t4-records-records-wrapped-record (records typed)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((obj (t4-records-step-at typed 1))
         (opened (proof-proof-unfold proof (list *t4-records-wrapped* obj)))
         (view (t4-records-records-choose records opened typed)))
      (proof-proof-transport proof typed view))))

(defun t4-records-records-invalid-record (records invalid)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((test (t4-records-step-at invalid 1))
         (obj (proof-term-at test 1))
         (typed (list *t4-records-record* obj))
         (assumed (proof-proof-assume proof typed t))
         (wrapped (t4-records-records-wrapped-record records assumed))
         (joined (proof-proof-cut proof wrapped invalid)))
      (proof-proof-front proof joined (proof-neg typed)))))

(defun t4-records-records-invalid-nonempty (records invalid)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((test (t4-records-step-at invalid 1))
         (obj (proof-term-at test 1))
         (assumed (proof-proof-assume proof obj nil))
         (assumed-nil (t4-records-records-nil-from-denial records assumed))
         (typed (t4-records-records-record-nil records))
         (known (t4-records-records-wrapped-record records typed))
         (reversed (proof-proof-symmetric proof assumed-nil))
         (known (proof-proof-rewrite proof known reversed '(1 1)))
         (joined (proof-proof-cut proof known invalid)))
      (proof-proof-front proof joined obj))))

(defun t4-records-records-backing-proof (records invalid)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((test (t4-records-step-at invalid 1))
         (obj (proof-term-at test 1))
         (condition (t4-records-valid-backing obj))
         (if-true (proof-proof-if-true proof condition))
         (yes (proof-proof-transport proof invalid if-true))
         (truth (proof-proof-prove proof *proof-true* nil nil))
         (if-false (proof-proof-if-false proof condition))
         (no (proof-proof-transport proof truth if-false)))
      (proof-proof-cases proof (cadr condition) yes no))))

(defun t4-records-records-nil-backing (records)
  (proof-with-checked-results
      ((answer (t4-records-prove records (t4-records-valid-backing *proof-false*) nil nil)))
    (car answer)))

(defun t4-records-records-decoders (records obj record wrapped)
  (proof-with-checked-results
      ((records (t4-records-records-represent records)))
    (let ((proof (t4-records-proof records)))
      (proof-with-checked-results
          ((fields (proof-proof-unfold proof (list *t4-records-fields* obj)))
           (fields (t4-records-records-choose records fields record))
           (backing (proof-proof-unfold proof (list *t4-records-backing* obj)))
           (backing (t4-records-records-choose records backing record)))
        (if (not wrapped)
            (cons (list fields backing) records)
          (proof-with-checked-results
              ((fields (t4-records-records-choose records fields wrapped))
               (backing (t4-records-records-choose records backing wrapped)))
            (cons (list fields backing) records)))))))

(defun t4-records-records-wrapper-parts (records invalid-record wrapped)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((literal (proof-step-first wrapped))
         (opened (proof-proof-unfold proof literal))
         (view (t4-records-records-choose records opened invalid-record))
         (first (proof-proof-rewrite proof wrapped view '(1)))
         (shape (proof-proof-conjunct proof first))
         (validity (proof-proof-conjunct proof (cadr shape)))
         (fields (proof-proof-conjunct proof (cadr validity))))
      (list (car shape) (car validity) (car fields) (cadr fields)))))

(defun t4-records-records-pack-view (records equation back fields)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((rhs (t4-records-step-at equation 2))
         (opened (proof-proof-unfold proof rhs))
         (packed (proof-proof-chain proof equation (list opened)))
         (packed (t4-records-records-choose records packed back)))
      (if fields
          (t4-records-records-choose records packed fields)
        packed))))

(defun t4-records-records-field-view (records key equation)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((operand (t4-records-step-at equation 1))
         (step (proof-proof-reflexive proof (t4-records-field key operand))))
      (proof-proof-rewrite proof step equation '(1 2 1 2)))))

(defun t4-records-records-decoded-types-prove (views typed back records)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((field-reversed (proof-proof-symmetric proof (car views)))
         (typed (proof-proof-rewrite proof typed field-reversed '(1 1)))
         (backing-reversed (proof-proof-symmetric proof (cadr views)))
         (back (proof-proof-rewrite-result proof back backing-reversed
                                           (t4-records-valid-backing *proof-result*)
                                           *proof-result*))
         (step (t4-division-combine (t4-records-records-lib records) (list typed back))))
      (cons step records))))

(defun t4-records-decoded-types-plain (typed records)
  (t4-records-let records
      ((:with views (t4-records-records-decoders records *library-x* typed nil))
       (back (t4-records-records-nil-backing records)))
    (t4-records-records-decoded-types-prove views typed back records)))

(defun t4-records-records-decoded-types-wrapped (invalid lsp records)
  (t4-records-let records
      ((parts (t4-records-records-wrapper-parts records invalid lsp))
       (:with views (t4-records-records-decoders records *library-x* invalid lsp))
       (back (t4-records-records-backing-proof records (cadr parts))))
    (t4-records-records-decoded-types-prove views (caddr parts) back records)))

(defun t4-records-decoded-types-other (invalid lsp records)
  (t4-records-let records
      ((:with views (t4-records-records-decoders records *library-x* invalid lsp))
       (typed (t4-records-records-record-nil records))
       (back (t4-records-records-backing-proof records lsp)))
    (t4-records-records-decoded-types-prove views typed back records)))

(defun t4-records-records-reconstruct-initial (views records packed)
  (t4-records-records-change-args records packed (seq-numbered views 1)))

(defun t4-records-reconstruct-plain (valid records packed)
  (t4-records-let records
      ((:with views (t4-records-records-decoders records *library-x* valid nil))
       (equation (t4-records-records-reconstruct-initial views records packed))
       (not-nil (proof-proof-not-nil (t4-records-proof records)))
       (step (t4-records-records-pack-view records equation not-nil nil)))
    (cons step records)))

(defun t4-records-records-reconstruct-wrapped (invalid lsp records packed)
  (t4-records-let records
      ((parts (t4-records-records-wrapper-parts records invalid lsp))
       (:with views (t4-records-records-decoders records *library-x* invalid lsp))
       (initial (t4-records-records-reconstruct-initial views records packed))
       (back (t4-records-records-invalid-nonempty records (cadr parts)))
       (branch (t4-records-records-pack-view records initial back (cadddr parts)))
       (proof (t4-records-proof records))
       (axiom (library-library-axiom (t4-records-records-lib records)
                                     "CAR-CDR-ELIM" (list *library-x*)))
       (reconstructed (proof-proof-modus-ponens proof axiom (car parts)))
       (step (proof-proof-chain proof branch (list reconstructed))))
    (cons step records)))

(defun t4-records-reconstruct-other (invalid lsp records packed)
  (t4-records-let records
      ((:with views (t4-records-records-decoders records *library-x* invalid lsp))
       (initial (t4-records-records-reconstruct-initial views records packed))
       (back (t4-records-records-invalid-nonempty records lsp))
       (not-nil (proof-proof-not-nil (t4-records-proof records)))
       (step (t4-records-records-pack-view records initial back not-nil)))
    (cons step records)))

(defun t4-records-records-get-view-show (typed lsp records opening)
  (t4-records-let records
      ((source (t4-records-records-choose records opening typed))
       (source (if lsp (t4-records-records-choose records source lsp) source))
       (:with views (t4-records-records-decoders records *library-y* typed lsp))
       (target (t4-records-records-field-view records *library-x* (car views)))
       (right (t4-records-step-at target 2))
       (proof (t4-records-proof records))
       (target
        (if (equal right (t4-records-field *library-x* *proof-false*))
            (proof-with-checked-results
                ((empty-assoc (t4-records-records-assoc-nil records *library-x*))
                 (target (proof-proof-rewrite proof target empty-assoc '(1 2 1)))
                 (value (proof-proof-compute proof (list *library-cdr* *proof-false*) *proof-nil*)))
              (proof-proof-chain proof target (list value)))
          target))
       (reversed (proof-proof-symmetric proof target))
       (step (proof-proof-chain proof source (list reversed))))
    (cons step records)))

(defun t4-records-records-set-view-equivalent-view (decoders sign extra records updated packed)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((parts (proof-list-of-length decoders 2))
         (line (t4-records-records-change-args records updated (list (list 3 (car parts)))))
         (right (t4-records-step-at line 2))
         (opened (proof-proof-unfold proof right))
         (new (t4-records-records-choose records opened sign))
         (update (proof-proof-chain proof line (list new extra))))
      (t4-records-records-change-args records packed (list (list 1 update) (list 2 (cadr parts)))))))

(defun t4-records-records-set-view-plain-branch (positive records src views updated packed)
  (t4-records-let records
      ((sign (proof-proof-assume (t4-records-proof records) *library-y* positive))
       (:with null-test (t4-records-records-null-test records sign positive))
       (actual (t4-records-records-choose records src null-test))
       (view (t4-records-records-set-view-equivalent-view views sign nil records updated packed))
       (proof (t4-records-proof records))
       (not-nil (proof-proof-not-nil proof))
       (expected (t4-records-records-pack-view records view not-nil nil))
       (reversed (proof-proof-symmetric proof expected))
       (step (proof-proof-chain proof actual (list reversed))))
    (cons step records)))

(defun t4-records-records-set-view-plain (rec records opening updated packed)
  (t4-records-let records
      ((src (t4-records-records-choose records opening rec))
       (:with views (t4-records-records-decoders records *library-z* rec nil))
       (:with yes (t4-records-records-set-view-plain-branch
                    t records src views updated packed))
       (:with no (t4-records-records-set-view-plain-branch
                   nil records src views updated packed))
       (step (proof-proof-cases (t4-records-proof records) *library-y* yes no)))
    (cons step records)))

(defun t4-records-records-set-view-other-branch
    (positive records src views updated packed back-nonzero empty)
  (t4-records-let records
      ((sign (proof-proof-assume (t4-records-proof records) *library-y* positive))
       (call (if positive
                 (list *t4-records-insert* *library-x* *library-y* *proof-false*)
               (list *t4-records-delete* *library-x* *proof-false*)))
       (:with simple (t4-records-records-unfold-side records call empty nil))
       (proof (t4-records-proof records))
       (new (if positive
                (proof-with-checked-results
                    ((rhs (t4-records-step-at simple 2))
                     (shape (t4-records-records-cons records rhs)))
                  (t4-records-records-nonempty records shape))
              (proof-proof-not-nil proof)))
       (view (t4-records-records-set-view-equivalent-view
              views sign simple records updated packed))
       (pack (t4-records-records-pack-view records view back-nonzero new))
       (actual (t4-records-records-choose records src sign))
       (reversed (proof-proof-symmetric proof pack))
       (step (proof-proof-chain proof actual (list reversed))))
    (cons step records)))

(defun t4-records-records-set-view-other (bad lsp records opening updated packed)
  (t4-records-let records
      ((src (t4-records-records-choose records opening bad))
       (src (t4-records-records-choose records src lsp))
       (:with views (t4-records-records-decoders records *library-z* bad lsp))
       (back-nonzero (t4-records-records-invalid-nonempty records lsp))
       (:with empty (t4-records-prove records (proof-neg (list *proof-consp* *proof-false*))
                                     nil (list *proof-not*)))
       (:with yes (t4-records-records-set-view-other-branch
                   t records src views updated packed back-nonzero empty))
       (:with no (t4-records-records-set-view-other-branch
                  nil records src views updated packed back-nonzero empty))
       (step (proof-proof-cases (t4-records-proof records) *library-y* yes no)))
    (cons step records)))

(defun t4-records-set-view-cons-leaf (pair tests records)
  (declare (ignore tests))
  (proof-with-checked-results ((shape (t4-records-records-cons records pair)))
    (cons shape records)))

(t4-records-define-by-value t4-records-set-view-by-value t4-records-set-view-cons-leaf nil)

(defun t4-records-set-view-wrapped-insert (records src views back old updated packed)
  (t4-records-let records
      ((positive (proof-proof-assume (t4-records-proof records) *library-y* t))
       (:with null-test (t4-records-records-null-test records positive t))
       (source (t4-records-records-choose records src null-test))
       (raw-insert (list *t4-records-insert* *library-x* *library-y* old))
       (view (proof-proof-unfold (t4-records-proof records) raw-insert))
       (template (list *proof-consp* *proof-result*))
       (rhs (t4-records-step-at view 2))
       (:with all-cons (t4-records-set-view-by-value 1000000 records rhs template nil))
       (all-cons (t4-records-records-lift records all-cons view template))
       (inserted (t4-records-records-nonempty records all-cons))
       (view (t4-records-records-set-view-equivalent-view views positive nil records updated packed))
       (pack (t4-records-records-pack-view records view back inserted))
       (proof (t4-records-proof records))
       (reversed (proof-proof-symmetric proof pack))
       (step (proof-proof-chain proof source (list reversed))))
    (cons step records)))

(defun t4-records-records-set-view-wrapped-pack-case
    (guard result records views negative back source updated packed)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((view (t4-records-records-set-view-equivalent-view
                views negative nil records updated packed))
         (pack (t4-records-records-pack-view records view back result))
         (selected (t4-records-records-choose records source guard))
         (reversed (proof-proof-symmetric proof pack)))
      (proof-proof-chain proof selected (list reversed)))))

(defun t4-records-records-set-view-wrapped-deny-test (opposite index records test)
  (let ((proof (t4-records-proof records)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof test t))
         (parts (proof-proof-conjunct proof assumed))
         (component (proof-term-at parts index))
         (joined (proof-proof-cut proof component opposite)))
      (proof-proof-front proof joined (proof-neg test)))))

(defun t4-records-set-view-wrapped-delete
    (records src views back old valid nonzero updated packed)
  (t4-records-let records
      ((negative (proof-proof-assume (t4-records-proof records) *library-y* nil))
       (:with null-test (t4-records-records-null-test records negative nil))
       (source (t4-records-records-choose records src null-test))
       (rhs (t4-records-step-at source 2))
       (test (proof-term-at rhs 1))
       (:with fields-cons (t4-records-records-nonempty-record records valid nonzero))
       (same-key (proof-eq *library-x* (t4-records-first-key old)))
       (:with view-delete (t4-records-records-unfold-side
                           records (list *t4-records-delete* *library-x* old) fields-cons t))
       (proof (t4-records-proof records))
       (same (proof-proof-assume proof same-key t))
       (deleted-head (t4-records-records-choose records view-delete same))
       (lacks-tail (list *t4-records-null* (list *library-cdr* old)))
       (absent-tail (proof-proof-assume proof lacks-tail t))
       (same (proof-proof-assume proof same-key t))
       (reversed (proof-proof-symmetric proof same))
       (test-true (t4-division-combine (t4-records-records-lib records)
                                      (list absent-tail reversed)))
       (:with simplified (t4-records-simplify records lacks-tail nil
                                              (list *t4-records-null* (proof-cl "EQ"))))
       (proof (t4-records-proof records))
       (tail-nil (proof-proof-rewrite proof absent-tail simplified '(1)))
       (deleted-nil (proof-proof-chain proof deleted-head (list tail-nil)))
       (empty (t4-records-records-denial-from-nil records deleted-nil))
       (has-tail (proof-proof-assume proof lacks-tail nil))
       (:with retained (t4-records-records-denied-null records has-tail))
       (proof (t4-records-proof records))
       (keep-tail (proof-proof-transport proof retained deleted-head))
       (yes (t4-records-records-set-view-wrapped-pack-case
              test-true empty records views negative back source updated packed))
       (test-false (t4-records-records-set-view-wrapped-deny-test has-tail 0 records test))
       (no (t4-records-records-set-view-wrapped-pack-case
            test-false keep-tail records views negative back source updated packed))
       (matched (proof-proof-cases proof lacks-tail yes no))
       (different (proof-proof-assume proof same-key nil))
       (kept (t4-records-records-choose records view-delete different))
       (rhs (t4-records-step-at kept 2))
       (shape (t4-records-records-cons records rhs))
       (nonempty (t4-records-records-nonempty records shape))
       (keeps-pair (proof-proof-transport proof nonempty kept))
       (reversed (t4-records-records-reversed-distinct records different))
       (test-false (t4-records-records-set-view-wrapped-deny-test reversed 1 records test))
       (unequal (t4-records-records-set-view-wrapped-pack-case
                 test-false keeps-pair records views negative back source updated packed))
       (step (proof-proof-cases proof same-key matched unequal)))
    (cons step records)))

(defun t4-records-records-set-view-wrapped (bad lsp records opening updated packed)
  (t4-records-let records
      ((src (t4-records-records-choose records opening bad))
       (literal (proof-step-first lsp))
       (:with double-negation
         (t4-records-prove records (proof-neg (proof-neg literal)) (list lsp) (list *proof-not*)))
       (src (t4-records-records-choose records src double-negation))
       (parts (t4-records-records-wrapper-parts records bad lsp))
       (valid (caddr parts))
       (nonzero (cadddr parts))
       (:with views (t4-records-records-decoders records *library-z* bad lsp))
       (back (t4-records-records-invalid-nonempty records (cadr parts)))
       (old (t4-records-step-at valid 1))
       (:with yes (t4-records-set-view-wrapped-insert records src views back old updated packed))
       (:with no (t4-records-set-view-wrapped-delete
                  records src views back old valid nonzero updated packed))
       (step (proof-proof-cases (t4-records-proof records) *library-y* yes no)))
    (cons step records)))

; A branch identifies its proof function and carries the captured terms.
(defun t4-records-representation-branch (records callback typed lsp)
  (case (car callback)
    (:decoded-plain (t4-records-decoded-types-plain typed records))
    (:decoded-wrapped (t4-records-records-decoded-types-wrapped typed lsp records))
    (:decoded-other (t4-records-decoded-types-other typed lsp records))
    (:reconstruct-plain (t4-records-reconstruct-plain typed records (cadr callback)))
    (:reconstruct-wrapped
     (t4-records-records-reconstruct-wrapped typed lsp records (cadr callback)))
    (:reconstruct-other (t4-records-reconstruct-other typed lsp records (cadr callback)))
    (:get (t4-records-records-get-view-show typed lsp records (cadr callback)))
    (:set-plain
     (t4-records-records-set-view-plain typed records (cadr callback)
                                        (caddr callback) (cadddr callback)))
    (:set-wrapped
     (t4-records-records-set-view-wrapped typed lsp records (cadr callback)
                                          (caddr callback) (cadddr callback)))
    (:set-other
     (t4-records-records-set-view-other typed lsp records (cadr callback)
                                        (caddr callback) (cadddr callback)))
    (otherwise
     (let ((entry (assoc-equal (if lsp (list typed lsp) (list typed)) callback)))
       (if entry
           (cdr entry)
         '(:failure "search-miss" ""))))))

(defun t4-records-records-representation-cases (records obj plain wrapped other)
  (let ((proof (t4-records-proof records))
        (record (list *t4-records-record* obj))
        (lsp (list *t4-records-wrapped* obj)))
    (t4-records-let records
        ((typed (proof-proof-assume proof record t))
         (invalid (proof-proof-assume proof record nil))
         (yes (proof-proof-assume proof lsp t))
         (no (proof-proof-assume proof lsp nil))
         (:with when-plain (t4-records-representation-branch records plain typed nil))
         (:with when-wrapped (t4-records-representation-branch records wrapped invalid yes))
         (:with when-other (t4-records-representation-branch records other invalid no))
         (proof (t4-records-proof records))
         (complex (proof-proof-cases proof lsp when-wrapped when-other))
         (step (proof-proof-cases proof record when-plain complex)))
      (cons step records))))

(defun t4-records-decoded-types-lemma (records name)
  (t4-records-let records
      ((:with step (t4-records-records-representation-cases
                    records *library-x* '(:decoded-plain) '(:decoded-wrapped) '(:decoded-other)))
       (claim (proof-step-first step)))
    (t4-records-add-lemma records name claim step nil)))

(defun t4-records-records-decoded-types (records obj)
  (let ((name "RECORD-DECODED-TYPES"))
    (proof-with-checked-results
        ((records (if (t4-records-records-has records name)
                      records
                    (t4-records-decoded-types-lemma records name)))
         (fact (t4-records-records-use records name (list obj) nil))
         (parts (proof-proof-conjunct (t4-records-proof records) fact)))
      (cons parts records))))

(defun t4-records-reconstruct-lemma (records name)
  (let ((packed (list *t4-records-pack* (list *t4-records-fields* *library-x*)
                      (list *t4-records-backing* *library-x*))))
    (t4-records-let records
        ((:with proof (t4-records-records-representation-cases
                        records *library-x* (list :reconstruct-plain packed)
                        (list :reconstruct-wrapped packed) (list :reconstruct-other packed)))
         (claim (proof-step-first proof)))
      (t4-records-add-lemma records name claim proof nil))))

(defun t4-records-records-reconstruct (records obj)
  (let ((name "RECORD-PACK-AFTER-DECODE"))
    (proof-with-checked-results
        ((records (if (t4-records-records-has records name)
                      records
                    (t4-records-reconstruct-lemma records name)))
         (step (t4-records-records-use records name (list obj) nil)))
      (cons step records))))

(defun t4-records-get-view-lemma (records name)
  (t4-records-let records
      ((opening (proof-proof-unfold (t4-records-proof records)
                                    (list *t4-records-get* *library-x* *library-y*)))
       (show (list :get opening))
       (:with proof (t4-records-records-representation-cases records *library-y* show show show))
       (claim (proof-step-first proof)))
    (t4-records-add-lemma records name claim proof nil)))

(defun t4-records-records-get-view (records key obj)
  (let ((name "RECORD-GET-FROM-FIELDS"))
    (proof-with-checked-results
        ((records (if (t4-records-records-has records name)
                      records
                    (t4-records-get-view-lemma records name)))
         (step (t4-records-records-use records name (list key obj) nil)))
      (cons step records))))

(defun t4-records-set-view-lemma (records name)
  (let* ((fields (list *t4-records-fields* *library-z*))
         (backing (list *t4-records-backing* *library-z*))
         (updated (list *t4-records-update* *library-x* *library-y* fields))
         (packed (list *t4-records-pack* updated backing)))
    (t4-records-let records
        ((opening (proof-proof-unfold (t4-records-proof records)
                                      (list *t4-records-set* *library-x* *library-y* *library-z*)))
         (:with proof
           (t4-records-records-representation-cases
            records *library-z* (list :set-plain opening updated packed)
            (list :set-wrapped opening updated packed) (list :set-other opening updated packed)))
         (claim (proof-step-first proof)))
      (t4-records-add-lemma records name claim proof nil))))

(defun t4-records-records-set-view (records key value obj)
  (let ((name "RECORD-SET-FROM-FIELDS"))
    (proof-with-checked-results
        ((records (t4-records-records-represent records))
         (records (if (t4-records-records-has records name)
                      records
                    (t4-records-set-view-lemma records name)))
         (step (t4-records-records-use records name (list key value obj) nil)))
      (cons step records))))

(defun t4-records-packed-bare (records packed base no-back has-fields)
  (t4-records-let records
      ((pack-nil (t4-records-records-pack-view records base no-back nil))
       (:with views (t4-records-records-decoders records *library-x* has-fields nil))
       (proof (t4-records-proof records))
       (fields-view (t4-records-records-change-args
                     records (list *t4-records-fields* packed) (list (list 1 pack-nil))))
       (fields (proof-proof-chain proof fields-view (list (car views))))
       (backing-view (t4-records-records-change-args
                       records (list *t4-records-backing* packed) (list (list 1 pack-nil))))
       (nil-back (t4-records-records-nil-from-denial records no-back))
       (reversed (proof-proof-symmetric proof nil-back))
       (backing (proof-proof-chain proof backing-view (list (cadr views) reversed)))
       (step (t4-division-combine (t4-records-records-lib records) (list fields backing))))
    (cons step records)))

(defun t4-records-packed-raw (records packed base yes-back bad-back bad-record no-fields)
  (t4-records-let records
      ((pack-raw (t4-records-records-pack-view records base yes-back no-fields))
       (:with views (t4-records-records-decoders records *library-y* bad-record bad-back))
       (proof (t4-records-proof records))
       (fields-view (t4-records-records-change-args
                     records (list *t4-records-fields* packed) (list (list 1 pack-raw))))
       (nil-fields (t4-records-records-nil-from-denial records no-fields))
       (reversed (proof-proof-symmetric proof nil-fields))
       (fields (proof-proof-chain proof fields-view (list (car views) reversed)))
       (backing-view (t4-records-records-change-args
                       records (list *t4-records-backing* packed) (list (list 1 pack-raw))))
       (backing (proof-proof-chain proof backing-view (list (cadr views))))
       (step (t4-division-combine (t4-records-records-lib records) (list fields backing))))
    (cons step records)))

(defun t4-records-packed-cell
    (records packed base yes-back bad-back yes-fields has-fields)
  (t4-records-let records
      ((pack-cell (t4-records-records-pack-view records base yes-back yes-fields))
       (cell (t4-records-step-at pack-cell 2))
       (proper (list *t4-records-record* cell))
       (assumed (proof-proof-assume (t4-records-proof records) proper t))
       (shape (t4-records-records-cons records cell))
       (:with parts (t4-records-records-components records assumed shape))
       (tail (t4-records-records-projections records (caddr parts) cell))
       (wrapped (t4-records-records-wrapped-record records tail))
       (proof (t4-records-proof records))
       (joined (proof-proof-cut proof wrapped bad-back))
       (bad-cell (proof-proof-front proof joined (proof-neg proper)))
       (opened (proof-proof-unfold proof (list *t4-records-wrapped* cell)))
       (lsp (t4-records-records-choose records opened bad-cell))
       (shape (t4-records-records-cons records cell))
       (lsp (t4-records-records-choose records lsp shape))
       (lsp (t4-records-records-projections records lsp cell))
       (lsp (t4-records-records-choose records lsp bad-back))
       (lsp (t4-records-records-choose records lsp has-fields))
       (valid-cell (proof-proof-transport proof yes-fields lsp))
       (:with views (t4-records-records-decoders records cell bad-cell valid-cell))
       (fields (t4-records-records-projections records (car views) cell))
       (backing (t4-records-records-projections records (cadr views) cell))
       (proof (t4-records-proof records))
       (fields-view (t4-records-records-change-args
                     records (list *t4-records-fields* packed) (list (list 1 pack-cell))))
       (fields (proof-proof-chain proof fields-view (list fields)))
       (backing-view (t4-records-records-change-args
                       records (list *t4-records-backing* packed) (list (list 1 pack-cell))))
       (backing (proof-proof-chain proof backing-view (list backing)))
       (step (t4-division-combine (t4-records-records-lib records) (list fields backing))))
    (cons step records)))

(defun t4-records-packed-types-lemma (records name)
  (let ((guard (list *t4-records-record* *library-x*))
        (validity (t4-records-valid-backing *library-y*)))
    (t4-records-let records
        ((proof (t4-records-proof records))
         (has-fields (proof-proof-assume proof guard t))
         (packed (list *t4-records-pack* *library-x* *library-y*))
         (base (proof-proof-reflexive proof packed))
         (no-back (proof-proof-assume proof *library-y* nil))
         (:with bare (t4-records-packed-bare records packed base no-back has-fields))
         (proof (t4-records-proof records))
         (yes-back (proof-proof-assume proof *library-y* t))
         (allowed (proof-proof-assume proof validity t))
         (bad-back (proof-proof-prove-if proof allowed yes-back))
         (bad-record (t4-records-records-invalid-record records bad-back))
         (no-fields (proof-proof-assume proof *library-x* nil))
         (:with raw (t4-records-packed-raw
                     records packed base yes-back bad-back bad-record no-fields))
         (yes-fields (proof-proof-assume (t4-records-proof records) *library-x* t))
         (:with pair (t4-records-packed-cell
                      records packed base yes-back bad-back yes-fields has-fields))
         (proof (t4-records-proof records))
         (with-backing (proof-proof-cases proof *library-x* pair raw))
         (result (proof-proof-cases proof *library-y* with-backing bare))
         (claim (proof-step-first result)))
      (t4-records-add-lemma records name claim result
                            (list (proof-neg guard) (proof-neg validity))))))

(defun t4-records-records-packed-types (records record backing typed allowed)
  (let ((name "RECORD-PACK-PROJECTIONS"))
    (proof-with-checked-results
        ((records (t4-records-records-represent records))
         (records (if (t4-records-records-has records name)
                      records
                    (t4-records-packed-types-lemma records name)))
         (fact (t4-records-records-use records name (list record backing) (list typed allowed)))
         (parts (proof-proof-conjunct (t4-records-proof records) fact)))
      (cons parts records))))

(defun t4-records-records-typed-update (records key value r typed)
  (t4-records-let records
      ((records (t4-records-records-represent records))
       (proof (t4-records-proof records))
       (step (proof-proof-unfold proof (list *t4-records-update* key value r)))
       (assumed (proof-proof-assume proof value t))
       (:with yes (t4-records-records-typed-insert records key value r typed assumed))
       (:with no (t4-records-records-typed-delete records key r typed))
       (proof (t4-records-proof records))
       (target (list *t4-records-record* *proof-result*))
       (positive (proof-proof-assume proof value t))
       (equation (t4-records-records-choose records step positive))
       (yes (t4-records-records-lift records yes equation target))
       (negative (proof-proof-assume proof value nil))
       (equation (t4-records-records-choose records step negative))
       (no (t4-records-records-lift records no equation target))
       (step (proof-proof-cases proof value yes no)))
    (cons step records)))

(defun t4-records-records-update-view-branch (positive records valid raw same rhs)
  (t4-records-let records
      ((proof (t4-records-proof records))
       (sign (proof-proof-assume proof *library-z* positive))
       (selected (t4-records-records-choose records raw sign))
       (left (t4-records-records-field-view records *library-x* selected))
       (typed (proof-proof-assume proof valid t))
       (:with read
        (t4-records-records-updated-lookup
         records *library-x* *library-y* (if positive *library-z* :none) *t4-records-w* typed))
       (proof (t4-records-proof records))
       (matched (proof-proof-assume proof same t))
       (when-same (t4-records-records-choose records read matched))
       (hit (proof-proof-rewrite proof left when-same '(1 2 1)))
       (hit
        (if positive
            (proof-with-checked-results
                ((value (library-library-axiom (t4-records-records-lib records)
                                               "CDR-CONS" (list *library-y* *library-z*))))
              (proof-proof-chain proof hit (list value)))
          (proof-with-checked-results
              ((value (proof-proof-compute proof (list *library-cdr* *proof-false*) *proof-nil*))
               (equation (t4-records-records-nil-from-denial records sign))
               (reversed (proof-proof-symmetric proof equation)))
            (proof-proof-chain proof hit (list value reversed)))))
       (unmatched (proof-proof-assume proof same nil))
       (when-different (t4-records-records-choose records read unmatched))
       (miss (proof-proof-rewrite proof left when-different '(1 2 1)))
       (if-true (proof-proof-if-true proof rhs))
       (reversed (proof-proof-symmetric proof if-true))
       (yes (proof-proof-chain proof hit (list reversed)))
       (if-false (proof-proof-if-false proof rhs))
       (reversed (proof-proof-symmetric proof if-false))
       (no (proof-proof-chain proof miss (list reversed)))
       (step (proof-proof-cases proof same yes no)))
    (cons step records)))

(defun t4-records-update-view-lemma (records name)
  (let* ((valid (list *t4-records-record* *t4-records-w*))
         (updated (list *t4-records-update* *library-y* *library-z* *t4-records-w*))
         (initial (t4-records-field *library-x* updated)))
    (t4-records-let records
        ((raw (proof-proof-unfold (t4-records-proof records) updated))
         (same (proof-eq *library-x* *library-y*))
         (rhs (proof-ite same *library-z* (t4-records-field *library-x* *t4-records-w*)))
         (:with yes (t4-records-records-update-view-branch t records valid raw same rhs))
         (:with no (t4-records-records-update-view-branch nil records valid raw same rhs))
         (proof (proof-proof-cases (t4-records-proof records) *library-z* yes no)))
      (t4-records-add-lemma records name (proof-eq initial rhs) proof (list (proof-neg valid))))))

(defun t4-records-records-update-view (records query key value r typed)
  (let ((name "RECORD-READ-AFTER-UPDATE"))
    (proof-with-checked-results
        ((records (t4-records-records-represent records))
         (records (if (t4-records-records-has records name)
                      records
                    (t4-records-update-view-lemma records name)))
         (step (t4-records-records-use records name (list query key value r) (list typed))))
      (cons step records))))

(defun t4-records-get-after-set-lemma (records name)
  (let ((written (list *t4-records-set* *library-y* *library-z* *t4-records-w*)))
    (t4-records-let records
        ((:with encoding (t4-records-records-set-view records *library-y* *library-z* *t4-records-w*))
         (:with decoded (t4-records-records-decoded-types records *t4-records-w*))
         (r (list *t4-records-fields* *t4-records-w*))
         (backing (list *t4-records-backing* *t4-records-w*))
         (updated (list *t4-records-update* *library-y* *library-z* r))
         (:with valid (t4-records-records-typed-update
                       records *library-y* *library-z* r (car decoded)))
         (:with projections (t4-records-records-packed-types
                             records updated backing valid (cadr decoded)))
         (changed (t4-records-records-change-args records
                   (list *t4-records-fields* written) (list (list 1 encoding))))
         (fields (proof-proof-chain (t4-records-proof records) changed (list (car projections))))
         (:with get-written (t4-records-records-get-view records *library-x* written))
         (field (t4-records-records-field-view records *library-x* fields))
         (:with update (t4-records-records-update-view
                        records *library-x* *library-y* *library-z* r (car decoded)))
         (read (proof-proof-chain (t4-records-proof records) get-written (list field update)))
         (:with get-obj (t4-records-records-get-view records *library-x* *t4-records-w*))
         (proof (t4-records-proof records))
         (reversed (proof-proof-symmetric proof get-obj))
         (step (proof-proof-rewrite proof read reversed '(1 2 3)))
         (claim (proof-step-first step)))
      (t4-records-add-lemma records name claim step nil))))

(defun t4-records-records-get-after-set (records query key value obj)
  (let ((name "RECORD-GET-AFTER-SET"))
    (proof-with-checked-results
        ((records (t4-records-records-represent records))
         (records (if (t4-records-records-has records name)
                      records
                    (t4-records-get-after-set-lemma records name)))
         (step (t4-records-records-use records name (list query key value obj) nil)))
      (cons step records))))

(defun t4-records-preservation-arguments (formula)
  (and (proof-is-call formula *library-implies*)
       (proof-with-checked-results ((guard (proof-term-at formula 1)))
         (and (proof-is-call guard *t4-records-record*)
              (proof-with-checked-results ((goal (proof-term-at formula 2)))
                (and (proof-is-call goal *t4-records-record*)
                     (proof-with-checked-results
                         ((parts (proof-list-of-length (cdr formula) 2))
                          (operation (proof-term-at (cadr parts) 1)))
                       (and (proof-is-call operation *t4-records-set*)
                            (proof-with-checked-results
                                ((obj (proof-term-at operation 3))
                                 (original (proof-term-at guard 1)))
                              (and (equal obj original) (list guard operation)))))))))))

(defun t4-records-record-preservation-proof (lib guard operation)
  (let ((records (t4-records-records-init lib)))
    (t4-records-let records
        ((operands (proof-list-of-length (cdr operation) 3))
         (key (car operands))
         (value (cadr operands))
         (obj (caddr operands))
         (proof (t4-records-proof records))
         (typed (proof-proof-assume proof guard t))
         (opened (proof-proof-unfold proof operation))
         (equation (t4-records-records-choose records opened typed))
         (is-nil (list *t4-records-null* value))
         (:with yes (t4-records-records-typed-delete records key obj typed))
         (not-nil (proof-proof-assume (t4-records-proof records) is-nil nil))
         (:with simplified (t4-records-simplify records is-nil nil
                                                (list *t4-records-null* (proof-cl "EQ"))))
         (proof (t4-records-proof records))
         (reduced (proof-proof-rewrite proof not-nil simplified '(1 1)))
         (either (proof-proof-nil-or-true proof value))
         (nonzero (proof-proof-cut proof either reduced))
         (:with no (t4-records-records-typed-insert records key value obj typed nonzero))
         (proof (t4-records-proof records))
         (template (list *t4-records-record* *proof-result*))
         (nil-branch (proof-proof-assume proof is-nil t))
         (nil-equation (t4-records-records-choose records equation nil-branch))
         (yes (t4-records-records-lift records yes nil-equation template))
         (nonzero-equation (t4-records-records-choose records equation not-nil))
         (no (t4-records-records-lift records no nonzero-equation template))
         (cases (proof-proof-cases proof is-nil yes no))
         (lib (t4-records-records-lib records))
         (step (t4-ordinals-ordinals-imply lib guard cases)))
      (cons step lib))))

(defun t4-records-read-matches (guard claim query key value obj)
  (proof-with-checked-results
      ((equality (proof-eq query key))
       (same (and (eq guard :none) (equal query key)
                  (proof-with-checked-results ((rhs (proof-term-at claim 2)))
                    (equal rhs value))))
       (different (and (equal guard (proof-neg equality))
                       (proof-with-checked-results ((rhs (proof-term-at claim 2)))
                         (equal rhs (list *t4-records-get* query obj))))))
    (and (or same different) (list guard query key value obj same))))

(defun t4-records-read-arguments (formula)
  (proof-with-checked-results
      ((parts (if (proof-is-call formula *library-implies*)
                  (proof-list-of-length (cdr formula) 2)
                (list :none formula)))
       (guard (car parts))
       (claim (cadr parts)))
    (and (proof-is-call claim *proof-equal*)
         (proof-with-checked-results ((get (proof-term-at claim 1)))
           (and (proof-is-call get *t4-records-get*)
                (proof-with-checked-results ((set (proof-term-at get 2)))
                  (and (proof-is-call set *t4-records-set*)
                       (proof-with-checked-results
                           ((args (proof-list-of-length (cdr get) 2))
                            (update (proof-list-of-length (cdr set) 3)))
                         (t4-records-read-matches guard claim (car args)
                                                 (car update) (cadr update) (caddr update))))))))))

(defun t4-records-record-read-proof (lib arguments)
  (let ((records (t4-records-records-init lib))
        (guard (car arguments))
        (query (cadr arguments))
        (key (caddr arguments))
        (value (cadddr arguments))
        (obj (nth 4 arguments))
        (same (nth 5 arguments)))
    (t4-records-let records
        ((:with equation (t4-records-records-get-after-set records query key value obj))
         (proof (t4-records-proof records))
         (condition (if same
                        (proof-proof-reflexive proof query)
                      (proof-proof-assume proof guard t)))
         (selected (t4-records-records-choose records equation condition))
         (lib (t4-records-records-lib records))
         (step (if same selected (t4-ordinals-ordinals-imply lib guard selected))))
      (cons step lib))))

(defun t4-records-record-preservation-with-replies (lib formula replies)
  (proof-with-checked-results ((args (t4-records-preservation-arguments formula)))
    (cond ((not args) (cons nil lib))
          ((endp replies) (list :t4-request :use-arithmetic nil lib))
          (t (proof-with-checked-results ((reply (car replies)))
               (t4-records-record-preservation-proof (cdr reply) (car args) (cadr args)))))))

(defun t4-records-record-read-with-replies (lib formula replies)
  (proof-with-checked-results ((args (t4-records-read-arguments formula)))
    (cond ((not args) (cons nil lib))
          ((endp replies) (list :t4-request :use-arithmetic nil lib))
          (t (proof-with-checked-results ((reply (car replies)))
               (t4-records-record-read-proof (cdr reply) args))))))
