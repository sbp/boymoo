(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defun t3-book-spines-book-proofs-p (value)
  (eq (car value) :t3-book-values-book-proofs))

(defun t3-book-spines-make-book-proofs (library packages visible)
  (list :t3-book-values-book-proofs library packages visible))

(defun t3-book-spines-library (lib)
  (if (t3-book-spines-book-proofs-p lib) (cadr lib) lib))

(defun t3-book-spines-proof (lib)
  (library-library-proof (t3-book-spines-library lib)))

(defun t3-book-spines-book-packages (lib)
  (and (t3-book-spines-book-proofs-p lib) (caddr lib)))

(defun t3-book-spines-book-visible (lib)
  (and (t3-book-spines-book-proofs-p lib) (cadddr lib)))

(defun t3-book-spines-book-library-p (lib)
  (or (t3-book-spines-book-proofs-p lib)
      (eq (proof-proof-kind (t3-book-spines-proof lib)) :t3-book)))

(defun t3-book-spines-inherited-library (lib)
  (let* ((library (t3-book-spines-library lib))
         (proof (library-library-proof library)))
    (if (eq (proof-proof-kind proof) :t3-book)
        (library-library-with-proof library (proof-proof-with-kind proof :base))
      library)))

(defconst *t3-book-spines-symbolp* (proof-cl "SYMBOLP"))
(defconst *t3-book-spines-symbol-name* (proof-cl "SYMBOL-NAME"))
(defconst *t3-book-spines-char-code* (proof-cl "CHAR-CODE"))
(defconst *t3-book-spines-code-char* (proof-cl "CODE-CHAR"))
(defconst *t3-book-spines-coerce* (proof-cl "COERCE"))
(defconst *t3-book-spines-numberp* (proof-sym "ACL2-NUMBERP" "ACL2"))
(defconst *t3-book-spines-package-name* (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2"))
(defconst *t3-book-spines-imports* (proof-sym "PKG-IMPORTS" "ACL2"))
(defconst *t3-book-spines-witness* (proof-sym "PKG-WITNESS" "ACL2"))
(defconst *t3-book-spines-intern* (proof-sym "INTERN-IN-PACKAGE-OF-SYMBOL" "ACL2"))
(defconst *t3-book-spines-bad-atom* (proof-sym "BAD-ATOM<=" "ACL2"))

(defun t3-book-spines-tagged (value tag)
  (and (consp value) (equal (car value) tag)))

(defun t3-book-spines-book-package-value (book-proofs function datum)
  (if (not (t3-book-spines-tagged datum "str"))
      (if (equal function *t3-book-spines-imports*)
          *proof-nil*
        (proof-sym "ACL2-PKG-WITNESS" "ACL2"))
    (proof-with-checked-results ((package (proof-term-at datum 1)))
      (and (member-equal package (t3-book-spines-book-visible book-proofs))
           (let ((names (assoc-equal package (t3-book-spines-book-packages book-proofs))))
             (cond
              ((not names)
               '(:failure "MissingProofInput" ""))
              ((equal function *t3-book-spines-imports*)
               (or (table-values (cdr names)) *proof-nil*))
              ((not (assoc-equal "ACL2-PKG-WITNESS" (cdr names)))
               (proof-sym "ACL2-PKG-WITNESS" package))
              (t nil)))))))

(defun t3-book-spines-character-data (characters)
  (if (endp characters)
      nil
    (cons (list "char" (char-code (car characters)))
          (t3-book-spines-character-data (cdr characters)))))

(defun t3-book-spines-coerce-codes (items)
  (cond
   ((endp items) nil)
   ((t3-book-spines-tagged (car items) "dot") nil)
   (t
    (proof-with-checked-results
     ((code (if (t3-book-spines-tagged (car items) "char")
                (proof-term-at (car items) 1)
              0))
      (rest (t3-book-spines-coerce-codes (cdr items))))
     (cons code rest)))))

(defun t3-book-spines-coerce-bytes (codes)
  (if (endp codes)
      nil
    (let ((byte (if (eq (car codes) t) 1 (car codes))))
      (cond ((not (integerp byte))
             '(:failure "failure" ""))
            ((or (< byte 0) (< 255 byte))
             '(:failure "Unproved" ""))
            (t (proof-with-checked-results ((rest (t3-book-spines-coerce-bytes (cdr codes))))
                 (cons (code-char byte) rest)))))))

(defun t3-book-spines-character-items (items)
  (if (endp items)
      nil
    (cons (list "char" (car items))
          (t3-book-spines-character-items (cdr items)))))

(defun t3-book-spines-book-coerce (datum kind)
  (if (equal kind (proof-cl "LIST"))
      (if (t3-book-spines-tagged datum "str")
          (proof-with-checked-results ((contents (proof-term-at datum 1)))
            (cond ((or (equal contents "") (equal contents 0) (not contents)) *proof-nil*)
                  ((stringp contents)
                   (t3-book-spines-character-data (coerce contents 'list)))
                  ((integerp contents) '(:failure "failure" ""))
                  ((consp contents) (t3-book-spines-character-items contents))
                  ((eq contents t) '(:failure "failure" ""))
                  (t '(:failure "failure" ""))))
        *proof-nil*)
    (proof-with-checked-results
     ((codes (t3-book-spines-coerce-codes (if (proof-compound datum) datum nil)))
      (characters (t3-book-spines-coerce-bytes codes)))
     (list "str" (coerce characters 'string)))))

(defun t3-book-spines-constant-intern (book-proofs term first)
  (proof-with-checked-results
   ((last-arg (proof-term-at term 2))
    (second (proof-term-at last-arg 1)))
   (if (and (t3-book-spines-tagged first "str") (t3-book-spines-tagged second "sym"))
       (proof-with-checked-results ((package (proof-term-at second 1)))
         (let ((imports (assoc-equal package (t3-book-spines-book-packages book-proofs))))
           (and imports
                (proof-with-checked-results ((name (proof-term-at first 1)))
                  (table-get (cdr imports) name (list "sym" package name))))))
     *proof-nil*)))

(defun t3-book-spines-constant-result (book-proofs term function first)
  (let ((symbolp (t3-book-spines-tagged first "sym")))
    (cond
     ((equal function *t3-book-spines-symbolp*) (if symbolp *proof-t* *proof-nil*))
     ((equal function *t3-book-spines-symbol-name*)
      (proof-with-checked-results ((name (if symbolp (proof-term-at first 2) "")))
        (list "str" name)))
     ((equal function *t3-book-spines-package-name*)
      (if (not symbolp)
          (list "str" "")
        (proof-with-checked-results ((package (proof-term-at first 1)))
          (and (member-equal package (t3-book-spines-book-visible book-proofs))
               (list "str" package)))))
     ((equal function *t3-book-spines-numberp*)
      (if (or (integerp first) (eq first t)
              (t3-book-spines-tagged first "ratio") (t3-book-spines-tagged first "complex"))
          *proof-t*
        *proof-nil*))
     ((equal function *t3-book-spines-char-code*)
      (if (t3-book-spines-tagged first "char") (proof-term-at first 1) 0))
     ((equal function *t3-book-spines-code-char*)
      (list "char" (if (or (eq first t) (and (integerp first) (<= 0 first) (<= first 255)))
                       first
                     0)))
     ((equal function *t3-book-spines-coerce*)
      (proof-with-checked-results
       ((last-arg (proof-term-at term 2))
        (kind (proof-term-at last-arg 1)))
       (t3-book-spines-book-coerce first kind)))
     ((member-equal function (list *t3-book-spines-imports* *t3-book-spines-witness*))
      (t3-book-spines-book-package-value book-proofs function first))
     ((equal function *t3-book-spines-intern*)
      (t3-book-spines-constant-intern book-proofs term first))
     ((equal function *t3-book-spines-bad-atom*) *proof-nil*)
     (t nil))))

(defun t3-book-spines-book-constant (book-proofs term)
  (let ((lib (t3-book-spines-library book-proofs)))
    (proof-with-checked-results ((known (t3-logic-libraryproofs-constant (t3-book-spines-inherited-library lib) term)))
      (if (or known (not (proof-all-quoted-p (cdr term))))
          known
        (proof-with-checked-results
         ((function (proof-term-at term 0))
          (first (if (consp (cdr term)) (proof-term-at (cadr term) 1) *proof-nil*))
          (result (t3-book-spines-constant-result book-proofs term function first)))
         (if (or result (equal function *t3-book-spines-char-code*))
             (proof-proof-compute (library-library-proof lib) term result)
           nil))))))

(mutual-recursion
 (defun t3-book-spines-simplify-visit (n book-proofs term evidence definitions)
   (declare (xargs :measure (nfix n)))
   (let* ((lib (t3-book-spines-library book-proofs))
          (proof (library-library-proof lib))
          (head (car term)))
     (cond
      ((zp n) '(:failure "Fuel" "t3-book-spines-book-simplify"))
      ((or (not (proof-compound term)) (equal head *proof-quote*)) nil)
      ((endp term) (proof-term-at term 0))
      ((or (proof-compound head) (member-equal head definitions))
       (proof-with-checked-results
        ((expansion (proof-simplify-expansion proof term))
         (next (t3-book-spines-simplify-visit (1- n) book-proofs (cadr expansion)
                                             evidence definitions)))
        (proof-proof-chain proof (car expansion) (list next))))
      ((equal head *proof-if*)
       (proof-with-checked-results
        ((test (proof-term-at term 1))
         (first (t3-book-spines-simplify-visit (1- n) book-proofs test evidence definitions))
         (path (proof-simplify-if-path proof term first evidence)))
        (if (eq (car path) :simplify)
            (proof-with-checked-results
             ((next (t3-book-spines-simplify-visit (1- n) book-proofs (caddr path)
                                                 evidence definitions)))
             (proof-proof-chain proof (cadr path) (list next)))
          path)))
      (t
       (proof-with-checked-results
        ((result (t3-book-spines-simplify-arguments (1- n) book-proofs term (cdr term)
                                                  1 nil evidence definitions))
         (current (if result (proof-rewritten-term result) term))
         (constant (t3-book-spines-book-constant book-proofs current)))
        (cond ((not constant) result)
              (result (proof-proof-chain proof result (list constant)))
              (t constant)))))))

 (defun t3-book-spines-simplify-arguments (n book-proofs term args index result evidence definitions)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t3-book-spines-book-simplify"))
    ((endp args) result)
    (t
     (proof-with-checked-results
      ((equation (t3-book-spines-simplify-visit (1- n) book-proofs (car args) evidence definitions))
       (next (proof-simplify-argument-result
              (library-library-proof (t3-book-spines-library book-proofs))
              term index result equation)))
      (t3-book-spines-simplify-arguments (1- n) book-proofs term (cdr args)
                                       (1+ index) next evidence definitions))))))

(defun t3-book-spines-book-simplify (book-proofs term evidence definitions)
  (t3-book-spines-simplify-visit 1000000 book-proofs term evidence definitions))

(defun t3-book-spines-library-constant (lib term)
  (if (t3-book-spines-book-library-p lib)
      (t3-book-spines-book-constant lib term)
    (t3-logic-libraryproofs-constant lib term)))

(defund t3-book-spines-library-simplify (lib term evidence definitions)
  (if (t3-book-spines-book-library-p lib)
      (t3-book-spines-book-simplify lib term evidence definitions)
    (t3-logic-libraryproofs-simplify lib term evidence definitions)))

(defund t3-book-spines-library-normalize (lib value evidence definitions)
  (t3-book-spines-library-simplify lib value evidence
                                  (append *t3-logic-wrappers* definitions)))

(defconst *t3-book-spines-guards*
  (list (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "NULL")
        (proof-cl "EQ") (proof-cl "EQL") (proof-cl "NOT")))

(defun t3-book-spines-callback-p (value)
  (and (consp value) (eq (car value) :callback)))

(defun t3-book-spines-callback-kind (value)
  (cadr value))

(defun t3-book-spines-callback-args (value)
  (cddr value))

(defun t3-book-spines-step-at (step index)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun t3-book-spines-constructor-form-rewrite (proof value equation branch index)
  (if branch
      (proof-with-checked-results
       ((previous (or equation (proof-proof-reflexive proof value))))
       (proof-proof-rewrite proof previous branch (list 1 2 index)))
    equation))

(defun t3-book-spines-constructor-form-loop (n lib value evidence definitions)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t3-book-spines-constructor-form")
    (let ((proof (t3-book-spines-proof lib)))
      (proof-with-checked-results
       ((equation (t3-book-spines-library-normalize lib value evidence definitions))
        (current (if equation (t3-book-spines-step-at equation 2) value))
        (equation
         (if (proof-is-call current *proof-if*)
             (proof-with-checked-results
              ((yes (proof-term-at current 2))
               (branch (t3-book-spines-constructor-form-loop (1- n) lib yes evidence definitions))
               (equation (t3-book-spines-constructor-form-rewrite proof value equation branch 2))
               (no (proof-term-at current 3))
               (branch (t3-book-spines-constructor-form-loop (1- n) lib no evidence definitions)))
              (t3-book-spines-constructor-form-rewrite proof value equation branch 3))
           equation)))
       (and equation (proof-proof-tidy proof equation))))))

(defun t3-book-spines-constructor-form (lib value evidence definitions)
  (t3-book-spines-constructor-form-loop 1000000 lib value evidence definitions))

(defun t3-book-spines-shallow (lib term evidence)
  (let ((proof (t3-book-spines-proof lib)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof term))
      (value (t3-book-spines-step-at opened 2))
      (constructor (t3-book-spines-constructor-form lib value evidence *t3-book-spines-guards*)))
     (proof-proof-chain proof opened (list constructor)))))

(defun t3-book-spines-replace-value (lib equation replacements)
  (declare (xargs :measure (acl2-count replacements)))
  (if (endp replacements)
      equation
    (proof-with-checked-results
     ((value (t3-book-spines-step-at equation 2))
      (slot (t3-book-spines-step-at (car replacements) 1))
      (rewritten (proof-proof-rewrite-result (t3-book-spines-proof lib)
                                            equation (car replacements)
                                            (proof-eq *proof-false* value) slot)))
     (t3-book-spines-replace-value lib rewritten (cdr replacements)))))

(defun t3-book-spines-bindings-map (pairs bindings)
  (if (endp pairs)
      bindings
    (t3-book-spines-bindings-map (cdr pairs)
                                 (table-put bindings (caar pairs) (cadar pairs)))))

(defun t3-book-spines-substitute-args (args mapping)
  (if (endp args)
      nil
    (proof-with-checked-results
     ((first (proof-subst (car args) mapping))
      (rest (t3-book-spines-substitute-args (cdr args) mapping)))
     (cons first rest))))

(defun t3-book-spines-actuals (calls mapping substitute)
  (if (endp calls)
      nil
    (let ((arguments (termination-call-actuals (car calls))))
      (proof-with-checked-results
       ((first (if substitute
                   (t3-book-spines-substitute-args arguments mapping)
                 arguments))
        (rest (t3-book-spines-actuals (cdr calls) mapping substitute)))
       (cons first rest)))))

(defun t3-book-spines-changes (left right index)
  (if (or (endp left) (endp right))
      nil
    (let ((rest (t3-book-spines-changes (cdr left) (cdr right) (1+ index))))
      (if (equal (car left) (car right))
          rest
        (cons (list index (car left) (car right)) rest)))))

(defun t3-book-spines-occurs-once (argument args)
  (let ((found (member-equal argument args)))
    (and found (not (member-equal argument (cdr found))))))

(defun t3-book-spines-invalid-bindings-p (changes arguments)
  (and (consp changes)
       (let ((arg (cadar changes)))
         (or (proof-compound arg)
             (not (t3-book-spines-occurs-once arg arguments))
             (t3-book-spines-invalid-bindings-p (cdr changes) arguments)))))

(defun t3-book-spines-tail-bindings (lib call)
  (proof-with-checked-results ((head (proof-term-at call 0)))
    (let ((definition (assoc-equal head (proof-proof-definitions (t3-book-spines-proof lib)))))
      (if (not definition)
          '(:failure "failure" "")
        (proof-with-checked-results
         ((fields (proof-list-of-length (cdr definition) 2))
          (calls (termination-recursive-calls *termination-all* (list (cons head fields))))
          (actuals (t3-book-spines-actuals
                    calls (t3-book-spines-bindings-map (seq-zip (car fields) (cdr call)) nil)
                    t)))
         (let ((distinct (proof-unique actuals)))
           (if (equal (len distinct) 1)
               (let ((changes (t3-book-spines-changes (cdr call) (car distinct) 1)))
                 (and (not (t3-book-spines-invalid-bindings-p changes (cdr call)))
                      (strip-cdrs changes)))
             nil)))))))

(defun t3-book-spines-map-parameter (lib call)
  (if (not (proof-compound call))
      nil
    (proof-with-checked-results ((head (proof-term-at call 0)))
      (let ((definition (assoc-equal head (proof-proof-definitions (t3-book-spines-proof lib)))))
        (and definition
             (proof-with-checked-results
              ((fields (proof-list-of-length (cdr definition) 2))
               (calls (termination-recursive-calls *termination-all* (list (cons head fields))))
               (actuals (t3-book-spines-actuals calls nil nil)))
              (let ((distinct (proof-unique actuals)))
                (if (equal (len distinct) 1)
                    (let ((changes (t3-book-spines-changes (car fields) (car distinct) 1)))
                      (if (equal (len changes) 1)
                          (let* ((change (car changes))
                                 (formal (cadr change))
                                 (actual (caddr change)))
                            (proof-with-checked-results
                             ((variable (proof-term-at call (car change))))
                             (and (equal actual (list *library-cdr* formal))
                                  (not (proof-compound variable))
                                  (t3-book-spines-occurs-once variable (cdr call))
                                  variable)))
                        nil))
                  nil))))))))

(defun t3-book-spines-all-lengths-p (terms)
  (or (endp terms)
      (and (proof-is-call (car terms) *library-len*)
           (t3-book-spines-all-lengths-p (cdr terms)))))

(defun t3-book-spines-mapped-list-consumer (lib formula lengthp)
  (if lengthp
      (proof-term-at formula 1)
    (and (proof-compound formula)
         (equal (len formula) 2)
         (assoc-equal (car formula) (proof-proof-definitions (t3-book-spines-proof lib)))
         formula)))

(defun t3-book-spines-mapped-list-matches (holds value call pairs)
  (if holds
      (and (proof-is-call value *proof-cons*)
           (proof-with-checked-results
            ((tail (proof-term-at value 2))
             (repeated (proof-subst call (t3-book-spines-bindings-map pairs nil))))
            (equal tail repeated)))
    (equal value *proof-false*)))

(defun t3-book-spines-mapped-list-length-case (lib holds observed expected evidence)
  (let ((proof (t3-book-spines-proof lib)))
    (proof-with-checked-results
     ((observed
       (if holds
           (proof-with-checked-results ((value (t3-book-spines-step-at observed 2)))
             (if (proof-is-call value *proof-plus*)
                 (proof-with-checked-results
                  ((addend (proof-term-at value 2))
                   (before (t3-book-spines-step-at (cadr evidence) 1)))
                  (if (equal addend before)
                      (proof-with-checked-results
                       ((rewritten (proof-proof-rewrite proof observed (cadr evidence) '(1 2 2))))
                       (proof-proof-tidy proof rewritten))
                    observed))
               observed))
         observed))
      (actual (t3-book-spines-step-at observed 2))
      (wanted (t3-book-spines-step-at expected 2)))
     (and (equal actual wanted)
          (proof-with-checked-results ((back (proof-proof-symmetric proof expected)))
            (proof-proof-chain proof observed (list back)))))))

(defun t3-book-spines-mapped-list-prove-case
    (holds lib call consumer lengthp formula variable test pairs hypothesis solve)
  (let ((proof (t3-book-spines-proof lib)))
    (proof-with-checked-results
     ((guard (proof-proof-assume proof test holds))
      (opened (t3-book-spines-shallow lib call (list guard)))
      (value (t3-book-spines-step-at opened 2))
      (matches (t3-book-spines-mapped-list-matches holds value call pairs)))
     (and matches
          (proof-with-checked-results
           ((same (proof-proof-reflexive proof consumer))
            (observed (proof-proof-rewrite proof same opened '(1 2 1)))
            (value (t3-book-spines-step-at observed 2))
            (read-value (t3-book-spines-shallow lib value (list guard)))
            (observed (proof-proof-chain proof observed (list read-value)))
            (evidence
             (if holds
                 (proof-with-checked-results
                  ((assumed (proof-proof-assume proof hypothesis t))
                   (smaller (library-library-builtin (t3-book-spines-library lib) 3 variable))
                   (induction (proof-proof-prove-if proof assumed smaller)))
                  (list guard induction))
               (list guard))))
           (if lengthp
               (proof-with-checked-results
                ((right (proof-term-at formula 2))
                 (expected (t3-book-spines-shallow lib right (list guard))))
                (t3-book-spines-mapped-list-length-case lib holds observed expected evidence))
             (proof-with-checked-results ((target (t3-book-spines-step-at observed 2)))
               (if (endp solve)
                   (list :callback :solve target evidence)
                 (proof-with-checked-results ((reply (car solve)))
                   (if reply
                       (proof-proof-transport proof reply observed)
                     (let ((back (proof-proof-symmetric proof observed)))
                       (if (failure-p back)
                           back
                         '(:failure "failure" "")))))))))))))

(defun t3-book-spines-mapped-list-cases (lib formula consumer call lengthp variable solve)
  (let* ((proof (t3-book-spines-proof lib))
         (test (list *proof-consp* variable))
         (tail (list *library-cdr* variable))
         (pairs (list (list variable tail)))
         (measure (list *library-count* variable))
         (smaller (list *proof-ordinal-less* (list *library-count* tail) measure)))
    (proof-with-checked-results
     ((substituted (proof-subst formula (t3-book-spines-bindings-map pairs nil))))
     (let ((hypothesis (proof-ite smaller substituted *proof-true*)))
       (proof-with-checked-results
        ((base (t3-book-spines-mapped-list-prove-case
                nil lib call consumer lengthp formula variable test pairs hypothesis solve)))
        (if (t3-book-spines-callback-p base)
            base
          (and base
               (proof-with-checked-results
                ((step (t3-book-spines-mapped-list-prove-case
                        t lib call consumer lengthp formula variable test pairs hypothesis
                        (if lengthp solve (cdr solve)))))
                (if (t3-book-spines-callback-p step)
                    step
                  (and step
                       (proof-with-checked-results
                        ((ordinal (library-library-builtin (t3-book-spines-library lib) 1 variable))
                         (cases (proof-proof-cases proof test step base)))
                        (proof-proof-induct proof ordinal cases formula measure
                                            (list pairs)))))))))))))

(defun t3-book-spines-mapped-list (lib formula solve)
  (let ((lengthp (and (proof-is-call formula *proof-equal*)
                      (t3-book-spines-all-lengths-p (cdr formula)))))
    (proof-with-checked-results
     ((consumer (t3-book-spines-mapped-list-consumer lib formula lengthp)))
     (and consumer
          (proof-with-checked-results
           ((call (proof-term-at consumer 1))
            (variable (t3-book-spines-map-parameter lib call)))
           (and variable
                (proof-with-checked-results
                 ((shape (if lengthp
                             (proof-with-checked-results ((right (proof-term-at formula 2)))
                               (equal right (list *library-len* variable)))
                           t)))
                 (and shape
                      (t3-book-spines-mapped-list-cases
                       lib formula consumer call lengthp variable solve)))))))))

(defun t3-book-spines-same-defined-fold-p (lib left right)
  (and (proof-compound left)
       (proof-with-checked-results ((head (proof-term-at left 0)))
         (and (proof-is-call right head)
              (if (assoc-equal head (proof-proof-definitions (t3-book-spines-proof lib))) t nil)))))

(defun t3-book-spines-fold-over-list-fix-equations
    (lib holds test fix variable pairs left right index)
  (let ((proof (t3-book-spines-proof lib)))
    (proof-with-checked-results
     ((guard (proof-proof-assume proof test holds))
      (opened (t3-book-spines-shallow lib fix (list guard)))
      (repeated (proof-subst fix (t3-book-spines-bindings-map pairs nil)))
      (value (t3-book-spines-step-at opened 2)))
     (and (equal value (if holds (list *proof-cons* (list *library-car* variable) repeated)
                         *proof-false*))
          (proof-with-checked-results
           ((same (proof-proof-reflexive proof left))
            (replaced (proof-proof-rewrite proof same opened (list 1 2 index)))
            (value (t3-book-spines-step-at replaced 2))
            (opened (t3-book-spines-shallow lib value (list guard)))
            (lhs (proof-proof-chain proof replaced (list opened)))
            (rhs (t3-book-spines-shallow lib right (list guard))))
           (list lhs rhs))))))

(defun t3-book-spines-fold-over-list-fix-try
    (choices lib formula variable tail test measure smaller yes base)
  (if (endp choices)
      nil
    (let ((proof (t3-book-spines-proof lib))
          (bindings (car choices)))
      (proof-with-checked-results
       ((step
         (and (member-equal (list variable tail) bindings)
              (proof-with-checked-results
               ((substituted (proof-subst formula (t3-book-spines-bindings-map bindings nil)))
                (assumed (proof-proof-assume proof (proof-ite smaller substituted *proof-true*) t))
                (decrease (library-library-builtin (t3-book-spines-library lib) 3 variable))
                (induction (proof-proof-prove-if proof assumed decrease))
                (lhs (t3-book-spines-replace-value lib (car yes) (list induction)))
                (actual (t3-book-spines-step-at lhs 2))
                (wanted (t3-book-spines-step-at (cadr yes) 2)))
               (and (equal actual wanted)
                    (proof-with-checked-results
                     ((back (proof-proof-symmetric proof (cadr yes)))
                      (step (proof-proof-chain proof lhs (list back)))
                      (ordinal (library-library-builtin (t3-book-spines-library lib) 1 variable))
                      (cases (proof-proof-cases proof test step base)))
                     (proof-proof-induct proof ordinal cases formula measure (list bindings))))))))
       (or step
           (t3-book-spines-fold-over-list-fix-try
            (cdr choices) lib formula variable tail test measure smaller yes base))))))

(defun t3-book-spines-fold-over-list-fix-cases (lib formula left right index fix variable)
  (let* ((proof (t3-book-spines-proof lib))
         (test (list *proof-consp* variable))
         (tail (list *library-cdr* variable))
         (pairs (list (list variable tail)))
         (measure (list *library-count* variable))
         (smaller (list *proof-ordinal-less* (list *library-count* tail) measure)))
    (proof-with-checked-results
     ((yes (t3-book-spines-fold-over-list-fix-equations lib t test fix variable
                                                       pairs left right index)))
     (and yes
          (proof-with-checked-results
           ((no (t3-book-spines-fold-over-list-fix-equations lib nil test fix variable
                                                           pairs left right index)))
           (and no
                (proof-with-checked-results
                 ((actual (t3-book-spines-step-at (car no) 2))
                  (wanted (t3-book-spines-step-at (cadr no) 2)))
                 (and (equal actual wanted)
                      (proof-with-checked-results
                       ((back (proof-proof-symmetric proof (cadr no)))
                        (base (proof-proof-chain proof (car no) (list back)))
                        (synchronized (t3-book-spines-tail-bindings lib right)))
                       (t3-book-spines-fold-over-list-fix-try
                        (list pairs synchronized) lib formula variable tail test measure
                        smaller yes base))))))))))

(defun t3-book-spines-fold-over-list-fix (lib formula)
  (and (proof-is-call formula *proof-equal*)
       (proof-with-checked-results
        ((sides (proof-list-of-length (cdr formula) 2))
         (shape (t3-book-spines-same-defined-fold-p lib (car sides) (cadr sides))))
        (and shape
             (let* ((left (car sides))
                    (right (cadr sides))
                    (changes (t3-book-spines-changes (cdr left) (cdr right) 1)))
               (and (equal (len changes) 1)
                    (let* ((change (car changes))
                           (fix (cadr change))
                           (variable (caddr change)))
                      (and (not (proof-compound variable))
                           (proof-with-checked-results ((mapped (t3-book-spines-map-parameter lib fix)))
                             (and (equal mapped variable)
                                  (t3-book-spines-fold-over-list-fix-cases
                                   lib formula left right (car change) fix variable)))))))))))

(defun t3-book-spines-car-of-fix (lib fix variable)
  (let* ((proof (t3-book-spines-proof lib))
         (test (list *proof-consp* variable))
         (call (list *library-car* fix)))
    (proof-with-checked-results
     ((cons-guard (proof-proof-assume proof test t))
      (atom-guard (proof-proof-assume proof test nil))
      (yes (t3-book-spines-shallow lib fix (list cons-guard)))
      (no (t3-book-spines-shallow lib fix (list atom-guard)))
      (value (t3-book-spines-step-at yes 2)))
     (and (proof-is-call value *proof-cons*)
          (proof-with-checked-results ((head (proof-term-at value 1)))
            (and (equal head (list *library-car* variable))
                 (proof-with-checked-results ((absent-value (t3-book-spines-step-at no 2)))
                   (and (equal absent-value *proof-false*)
                        (proof-with-checked-results
                         ((same (proof-proof-reflexive proof call))
                          (a (t3-book-spines-replace-value lib same (list yes)))
                          (same (proof-proof-reflexive proof call))
                          (b (t3-book-spines-replace-value lib same (list no)))
                          (value (t3-book-spines-step-at a 2))
                          (constant (t3-book-spines-library-constant lib value))
                          (on-cons (proof-proof-chain proof a (list constant)))
                          (absent (library-library-axiom (t3-book-spines-library lib) "COMPLETION-OF-CAR" (list variable)))
                          (value (t3-book-spines-step-at absent 2))
                          (selected (proof-proof-select proof value atom-guard))
                          (absent (proof-proof-chain proof absent (list selected)))
                          (value (t3-book-spines-step-at b 2))
                          (constant (t3-book-spines-library-constant lib value))
                          (back (proof-proof-symmetric proof absent))
                          (on-atom (proof-proof-chain proof b (list constant back))))
                         (proof-proof-cases proof test on-cons on-atom))))))))))

(defun t3-book-spines-commuting-axis (pairs variable)
  (if (endp pairs)
      nil
    (let ((arg (caar pairs)))
      (if (and (not (equal arg variable))
               (equal (cadar pairs) (list *library-cdr* arg)))
          arg
        (t3-book-spines-commuting-axis (cdr pairs) variable)))))

(defun t3-book-spines-commuting-result
    (lib result value recursive induction fix variable head replies)
  (let ((proof (t3-book-spines-proof lib)))
    (proof-with-checked-results
     ((current (t3-book-spines-step-at result 2))
      (recursive-call (and recursive (t3-book-spines-step-at induction 1))))
     (cond
      ((and recursive (equal current recursive-call))
       (proof-with-checked-results ((step (proof-proof-chain proof result (list induction))))
         (cons step replies)))
      ((equal current (list *library-car* fix))
       (proof-with-checked-results
        ((equation (t3-book-spines-car-of-fix lib fix variable))
         (step (proof-proof-chain proof result (list equation))))
        (cons step replies)))
      ((and (member-equal fix (cdr current)) (not (proof-is-call current head)))
       (if (endp replies)
           (cons (list :callback :rewriting current) nil)
         (proof-with-checked-results
          ((equation (car replies))
           (step (if equation
                     (proof-proof-chain proof result (list equation))
                   (and (not (equal current value)) result))))
          (cons step (cdr replies)))))
      (t (cons (and (not (equal current value)) result) replies))))))

(defund t3-book-spines-commuting-reflexive (lib value)
  (proof-proof-reflexive (t3-book-spines-proof lib) value))

(defund t3-book-spines-commuting-rewrite (lib result equation index)
  (if equation
      (let ((proof (t3-book-spines-proof lib)))
        (proof-with-checked-results
         ((step (proof-proof-rewrite proof result equation (list 1 2 index))))
         (proof-proof-tidy proof step)))
    result))

(mutual-recursion
 (defun t3-book-spines-commuting-step-visit
     (n value recursive lib induction fix variable head replies)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t3-book-spines-commuting-list-fix-step-equation"))
    ((or (not (proof-compound value)) (proof-is-call value *proof-quote*))
     (cons nil replies))
    (t
     (proof-with-checked-results
      ((result (t3-book-spines-commuting-reflexive lib value))
       (arguments (t3-book-spines-commuting-step-arguments
                   (1- n) (cdr value) 1 result recursive lib induction fix variable head replies)))
      (if (t3-book-spines-callback-p (car arguments))
          arguments
        (t3-book-spines-commuting-result lib (car arguments) value recursive induction
                                        fix variable head (cdr arguments)))))))

 (defun t3-book-spines-commuting-step-arguments
     (n args index result recursive lib induction fix variable head replies)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t3-book-spines-commuting-list-fix-step-equation"))
    ((endp args) (cons result replies))
    (t
     (proof-with-checked-results
      ((argument (t3-book-spines-commuting-step-visit
                  (1- n) (car args) recursive lib induction fix variable head replies)))
      (if (t3-book-spines-callback-p (car argument))
          argument
        (proof-with-checked-results
         ((result (t3-book-spines-commuting-rewrite lib result (car argument) index)))
         (t3-book-spines-commuting-step-arguments
          (1- n) (cdr args) (1+ index) result recursive lib induction fix variable head
          (cdr argument)))))))))

(defun t3-book-spines-commuting-list-fix-step-equation
    (value recursive lib induction fix variable head replies)
  (t3-book-spines-commuting-step-visit
   1000000 value recursive lib induction fix variable head replies))

(defun t3-book-spines-chain-if-equal (proof lhs rhs)
  (proof-with-checked-results
   ((actual (t3-book-spines-step-at lhs 2))
    (expected (t3-book-spines-step-at rhs 2)))
   (and (equal actual expected)
        (proof-with-checked-results ((back (proof-proof-symmetric proof rhs)))
          (proof-proof-chain proof lhs (list back))))))

(defun t3-book-spines-commuting-case
    (lib holds test left right induction fix variable replies)
  (let ((proof (t3-book-spines-proof lib)))
    (proof-with-checked-results
     ((guard (proof-proof-assume proof test holds))
      (lhs (t3-book-spines-shallow lib left (list guard)))
      (rhs (t3-book-spines-shallow lib right (list guard)))
      (value (t3-book-spines-step-at lhs 2))
      (equation (t3-book-spines-commuting-list-fix-step-equation
                 value holds lib induction fix variable (car left) replies)))
     (if (t3-book-spines-callback-p (car equation))
         equation
       (proof-with-checked-results
        ((lhs (proof-proof-chain proof lhs (list (car equation))))
         (step (t3-book-spines-chain-if-equal proof lhs rhs)))
        (cons step (cdr equation)))))))

(defun t3-book-spines-commuting-cases
    (lib formula left right fix variable axis pairs replies)
  (let* ((proof (t3-book-spines-proof lib))
         (test (list *proof-consp* axis))
         (measure (list *library-count* axis))
         (smaller (list *proof-ordinal-less*
                        (list *library-count* (list *library-cdr* axis)) measure)))
    (proof-with-checked-results
     ((substituted (proof-subst formula (t3-book-spines-bindings-map pairs nil)))
      (assumed (proof-proof-assume proof (proof-ite smaller substituted *proof-true*) t))
      (decrease (library-library-builtin (t3-book-spines-library lib) 3 axis))
      (induction (proof-proof-prove-if proof assumed decrease))
      (yes (t3-book-spines-commuting-case lib t test left right induction fix variable replies)))
     (cond
      ((t3-book-spines-callback-p (car yes)) (car yes))
      ((not (car yes)) nil)
      (t
       (proof-with-checked-results
        ((no (t3-book-spines-commuting-case lib nil test left right induction fix variable (cdr yes))))
        (if (t3-book-spines-callback-p (car no))
            (car no)
          (and (car no)
               (proof-with-checked-results
                ((ordinal (library-library-builtin (t3-book-spines-library lib) 1 axis))
                 (cases (proof-proof-cases proof test (car yes) (car no))))
                (proof-proof-induct proof ordinal cases formula measure (list pairs)))))))))))

(defun t3-book-spines-commuting-list-fix (lib formula rewriting)
  (and (proof-is-call formula *proof-equal*)
       (proof-with-checked-results
        ((sides (proof-list-of-length (cdr formula) 2))
         (shape (t3-book-spines-same-defined-fold-p lib (car sides) (cadr sides))))
        (and shape
             (let* ((left (car sides))
                    (right (cadr sides))
                    (changes (t3-book-spines-changes (cdr left) (cdr right) 1)))
               (and (equal (len changes) 1)
                    (let* ((change (car changes))
                           (fix (cadr change))
                           (variable (caddr change)))
                      (and (not (proof-compound variable))
                           (proof-with-checked-results ((mapped (t3-book-spines-map-parameter lib fix)))
                             (and (equal mapped variable)
                                  (proof-with-checked-results ((pairs (t3-book-spines-tail-bindings lib right)))
                                    (let ((axis (t3-book-spines-commuting-axis pairs variable)))
                                      (and axis
                                           (t3-book-spines-commuting-cases
                                            lib formula left right fix variable axis pairs
                                            rewriting))))))))))))))

(defun t3-book-spines-removal-over-list-fix-branch (tests lib fixed left original right)
  (let ((proof (t3-book-spines-proof lib)))
    (proof-with-checked-results
     ((retained (t3-book-spines-shallow lib fixed tests))
      (same (proof-proof-reflexive proof left))
      (lhs (t3-book-spines-replace-value lib same (list retained)))
      (value (t3-book-spines-step-at lhs 2))
      (opened (t3-book-spines-shallow lib value tests))
      (lhs (proof-proof-chain proof lhs (list opened)))
      (dropped (t3-book-spines-shallow lib original tests))
      (same (proof-proof-reflexive proof right))
      (rhs (t3-book-spines-replace-value lib same (list dropped)))
      (actual (t3-book-spines-step-at lhs 2))
      (expected (t3-book-spines-step-at rhs 2))
      (rhs (if (equal actual expected)
               rhs
             (proof-with-checked-results ((opened (t3-book-spines-shallow lib expected tests)))
               (proof-proof-chain proof rhs (list opened))))))
     (list lhs rhs))))

(defun t3-book-spines-removal-over-list-fix-cases (lib formula left right fixed original key variable)
  (let* ((proof (t3-book-spines-proof lib))
         (test (list *proof-consp* variable))
         (tail (list *library-cdr* variable))
         (pairs (list (list variable tail)))
         (measure (list *library-count* variable))
         (smaller (list *proof-ordinal-less* (list *library-count* tail) measure))
         (selected (proof-eq key (list *library-car* variable))))
    (proof-with-checked-results
     ((substituted (proof-subst formula (t3-book-spines-bindings-map pairs nil)))
      (assumed (proof-proof-assume proof (proof-ite smaller substituted *proof-true*) t))
      (decrease (library-library-builtin (t3-book-spines-library lib) 3 variable))
      (induction (proof-proof-prove-if proof assumed decrease))
      (atom-guard (proof-proof-assume proof test nil))
      (atom-eqs (t3-book-spines-removal-over-list-fix-branch
                 (list atom-guard) lib fixed left original right))
      (base (t3-book-spines-chain-if-equal proof (car atom-eqs) (cadr atom-eqs))))
     (and base
          (proof-with-checked-results
           ((cons-guard (proof-proof-assume proof test t))
            (selected-guard (proof-proof-assume proof selected t))
            (selected-eqs (t3-book-spines-removal-over-list-fix-branch
                           (list cons-guard selected-guard) lib fixed left original right))
            (hit (t3-book-spines-chain-if-equal proof (car selected-eqs) (cadr selected-eqs))))
           (and hit
                (proof-with-checked-results
                 ((not-selected (proof-proof-assume proof selected nil))
                  (other-eqs (t3-book-spines-removal-over-list-fix-branch
                              (list cons-guard not-selected) lib fixed left original right))
                  (lhs (t3-book-spines-replace-value lib (car other-eqs) (list induction)))
                  (miss (t3-book-spines-chain-if-equal proof lhs (cadr other-eqs))))
                 (and miss
                      (proof-with-checked-results
                       ((cases (proof-proof-cases proof selected hit miss))
                        (case-step (proof-proof-cases proof test cases base))
                        (ordinal (library-library-builtin (t3-book-spines-library lib) 1 variable)))
                       (proof-proof-induct proof ordinal case-step formula measure (list pairs)))))))))))

(defun t3-book-spines-removal-over-list-fix (lib formula)
  (and (proof-is-call formula *proof-equal*)
       (proof-with-checked-results ((sides (proof-list-of-length (cdr formula) 2)))
         (let ((left (car sides))
               (right (cadr sides)))
           (and (proof-compound left) (equal (len left) 3)
                (proof-compound right) (equal (len right) 2)
                (let* ((key (cadr left))
                       (fixed (caddr left))
                       (original (cadr right))
                       (variable (caddr original)))
                  (and (proof-is-call original (car left)) (equal (len original) 3)
                       (equal (cadr original) key)
                       (equal fixed (list (car right) variable))
                       (proof-with-checked-results ((mapped (t3-book-spines-map-parameter lib original)))
                         (and (equal mapped variable)
                              (proof-with-checked-results ((mapped (t3-book-spines-map-parameter lib fixed)))
                                (and (equal mapped variable)
                                     (t3-book-spines-removal-over-list-fix-cases
                                      lib formula left right fixed original key variable))))))))))))

(defun t3-book-spines-absence-proper-base (lib base proper variable no)
  (let ((proof (t3-book-spines-proof lib)))
    (proof-with-checked-results ((value (t3-book-spines-step-at base 2)))
      (if (not (equal value *proof-false*))
          base
        (proof-with-checked-results
         ((term (proof-step-first proper))
          (opened (t3-book-spines-shallow lib term (list no)))
          (value (t3-book-spines-step-at opened 2)))
         (and (equal value (proof-eq variable *proof-false*))
              (proof-with-checked-results
               ((rewritten (proof-proof-rewrite proof proper opened '(1)))
                (back (proof-proof-symmetric proof rewritten)))
               (proof-proof-chain proof base (list back)))))))))

(defun t3-book-spines-absence-base (lib operation proper variable no goal)
  (proof-with-checked-results
   ((base (t3-book-spines-shallow lib operation (list no)))
    (base (if proper
              (t3-book-spines-absence-proper-base lib base proper variable no)
            base)))
   (and base
        (proof-with-checked-results ((literal (proof-step-first base)))
          (and (equal literal goal) base)))))

(defun t3-book-spines-absence-member (lib member yes missing bindings)
  (let ((proof (t3-book-spines-proof lib)))
    (proof-with-checked-results
     ((look (t3-book-spines-shallow lib member (list yes)))
      (conditional (t3-book-spines-step-at look 2))
      (next-member (proof-subst member bindings)))
     (and (proof-is-call conditional *proof-if*)
          (proof-with-checked-results ((test (proof-term-at conditional 1)))
            (and (equal (cddr conditional) (list test next-member))
                 (proof-with-checked-results
                  ((opened (proof-proof-rewrite proof missing look '(1 1)))
                   (selection (proof-proof-if-true proof conditional))
                   (miss-first (proof-proof-rewrite proof opened selection '(1 1)))
                   (miss-first (proof-proof-tidy proof miss-first))
                   (selection (proof-proof-select proof conditional miss-first))
                   (miss-tail (proof-proof-rewrite proof opened selection '(1 1)))
                   (miss-tail (proof-proof-tidy proof miss-tail)))
                  (list miss-first miss-tail next-member))))))))

(defun t3-book-spines-absence-premise (lib proper yes guard bindings miss-tail tail)
  (if (not proper)
      miss-tail
    (let ((proof (t3-book-spines-proof lib)))
      (proof-with-checked-results
       ((term (proof-step-first proper))
        (tail-type (t3-book-spines-shallow lib term (list yes)))
        (known (proof-proof-rewrite proof proper tail-type '(1)))
        (known (proof-proof-tidy proof known))
        (literal (proof-step-first known)))
       (and (equal literal (list *t3-book-lemmas-true-listp* tail))
            (proof-with-checked-results
             ((substituted (proof-subst guard bindings))
              (selected (proof-proof-select proof substituted miss-tail)))
             (proof-proof-transport proof known selected)))))))

(defun t3-book-spines-absence-step (lib premise induction operation yes miss-first proper variable tail)
  (let ((proof (t3-book-spines-proof lib)))
    (proof-with-checked-results
     ((repeated (proof-proof-modus-ponens proof induction premise))
      (opened (t3-book-spines-shallow lib operation (list yes miss-first)))
      (step (proof-proof-rewrite-first proof opened repeated)))
     (if (not proper)
         step
       (proof-with-checked-results ((value (t3-book-spines-step-at step 2)))
         (if (equal value (list *proof-cons* (list *library-car* variable) tail))
             (proof-with-checked-results
              ((axiom (library-library-axiom (t3-book-spines-library lib) "CAR-CDR-ELIM" (list variable)))
               (reconstructed (proof-proof-modus-ponens proof axiom yes)))
              (proof-proof-chain proof step (list reconstructed)))
           step))))))

(defun t3-book-spines-absence-induct
    (lib formula goal guard member operation variable test yes base missing proper)
  (let* ((proof (t3-book-spines-proof lib))
         (tail (list *library-cdr* variable))
         (pairs (list (list variable tail)))
         (bindings (t3-book-spines-bindings-map pairs nil))
         (measure (list *library-count* variable))
         (smaller (list *proof-ordinal-less* (list *library-count* tail) measure)))
    (proof-with-checked-results
     ((members (t3-book-spines-absence-member lib member yes missing bindings)))
     (and members
          (let ((miss-first (car members))
                (miss-tail (cadr members))
                (next-member (caddr members)))
            (proof-with-checked-results
             ((substituted (proof-subst formula bindings))
              (assumed (proof-proof-assume proof (proof-ite smaller substituted *proof-true*) t))
              (decrease (library-library-builtin (t3-book-spines-library lib) 3 variable))
              (induction (proof-proof-prove-if proof assumed decrease))
              (premise (t3-book-spines-absence-premise lib proper yes guard bindings miss-tail tail)))
             (and premise
                  (proof-with-checked-results
                   ((step (t3-book-spines-absence-step
                           lib premise induction operation yes miss-first proper variable tail))
                    (claim (proof-step-first step)))
                   (and (equal claim goal)
                        (proof-with-checked-results ((claim (proof-step-first miss-tail)))
                          (and (equal claim (proof-neg next-member))
                               (proof-with-checked-results
                                ((cases (proof-proof-cases proof test step base))
                                 (case-step (t3-book-lemmas-implication (t3-book-spines-library lib) formula cases))
                                 (ordinal (library-library-builtin (t3-book-spines-library lib) 1 variable)))
                                (proof-proof-induct proof ordinal case-step formula measure
                                                    (list pairs))))))))))))))

(defun t3-book-spines-absence-cases (lib formula goal guard member operation variable proper-list)
  (let ((proof (t3-book-spines-proof lib))
        (test (list *proof-consp* variable)))
    (proof-with-checked-results
     ((assumed (proof-proof-assume proof guard t))
      (premises (if proper-list (proof-proof-conjunct proof assumed) (list assumed nil)))
      (yes (proof-proof-assume proof test t))
      (no (proof-proof-assume proof test nil))
      (base (t3-book-spines-absence-base lib operation (cadr premises) variable no goal)))
     (and base
          (t3-book-spines-absence-induct
           lib formula goal guard member operation variable test yes base
           (car premises) (cadr premises))))))

(defun t3-book-spines-absence-tests (guard)
  (if (proof-is-call guard *proof-if*)
      (proof-with-checked-results ((otherwise (proof-term-at guard 3)))
        (if (equal otherwise *proof-false*)
            (seq-slice guard 1 3)
          (list guard)))
    (list guard)))

(defun t3-book-spines-absence-shape (lib formula guard goal tests)
  (let ((denied (car tests)))
    (and (proof-is-call denied *proof-not*)
         (proof-with-checked-results ((member-call (proof-term-at denied 1)))
           (and (proof-compound member-call) (equal (len member-call) 3)
                (proof-with-checked-results ((sides (proof-list-of-length (cdr goal) 2)))
                  (let ((operation (car sides))
                        (expected (cadr sides))
                        (variable (caddr member-call))
                        (proper-list (equal (len tests) 2)))
                    (and (not (proof-compound variable))
                         (proof-with-checked-results ((mapped (t3-book-spines-map-parameter lib member-call)))
                           (and (equal mapped variable)
                                (proof-with-checked-results ((mapped (t3-book-spines-map-parameter lib operation)))
                                  (and (equal mapped variable)
                                       (if proper-list
                                           (and (equal (cadr tests) (list *t3-book-lemmas-true-listp* variable))
                                                (equal expected variable))
                                         (proof-is-call expected *proof-quote*))
                                       (t3-book-spines-absence-cases lib formula goal guard member-call
                                                                    operation variable proper-list)))))))))))))

(defun t3-book-spines-absence (lib formula)
  (and (proof-is-call formula *library-implies*)
       (proof-with-checked-results ((goal (proof-term-at formula 2)))
         (and (proof-is-call goal *proof-equal*)
              (proof-with-checked-results
               ((fields (proof-list-of-length (cdr formula) 2))
                (tests (t3-book-spines-absence-tests (car fields))))
               (t3-book-spines-absence-shape lib formula (car fields) goal tests))))))

(defun t3-book-spines-different-key-reduced (proofs induction lib removed left right)
  (let ((proof (t3-book-spines-proof lib)))
    (proof-with-checked-results
     ((removed-value (t3-book-spines-shallow lib removed proofs))
      (same (proof-proof-reflexive proof left))
      (lhs (proof-proof-rewrite proof same removed-value '(1 2 2)))
      (rhs (t3-book-spines-shallow lib right proofs))
      (actual (t3-book-spines-step-at lhs 2))
      (expected (t3-book-spines-step-at rhs 2))
      (lhs (if (equal actual expected)
               lhs
             (proof-with-checked-results ((opened (t3-book-spines-shallow lib actual proofs)))
               (proof-proof-chain proof lhs (list opened)))))
      (lhs (if induction (proof-proof-rewrite-first proof lhs induction) lhs))
      (original (t3-book-spines-step-at lhs 1)))
     (and (equal original left)
          (t3-book-spines-chain-if-equal proof lhs rhs)))))

(defun t3-book-spines-different-key-advance
    (lib formula removed left right variable test tail measure pairs selected
         assume-distinct cons-guard hits no)
  (let* ((proof (t3-book-spines-proof lib))
         (smaller (list *proof-ordinal-less* (list *library-count* tail) measure)))
    (proof-with-checked-results
     ((substituted (proof-subst formula (t3-book-spines-bindings-map pairs nil)))
      (assumed (proof-proof-assume proof (proof-ite smaller substituted *proof-true*) t))
      (decrease (library-library-builtin (t3-book-spines-library lib) 3 variable))
      (induction (proof-proof-prove-if proof assumed decrease))
      (remaining (proof-proof-modus-ponens proof induction assume-distinct))
      (not-selected (proof-proof-assume proof selected nil))
      (misses (t3-book-spines-different-key-reduced
                (list cons-guard not-selected) remaining lib removed left right)))
     (and misses
          (proof-with-checked-results
           ((cases (proof-proof-cases proof selected hits misses))
            (case-step (proof-proof-cases proof test cases no))
            (ordinal (library-library-builtin (t3-book-spines-library lib) 1 variable))
            (conditioned (t3-book-lemmas-implication (t3-book-spines-library lib) formula case-step)))
           (proof-proof-induct proof ordinal conditioned formula measure (list pairs)))))))

(defun t3-book-spines-different-key-cases (lib formula denied left right removed variable other)
  (let* ((proof (t3-book-spines-proof lib))
         (test (list *proof-consp* variable))
         (tail (list *library-cdr* variable))
         (measure (list *library-count* variable))
         (pairs (list (list variable tail)))
         (selected (proof-eq other (list *library-car* variable))))
    (proof-with-checked-results
     ((atom-guard (proof-proof-assume proof test nil))
      (no (t3-book-spines-different-key-reduced (list atom-guard) nil lib removed left right)))
     (and no
          (proof-with-checked-results
           ((assume-distinct (proof-proof-assume proof denied t))
            (cons-guard (proof-proof-assume proof test t))
            (matched (proof-proof-assume proof selected t))
            (different-head (proof-proof-rewrite proof assume-distinct matched '(1 1 2)))
            (different-head (proof-proof-tidy proof different-head))
            (hits (t3-book-spines-different-key-reduced
                   (list cons-guard matched different-head) nil lib removed left right)))
           (and hits
                (t3-book-spines-different-key-advance
                 lib formula removed left right variable test tail measure pairs selected
                 assume-distinct cons-guard hits no)))))))

(defun t3-book-spines-different-key-shape (lib formula denied left right)
  (and (proof-compound left) (equal (len left) 3)
       (proof-is-call right (car left)) (equal (len right) 3)
       (let ((key (cadr left))
             (removed (caddr left))
             (variable (caddr right)))
         (and (equal (cadr right) key) (not (proof-compound variable))
              (proof-with-checked-results ((mapped (t3-book-spines-map-parameter lib right)))
                (and (equal mapped variable)
                     (proof-with-checked-results ((mapped (t3-book-spines-map-parameter lib removed)))
                       (and (equal mapped variable) (equal (len removed) 3)
                            (let ((other (cadr removed)))
                              (and (equal denied (proof-neg (proof-eq key other)))
                                   (t3-book-spines-different-key-cases
                                    lib formula denied left right removed variable other)))))))))))

(defun t3-book-spines-different-key (lib formula)
  (and (proof-is-call formula *library-implies*)
       (proof-with-checked-results ((denied (proof-term-at formula 1)))
         (and (proof-is-call denied *proof-not*)
              (proof-with-checked-results ((goal (proof-term-at formula 2)))
                (and (proof-is-call goal *proof-equal*)
                     (proof-with-checked-results
                      ((fields (proof-list-of-length (cdr formula) 2))
                       (sides (proof-list-of-length (cdr (cadr fields)) 2)))
                      (t3-book-spines-different-key-shape lib formula denied
                                                        (car sides) (cadr sides)))))))))
