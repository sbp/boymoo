(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t4-evaluator-atom* (proof-cl "ATOM"))
(defconst *t4-evaluator-endp* (proof-cl "ENDP"))
(defconst *t4-evaluator-lambda* (proof-cl "LAMBDA"))
(defconst *t4-evaluator-symbolp* (proof-cl "SYMBOLP"))
(defconst *t4-evaluator-kwote* (proof-sym "KWOTE" "ACL2"))
(defconst *t4-evaluator-kwote-list* (proof-sym "KWOTE-LST" "ACL2"))
(defconst *t4-evaluator-operator* (proof-sym "T4-EVAL-OPERATOR" "ACL2"))
(defconst *t4-evaluator-values* (proof-sym "T4-EVAL-VALUES" "ACL2"))

(mutual-recursion
 (defun t4-evaluator-replace-terms (term replacements)
   (declare (xargs :measure (acl2-count term)))
   (let ((entry (assoc-equal term replacements)))
     (cond (entry (cdr entry))
           ((or (not (proof-compound term))
                (proof-is-call term *proof-quote*))
            term)
           ((endp term) '(:failure "malformed-candidate" ""))
           (t (proof-with-checked-results
               ((args (t4-evaluator-replace-terms-args (cdr term) replacements)))
               (cons (car term) args))))))
 (defun t4-evaluator-replace-terms-args (args replacements)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((arg (t4-evaluator-replace-terms (car args) replacements))
       (rest (t4-evaluator-replace-terms-args (cdr args) replacements)))
      (cons arg rest)))))

(defun t4-evaluator-argument-value-tail (tail obj values)
  (declare (xargs :measure (acl2-count tail)))
  (cond
   ((not (proof-is-call tail *library-cdr*))
    '(:failure "search-miss" ""))
   ((not (consp (cdr tail))) '(:failure "malformed-candidate" ""))
   ((not (equal (cadr tail) obj))
    (t4-evaluator-argument-value-tail
     (cadr tail) obj (list *library-cdr* values)))
   ((equal tail (list *library-cdr* obj))
    (list *library-car* values))
   (t '(:failure "search-miss" ""))))

(mutual-recursion
 (defun t4-evaluator-argument-value (term evaluator obj env values)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term evaluator)
     (proof-with-checked-results ((parts (proof-list-of-length term 3)))
       (let ((datum (cadr parts)) (environment (caddr parts)))
         (if (or (not (equal environment env))
                 (not (proof-is-call datum *library-car*)))
             '(:failure "search-miss" "")
           (proof-with-checked-results ((tail (proof-term-at datum 1)))
             (t4-evaluator-argument-value-tail tail obj values))))))
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) term)
    ((endp term) '(:failure "malformed-candidate" ""))
    (t (proof-with-checked-results
        ((args (t4-evaluator-argument-value-args
                (cdr term) evaluator obj env values)))
        (cons (car term) args)))))
 (defun t4-evaluator-argument-value-args (args evaluator obj env values)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((arg (t4-evaluator-argument-value (car args) evaluator obj env values))
       (rest (t4-evaluator-argument-value-args
              (cdr args) evaluator obj env values)))
      (cons arg rest)))))

(defun t4-evaluator-evaluator-lib (self) (nth 1 self))
(defun t4-evaluator-evaluator-ev (self) (nth 2 self))
(defun t4-evaluator-evaluator-list (self) (nth 3 self))
(defun t4-evaluator-evaluator-common (self) (nth 4 self))
(defun t4-evaluator-evaluator-operators (self) (nth 5 self))
(defun t4-evaluator-evaluator-obj (self) (nth 6 self))
(defun t4-evaluator-evaluator-env (self) (nth 7 self))
(defun t4-evaluator-evaluator-lst (self) (nth 8 self))
(defun t4-evaluator-evaluator-consp (self) (nth 9 self))
(defun t4-evaluator-evaluator-operator (self) (nth 10 self))
(defun t4-evaluator-evaluator-tail (self) (nth 11 self))
(defun t4-evaluator-evaluator-suffix (self) (nth 12 self))
(defun t4-evaluator-evaluator-properties (self) (nth 13 self))

(defun t4-evaluator-evaluator-with-lib (self lib)
  (update-nth 1 lib self))

(defun t4-evaluator-evaluator-with-properties (self properties)
  (update-nth 13 properties self))

(defun t4-evaluator-evaluator-proof (self)
  (library-library-proof (t4-evaluator-evaluator-lib self)))

(defun t4-evaluator-evaluator-init (prefix functions common operators suffix)
  (let* ((ground (proof-proof-init))
         (proof (proof-make-proof
                 (table-update (proof-proof-facts ground)
                                 (proof-proof-facts prefix))
                 (table-update (proof-proof-definitions ground)
                                 (proof-proof-definitions prefix))
                 (proof-proof-primitives ground))))
    (proof-with-checked-results
     ((lib (library-library-build (library-library-init proof)))
      (functions (proof-list-of-length functions 2))
      (obj-rule (proof-term-at common 0))
      (obj-equation (proof-term-at obj-rule 1))
      (obj-equation (proof-list-of-length obj-equation 3))
      (obj-call (proof-list-of-length (cadr obj-equation) 3))
      (lst-rule (proof-term-at common 4))
      (lst-equation (proof-term-at lst-rule 1))
      (lst-equation (proof-list-of-length lst-equation 3))
      (lst-call (proof-list-of-length (cadr lst-equation) 3)))
     (let ((obj (cadr obj-call)))
       (list :evaluator lib (car functions) (cadr functions) common operators
             obj (caddr obj-call) (cadr lst-call) (list *proof-consp* obj)
             (list *library-car* obj) (list *library-cdr* obj) suffix nil)))))

(defun t4-evaluator-evaluator-interpret (operators self result)
  (if (endp operators)
      result
    (proof-with-checked-results
     ((entry (proof-list-of-length (car operators) 2))
      (value (t4-evaluator-argument-value
              (cadr entry) (t4-evaluator-evaluator-ev self)
              (t4-evaluator-evaluator-obj self) (t4-evaluator-evaluator-env self)
              *t4-evaluator-values*)))
     (t4-evaluator-evaluator-interpret
      (cdr operators) self
      (proof-ite (proof-eq *t4-evaluator-operator* (car entry))
                 value result)))))

(defun t4-evaluator-evaluator-rule (common index)
  (proof-with-checked-results
   ((rule (proof-term-at common index))
    (parts (proof-list-of-length rule 2)))
   (cadr parts)))

(defun t4-evaluator-evaluator-definitions (self)
  (let* ((common (t4-evaluator-evaluator-common self))
         (ev (t4-evaluator-evaluator-ev self))
         (list-ev (t4-evaluator-evaluator-list self))
         (operator (t4-evaluator-evaluator-operator self))
         (env (t4-evaluator-evaluator-env self))
         (obj (t4-evaluator-evaluator-obj self))
         (lst (t4-evaluator-evaluator-lst self))
         (args (list list-ev (t4-evaluator-evaluator-tail self) env)))
    (proof-with-checked-results
     ((variable (t4-evaluator-evaluator-rule common 1))
      (quotation (t4-evaluator-evaluator-rule common 2))
      (abstraction (t4-evaluator-evaluator-rule common 3))
      (cons-rule (t4-evaluator-evaluator-rule common 5))
      (interpret (t4-evaluator-evaluator-interpret
                  (reverse (t4-evaluator-evaluator-operators self)) self *proof-false*))
      (abstraction-body (proof-term-at abstraction 2))
      (lambda-case (t4-evaluator-replace-terms
                    abstraction-body
                    (list (cons operator *t4-evaluator-operator*)
                          (cons args *t4-evaluator-values*))))
      (quote-body (proof-term-at quotation 2))
      (var-body (proof-term-at variable 2))
      (cons-body (proof-term-at cons-rule 2)))
     (let* ((dispatch
             (list (list *t4-evaluator-lambda*
                         (list *t4-evaluator-operator* *t4-evaluator-values*)
                         (proof-ite (list *proof-consp* *t4-evaluator-operator*)
                                    lambda-case interpret))
                   operator args))
            (body (proof-ite
                   (t4-evaluator-evaluator-consp self)
                   (proof-ite (proof-eq operator (proof-quote *proof-quote*))
                              quote-body dispatch)
                   (proof-ite (list *t4-evaluator-symbolp* obj)
                              var-body *proof-false*))))
       (list (list ev (list obj env) body)
             (list list-ev (list lst env)
                   (proof-ite (list *proof-consp* lst) cons-body *proof-false*)))))))

(defun t4-evaluator-step-right (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun t4-evaluator-evaluator-pick (self equation test)
  (let ((proof (t4-evaluator-evaluator-proof self)))
    (proof-with-checked-results
     ((term (t4-evaluator-step-right equation))
      (selected (proof-proof-select proof term test)))
     (proof-proof-chain proof equation (list selected)))))

(defun t4-evaluator-evaluator-type-of-pair (self pair)
  (proof-proof-fact (t4-evaluator-evaluator-proof self) "consp-cons"
                    (seq-zip (list *library-x* *library-y*) (cdr pair))))

(defun t4-evaluator-evaluator-list-case (self args env shape)
  (proof-with-checked-results
   ((unfolded (proof-proof-unfold
               (t4-evaluator-evaluator-proof self)
               (list (t4-evaluator-evaluator-list self) args env))))
   (t4-evaluator-evaluator-pick self unfolded shape)))

(defun t4-evaluator-evaluator-evaluation (self term env shape tag)
  (proof-with-checked-results
   ((unfolded (proof-proof-unfold
               (t4-evaluator-evaluator-proof self)
               (list (t4-evaluator-evaluator-ev self) term env)))
    (shaped (t4-evaluator-evaluator-pick self unfolded shape)))
   (t4-evaluator-evaluator-pick self shaped tag)))

(defun t4-evaluator-selection-step (lib step value selector)
  (proof-with-checked-results
   ((axiom (library-library-axiom
            lib (concatenate 'string (caddr selector) "-CONS") (cdr value))))
   (proof-proof-rewrite-first (library-library-proof lib) step axiom)))

(defun t4-evaluator-evaluator-selection (self proof value)
  (let ((lib (t4-evaluator-evaluator-lib self)))
    (proof-with-checked-results
     ((first (t4-evaluator-selection-step lib proof value *library-car*)))
     (t4-evaluator-selection-step lib first value *library-cdr*))))

(defun t4-evaluator-evaluator-selector-lemma (self selector)
  (let* ((lib (t4-evaluator-evaluator-lib self))
         (proof (library-library-proof lib))
         (x (t4-evaluator-evaluator-obj self))
         (env (t4-evaluator-evaluator-env self))
         (list-ev (t4-evaluator-evaluator-list self))
         (target (if (equal selector *library-car*)
                     (t4-evaluator-evaluator-ev self)
                   list-ev))
         (left (list selector (list list-ev x env)))
         (right (list target (list selector x) env))
         (pair (list *proof-consp* x)))
    (proof-with-checked-results
     ((present-test (proof-proof-assume proof pair t))
      (present (t4-evaluator-evaluator-list-case self x env present-test))
      (reflexive (proof-proof-reflexive proof left))
      (yes (proof-proof-rewrite proof reflexive present '(1 2 1)))
      (value (t4-evaluator-step-right present))
      (yes (t4-evaluator-evaluator-selection self yes value))
      (absent (proof-proof-assume proof pair nil))
      (empty (t4-evaluator-evaluator-list-case self x env absent))
      (reflexive (proof-proof-reflexive proof left))
      (no (proof-proof-rewrite proof reflexive empty '(1 2 1)))
      (computed (proof-proof-compute proof (list selector *proof-false*) *proof-nil*))
      (no (proof-proof-chain proof no (list computed)))
      (selector-name (proof-term-at selector 2))
      (completion (library-library-axiom
                   lib (concatenate 'string "COMPLETION-OF-" selector-name) (list x)))
      (atomic (t4-evaluator-evaluator-pick self completion absent))
      (reflexive (proof-proof-reflexive proof right))
      (reduced (proof-proof-rewrite proof reflexive atomic '(1 2 1)))
      (not-pair (t4-ordinals-ordinals-prove lib (proof-neg (list *proof-consp* *proof-false*))
                                            nil (list *proof-not*)))
      (lib (cdr not-pair))
      (self (t4-evaluator-evaluator-with-lib self lib))
      (proof (library-library-proof lib))
      (viewed
       (if (equal selector *library-car*)
           (proof-with-checked-results
            ((computed (proof-proof-compute
                        proof (list *t4-evaluator-symbolp* *proof-false*) *proof-t*))
             (symbol (proof-proof-true-from-eq proof computed))
             (viewed (t4-evaluator-evaluator-evaluation
                      self *proof-false* env (car not-pair) symbol))
             (not-nil (proof-proof-not-nil proof)))
            (t4-evaluator-evaluator-pick self viewed not-nil))
         (t4-evaluator-evaluator-list-case self *proof-false* env (car not-pair))))
      (rhs (proof-proof-chain proof reduced (list viewed)))
      (rhs (proof-proof-symmetric proof rhs))
      (no (proof-proof-chain proof no (list rhs)))
      (step (proof-proof-cases proof pair yes no))
      (name (concatenate 'string "EVAL-" (t4-evaluator-evaluator-suffix self)
                         "-" selector-name))
      (lib (library-library-lemma lib name (proof-eq left right) step nil)))
     (t4-evaluator-evaluator-with-properties
      (t4-evaluator-evaluator-with-lib self lib)
      (table-put (t4-evaluator-evaluator-properties self) selector
                   (proof-sym (concatenate 'string "SELF-" name) "ACL2"))))))

(mutual-recursion
 (defun t4-evaluator-evaluator-select-arguments-selectors (term list-ev)
   (declare (xargs :measure (acl2-count term)))
   (cond ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
          nil)
         ((endp term) '(:failure "malformed-candidate" ""))
         ((member-equal (car term) (list *library-car* *library-cdr*))
          (proof-with-checked-results ((arg (proof-term-at term 1)))
            (if (proof-is-call arg list-ev)
                term
              (t4-evaluator-evaluator-select-arguments-selector-args
               (cdr term) list-ev))))
         (t (t4-evaluator-evaluator-select-arguments-selector-args
             (cdr term) list-ev))))
 (defun t4-evaluator-evaluator-select-arguments-selector-args (args list-ev)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (or (t4-evaluator-evaluator-select-arguments-selectors (car args) list-ev)
         (t4-evaluator-evaluator-select-arguments-selector-args (cdr args) list-ev)))))

(defund t4-evaluator-evaluator-select-argument (self proof)
  (proof-with-checked-results
   ((term (t4-evaluator-step-right proof))
    (first (t4-evaluator-evaluator-select-arguments-selectors
            term (t4-evaluator-evaluator-list self))))
   (if (not first)
       (cons proof self)
     (proof-with-checked-results
      ((parts (proof-list-of-length first 2))
       (call (proof-list-of-length (cadr parts) 3))
       (selector (car parts))
       (self (if (assoc-equal selector (t4-evaluator-evaluator-properties self))
                 self
               (t4-evaluator-evaluator-selector-lemma self selector)))
       (pr (t4-evaluator-evaluator-proof self))
       (available (proof-proof-fact
                   pr (table-get (t4-evaluator-evaluator-properties self) selector nil)
                   (list (list (t4-evaluator-evaluator-obj self) (cadr call))
                         (list (t4-evaluator-evaluator-env self) (caddr call)))))
       (proof (proof-proof-rewrite-first pr proof available)))
      (list* :continue proof self)))))

(defun t4-evaluator-evaluator-select-arguments-loop (n self proof)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t4-evaluator-evaluator-select-arguments-loop")
    (let ((result (t4-evaluator-evaluator-select-argument self proof)))
      (if (eq (car result) :continue)
          (t4-evaluator-evaluator-select-arguments-loop (1- n) (cddr result) (cadr result))
        result))))

(defun t4-evaluator-evaluator-select-arguments (self proof)
  (t4-evaluator-evaluator-select-arguments-loop 1000000 self proof))

(defun t4-evaluator-evaluator-evaluates-quote (self value)
  (let* ((lib (t4-evaluator-evaluator-lib self))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((kwote (proof-proof-unfold proof (list *t4-evaluator-kwote* value)))
      (expansion (t4-evaluator-step-right kwote))
      (opened (proof-proof-unfold proof expansion))
      (kwote (proof-proof-chain proof kwote (list opened)))
      (term (t4-evaluator-step-right kwote))
      (first (library-library-axiom lib "CAR-CONS" (cdr term)))
      (tag (proof-eq (list *library-car* term) (proof-quote *proof-quote*)))
      (identity (proof-proof-reflexive proof (proof-quote *proof-quote*)))
      (swapped (proof-proof-symmetric proof first))
      (tagged (proof-proof-rewrite proof identity swapped '(1 1)))
      (literal (proof-step-first tagged)))
     (if (not (equal literal tag))
         '(:failure "inference-mismatch" "")
       (proof-with-checked-results
        ((shape (t4-evaluator-evaluator-type-of-pair self term))
         (value-eq (t4-evaluator-evaluator-evaluation self term *proof-false* shape tagged))
         (value-eq (t4-evaluator-evaluator-selection self value-eq term))
         (tail (proof-term-at term 2))
         (value-eq (t4-evaluator-evaluator-selection self value-eq tail))
         (unquoted (proof-proof-symmetric proof kwote))
         (quoted (proof-proof-rewrite proof value-eq unquoted '(1 1 1)))
         (result (t4-evaluator-step-right quoted)))
        (if (equal result value) quoted '(:failure "inference-mismatch" "")))))))

(defun t4-evaluator-evaluator-quoted-arguments-branch
    (positive self x env lhs pair hypothesis decrease)
  (let* ((lib (t4-evaluator-evaluator-lib self))
         (proof (library-library-proof lib))
         (definitions (list *t4-evaluator-endp* *t4-evaluator-atom* *proof-not*)))
    (proof-with-checked-results
     ((test (proof-proof-assume proof pair positive))
      (values (t4-evaluator-evaluator-list-case self x env test))
      (value (t4-evaluator-step-right values))
      (nonempty
       (if positive
           (proof-with-checked-results
            ((shape (t4-evaluator-evaluator-type-of-pair self value)))
            (t4-ordinals-ordinals-prove lib (proof-neg (list *t4-evaluator-endp* value))
                                        (list shape) definitions))
         (t4-ordinals-ordinals-prove lib (list *t4-evaluator-endp* *proof-false*)
                                     nil definitions)))
      (lib (cdr nonempty))
      (self (t4-evaluator-evaluator-with-lib self lib))
      (proof (library-library-proof lib))
      (opening (proof-proof-unfold proof (list *t4-evaluator-kwote-list* value)))
      (quote-list (t4-evaluator-evaluator-pick self opening (car nonempty)))
      (quote-list (if positive
                      (t4-evaluator-evaluator-selection self quote-list value)
                    quote-list))
      (quoted (t4-evaluator-step-right quote-list))
      (shape (if positive
                 (proof-with-checked-results
                  ((known (t4-evaluator-evaluator-type-of-pair self quoted)))
                  (cons known lib))
               (t4-ordinals-ordinals-prove lib
                                           (proof-neg (list *proof-consp* *proof-false*))
                                           nil (list *proof-not*))))
      (self (t4-evaluator-evaluator-with-lib self (cdr shape)))
      (proof (t4-evaluator-evaluator-proof self))
      (evaluated (t4-evaluator-evaluator-list-case self quoted *proof-false* (car shape)))
      (evaluated
       (if positive
           (proof-with-checked-results
            ((selected (t4-evaluator-evaluator-selection self evaluated quoted))
             (head (proof-term-at value 1))
             (evaluated-head (t4-evaluator-evaluator-evaluates-quote self head))
             (selected (proof-proof-rewrite-first proof selected evaluated-head))
             (assuming (proof-proof-assume proof hypothesis t))
             (smaller (proof-proof-prove-if proof assuming decrease)))
            (proof-proof-rewrite-first proof selected smaller))
         evaluated))
      (identity (proof-proof-reflexive proof lhs))
      (equality (proof-proof-rewrite proof identity values '(1 2 1 1)))
      (equality (proof-proof-rewrite proof equality quote-list '(1 2 1)))
      (original (proof-proof-symmetric proof values))
      (step (proof-proof-chain proof equality (list evaluated original))))
     (cons step self))))

(defun t4-evaluator-evaluator-quoted-arguments (self)
  (let* ((lib (t4-evaluator-evaluator-lib self))
         (x (t4-evaluator-evaluator-obj self))
         (env (t4-evaluator-evaluator-env self))
         (list-ev (t4-evaluator-evaluator-list self))
         (args (list list-ev x env))
         (lhs (list list-ev (list *t4-evaluator-kwote-list* args) *proof-false*))
         (claim (proof-eq lhs args))
         (pair (list *proof-consp* x))
         (mapping (list (list x (list *library-cdr* x)))))
    (proof-with-checked-results
     ((decrease (library-library-builtin lib 3 x))
      (smaller (proof-step-first decrease))
      (tail (list list-ev (list *library-cdr* x) env))
      (inductive (list list-ev (list *t4-evaluator-kwote-list* tail) *proof-false*))
      (hypothesis (proof-ite smaller (proof-eq inductive tail) *proof-true*))
      (ordinal (library-library-builtin lib 1 x))
      (yes (t4-evaluator-evaluator-quoted-arguments-branch
            t self x env lhs pair hypothesis decrease))
      (no (t4-evaluator-evaluator-quoted-arguments-branch
           nil (cdr yes) x env lhs pair hypothesis decrease))
      (self (cdr no))
      (lib (t4-evaluator-evaluator-lib self))
      (proof (library-library-proof lib))
      (case (proof-proof-cases proof pair (car yes) (car no)))
      (step (proof-proof-induct proof ordinal case claim
                                (t4-structural-count x) (list mapping)))
      (name (concatenate 'string "EVAL-" (t4-evaluator-evaluator-suffix self)
                         "-QUOTED-ARGUMENTS"))
      (lib (library-library-lemma lib name claim step nil)))
     (cons (proof-sym (concatenate 'string "SELF-" name) "ACL2")
           (t4-evaluator-evaluator-with-lib self lib)))))

(defun t4-evaluator-evaluator-different-tag (self test known)
  (let ((proof (t4-evaluator-evaluator-proof self)))
    (proof-with-checked-results ((literal (proof-step-first known)))
      (if (proof-is-call literal *proof-equal*)
          (proof-with-checked-results
           ((reflexive (proof-proof-reflexive proof test))
            (changed (proof-proof-rewrite proof reflexive known '(1 2 1)))
            (rhs (t4-evaluator-step-right changed))
            (computed (proof-proof-compute proof rhs *proof-nil*))
            (denied (proof-proof-chain proof changed (list computed)))
            (not-nil (proof-proof-not-nil proof))
            (swapped (proof-proof-symmetric proof denied)))
           (proof-proof-rewrite proof not-nil swapped '(1 1)))
        (proof-with-checked-results
         ((assumed (proof-proof-assume proof test t))
          (changed (proof-proof-rewrite-first proof known assumed))
          (literal (proof-step-first changed))
          (contradiction
           (if (proof-is-call literal *proof-consp*)
               (proof-with-checked-results
                ((computed (proof-proof-compute proof literal *proof-nil*))
                 (rewritten (proof-proof-rewrite proof changed computed '(1))))
                (proof-proof-tidy proof rewritten))
             (proof-with-checked-results
              ((argument (proof-term-at literal 1))
               (computed (proof-proof-compute proof argument *proof-t*))
               (negative (proof-proof-rewrite proof changed computed '(1 1)))
               (truth (proof-proof-prove proof *proof-true* nil nil)))
              (proof-proof-cut proof truth negative)))))
         (proof-proof-front proof contradiction (proof-neg test)))))))

(defun t4-evaluator-evaluator-disjoint-symbol (self term symbol)
  (let* ((proof (t4-evaluator-evaluator-proof self))
         (pair (list *proof-consp* term)))
    (proof-with-checked-results
     ((fact (proof-proof-fact proof "consp-not-symbolp" (list (list *library-x* term))))
      (condition (proof-proof-assume proof pair t))
      (deny (proof-proof-modus-ponens proof fact condition))
      (disjoint (proof-proof-cut proof symbol deny)))
     (proof-proof-front proof disjoint (proof-neg pair)))))

(defun t4-evaluator-evaluator-dispatch-operators (operators self body tag)
  (if (endp operators)
      (cons body self)
    (proof-with-checked-results
     ((entry (proof-list-of-length (car operators) 2))
      (test (proof-eq (t4-evaluator-evaluator-operator self) (car entry)))
      (rhs (t4-evaluator-step-right body))
      (branch-test (proof-term-at rhs 1)))
     (cond
      ((not (equal branch-test test)) '(:failure "inference-mismatch" ""))
      ((not tag) '(:failure "failure" ""))
      (t (proof-with-checked-results
          ((literal (proof-step-first tag)))
          (if (equal literal test)
              (proof-with-checked-results
               ((selected (t4-evaluator-evaluator-pick self body tag)))
               (t4-evaluator-evaluator-select-arguments self selected))
            (proof-with-checked-results
             ((different (t4-evaluator-evaluator-different-tag self test tag))
              (next (t4-evaluator-evaluator-pick self body different)))
             (t4-evaluator-evaluator-dispatch-operators (cdr operators) self next tag)))))))))

(defun t4-evaluator-evaluator-dispatch (self selected shape tag)
  (let ((proof (t4-evaluator-evaluator-proof self)))
    (proof-with-checked-results
     ((application (t4-evaluator-step-right selected))
      (opened (proof-proof-beta proof application))
      (body (proof-proof-chain proof selected (list opened)))
      (body (t4-evaluator-evaluator-pick self body shape))
      (literal (proof-step-first shape)))
     (if (equal literal (list *proof-consp* (t4-evaluator-evaluator-operator self)))
         (cons body self)
       (t4-evaluator-evaluator-dispatch-operators
        (t4-evaluator-evaluator-operators self) self body tag)))))

(defun t4-evaluator-evaluator-rebuilt-term (self goal shape not-quoted)
  (let* ((lib (t4-evaluator-evaluator-lib self))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length goal 3))
      (left (cadr parts))
      (right (caddr parts))
      (rebuilt (proof-term-at right 1))
      (term (proof-term-at left 1))
      (env (proof-term-at left 2))
      (original (t4-evaluator-evaluator-evaluation self term env shape not-quoted))
      (head (library-library-axiom lib "CAR-CONS" (cdr rebuilt)))
      (head (proof-proof-symmetric proof head))
      (rewritten-tag (proof-proof-rewrite proof not-quoted head '(1 1 1)))
      (shape (t4-evaluator-evaluator-type-of-pair self rebuilt))
      (replayed (t4-evaluator-evaluator-evaluation self rebuilt *proof-false* shape rewritten-tag))
      (replayed (t4-evaluator-evaluator-selection self replayed rebuilt))
      (named (t4-evaluator-evaluator-quoted-arguments self))
      (self (cdr named))
      (proof (t4-evaluator-evaluator-proof self))
      (bindings (list (list (t4-evaluator-evaluator-obj self)
                            (t4-evaluator-evaluator-tail self))))
      (same-args (proof-proof-fact proof (car named) bindings))
      (replayed (proof-proof-rewrite-first proof replayed same-args))
      (replayed (proof-proof-symmetric proof replayed))
      (step (proof-proof-chain proof original (list replayed))))
     (cons step self))))

(defun t4-evaluator-evaluator-clauses-close (index evidence self)
  (let* ((lib (t4-evaluator-evaluator-lib self))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((rule (proof-term-at (t4-evaluator-evaluator-common self) index))
      (rule (proof-list-of-length rule 2))
      (guard (car rule))
      (step (t4-ordinals-ordinals-imply lib guard evidence))
      (literal (proof-step-first step)))
     (if (equal literal (cons *library-implies* rule))
         (proof-proof-subsume proof step (list literal))
       '(:failure "inference-mismatch" "")))))

(defun t4-evaluator-evaluator-clauses-assumptions (common proof)
  (if (endp common)
      nil
    (proof-with-checked-results
     ((rule (proof-list-of-length (car common) 2))
      (assumption (proof-proof-assume proof (car rule) t))
      (rest (t4-evaluator-evaluator-clauses-assumptions (cdr common) proof)))
     (cons assumption rest))))

(defun t4-evaluator-evaluator-clauses-operator (entry self quote-tag)
  (let* ((proof (t4-evaluator-evaluator-proof self))
         (obj (t4-evaluator-evaluator-obj self))
         (env (t4-evaluator-evaluator-env self))
         (operator (t4-evaluator-evaluator-operator self)))
    (proof-with-checked-results
     ((entry (proof-list-of-length entry 2))
      (tag (proof-eq operator (car entry)))
      (guard (proof-ite (t4-evaluator-evaluator-consp self) tag *proof-false*))
      (assumed (proof-proof-assume proof guard t))
      (parts (proof-proof-conjunct proof assumed))
      (shape (car parts))
      (tag-proof (cadr parts))
      (computed (proof-proof-compute
                 proof (list *t4-evaluator-symbolp* (car entry)) *proof-t*))
      (value (proof-proof-true-from-eq proof computed))
      (reversed (proof-proof-symmetric proof tag-proof))
      (symbol (proof-proof-rewrite proof value reversed '(1 1)))
      (no-pair (t4-evaluator-evaluator-disjoint-symbol self operator symbol))
      (different (t4-evaluator-evaluator-different-tag self quote-tag tag-proof))
      (opened (t4-evaluator-evaluator-evaluation self obj env shape different))
      (dispatched (t4-evaluator-evaluator-dispatch self opened no-pair tag-proof))
      (literal (proof-step-first (car dispatched))))
     (if (not (equal literal
                     (proof-eq (list (t4-evaluator-evaluator-ev self) obj env) (cadr entry))))
         '(:failure "inference-mismatch" "")
       (let* ((self (cdr dispatched))
              (lib (t4-evaluator-evaluator-lib self))
              (proof (library-library-proof lib)))
         (proof-with-checked-results
          ((result (t4-ordinals-ordinals-imply lib guard (car dispatched)))
           (literal (proof-step-first result))
           (result (proof-proof-subsume proof result (list literal))))
          (cons result self)))))))

(defun t4-evaluator-evaluator-clauses-operators (operators self quote-tag)
  (if (endp operators)
      (cons nil self)
    (proof-with-checked-results
     ((result (t4-evaluator-evaluator-clauses-operator (car operators) self quote-tag))
      (rest (t4-evaluator-evaluator-clauses-operators
             (cdr operators) (cdr result) quote-tag)))
     (cons (cons (car result) (car rest)) (cdr rest)))))

(defun t4-evaluator-evaluator-clauses (self)
  (let* ((proof (t4-evaluator-evaluator-proof self))
         (common (t4-evaluator-evaluator-common self))
         (obj (t4-evaluator-evaluator-obj self))
         (env (t4-evaluator-evaluator-env self))
         (lst (t4-evaluator-evaluator-lst self))
         (quote-tag (proof-eq (t4-evaluator-evaluator-operator self) (proof-quote *proof-quote*))))
    (proof-with-checked-results
     ((assumptions (t4-evaluator-evaluator-clauses-assumptions common proof))
      (assumption (proof-term-at assumptions 0))
      (parts (proof-proof-conjunct proof assumption))
      (shape (car parts))
      (conditions (proof-proof-conjunct proof (cadr parts)))
      (no-quote (cadr conditions))
      (rule (t4-evaluator-evaluator-rule common 0))
      (rebuilt (t4-evaluator-evaluator-rebuilt-term self rule shape no-quote))
      (self (cdr rebuilt))
      (proof (t4-evaluator-evaluator-proof self))
      (p0 (t4-evaluator-evaluator-clauses-close 0 (car rebuilt) self))
      (symbol (proof-term-at assumptions 1))
      (shape (t4-evaluator-evaluator-disjoint-symbol self obj symbol))
      (step (t4-evaluator-evaluator-evaluation self obj env shape symbol))
      (p1 (t4-evaluator-evaluator-clauses-close 1 step self))
      (assumption (proof-term-at assumptions 2))
      (parts (proof-proof-conjunct proof assumption))
      (step (t4-evaluator-evaluator-evaluation self obj env (car parts) (cadr parts)))
      (p2 (t4-evaluator-evaluator-clauses-close 2 step self))
      (assumption (proof-term-at assumptions 3))
      (parts (proof-proof-conjunct proof assumption))
      (pair (cadr parts))
      (different (t4-evaluator-evaluator-different-tag self quote-tag pair))
      (lambda-case (t4-evaluator-evaluator-evaluation self obj env (car parts) different))
      (dispatched (t4-evaluator-evaluator-dispatch self lambda-case pair nil))
      (self (cdr dispatched))
      (p3 (t4-evaluator-evaluator-clauses-close 3 (car dispatched) self))
      (assumption (proof-term-at assumptions 4))
      (step (t4-evaluator-evaluator-list-case self lst env assumption))
      (p4 (t4-evaluator-evaluator-clauses-close 4 step self))
      (assumption (proof-term-at assumptions 5))
      (step (t4-evaluator-evaluator-list-case self lst env assumption))
      (p5 (t4-evaluator-evaluator-clauses-close 5 step self))
      (assumption (proof-term-at assumptions 6))
      (proof (t4-evaluator-evaluator-proof self))
      (parts (proof-proof-conjunct proof assumption))
      (step (t4-evaluator-evaluator-evaluation self obj env (car parts) (cadr parts)))
      (p6 (t4-evaluator-evaluator-clauses-close 6 step self))
      (assumption (proof-term-at assumptions 7))
      (parts (proof-proof-conjunct proof assumption))
      (shape (car parts))
      (nonoperator (proof-proof-conjunct proof (cadr parts)))
      (no-pair (car nonoperator))
      (no-symbol (cadr nonoperator))
      (different (t4-evaluator-evaluator-different-tag self quote-tag no-symbol))
      (nothing (t4-evaluator-evaluator-evaluation self obj env shape different))
      (dispatched (t4-evaluator-evaluator-dispatch self nothing no-pair no-symbol))
      (self (cdr dispatched))
      (p7 (t4-evaluator-evaluator-clauses-close 7 (car dispatched) self))
      (rest (t4-evaluator-evaluator-clauses-operators
             (t4-evaluator-evaluator-operators self) self quote-tag)))
     (cons (append (list p0 p1 p2 p3 p4 p5 p6 p7) (car rest))
           (cdr rest)))))

(defun t4-evaluator-request-p (value)
  (and (consp value)
       (eq (car value) :call)
       (or (eq (cadr value) :generate) (eq (cadr value) :used-prelude))))

(defun t4-evaluator-witness-arities-p (functions)
  (if (endp functions)
      t
    (proof-with-checked-results ((function (proof-list-of-length (car functions) 2)))
      (and (equal (cadr function) 2)
           (t4-evaluator-witness-arities-p (cdr functions))))))

(defun t4-evaluator-witness-goals (formulas mapping)
  (if (endp formulas)
      nil
    (proof-with-checked-results
     ((entry (proof-list-of-length (car formulas) 2))
      (goal (t4-bookwitness-replace-functions (cadr entry) mapping))
      (rest (t4-evaluator-witness-goals (cdr formulas) mapping)))
     (cons goal rest))))

(defun t4-evaluator-witness-rules (goals)
  (cond
   ((endp goals) (list t))
   ((not (proof-is-call (car goals) *library-implies*)) nil)
   (t (proof-with-checked-results ((goal (proof-term-at (car goals) 2)))
        (if (not (proof-is-call goal *proof-equal*))
            nil
          (proof-with-checked-results ((rest (t4-evaluator-witness-rules (cdr goals))))
            (and rest (cons t (cons (cdar goals) (cdr rest))))))))))

(defun t4-evaluator-witness-atomic-args-p (args)
  (or (endp args)
      (and (not (proof-compound (car args)))
           (t4-evaluator-witness-atomic-args-p (cdr args)))))

(defun t4-evaluator-witness-operator-tag (condition obj call)
  (and (proof-is-call condition *proof-if*)
    (proof-with-checked-results ((shape (proof-term-at condition 1)))
      (and (equal shape (list *proof-consp* obj))
        (proof-with-checked-results ((no (proof-term-at condition 3)))
          (and (equal no *proof-false*)
            (proof-with-checked-results ((tag (proof-term-at condition 2)))
              (and (proof-is-call tag *proof-equal*)
                (proof-with-checked-results ((left (proof-term-at tag 1)))
                  (and (equal left call)
                    (proof-with-checked-results ((right (proof-term-at tag 2)))
                      (and (proof-is-call right *proof-quote*) right))))))))))))

(defun t4-evaluator-witness-operators (rules obj call original)
  (if (endp rules)
      (list t)
    (proof-with-checked-results
     ((rule (proof-list-of-length (car rules) 2))
      (tag (t4-evaluator-witness-operator-tag (car rule) obj call)))
     (and tag
       (proof-with-checked-results ((left (proof-term-at (cadr rule) 1)))
         (and (equal left original)
           (proof-with-checked-results
            ((expression (proof-term-at (cadr rule) 2))
             (rest (t4-evaluator-witness-operators (cdr rules) obj call original)))
            (and rest (cons t (cons (list tag expression) (cdr rest)))))))))))

(defun t4-evaluator-witness-operator-keys (operators)
  (if (endp operators)
      nil
    (cons (caar operators) (t4-evaluator-witness-operator-keys (cdr operators)))))

(defun t4-evaluator-evaluator-add-definitions (definitions self)
  (if (endp definitions)
      self
    (let* ((definition (car definitions))
           (lib (t4-evaluator-evaluator-lib self))
           (proof (proof-proof-add-definition
                   (library-library-proof lib) (car definition)
                   (cadr definition) (caddr definition))))
      (t4-evaluator-evaluator-add-definitions
       (cdr definitions)
       (t4-evaluator-evaluator-with-lib self (library-library-with-proof lib proof))))))

(defun t4-evaluator-witness-firsts (steps)
  (if (endp steps)
      nil
    (proof-with-checked-results
     ((first (proof-step-first (car steps)))
      (rest (t4-evaluator-witness-firsts (cdr steps))))
     (cons first rest))))

(defun t4-evaluator-witness-finish (definition-data generated prelude)
  (proof-with-checked-results ((prelude (proof-list-of-length prelude 2)))
    (let* ((termination (cadr generated))
           (measure (text-find termination "(measure ")))
      (if (< measure 0)
          '(:failure "search-miss" "")
        (proof-with-checked-results ((local (proof-line "define" definition-data)))
          (list (+ (car generated) (car prelude))
                (concatenate 'string (seq-slice termination 0 measure) local
                             (seq-slice termination measure :none) (cadr prelude))))))))

(defun t4-evaluator-witness-prove (api generated definition-data self name available goals)
  (proof-with-checked-results
   ((generated (proof-list-of-length generated 2))
    (self (t4-evaluator-evaluator-add-definitions (cdr definition-data) self))
    (result (t4-evaluator-evaluator-clauses self))
    (proofs (car result))
    (firsts (t4-evaluator-witness-firsts proofs)))
   (if (not (equal firsts goals))
       '(:failure "inference-mismatch" "")
     (proof-with-checked-results
      ((target (proof-proof-entry "witness" name (cons name available) proofs)))
      (if (eq (car api) :replies)
          (proof-with-checked-results ((prelude (caddr api)))
            (t4-evaluator-witness-finish definition-data generated prelude))
        (list :call :used-prelude
              (library-library-entries (t4-evaluator-evaluator-lib (cdr result)))
              target))))))

(defun t4-evaluator-witness-attempt (api prefix name available goals rules operators suffix)
  (proof-with-checked-results
   ((self (t4-evaluator-evaluator-init prefix available (take 8 rules) operators suffix))
    (definitions (t4-evaluator-evaluator-definitions self))
    (definition-data (cons *termination-all* definitions)))
   (if (not api)
       (list :call :generate prefix "define" definition-data nil nil)
     (proof-with-checked-results
      ((generated (if (eq (car api) :replies) (cadr api) api)))
      (t4-evaluator-witness-prove api generated definition-data self name available goals)))))

(defun t4-evaluator-witness-validated (api prefix name available goals rules suffix)
  (proof-with-checked-results
   ((equation (proof-term-at (car rules) 1))
    (original (proof-term-at equation 1)))
   (and (and (proof-is-call original (car available))
              (t4-evaluator-witness-atomic-args-p (cdr original)))
     (proof-with-checked-results
      ((obj (proof-term-at original 1))
       (operators (t4-evaluator-witness-operators
                   (nthcdr 8 rules) obj (list *library-car* obj) original)))
      (and operators
        (let ((keys (t4-evaluator-witness-operator-keys (cdr operators))))
          (and (and (equal (len (proof-unique keys)) (len (cdr operators)))
                     (not (member-equal (proof-quote *proof-quote*) keys)))
            (let ((result (t4-evaluator-witness-attempt
                           api prefix name available goals rules (cdr operators) suffix)))
              (if (and (failure-p result)
                       (member-equal (cadr result)
                                     '("unproved" "search-miss" "inference-mismatch"
                                       "missing-proof-input" "malformed-candidate" "value" "assertion"
                                       "key" "type" "index" "recursion")))
                  nil
                result)))))))))

(defun t4-evaluator-evaluator-witness (api prefix name data suffix)
  (proof-with-checked-results ((parts (proof-list-of-length data 2)))
    (let ((functions (car parts)) (formulas (cadr parts)))
      (and (equal (len functions) 2)
        (proof-with-checked-results ((binary (t4-evaluator-witness-arities-p functions)))
          (and (and binary (<= 8 (len formulas)))
            (let* ((base (concatenate 'string "T4-EVAL-" suffix "-"))
                   (available (list (proof-sym (concatenate 'string base "0") "ACL2")
                                    (proof-sym (concatenate 'string base "1") "ACL2")))
                   (mapping (table-put
                             (list (cons (caar functions) (car available)))
                             (caadr functions) (cadr available))))
              (proof-with-checked-results
               ((goals (t4-evaluator-witness-goals formulas mapping))
                (rules (t4-evaluator-witness-rules goals)))
               (and rules
                 (t4-evaluator-witness-validated
                  api prefix name available goals (cdr rules) suffix))))))))))
