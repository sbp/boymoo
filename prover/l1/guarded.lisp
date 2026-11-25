(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-guarded-tame* (proof-sym "TAMEP" "ACL2"))
(defconst *l1-guarded-tame-function* (proof-sym "TAMEP-FUNCTIONP" "ACL2"))
(defconst *l1-guarded-suitably-tame* (proof-sym "SUITABLY-TAMEP-LISTP" "ACL2"))
(defconst *l1-guarded-badge* (proof-sym "BADGE" "ACL2"))
(defconst *l1-guarded-function-flag* (proof-sym "FN" "KEYWORD"))
(defconst *l1-guarded-syntax* (proof-sym "L1-SYNTAX-ARGUMENTS" "ACL2"))
(defconst *l1-guarded-value* (proof-sym "L1-CONSTANT-VALUE" "ACL2"))
(defconst *l1-guarded-symbolp* (proof-cl "SYMBOLP"))
(defconst *l1-guarded-control*
  (list (proof-sym "ZP" "ACL2") *proof-not* (proof-cl "ATOM") (proof-cl "ENDP")
        (proof-cl "EQ") (proof-cl "EQL") (proof-cl "NULL")))
(defconst *l1-guarded-apply-user* (proof-sym "APPLY$-USERFN" "ACL2"))
(defconst *l1-guarded-untame-apply* (proof-sym "UNTAME-APPLY$" "ACL2"))
(defconst *l1-guarded-untame-eval* (proof-sym "UNTAME-EV$" "ACL2"))
(defconst *l1-guarded-padded-failure* (proof-sym "L1-PADDED-WARRANT-FAILURE" "ACL2"))
(defconst *l1-guarded-take-failure* (proof-sym "L1-TAKE-WARRANT-FAILURE" "ACL2"))
(defconst *l1-guarded-arity-name* (proof-sym "L1-USER-APPLICATION-ARITY" "ACL2"))
(defconst *l1-guarded-take-name* (proof-sym "L1-TAKE-PADDED-ARGUMENTS" "ACL2"))

(defun l1-guarded-term-path (term path)
  (declare (xargs :measure (acl2-count path)))
  (if (endp path)
      term
    (proof-with-checked-results ((value (proof-term-at term (car path))))
      (l1-guarded-term-path value (cdr path)))))

(defun l1-guarded-step-first (step)
  (if step
      (proof-step-first step)
    '(:failure "failure" "")))

(defun l1-guarded-step-term (step index)
  (proof-with-checked-results ((first (l1-guarded-step-first step)))
    (proof-term-at first index)))

(defun l1-guarded-step-clause (step)
  (if step
      (proof-step-clause step)
    '(:failure "failure" "")))

(defun l1-guarded-assertion (condition)
  (if condition nil '(:failure "failure" "")))

(defun l1-guarded-rewrite-reduced (proof reduction step)
  (proof-with-checked-results
      ((term (l1-guarded-step-first step))
       (equality (l1-application-application-reduce reduction term))
       (first (l1-guarded-step-first equality))
       (rewritten (proof-proof-rewrite proof step equality '(1))))
    (proof-proof-tidy proof rewritten)))

(defun l1-guarded-tame-arguments (proof reduction function badge)
  (let ((subject (list *l1-guarded-tame*
                       (list *proof-cons* (proof-quote function) *l1-guarded-syntax*))))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof subject))
         (value (l1-guarded-step-term opened 2))
         (reduced (l1-application-application-reduce reduction value))
         (equation (proof-proof-chain proof opened (list reduced)))
         (right (l1-guarded-step-term equation 2))
         (arity (proof-term-at badge 1))
         (checked (l1-guarded-assertion
                   (equal right (list *l1-guarded-suitably-tame* (proof-quote arity)
                                      (proof-quote (nthcdr 3 badge)) *l1-guarded-syntax*))))
         (assumed (proof-proof-assume proof subject t))
         (rewritten (proof-proof-rewrite proof assumed equation '(1)))
         (step (proof-proof-tidy proof rewritten)))
      (list step subject))))

(defund l1-guarded-split-arguments (proof reduction argument-list)
  (proof-with-checked-results
      ((term (l1-guarded-step-first argument-list))
       (opened (proof-proof-unfold proof term))
       (outer (proof-proof-rewrite proof argument-list opened '(1)))
       (test (l1-guarded-step-term outer 1))
       (zero (l1-application-application-reduce reduction test))
       (zero-value (l1-guarded-step-term zero 2))
       (checked (l1-guarded-assertion (equal zero-value *proof-false*)))
       (not-nil (proof-proof-not-nil proof))
       (reversed (proof-proof-symmetric proof zero))
       (nonzero (proof-proof-rewrite proof not-nil reversed '(1 1)))
       (positive-length (proof-proof-prove-if proof outer nonzero))
       (conditional (l1-guarded-step-first positive-length))
       (empty-test (proof-term-at conditional 1))
       (empty-branch (proof-proof-if-true proof conditional))
       (empty-case (proof-proof-rewrite proof positive-length empty-branch '(1)))
       (empty-case (proof-proof-tidy proof empty-case))
       (nonempty (proof-proof-front proof empty-case (proof-neg empty-test)))
       (both (proof-proof-prove-if proof positive-length nonempty))
       (checks (proof-proof-conjunct proof both))
       (tail (l1-guarded-rewrite-reduced proof reduction (cadr checks))))
    (list (car checks) tail)))

(defun l1-guarded-quoted-function (argument)
  (let ((payload (list *library-cdr* argument)))
    (proof-ite
     (list *proof-consp* argument)
     (proof-ite
      (list (proof-cl "EQ") (list *library-car* argument) (proof-quote *proof-quote*))
      (proof-ite
       (list *proof-consp* payload)
       (proof-ite (list (proof-cl "NULL") (list *library-cdr* payload))
                  (list *l1-guarded-tame-function* (list *library-car* payload))
                  *proof-false*)
       *proof-false*)
      *proof-false*)
     *proof-false*)))

(defun l1-guarded-function-positions (flags index)
  (if (endp flags)
      nil
    (let* ((function-p (equal (car flags) *l1-guarded-function-flag*))
           (rest (l1-guarded-function-positions (cdr flags) (1+ index))))
      (if function-p
          (cons index rest)
        rest))))

(defund l1-guarded-quoted-argument
    (proof reduction head argument tame badge-equation position)
  (proof-with-checked-results
      ((head (l1-guarded-rewrite-reduced proof reduction head))
       (shape (l1-guarded-quoted-function argument))
       (expected (l1-application-application-reduce reduction shape))
       (head (if expected (proof-proof-transport proof head expected) head)))
    (let ((clause (list shape (proof-neg tame) (proof-neg badge-equation)))
          (name (proof-sym (concatenate 'string "L1-QUOTED-FUNCTION-ARGUMENT-"
                                       (decimal-text (1+ position)))
                           "ACL2")))
      (proof-with-checked-results ((step (proof-proof-subsume proof head clause)))
        (proof-proof-entry "lemma" name (cons name clause) (list step))))))

(defund l1-guarded-quoted-position
    (proof reduction tail tame badge-equation position positions count sources)
  (proof-with-checked-results
      ((arguments (l1-guarded-step-term tail 3))
       (parts (l1-guarded-split-arguments proof reduction tail)))
    (if (not (equal position (car positions)))
        (list (cadr parts) positions count sources)
      (proof-with-checked-results
          ((entry (l1-guarded-quoted-argument proof reduction (car parts)
                                             (list *library-car* arguments)
                                             tame badge-equation position)))
        (list (cadr parts) (cdr positions) (+ count (car (caddr entry)))
              (cons (cadddr entry) sources))))))

(defun l1-guarded-quoted-positions
    (remaining proof reduction tail tame badge-equation position positions count sources)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (list count (text-join "" (reverse sources)))
    (proof-with-checked-results
        ((next (l1-guarded-quoted-position proof reduction tail tame badge-equation
                                          position positions count sources)))
      (l1-guarded-quoted-positions (1- remaining) proof reduction (car next)
                                  tame badge-equation (1+ position)
                                  (cadr next) (caddr next) (cadddr next)))))

(defun l1-guarded-quoted-arguments (proof badge-test)
  (proof-with-checked-results
      ((function (l1-guarded-term-path badge-test '(1 1 1)))
       (right (proof-term-at badge-test 2))
       (badge (proof-term-at right 1)))
    (let* ((positions (l1-guarded-function-positions (nthcdr 3 badge) 0))
           (reduction (l1-application-application-init
                       proof function (list (cons function badge)) nil *l1-guarded-control*)))
      (proof-with-checked-results
          ((parts (l1-guarded-tame-arguments proof reduction function badge)))
        (let ((badge-equation (proof-eq (list *l1-guarded-badge* (proof-quote function)) right)))
          (if (endp positions)
              '(:failure "failure" "")
            (l1-guarded-quoted-positions (1+ (car (last positions))) proof reduction
                                        (car parts) (cadr parts)
                                        badge-equation 0 positions 0 nil)))))))

(defund l1-guarded-lemma-entry (name step)
  (proof-proof-entry "lemma" name (cons name (proof-step-clause step)) (list step)))

(defun l1-guarded-lemma-entries (lemmas count sources)
  (declare (xargs :measure (acl2-count lemmas)))
  (if (endp lemmas)
      (list count (text-join "" (reverse sources)))
    (let ((name (caar lemmas))
          (step (cadar lemmas)))
      (proof-with-checked-results ((entry (l1-guarded-lemma-entry name step)))
        (l1-guarded-lemma-entries (cdr lemmas) (+ count (car (caddr entry)))
                                 (cons (cadddr entry) sources))))))

(defun l1-guarded-put-fact (proof name step)
  (proof-proof-with-facts
   proof (table-put (proof-proof-facts proof) name (proof-step-clause step))))

(defund l1-guarded-padding-projection (proof actuals index restored once)
  (proof-with-checked-results
      ((equality (l1-application-select-component proof actuals index))
       (projection (l1-guarded-step-term equality 1))
       (right (l1-guarded-step-term restored 2))
       (restored (proof-proof-rewrite-result proof restored equality
                                             (proof-eq *proof-nil* right) projection))
       (right (l1-guarded-step-term once 2))
       (once (proof-proof-rewrite-result proof once equality
                                         (proof-eq *proof-nil* right) projection)))
    (list restored once)))

(defun l1-guarded-padding-projections (remaining index proof actuals restored once)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (list restored once)
    (proof-with-checked-results
        ((steps (l1-guarded-padding-projection proof actuals index restored once)))
      (l1-guarded-padding-projections (1- remaining) (1+ index) proof actuals
                                      (car steps) (cadr steps)))))

(defun l1-guarded-unpad-opened (proof restored)
  (proof-with-checked-results
      ((fact (proof-proof-fact proof *l1-guarded-arity-name* nil))
       (unpad (proof-proof-symmetric proof fact))
       (right (l1-guarded-step-term restored 2))
       (left (l1-guarded-step-term unpad 1)))
    (proof-proof-rewrite-result proof restored unpad (proof-eq *proof-nil* right) left)))

(defun l1-guarded-padding-failure
    (proof test badge-equation failure padded restored arity-equation)
  (proof-with-checked-results
      ((right (l1-guarded-step-term restored 2))
       (inner-test (l1-guarded-term-path right '(1 2)))
       (padded-mismatch (proof-proof-if-false proof inner-test))
       (closed (proof-proof-rewrite proof restored padded-mismatch '(1 2 1 2)))
       (original-mismatch (proof-proof-if-false proof test))
       (original-mismatch (proof-proof-symmetric proof original-mismatch))
       (closed (proof-proof-rewrite proof closed original-mismatch '(1 2 1 2)))
       (mismatch (proof-proof-symmetric proof closed))
       (mismatch (proof-proof-tidy proof mismatch))
       (proof (l1-guarded-put-fact proof *l1-guarded-arity-name* arity-equation)))
    (let ((opened (l1-guarded-unpad-opened proof restored))
          (claim (proof-eq failure padded)))
      (proof-with-checked-results
          ((proof (l1-witness-remove-facts proof (list *l1-guarded-arity-name*)))
           (opened opened)
           (match (proof-proof-symmetric proof opened))
           (match (proof-proof-subsume proof match (list claim (proof-neg badge-equation))))
           (cases (proof-proof-cases proof badge-equation match mismatch))
           (same-failure (proof-proof-subsume proof cases (list claim))))
        (cons same-failure proof)))))

(defun l1-guarded-padding-normalization-step (proof padded actuals failure arguments taken)
  (proof-with-checked-results
      ((padded-fact (proof-proof-fact proof *l1-guarded-padded-failure* nil))
       (take-fact (proof-proof-fact proof *l1-guarded-take-name* nil))
       (unpad (proof-proof-symmetric proof take-fact))
       (normalization (proof-proof-rewrite-result proof padded-fact unpad
                                                    (proof-eq *proof-nil* padded) actuals))
       (expected (proof-subst failure (list (cons arguments taken)))))
    (proof-proof-subsume proof normalization (list (proof-eq failure expected)))))

(defun l1-guarded-padding-normalization
    (proof same-failure take-equation padded actuals failure arguments taken)
  (let* ((proof (l1-guarded-put-fact proof *l1-guarded-take-name* take-equation))
         (proof (l1-guarded-put-fact proof *l1-guarded-padded-failure* same-failure))
         (step (l1-guarded-padding-normalization-step proof padded actuals failure arguments taken)))
    (proof-with-checked-results
        ((proof (l1-witness-remove-facts
                 proof (list *l1-guarded-take-name* *l1-guarded-padded-failure*)))
         (step step))
      (cons step proof))))

(defun l1-guarded-argument-arity-with-proof (proof test arguments failure)
  (proof-with-checked-results
      ((badge-equation (proof-term-at test 1))
       (matching (proof-proof-assume proof badge-equation t))
       (badge (proof-term-at badge-equation 2))
       (size (l1-guarded-term-path badge '(1 1)))
       (found (proof-proof-nil-or-true proof badge))
       (first (l1-guarded-step-first found))
       (computed (proof-proof-compute proof first *proof-nil*))
       (nonnil (proof-proof-rewrite proof found computed '(1)))
       (nonnil (proof-proof-tidy proof nonnil))
       (reversed (proof-proof-symmetric proof matching))
       (present (proof-proof-rewrite proof nonnil reversed '(1)))
       (present (proof-proof-tidy proof present))
       (function (l1-guarded-term-path badge-equation '(1 1)))
       (arity (proof-proof-fact proof (proof-sym "APPLY$-USERFN-TAKES-ARITY-ARGS" "ACL2")
                                (list (list (proof-sym "FN" "ACL2") function)
                                      (list (proof-sym "ARGS" "ACL2") arguments))))
       (restricted (proof-proof-modus-ponens proof arity present))
       (restricted (proof-proof-rewrite-first proof restricted matching))
       (designator (proof-term-at function 1)))
    (let* ((take (proof-sym "TAKE" "ACL2"))
           (true-list (proof-sym "TRUE-LISTP" "ACL2"))
           (reduction (l1-application-application-init
                       proof designator nil (list take *library-len* true-list) *l1-guarded-control*))
           (actuals (l1-primitive-cons-list (l1-application-select-args arguments size) *proof-false*)))
      (proof-with-checked-results
          ((result (l1-guarded-rewrite-reduced proof reduction restricted))
           (clause (list (proof-eq (list *l1-guarded-apply-user* function arguments)
                                   (list *l1-guarded-apply-user* function actuals))
                         (proof-neg badge-equation)))
           (arity-equation (proof-proof-subsume proof result clause))
           (length-term (list *library-len* actuals))
           (size-equation (l1-application-application-reduce reduction length-term))
           (clause (l1-guarded-step-clause size-equation))
           (checked (l1-guarded-assertion
                     (equal clause (list (proof-eq length-term (proof-quote size))))))
           (proper (l1-application-application-reduce reduction (list true-list actuals)))
           (first (l1-guarded-step-first proper))
           (proper (proof-proof-true-from-eq proof proper))
           (taken (list take (proof-quote size) arguments))
           (take-equation (l1-application-application-reduce reduction taken))
           (clause (l1-guarded-step-clause take-equation))
           (checked (l1-guarded-assertion (equal clause (list (proof-eq taken actuals)))))
           (padded (proof-subst failure (list (cons arguments actuals))))
           (restored (proof-proof-reflexive proof padded))
           (repeated (l1-primitive-cons-list (l1-application-select-args actuals size) *proof-false*))
           (once (proof-proof-reflexive proof repeated))
           (projections (l1-guarded-padding-projections size 0 proof actuals restored once))
           (once (cadr projections))
           (checked (l1-guarded-assertion
                     (equal (proof-step-clause once) (list (proof-eq repeated actuals)))))
           (same-failure (l1-guarded-padding-failure
                          proof test badge-equation failure padded (car projections) arity-equation))
           (normalization (l1-guarded-padding-normalization
                           (cdr same-failure) (car same-failure) take-equation
                           padded actuals failure arguments taken))
           (entries (l1-guarded-lemma-entries
                     (list (list *l1-guarded-arity-name* arity-equation)
                           (list (proof-sym "L1-PADDED-ARGUMENT-LENGTH" "ACL2") size-equation)
                           (list (proof-sym "L1-PADDED-ARGUMENT-PROPER" "ACL2") proper)
                           (list (proof-sym "L1-PADDED-ARGUMENT-IDEMPOTENT" "ACL2") once)
                           (list *l1-guarded-padded-failure* (car same-failure))
                           (list *l1-guarded-take-name* take-equation)
                           (list *l1-guarded-take-failure* (car normalization)))
                     0 nil)))
        (cons (append entries (list (proof-step-clause (car normalization))))
              (cdr normalization))))))

(defun l1-guarded-badge-validity (proof badge-equation)
  (proof-with-checked-results
      ((function (l1-guarded-term-path badge-equation '(1 1)))
       (badge (proof-term-at badge-equation 2))
       (designator (proof-term-at function 1))
       (value (proof-term-at badge 1)))
    (let* ((valid (proof-sym "APPLY$-BADGEP" "ACL2"))
           (extra (list *l1-guarded-tame-function* valid
                        (proof-sym "WEAK-APPLY$-BADGE-P" "ACL2")
                        *library-natp* (proof-sym "TRUE-LISTP" "ACL2") *library-len*
                        (proof-sym "ALL-NILS" "ACL2") (proof-sym "SUBSETP-EQUAL" "ACL2")
                        (proof-sym "MEMBER-EQUAL" "ACL2")))
           (reduction (l1-application-application-with-kind
                       (l1-application-application-init
                        proof designator (list (cons designator value)) extra *l1-guarded-control*)
                       :literal)))
      (proof-with-checked-results
          ((validity (l1-application-application-reduce reduction (list valid badge)))
           (first (l1-guarded-step-first validity))
           (checked (proof-proof-true-from-eq proof validity))
           (bare (l1-application-application-reduce reduction
                                                   (list *l1-guarded-tame-function* function)))
           (bare-value (l1-guarded-step-term bare 2))
           (asserted (l1-guarded-assertion (equal bare-value *proof-false*)))
           (not-nil (proof-proof-not-nil proof))
           (reversed (proof-proof-symmetric proof bare))
           (untame (proof-proof-rewrite proof not-nil reversed '(1 1)))
           (untame (proof-proof-tidy proof untame))
           (first (l1-guarded-step-first untame))
           (badge-test (proof-eq (list *l1-guarded-badge* function) badge))
           (untame (proof-proof-subsume proof untame (list first (proof-neg badge-test)))))
        (l1-guarded-lemma-entries
         (list (list (proof-sym "L1-BADGE-VALID" "ACL2") checked)
               (list (proof-sym "L1-BADGE-REQUIRES-QUOTED-USE" "ACL2") untame))
         0 nil)))))

(defund l1-guarded-constant-lambda-entry (proof suffix step)
  (let ((name (proof-sym (concatenate 'string "L1-CONSTANT-LAMBDA-" suffix) "ACL2")))
    (proof-with-checked-results
        ((first (l1-guarded-step-first step))
         (step (proof-proof-subsume proof step (list first))))
      (proof-proof-entry "lemma" name (list name first) (list step)))))

(defun l1-guarded-constant-lambda-entries (proof lemmas count sources)
  (declare (xargs :measure (acl2-count lemmas)))
  (if (endp lemmas)
      (list count (text-join "" (reverse sources)))
    (proof-with-checked-results
        ((entry (l1-guarded-constant-lambda-entry proof (caar lemmas) (cadar lemmas))))
      (l1-guarded-constant-lambda-entries proof (cdr lemmas) (+ count (car (caddr entry)))
                                         (cons (cadddr entry) sources)))))

(defun l1-guarded-constant-lambdas (proof arguments)
  (let* ((quoted (l1-primitive-cons-list (list (proof-quote *proof-quote*) *l1-guarded-value*)
                                         *proof-false*))
         (code (l1-primitive-cons-list (list (proof-quote (proof-cl "LAMBDA"))
                                             *proof-false* quoted)
                                       *proof-false*))
         (extra (list *l1-guarded-tame-function* (proof-sym "LAMBDA-OBJECT-SHAPEP" "ACL2")
                      (proof-sym "SYMBOL-LISTP" "ACL2")))
         (reduction (l1-application-application-with-kind
                     (l1-application-application-init
                      proof *l1-guarded-tame-function* nil extra :default)
                     :lambda)))
    (proof-with-checked-results
        ((tame-equation (l1-application-application-reduce reduction
                                                          (list *l1-guarded-tame-function* code)))
         (tame-value (l1-guarded-step-term tame-equation 2))
         (asserted (l1-guarded-assertion (equal tame-value *proof-true*)))
         (tame (proof-proof-true-from-eq proof tame-equation))
         (result (l1-application-application-reduce reduction
                                                   (list *l1-application-apply* code arguments)))
         (value (l1-guarded-step-term result 2))
         (asserted (l1-guarded-assertion (equal value *l1-guarded-value*))))
      (l1-guarded-constant-lambda-entries proof (list (list "TAME" tame) (list "VALUE" result))
                                         0 nil))))

(defun l1-guarded-actual-bindings (formals actuals bindings)
  (declare (xargs :measure (acl2-count formals)))
  (if (or (endp formals) (endp actuals))
      bindings
    (l1-guarded-actual-bindings (cdr formals) (cdr actuals)
                                (table-put bindings (car formals) (car actuals)))))

(defund l1-guarded-result-call-route (term names calls)
  (cond
   ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
    (list :finished calls))
   ((endp term) (l1-witness-need-at-least term 1))
   (t
    (let ((head (car term))
          (args (cdr term)))
      (cond
       ((equal head *termination-return-last*)
        (if (endp args)
            '(:failure "failure" "")
          (list :visit (car (last args)) calls)))
       ((proof-compound head)
        (proof-with-checked-results
            ((body (proof-term-at head 2))
             (formals (proof-term-at head 1))
             (value (proof-subst body (l1-guarded-actual-bindings formals args nil))))
          (list :visit value calls)))
       (t (list :arguments args (if (member-equal head names) (cons term calls) calls))))))))

(mutual-recursion
 (defun l1-guarded-result-calls-visit (n term names calls)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "l1-guarded-result-calls-visit")
     (proof-with-checked-results ((next (l1-guarded-result-call-route term names calls)))
       (case (car next)
         (:visit (l1-guarded-result-calls-visit (1- n) (cadr next) names (caddr next)))
         (:arguments (l1-guarded-result-calls-arguments (1- n) (cadr next) names (caddr next)))
         (otherwise (cadr next))))))

 (defun l1-guarded-result-calls-arguments (n args names calls)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "l1-guarded-result-calls-arguments"))
         ((endp args) calls)
         (t
          (proof-with-checked-results
              ((calls (l1-guarded-result-calls-visit (1- n) (car args) names calls)))
            (l1-guarded-result-calls-arguments (1- n) (cdr args) names calls))))))

(defun l1-guarded-result-calls (term names)
  (proof-with-checked-results ((calls (l1-guarded-result-calls-visit 1000000 term names nil)))
    (reverse calls)))

(defun l1-guarded-audit-definitions (definitions records)
  (declare (xargs :measure (acl2-count records)))
  (if (endp records)
      definitions
    (proof-with-checked-results ((record (proof-list-of-length (car records) 3)))
      (l1-guarded-audit-definitions (table-put definitions (car record) (cdr record))
                                    (cdr records)))))

(defun l1-guarded-audit-grants (grants functions data)
  (declare (xargs :measure (acl2-count functions)))
  (if (endp functions)
      grants
    (proof-with-checked-results
        ((function (proof-list-of-length (car functions) 2))
         (formulas (proof-term-at data 1)))
      (l1-guarded-audit-grants (table-put grants (car function) formulas)
                              (cdr functions) data))))

(defun l1-guarded-affected-grants-p (formulas affected)
  (if (endp formulas)
      nil
    (proof-with-checked-results
        ((formula (proof-list-of-length (car formulas) 2))
         (calls (l1-witness-dependencies-collect (cadr formula) nil)))
      (or (intersectp-equal calls affected)
          (l1-guarded-affected-grants-p (cdr formulas) affected)))))

(defund l1-guarded-audit-record (record definitions grants affected)
  (proof-with-checked-results ((record (proof-list-of-length record 3)))
    (let ((kind (cadr record))
          (data (caddr record)))
      (cond
       ((equal kind "define")
        (proof-with-checked-results
            ((definitions
              (if (integerp data)
                  '(:failure "failure" "")
                (l1-guarded-audit-definitions definitions (cdr data))))
             (dependent (l1-witness-affected-definitions-p (cdr data) affected))
             (affected (if dependent (l1-witness-affected-definition-names (cdr data) affected)
                         affected)))
          (list definitions grants affected)))
       ((equal kind "constrain")
        (proof-with-checked-results
            ((functions (proof-term-at data 0))
             (grants (l1-guarded-audit-grants grants functions data))
             (formulas (proof-term-at data 1))
             (dependent (and (not (equal formulas *proof-nil*))
                             (l1-guarded-affected-grants-p formulas affected))))
          (list definitions grants
                (if dependent (union-equal affected (strip-cars functions)) affected))))
       ((equal kind "choose")
        '(:failure "failure" ""))
       (t (list definitions grants affected))))))

(defun l1-guarded-audit-lookup (name map)
  (let ((found (assoc-equal name map)))
    (if found
        (cdr found)
      '(:failure "failure" ""))))

(defun l1-guarded-same-set-p (left right)
  (and (subsetp-equal left right) (subsetp-equal right left)))

(defund l1-guarded-audit-application-case (branch formals affected specials dynamic)
  (proof-with-checked-results
      ((parts (proof-list-of-length (cdr branch) 3))
       (test (car parts))
       (result (cadr parts))
       (checked (l1-guarded-assertion (proof-is-call test (proof-cl "EQ"))))
       (operand (proof-term-at test 1))
       (formal (proof-term-at formals 0))
       (checked (l1-guarded-assertion (equal operand formal)))
       (designator (proof-term-at test 2))
       (checked (l1-guarded-assertion (proof-is-call designator *proof-quote*)))
       (name (proof-term-at designator 1))
       (calls (l1-witness-dependencies-collect result nil)))
    (list (add-to-set-equal name specials)
          (if (intersectp-equal calls affected) (add-to-set-equal name dynamic) dynamic))))

(defund l1-guarded-audit-badge-case (branch required)
  (proof-with-checked-results
      ((parts (proof-list-of-length (cdr branch) 3))
       (name (l1-guarded-term-path (car parts) '(2 1)))
       (flag (table-get required name nil)))
    (l1-guarded-assertion
     (or (not flag)
         (equal (cadr parts)
                (proof-quote (list (proof-sym "APPLY$-BADGE" "ACL2") 2 1 flag *proof-nil*)))))))

(defun l1-guarded-audit-argument-guards (positions actuals)
  (if (endp positions)
      nil
    (proof-with-checked-results
        ((actual (proof-term-at actuals (car positions)))
         (rest (l1-guarded-audit-argument-guards (cdr positions) actuals)))
      (cons (list *l1-guarded-tame-function* actual) rest))))

(defun l1-guarded-audit-guard-conditional (guards)
  (if (endp (cdr guards))
      (car guards)
    (proof-ite (car guards) (l1-guarded-audit-guard-conditional (cdr guards)) *proof-false*)))

(defun l1-guarded-audit-callbacks (positions formals)
  (if (endp positions)
      nil
    (proof-with-checked-results
        ((formal (proof-term-at formals (car positions)))
         (rest (l1-guarded-audit-callbacks (cdr positions) formals)))
      (add-to-set-equal formal rest))))

(defun l1-guarded-audit-recursive-call (call positions formals)
  (declare (xargs :measure (acl2-count positions)))
  (and (consp positions)
    (proof-with-checked-results
        ((actual (proof-term-at call (1+ (car positions))))
         (formal (proof-term-at formals (car positions)))
         (checked (l1-guarded-assertion (equal actual formal))))
      (l1-guarded-audit-recursive-call call (cdr positions) formals))))

(defun l1-guarded-audit-applied (calls function positions formals applied)
  (declare (xargs :measure (acl2-count calls)))
  (if (endp calls)
      applied
    (let ((call (car calls)))
      (proof-with-checked-results ((head (proof-term-at call 0)))
        (cond
         ((equal head *l1-application-apply*)
          (proof-with-checked-results ((designator (proof-term-at call 1)))
            (l1-guarded-audit-applied (cdr calls) function positions formals
                                      (add-to-set-equal designator applied))))
         ((equal head function)
          (proof-with-checked-results ((checked (l1-guarded-audit-recursive-call call positions formals)))
            (l1-guarded-audit-applied (cdr calls) function positions formals applied)))
         (t '(:failure "failure" "")))))))

(defund l1-guarded-audit-row (parts definitions affected primitive specials)
  (proof-with-checked-results
      ((parts (proof-list-of-length parts 3))
       (comparison (car parts))
       (test (cadr parts))
       (guard (caddr parts))
       (function (l1-guarded-term-path test '(1 1 1 1)))
       (badge (l1-guarded-term-path test '(1 2 1)))
       (checked (l1-guarded-assertion (not (or (member-equal function primitive)
                                             (member-equal function specials)))))
       (flags (nthcdr 3 badge))
       (positions (l1-guarded-function-positions flags 0))
       (arity (proof-term-at badge 1))
       (argument (l1-witness-comparison-argument comparison))
       (actuals (l1-application-select-args argument arity))
       (first (proof-term-at positions 0))
       (checked (l1-guarded-assertion (and (equal first 0) (equal (len flags) arity))))
       (equation (proof-term-at test 2))
       (checked (l1-guarded-assertion
                 (equal equation (proof-eq (list *l1-guarded-apply-user*
                                                 (proof-quote function) argument)
                                           (cons function actuals)))))
       (guards (l1-guarded-audit-argument-guards positions actuals))
       (checked (l1-guarded-assertion (equal guard (l1-guarded-audit-guard-conditional guards))))
       (definition (l1-guarded-audit-lookup function definitions))
       (formals (car definition))
       (callbacks (l1-guarded-audit-callbacks positions formals))
       (calls (l1-guarded-result-calls (cadr definition) affected))
       (applied (l1-guarded-audit-applied calls function positions formals nil)))
    (l1-guarded-assertion (l1-guarded-same-set-p applied callbacks))))

(defconst *l1-guarded-audit-early*
  (list (proof-sym "BADGE-USERFN-TYPE" "ACL2")
        (proof-sym "APPLY$-USERFN-TAKES-ARITY-ARGS" "ACL2")
        (proof-sym "UNTAME-APPLY$-TAKES-ARITY-ARGS" "ACL2")
        (proof-sym "UNTAME-APPLY$ constraint 1" "ACL2")))

