(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-lemmas-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *t3-book-lemmas-iff* (proof-sym "IFF" "ACL2"))
(defconst *t3-book-lemmas-true-listp* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *t3-book-lemmas-exported-nfix* (proof-sym "NFIX" "ACL2"))
(defconst *t3-book-lemmas-setp* (proof-sym "SETP" "SET"))
(defconst *t3-book-lemmas-empty* (proof-sym "EMPTYP$INLINE" "SET"))
(defconst *t3-book-lemmas-sfix* (proof-sym "SFIX$INLINE" "SET"))
(defconst *t3-book-lemmas-set-tail* (proof-sym "TAIL$INLINE" "SET"))

; These computation and simplification rules are also used in logic.lisp.
(defconst *t3-book-lemmas-reciprocal* (proof-sym "UNARY-/" "ACL2"))
(defconst *t3-book-lemmas-wrappers*
  (list *termination-return-last* (proof-sym "THE-CHECK" "ACL2")))

(defun t3-book-lemmas-rational-value (datum)
  (cond ((integerp datum) datum)
        ((eq datum t) 1)
        ((and (consp datum) (equal (car datum) "ratio"))
         (proof-with-checked-results
             ((num (proof-term-at datum 1))
              (den (proof-term-at datum 2)))
           (let ((num (if (eq num t) 1 num))
                 (den (if (eq den t) 1 den)))
             (cond ((not (and (rationalp num) (rationalp den)))
                    '(:failure "failure" ""))
                   ((equal den 0)
                    '(:failure "failure" ""))
                   (t (/ num den))))))
        (t nil)))

(defun t3-book-lemmas-rational-result (head values)
  (proof-with-checked-results
      ((first (proof-constant-book-argument values 0))
       (second (and (member-equal head (list *proof-less* *proof-plus* *proof-times*))
                    (proof-constant-book-argument values 1))))
    (if (equal head *proof-less*)
        (if (< first second) *proof-t* *proof-nil*)
      (let ((value (cond ((equal head *proof-plus*) (+ first second))
                         ((equal head *proof-times*) (* first second))
                         ((equal head *proof-minus*) (- first))
                         ((equal first 0) 0)
                         (t (/ first)))))
        (if (integerp value)
            value
          (list "ratio" (numerator value) (denominator value)))))))

(defun t3-book-lemmas-rational-values (args)
  (if (endp args)
      nil
    (proof-with-checked-results
        ((datum (proof-term-at (car args) 1))
         (value (t3-book-lemmas-rational-value datum))
         (rest (t3-book-lemmas-rational-values (cdr args))))
      (cons value rest))))

(defun t3-book-lemmas-constant-character (proof term args)
  (proof-with-checked-results ((arg (proof-constant-book-argument args 0)))
    (if (proof-is-call arg *proof-quote*)
        (proof-with-checked-results ((value (proof-term-at arg 1)))
          (proof-proof-compute proof term
                               (if (equal (proof-datum-head value) "char")
                                   *proof-t*
                                 *proof-nil*)))
      (proof-proof-constant-base proof term))))

(defun t3-book-lemmas-constant-selector-value (head value)
  (cond ((or (not (proof-compound value)) (endp value)) *proof-nil*)
        ((equal head *library-car*) (car value))
        ((endp (cdr value)) *proof-nil*)
        ((and (endp (cddr value)) (not (cadr value)))
         '(:failure "missing-proof-input" ""))
        ((and (endp (cddr value)) (equal (proof-datum-head (cadr value)) "dot"))
         (proof-term-at (cadr value) 1))
        (t (cdr value))))

(defun t3-book-lemmas-constant-selector (lib term head args)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((arg (proof-constant-book-argument args 0)))
      (cond ((proof-is-call arg *proof-cons*)
             (library-library-axiom lib (if (equal head *library-car*) "CAR-CONS" "CDR-CONS")
                                    (cdr arg)))
            ((proof-is-call arg *proof-quote*)
             (proof-with-checked-results
                 ((value (proof-term-at arg 1))
                  (result (t3-book-lemmas-constant-selector-value head value)))
               (proof-proof-compute proof term result)))
            (t (proof-proof-constant-base proof term))))))

(defun t3-book-lemmas-constant-cons (proof term args)
  (proof-with-checked-results
      ((values (proof-quoted-values (seq-slice args 0 3)))
       (parts (proof-list-of-length values 2)))
    (proof-proof-compute proof term
                         (proof-constant-cons-value (car parts) (cadr parts)))))

(defun t3-book-lemmas-constant-consp (lib term args)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((arg (proof-constant-book-argument args 0)))
      (if (and (proof-is-call arg *proof-cons*)
               (assoc-equal (proof-sym "SELF-T3-CONSP-CONS-TRUE" "ACL2")
                            (proof-proof-facts proof)))
          (library-library-cite lib "T3-CONSP-CONS-TRUE" (cdr arg) nil)
        (proof-proof-constant-base proof term)))))

(defun t3-book-lemmas-constant (lib term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((parts (proof-constant-call-parts term)))
      (let ((head (car parts))
            (args (cdr parts)))
        (cond
         ((equal head (proof-cl "CHARACTERP"))
          (t3-book-lemmas-constant-character proof term args))
         ((and (member-equal head (list *proof-plus* *proof-times* *proof-minus*
                                       *proof-less* *t3-book-lemmas-reciprocal*))
               (proof-all-quoted-p args))
          (proof-with-checked-results ((values (t3-book-lemmas-rational-values args)))
            (if (member-equal nil values)
                (proof-proof-constant-base proof term)
              (proof-with-checked-results ((result (t3-book-lemmas-rational-result head values)))
                (proof-proof-compute proof term result)))))
         ((member-equal head (list *library-car* *library-cdr*))
          (t3-book-lemmas-constant-selector lib term head args))
         ((and (equal head *proof-cons*) (proof-all-quoted-p args))
          (t3-book-lemmas-constant-cons proof term args))
         ((equal head *proof-consp*) (t3-book-lemmas-constant-consp lib term args))
         (t (proof-proof-constant-base proof term)))))))

(mutual-recursion
 (defun t3-book-lemmas-simplify-visit (n lib term evidence definitions)
   (declare (xargs :measure (nfix n)))
   (let ((proof (library-library-proof lib))
         (head (proof-datum-head term)))
     (cond
      ((zp n) '(:failure "fuel" "t3-book-lemmas-simplify"))
      ((or (not (proof-compound term)) (equal head *proof-quote*)) nil)
      ((endp term) '(:failure "missing-proof-input" ""))
      ((or (proof-compound head) (member-equal head definitions))
       (proof-with-checked-results
           ((expansion (proof-simplify-expansion proof term))
            (next (t3-book-lemmas-simplify-visit (1- n) lib (cadr expansion)
                                               evidence definitions)))
         (proof-proof-chain proof (car expansion) (list next))))
      ((equal head *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at term 1))
            (first (t3-book-lemmas-simplify-visit (1- n) lib test evidence definitions))
            (path (proof-simplify-if-path proof term first evidence)))
         (if (eq (car path) :simplify)
             (proof-with-checked-results
                 ((next (t3-book-lemmas-simplify-visit (1- n) lib (caddr path)
                                                    evidence definitions)))
               (proof-proof-chain proof (cadr path) (list next)))
           path)))
      (t
       (proof-with-checked-results
           ((result (t3-book-lemmas-simplify-arguments (1- n) lib term (cdr term)
                                                      1 nil evidence definitions))
            (current (if result (proof-rewritten-term result) term))
            (constant (t3-book-lemmas-constant lib current)))
         (cond ((not constant) result)
               (result (proof-proof-chain proof result (list constant)))
               (t constant)))))))

 (defun t3-book-lemmas-simplify-arguments (n lib term args index result evidence definitions)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "t3-book-lemmas-simplify"))
         ((endp args) result)
         (t
          (proof-with-checked-results
              ((equality (t3-book-lemmas-simplify-visit (1- n) lib (car args)
                                                       evidence definitions))
               (next (proof-simplify-argument-result
                      (library-library-proof lib) term index result equality)))
            (t3-book-lemmas-simplify-arguments (1- n) lib term (cdr args)
                                             (1+ index) next evidence definitions))))))

(defun t3-book-lemmas-simplify (lib term evidence definitions)
  (t3-book-lemmas-simplify-visit 1000000 lib term evidence definitions))

(defun t3-book-lemmas-simplify-first (lib step evidence definitions)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (equality (t3-book-lemmas-simplify lib literal evidence definitions)))
      (if equality
          (proof-with-checked-results ((rewritten (proof-proof-rewrite proof step equality '(1))))
            (proof-proof-tidy proof rewritten))
        step))))

(defun t3-book-lemmas-normalize (lib term evidence definitions)
  (t3-book-lemmas-simplify lib term evidence (append *t3-book-lemmas-wrappers* definitions)))

(defun t3-book-lemmas-true-equality (lib step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (parts (proof-list-of-length literal 3))
         (reflexive (proof-proof-fact proof "equal-same" (list (list *library-x* (cadr parts)))))
         (result (proof-proof-rewrite proof reflexive step '(1 1 2))))
      (proof-proof-tidy proof result))))

(defun t3-book-lemmas-nil-value (lib denial)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first denial))
         (term (proof-term-at literal 1))
         (either (proof-proof-nil-or-true proof term))
         (positive (proof-proof-front proof either term)))
      (proof-proof-cut proof positive denial))))

(defun t3-book-lemmas-implication (lib term consequent)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (proof-term-at term 1))
         (equation (proof-proof-unfold proof term))
         (body (proof-rewritten-term equation))
         (proved (proof-proof-prove proof *proof-true* nil nil))
         (inner (proof-term-at body 2))
         (selected (proof-proof-select proof inner consequent))
         (inner-yes (proof-proof-transport proof proved selected))
         (if-true (proof-proof-if-true proof body))
         (yes (proof-proof-transport proof inner-yes if-true))
         (if-false (proof-proof-if-false proof body))
         (no (proof-proof-transport proof proved if-false))
         (joined (proof-proof-cases proof test yes no)))
      (proof-proof-transport proof joined equation))))

(defun t3-book-lemmas-boolean-value (lib)
  (let* ((proof (library-library-proof lib))
         (recognized (list *t3-book-lemmas-booleanp* *library-x*))
         (desired (proof-eq *library-x* *proof-true*))
         (eq-head (proof-cl "EQ")))
    (proof-with-checked-results
        ((positive (proof-proof-assume proof *library-x* t))
         (assumed (proof-proof-assume proof recognized t))
         (boolean (t3-book-lemmas-simplify-first lib assumed nil
                                                (list *t3-book-lemmas-booleanp* eq-head)))
         (denial (proof-proof-assume proof desired nil))
         (equal-nil (proof-proof-prove-if proof boolean denial))
         (simplified (t3-book-lemmas-simplify-first lib equal-nil nil (list eq-head)))
         (rewritten (proof-proof-rewrite proof positive simplified '(1)))
         (tidied (proof-proof-tidy proof rewritten))
         (conclusion (proof-proof-front proof tidied desired)))
      (library-library-lemma lib "T3-BOOLEAN-TRUE" desired conclusion
                             (list (proof-neg recognized) (proof-neg *library-x*))))))

(defun t3-book-lemmas-iff-direction (lib equivalent opened target premise name)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof equivalent t))
         (contradiction (proof-proof-rewrite proof assumed opened '(1)))
         (x-guard (proof-proof-assume proof *library-x* (equal target *library-y*)))
         (x-case (proof-proof-prove-if proof contradiction x-guard))
         (y-guard (proof-proof-assume proof *library-y* (equal target *library-x*)))
         (y-case (proof-proof-prove-if proof x-case y-guard))
         (conclusion (proof-proof-front proof y-case target)))
      (library-library-lemma lib name target conclusion
                             (list (proof-neg equivalent) (proof-neg premise))))))

(defun t3-book-lemmas-iff-elimination (lib)
  (let ((equivalent (list *t3-book-lemmas-iff* *library-x* *library-y*))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof equivalent))
         (left (t3-book-lemmas-iff-direction lib equivalent opened
                                            *library-x* *library-y* "T3-IFF-LEFT")))
      (t3-book-lemmas-iff-direction left equivalent opened
                                   *library-y* *library-x* "T3-IFF-RIGHT"))))

(defun t3-book-lemmas-cons-equality-different (project part rhs-nil lib left whole)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof whole t))
         (reflexive (proof-proof-reflexive proof (list project left)))
         (observed (proof-proof-rewrite proof reflexive assumed '(1 2 1)))
         (simplified (t3-book-lemmas-simplify-first lib observed nil nil))
         (part-denied (proof-proof-assume proof part nil))
         (contradiction (proof-proof-cut proof simplified part-denied))
         (denied (proof-proof-front proof contradiction (proof-neg whole)))
         (value (t3-book-lemmas-nil-value lib denied))
         (symmetric (proof-proof-symmetric proof rhs-nil)))
      (proof-proof-chain proof value (list symmetric)))))

(defun t3-book-lemmas-cons-equality (lib)
  (let* ((proof (library-library-proof lib))
         (u (proof-sym "U" "ACL2"))
         (left (list *proof-cons* *library-x* *library-y*))
         (right (list *proof-cons* *library-z* u))
         (whole (proof-eq left right))
         (first (proof-eq *library-x* *library-z*))
         (rest (proof-eq *library-y* u))
         (conjunction (proof-ite first rest *proof-false*)))
    (proof-with-checked-results
        ((a (proof-proof-assume proof first t))
         (b (proof-proof-assume proof rest t))
         (reflexive (proof-proof-reflexive proof left))
         (head-rewrite (proof-proof-rewrite proof reflexive a '(1 2 1)))
         (rewritten (proof-proof-rewrite proof head-rewrite b '(1 2 2)))
         (combined (proof-proof-tidy proof rewritten))
         (if-true (proof-proof-if-true proof conjunction))
         (rest-true (t3-book-lemmas-true-equality lib b))
         (rhs-true (proof-proof-chain proof if-true (list rest-true)))
         (whole-true (t3-book-lemmas-true-equality lib combined))
         (reverse-true (proof-proof-symmetric proof rhs-true))
         (both (proof-proof-chain proof whole-true (list reverse-true)))
         (tail-true (proof-proof-if-true proof conjunction))
         (rest-denied (proof-proof-assume proof rest nil))
         (rest-nil (t3-book-lemmas-nil-value lib rest-denied))
         (tail-nil (proof-proof-chain proof tail-true (list rest-nil)))
         (different-tail (t3-book-lemmas-cons-equality-different
                          *library-cdr* rest tail-nil lib left whole))
         (tails (proof-proof-cases proof rest both different-tail))
         (if-false (proof-proof-if-false proof conjunction))
         (different-head (t3-book-lemmas-cons-equality-different
                          *library-car* first if-false lib left whole))
         (result (proof-proof-cases proof first tails different-head)))
      (library-library-lemma lib "T3-EQUAL-CONS" (proof-eq whole conjunction) result nil))))

(defun t3-book-lemmas-natural-fix (lib)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((exported (proof-proof-unfold proof (list *t3-book-lemmas-exported-nfix* *library-x*)))
         (local (proof-proof-unfold proof (list *library-nfix* *library-x*)))
         (body (proof-rewritten-term local))
         (simplified (t3-book-lemmas-simplify lib body nil (list *library-natp*)))
         (chained (proof-proof-chain proof local (list simplified)))
         (symmetric (proof-proof-symmetric proof chained))
         (same (proof-proof-chain proof exported (list symmetric)))
         (claim (proof-step-first same)))
      (library-library-lemma lib "T3-EXPORTED-NFIX" claim same nil))))

(defun t3-book-lemmas-set-tail-is-empty (is-nil lib empty nil-test atom definitions)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((evidence (proof-proof-assume proof nil-test is-nil))
         (equation (t3-book-lemmas-normalize lib empty (list atom evidence) definitions))
         (right (and is-nil (proof-rewritten-term equation)))
         (equation (if (and is-nil (equal right nil-test))
                       (proof-with-checked-results ((equal-true (t3-book-lemmas-true-equality lib evidence)))
                         (proof-proof-chain proof equation (list equal-true)))
                     equation)))
      (proof-proof-true-from-eq proof equation))))

(defun t3-book-lemmas-set-tail (lib)
  (let* ((proof (library-library-proof lib))
         (empty (list *t3-book-lemmas-empty* *library-x*))
         (cons-test (list *proof-consp* *library-x*))
         (nil-test (proof-eq *library-x* *proof-false*))
         (definitions (list *t3-book-lemmas-empty* *t3-book-lemmas-setp*
                            (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "EQ")
                            (proof-cl "NULL") *proof-not*))
         (tail (list *t3-book-lemmas-set-tail* *library-x*))
         (goal (list *proof-ordinal-less* (list *library-count* tail)
                     (list *library-count* *library-x*))))
    (proof-with-checked-results
        ((not-empty (proof-proof-assume proof empty nil))
         (atom (proof-proof-assume proof cons-test nil))
         (yes (t3-book-lemmas-set-tail-is-empty t lib empty nil-test atom definitions))
         (no (t3-book-lemmas-set-tail-is-empty nil lib empty nil-test atom definitions))
         (cases (proof-proof-cases proof nil-test yes no))
         (contradiction (proof-proof-cut proof cases not-empty))
         (positive (proof-proof-front proof contradiction cons-test))
         (opened (t3-book-lemmas-normalize lib tail (list not-empty)
                                           (list *t3-book-lemmas-set-tail* *t3-book-lemmas-sfix*)))
         (builtin (library-library-builtin lib 3 *library-x*))
         (smaller (proof-proof-discharge proof builtin positive))
         (symmetric (proof-proof-symmetric proof opened))
         (rewritten (proof-proof-rewrite proof smaller symmetric '(1 1 1)))
         (result (proof-proof-tidy proof rewritten)))
      (library-library-lemma lib "T3-SET-TAIL-COUNT" goal result (list empty)))))

(defun t3-book-lemmas-proper-list-branches (lib cons-test holds opened definition equivalent defs)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof cons-test holds))
         (left-normal (t3-book-lemmas-normalize lib definition (list assumed) defs))
         (left (proof-proof-chain proof opened (list left-normal)))
         (body (proof-rewritten-term equivalent))
         (right-normal (t3-book-lemmas-normalize lib body (list assumed) defs))
         (right (proof-proof-chain proof equivalent (list right-normal))))
      (list left right))))

(defun t3-book-lemmas-proper-list-conjunct (n proof premise)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t3-book-lemmas-proper-list-conjunct")
    (proof-with-checked-results
        ((literal (proof-step-first premise))
         (no (and (proof-is-call literal *proof-if*) (proof-term-at literal 3))))
      (if (equal no *proof-false*)
          (proof-with-checked-results ((conjuncts (proof-proof-conjunct proof premise)))
            (t3-book-lemmas-proper-list-conjunct (1- n) proof (cadr conjuncts)))
        premise))))

(defun t3-book-lemmas-proper-list-premise (proof antecedent equality)
  (proof-with-checked-results
      ((assumed (proof-proof-assume proof antecedent t))
       (rewritten (proof-proof-rewrite proof assumed equality '(1))))
    (proof-proof-tidy proof rewritten)))

(defun t3-book-lemmas-proper-list-base (lib term antecedent left right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left-value (proof-rewritten-term left))
         (right-value (proof-rewritten-term right)))
      (if (not (member-equal left-value (list *proof-false* right-value)))
          nil
        (proof-with-checked-results
            ((premise (t3-book-lemmas-proper-list-premise proof antecedent left))
             (base (if (equal left-value *proof-false*)
                       (proof-proof-subsume proof premise
                                            (proof-unique (cons right-value (proof-step-clause premise))))
                     premise))
             (transported (proof-proof-transport proof base right)))
          (t3-book-lemmas-implication lib term transported))))))

(defun t3-book-lemmas-proper-list-induct (lib term variable predicate antecedent branches base-case)
  (let* ((proof (library-library-proof lib))
         (left (car branches))
         (right (cadr branches))
         (tail (list *library-cdr* variable))
         (smaller-type (list predicate tail))
         (cons-test (list *proof-consp* variable)))
    (proof-with-checked-results
        ((premise (t3-book-lemmas-proper-list-premise proof antecedent left))
         (conjunct (t3-book-lemmas-proper-list-conjunct 1000000 proof premise))
         (first (proof-step-first conjunct))
         (right-value (and (equal first smaller-type) (proof-rewritten-term right))))
      (if (not (equal right-value (list *t3-book-lemmas-true-listp* tail)))
          nil
        (let* ((measure (list *library-count* variable))
               (binding (list variable tail))
               (substitutions (list (list binding)))
               (smaller (list *proof-ordinal-less* (list *library-count* tail) measure)))
          (proof-with-checked-results
              ((smaller-term (proof-subst term (list (cons variable tail))))
               (assumed (proof-proof-assume proof (proof-ite smaller smaller-term *proof-true*) t))
               (decrease (library-library-builtin lib 3 variable))
               (induction (proof-proof-prove-if proof assumed decrease))
               (consequent (proof-proof-modus-ponens proof induction conjunct))
               (transported (proof-proof-transport proof consequent right))
               (step-case (t3-book-lemmas-implication lib term transported))
               (ordinal (library-library-builtin lib 1 variable))
               (cases (proof-proof-cases proof cons-test step-case base-case)))
            (proof-proof-induct proof ordinal cases term measure substitutions)))))))

(defun t3-book-lemmas-proper-list-recognizer (lib term variable predicate antecedent result opened definition)
  (let* ((proof (library-library-proof lib))
         (cons-test (list *proof-consp* variable))
         (defs (list (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "NULL")
                     (proof-cl "EQ") *proof-not*)))
    (proof-with-checked-results
        ((equivalent (proof-proof-unfold proof result))
         (step (t3-book-lemmas-proper-list-branches lib cons-test t opened definition equivalent defs))
         (base (t3-book-lemmas-proper-list-branches lib cons-test nil opened definition equivalent defs))
         (base-case (t3-book-lemmas-proper-list-base lib term antecedent (car base) (cadr base))))
      (and base-case
           (t3-book-lemmas-proper-list-induct lib term variable predicate antecedent step base-case)))))

(defun t3-book-lemmas-proper-list-wrapper (definition variable)
  (if (not (proof-is-call definition *proof-if*))
      nil
    (proof-with-checked-results ((no (proof-term-at definition 3)))
      (let ((condition (cadr definition)))
        (and (equal no *proof-false*)
             (proof-compound condition)
             (equal (cdr condition) (list variable))
             condition)))))

(defund t3-book-lemmas-proper-list-input (lib term wrappers)
  (if (not (proof-is-call term *library-implies*))
      nil
    (proof-with-checked-results ((result (proof-term-at term 2)))
      (if (not (proof-is-call result *t3-book-lemmas-true-listp*))
          nil
        (proof-with-checked-results
            ((args (proof-list-of-length (cdr term) 2))
             (variable (proof-term-at result 1)))
          (let* ((proof (library-library-proof lib))
                 (antecedent (car args))
                 (predicate (car antecedent)))
            (if (or (proof-compound variable)
                    (not (proof-compound antecedent))
                    (not (equal (cdr antecedent) (list variable)))
                    (not (assoc-equal predicate (proof-proof-definitions proof)))
                    (member-equal predicate wrappers))
                nil
              (proof-with-checked-results
                  ((opened (proof-proof-unfold proof antecedent))
                   (definition (proof-rewritten-term opened))
                   (condition (t3-book-lemmas-proper-list-wrapper definition variable)))
                (list condition result predicate variable antecedent opened definition)))))))))

(defun t3-book-lemmas-proper-list-finish (lib term input fact)
  (let ((proof (library-library-proof lib))
        (result (cadr input))
        (predicate (caddr input))
        (variable (cadddr input))
        (antecedent (car (cddddr input)))
        (opened (cadr (cddddr input)))
        (definition (caddr (cddddr input))))
    (if fact
        (proof-with-checked-results
            ((assumption (t3-book-lemmas-proper-list-premise proof antecedent opened))
             (parts (proof-proof-conjunct proof assumption))
             (consequent (proof-proof-modus-ponens proof fact (car parts))))
          (t3-book-lemmas-implication lib term consequent))
      (t3-book-lemmas-proper-list-recognizer
       lib term variable predicate antecedent result opened definition))))

(defun t3-book-lemmas-implies-proper-list-visit (n lib term wrappers)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t3-book-lemmas-implies-proper-list")
    (proof-with-checked-results ((input (t3-book-lemmas-proper-list-input lib term wrappers)))
      (if (not input)
          nil
        (proof-with-checked-results
            ((fact (and (car input)
                        (t3-book-lemmas-implies-proper-list-visit
                         (1- n) lib (list *library-implies* (car input) (cadr input))
                         (append wrappers (list (caddr input)))))))
          (t3-book-lemmas-proper-list-finish lib term input fact))))))

(defun t3-book-lemmas-implies-proper-list (lib term wrappers)
  (t3-book-lemmas-implies-proper-list-visit 1000000 lib term wrappers))

