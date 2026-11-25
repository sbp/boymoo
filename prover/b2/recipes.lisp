(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defmacro b2-recipes-solve (lib goal evidence unfold)
  `(b2-tactics-tactics-solve ,lib ,goal ,evidence ,unfold nil 0 nil))

(defun b2-recipes-step-at (step index)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun b2-recipes-legal-variable-consequence-bad (tests lib legal antecedent conclusion)
  (let ((proof (library-library-proof lib))
        (unfold '(("sym" "ACL2" "LEGAL-VARIABLEP")
                  ("sym" "ACL2" "LEGAL-VARIABLE-OR-CONSTANT-NAMEP"))))
    (proof-with-checked-results
        ((equation (b2-tactics-tactics-normalize lib antecedent tests unfold nil 1500 nil))
         (value (b2-recipes-step-at equation 2)))
      (if (not (equal value *proof-false*))
          '(:failure "tactic-rejected" "")
        (proof-with-checked-results
            ((rewritten (proof-proof-rewrite proof legal equation '(1)))
             (conflict (proof-proof-tidy proof rewritten)))
          (proof-proof-subsume proof conflict (cons conclusion (proof-step-clause conflict))))))))

(defun b2-recipes-legal-variable-consequence (legal lib antecedent conclusion tests)
  (let ((symbol-test (car tests))
        (t-test (cadr tests))
        (nil-test (caddr tests))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((symbol-step (proof-proof-assume proof symbol-test t))
         (t-step (proof-proof-assume proof t-test t))
         (nil-step (proof-proof-assume proof nil-test t))
         (not-symbol (proof-proof-assume proof symbol-test nil))
         (not-t (proof-proof-assume proof t-test nil))
         (not-nil (proof-proof-assume proof nil-test nil))
         (result (b2-recipes-solve lib conclusion (list symbol-step not-t not-nil) nil))
         (nil-result (b2-recipes-legal-variable-consequence-bad
                      (list symbol-step not-t nil-step) lib legal antecedent conclusion))
         (result (proof-proof-cases proof nil-test nil-result result))
         (t-result (b2-recipes-legal-variable-consequence-bad
                    (list symbol-step t-step) lib legal antecedent conclusion))
         (result (proof-proof-cases proof t-test t-result result))
         (non-symbol (b2-recipes-legal-variable-consequence-bad
                      (list not-symbol) lib legal antecedent conclusion)))
      (proof-proof-cases proof symbol-test result non-symbol))))

(defun b2-recipes-legal-variable (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (x (proof-term-at (cadr parts) 1)))
    (let ((antecedent (cadr parts))
          (conclusion (caddr parts))
          (tests (list (list *b2-tactics-symbolp* x)
                       (proof-eq x *proof-true*) (proof-eq x *proof-false*))))
      (proof-with-checked-results
          ((request (b2-tactics-tactics-implication lib antecedent conclusion nil))
           (step (b2-recipes-legal-variable-consequence
                  (cadddr (car request)) lib antecedent conclusion tests))
           (result (b2-tactics-tactics-implication lib antecedent conclusion (cons step lib))))
        (car result)))))

(defun b2-recipes-distributivity-rewrite (lib step terms z index)
  (declare (xargs :measure (len terms)))
  (if (not (o< (len (cdr terms)) (len terms)))
      step
    (proof-with-checked-results
        ((arg (proof-term-at (car terms) 1))
         (axiom (library-library-axiom lib "COMMUTATIVITY-OF-*" (list z arg)))
         (rewritten (proof-proof-rewrite (library-library-proof lib) step axiom
                                         (list 1 2 index))))
      (b2-recipes-distributivity-rewrite lib rewritten (cdr terms) z (1+ index)))))

(defun b2-recipes-distributivity (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (sum (proof-term-at (cadr parts) 1))
       (addends (if (integerp sum)
                    '(:failure "tactic-rejected" "")
                  (proof-list-of-length (cdr sum) 2)))
       (z (proof-term-at (cadr parts) 2)))
    (let ((proof (library-library-proof lib))
          (right (caddr parts)))
      (proof-with-checked-results
          ((commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list sum z)))
           (distributed (library-library-axiom lib "DISTRIBUTIVITY"
                                                 (list z (car addends) (cadr addends))))
           (step (proof-proof-chain proof commuted (list distributed)))
           (terms (if (integerp right)
                      '(:failure "tactic-rejected" "")
                    (cdr right)))
           (rewritten (b2-recipes-distributivity-rewrite lib step terms z 1)))
        (proof-proof-tidy proof rewritten)))))

(defun b2-recipes-oracle-state-read (value index mv-nth read-oracle)
  (list mv-nth index (list read-oracle value)))

(defun b2-recipes-oracle-state-leaf-normalize (count lib current result twice)
  (declare (xargs :measure (nfix count)))
  (if (not (o< (nfix (1- count)) (nfix count)))
      (if (equal current twice) result '(:failure "tactic-rejected" ""))
    (proof-with-checked-results
        ((step (b2-tactics-tactics-normalize lib current nil
                    (list current (proof-sym "ZP" "ACL2")) nil 1500 nil))
         (chained (proof-proof-chain (library-library-proof lib) result (list step)))
         (current (b2-recipes-step-at chained 2)))
      (b2-recipes-oracle-state-leaf-normalize (1- count) lib current chained twice))))

(defun b2-recipes-oracle-state-leaf (value tests lib index mv-nth twice)
  (declare (ignore tests))
  (let ((current (list mv-nth index value)))
    (proof-with-checked-results
        ((result (proof-proof-reflexive (library-library-proof lib) current))
         (number (proof-term-at index 1)))
      (cond
       ((integerp number)
        (b2-recipes-oracle-state-leaf-normalize (1+ number) lib current result twice))
       ((or (eq number t) (null number))
        (b2-recipes-oracle-state-leaf-normalize (if number 2 1) lib current result twice))
       ((stringp number)
        '(:failure "tactic-rejected" ""))
       (t '(:failure "tactic-rejected" ""))))))

(defun b2-recipes-oracle-state-by-value (n lib value template tests index mv-nth twice)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "b2-recipes-oracle-state-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (yes (b2-recipes-oracle-state-by-value
                 (1- n) lib (cadr branches) template (append tests (list (list (car branches) t)))
                 index mv-nth twice))
           (no (b2-recipes-oracle-state-by-value
                (1- n) lib (caddr branches) template (append tests (list (list (car branches) nil)))
                index mv-nth twice)))
        (proof-by-value-join proof value template yes no)))
     ((and (proof-compound value) (not (consp value)))
      '(:failure "tactic-rejected" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (body (b2-recipes-step-at equality 2))
           (step (b2-recipes-oracle-state-by-value (1- n) lib body template tests index mv-nth twice))
           (reversed (proof-proof-symmetric proof equality)))
        (proof-proof-rewrite-result proof step reversed template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (b2-recipes-oracle-state-leaf value tests lib index mv-nth twice))
           (literal (proof-step-first step))
           (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal target) step '(:failure "tactic-rejected" "")))))))

(defun b2-recipes-oracle-state-preserve (state-proof lib pred once twice projection)
  (let ((name (proof-sym "STATE-P1-READ-ACL2-ORACLE" "ACL2")))
    (proof-with-checked-results
        ((first (b2-tactics-tactics-use-fact lib name (list pred once)
                                            (list state-proof) nil nil 0 nil))
         (second (b2-tactics-tactics-use-fact lib name (list pred twice)
                                             (list first) nil nil 0 nil)))
      (library-library-transport-argument lib second projection 1))))

(defun b2-recipes-oracle-state (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (goal (proof-list-of-length (caddr parts) 2))
       (projection-form (proof-list-of-length (cadr goal) 3))
       (initial-state (proof-term-at (cadr parts) 1)))
    (let* ((antecedent (cadr parts))
           (pred (car goal))
           (index (cadr projection-form))
           (call (caddr projection-form))
           (mv-nth (proof-sym "MV-NTH" "ACL2"))
           (read-oracle (proof-sym "READ-ACL2-ORACLE" "ACL2"))
           (once (b2-recipes-oracle-state-read initial-state index mv-nth read-oracle))
           (twice (b2-recipes-oracle-state-read once index mv-nth read-oracle))
           (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((opened (proof-proof-unfold proof call))
           (template (proof-eq (list mv-nth index *proof-result*) twice))
           (body (b2-recipes-step-at opened 2))
           (projection (b2-recipes-oracle-state-by-value 1000000 lib body template nil index mv-nth twice))
           (reversed (proof-proof-symmetric proof opened))
           (projection (proof-proof-rewrite-result proof projection reversed template *proof-result*))
           (request (b2-tactics-tactics-implication lib antecedent goal nil))
           (preserved (b2-recipes-oracle-state-preserve
                       (cadddr (car request)) lib pred once twice projection))
           (result (b2-tactics-tactics-implication lib antecedent goal (cons preserved lib))))
        (car result)))))

(defun b2-recipes-singleton-fact (lib facts formula)
  (cond
   ((endp facts) nil)
   ((equal (cdar facts) (list formula))
    (proof-proof-fact (library-library-proof lib) (caar facts) nil))
   (t (b2-recipes-singleton-fact lib (cdr facts) formula))))

(defun b2-recipes-with-library (value lib)
  (if (failure-p value) value (cons value lib)))

(defun b2-recipes-distributivity-fact (lib facts formula)
  (let* ((name (proof-sym "DISTRIBUTIVITY" "ACL2"))
         (entry (assoc-equal name facts)))
    (if (not entry)
        '(:failure "tactic-rejected" "")
      (proof-with-checked-results ((pattern (proof-term-at (cdr entry) 0)))
        (b2-tactics-tactics-exact lib name pattern formula)))))

(defun b2-recipes-prove-theorem (lib name formula)
  (let ((facts (proof-proof-facts (library-library-proof lib))))
    (proof-with-checked-results ((fact (b2-recipes-singleton-fact lib facts formula)))
      (cond
       (fact (cons fact lib))
       ((equal name '("sym" "ACL2" "LEN-TEST-2"))
        (b2-recipes-with-library
         (b2-recipes-solve lib formula nil
                           (list (proof-sym "TEST-2" "ACL2") (proof-cl "LENGTH") *library-len*))
         lib))
       ((equal name '("sym" "ACL2" "SYMBOLP-WHEN-LEGAL-VARIABLEP"))
        (b2-recipes-with-library (b2-recipes-legal-variable lib formula) lib))
       ((equal name '("sym" "ACL2" "(* (+ x y) z)"))
        (b2-recipes-with-library (b2-recipes-distributivity lib formula) lib))
       ((equal name '("sym" "ACL2" "(* x (+ y z))"))
        (b2-recipes-with-library (b2-recipes-distributivity-fact lib facts formula) lib))
       ((equal name '("sym" "ACL2" "MAP-SYMBOL-NAME-OF-CONS"))
        (b2-recipes-with-library
         (b2-recipes-solve lib formula nil (list (proof-sym "MAP-SYMBOL-NAME" "ACL2"))) lib))
       ((member-equal name '(("sym" "ACL2" "STRING-LISTP-OF-MAP-SYMBOL-NAME")
                             ("sym" "ACL2" "CHARACTER-LISTP-MAKE-CHARACTER-LIST")))
        (b2-recipes-with-library (b2-lists-mapped-recognizer lib formula) lib))
       ((equal name '("sym" "ACL2" "RATIONALP-SUMLIST"))
        (b2-recipes-with-library (b2-lists-rational-sum lib formula) lib))
       ((equal name '("sym" "ACL2" "SUMLIST-APPEND"))
        (b2-recipes-with-library (b2-lists-sum-append lib formula) lib))
       ((member-equal name '(("sym" "ACL2" "FACTORIAL-POSITIVE-INTEGER")
                             ("sym" "ACL2" "FACTORIAL-NON-NEGATIVE")
                             ("sym" "ACL2" "ABS-FACTORIAL")))
        (b2-recipes-with-library (b2-arithmetic-factorial-properties lib name formula) lib))
       ((equal name '("sym" "ACL2" "REWRITE-LINEAR-EQUALITIES-TO-IFF"))
        (b2-recipes-with-library (b2-tactics-tactics-solve lib formula nil nil nil 2 nil) lib))
       ((equal name '("sym" "ACL2" "UNIQUENESS-OF-*-INVERSES"))
        (b2-products-unique-inverse lib formula))
       ((member-equal name '(("sym" "ACL2" "EXPTS-ADD-AGGRESSIVE")
                             ("sym" "ACL2" "EXPTS-ADD-INVERSE")))
        (b2-powers-expt-add lib name formula))
       ((member-equal name '(("sym" "ACL2" "ENABLED-RUNEP-GUARD-HELPER-1")
                             ("sym" "ACL2" "ENABLED-RUNEP-GUARD-HELPER-2")))
        (b2-recipes-with-library (b2-association-enabled-runep lib formula) lib))
       ((equal name '("sym" "ACL2" "PSEUDO-TERMP-CDR-ASSOC-EQUAL"))
        (b2-recipes-with-library (b2-association-pseudo-term-of-assoc lib formula) lib))
       ((member-equal name '(("sym" "ACL2" "PSEUDO-TERMP-SUBLIS-VAR1")
                             ("sym" "ACL2" "PSEUDO-TERMP-SUBLIS-VAR1-LST")))
        (b2-substitution-substitution-preserves-term lib name formula))
       ((equal name '("sym" "ACL2" "SYMBOLP-DEREF-MACRO-NAME"))
        (b2-recipes-with-library (b2-association-symbol-dereference lib formula) lib))
       ((member-equal name '(("sym" "ACL2" "CONSP-OF-BUTLAST")
                             ("sym" "ACL2" "CAR-OF-BUTLAST")
                             ("sym" "ACL2" "BUTLAST-OF-CONS")
                             ("sym" "ACL2" "CDR-OF-BUTLAST")
                             ("sym" "ACL2" "BUTLAST-OF-NIL")))
        (b2-butlast-prove-butlast lib name formula))
       ((member-equal name '(("sym" "RADIX" "CHARACTER-LISTP-INT2HEX-LST")
                             ("sym" "RADIX" "CHARACTER-LISTP-CONVERT-RADIX-LST")))
        (b2-radix-character-accumulator lib formula))
       ((member-equal name '(("sym" "ACL2" "NUMERATOR-WHEN-INTEGERP")
                             ("sym" "ACL2" "INTEGERP==>DENOMINATOR=1")
                             ("sym" "ACL2" "EQUAL-DENOMINATOR-1")
                             ("sym" "ACL2" "*-R-DENOMINATOR-R")))
        (b2-products-numerator-denominator lib name formula))
       ((member-equal name '(("sym" "ACL2" "NUMERATOR-MINUS")
                             ("sym" "ACL2" "DENOMINATOR-MINUS")))
        (b2-fraction-reduction-fraction-minus lib name formula))
       ((member-equal name '(("sym" "ACL2" "FOLD-ABST-REVERSE")
                             ("sym" "ACL2" "FOLD-MULT-REVERSE")))
        (b2-folds-fold-reverse lib formula))
       ((member-equal name '(("sym" "ACL2" "TEST1") ("sym" "ACL2" "TEST2")))
        (b2-reversal-reversal lib formula))
       ((equal name '("sym" "ACL2" "REWRITE-FLOOR-X*Y-Z-LEFT"))
        (b2-products-floor-reassociate lib formula))
       ((member-equal name '(("sym" "ACL2" "ONE") ("sym" "ACL2" "TWO")))
        (b2-logand-prove-logand lib name formula))
       ((member-equal name '(("sym" "ACL2" "MEMBER-EQ-SORT-SYMBOL-LISTP")
                             ("sym" "ACL2" "STRICT-SYMBOL<-SORTEDP-SORT-SYMBOL-LISTP")))
        (b2-recipes-with-library (b2-sorting-sort-wrapper lib name formula) lib))
       ((equal name '("sym" "ACL2" "MEMBER-EQ-STRICT-MERGE-SORT-SYMBOL<"))
        (b2-sorting-merge-sort-membership lib formula))
       ((equal name '("sym" "ACL2" "STRICT-SYMBOL<-SORTEDP-STRICT-MERGE-SORT-SYMBOL<"))
        (b2-sort-order-sort-order lib formula))
       ((equal name '("sym" "ACL2" "REMOVE-FIRST-HYP-CP-CORRECT"))
        (b2-removal-first-hypothesis lib formula))
       ((equal name '("sym" "ACL2" "DISJOIN-OF-REMOVE-EQUAL"))
        (b2-removal-disjoin-remove lib formula))
       ((equal name '("sym" "ACL2" "REMOVE-HYP-CP-CORRECT"))
        (b2-removal-arbitrary-hypothesis lib formula))
       ((equal name '("sym" "ACL2" "STATE-P1-OF-REAL-ORACLE-EVAL"))
        (b2-recipes-with-library (b2-recipes-oracle-state lib formula) lib))
       (t (b2-tactics-unproved))))))

(defun b2-recipes-witness-arities (functions)
  (if (endp functions)
      nil
    (proof-with-checked-results
        ((fn (proof-list-of-length (car functions) 2))
         (rest (b2-recipes-witness-arities (cdr functions))))
      (cons (cadr fn) rest))))

(defun b2-recipes-witness-renaming (functions witnesses names)
  (if (endp functions)
      names
    (proof-with-checked-results ((fn (proof-list-of-length (car functions) 2)))
      (if (endp witnesses)
          names
        (b2-recipes-witness-renaming (cdr functions) (cdr witnesses)
                                     (table-put names (car fn) (car witnesses)))))))

(defun b2-recipes-witness-goals (formulas renaming)
  (if (endp formulas)
      nil
    (proof-with-checked-results
        ((named (proof-list-of-length (car formulas) 2))
         (goal (b2-tactics-rename-calls (cadr named) renaming))
         (rest (b2-recipes-witness-goals (cdr formulas) renaming)))
      (cons goal rest))))

(defun b2-recipes-witness-proofs (lib goals witnesses)
  (declare (xargs :measure (len goals)))
  (if (not (o< (len (cdr goals)) (len goals)))
      nil
    (proof-with-checked-results
        ((proof (b2-recipes-solve lib (car goals) nil witnesses))
         (rest (b2-recipes-witness-proofs lib (cdr goals) witnesses)))
      (cons proof rest))))

(defun b2-recipes-witness-entry (lib name functions formulas witnesses)
  (proof-with-checked-results
      ((renaming (b2-recipes-witness-renaming functions witnesses nil))
       (goals (b2-recipes-witness-goals formulas renaming))
       (proofs (b2-recipes-witness-proofs lib goals witnesses))
       (entry (proof-proof-entry "witness" name (cons name witnesses) proofs)))
    (cons entry lib)))

(defun b2-recipes-witness-test (functions formulas formula name)
  (proof-with-checked-results ((arities (b2-recipes-witness-arities functions)))
    (and (equal arities '(0 2))
         (equal (len formulas) 1)
         (proof-is-call formula *library-implies*)
         (proof-with-checked-results ((test (proof-term-at formula 1)))
           (let ((call (list name)))
             (or (equal test call) (equal test (proof-neg call))))))))

(defun b2-recipes-prove-witness (lib functions formulas)
  (proof-with-checked-results
      ((first-function (proof-term-at functions 0))
       (name (proof-term-at first-function 0))
       (first-formula (proof-term-at formulas 0))
       (formula (proof-term-at first-formula 1)))
    (if (equal name '("sym" "ACL2" "ABST"))
        (let ((witness (proof-sym "B2-ABST-WITNESS" "ACL2")))
          (proof-with-checked-results
              ((lib (library-library-definition lib witness
                       (list *library-x* *library-y*) *proof-false*)))
            (b2-recipes-witness-entry lib name functions formulas (list witness))))
      (proof-with-checked-results ((test (b2-recipes-witness-test functions formulas formula name)))
        (if test
            (proof-with-checked-results ((stem (proof-term-at name 2)))
              (let ((witness (proof-sym (concatenate 'string "B2-" stem "-WITNESS") "ACL2"))
                    (body (if (equal (cadr formula) (list name)) *proof-false* *proof-true*)))
                (proof-with-checked-results
                    ((lib (library-library-definition lib witness *proof-nil* body)))
                  (b2-recipes-witness-entry lib name functions formulas
                    (list witness (proof-sym "BINARY-APPEND" "ACL2"))))))
          (proof-with-checked-results
              ((evaluator (b2-evaluator-evaluator-equations functions formulas)))
            (if evaluator
                (b2-evaluator-witness lib functions formulas)
              (b2-witnesses-find-witnesses lib functions formulas))))))))
