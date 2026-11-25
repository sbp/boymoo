(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-theorems-true-listp* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *b1-theorems-all-fnnames* (proof-sym "ALL-FNNAMES1" "ACL2"))
(defconst *b1-theorems-add-to-set* (proof-sym "ADD-TO-SET-EQUAL" "ACL2"))
(defconst *b1-theorems-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *b1-theorems-iff* (proof-sym "IFF" "ACL2"))
(defconst *b1-theorems-realfix* (proof-sym "REALFIX" "ACL2"))

(defun b1-theorems-term-tail (term)
  (if (integerp term)
      (proof-term-at term 1)
    (cdr term)))

(defun b1-theorems-step-result (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun b1-theorems-all-fnnames-bindings (pairs bindings)
  (if (endp pairs)
      bindings
    (b1-theorems-all-fnnames-bindings
     (cdr pairs)
     (table-put bindings (caar pairs) (cadar pairs)))))

(defun b1-theorems-all-fnnames-rewrite (proof step opened template)
  (proof-with-checked-results
      ((reversed (proof-proof-symmetric proof opened)))
    (proof-proof-rewrite-result proof step reversed template *proof-result*)))

(mutual-recursion
 (defun b1-theorems-all-fnnames-consequence-true-list
     (n value tests lib induction initial initial-acc formals template)
   (declare (xargs :measure (acl2-count n)))
   (let ((proof (library-library-proof lib)))
     (cond
      ((zp n) '(:failure "fuel" "b1-theorems-all-fnnames-consequence-true-list"))
      ((equal value initial-acc) (cons initial induction))
      ((proof-is-call value *b1-theorems-all-fnnames*)
       (proof-with-checked-results
           ((argument (proof-term-at value 3))
            (child-acc (b1-theorems-all-fnnames-consequence-true-list
                        (1- n) argument tests lib induction initial initial-acc
                        formals template))
            (child (b1-induction-tree-induction-hypothesis
                    (cdr child-acc)
                    (b1-theorems-all-fnnames-bindings
                     (seq-zip formals (cdr value)) nil)
                    tests))
            (step (proof-proof-modus-ponens proof (car child) (car child-acc))))
         (cons step (cdr child))))
      ((proof-is-call value *proof-cons*)
       (proof-with-checked-results
           ((argument (proof-term-at value 2))
            (tail (b1-theorems-all-fnnames-consequence-true-list
                   (1- n) argument tests lib induction initial initial-acc
                   formals template))
            (step (b1-logic-bookproof-normalize-proof
                   lib (list *b1-theorems-true-listp* value) (list (car tail))
                   (list *b1-theorems-true-listp*) nil nil)))
         (cons step (cdr tail))))
      (t
       (proof-with-checked-results
           ((opened (b1-logic-bookproof-normalize
                     lib value nil (list *b1-theorems-add-to-set*) nil nil nil nil))
            (result (b1-theorems-step-result opened)))
         (if (equal result value)
             '(:failure "unproved" "")
           (proof-with-checked-results
               ((branches (b1-theorems-all-fnnames-by-value
                           (1- n) result tests lib induction initial initial-acc
                           formals template))
                (step (b1-theorems-all-fnnames-rewrite
                       proof (car branches) opened template)))
             (cons step (cdr branches)))))))))

 (defun b1-theorems-all-fnnames-by-value
     (n value tests lib induction initial initial-acc formals template)
   (declare (xargs :measure (acl2-count n)))
   (let ((proof (library-library-proof lib)))
     (cond
      ((zp n) '(:failure "fuel" "b1-theorems-all-fnnames-by-value"))
      ((proof-is-call value *proof-if*)
       (proof-with-checked-results
           ((branches (proof-list-of-length (cdr value) 3))
            (yes (b1-theorems-all-fnnames-by-value
                  (1- n) (cadr branches) (append tests (list (list (car branches) t)))
                  lib induction initial initial-acc formals template))
            (no (b1-theorems-all-fnnames-by-value
                 (1- n) (caddr branches) (append tests (list (list (car branches) nil)))
                 lib (cdr yes) initial initial-acc formals template))
            (if-true (proof-proof-if-true proof value))
            (yes-proof (b1-theorems-all-fnnames-rewrite proof (car yes) if-true template))
            (if-false (proof-proof-if-false proof value))
            (no-proof (b1-theorems-all-fnnames-rewrite proof (car no) if-false template))
            (step (proof-proof-cases proof (car branches) yes-proof no-proof)))
         (cons step (cdr no))))
      ((not value) '(:failure "failure" ""))
      ((and (proof-compound value) (proof-compound (car value)))
       (proof-with-checked-results
           ((equality (proof-proof-beta proof value))
            (result (b1-theorems-step-result equality))
            (opened (b1-theorems-all-fnnames-by-value
                     (1- n) result tests lib induction initial initial-acc
                     formals template))
            (step (b1-theorems-all-fnnames-rewrite
                   proof (car opened) equality template)))
         (cons step (cdr opened))))
      (t
       (proof-with-checked-results
           ((leaf (b1-theorems-all-fnnames-consequence-true-list
                   (1- n) value tests lib induction initial initial-acc
                   formals template))
            (literal (proof-step-first (car leaf)))
            (target (proof-subst template (list (cons *proof-result* value)))))
         (if (equal literal target)
             leaf
           '(:failure "failure" ""))))))))

(defun b1-theorems-all-fnnames-consequence
    (initial lib call template induction formals initial-acc)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof call))
         (result (b1-theorems-step-result opened))
         (branches (b1-theorems-all-fnnames-by-value
                    1000000 result nil lib induction initial initial-acc formals template))
         (step (b1-theorems-all-fnnames-rewrite proof (car branches) opened template)))
      (cons step (cdr branches)))))

(defun b1-theorems-all-fnnames (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 3))
       (conclusion (proof-list-of-length (caddr formula) 2))
       (call (proof-list-of-length (cadr conclusion) 4)))
    (let* ((template (list *b1-theorems-true-listp* *proof-result*))
           (induction (b1-induction-tree-induction-init lib formula (caddr call)))
           (definition (assoc-equal *b1-theorems-all-fnnames*
                                    (proof-proof-definitions (library-library-proof lib)))))
      (if (not definition)
          '(:failure "failure" "")
        (proof-with-checked-results
            ((definition (proof-list-of-length (cdr definition) 2))
             (premise (b1-logic-bookproof-prove-implication-premise lib formula))
             (consequence (b1-theorems-all-fnnames-consequence
                           premise lib call template induction (car definition) (cadddr call)))
             (case-step (b1-logic-bookproof-prove-implication-with-premise
                         lib formula premise (car consequence))))
          (b1-induction-tree-induction-finish (cdr consequence) case-step))))))

(defun b1-theorems-realfix-rational (lib term)
  (proof-with-checked-results ((argument (proof-term-at term 1)))
    (let ((test (list *library-rationalp* argument))
          (claim (list *library-rationalp* term))
          (unfold (list *b1-theorems-realfix*))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((yes-assumption (proof-proof-assume proof test t))
           (yes (b1-logic-bookproof-normalize-proof
                 lib claim (list yes-assumption) unfold nil nil))
           (no-assumption (proof-proof-assume proof test nil))
           (no (b1-logic-bookproof-normalize-proof
                lib claim (list no-assumption) unfold nil nil)))
        (proof-proof-cases proof test yes no)))))

(defun b1-theorems-complex-opener-rewrite (proof completion argument position)
  (proof-with-checked-results
      ((opened (proof-proof-unfold proof argument))
       (reversed (proof-proof-symmetric proof opened)))
    (proof-proof-rewrite proof completion reversed (list 1 2 position))))

(defun b1-theorems-complex-opener (lib formula)
  (proof-with-checked-results
      ((call (proof-term-at formula 1))
       (arguments (b1-theorems-term-tail call))
       (arguments (proof-list-of-length arguments 2)))
    (let* ((a (car arguments))
           (b (cadr arguments))
           (x (list *b1-theorems-realfix* a))
           (y (list *b1-theorems-realfix* b))
           (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((fact (library-library-axiom lib "COMPLEX-DEFINITION" (list x y)))
           (literal (proof-step-first fact))
           (condition (proof-term-at literal 1))
           (rational-x (b1-theorems-realfix-rational lib x))
           (rational-y (b1-theorems-realfix-rational lib y))
           (guard (b1-logic-bookproof-normalize-proof
                   lib condition (list rational-x rational-y) nil nil nil))
           (valid (proof-proof-modus-ponens proof fact guard))
           (completion (library-library-axiom lib "COMPLETION-OF-COMPLEX" (list a b)))
           (completion (b1-theorems-complex-opener-rewrite proof completion x 1))
           (completion (b1-theorems-complex-opener-rewrite proof completion y 2)))
        (proof-proof-chain proof completion (list valid))))))

(defun b1-theorems-predicate-equality-cases (variables booleans rules lib formula)
  (if (endp variables)
      (b1-logic-bookproof-normalize-proof lib formula nil (list *b1-theorems-iff*) rules nil)
    (let ((term (car variables))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((yes-assumption (proof-proof-assume proof term t))
           (boolean (if (consp booleans)
                        (car booleans)
                      '(:failure "failure" "")))
           (yes (b1-logic-bookproof-boolean-value lib yes-assumption boolean))
           (no-assumption (proof-proof-assume proof term nil))
           (no (b1-logic-bookproof-false-value lib no-assumption))
           (yes-proof (b1-theorems-predicate-equality-cases
                       (cdr variables) (cdr booleans)
                       (append rules (list (b1-logic-equal-to yes))) lib formula))
           (no-proof (b1-theorems-predicate-equality-cases
                      (cdr variables) (cdr booleans)
                      (append rules (list (b1-logic-equal-to no))) lib formula)))
        (proof-proof-cases proof term yes-proof no-proof)))))

(defun b1-theorems-predicate-equality (lib formula booleans)
  (proof-with-checked-results
      ((left (proof-term-at formula 1))
       (variables (b1-theorems-term-tail left)))
    (b1-theorems-predicate-equality-cases variables booleans nil lib formula)))

(defun b1-theorems-equal-of-predicates-consequence (hypothesis lib formula)
  (proof-with-checked-results
      ((conjuncts (b1-logic-bookproof-split-conjuncts lib hypothesis))
       (conclusion (proof-term-at formula 2)))
    (b1-theorems-predicate-equality lib conclusion (seq-slice conjuncts -2 :none))))

(defun b1-theorems-equal-of-predicates (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-theorems-equal-of-predicates-consequence premise lib formula)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-theorems-linear-equality-facts (proof terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((arguments (b1-theorems-term-tail (car terms)))
         (fact (proof-proof-fact proof "booleanp-<"
                                 (seq-zip (list *library-x* *library-y*) arguments)))
         (rest (b1-theorems-linear-equality-facts proof (cdr terms))))
      (cons fact rest))))

(defun b1-theorems-linear-equalities (lib formula)
  (proof-with-checked-results
      ((left (proof-term-at formula 1))
       (terms (b1-theorems-term-tail left))
       (facts (b1-theorems-linear-equality-facts (library-library-proof lib) terms)))
    (b1-theorems-predicate-equality lib formula facts)))

(defun b1-theorems-project-conjunct-consequence (n hypothesis lib formula)
  (declare (xargs :measure (acl2-count n)))
  (if (zp n)
      '(:failure "fuel" "b1-theorems-project-conjunct-consequence")
    (proof-with-checked-results
        ((literal (proof-step-first hypothesis))
         (otherwise (and (proof-is-call literal *proof-if*)
                         (proof-term-at literal 3))))
      (if (equal otherwise *proof-false*)
          (proof-with-checked-results
              ((parts (proof-proof-conjunct (library-library-proof lib) hypothesis))
               (part (proof-step-first (car parts)))
               (conclusion (proof-term-at formula 2)))
            (if (equal part conclusion)
                (car parts)
              (b1-theorems-project-conjunct-consequence (1- n) (cadr parts) lib formula)))
        (proof-with-checked-results ((conclusion (proof-term-at formula 2)))
          (if (equal literal conclusion)
              hypothesis
            '(:failure "unproved" "")))))))

(defun b1-theorems-project-conjunct (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-theorems-project-conjunct-consequence 1000000 premise lib formula)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defconst *b1-theorems-unproved*
  '("A-IN-ACL2-PKG"))

(defconst *b1-theorems-list-recipes*
  '(("TRUE-LISTP" . b1-abstract-lists-abstract-list-proper)
    ("CONS" . b1-abstract-lists-abstract-list-cons)
    ("CAR" . b1-abstract-lists-abstract-list-car)
    ("CDR" . b1-abstract-lists-abstract-list-cdr)
    ("MEMBER-EQUAL" . b1-abstract-lists-abstract-list-member)
    ("MEMBERP-EQUAL" . b1-abstract-lists-abstract-list-memberp)
    ("APPEND" . b1-abstract-lists-abstract-list-append)
    ("FIRSTN" . b1-abstract-lists-reuse-abstract-list)
    ("LAST" . b1-abstract-lists-reuse-abstract-list)
    ("NTH-SEG" . b1-abstract-lists-reuse-abstract-list)
    ("PUT-SEG" . b1-abstract-lists-reuse-abstract-list)
    ("REMOVE-EQUAL" . b1-abstract-lists-reuse-abstract-list)
    ("REMOVE-DUPLICATES-EQUAL" . b1-abstract-lists-reuse-abstract-list)
    ("REVAPPEND" . b1-abstract-lists-reuse-abstract-list)
    ("REVERSE" . b1-abstract-lists-abstract-list-reverse)
    ("NTHCDR" . b1-abstract-lists-abstract-list-nthcdr)
    ("MAKE-LIST" . b1-abstract-lists-abstract-make-list)
    ("INITIAL-SUBLISTP-EQUAL" . b1-abstract-lists-abstract-list-initial-sublist)
    ("PUT-NTH" . b1-abstract-lists-abstract-list-put-nth)
    ("TAKE" . b1-abstract-lists-abstract-list-bounded-operation)
    ("BUTLAST" . b1-abstract-lists-abstract-list-butlast)
    ("SUBSEQ" . b1-abstract-lists-abstract-list-subseq)
    ("UPDATE-NTH" . b1-abstract-lists-abstract-list-bounded-operation)
    ("NTH" . b1-abstract-lists-abstract-list-nth)))

(defconst *b1-theorems-bit-types*
  '("IFLOOR-TYPE"
    "IMOD-TYPE"
    "EXPT2-TYPE"
    "LOGCAR-TYPE"
    "LOGCDR-TYPE"
    "LOGCONS-TYPE"
    "LOGMASK-TYPE"
    "LOGHEAD-TYPE"
    "LOGTAIL-TYPE"
    "LOGAPP-TYPE"
    "LOGRPL-TYPE"
    "LOGEXT-TYPE"
    "LOGREV-TYPE"
    "LOGSAT-TYPE"
    "LOGEXTU-TYPE"
    "LOGNOTU-TYPE"
    "INTEGERP-OF-LOGSQUASH"
    "ASHU-TYPE"
    "LSHU-TYPE"
    "LOGITE-TYPE"
    "BITP-OF-B-ITE"))

(defun b1-theorems-list-recipe-variants (operation recipe variants)
  (if (endp variants)
      nil
    (cons (cons (concatenate 'string "LIST-TYPE-" operation (car variants)) recipe)
          (b1-theorems-list-recipe-variants operation recipe (cdr variants)))))

(defun b1-theorems-list-recipe-entries (operations)
  (if (endp operations)
      nil
    (append (b1-theorems-list-recipe-variants
             (caar operations) (cdar operations) '("00" "10" "11"))
            (b1-theorems-list-recipe-entries (cdr operations)))))

(defun b1-theorems-bit-type-entries (labels)
  (if (endp labels)
      nil
    (cons (cons (car labels) 'b1-bit-types-bit-operation-type)
          (b1-theorems-bit-type-entries (cdr labels)))))

(defconst *b1-theorems-recipes*
  (table-update
   (table-update
    '(("TRUE-LISTP-ALL-FNNAMES" . b1-theorems-all-fnnames)
      ("COMPLEX-OPENER" . b1-theorems-complex-opener)
      ("EQUAL-OF-PREDICATES-REWRITE" . b1-theorems-equal-of-predicates)
      ("REWRITE-LINEAR-EQUALITIES-TO-IFF" . b1-theorems-linear-equalities)
      ("REMOVE-WEAK-INEQUALITIES-ONE" . b1-theorems-project-conjunct)
      ("REMOVE-WEAK-INEQUALITIES-TWO" . b1-theorems-project-conjunct)
      ("OPEN-INPUT-CHANNELS-OF-MV-NTH-2-OF-READ-ACL2-ORACLE" . b1-structures-oracle-projection)
      ("W-OF-MV-NTH-2-OF-READ-ACL2-ORACLE" . b1-structures-oracle-projection)
      ("PSEUDO-TERMP-IMPLIES-PSEUDO-TERM-LISTP-CDR" . b1-structures-pseudo-tail)
      ("PSEUDO-TERMP-LAMBDA-LEMMA" . b1-structures-pseudo-lambda)
      ("UNIQUENESS-OF-*-INVERSES" . b1-arithmetic-inverse-uniqueness)
      ("NOT-INTEGERP-/-1" . b1-reciprocal-above-one)
      ("NOT-INTEGERP-/-2" . b1-reciprocal-below-minus-one)
      ("INTEGERP-/-HELPER" . b1-reciprocal-integer-reciprocal)
      ("NUMERATOR-WHEN-INTEGERP" . b1-arithmetic-numerator-when-integer)
      ("NUMERATOR-MINUS" . b1-reduced-numerator-minus)
      ("DENOMINATOR-MINUS" . b1-reduced-denominator-minus)
      ("INTEGERP==>DENOMINATOR=1" . b1-arithmetic-denominator-when-integer)
      ("EQUAL-DENOMINATOR-1" . b1-arithmetic-denominator-one)
      ("*-R-DENOMINATOR-R" . b1-arithmetic-times-denominator)
      ("EXPTS-ADD-AGGRESSIVE" . b1-powers-exponent-addition-goal)
      ("EXPTS-ADD-INVERSE" . b1-powers-exponent-addition-goal)
      ("EXPONENTS-ADD-FOR-NONPOS-EXPONENTS" . b1-theorems-exponent-addition-nonpositive)
      ("EXPONENTS-ADD-FOR-NONNEG-EXPONENTS" . b1-theorems-exponent-addition-nonnegative)
      ("EXPONENTS-ADD-2" . b1-powers-exponents-add-two)
      ("EXPONENTS-ADD-1" . b1-powers-exponent-addition-goal)
      ("EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-EVEN-EXPONENT" . b1-parity-even-power-positive)
      ("EXPT-TYPE-PRESCRIPTION-NEGATIVE-BASE-ODD-EXPONENT" . b1-parity-odd-power-negative)
      ("EXPT-NEGATIVE-BASE-EVEN-EXPONENT" . b1-parity-negated-base)
      ("EXPT-NEGATIVE-BASE-ODD-EXPONENT" . b1-parity-negated-base)
      ("EXPT-IS-INCREASING-FOR-BASE>1" . b1-monotone-increasing-power)
      ("REWRITE-FLOOR-MOD" . b1-floor-rewrite-floor-mod)
      ("REWRITE-MOD-MOD" . b1-floor-rewrite-mod-mod)
      ("(floor (+ x y) z)" . b1-floor-sum-floor-sum)
      ("(mod (+ x y) z)" . b1-floor-sum-mod-sum)
      ("LOGAND-Y-X" . b1-bitwise-logand-commutative)
      ("LOGAND-Y-X-Z" . b1-bitwise-interchange-logand)
      ("(equal (logand x y) -1)" . b1-conjunction-full-conjunction)
      ("LOGAND-ASSOC" . b1-conjunction-associated-conjunction)
      ("MOD-EXPT-FAST-IS-MOD-EXPT" . b1-mod-expt-mod-expt-fast)
      ("PERM-IS-AN-EQUIVALENCE" . b1-permutation-permutation-is-equivalence)
      ("*-OF-/-SAME" . b1-division-product-with-inverse)
      ("*-OF-*-OF-/-SAME" . b1-division-product-with-inverse)
      ("EQUAL-OF-*-OF-/" . b1-division-multiply-division-equality)
      ("EQUAL-OF-/" . b1-division-reciprocal-equality)
      ("<-OF-*-OF-/-ARG1-ARG1" . b1-division-divide-positive)
      ("<-OF-*-OF-/-ARG1-ARG2" . b1-division-divide-positive)
      ("<-OF-*-OF-/-ARG1-ARG3" . b1-division-divide-positive)
      ("<-OF-*-OF-/-ARG2-ARG1" . b1-division-divide-positive)
      ("<-OF-*-OF-/-ARG2-ARG2" . b1-division-divide-positive)
      ("<-OF-*-OF-/-ARG2-ARG1-GEN" . b1-division-divide-by-sign)
      ("<-OF-*-OF-CONSTANT-AND-CONSTANT-GEN" . b1-theorems-divide-by-inverted-sign)
      ("EQUAL-OF-NUMERATOR-SAME" . b1-numerators-equal-numerator)
      ("<-OF-NUMERATOR-AND-0" . b1-numerators-negative-numerator)
      ("NUMERATOR-OF-/-WHEN-INTEGERP" . b1-numerators-reciprocal-numerator)
      ("NUMERATOR-OF--" . b1-theorems-negated-numerator)
      ("NUMERATOR-OF-+-OF---AND--" . b1-numerators-numerator-distribute-sign)
      ("NUMERATOR-OF-*-OF---ARG2" . b1-numerators-numerator-distribute-sign)
      ("<=-OF-NUMERATOR-OF-*-OF-/" . b1-numerators-numerator-upper-bound)
      ("INTEGERP-SQUEEZE" . b1-integer-open-unit-interval)
      ("INTEGERP-OF-+-OF--1/2" . b1-integrality-half-shift)
      ("INTEGERP-OF-+-OF-1/2-AND-*-OF--1/2" . b1-integrality-reflected-half)
      ("INTEGERP-OF-+-OF---AND--" . b1-integrality-negated-sum-integral)
      ("INTEGERP-OF-+-OF-1/2-AND-*-OF-1/2" . b1-integrality-half-complement)
      ("INTEGERP-CHOICE" . b1-integrality-half-choice)
      ("NUMERATOR-WHEN-DENOMINATOR-IS-1" . b1-numerators-unit-denominator)
      ("MOD-OF-2-UPPER-BOUND" . b1-modular-remainder-consequence)
      ("INTEGERP-OF-MOD-OF-2" . b1-modular-remainder-consequence)
      ("MOD-OF-2-LOWER-BOUND" . b1-modular-remainder-consequence)
      ("HELPER-0-AUX" . b1-modular-exact-remainder-quotient)
      ("HELPER-0" . b1-theorems-helper-zero)
      ("HELPER-1-AUX" . b1-modular-exact-remainder-quotient)
      ("HELPER-1-AUX2" . b1-theorems-helper-one-auxiliary)
      ("HELPER-1" . b1-integrality-increment-half)
      ("<<-IRREFLEXIVE" . b1-total-order-strict-irreflexive)
      ("<<-TRANSITIVE" . b1-total-order-strict-transitive)
      ("<<-ASYMMETRIC" . b1-total-order-strict-asymmetric)
      ("<<-TRICHOTOMY" . b1-total-order-strict-total)
      ("<<-IMPLIES-LEXORDER" . b1-total-order-strict-implies-order)
      ("FAST-LEXORDER-IS-LEXORDER" . b1-lexical-fast-lexorder)
      ("FAST-<<-IS-<<" . b1-lexical-fast-strict-order)
      ("NO-DUPLICATESP-EQUAL-APPEND-IFF" . b1-list-sets-no-duplicate-append)
      ("INTERSECTP-EQUAL-APPEND2" . b1-list-sets-intersect-append)
      ("TRUE-LISTP-CDR-GET-OPTION-ENTRY" . b1-structures-option-entry-tail)
      ("OPEN-MV-NTH" . b1-structures-open-mv-nth)
      ("ARRAY1P-CONSP-HEADER" . b1-arrays-header-exists)
      ("ARRAY1P-CAR-HEADER" . b1-arrays-header-key)
      ("ARRAY1P-FORWARD-MODULAR" . b1-arrays-array-forward-modular)
      ("ARRAY1P-COMPRESS1" . b1-array-scan-valid-compressed-array)
      ("ARRAY1P-COMPRESS1-PROPERTIES" . b1-arrays-compress-array-properties)
      ("ARRAY1P-ASET1" . b1-arrays-update-is-array)
      ("ARRAY1P-ASET1-PROPERTIES" . b1-arrays-update-array-properties)
      ("ARRAY1P-ACONS-PROPERTIES" . b1-arrays-inserted-properties)
      ("AREF1-ASET1-EQUAL" . b1-arrays-read-updated-array)
      ("AREF1-ASET1-NOT-EQUAL" . b1-arrays-read-updated-array)
      ("AREF1-ASET1" . b1-arrays-read-updated-array-cases)
      ("AREF1-COMPRESS1" . b1-array-scan-read-compressed-array)
      ("RESET-ARRAY1*" . b1-arrays-reset-contents)
      ("ARRAY1P-RESET-ARRAY1" . b1-arrays-reset-is-array)
      ("ARRAY1P-RESET-ARRAY1-PROPERTIES" . b1-arrays-reset-properties)
      ("AREF1-RESET-ARRAY1" . b1-arrays-read-reset-array)
      ("CAR-OF-REVAPPEND" . b1-revappend-car-of-revappend)
      ("CONSP-OF-REVAPPEND" . b1-revappend-consp-of-revappend)
      ("REVAPPEND-IFF" . b1-revappend-revappend-nonempty)
      ("REVAPPEND-OF-APPEND-ARG2" . b1-revappend-accumulator-commutation)
      ("REVAPPEND-NORMALIZE-ACC" . b1-revappend-revappend-with-nil-accumulator)
      ("APPEND-OF-REVAPPEND-OF-NIL-ARG1" . b1-revappend-revappend-with-nil-accumulator)
      ("TRUE-LIST-FIX-OF-REVAPPEND" . b1-revappend-accumulator-commutation)
      ("LEN-OF-REVAPPEND" . b1-revappend-length-of-revappend)
      ("REVAPPEND-OF-REVAPPEND" . b1-revappend-reversed-twice)
      ("REVAPPEND-OF-TRUE-LIST-FIX-ARG1" . b1-revappend-revappend-of-list-fix)
      ("CDR-OF-REVAPPEND" . b1-revappend-cdr-of-revappend)
      ("<=-OF-ACL2-COUNT-OF-REVAPPEND-LINEAR" . b1-revappend-count-of-revappend)
      ("INTERSECTION-EQUAL-OF-REVAPPEND-ARG1-IFF" . b1-revappend-intersects-reversed-first)
      ("INTERSECTION-EQUAL-OF-REVAPPEND-ARG2-IFF" . b1-revappend-intersects-reversed-second)
      ("MEMBER-EQUAL-OF-REVAPPEND-IFF" . b1-revappend-member-of-revappend)
      ("EQUAL-OF-REVAPPEND-SAME-ARG2" . b1-revappend-reverse-not-unchanged)
      ("EQUAL-OF-REVAPPEND-AND-REVAPPEND-WHEN-SAME-LENGTH" . b1-revappend-revappend-pair-equality)
      ("REAL/RATIONALP-MAXLIST" . b1-list-types-numeric-fold-type)
      ("NATURALP-EXCESS-NATURAL" . b1-list-types-natural-excess)
      ("REAL/RATIONALP-MINLIST" . b1-list-types-numeric-fold-type)
      ("REAL/RATIONALP-SUM" . b1-list-types-numeric-fold-type)
      ("REAL/RATIONAL-LISTP-NUMERIC-INSERT" . b1-list-types-numeric-insert-type)
      ("REAL/RATIONAL-LISTP-NUMERIC-SORT" . b1-list-types-numeric-sort-type)
      ("NOT-MEMBER-EQUAL-OF-NIL" . b1-membership-member-nil)
      ("MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-CDR-CHEAP" . b1-membership-member-from-tail)
      ("MEMBER-EQUAL-OF-TRUE-LIST-FIX" . b1-membership-member-of-fixed-list)
      ("MEMBER-EQUAL-OF-TRUE-LIST-FIX-IFF" . b1-membership-member-of-fixed-list-iff)
      ("MEMBER-EQUAL-WHEN-MEMBER-EQUAL-OF-MEMBER-EQUAL" . b1-membership-member-of-suffix)
      ("MEMBER-EQUAL-OF-UNION-EQUAL" . b1-membership-member-of-set-operation)
      ("MEMBER-EQUAL-OF-SET-DIFFERENCE-EQUAL" . b1-membership-member-of-set-operation)
      ("MEMBER-EQUAL-OF-REMOVE-EQUAL" . b1-membership-member-of-set-operation)
      ("MEMBER-EQUAL-OF-REMOVE1-EQUAL-IRREL" . b1-membership-member-of-set-operation)
      ("MEMBER-EQUAL-OF-REMOVE1-EQUAL-UNDER-IFF" . b1-membership-member-after-removal-iff)
      ("CONSP-WHEN-MEMBER-EQUAL" . b1-membership-member-requires-cons)
      ("TRUE-LISTP-OF-MEMBER-EQUAL" . b1-membership-member-proper)
      ("NOT-MEMBER-EQUAL-OF-MEMBER-EQUAL-WHEN-NOT-MEMBER-EQUAL" . b1-membership-member-contrapositive)
      ("NOT-MEMBER-EQUAL-OF-CDR-WHEN-NOT-MEMBER-EQUAL" . b1-membership-member-contrapositive)
      ("MEMBER-EQUAL-OF-CONSTANT-WHEN-NOT-EQUAL-CAR" . b1-membership-membership-head-step)
      ("MEMBER-EQUAL-WHEN-SINGLETON" . b1-membership-singleton-member)
      ("MEMBER-EQUAL-OF-NTH-SAME" . b1-membership-member-at-index)
      ("MEMBER-EQUAL-OF-SINGLETON-CONSTANT-IFF" . b1-membership-member-of-singleton-length)
      ("MEMBER-EQUAL-OF-REMOVE-DUPLICATES-EQUAL-IFF" . b1-membership-member-of-set-operation)
      ("SUBSETP-EQUAL-CONS" . b1-set-laws-subset-of-extension)
      ("SUBSETP-EQUAL-REFLEXIVE" . b1-set-laws-subset-reflexive)
      ("SUBSETP-EQUAL-TRANSITIVE" . b1-set-laws-subset-transitive)
      ("SUBSETP-EQUAL-APPEND-CROCK" . b1-set-laws-subset-append-singleton)
      ("SUBSETP-EQUAL-APPEND2" . b1-set-laws-subset-of-extension)
      ("SUBSETP-EQUAL-ADJOIN-EQUAL1" . b1-set-laws-subset-adjoin)
      ("SUBSETP-EQUAL-INTERSECTION-EQUAL" . b1-set-laws-subset-of-set-operation)
      ("SUBSETP-EQUAL-SET-DIFFERENCE-EQUAL" . b1-set-laws-subset-of-set-operation)
      ("SUBSETP-EQUAL-UNION-EQUAL" . b1-set-laws-subset-of-set-operation)
      ("SET-EQUAL-SYMMETRIC" . b1-set-laws-set-equal-law)
      ("SET-EQUAL-TRANSITIVE" . b1-set-laws-set-equal-law)
      ("MEMBERP-EQUAL-SUBSETP-EQUAL" . b1-set-laws-memberp-subset)
      ("MEMBERP-EQUAL-SET-EQUAL" . b1-set-laws-memberp-set-equal)
      ("MEMBERP-EQUAL-ADJOIN-EQUAL" . b1-set-laws-memberp-of-set-operation)
      ("MEMBERP-EQUAL-INTERSECTION-EQUAL" . b1-set-laws-memberp-of-set-operation)
      ("MEMBERP-EQUAL-SET-DIFFERENCE-EQUAL" . b1-set-laws-memberp-of-set-operation)
      ("MEMBERP-EQUAL-UNION-EQUAL" . b1-set-laws-memberp-of-set-operation)
      ("SETP-EQUAL-CONS" . b1-set-laws-setp-cons)
      ("SETP-EQUAL-ADJOIN-EQUAL" . b1-set-laws-setp-adjoin)
      ("SETP-EQUAL-INTERSECTION-EQUAL" . b1-set-laws-setp-under-operation)
      ("SETP-EQUAL-SET-DIFFERENCE-EQUAL" . b1-set-laws-setp-under-operation)
      ("SETP-EQUAL-UNION-EQUAL" . b1-set-laws-setp-under-operation)
      ("SUBSETP-EQUAL-INTERSECTION-EQUAL-INSTANCE" . b1-set-laws-subset-filter-identity)
      ("SUBSETP-EQUAL-UNION-EQUAL-INSTANCE" . b1-set-laws-subset-filter-identity)
      ("SUBSETP-EQUAL-SET-DIFFERENCE-EQUAL-INSTANCE" . b1-set-laws-subset-filter-identity)
      ("SET-DIFFERENCE-EQUAL-CONS" . b1-set-laws-difference-of-redundant-cons)
      ("SET-DIFFERENCE-NULL-INTERSECTION" . b1-set-laws-difference-of-disjoint)
      ("NO-DUPLICATESP-EQUAL-APPEND" . b1-set-laws-no-duplicates-append)
      ("SETP-EQUAL-APPEND" . b1-set-laws-setp-append)
      ("TRUE-LISTP-OF-SPLIT-///.PRE-///" . b1-fixtypes-split-result-proper)
      ("TRUE-LISTP-OF-SPLIT-///.POST-///" . b1-fixtypes-split-result-proper)
      ("CHARACTER-LISTP-OF-PACK-LIST" . b1-printing-pack-character-lists)
      ("CHARACTER-LISTP-OF-PACK-TREE" . b1-printing-pack-character-lists)
      ("CAR-OF-PROD-CONS" . b1-fixtypes-product-selector)
      ("CDR-OF-PROD-CONS" . b1-fixtypes-product-selector)
      ("PROD-CONS-OF-CAR/CDR" . b1-fixtypes-product-reconstruction)
      ("EQUAL-OF-PROD-CONS" . b1-fixtypes-product-equality)
      ("ACL2-COUNT-OF-PROD-CONS" . b1-fixtypes-product-size)
      ("PROD-CONS-EQUAL-CONS" . b1-fixtypes-product-against-cons)
      ("PROD-CONS-NOT-CONSP-FORWARD" . b1-fixtypes-product-empty)
      ("TAG-FORWARD-TO-CONSP" . b1-fixtypes-tag-implies-cons)
      ("SYMBOL-LISTP-OF-LOOK-UP-FORMALS" . b1-fixtypes-lookup-result-type)
      ("SYMBOL-LISTP-OF-LOOK-UP-RETURN-VALS" . b1-fixtypes-lookup-result-type)
      ("BOOLEANP-OF-LOOK-UP-FORMALS" . b1-fixtypes-lookup-result-type)
      ("MV-NTH-OF-CONS" . b1-fixtypes-mv-nth-of-cons)
      ("IDENTITY-CP-WELLFORMED" . b1-fixtypes-identity-processor-wellformed)
      ("IDENTITY-CP-CORRECT" . b1-fixtypes-identity-processor-correct)
      ("EVAL-FOR-MV-NTH-REC-THM" . b1-clause-processors-mv-nth-evaluation-recursion)
      ("MV-NTH-CONS-META" . b1-clause-processors-mv-nth-evaluation-meta)
      ("FLAG-IS-CP-WELLFORMED" . b1-clause-processors-flag-processor-wellformed)
      ("FLAG-IS-CP-CORRECT" . b1-clause-processors-flag-processor-correct)
      ("ALIST-TYPE-ALISTP" . b1-typed-alists-alist-type-is-alist)
      ("ALIST-TYPE-ACONS" . b1-typed-alists-alist-type-acons)
      ("ALIST-TYPE-APPEND" . b1-typed-alists-typed-alist-recursion)
      ("ALIST-TYPE-BIND-EQUAL" . b1-typed-alists-typed-alist-recursion)
      ("ALIST-TYPE-REMBIND-EQUAL" . b1-typed-alists-typed-alist-recursion)
      ("ALIST-TYPE-PAIRLIS$" . b1-typed-alists-paired-alist-type)
      ("ALIST-TYPE-BIND-ALL-EQUAL" . b1-typed-alists-paired-alist-type)
      ("ALIST-TYPE-DOMAIN-RESTRICT-EQUAL" . b1-typed-alists-typed-alist-recursion)
      ("ALIST-TYPE-BIND-PAIRS-EQUAL" . b1-typed-alists-typed-alist-recursion)
      ("ALIST-TYPE-ASSOC-EQUAL" . b1-typed-alists-typed-alist-lookup)
      ("ALIST-TYPE-BOUND?-EQUAL" . b1-typed-alists-alist-bound-requires-key)
      ("ALIST-TYPE-ALL-BOUND?-EQUAL" . b1-typed-alists-all-bound-requires-keys)
      ("ALIST-TYPE-BINDING-EQUAL" . b1-typed-alists-alist-type-binding)
      ("ALIST-TYPE-CDR-ASSOC-EQUAL" . b1-typed-alists-range-of-association)
      ("ALIST-TYPE-DOMAIN" . b1-typed-alists-alist-projection-type)
      ("ALIST-TYPE-RANGE" . b1-typed-alists-alist-projection-type)
      ("ALIST-TYPE-COLLECT-BOUND-EQUAL" . b1-typed-alists-types-of-bound-entries)
      ("ALIST-TYPE-ALL-BINDINGS-EQUAL" . b1-typed-alists-types-of-bound-entries)
      ("STRINGP-OF-STRING-DOWNCASE$" . b1-xdoc-types-string-result)
      ("CHARACTER-LISTP-OF-CHARS-ESCAPE" . b1-xdoc-types-escaped-list-type)
      ("TRUE-LISTP-OF-MV-NTH-0-PARTITION-MACRO-ARGS" . b1-xdoc-types-partition-macro-args)
      ("ALISTP-OF-MV-NTH-1-PARTITION-MACRO-ARGS" . b1-xdoc-types-partition-macro-args)
      ("TREE-LISTP-WHEN-STRING-LISTP" . b1-xdoc-types-list-type-implication)
      ("TRUE-LISTP-WHEN-TREE-LISTP" . b1-xdoc-types-list-type-implication)
      ("TREEP-OF-CONS" . b1-xdoc-types-tree-cons)
      ("KEYWORD-TREE-ALISTP-OF-CONS" . b1-xdoc-types-tree-alist-cons)
      ("STRINGP-OF-TREE-TO-STRING" . b1-xdoc-types-string-result)
      ("STRINGP-OF-TREE-LIST-TO-STRING" . b1-xdoc-types-string-result)
      ("STRINGP-OF-MV-NTH-0-KEYWORD-OR-TREE-TAG-TO-STRINGS" . b1-xdoc-types-mv-string-result)
      ("STRINGP-OF-MV-NTH-1-KEYWORD-OR-TREE-TAG-TO-STRINGS" . b1-xdoc-types-mv-string-result)
      ("STRINGP-OF-KEYWORD-TREE-ALIST-TO-STRING" . b1-xdoc-types-string-result)
      ("TREEP-OF-MAKE-TREE-TAG" . b1-xdoc-types-tree-constructor)
      ("TREEP-OF-MAKE-TREE-DIR/&&" . b1-xdoc-types-tree-constructor)
      ("STRINGP-OF-DESC-THINGS-TO-STRING" . b1-xdoc-types-string-result)
      ("STRING-LISTP-OF-CODEBLOCK-TERMINATE-LINES" . b1-xdoc-types-escaped-list-type)
      ("INTEGERP-OF-LOGBITP-MISMATCH" . b1-bit-length-mismatch-is-integer)
      ("LOGBITP-MISMATCH-UNDER-IFF" . b1-mismatch-mismatch-exists)
      ("LOGBITP-MISMATCH-UPPER-BOUND" . b1-mismatch-mismatch-bound)
      ("LOGBITP-MISMATCH-UPPER-BOUND-FOR-NONNEGATIVES" . b1-mismatch-mismatch-bound)
      ("BFIX-BITP" . b1-fixer-laws-bit-fix-identity)
      ("MAYBE-BITP-COMPOUND-RECOGNIZER" . b1-fixer-laws-maybe-recognizer)
      ("MAYBE-INTEGERP-COMPOUND-RECOGNIZER" . b1-fixer-laws-maybe-recognizer)
      ("MAYBE-POSP-COMPOUND-RECOGNIZER" . b1-fixer-laws-maybe-recognizer)
      ("CHAREQV-IS-AN-EQUIVALENCE" . b1-fixer-laws-equality-equivalence)
      ("CHAREQV-IMPLIES-EQUAL-CHAR-FIX-1" . b1-fixer-laws-fixed-congruence)
      ("CHAREQV-IMPLIES-EQUAL-CHAR-CODE-1" . b1-fixer-laws-fixed-congruence)
      ("CHAREQV-IMPLIES-EQUAL-CHAR<-1" . b1-fixer-laws-fixed-congruence)
      ("CHAREQV-IMPLIES-EQUAL-CHAR<-2" . b1-fixer-laws-fixed-congruence)
      ("STREQV-IS-AN-EQUIVALENCE" . b1-fixer-laws-equality-equivalence)
      ("STREQV-IMPLIES-EQUAL-STR-FIX-1" . b1-fixer-laws-fixed-congruence)
      ("STREQV-IMPLIES-EQUAL-CHAR-1" . b1-fixer-laws-fixed-congruence)
      ("STREQV-IMPLIES-EQUAL-STRING-APPEND-1" . b1-fixer-laws-fixed-congruence)
      ("STREQV-IMPLIES-EQUAL-STRING-APPEND-2" . b1-fixer-laws-fixed-congruence))
    (b1-theorems-list-recipe-entries *b1-theorems-list-recipes*))
   (b1-theorems-bit-type-entries *b1-theorems-bit-types*)))

(defun b1-theorems-exponent-addition-nonpositive (lib formula)
  (b1-powers-exponent-addition-goal lib formula -1))

(defun b1-theorems-exponent-addition-nonnegative (lib formula)
  (b1-powers-exponent-addition-goal lib formula 1))

(defun b1-theorems-divide-by-inverted-sign (lib formula)
  (b1-division-divide-by-sign lib formula t))

(defun b1-theorems-negated-numerator (lib formula)
  (proof-with-checked-results
      ((left (proof-term-at formula 1))
       (negation (proof-term-at left 1))
       (argument (proof-term-at negation 1)))
    (b1-numerators-numerator-negation lib argument)))

(defun b1-theorems-helper-zero (lib formula)
  (b1-modular-exact-remainder-integral lib formula "HELPER-0-AUX"))

(defun b1-theorems-helper-one-auxiliary (lib formula)
  (b1-modular-exact-remainder-integral lib formula "HELPER-1-AUX"))

(defun b1-theorems-with-library (step lib)
  (if (failure-p step)
      step
    (cons step lib)))

(defun b1-theorems-apply-recipe-id (recipe lib formula index)
  (case recipe
    (b1-theorems-all-fnnames
     (b1-theorems-with-library (b1-theorems-all-fnnames lib formula) lib))
    (b1-theorems-complex-opener
     (b1-theorems-with-library (b1-theorems-complex-opener lib formula) lib))
    (b1-theorems-equal-of-predicates
     (b1-theorems-with-library (b1-theorems-equal-of-predicates lib formula) lib))
    (b1-theorems-linear-equalities
     (b1-theorems-with-library (b1-theorems-linear-equalities lib formula) lib))
    (b1-theorems-project-conjunct
     (b1-theorems-with-library (b1-theorems-project-conjunct lib formula) lib))
    (b1-structures-oracle-projection
     (b1-theorems-with-library (b1-structures-oracle-projection lib formula) lib))
    (b1-structures-pseudo-tail
     (b1-theorems-with-library (b1-structures-pseudo-tail lib formula) lib))
    (b1-structures-pseudo-lambda
     (b1-structures-pseudo-lambda lib formula))
    (b1-arithmetic-inverse-uniqueness
     (b1-theorems-with-library (b1-arithmetic-inverse-uniqueness lib formula) lib))
    (b1-reciprocal-above-one
     (b1-reciprocal-above-one lib formula))
    (b1-reciprocal-below-minus-one
     (b1-reciprocal-below-minus-one lib formula))
    (b1-reciprocal-integer-reciprocal
     (b1-reciprocal-integer-reciprocal lib formula))
    (b1-arithmetic-numerator-when-integer
     (b1-theorems-with-library (b1-arithmetic-numerator-when-integer lib formula) lib))
    (b1-reduced-numerator-minus
     (b1-reduced-numerator-minus lib formula))
    (b1-reduced-denominator-minus
     (b1-reduced-denominator-minus lib formula))
    (b1-arithmetic-denominator-when-integer
     (b1-theorems-with-library (b1-arithmetic-denominator-when-integer lib formula) lib))
    (b1-arithmetic-denominator-one
     (b1-theorems-with-library (b1-arithmetic-denominator-one lib formula) lib))
    (b1-arithmetic-times-denominator
     (b1-theorems-with-library (b1-arithmetic-times-denominator lib formula) lib))
    (b1-powers-exponent-addition-goal
     (b1-powers-exponent-addition-goal lib formula 0))
    (b1-theorems-exponent-addition-nonpositive
     (b1-theorems-exponent-addition-nonpositive lib formula))
    (b1-theorems-exponent-addition-nonnegative
     (b1-theorems-exponent-addition-nonnegative lib formula))
    (b1-powers-exponents-add-two
     (b1-powers-exponents-add-two lib formula))
    (b1-parity-even-power-positive
     (b1-parity-even-power-positive lib formula))
    (b1-parity-odd-power-negative
     (b1-parity-odd-power-negative lib formula))
    (b1-parity-negated-base
     (b1-parity-negated-base lib formula))
    (b1-monotone-increasing-power
     (b1-monotone-increasing-power lib formula))
    (b1-floor-rewrite-floor-mod
     (b1-floor-rewrite-floor-mod lib formula))
    (b1-floor-rewrite-mod-mod
     (b1-floor-rewrite-mod-mod lib formula))
    (b1-floor-sum-floor-sum
     (b1-floor-sum-floor-sum lib formula))
    (b1-floor-sum-mod-sum
     (b1-floor-sum-mod-sum lib formula))
    (b1-bitwise-logand-commutative
     (b1-bitwise-logand-commutative lib formula))
    (b1-bitwise-interchange-logand
     (b1-theorems-with-library (b1-bitwise-interchange-logand lib formula) lib))
    (b1-conjunction-full-conjunction
     (b1-conjunction-full-conjunction lib formula))
    (b1-conjunction-associated-conjunction
     (b1-conjunction-associated-conjunction lib formula))
    (b1-mod-expt-mod-expt-fast
     (b1-mod-expt-mod-expt-fast lib formula))
    (b1-permutation-permutation-is-equivalence
     (b1-permutation-permutation-is-equivalence lib formula))
    (b1-division-product-with-inverse
     (b1-theorems-with-library (b1-division-product-with-inverse lib formula) lib))
    (b1-division-multiply-division-equality
     (b1-theorems-with-library (b1-division-multiply-division-equality lib formula) lib))
    (b1-division-reciprocal-equality
     (b1-theorems-with-library (b1-division-reciprocal-equality lib formula) lib))
    (b1-division-divide-positive
     (b1-division-divide-positive lib formula))
    (b1-division-divide-by-sign
     (b1-division-divide-by-sign lib formula nil))
    (b1-theorems-divide-by-inverted-sign
     (b1-theorems-divide-by-inverted-sign lib formula))
    (b1-numerators-equal-numerator
     (b1-theorems-with-library (b1-numerators-equal-numerator lib formula) lib))
    (b1-numerators-negative-numerator
     (b1-numerators-negative-numerator lib formula))
    (b1-numerators-reciprocal-numerator
     (b1-numerators-reciprocal-numerator lib formula))
    (b1-theorems-negated-numerator
     (b1-theorems-negated-numerator lib formula))
    (b1-numerators-numerator-distribute-sign
     (b1-numerators-numerator-distribute-sign lib formula))
    (b1-numerators-numerator-upper-bound
     (b1-numerators-numerator-upper-bound lib formula))
    (b1-integer-open-unit-interval
     (b1-theorems-with-library (b1-integer-open-unit-interval lib formula) lib))
    (b1-integrality-half-shift
     (b1-integrality-half-shift lib formula))
    (b1-integrality-reflected-half
     (b1-integrality-reflected-half lib formula))
    (b1-integrality-negated-sum-integral
     (b1-integrality-negated-sum-integral lib formula))
    (b1-integrality-half-complement
     (b1-integrality-half-complement lib formula))
    (b1-integrality-half-choice
     (b1-integrality-half-choice lib formula))
    (b1-numerators-unit-denominator
     (b1-theorems-with-library (b1-numerators-unit-denominator lib formula) lib))
    (b1-modular-remainder-consequence
     (b1-modular-remainder-consequence lib formula))
    (b1-modular-exact-remainder-quotient
     (b1-modular-exact-remainder-quotient lib formula))
    (b1-theorems-helper-zero
     (b1-theorems-helper-zero lib formula))
    (b1-theorems-helper-one-auxiliary
     (b1-theorems-helper-one-auxiliary lib formula))
    (b1-integrality-increment-half
     (b1-integrality-increment-half lib formula))
    (b1-total-order-strict-irreflexive
     (b1-theorems-with-library (b1-total-order-strict-irreflexive lib formula) lib))
    (b1-total-order-strict-transitive
     (b1-theorems-with-library (b1-total-order-strict-transitive lib formula) lib))
    (b1-total-order-strict-asymmetric
     (b1-theorems-with-library (b1-total-order-strict-asymmetric lib formula) lib))
    (b1-total-order-strict-total
     (b1-theorems-with-library (b1-total-order-strict-total lib formula) lib))
    (b1-total-order-strict-implies-order
     (b1-theorems-with-library (b1-total-order-strict-implies-order lib formula) lib))
    (b1-lexical-fast-lexorder
     (b1-theorems-with-library (b1-lexical-fast-lexorder lib formula) lib))
    (b1-lexical-fast-strict-order
     (b1-lexical-fast-strict-order lib formula))
    (b1-list-sets-no-duplicate-append
     (b1-list-sets-no-duplicate-append lib formula))
    (b1-list-sets-intersect-append
     (b1-list-sets-intersect-append lib formula))
    (b1-structures-option-entry-tail
     (b1-theorems-with-library (b1-structures-option-entry-tail lib formula) lib))
    (b1-structures-open-mv-nth
     (b1-theorems-with-library (b1-structures-open-mv-nth lib formula) lib))
    (b1-arrays-header-exists
     (b1-theorems-with-library (b1-arrays-header-exists lib formula) lib))
    (b1-arrays-header-key
     (b1-arrays-header-key lib formula))
    (b1-arrays-array-forward-modular
     (b1-theorems-with-library (b1-arrays-array-forward-modular lib formula) lib))
    (b1-array-scan-valid-compressed-array
     (b1-array-scan-valid-compressed-array lib formula))
    (b1-arrays-compress-array-properties
     (b1-arrays-compress-array-properties lib formula))
    (b1-arrays-update-is-array
     (b1-theorems-with-library (b1-arrays-update-is-array lib formula) lib))
    (b1-arrays-update-array-properties
     (b1-theorems-with-library (b1-arrays-update-array-properties lib formula) lib))
    (b1-arrays-inserted-properties
     (b1-theorems-with-library (b1-arrays-inserted-properties lib formula) lib))
    (b1-arrays-read-updated-array
     (b1-theorems-with-library (b1-arrays-read-updated-array lib formula) lib))
    (b1-arrays-read-updated-array-cases
     (b1-theorems-with-library (b1-arrays-read-updated-array-cases lib formula) lib))
    (b1-array-scan-read-compressed-array
     (b1-array-scan-read-compressed-array lib formula))
    (b1-arrays-reset-contents
     (b1-arrays-reset-contents lib formula))
    (b1-arrays-reset-is-array
     (b1-arrays-reset-is-array lib formula))
    (b1-arrays-reset-properties
     (b1-arrays-reset-properties lib formula))
    (b1-arrays-read-reset-array
     (b1-arrays-read-reset-array lib formula))
    (b1-revappend-car-of-revappend
     (b1-theorems-with-library (b1-revappend-car-of-revappend lib formula) lib))
    (b1-revappend-consp-of-revappend
     (b1-theorems-with-library (b1-revappend-consp-of-revappend lib formula) lib))
    (b1-revappend-revappend-nonempty
     (b1-theorems-with-library (b1-revappend-revappend-nonempty lib formula) lib))
    (b1-revappend-accumulator-commutation
     (b1-theorems-with-library (b1-revappend-accumulator-commutation lib formula) lib))
    (b1-revappend-revappend-with-nil-accumulator
     (b1-theorems-with-library (b1-revappend-revappend-with-nil-accumulator lib formula) lib))
    (b1-revappend-length-of-revappend
     (b1-theorems-with-library (b1-revappend-length-of-revappend lib formula) lib))
    (b1-revappend-reversed-twice
     (b1-theorems-with-library (b1-revappend-reversed-twice lib formula) lib))
    (b1-revappend-revappend-of-list-fix
     (b1-theorems-with-library (b1-revappend-revappend-of-list-fix lib formula) lib))
    (b1-revappend-cdr-of-revappend
     (b1-theorems-with-library (b1-revappend-cdr-of-revappend lib formula) lib))
    (b1-revappend-count-of-revappend
     (b1-revappend-count-of-revappend lib formula))
    (b1-revappend-intersects-reversed-first
     (b1-theorems-with-library (b1-revappend-intersects-reversed-first lib formula) lib))
    (b1-revappend-intersects-reversed-second
     (b1-revappend-intersects-reversed-second lib formula))
    (b1-revappend-member-of-revappend
     (b1-revappend-member-of-revappend lib formula))
    (b1-revappend-reverse-not-unchanged
     (b1-theorems-with-library (b1-revappend-reverse-not-unchanged lib formula) lib))
    (b1-revappend-revappend-pair-equality
     (b1-theorems-with-library (b1-revappend-revappend-pair-equality lib formula) lib))
    (b1-list-types-numeric-fold-type
     (b1-theorems-with-library (b1-list-types-numeric-fold-type lib formula) lib))
    (b1-list-types-natural-excess
     (b1-list-types-natural-excess lib formula))
    (b1-list-types-numeric-insert-type
     (b1-theorems-with-library (b1-list-types-numeric-insert-type lib formula) lib))
    (b1-list-types-numeric-sort-type
     (b1-theorems-with-library (b1-list-types-numeric-sort-type lib formula) lib))
    (b1-membership-member-nil
     (b1-theorems-with-library (b1-membership-member-nil lib formula) lib))
    (b1-membership-member-from-tail
     (b1-theorems-with-library (b1-membership-member-from-tail lib formula) lib))
    (b1-membership-member-of-fixed-list
     (b1-membership-member-of-fixed-list lib formula))
    (b1-membership-member-of-fixed-list-iff
     (b1-theorems-with-library (b1-membership-member-of-fixed-list-iff lib formula) lib))
    (b1-membership-member-of-suffix
     (b1-theorems-with-library (b1-membership-member-of-suffix lib formula) lib))
    (b1-membership-member-of-set-operation
     (b1-theorems-with-library (b1-membership-member-of-set-operation lib formula) lib))
    (b1-membership-member-after-removal-iff
     (b1-theorems-with-library (b1-membership-member-after-removal-iff lib formula) lib))
    (b1-membership-member-requires-cons
     (b1-theorems-with-library (b1-membership-member-requires-cons lib formula) lib))
    (b1-membership-member-proper
     (b1-theorems-with-library (b1-membership-member-proper lib formula) lib))
    (b1-membership-member-contrapositive
     (b1-theorems-with-library (b1-membership-member-contrapositive lib formula) lib))
    (b1-membership-membership-head-step
     (b1-theorems-with-library (b1-membership-membership-head-step lib formula) lib))
    (b1-membership-singleton-member
     (b1-theorems-with-library (b1-membership-singleton-member lib formula) lib))
    (b1-membership-member-at-index
     (b1-membership-member-at-index lib formula))
    (b1-membership-member-of-singleton-length
     (b1-theorems-with-library (b1-membership-member-of-singleton-length lib formula) lib))
    (b1-set-laws-subset-of-extension
     (b1-set-laws-subset-of-extension lib formula))
    (b1-set-laws-subset-reflexive
     (b1-theorems-with-library (b1-set-laws-subset-reflexive lib formula) lib))
    (b1-set-laws-subset-transitive
     (b1-set-laws-subset-transitive lib formula))
    (b1-set-laws-subset-append-singleton
     (b1-theorems-with-library (b1-set-laws-subset-append-singleton lib formula) lib))
    (b1-set-laws-subset-adjoin
     (b1-set-laws-subset-adjoin lib formula))
    (b1-set-laws-subset-of-set-operation
     (b1-set-laws-subset-of-set-operation lib formula))
    (b1-set-laws-set-equal-law
     (b1-theorems-with-library (b1-set-laws-set-equal-law lib formula) lib))
    (b1-set-laws-memberp-subset
     (b1-set-laws-memberp-subset lib formula))
    (b1-set-laws-memberp-set-equal
     (b1-theorems-with-library (b1-set-laws-memberp-set-equal lib formula) lib))
    (b1-set-laws-memberp-of-set-operation
     (b1-set-laws-memberp-of-set-operation lib formula))
    (b1-set-laws-setp-cons
     (b1-set-laws-setp-cons lib formula))
    (b1-set-laws-setp-adjoin
     (b1-set-laws-setp-adjoin lib formula))
    (b1-set-laws-setp-under-operation
     (b1-set-laws-setp-under-operation lib formula))
    (b1-set-laws-subset-filter-identity
     (b1-theorems-with-library (b1-set-laws-subset-filter-identity lib formula) lib))
    (b1-set-laws-difference-of-redundant-cons
     (b1-theorems-with-library (b1-set-laws-difference-of-redundant-cons lib formula) lib))
    (b1-set-laws-difference-of-disjoint
     (b1-theorems-with-library (b1-set-laws-difference-of-disjoint lib formula) lib))
    (b1-set-laws-no-duplicates-append
     (b1-set-laws-no-duplicates-append lib formula))
    (b1-set-laws-setp-append
     (b1-theorems-with-library (b1-set-laws-setp-append lib formula) lib))
    (b1-fixtypes-split-result-proper
     (b1-theorems-with-library (b1-fixtypes-split-result-proper lib formula) lib))
    (b1-printing-pack-character-lists
     (b1-printing-pack-character-lists lib formula))
    (b1-fixtypes-product-selector
     (b1-theorems-with-library (b1-fixtypes-product-selector lib formula) lib))
    (b1-fixtypes-product-reconstruction
     (b1-theorems-with-library (b1-fixtypes-product-reconstruction lib formula) lib))
    (b1-fixtypes-product-equality
     (b1-theorems-with-library (b1-fixtypes-product-equality lib formula) lib))
    (b1-fixtypes-product-size
     (b1-fixtypes-product-size lib formula))
    (b1-fixtypes-product-against-cons
     (b1-theorems-with-library (b1-fixtypes-product-against-cons lib formula) lib))
    (b1-fixtypes-product-empty
     (b1-theorems-with-library (b1-fixtypes-product-empty lib formula) lib))
    (b1-fixtypes-tag-implies-cons
     (b1-theorems-with-library (b1-fixtypes-tag-implies-cons lib formula) lib))
    (b1-fixtypes-lookup-result-type
     (b1-theorems-with-library (b1-fixtypes-lookup-result-type lib formula) lib))
    (b1-fixtypes-mv-nth-of-cons
     (b1-theorems-with-library (b1-fixtypes-mv-nth-of-cons lib formula) lib))
    (b1-fixtypes-identity-processor-wellformed
     (b1-theorems-with-library (b1-fixtypes-identity-processor-wellformed lib formula) lib))
    (b1-fixtypes-identity-processor-correct
     (b1-theorems-with-library (b1-fixtypes-identity-processor-correct lib formula) lib))
    (b1-clause-processors-mv-nth-evaluation-recursion
     (b1-clause-processors-mv-nth-evaluation-recursion lib formula))
    (b1-clause-processors-mv-nth-evaluation-meta
     (b1-theorems-with-library (b1-clause-processors-mv-nth-evaluation-meta lib formula) lib))
    (b1-clause-processors-flag-processor-wellformed
     (b1-theorems-with-library (b1-clause-processors-flag-processor-wellformed lib formula) lib))
    (b1-clause-processors-flag-processor-correct
     (b1-theorems-with-library (b1-clause-processors-flag-processor-correct lib formula) lib))
    (b1-typed-alists-alist-type-is-alist
     (b1-theorems-with-library (b1-typed-alists-alist-type-is-alist lib formula) lib))
    (b1-typed-alists-alist-type-acons
     (b1-theorems-with-library (b1-typed-alists-alist-type-acons lib formula) lib))
    (b1-typed-alists-typed-alist-recursion
     (b1-theorems-with-library (b1-typed-alists-typed-alist-recursion lib formula) lib))
    (b1-typed-alists-paired-alist-type
     (b1-theorems-with-library (b1-typed-alists-paired-alist-type lib formula) lib))
    (b1-typed-alists-typed-alist-lookup
     (b1-theorems-with-library (b1-typed-alists-typed-alist-lookup lib formula) lib))
    (b1-typed-alists-alist-bound-requires-key
     (b1-theorems-with-library (b1-typed-alists-alist-bound-requires-key lib formula) lib))
    (b1-typed-alists-all-bound-requires-keys
     (b1-theorems-with-library (b1-typed-alists-all-bound-requires-keys lib formula) lib))
    (b1-typed-alists-alist-type-binding
     (b1-typed-alists-alist-type-binding lib formula))
    (b1-typed-alists-range-of-association
     (b1-typed-alists-range-of-association lib formula))
    (b1-typed-alists-alist-projection-type
     (b1-theorems-with-library (b1-typed-alists-alist-projection-type lib formula) lib))
    (b1-typed-alists-types-of-bound-entries
     (b1-theorems-with-library (b1-typed-alists-types-of-bound-entries lib formula) lib))
    (b1-xdoc-types-string-result
     (b1-theorems-with-library (b1-xdoc-types-string-result lib formula) lib))
    (b1-xdoc-types-escaped-list-type
     (b1-xdoc-types-escaped-list-type lib formula))
    (b1-xdoc-types-partition-macro-args
     (b1-xdoc-types-partition-macro-args lib formula))
    (b1-xdoc-types-list-type-implication
     (b1-theorems-with-library (b1-xdoc-types-list-type-implication lib formula) lib))
    (b1-xdoc-types-tree-cons
     (b1-theorems-with-library (b1-xdoc-types-tree-cons lib formula) lib))
    (b1-xdoc-types-tree-alist-cons
     (b1-theorems-with-library (b1-xdoc-types-tree-alist-cons lib formula) lib))
    (b1-xdoc-types-mv-string-result
     (b1-theorems-with-library (b1-xdoc-types-mv-string-result lib formula) lib))
    (b1-xdoc-types-tree-constructor
     (b1-theorems-with-library (b1-xdoc-types-tree-constructor lib formula) lib))
    (b1-bit-length-mismatch-is-integer
     (b1-bit-length-mismatch-is-integer lib formula))
    (b1-mismatch-mismatch-exists
     (b1-mismatch-mismatch-exists lib formula))
    (b1-mismatch-mismatch-bound
     (b1-mismatch-mismatch-bound lib formula))
    (b1-fixer-laws-bit-fix-identity
     (b1-theorems-with-library (b1-fixer-laws-bit-fix-identity lib formula) lib))
    (b1-fixer-laws-maybe-recognizer
     (b1-theorems-with-library (b1-fixer-laws-maybe-recognizer lib formula) lib))
    (b1-fixer-laws-equality-equivalence
     (b1-theorems-with-library (b1-fixer-laws-equality-equivalence lib formula) lib))
    (b1-fixer-laws-fixed-congruence
     (b1-theorems-with-library (b1-fixer-laws-fixed-congruence lib formula) lib))
    (b1-abstract-lists-abstract-list-proper
     (b1-theorems-with-library (b1-abstract-lists-abstract-list-proper lib formula index) lib))
    (b1-abstract-lists-abstract-list-cons
     (b1-theorems-with-library (b1-abstract-lists-abstract-list-cons lib formula index) lib))
    (b1-abstract-lists-abstract-list-car
     (b1-theorems-with-library (b1-abstract-lists-abstract-list-car lib formula index) lib))
    (b1-abstract-lists-abstract-list-cdr
     (b1-theorems-with-library (b1-abstract-lists-abstract-list-cdr lib formula index) lib))
    (b1-abstract-lists-abstract-list-member
     (b1-theorems-with-library (b1-abstract-lists-abstract-list-member lib formula index) lib))
    (b1-abstract-lists-abstract-list-memberp
     (b1-abstract-lists-abstract-list-memberp lib formula index))
    (b1-abstract-lists-abstract-list-append
     (b1-theorems-with-library (b1-abstract-lists-abstract-list-append lib formula index) lib))
    (b1-abstract-lists-reuse-abstract-list
     (b1-theorems-with-library (b1-abstract-lists-reuse-abstract-list lib formula index) lib))
    (b1-abstract-lists-abstract-list-reverse
     (b1-theorems-with-library (b1-abstract-lists-abstract-list-reverse lib formula index) lib))
    (b1-abstract-lists-abstract-list-nthcdr
     (b1-theorems-with-library (b1-abstract-lists-abstract-list-nthcdr lib formula index) lib))
    (b1-abstract-lists-abstract-make-list
     (b1-theorems-with-library (b1-abstract-lists-abstract-make-list lib formula index) lib))
    (b1-abstract-lists-abstract-list-initial-sublist
     (b1-theorems-with-library (b1-abstract-lists-abstract-list-initial-sublist lib formula index) lib))
    (b1-abstract-lists-abstract-list-put-nth
     (b1-abstract-lists-abstract-list-put-nth lib formula index))
    (b1-abstract-lists-abstract-list-bounded-operation
     (b1-abstract-lists-abstract-list-bounded-operation lib formula index))
    (b1-abstract-lists-abstract-list-butlast
     (b1-abstract-lists-abstract-list-butlast-with-library lib formula index))
    (b1-abstract-lists-abstract-list-subseq
     (b1-abstract-lists-abstract-list-subseq lib formula index))
    (b1-abstract-lists-abstract-list-nth
     (b1-abstract-lists-abstract-list-nth lib formula index))
    (b1-bit-types-bit-operation-type
     (b1-bit-types-bit-operation-type lib formula))
    (otherwise '(:failure "failure" ""))))

(defun b1-theorems-apply-recipe-with-index (label lib formula index)
  (let ((recipe (assoc-equal label *b1-theorems-recipes*)))
    (if recipe
        (b1-theorems-apply-recipe-id (cdr recipe) lib formula index)
      '(:failure "failure" ""))))

(defun b1-theorems-apply-recipe (label lib formula)
  (b1-theorems-apply-recipe-with-index label lib formula nil))
