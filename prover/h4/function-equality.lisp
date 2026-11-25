(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h4-function-equality-apply* (proof-sym "APPLY$" "ACL2"))
(defconst *h4-function-equality-apply-equivalence* (proof-sym "APPLY$-EQUIVALENCE" "ACL2"))
(defconst *h4-function-equality-apply-witness* (proof-sym "APPLY$-EQUIVALENCE-WITNESS" "ACL2"))
(defconst *h4-function-equality-apply-definition* (proof-sym "APPLY$-EQUIVALENCE definition" "ACL2"))
(defconst *h4-function-equality-apply-necessity* (proof-sym "APPLY$-EQUIVALENCE-NECC" "ACL2"))
(defconst *h4-function-equality-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *h4-function-equality-fn-equal* (proof-sym "FN-EQUAL" "ACL2"))
(defconst *h4-function-equality-fn1* (proof-sym "FN1" "ACL2"))
(defconst *h4-function-equality-fn2* (proof-sym "FN2" "ACL2"))
(defconst *h4-function-equality-args* (proof-sym "ARGS" "ACL2"))

(defun h4-function-equality-from-contrapositive (p step evidence)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((literal (proof-step-first step))
      (premise (proof-term-at literal 1))
      (hypothesis (proof-term-at premise 1))
      (assumed (proof-proof-assume proof hypothesis nil))
      (negative (h4-book-flatten-modus-ponens p step assumed))
      (result (proof-proof-cut proof evidence negative)))
     (proof-proof-front proof result hypothesis))))

(defun h4-function-equality-apply-at (p equivalence arguments)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((literal (proof-step-first equivalence))
      (parts (proof-list-of-length literal 3))
      (necessity (proof-proof-fact proof *h4-function-equality-apply-necessity*
                                  (list (list *h4-function-equality-fn1* (cadr parts))
                                        (list *h4-function-equality-fn2* (caddr parts))
                                        (list *h4-function-equality-args* arguments))))
      (literal (proof-step-first necessity))
      (test (proof-term-at literal 1))
      (normalized (h4-book-flatten-normalize p test nil nil nil))
      (necessity (proof-proof-rewrite proof necessity normalized '(1 1))))
     (h4-function-equality-from-contrapositive p necessity equivalence))))

(defun h4-function-equality-definition (p left right)
  (proof-proof-fact (library-library-proof p) *h4-function-equality-apply-definition*
                   (list (list *h4-function-equality-fn1* left)
                         (list *h4-function-equality-fn2* right))))

(defun h4-function-equality-open-definition (p definition)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((body (h4-book-flatten-step-right definition))
      (beta (proof-proof-beta proof body)))
     (proof-proof-chain proof definition (list beta)))))

(defun h4-function-equality-apply-equivalence-finish (p definition checked)
  (proof-with-checked-results
   ((checked checked)
    (equality (h4-function-equality-open-definition p definition)))
   (proof-proof-transport (library-library-proof p) checked equality)))

(defun h4-function-equality-unequal-functions (p equivalence unequal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((literal (proof-step-first equivalence))
      (definition (proof-proof-unfold proof literal))
      (opened (proof-proof-rewrite proof equivalence definition '(1)))
      (opened (proof-proof-prove-if proof opened unequal))
      (first-and-rest (h4-book-flatten-conjunct p opened))
      (second-and-extensional (h4-book-flatten-conjunct p (cadr first-and-rest))))
     (cons (car first-and-rest) second-and-extensional))))

(defun h4-function-equality-introduce-fn-equal (p left right evidence)
  (let* ((proof (library-library-proof p))
         (formula (list *h4-function-equality-fn-equal* left right))
         (test (proof-eq left right))
         (expand (list *h4-function-equality-fn-equal*)))
    (proof-with-checked-results
     ((same (proof-proof-assume proof test t))
      (yes (h4-book-flatten-establish p formula (list same) expand nil))
      (different (proof-proof-assume proof test nil))
      (no (h4-book-flatten-establish p formula (cons different evidence) expand nil)))
     (h4-book-flatten-case-of p formula test yes no))))

(defun h4-function-equality-pointwise-lemma (p)
  (let* ((proof (library-library-proof p))
         (fn-equal (list *h4-function-equality-fn-equal*
                         *h4-function-equality-fn1* *h4-function-equality-fn2*))
         (left (list *h4-function-equality-apply*
                     *h4-function-equality-fn1* *h4-function-equality-args*))
         (right (list *h4-function-equality-apply*
                      *h4-function-equality-fn2* *h4-function-equality-args*))
         (goal (proof-eq left right))
         (test (proof-eq *h4-function-equality-fn1* *h4-function-equality-fn2*)))
    (proof-with-checked-results
     ((premise (proof-proof-assume proof fn-equal t))
      (same (proof-proof-assume proof test t))
      (reflexive (proof-proof-reflexive proof left))
      (yes (proof-proof-rewrite proof reflexive same '(1 2 1)))
      (different (proof-proof-assume proof test nil))
      (parts (h4-function-equality-unequal-functions p premise different))
      (no (h4-function-equality-apply-at p (caddr parts) *h4-function-equality-args*))
      (step (h4-book-flatten-case-of p goal test yes no)))
     (h4-association-local-lemma p "FN-EQUAL-AT-ARGUMENTS" step))))

(defconst *h4-function-equality-boolean-definitions*
  (list *h4-function-equality-booleanp* (proof-cl "EQ")))

(defun h4-function-equality-boolean (p value)
  (h4-book-flatten-establish p (list *h4-function-equality-booleanp* value)
                             nil *h4-function-equality-boolean-definitions* nil))

(defun h4-function-equality-boolean-after (value-equality p)
  (proof-with-checked-results
   ((value (h4-book-flatten-step-right value-equality))
    (boolean (h4-function-equality-boolean p value)))
   (library-library-transport-argument p boolean value-equality 1)))

(defun h4-function-equality-boolean-value (value p)
  (if (member-equal value (list *proof-true* *proof-false*))
      (h4-function-equality-boolean p value)
    (let ((proof (library-library-proof p)))
      (proof-with-checked-results
       ((parts (proof-list-of-length value 3))
        (definition (h4-function-equality-definition p (cadr parts) (caddr parts)))
        (equality (h4-function-equality-open-definition p definition))
        (test (h4-book-flatten-step-right equality))
        (same (proof-proof-assume proof test t))
        (left (proof-term-at test 1))
        (equal-same (proof-proof-fact proof "equal-same" (list (list *library-x* left))))
        (value-equality (proof-proof-rewrite proof equal-same same '(1 1 2)))
        (yes (h4-function-equality-boolean-after value-equality p))
        (different (proof-proof-assume proof test nil))
        (value-equality (h4-book-flatten-nil-value p different))
        (no (h4-function-equality-boolean-after value-equality p))
        (result (h4-book-flatten-case-of p (list *h4-function-equality-booleanp* test)
                                         test yes no)))
       (library-library-transport-argument p result equality 1)))))

(defun h4-function-equality-boolean-by-value (n p value)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h4-function-equality-boolean-by-value")
    (let ((proof (library-library-proof p))
          (template (list *h4-function-equality-booleanp* *proof-result*)))
      (cond
       ((proof-is-call value *proof-if*)
        (proof-with-checked-results
         ((branches (proof-list-of-length (cdr value) 3))
          (yes (h4-function-equality-boolean-by-value (1- n) p (cadr branches)))
          (no (h4-function-equality-boolean-by-value (1- n) p (caddr branches))))
         (proof-by-value-join proof value template yes no)))
       ((and (proof-compound value) (endp value)) '(:failure "failure" ""))
       ((and (proof-compound value) (proof-compound (car value)))
        (proof-with-checked-results
         ((equality (proof-proof-beta proof value))
          (body (h4-book-flatten-step-right equality))
          (opened (h4-function-equality-boolean-by-value (1- n) p body))
          (symmetric (proof-proof-symmetric proof equality)))
         (proof-proof-rewrite-result proof opened symmetric template *proof-result*)))
       (t (proof-with-checked-results
           ((step (h4-function-equality-boolean-value value p))
            (first (proof-step-first step)))
           (if (equal first (list *h4-function-equality-booleanp* value))
               step
             '(:failure "failure" ""))))))))

(defun h4-function-equality-reverse-extensional (different p xy)
  (let* ((proof (library-library-proof p))
         (witness (list *h4-function-equality-apply-witness* *library-y* *library-x*)))
    (proof-with-checked-results
     ((parts (h4-function-equality-unequal-functions p xy different))
      (definition (h4-function-equality-definition p *library-y* *library-x*))
      (at-witness (h4-function-equality-apply-at p (caddr parts) witness))
      (checked (proof-proof-symmetric proof at-witness))
      (result (h4-function-equality-apply-equivalence-finish p definition checked)))
     (h4-function-equality-introduce-fn-equal
      p *library-y* *library-x* (list (cadr parts) (car parts) result)))))

(defun h4-function-equality-reverse (p formula)
  (let* ((proof (library-library-proof p))
         (test (proof-eq *library-x* *library-y*)))
    (proof-with-checked-results
     ((premise (proof-term-at formula 1))
      (xy (proof-proof-assume proof premise t))
      (goal (proof-term-at formula 2))
      (same (proof-proof-assume proof test t))
      (same (proof-proof-symmetric proof same))
      (yes (h4-book-flatten-establish p goal (list same)
                                      (list *h4-function-equality-fn-equal*) nil))
      (different (proof-proof-assume proof test nil))
      (no (h4-function-equality-reverse-extensional different p xy))
      (result (h4-book-flatten-case-of p goal test yes no)))
     (h4-book-flatten-imply p formula result))))

(defun h4-function-equality-compose-extensional (x-not-y y-not-z p xy yz)
  (let* ((proof (library-library-proof p))
         (witness (list *h4-function-equality-apply-witness* *library-x* *library-z*)))
    (proof-with-checked-results
     ((left (h4-function-equality-unequal-functions p xy x-not-y))
      (right (h4-function-equality-unequal-functions p yz y-not-z))
      (definition (h4-function-equality-definition p *library-x* *library-z*))
      (first (h4-function-equality-apply-at p (caddr left) witness))
      (second (h4-function-equality-apply-at p (caddr right) witness))
      (checked (proof-proof-chain proof first (list second)))
      (result (h4-function-equality-apply-equivalence-finish p definition checked)))
     (h4-function-equality-introduce-fn-equal
      p *library-x* *library-z* (list (car left) (cadr right) result)))))

(defun h4-function-equality-compose-right (p goal x-not-y xy yz)
  (let* ((proof (library-library-proof p))
         (test (proof-eq *library-y* *library-z*)))
    (proof-with-checked-results
     ((same (proof-proof-assume proof test t))
      (yes (proof-proof-rewrite proof xy same '(1 2)))
      (different (proof-proof-assume proof test nil))
      (no (h4-function-equality-compose-extensional x-not-y different p xy yz)))
     (h4-book-flatten-case-of p goal test yes no))))

(defun h4-function-equality-compose (p formula)
  (let* ((proof (library-library-proof p))
         (test (proof-eq *library-x* *library-y*)))
    (proof-with-checked-results
     ((premise (proof-term-at formula 1))
      (assumed (proof-proof-assume proof premise t))
      (conjuncts (h4-book-flatten-conjunct p assumed))
      (goal (proof-term-at formula 2))
      (same (proof-proof-assume proof test t))
      (same (proof-proof-symmetric proof same))
      (yes (proof-proof-rewrite proof (cadr conjuncts) same '(1 1)))
      (different (proof-proof-assume proof test nil))
      (no (h4-function-equality-compose-right p goal different (car conjuncts) (cadr conjuncts)))
      (result (h4-book-flatten-case-of p goal test yes no)))
     (h4-book-flatten-imply p formula result))))

(defun h4-function-equality-fn-equal-is-equivalence (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((parts (proof-list-of-length (seq-slice formula 1 3) 2))
      (boolean (proof-term-at (car parts) 1))
      (definition (proof-proof-unfold proof boolean))
      (body (h4-book-flatten-step-right definition))
      (subtype (h4-function-equality-boolean-by-value 1000000 p body))
      (subtype (library-library-transport-argument p subtype definition 1))
      (rest (cadr parts))
      (parts (proof-list-of-length (seq-slice rest 1 3) 2))
      (identity (h4-book-flatten-establish p (car parts) nil
                                          (list *h4-function-equality-fn-equal*) nil))
      (rest2 (cadr parts))
      (parts (proof-list-of-length (seq-slice rest2 1 3) 2))
      (reversed (h4-function-equality-reverse p (car parts)))
      (transitive (h4-function-equality-compose p (cadr parts)))
      (last (h4-book-flatten-conjunction p rest2 reversed transitive))
      (properties (h4-book-flatten-conjunction p rest identity last)))
     (h4-book-flatten-conjunction p formula subtype properties))))

(defun h4-function-equality-caller-congruence-init (p formula measure descent)
  (proof-with-checked-results
   ((premise (proof-term-at formula 1))
    (assumed (proof-proof-assume (library-library-proof p) premise t))
    (functions (proof-list-of-length (cdr premise) 2))
    (goal (proof-term-at formula 2))
    (call (proof-term-at goal 1)))
   (list :h4-function-equality-caller-congruence
         p formula measure descent assumed (car functions) (cadr functions)
         call nil nil)))

(defun h4-function-equality-caller-congruence-p (caller)
  (nth 1 caller))

(defun h4-function-equality-caller-congruence-formula (caller)
  (nth 2 caller))

(defun h4-function-equality-caller-congruence-measure (caller)
  (nth 3 caller))

(defun h4-function-equality-caller-congruence-descent (caller)
  (nth 4 caller))

(defun h4-function-equality-caller-congruence-premise (caller)
  (nth 5 caller))

(defun h4-function-equality-caller-congruence-left-function (caller)
  (nth 6 caller))

(defun h4-function-equality-caller-congruence-right-function (caller)
  (nth 7 caller))

(defun h4-function-equality-caller-congruence-call (caller)
  (nth 8 caller))

(defun h4-function-equality-caller-congruence-substitutions (caller)
  (nth 9 caller))

(defun h4-function-equality-caller-congruence-pointwise (caller)
  (nth 10 caller))

(defun h4-function-equality-descent-request-p (result)
  (and (consp result) (eq (car result) :h4-function-equality-descent-request)))

(defmacro h4-function-equality-with-results (bindings body)
  (if (endp bindings)
      body
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (or (failure-p ,name) (h4-function-equality-descent-request-p ,name))
             ,name
           (h4-function-equality-with-results ,(cdr bindings) ,body))))))

; Build the arithmetic support with the Library's H4 propositional rules.

(defun h4-function-equality-build-integer-closure-lemmas (library both recipes)
  (declare (xargs :measure (acl2-count recipes)))
  (if (endp recipes)
      library
    (let* ((recipe (car recipes))
           (head (car recipe))
           (axiom (cadr recipe))
           (name (caddr recipe))
           (x *library-x*)
           (y *library-y*))
      (proof-with-checked-results
       ((fact (library-inherited proof-proof-fact library axiom nil))
        (step (h4-book-flatten-modus-ponens library fact both))
        (library (library-library-lemma library name (library-integer (list head x y)) step
                                        (library-guards (list (library-integer x)
                                                              (library-integer y))))))
       (h4-function-equality-build-integer-closure-lemmas library both (cdr recipes))))))

(defun h4-function-equality-build-logic-and-types (library)
  (let* ((x *library-x*)
         (y *library-y*)
         (z *library-z*)
         (conditional (proof-ite x y z))
         (integer-x (library-integer x))
         (integer-y (library-integer y))
         (nat (list *library-natp* x))
         (cons-test (list *proof-consp* x))
         (ordinal (list *proof-ordinalp* x))
         (ordinal-lt (list *proof-ordinal-less* x y))
         (nfix (list *library-nfix* x))
         (gap (list *library-gap* x y)))
    (proof-with-checked-results
     ((middle (library-inherited proof-proof-excluded-middle library x))
      (library (library-library-lemma library "EXCLUDED-MIDDLE" (proof-neg x) middle (list x)))
      (when-false (library-inherited proof-proof-if-false library conditional))
      (library (library-library-lemma library "IF-FALSE" (proof-eq conditional z) when-false (list x)))
      (when-true (library-inherited proof-proof-if-true library conditional))
      (library (library-library-lemma library "IF-TRUE" (proof-eq conditional y) when-true
                                      (list (proof-neg x))))
      (integers (library-library-ints library (list x y)))
      (both (library-inherited h4-book-measures-prove library
                               (proof-ite integer-x integer-y *proof-false*) integers nil))
      (library (h4-function-equality-build-integer-closure-lemmas
                library both (list (list *proof-plus* "integerp-binary-+" "INTEGER-SUM")
                                   (list *proof-times* "integerp-binary-*" "INTEGER-PRODUCT"))))
      (negation (library-inherited proof-proof-fact library "integerp-unary--" nil))
      (step (h4-book-flatten-modus-ponens library negation (car integers)))
      (library (library-library-lemma library "INTEGER-NEGATION" (library-integer (library-minus x))
                                      step (list (proof-neg integer-x))))

      (nat-hyp (library-inherited proof-proof-assume library nat t))
      (opened (library-inherited proof-proof-unfold library nat))
      (nat-open (library-inherited proof-proof-rewrite library nat-hyp opened '(1)))
      (nat-parts (h4-book-flatten-conjunct library nat-open))
      (library (library-library-lemma library "NATURAL-INTEGER" integer-x (car nat-parts)
                                      (list (proof-neg nat))))
      (library (library-library-lemma library "NATURAL-NONNEGATIVE" (library-nonnegative x)
                                      (cadr nat-parts) (list (proof-neg nat))))
      (neg-x (library-inherited proof-proof-assume library (library-lt x *proof-zero*) nil))
      (bounded (library-inherited h4-book-measures-prove library nat (list (car integers) neg-x)
                                  (list *library-natp*)))
      (library (library-library-lemma library "NATURAL-FROM-BOUNDS" nat bounded
                                      (list (proof-neg integer-x) (library-lt x *proof-zero*))))

      (consp-fact (library-inherited proof-proof-fact library "consp-not-acl2-numberp" nil))
      (consp-hyp (library-inherited proof-proof-assume library cons-test t))
      (nonnumber (h4-book-flatten-modus-ponens library consp-fact consp-hyp))
      (numeric (library-inherited proof-proof-assume library (list *library-numberp* x) t))
      (finite (library-inherited proof-proof-cut library numeric nonnumber))
      (finite (library-inherited proof-proof-front library finite (proof-neg cons-test)))
      (number-finite (library-inherited h4-book-measures-prove library (list *library-o-finp* x)
                                        (list finite) (list *library-o-finp* (proof-cl "ATOM"))))
      (numeric-first (proof-step-first numeric))
      (library (library-library-lemma library "NUMBER-FINITE" (list *library-o-finp* x)
                                      number-finite (list (proof-neg numeric-first))))
      (number-x (h4-association-number library x (list (car integers))))
      (integer-finite (library-library-cite library "NUMBER-FINITE" (list x) (list number-x)))
      (library (library-library-lemma library "INTEGER-FINITE" (list *library-o-finp* x)
                                      integer-finite (list (proof-neg integer-x))))

      (x-finite (library-library-cite library "INTEGER-FINITE" (list x) (list (car nat-parts))))
      (natural-ordinal (library-inherited h4-book-measures-prove library ordinal (list x-finite nat-hyp)
                                          (list *proof-ordinalp*)))
      (library (library-library-lemma library "NATURAL-ORDINAL" ordinal natural-ordinal
                                      (list (proof-neg nat))))
      (x-finite (library-library-cite library "INTEGER-FINITE" (list x) (list (car integers))))
      (y-finite (library-library-cite library "INTEGER-FINITE" (list y) (list (cadr integers))))
      (finite-order (library-inherited h4-book-measures-simplify library ordinal-lt (list x-finite y-finite)
                                       (list *proof-ordinal-less* *proof-not*)))
      (library (library-library-lemma library "FINITE-ORDER" (proof-eq ordinal-lt (library-lt x y))
                                      finite-order (library-guards (list integer-x integer-y))))

      (library (library-library-definition library *library-nfix* (list x) (proof-ite nat x *proof-zero*)))
      (good-eq (library-inherited h4-book-measures-simplify library nfix (list nat-hyp) (list *library-nfix*)))
      (good (library-library-transport-argument library nat-hyp good-eq 1))
      (zero-natural (library-inherited h4-book-measures-prove library (list *library-natp* *proof-zero*)
                                        nil (list *library-natp* *proof-not*)))
      (not-natural (library-inherited proof-proof-assume library nat nil))
      (bad-eq (library-inherited h4-book-measures-simplify library nfix (list not-natural) (list *library-nfix*)))
      (bad (library-library-transport-argument library zero-natural bad-eq 1))
      (cases (library-inherited proof-proof-cases library nat good bad))
      (library (library-library-lemma library "NFIX-NATURAL" (list *library-natp* nfix) cases nil))
      (fixed (library-inherited proof-proof-fact library (library-lemma-name "NFIX-NATURAL") nil))
      (nfix-integer (library-library-cite library "NATURAL-INTEGER" (list nfix) (list fixed)))
      (library (library-library-lemma library "NFIX-INTEGER" (library-integer nfix) nfix-integer nil))
      (nfix-ordinal (library-library-cite library "NATURAL-ORDINAL" (list nfix) (list fixed)))
      (library (library-library-lemma library "NFIX-ORDINAL" (list *proof-ordinalp* nfix) nfix-ordinal nil))
      (library (library-library-definition library *library-gap* (list x y)
                                           (list *library-nfix* (library-diff x y))))
      (difference-ordinal (library-library-cite library "NFIX-ORDINAL" (list (library-diff x y)) nil))
      (opened (library-inherited proof-proof-unfold library gap))
      (gap-ordinal (library-library-transport-argument library difference-ordinal opened 1)))
     (library-library-lemma library "GAP-ORDINAL" (list *proof-ordinalp* gap) gap-ordinal nil))))

(defun h4-function-equality-build-additive-identities (library)
  (let ((x *library-x*)
        (y *library-y*)
        (z *library-z*)
        (zero *proof-zero*)
        (fix (proof-sym "FIX" "ACL2")))
    (proof-with-checked-results
     ((ints (library-library-ints library (list x)))
      (left-zero (library-library-axiom library "UNICITY-OF-0" (list x)))
      (x-number (h4-association-number library x ints))
      (fixed (library-inherited h4-book-measures-simplify library (list fix x) (list x-number) (list fix)))
      (left-zero (library-inherited proof-proof-chain library left-zero (list fixed)))
      (library (library-library-lemma library "ADD-ZERO-LEFT" (proof-eq (library-plus zero x) x)
                                      left-zero (list (proof-neg (library-integer x)))))
      (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list x zero)))
      (right-zero (library-inherited proof-proof-chain library commute (list left-zero)))
      (library (library-library-lemma library "ADD-ZERO-RIGHT" (proof-eq (library-plus x zero) x)
                                      right-zero (list (proof-neg (library-integer x)))))
      (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+" (list x y z)))
      (step (library-inherited proof-proof-symmetric library assoc-step))
      (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list x y)))
      (step (library-inherited proof-proof-rewrite library step commute '(1 2 1)))
      (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+" (list y x z)))
      (step (library-inherited proof-proof-chain library step (list assoc-step)))
      (library (library-library-lemma library "ADD-SWAP"
                                      (proof-eq (library-plus x (library-plus y z))
                                                (library-plus y (library-plus x z))) step nil))

      (inverse (library-library-axiom library "INVERSE-OF-+" (list x)))
      (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list (library-minus x) x)))
      (reverse (library-inherited proof-proof-chain library commute (list inverse)))
      (involution (library-additive-identities-inverse-unique (library-minus x) x reverse ints library))
      (involution (library-inherited proof-proof-symmetric library involution))
      (library (library-library-lemma library "DOUBLE-NEGATION"
                                      (proof-eq (library-minus (library-minus x)) x)
                                      involution (list (proof-neg (library-integer x)))))
      (ints (library-library-ints library (list x y))))
     (let ((a (library-plus x y))
           (b (library-plus (library-minus x) (library-minus y))))
       (proof-with-checked-results
        ((zero-sum (library-library-linear-equal library (library-plus a b) zero ints))
         (distribute (library-additive-identities-inverse-unique a b zero-sum ints library))
         (distribute (library-inherited proof-proof-symmetric library distribute)))
        (library-library-lemma library "NEGATE-SUM" (proof-eq (library-minus a) b) distribute
                               (library-guards (list (library-integer x) (library-integer y)))))))))

(defun h4-function-equality-build-tenfold-increase (library ix px)
  (let* ((proof (library-library-proof library))
         (nine (proof-quote 9))
         (ten (proof-quote 10))
         (times-x (list *proof-times* nine *library-x*))
         (fix (proof-sym "FIX" "ACL2")))
    (proof-with-checked-results
     ((rational-nine (h4-association-rational library nine nil))
      (rational-x (h4-association-rational library *library-x* (list ix)))
      (positive-nine (h4-book-measures-prove proof (library-positive nine) nil nil))
      (pos-product (library-library-cite library "POSITIVE-PRODUCT"
                                         (list nine *library-x*)
                                         (list rational-nine rational-x positive-nine px)))
      (result (library-library-less-from-difference
               library *library-x* (library-plus *library-x* times-x) pos-product (list ix)))
      (expansion (library-library-axiom library "COMMUTATIVITY-OF-*" (list ten *library-x*)))
      (sum-ten (proof-proof-compute proof (library-plus *proof-one* nine) 10))
      (ten-sum (proof-proof-symmetric proof sum-ten))
      (expansion (proof-proof-rewrite proof expansion ten-sum '(1 2 2)))
      (distributed (library-library-axiom library "DISTRIBUTIVITY"
                                          (list *library-x* *proof-one* nine)))
      (expansion (proof-proof-chain proof expansion (list distributed)))
      (one-x (library-library-axiom library "UNICITY-OF-1" (list *library-x*)))
      (number-x (h4-association-number library *library-x* (list ix)))
      (fixed (h4-book-measures-simplify proof (list fix *library-x*) (list number-x) (list fix)))
      (one-x (proof-proof-chain proof one-x (list fixed)))
      (x-one (library-library-axiom library "COMMUTATIVITY-OF-*" (list *library-x* *proof-one*)))
      (x-one (proof-proof-chain proof x-one (list one-x)))
      (expansion (proof-proof-rewrite proof expansion x-one '(1 2 1)))
      (x-nine (library-library-axiom library "COMMUTATIVITY-OF-*" (list *library-x* nine)))
      (expansion (proof-proof-rewrite proof expansion x-nine '(1 2 2)))
      (step (library-library-transport-argument library result expansion 2)))
     (library-library-lemma
      library "TENFOLD-LARGER" (library-lt *library-x* (list *proof-times* ten *library-x*))
      step (library-guards (list (library-integer *library-x*) (library-positive *library-x*)))))))

(defun h4-function-equality-build-ordered-arithmetic (library)
  (let* ((x *library-x*)
         (y *library-y*)
         (integer-x (library-integer x))
         (integer-y (library-integer y))
         (positive-x (library-positive x))
         (positive-y (library-positive y))
         (negative-x (library-lt x *proof-zero*))
         (negative-y (library-lt y *proof-zero*))
         (difference (library-diff y x))
         (compare-xy (library-lt x y))
         (proof (library-library-proof library)))
    (proof-with-checked-results
     ((ints (library-library-ints library (list x y)))
      (a (library-library-axiom library "<-ON-OTHERS" (list x y)))
      (b (library-library-axiom library "<-ON-OTHERS" (list *proof-zero* difference)))
      (delta (library-library-linear-equal
              library (library-diff *proof-zero* difference) (library-diff x y) ints))
      (b (proof-proof-rewrite proof b delta '(1 2 1)))
      (b (proof-proof-symmetric proof b))
      (step (proof-proof-chain proof a (list b)))
      (library (library-library-lemma library "LESS-DIFFERENCE"
                                      (proof-eq compare-xy (library-positive difference))
                                      step (library-guards (list integer-x integer-y))))
      (proof (library-library-proof library))

      (px (proof-proof-assume proof positive-x t))
      (py (proof-proof-assume proof positive-y t))
      (positive (library-library-axiom library "POSITIVE" (list x y)))
      (parts (h4-book-flatten-conjunct library positive))
      (both-positive (proof-ite positive-x positive-y *proof-false*))
      (premise (h4-book-measures-prove proof both-positive (list px py) nil))
      (step (h4-book-flatten-modus-ponens library (car parts) premise))
      (library (library-library-lemma library "POSITIVE-SUM"
                                      (library-positive (library-plus x y)) step
                                      (library-guards (list positive-x positive-y))))
      (proof (library-library-proof library))
      (r-x (list *library-rationalp* x))
      (r-y (list *library-rationalp* y))
      (rx (proof-proof-assume proof r-x t))
      (ry (proof-proof-assume proof r-y t))
      (both-rational-positive (proof-ite r-x (proof-ite r-y both-positive *proof-false*)
                                         *proof-false*))
      (premise (h4-book-measures-prove proof both-rational-positive (list rx ry px py) nil))
      (step (h4-book-flatten-modus-ponens library (cadr parts) premise))
      (library (library-library-lemma library "POSITIVE-PRODUCT"
                                      (library-positive (list *proof-times* x y)) step
                                      (library-guards (list r-x r-y positive-x positive-y))))
      (proof (library-library-proof library))

      (ix (car ints))
      (iy (cadr ints))
      (trichotomy (library-library-axiom library "TRICHOTOMY" (list x)))
      (parts (h4-book-flatten-conjunct library trichotomy))
      (tri (car parts))
      (exclusive (cadr parts))
      (opposite (library-library-comparison library x *proof-zero* (list ix)))
      (delta (library-library-linear-equal library (library-diff *proof-zero* x)
                                           (library-minus x) (list ix)))
      (opposite (proof-proof-rewrite proof opposite delta '(1 2 2)))
      (exclusive-first (proof-step-first exclusive))
      (test (proof-term-at exclusive-first 1))
      (test-equality (h4-book-measures-simplify proof test
                                           (list px) (list *proof-not*)))
      (exclusive (proof-proof-rewrite proof exclusive test-equality '(1 1)))
      (exclusive (h4-book-measures-simplify-first proof exclusive nil nil))
      (step (library-library-transport-argument library exclusive opposite 1))
      (library (library-library-lemma library "POSITIVE-NONNEGATIVE"
                                      (library-nonnegative x) step
                                      (library-guards (list integer-x positive-x))))
      (proof (library-library-proof library))

      (goal (library-positive (library-plus y x)))
      (good (library-library-cite library "POSITIVE-SUM" (list y x) (list py px)))
      (x-zero (proof-eq x *proof-zero*))
      (y-zero (library-library-cite library "ADD-ZERO-RIGHT" (list y) (list iy)))
      (zero-case (library-library-transport-argument library py y-zero 2))
      (x-is-zero (proof-proof-assume proof x-zero t))
      (zero-x (proof-proof-symmetric proof x-is-zero))
      (zero-case (proof-proof-rewrite proof zero-case zero-x '(1 2 2)))
      (zero-case (proof-proof-tidy proof zero-case))
      (number-x (h4-association-number library x (list ix)))
      (disjunction (h4-book-flatten-modus-ponens library tri number-x))
      (x-not-positive (proof-proof-assume proof positive-x nil))
      (x-not-zero (proof-proof-assume proof x-zero nil))
      (negative-case (h4-book-measures-simplify-first proof disjunction
                                                  (list x-not-positive x-not-zero) nil))
      (negative-case (proof-proof-transport proof negative-case opposite))
      (x-bound (proof-proof-assume proof negative-x nil))
      (contradiction (proof-proof-cut proof negative-case x-bound))
      (impossible (proof-proof-subsume proof contradiction
                                       (cons goal (proof-step-clause contradiction))))
      (branch (proof-proof-cases proof x-zero zero-case impossible))
      (step (proof-proof-cases proof positive-x good branch))
      (library (library-library-lemma library "POSITIVE-PLUS-NONNEGATIVE" goal step
                                      (list (proof-neg integer-x) (proof-neg integer-y)
                                            (proof-neg positive-y) negative-x)))
      (proof (library-library-proof library))

      (sum (library-plus y x))
      (goal (library-nonnegative sum))
      (y-bound (proof-proof-assume proof negative-y nil))
      (sum-type (library-library-type-of library sum ints))
      (pos-sum (library-library-cite library "POSITIVE-PLUS-NONNEGATIVE"
                                      (list y x) (list iy ix px y-bound)))
      (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list x y)))
      (pos-sum (proof-proof-rewrite proof pos-sum commute '(1 2)))
      (good (library-library-cite library "POSITIVE-NONNEGATIVE"
                                   (list sum) (list sum-type pos-sum)))
      (y-zero (library-library-cite library "ADD-ZERO-RIGHT" (list y) (list iy)))
      (zero-y (proof-proof-symmetric proof y-zero))
      (zero-case (proof-proof-rewrite proof y-bound zero-y '(1 1 1)))
      (zero-case (proof-proof-tidy proof zero-case))
      (x-is-zero (proof-proof-assume proof x-zero t))
      (zero-x (proof-proof-symmetric proof x-is-zero))
      (zero-case (proof-proof-rewrite proof zero-case zero-x '(1 1 1 2)))
      (zero-case (proof-proof-tidy proof zero-case))
      (impossible (proof-proof-subsume proof contradiction
                                       (cons goal (proof-step-clause contradiction))))
      (branch (proof-proof-cases proof x-zero zero-case impossible))
      (step (proof-proof-cases proof positive-x good branch))
      (library (library-library-lemma library "NONNEGATIVE-SUM" goal step
                                      (list (proof-neg integer-x) (proof-neg integer-y)
                                            negative-x negative-y)))
      (proof (library-library-proof library))

      (nx (proof-proof-assume proof (list *library-natp* x) t))
      (ny (proof-proof-assume proof (list *library-natp* y) t))
      (ix-nat (library-library-cite library "NATURAL-INTEGER" (list x) (list nx)))
      (iy-nat (library-library-cite library "NATURAL-INTEGER" (list y) (list ny)))
      (x-nat-bound (library-library-cite library "NATURAL-NONNEGATIVE" (list x) (list nx)))
      (y-nat-bound (library-library-cite library "NATURAL-NONNEGATIVE" (list y) (list ny)))
      (sum-nat-bound (library-library-cite library "NONNEGATIVE-SUM" (list y x)
                                           (list iy-nat ix-nat y-nat-bound x-nat-bound)))
      (sum (library-plus x y))
      (sum-type (library-library-type-of library sum (list ix-nat iy-nat)))
      (sum-nat (library-library-cite library "NATURAL-FROM-BOUNDS" (list sum)
                                     (list sum-type sum-nat-bound)))
      (nat-x (proof-step-first nx))
      (nat-y (proof-step-first ny))
      (library (library-library-lemma library "NATURAL-SUM" (list *library-natp* sum)
                                      sum-nat (library-guards (list nat-x nat-y))))
      (proof (library-library-proof library))

      (pos-one (h4-book-measures-prove proof (library-positive *proof-one*) nil nil))
      (one-type (library-library-type-of library *proof-one* nil))
      (nonnegative-x (proof-proof-assume proof negative-x nil))
      (step (library-library-cite library "POSITIVE-PLUS-NONNEGATIVE" (list x *proof-one*)
                                   (list ix one-type pos-one nonnegative-x)))
      (one-plus-x (library-plus *proof-one* x))
      (library (library-library-lemma library "POSITIVE-ONE-PLUS" (library-positive one-plus-x)
                                      step (list (proof-neg integer-x) negative-x)))
      (step (library-library-less-from-difference library x one-plus-x pos-one (list ix)))
      (library (library-library-lemma library "SUCCESSOR-LARGER" (library-lt x one-plus-x)
                                      step (list (proof-neg integer-x))))
      (proof (library-library-proof library))

      (nonless (proof-proof-assume proof compare-xy nil))
      (delta (library-diff x y))
      (offset (library-library-axiom library "<-ON-OTHERS" (list x y)))
      (nonneg-delta (proof-proof-rewrite proof nonless offset '(1 1)))
      (delta-type (library-library-type-of library delta ints))
      (bound (library-library-cite library "POSITIVE-ONE-PLUS" (list delta)
                                    (list delta-type nonneg-delta)))
      (step (library-library-less-from-difference library y one-plus-x bound ints))
      (library (library-library-lemma
                library "LESS-THAN-NEXT" (library-lt y one-plus-x) step
                (append (library-guards (list integer-x integer-y)) (list compare-xy)))))
     (h4-function-equality-build-tenfold-increase library ix px))))

(defun h4-function-equality-build-count-leaf (leaf library integer-abs length)
  (cond
   ((proof-is-call leaf *proof-plus*)
    (library-library-cite library "SUM-NUMBER" (cdr leaf) nil))
   ((proof-is-call leaf *proof-minus*)
    (library-library-cite library "NEGATION-NUMBER" (cdr leaf) nil))
   ((or (proof-is-call leaf integer-abs) (proof-is-call leaf length))
    (library-library-cite library (if (equal (car leaf) integer-abs)
                                      "ABS-NUMBER" "LENGTH-NUMBER")
                          (cdr leaf) nil))
   (t
    (let ((proof (library-library-proof library)))
      (proof-with-checked-results
          ((evidence (if (equal leaf *library-x*)
                         (proof-with-checked-results
                             ((integer-x (proof-proof-assume proof (library-integer *library-x*) t)))
                           (list integer-x))
                       nil)))
        (h4-association-number library leaf evidence))))))

(defun h4-function-equality-build-count-leaf-proofs (requests library integer-abs length)
  (if (endp requests)
      nil
    (let* ((request (car requests))
           (step (h4-function-equality-build-count-leaf (car request) library integer-abs length)))
      (cons (cons request step)
            (h4-function-equality-build-count-leaf-proofs (cdr requests) library integer-abs length)))))

(defun h4-function-equality-build-count-numeric-lemma (library function name integer-abs length)
  (let* ((proof (library-library-proof library))
         (call (list function *library-x*))
         (template (list *library-numberp* *proof-result*)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof call))
      (opened-first (proof-step-first opened))
      (body (proof-term-at opened-first 2))
      (requests (proof-proof-by-value-leaves proof body nil))
      (leaf (h4-function-equality-build-count-leaf-proofs requests library integer-abs length))
      (step (proof-proof-by-value proof body template leaf nil))
      (closed (proof-proof-symmetric proof opened))
      (step (proof-proof-rewrite-result proof step closed template *proof-result*)))
     (library-library-lemma library name (list *library-numberp* call) step nil))))

(defun h4-function-equality-build-count-lemmas (library)
  (let* ((x *library-x*)
         (y *library-y*)
         (integer-abs (proof-sym "INTEGER-ABS" "ACL2"))
         (length (proof-cl "LENGTH"))
         (size (list *library-count* x)))
    (proof-with-checked-results
     ((closure (library-library-axiom library "CLOSURE" (list x y)))
      (parts (h4-book-flatten-conjunct library closure))
      (add (car parts))
      (parts (h4-book-flatten-conjunct library (cadr parts)))
      (parts (h4-book-flatten-conjunct library (cadr parts)))
      (minus-number (car parts))
      (library (library-library-lemma library "SUM-NUMBER"
                                      (list *library-numberp* (library-plus x y)) add nil))
      (library (library-library-lemma library "NEGATION-NUMBER"
                                      (list *library-numberp* (library-minus x)) minus-number nil))
      (library (h4-function-equality-build-count-numeric-lemma
                library integer-abs "ABS-NUMBER" integer-abs length))
      (library (h4-function-equality-build-count-numeric-lemma
                library length "LENGTH-NUMBER" integer-abs length))
      (library (h4-function-equality-build-count-numeric-lemma
                library *library-count* "COUNT-NUMBER" integer-abs length))
      (proof (library-library-proof library))
      (count-number (library-library-cite library "COUNT-NUMBER" (list x) nil))
      (is-finite (library-library-cite library "NUMBER-FINITE" (list size) (list count-number)))
      (ordinal (library-library-builtin library 1 x))
      (step (h4-book-measures-simplify-first proof ordinal (list is-finite) (list *proof-ordinalp*)))
      (library (library-library-lemma library "COUNT-NATURAL" (list *library-natp* size) step nil))
      (natural-size (h4-book-measures-natural library size))
      (step (library-library-cite library "NATURAL-INTEGER" (list size) (list natural-size))))
     (library-library-lemma library "COUNT-INTEGER" (library-integer size) step nil))))

(defun h4-function-equality-build (p)
  (proof-with-checked-results
      ((p (h4-function-equality-build-logic-and-types p))
       (p (h4-function-equality-build-additive-identities p))
       (p (h4-function-equality-build-ordered-arithmetic p))
       (p (library-library-order-lemmas p))
       (p (library-library-length-lemmas p))
       (p (h4-function-equality-build-count-lemmas p)))
    (library-library-build-after-count p)))

(defun h4-function-equality-loop-congruence-descends (comparison evidence p)
  (proof-with-checked-results
   ((hypotheses (descent-hypotheses-init p nil evidence))
    (direct (descent-direct-builtin p (list comparison) hypotheses)))
   (if (car direct)
       (cons (car direct) p)
     (proof-with-checked-results
      ((next (if (assoc-equal (proof-sym "SELF-COUNT-CAR-WEAK" "ACL2")
                               (proof-proof-facts (library-library-proof p)))
                 p
               (h4-function-equality-build p)))
       (hypotheses (descent-hypotheses-with-proof (cdr direct) next))
       (result (h4-book-measures-selector-decrease next comparison hypotheses)))
      (cons (car result) next)))))

(defun h4-function-equality-caller-descent (caller comparison evidence)
  (let ((p (h4-function-equality-caller-congruence-p caller))
        (descent (h4-function-equality-caller-congruence-descent caller)))
    (cond
     ((eq descent :selector)
      (h4-function-equality-loop-congruence-descends comparison evidence p))
     ((and (consp descent) (eq (car descent) :callback))
      (let ((reply (assoc-equal (list comparison evidence) (cadr descent))))
        (if reply
            (cdr reply)
          (list :h4-function-equality-descent-request comparison evidence p))))
     (t '(:failure "failure" "")))))

(defun h4-function-equality-caller-pointwise (caller)
  (let ((name (h4-function-equality-caller-congruence-pointwise caller)))
    (if name
        (cons name caller)
      (proof-with-checked-results
       ((lemma (h4-function-equality-pointwise-lemma
                (h4-function-equality-caller-congruence-p caller))))
       (cons (car lemma) (update-nth 10 (car lemma) (update-nth 1 (cdr lemma) caller)))))))

(defun h4-function-equality-caller-apply-pointwise (caller left right)
  (proof-with-checked-results
   ((pointwise (h4-function-equality-caller-pointwise caller))
    (arguments (proof-term-at left 2)))
   (let* ((caller (cdr pointwise))
          (proof (library-library-proof (h4-function-equality-caller-congruence-p caller))))
     (proof-with-checked-results
      ((step (proof-proof-use proof (car pointwise)
                              (list (list *h4-function-equality-fn1* (cadr left))
                                    (list *h4-function-equality-fn2* (cadr right))
                                    (list *h4-function-equality-args* arguments))
                              (list (h4-function-equality-caller-congruence-premise caller)))))
      (cons step caller)))))

(defun h4-function-equality-changed-bindings (formals actuals)
  (if (or (endp formals) (endp actuals))
      nil
    (let ((rest (h4-function-equality-changed-bindings (cdr formals) (cdr actuals))))
      (if (equal (car formals) (car actuals))
          rest
        (cons (list (car formals) (car actuals)) rest)))))

(defun h4-function-equality-caller-recursive-application (caller left evidence)
  (let* ((p (h4-function-equality-caller-congruence-p caller))
         (measure (h4-function-equality-caller-congruence-measure caller))
         (call (h4-function-equality-caller-congruence-call caller))
         (bindings (h4-function-equality-changed-bindings (cdr call) (cdr left)))
         (substitutions (h4-function-equality-caller-congruence-substitutions caller))
         (caller (update-nth 9 (append substitutions (list bindings)) caller))
         (mapping (h4-book-flatten-binding-map bindings nil)))
    (h4-function-equality-with-results
     ((smaller (proof-subst measure mapping))
      (comparison (list *proof-ordinal-less* smaller measure))
      (child (proof-subst (h4-function-equality-caller-congruence-formula caller) mapping))
      (assumed (proof-proof-assume (library-library-proof p)
                                   (proof-ite comparison child *proof-true*) t))
      (descent (h4-function-equality-caller-descent caller comparison evidence))
      (caller (update-nth 1 (cdr descent) caller))
      (induction (proof-proof-prove-if (library-library-proof (cdr descent)) assumed (car descent)))
      (step (h4-book-flatten-modus-ponens (cdr descent) induction
                                          (h4-function-equality-caller-congruence-premise caller))))
     (cons step caller))))

(defun h4-function-equality-caller-argument-law (caller left index replacement)
  (let ((replaced (append (seq-slice left 0 index) (list replacement)
                          (seq-slice left (1+ index) :none))))
    (h4-book-flatten-fact-instance
     (h4-function-equality-caller-congruence-p caller) (proof-eq left replaced)
     (list (h4-function-equality-caller-congruence-premise caller)) :none nil)))

(defun h4-function-equality-caller-application-argument (caller left first second index evidence)
  (and (equal first (h4-function-equality-caller-congruence-left-function caller))
       (equal second (h4-function-equality-caller-congruence-right-function caller))
       (proof-with-checked-results
        ((head (proof-term-at (h4-function-equality-caller-congruence-call caller) 0)))
        (if (equal (car left) head)
            (h4-function-equality-caller-recursive-application caller left evidence)
          (proof-with-checked-results
           ((law (h4-function-equality-caller-argument-law caller left index second)))
           (and law (cons law caller)))))))

(defun h4-function-equality-caller-application-arguments
    (caller left firsts seconds index evidence outcome)
  (declare (xargs :measure (acl2-count firsts)))
  (cond
   (outcome outcome)
   ((or (endp firsts) (endp seconds))
    (proof-with-checked-results
     ((step (proof-proof-reflexive
             (library-library-proof (h4-function-equality-caller-congruence-p caller)) left)))
     (cons step caller)))
   (t
    (h4-function-equality-caller-application-arguments
     caller left (cdr firsts) (cdr seconds) (1+ index) evidence
     (h4-function-equality-caller-application-argument
      caller left (car firsts) (car seconds) index evidence)))))

(defun h4-function-equality-caller-congruence-application (caller left right evidence)
  (proof-with-checked-results
   ((head (proof-term-at left 0))
    (left-match (and (equal head *h4-function-equality-apply*)
                     (proof-with-checked-results ((first (proof-term-at left 1)))
                       (equal first (h4-function-equality-caller-congruence-left-function caller)))))
    (right-match (and left-match
                      (proof-with-checked-results ((second (proof-term-at right 1)))
                        (equal second (h4-function-equality-caller-congruence-right-function caller))))))
   (if right-match
       (h4-function-equality-caller-apply-pointwise caller left right)
     (h4-function-equality-caller-application-arguments caller left (cdr left) (cdr right)
                                                       1 evidence nil))))

(defun h4-function-equality-restore-branches (caller step left right hypothesis right-hypothesis)
  (let ((proof (library-library-proof (h4-function-equality-caller-congruence-p caller))))
    (proof-with-checked-results
     ((left (proof-proof-select proof left hypothesis))
      (left (proof-proof-symmetric proof left))
      (step (proof-proof-rewrite proof step left '(1 1)))
      (right (proof-proof-select proof right right-hypothesis))
      (right (proof-proof-symmetric proof right))
      (step (proof-proof-rewrite proof step right '(1 2))))
     (cons step caller))))

(defun h4-function-equality-compare-next (caller frames left right evidence)
  (let* ((p (h4-function-equality-caller-congruence-p caller))
         (proof (library-library-proof p)))
    (cond
     ((equal left right)
      (proof-with-checked-results ((step (proof-proof-reflexive proof left)))
        (list :result caller frames step)))
     ((and (proof-is-call left *proof-if*) (proof-is-call right *proof-if*))
      (list :conditional caller frames left right evidence))
     (t
      (proof-with-checked-results
       ((reduce-left (h4-book-flatten-normalize p left evidence nil nil))
        (reduce-right (h4-book-flatten-normalize p right evidence nil nil))
        (first (h4-book-flatten-step-right reduce-left))
        (second (h4-book-flatten-step-right reduce-right)))
       (cond
        ((or (not (equal first left)) (not (equal second right)))
         (list :compare caller (cons (list :chain reduce-left reduce-right) frames)
               first second evidence))
        ((or (not (proof-compound left)) (not (proof-compound right)))
         '(:failure "failure" ""))
        (t
         (h4-function-equality-with-results
          ((first-head (proof-term-at left 0))
           (second-head (proof-term-at right 0)))
          (if (equal first-head second-head)
              (h4-function-equality-with-results
               ((application (h4-function-equality-caller-congruence-application
                              caller left right evidence)))
               (list :align (cdr application) frames (car application) (cdr right)
                     1 evidence))
            '(:failure "failure" ""))))))))))

(defun h4-function-equality-align-next (caller frames step arguments index evidence)
  (if (endp arguments)
      (proof-with-checked-results
       ((step (proof-proof-tidy
               (library-library-proof (h4-function-equality-caller-congruence-p caller)) step)))
       (list :result caller frames step))
    (proof-with-checked-results
     ((rhs (h4-book-flatten-step-right step))
      (other (proof-term-at rhs index)))
     (if (equal other (car arguments))
         (list :align caller frames step (cdr arguments) (1+ index) evidence)
       (list :compare caller (cons (list :rewrite step (cdr arguments) index evidence) frames)
             other (car arguments) evidence)))))

(defun h4-function-equality-branch-next (caller frames left right evidence tests-equal test index)
  (let* ((proof (library-library-proof (h4-function-equality-caller-congruence-p caller)))
         (positive (= index 2)))
    (proof-with-checked-results
     ((hypothesis (proof-proof-assume proof test positive))
      (right-hypothesis
       (if tests-equal
           (proof-proof-rewrite proof hypothesis tests-equal (if positive '(1) '(1 1)))
         hypothesis))
      (a (proof-term-at left index))
      (b (proof-term-at right index)))
     (list :compare caller (cons (list :restore left right hypothesis right-hypothesis) frames)
           a b (append evidence (list hypothesis right-hypothesis))))))

(defun h4-function-equality-positive-next (caller frames left right evidence test tests-equal)
  (h4-function-equality-branch-next
   caller (cons (list :negative left right evidence test tests-equal) frames)
   left right evidence tests-equal test 2))

(defun h4-function-equality-conditional-next (caller frames left right evidence)
  (proof-with-checked-results
   ((test (proof-term-at left 1))
    (other (proof-term-at right 1)))
   (if (equal test other)
       (h4-function-equality-positive-next caller frames left right evidence test nil)
     (list :compare caller (cons (list :positive left right evidence test) frames)
           test other evidence))))

; Each frame records the remaining proof operations for one recursive comparison.
(defun h4-function-equality-resume-comparison (caller frames step)
  (if (endp frames)
      (cons :done (cons step caller))
    (let* ((frame (car frames))
           (frames (cdr frames))
           (p (h4-function-equality-caller-congruence-p caller))
           (proof (library-library-proof p)))
      (case (car frame)
        (:chain
         (proof-with-checked-results
          ((reverse-right (proof-proof-symmetric proof (caddr frame)))
           (step (proof-proof-chain proof (cadr frame) (list step reverse-right))))
          (list :result caller frames step)))
        (:rewrite
         (let ((index (cadddr frame)))
           (proof-with-checked-results
            ((step (proof-proof-rewrite proof (cadr frame) step (list 1 2 index))))
            (list :align caller frames step (caddr frame) (1+ index) (nth 4 frame)))))
        (:positive
         (h4-function-equality-positive-next caller frames (cadr frame) (caddr frame)
                                             (cadddr frame) (nth 4 frame) step))
        (:negative
         (let ((left (cadr frame))
               (right (caddr frame))
               (test (nth 4 frame)))
           (h4-function-equality-branch-next
            caller (cons (list :join left right test step) frames)
            left right (cadddr frame) (nth 5 frame) test 3)))
        (:restore
         (proof-with-checked-results
          ((restored (h4-function-equality-restore-branches
                      caller step (cadr frame) (caddr frame) (cadddr frame) (nth 4 frame))))
          (list :result (cdr restored) frames (car restored))))
        (:join
         (proof-with-checked-results
          ((step (h4-book-flatten-case-of p (proof-eq (cadr frame) (caddr frame))
                                         (cadddr frame) (nth 4 frame) step)))
          (list :result caller frames step)))
        (otherwise '(:failure "failure" ""))))))

(defun h4-function-equality-comparison-next (work)
  (let ((caller (cadr work))
        (frames (caddr work))
        (args (cdddr work)))
    (case (car work)
      (:compare (h4-function-equality-compare-next caller frames (car args) (cadr args) (caddr args)))
      (:conditional
       (h4-function-equality-conditional-next caller frames (car args) (cadr args) (caddr args)))
      (:align (h4-function-equality-align-next caller frames (car args) (cadr args)
                                              (caddr args) (cadddr args)))
      (:result (h4-function-equality-resume-comparison caller frames (car args)))
      (otherwise '(:failure "failure" "")))))

(defun h4-function-equality-compare-run (n work)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h4-function-equality-compare-run"))
   ((eq (car work) :done) (cdr work))
   ((member-eq (car work) '(:failure :h4-function-equality-descent-request)) work)
   (t (h4-function-equality-compare-run (1- n) (h4-function-equality-comparison-next work)))))

(defun h4-function-equality-caller-congruence-compare (caller left right evidence)
  (h4-function-equality-compare-run 1000000 (list :compare caller nil left right evidence)))

(defun h4-function-equality-logical-arguments (args path index)
  (if (endp args)
      nil
    (cons (list (car args) (append path (list index)))
          (h4-function-equality-logical-arguments (cdr args) path (1+ index)))))

(defun h4-function-equality-logical-next (proof result pending)
  (let ((value (caar pending))
        (path (cadar pending))
        (rest (cdr pending)))
    (if (or (not (proof-compound value)) (proof-is-call value *proof-quote*))
        (cons :visit (cons result rest))
      (proof-with-checked-results ((head (proof-term-at value 0)))
        (if (or (proof-compound head) (equal head *termination-return-last*))
            (proof-with-checked-results
             ((equality (if (proof-compound head)
                            (proof-proof-beta proof value)
                          (proof-proof-unfold proof value)))
              (result (proof-proof-rewrite proof result equality (append '(1 2) path)))
              (body (h4-book-flatten-step-right equality)))
             (list* :visit result (list body path) rest))
          (list* :visit result
                 (append (h4-function-equality-logical-arguments (cdr value) path 1) rest)))))))

(defun h4-function-equality-logical-visit (n proof progress)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h4-function-equality-logical-visit"))
   ((not (eq (car progress) :visit)) progress)
   ((endp (cddr progress)) (cadr progress))
   (t (h4-function-equality-logical-visit
       (1- n) proof
       (h4-function-equality-logical-next proof (cadr progress) (cddr progress))))))

(defun h4-function-equality-logical-equation (p function)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((equation (proof-proof-fact proof function nil))
      (body (h4-book-flatten-step-right equation)))
     (h4-function-equality-logical-visit 1000000 proof (list :visit equation (list body nil))))))

(defun h4-function-equality-function-definition (proof name)
  (let ((entry (assoc-equal name (proof-proof-definitions proof))))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun h4-function-equality-caller-congruence-prove (caller ordinal)
  (let* ((p (h4-function-equality-caller-congruence-p caller))
         (formula (h4-function-equality-caller-congruence-formula caller))
         (proof (library-library-proof p)))
    (h4-function-equality-with-results
     ((goal (proof-term-at formula 2))
      (sides (proof-list-of-length goal 3))
      (left (cadr sides))
      (right (caddr sides))
      (head (proof-term-at left 0))
      (equation (h4-function-equality-logical-equation p head))
      (definition (h4-function-equality-function-definition proof head))
      (formals (car definition))
      (opened-left (proof-proof-instantiate proof equation (seq-zip formals (cdr left))))
      (opened-right (proof-proof-instantiate proof equation (seq-zip formals (cdr right))))
      (lhs (h4-book-flatten-step-right opened-left))
      (rhs (h4-book-flatten-step-right opened-right))
      (compared (h4-function-equality-caller-congruence-compare caller lhs rhs nil))
      (caller (cdr compared))
      (p (h4-function-equality-caller-congruence-p caller))
      (proof (library-library-proof p))
      (reversed (proof-proof-symmetric proof opened-right))
      (result (proof-proof-chain proof opened-left (list (car compared) reversed)))
      (case-step (h4-book-flatten-imply p formula result))
      (substitutions (h4-function-equality-caller-congruence-substitutions caller))
      (step (if substitutions
                (if ordinal
                    (proof-proof-induct proof ordinal case-step formula
                                        (h4-function-equality-caller-congruence-measure caller)
                                        (proof-unique substitutions))
                  '(:failure "failure" ""))
              case-step)))
     (cons step caller))))

(defun h4-function-equality-prove-congruence (p formula measure descent ordinal)
  (h4-function-equality-with-results
   ((caller (h4-function-equality-caller-congruence-init p formula measure descent))
    (result (h4-function-equality-caller-congruence-prove caller ordinal)))
   (cons (car result) (h4-function-equality-caller-congruence-p (cdr result)))))

(defun h4-function-equality-loop-congruence (p formula)
  (proof-with-checked-results
   ((goal (proof-term-at formula 2))
    (sides (proof-list-of-length goal 3))
    (call (cadr sides))
    (head (proof-term-at call 0))
    (definition (h4-function-equality-function-definition (library-library-proof p) head))
    (parts (proof-list-of-length definition 2))
    (formals (car parts))
    (definitions (list (cons head parts)))
    (calls (termination-recursive-calls *termination-all* definitions)))
   (if (endp calls)
       (h4-function-equality-prove-congruence p formula nil nil nil)
     (proof-with-checked-results ((plan (termination-selector-plan definitions calls)))
       (let ((selected (assoc-equal head plan)))
         (if selected
             (proof-with-checked-results
              ((index (seq-index formals (cdr selected)))
               (argument (proof-term-at call (1+ index)))
               (ordinal (library-library-builtin p 1 argument)))
              (h4-function-equality-prove-congruence
               p formula (list *library-count* argument) :selector ordinal))
           '(:failure "failure" "")))))))
