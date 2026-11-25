(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-powers-fix* (proof-sym "FIX" "ACL2"))
(defconst *b1-powers-expt-unfold*
  (list *b1-quotient-expt* *b1-quotient-zip* *b1-quotient-numeric-eq* *b1-powers-fix*))

(defun b1-powers-expt (base exponent)
  (list *b1-quotient-expt* base exponent))

(defun b1-powers-expt-number-by-value (n lib value template)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((zp n) '(:failure "fuel" "b1-powers-expt-number-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
       ((parts (proof-list-of-length (cdr value) 3))
        (test (car parts))
        (yes (b1-powers-expt-number-by-value (1- n) lib (cadr parts) template))
        (no (b1-powers-expt-number-by-value (1- n) lib (caddr parts) template))
        (branch (proof-proof-if-true proof value))
        (branch (proof-proof-symmetric proof branch))
        (yes (proof-proof-rewrite-result proof yes branch template *proof-result*))
        (branch (proof-proof-if-false proof value))
        (branch (proof-proof-symmetric proof branch))
        (no (proof-proof-rewrite-result proof no branch template *proof-result*)))
       (proof-proof-cases proof test yes no)))
     ((and (proof-compound value) (not (consp value)))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
       ((equality (proof-proof-beta proof value))
        (child (proof-rewritten-term equality))
        (step (b1-powers-expt-number-by-value (1- n) lib child template))
        (reversed (proof-proof-symmetric proof equality)))
       (proof-proof-rewrite-result proof step reversed template *proof-result*)))
     (t
      (proof-with-checked-results
       ((step (b1-arithmetic-known-type lib *library-numberp* value nil))
        (literal (proof-step-first step))
        (expected (proof-subst template (list (cons *proof-result* value)))))
       (if (equal literal expected)
           step
         '(:failure "failure" "")))))))

(defun b1-powers-expt-number-lemma (lib)
  (let ((proof (library-library-proof lib))
        (template (list *library-numberp* *proof-result*))
        (call (b1-powers-expt *library-x* *library-y*)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof call))
      (value (proof-rewritten-term opened))
      (step (b1-powers-expt-number-by-value 1000000 lib value template))
      (reversed (proof-proof-symmetric proof opened))
      (step (proof-proof-rewrite-result proof step reversed template *proof-result*)))
     (library-library-lemma lib "EXPT-NUMBER" (list *library-numberp* call) step nil))))

(defun b1-powers-expt-number (lib base exponent)
  (let ((name (proof-sym "SELF-EXPT-NUMBER" "ACL2")))
    (proof-with-checked-results
     ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
               lib
             (b1-powers-expt-number-lemma lib)))
      (step (library-inherited proof-proof-fact lib name
                               (list (list *library-x* base) (list *library-y* exponent)))))
     (cons step lib))))

(defun b1-powers-expt-zero (lib base)
  (b1-logic-bookproof-normalize lib (b1-powers-expt base *proof-zero*) nil
                               *b1-powers-expt-unfold* nil nil nil nil))

(defun b1-powers-multiply-inverse (lib a b term inverse numeric)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((association (library-library-axiom lib "ASSOCIATIVITY-OF-*" (list a b term)))
      (step (proof-proof-symmetric proof association))
      (step (proof-proof-rewrite proof step inverse '(1 2 1)))
      (unit (b1-arithmetic-multiply-one lib term (list numeric) t)))
     (proof-proof-chain proof step (list unit)))))

(defun b1-powers-build-recurrences-step-up (lib base k integer-k number nonzero inverse)
  (let ((successor (library-plus k *proof-one*))
        (inv (b1-arithmetic-reciprocal base))
        (negative (library-lt k *proof-zero*)))
    (proof-with-checked-results
     ((yes (library-inherited proof-proof-assume lib negative t))
      (integer-zero (library-library-type-of lib *proof-zero* nil))
      (not-positive (library-library-cite lib "LESS-TO-WEAK" (list k *proof-zero*)
                                          (list integer-k integer-zero yes)))
      (not-zero (b1-arithmetic-comparison-excludes lib yes *proof-zero* 1))
      (opened (b1-logic-bookproof-normalize
               lib (b1-powers-expt base k)
               (list integer-k number nonzero not-positive not-zero)
               *b1-powers-expt-unfold* nil nil nil nil))
      (rhs (library-inherited proof-proof-reflexive
                              lib (b1-arithmetic-product base (b1-powers-expt base k))))
      (rhs (library-inherited proof-proof-rewrite lib rhs opened '(1 2 2)))
      (term (b1-powers-expt base successor))
      (numeric (b1-powers-expt-number lib base successor))
      (lib (cdr numeric))
      (cancel (b1-powers-multiply-inverse lib base inv term inverse (car numeric)))
      (rhs (library-inherited proof-proof-chain lib rhs (list cancel))))
     (let ((proof (library-library-proof lib)))
       (proof-with-checked-results
        ((no (proof-proof-assume proof negative nil))
         (successor-positive (library-library-cite lib "POSITIVE-ONE-PLUS" (list k)
                                                   (list integer-k no)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-+" (list *proof-one* k)))
         (successor-positive (proof-proof-rewrite proof successor-positive commute '(1 2)))
         (int-successor (library-library-type-of lib successor (list integer-k)))
         (successor-nonzero (b1-arithmetic-comparison-excludes
                             lib successor-positive *proof-zero* 2))
         (lhs (b1-logic-bookproof-normalize
               lib (b1-powers-expt base successor)
               (list int-successor number nonzero successor-positive successor-nonzero)
               *b1-powers-expt-unfold* nil nil nil nil))
         (cancel (b1-arithmetic-number-sums-linear-equal
                  lib (library-plus successor *proof-neg-one*) k (list integer-k)))
         (lhs (proof-proof-rewrite proof lhs cancel '(1 2 2 2)))
         (reversed (proof-proof-symmetric proof rhs))
         (step (proof-proof-cases proof negative reversed lhs)))
        (cons step lib))))))

(defun b1-powers-build-recurrences-step-down (lib base k integer-k number nonzero inverse)
  (let ((predecessor (library-plus k *proof-neg-one*))
        (inv (b1-arithmetic-reciprocal base)))
    (proof-with-checked-results
     ((integer-predecessor (library-library-type-of lib predecessor (list integer-k)))
      (step (library-library-cite lib "EXPT-STEP-UP" (list base predecessor)
                                  (list integer-predecessor number nonzero)))
      (back (b1-arithmetic-number-sums-linear-equal
             lib (library-plus predecessor *proof-one*) k (list integer-k)))
      (step (library-inherited proof-proof-rewrite lib step back '(1 1 2)))
      (multiplied (library-inherited proof-proof-reflexive
                                     lib (b1-arithmetic-product inv (b1-powers-expt base k))))
      (multiplied (library-inherited proof-proof-rewrite lib multiplied step '(1 2 2)))
      (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list inv base)))
      (swapped (library-inherited proof-proof-chain lib commute (list inverse)))
      (term (b1-powers-expt base predecessor))
      (numeric (b1-powers-expt-number lib base predecessor))
      (lib (cdr numeric))
      (cancel (b1-powers-multiply-inverse lib inv base term swapped (car numeric)))
      (multiplied (library-inherited proof-proof-chain lib multiplied (list cancel)))
      (step (library-inherited proof-proof-symmetric lib multiplied)))
     (cons step lib))))

(defun b1-powers-build-recurrences (lib)
  (let* ((name (proof-sym "SELF-EXPT-STEP-DOWN" "ACL2"))
         (proof (library-library-proof lib)))
    (if (assoc-equal name (proof-proof-facts proof))
        lib
      (let ((base *library-x*)
            (k *library-y*))
        (proof-with-checked-results
         ((integer-k (proof-proof-assume proof (library-integer k) t))
          (number (proof-proof-assume proof (list *library-numberp* base) t))
          (nonzero (proof-proof-assume proof (proof-eq base *proof-zero*) nil))
          (integer-claim (proof-step-first integer-k))
          (number-claim (proof-step-first number))
          (nonzero-claim (proof-step-first nonzero))
          (zero-test (proof-term-at nonzero-claim 1))
          (guards (list (proof-neg integer-claim) (proof-neg number-claim) zero-test))
          (inverse (b1-arithmetic-inverse-product lib base number nonzero))
          (step-up (b1-powers-build-recurrences-step-up lib base k integer-k number nonzero inverse))
          (claim (proof-step-first (car step-up)))
          (lib (library-library-lemma (cdr step-up) "EXPT-STEP-UP" claim (car step-up) guards))
          (step-down (b1-powers-build-recurrences-step-down
                      lib base k integer-k number nonzero inverse))
          (claim (proof-step-first (car step-down))))
         (library-library-lemma (cdr step-down) "EXPT-STEP-DOWN" claim (car step-down) guards))))))

(defun b1-powers-natural-predecessor (lib natural nonzero)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((natural-claim (proof-step-first natural))
      (n (proof-term-at natural-claim 1))
      (previous (library-plus n *proof-neg-one*))
      (int-n (library-library-cite lib "NATURAL-INTEGER" (list n) (list natural)))
      (nonnegative-n (library-library-cite lib "NATURAL-NONNEGATIVE" (list n) (list natural)))
      (comparison (b1-arithmetic-integer-compare lib n *proof-zero* (list int-n)))
      (pos-n (proof-proof-discharge proof comparison nonnegative-n))
      (pos-n (proof-proof-discharge proof pos-n nonzero))
      (at-least-one (b1-arithmetic-integer-discrete lib pos-n int-n))
      (others (library-library-axiom lib "<-ON-OTHERS" (list n *proof-one*)))
      (lower (proof-proof-rewrite proof at-least-one others '(1 1)))
      (lower (b1-arithmetic-simplify-first lib lower))
      (int-previous (library-library-type-of lib previous (list int-n)))
      (nat-previous (library-library-cite lib "NATURAL-FROM-BOUNDS" (list previous)
                                        (list int-previous lower)))
      (builtin (library-library-builtin lib 10 n))
      (descent (proof-proof-discharge proof builtin int-n))
      (descent (proof-proof-discharge proof descent pos-n)))
     (list nat-previous descent))))

(defun b1-powers-power-addition-case-at-zero (lib base n signed j integer-j zero-n claim)
  (proof-with-checked-results
   ((base-case (library-inherited proof-proof-assume lib zero-n t))
    (base-case (if (equal signed n)
                   base-case
                 (proof-with-checked-results
                  ((start (library-inherited proof-proof-reflexive lib signed))
                   (changed (library-inherited proof-proof-rewrite lib start base-case '(1 2 1)))
                   (zero (b1-logic-bookproof-constant lib (library-minus *proof-zero*))))
                  (library-inherited proof-proof-chain lib changed (list zero)))))
    (expt-zero (b1-powers-expt-zero lib base))
    (add-zero (library-library-cite lib "ADD-ZERO-LEFT" (list j) (list integer-j)))
    (term (b1-powers-expt base j))
    (numeric (b1-powers-expt-number lib base j))
    (lib (cdr numeric))
    (multiply-one (b1-arithmetic-multiply-one lib term (list (car numeric)) t))
    (rules (list (b1-logic-equal-to base-case) (b1-logic-equal-to expt-zero)
                 (b1-logic-equal-to add-zero) (b1-logic-equal-to multiply-one)))
    (at-zero (b1-logic-bookproof-normalize-proof lib claim nil nil rules nil)))
   (cons at-zero lib)))

(defun b1-powers-power-addition-case-consequence
    (premise lib direction base n j signed signed-predecessor total child-total
             claim formula bindings weight recurrence)
  (proof-with-checked-results
   ((parts (b1-logic-bookproof-split-conjuncts lib premise))
    (parts (proof-list-of-length parts 4))
    (nat-n (car parts))
    (integer-j (cadr parts))
    (number-base (caddr parts))
    (nz (cadddr parts))
    (int-n (library-library-cite lib "NATURAL-INTEGER" (list n) (list nat-n)))
    (types (list int-n integer-j))
    (zero-n (proof-eq n *proof-zero*))
    (at-zero (b1-powers-power-addition-case-at-zero lib base n signed j integer-j zero-n claim))
    (lib (cdr at-zero)))
   (let ((proof (library-library-proof lib)))
     (proof-with-checked-results
      ((nonzero (proof-proof-assume proof zero-n nil))
       (previous (b1-powers-natural-predecessor lib nat-n nonzero))
       (nat-predecessor (car previous))
       (descent (cadr previous))
       (child-formula (proof-subst formula bindings))
       (descent-claim (proof-step-first descent))
       (hyp (proof-proof-assume proof (proof-ite descent-claim child-formula *proof-true*) t))
       (induction (proof-proof-prove-if proof hyp descent))
       (child-guard (b1-logic-bookproof-normalize-proof
                     lib (cadr child-formula) (list nat-predecessor integer-j number-base nz)
                     nil nil nil))
       (smaller (proof-proof-modus-ponens proof induction child-guard))
       (int-predecessor (library-library-type-of lib signed-predecessor types))
       (natural-step (library-library-cite lib recurrence (list base signed-predecessor)
                                          (list int-predecessor number-base nz)))
       (int-child-total (library-library-type-of lib child-total types))
       (total-step (library-library-cite lib recurrence (list base child-total)
                                        (list int-child-total number-base nz)))
       (natural-change (b1-arithmetic-number-sums-linear-equal
                        lib (library-plus signed-predecessor direction) signed types))
       (total-change (b1-arithmetic-number-sums-linear-equal
                      lib (library-plus child-total direction) total types))
       (natural-step (proof-proof-rewrite proof natural-step natural-change '(1 1 2)))
       (total-step (proof-proof-rewrite proof total-step total-change '(1 1 2)))
       (total-step (proof-proof-rewrite proof total-step smaller '(1 2 2)))
       (associate (library-library-axiom lib "ASSOCIATIVITY-OF-*"
                                         (list weight (b1-powers-expt base signed-predecessor)
                                               (b1-powers-expt base j))))
       (associate (proof-proof-symmetric proof associate))
       (total-step (proof-proof-chain proof total-step (list associate)))
       (reversed (proof-proof-symmetric proof natural-step))
       (total-step (proof-proof-rewrite proof total-step reversed '(1 2 1)))
       (step (proof-proof-cases proof zero-n (car at-zero) total-step)))
      (cons step lib)))))

(defun b1-powers-power-addition-case (lib direction)
  (let* ((positive (equal direction *proof-one*))
         (tag (if positive "POSITIVE" "NEGATIVE"))
         (name (proof-sym (concatenate 'string "SELF-EXPT-ADD-" tag) "ACL2")))
    (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
        (cons name lib)
      (proof-with-checked-results ((lib (b1-powers-build-recurrences lib)))
        (let* ((base *library-x*)
               (n *library-y*)
               (j *library-z*)
               (signed (if positive n (library-minus n)))
               (predecessor (library-plus n *proof-neg-one*))
               (signed-predecessor (if positive predecessor (library-minus predecessor)))
               (total (library-plus signed j))
               (child-total (library-plus signed-predecessor j))
               (number (list *library-numberp* base))
               (nonzero (proof-neg (proof-eq base *proof-zero*)))
               (guard (proof-ite (list *library-natp* n)
                        (proof-ite (library-integer j)
                          (proof-ite number nonzero *proof-false*) *proof-false*)
                        *proof-false*))
               (claim (proof-eq (b1-powers-expt base total)
                                (b1-arithmetic-product (b1-powers-expt base signed)
                                                       (b1-powers-expt base j))))
               (formula (list *library-implies* guard claim))
               (bindings (list (cons n predecessor)))
               (weight (if positive base (b1-arithmetic-reciprocal base)))
               (recurrence (if positive "EXPT-STEP-UP" "EXPT-STEP-DOWN")))
          (proof-with-checked-results
           ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
            (consequence (b1-powers-power-addition-case-consequence
                          premise lib direction base n j signed signed-predecessor total
                          child-total claim formula bindings weight recurrence))
            (lib (cdr consequence))
            (step (b1-logic-bookproof-prove-implication-with-premise
                   lib formula premise (car consequence)))
            (ordinal (library-library-builtin lib 1 n))
            (step (library-inherited proof-proof-induct lib ordinal step formula
                                     (list *library-count* n) (list (list (list n predecessor)))))
            (lib (library-library-lemma lib (concatenate 'string "EXPT-ADD-" tag) formula step nil)))
           (cons name lib)))))))

(defun b1-powers-signed-power-addition-cite (direction n nat lib base j arguments)
  (proof-with-checked-results
   ((added (b1-powers-power-addition-case lib direction))
    (lib (cdr added))
    (fact (library-inherited proof-proof-fact lib (car added)
                             (list (list *library-x* base) (list *library-y* n) (list *library-z* j))))
    (fact-claim (proof-step-first fact))
    (test (proof-term-at fact-claim 1))
    (guard (b1-logic-bookproof-normalize-proof lib test (cons nat arguments) nil nil nil))
    (step (library-inherited proof-proof-modus-ponens lib fact guard)))
   (cons step lib)))

(defun b1-powers-signed-power-addition (lib base i j integer-i integer-j number nonzero)
  (let ((test (library-lt i *proof-zero*))
        (arguments (list number nonzero integer-j)))
    (proof-with-checked-results
     ((negative-test (library-inherited proof-proof-assume lib test nil))
      (natural (library-library-cite lib "NATURAL-FROM-BOUNDS" (list i)
                                     (list integer-i negative-test)))
      (nonnegative-result (b1-powers-signed-power-addition-cite
                           *proof-one* i natural lib base j arguments))
      (lib (cdr nonnegative-result))
      (positive-neg (library-inherited proof-proof-assume lib test t))
      (order (library-library-comparison lib i *proof-zero* (list integer-i)))
      (positive-neg (library-inherited proof-proof-rewrite lib positive-neg order '(1)))
      (minus-i (library-minus i))
      (natural-neg-int (library-library-type-of lib minus-i (list integer-i)))
      (drop-zero (library-library-cite lib "ADD-ZERO-LEFT" (list minus-i) (list natural-neg-int)))
      (positive-neg (library-inherited proof-proof-rewrite lib positive-neg drop-zero '(1 2)))
      (neg-bound (library-library-cite lib "POSITIVE-NONNEGATIVE" (list minus-i)
                                      (list natural-neg-int positive-neg)))
      (natural-neg (library-library-cite lib "NATURAL-FROM-BOUNDS" (list minus-i)
                                        (list natural-neg-int neg-bound)))
      (negative-result (b1-powers-signed-power-addition-cite
                        *proof-neg-one* minus-i natural-neg lib base j arguments))
      (lib (cdr negative-result))
      (involution (library-library-cite lib "DOUBLE-NEGATION" (list i) (list integer-i)))
      (negative-step (library-inherited proof-proof-rewrite-first lib (car negative-result) involution))
      (step (library-inherited proof-proof-cases lib test negative-step (car nonnegative-result))))
     (cons step lib))))

(defun b1-powers-nonzero-fixed-base (lib base nonzero-fix)
  (let* ((proof (library-library-proof lib))
         (test (list *library-numberp* base))
         (call (list *b1-powers-fix* base))
         (unfold (list *b1-powers-fix*)))
    (proof-with-checked-results
     ((assumed (proof-proof-assume proof test nil))
      (fixed (b1-logic-bookproof-normalize lib call (list assumed) unfold nil nil nil nil))
      (cut (proof-proof-cut proof fixed nonzero-fix))
      (nonnumber (proof-proof-front proof cut test))
      (fixed-exact (b1-logic-bookproof-normalize lib call (list nonnumber) unfold nil nil nil nil))
      (nonzero (proof-proof-rewrite proof nonzero-fix fixed-exact '(1 1 1)))
      (nonzero (proof-proof-tidy proof nonzero)))
     (list nonnumber nonzero))))

(defun b1-powers-exponents-add-two-consequence (premise lib)
  (proof-with-checked-results
   ((parts (b1-logic-bookproof-split-conjuncts lib premise))
    (parts (proof-list-of-length parts 4))
    (nonzero (car parts))
    (number (cadr parts))
    (integral-i (caddr parts))
    (integral-j (cadddr parts))
    (number-claim (proof-step-first number))
    (base (proof-term-at number-claim 1))
    (i-claim (proof-step-first integral-i))
    (i (proof-term-at i-claim 1))
    (j-claim (proof-step-first integral-j))
    (j (proof-term-at j-claim 1))
    (reversed (b1-reciprocal-reverse-inequality lib nonzero)))
   (b1-powers-signed-power-addition lib base i j integral-i integral-j number reversed)))

(defun b1-powers-exponents-add-two (lib formula)
  (proof-with-checked-results
   ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
    (consequence (b1-powers-exponents-add-two-consequence premise lib))
    (lib (cdr consequence))
    (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car consequence))))
   (cons step lib)))

(defun b1-powers-exponent-addition-goal-terms (term)
  (if (proof-is-call term *b1-quotient-expt*)
      (proof-with-checked-results
       ((parts (proof-list-of-length term 3))
        (base (cadr parts))
        (total (caddr parts))
        (exponents (if (integerp total)
                       '(:failure "failure" "")
                     (proof-list-of-length (seq-slice total 1 :none) 2))))
       (list base (car exponents) (cadr exponents) total))
    (proof-with-checked-results
     ((parts (proof-list-of-length term 3))
      (lhs (cadr parts))
      (rhs (caddr parts))
      (base (proof-term-at lhs 1))
      (i (proof-term-at lhs 2))
      (j (proof-term-at rhs 2)))
     (list base i j (library-plus i j)))))

(defun b1-powers-exponent-addition-goal-signs (facts position signs)
  (if (endp facts)
      signs
    (proof-with-checked-results
     ((literal (proof-step-first (car facts)))
      (comparison (proof-term-at literal 1))
      (term (proof-term-at comparison position)))
     (b1-powers-exponent-addition-goal-signs
      (cdr facts) position (table-put signs term (car facts))))))

(defun b1-powers-exponent-addition-goal-sign (signs term)
  (let ((entry (assoc-equal term signs)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun b1-powers-exponent-addition-goal-negative
    (lib term other no-zero types signs)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((order (library-library-comparison lib term *proof-zero* types))
      (below (b1-arithmetic-integer-compare lib *proof-zero* term types))
      (sign (b1-powers-exponent-addition-goal-sign signs term))
      (below (proof-proof-discharge proof below sign))
      (reversed (b1-reciprocal-reverse-inequality lib no-zero))
      (below (proof-proof-discharge proof below reversed))
      (term-positive (proof-proof-rewrite proof below order '(1)))
      (signed (library-minus term))
      (signed-other (library-minus other))
      (flips (library-library-axiom lib "<-ON-OTHERS" (list *proof-zero* other)))
      (right (proof-rewritten-term flips))
      (delta (proof-term-at right 1))
      (delta (b1-arithmetic-number-sums-linear-equal lib delta signed-other types))
      (flips (proof-proof-rewrite proof flips delta '(1 2 1)))
      (other-sign (b1-powers-exponent-addition-goal-sign signs other))
      (bound (proof-proof-rewrite proof other-sign flips '(1 1)))
      (positive-claim (proof-step-first term-positive))
      (value (proof-term-at positive-claim 2))
      (delta (b1-arithmetic-number-sums-linear-equal lib value signed types))
      (term-positive (proof-proof-rewrite proof term-positive delta '(1 2))))
     (list signed signed-other term-positive bound))))

(defun b1-powers-exponent-addition-goal-nonnegative
    (lib term other no-zero types signs)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((comparison (b1-arithmetic-integer-compare lib term *proof-zero* types))
      (sign (b1-powers-exponent-addition-goal-sign signs term))
      (term-positive (proof-proof-discharge proof comparison sign))
      (term-positive (proof-proof-discharge proof term-positive no-zero))
      (bound (b1-powers-exponent-addition-goal-sign signs other)))
     (list term other term-positive bound))))

(defun b1-powers-exponent-addition-goal-same-sign
    (lib terms i-zero evidence types facts same-sign claim)
  (let* ((proof (library-library-proof lib))
         (i (cadr terms))
         (j (caddr terms))
         (total (cadddr terms))
         (term (if i-zero j i))
         (other (if i-zero i j))
         (no-zero (if i-zero (cadr evidence) (car evidence)))
         (positive (or (equal same-sign 1) (eq same-sign t))))
    (proof-with-checked-results
     ((signs (b1-powers-exponent-addition-goal-signs (take 2 facts)
                                                   (if positive 1 2) nil))
      (bounds (if (equal same-sign -1)
                  (b1-powers-exponent-addition-goal-negative
                   lib term other no-zero types signs)
                (b1-powers-exponent-addition-goal-nonnegative
                 lib term other no-zero types signs)))
      (term (car bounds))
      (other (cadr bounds))
      (int-other (library-library-type-of lib other types))
      (int-term (library-library-type-of lib term types))
      (step (library-library-cite lib "POSITIVE-PLUS-NONNEGATIVE" (list other term)
                                  (list int-other int-term (caddr bounds) (cadddr bounds))))
      (target (if positive total (library-minus total)))
      (literal (proof-step-first step))
      (value (proof-term-at literal 2))
      (delta (b1-arithmetic-number-sums-linear-equal lib value target types))
      (step (proof-proof-rewrite proof step delta '(1 2)))
      (step (proof-proof-rewrite-first proof step (caddr evidence)))
      (step (b1-arithmetic-simplify-first lib step))
      (step (proof-proof-tidy proof step)))
     (proof-proof-subsume proof step (cons claim (proof-step-clause step))))))

(defun b1-powers-exponent-addition-goal-opposite-cases-exponent-value
    (k is-zero equality integral lib base base-zero zero-base)
  (let ((call (b1-powers-expt base k)))
    (if (or is-zero base-zero)
        (b1-logic-bookproof-normalize lib call (list equality integral zero-base)
                                     (list *b1-quotient-expt* *b1-quotient-zip*
                                           *b1-quotient-numeric-eq*) nil nil nil nil)
      (library-inherited proof-proof-reflexive lib call))))

(defun b1-powers-exponent-addition-goal-opposite-cases-zero-product (term lib)
  (if (proof-is-call term *proof-times*)
      (proof-with-checked-results ((parts (proof-list-of-length (cdr term) 2)))
        (let ((a (car parts))
              (b (cadr parts)))
          (cond ((equal b *proof-zero*) (b1-arithmetic-multiply-zero lib a))
                ((equal a *proof-zero*)
                 (proof-with-checked-results
                  ((commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list a b)))
                   (product-zero (b1-arithmetic-multiply-zero lib b)))
                  (library-inherited proof-proof-chain lib commute (list product-zero))))
                (t nil))))
    nil))

(defund b1-powers-exponent-addition-goal-normalize-step (lib claim evidence rules replies)
  (proof-with-checked-results
   ((result (b1-logic-bookproof-normalize-proof-with-library
             lib claim evidence nil rules nil replies)))
   (cond ((b1-logic-call-p result)
          (let ((current (b1-logic-call-library result))
                (term (b1-logic-call-term result)))
            (proof-with-checked-results
             ((step (b1-powers-exponent-addition-goal-opposite-cases-zero-product term current)))
             (cons :reply (cons step current)))))
         ((b1-logic-branch-p result)
          '(:failure "failure" ""))
         (t (car result)))))

(defun b1-powers-exponent-addition-goal-normalize (n lib claim evidence rules replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "b1-powers-exponent-addition-goal-normalize")
    (let ((result (b1-powers-exponent-addition-goal-normalize-step
                   lib claim evidence rules replies)))
      (if (eq (car result) :reply)
          (b1-powers-exponent-addition-goal-normalize
           (1- n) lib claim evidence rules (append replies (list (cdr result))))
        result))))

(defun b1-powers-exponent-addition-goal-values
    (lib terms statuses evidence types int-total addition claim)
  (let ((base (car terms))
        (base-zero (cadddr statuses))
        (zero-base (cadddr evidence))
        (sum-zero (caddr statuses)))
    (proof-with-checked-results
     ((i-value (b1-powers-exponent-addition-goal-opposite-cases-exponent-value
                (cadr terms) (car statuses) (car evidence) (car types) lib base base-zero zero-base))
      (j-value (b1-powers-exponent-addition-goal-opposite-cases-exponent-value
                (caddr terms) (cadr statuses) (cadr evidence) (cadr types) lib base base-zero zero-base))
      (total-value (b1-powers-exponent-addition-goal-opposite-cases-exponent-value
                    (cadddr terms) sum-zero (caddr evidence) int-total lib base base-zero zero-base))
      (rules (list (b1-logic-equal-to i-value) (b1-logic-equal-to j-value)
                   (b1-logic-equal-to total-value)))
      (rules
       (if base-zero
           rules
         (proof-with-checked-results
          ((rule (if sum-zero
                     (proof-with-checked-results
                      ((reversed (library-inherited proof-proof-symmetric lib addition)))
                      (library-inherited proof-proof-chain lib reversed (list total-value)))
                   addition)))
          (append rules (list (b1-logic-equal-to rule)))))))
     (b1-powers-exponent-addition-goal-normalize
      1000000 lib claim evidence (append rules (list '(:callback :zero-product))) nil))))

(defun b1-powers-exponent-addition-goal-opposite-cases
    (predicates statuses evidence lib terms sum-test types int-total facts addition claim same-sign)
  (declare (xargs :measure (acl2-count predicates)))
  (let ((proof (library-library-proof lib)))
    (if (endp predicates)
        (let ((i-zero (car statuses))
              (j-zero (cadr statuses))
              (sum-zero (caddr statuses))
              (base-zero (cadddr statuses)))
          (cond
           ((and i-zero j-zero (not sum-zero))
            (proof-with-checked-results
             ((rules (list (b1-logic-equal-to (car evidence)) (b1-logic-equal-to (cadr evidence))))
              (equality (b1-logic-bookproof-normalize-proof lib sum-test nil nil rules nil)))
             (b1-logic-bookproof-contradiction lib equality (caddr evidence) claim)))
           ((and base-zero sum-zero same-sign (not (equal same-sign 0)) (not (and i-zero j-zero)))
            (b1-powers-exponent-addition-goal-same-sign lib terms i-zero evidence types facts
                                                      same-sign claim))
           (t (b1-powers-exponent-addition-goal-values lib terms statuses evidence types
                                                     int-total addition claim))))
      (let ((test (car predicates))
            (rest (cdr predicates)))
        (proof-with-checked-results
         ((assumed (proof-proof-assume proof test t))
          (yes (b1-powers-exponent-addition-goal-opposite-cases
                rest (append statuses (list t)) (append evidence (list assumed))
                lib terms sum-test types int-total facts addition claim same-sign))
          (assumed (proof-proof-assume proof test nil))
          (no (b1-powers-exponent-addition-goal-opposite-cases
               rest (append statuses (list nil)) (append evidence (list assumed))
               lib terms sum-test types int-total facts addition claim same-sign)))
         (proof-proof-cases proof test yes no))))))

(defun b1-powers-exponent-addition-goal-consequence-cases
    (lib terms tests facts types int-total claim same-sign)
  (let ((base (car terms))
        (i (cadr terms))
        (j (caddr terms)))
    (proof-with-checked-results
     ((assumed (library-inherited proof-proof-assume lib (cadddr tests) nil))
      (base-type (b1-powers-nonzero-fixed-base lib base assumed))
      (addition (b1-powers-signed-power-addition lib base i j (car types) (cadr types)
                                                (car base-type) (cadr base-type)))
      (lib (cdr addition))
      (step (b1-powers-exponent-addition-goal-opposite-cases
             tests nil nil lib terms (caddr tests) types int-total facts (car addition)
             claim same-sign)))
     (cons step lib))))

(defun b1-powers-exponent-addition-goal-consequence (premise lib terms tests claim same-sign)
  (proof-with-checked-results
   ((facts (b1-logic-bookproof-split-conjuncts lib premise))
    (types (proof-list-of-length (seq-slice facts -2 :none) 2))
    (int-total (library-library-type-of lib (cadddr terms) types))
    (i-claim (proof-step-first (car types))))
   (if (not (equal i-claim (library-integer (cadr terms))))
       '(:failure "failure" "")
     (proof-with-checked-results ((j-claim (proof-step-first (cadr types))))
       (if (not (equal j-claim (library-integer (caddr terms))))
           '(:failure "failure" "")
         (b1-powers-exponent-addition-goal-consequence-cases
          lib terms tests facts types int-total claim same-sign))))))

(defun b1-powers-exponent-addition-goal (lib formula same-sign)
  (proof-with-checked-results
   ((claim (proof-term-at formula 2))
    (term (proof-term-at claim 1))
    (terms (b1-powers-exponent-addition-goal-terms term))
    (fixed (proof-eq (list *b1-powers-fix* (car terms)) *proof-zero*))
    (tests (list (proof-eq (cadr terms) *proof-zero*)
                 (proof-eq (caddr terms) *proof-zero*)
                 (proof-eq (cadddr terms) *proof-zero*) fixed))
    (premise (b1-logic-bookproof-prove-implication-premise lib formula))
    (consequence (b1-powers-exponent-addition-goal-consequence
                  premise lib terms tests claim same-sign))
    (lib (cdr consequence))
    (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car consequence))))
   (cons step lib)))
