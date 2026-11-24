(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t2-round-ties-round* (proof-cl "ROUND"))

(defun t2-round-ties-first-at (step index)
  (proof-with-checked-results
    ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun t2-round-ties-replace-body (lib step equality)
  (proof-with-checked-results
    ((body (t2-round-ties-first-at step 2))
     (slot (t2-round-ties-first-at equality 1)))
    (proof-proof-rewrite-result (library-library-proof lib) step equality
                                (proof-eq *proof-zero* body) slot)))

(defun t2-round-ties-round-branch (lib opened tests)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
      ((body (t2-round-ties-first-at opened 2))
       (reduced (t2-arithmetic-simplify proof body tests (list *proof-not*))))
      (proof-proof-chain proof opened (list reduced)))))

(defun t2-round-ties-conditional-equation-choose (tests lib left right known)
  (let ((proof (library-library-proof lib))
        (evidence (append known tests)))
    (proof-with-checked-results
      ((a (t2-round-ties-round-branch lib left evidence))
       (b (t2-round-ties-round-branch lib right evidence))
       (back (proof-proof-symmetric proof b)))
      (proof-proof-chain proof a (list back)))))

(defun t2-round-ties-conditional-equation (lib left right below above known tie)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
      ((lower (proof-proof-assume proof below t))
       (not-lower (proof-proof-assume proof below nil))
       (higher (proof-proof-assume proof above t))
       (not-higher (proof-proof-assume proof above nil))
       (tied
        (if (eq tie :none)
            (t2-round-ties-conditional-equation-choose
             (list not-lower not-higher) lib left right known)
          (proof-with-checked-results
            ((at-tie (proof-proof-assume proof tie t))
             (yes (t2-round-ties-conditional-equation-choose
                   (list not-lower not-higher at-tie) lib left right known))
             (off-tie (proof-proof-assume proof tie nil))
             (no (t2-round-ties-conditional-equation-choose
                  (list not-lower not-higher off-tie) lib left right known)))
            (proof-proof-cases proof tie yes no))))
       (opposite (t2-order-opposite-order lib lower))
       (below-case (t2-round-ties-conditional-equation-choose
                    (list lower opposite) lib left right known))
       (above-case (t2-round-ties-conditional-equation-choose
                    (list not-lower higher) lib left right known))
       (other (proof-proof-cases proof above above-case tied)))
      (proof-proof-cases proof below below-case other))))

(defun t2-round-ties-integral-floor (lib cases tests unit)
  (proof-with-checked-results
    ((integral (proof-term-at tests 1))
     (literal (proof-step-first integral)))
    (if (equal literal (t2-quotient-rounding-quotient-cases-integral cases))
        (proof-with-checked-results
          ((value (t2-quotient-rounding-quotient-cases-value cases *t2-floor-floor* tests)))
          (library-library-transport-argument lib integral value 1))
      (proof-with-checked-results
        ((bracket (library-library-cite
                   lib "NONINTEGER-FLOOR-INTERVAL"
                   (list (t2-quotient-rounding-quotient-cases-ratio cases))
                   (list (first tests) integral)))
         (conjuncts (t2-arithmetic-arithmetic-conjunct lib bracket)))
        (library-library-transport-argument lib (first conjuncts) unit 1)))))

(defun t2-round-ties-unit-remainder (lib ratio unit integral)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
      ((remainder (proof-proof-unfold proof (list *t2-quotient-rounding-mod* ratio *proof-one*)))
       (unit-floor (t2-round-ties-first-at unit 2))
       (unit-type (proof-proof-rewrite proof integral unit '(1 1)))
       (number (t2-arithmetic-number lib unit-floor (list unit-type)))
       (multiplied (t2-field-identity lib unit-floor number *proof-times*))
       (remainder (proof-proof-rewrite proof remainder multiplied '(1 2 2 1)))
       (back (proof-proof-symmetric proof unit)))
      (proof-proof-rewrite proof remainder back '(1 2 2 1)))))

(defun t2-round-ties-negative-shift (lib ratio floor increment)
  (let ((proof (library-library-proof lib))
        (source (library-diff ratio increment)))
    (proof-with-checked-results
      ((start (t2-arithmetic-arithmetic-reflexive lib source))
       (distributed (library-library-axiom
                     lib "DISTRIBUTIVITY-OF-MINUS-OVER-+" (list *proof-one* floor)))
       (result (proof-proof-rewrite proof start distributed '(1 2 2)))
       (computed (proof-proof-compute proof (library-minus *proof-one*) -1))
       (result (proof-proof-rewrite proof result computed '(1 2 2 1)))
       (actual (t2-round-ties-first-at result 2))
       (normalized (t2-book-logic-ac-equal
                    lib actual (library-plus (library-diff ratio floor) *proof-neg-one*))))
      (proof-proof-chain proof result (list normalized)))))

(defun t2-round-ties-rational-integral (lib cases tests left right)
  (let ((proof (library-library-proof lib))
        (ratio (t2-quotient-rounding-quotient-cases-ratio cases)))
    (proof-with-checked-results
      ((value (t2-quotient-rounding-quotient-cases-value cases *t2-floor-floor* tests))
       (right (t2-round-ties-replace-body lib right value))
       (inverse (library-library-axiom lib "INVERSE-OF-+" (list ratio)))
       (right (t2-round-ties-replace-body lib right inverse))
       (comparison (t2-book-logic-constant lib (library-lt *proof-zero* *t2-exponent-parity-half*)))
       (true (proof-proof-true-from-eq proof comparison))
       (right (t2-round-ties-round-branch lib right (list true)))
       (back (proof-proof-symmetric proof right)))
      (proof-proof-chain proof left (list back)))))

(defun t2-round-ties-translate-negative-test (lib left first second slot)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
      ((comparison (library-library-cite lib "FIELD-ORDER-TRANSLATION"
                                         (list first second *proof-neg-one*) nil))
       (shifted-half (t2-book-logic-constant lib
                      (library-plus *t2-exponent-parity-half* *proof-neg-one*)))
       (comparison (proof-proof-rewrite proof comparison shifted-half (list 1 1 slot))))
      (t2-round-ties-replace-body lib left comparison))))

(defun t2-round-ties-rational-negative (lib ratio floor increment integral tests left remainder)
  (let ((proof (library-library-proof lib))
        (half *t2-exponent-parity-half*)
        (args (list *library-x* *library-y*)))
    (proof-with-checked-results
      ((ceiling (library-library-cite lib "CEILING-BY-FLOOR" args nil))
       (ceiling (t2-round-ties-round-branch lib ceiling tests))
       (ceiling-unit (library-library-cite lib "CEILING-UNIT-DIVISOR" args nil))
       (back (proof-proof-symmetric proof ceiling-unit))
       (ceiling (proof-proof-chain proof back (list ceiling)))
       (left (t2-round-ties-replace-body lib left ceiling))
       (integer-shift (t2-arithmetic-linear-equal
                       lib (library-plus increment *proof-neg-one*) floor (list integral)))
       (left (t2-round-ties-replace-body lib left integer-shift))
       (negative-shift (t2-round-ties-negative-shift lib ratio floor increment))
       (left (t2-round-ties-replace-body lib left negative-shift))
       (left (t2-round-ties-translate-negative-test lib left half remainder 1))
       (left (t2-round-ties-translate-negative-test lib left remainder half 2))
       (parity (library-library-cite lib "HALF-INTEGRAL-ALTERNATES" (list floor) (list integral)))
       (commuted (library-library-axiom lib "COMMUTATIVITY-OF-+" (list floor *proof-one*)))
       (parity (proof-proof-rewrite proof parity commuted '(1 1 1 2)))
       (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list half increment)))
       (parity (proof-proof-rewrite proof parity commuted '(1 1 1))))
      (list left parity))))

(defun t2-round-ties-rational-nonnegative (lib floor left unit even)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
      ((back (proof-proof-symmetric proof unit))
       (left (t2-round-ties-replace-body lib left back))
       (commuted (library-library-axiom lib "COMMUTATIVITY-OF-+" (list floor *proof-one*)))
       (left (t2-round-ties-replace-body lib left commuted))
       (back (proof-proof-symmetric proof even))
       (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list *t2-exponent-parity-half* floor)))
       (parity (proof-proof-rewrite proof back commuted '(1 1 1)))
       (parity (proof-proof-chain proof parity (list even))))
      (list left parity))))

(defun t2-round-ties-rational-round (lib cases opened expected tests)
  (let* ((proof (library-library-proof lib))
         (ratio (t2-quotient-rounding-quotient-cases-ratio cases))
         (floor (list *t2-floor-floor* *library-x* *library-y*))
         (increment (library-plus *proof-one* floor)))
    (proof-with-checked-results
      ((unit (library-library-cite lib "FLOOR-UNIT-DIVISOR" (list *library-x* *library-y*) nil))
       (integral (t2-round-ties-integral-floor lib cases tests unit))
       (even (proof-proof-fact proof (proof-sym "SELF-EVEN-HALF-INTEGRAL" "ACL2")
                               (list (list *library-y* floor))))
       (reflexive (t2-arithmetic-arithmetic-reflexive lib expected))
       (right (t2-round-ties-round-branch lib reflexive tests))
       (unit-remainder (t2-round-ties-unit-remainder lib ratio unit integral))
       (right (t2-round-ties-replace-body lib right unit-remainder))
       (right (t2-round-ties-replace-body lib right even))
       (left (t2-round-ties-round-branch lib opened tests))
       (integer-test (proof-term-at tests 1))
       (integer-literal (proof-step-first integer-test)))
      (if (equal integer-literal (t2-quotient-rounding-quotient-cases-integral cases))
          (t2-round-ties-rational-integral lib cases tests left right)
        (let ((remainder (library-diff ratio floor))
              (half *t2-exponent-parity-half*))
          (proof-with-checked-results
            ((sign-test (proof-term-at tests 2))
             (sign (proof-step-first sign-test))
             (branch
              (if (equal sign (t2-quotient-rounding-quotient-cases-negative cases))
                  (t2-round-ties-rational-negative
                   lib ratio floor increment integral tests left remainder)
                (t2-round-ties-rational-nonnegative lib floor left unit even)))
             (half-value (t2-book-logic-constant lib (t2-field-reciprocal *t2-half-parity-two*)))
             (left (t2-round-ties-replace-body lib (first branch) half-value))
             (left (t2-round-ties-replace-body lib left (second branch))))
            (t2-round-ties-conditional-equation
             lib left right (library-lt remainder half) (library-lt half remainder)
             nil (t2-exponent-parity-half-integral floor))))))))

(defun t2-round-ties-nonrational-impossible (lib comparison beyond negative)
  (let ((proof (library-library-proof lib)))
    (if negative
        (proof-with-checked-results
          ((constant (t2-book-logic-constant lib (library-lt *proof-zero* *t2-exponent-parity-half*)))
           (bound (proof-proof-true-from-eq proof constant))
           (chained (t2-order-strict-chain lib bound beyond))
           (lib (cdr chained))
           (opposite (t2-order-opposite-order lib comparison))
           (cut (proof-proof-cut (library-library-proof lib) (car chained) opposite)))
          (cons cut lib))
      (proof-with-checked-results
        ((constant (t2-book-logic-constant lib (library-lt *t2-half-parity-neg-half* *proof-zero*)))
         (bound (proof-proof-true-from-eq proof constant))
         (chained (t2-order-strict-chain lib beyond bound))
         (lib (cdr chained))
         (cut (proof-proof-cut (library-library-proof lib) (car chained) comparison)))
        (cons cut lib)))))

(defun t2-round-ties-nonrational-branch (lib cases opened right not-rational not-integer
                                        negative function threshold)
  (let* ((proof (library-library-proof lib))
         (ratio (t2-quotient-rounding-quotient-cases-ratio cases))
         (half *t2-exponent-parity-half*)
         (zero *proof-zero*)
         (adjustment (if negative -1 1))
         (excluded (if negative (library-lt half ratio)
                     (library-lt ratio *t2-half-parity-neg-half*))))
    (proof-with-checked-results
      ((comparison (proof-proof-assume
                    proof (t2-quotient-rounding-quotient-cases-negative cases) negative))
       (left (t2-round-ties-round-branch lib opened (list not-integer comparison)))
       (unit (library-library-cite lib (concatenate 'string (third function) "-UNIT-DIVISOR")
                                    (list *library-x* *library-y*) nil))
       (back (proof-proof-symmetric proof unit))
       (value (t2-quotient-rounding-quotient-cases-value cases function (list not-rational)))
       (zero-value (proof-proof-chain proof back (list value)))
       (left (t2-round-ties-replace-body lib left zero-value))
       (start (t2-arithmetic-arithmetic-reflexive lib (library-diff ratio zero)))
       (computed (proof-proof-compute proof (library-minus zero) 0))
       (remainder (proof-proof-rewrite proof start computed '(1 2 2)))
       (numeric (t2-field-number lib ratio))
       (identity (t2-field-identity lib ratio numeric *proof-plus*))
       (remainder (proof-proof-chain proof remainder (list identity)))
       (left (t2-round-ties-replace-body lib left remainder))
       (half-value (t2-book-logic-constant lib (t2-field-reciprocal *t2-half-parity-two*)))
       (left (t2-round-ties-replace-body lib left half-value))
       (zero-half (t2-book-logic-constant lib (t2-products-times zero half)))
       (left (t2-round-ties-replace-body lib left zero-half))
       (integer-zero (proof-proof-compute proof (library-integer zero) *proof-t*))
       (left (t2-round-ties-replace-body lib left integer-zero))
       (plus-unit (proof-proof-compute proof (library-plus zero (proof-quote adjustment)) adjustment))
       (left (t2-round-ties-replace-body lib left plus-unit))
       (beyond (proof-proof-assume proof excluded t))
       (impossible (t2-round-ties-nonrational-impossible lib comparison beyond negative))
       (lib (cdr impossible))
       (unneeded (proof-proof-front (library-library-proof lib) (car impossible) (proof-neg excluded)))
       (branch (t2-round-ties-conditional-equation
                lib left right (library-lt ratio threshold) (library-lt threshold ratio)
                (list unneeded) :none)))
      (cons branch lib))))

(defun t2-round-ties-nonrational-round (lib cases opened expected not-rational)
  (let ((proof (library-library-proof lib))
        (ratio (t2-quotient-rounding-quotient-cases-ratio cases))
        (integral (t2-quotient-rounding-quotient-cases-integral cases))
        (negative (t2-quotient-rounding-quotient-cases-negative cases)))
    (proof-with-checked-results
      ((integer-test (proof-proof-assume proof integral t))
       (integer-rational (t2-arithmetic-rational lib ratio (list integer-test)))
       (contradiction (proof-proof-cut proof integer-rational not-rational))
       (not-integer (proof-proof-front proof contradiction (proof-neg integral)))
       (start (t2-arithmetic-arithmetic-reflexive lib expected))
       (right (t2-round-ties-round-branch lib start (list not-rational)))
       (yes (t2-round-ties-nonrational-branch lib cases opened right not-rational not-integer
                                             t *t2-quotient-rounding-ceiling* *t2-half-parity-neg-half*))
       (lib (cdr yes))
       (no (t2-round-ties-nonrational-branch lib cases opened right not-rational not-integer
                                            nil *t2-floor-floor* *t2-exponent-parity-half*))
       (lib (cdr no))
       (step (proof-proof-cases (library-library-proof lib) negative (car yes) (car no))))
      (cons step lib))))

(defun t2-round-ties-build-branch (tests lib cases opened expected)
  (proof-with-checked-results
    ((rat (proof-term-at tests 0))
     (literal (proof-step-first rat)))
    (if (equal literal (t2-quotient-rounding-quotient-cases-rat cases))
        (proof-with-checked-results
          ((step (t2-round-ties-rational-round lib cases opened expected tests)))
          (cons step lib))
      (t2-round-ties-nonrational-round lib cases opened expected rat))))

(defun t2-round-ties-build-prove (n cases opened expected replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t2-round-ties-build-prove")
    (proof-with-checked-results
      ((result (t2-quotient-rounding-quotient-cases-prove-with-library cases replies nil)))
      (if (t2-quotient-rounding-branch-request-p result)
          (let* ((tests (t2-quotient-rounding-branch-request-tests result))
                 (lib (t2-quotient-rounding-branch-request-lib result))
                 (branch-cases (t2-quotient-rounding-quotient-cases-init
                                lib
                                (t2-quotient-rounding-quotient-cases-dividend cases)
                                (t2-quotient-rounding-quotient-cases-divisor cases))))
            (proof-with-checked-results
              ((branch (t2-round-ties-build-branch tests lib branch-cases opened expected))
               (replies (table-put replies tests branch)))
              (t2-round-ties-build-prove (1- n) cases opened expected replies)))
        result))))

(defun t2-round-ties-build (lib)
  (let* ((x *library-x*)
         (y *library-y*)
         (cases (t2-quotient-rounding-quotient-cases-init lib x y))
         (ratio (t2-quotient-rounding-quotient-cases-ratio cases))
         (floor (list *t2-floor-floor* x y))
         (remainder (list *t2-quotient-rounding-mod* ratio *proof-one*))
         (increment (library-plus *proof-one* floor))
         (half *t2-exponent-parity-half*)
         (rational
          (proof-ite (library-lt remainder half) floor
                     (proof-ite (library-lt half remainder) increment
                                (proof-ite (list *t2-exponent-parity-evenp* floor) floor increment))))
         (nonrational
          (proof-ite (library-lt half ratio) *proof-one*
                     (proof-ite (library-lt ratio *t2-half-parity-neg-half*)
                                *proof-neg-one* *proof-zero*)))
         (expected (proof-ite (proof-neg (t2-quotient-rounding-quotient-cases-rat cases))
                              nonrational rational)))
    (proof-with-checked-results
      ((opened (t2-quotient-rounding-opened-rounding lib *t2-round-ties-round* x y))
       (result (t2-round-ties-build-prove 1000000 cases opened expected nil))
       (step (car result))
       (claim (proof-step-first step)))
      (library-library-lemma (cdr result) "ROUND-BY-FLOOR" claim step nil))))
