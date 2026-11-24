(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun t2-floor-thresholds-step-argument (step index)
  (if step
      (proof-with-checked-results ((literal (proof-step-first step)))
        (proof-term-at literal index))
    '(:failure "failure" "")))

(defun t2-floor-thresholds-current-cases (cases before after)
  (if (and (not (equal before after))
           (equal (t2-quotient-rounding-quotient-cases-lib cases) before))
      (t2-quotient-rounding-quotient-cases-with-lib cases after)
    cases))

(defun t2-floor-thresholds-floor-with-zero-ratio (lib cases product)
  (proof-with-checked-results
      ((zero-type (t2-arithmetic-arithmetic-type-of lib *proof-zero* nil))
       (integral (library-library-transport-argument lib zero-type product 1))
       (ratio (t2-arithmetic-rational
               lib (t2-quotient-rounding-quotient-cases-ratio cases)
               (list integral)))
       (value (t2-quotient-rounding-quotient-cases-value
               cases *t2-floor-floor* (list ratio integral))))
    (proof-proof-chain (library-library-proof lib) value (list product))))

(defun t2-floor-thresholds-fixed-zero-floor (lib cases zero)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reciprocal-value (t2-field-reciprocal-zero lib *library-y* zero))
         (reflexive (proof-proof-reflexive
                     proof (t2-quotient-rounding-quotient-cases-ratio cases)))
         (product (proof-proof-rewrite proof reflexive reciprocal-value '(1 2 2)))
         (zero-result (t2-products-product-zero lib *library-x*))
         (next-lib (cdr zero-result))
         (product (proof-proof-chain (library-library-proof next-lib)
                                     product (list (car zero-result))))
         (floor (t2-floor-thresholds-floor-with-zero-ratio
                 next-lib
                 (t2-floor-thresholds-current-cases cases lib next-lib)
                 product)))
      (cons floor next-lib))))

(defun t2-floor-thresholds-below-integer (lib cases floor)
  (let ((q (t2-quotient-rounding-quotient-cases-ratio cases))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((ratio (proof-proof-assume
                 proof (t2-quotient-rounding-quotient-cases-rat cases) t))
         (thresholds (library-library-ints lib (list *library-z*)))
         (threshold (car thresholds))
         (bracket (library-library-cite
                   lib "RATIONAL-QUOTIENT-FLOOR-BRACKET"
                   (list *library-x* *library-y*) (list ratio)))
         (parts (t2-power-conjuncts lib bracket 3))
         (integral (car parts))
         (low (cadr parts))
         (high (caddr parts))
         (rat-floor (t2-arithmetic-rational lib floor (list integral)))
         (left (library-lt floor *library-z*))
         (right (library-lt q *library-z*))
         (assume-right (proof-proof-assume proof right t))
         (left-result (t2-rounding-weak-then-strict
                       lib low assume-right (list ratio rat-floor)))
         (lib (cdr left-result))
         (proof (library-library-proof lib))
         (assume-left (proof-proof-assume proof left t))
         (step (t2-products-discrete-step lib assume-left (list integral threshold)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-+" (list *proof-one* floor)))
         (step (proof-proof-rewrite proof step commute '(1 1 2)))
         (rat-next (t2-arithmetic-rational lib (library-plus floor *proof-one*) (list integral)))
         (rat-threshold (t2-arithmetic-rational lib *library-z* (list threshold)))
         (right-result (t2-power-products-strict-then-weak
                        lib high step (list rat-next rat-threshold)))
         (lib (cdr right-result))
         (left-boolean (t2-order-boolean-less lib left))
         (right-boolean (t2-order-boolean-less lib right))
         (result (t2-field-equal-predicates
                  lib left right (car right-result) (car left-result)
                  left-boolean right-boolean))
         (claim (proof-step-first (car result)))
         (ratio-test (proof-step-first ratio))
         (threshold-test (proof-step-first threshold)))
      (library-library-lemma
       (cdr result) "FLOOR-BELOW-INTEGER-THRESHOLD" claim (car result)
       (library-guards (list ratio-test threshold-test))))))

(defun t2-floor-thresholds-deny-positive-floor
    (proof quotient-cap below-one negative-floor-cap test)
  (proof-with-checked-results
      ((bound (proof-proof-assume proof quotient-cap t))
       (transported (proof-proof-transport proof bound below-one))
       (contradiction (proof-proof-cut proof transported negative-floor-cap)))
    (proof-proof-front proof contradiction (proof-neg test))))

(defun t2-floor-thresholds-positive-test-branch (proof value quotient-cap holds)
  (proof-with-checked-results
      ((evidence (proof-proof-assume proof quotient-cap holds))
       (simplified (t2-arithmetic-simplify
                    proof (proof-neg quotient-cap) (list evidence) (list *proof-not*)))
       (reversed (proof-proof-symmetric proof simplified)))
    (proof-proof-chain proof value (list reversed))))

(defun t2-floor-thresholds-zero-test-branch (lib rhs nonnegative quotient-cap value holds)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((capped (proof-proof-assume proof quotient-cap holds))
         (reduced (t2-arithmetic-simplify proof rhs (list nonnegative) (list *proof-not*)))
         (truth (t2-rational-scaling-truth-value lib quotient-cap capped))
         (lib (cdr truth))
         (proof (library-library-proof lib))
         (reduced (proof-proof-chain proof reduced (list (car truth))))
         (reversed (proof-proof-symmetric proof reduced))
         (branch (proof-proof-chain proof value (list reversed))))
      (cons branch lib))))

(defun t2-floor-thresholds-zero-quotient-test
    (lib floor ratio floor-type below-one quotient-cap negative-floor-cap test positive-floor)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((zero-type (t2-arithmetic-arithmetic-type-of lib *proof-zero* nil))
         (below-zero (library-library-cite
                      lib "FLOOR-BELOW-INTEGER-THRESHOLD"
                      (list *library-x* *library-y* *proof-zero*) (list ratio zero-type)))
         (quotient-negative (t2-floor-thresholds-step-argument below-zero 2))
         (rhs (proof-ite (proof-neg quotient-negative) quotient-cap *proof-false*))
         (negative (proof-proof-assume proof quotient-negative t))
         (floor-negative (proof-proof-transport proof negative below-zero))
         (distinct (t2-order-distinct lib floor-negative))
         (no (t2-field-false-value lib distinct))
         (reduced (t2-arithmetic-simplify proof rhs (list negative) (list *proof-not*)))
         (reversed (proof-proof-symmetric proof reduced))
         (no (proof-proof-chain proof no (list reversed)))
         (nonnegative (proof-proof-assume proof quotient-negative nil))
         (not-negative (library-library-transport-argument lib nonnegative below-zero 1))
         (not-positive (t2-floor-thresholds-deny-positive-floor
                        proof quotient-cap below-one negative-floor-cap test))
         (numeric (t2-arithmetic-number lib floor (list floor-type)))
         (zero (t2-order-zero-from-sign lib floor not-positive not-negative numeric))
         (within (t2-field-true-equality lib zero))
         (distinct (t2-order-distinct lib positive-floor))
         (reverse-distinct (t2-products-flip-neq lib distinct))
         (outside (t2-field-false-value lib reverse-distinct))
         (inside (t2-floor-thresholds-zero-test-branch
                  lib rhs nonnegative quotient-cap within t))
         (outside (t2-floor-thresholds-zero-test-branch
                   (cdr inside) rhs nonnegative quotient-cap outside nil))
         (lib (cdr outside))
         (proof (library-library-proof lib))
         (branch (proof-proof-cases proof quotient-cap (car inside) (car outside)))
         (step (proof-proof-cases proof quotient-negative no branch))
         (claim (proof-step-first step))
         (ratio-test (proof-step-first ratio)))
      (library-library-lemma lib "FLOOR-ZERO-QUOTIENT-TEST" claim step
                             (list (proof-neg ratio-test))))))

(defun t2-floor-thresholds-sign-and-zero (lib cases floor)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((ratio (proof-proof-assume
                 proof (t2-quotient-rounding-quotient-cases-rat cases) t))
         (floor-type (library-library-cite lib "FLOOR-IS-INTEGER"
                                          (list *library-x* *library-y*) nil))
         (one (t2-arithmetic-arithmetic-type-of lib *proof-one* nil))
         (below-one (library-library-cite
                     lib "FLOOR-BELOW-INTEGER-THRESHOLD"
                     (list *library-x* *library-y* *proof-one*) (list ratio one)))
         (literal (proof-step-first below-one))
         (parts (proof-list-of-length (cdr literal) 2))
         (quotient-cap (cadr parts))
         (test (library-positive floor))
         (yes (proof-proof-assume proof test t))
         (negative-floor-cap (t2-numeric-types-one-bound lib yes floor-type))
         (no (t2-floor-thresholds-deny-positive-floor
              proof quotient-cap below-one negative-floor-cap test))
         (above-cap (proof-proof-assume proof quotient-cap nil))
         (above-one (library-library-transport-argument lib above-cap below-one 1))
         (one-positive (t2-arithmetic-arithmetic-prove
                        lib (library-lt *proof-zero* *proof-one*) nil nil))
         (one-rational (t2-arithmetic-rational lib *proof-one* nil))
         (floor-rational (t2-arithmetic-rational lib floor (list floor-type)))
         (positive-result (t2-power-products-strict-then-weak
                           lib one-positive above-one (list one-rational floor-rational)))
         (positive-floor (car positive-result))
         (lib (cdr positive-result))
         (left (t2-field-false-value lib no))
         (right (t2-rational-scaling-truth-value lib test positive-floor))
         (lib (cdr right))
         (proof (library-library-proof lib))
         (yes-branch (t2-floor-thresholds-positive-test-branch proof left quotient-cap t))
         (no-branch (t2-floor-thresholds-positive-test-branch proof (car right) quotient-cap nil))
         (positive-test (proof-proof-cases proof quotient-cap yes-branch no-branch))
         (claim (proof-step-first positive-test))
         (ratio-test (proof-step-first ratio))
         (lib (library-library-lemma lib "FLOOR-POSITIVE-QUOTIENT-TEST" claim positive-test
                                     (list (proof-neg ratio-test)))))
      (t2-floor-thresholds-zero-quotient-test
       lib floor ratio floor-type below-one quotient-cap negative-floor-cap test positive-floor))))

(defun t2-floor-thresholds-signed-quotient-test (lib cases threshold sign increasing)
  (let ((q (t2-quotient-rounding-quotient-cases-ratio cases)))
    (proof-with-checked-results
        ((parts (t2-floor-bracket-signed-divisor lib sign))
         (numeric (cadr parts))
         (different (caddr parts))
         (ratio (proof-proof-assume
                 (library-library-proof lib)
                 (t2-quotient-rounding-quotient-cases-rat cases) t))
         (threshold-rational (t2-arithmetic-rational lib threshold nil))
         (comparison (library-library-cite
                      lib "RATIONAL-OPERANDS-SIGNED-ORDER"
                      (list q threshold *library-y*)
                      (list ratio threshold-rational numeric different)))
         (sign-test (if increasing sign (t2-order-opposite-order lib sign)))
         (comparison (t2-input-fields-select lib comparison sign-test))
         (unit (if (equal threshold *proof-zero*)
                   (t2-products-product-zero lib *library-y*)
                 (proof-with-checked-results
                     ((identity (t2-field-identity lib *library-y* numeric *proof-times*)))
                   (cons identity lib))))
         (lib (cdr unit))
         (proof (library-library-proof lib))
         (side (if increasing 2 1))
         (comparison (proof-proof-rewrite proof comparison (car unit) (list 1 2 side)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list *library-y* q)))
         (cancelled (t2-quotient-rounding-cancel-divisor lib *library-x* *library-y* (car parts)))
         (cancelled (proof-proof-chain proof commute (list cancelled)))
         (comparison (proof-proof-rewrite proof comparison cancelled (list 1 2 (- 3 side))))
         (value (if (equal threshold *proof-zero*) *proof-zero* *library-y*))
         (args (if increasing (list *library-x* value) (list value *library-x*)))
         (fixed-test (library-library-cite lib "FIELD-FIX-ORDER" args nil))
         (value-type (if (equal threshold *proof-zero*)
                         (t2-arithmetic-number lib *proof-zero* nil)
                       numeric))
         (fix (t2-field-numeric-fix lib value value-type))
         (fixed-test (proof-proof-rewrite proof fixed-test fix (list 1 2 side)))
         (reversed (proof-proof-symmetric proof fixed-test))
         (comparison (proof-proof-chain proof comparison (list reversed))))
      (cons (list comparison different) lib))))

(defun t2-floor-thresholds-rewrite-zero-test (lib condition side)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (t2-floor-thresholds-step-argument condition 1))
         (comparison (library-library-cite lib "FIELD-FIX-ORDER" (cdr test) nil))
         (numeric (t2-arithmetic-number lib *proof-zero* nil))
         (fix (t2-field-numeric-fix lib *proof-zero* numeric))
         (comparison (proof-proof-rewrite proof comparison fix (list 1 2 side))))
      (proof-proof-rewrite proof condition comparison '(1 1)))))

(defun t2-floor-thresholds-no-sign-floor (lib cases no-positive no-negative)
  (let ((fixed-value (t2-field-fixed *library-y*)))
    (proof-with-checked-results
        ((nonpositive (t2-floor-thresholds-rewrite-zero-test lib no-positive 1))
         (nonnegative (t2-floor-thresholds-rewrite-zero-test lib no-negative 2))
         (numeric (t2-field-number lib fixed-value))
         (zero (t2-order-zero-from-sign lib fixed-value nonpositive nonnegative numeric)))
      (t2-floor-thresholds-fixed-zero-floor lib cases zero))))

(defun t2-floor-thresholds-reduce-with-evidence (lib result value known)
  (declare (xargs :measure (acl2-count known)))
  (if (endp known)
      (cons result lib)
    (let ((evidence (car known))
          (proof (library-library-proof lib)))
      (proof-with-checked-results ((literal (proof-step-first evidence)))
        (let ((matches (or (equal literal value) (equal literal (proof-neg value)))))
          (cond
           ((and matches (proof-is-call value *proof-less*))
            (proof-with-checked-results
                ((truth (t2-rational-scaling-truth-value lib value evidence))
                 (lib (cdr truth))
                 (step (proof-proof-chain (library-library-proof lib) result (list (car truth)))))
              (cons step lib)))
           ((and matches (proof-is-call value *proof-equal*))
            (proof-with-checked-results
                ((equality (if (equal literal value)
                               (t2-field-true-equality lib evidence)
                             (t2-field-false-value lib evidence)))
                 (step (proof-proof-chain proof result (list equality))))
              (cons step lib)))
           (t (t2-floor-thresholds-reduce-with-evidence lib result value (cdr known)))))))))

(defun t2-floor-thresholds-case-alignment-reduce (step lib known)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((body (t2-floor-thresholds-step-argument step 2))
         (simplified (t2-arithmetic-simplify proof body known (list *proof-not*)))
         (result (proof-proof-chain proof step (list simplified)))
         (value (t2-floor-thresholds-step-argument result 2)))
      (t2-floor-thresholds-reduce-with-evidence lib result value known))))

(defun t2-floor-thresholds-case-alignment (lib left right known tests)
  (declare (xargs :measure (acl2-count tests)))
  (proof-with-checked-results
      ((a (t2-floor-thresholds-case-alignment-reduce left lib known))
       (b (t2-floor-thresholds-case-alignment-reduce right (cdr a) known))
       (lib (cdr b))
       (proof (library-library-proof lib))
       (a-body (t2-floor-thresholds-step-argument (car a) 2))
       (b-body (t2-floor-thresholds-step-argument (car b) 2)))
    (cond
     ((equal a-body b-body)
      (proof-with-checked-results
          ((reversed (proof-proof-symmetric proof (car b)))
           (step (proof-proof-chain proof (car a) (list reversed))))
        (cons step lib)))
     ((endp tests)
      '(:failure "failure" ""))
     (t
      (let ((test (car tests))
            (rest (cdr tests)))
        (proof-with-checked-results
            ((assume-yes (proof-proof-assume proof test t))
             (yes (t2-floor-thresholds-case-alignment
                   lib left right (append known (list assume-yes)) rest))
             (lib (cdr yes))
             (proof (library-library-proof lib))
             (assume-no (proof-proof-assume proof test nil))
             (no (t2-floor-thresholds-case-alignment
                  lib left right (append known (list assume-no)) rest))
             (lib (cdr no))
             (step (proof-proof-cases (library-library-proof lib) test (car yes) (car no))))
          (cons step lib)))))))

(defun t2-floor-thresholds-floor-sign-branch
    (lib cases threshold normalized expected sign-test increasing decisions)
  (proof-with-checked-results
      ((sign (proof-proof-assume (library-library-proof lib) sign-test t))
       (signed (t2-floor-thresholds-signed-quotient-test lib cases threshold sign increasing))
       (relation (caar signed))
       (lib (cdr signed))
       (specialized (t2-round-ties-replace-body lib normalized relation))
       (decisions (if decisions
                      decisions
                    (proof-with-checked-results
                        ((body (t2-floor-thresholds-step-argument relation 2)))
                      (list body))))
       (opposite (t2-order-opposite-order lib sign)))
    (t2-floor-thresholds-case-alignment lib specialized expected (list sign opposite) decisions)))

(defun t2-floor-thresholds-express-floor-sign
    (lib cases pos-y neg-y pos-x neg-x rat positive-floor)
  (proof-with-checked-results
      ((threshold (if positive-floor *proof-one* *proof-zero*))
       (normalized
        (if positive-floor
            (library-library-cite lib "FLOOR-POSITIVE-QUOTIENT-TEST"
                                  (list *library-x* *library-y*) (list rat))
          (proof-with-checked-results
              ((zero-type (t2-arithmetic-arithmetic-type-of lib *proof-zero* nil)))
            (library-library-cite lib "FLOOR-BELOW-INTEGER-THRESHOLD"
                                  (list *library-x* *library-y* *proof-zero*) (list rat zero-type)))))
       (forward (if positive-floor
                    (proof-ite pos-y (proof-neg (library-lt *library-x* *library-y*)) *proof-false*)
                  (proof-ite pos-x neg-y *proof-false*)))
       (backward (if positive-floor
                     (proof-ite neg-y (proof-neg (library-lt *library-y* *library-x*)) *proof-false*)
                   (proof-ite neg-x pos-y *proof-false*)))
       (expected (proof-proof-reflexive
                  (library-library-proof lib) (proof-ite forward forward backward)))
       (decisions (if positive-floor nil (list pos-x neg-x)))
       (yes (t2-floor-thresholds-floor-sign-branch
             lib cases threshold normalized expected pos-y t decisions))
       (yes-lib (cdr yes))
       (no (t2-floor-thresholds-floor-sign-branch
            yes-lib cases threshold normalized expected neg-y nil decisions))
       (next-lib (cdr no))
       (proof (library-library-proof next-lib))
       (no-positive (proof-proof-assume proof pos-y nil))
       (no-negative (proof-proof-assume proof neg-y nil))
       (zero (t2-floor-thresholds-no-sign-floor
              next-lib (t2-floor-thresholds-current-cases cases lib next-lib)
              no-positive no-negative))
       (lib (cdr zero))
       (proof (library-library-proof lib))
       (index (if positive-floor 2 1))
       (lhs (t2-floor-thresholds-step-argument normalized 1))
       (reflexive (proof-proof-reflexive proof lhs))
       (no-floor (proof-proof-rewrite proof reflexive (car zero) (list 1 2 index)))
       (zero-axiom (library-library-axiom lib "ZERO" nil))
       (false (t2-field-false-value lib zero-axiom))
       (no-floor (proof-proof-chain proof no-floor (list false)))
       (absent (t2-floor-thresholds-case-alignment
                lib no-floor expected (list no-positive no-negative) decisions))
       (lib (cdr absent))
       (proof (library-library-proof lib))
       (when-nonpositive (proof-proof-cases proof neg-y (car no) (car absent)))
       (step (proof-proof-cases proof pos-y (car yes) when-nonpositive))
       (claim (proof-step-first step))
       (rat-test (proof-step-first rat)))
    (library-library-lemma lib (if positive-floor
                                   "FLOOR-POSITIVE-DIVISOR-TEST"
                                 "FLOOR-NEGATIVE-DIVISOR-TEST")
                           claim step (list (proof-neg rat-test)))))

(defun t2-floor-thresholds-express-floor-signs (lib cases)
  (let ((pos-y (library-positive *library-y*))
        (neg-y (library-lt *library-y* *proof-zero*))
        (pos-x (library-positive *library-x*))
        (neg-x (library-lt *library-x* *proof-zero*)))
    (proof-with-checked-results
        ((rat (proof-proof-assume (library-library-proof lib)
                                 (t2-quotient-rounding-quotient-cases-rat cases) t))
         (positive (t2-floor-thresholds-express-floor-sign lib cases pos-y neg-y pos-x neg-x rat t)))
      (t2-floor-thresholds-express-floor-sign
       positive (t2-floor-thresholds-current-cases cases lib positive)
       pos-y neg-y pos-x neg-x rat nil))))

(defun t2-floor-thresholds-impossible-interval (lib condition comparison sign)
  (proof-with-checked-results
      ((amount (proof-proof-assume (library-library-proof lib) comparison t))
       (endpoint (proof-term-at condition 1))
       (passed (if (equal endpoint *proof-zero*)
                   (t2-order-strict-chain lib sign amount)
                 (t2-order-strict-chain lib amount sign)))
       (lib (cdr passed))
       (proof (library-library-proof lib))
       (opposite (proof-proof-assume proof condition nil))
       (cut (proof-proof-cut proof (car passed) opposite))
       (not-comparison (proof-proof-front proof cut (proof-neg comparison)))
       (test (proof-ite (proof-neg condition) comparison *proof-false*))
       (evidence (proof-proof-assume proof condition t))
       (yes (t2-arithmetic-simplify proof test (list evidence) (list *proof-not*)))
       (reduced (t2-arithmetic-simplify proof test (list opposite) (list *proof-not*)))
       (false (t2-field-false-value lib not-comparison))
       (no (proof-proof-chain proof reduced (list false)))
       (step (proof-proof-cases proof condition yes no)))
    (cons step lib)))

(defun t2-floor-thresholds-floor-zero-branch
    (lib cases rat expected forward condition comparison sign increasing)
  (proof-with-checked-results
      ((step (library-library-cite lib "FLOOR-ZERO-QUOTIENT-TEST"
                                   (list *library-x* *library-y*) (list rat)))
       (zero-relation (t2-floor-thresholds-signed-quotient-test lib cases *proof-zero* sign increasing))
       (lib (cdr zero-relation))
       (step (t2-round-ties-replace-body lib step (caar zero-relation)))
       (one-relation (t2-floor-thresholds-signed-quotient-test lib cases *proof-one* sign increasing))
       (lib (cdr one-relation))
       (step (t2-round-ties-replace-body lib step (caar one-relation)))
       (rhs (proof-proof-select (library-library-proof lib) expected (cadar zero-relation)))
       (impossible (t2-floor-thresholds-impossible-interval lib condition comparison sign))
       (lib (cdr impossible))
       (proof (library-library-proof lib))
       (rhs (t2-round-ties-replace-body lib rhs (car impossible)))
       (reduced
        (if increasing
            (t2-field-cancellation-guarded-identity lib forward)
          (proof-with-checked-results ((body (t2-floor-thresholds-step-argument rhs 2)))
            (t2-arithmetic-simplify proof body nil nil))))
       (rhs (proof-proof-chain proof rhs (list reduced)))
       (reversed (proof-proof-symmetric proof rhs))
       (step (proof-proof-chain proof step (list reversed))))
    (cons step lib)))

(defun t2-floor-thresholds-express-floor-zero (lib cases)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((rat (proof-proof-assume proof (t2-quotient-rounding-quotient-cases-rat cases) t))
         (numeric (proof-proof-assume proof (list *library-numberp* *library-y*) t))
         (zero-y (proof-eq *library-y* *proof-zero*))
         (pos-y (library-positive *library-y*))
         (pos-x (library-positive *library-x*))
         (neg-x (library-lt *library-x* *proof-zero*))
         (forward (proof-ite (proof-neg neg-x) (library-lt *library-x* *library-y*) *proof-false*))
         (backward (proof-ite (proof-neg pos-x) (library-lt *library-y* *library-x*) *proof-false*))
         (expected (proof-ite zero-y zero-y (proof-ite forward forward backward)))
         (zero (proof-proof-assume proof zero-y t))
         (fix (t2-field-numeric-fix lib *library-y* numeric))
         (completed (proof-proof-chain proof fix (list zero)))
         (fixed-floor (t2-floor-thresholds-fixed-zero-floor lib cases completed))
         (lib (cdr fixed-floor))
         (proof (library-library-proof lib))
         (yes (t2-field-true-equality lib (car fixed-floor)))
         (rhs (proof-proof-if-true proof expected))
         (true-zero (t2-field-true-equality lib zero))
         (rhs (proof-proof-chain proof rhs (list true-zero)))
         (reversed (proof-proof-symmetric proof rhs))
         (yes (proof-proof-chain proof yes (list reversed)))
         (positive-y (proof-proof-assume proof pos-y t))
         (nonpositive-y (proof-proof-assume proof pos-y nil))
         (nonzero-y (proof-proof-assume proof zero-y nil))
         (negative-y (t2-rational-scaling-negative-number lib numeric nonpositive-y nonzero-y))
         (positive (t2-floor-thresholds-floor-zero-branch
                    lib cases rat expected forward pos-x (library-lt *library-y* *library-x*) positive-y t))
         (negative (t2-floor-thresholds-floor-zero-branch
                    (cdr positive) cases rat expected forward neg-x
                    (library-lt *library-x* *library-y*) negative-y nil))
         (lib (cdr negative))
         (proof (library-library-proof lib))
         (nonzero (proof-proof-cases proof pos-y (car positive) (car negative)))
         (step (proof-proof-cases proof zero-y yes nonzero))
         (claim (proof-step-first step))
         (rat-test (proof-step-first rat))
         (number-test (proof-step-first numeric)))
      (library-library-lemma lib "FLOOR-ZERO-DIVISOR-TEST" claim step
                             (library-guards (list rat-test number-test))))))

(defun t2-floor-thresholds-build (lib)
  (let ((cases (t2-quotient-rounding-quotient-cases-init lib *library-x* *library-y*))
        (floor (list *t2-floor-floor* *library-x* *library-y*)))
    (proof-with-checked-results
        ((threshold (t2-floor-thresholds-below-integer lib cases floor))
         (cases (t2-floor-thresholds-current-cases cases lib threshold))
         (sign-and-zero (t2-floor-thresholds-sign-and-zero threshold cases floor))
         (cases (t2-floor-thresholds-current-cases cases threshold sign-and-zero))
         (signs (t2-floor-thresholds-express-floor-signs sign-and-zero cases))
         (cases (t2-floor-thresholds-current-cases cases sign-and-zero signs)))
      (t2-floor-thresholds-express-floor-zero signs cases))))
