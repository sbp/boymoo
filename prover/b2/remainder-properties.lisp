(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-remainder-properties-linear-mod* '("sym" "ACL2" "LINEARIZE-MOD"))
(defconst *b2-remainder-properties-linear-rem* '("sym" "ACL2" "LINEARIZE-REM"))
(defconst *b2-remainder-properties-mod-type* '("sym" "ACL2" "MOD-TYPE"))
(defconst *b2-remainder-properties-rem-type* '("sym" "ACL2" "REM-TYPE"))
(defconst *b2-remainder-properties-rem-bounds* '("sym" "ACL2" "REM-BOUNDS"))
(defconst *b2-remainder-properties-remainder-properties*
  (list *b2-remainder-properties-linear-mod* *b2-remainder-properties-linear-rem*
        *b2-remainder-properties-mod-type* *b2-remainder-properties-rem-bounds*
        *b2-remainder-properties-rem-type*))
(defconst *b2-remainder-properties-abs* '("sym" "COMMON-LISP" "ABS"))

(defun b2-remainder-properties-multiplied-equivalence-divide
    (part lib reciprocal scale known solver inverse)
  (proof-with-checked-results
      ((typed (b2-floor-translation-rational-type lib part known solver))
       (lib (b2-numeric-types-types-lib (cdr typed)))
       (numeric (b2-scaling-number-of-rational lib part (car typed)))
       (divided (b2-products-distribute-cancel lib reciprocal scale part inverse numeric)))
    (cons divided (cdr typed))))

(defun b2-remainder-properties-multiplied-equivalence-transport
    (same lib left right a reciprocal scale known solver inverse)
  (proof-with-checked-results
      ((lifted (b2-algebra-congruence lib same (b2-products-product reciprocal a) '(2)))
       (first (b2-remainder-properties-multiplied-equivalence-divide
               left lib reciprocal scale known solver inverse))
       (lib (b2-numeric-types-types-lib (cdr first)))
       (reverse (proof-proof-symmetric (library-library-proof lib) (car first)))
       (second (b2-remainder-properties-multiplied-equivalence-divide
                right lib reciprocal scale known (cdr first) inverse))
       (proof (library-library-proof (b2-numeric-types-types-lib (cdr second))))
       (step (proof-proof-chain proof reverse (list lifted (car second)))))
    (cons step (cdr second))))

(defun b2-remainder-properties-multiplied-equivalence (lib left right scale known solver)
  (let* ((a (b2-products-product scale left))
         (b (b2-products-product scale right))
         (input-test (proof-eq a b))
         (result (proof-eq left right))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((inverses (b2-quotient-algebra-inverses lib scale known))
         (reciprocal (list *b2-products-recip* scale))
         (yes (proof-proof-assume proof input-test t))
         (no (proof-proof-assume proof input-test nil))
         (forward (b2-remainder-properties-multiplied-equivalence-transport
                   yes lib left right a reciprocal scale known solver (cadr inverses)))
         (lib (b2-numeric-types-types-lib (cdr forward)))
         (positive (b2-algebra-boolean-equivalence-positive
                    lib (proof-eq input-test result) yes (car forward)))
         (same (proof-proof-assume (library-library-proof lib) result t))
         (backward (b2-algebra-congruence lib same a '(2)))
         (step (b2-algebra-boolean-equivalence-negative lib input-test result no positive backward)))
      (cons step (cdr forward)))))

(defun b2-remainder-properties-remainder-init (lib op known)
  (proof-with-checked-results
      ((solver (b2-numeric-types-types-init lib))
       (quotient (if (equal op *b2-floor-intervals-mod*)
                     *b2-floor-intervals-floor*
                   *b2-numeric-types-truncate*))
       (value (list op *library-x* *library-y*))
       (q (list quotient *library-x* *library-y*))
       (ratio (b2-floor-translation-ratio *library-x* *library-y*))
       (gap (library-diff ratio q))
       (rx (b2-powers-evidence-step known (list *library-rationalp* *library-x*)))
       (ry (b2-powers-evidence-step known (list *library-rationalp* *library-y*)))
       (nonzero (b2-quotient-algebra-require-nonzero lib *library-y* known))
       (expression (b2-floor-translation-remainder-as-product
                    lib *library-x* *library-y* known solver op)))
    (list :b2-remainder-properties-remainder (cdr expression) known op value q ratio gap
          rx ry nonzero (car expression))))

(defun b2-remainder-properties-remainder-solver (self) (cadr self))
(defun b2-remainder-properties-remainder-known (self) (caddr self))
(defun b2-remainder-properties-remainder-op (self) (cadddr self))
(defun b2-remainder-properties-remainder-value (self) (nth 4 self))
(defun b2-remainder-properties-remainder-q (self) (nth 5 self))
(defun b2-remainder-properties-remainder-r (self) (nth 6 self))
(defun b2-remainder-properties-remainder-gap (self) (nth 7 self))
(defun b2-remainder-properties-remainder-rx (self) (nth 8 self))
(defun b2-remainder-properties-remainder-ry (self) (nth 9 self))
(defun b2-remainder-properties-remainder-nonzero (self) (nth 10 self))
(defun b2-remainder-properties-remainder-expression (self) (nth 11 self))

(defun b2-remainder-properties-remainder-lib (self)
  (b2-numeric-types-types-lib (b2-remainder-properties-remainder-solver self)))

(defun b2-remainder-properties-remainder-with-solver (self solver)
  (list* (car self) solver (cddr self)))

(defun b2-remainder-properties-remainder-with-library (self lib)
  (b2-remainder-properties-remainder-with-solver
   self (b2-numeric-types-types-with-library (b2-remainder-properties-remainder-solver self) lib)))

(defun b2-remainder-properties-remainder-type (self value)
  (proof-with-checked-results
      ((typed (b2-floor-translation-rational-type
               (b2-remainder-properties-remainder-lib self) value
               (b2-remainder-properties-remainder-known self)
               (b2-remainder-properties-remainder-solver self))))
    (cons (car typed) (b2-remainder-properties-remainder-with-solver self (cdr typed)))))

(defun b2-remainder-properties-remainder-quotient-integer (self)
  (let ((q (b2-remainder-properties-remainder-q self)))
    (proof-with-checked-results
        ((typed (b2-numeric-types-types-quotient-integer
                 (b2-remainder-properties-remainder-solver self) (car q) (cadr q) (caddr q))))
      (cons (car typed) (b2-remainder-properties-remainder-with-solver self (cdr typed))))))

(defun b2-remainder-properties-remainder-library-replies (replies)
  (if (endp replies)
      nil
    (let ((reply (car replies)))
      (cons (if (failure-p reply)
                reply
              (cons (car reply) (b2-remainder-properties-remainder-lib (cdr reply))))
            (b2-remainder-properties-remainder-library-replies (cdr replies))))))

(defun b2-remainder-properties-remainder-case-result (result self replies)
  (proof-with-checked-results ((value (car result)))
    (let ((current (if (endp replies) self (cdar (last replies)))))
      (cons value (b2-remainder-properties-remainder-with-library current (cdr result))))))

(defun b2-remainder-properties-remainder-sign-cases (self term typed distinct replies)
  (proof-with-checked-results
      ((result (b2-rational-order-sign-cases
                (b2-remainder-properties-remainder-lib self) term typed distinct
                (b2-remainder-properties-remainder-library-replies replies))))
    (b2-remainder-properties-remainder-case-result result self replies)))

(defun b2-remainder-properties-remainder-with-divisor (self prove)
  (b2-remainder-properties-remainder-sign-cases
   self *library-y*
   (b2-remainder-properties-remainder-ry self)
   (b2-remainder-properties-remainder-nonzero self)
   prove))

(defun b2-remainder-properties-remainder-choose (self test evidence replies)
  (proof-with-checked-results
      ((result (b2-tactics-choose
                (b2-remainder-properties-remainder-lib self) test evidence
                (b2-remainder-properties-remainder-library-replies replies))))
    (b2-remainder-properties-remainder-case-result result self replies)))

; A signed case split makes at most two requests.
(defmacro b2-remainder-properties-two-cases (replies result request run prove)
  `(let ((,replies nil))
     (proof-with-checked-results ((,result ,run))
       (if (eq (caar ,result) :call)
           (proof-with-checked-results
               ((,request (car ,result))
                (case-reply ,prove)
                (,replies (list case-reply))
                (,result ,run))
             (if (eq (caar ,result) :call)
                 (proof-with-checked-results
                     ((,request (car ,result))
                      (case-reply ,prove)
                      (,replies (append ,replies (list case-reply))))
                   ,run)
               ,result))
         ,result))))

(defun b2-remainder-properties-remainder-comparisons-reduction (lib value reduction)
  (proof-with-checked-results
      ((rule (b2-fraction-reduction-negative-first lib *library-y* value))
       (proof (library-library-proof (cdr rule)))
       (changed (proof-proof-rewrite proof (car rule) reduction '(1 2 1)))
       (step (proof-proof-tidy proof changed)))
    (cons step (cdr rule))))

(defun b2-remainder-properties-remainder-comparisons-reductions
    (self negative sign gap term first second)
  (if negative
      (proof-with-checked-results
          ((lib (b2-remainder-properties-remainder-lib self))
           (scale (library-minus *library-y*))
           (opposite (b2-scaling-opposite-sign lib *library-y*
                                              (b2-remainder-properties-remainder-ry self)))
           (positive (proof-proof-transport (library-library-proof lib) sign opposite))
           (first (b2-remainder-properties-remainder-comparisons-reduction lib gap first))
           (second (b2-remainder-properties-remainder-comparisons-reduction (cdr first) term second)))
        (cons (list scale positive (car first) (car second))
              (b2-remainder-properties-remainder-with-library self (cdr second))))
    (cons (list *library-y* sign first second) self)))

(defun b2-remainder-properties-remainder-comparisons-order
    (self a b scale positive reduction-a reduction-b display-a display-b negative)
  (proof-with-checked-results
      ((type-a (b2-remainder-properties-remainder-type self a))
       (type-b (b2-remainder-properties-remainder-type (cdr type-a) b))
       (scale-type (b2-remainder-properties-remainder-type (cdr type-b) scale))
       (lib (b2-remainder-properties-remainder-lib (cdr scale-type)))
       (scaled (b2-scaling-rational-scale-order
                lib a b scale (list (car type-a) (car type-b) (car scale-type)) positive))
       (lib (cdr scaled))
       (proof (library-library-proof lib))
       (first (proof-proof-rewrite proof (car scaled) reduction-a '(1 1 1)))
       (changed (proof-proof-rewrite proof first reduction-b '(1 1 2)))
       (changed (if negative
                    (proof-with-checked-results
                        ((reverse (b2-rational-order-reverse-negations lib display-a display-b)))
                      (proof-proof-rewrite proof changed reverse '(1 1)))
                  changed))
       (step (proof-proof-tidy proof changed)))
    (cons step (b2-remainder-properties-remainder-with-library (cdr scale-type) lib))))

(defun b2-remainder-properties-remainder-comparisons (self reference negative sign)
  (let ((term (b2-floor-translation-ratio reference *library-y*))
        (gap (b2-remainder-properties-remainder-gap self))
        (value (b2-remainder-properties-remainder-value self))
        (ry (b2-remainder-properties-remainder-ry self))
        (nonzero (b2-remainder-properties-remainder-nonzero self))
        (expression (b2-remainder-properties-remainder-expression self)))
    (proof-with-checked-results
        ((reference-type (b2-remainder-properties-remainder-type self reference))
         (self (cdr reference-type))
         (lib (b2-remainder-properties-remainder-lib self))
         (scaled (b2-floor-intervals-scaled-dividend
                  lib reference *library-y* (car reference-type) ry nonzero))
         (inverse (proof-proof-symmetric (library-library-proof lib) expression))
         (reduced (b2-remainder-properties-remainder-comparisons-reductions
                   self negative sign gap term inverse scaled))
         (scale (caar reduced))
         (positive (cadar reduced))
         (reduction-a (caddar reduced))
         (reduction-b (cadddr (car reduced)))
         (first (b2-remainder-properties-remainder-comparisons-order
                 (cdr reduced) gap term scale positive reduction-a reduction-b value reference negative))
         (second (b2-remainder-properties-remainder-comparisons-order
                  (cdr first) term gap scale positive reduction-b reduction-a reference value negative)))
      (cons (if negative (list (car second) (car first)) (list (car first) (car second)))
            (cdr second)))))

(defun b2-remainder-properties-remainder-linearize-prove (negative sign facts self goal equality)
  (proof-with-checked-results
      ((ordered (b2-remainder-properties-remainder-comparisons self *library-z* negative sign))
       (step (b2-tactics-tactics-solve (b2-remainder-properties-remainder-lib (cdr ordered))
                                      goal facts nil (cons equality (car ordered)) 0 t)))
    (cons step (cdr ordered))))

(defun b2-remainder-properties-remainder-double-negative (self rule)
  (let ((gap (b2-remainder-properties-remainder-gap self))
        (expression (b2-remainder-properties-remainder-expression self)))
    (proof-with-checked-results
        ((reduction (b2-fraction-reduction-negative-factor
                     (b2-remainder-properties-remainder-lib self) *library-y* gap))
         (self (b2-remainder-properties-remainder-with-library self (cdr reduction)))
         (proof (library-library-proof (cdr reduction)))
         (rule (proof-proof-rewrite proof rule (car reduction) '(1 2 1)))
         (literal (proof-step-first expression))
         (product (proof-term-at literal 2))
         (typed (b2-remainder-properties-remainder-type self product))
         (lib (b2-remainder-properties-remainder-lib (cdr typed)))
         (numeric (b2-scaling-number-of-rational lib product (car typed)))
         (twice (b2-fraction-reduction-twice-negated lib product numeric))
         (step (proof-proof-chain (library-library-proof lib) rule (list twice))))
      (cons step (cdr typed)))))

(defun b2-remainder-properties-remainder-sign-rule (self divisor-negative gap-negative distance)
  (let ((lib (b2-remainder-properties-remainder-lib self)))
    (cond
     (divisor-negative
      (proof-with-checked-results
          ((rule (b2-fraction-reduction-negative-first lib *library-y* distance))
           (self (b2-remainder-properties-remainder-with-library self (cdr rule))))
        (if gap-negative
            (b2-remainder-properties-remainder-double-negative self (car rule))
          (cons (car rule) self))))
     (gap-negative
      (proof-with-checked-results
          ((rule (b2-fraction-reduction-negative-factor
                  lib *library-y* (b2-remainder-properties-remainder-gap self))))
        (cons (car rule) (b2-remainder-properties-remainder-with-library self (cdr rule)))))
     (t
      (proof-with-checked-results
          ((literal (proof-step-first (b2-remainder-properties-remainder-expression self)))
           (product (proof-term-at literal 2))
           (step (proof-proof-reflexive (library-library-proof lib) product)))
        (cons step self))))))

(defun b2-remainder-properties-remainder-distance-positive (self gap-negative gap-sign)
  (if gap-negative
      (let ((gap (b2-remainder-properties-remainder-gap self)))
        (proof-with-checked-results
            ((typed (b2-remainder-properties-remainder-type self gap))
             (lib (b2-remainder-properties-remainder-lib (cdr typed)))
             (opposite (b2-scaling-opposite-sign lib gap (car typed)))
             (step (proof-proof-transport (library-library-proof lib) gap-sign opposite)))
          (cons step (cdr typed))))
    (cons gap-sign self)))

(defun b2-remainder-properties-remainder-sign-finish (self emitted negative)
  (if negative
      (let ((value (b2-remainder-properties-remainder-value self)))
        (proof-with-checked-results
            ((typed (b2-remainder-properties-remainder-type self value))
             (lib (b2-remainder-properties-remainder-lib (cdr typed)))
             (proof (library-library-proof lib))
             (opposite (b2-scaling-opposite-sign lib value (car typed)))
             (changed (proof-proof-rewrite proof emitted opposite '(1)))
             (step (proof-proof-tidy proof changed)))
          (cons step (cdr typed))))
    (cons emitted self)))

(defun b2-remainder-properties-remainder-remainder-sign
    (self divisor-negative divisor-sign gap-negative gap-sign)
  (let* ((gap (b2-remainder-properties-remainder-gap self))
         (scale (if divisor-negative (library-minus *library-y*) *library-y*))
         (distance (if gap-negative (library-minus gap) gap)))
    (proof-with-checked-results
        ((scale-type (b2-remainder-properties-remainder-type self scale))
         (distance-type (b2-remainder-properties-remainder-type (cdr scale-type) distance))
         (self (cdr distance-type))
         (lib (b2-remainder-properties-remainder-lib self))
         (divisor-positive
          (if divisor-negative
              (proof-with-checked-results
                  ((opposite (b2-scaling-opposite-sign
                              lib *library-y* (b2-remainder-properties-remainder-ry self))))
                (proof-proof-transport (library-library-proof lib) divisor-sign opposite))
            divisor-sign))
         (distance-positive
          (b2-remainder-properties-remainder-distance-positive self gap-negative gap-sign))
         (self (cdr distance-positive))
         (lib (b2-remainder-properties-remainder-lib self))
         (positive (library-library-cite
                    lib "POSITIVE-PRODUCT" (list scale distance)
                    (list (car scale-type) (car distance-type) divisor-positive (car distance-positive))))
         (rule (b2-remainder-properties-remainder-sign-rule self divisor-negative gap-negative distance))
         (self (cdr rule))
         (proof (library-library-proof (b2-remainder-properties-remainder-lib self)))
         (emitted (proof-proof-rewrite proof positive (car rule) '(1 2)))
         (emitted (proof-proof-tidy proof emitted))
         (negative (not (eq divisor-negative gap-negative)))
         (expression (proof-proof-symmetric proof (b2-remainder-properties-remainder-expression self)))
         (emitted (proof-proof-rewrite proof emitted expression (if negative '(1 2 1) '(1 2))))
         (emitted (proof-proof-tidy proof emitted)))
      (b2-remainder-properties-remainder-sign-finish self emitted negative))))

(defun b2-remainder-properties-remainder-gap-sign (self negative weak inexact)
  (let* ((q (b2-remainder-properties-remainder-q self))
         (ratio (b2-remainder-properties-remainder-r self))
         (test (proof-eq q ratio)))
    (proof-with-checked-results
        ((typed (b2-remainder-properties-remainder-quotient-integer self))
         (proof (library-library-proof (b2-remainder-properties-remainder-lib (cdr typed))))
         (assumed (proof-proof-assume proof test t))
         (changed (proof-proof-rewrite proof (car typed) assumed '(1 1)))
         (false (proof-proof-tidy proof changed))
         (failure (proof-proof-cut proof false inexact))
         (unequal (proof-proof-front proof failure (proof-neg test)))
         (qt (b2-remainder-properties-remainder-type (cdr typed) q))
         (rt (b2-remainder-properties-remainder-type (cdr qt) ratio))
         (lib (b2-remainder-properties-remainder-lib (cdr rt)))
         (strict (b2-rational-order-strict-from-weak
                  lib weak unequal (if negative (car rt) (car qt)) (if negative (car qt) (car rt))))
         (orders (b2-rational-order-difference-orders lib ratio q (car rt) (car qt)))
         (proof (library-library-proof lib))
         (changed (proof-proof-rewrite proof strict (if negative (caddr orders) (cadddr orders)) '(1)))
         (step (proof-proof-tidy proof changed)))
      (cons step (cdr rt)))))

(defun b2-remainder-properties-remainder-signs-nonzero-gap
    (negative-gap lower facts self goal divisor-negative divisor-sign inexact)
  (proof-with-checked-results
      ((gap (b2-remainder-properties-remainder-gap-sign self negative-gap lower inexact))
       (rem (b2-remainder-properties-remainder-remainder-sign
             (cdr gap) divisor-negative divisor-sign negative-gap (car gap)))
       (value (b2-remainder-properties-remainder-value (cdr rem)))
       (typed (b2-remainder-properties-remainder-type (cdr rem) value))
       (self (cdr typed))
       (lib (b2-remainder-properties-remainder-lib self))
       (zero (library-library-rational lib *proof-zero* nil))
       (negative (not (eq negative-gap divisor-negative)))
       (opposite (b2-rational-order-weak-from-strict
                  lib (car rem) (if negative (car typed) zero) (if negative zero (car typed))))
       (step (b2-tactics-tactics-solve lib goal (append facts (list (car rem) opposite)) nil nil 0 t)))
    (cons step self)))

(defun b2-remainder-properties-remainder-signs-dividend
    (dividend-negative facts self goal divisor-negative divisor-sign evidence)
  (let* ((direction (not (eq dividend-negative divisor-negative)))
         (rx (b2-remainder-properties-remainder-rx self))
         (ry (b2-remainder-properties-remainder-ry self))
         (lib (b2-remainder-properties-remainder-lib self)))
    (proof-with-checked-results
        ((comparisons (b2-truncate-intervals-ratio-comparisons
                       lib *library-x* *library-y* rx ry divisor-sign divisor-negative))
         (lib (cdr comparisons))
         (proof (library-library-proof lib))
         (equation (nth (if direction 1 0) (car comparisons)))
         (known (b2-tactics-tactics-evidence lib facts))
         (literal (proof-step-first equation))
         (test (proof-term-at literal 1))
         (given (b2-powers-evidence-step known (proof-neg test)))
         (changed (proof-proof-rewrite proof given equation '(1 1)))
         (sign (proof-proof-tidy proof changed))
         (bounds (b2-truncate-intervals-truncate-interval
                  lib *library-x* *library-y* rx ry sign direction))
         (self (b2-remainder-properties-remainder-with-library self (cdr bounds))))
      (b2-remainder-properties-remainder-signs-nonzero-gap
       direction (caar bounds) (append evidence facts) self goal
       divisor-negative divisor-sign (car (last evidence))))))

(defun b2-remainder-properties-remainder-signs-dividend-cases
    (self distinct goal divisor-negative divisor-sign evidence)
  (b2-remainder-properties-two-cases
   replies result request
   (b2-remainder-properties-remainder-sign-cases
    self *library-x* (b2-remainder-properties-remainder-rx self) distinct replies)
   (b2-remainder-properties-remainder-signs-dividend
    (cadr request) (cadddr request) (cdr result) goal divisor-negative divisor-sign evidence)))

(defun b2-remainder-properties-remainder-signs-inexact
    (self goal divisor-negative divisor-sign evidence)
  (let* ((lib (b2-remainder-properties-remainder-lib self))
         (proof (library-library-proof lib))
         (inexact (car (last evidence))))
    (if (equal (b2-remainder-properties-remainder-op self) *b2-floor-intervals-mod*)
        (proof-with-checked-results
            ((bounds (b2-floor-intervals-floor-interval lib *library-x* *library-y*
                      (b2-remainder-properties-remainder-rx self)
                      (b2-remainder-properties-remainder-ry self)))
             (self (b2-remainder-properties-remainder-with-library self (cdr bounds))))
          (b2-remainder-properties-remainder-signs-nonzero-gap
           nil (caar bounds) evidence self goal divisor-negative divisor-sign inexact))
      (proof-with-checked-results
          ((test (proof-eq *library-x* *proof-zero*))
           (assumed (proof-proof-assume proof test t))
           (source (b2-algebra-congruence lib assumed (b2-remainder-properties-remainder-r self) '(1)))
           (zero-product (b2-products-zero-left-product lib (list *b2-products-recip* *library-y*)))
           (lib (cdr zero-product))
           (proof (library-library-proof lib))
           (numerical (proof-proof-chain proof source (list (car zero-product))))
           (zero-type (library-library-type-of lib *proof-zero* nil))
           (must-be-integer (library-library-transport-argument lib zero-type numerical 1))
           (cut (proof-proof-cut proof must-be-integer inexact))
           (distinct (proof-proof-front proof cut (proof-neg test)))
           (self (b2-remainder-properties-remainder-with-library self lib)))
        (b2-remainder-properties-remainder-signs-dividend-cases
         self distinct goal divisor-negative divisor-sign evidence)))))

(defun b2-remainder-properties-remainder-signs-exact-solve (lib test evidence goal)
  (b2-remainder-properties-two-cases
   replies result request
   (b2-tactics-choose lib test evidence replies)
   (let ((current-lib (caddr request))
         (facts (car (cddddr request))))
     (proof-with-checked-results
         ((step (b2-tactics-tactics-solve current-lib goal facts nil nil 0 nil)))
       (cons step current-lib)))))

(defun b2-remainder-properties-remainder-signs-exact-cases (lib test evidence next-test goal)
  (b2-remainder-properties-two-cases
   replies result request
   (b2-tactics-choose lib test evidence replies)
   (b2-remainder-properties-remainder-signs-exact-solve
    (caddr request) next-test (car (cddddr request)) goal)))

(defun b2-remainder-properties-remainder-signs-check
    (exact evidence self goal integral divisor-negative divisor-sign)
  (if exact
      (let* ((lib (b2-remainder-properties-remainder-lib self))
             (proof (library-library-proof lib))
             (mod-p (equal (b2-remainder-properties-remainder-op self) *b2-floor-intervals-mod*))
             (rule (if mod-p *b2-quotient-algebra-zero-mod* *b2-quotient-algebra-zero-rem*))
             (test (proof-eq (b2-remainder-properties-remainder-value self) *proof-zero*)))
        (proof-with-checked-results
            ((equivalence (b2-tactics-tactics-use-fact
                           lib rule (proof-eq test integral)
                           (table-values (b2-remainder-properties-remainder-known self))
                           '(("sym" "ACL2" "FORCE")) nil 0 nil))
             (value (proof-proof-transport proof (car (last evidence)) equivalence))
             (evidence (append evidence (list value))))
          (if mod-p
              (proof-with-checked-results
                  ((step (b2-tactics-tactics-solve lib goal evidence nil nil 0 nil)))
                (cons step self))
            (proof-with-checked-results
                ((result (b2-remainder-properties-remainder-signs-exact-cases
                          lib (library-lt *library-x* *proof-zero*) evidence
                          (library-lt *proof-zero* *library-x*) goal)))
              (cons (car result) (b2-remainder-properties-remainder-with-library self (cdr result)))))))
    (b2-remainder-properties-remainder-signs-inexact self goal divisor-negative divisor-sign evidence)))

(defun b2-remainder-properties-remainder-signs-classify
    (divisor-negative divisor-sign division self goal integral)
  (b2-remainder-properties-two-cases
   replies result request
   (b2-remainder-properties-remainder-choose self integral division replies)
   (b2-remainder-properties-remainder-signs-check
    (cadddr request) (car (cddddr request)) (cdr result) goal integral divisor-negative divisor-sign)))

(defun b2-remainder-properties-remainder-unit-gap-bound (self high negative)
  (let* ((lib (b2-remainder-properties-remainder-lib self))
         (proof (library-library-proof lib))
         (offset (library-minus (b2-remainder-properties-remainder-q self)))
         (ratio (b2-remainder-properties-remainder-r self)))
    (proof-with-checked-results
        ((literal (proof-step-first high))
         (parts (proof-list-of-length literal 3))
         (left (cadr parts))
         (right (caddr parts))
         (shift (b2-algebra-cancel-common-shift lib offset left right))
         (lifted (proof-proof-transport proof high shift))
         (exchanged (library-library-axiom lib "COMMUTATIVITY-OF-+" (list offset ratio)))
         (typed (b2-remainder-properties-remainder-quotient-integer self))
         (self (cdr typed))
         (lib (b2-remainder-properties-remainder-lib self))
         (proof (library-library-proof lib))
         (identity (b2-tactics-tactics-linear-equal lib
                    (library-plus offset (if negative left right))
                    (if negative *proof-neg-one* *proof-one*) (list (car typed))))
         (first (proof-proof-rewrite proof lifted (if negative identity exchanged) '(1 1)))
         (changed (proof-proof-rewrite proof first (if negative exchanged identity) '(1 2)))
         (step (proof-proof-tidy proof changed)))
      (cons step self))))

(defun b2-remainder-properties-remainder-absolute-unit (self reference ratio-negative unit)
  (let ((lib (b2-remainder-properties-remainder-lib self)))
    (cond
     (ratio-negative
      (proof-with-checked-results
          ((view (b2-fraction-reduction-negative-first
                   lib *library-y* (list *b2-products-recip* *library-y*)))
           (lib (cdr view))
           (proof (library-library-proof lib))
           (changed (proof-proof-rewrite proof (car view) unit '(1 2 1)))
           (computed (proof-proof-compute proof (library-minus *proof-one*) -1))
           (step (proof-proof-chain proof changed (list computed))))
        (cons step (b2-remainder-properties-remainder-with-library self lib))))
     ((not (equal reference *library-y*))
      (proof-with-checked-results
          ((numeric (b2-scaling-number-of-rational
                     lib *library-y* (b2-remainder-properties-remainder-ry self)))
           (norm (b2-fraction-reduction-twice-negated lib *library-y* numeric))
           (lifted (b2-algebra-congruence
                    lib norm (b2-floor-translation-ratio reference *library-y*) '(1)))
           (step (proof-proof-chain (library-library-proof lib) lifted (list unit))))
        (cons step self)))
     (t (cons unit self)))))

(defun b2-remainder-properties-remainder-absolute-bound-prove
    (negative sign facts self goal dividend-sign lower)
  (let* ((magnitude (if negative (library-minus *library-y*) *library-y*))
         (reference (if lower (library-minus magnitude) magnitude))
         (ratio-negative (not (eq negative lower)))
         (lib (b2-remainder-properties-remainder-lib self))
         (rx (b2-remainder-properties-remainder-rx self))
         (ry (b2-remainder-properties-remainder-ry self)))
    (proof-with-checked-results
        ((comparisons (b2-truncate-intervals-ratio-comparisons
                       lib *library-x* *library-y* rx ry sign negative))
         (lib (cdr comparisons))
         (proof (library-library-proof lib))
         (comparison (nth (if ratio-negative 1 0) (car comparisons)))
         (changed (proof-proof-rewrite proof dividend-sign comparison '(1 1)))
         (ratio-sign (proof-proof-tidy proof changed))
         (interval (b2-truncate-intervals-truncate-interval
                    lib *library-x* *library-y* rx ry ratio-sign ratio-negative))
         (self (b2-remainder-properties-remainder-with-library self (cdr interval)))
         (upper-gap (b2-remainder-properties-remainder-unit-gap-bound self (cadar interval) ratio-negative))
         (orders (b2-remainder-properties-remainder-comparisons (cdr upper-gap) reference negative sign))
         (order (nth (if lower 1 0) (car orders)))
         (self (cdr orders))
         (lib (b2-remainder-properties-remainder-lib self))
         (inverse (b2-quotient-algebra-inverses lib *library-y*
                                               (b2-remainder-properties-remainder-known self)))
         (unit (b2-remainder-properties-remainder-absolute-unit self reference ratio-negative (car inverse)))
         (self (cdr unit))
         (lib (b2-remainder-properties-remainder-lib self))
         (proof (library-library-proof lib))
         (changed (proof-proof-rewrite proof order (car unit)
                                       (if ratio-negative '(1 2 1) '(1 2 2))))
         (order (proof-proof-tidy proof changed))
         (actual (proof-proof-transport proof (car upper-gap) order))
         (step (b2-tactics-tactics-solve
                lib goal (append facts (list actual ry))
                (list (list *b2-remainder-properties-abs* *library-y*)
                      (list (proof-cl "MINUSP") *library-y*))
                nil 0 nil)))
      (cons step self))))

(defun b2-remainder-properties-remainder-divisor-branch
    (self negative sign facts recipe goal args)
  (case recipe
    (:linearize
     (b2-remainder-properties-remainder-linearize-prove negative sign facts self goal (car args)))
    (:signs
     (b2-remainder-properties-remainder-signs-classify
      negative sign facts self goal (car args)))
    (:absolute-bound
     (b2-remainder-properties-remainder-absolute-bound-prove
      negative sign facts self goal (car args) (cadr args)))
    (otherwise (b2-tactics-unproved))))

(defun b2-remainder-properties-remainder-divisor-cases (self recipe goal args)
  (b2-remainder-properties-two-cases
   replies result request
   (b2-remainder-properties-remainder-with-divisor self replies)
   (b2-remainder-properties-remainder-divisor-branch
    (cdr result) (cadr request) (caddr request) (cadddr request) recipe goal args)))

(defun b2-remainder-properties-remainder-linearize (self goal)
  (let ((reference (b2-floor-translation-ratio *library-z* *library-y*)))
    (proof-with-checked-results
        ((typed (b2-remainder-properties-remainder-type self *library-z*))
         (self (cdr typed))
         (lib (b2-remainder-properties-remainder-lib self))
         (scale (b2-floor-intervals-scaled-dividend lib *library-z* *library-y* (car typed)
                 (b2-remainder-properties-remainder-ry self)
                 (b2-remainder-properties-remainder-nonzero self)))
         (equivalence (b2-remainder-properties-multiplied-equivalence
                       lib (b2-remainder-properties-remainder-gap self) reference *library-y*
                       (b2-remainder-properties-remainder-known self)
                       (b2-remainder-properties-remainder-solver self)))
         (self (b2-remainder-properties-remainder-with-solver self (cdr equivalence)))
         (proof (library-library-proof (b2-remainder-properties-remainder-lib self)))
         (reverse (proof-proof-symmetric proof (b2-remainder-properties-remainder-expression self)))
         (first (proof-proof-rewrite proof (car equivalence) reverse '(1 1 1)))
         (last (proof-proof-rewrite proof first scale '(1 1 2)))
         (equality (proof-proof-tidy proof last)))
      (b2-remainder-properties-remainder-divisor-cases self :linearize goal (list equality)))))

(defun b2-remainder-properties-remainder-signs (self goal)
  (let ((integral (library-integer (b2-remainder-properties-remainder-r self))))
    (b2-remainder-properties-remainder-divisor-cases self :signs goal (list integral))))

(defun b2-remainder-properties-remainder-absolute-bound (self goal given lower)
  (let ((lib (b2-remainder-properties-remainder-lib self))
        (test (if lower
                  (library-lt *proof-zero* *library-x*)
                (library-lt *library-x* *proof-zero*))))
    (proof-with-checked-results
        ((known (b2-tactics-tactics-evidence lib (list given)))
         (dividend-sign (b2-powers-evidence-step known (proof-neg test))))
      (b2-remainder-properties-remainder-divisor-cases
       self :absolute-bound goal (list dividend-sign lower)))))

(defun b2-remainder-properties-remainder-theorem-bound (premise lib goal lower)
  (proof-with-checked-results
      ((known (b2-quotient-algebra-with-forced lib premise))
       (remainder (b2-remainder-properties-remainder-init lib *b2-floor-translation-rem* known))
       (result (b2-remainder-properties-remainder-absolute-bound remainder goal premise lower)))
    (cons (car result) (b2-remainder-properties-remainder-lib (cdr result)))))

(defun b2-remainder-properties-remainder-theorem-bound-step (lib branch lower)
  (proof-with-checked-results
      ((parts (proof-list-of-length branch 3))
       (condition (cadr parts))
       (goal (caddr parts))
       (premise (proof-proof-assume (library-library-proof lib) condition t))
       (outcome (b2-remainder-properties-remainder-theorem-bound premise lib goal lower)))
    (b2-tactics-tactics-implication lib condition goal outcome)))

(defun b2-remainder-properties-remainder-theorem-bounds (lib formula branches)
  (let ((first-branch (consp branches))
        (second-branch (consp (cdr branches))))
    (proof-with-checked-results
        ((first (if first-branch
                    (b2-remainder-properties-remainder-theorem-bound-step lib (car branches) nil)
                  (cons nil lib)))
         (second (if second-branch
                     (b2-remainder-properties-remainder-theorem-bound-step (cdr first) (cadr branches) t)
                   (cons nil (cdr first))))
         (evidence (if second-branch (list (car first) (car second))
                     (if first-branch (list (car first)) nil)))
         (step (b2-tactics-tactics-solve (cdr second) formula evidence nil nil 0 nil)))
      (cons step (cdr second)))))

(defun b2-remainder-properties-remainder-theorem-prove (premise lib name op goal)
  (proof-with-checked-results
      ((known (b2-quotient-algebra-with-forced lib premise))
       (remainder (b2-remainder-properties-remainder-init lib op known))
       (result
        (if (member-equal name (list *b2-remainder-properties-linear-mod*
                                     *b2-remainder-properties-linear-rem*))
            (b2-remainder-properties-remainder-linearize remainder goal)
          (b2-remainder-properties-remainder-signs remainder goal))))
    (cons (car result) (b2-remainder-properties-remainder-lib (cdr result)))))

(defun b2-remainder-properties-remainder-theorem (lib name formula)
  (if (equal name *b2-remainder-properties-rem-bounds*)
      (if (integerp formula)
          '(:failure "tactic-rejected" "")
        (b2-remainder-properties-remainder-theorem-bounds lib formula (seq-slice formula 1 3)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (condition (cadr parts))
         (goal (caddr parts))
         (op (if (member-equal name (list *b2-remainder-properties-linear-mod*
                                         *b2-remainder-properties-mod-type*))
                 *b2-floor-intervals-mod*
               *b2-floor-translation-rem*))
         (premise (proof-proof-assume (library-library-proof lib) condition t))
         (result (b2-remainder-properties-remainder-theorem-prove premise lib name op goal)))
      (b2-tactics-tactics-implication lib condition goal result))))
