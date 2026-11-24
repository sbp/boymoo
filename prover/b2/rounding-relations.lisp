(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-rounding-relations-floor-as-truncate* '("sym" "ACL2" "FLOOR-AS-TRUNCATE"))

; A signed case split makes at most two requests.
(defmacro b2-rounding-relations-two-cases (replies result request run prove)
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

(defun b2-rounding-relations-floor-as-truncate-nonnegative
    (lib evidence sign inexact goal q quotient value q-type t-type ratio-type zero rx ry bounds)
  (let* ((proof (library-library-proof lib))
         (zero-test (proof-eq value *proof-zero*)))
    (proof-with-checked-results
        ((equal-zero (proof-proof-assume proof zero-test t))
         (zero-type (library-library-type-of lib *proof-zero* nil))
         (reverse-zero (proof-proof-symmetric proof equal-zero))
         (changed-type (proof-proof-rewrite proof zero-type reverse-zero '(1 1)))
         (typed (proof-proof-tidy proof changed-type))
         (contradiction (proof-proof-cut proof typed inexact))
         (distinct (proof-proof-front proof contradiction (proof-neg zero-test)))
         (different (b2-strict-order-flipped-distinct lib value *proof-zero* distinct))
         (positive (b2-rational-order-strict-from-weak lib sign different zero ratio-type))
         (interval (b2-truncate-intervals-truncate-interval
                    lib *library-x* *library-y* rx ry sign nil))
         (equal-step (b2-floor-translation-unique-integer
                      (cdr interval) value q quotient ratio-type q-type t-type bounds (car interval)))
         (step (b2-tactics-tactics-solve
                (cdr equal-step) goal (append evidence (list positive)) nil
                (list (car equal-step)) 0 nil)))
      (cons step (cdr equal-step)))))

(defun b2-rounding-relations-floor-as-truncate-negative
    (lib evidence sign inexact goal q quotient value q-type t-type ratio-type zero rx ry bounds)
  (proof-with-checked-results
      ((nonpositive (b2-rational-order-weak-from-strict lib sign ratio-type zero))
       (interval (b2-truncate-intervals-truncate-interval
                  lib *library-x* *library-y* rx ry nonpositive t))
       (lib (cdr interval))
       (proof (library-library-proof lib))
       (candidate (library-plus *proof-neg-one* quotient))
       (integer-candidate (library-library-type-of lib candidate (list t-type)))
       (rc (library-library-rational lib candidate (list integer-candidate)))
       (rt (library-library-rational lib quotient (list t-type)))
       (lower (b2-rational-order-weak-from-strict lib (cadar interval) rc ratio-type))
       (same-test (proof-eq quotient value))
       (assumed (proof-proof-assume proof same-test t))
       (changed-type (proof-proof-rewrite proof t-type assumed '(1 1)))
       (typed-if-same (proof-proof-tidy proof changed-type))
       (cut (proof-proof-cut proof typed-if-same inexact))
       (different (proof-proof-front proof cut (proof-neg same-test)))
       (strict (b2-rational-order-strict-from-weak lib (caar interval) different ratio-type rt))
       (cancel (b2-tactics-tactics-linear-equal
                lib (library-plus *proof-one* candidate) quotient (list t-type)))
       (upper (library-library-transport-argument lib strict cancel 2))
       (equal-step (b2-floor-translation-unique-integer
                    lib value q candidate ratio-type q-type integer-candidate bounds (list lower upper)))
       (step (b2-tactics-tactics-solve
              (cdr equal-step) goal (append evidence (list nonpositive)) nil
              (list (car equal-step)) 0 nil)))
    (cons step (cdr equal-step))))

(defun b2-rounding-relations-floor-as-truncate-direction
    (negative evidence lib inexact goal q quotient value q-type t-type ratio-type zero rx ry bounds)
  (let ((sign (car (last evidence))))
    (if negative
        (b2-rounding-relations-floor-as-truncate-negative
         lib evidence sign inexact goal q quotient value q-type t-type ratio-type zero rx ry bounds)
      (b2-rounding-relations-floor-as-truncate-nonnegative
       lib evidence sign inexact goal q quotient value q-type t-type ratio-type zero rx ry bounds))))

(defun b2-rounding-relations-choose-direction
    (lib test facts inexact goal q quotient value q-type t-type ratio-type zero rx ry bounds)
  (b2-rounding-relations-two-cases
   replies result request
   (b2-tactics-choose lib test facts replies)
   (b2-rounding-relations-floor-as-truncate-direction
    (cadddr request) (car (cddddr request)) (caddr request)
    inexact goal q quotient value q-type t-type ratio-type zero rx ry bounds)))

(defun b2-rounding-relations-floor-as-truncate-integral
    (integer-ratio facts lib goal q quotient value q-type t-type ratio-type zero rx ry bounds)
  (let ((last-fact (car (last facts))))
    (if integer-ratio
        (proof-with-checked-results
            ((floor-rule (b2-quotient-algebra-exact-quotient lib q value))
             (proof (library-library-proof (cdr floor-rule)))
             (same-floor (proof-proof-transport proof last-fact (car floor-rule)))
             (truncate-rule (b2-quotient-algebra-exact-quotient (cdr floor-rule) quotient value))
             (lib (cdr truncate-rule))
             (proof (library-library-proof lib))
             (same-truncate (proof-proof-transport proof last-fact (car truncate-rule)))
             (reverse (proof-proof-symmetric proof same-truncate))
             (equal-step (proof-proof-chain proof same-floor (list reverse)))
             (step (b2-tactics-tactics-solve lib goal facts nil (list equal-step) 0 nil)))
          (cons step lib))
      (b2-rounding-relations-choose-direction
       lib (library-lt value *proof-zero*) facts
       last-fact goal q quotient value q-type t-type ratio-type zero rx ry bounds))))

(defun b2-rounding-relations-choose-integral
    (lib exact goal q quotient value q-type t-type ratio-type zero rx ry bounds)
  (b2-rounding-relations-two-cases
   replies result request
   (b2-tactics-choose lib exact nil replies)
   (b2-rounding-relations-floor-as-truncate-integral
    (cadddr request) (car (cddddr request)) (caddr request)
    goal q quotient value q-type t-type ratio-type zero rx ry bounds)))

(defun b2-rounding-relations-floor-as-truncate-prove
    (premise lib goal q quotient value q-type t-type exact solver)
  (proof-with-checked-results
      ((sure (b2-quotient-algebra-with-forced lib premise))
       (rx (b2-powers-evidence-step sure (list *library-rationalp* *library-x*)))
       (ry (b2-powers-evidence-step sure (list *library-rationalp* *library-y*)))
       (ratio-type (b2-floor-translation-rational-type lib value sure solver))
       (bounds (b2-floor-intervals-floor-interval
                (b2-numeric-types-types-lib (cdr ratio-type)) *library-x* *library-y* rx ry))
       (lib (cdr bounds))
       (zero (library-library-rational lib *proof-zero* nil)))
    (b2-rounding-relations-choose-integral
     lib exact goal q quotient value q-type t-type (car ratio-type) zero rx ry (car bounds))))

(defun b2-rounding-relations-floor-as-truncate (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (condition (cadr parts))
       (goal (caddr parts))
       (q (list *b2-floor-intervals-floor* *library-x* *library-y*))
       (quotient (list *b2-numeric-types-truncate* *library-x* *library-y*))
       (value (b2-floor-translation-ratio *library-x* *library-y*))
       (solver (b2-numeric-types-types-init lib))
       (q-type (b2-numeric-types-types-floor solver *library-x* *library-y*))
       (t-type (b2-numeric-types-types-quotient-integer
                (cdr q-type) *b2-numeric-types-truncate* *library-x* *library-y*))
       (exact (library-integer value))
       (lib (b2-numeric-types-types-lib (cdr t-type)))
       (premise (proof-proof-assume (library-library-proof lib) condition t))
       (result (b2-rounding-relations-floor-as-truncate-prove
                premise lib goal q quotient value (car q-type) (car t-type) exact (cdr t-type))))
    (b2-tactics-tactics-implication lib condition goal result)))
