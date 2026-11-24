(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-floor-ranges-sign* (proof-sym "FLOOR-TYPE-1" "ACL2"))
(defconst *b2-floor-ranges-positive* (proof-sym "FLOOR-TYPE-2" "ACL2"))
(defconst *b2-floor-ranges-at-zero* (proof-sym "FLOOR-TYPE-3" "ACL2"))
(defconst *b2-floor-ranges-at-minus-one* (proof-sym "FLOOR-TYPE-4" "ACL2"))

(defconst *b2-floor-ranges-floor-ranges*
  (list *b2-floor-ranges-sign* *b2-floor-ranges-positive*
        *b2-floor-ranges-at-zero* *b2-floor-ranges-at-minus-one*))

(defun b2-floor-ranges-floor-below-forward (step lib qt kt rt sr kr bounds)
  (b2-reciprocal-results lib
      ((beyond (b2-butlast-integer-after-successor lib step (list qt kt))))
    (b2-reciprocal-return lib
      (b2-rational-order-rational-order-chain lib (cadr bounds) beyond (list rt sr kr)))))

(defun b2-floor-ranges-floor-below-backward (step lib qr rt kr bounds)
  (b2-reciprocal-return lib
    (b2-rational-order-rational-order-chain lib (car bounds) step (list qr rt kr))))

(defun b2-floor-ranges-floor-below (lib q r k qt rt kt bounds)
  (b2-reciprocal-results lib
      ((first (library-lt q k))
       (last (library-lt r k))
       (qr (library-library-rational lib q (list qt)))
       (kr (library-library-rational lib k (list kt)))
       (sr (library-library-rational lib (library-plus *proof-one* q) (list qt)))
       (result (b2-reciprocal-equivalence lib first last step
                 (b2-floor-ranges-floor-below-forward step lib qt kt rt sr kr bounds)
                 (b2-floor-ranges-floor-below-backward step lib qr rt kr bounds))))
    (car result)))

(defun b2-floor-ranges-floor-point-outside (assumption reaches position lib same bounds)
  (b2-reciprocal-results lib
      ((equal-step (b2-reciprocal-assume lib same))
       (replaced (b2-reciprocal-rewrite lib reaches equal-step position))
       (replaced (b2-reciprocal-tidy lib replaced))
       (conflict
        (let ((proof (library-library-proof lib)))
          (if (equal reaches (car bounds))
              (proof-proof-cut proof assumption replaced)
            (proof-proof-cut proof replaced assumption)))))
    (proof-proof-front (library-library-proof lib) conflict (proof-neg same))))

(defun b2-floor-ranges-floor-point-low-high (within facts lib r q level rt qt bounds same goal)
  (b2-reciprocal-results lib
      ((exact
        (if within
            (b2-reciprocal-results lib
                ((typed (library-library-type-of lib level nil)))
              (b2-floor-translation-unique-integer lib r q level rt qt typed bounds facts))
          (b2-reciprocal-return lib
            (b2-floor-ranges-floor-point-outside
             (car (last facts)) (cadr bounds) '(1 2 2) lib same bounds))) :library))
    (b2-reciprocal-return lib (b2-reciprocal-solve lib goal (append facts (list exact))))))

(defun b2-floor-ranges-floor-point-low
    (too-low initial lib bounds same goal upper r q level rt qt)
  (if too-low
      (b2-reciprocal-results lib
          ((different (b2-floor-ranges-floor-point-outside
                       (car (last initial)) (car bounds) '(1 1 2) lib same bounds)))
        (b2-reciprocal-return lib (b2-reciprocal-solve lib goal (append initial (list different)))))
    (b2-reciprocal-choose lib upper initial within facts
      (b2-floor-ranges-floor-point-low-high within facts lib r q level rt qt bounds same goal))))

(defun b2-floor-ranges-floor-point (lib q r level qt rt bounds)
  (b2-reciprocal-results lib
      ((lower (library-lt r level))
       (upper (library-lt r (library-plus *proof-one* level)))
       (same (proof-eq q level))
       (expected (b2-powers-and-terms (list (proof-neg lower) upper)))
       (goal (proof-eq same expected)))
    (b2-reciprocal-choose lib lower nil too-low initial
      (b2-floor-ranges-floor-point-low
       too-low initial lib bounds same goal upper r q level rt qt))))

(defun b2-floor-ranges-strictly-positive-integer-prove (positive facts lib q typed goal)
  (b2-reciprocal-results lib
      ((proof
        (if positive
            (b2-reciprocal-results lib
                ((proof (b2-butlast-integer-after-successor lib (car (last facts)) (list typed)))
                 (unit (proof-proof-compute (library-library-proof lib)
                                            (library-plus *proof-one* *proof-zero*) 1))
                 (proof (b2-reciprocal-rewrite lib proof unit '(1 1 2))))
              (b2-reciprocal-tidy lib proof))
          (b2-bounds-prove-integer-bound lib (library-lt q *proof-one*)
                                         (append facts (list typed))))))
    (b2-reciprocal-return lib (b2-reciprocal-solve lib goal (append facts (list proof))))))

(defun b2-floor-ranges-strictly-positive-integer (lib q typed)
  (let ((test (library-positive q))
        (goal (proof-eq (library-positive q) (proof-neg (library-lt q *proof-one*)))))
    (proof-with-checked-results
        ((result
          (b2-reciprocal-choose lib test nil positive facts
            (b2-floor-ranges-strictly-positive-integer-prove positive facts lib q typed goal))))
      (car result))))

(defun b2-floor-ranges-scaled-threshold-negative-one
    (lib x y rx ry scale equation unit negative)
  (b2-reciprocal-results lib
      ((inverted (b2-products-product scale *proof-neg-one*))
       (expanded (proof-proof-reflexive (library-library-proof lib) inverted))
       (minus-one (proof-proof-compute (library-library-proof lib) (library-minus *proof-one*) -1))
       (minus-one (b2-reciprocal-symmetric lib minus-one))
       (expanded (b2-reciprocal-rewrite lib expanded minus-one '(1 2 2)))
       (negative-factor (b2-fraction-reduction-negative-factor lib scale *proof-one*) :library)
       (computed (b2-reciprocal-chain lib expanded negative-factor))
       (computed (b2-reciprocal-rewrite lib computed unit '(1 2 1)))
       (computed (b2-reciprocal-tidy lib computed))
       (computed
        (if negative
            (b2-reciprocal-results lib
                ((numeric (b2-scaling-number-of-rational lib y ry))
                 (double (b2-fraction-reduction-twice-negated lib y numeric)))
              (b2-reciprocal-chain lib computed double))
          computed))
       (mirror
        (if negative
            (b2-reciprocal-results lib
                ((mirror (b2-rational-order-reverse-negations lib x (library-minus y)))
                 (numeric (b2-scaling-number-of-rational lib y ry))
                 (double (b2-fraction-reduction-twice-negated lib y numeric)))
              (b2-reciprocal-rewrite lib mirror double '(1 1 2)))
          (b2-reciprocal-results lib
              ((mirror (b2-rational-order-reverse-negations lib (library-minus x) y))
               (numeric (b2-scaling-number-of-rational lib x rx))
               (double (b2-fraction-reduction-twice-negated lib x numeric)))
            (b2-reciprocal-rewrite lib mirror double '(1 1 1)))))
       (equation (b2-reciprocal-rewrite lib equation computed '(1 1 2)))
       (equation (b2-reciprocal-rewrite lib equation mirror '(1 1))))
    (b2-reciprocal-return lib (b2-reciprocal-tidy lib equation))))

(defun b2-floor-ranges-scaled-threshold (lib x y k rx ry sign negative)
  (if (equal k *proof-zero*)
      (b2-reciprocal-results lib
          ((bounds (b2-truncate-intervals-ratio-comparisons lib x y rx ry sign negative) :library))
        (cons (car bounds) lib))
    (b2-reciprocal-results lib
        ((data (b2-truncate-intervals-positive-ratio-scale lib x y rx ry sign negative) :library)
         (r (car data))
         (scale (cadr data))
         (rt (caddr data))
         (st (cadddr data))
         (kt (library-library-rational lib k nil))
         (equation (b2-scaling-rational-scale-order lib r k scale (list rt kt st) (nth 4 data)) :library)
         (equation (b2-reciprocal-rewrite lib equation (nth 5 data) '(1 1 1)))
         (commute (b2-reciprocal-axiom lib "COMMUTATIVITY-OF-*" scale *proof-one*))
         (numeric (b2-scaling-number-of-rational lib scale st))
         (unit (b2-products-multiplicative-unit lib scale numeric))
         (unit (b2-reciprocal-chain lib commute unit)))
      (if (equal k *proof-one*)
          (b2-reciprocal-results lib
              ((equation (b2-reciprocal-rewrite lib equation unit '(1 1 2)))
               (equation
                (if negative
                    (b2-reciprocal-results lib
                        ((change (b2-rational-order-reverse-negations lib x y)))
                      (b2-reciprocal-rewrite lib equation change '(1 1)))
                  equation)))
            (b2-reciprocal-return lib (b2-reciprocal-tidy lib equation)))
        (b2-floor-ranges-scaled-threshold-negative-one
         lib x y rx ry scale equation unit negative)))))

(defun b2-floor-ranges-floor-range-theorem-consequent-rules
    (lib name q r fq rq facts)
  (if (member-equal name (list *b2-floor-ranges-sign* *b2-floor-ranges-positive*))
      (let ((level (if (equal name *b2-floor-ranges-sign*) *proof-zero* *proof-one*)))
        (b2-reciprocal-results lib
            ((typed (library-library-type-of lib level nil))
             (below (b2-floor-ranges-floor-below lib q r level fq rq typed facts))
             (rules (if (equal name *b2-floor-ranges-sign*)
                        (list below)
                      (b2-reciprocal-results lib
                          ((positive (b2-floor-ranges-strictly-positive-integer lib q fq)))
                        (list positive below)))))
          (cons (list rules (list level)) lib)))
    (let* ((level (if (equal name *b2-floor-ranges-at-zero*) *proof-zero* *proof-neg-one*))
           (is-zero (equal level *proof-zero*))
           (next-level (if is-zero *proof-one* *proof-zero*))
           (value (if is-zero 1 0)))
      (b2-reciprocal-results lib
          ((point (b2-floor-ranges-floor-point lib q r level fq rq facts) :library)
           (reduction (proof-proof-compute (library-library-proof lib)
                                           (library-plus *proof-one* level) value))
           (point (b2-reciprocal-rewrite lib point reduction '(1 2 2 2)))
           (point (b2-reciprocal-tidy lib point)))
        (cons (list (list point) (list level next-level)) lib)))))

(defun b2-floor-ranges-floor-range-theorem-consequent-divisor-equations
    (lib levels rx ry sign negative)
  (declare (xargs :measure (acl2-count levels)))
  (if (endp levels)
      (cons nil lib)
    (b2-reciprocal-results lib
        ((equation (b2-floor-ranges-scaled-threshold
                    lib *library-x* *library-y* (car levels) rx ry sign negative) :library)
         (tail (b2-floor-ranges-floor-range-theorem-consequent-divisor-equations
                lib (cdr levels) rx ry sign negative) :library))
      (cons (cons equation tail) lib))))

(defun b2-floor-ranges-floor-range-theorem-consequent-divisor-rewrites (lib equations)
  (declare (xargs :measure (acl2-count equations)))
  (if (endp equations)
      nil
    (b2-reciprocal-results lib
        ((reverse (b2-reciprocal-symmetric lib (car equations)))
         (more (b2-floor-ranges-floor-range-theorem-consequent-divisor-rewrites lib (cdr equations))))
      (cons reverse more))))

(defun b2-floor-ranges-floor-range-theorem-consequent-divisor-tests (equations)
  (declare (xargs :measure (acl2-count equations)))
  (if (endp equations)
      nil
    (proof-with-checked-results
        ((equation (proof-step-first (car equations)))
         (test (proof-term-at equation 1))
         (more (b2-floor-ranges-floor-range-theorem-consequent-divisor-tests (cdr equations))))
      (cons test more))))

(defun b2-floor-ranges-floor-range-theorem-consequent-divisor-complete (tests bounds lib goal rewrites)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      (b2-reciprocal-return lib (b2-reciprocal-solve lib goal bounds nil rewrites t))
    (b2-reciprocal-choose lib (car tests) bounds holds more
      (b2-floor-ranges-floor-range-theorem-consequent-divisor-complete
       (cdr tests) more lib goal rewrites))))

(defun b2-floor-ranges-floor-range-theorem-consequent-divisor-finish
    (facts lib name negative sign rx ry rz x-negative x-positive tests goal rewrites)
  (b2-reciprocal-results lib
      ((fact-list
        (if (equal name *b2-floor-ranges-positive*)
            (b2-reciprocal-results lib
                ((known (b2-tactics-tactics-evidence lib facts))
                 (opposite (cdr (assoc-equal (if negative x-positive x-negative) known))))
              (if opposite
                  (b2-reciprocal-results lib
                      ((order (if negative
                                  (b2-rational-order-rational-order-chain
                                   lib sign opposite (list ry rz rx))
                                (b2-rational-order-rational-order-chain
                                 lib opposite sign (list rx rz ry)))))
                    (append facts (list order)))
                facts))
          facts)))
    (b2-floor-ranges-floor-range-theorem-consequent-divisor-complete
     tests fact-list lib goal rewrites)))

(defun b2-floor-ranges-floor-range-theorem-consequent-divisor-signed
    (below facts lib name negative sign rx ry rz x-negative x-positive tests goal rewrites)
  (if below
      (b2-reciprocal-results lib
          ((weak (b2-rational-order-weak-from-strict lib (car (last facts)) rx rz)))
        (b2-floor-ranges-floor-range-theorem-consequent-divisor-finish
         (append facts (list weak)) lib name negative sign rx ry rz x-negative x-positive
         tests goal rewrites))
    (b2-reciprocal-choose lib x-positive facts holds extra
      (b2-floor-ranges-floor-range-theorem-consequent-divisor-finish
       extra lib name negative sign rx ry rz x-negative x-positive tests goal rewrites))))

(defun b2-floor-ranges-floor-range-theorem-consequent-divisor
    (negative sign evidence lib name rx ry levels rules goal)
  (b2-reciprocal-results lib
      ((rz (library-library-rational lib *proof-zero* nil))
       (equations (b2-floor-ranges-floor-range-theorem-consequent-divisor-equations
                   lib levels rx ry sign negative) :library)
       (reverse (b2-floor-ranges-floor-range-theorem-consequent-divisor-rewrites lib equations))
       (rewrites (append rules reverse))
       (tests (b2-floor-ranges-floor-range-theorem-consequent-divisor-tests equations))
       (x-negative (library-lt *library-x* *proof-zero*))
       (x-positive (library-lt *proof-zero* *library-x*)))
    (b2-reciprocal-choose lib x-negative evidence below facts
      (b2-floor-ranges-floor-range-theorem-consequent-divisor-signed
       below facts lib name negative sign rx ry rz x-negative x-positive tests goal rewrites))))

(defun b2-floor-ranges-floor-range-theorem-consequent-divisor-reply
    (request lib name rx ry levels rules goal)
  (b2-floor-ranges-floor-range-theorem-consequent-divisor
   (cadr request) (caddr request) (cadddr request) lib name rx ry levels rules goal))

(defun b2-floor-ranges-floor-range-theorem-consequent
    (premise lib name goal q r types)
  (b2-reciprocal-results lib
      ((known (b2-quotient-algebra-with-forced lib premise))
       (rx (b2-reciprocal-evidence-at known (list *library-rationalp* *library-x*)))
       (ry (b2-reciprocal-evidence-at known (list *library-rationalp* *library-y*)))
       (ratio-type (b2-floor-translation-rational-type lib r known types))
       (rq (car ratio-type))
       (floor-type (b2-numeric-types-types-floor (cdr ratio-type) *library-x* *library-y*)))
    (let ((lib (b2-numeric-types-types-lib (cdr floor-type)))
          (fq (car floor-type)))
      (b2-reciprocal-results lib
          ((facts (b2-floor-intervals-floor-interval lib *library-x* *library-y* rx ry) :library)
           (rules-and-levels (b2-floor-ranges-floor-range-theorem-consequent-rules
                              lib name q r fq rq facts) :library)
           (rules (car rules-and-levels))
           (levels (cadr rules-and-levels))
           (distinct (b2-quotient-algebra-require-nonzero lib *library-y* known))
           (first (b2-rational-order-sign-cases lib *library-y* ry distinct nil))
           (reply (b2-floor-ranges-floor-range-theorem-consequent-divisor-reply
                   (car first) (cdr first) name rx ry levels rules goal))
           (next (b2-rational-order-sign-cases lib *library-y* ry distinct (list reply))))
        (if (eq (caar next) :call)
            (b2-reciprocal-results lib
                ((other (b2-floor-ranges-floor-range-theorem-consequent-divisor-reply
                         (car next) (cdr next) name rx ry levels rules goal)))
              (b2-rational-order-sign-cases lib *library-y* ry distinct (list reply other)))
          next)))))

(defun b2-floor-ranges-floor-range-theorem (lib name formula)
  (b2-reciprocal-results lib
      ((parts (proof-list-of-length formula 3))
       (q (list *b2-floor-intervals-floor* *library-x* *library-y*))
       (r (b2-floor-translation-ratio *library-x* *library-y*))
       (types (b2-numeric-types-types-init lib)))
    (b2-reciprocal-imply lib (cadr parts) (caddr parts) premise
      (b2-floor-ranges-floor-range-theorem-consequent premise lib name (caddr parts) q r types))))
