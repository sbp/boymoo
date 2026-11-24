(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)
(logic)

(defun t2-floor-split-left (equality)
  (proof-with-checked-results ((literal (proof-step-first equality)))
    (proof-term-at literal 1)))

(defun t2-floor-split-bracket-finish (lib zero-test py smaller ry ratio-type ix iy px wide)
  (let ((proof (library-library-proof lib))
        (dividend *library-x*)
        (divisor *library-y*))
    (proof-with-checked-results
        ((reciprocal (library-library-cite lib "FIELD-RECIPROCAL-POSITIVE"
                                           (list divisor) (list ry)))
         (reciprocal-positive (proof-proof-transport proof py reciprocal))
         (ratio-positive (proof-proof-transport proof reciprocal-positive zero-test))
         (zero-type (t2-arithmetic-arithmetic-type-of lib *proof-zero* nil))
         (floor-zero (library-library-cite lib "FLOOR-BELOW-INTEGER-THRESHOLD"
                                           (list dividend divisor *proof-zero*)
                                           (list ratio-type zero-type)))
         (opposite (t2-order-opposite-order lib ratio-positive))
         (floor-nonnegative (library-library-transport-argument lib opposite floor-zero 1))
         (floor-order (library-library-cite lib "FLOOR-BELOW-INTEGER-THRESHOLD"
                                            (list dividend divisor dividend) (list ratio-type ix)))
         (floor-smaller (proof-proof-transport proof smaller floor-order))
         (floor-type (library-library-cite lib "FLOOR-IS-INTEGER" (list dividend divisor) nil))
         (literal (proof-step-first floor-type)))
      (if (not (equal literal (library-integer (list *t2-floor-floor* dividend divisor))))
          '(:failure "RecipeMismatch" "")
        (proof-with-checked-results
            ((step (t2-power-join lib (list floor-type floor-nonnegative floor-smaller)))
             (claim (proof-step-first step))
             (ix (proof-step-first ix))
             (iy (proof-step-first iy))
             (px (proof-step-first px))
             (wide (proof-step-first wide)))
          (library-library-lemma lib "FLOOR-SPLIT-BOUNDS" claim step
                                 (library-guards (list ix iy px wide))))))))

(defun t2-floor-split-quotient-bracket (lib)
  (let ((proof (library-library-proof lib))
        (dividend *library-x*)
        (divisor *library-y*))
    (if (assoc-equal (proof-sym "SELF-FLOOR-SPLIT-BOUNDS" "ACL2") (proof-proof-facts proof))
        lib
      (proof-with-checked-results
          ((integers (library-library-ints lib (list dividend divisor)))
           (px (proof-proof-assume proof (library-positive dividend) t))
           (wide (proof-proof-assume proof (library-lt *proof-one* divisor) t))
           (one-positive (t2-arithmetic-arithmetic-prove lib (library-positive *proof-one*) nil nil))
           (py (t2-order-strict-chain lib one-positive wide))
           (lib (cdr py))
           (py (car py))
           (ix (car integers))
           (iy (cadr integers))
           (rx (t2-arithmetic-rational lib dividend (list ix)))
           (ry (t2-arithmetic-rational lib divisor (list iy)))
           (invert (t2-field-reciprocal divisor))
           (ratio (t2-products-times dividend invert))
           (ratio-type (t2-order-rational lib ratio (list rx ry)))
           (number-y (t2-order-number-from-rational lib ry))
           (identity-y (t2-field-identity lib divisor number-y *proof-times*))
           (number-y (t2-order-number-from-rational lib ry))
           (distinct (t2-order-distinct lib py))
           (nonzero (t2-products-flip-neq lib distinct))
           (unit (t2-field-inverse lib number-y nonzero))
           (bound (library-library-cite lib "RATIONAL-POSITIVE-ORDER"
                                        (list invert *proof-one* divisor) (list ry py))))
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results
              ((bound (proof-proof-rewrite proof bound unit '(1 1 1)))
               (bound (proof-proof-rewrite proof bound identity-y '(1 1 2)))
               (reciprocal-bound (proof-proof-rewrite proof wide bound '(1)))
               (smaller (library-library-cite lib "RATIONAL-POSITIVE-ORDER"
                                              (list invert *proof-one* dividend) (list rx px)))
               (number-x (t2-order-number-from-rational lib rx))
               (identity-x (t2-field-identity lib dividend number-x *proof-times*))
               (smaller (proof-proof-rewrite proof smaller identity-x '(1 1 2)))
               (smaller (proof-proof-transport proof reciprocal-bound smaller))
               (zero-test (library-library-cite lib "RATIONAL-POSITIVE-ORDER"
                                                (list *proof-zero* invert dividend) (list rx px)))
               (product-zero (t2-products-product-zero lib dividend))
               (lib (cdr product-zero))
               (zero-test (proof-proof-rewrite
                           (library-library-proof lib) zero-test (car product-zero) '(1 1 1))))
            (t2-floor-split-bracket-finish lib zero-test py smaller ry ratio-type ix iy px wide)))))))

(defun t2-floor-split-complement-scheme (negative parent)
  (if (not (proof-is-call negative *proof-minus*))
      nil
    (proof-with-checked-results
        ((removed (proof-term-at negative 1))
         (first (and (proof-is-call removed *proof-plus*) (proof-term-at removed 1))))
      (if (not (equal first *proof-one*))
          nil
        (proof-with-checked-results ((floor (proof-term-at removed 2)))
          (if (not (proof-is-call floor *t2-floor-floor*))
              nil
            (proof-with-checked-results ((value (proof-term-at floor 1)))
              (if (equal value parent) (list floor t) nil))))))))

(defun t2-floor-split-scheme (term parent)
  (cond
   ((proof-is-call term *t2-floor-floor*)
    (proof-with-checked-results ((value (proof-term-at term 1)))
      (if (equal value parent) (list term nil) nil)))
   ((proof-is-call term *proof-plus*)
    (proof-with-checked-results ((value (proof-term-at term 1)))
      (if (equal value parent)
          (proof-with-checked-results ((negative (proof-term-at term 2)))
            (t2-floor-split-complement-scheme negative parent))
        nil)))
   (t nil)))

(defun t2-floor-split-hypotheses-with-library (hypotheses before after)
  (if (equal (t2-tactics-ruler-facts-proof hypotheses) before)
      (t2-tactics-ruler-facts-with-proof hypotheses after)
    hypotheses))

(defun t2-floor-split-divisor-bounds (lib base hypotheses)
  ;; RulerFacts supplies the derived premises for a symbolic divisor.
  (if (proof-is-call base *proof-quote*)
      (proof-with-checked-results
          ((bounds (t2-floor-divisor-bounds lib base
                                            (t2-tactics-ruler-facts-hypotheses hypotheses))))
        (list (caar bounds) (cdr bounds) hypotheses))
    (proof-with-checked-results
        ((integral (t2-tactics-ruler-facts-find hypotheses (library-integer base)))
         (wide (t2-tactics-ruler-facts-find (cdr integral) (library-lt *proof-one* base)))
         (hypotheses (cdr wide)))
      (if (and (car integral) (car wide))
          (list (list (car integral) (car wide)) lib hypotheses)
        (proof-with-checked-results
            ((premise (t2-tactics-ruler-facts-require hypotheses (list *t2-floor-print-base* base)))
             (bounds (t2-floor-print-base-facts lib base (car premise)))
             (hypotheses (t2-floor-split-hypotheses-with-library
                          (cdr premise) lib (cdr bounds))))
          (list (car bounds) (cdr bounds) hypotheses))))))

(defun t2-floor-split-count-quotient (lib integral nonnegative smaller int-value pos-value)
  (proof-with-checked-results
      ((after (t2-arithmetic-natural-from-sign lib integral nonnegative))
       (after (t2-arithmetic-count-natural lib after))
       (lib (cdr after))
       (after (car after))
       (before (t2-arithmetic-natural-from-positive lib int-value pos-value))
       (before (t2-arithmetic-count-natural lib before))
       (lib (cdr before))
       (before (car before))
       (comparison (library-library-transport-argument lib smaller after 1))
       (comparison (library-library-transport-argument lib comparison before 2))
       (left (t2-floor-split-left after))
       (right (t2-floor-split-left before))
       (ordinal (t2-arithmetic-arithmetic-ordinal-comparison lib left right nil))
       (step (proof-proof-transport (library-library-proof lib) comparison ordinal)))
    (cons step lib)))

(defun t2-floor-split-count-complement (lib floor integral nonnegative smaller int-value)
  (let ((proof (library-library-proof lib))
        (removed (library-plus *proof-one* floor)))
    (proof-with-checked-results
        ((int-removed (t2-arithmetic-arithmetic-type-of lib removed (list integral)))
         (bound (t2-products-discrete-step lib smaller (list int-value integral)))
         (translation (library-library-cite lib "FIELD-ORDER-TRANSLATION"
                                              (list *proof-zero* *proof-one* floor) nil))
         (positive (t2-arithmetic-arithmetic-prove lib (library-positive *proof-one*) nil nil))
         (next-floor (proof-proof-transport proof positive translation))
         (numeric (t2-arithmetic-number lib floor (list integral)))
         (zero (t2-arithmetic-arithmetic-numeric-add-zero lib numeric))
         (next-floor (proof-proof-rewrite proof next-floor zero '(1 1)))
         (positive-removed (t2-arithmetic-arithmetic-compare-chain
                            lib nonnegative next-floor (list integral int-removed))))
      (t2-subtraction-count-subtraction lib int-value int-removed positive-removed bound))))

(defun t2-floor-split-decrease (lib split hypotheses)
  (proof-with-checked-results
      ((split (proof-list-of-length split 2))
       (floor (car split))
       (parts (proof-list-of-length floor 3))
       (value (cadr parts))
       (divisor (caddr parts))
       (int-value (t2-tactics-ruler-facts-require hypotheses (library-integer value)))
       (pos-value (t2-tactics-ruler-facts-require (cdr int-value) (library-positive value)))
       (bounds (t2-floor-split-divisor-bounds lib divisor (cdr pos-value)))
       (lib (cadr bounds))
       (hypotheses (caddr bounds))
       (built (t2-floor-split-quotient-bracket lib))
       (about-floor (library-library-cite built "FLOOR-SPLIT-BOUNDS" (list value divisor)
                                          (list (car int-value) (caar bounds) (car pos-value)
                                                (cadar bounds))))
       (conjuncts (t2-power-conjuncts built about-floor 3))
       (integral (car conjuncts))
       (nonnegative (cadr conjuncts))
       (smaller (caddr conjuncts))
       (decrease (if (cadr split)
                     (t2-floor-split-count-complement built floor integral nonnegative
                                                       smaller (car int-value))
                   (t2-floor-split-count-quotient built integral nonnegative smaller
                                                  (car int-value) (car pos-value)))))
    (list (car decrease) (cdr decrease)
          (t2-floor-split-hypotheses-with-library hypotheses lib (cdr decrease)))))

(defun t2-floor-split-clause-scheme (clause measure)
  (proof-with-checked-results
      ((smaller (proof-term-at (car (last clause)) 1))
       (term (proof-term-at smaller 1))
       (parent (proof-term-at measure 1)))
    (t2-floor-split-scheme term parent)))

(defun t2-floor-split-schemes (cases measure)
  (if (endp cases)
      nil
    (if (cadar cases)
        (proof-with-checked-results
            ((split (t2-floor-split-clause-scheme (caar cases) measure))
             (rest (t2-floor-split-schemes (cdr cases) measure)))
          (cons split rest))
      (t2-floor-split-schemes (cdr cases) measure))))

(defun t2-floor-split-has-complement (splits)
  (and (consp splits)
       (or (cadar splits) (t2-floor-split-has-complement (cdr splits)))))

(defun t2-floor-split-case-proof (lib clause call measure)
  (if call
      (proof-with-checked-results
          ((split (t2-floor-split-clause-scheme clause measure))
           (facts (t2-tactics-ruler-facts-init lib (termination-call-tests call) nil))
           (decrease (t2-floor-split-decrease lib split facts)))
        (cons (car decrease) (cadr decrease)))
    (proof-with-checked-results
        ((parent (proof-term-at measure 1))
         (step (library-library-builtin lib 1 parent)))
      (cons step lib))))

(defun t2-floor-split-case-proofs (lib cases measure seen)
  (declare (xargs :measure (len cases)))
  (if (or (endp cases) (not (o< (len (cdr cases)) (len cases))))
      (cons nil lib)
    (let ((clause (caar cases))
          (call (cadar cases)))
      (if (member-equal clause seen)
          (t2-floor-split-case-proofs lib (cdr cases) measure seen)
        (proof-with-checked-results
            ((result (t2-floor-split-case-proof lib clause call measure))
             (lib (cdr result))
             (step (proof-proof-subsume (library-library-proof lib) (car result) clause))
             (rest (t2-floor-split-case-proofs lib (cdr cases) measure (cons clause seen))))
          (cons (cons step (car rest)) (cdr rest)))))))

(defun t2-floor-split-definition (lib definitions calls measures)
  (if (or (not (equal (len definitions) 1)) (endp calls))
      (cons nil lib)
    (proof-with-checked-results ((name (proof-term-at (car definitions) 0)))
      (let ((entry (assoc-equal name measures)))
        (cond
         ((not entry) '(:failure "MissingBinding" ""))
         ((not (proof-is-call (cdr entry) *library-count*)) (cons nil lib))
         (t
          (let ((measure (cdr entry)))
            (proof-with-checked-results
                ((cases (termination-obligation-cases definitions measures calls))
                 (splits (t2-floor-split-schemes cases measure)))
              (if (or (member-equal nil splits) (not (t2-floor-split-has-complement splits)))
                  (cons nil lib)
                (proof-with-checked-results
                    ((proofs (t2-floor-split-case-proofs lib cases measure nil))
                     (entry (proof-proof-entry "measure" name (list name measure) (car proofs))))
                  (cons entry (cdr proofs))))))))))))
