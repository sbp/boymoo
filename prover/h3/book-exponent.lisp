(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

; A paired binding carries the updated Library or Bounds into the next form.
; A plain binding leaves that object as it is.
(defmacro h3-book-exponent-bind (object bindings body)
  (if (endp bindings)
      body
    (let* ((binding (car bindings))
           (name (car binding))
           (form (cadr binding))
           (rest (cdr bindings)))
      (if (eq (caddr binding) :pair)
          `(let ((exponent-binding-result ,form))
             (if (failure-p exponent-binding-result)
                 (cons exponent-binding-result ,object)
               (let ((,name (car exponent-binding-result))
                     (,object (cdr exponent-binding-result)))
                 (if (failure-p ,name)
                     (cons ,name ,object)
                   (h3-book-exponent-bind ,object ,rest ,body)))))
        `(let ((,name ,form))
           (if (failure-p ,name)
               (cons ,name ,object)
             (h3-book-exponent-bind ,object ,rest ,body)))))))

(defun h3-book-exponent-first-result (result)
  (if (failure-p result) result (car result)))

(defun h3-book-exponent-first-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h3-book-exponent-two-arguments (term)
  (if (integerp term)
      (proof-term-at term 1)
    (proof-list-of-length (cdr term) 2)))

(defun h3-book-exponent-fresh-search (lib)
  (h3-rewrite-search-init lib nil nil nil 150 nil))

(defun h3-book-exponent-prove (lib term)
  (h3-book-exponent-first-result
   (h3-rewrite-search-prove (h3-book-exponent-fresh-search lib) term nil)))

(defun h3-book-exponent-with-library-result (context result)
  (if (failure-p result)
      (cons result context)
    (cons (car result)
          (h3-book-order-bounds-with-library context (cdr result)))))

(defun h3-book-exponent-library-result (result)
  (if (failure-p result)
      result
    (cons (car result) (h3-book-order-bounds-lib (cdr result)))))

(defun h3-book-exponent-type-and-bound (lib term context)
  (let* ((evidence (h3-book-order-bounds-evidence context))
         (nature (table-get evidence (list *library-natp* term) nil))
         (test (list *proof-integerp* term)))
    (if nature
        (h3-book-exponent-bind lib
          ((registered (h3-book-sums-lemmas-with-library lib) :pair)
           (integer (library-library-cite lib "NATURAL-INTEGER"
                                          (list term) (list nature)))
           (bound (library-library-cite lib "NATURAL-NONNEGATIVE"
                                        (list term) (list nature))))
          (cons (list integer bound) lib))
      (let ((integer (table-get evidence test nil)))
        (if integer
            (cons (list integer
                        (table-get evidence (library-le *proof-zero* term) nil))
                  lib)
          (let* ((search (h3-rewrite-search-init
                          lib *h3-book-descent-transparent* nil nil 150 nil))
                 (derived (h3-book-exponent-first-result
                           (h3-rewrite-search-derive search test evidence nil nil))))
            (if (h3-rewrite-unproved-p derived)
                (h3-book-exponent-bind lib
                  ((registered (h3-book-sums-lemmas-with-library lib) :pair))
                  (let ((typed (library-library-type-of
                                lib term (table-values evidence))))
                    (cons (cond
                           ((and (failure-p typed)
                                 (or (equal (cadr typed) "value")
                                     (h3-rewrite-unproved-p typed)))
                            '(:failure "Unproved" ""))
                           ((failure-p typed) typed)
                           (t (list typed nil)))
                          lib)))
              (cons (if (failure-p derived) derived (list derived nil)) lib))))))))

(defun h3-book-exponent-two-data (lib)
  (let* ((search (h3-book-exponent-fresh-search lib))
         (integer-result
          (h3-rewrite-search-prove search
                                   (list *proof-integerp* *h3-book-rounding-two*) nil)))
    (proof-with-checked-results
     ((integer (h3-book-exponent-first-result integer-result))
      (positive (h3-book-exponent-first-result
                 (h3-rewrite-search-prove
                  (cdr integer-result)
                  (library-lt *proof-zero* *h3-book-rounding-two*) nil))))
     (list integer positive))))

(defun h3-book-exponent-floor-power-shift (lib statement exponent value)
  (h3-book-exponent-bind lib
    ((two (h3-book-exponent-two-data lib))
     (index (h3-book-exponent-first-at exponent 1))
     (factor (h3-book-powers-power *h3-book-rounding-two* index))
     (inside (list *h3-book-rounding-fl* value))
     (sides (h3-book-exponent-two-arguments statement))
     (conditional (cadr sides))
     (test (library-lt index *proof-zero*))
     (nonnegative (proof-proof-assume (library-library-proof lib) test nil))
     (divisors (h3-book-powers-natural-power lib (car two) (cadr two)
                                            exponent nonnegative) :pair)
     (division (h3-book-rounding-floor-divisor-shift
                lib value (car divisors) (cadr divisors)) :pair)
     (inside-division (h3-book-rounding-divide-floor lib inside factor))
     (value-division (h3-book-rounding-divide-floor lib value factor))
     (value-division-back (proof-proof-symmetric (library-library-proof lib)
                                                value-division))
     (shifted (proof-proof-chain (library-library-proof lib) inside-division
                                (list division value-division-back)))
     (selection (proof-proof-select (library-library-proof lib) conditional nonnegative))
     (selection-back (proof-proof-symmetric (library-library-proof lib) selection))
     (shifted (proof-proof-chain (library-library-proof lib) shifted (list selection-back)))
     (below (proof-proof-assume (library-library-proof lib) test t))
     (opposite (library-library-type-of lib (library-minus index) (list exponent)))
     (rational-index (h3-book-numerator-as-rational lib exponent))
     (numeric-index (h3-book-signs-number lib rational-index))
     (reflection (h3-book-signs-negative-reflection-with-library lib numeric-index) :pair)
     (sign (proof-proof-rewrite (library-library-proof lib) below reflection '(1)))
     (bound (h3-book-powers-nonnegative-integer lib opposite sign))
     (opposite-power (h3-book-powers-natural-power lib (car two) (cadr two)
                                                  opposite bound) :pair)
     (floor-integer (h3-book-rounding-integer-floor-result lib inside nil) :pair)
     (original (proof-term-at (car sides) 1))
     (rational-base (h3-book-numerator-as-rational lib (car two)))
     (base (h3-book-powers-positive-base lib rational-base (cadr two)) :pair)
     (original-reflexive (proof-proof-reflexive (library-library-proof lib) original))
     (power-opposite (h3-book-powers-power-opposite
                      lib (car base) (cadr base) exponent) :pair)
     (opposite-back (proof-proof-symmetric (library-library-proof lib) power-opposite))
     (equivalent (proof-proof-rewrite (library-library-proof lib)
                                     original-reflexive opposite-back '(1 2 1)))
     (integer-term (h3-book-exponent-first-at equivalent 2))
     (integer (library-library-type-of lib integer-term
                                       (list (car opposite-power) floor-integer)))
     (integer (library-library-transport-argument lib integer equivalent 1))
     (exactly (h3-book-rounding-fl-at-integer lib integer))
     (reversed-test (h3-rewrite-introduce-double-negation lib below))
     (selection (proof-proof-select (library-library-proof lib)
                                    conditional reversed-test))
     (selection-back (proof-proof-symmetric (library-library-proof lib) selection))
     (exactly (proof-proof-chain (library-library-proof lib) exactly (list selection-back))))
    (cons (proof-proof-cases (library-library-proof lib) test exactly shifted) lib)))

(mutual-recursion
 (defun h3-book-exponent-product-factors (term)
   (declare (xargs :measure (acl2-count term)))
   (if (proof-is-call term *proof-times*)
       (h3-book-exponent-product-factors-list (cdr term))
     (list term)))
 (defun h3-book-exponent-product-factors-list (terms)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (append (h3-book-exponent-product-factors (car terms))
             (h3-book-exponent-product-factors-list (cdr terms))))))

(defun h3-book-exponent-nonzero-base-in-context (term context)
  (let ((search (h3-book-order-bounds-search context))
        (evidence (h3-book-order-bounds-evidence context)))
    (h3-book-exponent-bind context
      ((nonzero (h3-rewrite-search-known
                 search (proof-neg (proof-eq term *proof-zero*)) evidence)))
      (if nonzero
          (h3-book-exponent-bind context
            ((numeric (h3-book-order-bounds-numeric context term)))
            (cons (list numeric nonzero) context))
        (h3-book-exponent-bind context
          ((rational (h3-book-order-bounds-rational context term))
           (positive (h3-book-order-bounds-bound-with-bounds
                      context (library-lt *proof-zero* term)) :pair))
          (h3-book-exponent-with-library-result
           context (h3-book-powers-positive-base
                    (h3-book-order-bounds-lib context) rational positive)))))))

(defun h3-book-exponent-nonzero-base-with-context (lib term context)
  (h3-book-exponent-nonzero-base-in-context
   term (h3-book-order-bounds-with-library context lib)))

(defun h3-book-exponent-nonzero-base (lib term context)
  (h3-book-exponent-library-result
   (h3-book-exponent-nonzero-base-with-context lib term context)))

(defun h3-book-exponent-power-factor-value-in-context (factor context)
  (let ((reciprocal (proof-is-call factor *h3-book-arithmetic-divide*)))
    (h3-book-exponent-bind context
      ((term (if reciprocal (proof-term-at factor 1) factor))
       (index-term (proof-term-at term 2))
       (index-data (h3-book-exponent-with-library-result
                    context (h3-book-exponent-type-and-bound
                             (h3-book-order-bounds-lib context) index-term context)) :pair)
       (index (car index-data)))
      (if reciprocal
          (h3-book-exponent-bind context
            ((base-term (proof-term-at term 1))
             (base (h3-book-exponent-nonzero-base-in-context base-term context) :pair)
             (lib (h3-book-order-bounds-lib context))
             (opposite (library-library-type-of lib (library-minus index-term) (list index)))
             (equation (h3-book-exponent-with-library-result
                        context (h3-book-powers-power-opposite
                                 lib (car base) (cadr base) index)) :pair)
             (symmetric (proof-proof-symmetric
                         (library-library-proof (h3-book-order-bounds-lib context)) equation)))
            (cons (list opposite symmetric) context))
        (h3-book-exponent-bind context
          ((reflexive (proof-proof-reflexive
                       (library-library-proof (h3-book-order-bounds-lib context)) term)))
          (cons (list index reflexive) context))))))

(defun h3-book-exponent-power-factor-value (lib factor context)
  (h3-book-exponent-library-result
   (h3-book-exponent-power-factor-value-in-context
    factor (h3-book-order-bounds-with-library context lib))))

(defun h3-book-exponent-combine-power-factors-in-context (first second target context)
  (h3-book-exponent-bind context
    ((registered (h3-book-exponent-with-library-result
                  context (h3-book-sums-lemmas-with-library
                           (h3-book-order-bounds-lib context))) :pair)
     (first-value (h3-book-exponent-power-factor-value-in-context first context) :pair)
     (second-value (h3-book-exponent-power-factor-value-in-context second context) :pair)
     (source (list *proof-times* first second))
     (proof (library-library-proof (h3-book-order-bounds-lib context)))
     (reflexive (proof-proof-reflexive proof source))
     (result (proof-proof-rewrite proof reflexive (cadr first-value) '(1 2 1)))
     (result (proof-proof-rewrite proof result (cadr second-value) '(1 2 2)))
     (sides (h3-book-exponent-two-arguments target))
     (base (h3-book-exponent-nonzero-base-in-context (car sides) context) :pair)
     (first-index (car first-value))
     (second-index (car second-value))
     (lib (h3-book-order-bounds-lib context))
     (addition (h3-book-exponent-with-library-result
                context (h3-book-powers-power-add-integer
                         lib (car base) (cadr base) first-index second-index)) :pair)
     (left (h3-book-exponent-first-at addition 1))
     (sum (proof-term-at left 2))
     (evidence (append (table-values (h3-book-order-bounds-evidence context))
                       (list first-index second-index)))
     (alignment (h3-book-exponent-with-library-result
                 context (h3-book-translation-sum-equality
                          (h3-book-order-bounds-lib context) sum (cadr sides) evidence))
                :pair)
     (proof (library-library-proof (h3-book-order-bounds-lib context)))
     (addition (proof-proof-rewrite proof addition alignment '(1 1 2)))
     (symmetric (proof-proof-symmetric proof addition)))
    (cons (proof-proof-chain proof result (list symmetric)) context)))

(defun h3-book-exponent-combine-power-factors (lib first second target context)
  (h3-book-exponent-library-result
   (h3-book-exponent-combine-power-factors-in-context
    first second target (h3-book-order-bounds-with-library context lib))))

(defun h3-book-exponent-factor-as-power (term)
  (proof-with-checked-results
   ((power (if (proof-is-call term *h3-book-arithmetic-divide*)
               (proof-term-at term 1)
             term)))
   (and (proof-is-call power *h3-book-powers-expt*) power)))

(defun h3-book-exponent-power-factors (factors)
  (declare (xargs :measure (acl2-count factors)))
  (if (endp factors)
      nil
    (proof-with-checked-results
     ((first (h3-book-exponent-factor-as-power (car factors)))
      (rest (h3-book-exponent-power-factors (cdr factors))))
     (if first (cons (car factors) rest) rest))))

(defun h3-book-exponent-align-product (remaining aligned)
  (declare (xargs :measure (acl2-count remaining)))
  (if (endp remaining)
      aligned
    (h3-book-exponent-align-product (cdr remaining)
                                   (list *proof-times* aligned (car remaining)))))

(defun h3-book-exponent-product-candidate (source target factors powers power reversep context)
  (h3-book-exponent-bind context
    ((pair (cons *proof-times* powers))
     (remaining (remove1-equal (cadr powers) (remove1-equal (car powers) factors)))
     (aligned (h3-book-exponent-align-product remaining pair))
     (arrangement (h3-book-arithmetic-associative-equal
                   (h3-book-order-bounds-lib context) source aligned))
     (position (list* 1 2 (make-list-ac (len remaining) 1 nil)))
     (product (h3-book-exponent-combine-power-factors-in-context
               (car powers) (cadr powers) power context) :pair)
     (lib (h3-book-order-bounds-lib context))
     (proof (library-library-proof lib))
     (rewritten (proof-proof-rewrite proof arrangement product position))
     (right (h3-book-exponent-first-at rewritten 2))
     (alignment (h3-book-arithmetic-associative-equal lib right target))
     (chained (proof-proof-chain proof rewritten (list alignment))))
    (cons (if reversep (proof-proof-symmetric proof chained) chained) context)))

(defun h3-book-exponent-try-product-targets (values source target factors powers base reversep context)
  (declare (xargs :measure (acl2-count values)))
  (if (endp values)
      (cons nil context)
    (h3-book-exponent-bind context
      ((value (car values))
       (matches (if (proof-is-call value *h3-book-powers-expt*)
                    (proof-with-checked-results ((term (proof-term-at value 1)))
                      (equal term base))
                  nil)))
      (if matches
          (let ((result (h3-book-exponent-product-candidate
                         source target factors powers value reversep context)))
            (if (h3-rewrite-unproved-p (car result))
                (h3-book-exponent-try-product-targets
                 (cdr values) source target factors powers base reversep (cdr result))
              result))
        (h3-book-exponent-try-product-targets
         (cdr values) source target factors powers base reversep context)))))

(defun h3-book-exponent-try-product (source target reversep context)
  (h3-book-exponent-bind context
    ((factors (h3-book-exponent-product-factors source))
     (powers (h3-book-exponent-power-factors factors)))
    (if (equal (len powers) 2)
        (h3-book-exponent-bind context
          ((first (h3-book-exponent-factor-as-power (car powers)))
           (base (proof-term-at first 1))
           (second (h3-book-exponent-factor-as-power (cadr powers)))
           (other-base (proof-term-at second 1)))
          (if (equal base other-base)
              (h3-book-exponent-try-product-targets
               (h3-book-exponent-product-factors target)
               source target factors powers base reversep context)
            (cons nil context)))
      (cons nil context))))

(defun h3-book-exponent-power-product-equality-in-context (goal context)
  (if (proof-is-call goal *proof-equal*)
      (h3-book-exponent-bind context
        ((equality (proof-list-of-length goal 3))
         (source (cadr equality))
         (target (caddr equality))
         (forward (h3-book-exponent-try-product source target nil context) :pair))
        (if forward
            (cons forward context)
          (h3-book-exponent-try-product target source t context)))
    (cons nil context)))

(defun h3-book-exponent-power-product-equality (lib goal context)
  (h3-book-exponent-library-result
   (h3-book-exponent-power-product-equality-in-context
    goal (h3-book-order-bounds-with-library context lib))))

(defun h3-book-exponent-find-factor (factors head reciprocal)
  (declare (xargs :measure (acl2-count factors)))
  (if (endp factors)
      '(:failure "failure" "")
    (let ((factor (car factors)))
      (proof-with-checked-results
       ((matches
         (and (proof-is-call factor head)
              (if reciprocal
                  (proof-with-checked-results ((term (proof-term-at factor 1)))
                    (proof-is-call term *h3-book-powers-expt*))
                t))))
       (if matches
           factor
         (h3-book-exponent-find-factor (cdr factors) head reciprocal))))))

(defun h3-book-exponent-power-shift-two-factors-in-context (goal context)
  (h3-book-exponent-bind context
    ((sides (h3-book-exponent-two-arguments goal))
     (left (car sides))
     (conditional (cadr sides))
     (term (proof-term-at left 1))
     (factors (h3-book-exponent-product-factors term))
     (reciprocal (h3-book-exponent-find-factor factors *h3-book-arithmetic-divide* t))
     (numerator (h3-book-exponent-find-factor factors *h3-book-powers-expt* nil))
     (inside (h3-book-exponent-find-factor factors *h3-book-rounding-fl* nil))
     (denominator (proof-term-at reciprocal 1))
     (denominator-index (proof-term-at denominator 2))
     (numerator-index (proof-term-at numerator 2))
     (denominator-type (h3-book-exponent-with-library-result
                        context (h3-book-exponent-type-and-bound
                                 (h3-book-order-bounds-lib context)
                                 denominator-index context)) :pair)
     (numerator-type (h3-book-exponent-with-library-result
                      context (h3-book-exponent-type-and-bound
                               (h3-book-order-bounds-lib context)
                               numerator-index context)) :pair)
     (test (proof-term-at conditional 1))
     (comparison (proof-term-at test 1))
     (shift (proof-term-at comparison 1))
     (lib (h3-book-order-bounds-lib context))
     (two (h3-book-exponent-two-data lib))
     (rational-base (h3-book-numerator-as-rational lib (car two)))
     (base (h3-book-exponent-with-library-result
            context (h3-book-powers-positive-base lib rational-base (cadr two))) :pair)
     (registered (h3-book-exponent-with-library-result
                  context (h3-book-sums-lemmas-with-library
                           (h3-book-order-bounds-lib context))) :pair)
     (shift-integer (library-library-type-of
                     (h3-book-order-bounds-lib context) shift
                     (list (car denominator-type) (car numerator-type))))
     (opposite-power (h3-book-powers-power *h3-book-rounding-two* (library-minus shift)))
     (coefficient (h3-book-exponent-combine-power-factors-in-context
                   numerator reciprocal opposite-power context) :pair)
     (opposite (h3-book-exponent-with-library-result
                context (h3-book-powers-power-opposite
                         (h3-book-order-bounds-lib context)
                         (car base) (cadr base) shift-integer)) :pair)
     (lib (h3-book-order-bounds-lib context))
     (proof (library-library-proof lib))
     (coefficient (proof-proof-chain proof coefficient (list opposite)))
     (aligned (list *proof-times* (list *proof-times* numerator reciprocal) inside))
     (arranged (h3-book-arithmetic-associative-equal lib term aligned))
     (arranged (proof-proof-rewrite proof arranged coefficient '(1 2 1)))
     (reflexive (proof-proof-reflexive proof left))
     (paired (proof-proof-rewrite proof reflexive arranged '(1 2 1)))
     (right (h3-book-exponent-first-at paired 2))
     (choice (proof-eq right conditional))
     (value (proof-term-at inside 1))
     (shifted (h3-book-exponent-with-library-result
               context (h3-book-exponent-floor-power-shift
                        lib choice shift-integer value)) :pair))
    (cons (proof-proof-chain
           (library-library-proof (h3-book-order-bounds-lib context))
           paired (list shifted))
          context)))

(defun h3-book-exponent-power-shift-two-factors (lib goal context)
  (h3-book-exponent-library-result
   (h3-book-exponent-power-shift-two-factors-in-context
    goal (h3-book-order-bounds-with-library context lib))))

(defun h3-book-exponent-expt-term (term)
  (cond ((failure-p term) term)
        ((proof-is-call term *h3-book-powers-expt*) term)
        (t nil)))

(defun h3-book-exponent-typed-power (goal)
  (cond
   ((or (proof-is-call goal *proof-integerp*)
        (proof-is-call goal *library-rationalp*))
    (h3-book-exponent-expt-term (proof-term-at goal 1)))
   ((proof-is-call goal *proof-less*)
    (proof-with-checked-results ((left (proof-term-at goal 1)))
      (and (equal left *proof-zero*)
           (h3-book-exponent-expt-term (proof-term-at goal 2)))))
   ((proof-is-call goal *proof-not*)
    (proof-with-checked-results ((inner (proof-term-at goal 1)))
      (if (proof-is-call inner *proof-less*)
          (proof-with-checked-results ((right (proof-term-at inner 2)))
            (and (equal right *proof-zero*)
                 (h3-book-exponent-expt-term (proof-term-at inner 1))))
        nil)))
   (t nil)))

(defun h3-book-exponent-zero-branch (lib case-step term test holds value)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((test-step (proof-proof-assume proof test holds))
      (selection (h3-book-powers-power-equation lib term value (list test-step)))
      (nonnegative (h3-book-exponent-prove lib (library-le *proof-zero* value)))
      (chained (proof-proof-chain proof case-step (list selection)))
      (backward (proof-proof-symmetric proof chained)))
     (proof-proof-rewrite proof nonnegative backward '(1 1 1)))))

(defun h3-book-exponent-nonnegative-power (term base-term index base base-bound known context)
  (h3-book-exponent-bind context
    ((lib (h3-book-order-bounds-lib context))
     (proof (library-library-proof lib))
     (zero (proof-eq base-term *proof-zero*))
     (numeric (h3-book-signs-number lib base))
     (nonzero (proof-proof-assume proof zero nil))
     (negative-zero (proof-step-first nonzero))
     (reversed-zero (h3-rewrite-search-known
                     (h3-book-order-bounds-search context)
                     (proof-neg (proof-eq *proof-zero* base-term))
                     (list (cons negative-zero nonzero))))
     (numeric-zero (h3-book-order-bounds-numeric context *proof-zero*))
     (positive (h3-book-exponent-with-library-result
                context (h3-book-floor-strict-from-weak-with-library
                         lib numeric-zero numeric base-bound reversed-zero)) :pair)
     (result (h3-book-exponent-with-library-result
              context (h3-book-powers-positive-power
                       (h3-book-order-bounds-lib context) base positive known)) :pair)
     (lib (h3-book-order-bounds-lib context))
     (rational-power (h3-book-powers-rational-power lib base index))
     (numeric-power (h3-book-signs-number lib rational-power))
     (signs (h3-book-exponent-with-library-result
             context (h3-book-signs-sign-evidence-with-library lib numeric-power 1 result))
            :pair)
     (negative (h3-book-signs-signs-negative signs))
     (lib (h3-book-order-bounds-lib context))
     (proof (library-library-proof lib))
     (reflexive (proof-proof-reflexive proof term))
     (at-zero (proof-proof-assume proof zero t))
     (case-step (proof-proof-rewrite proof reflexive at-zero '(1 2 1)))
     (zero-power (h3-book-exponent-first-at case-step 2))
     (opened (proof-proof-unfold proof zero-power))
     (body (h3-book-exponent-first-at opened 2))
     (test (proof-term-at body 1))
     (yes (h3-book-exponent-zero-branch lib case-step zero-power test t *proof-one*))
     (no (h3-book-exponent-zero-branch lib case-step zero-power test nil *proof-zero*))
     (branches (proof-proof-cases proof test yes no)))
    (cons (proof-proof-cases proof zero branches negative) context)))

(defun h3-book-exponent-type-base (goal base-term context)
  (if (proof-is-call goal *proof-integerp*)
      (h3-book-exponent-bind context
        ((typed (h3-book-exponent-with-library-result
                 context (h3-book-exponent-type-and-bound
                          (h3-book-order-bounds-lib context) base-term context)) :pair))
        (cons (list (car typed) nil) context))
    (h3-book-exponent-bind context
      ((base (h3-book-order-bounds-rational context base-term))
       (goal (if (proof-is-call goal *proof-less*)
                 (library-lt *proof-zero* base-term)
               (library-le *proof-zero* base-term)))
       (bound (h3-book-order-bounds-bound-with-bounds context goal) :pair))
      (cons (list base bound) context))))

(defun h3-book-exponent-typed-power-result (goal term base-term index base base-bound known bound context)
  (cond
   ((proof-is-call goal *proof-integerp*)
    (h3-book-exponent-bind context
      ((weak (if bound
                 (cons bound context)
               (h3-book-order-bounds-bound-with-bounds
                context (library-le *proof-zero* index))) :pair))
      (h3-book-exponent-with-library-result
       context (h3-book-powers-integral-power-natural
                (h3-book-order-bounds-lib context) base known weak))))
   ((proof-is-call goal *proof-less*)
    (h3-book-exponent-with-library-result
     context (h3-book-powers-positive-power
              (h3-book-order-bounds-lib context) base base-bound known)))
   (t (h3-book-exponent-nonnegative-power term base-term index base base-bound known context))))

(defun h3-book-exponent-type-argument (goal)
  (proof-with-checked-results ((head (proof-term-at goal 0)))
    (cond ((equal head *proof-less*) '(2))
          ((equal head *proof-not*) '(1 1))
          ((equal head *proof-integerp*) '(1))
          (t '(:failure "failure" "")))))

(defun h3-book-exponent-noninteger-case (goal term test proved context)
  (let* ((lib (h3-book-order-bounds-lib context))
         (proof (library-library-proof lib)))
    (h3-book-exponent-bind context
      ((absent (proof-proof-assume proof test nil))
       (equation (h3-book-powers-power-equation lib term *proof-one* (list absent)))
       (argument (h3-book-exponent-type-argument goal))
       (reflexive (proof-proof-reflexive proof goal))
       (tautology (proof-proof-rewrite proof reflexive equation (append '(1 2) argument)))
       (true-goal (h3-book-exponent-first-at tautology 2))
       (truth (h3-book-exponent-prove lib true-goal))
       (transported (proof-proof-transport proof truth tautology)))
      (cons (proof-proof-cases proof test proved transported) context))))

(defun h3-book-exponent-exponent-type-theorem-in-context (goal term context)
  (h3-book-exponent-bind context
    ((parts (h3-book-exponent-two-arguments term))
     (base-term (car parts))
     (index (cadr parts)))
    (if (proof-is-call goal *library-rationalp*)
        (h3-book-exponent-bind context
          ((rational (h3-book-order-bounds-rational context base-term)))
          (cons (h3-book-powers-rational-power
                 (h3-book-order-bounds-lib context) rational index)
                context))
      (h3-book-exponent-bind context
        ((base-data (h3-book-exponent-type-base goal base-term context) :pair))
        (let* ((typing (h3-book-exponent-with-library-result
                        context (h3-book-exponent-type-and-bound
                                 (h3-book-order-bounds-lib context) index context)))
               (typed (car typing))
               (context (cdr typing)))
          (h3-book-exponent-bind context
            ((typed (if (h3-rewrite-unproved-p typed) nil typed))
             (integer (car typed))
             (test (list *proof-integerp* index))
             (known (or integer (proof-proof-assume
                                 (library-library-proof (h3-book-order-bounds-lib context))
                                 test t)))
             (proved (h3-book-exponent-typed-power-result
                      goal term base-term index (car base-data) (cadr base-data)
                      known (cadr typed) context) :pair))
            (if integer
                (cons proved context)
              (h3-book-exponent-noninteger-case goal term test proved context))))))))

(defun h3-book-exponent-exponent-type-theorem (lib goal term context)
  (h3-book-exponent-library-result
   (h3-book-exponent-exponent-type-theorem-in-context
    goal term (h3-book-order-bounds-with-library context lib))))

(defun h3-book-exponent-conjuncts (goal)
  (if (proof-is-call goal *proof-if*)
      (proof-with-checked-results ((other (proof-term-at goal 3)))
        (if (equal other *proof-false*)
            (proof-with-checked-results
             ((first-power (h3-book-exponent-typed-power (cadr goal))))
             (and first-power
                  (proof-with-checked-results
                   ((second-power (h3-book-exponent-typed-power (caddr goal))))
                   (and second-power (list (cadr goal) (caddr goal))))))
          nil))
    nil))

(defun h3-book-exponent-has-product (args)
  (declare (xargs :measure (acl2-count args)))
  (and (consp args)
       (or (proof-is-call (car args) *proof-times*)
           (h3-book-exponent-has-product (cdr args)))))

(defun h3-book-exponent-single-shift (goal context)
  (h3-book-exponent-bind context
    ((left (proof-term-at goal 1))
     (term (proof-term-at left 1))
     (parts (h3-book-exponent-two-arguments term))
     (power (proof-term-at (car parts) 1))
     (index (proof-term-at power 2))
     (typed (h3-book-exponent-with-library-result
             context (h3-book-exponent-type-and-bound
                      (h3-book-order-bounds-lib context) index context)) :pair)
     (value (proof-term-at (cadr parts) 1)))
    (h3-book-exponent-with-library-result
     context (h3-book-exponent-floor-power-shift
              (h3-book-order-bounds-lib context) goal (car typed) value))))

(defun h3-book-exponent-prove-conjuncts (goals context)
  (let ((first (car goals))
        (second (cadr goals)))
    (h3-book-exponent-bind context
      ((first-term (h3-book-exponent-typed-power first))
       (first-step (h3-book-exponent-exponent-type-theorem-in-context
                    first first-term context) :pair)
       (second-term (h3-book-exponent-typed-power second))
       (second-step (h3-book-exponent-exponent-type-theorem-in-context
                     second second-term context) :pair))
      (cons (h3-book-floor-conjunct-proof
             (h3-book-order-bounds-lib context) (list first-step second-step))
            context))))

(defun h3-book-exponent-theorem-recipe (goal single double term conjuncts context)
  (cond (single (h3-book-exponent-single-shift goal context))
        (double (h3-book-exponent-power-shift-two-factors-in-context goal context))
        (term (h3-book-exponent-exponent-type-theorem-in-context goal term context))
        (conjuncts (h3-book-exponent-prove-conjuncts conjuncts context))
        (t (h3-book-exponent-power-product-equality-in-context goal context))))

(defun h3-book-exponent-exponent-theorem (lib name formula)
  (h3-book-exponent-bind lib
    ((parts (if (proof-is-call formula *library-implies*)
                (h3-book-exponent-two-arguments formula)
              (list nil formula)))
     (guard (car parts))
     (goal (cadr parts))
     (single (equal name "FL-SHIFT-FL"))
     (double (member-equal name '("FL-SHIFT-FL-2-FACTORS" "FL-SHIFT-FL-2-FACTORS-2")))
     (term (h3-book-exponent-typed-power goal))
     (conjuncts (h3-book-exponent-conjuncts goal))
     (product (and (proof-is-call goal *proof-equal*)
                   (h3-book-exponent-has-product (cdr goal)))))
    (if (or single double term conjuncts product)
        (h3-book-exponent-bind lib
          ((guardp (and guard (not (equal guard 0)) (not (equal guard ""))))
           (evidence (if guardp
                         (proof-with-checked-results
                          ((step (proof-proof-assume (library-library-proof lib) guard t)))
                          (list step))
                       nil))
           (context (h3-book-order-bounds-init lib evidence))
           (step (h3-book-exponent-library-result
                  (h3-book-exponent-theorem-recipe
                   goal single double term conjuncts context)) :pair))
          (cons (if (and step guardp)
                    (h3-rewrite-implication lib guard step)
                  step)
                lib))
      (cons nil lib))))
