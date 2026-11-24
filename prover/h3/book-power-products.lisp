(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-book-power-products-distribute* "H3-BOOK-POWER-OF-PRODUCT")
(defconst *h3-book-power-products-compose* "H3-BOOK-POWER-OF-POWER")

; A paired binding carries the Library with the value into the next binding.
; Binding the Library itself uses the returned Library and ignores the value.
(defmacro h3-book-power-products-with-results (library bindings result)
  (if (endp bindings)
      result
    (let* ((name (caar bindings))
           (form (cadar bindings))
           (kind (caddar bindings))
           (rest (cdr bindings))
           (next `(h3-book-power-products-with-results ,library ,rest ,result)))
      (cond ((eq kind :pair)
             `(let ((h3-book-power-products-reply ,form))
                (cond ((failure-p h3-book-power-products-reply)
                       (cons h3-book-power-products-reply ,library))
                      ((failure-p (car h3-book-power-products-reply))
                       h3-book-power-products-reply)
                      (t (let ((,library (cdr h3-book-power-products-reply))
                               ,@(if (eq name library)
                                     nil
                                   `((,name (car h3-book-power-products-reply)))))
                           ,next)))))
            ((eq kind :library)
             `(let ((h3-book-power-products-next-library ,form))
                (if (failure-p h3-book-power-products-next-library)
                    (cons h3-book-power-products-next-library ,library)
                  (let ((,library h3-book-power-products-next-library))
                    ,next))))
            (t `(let ((,name ,form))
                  (if (failure-p ,name)
                      (cons ,name ,library)
                    ,next)))))))

(defun h3-book-power-products-checked-pair (result)
  (if (failure-p (car result)) (car result) result))

(defun h3-book-power-products-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h3-book-power-products-term-arguments (term)
  (if (integerp term)
      (proof-term-at term 1)
    (cdr term)))

(defun h3-book-power-products-context-step (context term)
  (let ((entry (assoc-equal term context)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun h3-book-power-products-nonzero-product-data
    (library left right left-nonzero right-nonzero)
  (proof-with-checked-results
      ((a (h3-book-power-products-step-at left 1))
       (b (h3-book-power-products-step-at right 1))
       (numeric (h3-book-arithmetic-typed-number library (list *proof-times* a b)))
       (nonzero (h3-book-arithmetic-no-zero-product
                 library a b left right left-nonzero right-nonzero)))
    (list numeric nonzero)))

(defun h3-book-power-products-distribute-goal (a b n)
  (proof-eq (h3-book-powers-power (list *proof-times* a b) n)
            (list *proof-times* (h3-book-powers-power a n) (h3-book-powers-power b n))))

(defun h3-book-power-products-distribution-at-one-rewrite
    (library rhs terms position evidence)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      rhs
    (proof-with-checked-results
        ((equation (h3-book-powers-power-equation library (car terms) *proof-one* evidence))
         (rhs (proof-proof-rewrite (library-library-proof library)
                                   rhs equation (list 1 2 position))))
      (h3-book-power-products-distribution-at-one-rewrite
       library rhs (cdr terms) (+ 1 position) evidence))))

(defun h3-book-power-products-distribution-at-one (library target evidence)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((arguments (h3-book-power-products-term-arguments target))
         (parts (proof-list-of-length arguments 2))
         (lhs (h3-book-powers-power-equation library (car parts) *proof-one* evidence))
         (rhs (proof-proof-reflexive proof (cadr parts)))
         (factors (h3-book-power-products-term-arguments (cadr parts)))
         (rhs (h3-book-power-products-distribution-at-one-rewrite
               library rhs factors 1 evidence))
         (one (proof-proof-compute proof (list *proof-times* *proof-one* *proof-one*) 1))
         (rhs (proof-proof-chain proof rhs (list one)))
         (flipped (proof-proof-symmetric proof rhs)))
      (proof-proof-chain proof lhs (list flipped)))))

(defun h3-book-power-products-reflect-index-with-library (library negative integer)
  (h3-book-power-products-with-results library
      ((index (h3-book-power-products-step-at integer 1))
       (library (h3-book-sums-lemmas-with-library library) :pair)
       (opposite (library-library-type-of library (library-minus index) (list integer)))
       (rational (h3-book-numerator-as-rational library integer))
       (numeric (h3-book-signs-number library rational))
       (reflected (h3-book-signs-negative-reflection-with-library library numeric) :pair)
       (positive (proof-proof-rewrite (library-library-proof library) negative reflected '(1)))
       (bound (h3-book-powers-nonnegative-integer library opposite positive)))
    (cons (list opposite bound) library)))

(defun h3-book-power-products-reflect-index (library negative integer)
  (h3-book-power-products-checked-pair
   (h3-book-power-products-reflect-index-with-library library negative integer)))

(defun h3-book-power-products-compose-goal (base first second)
  (proof-eq (h3-book-powers-power (h3-book-powers-power base first) second)
            (h3-book-powers-power base (list *proof-times* first second))))

(defun h3-book-power-products-predecessor-multiple-with-library (library first second child)
  (h3-book-power-products-with-results library
      ((m (h3-book-power-products-step-at first 1))
       (n (h3-book-power-products-step-at second 1))
       (previous (h3-book-power-products-step-at child 1))
       (product (list *proof-times* m previous))
       (previous-arguments (h3-book-power-products-term-arguments previous))
       (expanded (library-library-axiom library "DISTRIBUTIVITY" (cons m previous-arguments)))
       (start (proof-proof-reflexive (library-library-proof library) (library-plus m product)))
       (source (proof-proof-rewrite (library-library-proof library) start expanded '(1 2 2)))
       (rational (h3-book-numerator-as-rational library first))
       (numeric (h3-book-signs-number library rational))
       (opposite (h3-book-signs-times-negative-one-with-library library numeric) :pair)
       (commute (library-library-axiom library "COMMUTATIVITY-OF-*" (list m *proof-neg-one*)))
       (negative (proof-proof-chain (library-library-proof library) commute (list opposite)))
       (source (proof-proof-rewrite (library-library-proof library) source negative '(1 2 2 1)))
       (source-term (h3-book-power-products-step-at source 2))
       (sum (h3-book-translation-sum-equality
             library source-term (list *proof-times* m n) (list first second)) :pair)
       (step (proof-proof-chain (library-library-proof library) source (list sum))))
    (cons step library)))

(defun h3-book-power-products-predecessor-multiple (library first second child)
  (h3-book-power-products-checked-pair
   (h3-book-power-products-predecessor-multiple-with-library library first second child)))

(defun h3-book-power-products-product-factor (product position)
  (cond ((natp position) (proof-term-at product position))
        ((and (integerp position) (<= -3 position)) (proof-term-at product (+ 3 position)))
        ((integerp position) '(:failure "failure" ""))
        ((eq position t) (proof-term-at product 1))
        ((null position) (proof-term-at product 0))
        (t '(:failure "failure" ""))))

(defun h3-book-power-products-zero-product-exponent
    (library base first second zero position)
  (let ((product (list *proof-times* first second))
        (proof (library-library-proof library)))
    (proof-with-checked-results
        ((factor (h3-book-power-products-product-factor product position))
         (reduced (h3-book-arithmetic-zero-product library first second factor zero))
         (start (proof-proof-reflexive proof (h3-book-powers-power base product)))
         (result (proof-proof-rewrite proof start reduced '(1 2 2)))
         (zero-law (h3-book-power-identities-power-index-zero library base)))
      (proof-proof-chain proof result (list zero-law)))))

(defun h3-book-power-products-prove-natural-distribution-empty
    (zero library target whole)
  (cons (h3-book-power-products-distribution-at-one library target (list whole zero))
        library))

(defun h3-book-power-products-distribution-predecessors
    (library result bases position whole positive)
  (declare (xargs :measure (acl2-count bases)))
  (if (endp bases)
      (cons result library)
    (h3-book-power-products-with-results library
        ((equation (h3-book-powers-predecessor-equation
                    library (caar bases) (cadar bases) whole positive) :pair)
         (rewritten (proof-proof-rewrite (library-library-proof library)
                                         result equation (list 1 2 position))))
      (h3-book-power-products-distribution-predecessors
       library rewritten (cdr bases) (+ 1 position) whole positive))))

(defun h3-book-power-products-prove-natural-distribution-advance
    (positive child hypothesis library combined nonzero whole target b b-nz c c-nz)
  (declare (ignore child))
  (h3-book-power-products-with-results library
      ((actual (h3-book-powers-predecessor-equation library combined nonzero whole positive) :pair)
       (actual (proof-proof-rewrite (library-library-proof library) actual hypothesis '(1 2 2)))
       (expected (proof-proof-reflexive (library-library-proof library) (caddr target)))
       (expected (h3-book-power-products-distribution-predecessors
                  library expected (list (list b b-nz) (list c c-nz)) 1 whole positive) :pair)
       (left (h3-book-power-products-step-at actual 2))
       (right (h3-book-power-products-step-at expected 2))
       (order (h3-book-arithmetic-associative-equal library left right))
       (flipped (proof-proof-symmetric (library-library-proof library) expected))
       (step (proof-proof-chain (library-library-proof library) actual (list order flipped))))
    (cons step library)))

(defun h3-book-power-products-prove-natural-distribution-with-library (library)
  (let* ((b-type (list *library-numberp* *library-y*))
         (b-nonzero (proof-neg (proof-eq *library-y* *proof-zero*)))
         (c-type (list *library-numberp* *library-z*))
         (c-nonzero (proof-neg (proof-eq *library-z* *proof-zero*)))
         (integer (list *proof-integerp* *library-x*))
         (lower (library-le *proof-zero* *library-x*)))
    (h3-book-power-products-with-results library
        ((library (h3-book-sums-lemmas-with-library library) :pair)
         (guard (h3-book-floor-conjunction
                 (list b-type b-nonzero c-type c-nonzero integer lower)))
         (target (h3-book-power-products-distribute-goal *library-y* *library-z* *library-x*))
         (formula (list *library-implies* guard target))
         (assumed (proof-proof-assume (library-library-proof library) guard t))
         (context (h3-rewrite-search-context
                   (h3-rewrite-search-init library nil nil nil 150 nil) (list assumed)))
         (b (h3-book-power-products-context-step context b-type))
         (b-nz (h3-book-power-products-context-step context b-nonzero))
         (c (h3-book-power-products-context-step context c-type))
         (c-nz (h3-book-power-products-context-step context c-nonzero))
         (whole (h3-book-power-products-context-step context integer))
         (bound (h3-book-power-products-context-step context lower))
         (product (h3-book-power-products-nonzero-product-data library b c b-nz c-nz))
         (zero-case (h3-book-powers-natural-exponent-induction-zero library whole))
         (empty (h3-book-power-products-prove-natural-distribution-empty
                 (cadr zero-case) library target whole) :pair)
         (advance (h3-book-powers-natural-exponent-induction-step
                   library (list b b-nz c c-nz) formula whole bound (car zero-case)) :pair)
         (nonempty (h3-book-power-products-prove-natural-distribution-advance
                    (car advance) (cadr advance) (caddr advance) library
                    (car product) (cadr product) whole target b b-nz c c-nz) :pair)
         (proof (h3-book-powers-natural-exponent-induction
                 library formula whole (car zero-case) (cadddr advance) empty nonempty) :pair)
         (library (library-library-lemma library *h3-book-power-products-distribute*
                                        formula proof nil) :library))
      (cons nil library))))

(defun h3-book-power-products-prove-natural-distribution (library)
  (let ((result (h3-book-power-products-prove-natural-distribution-with-library library)))
    (if (failure-p (car result)) (car result) (cdr result))))

(defun h3-book-power-products-natural-distribution-with-library (library b b-nz c c-nz n bound)
  (let* ((name (proof-sym (concatenate 'string "SELF-" *h3-book-power-products-distribute*)
                          "ACL2"))
         (extension (if (assoc-equal name (proof-proof-facts (library-library-proof library)))
                        (cons nil library)
                      (h3-book-power-products-prove-natural-distribution-with-library library))))
    (if (failure-p (car extension))
        extension
      (let ((library (cdr extension)))
        (h3-book-power-products-with-results library
            ((index (h3-book-power-products-step-at n 1))
             (left (h3-book-power-products-step-at b 1))
             (right (h3-book-power-products-step-at c 1))
             (theorem (library-library-cite library *h3-book-power-products-distribute*
                                            (list index left right) nil))
             (premises (h3-book-floor-conjunct-proof library (list b b-nz c c-nz n bound)))
             (step (proof-proof-modus-ponens (library-library-proof library) theorem premises)))
          (cons step library))))))

(defun h3-book-power-products-natural-distribution (library b b-nz c c-nz n bound)
  (h3-book-power-products-checked-pair
   (h3-book-power-products-natural-distribution-with-library library b b-nz c c-nz n bound)))

(defun h3-book-power-products-distribution-inverses
    (library inverted bases position index below)
  (declare (xargs :measure (acl2-count bases)))
  (if (endp bases)
      (cons inverted library)
    (h3-book-power-products-with-results library
        ((law (h3-book-powers-inverse-power-equation
               library (caar bases) (cadar bases) index below) :pair)
         (flipped (proof-proof-symmetric (library-library-proof library) law))
         (inverted (proof-proof-rewrite (library-library-proof library)
                                        inverted flipped (list 1 2 position))))
      (h3-book-power-products-distribution-inverses
       library inverted (cdr bases) (+ 1 position) index below))))

(defun h3-book-power-products-integer-distribution-with-library (library b b-nz c c-nz n)
  (h3-book-power-products-with-results library
      ((index (h3-book-power-products-step-at n 1))
       (typed (h3-book-power-products-nonzero-product-data library b c b-nz c-nz))
       (test (library-lt index *proof-zero*))
       (not-below (proof-proof-assume (library-library-proof library) test nil))
       (nonnegative (h3-book-power-products-natural-distribution-with-library
                     library b b-nz c c-nz n not-below) :pair)
       (below (proof-proof-assume (library-library-proof library) test t))
       (reflection (h3-book-power-products-reflect-index-with-library library below n) :pair)
       (opposite (car reflection))
       (bound (cadr reflection))
       (equation (h3-book-power-products-natural-distribution-with-library
                  library b b-nz c c-nz opposite bound) :pair)
       (inverted (h3-book-powers-inverse-power-equation
                  library (car typed) (cadr typed) n below) :pair)
       (inverted (proof-proof-rewrite (library-library-proof library) inverted equation '(1 2 1)))
       (power-product (h3-book-power-products-step-at equation 2))
       (factors (h3-book-power-products-term-arguments power-product))
       (powers (proof-list-of-length factors 2))
       (first (car powers))
       (second (cadr powers))
       (target (proof-eq (list *h3-book-arithmetic-divide* (list *proof-times* first second))
                         (list *proof-times*
                               (list *h3-book-arithmetic-divide* first)
                               (list *h3-book-arithmetic-divide* second))))
       (first-type (h3-book-powers-numeric-power library first))
       (second-type (h3-book-powers-numeric-power library second))
       (opposite-index (h3-book-power-products-step-at opposite 1))
       (first-nonzero (h3-book-powers-nonzero-power library b b-nz opposite-index))
       (second-nonzero (h3-book-powers-nonzero-power library c c-nz opposite-index))
       (product (h3-book-arithmetic-reciprocal-product-nonzero
                 library target first-type second-type first-nonzero second-nonzero))
       (inverted (proof-proof-chain (library-library-proof library) inverted (list product)))
       (inverted (h3-book-power-products-distribution-inverses
                  library inverted (list (list b b-nz) (list c c-nz)) 1 n below) :pair)
       (step (proof-proof-cases (library-library-proof library) test inverted nonnegative)))
    (cons step library)))

(defun h3-book-power-products-integer-distribution (library b b-nz c c-nz n)
  (h3-book-power-products-checked-pair
   (h3-book-power-products-integer-distribution-with-library library b b-nz c c-nz n)))

(defun h3-book-power-products-distribute-power-default (position fixed status library goal a b n)
  (let* ((target (cadr goal))
         (pair (caddr goal))
         (prod (cadr target))
         (term (nth position pair))
         (base (cadr term))
         (proof (library-library-proof library)))
    (proof-with-checked-results
        ((flat (h3-book-arithmetic-zero-product library a b base status))
         (numeric (h3-book-arithmetic-typed-number library prod))
         (product-fixed (h3-book-arithmetic-fix-value library prod numeric))
         (product-fixed (proof-proof-chain proof product-fixed (list flat)))
         (zip-test (list *h3-book-power-identities-zip* n))
         (zip (proof-proof-assume proof zip-test t))
         (empty (h3-book-power-products-distribution-at-one library goal (list zip)))
         (notzip (proof-proof-assume proof zip-test nil))
         (left (h3-book-powers-power-equation library target *proof-zero* (list product-fixed notzip)))
         (right (h3-book-powers-power-equation library term *proof-zero* (list fixed notzip)))
         (applied (proof-proof-reflexive proof pair))
         (applied (proof-proof-rewrite proof applied right (list 1 2 position)))
         (clear (if (equal position 1)
                    (h3-book-arithmetic-zero-left library (caddr pair))
                  (h3-event-counts-multiply-zero library (cadr pair))))
         (applied (proof-proof-chain proof applied (list clear)))
         (flipped (proof-proof-symmetric proof applied))
         (ordinary (proof-proof-chain proof left (list flipped))))
      (proof-proof-cases proof zip-test empty ordinary))))

(defun h3-book-power-products-distribute-power-first-numeric (a-type a-nonzero library goal a b n index)
  (h3-book-power-identities-with-base-forms
   library library b
   (b-type b-nonzero)
   (h3-book-power-products-integer-distribution-with-library
    library a-type a-nonzero b-type b-nonzero index)
   (fixed status)
   (cons (h3-book-power-products-distribute-power-default 2 fixed status library goal a b n)
         library)))

(defun h3-book-power-products-distribute-power-with-library (library a b n)
  (let* ((goal (h3-book-power-products-distribute-goal a b n))
         (test (list *proof-integerp* n)))
    (h3-book-power-products-with-results library
        ((not-integer (proof-proof-assume (library-library-proof library) test nil))
         (no (h3-book-power-products-distribution-at-one library goal (list not-integer)))
         (index (proof-proof-assume (library-library-proof library) test t))
         (yes (h3-book-power-identities-with-base-forms
               library library a
               (a-type a-nonzero)
               (h3-book-power-products-distribute-power-first-numeric
                a-type a-nonzero library goal a b n index)
               (fixed status)
               (cons (h3-book-power-products-distribute-power-default 1 fixed status library goal a b n)
                     library)) :pair)
         (step (proof-proof-cases (library-library-proof library) test yes no)))
      (cons step library))))

(defun h3-book-power-products-distribute-power (library a b n)
  (h3-book-power-products-checked-pair
   (h3-book-power-products-distribute-power-with-library library a b n)))

(defun h3-book-power-products-power-reciprocal-base-numeric
    (base-type nonzero library base reciprocal index target term final)
  (h3-book-power-products-with-results library
      ((law (h3-book-arithmetic-inverse library base base-type nonzero))
       (equation (h3-book-power-products-distribute-power-with-library
                  library base reciprocal index) :pair)
       (equation (proof-proof-rewrite (library-library-proof library) equation law '(1 1 1)))
       (flipped (proof-proof-symmetric (library-library-proof library) equation))
       (unit (h3-book-power-identities-power-base-one library index) :pair)
       (equation (proof-proof-chain (library-library-proof library) flipped (list unit)))
       (known (h3-book-powers-power-inverse-law library base-type nonzero index))
       (before (library-library-axiom library "COMMUTATIVITY-OF-*" (list target term)))
       (right (library-library-axiom library "COMMUTATIVITY-OF-*" (list final term)))
       (right (proof-proof-chain (library-library-proof library) right (list known)))
       (flipped (proof-proof-symmetric (library-library-proof library) right))
       (equal-product (proof-proof-chain (library-library-proof library)
                                         before (list equation flipped)))
       (cancelled (h3-book-arithmetic-cancel-product
                   library target final term known equal-product))
       (numeric-target (h3-book-powers-numeric-power library target))
       (fixed-target (h3-book-arithmetic-fix-value library target numeric-target))
       (cancelled (proof-proof-rewrite (library-library-proof library) cancelled fixed-target '(1 1)))
       (numeric-final (h3-book-arithmetic-typed-number library final))
       (fixed-final (h3-book-arithmetic-fix-value library final numeric-final))
       (step (proof-proof-rewrite (library-library-proof library) cancelled fixed-final '(1 2))))
    (cons step library)))

(defun h3-book-power-products-reciprocal-base-default-branch
    (library test holds value target target-fixed term fixed final)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((branch (proof-proof-assume proof test holds))
         (left (h3-book-powers-power-equation library target value (list target-fixed branch)))
         (right (proof-proof-reflexive proof final))
         (at-value (h3-book-powers-power-equation library term value (list fixed branch)))
         (right (proof-proof-rewrite proof right at-value '(1 2 1)))
         (computed (proof-proof-compute proof (list *h3-book-arithmetic-divide* value) (cadr value)))
         (right (proof-proof-chain proof right (list computed)))
         (flipped (proof-proof-symmetric proof right)))
      (proof-proof-chain proof left (list flipped)))))

(defun h3-book-power-products-power-reciprocal-base-default
    (fixed status library base reciprocal index target term final)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((empty (h3-book-arithmetic-zero-test library base status))
         (numeric (h3-book-arithmetic-typed-number library reciprocal))
         (target-fixed (h3-book-arithmetic-fix-value library reciprocal numeric))
         (target-fixed (proof-proof-chain proof target-fixed (list empty)))
         (test (list *h3-book-power-identities-zip* index))
         (yes (h3-book-power-products-reciprocal-base-default-branch
               library test t *proof-one* target target-fixed term fixed final))
         (no (h3-book-power-products-reciprocal-base-default-branch
              library test nil *proof-zero* target target-fixed term fixed final)))
      (proof-proof-cases proof test yes no))))

(defun h3-book-power-products-power-reciprocal-base-with-library (library base index)
  (let* ((term (h3-book-powers-power base index))
         (reciprocal (list *h3-book-arithmetic-divide* base))
         (target (h3-book-powers-power reciprocal index))
         (final (list *h3-book-arithmetic-divide* term)))
    (h3-book-power-identities-with-base-forms
     library library base
     (base-type nonzero)
     (h3-book-power-products-power-reciprocal-base-numeric
      base-type nonzero library base reciprocal index target term final)
     (fixed status)
     (cons (h3-book-power-products-power-reciprocal-base-default
            fixed status library base reciprocal index target term final)
           library))))

(defun h3-book-power-products-power-reciprocal-base (library base index)
  (h3-book-power-products-checked-pair
   (h3-book-power-products-power-reciprocal-base-with-library library base index)))

(defun h3-book-power-products-prove-natural-composition-empty (zero library target second)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((reduced (h3-book-powers-power-equation
                   library (cadr target) *proof-one* (list second zero)))
         (expected (h3-book-power-products-zero-product-exponent
                    library *library-y* *library-z* *library-x* zero 2))
         (flipped (proof-proof-symmetric proof expected)))
      (proof-proof-chain proof reduced (list flipped)))))

(defun h3-book-power-products-prove-natural-composition-advance
    (positive child hypothesis library outer-type outer-nonzero second base nonzero first)
  (h3-book-power-products-with-results library
      ((actual (h3-book-powers-predecessor-equation
                library outer-type outer-nonzero second positive) :pair)
       (actual (proof-proof-rewrite (library-library-proof library) actual hypothesis '(1 2 2)))
       (previous (h3-book-power-products-step-at child 1))
       (multiplication (library-library-type-of
                        library (list *proof-times* *library-z* previous) (list first child)))
       (addition (h3-book-powers-power-add-integer
                  library base nonzero first multiplication) :pair)
       (aligned (h3-book-power-products-predecessor-multiple-with-library
                 library first second child) :pair)
       (addition (proof-proof-rewrite (library-library-proof library) addition aligned '(1 1 2)))
       (flipped (proof-proof-symmetric (library-library-proof library) addition))
       (step (proof-proof-chain (library-library-proof library) actual (list flipped))))
    (cons step library)))

(defun h3-book-power-products-prove-natural-composition-with-library (library)
  (let* ((b-type (list *library-numberp* *library-y*))
         (b-nonzero (proof-neg (proof-eq *library-y* *proof-zero*)))
         (first-type (list *proof-integerp* *library-z*))
         (second-type (list *proof-integerp* *library-x*))
         (lower (library-le *proof-zero* *library-x*)))
    (h3-book-power-products-with-results library
        ((library (h3-book-sums-lemmas-with-library library) :pair)
         (guard (h3-book-floor-conjunction (list b-type b-nonzero first-type second-type lower)))
         (target (h3-book-power-products-compose-goal *library-y* *library-z* *library-x*))
         (formula (list *library-implies* guard target))
         (assumed (proof-proof-assume (library-library-proof library) guard t))
         (context (h3-rewrite-search-context
                   (h3-rewrite-search-init library nil nil nil 150 nil) (list assumed)))
         (base (h3-book-power-products-context-step context b-type))
         (nonzero (h3-book-power-products-context-step context b-nonzero))
         (first (h3-book-power-products-context-step context first-type))
         (second (h3-book-power-products-context-step context second-type))
         (bound (h3-book-power-products-context-step context lower))
         (outer-base (h3-book-powers-power *library-y* *library-z*))
         (outer-type (h3-book-powers-numeric-power library outer-base))
         (outer-nonzero (h3-book-powers-nonzero-power library base nonzero *library-z*))
         (zero-case (h3-book-powers-natural-exponent-induction-zero library second))
         (empty (h3-book-power-products-prove-natural-composition-empty
                 (cadr zero-case) library target second))
         (advance (h3-book-powers-natural-exponent-induction-step
                   library (list base nonzero first) formula second bound (car zero-case)) :pair)
         (nonempty (h3-book-power-products-prove-natural-composition-advance
                    (car advance) (cadr advance) (caddr advance) library
                    outer-type outer-nonzero second base nonzero first) :pair)
         (theorem (h3-book-powers-natural-exponent-induction
                   library formula second (car zero-case) (cadddr advance) empty nonempty) :pair)
         (library (library-library-lemma library *h3-book-power-products-compose*
                                        formula theorem nil) :library))
      (cons nil library))))

(defun h3-book-power-products-prove-natural-composition (library)
  (let ((result (h3-book-power-products-prove-natural-composition-with-library library)))
    (if (failure-p (car result)) (car result) (cdr result))))

(defun h3-book-power-products-natural-composition-with-library (library base nonzero first second bound)
  (let* ((name (proof-sym (concatenate 'string "SELF-" *h3-book-power-products-compose*)
                          "ACL2"))
         (extension (if (assoc-equal name (proof-proof-facts (library-library-proof library)))
                        (cons nil library)
                      (h3-book-power-products-prove-natural-composition-with-library library))))
    (if (failure-p (car extension))
        extension
      (let ((library (cdr extension)))
        (h3-book-power-products-with-results library
            ((n (h3-book-power-products-step-at second 1))
             (b (h3-book-power-products-step-at base 1))
             (m (h3-book-power-products-step-at first 1))
             (theorem (library-library-cite library *h3-book-power-products-compose*
                                            (list n b m) nil))
             (premises (h3-book-floor-conjunct-proof library (list base nonzero first second bound)))
             (step (proof-proof-modus-ponens (library-library-proof library) theorem premises)))
          (cons step library))))))

(defun h3-book-power-products-natural-composition (library base nonzero first second bound)
  (h3-book-power-products-checked-pair
   (h3-book-power-products-natural-composition-with-library library base nonzero first second bound)))

(defun h3-book-power-products-integer-composition-with-library (library base nonzero first second)
  (h3-book-power-products-with-results library
      ((b (h3-book-power-products-step-at base 1))
       (m (h3-book-power-products-step-at first 1))
       (n (h3-book-power-products-step-at second 1))
       (combined (list *proof-times* m n))
       (test (library-lt n *proof-zero*))
       (bound (proof-proof-assume (library-library-proof library) test nil))
       (nonnegative (h3-book-power-products-natural-composition-with-library
                     library base nonzero first second bound) :pair)
       (negative (proof-proof-assume (library-library-proof library) test t))
       (reflection (h3-book-power-products-reflect-index-with-library library negative second) :pair)
       (opposite (car reflection))
       (bound (cadr reflection))
       (reduced (h3-book-power-products-natural-composition-with-library
                 library base nonzero first opposite bound) :pair)
       (outer (h3-book-powers-numeric-power library (h3-book-powers-power b m)))
       (outer-nonzero (h3-book-powers-nonzero-power library base nonzero m))
       (inverted (h3-book-powers-inverse-power-equation library outer outer-nonzero second negative) :pair)
       (inverted (proof-proof-rewrite (library-library-proof library) inverted reduced '(1 2 1)))
       (signed-product (h3-book-signs-minus-product-with-library library m n nil) :pair)
       (inverted (proof-proof-rewrite (library-library-proof library) inverted signed-product '(1 2 1 2)))
       (product-integer (library-library-type-of library combined (list first second)))
       (negative-product (library-library-type-of library (library-minus combined) (list product-integer)))
       (reciprocal (h3-book-powers-power-opposite library base nonzero negative-product) :pair)
       (alignment (h3-book-translation-sum-equality
                   library (library-minus (library-minus combined)) combined (list product-integer)) :pair)
       (reciprocal (proof-proof-rewrite (library-library-proof library) reciprocal alignment '(1 1 2)))
       (flipped (proof-proof-symmetric (library-library-proof library) reciprocal))
       (negative-proof (proof-proof-chain (library-library-proof library) inverted (list flipped)))
       (step (proof-proof-cases (library-library-proof library) test negative-proof nonnegative)))
    (cons step library)))

(defun h3-book-power-products-integer-composition (library base nonzero first second)
  (h3-book-power-products-checked-pair
   (h3-book-power-products-integer-composition-with-library library base nonzero first second)))

(defun h3-book-power-products-compose-power-default-first-zero (zero library base first m n target)
  (h3-book-power-products-with-results library
      ((inner (h3-book-powers-power-equation
               library (h3-book-powers-power base m) *proof-one* (list first zero)))
       (result (proof-proof-reflexive (library-library-proof library) (cadr target)))
       (result (proof-proof-rewrite (library-library-proof library) result inner '(1 2 1)))
       (unit (h3-book-power-identities-power-base-one library n) :pair)
       (known (proof-proof-chain (library-library-proof library) result (list unit)))
       (expected (h3-book-power-products-zero-product-exponent library base m n zero 1))
       (flipped (proof-proof-symmetric (library-library-proof library) expected))
       (step (proof-proof-chain (library-library-proof library) known (list flipped))))
    (cons step library)))

(defun h3-book-power-products-compose-power-default-second-zero (zero library base second m n target)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((known (h3-book-powers-power-equation
                 library (cadr target) *proof-one* (list second zero)))
         (expected (h3-book-power-products-zero-product-exponent library base m n zero 2))
         (flipped (proof-proof-symmetric proof expected)))
      (proof-proof-chain proof known (list flipped)))))

(defun h3-book-power-products-compose-power-default
    (fixed status library base first second m n target)
  (declare (ignore status))
  (let ((m-zero (proof-eq m *proof-zero*))
        (n-zero (proof-eq n *proof-zero*)))
    (h3-book-power-products-with-results library
        ((m-rational (h3-book-numerator-as-rational library first))
         (m-numeric (h3-book-signs-number library m-rational))
         (n-rational (h3-book-numerator-as-rational library second))
         (n-numeric (h3-book-signs-number library n-rational))
         (m-nz (proof-proof-assume (library-library-proof library) m-zero nil))
         (n-nz (proof-proof-assume (library-library-proof library) n-zero nil))
         (product-type (library-library-type-of library (list *proof-times* m n) (list first second)))
         (product-data (h3-book-power-products-nonzero-product-data library m-numeric n-numeric m-nz n-nz))
         (product-nonzero (cadr product-data))
         (inner (h3-book-powers-power-equation library (h3-book-powers-power base m)
                                               *proof-zero* (list first fixed m-nz)))
         (result (proof-proof-reflexive (library-library-proof library) (cadr target)))
         (result (proof-proof-rewrite (library-library-proof library) result inner '(1 2 1)))
         (zero-type (h3-book-arithmetic-typed-number library *proof-zero*))
         (fixed-zero (h3-book-arithmetic-fix-value library *proof-zero* zero-type))
         (outer-transformed (h3-book-power-products-step-at result 2))
         (actual (h3-book-powers-power-equation library outer-transformed *proof-zero*
                                                (list fixed-zero second n-nz)))
         (expected (h3-book-powers-power-equation library (caddr target) *proof-zero*
                                                  (list fixed product-type product-nonzero)))
         (flipped (proof-proof-symmetric (library-library-proof library) expected))
         (no-zero (proof-proof-chain (library-library-proof library) result (list actual flipped)))
         (m-assumption (proof-proof-assume (library-library-proof library) m-zero t))
         (first-zero (h3-book-power-products-compose-power-default-first-zero
                      m-assumption library base first m n target) :pair)
         (n-assumption (proof-proof-assume (library-library-proof library) n-zero t))
         (second-zero (h3-book-power-products-compose-power-default-second-zero
                       n-assumption library base second m n target))
         (rest (proof-proof-cases (library-library-proof library) n-zero second-zero no-zero))
         (step (proof-proof-cases (library-library-proof library) m-zero first-zero rest)))
      (cons step library))))

(defun h3-book-power-products-compose-power-with-library (library base first second)
  (h3-book-power-products-with-results library
      ((m (h3-book-power-products-step-at first 1))
       (n (h3-book-power-products-step-at second 1))
       (target (h3-book-power-products-compose-goal base m n))
       (library (h3-book-sums-lemmas-with-library library) :pair))
    (h3-book-power-identities-with-base-forms
     library library base
     (b-type b-nonzero)
     (h3-book-power-products-integer-composition-with-library library b-type b-nonzero first second)
     (fixed status)
     (h3-book-power-products-compose-power-default fixed status library base first second m n target))))

(defun h3-book-power-products-compose-power (library base first second)
  (h3-book-power-products-checked-pair
   (h3-book-power-products-compose-power-with-library library base first second)))

(defun h3-book-power-products-goal-arguments (value)
  (if (equal (len value) 3)
      (cdr value)
    '(:failure "failure" "")))

(defun h3-book-power-products-guard-present-p (guard)
  (cond ((acl2-numberp guard) (not (equal guard 0)))
        ((stringp guard) (not (equal guard "")))
        (t (not (null guard)))))

(defun h3-book-power-products-theorem-compose (library guard base first second)
  (h3-book-power-products-with-results library
      ((assumed (proof-proof-assume (library-library-proof library) guard t))
       (context (h3-book-order-bounds-init library (list assumed)))
       (first-type (h3-book-exponent-type-and-bound library first context) :pair)
       (context (h3-book-order-bounds-with-library context library))
       (second-type (h3-book-exponent-type-and-bound library second context) :pair))
    (h3-book-power-products-compose-power-with-library
     library base (car first-type) (car second-type))))

(defun h3-book-power-products-theorem-match (library guard goal power-term)
  (h3-book-power-products-with-results library
      ((power-parts (proof-list-of-length power-term 3))
       (value (cadr power-parts))
       (exponent (caddr power-parts)))
    (cond
     ((proof-is-call value *proof-times*)
      (h3-book-power-products-with-results library
          ((args (h3-book-power-products-goal-arguments value)))
        (if (equal goal (h3-book-power-products-distribute-goal (car args) (cadr args) exponent))
            (h3-book-power-products-distribute-power-with-library library (car args) (cadr args) exponent)
          (cons nil library))))
     ((proof-is-call value *h3-book-arithmetic-divide*)
      (h3-book-power-products-with-results library
          ((right (proof-term-at goal 2))
           (base (proof-term-at value 1)))
        (if (equal right (list *h3-book-arithmetic-divide* (h3-book-powers-power base exponent)))
            (h3-book-power-products-power-reciprocal-base-with-library library base exponent)
          (cons nil library))))
     ((and (h3-book-power-products-guard-present-p guard)
           (proof-is-call value *h3-book-powers-expt*))
      (h3-book-power-products-with-results library
          ((args (h3-book-power-products-goal-arguments value)))
        (if (equal goal (h3-book-power-products-compose-goal (car args) (cadr args) exponent))
            (h3-book-power-products-theorem-compose library guard (car args) (cadr args) exponent)
          (cons nil library))))
     (t (cons nil library)))))

(defun h3-book-power-products-power-products-theorem-with-library (library formula)
  (h3-book-power-products-with-results library
      ((parts (if (proof-is-call formula *library-implies*)
                  (proof-list-of-length (cdr formula) 2)
                (list nil formula)))
       (guard (car parts))
       (goal (cadr parts)))
    (if (not (proof-is-call goal *proof-equal*))
        (cons nil library)
      (h3-book-power-products-with-results library
          ((power-term (proof-term-at goal 1)))
        (if (not (proof-is-call power-term *h3-book-powers-expt*))
            (cons nil library)
          (h3-book-power-products-with-results library
              ((result (h3-book-power-products-theorem-match library guard goal power-term) :pair))
            (cons (if (and result (h3-book-power-products-guard-present-p guard))
                      (h3-rewrite-implication library guard result)
                    result)
                  library)))))))

(defun h3-book-power-products-power-products-theorem (library formula)
  (h3-book-power-products-checked-pair
   (h3-book-power-products-power-products-theorem-with-library library formula)))
