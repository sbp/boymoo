(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h3-book-quotient-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h3-book-quotient-tail-of-size (term size)
  (if (integerp term)
      '(:failure "failure" "")
    (proof-list-of-length (cdr term) size)))

(defun h3-book-quotient-reciprocal-factor (term)
  (cond
   ((proof-is-call term *h3-book-arithmetic-divide*)
    (proof-with-checked-results ((divisor (proof-term-at term 1)))
      (list divisor *proof-one*)))
   ((proof-is-call term *proof-times*)
    (proof-with-checked-results ((left (proof-term-at term 1)))
      (if (proof-is-call left *h3-book-arithmetic-divide*)
          (proof-with-checked-results ((divisor (proof-term-at left 1))
                                       (right (proof-term-at term 2)))
            (list divisor right))
        (proof-with-checked-results ((right (proof-term-at term 2)))
          (if (proof-is-call right *h3-book-arithmetic-divide*)
              (proof-with-checked-results ((divisor (proof-term-at right 1)))
                (list divisor left))
            nil)))))))

(defun h3-book-quotient-cancel-inverse-pair (lib term divisor argument law)
  (let ((proof (library-library-proof lib))
        (grouped (list *proof-times*
                       (list *proof-times* divisor (list *h3-book-arithmetic-divide* divisor))
                       argument)))
    (proof-with-checked-results
        ((step (h3-book-arithmetic-associative-equal lib term grouped))
         (step (proof-proof-rewrite proof step law '(1 2 1)))
         (unit (library-library-axiom lib "UNICITY-OF-1" (list argument))))
      (proof-proof-chain proof step (list unit)))))

(defun h3-book-quotient-clear-reciprocal (lib term divisor law numerator-type)
  (let ((proof (library-library-proof lib))
        (product (list *proof-times* term divisor)))
    (proof-with-checked-results ((fraction (h3-book-quotient-reciprocal-factor term)))
      (cond
       ((or (not fraction) (not (equal (car fraction) divisor)))
        (proof-proof-reflexive proof product))
       ((proof-is-call term *h3-book-arithmetic-divide*)
        (proof-with-checked-results
            ((commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list term divisor))))
          (proof-proof-chain proof commuted (list law))))
       (t
        (let ((numerator (cadr fraction)))
          (proof-with-checked-results
              ((step (h3-book-quotient-cancel-inverse-pair lib product divisor numerator law)))
            (if numerator-type
                (proof-with-checked-results
                    ((fixed (h3-book-arithmetic-fix-value lib numerator numerator-type)))
                  (proof-proof-chain proof step (list fixed)))
              step))))))))

(defun h3-book-quotient-rational-binary (lib productp args)
  (if (equal (len args) 2)
      (if productp
          (h3-book-signs-rational-product lib (car args) (cadr args))
        (h3-numeric-rational-sum lib (car args) (cadr args)))
    '(:failure "failure" "")))

(mutual-recursion
 (defun h3-book-quotient-rational-type (lib term evidence)
   (declare (xargs :measure (acl2-count term)))
   (let* ((proof (library-library-proof lib))
          (claim (list *library-rationalp* term))
          (known (table-get evidence claim nil))
          (integer (table-get evidence (list *proof-integerp* term) nil)))
     (cond
      (known known)
      (integer
       (proof-with-checked-results
           ((rule (library-library-axiom lib "INTEGER-IMPLIES-RATIONAL" (list term))))
         (proof-proof-modus-ponens proof rule integer)))
      ((or (proof-is-call term *h3-book-arithmetic-divide*)
           (proof-is-call term *proof-minus*))
       (if (endp (cdr term))
           '(:failure "failure" "")
         (let ((name (if (proof-is-call term *h3-book-arithmetic-divide*)
                         "rationalp-unary-/"
                       "rationalp-unary--")))
           (proof-with-checked-results
               ((rule (proof-proof-fact proof name (list (list *library-x* (cadr term)))))
                (rational (h3-book-quotient-rational-type lib (cadr term) evidence)))
             (proof-proof-modus-ponens proof rule rational)))))
      ((and (consp term)
            (or (proof-is-call term *proof-times*) (proof-is-call term *proof-plus*)))
       (proof-with-checked-results
           ((args (h3-book-quotient-rational-type-arguments lib (cdr term) evidence)))
         (h3-book-quotient-rational-binary lib (proof-is-call term *proof-times*) args)))
      (t
       (let ((search (h3-rewrite-search-init lib nil nil nil 150 nil)))
         (car (h3-rewrite-search-prove search claim nil)))))))

 (defun h3-book-quotient-rational-type-arguments (lib args evidence)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((first (h3-book-quotient-rational-type lib (car args) evidence))
          (rest (h3-book-quotient-rational-type-arguments lib (cdr args) evidence)))
       (cons first rest)))))

(defun h3-book-quotient-rational-difference (lib first second)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((term (h3-book-quotient-step-at second 1))
         (rule (proof-proof-fact proof "rationalp-unary--" (list (list *library-x* term))))
         (negative (proof-proof-modus-ponens proof rule second)))
      (h3-numeric-rational-sum lib first negative))))

; A checked :paired binding supplies both its value and the next Library.
(defmacro h3-book-quotient-with-library (lib bindings result)
  (if (endp bindings)
      `(cons ,result ,lib)
    (let* ((binding (car bindings))
           (name (car binding))
           (form (cadr binding))
           (rest (cdr bindings)))
      (if (eq (caddr binding) :paired)
          `(let ((,name ,form))
             (if (failure-p ,name)
                 (cons ,name ,lib)
               (let ((,lib (cdr ,name))
                     (,name (car ,name)))
                 (if (failure-p ,name)
                     (cons ,name ,lib)
                   (h3-book-quotient-with-library ,lib ,rest ,result)))))
        `(let ((,name ,form))
           (if (failure-p ,name)
               (cons ,name ,lib)
             (h3-book-quotient-with-library ,lib ,rest ,result)))))))

(defun h3-book-quotient-distribute-difference-with-library (lib a b factor)
  (let ((proof (library-library-proof lib))
        (delta (library-diff a b)))
    (h3-book-quotient-with-library lib
        ((commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list delta factor)))
         (distributed (library-library-axiom lib "DISTRIBUTIVITY" (list factor a (library-minus b))))
         (expanded (proof-proof-chain proof commuted (list distributed)))
         (negative (h3-book-signs-minus-product-with-library lib factor b nil) :paired)
         (proof (library-library-proof lib))
         (expanded (proof-proof-rewrite proof expanded negative '(1 2 2)))
         (from (h3-book-quotient-step-at expanded 2))
         (ordered (library-diff (list *proof-times* a factor) (list *proof-times* b factor)))
         (equality (h3-book-arithmetic-associative-equal lib from ordered))
         (chained (proof-proof-chain proof expanded (list equality))))
      (proof-proof-symmetric proof chained))))

(defun h3-book-quotient-opposite-difference-with-library (lib a b)
  (h3-book-quotient-with-library lib
      ((added (h3-book-sums-lemmas-with-library lib) :paired)
       (proof (library-library-proof lib))
       (equality (library-library-cite lib *h3-book-sums-negate* (list a (library-minus b)) nil))
       (double (library-library-cite lib *h3-book-sums-double* (list b) nil))
       (equality (proof-proof-rewrite proof equality double '(1 2 2)))
       (right (h3-book-quotient-step-at equality 2))
       (commuted (library-library-axiom lib "COMMUTATIVITY-OF-+" (cdr right)))
       (equality (proof-proof-chain proof equality (list commuted)))
       (addend (library-library-cite lib *h3-book-sums-add* (list b (library-minus a)) nil))
       (restored (proof-proof-symmetric proof addend)))
    (proof-proof-chain proof equality (list restored))))

(defun h3-book-quotient-scale-order-comparison (lib left right scalar signs types positive)
  (if types
      (h3-book-quotient-with-library lib
          ((parts (proof-list-of-length types 2))
           (first (if positive (car parts) (cadr parts)))
           (second (if positive (cadr parts) (car parts)))
           (delta (h3-book-quotient-rational-difference lib first second))
           (comparison (h3-book-signs-rational-scaling-with-library lib delta scalar signs -1) :paired))
        comparison)
    (h3-book-quotient-with-library lib
        ((comparison (h3-book-signs-scaled-comparison-with-library lib (library-diff left right)
                                                     scalar signs -1) :paired))
      comparison)))

(defun h3-book-quotient-scale-order-reflect (lib scaled a b)
  (h3-book-quotient-with-library lib
      ((opposite (h3-book-quotient-opposite-difference-with-library lib a b) :paired)
       (proof (library-library-proof lib))
       (opposite (proof-proof-symmetric proof opposite))
       (scaled (proof-proof-rewrite proof scaled opposite '(1 2 2)))
       (difference (h3-book-arithmetic-typed-number lib (library-diff a b)))
       (reflection (h3-book-signs-negative-reflection-with-library lib difference) :paired)
       (proof (library-library-proof lib))
       (reflection (proof-proof-symmetric proof reflection)))
    (proof-proof-chain proof scaled (list reflection))))

(defun h3-book-quotient-scale-order-with-library (lib a b scalar signs types)
  (let* ((positive (< 0 (h3-book-signs-signs-sign signs)))
         (left (if positive a b))
         (right (if positive b a)))
    (h3-book-quotient-with-library lib
        ((z (h3-book-quotient-step-at scalar 1))
         (scaled (library-library-axiom lib "<-ON-OTHERS"
                                        (list (list *proof-times* left z) (list *proof-times* right z))))
         (distributed (h3-book-quotient-distribute-difference-with-library lib left right z) :paired)
         (proof (library-library-proof lib))
         (scaled (proof-proof-rewrite proof scaled distributed '(1 2 1)))
         (comparison (h3-book-quotient-scale-order-comparison lib left right scalar signs types positive) :paired)
         (proof (library-library-proof lib))
         (scaled (proof-proof-chain proof scaled (list comparison)))
         (scaled (if positive (cons scaled lib)
                   (h3-book-quotient-scale-order-reflect lib scaled a b)) :paired)
         (proof (library-library-proof lib))
         (comparison (library-library-axiom lib "<-ON-OTHERS" (list a b)))
         (scaled (proof-proof-symmetric proof scaled)))
      (proof-proof-chain proof comparison (list scaled)))))

(defun h3-book-quotient-symmetric (step proof)
  (proof-proof-symmetric proof step))

(defun h3-book-quotient-quotient-equality-branch-forward (equality lib quotient divisor law q)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step (proof-proof-reflexive proof (list *proof-times* quotient divisor)))
         (step (proof-proof-rewrite proof step equality '(1 2 1)))
         (cleared (h3-book-quotient-clear-reciprocal lib quotient divisor law nil))
         (step (proof-proof-rewrite proof step cleared '(1 1)))
         (from (h3-book-quotient-step-at step 2))
         (to (proof-term-at q 2))
         (arranged (h3-book-arithmetic-associative-equal lib from to)))
      (proof-proof-chain proof step (list arranged)))))

(defun h3-book-quotient-quotient-equality-branch-backward
    (equality lib q reciprocal numerator quotient divisor result law result-type)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((base (proof-term-at q 1))
         (step (proof-proof-reflexive proof (list *proof-times* base reciprocal)))
         (step (proof-proof-rewrite proof step equality '(1 2 1)))
         (multiply (h3-book-arithmetic-multiply-fix lib numerator reciprocal))
         (step (proof-proof-rewrite proof step multiply '(1 1)))
         (source (h3-book-quotient-step-at step 1))
         (arranged (h3-book-arithmetic-associative-equal lib source quotient))
         (step (proof-proof-rewrite proof step arranged '(1 1)))
         (target (h3-book-quotient-step-at step 2))
         (cancelled (h3-book-quotient-cancel-inverse-pair lib target divisor result law))
         (step (proof-proof-chain proof step (list cancelled)))
         (fixed (h3-book-arithmetic-fix-value lib result result-type)))
      (proof-proof-chain proof step (list fixed)))))

(defun h3-book-quotient-quotient-equality-zero
    (lib formula quotient divisor reciprocal numerator result status fixed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (proof-step-first status))
         (fixed (if (proof-is-call first *proof-equal*)
                    (proof-proof-chain proof fixed (list status))
                  fixed))
         (zero (h3-book-arithmetic-zero-test lib divisor status))
         (product (proof-proof-reflexive proof quotient))
         (factor (proof-term-at quotient 1))
         (index (if (equal factor reciprocal) 1 2))
         (product (proof-proof-rewrite proof product zero (list 1 2 index)))
         (from (h3-book-quotient-step-at product 2))
         (ordered (h3-book-arithmetic-associative-equal lib from (list *proof-times* numerator *proof-zero*)))
         (vanishes (h3-event-counts-multiply-zero lib numerator))
         (product (proof-proof-chain proof product (list ordered vanishes)))
         (symmetric (h3-book-arithmetic-with-equivalent-equalities
                     lib (proof-eq *proof-zero* result) (proof-eq result *proof-zero*)
                     (h3-book-quotient-symmetric proof) (h3-book-quotient-symmetric proof))))
      (let ((search (h3-rewrite-search-init lib (list *proof-not*) nil nil 150 nil)))
        (car (h3-rewrite-search-prove search formula (list fixed product symmetric)))))))

(defun h3-book-quotient-quotient-equality-nonzero
    (lib formula p q number-test quotient divisor reciprocal numerator result numeric status fixed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((law (h3-book-arithmetic-inverse lib divisor numeric status))
         (symmetric (proof-proof-symmetric proof fixed))
         (not-zero (proof-proof-rewrite proof status symmetric '(1 1 1)))
         (result-type (proof-proof-assume proof number-test t))
         (comparison
          (h3-book-arithmetic-with-equivalent-equalities
           lib p q
           (h3-book-quotient-quotient-equality-branch-forward lib quotient divisor law q)
           (h3-book-quotient-quotient-equality-branch-backward
            lib q reciprocal numerator quotient divisor result law result-type)))
         (search (h3-rewrite-search-init lib (list *proof-not*) nil nil 150 nil))
         (yes (car (h3-rewrite-search-prove search formula (list not-zero result-type comparison))))
         (absent (proof-proof-assume proof number-test nil))
         (typed (h3-book-arithmetic-typed-number lib quotient))
         (given (proof-proof-assume proof p t))
         (impossible (proof-proof-rewrite proof typed given '(1 1)))
         (cut (proof-proof-cut proof impossible absent))
         (negative (proof-proof-front proof cut (proof-neg p)))
         (search (h3-rewrite-search-init lib (list *proof-not*) nil nil 150 nil))
         (nil-step (h3-rewrite-nil-value lib negative))
         (no (car (h3-rewrite-search-prove search formula (list not-zero absent nil-step)))))
      (proof-proof-cases proof number-test yes no))))

(defun h3-book-quotient-quotient-equality-branch
    (numeric status nonzero lib formula p q number-test quotient divisor reciprocal numerator result)
  (proof-with-checked-results ((fixed (h3-book-arithmetic-fix-value lib divisor numeric)))
    (if nonzero
        (h3-book-quotient-quotient-equality-nonzero
         lib formula p q number-test quotient divisor reciprocal numerator result numeric status fixed)
      (h3-book-quotient-quotient-equality-zero
       lib formula quotient divisor reciprocal numerator result status fixed))))

(defun h3-book-quotient-quotient-equality (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 3))
       (p (cadr formula))
       (rhs (caddr formula))
       (pair (h3-book-quotient-tail-of-size p 2))
       (quotient (car pair))
       (result (cadr pair))
       (fraction (h3-book-quotient-reciprocal-factor quotient))
       (fraction (or fraction '(:failure "failure" "")))
       (divisor (car fraction))
       (numerator (cadr fraction))
       (reciprocal (list *h3-book-arithmetic-divide* divisor))
       (conditional (proof-term-at rhs 3))
       (branches (h3-book-quotient-tail-of-size conditional 3))
       (number-test (car branches))
       (q (cadr branches)))
    (h3-book-arithmetic-with-scalar-cases
     lib divisor
     (h3-book-quotient-quotient-equality-branch
      lib formula p q number-test quotient divisor reciprocal numerator result))))

; Each sign case receives the Library from the preceding proof operations.
(defmacro h3-book-quotient-each-sign-with-library (lib numeric case &rest args)
  `(h3-book-signs-each-sign-with-library ,lib ,numeric ,case ,@args))

(defmacro h3-book-quotient-sign-callback (lib signs case &rest args)
  `(,case ,signs ,lib ,@args))

(defun h3-book-quotient-fraction-index (sides index)
  (if (endp sides)
      '(:failure "failure" "")
    (proof-with-checked-results ((found (h3-book-quotient-reciprocal-factor (car sides))))
      (if found
          index
        (h3-book-quotient-fraction-index (cdr sides) (1+ index))))))

(defun h3-book-quotient-quotient-order-nonzero
    (lib signs sides forms scalar divisor scalar-num quotient numerator-num fraction-index)
  (h3-book-quotient-with-library lib
      ((sides (proof-list-of-length sides 2))
       (equation (h3-book-quotient-scale-order-with-library
                  lib (car sides) (cadr sides) scalar signs forms) :paired)
       (law (h3-book-arithmetic-inverse lib divisor scalar-num (h3-book-signs-signs-zero signs)))
       (clearing (h3-book-quotient-clear-reciprocal lib quotient divisor law numerator-num))
       (position (if (< 0 (h3-book-signs-signs-sign signs)) fraction-index (- 3 fraction-index))))
    (proof-proof-rewrite (library-library-proof lib) equation clearing (list 1 2 position))))

(defun h3-book-quotient-quotient-order-zero-product (lib quotient numerator zero)
  (if (proof-is-call quotient *proof-times*)
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((product (proof-proof-reflexive proof quotient))
             (factor (proof-term-at quotient 1))
             (position (if (proof-is-call factor *h3-book-arithmetic-divide*) 1 2))
             (product (proof-proof-rewrite proof product zero (list 1 2 position)))
             (from (h3-book-quotient-step-at product 2))
             (normalized (h3-book-arithmetic-associative-equal
                          lib from (list *proof-times* numerator *proof-zero*)))
             (vanishes (h3-event-counts-multiply-zero lib numerator)))
          (proof-proof-chain proof product (list normalized vanishes))))
    zero))

(defun h3-book-quotient-quotient-order-zero
    (lib signs divisor quotient numerator comparison fraction-index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((zero (h3-book-arithmetic-zero-test lib divisor (h3-book-signs-signs-zero signs)))
         (zero (h3-book-quotient-quotient-order-zero-product lib quotient numerator zero))
         (identity (proof-proof-reflexive proof comparison)))
      (proof-proof-rewrite proof identity zero (list 1 2 fraction-index)))))

(defun h3-book-quotient-quotient-order-case
    (signs lib sides forms scalar divisor scalar-num quotient numerator numerator-num
         comparison fraction-index target)
  (h3-book-quotient-with-library lib
      ((equation (if (equal (h3-book-signs-signs-sign signs) 0)
                     (cons (h3-book-quotient-quotient-order-zero
                            lib signs divisor quotient numerator comparison fraction-index)
                           lib)
                   (h3-book-quotient-quotient-order-nonzero
                    lib signs sides forms scalar divisor scalar-num quotient numerator-num fraction-index))
                 :paired)
       (search (h3-rewrite-search-init lib (list *proof-not*) nil nil 150 nil))
       (right (proof-term-at target 2))
       (conditions (h3-book-signs-sign-conditions-with-library lib signs) :paired)
       (search (h3-rewrite-search-with-lib search lib))
       (evidence (h3-rewrite-search-context search conditions))
       (reduction (car (h3-rewrite-search-reduce search right evidence nil nil)))
       (reduction (or reduction '(:failure "unproved" "")))
       (from (h3-book-quotient-step-at equation 2))
       (to (h3-book-quotient-step-at reduction 2))
       (aligned (h3-book-arithmetic-associative-equal lib from to))
       (proof (library-library-proof lib))
       (reduction (proof-proof-symmetric proof reduction)))
    (proof-proof-chain proof equation (list aligned reduction))))

(defun h3-book-quotient-quotient-order-with-library (lib formula)
  (h3-book-quotient-with-library lib
      ((parts (h3-book-quotient-tail-of-size formula 2))
       (guard (car parts))
       (target (cadr parts))
       (comparison (proof-term-at target 1))
       (search (h3-rewrite-search-init lib nil nil nil 150 nil))
       (given (proof-proof-assume (library-library-proof lib) guard t))
       (context (h3-rewrite-search-context search (list given)))
       (sides (if (integerp comparison)
                  '(:failure "failure" "")
                (cdr comparison)))
       (fraction-index (h3-book-quotient-fraction-index sides 1))
       (quotient (nth (1- fraction-index) sides))
       (fraction (h3-book-quotient-reciprocal-factor quotient))
       (divisor (car fraction))
       (numerator (cadr fraction))
       (scalar (h3-book-quotient-rational-type lib divisor context))
       (scalar-num (h3-book-signs-number lib scalar))
       (forms (h3-book-quotient-rational-type-arguments lib sides context))
       (numerator-rational (h3-book-quotient-rational-type lib numerator context))
       (numerator-num (h3-book-signs-number lib numerator-rational))
       (result (h3-book-quotient-each-sign-with-library
                lib scalar-num h3-book-quotient-sign-callback h3-book-quotient-quotient-order-case
                sides forms scalar divisor scalar-num quotient numerator numerator-num
                comparison fraction-index target) :paired))
    (h3-rewrite-implication lib guard result)))

(defun h3-book-quotient-factor-order-factor (lib term base multiplier scalar)
  (if (and (equal term multiplier) (equal base *proof-one*))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((unit (library-library-axiom lib "UNICITY-OF-1" (list multiplier)))
             (numeric (h3-book-signs-number lib scalar))
             (fixed (h3-book-arithmetic-fix-value lib multiplier numeric))
             (identity (proof-proof-chain proof unit (list fixed))))
          (proof-proof-symmetric proof identity)))
    (h3-book-arithmetic-factor-out lib term base multiplier)))

(defun h3-book-quotient-factor-order-original (lib terms index yes multiplier scalar original)
  (if (endp terms)
      original
    (proof-with-checked-results
        ((base (proof-term-at yes index))
         (factored (h3-book-quotient-factor-order-factor lib (car terms) base multiplier scalar))
         (original (proof-proof-rewrite (library-library-proof lib) original factored (list 1 2 index))))
      (h3-book-quotient-factor-order-original lib (cdr terms) (1+ index) yes multiplier scalar original))))

(defun h3-book-quotient-factor-order-vanishes (lib bases index multiplier status vanishes)
  (if (endp bases)
      vanishes
    (proof-with-checked-results
        ((zero (h3-book-arithmetic-zero-product lib (car bases) multiplier multiplier status))
         (vanishes (proof-proof-rewrite (library-library-proof lib) vanishes zero (list 1 2 index))))
      (h3-book-quotient-factor-order-vanishes lib (cdr bases) (1+ index) multiplier status vanishes))))

(defun h3-book-quotient-factor-order-select (proof selected negative)
  (proof-with-checked-results ((right (h3-book-quotient-step-at selected 2)))
    (if (proof-is-call right *proof-if*)
        (proof-with-checked-results ((branch (proof-proof-select proof right negative)))
          (proof-proof-chain proof selected (list branch)))
      selected)))

(defun h3-book-quotient-factor-order-nonzero (lib signs conditional scalar original)
  (h3-book-quotient-with-library lib
      ((proof (library-library-proof lib))
       (selected (proof-proof-select proof conditional (h3-book-signs-signs-positive signs)))
       (selected (h3-book-quotient-factor-order-select proof selected (h3-book-signs-signs-negative signs)))
       (right (h3-book-quotient-step-at selected 2))
       (arguments (h3-book-quotient-tail-of-size right 2))
       (scaled (h3-book-quotient-scale-order-with-library
                lib (car arguments) (cadr arguments) scalar signs nil) :paired)
       (proof (library-library-proof lib))
       (scaled (proof-proof-symmetric proof scaled))
       (selected (proof-proof-symmetric proof selected)))
    (proof-proof-chain proof original (list scaled selected))))

(defun h3-book-quotient-factor-order-zero (lib signs search conditional original yes multiplier)
  (h3-book-quotient-with-library lib
      ((conditions (h3-book-signs-sign-conditions-with-library lib signs) :paired)
       (search (h3-rewrite-search-with-lib search lib))
       (condition (h3-rewrite-search-context search conditions))
       (selected (car (h3-rewrite-search-reduce search conditional condition nil nil)))
       (selected (or selected '(:failure "unproved" "")))
       (vanishes (h3-book-quotient-factor-order-vanishes
                  lib (cdr yes) 1 multiplier (h3-book-signs-signs-zero signs) original))
       (right (h3-book-quotient-step-at vanishes 2))
       (proof (library-library-proof lib))
       (empty (proof-proof-compute proof right *proof-nil*))
       (selected (proof-proof-symmetric proof selected)))
    (proof-proof-chain proof vanishes (list empty selected))))

(defun h3-book-quotient-factor-order-case
    (signs lib conditional goal nonzero scalar original search yes multiplier)
  (cond
   ((and (equal (h3-book-signs-signs-sign signs) 0) nonzero)
    (let ((proof (library-library-proof lib)))
      (h3-book-quotient-with-library lib
          ((contradiction (proof-proof-cut proof (h3-book-signs-signs-zero signs) nonzero)))
        (proof-proof-subsume proof contradiction (cons goal (proof-step-clause contradiction))))))
   ((not (equal (h3-book-signs-signs-sign signs) 0))
    (h3-book-quotient-factor-order-nonzero lib signs conditional scalar original))
   (t
    (h3-book-quotient-factor-order-zero lib signs search conditional original yes multiplier))))

(defun h3-book-quotient-factor-order-prove (lib guard goal compare conditional yes multiplier)
  (h3-book-quotient-with-library lib
      ((proof (library-library-proof lib))
       (search (h3-rewrite-search-init lib (list *proof-not*) nil nil 150 nil))
       (given (proof-proof-assume proof guard t))
       (evidence (h3-rewrite-search-context search (list given)))
       (scalar (table-get evidence (list *library-rationalp* multiplier) nil))
       (nonzero (h3-rewrite-search-known search (proof-neg (proof-eq multiplier *proof-zero*)) evidence))
       (result
        (if scalar
            (h3-book-quotient-with-library lib
                ((original (proof-proof-reflexive proof compare))
                 (original (h3-book-quotient-factor-order-original lib (cdr compare) 1 yes multiplier scalar original))
                 (numeric (h3-book-signs-number lib scalar))
                 (result (h3-book-quotient-each-sign-with-library
                          lib numeric h3-book-quotient-sign-callback h3-book-quotient-factor-order-case
                          conditional goal nonzero scalar original search yes multiplier) :paired))
              (h3-rewrite-implication lib guard result))
          (cons nil lib)) :paired))
    result))

(defun h3-book-quotient-factor-order-alternative (no negative multiplier)
  (or (equal no negative)
      (and (proof-is-call no *proof-if*)
           (proof-with-checked-results ((test (proof-term-at no 1)))
             (and (equal test (library-lt multiplier *proof-zero*))
                  (proof-with-checked-results ((branch (proof-term-at no 2)))
                    (equal branch negative)))))))

(defun h3-book-quotient-factor-order-conditional (lib guard goal)
  (h3-book-quotient-with-library lib
      ((parts (h3-book-quotient-tail-of-size goal 2))
       (compare (car parts))
       (conditional (cadr parts))
       (branches (h3-book-quotient-tail-of-size conditional 3))
       (test (car branches))
       (yes (cadr branches))
       (no (caddr branches))
       (left (and (proof-is-call test *proof-less*) (proof-term-at test 1)))
       (result
        (if (and (equal left *proof-zero*) (proof-is-call yes *proof-less*))
            (h3-book-quotient-with-library lib
                ((multiplier (proof-term-at test 2))
                 (negative (cons *proof-less* (reverse (cdr yes))))
                 (matches (h3-book-quotient-factor-order-alternative no negative multiplier))
                 (result (if matches
                             (h3-book-quotient-factor-order-prove lib guard goal compare conditional yes multiplier)
                           (cons nil lib)) :paired))
              result)
          (cons nil lib)) :paired))
    result))

(defun h3-book-quotient-factor-order-with-library (lib formula)
  (if (not (proof-is-call formula *library-implies*))
      (cons nil lib)
    (h3-book-quotient-with-library lib
        ((parts (h3-book-quotient-tail-of-size formula 2))
         (guard (car parts))
         (goal (cadr parts))
         (left (and (proof-is-call goal *proof-equal*) (proof-term-at goal 1)))
         (right (and (proof-is-call left *proof-less*) (proof-term-at goal 2)))
         (result (if (proof-is-call right *proof-if*)
                     (h3-book-quotient-factor-order-conditional lib guard goal)
                   (cons nil lib)) :paired))
      result)))

(defun h3-book-quotient-product-equals-factor-branch-forward (equality lib product reciprocal factor other law q)
  (let ((proof (library-library-proof lib))
        (term (list *proof-times* product reciprocal)))
    (proof-with-checked-results
        ((initial (proof-proof-reflexive proof term))
         (fixed (proof-proof-rewrite proof initial equality '(1 2 1)))
         (cancelled (h3-book-quotient-cancel-inverse-pair lib term factor other law))
         (fixed (proof-proof-rewrite proof fixed cancelled '(1 1)))
         (fixed (proof-proof-chain proof fixed (list law)))
         (test (list *library-numberp* other))
         (present (proof-proof-assume proof test t))
         (present-fix (h3-book-arithmetic-fix-value lib other present))
         (yes (proof-proof-rewrite proof fixed present-fix '(1 1)))
         (missing (proof-proof-assume proof test nil))
         (missing-fix (h3-book-arithmetic-fix-value lib other missing))
         (no (proof-proof-rewrite proof fixed missing-fix '(1 1)))
         (literal (proof-step-first no))
         (computed (proof-proof-compute proof literal *proof-nil*))
         (false-step (proof-proof-rewrite proof no computed '(1)))
         (impossible (proof-proof-tidy proof false-step))
         (no (proof-proof-subsume proof impossible (cons q (proof-step-clause impossible)))))
      (proof-proof-cases proof test yes no))))

(defun h3-book-quotient-product-equals-factor-branch-backward (equality lib product position factor numeric)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((initial (proof-proof-reflexive proof product))
         (equation (proof-proof-rewrite proof initial equality (list 1 2 position)))
         (right (h3-book-quotient-step-at equation 2))
         (arranged (h3-book-arithmetic-associative-equal lib right (list *proof-times* *proof-one* factor)))
         (unit (library-library-axiom lib "UNICITY-OF-1" (list factor)))
         (fixed (h3-book-arithmetic-fix-value lib factor numeric)))
      (proof-proof-chain proof equation (list arranged unit fixed)))))

(defun h3-book-quotient-product-equals-factor-zero (lib search formula p product factor numeric status)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((literal (proof-step-first status)))
      (if (proof-is-call literal *proof-equal*)
          (proof-with-checked-results
              ((parts (h3-book-quotient-tail-of-size product 2))
               (zero (h3-book-arithmetic-zero-product lib (car parts) (cadr parts) factor status)))
            (car (h3-rewrite-search-prove search formula (list numeric status zero))))
        (proof-with-checked-results
            ((typed (h3-book-arithmetic-typed-number lib product))
             (given (proof-proof-assume proof p t))
             (contradicted (proof-proof-rewrite proof typed given '(1 1)))
             (cut (proof-proof-cut proof contradicted status))
             (negative (proof-proof-front proof cut (proof-neg p)))
             (nil-step (h3-rewrite-nil-value lib negative)))
          (car (h3-rewrite-search-prove search formula (list numeric nil-step))))))))

(defun h3-book-quotient-product-equals-factor-branch
    (numeric status nonzero lib formula p q product factor position other reciprocal)
  (let ((search (h3-rewrite-search-init lib (list *proof-not*) nil nil 150 nil)))
    (if (not nonzero)
        (h3-book-quotient-product-equals-factor-zero lib search formula p product factor numeric status)
      (proof-with-checked-results
          ((law (h3-book-arithmetic-inverse lib factor numeric status))
           (comparison
            (h3-book-arithmetic-with-equivalent-equalities
             lib p q
             (h3-book-quotient-product-equals-factor-branch-forward lib product reciprocal factor other law q)
             (h3-book-quotient-product-equals-factor-branch-backward lib product position factor numeric))))
        (car (h3-rewrite-search-prove search formula (list numeric status comparison)))))))

(defun h3-book-quotient-product-equals-factor (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 3))
       (p (cadr formula))
       (right (caddr formula))
       (pair (h3-book-quotient-tail-of-size p 2))
       (product (car pair))
       (factor (cadr pair))
       (right-factor (proof-term-at product 2))
       (position (if (equal right-factor factor) 1 2))
       (other (proof-term-at product position))
       (inside (proof-term-at right 2))
       (q (proof-term-at inside 3))
       (reciprocal (list *h3-book-arithmetic-divide* factor)))
    (h3-book-arithmetic-with-scalar-cases
     lib factor
     (h3-book-quotient-product-equals-factor-branch
      lib formula p q product factor position other reciprocal))))

(defun h3-book-quotient-reciprocal-of-opposite-zero-source (lib opposite value status)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((literal (proof-step-first status)))
      (if (proof-is-call literal *proof-equal*)
          (proof-with-checked-results
              ((initial (proof-proof-reflexive proof opposite))
               (source (proof-proof-rewrite proof initial status '(1 2 1)))
               (right (h3-book-quotient-step-at source 2))
               (computed (proof-proof-compute proof right 0)))
            (proof-proof-chain proof source (list computed)))
        (proof-with-checked-results ((rule (library-library-axiom lib "DEFAULT-UNARY-MINUS" (list value))))
          (proof-proof-modus-ponens proof rule status))))))

(defun h3-book-quotient-reciprocal-of-opposite-zero (lib left right opposite value status)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((source (h3-book-quotient-reciprocal-of-opposite-zero-source lib opposite value status))
         (first (proof-proof-reflexive proof left))
         (first (proof-proof-rewrite proof first source '(1 2 1)))
         (second (proof-proof-reflexive proof right))
         (zero (h3-book-arithmetic-zero-test lib value status))
         (second (proof-proof-rewrite proof second zero '(1 2 1)))
         (first-right (h3-book-quotient-step-at first 2))
         (first-zero (proof-proof-compute proof first-right 0))
         (second-right (h3-book-quotient-step-at second 2))
         (second-zero (proof-proof-compute proof second-right 0))
         (second (proof-proof-chain proof second (list second-zero)))
         (second (proof-proof-symmetric proof second)))
      (proof-proof-chain proof first (list first-zero second)))))

(defun h3-book-quotient-reciprocal-of-opposite-nonzero (lib left right opposite value reciprocal numeric status)
  (h3-book-quotient-with-library lib
      ((added (h3-book-sums-lemmas-with-library lib) :paired)
       (proof (library-library-proof lib))
       (test (proof-eq opposite *proof-zero*))
       (double (proof-proof-reflexive proof (library-minus opposite)))
       (given (proof-proof-assume proof test t))
       (double (proof-proof-rewrite proof double given '(1 2 1)))
       (minus-zero (proof-proof-compute proof (library-minus *proof-zero*) 0))
       (double (proof-proof-chain proof double (list minus-zero)))
       (restored (library-library-cite lib *h3-book-sums-double* (list value) nil))
       (fixed (h3-book-arithmetic-fix-value lib value numeric))
       (restored (proof-proof-chain proof restored (list fixed)))
       (tested (proof-proof-rewrite proof double restored '(1 1)))
       (contradiction (proof-proof-cut proof tested status))
       (opposite-nonzero (proof-proof-front proof contradiction (proof-neg test)))
       (opposite-type (h3-book-arithmetic-typed-number lib opposite))
       (first-law (h3-book-arithmetic-inverse lib opposite opposite-type opposite-nonzero))
       (source (list *proof-times* value reciprocal))
       (negative (h3-book-signs-minus-product-with-library lib value right t) :paired)
       (inner-negative (h3-book-signs-minus-product-with-library lib value reciprocal nil) :paired)
       (proof (library-library-proof lib))
       (negative (proof-proof-rewrite proof negative inner-negative '(1 2 1)))
       (normal (library-library-cite lib *h3-book-sums-double* (list source) nil))
       (source-type (h3-book-arithmetic-typed-number lib source))
       (fixed (h3-book-arithmetic-fix-value lib source source-type))
       (normal (proof-proof-chain proof normal (list fixed)))
       (original-law (h3-book-arithmetic-inverse lib value numeric status))
       (second-law (proof-proof-chain proof negative (list normal original-law)))
       (forward (library-library-axiom lib "COMMUTATIVITY-OF-*" (list left opposite)))
       (forward (proof-proof-chain proof forward (list first-law)))
       (backward (library-library-axiom lib "COMMUTATIVITY-OF-*" (list right opposite)))
       (backward (proof-proof-chain proof backward (list second-law)))
       (backward (proof-proof-symmetric proof backward))
       (equality (proof-proof-chain proof forward (list backward)))
       (cancelled (h3-book-arithmetic-cancel-product lib left right opposite first-law equality))
       (left-type (h3-book-arithmetic-typed-number lib left))
       (left-fix (h3-book-arithmetic-fix-value lib left left-type))
       (cancelled (proof-proof-rewrite proof cancelled left-fix '(1 1)))
       (right-type (h3-book-arithmetic-typed-number lib right))
       (right-fix (h3-book-arithmetic-fix-value lib right right-type))
       (cancelled (proof-proof-rewrite proof cancelled right-fix '(1 2))))
    (proof-proof-tidy proof cancelled)))

(defun h3-book-quotient-reciprocal-of-opposite-case
    (numeric status nonzero lib left right opposite value reciprocal)
  (if nonzero
      (h3-book-quotient-reciprocal-of-opposite-nonzero lib left right opposite value reciprocal numeric status)
    (cons (h3-book-quotient-reciprocal-of-opposite-zero lib left right opposite value status) lib)))

(defun h3-book-quotient-reciprocal-of-opposite-with-library (lib formula)
  (h3-book-quotient-with-library lib
      ((formula (proof-list-of-length formula 3))
       (left (cadr formula))
       (right (caddr formula))
       (opposite (proof-term-at left 1))
       (value (proof-term-at opposite 1))
       (reciprocal (proof-term-at right 1))
       (proof (library-library-proof lib))
       (number-test (list *library-numberp* value))
       (zero-test (proof-eq value *proof-zero*))
       (known (proof-proof-assume proof number-test t))
       (equal-zero (proof-proof-assume proof zero-test t))
       (equal-case (h3-book-quotient-reciprocal-of-opposite-case
                    known equal-zero nil lib left right opposite value reciprocal) :paired)
       (different (proof-proof-assume proof zero-test nil))
       (different-case (h3-book-quotient-reciprocal-of-opposite-case
                        known different t lib left right opposite value reciprocal) :paired)
       (proof (library-library-proof lib))
       (nonnumeric (proof-proof-assume proof number-test nil))
       (numeric (proof-proof-cases proof zero-test equal-case different-case))
       (nonnumeric (h3-book-quotient-reciprocal-of-opposite-case
                    nonnumeric nonnumeric nil lib left right opposite value reciprocal) :paired))
    (proof-proof-cases proof number-test numeric nonnumeric)))

(defun h3-book-quotient-quotient-theorem-with-library (lib name formula)
  (cond
   ((member-equal name '("EQUAL-*-/-1" "EQUAL-*-/-2"))
    (cons (h3-book-quotient-quotient-equality lib formula) lib))
   ((text-starts-with name "NORMALIZE-<-/-TO-*-")
    (h3-book-quotient-quotient-order-with-library lib formula))
   ((member-equal name '("EQUAL-*-X-Y-X" "EQUAL-*-Y-X-X"))
    (cons (h3-book-quotient-product-equals-factor lib formula) lib))
   ((equal name "RECIPROCAL-MINUS-A")
    (h3-book-quotient-reciprocal-of-opposite-with-library lib formula))
   (t (cons nil lib))))

