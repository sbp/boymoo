(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *quotient-proofs-quotient* (proof-sym "NONNEGATIVE-INTEGER-QUOTIENT" "ACL2"))
(defconst *quotient-proofs-numerator* (proof-cl "NUMERATOR"))
(defconst *quotient-proofs-denominator* (proof-cl "DENOMINATOR"))
(defconst *quotient-proofs-floor* (proof-cl "FLOOR"))
(defconst *quotient-proofs-truncate* (proof-cl "TRUNCATE"))
(defconst *quotient-proofs-reciprocal* (proof-sym "UNARY-/" "ACL2"))

; A pair of binding names receives a value and the updated object.
(defmacro quotient-proofs-let* (bindings body)
  (if (endp bindings)
      body
    (let* ((binding (car bindings))
           (name (car binding))
           (expression (cadr binding))
           (rest (cdr bindings)))
      (if (consp name)
          `(let ((quotient-proofs-pair ,expression))
             (cond ((failure-p quotient-proofs-pair) quotient-proofs-pair)
                   ((failure-p (car quotient-proofs-pair))
                    (car quotient-proofs-pair))
                   (t (let ((,(car name) (car quotient-proofs-pair))
                            (,(cadr name) (cdr quotient-proofs-pair)))
                        (quotient-proofs-let* ,rest ,body)))))
        `(let ((,name ,expression))
           (if (failure-p ,name)
               ,name
             (quotient-proofs-let* ,rest ,body)))))))

(defmacro quotient-proofs-proof-call (operation lib &rest args)
  `(,operation (library-library-proof ,lib) ,@args))

(defun quotient-proofs-has-lemma (lib name)
  (assoc-equal (proof-sym (concatenate 'string "SELF-" name) "ACL2")
               (proof-proof-facts (library-library-proof lib))))

(defun quotient-proofs-base-library-p (lib)
  (eq (proof-proof-kind (library-library-proof lib)) :base))

(defun quotient-proofs-rational (lib term evidence)
  (if (quotient-proofs-base-library-p lib)
      (cons (library-library-rational lib term evidence) lib)
    (lemmas-slice-library-rational lib term evidence)))

(defun quotient-proofs-number (lib term evidence)
  (if (quotient-proofs-base-library-p lib)
      (cons (library-library-number lib term evidence) lib)
    (lemmas-slice-library-number lib term evidence)))

(defun quotient-proofs-one-product (lib value types)
  (if (quotient-proofs-base-library-p lib)
      (let ((fix (proof-sym "FIX" "ACL2")))
        (quotient-proofs-let*
         ((numeric (library-library-number lib value types))
          (identity (quotient-proofs-proof-call proof-proof-simplify lib (list fix value)
                                              (list numeric) (list fix)))
          (one (library-library-axiom lib "UNICITY-OF-1" (list value)))
          (result (quotient-proofs-proof-call proof-proof-chain lib one (list identity))))
         (cons result lib)))
    (product-arithmetic-one-product lib value types)))

(defun quotient-proofs-lemma-conditions (steps)
  (if (endp steps)
      nil
    (quotient-proofs-let*
     ((first (proof-step-first (car steps)))
      (rest (quotient-proofs-lemma-conditions (cdr steps))))
     (cons (proof-neg first) rest))))

(defun quotient-proofs-count-order (lib a b types nonnegative-a nonnegative-b less)
  (quotient-proofs-let*
   (((ia lib) (countdowns-type-of lib a types))
    ((ib lib) (countdowns-type-of lib b types))
    (finite (library-library-cite lib "FINITE-ORDER" (list a b) (list ia ib)))
    (ordinal (quotient-proofs-proof-call proof-proof-transport lib less finite))
    ((identity-a lib) (subtraction-count-identity lib a ia nonnegative-a))
    (reverse-a (quotient-proofs-proof-call proof-proof-symmetric lib identity-a))
    (ordinal (quotient-proofs-proof-call proof-proof-rewrite lib ordinal reverse-a '(1 1)))
    ((identity-b lib) (subtraction-count-identity lib b ib nonnegative-b))
    (reverse-b (quotient-proofs-proof-call proof-proof-symmetric lib identity-b))
    (ordinal (quotient-proofs-proof-call proof-proof-rewrite lib ordinal reverse-b '(1 2)))
    (order (quotient-proofs-proof-call proof-proof-tidy lib ordinal)))
   (cons order lib)))

(defun quotient-proofs-quotient-hypotheses (i j)
  (product-arithmetic-conjunction
   (list (list *library-natp* i) (library-integer j) (library-positive j))))

(defun quotient-proofs-quotient-properties (i j value)
  (product-arithmetic-conjunction
   (list (list *library-natp* value)
         (library-le (product-arithmetic-product j value) i)
         (library-lt i (product-arithmetic-product j (library-plus *proof-one* value))))))

(defun quotient-proofs-bound-parts (lib proof)
  (quotient-proofs-let*
   ((parts (quotient-proofs-proof-call proof-proof-conjunct lib proof))
    (bounds (quotient-proofs-proof-call proof-proof-conjunct lib (cadr parts))))
   (cons (car parts) bounds)))

(defun quotient-proofs-product-successor (lib divisor value types)
  (quotient-proofs-let*
   ((expanded (library-library-axiom lib "DISTRIBUTIVITY" (list divisor *proof-one* value)))
    (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list divisor *proof-one*)))
    ((unit lib) (quotient-proofs-one-product lib divisor types))
    (identity (quotient-proofs-proof-call proof-proof-chain lib commute (list unit)))
    (result (quotient-proofs-proof-call proof-proof-rewrite lib expanded identity '(1 2 1)))
    (result (quotient-proofs-proof-call proof-proof-tidy lib result)))
   (cons result lib)))

(defun quotient-proofs-quotient-lemma-branch (q tests lib induction iy pos-y bound-x types)
  (if (endp tests)
      '(:failure "failure" "")
    (let* ((signed-test (car (last tests)))
           (test (car signed-test))
           (holds (cadr signed-test)))
      (if (equal q *proof-zero*)
          (quotient-proofs-let*
           (((zero lib) (product-arithmetic-product-zero lib *library-y* iy))
            (reverse-zero (quotient-proofs-proof-call proof-proof-symmetric lib zero))
            (bound (quotient-proofs-proof-call proof-proof-rewrite lib bound-x reverse-zero
                                              '(1 1 2)))
            (bound (quotient-proofs-proof-call proof-proof-tidy lib bound))
            (sum (library-plus *proof-one* *proof-zero*))
            (unit (quotient-proofs-proof-call proof-proof-reflexive lib
                                             (product-arithmetic-product *library-y* sum)))
            (sum-value (quotient-proofs-proof-call proof-proof-compute lib sum 1))
            (unit (quotient-proofs-proof-call proof-proof-rewrite lib unit sum-value '(1 2 2)))
            (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list *library-y* *proof-one*)))
            ((one lib) (quotient-proofs-one-product lib *library-y* types))
            (unit (quotient-proofs-proof-call proof-proof-chain lib unit (list commute one)))
            (test-proof (quotient-proofs-proof-call proof-proof-assume lib test holds))
            (upper (library-library-transport-argument lib test-proof unit 2))
            ((natural lib) (lemmas-slice-library-natural lib *proof-zero*))
            (result (product-arithmetic-conjoin lib (list natural bound upper))))
           (cons (list result induction) lib))
        (quotient-proofs-let*
         ((smaller (library-diff *library-x* *library-y*))
          (not-below (quotient-proofs-proof-call proof-proof-assume lib test nil))
          (difference (library-library-axiom lib "<-ON-OTHERS" (list *library-x* *library-y*)))
          (lower (quotient-proofs-proof-call proof-proof-rewrite lib not-below difference '(1 1)))
          (lower (quotient-proofs-proof-call proof-proof-tidy lib lower))
          ((integral lib) (countdowns-type-of lib smaller types))
          (natural (library-library-cite lib "NATURAL-FROM-BOUNDS" (list smaller)
                                         (list integral lower)))
          (less (library-library-less-from-difference lib smaller *library-x* pos-y types))
          ((order lib) (quotient-proofs-count-order lib smaller *library-x* types lower bound-x less))
          ((ih induction) (book-logic-tree-induction-at induction smaller order nil))
          (inherited (quotient-proofs-proof-call proof-proof-prove lib
                                                (quotient-proofs-quotient-hypotheses smaller *library-y*)
                                                (list natural iy pos-y) nil))
          (bounds (quotient-proofs-proof-call proof-proof-modus-ponens lib ih inherited))
          (parts (quotient-proofs-bound-parts lib bounds))
          (partial (list *quotient-proofs-quotient* smaller *library-y*))
          ((one-natural lib) (lemmas-slice-library-natural lib *proof-one*))
          (q-natural (library-library-cite lib "NATURAL-SUM" (list *proof-one* partial)
                                           (list one-natural (car parts))))
          (partial-int (library-library-cite lib "NATURAL-INTEGER" (list partial)
                                             (list (car parts))))
          (proof-types (append types (list partial-int)))
          ((expanded lib) (quotient-proofs-product-successor lib *library-y* partial proof-types))
          (scaled-partial (product-arithmetic-product *library-y* partial))
          (difference (library-library-axiom lib "<-ON-OTHERS" (list smaller scaled-partial)))
          (delta (quotient-proofs-proof-call proof-proof-rewrite lib (cadr parts) difference '(1 1)))
          (delta (quotient-proofs-proof-call proof-proof-tidy lib delta))
          (larger (library-library-weak-from-difference lib (library-plus *library-y* scaled-partial)
                                                        *library-x* delta proof-types))
          (reverse-expanded (quotient-proofs-proof-call proof-proof-symmetric lib expanded))
          (bound (quotient-proofs-proof-call proof-proof-rewrite lib larger reverse-expanded '(1 1 2)))
          (bound (quotient-proofs-proof-call proof-proof-tidy lib bound))
          (scaled-q (product-arithmetic-product *library-y* q))
          (comparison (library-library-comparison lib smaller scaled-q proof-types))
          (positive-delta (quotient-proofs-proof-call proof-proof-rewrite lib (caddr parts)
                                                     comparison '(1)))
          (positive-delta (quotient-proofs-proof-call proof-proof-tidy lib positive-delta))
          (shifted (library-library-less-from-difference lib *library-x*
                                                         (library-plus *library-y* scaled-q)
                                                         positive-delta proof-types))
          ((successor lib) (quotient-proofs-product-successor lib *library-y* q proof-types))
          (upper (library-library-transport-argument lib shifted successor 2))
          (result (product-arithmetic-conjoin lib (list q-natural bound upper))))
         (cons (list result induction) lib))))))

(defun quotient-proofs-quotient-lemma-by-value (n lib value template tests induction
                                                 iy pos-y bound-x types)
  (cond
   ((zp n) '(:failure "fuel" "quotient-proofs-quotient-lemma-by-value"))
   ((proof-is-call value *proof-if*)
    (let ((test (cadr value)))
      (quotient-proofs-let*
       (((yes lib) (quotient-proofs-quotient-lemma-by-value
                    (1- n) lib (caddr value) template (append tests (list (list test t)))
                    induction iy pos-y bound-x types))
        ((no lib) (quotient-proofs-quotient-lemma-by-value
                   (1- n) lib (cadddr value) template (append tests (list (list test nil)))
                   (cadr yes) iy pos-y bound-x types))
        (yes-equation (quotient-proofs-proof-call proof-proof-if-true lib value))
        (yes-equation (quotient-proofs-proof-call proof-proof-symmetric lib yes-equation))
        (yes-proof (quotient-proofs-proof-call proof-proof-rewrite-result lib (car yes) yes-equation
                                              template *proof-result*))
        (no-equation (quotient-proofs-proof-call proof-proof-if-false lib value))
        (no-equation (quotient-proofs-proof-call proof-proof-symmetric lib no-equation))
        (no-proof (quotient-proofs-proof-call proof-proof-rewrite-result lib (car no) no-equation
                                             template *proof-result*))
        (result (quotient-proofs-proof-call proof-proof-cases lib test yes-proof no-proof)))
       (cons (list result (cadr no)) lib))))
   ((and (proof-compound value) (endp value))
    '(:failure "failure" ""))
   ((and (proof-compound value) (proof-compound (car value)))
    (quotient-proofs-let*
     ((equality (quotient-proofs-proof-call proof-proof-beta lib value))
      (equality-first (proof-step-first equality))
      ((opened lib) (quotient-proofs-quotient-lemma-by-value
                     (1- n) lib (caddr equality-first) template tests
                     induction iy pos-y bound-x types))
      (reverse (quotient-proofs-proof-call proof-proof-symmetric lib equality))
      (result (quotient-proofs-proof-call proof-proof-rewrite-result lib (car opened) reverse
                                          template *proof-result*)))
     (cons (list result (cadr opened)) lib)))
   (t
    (quotient-proofs-let*
     (((branch lib) (quotient-proofs-quotient-lemma-branch
                     value tests lib induction iy pos-y bound-x types))
      (first (proof-step-first (car branch)))
      (expected (proof-subst template (list (cons *proof-result* value)))))
     (if (equal first expected)
         (cons branch lib)
       '(:failure "failure" ""))))))

(defun quotient-proofs-quotient-lemma (lib)
  (let ((name "QUOTIENT-BOUNDS"))
    (if (quotient-proofs-has-lemma lib name)
        lib
      (quotient-proofs-let*
       ((value (list *quotient-proofs-quotient* *library-x* *library-y*))
        (hypothesis (quotient-proofs-proof-call proof-proof-assume lib
                                               (quotient-proofs-quotient-hypotheses
                                                *library-x* *library-y*) t))
        (hypothesis-first (proof-step-first hypothesis))
        (formula (list *library-implies* hypothesis-first
                       (quotient-proofs-quotient-properties *library-x* *library-y* value)))
        (induction (book-logic-tree-induction-init lib formula *library-x*))
        (hypothesis-parts (quotient-proofs-proof-call proof-proof-conjunct lib hypothesis))
        (natural-x (car hypothesis-parts))
        (divisor (quotient-proofs-proof-call proof-proof-conjunct lib (cadr hypothesis-parts)))
        (iy (car divisor))
        (pos-y (cadr divisor))
        (ix (library-library-cite lib "NATURAL-INTEGER" (list *library-x*) (list natural-x)))
        (bound-x (library-library-cite lib "NATURAL-NONNEGATIVE" (list *library-x*) (list natural-x)))
        (types (list ix iy))
        (i-zero (library-library-type-of lib *proof-zero* nil))
        (bound-y (library-library-cite lib "LESS-TO-WEAK" (list *proof-zero* *library-y*)
                                      (list i-zero iy pos-y)))
        (opened (quotient-proofs-proof-call proof-proof-unfold lib value))
        (opened-first (proof-step-first opened))
        (guard (cadr (caddr opened-first)))
        (nonzero (product-arithmetic-positive-nonzero lib *library-y* pos-y))
        (reduced (quotient-proofs-proof-call proof-proof-simplify lib guard
                                            (append types (list bound-y nonzero))
                                            (list *subtraction-nfix* *subtraction-ifix*
                                                  *subtraction-numeric-equal*)))
        (equation (quotient-proofs-proof-call proof-proof-rewrite lib opened reduced '(1 2 1)))
        (equation (quotient-proofs-proof-call proof-proof-tidy lib equation))
        (template (quotient-proofs-quotient-properties *library-x* *library-y* *proof-result*))
        (equation-first (proof-step-first equation))
        ((selected lib) (quotient-proofs-quotient-lemma-by-value
                         1000000 lib (caddr equation-first) template nil
                         induction iy pos-y bound-x types))
        (reverse (quotient-proofs-proof-call proof-proof-symmetric lib equation))
        (result (quotient-proofs-proof-call proof-proof-rewrite-result lib (car selected) reverse
                                            template *proof-result*))
        (proof (witnesses-prove-implication lib formula hypothesis result))
        (finished (book-logic-tree-induction-finish (cadr selected) proof)))
       (library-library-lemma lib name formula finished nil)))))

(defun quotient-proofs-quotient-bounds (lib i j natural-i integer-j positive-j)
  (quotient-proofs-let*
   ((lib (quotient-proofs-quotient-lemma lib))
    (theorem (library-library-cite lib "QUOTIENT-BOUNDS" (list i j) nil))
    (premise (quotient-proofs-proof-call proof-proof-prove lib
                                        (quotient-proofs-quotient-hypotheses i j)
                                        (list natural-i integer-j positive-j) nil))
    (proof (quotient-proofs-proof-call proof-proof-modus-ponens lib theorem premise))
    (parts (quotient-proofs-bound-parts lib proof)))
   (cons parts lib)))

(defun quotient-proofs-reciprocal-cancel (lib value types positive-value)
  (quotient-proofs-let*
   ((law (library-library-axiom lib "INVERSE-OF-*" (list value)))
    (law-first (proof-step-first law))
    ((numeric lib) (quotient-proofs-number lib value types))
    (nonzero (product-arithmetic-positive-nonzero lib value positive-value))
    (premise (quotient-proofs-proof-call proof-proof-prove lib (cadr law-first)
                                        (list numeric nonzero) nil))
    (result (quotient-proofs-proof-call proof-proof-modus-ponens lib law premise)))
   (cons result lib)))

(defun quotient-proofs-quotient-ratio-rewrite (lib base result pos radix scale decomposed types)
  (quotient-proofs-let*
   (((cancel lib) (quotient-proofs-reciprocal-cancel lib base types pos))
    (prefix (quotient-proofs-proof-call proof-proof-reflexive lib scale))
    (prefix (if (equal base radix)
                prefix
              (quotient-proofs-let*
               ((reverse (quotient-proofs-proof-call proof-proof-symmetric lib decomposed)))
               (quotient-proofs-proof-call proof-proof-rewrite lib prefix reverse '(1 2 2)))))
    (arranged (product-arithmetic-product
               (product-arithmetic-product base (list *quotient-proofs-reciprocal* base)) result))
    (prefix-first (proof-step-first prefix))
    (reordering (product-arithmetic-product-equal lib (caddr prefix-first) arranged))
    (proof (quotient-proofs-proof-call proof-proof-chain lib prefix (list reordering)))
    (proof (quotient-proofs-proof-call proof-proof-rewrite lib proof cancel '(1 2 1)))
    (proof (quotient-proofs-proof-call proof-proof-tidy lib proof))
    ((unit lib) (quotient-proofs-one-product lib result types))
    (proof (quotient-proofs-proof-call proof-proof-chain lib proof (list unit))))
   (cons proof lib)))

(defun quotient-proofs-quotient-ratio (lib n radix types positive-radix)
  (quotient-proofs-let*
   ((inverse (list *quotient-proofs-reciprocal* radix))
    (fraction (product-arithmetic-product n inverse))
    ((r-radix lib) (quotient-proofs-rational lib radix types))
    (closure (quotient-proofs-proof-call proof-proof-fact lib "rationalp-unary-/"
                                        (list (list *library-x* radix))))
    (r-inverse (quotient-proofs-proof-call proof-proof-modus-ponens lib closure r-radix))
    (closure (quotient-proofs-proof-call proof-proof-fact lib "rationalp-binary-*"
                                        (list (list *library-x* n) (list *library-y* inverse))))
    (closure-first (proof-step-first closure))
    ((r-n lib) (quotient-proofs-rational lib n types))
    (arguments (quotient-proofs-proof-call proof-proof-prove lib (cadr closure-first)
                                          (list r-n r-inverse) nil))
    (rational (quotient-proofs-proof-call proof-proof-modus-ponens lib closure arguments))
    (n-top (list *quotient-proofs-numerator* fraction))
    (n-bottom (list *quotient-proofs-denominator* fraction))
    (basic (library-library-axiom lib "RATIONAL-IMPLIES1" (list fraction)))
    (basic (quotient-proofs-proof-call proof-proof-modus-ponens lib basic rational))
    (basic (quotient-proofs-proof-call proof-proof-conjunct lib basic))
    (int-bottom (car basic))
    (constraints (quotient-proofs-proof-call proof-proof-conjunct lib (cadr basic)))
    (int-top (car constraints))
    (positive-bottom (cadr constraints))
    (types (append types (list int-top int-bottom)))
    (decomposed (library-library-axiom lib "RATIONAL-IMPLIES2" (list fraction)))
    (decomposed (quotient-proofs-proof-call proof-proof-modus-ponens lib decomposed rational))
    (scale (product-arithmetic-product (product-arithmetic-product radix n-bottom) fraction))
    ((first-rewrite lib) (quotient-proofs-quotient-ratio-rewrite
                          lib radix (product-arithmetic-product n-bottom n) positive-radix
                          radix scale decomposed types))
    ((second-rewrite lib) (quotient-proofs-quotient-ratio-rewrite
                           lib n-bottom (product-arithmetic-product radix n-top) positive-bottom
                           radix scale decomposed types))
    (reverse (quotient-proofs-proof-call proof-proof-symmetric lib second-rewrite))
    (equation (quotient-proofs-proof-call proof-proof-chain lib reverse (list first-rewrite))))
   (cons (list n-top n-bottom int-top int-bottom positive-bottom equation) lib)))

(defun quotient-proofs-radix-assumptions (lib)
  (quotient-proofs-let*
   ((ints (library-library-ints lib (list *library-x* *library-y*)))
    (px (quotient-proofs-proof-call proof-proof-assume lib (library-positive *library-x*) t))
    (radix (quotient-proofs-proof-call proof-proof-assume lib
                                       (library-lt *proof-one* *library-y*) t))
    (i-zero (library-library-type-of lib *proof-zero* nil))
    (i-one (library-library-type-of lib *proof-one* nil))
    (unit (quotient-proofs-proof-call proof-proof-prove lib (library-lt *proof-zero* *proof-one*)
                                     nil nil))
    (py (library-library-cite lib "LESS-TRANSITIVE" (list *proof-zero* *proof-one* *library-y*)
                               (list i-zero i-one (cadr ints) unit radix))))
   (list (append ints (list px radix)) py)))

(defun quotient-proofs-radix-name (function suffix)
  (cond ((atom (cddr function)) '(:failure "failure" ""))
        ((stringp (caddr function))
         (concatenate 'string "RADIX-" (caddr function) suffix))
        ((integerp (caddr function)) '(:failure "failure" ""))
        (t '(:failure "failure" ""))))

(defun quotient-proofs-radix-product-lemma-branch-unit-product (value lib bottom guard types)
  (quotient-proofs-let*
   ((expression (product-arithmetic-product bottom value))
    (reflexive (quotient-proofs-proof-call proof-proof-reflexive lib expression))
    (reduced (quotient-proofs-proof-call proof-proof-rewrite lib reflexive guard '(1 2 1)))
    ((one lib) (quotient-proofs-one-product lib value types))
    (result (quotient-proofs-proof-call proof-proof-chain lib reduced (list one))))
   (cons result lib)))

(defun quotient-proofs-radix-product-lemma-unit-bounds (lib bottom top i-top natural-top guard types)
  (quotient-proofs-let*
   ((weak (library-library-cite lib "WEAK-REFLEXIVE" (list top) (list i-top)))
    ((product-top lib) (quotient-proofs-radix-product-lemma-branch-unit-product
                         top lib bottom guard types))
    (reverse (quotient-proofs-proof-call proof-proof-symmetric lib product-top))
    (weak (quotient-proofs-proof-call proof-proof-rewrite lib weak reverse '(1 1 2)))
    (weak (quotient-proofs-proof-call proof-proof-tidy lib weak))
    (successor (library-library-cite lib "SUCCESSOR-LARGER" (list top) (list i-top)))
    (successor-first (proof-step-first successor))
    (sum (library-plus *proof-one* top))
    (aligned (library-library-linear-equal lib (caddr successor-first) sum types))
    (successor (quotient-proofs-proof-call proof-proof-rewrite lib successor aligned '(1 2)))
    (successor (quotient-proofs-proof-call proof-proof-tidy lib successor))
    ((product-sum lib) (quotient-proofs-radix-product-lemma-branch-unit-product
                         sum lib bottom guard types))
    (strict (library-library-transport-argument lib successor product-sum 2)))
   (cons (list natural-top weak strict) lib)))

(defun quotient-proofs-radix-product-lemma-branch (unit lib function test template
                                                       top bottom i-top i-bottom p-bottom cross
                                                       py types natural-top bound-top)
  (quotient-proofs-let*
   ((guard (quotient-proofs-proof-call proof-proof-assume lib test unit))
    (call (list function *library-x* *library-y*))
    (equation (quotient-proofs-proof-call proof-proof-simplify lib call (list guard bound-top)
                                         (list function *subtraction-numeric-equal*)))
    (equation-first (proof-step-first equation))
    (q (caddr equation-first))
    ((bounds lib)
     (if unit
         (quotient-proofs-radix-product-lemma-unit-bounds lib bottom top i-top natural-top guard types)
       (quotient-proofs-quotient-bounds lib top bottom natural-top i-bottom p-bottom)))
    (iq (library-library-cite lib "NATURAL-INTEGER" (list q) (list (car bounds))))
    (integers (append types (list iq)))
    (scaled-q (product-arithmetic-product *library-y* q))
    (too-small (quotient-proofs-proof-call proof-proof-assume lib (library-lt *library-x* scaled-q) t))
    ((multiplied lib) (product-arithmetic-product-order
                       lib *library-x* scaled-q bottom integers too-small p-bottom))
    (reverse-cross (quotient-proofs-proof-call proof-proof-symmetric lib cross))
    (multiplied (quotient-proofs-proof-call proof-proof-rewrite lib multiplied reverse-cross '(1 1)))
    (multiplied-first (proof-step-first multiplied))
    (arranged (product-arithmetic-product-equal
               lib (caddr multiplied-first)
               (product-arithmetic-product *library-y* (product-arithmetic-product bottom q))))
    (multiplied (quotient-proofs-proof-call proof-proof-rewrite lib multiplied arranged '(1 2)))
    (multiplied (quotient-proofs-proof-call proof-proof-tidy lib multiplied))
    ((contradicted lib) (product-arithmetic-reflect-product-order
                         lib top (product-arithmetic-product bottom q) *library-y*
                         integers multiplied py))
    (lower (quotient-proofs-proof-call proof-proof-cut lib contradicted (cadr bounds)))
    (too-small-first (proof-step-first too-small))
    (lower (quotient-proofs-proof-call proof-proof-front lib lower (proof-neg too-small-first)))
    (successor (library-plus *proof-one* q))
    ((multiplied lib) (product-arithmetic-product-order
                       lib top (product-arithmetic-product bottom successor) *library-y*
                       integers (caddr bounds) py))
    (multiplied (quotient-proofs-proof-call proof-proof-rewrite lib multiplied cross '(1 1)))
    (multiplied-first (proof-step-first multiplied))
    (scaled-successor (product-arithmetic-product *library-y* successor))
    (arranged (product-arithmetic-product-equal
               lib (caddr multiplied-first) (product-arithmetic-product bottom scaled-successor)))
    (multiplied (quotient-proofs-proof-call proof-proof-rewrite lib multiplied arranged '(1 2)))
    (multiplied (quotient-proofs-proof-call proof-proof-tidy lib multiplied))
    ((upper lib) (product-arithmetic-reflect-product-order
                  lib *library-x* scaled-successor bottom integers multiplied p-bottom))
    (proof (product-arithmetic-conjoin lib (list (car bounds) lower upper)))
    (reverse-equation (quotient-proofs-proof-call proof-proof-symmetric lib equation))
    (proof (quotient-proofs-proof-call proof-proof-rewrite-result lib proof reverse-equation
                                       template *proof-result*)))
   (cons proof lib)))

(defun quotient-proofs-radix-product-lemma (lib function)
  (quotient-proofs-let*
   ((name (quotient-proofs-radix-name function "-PRODUCT-BOUNDS")))
   (if (quotient-proofs-has-lemma lib name)
       (cons name lib)
     (quotient-proofs-let*
      ((radix (quotient-proofs-radix-assumptions lib))
       (assumptions (car radix))
       (py (cadr radix))
       (px (caddr assumptions))
       (inputs (list (car assumptions) (cadr assumptions)))
       ((ratio lib) (quotient-proofs-quotient-ratio lib *library-x* *library-y* inputs py))
       (top (car ratio))
       (bottom (cadr ratio))
       (i-top (caddr ratio))
       (i-bottom (cadddr ratio))
       (p-bottom (nth 4 ratio))
       (cross (nth 5 ratio))
       (types (append inputs (list i-top i-bottom)))
       ((pos-product lib) (product-arithmetic-positive-product lib bottom *library-x* types p-bottom px))
       (reverse-cross (quotient-proofs-proof-call proof-proof-symmetric lib cross))
       (product-top (quotient-proofs-proof-call proof-proof-rewrite lib pos-product reverse-cross '(1 2)))
       (product-top (quotient-proofs-proof-call proof-proof-tidy lib product-top))
       ((p-top lib) (product-arithmetic-reflect-positive-product lib top *library-y* types product-top py))
       (i-zero (library-library-type-of lib *proof-zero* nil))
       (bound-top (library-library-cite lib "LESS-TO-WEAK" (list *proof-zero* top)
                                        (list i-zero i-top p-top)))
       (natural-top (library-library-cite lib "NATURAL-FROM-BOUNDS" (list top)
                                          (list i-top bound-top)))
       (test (proof-eq bottom *proof-one*))
       (template (quotient-proofs-quotient-properties *library-x* *library-y* *proof-result*))
       ((yes lib) (quotient-proofs-radix-product-lemma-branch
                   t lib function test template top bottom i-top i-bottom p-bottom cross
                   py types natural-top bound-top))
       ((no lib) (quotient-proofs-radix-product-lemma-branch
                  nil lib function test template top bottom i-top i-bottom p-bottom cross
                  py types natural-top bound-top))
       (proof (quotient-proofs-proof-call proof-proof-cases lib test yes no))
       (first (proof-step-first proof))
       (conditions (quotient-proofs-lemma-conditions assumptions))
       (lib (library-library-lemma lib name first proof conditions)))
      (cons name lib)))))

(defun quotient-proofs-radix-less-lemma (lib function)
  (quotient-proofs-let*
   ((name (quotient-proofs-radix-name function "-LESS")))
   (if (quotient-proofs-has-lemma lib name)
       (cons name lib)
     (quotient-proofs-let*
      ((radix-assumptions (quotient-proofs-radix-assumptions lib))
       (assumptions (car radix-assumptions))
       (py (cadr radix-assumptions))
       (ix (car assumptions))
       (iy (cadr assumptions))
       (px (caddr assumptions))
       (radix (cadddr assumptions))
       ((bounds-name lib) (quotient-proofs-radix-product-lemma lib function))
       (bounds (library-library-cite lib bounds-name (list *library-x* *library-y*) assumptions))
       (parts (quotient-proofs-bound-parts lib bounds))
       (q (list function *library-x* *library-y*))
       (iq (library-library-cite lib "NATURAL-INTEGER" (list q) (list (car parts))))
       (types (list ix iy iq))
       ((between lib) (product-arithmetic-product-order lib *proof-one* *library-y*
                                                         *library-x* types radix px))
       (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list *library-x* *proof-one*)))
       ((unit lib) (quotient-proofs-one-product lib *library-x* types))
       (one (quotient-proofs-proof-call proof-proof-chain lib commute (list unit)))
       (between (quotient-proofs-proof-call proof-proof-rewrite lib between one '(1 1)))
       (between (quotient-proofs-proof-call proof-proof-tidy lib between))
       (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list *library-x* *library-y*)))
       (between (quotient-proofs-proof-call proof-proof-rewrite lib between commute '(1 2)))
       (between (quotient-proofs-proof-call proof-proof-tidy lib between))
       (left (product-arithmetic-product *library-y* q))
       (right (product-arithmetic-product *library-y* *library-x*))
       ((i-left lib) (countdowns-type-of lib left types))
       ((i-right lib) (countdowns-type-of lib right types))
       (scaled (library-library-cite lib "WEAK-THEN-LESS" (list left *library-x* right)
                                      (list i-left ix i-right (cadr parts) between)))
       ((less lib) (product-arithmetic-reflect-product-order
                    lib q *library-x* *library-y* types scaled py))
       (first (proof-step-first less))
       (conditions (quotient-proofs-lemma-conditions assumptions))
       (lib (library-library-lemma lib name first less conditions)))
      (cons name lib)))))

(defun quotient-proofs-radix-lemma (lib function)
  (quotient-proofs-let*
   ((name (quotient-proofs-radix-name function "-DECREASE")))
   (if (quotient-proofs-has-lemma lib name)
       (cons name lib)
     (quotient-proofs-let*
      ((radix-assumptions (quotient-proofs-radix-assumptions lib))
       (assumptions (car radix-assumptions))
       (ix (car assumptions))
       (iy (cadr assumptions))
       (px (caddr assumptions))
       (q (list function *library-x* *library-y*))
       ((bounds-name lib) (quotient-proofs-radix-product-lemma lib function))
       (bounds (library-library-cite lib bounds-name (list *library-x* *library-y*) assumptions))
       (parts (quotient-proofs-bound-parts lib bounds))
       (natural (car parts))
       (iq (library-library-cite lib "NATURAL-INTEGER" (list q) (list natural)))
       ((less-name lib) (quotient-proofs-radix-less-lemma lib function))
       (less (library-library-cite lib less-name (list *library-x* *library-y*) assumptions))
       (bq (library-library-cite lib "NATURAL-NONNEGATIVE" (list q) (list natural)))
       (i-zero (library-library-type-of lib *proof-zero* nil))
       (bx (library-library-cite lib "LESS-TO-WEAK" (list *proof-zero* *library-x*)
                                  (list i-zero ix px)))
       ((proof lib) (quotient-proofs-count-order lib q *library-x* (list ix iy iq) bq bx less))
       (first (proof-step-first proof))
       (conditions (quotient-proofs-lemma-conditions assumptions))
       (lib (library-library-lemma lib name first proof conditions)))
      (cons name lib)))))

(defun quotient-proofs-counter-definitions (lib wrappers)
  (if (endp wrappers)
      nil
    (let ((rest (quotient-proofs-counter-definitions lib (cdr wrappers))))
      (if (assoc-equal (car wrappers)
                       (proof-proof-definitions (library-library-proof lib)))
          (cons (car wrappers) rest)
        rest))))

(defun quotient-proofs-dividend-rulers-lower (lib value base integral lower
                                               lower-first wrapped-bound pos-base)
  (quotient-proofs-let*
   (((adjusted lib)
     (if (equal lower-first wrapped-bound)
         (let ((natural-value (list *library-natp* value))
               (clip (list *library-nfix* value)))
           (quotient-proofs-let*
            ((not-natural (quotient-proofs-proof-call proof-proof-assume lib natural-value nil))
             ((equation lib) (lemmas-nfix-equation lib value))
             (clipped (quotient-proofs-proof-call proof-proof-simplify lib clip (list not-natural)
                                                 (list *library-nfix*)))
             (clipped (quotient-proofs-proof-call proof-proof-chain lib equation (list clipped)))
             (bad (quotient-proofs-proof-call proof-proof-rewrite lib lower clipped '(1 1 1)))
             (bad (quotient-proofs-proof-call proof-proof-tidy lib bad))
             (natural (quotient-proofs-proof-call proof-proof-cut lib pos-base bad))
             (natural (quotient-proofs-proof-call proof-proof-front lib natural natural-value))
             (integral (library-library-cite lib "NATURAL-INTEGER" (list value) (list natural)))
             (same (quotient-proofs-proof-call proof-proof-simplify lib clip (list natural)
                                              (list *library-nfix*)))
             (same (quotient-proofs-proof-call proof-proof-chain lib equation (list same)))
             (lower (quotient-proofs-proof-call proof-proof-rewrite lib lower same '(1 1 1)))
             (lower (quotient-proofs-proof-call proof-proof-tidy lib lower)))
            (cons (list integral lower) lib)))
       (cons (list integral lower) lib)))
    (integral (car adjusted)))
   (if integral
       (quotient-proofs-let*
        ((i-zero (library-library-type-of lib *proof-zero* nil))
         ((i-base lib) (countdowns-type-of lib base nil))
         (strict (library-library-cite lib "LESS-THEN-WEAK" (list *proof-zero* base value)
                                       (list i-zero i-base integral pos-base (cadr adjusted)))))
        (cons (list integral strict) lib))
     (cons nil lib))))

(defun quotient-proofs-dividend-rulers-derived (lib value base integral plain-bound
                                                  wrapped-bound definitions derived)
  (declare (xargs :measure (acl2-count derived)))
  (if (endp derived)
      (cons nil lib)
    (quotient-proofs-let*
     ((premise (cdar derived))
      (first (proof-step-first premise)))
     (if (and (proof-is-call first *proof-not*)
              (proof-is-call (cadr first) *proof-less*))
         (quotient-proofs-let*
          ((lower (if (or (equal first plain-bound) (equal first wrapped-bound))
                      premise
                    (quotient-proofs-proof-call proof-proof-simplify-first lib premise nil
                                               definitions)))
           (lower-first (proof-step-first lower)))
          (if (or (equal lower-first plain-bound) (equal lower-first wrapped-bound))
              (quotient-proofs-let*
               ((pos-base (quotient-proofs-proof-call proof-proof-prove lib
                                                     (library-positive base) nil nil))
                ((proved lib) (quotient-proofs-dividend-rulers-lower
                               lib value base integral lower lower-first wrapped-bound pos-base)))
               (if proved
                   (cons proved lib)
                 (quotient-proofs-dividend-rulers-derived
                  lib value base integral plain-bound wrapped-bound definitions (cdr derived))))
            (quotient-proofs-dividend-rulers-derived
             lib value base integral plain-bound wrapped-bound definitions (cdr derived))))
       (quotient-proofs-dividend-rulers-derived
        lib value base integral plain-bound wrapped-bound definitions (cdr derived))))))

(defun quotient-proofs-dividend-rulers-with-rulers (lib value base rulers)
  (quotient-proofs-let*
   (((integral rulers) (rulers-rulers-find rulers (library-integer value)))
    ((pos rulers) (rulers-rulers-find rulers (library-positive value))))
   (if (and integral pos)
       (cons (cons (list integral pos) rulers) lib)
     (quotient-proofs-let*
      ((wrapped (list *subtraction-nfix* value))
       (definitions (quotient-proofs-counter-definitions lib *countdowns-counter-wrappers*))
       (derived (rulers-rulers-derived rulers))
       ((proved lib) (quotient-proofs-dividend-rulers-derived
                      lib value base integral (proof-neg (library-lt value base))
                      (proof-neg (library-lt wrapped base)) definitions derived)))
      (cons (cons proved rulers) lib)))))

(defun quotient-proofs-quotient-call (lib term value)
  (cond
   ((not (proof-compound term)) nil)
   ((endp term) '(:failure "failure" ""))
   ((or (proof-compound (car term))
        (member-equal (car term)
                      (list* *quotient-proofs-floor* *quotient-proofs-truncate*
                             *countdowns-counter-wrappers*)))
    (quotient-proofs-let*
     ((definitions (quotient-proofs-counter-definitions lib *countdowns-counter-wrappers*))
      (opening (quotient-proofs-proof-call proof-proof-simplify lib term nil definitions))
      (actual (if opening
                  (quotient-proofs-let* ((first (proof-step-first opening))) (caddr first))
                term)))
     (cond
      ((not (or (proof-is-call actual *quotient-proofs-floor*)
                (proof-is-call actual *quotient-proofs-truncate*)))
       nil)
      ((endp (cdr actual)) '(:failure "failure" ""))
      ((not (equal (cadr actual) value)) nil)
      ((endp (cddr actual)) '(:failure "failure" ""))
      ((not (proof-is-call (caddr actual) *proof-quote*)) nil)
      ((endp (cdaddr actual)) '(:failure "failure" ""))
      ((and (integerp (cadr (caddr actual))) (<= 2 (cadr (caddr actual))))
       (list actual opening))
      (t nil))))
   (t nil)))

(defun quotient-proofs-quotient-decrease-from-call (lib projected rulers)
  (quotient-proofs-let*
   ((actual (proof-list-of-length (car projected) 3))
    (opening (cadr projected))
    (function (car actual))
    (value (cadr actual))
    (base (caddr actual))
    ((derived lib) (quotient-proofs-dividend-rulers-with-rulers lib value base rulers))
    (hypotheses (car derived))
    (rulers (cdr derived)))
   (if (not hypotheses)
       (cons (list nil rulers) lib)
     (quotient-proofs-let*
      (((lemma lib) (quotient-proofs-radix-lemma lib function))
       (i-base (library-library-type-of lib base nil))
       (radix (quotient-proofs-proof-call proof-proof-prove lib
                                         (library-lt *proof-one* base) nil nil))
       (proof (library-library-cite lib lemma (list value base)
                                    (list (car hypotheses) i-base (cadr hypotheses) radix)))
       (proof (if opening
                  (quotient-proofs-let*
                   ((reverse (quotient-proofs-proof-call proof-proof-symmetric lib opening))
                    (proof (quotient-proofs-proof-call proof-proof-rewrite lib proof reverse '(1 1 1))))
                   (quotient-proofs-proof-call proof-proof-tidy lib proof))
                proof))
       (first (proof-step-first proof))
       (head (proof-term-at first 0)))
      (if (equal head *proof-ordinal-less*)
          (cons (list proof rulers) lib)
        '(:failure "failure" ""))))))

(defun quotient-proofs-quotient-decrease-with-rulers (lib goal rulers)
  (quotient-proofs-let*
   ((goal (proof-list-of-length goal 3)))
   (let ((child (cadr goal))
         (parent (caddr goal)))
     (if (and (proof-is-call child *library-count*)
              (proof-is-call parent *library-count*))
         (quotient-proofs-let*
          ((term (proof-term-at child 1))
           (value (proof-term-at parent 1))
           (projected (quotient-proofs-quotient-call lib term value)))
          (if projected
              (quotient-proofs-quotient-decrease-from-call lib projected rulers)
            (cons (list nil rulers) lib)))
       (cons (list nil rulers) lib)))))

(defun quotient-proofs-quotient-decrease (lib goal rulers)
  (quotient-proofs-let*
   (((result lib) (quotient-proofs-quotient-decrease-with-rulers lib goal rulers)))
   (cons (car result) lib)))

(defun quotient-proofs-radix-calls-binding (pairs bindings)
  (if (endp pairs)
      bindings
    (quotient-proofs-radix-calls-binding
     (cdr pairs) (table-put bindings (caar pairs) (cadar pairs)))))

(defun quotient-proofs-radix-calls-changes (actuals recursive-actuals binding)
  (declare (xargs :measure (acl2-count actuals)))
  (if (or (endp actuals) (endp recursive-actuals))
      nil
    (let ((old (car actuals))
          (new (car recursive-actuals)))
      (if (proof-compound old)
          (quotient-proofs-radix-calls-changes (cdr actuals) (cdr recursive-actuals) binding)
        (quotient-proofs-let*
         ((substituted (proof-subst new binding))
          (change (if (equal old substituted)
                      nil
                    (quotient-proofs-let*
                     ((new (proof-subst new binding)))
                     (list old new))))
          (rest (quotient-proofs-radix-calls-changes (cdr actuals) (cdr recursive-actuals)
                                                    binding)))
         (if change (cons change rest) rest))))))

; The cursor retains the formula agenda, the invocations of the current
; formula call, and the argument changes of the current invocation.
(defun quotient-proofs-radix-calls-start (formula)
  (list (list formula) nil nil nil nil nil nil nil))

(defun quotient-proofs-radix-calls-next-aux (n lib cursor)
  (if (zp n)
      '(:failure "fuel" "quotient-proofs-radix-calls-next-aux")
    (let ((agenda (car cursor))
          (invocations (cadr cursor))
          (actuals (caddr cursor))
          (binding (cadddr cursor))
          (pending-changes (nth 4 cursor))
          (changes (nth 5 cursor))
          (test (nth 6 cursor))
          (holds (nth 7 cursor)))
      (cond
       ((consp pending-changes)
        (let ((variable (caar pending-changes))
              (child (cadar pending-changes))
              (next (list agenda invocations actuals binding (cdr pending-changes)
                          changes test holds)))
          (quotient-proofs-let*
           ((projected (quotient-proofs-quotient-call lib child variable)))
           (if projected
               (quotient-proofs-let*
                ((test (proof-subst test binding)))
                (cons (list variable child changes test holds) next))
             (quotient-proofs-radix-calls-next-aux (1- n) lib next)))))
       ((consp invocations)
        (let* ((call (car invocations))
               (tests (termination-call-tests call)))
          (if (= (len tests) 1)
              (quotient-proofs-let*
               ((changes (quotient-proofs-radix-calls-changes
                          actuals (termination-call-actuals call) binding)))
               (quotient-proofs-radix-calls-next-aux
                (1- n) lib (list agenda (cdr invocations) actuals binding changes changes
                                 (caar tests) (cadar tests))))
            (quotient-proofs-radix-calls-next-aux
             (1- n) lib (list agenda (cdr invocations) actuals binding nil nil nil nil)))))
       ((consp agenda)
        (let ((term (car agenda))
              (rest (cdr agenda)))
          (cond
           ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
            (quotient-proofs-radix-calls-next-aux (1- n) lib
                                                 (list rest nil nil nil nil nil nil nil)))
           ((endp term) '(:failure "failure" ""))
           (t
            (let* ((agenda (append (reverse (cdr term)) rest))
                   (function (car term))
                   (definition (assoc-equal function
                                            (proof-proof-definitions (library-library-proof lib)))))
              (if (not (and definition (= (len (proof-unique (cdr term)))
                                         (len (cadr definition)))))
                  (quotient-proofs-radix-calls-next-aux
                   (1- n) lib (list agenda nil nil nil nil nil nil nil))
                (quotient-proofs-let*
                 ((fits (book-logic-within-size (caddr definition) 300)))
                 (if (not fits)
                     (quotient-proofs-radix-calls-next-aux
                      (1- n) lib (list agenda nil nil nil nil nil nil nil))
                   (quotient-proofs-let*
                    ((binding (quotient-proofs-radix-calls-binding
                               (seq-zip (cadr definition) (cdr term)) nil))
                     (invocations (termination-recursive-calls *termination-all* (list definition))))
                    (quotient-proofs-radix-calls-next-aux
                     (1- n) lib (list agenda invocations (cdr term) binding nil nil nil nil)))))))))))
       (t nil)))))

(defun quotient-proofs-radix-calls-next (lib cursor)
  (quotient-proofs-radix-calls-next-aux 1000000 lib cursor))

(defun quotient-proofs-prove-radix-induction-base (lib candidate)
  (quotient-proofs-let*
   ((base (quotient-proofs-proof-call proof-proof-assume lib (cadddr candidate)
                                     (not (nth 4 candidate)))))
   (list base)))

(defun quotient-proofs-prove-radix-induction-extras (variable changes)
  (if (endp changes)
      nil
    (let ((extras (quotient-proofs-prove-radix-induction-extras variable (cdr changes))))
      (if (equal variable (caar changes))
          extras
        (cons (car changes) extras)))))

(defun quotient-proofs-prove-radix-induction (lib formula candidate)
  (let* ((variable (car candidate))
         (child (cadr candidate))
         (changes (caddr candidate))
         (test (cadddr candidate))
         (holds (nth 4 candidate))
         (order (list *proof-ordinal-less* (list *library-count* child)
                      (list *library-count* variable))))
    (quotient-proofs-let*
     ((rulers (rulers-rulers-init lib (list (list test holds)) nil))
      ((smaller lib) (quotient-proofs-quotient-decrease lib order rulers)))
     (if (not smaller)
         (cons nil lib)
       (quotient-proofs-let*
        ((induction (book-logic-tree-induction-init lib formula variable))
         (extras (quotient-proofs-prove-radix-induction-extras variable changes))
         ((instance induction) (book-logic-tree-induction-at induction child smaller extras))
         (premise (quotient-proofs-proof-call proof-proof-assume lib test holds)))
        (cons (list induction (list premise instance)) lib))))))

(defun quotient-proofs-prove-radix-induction-finish (lib candidate induction base step)
  (let ((test (cadddr candidate))
        (holds (nth 4 candidate)))
    (quotient-proofs-let*
     ((proof (quotient-proofs-proof-call proof-proof-cases lib test
                                        (if holds step base) (if holds base step))))
     (book-logic-tree-induction-finish induction proof))))
