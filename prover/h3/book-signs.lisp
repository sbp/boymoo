(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-book-signs-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *h3-book-signs-case-split* (proof-sym "CASE-SPLIT" "ACL2"))
(defconst *h3-book-signs-complexp* (proof-sym "COMPLEX-RATIONALP" "ACL2"))
(defconst *h3-book-signs-prefix* "H3-BOOK-SIGN-")
(defconst *h3-book-signs-sign-names* '((-1 . "NEGATIVE") (0 . "ZERO") (1 . "POSITIVE")))
(defconst *h3-book-signs-product-signs*
  '("PRODUCT-GREATER-THAN-ZERO" "PRODUCT-GREATER-THAN-ZERO-2" "PRODUCT-LESS-THAN-ZERO"))

(defun h3-book-signs-make-signs (sign negative zero positive)
  (list sign negative zero positive))

(defun h3-book-signs-signs-sign (signs)
  (car signs))

(defun h3-book-signs-signs-negative (signs)
  (cadr signs))

(defun h3-book-signs-signs-zero (signs)
  (caddr signs))

(defun h3-book-signs-signs-positive (signs)
  (cadddr signs))

(defun h3-book-signs-signs-at (signs sign)
  (cond
   ((integerp sign)
    (let* ((index (+ sign 1))
           (index (if (< index 0) (+ index 3) index)))
      (if (and (<= 0 index) (< index 3))
          (nth (+ index 1) signs)
        '(:failure "failure" ""))))
   ((rationalp sign) '(:failure "failure" ""))
   ((stringp sign) '(:failure "failure" ""))
   ((consp sign) '(:failure "failure" ""))
   ((eq sign t) (h3-book-signs-signs-positive signs))
   (t '(:failure "failure" ""))))

(defun h3-book-signs-sign-test (term sign)
  (cond ((< sign 0) (library-lt term *proof-zero*))
        ((< 0 sign) (library-lt *proof-zero* term))
        (t (proof-eq term *proof-zero*))))

(defun h3-book-signs-step-at (step index)
  (proof-with-checked-results ((first (proof-step-first step)))
    (proof-term-at first index)))

(defun h3-book-signs-tail-of-size (term size)
  (if (integerp term)
      '(:failure "failure" "")
    (proof-list-of-length (cdr term) size)))

(defun h3-book-signs-sign-name (sign)
  (let ((entry (assoc-equal sign *h3-book-signs-sign-names*)))
    (if entry (cdr entry) (table-delete nil sign))))

(defun h3-book-signs-search (lib definitions)
  (h3-rewrite-search-init lib definitions nil nil 150 nil))

(defun h3-book-signs-prove (lib definitions goal hypotheses)
  (car (h3-rewrite-search-prove (h3-book-signs-search lib definitions) goal hypotheses)))

(defun h3-book-signs-number (lib rational)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((term (h3-book-signs-step-at rational 1))
      (rule (proof-proof-fact inference "rationalp-acl2-numberp" (list (list *library-x* term)))))
     (proof-proof-modus-ponens inference rule rational))))

(defun h3-book-signs-positive-reflection (lib term)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((equation (library-library-axiom lib "<-ON-OTHERS" (list *proof-zero* term)))
      (opposite (library-minus term))
      (unity (library-library-axiom lib "UNICITY-OF-0" (list opposite)))
      (numeric (h3-book-arithmetic-typed-number lib opposite))
      (fixed (h3-book-arithmetic-fix-value lib opposite numeric))
      (zero (proof-proof-chain inference unity (list fixed))))
     (proof-proof-rewrite inference equation zero '(1 2 1)))))

(defun h3-book-signs-checked-pair (pair)
  (if (failure-p (car pair)) (car pair) pair))

; A binding marked :pair advances the Library before checking its result.
(defmacro h3-book-signs-with-library-results (lib bindings result)
  (if (endp bindings)
      result
    (let ((name (caar bindings))
          (form (cadar bindings)))
      (if (eq (caddar bindings) :pair)
          `(let ((,name ,form))
             (if (failure-p ,name)
                 (cons ,name ,lib)
               (let ((,lib (cdr ,name))
                     (,name (car ,name)))
                 (if (failure-p ,name)
                     (cons ,name ,lib)
                   (h3-book-signs-with-library-results ,lib ,(cdr bindings) ,result)))))
        `(let ((,name ,form))
           (if (failure-p ,name)
               (cons ,name ,lib)
             (h3-book-signs-with-library-results ,lib ,(cdr bindings) ,result)))))))

(defun h3-book-signs-negative-reflection-with-library (lib numeric)
  (h3-book-signs-with-library-results lib
   ((term (h3-book-signs-step-at numeric 1))
    (registered (h3-book-sums-lemmas-with-library lib) :pair)
    (inference (library-library-proof lib))
    (double (library-library-cite lib *h3-book-sums-double* (list term) nil))
    (fixed (h3-book-arithmetic-fix-value lib term numeric))
    (double (proof-proof-chain inference double (list fixed)))
    (positive (h3-book-signs-positive-reflection lib (library-minus term)))
    (equation (proof-proof-rewrite inference positive double '(1 2 1))))
   (cons (proof-proof-symmetric inference equation) lib)))

(defun h3-book-signs-zero-contradiction (lib term index sign)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((equal (proof-proof-assume inference (proof-eq term *proof-zero*) t))
      (order (proof-proof-rewrite inference sign equal (list 1 index)))
      (zero (library-library-axiom lib "ZERO" nil))
      (contradiction (proof-proof-cut inference order zero))
      (first (proof-step-first equal)))
     (proof-proof-front inference contradiction (proof-neg first)))))

(defun h3-book-signs-sign-evidence-zero (lib sign proof)
  (let ((inference (library-library-proof lib)))
    (h3-book-signs-with-library-results lib
     ((zero-order (library-library-axiom lib "ZERO" nil))
      (substitution (proof-proof-symmetric inference proof))
      (negative (proof-proof-rewrite inference zero-order substitution '(1 1 1)))
      (positive (proof-proof-rewrite inference zero-order substitution '(1 1 2))))
     (cons (h3-book-signs-make-signs sign negative proof positive) lib))))

(defun h3-book-signs-sign-evidence-nonzero (lib numeric term sign proof)
  (let* ((inference (library-library-proof lib))
         (positive-test (h3-book-signs-sign-test term 1)))
    (h3-book-signs-with-library-results lib
     ((trichotomy (library-library-axiom lib "TRICHOTOMY" (list term)))
      (conjuncts (proof-proof-conjunct inference trichotomy))
      (pos (if (< 0 sign) proof (proof-proof-assume inference positive-test t)))
      (introduced (h3-rewrite-introduce-double-negation lib pos))
      (only-positive (proof-proof-prove-if inference (cadr conjuncts) introduced))
      (reflection (h3-book-signs-negative-reflection-with-library lib numeric) :pair)
      (inference (library-library-proof lib)))
     (if (< 0 sign)
         (h3-book-signs-with-library-results lib
          ((opposite (proof-proof-symmetric inference reflection))
           (negative (proof-proof-rewrite inference only-positive opposite '(1 1)))
           (negative (proof-proof-tidy inference negative))
           (zero (h3-book-signs-zero-contradiction lib term 2 proof)))
          (cons (h3-book-signs-make-signs sign negative zero proof) lib))
       (h3-book-signs-with-library-results lib
        ((opposite (proof-proof-rewrite inference proof reflection '(1)))
         (positive (proof-proof-cut inference opposite only-positive))
         (positive (proof-proof-front inference positive (proof-neg positive-test)))
         (zero (h3-book-signs-zero-contradiction lib term 1 proof)))
        (cons (h3-book-signs-make-signs sign proof zero positive) lib))))))

(defun h3-book-signs-sign-evidence-with-library (lib numeric sign proof)
  (h3-book-signs-with-library-results lib ((term (h3-book-signs-step-at numeric 1)))
   (if (equal sign 0)
       (h3-book-signs-sign-evidence-zero lib sign proof)
     (h3-book-signs-sign-evidence-nonzero lib numeric term sign proof))))

(defun h3-book-signs-each-sign-prepare-with-library (lib numeric)
  (let ((inference (library-library-proof lib)))
    (h3-book-signs-with-library-results lib
     ((term (h3-book-signs-step-at numeric 1))
      (positive-test (h3-book-signs-sign-test term 1))
      (zero-test (h3-book-signs-sign-test term 0))
      (positive (proof-proof-assume inference positive-test t))
      (zero (proof-proof-assume inference zero-test t))
      (trichotomy (library-library-axiom lib "TRICHOTOMY" (list term)))
      (conjuncts (proof-proof-conjunct inference trichotomy))
      (negative (proof-proof-modus-ponens inference (car conjuncts) numeric))
      (not-positive (proof-proof-assume inference positive-test nil))
      (negative (proof-proof-prove-if inference negative not-positive))
      (not-zero (proof-proof-assume inference zero-test nil))
      (negative (proof-proof-prove-if inference negative not-zero))
      (reflection (h3-book-signs-negative-reflection-with-library lib numeric) :pair)
      (negative (proof-proof-transport (library-library-proof lib) negative reflection)))
     (cons (list positive zero negative) lib))))

(defun h3-book-signs-each-sign-finish (lib numeric positive zero negative)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((term (h3-book-signs-step-at numeric 1))
      (other (proof-proof-cases inference (h3-book-signs-sign-test term 0) zero negative)))
     (proof-proof-cases inference (h3-book-signs-sign-test term 1) positive other))))

(defmacro h3-book-signs-invoke-case (case lib signs &rest args)
  (if (consp case)
      `(,(car case) ,signs ,lib ,@args)
    `(,case ,lib ,signs ,@args)))

(defmacro h3-book-signs-each-sign-with-library (lib numeric case &rest args)
  `(let ((h3-book-signs-case-library ,lib)
         (h3-book-signs-case-numeric ,numeric))
     (h3-book-signs-with-library-results h3-book-signs-case-library
      ((h3-book-signs-case-assumptions
        (h3-book-signs-each-sign-prepare-with-library
         h3-book-signs-case-library h3-book-signs-case-numeric) :pair)
       (h3-book-signs-case-positive
        (h3-book-signs-sign-evidence-with-library
         h3-book-signs-case-library h3-book-signs-case-numeric 1
         (car h3-book-signs-case-assumptions)) :pair)
       (h3-book-signs-case-positive
        (h3-book-signs-invoke-case
         ,case h3-book-signs-case-library h3-book-signs-case-positive ,@args) :pair)
       (h3-book-signs-case-zero
        (h3-book-signs-sign-evidence-with-library
         h3-book-signs-case-library h3-book-signs-case-numeric 0
         (cadr h3-book-signs-case-assumptions)) :pair)
       (h3-book-signs-case-zero
        (h3-book-signs-invoke-case
         ,case h3-book-signs-case-library h3-book-signs-case-zero ,@args) :pair)
       (h3-book-signs-case-negative
        (h3-book-signs-sign-evidence-with-library
         h3-book-signs-case-library h3-book-signs-case-numeric -1
         (caddr h3-book-signs-case-assumptions)) :pair)
       (h3-book-signs-case-negative
        (h3-book-signs-invoke-case
         ,case h3-book-signs-case-library h3-book-signs-case-negative ,@args) :pair))
      (cons (h3-book-signs-each-sign-finish
             h3-book-signs-case-library h3-book-signs-case-numeric
             h3-book-signs-case-positive h3-book-signs-case-zero h3-book-signs-case-negative)
            h3-book-signs-case-library))))

(defmacro h3-book-signs-each-sign (lib numeric case &rest args)
  `(h3-book-signs-checked-pair
    (h3-book-signs-each-sign-with-library ,lib ,numeric ,case ,@args)))

(defun h3-book-signs-true-boolean-lemma (lib label)
  (let* ((inference (library-library-proof lib))
         (boolean (list *h3-book-signs-booleanp* *library-x*))
         (value (proof-eq *library-x* *proof-true*)))
    (proof-with-checked-results
     ((assumption (proof-proof-assume inference boolean t))
      (definition (proof-proof-unfold inference boolean))
      (opened (proof-proof-rewrite inference assumption definition '(1)))
      (test (h3-book-signs-step-at opened 1))
      (opened
       (if (proof-is-call test (proof-cl "EQ"))
           (proof-with-checked-results ((definition (proof-proof-unfold inference test)))
             (proof-proof-rewrite inference opened definition '(1 1)))
         opened))
      (denied (proof-proof-assume inference value nil))
      (empty (proof-proof-prove-if inference opened denied))
      (first (proof-step-first empty))
      (empty
       (if (proof-is-call first (proof-cl "EQ"))
           (proof-with-checked-results ((definition (proof-proof-unfold inference first)))
             (proof-proof-rewrite inference empty definition '(1)))
         empty))
      (assumption (proof-proof-assume inference *library-x* t))
      (recipe (proof-proof-rewrite inference assumption empty '(1)))
      (recipe (proof-proof-tidy inference recipe))
      (recipe (proof-proof-front inference recipe value)))
     (library-library-lemma lib label value recipe
                            (list (proof-neg boolean) (proof-neg *library-x*))))))

(defun h3-book-signs-boolean-fact (lib term)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((head (proof-term-at term 0))
      (first (proof-term-at term 1)))
     (let ((binding (list *library-x* first)))
       (cond
        ((equal head *proof-integerp*)
         (proof-proof-fact inference "booleanp-integerp" (list binding)))
        ((equal head *library-rationalp*)
         (proof-proof-fact inference "booleanp-rationalp" (list binding)))
        ((equal head *h3-book-signs-complexp*)
         (proof-proof-fact inference "booleanp-complex-rationalp" (list binding)))
        (t (proof-with-checked-results ((second (proof-term-at term 2)))
             (proof-proof-fact inference "booleanp-<" (list binding (list *library-y* second))))))))))

(defun h3-book-signs-predicate-value-with-library (lib proof)
  (h3-book-signs-with-library-results lib ((term (proof-step-first proof)))
   (cond
    ((proof-is-call term *proof-not*) (cons (h3-rewrite-nil-value lib proof) lib))
    ((proof-is-call term *proof-equal*) (cons (h3-book-arithmetic-truth-value lib proof) lib))
    (t (let* ((label (concatenate 'string *h3-book-signs-prefix* "TRUE-BOOLEAN"))
              (name (proof-sym (concatenate 'string "SELF-" label) "ACL2")))
         (h3-book-signs-with-library-results lib
          ((updated (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                        lib
                      (h3-book-signs-true-boolean-lemma lib label))))
          (let ((lib updated))
            (h3-book-signs-with-library-results lib ((boolean (h3-book-signs-boolean-fact lib term)))
             (cons (library-library-cite lib label (list term) (list boolean proof)) lib)))))))))

(defun h3-book-signs-times-minus-lemma (lib label)
  (let ((formula (proof-eq (list *proof-times* *library-x* (library-minus *library-y*))
                           (library-minus (list *proof-times* *library-x* *library-y*)))))
    (proof-with-checked-results ((proof (h3-book-arithmetic-negative-product lib formula)))
      (library-library-lemma lib label formula proof nil))))

(defun h3-book-signs-minus-product-with-library (lib a b lefthand)
  (let* ((label (concatenate 'string *h3-book-signs-prefix* "TIMES-MINUS"))
         (name (proof-sym (concatenate 'string "SELF-" label) "ACL2")))
    (h3-book-signs-with-library-results lib
     ((updated (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                   lib
                 (h3-book-signs-times-minus-lemma lib label))))
     (let ((lib updated)
           (inference (library-library-proof updated)))
       (if (not lefthand)
           (cons (library-library-cite lib label (list a b) nil) lib)
         (h3-book-signs-with-library-results lib
          ((commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list (library-minus a) b)))
           (minus (library-library-cite lib label (list b a) nil))
           (step (proof-proof-chain inference commuted (list minus)))
           (exchange (library-library-axiom lib "COMMUTATIVITY-OF-*" (list b a))))
          (cons (proof-proof-rewrite inference step exchange '(1 2 1)) lib)))))))

(defun h3-book-signs-times-negative-one-with-library (lib numeric)
  (let ((inference (library-library-proof lib)))
    (h3-book-signs-with-library-results lib
     ((term (h3-book-signs-step-at numeric 1))
      (product (list *proof-times* *proof-neg-one* term))
      (literal (proof-proof-compute inference (library-minus *proof-one*) -1))
      (literal (proof-proof-symmetric inference literal))
      (changed (proof-proof-reflexive inference product))
      (changed (proof-proof-rewrite inference changed literal '(1 2 1)))
      (negative (h3-book-signs-minus-product-with-library lib *proof-one* term t) :pair)
      (inference (library-library-proof lib))
      (changed (proof-proof-chain inference changed (list negative)))
      (unity (library-library-axiom lib "UNICITY-OF-1" (list term)))
      (fixed (h3-book-arithmetic-fix-value lib term numeric))
      (identity (proof-proof-chain inference unity (list fixed))))
     (cons (proof-proof-rewrite inference changed identity '(1 2 1)) lib))))

(defun h3-book-signs-rational-product (lib ra rb)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((a (h3-book-signs-step-at ra 1))
      (b (h3-book-signs-step-at rb 1))
      (rule (proof-proof-fact inference "rationalp-binary-*"
                             (list (list *library-x* a) (list *library-y* b)))))
     (h3-symbolic-order-guarded lib rule (list ra rb)))))

(defun h3-book-signs-rational-sign-adjust (lib rational signs)
  (h3-book-signs-with-library-results lib ((term (h3-book-signs-step-at rational 1)))
   (if (< (h3-book-signs-signs-sign signs) 0)
       (h3-book-signs-with-library-results lib
        ((numeric (h3-book-signs-number lib rational))
         (reflection (h3-book-signs-negative-reflection-with-library lib numeric) :pair)
         (inference (library-library-proof lib))
         (pos (proof-proof-rewrite inference (h3-book-signs-signs-negative signs) reflection '(1)))
         (rule (proof-proof-fact inference "rationalp-unary--" (list (list *library-x* term))))
         (rational (proof-proof-modus-ponens inference rule rational)))
        (cons (list rational pos) lib))
     (cons (list rational (h3-book-signs-signs-positive signs)) lib))))

(defun h3-book-signs-rational-sign-remove-minus (lib positive a b lefthand position)
  (h3-book-signs-with-library-results lib
   ((minus (h3-book-signs-minus-product-with-library lib a b lefthand) :pair))
   (cons (proof-proof-rewrite (library-library-proof lib) positive minus position) lib)))

(defun h3-book-signs-rational-sign-remove-double (lib positive product numeric)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((double (library-library-cite lib *h3-book-sums-double* (list product) nil))
      (fixed (h3-book-arithmetic-fix-value lib product numeric))
      (reduced (proof-proof-chain inference double (list fixed))))
     (proof-proof-rewrite inference positive reduced '(1 2)))))

(defun h3-book-signs-rational-sign-nonzero (lib ra rb sa sb a b product numeric result-sign)
  (let ((negative-a (< (h3-book-signs-signs-sign sa) 0))
        (negative-b (< (h3-book-signs-signs-sign sb) 0)))
    (h3-book-signs-with-library-results lib
     ((first (h3-book-signs-rational-sign-adjust lib ra sa) :pair)
      (second (h3-book-signs-rational-sign-adjust lib rb sb) :pair)
      (r1 (car first))
      (r2 (car second))
      (a-adjusted (h3-book-signs-step-at r1 1))
      (b-adjusted (h3-book-signs-step-at r2 1))
      (axiom (library-library-axiom lib "POSITIVE" (list a-adjusted b-adjusted)))
      (conjuncts (proof-proof-conjunct (library-library-proof lib) axiom))
      (positive (h3-symbolic-order-guarded lib (cadr conjuncts)
                                          (list r1 r2 (cadr first) (cadr second))))
      (positive (if negative-a
                    (h3-book-signs-rational-sign-remove-minus lib positive a b-adjusted t '(1 2))
                  (cons positive lib)) :pair)
      (positive (if negative-b
                    (h3-book-signs-rational-sign-remove-minus
                     lib positive a b nil (if negative-a '(1 2 1) '(1 2)))
                  (cons positive lib)) :pair)
      (positive (if (and negative-a negative-b)
                    (h3-book-signs-rational-sign-remove-double lib positive product numeric)
                  positive))
      (positive (if (< result-sign 0)
                    (h3-book-signs-with-library-results lib
                     ((reflection (h3-book-signs-negative-reflection-with-library lib numeric) :pair))
                     (cons (proof-proof-transport (library-library-proof lib) positive reflection) lib))
                  (cons positive lib)) :pair))
     (h3-book-signs-sign-evidence-with-library lib numeric result-sign positive))))

(defun h3-book-signs-rational-sign-with-library (lib ra rb sa sb)
  (h3-book-signs-with-library-results lib
   ((a (h3-book-signs-step-at ra 1))
    (b (h3-book-signs-step-at rb 1))
    (product (list *proof-times* a b))
    (rational (h3-book-signs-rational-product lib ra rb))
    (numeric (h3-book-signs-number lib rational))
    (sign-a (h3-book-signs-signs-sign sa))
    (result-sign (* sign-a (h3-book-signs-signs-sign sb))))
   (if (equal result-sign 0)
       (let ((term (if (equal sign-a 0) a b))
             (status (h3-book-signs-signs-zero (if (equal sign-a 0) sa sb))))
         (h3-book-signs-with-library-results lib
          ((equation (h3-book-arithmetic-zero-product lib a b term status)))
          (h3-book-signs-sign-evidence-with-library lib numeric 0 equation)))
     (h3-book-signs-rational-sign-nonzero lib ra rb sa sb a b product numeric result-sign))))

(defun h3-book-signs-rational-scaling-case (s1 lib r1 r2 s2 orientation)
  (h3-book-signs-with-library-results lib
   ((product (h3-book-signs-rational-sign-with-library lib r1 r2 s1 s2) :pair)
    (left (h3-book-signs-signs-at product orientation))
    (left (h3-book-signs-predicate-value-with-library lib left) :pair)
    (right (h3-book-signs-signs-at s1 (* orientation (h3-book-signs-signs-sign s2))))
    (right (h3-book-signs-predicate-value-with-library lib right) :pair)
    (inference (library-library-proof lib))
    (reverse (proof-proof-symmetric inference right)))
   (cons (proof-proof-chain inference left (list reverse)) lib)))

(defun h3-book-signs-rational-scaling-lemma (lib label sign orientation)
  (let ((inference (library-library-proof lib)))
    (h3-book-signs-with-library-results lib
     ((r1 (proof-proof-assume inference (list *library-rationalp* *library-x*) t))
      (r2 (proof-proof-assume inference (list *library-rationalp* *library-y*) t))
      (condition (h3-book-signs-sign-test *library-y* sign))
      (numeric (h3-book-signs-number lib r2))
      (given (proof-proof-assume inference condition t))
      (s2 (h3-book-signs-sign-evidence-with-library lib numeric sign given) :pair)
      (numeric (h3-book-signs-number lib r1))
      (step (h3-book-signs-each-sign-with-library
             lib numeric (h3-book-signs-rational-scaling-case) r1 r2 s2 orientation) :pair)
      (claim (proof-step-first step))
      (rational-x (proof-step-first r1))
      (rational-y (proof-step-first r2))
      (updated (library-library-lemma lib label claim step
                                      (list (proof-neg rational-x) (proof-neg rational-y)
                                            (proof-neg condition)))))
     (cons nil updated))))

(defun h3-book-signs-rational-scaling-with-library (lib ra rb sb orientation)
  (h3-book-signs-with-library-results lib
   ((sign (h3-book-signs-signs-sign sb))
    (multiplier (h3-book-signs-sign-name sign))
    (test (h3-book-signs-sign-name orientation))
    (label (concatenate 'string *h3-book-signs-prefix* multiplier "-MULTIPLIER-" test))
    (name (proof-sym (concatenate 'string "SELF-" label) "ACL2"))
    (registered (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                    (cons nil lib)
                  (h3-book-signs-rational-scaling-lemma lib label sign orientation)) :pair)
    (a (h3-book-signs-step-at ra 1))
    (b (h3-book-signs-step-at rb 1))
    (status (h3-book-signs-signs-at sb sign)))
   (cons (library-library-cite lib label (list a b) (list ra rb status)) lib)))

(defun h3-book-signs-comparison-by-parts-default (lib name missing)
  (proof-with-checked-results ((axiom (library-library-axiom lib name (list *library-x*))))
    (proof-proof-modus-ponens (library-library-proof lib) axiom missing)))

(defun h3-book-signs-comparison-by-parts-lemma (lib label orientation)
  (let* ((inference (library-library-proof lib))
         (comparison (h3-book-signs-sign-test *library-x* orientation))
         (real (list *h3-numeric-real* *library-x*))
         (imag (list *h3-numeric-imaginary* *library-x*))
         (lex (proof-ite (proof-eq real *proof-zero*)
                         (h3-book-signs-sign-test imag orientation)
                         (h3-book-signs-sign-test real orientation)))
         (goal (proof-eq comparison lex))
         (is-rational (list *library-rationalp* *library-x*)))
    (proof-with-checked-results
     ((rational (proof-proof-assume inference is-rational t))
      (other (proof-proof-assume inference is-rational nil))
      (order (library-library-axiom lib "COMPLETION-OF-<" (cdr comparison)))
      (search (h3-book-signs-search lib nil))
      (parts (h3-numeric-rational-components lib rational))
      (yes-result (h3-rewrite-search-prove search goal parts))
      (yes (car yes-result))
      (numeric (list *library-numberp* *library-x*))
      (present (proof-proof-assume inference numeric t))
      (missing (proof-proof-assume inference numeric nil))
      (default-real (h3-book-signs-comparison-by-parts-default lib "DEFAULT-REALPART" missing))
      (default-imag (h3-book-signs-comparison-by-parts-default lib "DEFAULT-IMAGPART" missing))
      (numeric-result (h3-rewrite-search-prove (cdr yes-result) goal (list order other present)))
      (numeric-order (car numeric-result))
      (default-result (h3-rewrite-search-prove (cdr numeric-result) goal
                                             (list order other missing default-real default-imag)))
      (default-order (car default-result))
      (no (proof-proof-cases inference numeric numeric-order default-order))
      (step (proof-proof-cases inference is-rational yes no)))
     (library-library-lemma lib label goal step nil))))

(defun h3-book-signs-comparison-by-parts-with-library (lib term orientation)
  (h3-book-signs-with-library-results lib
   ((sign (h3-book-signs-sign-name orientation))
    (label (concatenate 'string *h3-book-signs-prefix* "ORDER-BY-PARTS-" sign))
    (name (proof-sym (concatenate 'string "SELF-" label) "ACL2"))
    (updated (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                 lib
               (h3-book-signs-comparison-by-parts-lemma lib label orientation))))
   (cons (library-library-cite updated label (list term) nil) updated)))

(defun h3-book-signs-scaled-parts-component (lib head name product parts source real imag)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((opened (proof-proof-reflexive inference (list head product)))
      (opened (proof-proof-rewrite inference opened source '(1 2 1)))
      (rule (library-library-axiom lib name (cdr parts)))
      (rule (h3-symbolic-order-guarded lib rule (list real imag))))
     (proof-proof-chain inference opened (list rule)))))

(defun h3-book-signs-scaled-parts (lib term scalar-type)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((scalar (h3-book-signs-step-at scalar-type 1))
      (components (h3-numeric-real-and-imaginary lib term))
      (real (car components))
      (imag (cadr components))
      (source (h3-book-arithmetic-multiply-fix lib term scalar))
      (source (proof-proof-symmetric inference source))
      (complex-value (h3-numeric-decompose lib term))
      (complex-value (proof-proof-symmetric inference complex-value))
      (source (proof-proof-rewrite inference source complex-value '(1 2 1)))
      (expanded (h3-numeric-expand-complex lib real imag))
      (source (proof-proof-rewrite inference source expanded '(1 2 1)))
      (rhs (h3-book-signs-step-at source 2))
      (expanded (proof-term-at rhs 1))
      (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list expanded scalar)))
      (distributed (h3-book-arithmetic-multiply-out lib scalar expanded))
      (source (proof-proof-chain inference source (list commuted distributed)))
      (product-real (h3-book-signs-rational-product lib real scalar-type))
      (product-imag (h3-book-signs-rational-product lib imag scalar-type))
      (target (h3-numeric-expand-complex lib product-real product-imag))
      (source-rhs (h3-book-signs-step-at source 2))
      (target-rhs (h3-book-signs-step-at target 2))
      (equal (h3-book-arithmetic-associative-equal lib source-rhs target-rhs))
      (reverse (proof-proof-symmetric inference target))
      (source (proof-proof-chain inference source (list equal reverse)))
      (source-first (proof-step-first source))
      (sides (h3-book-signs-tail-of-size source-first 2))
      (product (car sides))
      (parts (cadr sides))
      (real-step (h3-book-signs-scaled-parts-component
                  lib *h3-numeric-real* "REALPART-COMPLEX" product parts source product-real product-imag))
      (imag-step (h3-book-signs-scaled-parts-component
                  lib *h3-numeric-imaginary* "IMAGPART-COMPLEX" product parts source product-real product-imag)))
     (list real-step imag-step))))

(defun h3-book-signs-scaled-comparison-rewrite-zero (lib test zero position)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((identity (proof-proof-reflexive inference test))
      (eq-test (proof-proof-rewrite inference identity zero (list 1 2 position)))
      (rhs (h3-book-signs-step-at eq-test 2))
      (evaluated (proof-proof-compute inference rhs (cadr *proof-false*))))
     (proof-proof-chain inference eq-test (list evaluated)))))

(defun h3-book-signs-scaled-comparison-zero (lib term factor status test position)
  (proof-with-checked-results
   ((zero (h3-book-arithmetic-zero-product lib term factor factor status)))
   (h3-book-signs-scaled-comparison-rewrite-zero lib test zero position)))

(defun h3-book-signs-scaled-comparison-rewrite-component
    (lib step scalar-type scale component sign place)
  (h3-book-signs-with-library-results lib
   ((equation (h3-book-signs-rational-scaling-with-library lib component scalar-type scale sign) :pair))
   (cons (proof-proof-rewrite (library-library-proof lib) step equation (list 1 2 place)) lib)))

(defun h3-book-signs-scaled-comparison-with-library (lib term scalar-type scale orientation)
  (h3-book-signs-with-library-results lib
   ((factor (h3-book-signs-step-at scalar-type 1))
    (product (list *proof-times* term factor))
    (test (h3-book-signs-sign-test product orientation))
    (position (if (< orientation 0) 1 2))
    (sign (h3-book-signs-signs-sign scale)))
   (if (equal sign 0)
       (cons (h3-book-signs-scaled-comparison-zero
              lib term factor (h3-book-signs-signs-zero scale) test position)
             lib)
     (h3-book-signs-with-library-results lib
      ((step (h3-book-signs-comparison-by-parts-with-library lib product orientation) :pair)
       (parts (h3-book-signs-scaled-parts lib term scalar-type))
       (components (h3-numeric-real-and-imaginary lib term))
       (inference (library-library-proof lib))
       (step (proof-proof-rewrite inference step (car parts) '(1 2 1 1)))
       (step (proof-proof-rewrite inference step (cadr parts) (list 1 2 2 position)))
       (step (proof-proof-rewrite inference step (car parts) (list 1 2 3 position)))
       (step (h3-book-signs-scaled-comparison-rewrite-component
              lib step scalar-type scale (car components) 0 1) :pair)
       (step (h3-book-signs-scaled-comparison-rewrite-component
              lib step scalar-type scale (cadr components) orientation 2) :pair)
       (step (h3-book-signs-scaled-comparison-rewrite-component
              lib step scalar-type scale (car components) orientation 3) :pair)
       (order (h3-book-signs-comparison-by-parts-with-library lib term (* orientation sign)) :pair)
       (inference (library-library-proof lib))
       (reverse (proof-proof-symmetric inference order)))
      (cons (proof-proof-chain inference step (list reverse)) lib)))))

(defun h3-book-signs-nonnumeric-signs-default (lib name args absent)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((axiom (library-library-axiom lib name args))
      (equation (proof-proof-modus-ponens inference axiom absent))
      (rhs (h3-book-signs-step-at equation 2))
      (evaluated (proof-proof-compute inference rhs (cadr *proof-false*))))
     (proof-proof-chain inference equation (list evaluated)))))

(defun h3-book-signs-nonnumeric-signs (lib term absent)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((negative (h3-book-signs-nonnumeric-signs-default lib "DEFAULT-<-1" (list term *proof-zero*) absent))
      (positive (h3-book-signs-nonnumeric-signs-default lib "DEFAULT-<-2" (list *proof-zero* term) absent))
      (zero (proof-eq term *proof-zero*))
      (numeric (h3-book-arithmetic-typed-number lib *proof-zero*))
      (given (proof-proof-assume inference zero t))
      (given (proof-proof-symmetric inference given))
      (numeric (proof-proof-rewrite inference numeric given '(1 1)))
      (disproved (proof-proof-cut inference numeric absent))
      (disproved (proof-proof-front inference disproved (proof-neg zero))))
     (list negative positive disproved))))

(defun h3-book-signs-sign-conditions-with-library (lib signs)
  (let ((negative (h3-book-signs-signs-negative signs))
        (zero (h3-book-signs-signs-zero signs))
        (positive (h3-book-signs-signs-positive signs)))
    (h3-book-signs-with-library-results lib
     ((negative-value (h3-book-signs-predicate-value-with-library lib negative) :pair)
      (zero-value (h3-book-signs-predicate-value-with-library lib zero) :pair)
      (positive-value (h3-book-signs-predicate-value-with-library lib positive) :pair))
     (cons (list negative zero positive negative-value zero-value positive-value) lib))))

(defun h3-book-signs-scale-sign-goal-prove-goal
    (equation evidence lib formula comparison term scalar swapped orientation)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((equation
       (if swapped
           (proof-with-checked-results
            ((first (proof-proof-reflexive inference comparison))
             (exchange (library-library-axiom lib "COMMUTATIVITY-OF-*" (list scalar term)))
             (first (proof-proof-rewrite inference first exchange
                                         (list 1 2 (if (< orientation 0) 1 2)))))
            (proof-proof-chain inference first (list equation)))
         equation)))
     (h3-book-signs-prove lib (list *proof-not*) formula (cons equation evidence)))))

(defun h3-book-signs-scale-sign-goal-other-cases-signed
    (values lib equation scalar-facts kind formula comparison term scalar swapped orientation)
  (h3-book-signs-with-library-results lib
   ((facts (h3-book-signs-sign-conditions-with-library lib values) :pair)
    (numeric (proof-proof-assume (library-library-proof lib) kind t)))
   (cons (h3-book-signs-scale-sign-goal-prove-goal
          equation (append scalar-facts facts (list numeric)) lib formula comparison term
          scalar swapped orientation)
         lib)))

(defun h3-book-signs-scale-sign-goal-other-cases
    (equation scalar-facts lib formula comparison term scalar swapped orientation)
  (let ((kind (list *library-numberp* term))
        (inference (library-library-proof lib)))
    (h3-book-signs-with-library-results lib
     ((missing (proof-proof-assume inference kind nil))
      (defaults (h3-book-signs-nonnumeric-signs lib term missing))
      (other (h3-book-signs-scale-sign-goal-prove-goal
              equation (append scalar-facts (cons missing defaults)) lib
              formula comparison term scalar swapped orientation))
      (numeric (proof-proof-assume inference kind t))
      (valid (h3-book-signs-each-sign-with-library
              lib numeric (h3-book-signs-scale-sign-goal-other-cases-signed)
              equation scalar-facts kind formula comparison term scalar swapped orientation) :pair))
     (cons (proof-proof-cases (library-library-proof lib) kind valid other) lib))))

(defun h3-book-signs-scale-sign-goal-scaled-case
    (scale lib formula comparison term scalar swapped orientation rational yes)
  (h3-book-signs-with-library-results lib
   ((equation (h3-book-signs-scaled-comparison-with-library lib term rational scale orientation) :pair)
    (facts (h3-book-signs-sign-conditions-with-library lib scale) :pair))
   (h3-book-signs-scale-sign-goal-other-cases
    equation (append facts (list yes)) lib formula comparison term scalar swapped orientation)))

(defun h3-book-signs-scale-sign-goal-rational (lib scalar yes neg-complex)
  (let ((inference (library-library-proof lib)))
    (proof-with-checked-results
     ((fact (proof-proof-fact inference "acl2-numberp-cases" (list (list *library-x* scalar))))
      (choices (proof-proof-modus-ponens inference fact yes))
      (rat (list *library-rationalp* scalar))
      (other (proof-proof-assume inference rat nil))
      (is-complex (proof-proof-prove-if inference choices other))
      (rational (if neg-complex
                    (proof-proof-cut inference is-complex neg-complex)
                  '(:failure "failure" ""))))
     (proof-proof-front inference rational rat))))

(defun h3-book-signs-scale-sign-goal-default
    (lib numeric good formula comparison term scalar swapped orientation)
  (h3-book-signs-with-library-results lib
   ((no (proof-proof-assume (library-library-proof lib) numeric nil))
    (product (list *proof-times* term scalar))
    (zero (h3-book-arithmetic-zero-product lib term scalar scalar no))
    (target (h3-book-signs-sign-test product orientation))
    (default (h3-book-signs-scaled-comparison-rewrite-zero lib target zero (if (< orientation 0) 1 2)))
    (defaults (h3-book-signs-nonnumeric-signs lib scalar no))
    (bad (h3-book-signs-scale-sign-goal-other-cases
          default (cons no defaults) lib formula comparison term scalar swapped orientation) :pair))
   (cons (proof-proof-cases (library-library-proof lib) numeric good bad) lib)))

(defun h3-book-signs-scale-sign-goal-with-library (lib formula term scalar swapped rational neg-complex)
  (h3-book-signs-with-library-results lib
   ((comparison (proof-term-at formula 1))
    (right (proof-term-at comparison 2))
    (orientation (if (equal right *proof-zero*) -1 1))
    (numeric (list *library-numberp* scalar))
    (known-rational (not (null rational)))
    (yes (if known-rational
             (h3-book-signs-number lib rational)
           (proof-proof-assume (library-library-proof lib) numeric t)))
    (rational (if known-rational rational (h3-book-signs-scale-sign-goal-rational lib scalar yes neg-complex)))
    (good (h3-book-signs-each-sign-with-library
           lib yes (h3-book-signs-scale-sign-goal-scaled-case)
           formula comparison term scalar swapped orientation rational yes) :pair))
   (if known-rational
       (cons good lib)
     (h3-book-signs-scale-sign-goal-default lib numeric good formula comparison term scalar swapped orientation))))

(defun h3-book-signs-product-sign-theorem-negative (lib goal x y premise search)
  (let ((complex-y (list *h3-book-signs-complexp* y)))
    (h3-book-signs-with-library-results lib
     ((complex (proof-proof-assume (library-library-proof lib) complex-y t))
      (search-result (h3-rewrite-search-prove
                      search (proof-neg (list *h3-book-signs-complexp* x)) (list premise complex)))
      (complex-x-absent (car search-result))
      (left (h3-book-signs-scale-sign-goal-with-library lib goal y x t nil complex-x-absent) :pair)
      (not-complex-y (proof-proof-assume (library-library-proof lib) complex-y nil))
      (right (h3-book-signs-scale-sign-goal-with-library lib goal x y nil nil not-complex-y) :pair))
     (cons (proof-proof-cases (library-library-proof lib) complex-y left right) lib))))

(defun h3-book-signs-product-sign-theorem-positive (lib name goal x y premise search)
  (let* ((swapped (equal name "PRODUCT-GREATER-THAN-ZERO-2"))
         (term (if swapped y x))
         (scalar (if swapped x y)))
    (h3-book-signs-with-library-results lib
     ((search-result (h3-rewrite-search-prove search (proof-neg (list *h3-book-signs-complexp* scalar))
                                            (list premise)))
      (not-complex (car search-result)))
     (h3-book-signs-scale-sign-goal-with-library lib goal term scalar swapped nil not-complex))))

(defun h3-book-signs-product-sign-theorem-with-library (lib name formula)
  (h3-book-signs-with-library-results lib
   ((fields (h3-book-signs-tail-of-size formula 2))
    (condition (car fields))
    (goal (cadr fields))
    (comparison (proof-term-at goal 1))
    (right (proof-term-at comparison 2))
    (product (if (equal right *proof-zero*) (proof-term-at comparison 1) right))
    (factors (h3-book-signs-tail-of-size product 2))
    (x (car factors))
    (y (cadr factors))
    (premise (proof-proof-assume (library-library-proof lib) condition t))
    (search (h3-book-signs-search lib (list *h3-book-signs-case-split* *proof-not*)))
    (proof (if (equal name "PRODUCT-LESS-THAN-ZERO")
               (h3-book-signs-product-sign-theorem-negative lib goal x y premise search)
             (h3-book-signs-product-sign-theorem-positive lib name goal x y premise search)) :pair))
   (cons (h3-rewrite-implication lib condition proof) lib)))

(defun h3-book-signs-rational-product-sign-goal-first-sign-second-sign
    (b lib search target first second orientation a)
  (h3-book-signs-with-library-results lib
   ((product (h3-book-signs-rational-sign-with-library lib first second a b) :pair)
    (product (h3-book-signs-signs-at product orientation))
    (result (h3-book-signs-predicate-value-with-library lib product) :pair)
    (a-facts (h3-book-signs-sign-conditions-with-library lib a) :pair)
    (b-facts (h3-book-signs-sign-conditions-with-library lib b) :pair)
    (search (h3-rewrite-search-with-lib search lib))
    (conditions (h3-rewrite-search-context search (append a-facts b-facts)))
    (rhs (proof-term-at target 2))
    (expected (car (h3-rewrite-search-reduce search rhs conditions nil nil))))
   (if (not expected)
       (cons '(:failure "unproved" "") lib)
     (h3-book-signs-with-library-results lib
      ((expected-value (h3-book-signs-step-at expected 2))
       (result-value (h3-book-signs-step-at result 2)))
      (if (equal expected-value result-value)
          (let ((inference (library-library-proof lib)))
            (h3-book-signs-with-library-results lib ((reverse (proof-proof-symmetric inference expected)))
             (cons (proof-proof-chain inference result (list reverse)) lib)))
        (cons '(:failure "unproved" "") lib))))))

(defun h3-book-signs-rational-product-sign-goal-first-sign
    (a lib search target first second orientation)
  (h3-book-signs-with-library-results lib ((numeric (h3-book-signs-number lib second)))
   (h3-book-signs-each-sign-with-library
    lib numeric (h3-book-signs-rational-product-sign-goal-first-sign-second-sign)
    search target first second orientation a)))

(defun h3-book-signs-rational-product-sign-goal-with-library (lib target first second orientation)
  (h3-book-signs-with-library-results lib
   ((search (h3-book-signs-search lib (list *proof-not* (proof-sym "IFF" "ACL2"))))
    (numeric (h3-book-signs-number lib first)))
   (h3-book-signs-each-sign-with-library
    lib numeric (h3-book-signs-rational-product-sign-goal-first-sign) search target first second orientation)))

(defun h3-book-signs-conditional-product-sign-rationals (operands evidence)
  (if (endp operands)
      nil
    (cons (table-get evidence (list *library-rationalp* (car operands)) nil)
          (h3-book-signs-conditional-product-sign-rationals (cdr operands) evidence))))

(defun h3-book-signs-conditional-product-sign-all (proofs)
  (or (endp proofs)
      (and (car proofs) (h3-book-signs-conditional-product-sign-all (cdr proofs)))))

(defun h3-book-signs-conditional-product-sign-scale (lib guard target product evidence index)
  (h3-book-signs-with-library-results lib
   ((scalar (proof-term-at product index))
    (rational (table-get evidence (list *library-rationalp* scalar) nil)))
   (if rational
       (h3-book-signs-with-library-results lib
        ((other (proof-term-at product (- 3 index)))
         (proof (h3-book-signs-scale-sign-goal-with-library
                 lib target other scalar (equal index 1) rational nil) :pair))
        (cons (h3-rewrite-implication lib guard proof) lib))
     (cons nil lib))))

(defun h3-book-signs-conditional-product-sign-scales (lib guard target product evidence)
  (let ((second (h3-book-signs-conditional-product-sign-scale lib guard target product evidence 2)))
    (if (car second)
        second
      (h3-book-signs-conditional-product-sign-scale lib guard target product evidence 1))))

(defun h3-book-signs-conditional-product-sign-proof (lib guard target product second)
  (h3-book-signs-with-library-results lib
   ((search (h3-book-signs-search lib nil))
    (given (proof-proof-assume (library-library-proof lib) guard t))
    (evidence (h3-rewrite-search-context search (list given)))
    (rational (h3-book-signs-conditional-product-sign-rationals (cdr product) evidence)))
   (if (h3-book-signs-conditional-product-sign-all rational)
       (if (/= (len rational) 2)
           (cons '(:failure "failure" "") lib)
         (let* ((orientation (if (equal second *proof-zero*) -1 1))
                (result (h3-book-signs-rational-product-sign-goal-with-library
                         lib target (car rational) (cadr rational) orientation))
                (proof (car result))
                (lib (cdr result)))
           (cond ((h3-rewrite-unproved-p proof)
                  (h3-book-signs-conditional-product-sign-scales lib guard target product evidence))
                 ((failure-p proof) result)
                 (t (cons (h3-rewrite-implication lib guard proof) lib)))))
     (h3-book-signs-conditional-product-sign-scales lib guard target product evidence))))

(defun h3-book-signs-conditional-product-sign-target (lib guard target)
  (if (not (proof-is-call target *proof-equal*))
      (cons nil lib)
    (h3-book-signs-with-library-results lib ((left (proof-term-at target 1)))
     (if (not (proof-is-call left *proof-less*))
         (cons nil lib)
       (h3-book-signs-with-library-results lib ((right (proof-term-at target 2)))
        (if (not (proof-is-call right *proof-if*))
            (cons nil lib)
          (h3-book-signs-with-library-results lib
           ((comparison (h3-book-signs-tail-of-size left 2))
            (first (car comparison))
            (second (cadr comparison))
            (product (cond ((equal second *proof-zero*) first)
                           ((equal first *proof-zero*) second))))
           (if (proof-is-call product *proof-times*)
               (h3-book-signs-conditional-product-sign-proof lib guard target product second)
             (cons nil lib)))))))))

(defun h3-book-signs-conditional-product-sign-with-library (lib formula)
  (if (proof-is-call formula *library-implies*)
      (h3-book-signs-with-library-results lib ((fields (h3-book-signs-tail-of-size formula 2)))
       (h3-book-signs-conditional-product-sign-target lib (car fields) (cadr fields)))
    (cons nil lib)))

(defun h3-book-signs-boolean-comparison-equality-branch (lib q truth formula p-eq search)
  (h3-book-signs-with-library-results lib
   ((given (proof-proof-assume (library-library-proof lib) q truth))
    (q-eq (h3-book-signs-predicate-value-with-library lib given) :pair)
    (search (h3-rewrite-search-with-lib search lib))
    (result (h3-rewrite-search-prove search formula (list p-eq q-eq)))
    (step (car result)))
   (cons (list step (cdr result)) lib)))

(defun h3-book-signs-boolean-comparison-equality-given (p-truth lib p q formula search)
  (h3-book-signs-with-library-results lib
   ((given (proof-proof-assume (library-library-proof lib) p p-truth))
    (p-eq (h3-book-signs-predicate-value-with-library lib given) :pair)
    (yes (h3-book-signs-boolean-comparison-equality-branch lib q t formula p-eq search) :pair)
    (no (h3-book-signs-boolean-comparison-equality-branch lib q nil formula p-eq (cadr yes)) :pair)
    (step (proof-proof-cases (library-library-proof lib) q (car yes) (car no))))
   (cons (list step (cadr no)) lib)))

(defun h3-book-signs-boolean-comparison-equality-prove (lib formula p q iff)
  (h3-book-signs-with-library-results lib
   ((search (h3-book-signs-search lib (list *proof-not* iff)))
    (yes (h3-book-signs-boolean-comparison-equality-given t lib p q formula search) :pair)
    (no (h3-book-signs-boolean-comparison-equality-given nil lib p q formula (cadr yes)) :pair))
   (cons (proof-proof-cases (library-library-proof lib) p (car yes) (car no)) lib)))

(defun h3-book-signs-boolean-comparison-equality-with-library (lib formula)
  (let ((iff (proof-sym "IFF" "ACL2")))
    (if (not (proof-is-call formula *proof-equal*))
        (cons nil lib)
      (h3-book-signs-with-library-results lib ((left (proof-term-at formula 1)))
       (if (not (proof-is-call left *proof-equal*))
           (cons nil lib)
         (h3-book-signs-with-library-results lib ((right (proof-term-at formula 2)))
          (if (not (proof-is-call right iff))
              (cons nil lib)
            (h3-book-signs-with-library-results lib ((tests (h3-book-signs-tail-of-size left 2)))
             (let ((p (car tests))
                   (q (cadr tests)))
               (if (and (equal (cdr right) tests)
                        (proof-is-call p *proof-less*) (proof-is-call q *proof-less*))
                   (h3-book-signs-boolean-comparison-equality-prove lib formula p q iff)
                 (cons nil lib)))))))))))

