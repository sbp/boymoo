(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-numeric-types-floor* (proof-cl "FLOOR"))
(defconst *b2-numeric-types-truncate* (proof-cl "TRUNCATE"))
(defconst *b2-numeric-types-characterp* (proof-cl "CHARACTERP"))
(defconst *b2-numeric-types-stringp* (proof-cl "STRINGP"))
(defconst *b2-numeric-types-coerce* (proof-cl "COERCE"))
(defconst *b2-numeric-types-count* (proof-sym "ACL2-COUNT" "ACL2"))
(defconst *b2-numeric-types-logrev* (proof-sym "LOGREV1" "ACL2"))
(defconst *b2-numeric-types-zp* (proof-sym "ZP" "ACL2"))
(defconst *b2-numeric-types-the-check* (proof-sym "THE-CHECK" "ACL2"))
(defconst *b2-numeric-types-size* (proof-sym "SIZE" "ACL2"))
(defconst *b2-numeric-types-i* (proof-sym "I" "ACL2"))
(defconst *b2-numeric-types-j* (proof-sym "J" "ACL2"))
(defconst *b2-numeric-types-types*
  (list *library-numberp* *b2-signed-bitwise-bitp* *library-natp*
        *b2-numeric-types-characterp* *proof-integerp* *library-rationalp*
        *b2-numeric-types-stringp*))
(defconst *b2-numeric-types-sums*
  (list (cons *proof-plus* "INTEGER-SUM")
        (cons *proof-times* "INTEGER-PRODUCT")
        (cons *proof-minus* "INTEGER-NEGATION")))

(defun b2-numeric-types-split (lib test prove)
  (proof-with-checked-results ((yes (proof-proof-assume (library-library-proof lib) test t)))
    (if (endp prove)
        (cons (list :call lib yes t) lib)
      (proof-with-checked-results
          ((first (car prove))
           (no (proof-proof-assume (library-library-proof (cdr first)) test nil)))
        (if (endp (cdr prove))
            (cons (list :call (cdr first) no nil) (cdr first))
          (proof-with-checked-results ((second (cadr prove)))
            (let ((lib (cdr second)))
              (proof-with-checked-results
                  ((step (proof-proof-cases (library-library-proof lib) test (car first) (car second))))
                (cons step lib)))))))))

(defmacro b2-numeric-types-with-split (library test formals body)
  (let ((branch `(let ((,(car formals) (cadr (car split-request)))
                       (,(cadr formals) (caddr (car split-request)))
                       (,(caddr formals) (cadddr (car split-request))))
                   ,body)))
    `(let ((split-lib ,library) (split-test ,test))
       (proof-with-checked-results
           ((split-request (b2-numeric-types-split split-lib split-test nil))
            (first-answer ,branch)
            (split-request (b2-numeric-types-split split-lib split-test (list first-answer)))
            (second-answer ,branch))
         (b2-numeric-types-split split-lib split-test (list first-answer second-answer))))))

(defun b2-numeric-types-natural-quotient-zero (evidence lib goal opens)
  (proof-with-checked-results
      ((step (b2-tactics-tactics-solve lib goal evidence opens nil 0 nil)))
    (cons step lib)))

(defun b2-numeric-types-natural-quotient-positive-divisor-integer-dividend-nonnegative-dividend
    (sign-proof is-negative lib dividend-type divisor-type divisor-positive ys bounds goal opens)
  (if is-negative
      (proof-with-checked-results
          ((zero-type (library-library-type-of lib *proof-zero* nil))
           (less (library-library-cite
                  lib "LESS-TRANSITIVE" (list *library-x* *proof-zero* *library-y*)
                  (list dividend-type zero-type divisor-type sign-proof divisor-positive))))
        (b2-numeric-types-natural-quotient-zero
         (append ys (list dividend-type less)) lib goal opens))
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((natural (library-library-cite lib "NATURAL-FROM-BOUNDS" (list *library-x*)
                                          (list dividend-type sign-proof)))
           (condition (b2-signed-bitwise-step-at bounds 1))
           (guard (b2-tactics-tactics-solve
                   lib condition (list natural divisor-type divisor-positive) nil nil 0 nil))
           (consequence (proof-proof-modus-ponens proof bounds guard))
           (result (proof-proof-conjunct proof consequence)))
        (cons (car result) lib)))))

(defun b2-numeric-types-natural-quotient-positive-divisor-integer-dividend
    (dividend-type holds lib divisor-type divisor-positive ys bounds goal opens)
  (if (not holds)
      (b2-numeric-types-natural-quotient-zero (append ys (list dividend-type)) lib goal opens)
    (b2-numeric-types-with-split
     lib (library-lt *library-x* *proof-zero*) (branch-lib sign-proof is-negative)
     (b2-numeric-types-natural-quotient-positive-divisor-integer-dividend-nonnegative-dividend
      sign-proof is-negative branch-lib dividend-type divisor-type divisor-positive ys bounds goal opens))))

(defun b2-numeric-types-natural-quotient-positive-divisor
    (typed nonnegative nonzero lib goal opens)
  (let ((sign (library-positive *library-y*))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opposite (proof-proof-assume proof sign nil))
         (equality (b2-powers-zero-from-signs lib *library-y* typed nonnegative opposite))
         (contradiction (proof-proof-cut proof equality nonzero))
         (divisor-positive (proof-proof-front proof contradiction sign))
         (label (b2-quotients-nonnegative-quotient lib nil))
         (bounds (proof-proof-fact (library-library-proof (cdr label)) (car label) nil)))
      (let ((ys (list typed nonnegative nonzero divisor-positive)))
        (b2-numeric-types-with-split
         (cdr label) (library-integer *library-x*) (branch-lib dividend-type holds)
         (b2-numeric-types-natural-quotient-positive-divisor-integer-dividend
          dividend-type holds branch-lib typed divisor-positive ys bounds goal opens))))))

(defun b2-numeric-types-natural-quotient-integer-divisor-nonnegative-divisor-nonzero-divisor
    (zero-test is-zero lib typed sign-proof goal opens)
  (if is-zero
      (b2-numeric-types-natural-quotient-zero (list typed sign-proof zero-test) lib goal opens)
    (b2-numeric-types-natural-quotient-positive-divisor typed sign-proof zero-test lib goal opens)))

(defun b2-numeric-types-natural-quotient-integer-divisor-nonnegative-divisor
    (sign-proof is-negative lib typed goal opens)
  (if is-negative
      (b2-numeric-types-natural-quotient-zero (list typed sign-proof) lib goal opens)
    (b2-numeric-types-with-split
     lib (proof-eq *library-y* *proof-zero*) (branch-lib zero-test is-zero)
     (b2-numeric-types-natural-quotient-integer-divisor-nonnegative-divisor-nonzero-divisor
      zero-test is-zero branch-lib typed sign-proof goal opens))))

(defun b2-numeric-types-natural-quotient-integer-divisor (typed holds lib goal opens)
  (if (not holds)
      (b2-numeric-types-natural-quotient-zero (list typed) lib goal opens)
    (b2-numeric-types-with-split
     lib (library-lt *library-y* *proof-zero*) (branch-lib sign-proof is-negative)
     (b2-numeric-types-natural-quotient-integer-divisor-nonnegative-divisor
      sign-proof is-negative branch-lib typed goal opens))))

(defun b2-numeric-types-natural-quotient (lib i j)
  (let ((name (proof-sym "B2-QUOTIENT-NATURAL" "ACL2")))
    (proof-with-checked-results
        ((result
          (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
              (cons name lib)
            (let* ((call (list *b2-quotients-niq* *library-x* *library-y*))
                   (goal (list *library-natp* call))
                   (opens (list call *library-natp* *b2-quotients-ifix* *b2-quotients-nfix*)))
              (proof-with-checked-results
                  ((step (b2-numeric-types-with-split
                          lib (library-integer *library-y*) (branch-lib typed holds)
                          (b2-numeric-types-natural-quotient-integer-divisor
                           typed holds branch-lib goal opens))))
                (b2-tactics-tactics-add-lemma (cdr step) "QUOTIENT-NATURAL" (car step) :none))))))
      (let ((lib (cdr result)))
        (proof-with-checked-results
            ((step (proof-proof-fact (library-library-proof lib) name
                                     (list (list *library-x* i) (list *library-y* j)))))
          (cons step lib))))))

(defun b2-numeric-types-fraction-integer-branch (evidence rational lib field stem)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step
          (if rational
              (proof-with-checked-results
                  ((factors (b2-products-rational-factors lib *library-x* evidence)))
                (if (equal field *b2-products-num*) (cadr factors) (car factors)))
            (proof-with-checked-results
                ((equation (library-library-axiom lib (concatenate 'string "COMPLETION-OF-" stem)
                                                  (list *library-x*)))
                 (completion (b2-signed-bitwise-step-at equation 2))
                 (reduction (b2-tactics-tactics-normalize lib completion (list evidence) nil nil 1500 nil))
                 (equation (proof-proof-chain proof equation (list reduction)))
                 (value (b2-signed-bitwise-step-at equation 2))
                 (typed (library-library-type-of lib value nil)))
              (library-library-transport-argument lib typed equation 1)))))
      (cons step lib))))

(defun b2-numeric-types-fraction-integer (lib field value)
  (proof-with-checked-results ((stem (proof-term-at field 2)))
    (let* ((label (concatenate 'string "INTEGERP-" stem))
           (name (proof-sym (concatenate 'string "B2-" label) "ACL2")))
      (proof-with-checked-results
          ((result
            (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                (cons name lib)
              (proof-with-checked-results
                  ((branches (b2-numeric-types-with-split
                              lib (list *library-rationalp* *library-x*) (branch-lib evidence rational)
                              (b2-numeric-types-fraction-integer-branch evidence rational branch-lib field stem))))
                (b2-tactics-tactics-add-lemma (cdr branches) label (car branches) :none)))))
        (let ((lib (cdr result)))
          (proof-with-checked-results
              ((step (proof-proof-fact (library-library-proof lib) name (list (list *library-x* value)))))
            (cons step lib)))))))

(defun b2-numeric-types-predecessor-natural (lib value typed above-zero)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((law (proof-proof-fact proof "integer-discrete" (list (list *library-x* value))))
         (condition (b2-signed-bitwise-step-at law 1))
         (premise (b2-tactics-tactics-solve lib condition (list typed above-zero) nil nil 0 nil))
         (at-least-one (proof-proof-modus-ponens proof law premise)))
      (let ((child (library-plus *proof-neg-one* value)))
        (proof-with-checked-results
            ((equation (library-library-axiom lib "<-ON-OTHERS" (list value *proof-one*)))
             (comparison (b2-signed-bitwise-step-at equation 2))
             (delta (proof-term-at comparison 1))
             (difference (b2-tactics-tactics-linear-equal lib delta child (list typed)))
             (equation (proof-proof-rewrite proof equation difference '(1 2 1)))
             (bound (proof-proof-rewrite proof at-least-one equation '(1 1)))
             (bound (proof-proof-tidy proof bound))
             (child-type (library-library-type-of lib child (list typed))))
          (library-library-cite lib "NATURAL-FROM-BOUNDS" (list child) (list child-type bound)))))))

(defun b2-numeric-types-positive-power-establish-exponent-case
    (equality is-zero lib target call tx px ty nonnegative formula measure child binding)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step
          (if is-zero
              (b2-tactics-tactics-solve lib target (list equality) (list call *b2-powers-zip*) nil 0 nil)
            (let ((test (library-positive *library-y*)))
              (proof-with-checked-results
                  ((opposite (proof-proof-assume proof test nil))
                   (impossible (b2-powers-zero-from-signs lib *library-y* ty nonnegative opposite))
                   (greater (proof-proof-cut proof impossible equality))
                   (greater (proof-proof-front proof greater test))
                   (smaller (library-library-builtin lib 14 *library-y*))
                   (smaller (proof-proof-discharge proof smaller ty))
                   (smaller (proof-proof-discharge proof smaller greater))
                   (inherited (b2-tactics-tactics-induction-hypothesis lib formula measure binding smaller))
                   (natural-child (b2-numeric-types-predecessor-natural lib *library-y* ty greater))
                   (condition (b2-signed-bitwise-step-at inherited 1))
                   (guard (b2-tactics-tactics-solve lib condition (list tx px natural-child) nil nil 0 nil))
                   (conclusion (proof-proof-modus-ponens proof inherited guard))
                   (result-types (proof-proof-conjunct proof conclusion)))
                (let* ((rest (list *b2-powers-expt* *library-x* child))
                       (product (b2-products-product *library-x* rest)))
                  (proof-with-checked-results
                      ((integer-product (library-library-type-of lib product (list tx (car result-types))))
                       (base-rational (library-library-rational lib *library-x* (list tx)))
                       (power-rational (library-library-rational lib rest (list (car result-types))))
                       (above-zero (library-library-cite lib "POSITIVE-PRODUCT" (list *library-x* rest)
                                                         (list base-rational power-rational px (cadr result-types))))
                       (number (library-library-number lib *library-x* (list tx)))
                       (nonzero (b2-tactics-tactics-from-impossible
                                 lib (proof-neg (proof-eq *library-x* *proof-zero*)) px nil nil nil 1500 nil))
                       (equation (b2-powers-open-nonzero-expt lib *library-x* *library-y* ty greater number nonzero))
                       (expansion (b2-signed-bitwise-step-at equation 2))
                       (smaller-power (proof-term-at expansion 2))
                       (actual (proof-term-at smaller-power 2))
                       (reduced (b2-tactics-tactics-linear-equal lib actual child (list ty)))
                       (equation (proof-proof-rewrite proof equation reduced '(1 2 2 2)))
                       (equation (proof-proof-tidy proof equation)))
                    (b2-tactics-tactics-solve
                     lib target (list integer-product above-zero) nil (list equation) 0 nil))))))))
      (cons step lib))))

(defun b2-numeric-types-positive-power-establish (premise lib target call formula measure child binding)
  (proof-with-checked-results
      ((known (b2-tactics-tactics-evidence lib (list premise)))
       (tx (b2-signed-bitwise-known-step known (library-integer *library-x*)))
       (px (b2-signed-bitwise-known-step known (library-positive *library-x*)))
       (ny (b2-signed-bitwise-known-step known (list *library-natp* *library-y*)))
       (ty (library-library-cite lib "NATURAL-INTEGER" (list *library-y*) (list ny)))
       (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE" (list *library-y*) (list ny))))
    (b2-numeric-types-with-split
     lib (proof-eq *library-y* *proof-zero*) (branch-lib equality is-zero)
     (b2-numeric-types-positive-power-establish-exponent-case
      equality is-zero branch-lib target call tx px ty nonnegative formula measure child binding))))

(defun b2-numeric-types-positive-power-build (lib)
  (let ((call (list *b2-powers-expt* *library-x* *library-y*)))
    (proof-with-checked-results
        ((condition (b2-powers-and-terms
                     (list (library-integer *library-x*) (library-positive *library-x*)
                           (list *library-natp* *library-y*))))
         (target (b2-powers-and-terms (list (library-integer call) (library-positive call)))))
      (let* ((formula (list *library-implies* condition target))
             (measure (list *b2-numeric-types-count* *library-y*))
             (child (library-plus *proof-neg-one* *library-y*))
             (binding (list (list *library-y* child))))
        (proof-with-checked-results
            ((request (b2-tactics-tactics-implication lib condition target nil))
             (body (b2-numeric-types-positive-power-establish
                    (nth 3 (car request)) (cdr request) target call formula measure child binding))
             (case-proof (b2-tactics-tactics-implication lib condition target body))
             (ordinal (library-library-builtin (cdr case-proof) 1 *library-y*))
             (induction (proof-proof-induct (library-library-proof (cdr case-proof))
                                            ordinal (car case-proof) formula measure (list binding))))
          (b2-tactics-tactics-add-lemma (cdr case-proof) "POSITIVE-INTEGER-EXPT" induction :none))))))

(defun b2-numeric-types-positive-power (lib base exponent kind above natural)
  (let ((name (proof-sym "B2-POSITIVE-INTEGER-EXPT" "ACL2")))
    (proof-with-checked-results
        ((added (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                    (cons name lib)
                  (b2-numeric-types-positive-power-build lib))))
      (let* ((lib (cdr added))
             (proof (library-library-proof lib)))
        (proof-with-checked-results
            ((step (proof-proof-fact proof name (list (list *library-x* base) (list *library-y* exponent))))
             (condition (b2-signed-bitwise-step-at step 1))
             (premise (b2-tactics-tactics-solve lib condition (list kind above natural) nil nil 0 nil))
             (conclusion (proof-proof-modus-ponens proof step premise))
             (steps (proof-proof-conjunct proof conclusion)))
          (cons steps lib))))))

(defun b2-numeric-types-natural-product-positive-factor (lib term kind not-negative not-zero)
  (let ((test (library-positive term))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opposite (proof-proof-assume proof test nil))
         (equality (b2-powers-zero-from-signs lib term kind not-negative opposite))
         (contradiction (proof-proof-cut proof equality not-zero)))
      (proof-proof-front proof contradiction test))))

(defun b2-numeric-types-natural-product-conclude-left-case-right-case
    (second is-zero-right lib first types weak zero goal product)
  (if is-zero-right
      (proof-with-checked-results
          ((rule (b2-products-zero-product lib *library-x*))
           (step (b2-tactics-tactics-solve (cdr rule) goal (list second zero) nil (list (car rule)) 0 nil)))
        (cons step (cdr rule)))
    (proof-with-checked-results
        ((positive-x (b2-numeric-types-natural-product-positive-factor lib *library-x* (car types) (car weak) first))
         (positive-y (b2-numeric-types-natural-product-positive-factor lib *library-y* (cadr types) (cadr weak) second))
         (rational-x (library-library-rational lib *library-x* types))
         (rational-y (library-library-rational lib *library-y* types))
         (positive-product (library-library-cite lib "POSITIVE-PRODUCT" (list *library-x* *library-y*)
                                                  (list rational-x rational-y positive-x positive-y)))
         (typed (library-library-type-of lib product types))
         (nonnegative (library-library-cite lib "POSITIVE-NONNEGATIVE" (list product) (list typed positive-product)))
         (step (library-library-cite lib "NATURAL-FROM-BOUNDS" (list product) (list typed nonnegative))))
      (cons step lib))))

(defun b2-numeric-types-natural-product-conclude-left-case (first is-zero lib types weak zero goal product)
  (if is-zero
      (proof-with-checked-results
          ((rule (b2-products-zero-left-product lib *library-y*))
           (step (b2-tactics-tactics-solve (cdr rule) goal (list first zero) nil (list (car rule)) 0 nil)))
        (cons step (cdr rule)))
    (b2-numeric-types-with-split
     lib (proof-eq *library-y* *proof-zero*) (branch-lib second is-zero-right)
     (b2-numeric-types-natural-product-conclude-left-case-right-case
      second is-zero-right branch-lib first types weak zero goal product))))

(defun b2-numeric-types-natural-product-conclude (premise lib goal product)
  (proof-with-checked-results
      ((natural (proof-proof-conjunct (library-library-proof lib) premise))
       (integer-x (library-library-cite lib "NATURAL-INTEGER" (list *library-x*) (list (car natural))))
       (integer-y (library-library-cite lib "NATURAL-INTEGER" (list *library-y*) (list (cadr natural))))
       (weak-x (library-library-cite lib "NATURAL-NONNEGATIVE" (list *library-x*) (list (car natural))))
       (weak-y (library-library-cite lib "NATURAL-NONNEGATIVE" (list *library-y*) (list (cadr natural))))
       (zero (library-library-natural lib *proof-zero*)))
    (b2-numeric-types-with-split
     lib (proof-eq *library-x* *proof-zero*) (branch-lib first is-zero)
     (b2-numeric-types-natural-product-conclude-left-case
      first is-zero branch-lib (list integer-x integer-y) (list weak-x weak-y) zero goal product))))

(defun b2-numeric-types-natural-product-build (lib)
  (let* ((product (b2-products-product *library-x* *library-y*))
         (goal (list *library-natp* product)))
    (proof-with-checked-results
        ((condition (b2-powers-and-terms (list (list *library-natp* *library-x*) (list *library-natp* *library-y*))))
         (request (b2-tactics-tactics-implication lib condition goal nil))
         (body (b2-numeric-types-natural-product-conclude (nth 3 (car request)) (cdr request) goal product))
         (lemma (b2-tactics-tactics-implication lib condition goal body)))
      (b2-tactics-tactics-add-lemma (cdr lemma) "NATURAL-PRODUCT" (car lemma) :none))))

(defun b2-numeric-types-natural-product (lib left right natural-left natural-right)
  (let ((name (proof-sym "B2-NATURAL-PRODUCT" "ACL2")))
    (proof-with-checked-results
        ((added (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                    (cons name lib)
                  (b2-numeric-types-natural-product-build lib))))
      (let* ((lib (cdr added))
             (proof (library-library-proof lib)))
        (proof-with-checked-results
            ((statement (proof-proof-fact proof name (list (list *library-x* left) (list *library-y* right))))
             (condition (b2-signed-bitwise-step-at statement 1))
             (premise (b2-tactics-tactics-solve lib condition (list natural-left natural-right) nil nil 0 nil))
             (step (proof-proof-modus-ponens proof statement premise)))
          (cons step lib))))))

(defun b2-numeric-types-types-init (lib)
  (proof-with-checked-results ((search (b2-search-search-init lib 14 nil)))
    (list :b2-numeric-types-types lib search nil 36)))

(defun b2-numeric-types-types-lib (types)
  (cadr types))

(defun b2-numeric-types-types-search (types)
  (caddr types))

(defun b2-numeric-types-types-visited (types)
  (cadddr types))

(defun b2-numeric-types-types-fuel (types)
  (nth 4 types))

(defun b2-numeric-types-types-with-search (types search)
  (update-nth 2 search types))

; Search retains the index made at initialization and looks up facts in the current Library.
(defun b2-numeric-types-types-with-library (types lib)
  (b2-numeric-types-types-with-search
   (update-nth 1 lib types)
   (b2-search-search-with-lib (b2-numeric-types-types-search types) lib)))

(defun b2-numeric-types-types-with-visited (types visited)
  (update-nth 3 visited types))

(defun b2-numeric-types-types-with-fuel (types fuel)
  (update-nth 4 fuel types))

(defun b2-numeric-types-types-library-result (types result)
  (if (failure-p result)
      result
    (cons (car result) (b2-numeric-types-types-with-library types (cdr result)))))

(defun b2-numeric-types-types-fact (types goal known)
  (proof-with-checked-results
      ((result (b2-search-search-fact (b2-numeric-types-types-search types) goal known 0 0))
       (step (car result)))
    (cons step (b2-numeric-types-types-with-search types (cdr result)))))

(defun b2-numeric-types-types-known-natural (types value evidence)
  (let* ((lib (b2-numeric-types-types-lib types))
         (goal (list *library-natp* value)))
    (proof-with-checked-results ((known (b2-tactics-tactics-evidence lib evidence)))
      (let ((entry (assoc-equal goal known)))
        (if entry
            (cons (cdr entry) types)
          (b2-numeric-types-types-fact types goal known))))))

(defun b2-numeric-types-types-definition-size (lib operator)
  (let ((entry (assoc-equal operator (proof-proof-definitions (library-library-proof lib)))))
    (if entry
        (proof-with-checked-results ((body (proof-term-at (cdr entry) 1)))
          (b2-search-size body 120))
      120)))

(defun b2-numeric-types-check-arity (supplied required)
  (if (equal supplied required)
      t
    '(:failure "tactic-rejected" "")))

(mutual-recursion
 (defun b2-numeric-types-types-prove-run (n types predicate value evidence depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-prove-run")
     (let ((goal (list predicate value))
           (lib (b2-numeric-types-types-lib types)))
       (proof-with-checked-results ((known (b2-tactics-tactics-evidence lib evidence)))
         (let ((entry (assoc-equal goal known)))
           (if entry
               (cons (cdr entry) types)
             (proof-with-checked-results ((row (b2-numeric-types-types-fact types goal known)))
               (if (car row)
                   row
                 (let* ((types (cdr row))
                        (fuel (1- (b2-numeric-types-types-fuel types)))
                        (visited (b2-numeric-types-types-visited types)))
                   (if (or (<= depth 0) (< fuel 0) (member-equal goal visited))
                       (b2-tactics-unproved)
                     (let ((types (b2-numeric-types-types-with-visited
                                   (b2-numeric-types-types-with-fuel types fuel)
                                   (cons goal visited))))
                       (proof-with-checked-results
                           ((result (b2-numeric-types-types-infer-run
                                     (1- n) types predicate value (table-values known) depth)))
                         (cons (car result)
                               (b2-numeric-types-types-with-visited (cdr result) visited))))))))))))))

 (defun b2-numeric-types-types-infer-run (n types predicate value evidence depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-infer-run")
     (let* ((lib (b2-numeric-types-types-lib types))
            (proof (library-library-proof lib))
            (goal (list predicate value)))
       (proof-with-checked-results ((operator (b2-search-head value)))
         (cond
          ((proof-is-call value *proof-quote*)
           (proof-with-checked-results
               ((step (b2-tactics-tactics-solve
                       lib goal evidence
                       (if (assoc-equal predicate (proof-proof-definitions proof)) (list predicate) nil)
                       nil 0 nil)))
             (cons step types)))
          ((and (equal operator *b2-floor-intervals-mod*)
                (member-equal predicate (list *library-natp* *b2-signed-bitwise-bitp*)))
           (b2-numeric-types-types-remainder-type-run (1- n) types predicate value evidence depth))
          ((and (equal predicate *b2-numeric-types-stringp*)
                (equal operator *b2-numeric-types-coerce*))
           (proof-with-checked-results
               ((step (b2-tactics-tactics-use-fact
                       lib (list "str" "stringp-coerce") goal evidence nil nil 0 nil)))
             (cons step types)))
          ((and (equal operator *b2-powers-expt*)
                (member-equal predicate (list *proof-integerp* *library-natp*)))
           (proof-with-checked-results
               ((power (b2-numeric-types-types-power-run (1- n) types value evidence depth)))
             (let ((types (cdr power))
                   (typed (caar power)))
               (if (equal predicate *proof-integerp*)
                   (cons typed types)
                 (let ((lib (b2-numeric-types-types-lib types)))
                   (proof-with-checked-results
                       ((bound (library-library-cite lib "POSITIVE-NONNEGATIVE" (list value)
                                                     (list typed (cadar power))))
                        (step (library-library-cite lib "NATURAL-FROM-BOUNDS" (list value)
                                                    (list typed bound))))
                     (cons step types)))))))
          ((and (equal predicate *proof-integerp*) (equal operator *b2-signed-bitwise-logand*))
           (b2-numeric-types-types-logand-run (1- n) types value))
          ((and (equal predicate *proof-integerp*) (assoc-equal operator *b2-numeric-types-sums*))
           (proof-with-checked-results
               ((kinds (b2-numeric-types-types-prove-terms-run
                        (1- n) types *proof-integerp* (cdr value) evidence (1- depth)))
                (step (library-library-cite
                       (b2-numeric-types-types-lib (cdr kinds))
                       (cdr (assoc-equal operator *b2-numeric-types-sums*)) (cdr value) (car kinds))))
             (cons step (cdr kinds))))
          ((and (equal predicate *proof-integerp*)
                (member-equal operator (list *b2-products-num* *b2-products-den*)))
           (proof-with-checked-results ((argument (proof-term-at value 1)))
             (b2-numeric-types-types-library-result
              types (b2-numeric-types-fraction-integer lib operator argument))))
          ((and (equal predicate *proof-integerp*)
                (member-equal operator (list *b2-quotients-nfix* *b2-quotients-niq*)))
           (proof-with-checked-results
               ((natural (b2-numeric-types-types-prove-run (1- n) types *library-natp*
                                                           value evidence (1- depth)))
                (step (library-library-cite (b2-numeric-types-types-lib (cdr natural))
                                            "NATURAL-INTEGER" (list value) (list (car natural)))))
             (cons step (cdr natural))))
          ((and (equal predicate *proof-integerp*)
                (member-equal operator (list *b2-numeric-types-floor* *b2-numeric-types-truncate*)))
           (proof-with-checked-results
               ((arity (b2-numeric-types-check-arity (len value) 3)))
             (b2-numeric-types-types-quotient-integer-run (1- n) types operator (cadr value) (caddr value))))
          ((and (equal predicate *library-natp*) (equal operator *b2-quotients-niq*))
           (proof-with-checked-results
               ((arity (b2-numeric-types-check-arity (len value) 3)))
             (b2-numeric-types-types-library-result
              types (b2-numeric-types-natural-quotient lib (cadr value) (caddr value)))))
          ((and (equal predicate *library-natp*)
                (member-equal operator (list *b2-quotients-nfix* *b2-numeric-types-count* *library-len*)))
           (proof-with-checked-results ((step (b2-measures-measure-natural lib value)))
             (cons step types)))
          ((and (equal predicate *library-natp*) (equal operator *b2-numeric-types-logrev*))
           (b2-numeric-types-types-reversal-run (1- n) types value evidence depth))
          ((and (equal predicate *library-natp*) (equal operator *b2-quotients-ifix*))
           (proof-with-checked-results
               ((argument (proof-term-at value 1))
                (natural (b2-numeric-types-types-prove-run (1- n) types *library-natp* argument evidence (1- depth))))
             (let ((lib (b2-numeric-types-types-lib (cdr natural))))
               (proof-with-checked-results
                   ((typed (library-library-cite lib "NATURAL-INTEGER" (cdr value) (list (car natural))))
                    (equation (b2-tactics-tactics-normalize lib value (list typed) (list value) nil 1500 nil))
                    (step (library-library-transport-argument lib (car natural) equation 1)))
                 (cons step (cdr natural))))))
          ((and (equal predicate *library-natp*) (equal operator *proof-plus*))
           (b2-numeric-types-types-natural-sum-run (1- n) types value evidence depth))
          ((and (equal predicate *library-natp*) (equal operator *proof-times*))
           (proof-with-checked-results
               ((kinds (b2-numeric-types-types-prove-terms-run
                        (1- n) types *library-natp* (cdr value) evidence (1- depth)))
                (arity (b2-numeric-types-check-arity (+ (len value) (len (car kinds))) 5)))
             (let ((types (cdr kinds)))
               (b2-numeric-types-types-library-result
                types (b2-numeric-types-natural-product (b2-numeric-types-types-lib types)
                                                        (cadr value) (caddr value) (caar kinds) (cadar kinds))))))
          (t (b2-numeric-types-types-infer-result-run (1- n) types predicate value evidence depth operator)))))))

 (defun b2-numeric-types-types-infer-result-run (n types predicate value evidence depth operator)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-infer-result-run")
     (proof-with-checked-results
         ((natural (if (equal predicate *proof-integerp*)
                       (b2-numeric-types-types-known-natural types value evidence)
                     (cons nil types))))
       (let* ((types (cdr natural))
              (lib (b2-numeric-types-types-lib types)))
         (cond
          ((car natural)
           (proof-with-checked-results
               ((step (library-library-cite lib "NATURAL-INTEGER" (list value) (list (car natural)))))
             (cons step types)))
          ((and (equal predicate *library-numberp*)
                (or (assoc-equal operator *b2-numeric-types-sums*) (equal operator *b2-products-recip*)))
           (proof-with-checked-results ((step (b2-products-numeric-closure lib value)))
             (cons step types)))
          (t
           (proof-with-checked-results ((size (b2-numeric-types-types-definition-size lib operator)))
             (if (< size 120)
                 (b2-numeric-types-types-by-value-run (1- n) types predicate value evidence depth)
               (b2-tactics-unproved)))))))))

 (defun b2-numeric-types-types-prove-terms-run (n types predicate terms evidence depth)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-numeric-types-types-prove-terms-run"))
    ((endp terms) (cons nil types))
    (t
     (proof-with-checked-results
         ((first (b2-numeric-types-types-prove-run (1- n) types predicate (car terms) evidence depth))
          (rest (b2-numeric-types-types-prove-terms-run (1- n) (cdr first) predicate (cdr terms) evidence depth)))
       (cons (cons (car first) (car rest)) (cdr rest))))))

 (defun b2-numeric-types-types-natural-sum-run (n types value evidence depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-natural-sum-run")
     (proof-with-checked-results ((left (proof-term-at value 1)))
       (if (equal left *proof-neg-one*)
           (proof-with-checked-results
               ((argument (proof-term-at value 2))
                (typed (b2-numeric-types-types-prove-run (1- n) types *proof-integerp* argument evidence (1- depth)))
                (positive (b2-numeric-types-types-positive-run (1- n) (cdr typed) argument evidence (1- depth)))
                (step (b2-numeric-types-predecessor-natural (b2-numeric-types-types-lib (cdr positive))
                                                            argument (car typed) (car positive))))
             (cons step (cdr positive)))
         (proof-with-checked-results
             ((kinds (b2-numeric-types-types-prove-terms-run
                      (1- n) types *library-natp* (cdr value) evidence (1- depth)))
              (step (library-library-cite (b2-numeric-types-types-lib (cdr kinds))
                                          "NATURAL-SUM" (cdr value) (car kinds))))
           (cons step (cdr kinds)))))))

 (defun b2-numeric-types-types-logand-run (n types value)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-logand-run")
     (let ((lib (b2-numeric-types-types-lib types)))
       (proof-with-checked-results
           ((arity (b2-numeric-types-check-arity (len value) 3))
            (result (b2-signed-bitwise-integer-logand lib (cadr value) (caddr value) nil)))
         (if (b2-signed-bitwise-floor-request-p result)
             (let ((request (car result)))
               (proof-with-checked-results
                   ((floor-type (b2-numeric-types-types-floor-run
                                 (1- n) (b2-numeric-types-types-with-library types (caddr request))
                                 (nth 3 request) (nth 4 request))))
                 (b2-numeric-types-types-library-result
                  (cdr floor-type)
                  (b2-signed-bitwise-integer-logand
                   lib (cadr value) (caddr value)
                   (cons (car floor-type) (b2-numeric-types-types-lib (cdr floor-type)))))))
           (b2-numeric-types-types-library-result types result))))))

 (defun b2-numeric-types-types-power-run (n types call evidence depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-power-run")
     (proof-with-checked-results ((call (proof-list-of-length call 3)))
       (let ((base (cadr call))
             (exponent (caddr call)))
         (proof-with-checked-results
             ((typed (b2-numeric-types-types-prove-run
                      (1- n) types *proof-integerp* base evidence (1- depth)))
              (natural (b2-numeric-types-types-prove-run
                        (1- n) (cdr typed) *library-natp* exponent evidence (1- depth)))
              (above (b2-numeric-types-types-positive-run (1- n) (cdr natural) base evidence (1- depth))))
           (let ((types (cdr above)))
             (b2-numeric-types-types-library-result
              types (b2-numeric-types-positive-power (b2-numeric-types-types-lib types)
                                                     base exponent (car typed) (car above) (car natural)))))))))

 (defun b2-numeric-types-types-remainder-type-run (n types predicate value evidence depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-remainder-type-run")
     (proof-with-checked-results ((call (proof-list-of-length value 3)))
       (let ((i (cadr call))
             (j (caddr call))
             (lib (b2-numeric-types-types-lib types)))
         (proof-with-checked-results
             ((equal-two (if (equal predicate *b2-signed-bitwise-bitp*)
                             (b2-tactics-tactics-solve
                              lib (proof-eq j (proof-quote 2)) evidence (list j) nil 0 nil)
                           nil))
              (typed-i (b2-numeric-types-types-prove-run
                        (1- n) types *proof-integerp* i evidence (1- depth)))
              (typed-j (b2-numeric-types-types-prove-run
                        (1- n) (cdr typed-i) *proof-integerp* j evidence (1- depth)))
              (above (b2-numeric-types-types-positive-run (1- n) (cdr typed-j) j evidence (1- depth)))
              (floor (b2-numeric-types-types-floor-run (1- n) (cdr above) i j))
              (remainder (b2-floor-intervals-integer-remainder
                          (b2-numeric-types-types-lib (cdr floor)) i j
                          (car typed-i) (car typed-j) (car above) (car floor))))
           (let ((lib (cdr remainder))
                 (typed (caar remainder))
                 (low (cadar remainder)))
             (proof-with-checked-results
                 ((step (if (not equal-two)
                            (library-library-cite lib "NATURAL-FROM-BOUNDS" (list value) (list typed low))
                          (proof-with-checked-results
                              ((upper (proof-proof-rewrite (library-library-proof lib)
                                                           (caddar remainder) equal-two '(1 2))))
                            (b2-signed-bitwise-bit-from-bounds lib typed low upper)))))
               (cons step (b2-numeric-types-types-with-library (cdr floor) lib)))))))))

 (defun b2-numeric-types-types-reversal-establish
     (n natural types function stop next-call induction test source)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-reversal-establish")
     (let ((lib (b2-numeric-types-types-lib types)))
       (proof-with-checked-results
           ((base (b2-tactics-tactics-normalize lib function (list stop) (list function) nil 1500 nil))
            (value (b2-signed-bitwise-step-at base 2))
            (good (b2-numeric-types-types-prove-run (1- n) types *library-natp* value (list natural) 7))
            (done (library-library-transport-argument (b2-numeric-types-types-lib (cdr good)) (car good) base 1))
            (argument (proof-term-at next-call 3))
            (new-arg (b2-numeric-types-types-prove-run (1- n) (cdr good) *library-natp* argument (list natural) 7)))
         (let* ((types (cdr new-arg))
                (lib (b2-numeric-types-types-lib types))
                (proof (library-library-proof lib)))
           (proof-with-checked-results
               ((step (proof-proof-modus-ponens proof induction (car new-arg)))
                (transported (library-library-transport-argument lib step source 1))
                (result (proof-proof-cases proof test done transported)))
             (cons result types)))))))

 (defun b2-numeric-types-types-reversal-build-run (n types)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-reversal-build-run")
     (let* ((lib (b2-numeric-types-types-lib types))
            (proof (library-library-proof lib))
            (size *b2-numeric-types-size*)
            (variables (list size *b2-numeric-types-i* *b2-numeric-types-j*))
            (function (cons *b2-numeric-types-logrev* variables))
            (condition (list *library-natp* *b2-numeric-types-j*))
            (goal (list *library-natp* function))
            (formula (list *library-implies* condition goal))
            (measure (list *b2-numeric-types-count* size))
            (test (list *b2-numeric-types-zp* size)))
       (proof-with-checked-results
           ((stop (proof-proof-assume proof test t))
            (run (proof-proof-assume proof test nil))
            (source (b2-tactics-tactics-normalize
                     lib function (list run) (list function *b2-numeric-types-the-check*) nil 1500 nil))
            (next-call (b2-signed-bitwise-step-at source 2))
            (binding (seq-zip variables (cdr next-call)))
            (rulers (b2-measures-rulers-init lib (list run)))
            (typed (b2-measures-rulers-require rulers (library-integer size)))
            (positive-size (b2-measures-rulers-require (cdr typed) (library-positive size)))
            (decrease (library-library-builtin lib 14 size))
            (decrease (proof-proof-discharge proof decrease (car typed)))
            (decrease (proof-proof-discharge proof decrease (car positive-size)))
            (induction (b2-tactics-tactics-induction-hypothesis lib formula measure binding decrease))
            (request (b2-tactics-tactics-implication lib condition goal nil))
            (body (b2-numeric-types-types-reversal-establish
                   (1- n) (nth 3 (car request)) (b2-numeric-types-types-with-library types (cdr request))
                   function stop next-call induction test source))
            (lemma (b2-tactics-tactics-implication
                    lib condition goal (cons (car body) (b2-numeric-types-types-lib (cdr body)))))
            (ordinal (library-library-builtin (cdr lemma) 1 size))
            (inductive (proof-proof-induct (library-library-proof (cdr lemma))
                                           ordinal (car lemma) formula measure (list binding))))
         (b2-numeric-types-types-library-result
          (cdr body) (b2-tactics-tactics-add-lemma (cdr lemma) "NATURAL-LOGREV" inductive :none))))))

 (defun b2-numeric-types-types-reversal-run (n types call evidence depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-reversal-run")
     (let* ((lib (b2-numeric-types-types-lib types))
            (name (proof-sym "B2-NATURAL-LOGREV" "ACL2")))
       (proof-with-checked-results
           ((built (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                       (cons name types)
                     (b2-numeric-types-types-reversal-build-run (1- n) types)))
            (rule (proof-proof-fact
                   (library-library-proof (b2-numeric-types-types-lib (cdr built))) name
                   (seq-zip (list *b2-numeric-types-size* *b2-numeric-types-i* *b2-numeric-types-j*)
                           (cdr call))))
            (argument (proof-term-at call 3))
            (natural (b2-numeric-types-types-prove-run (1- n) (cdr built) *library-natp* argument evidence (1- depth)))
            (step (proof-proof-modus-ponens
                   (library-library-proof (b2-numeric-types-types-lib (cdr natural))) rule (car natural))))
         (cons step (cdr natural))))))

 (defun b2-numeric-types-types-positive-open-run (n types value evidence depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-positive-open-run")
     (let ((lib (b2-numeric-types-types-lib types)))
       (proof-with-checked-results
           ((operator (b2-search-head value))
            (size (b2-numeric-types-types-definition-size lib operator)))
         (if (>= size 120)
             (b2-tactics-unproved)
           (proof-with-checked-results
               ((equation (b2-tactics-tactics-normalize lib value evidence (list value) nil 1500 nil)))
             (if (not equation)
                 (b2-tactics-unproved)
               (proof-with-checked-results
                   ((result (b2-signed-bitwise-step-at equation 2))
                    (fact (b2-numeric-types-types-positive-run (1- n) types result evidence (1- depth)))
                    (step (library-library-transport-argument
                           (b2-numeric-types-types-lib (cdr fact)) (car fact) equation 2)))
                 (cons step (cdr fact))))))))))

 (defun b2-numeric-types-types-positive-run (n types value evidence depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-positive-run")
     (let* ((lib (b2-numeric-types-types-lib types))
            (solve (b2-tactics-tactics-solve lib (library-positive value) evidence nil nil 0 nil)))
       (cond
        ((not (failure-p solve)) (cons solve types))
        ((not (b2-tactics-unproved-p solve)) solve)
        ((<= depth 0) (b2-tactics-unproved))
        ((proof-is-call value *b2-powers-expt*)
         (proof-with-checked-results ((power (b2-numeric-types-types-power-run (1- n) types value evidence depth)))
           (cons (cadar power) (cdr power))))
        ((proof-is-call value *b2-quotients-ifix*)
         (proof-with-checked-results
             ((argument (proof-term-at value 1))
              (typed (b2-numeric-types-types-prove-run (1- n) types *proof-integerp* argument evidence (1- depth))))
           (let ((facts (append evidence (list (car typed)))))
             (proof-with-checked-results
                 ((equation (b2-tactics-tactics-normalize
                             (b2-numeric-types-types-lib (cdr typed)) value facts (list value) nil 1500 nil))
                  (fact (b2-numeric-types-types-positive-run (1- n) (cdr typed) argument facts (1- depth)))
                  (right (if equation (b2-signed-bitwise-step-at equation 2) nil)))
               (if (and equation (equal right argument))
                   (proof-with-checked-results
                       ((step (library-library-transport-argument
                               (b2-numeric-types-types-lib (cdr fact)) (car fact) equation 2)))
                     (cons step (cdr fact)))
                 (b2-numeric-types-types-positive-open-run (1- n) (cdr fact) value evidence depth))))))
        (t (b2-numeric-types-types-positive-open-run (1- n) types value evidence depth))))))

 (defun b2-numeric-types-types-by-value-visit-run (n types predicate value evidence depth template tests)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-by-value-visit-run")
     (let ((lib (b2-numeric-types-types-lib types)))
       (cond
        ((proof-is-call value *proof-if*)
         (proof-with-checked-results
             ((branches (proof-list-of-length (cdr value) 3))
              (yes (b2-numeric-types-types-by-value-visit-run
                    (1- n) types predicate (cadr branches) evidence depth template
                    (append tests (list (list (car branches) t)))))
              (no (b2-numeric-types-types-by-value-visit-run
                   (1- n) (cdr yes) predicate (caddr branches) evidence depth template
                   (append tests (list (list (car branches) nil)))))
              (step (b2-signed-bitwise-by-value-join
                     (b2-numeric-types-types-lib (cdr no)) value template (car yes) (car no))))
           (cons step (cdr no))))
        ((and (proof-compound value) (endp value)) '(:failure "tactic-rejected" ""))
        ((and (proof-compound value) (proof-compound (car value)))
         (proof-with-checked-results
             ((equation (proof-proof-beta (library-library-proof lib) value))
              (value (b2-signed-bitwise-step-at equation 2))
              (result (b2-numeric-types-types-by-value-visit-run
                       (1- n) types predicate value evidence depth template tests)))
           (let ((proof (library-library-proof (b2-numeric-types-types-lib (cdr result)))))
             (proof-with-checked-results
                 ((reverse (proof-proof-symmetric proof equation))
                  (step (proof-proof-rewrite-result proof (car result) reverse template *proof-result*)))
               (cons step (cdr result))))))
        (t
         (proof-with-checked-results
             ((result (b2-numeric-types-types-by-value-leaf
                       (1- n) value tests types predicate evidence depth))
              (step (b2-signed-bitwise-by-value-check value template (car result))))
           (cons step (cdr result))))))))

 (defun b2-numeric-types-types-by-value-leaf (n value tests types predicate evidence depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-by-value-leaf")
     (proof-with-checked-results
         ((signed (b2-signed-bitwise-assumptions (b2-numeric-types-types-lib types) tests)))
       (b2-numeric-types-types-prove-run (1- n) types predicate value (append evidence signed) (1- depth)))))

 (defun b2-numeric-types-types-by-value-run (n types predicate call evidence depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-by-value-run")
     (proof-with-checked-results
         ((equation (b2-tactics-tactics-normalize
                     (b2-numeric-types-types-lib types) call evidence (list call) nil 1500 t)))
       (if (not equation)
           (b2-tactics-unproved)
         (let ((template (list predicate *proof-result*)))
           (proof-with-checked-results
               ((value (b2-signed-bitwise-step-at equation 2))
                (typed (b2-numeric-types-types-by-value-visit-run
                        (1- n) types predicate value evidence depth template nil)))
             (let ((proof (library-library-proof (b2-numeric-types-types-lib (cdr typed)))))
               (proof-with-checked-results
                   ((reverse (proof-proof-symmetric proof equation))
                    (step (proof-proof-rewrite-result proof (car typed) reverse template *proof-result*)))
                 (cons step (cdr typed))))))))))

 (defun b2-numeric-types-types-floor-run (n types i j)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-floor-run")
     (b2-numeric-types-types-quotient-integer-run (1- n) types *b2-numeric-types-floor* i j)))

 (defun b2-numeric-types-types-quotient-integer-run (n types operation i j)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-numeric-types-types-quotient-integer-run")
     (proof-with-checked-results ((stem (proof-term-at operation 2)))
       (let* ((lib (b2-numeric-types-types-lib types))
              (label (concatenate 'string "INTEGERP-" stem))
              (name (proof-sym (concatenate 'string "B2-" label) "ACL2")))
         (proof-with-checked-results
             ((result
               (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                   (cons name types)
                 (proof-with-checked-results
                     ((step (b2-numeric-types-types-by-value-run
                             (1- n) types *proof-integerp* (list operation *library-x* *library-y*) nil 10)))
                   (b2-numeric-types-types-library-result
                    (cdr step) (b2-tactics-tactics-add-lemma (b2-numeric-types-types-lib (cdr step))
                                                            label (car step) :none)))))
              (step (proof-proof-fact
                     (library-library-proof (b2-numeric-types-types-lib (cdr result))) name
                     (list (list *library-x* i) (list *library-y* j)))))
           (cons step (cdr result))))))))

(defun b2-numeric-types-types-prove (types predicate value evidence depth)
  (b2-numeric-types-types-prove-run 1000000 types predicate value evidence depth))

(defun b2-numeric-types-types-infer (types predicate value evidence depth)
  (b2-numeric-types-types-infer-run 1000000 types predicate value evidence depth))

(defun b2-numeric-types-types-power (types call evidence depth)
  (b2-numeric-types-types-power-run 1000000 types call evidence depth))

(defun b2-numeric-types-types-remainder-type (types predicate value evidence depth)
  (b2-numeric-types-types-remainder-type-run 1000000 types predicate value evidence depth))

(defun b2-numeric-types-types-reversal (types call evidence depth)
  (b2-numeric-types-types-reversal-run 1000000 types call evidence depth))

(defun b2-numeric-types-types-positive (types value evidence depth)
  (b2-numeric-types-types-positive-run 1000000 types value evidence depth))

(defun b2-numeric-types-types-by-value (types predicate call evidence depth)
  (b2-numeric-types-types-by-value-run 1000000 types predicate call evidence depth))

(defun b2-numeric-types-types-floor (types i j)
  (b2-numeric-types-types-floor-run 1000000 types i j))

(defun b2-numeric-types-types-quotient-integer (types operation i j)
  (b2-numeric-types-types-quotient-integer-run 1000000 types operation i j))

(defun b2-numeric-types-type-theorem-lambda (lib result target equation)
  (if (and (not equation) (proof-compound result) (proof-is-call (car result) (proof-cl "LAMBDA")))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((beta (proof-proof-beta proof result))
             (body (b2-signed-bitwise-step-at beta 2))
             (test (if (proof-is-call body *proof-if*) (proof-term-at body 1) nil)))
          (if (proof-is-call test *proof-integerp*)
              (proof-with-checked-results
                  ((term (proof-term-at test 1))
                   (natural (list *library-natp* term))
                   (definition (proof-proof-unfold proof natural))
                   (defined (b2-signed-bitwise-step-at definition 2)))
                (if (equal defined body)
                    (proof-with-checked-results
                        ((reverse (proof-proof-symmetric proof definition))
                         (equation (proof-proof-chain proof beta (list reverse))))
                      (list natural equation))
                  (list target equation)))
            (list target equation))))
    (list target equation)))

(defun b2-numeric-types-type-theorem-establish (evidence types target equation)
  (proof-with-checked-results
      ((result (b2-numeric-types-types-prove types (car target) (cadr target) evidence 7)))
    (let ((lib (b2-numeric-types-types-lib (cdr result))))
      (proof-with-checked-results
          ((step (if equation
                     (proof-proof-transport (library-library-proof lib) (car result) equation)
                   (car result))))
        (cons step lib)))))

(defun b2-numeric-types-type-theorem (lib formula)
  (proof-with-checked-results
      ((forms (if (proof-is-call formula *library-implies*)
                  (proof-list-of-length (cdr formula) 2)
                (list :none formula))))
    (let ((condition (car forms))
          (result (cadr forms)))
      (proof-with-checked-results
          ((beta-target (b2-search-beta-predicate result))
           (target (or beta-target result))
           (equation (if (equal target result) nil (proof-proof-beta (library-library-proof lib) result)))
           (reduced (b2-numeric-types-type-theorem-lambda lib result target equation)))
        (let ((target (car reduced))
              (equation (cadr reduced)))
          (if (and (proof-compound target) (equal (len target) 2)
                   (member-equal (car target) *b2-numeric-types-types*)
                   (proof-compound (cadr target)))
              (proof-with-checked-results ((types (b2-numeric-types-types-init lib)))
                (if (eq condition :none)
                    (b2-numeric-types-type-theorem-establish nil types target equation)
                  (proof-with-checked-results
                      ((request (b2-tactics-tactics-implication lib condition result nil))
                       (evidence (b2-search-search-extend
                                  (b2-numeric-types-types-search types) (nth 3 (car request))))
                       (body (b2-numeric-types-type-theorem-establish evidence types target equation)))
                    (b2-tactics-tactics-implication lib condition result body))))
            (b2-tactics-unproved)))))))
