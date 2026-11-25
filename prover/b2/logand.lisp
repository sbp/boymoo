(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-logand-logand* (proof-sym "BINARY-LOGAND" "ACL2"))
(defconst *b2-logand-even* (proof-cl "EVENP"))
(defconst *b2-logand-two* (proof-quote 2))

(defun b2-logand-weak-parts (step)
  (proof-with-checked-results
      ((first (b2-removal-first step))
       (negative (proof-list-of-length first 2)))
    (proof-list-of-length (cadr negative) 3)))

(defun b2-logand-nonnegative-difference (library weak)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((parts (b2-logand-weak-parts weak))
         (equation (library-library-axiom library "<-ON-OTHERS"
                                           (list (cadr parts) (caddr parts))))
         (rewritten (proof-proof-rewrite proof weak equation '(1 1))))
      (proof-proof-tidy proof rewritten))))

(defun b2-logand-weak-chain (library left right types)
  (proof-with-checked-results
      ((left-parts (b2-logand-weak-parts left))
       (a (caddr left-parts))
       (b (cadr left-parts))
       (right-parts (b2-logand-weak-parts right))
       (c (cadr right-parts))
       (d1 (library-diff b a))
       (d2 (library-diff c b))
       (d1-type (library-library-type-of library d1 types))
       (d2-type (library-library-type-of library d2 types))
       (left-positive (b2-logand-nonnegative-difference library left))
       (right-positive (b2-logand-nonnegative-difference library right))
       (total (library-library-cite library "NONNEGATIVE-SUM" (list d1 d2)
                                    (list d1-type d2-type left-positive right-positive))))
    (b2-tactics-tactics-weak-from-difference library a c total types)))

(defun b2-logand-weak-shift (library bound amount types)
  (proof-with-checked-results
      ((parts (b2-logand-weak-parts bound))
       (nonnegative (b2-logand-nonnegative-difference library bound)))
    (b2-tactics-tactics-weak-from-difference library
                                           (library-plus (caddr parts) amount)
                                           (library-plus (cadr parts) amount)
                                           nonnegative types)))

(defun b2-logand-distinct-bound (library weak different types)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((parts (b2-logand-weak-parts weak))
         (b (cadr parts))
         (a (caddr parts))
         (d (library-diff b a))
         (test (library-lt a b))
         (impossible (proof-proof-assume proof test nil))
         (comparison (library-library-comparison library a b types))
         (rewritten (proof-proof-rewrite proof impossible comparison '(1 1)))
         (nonpositive (proof-proof-tidy proof rewritten))
         (d-type (library-library-type-of library d types))
         (nonnegative (b2-logand-nonnegative-difference library weak))
         (zero (b2-powers-zero-from-signs library d d-type nonnegative nonpositive))
         (result (b2-tactics-tactics-linear-equal library (library-plus d a) b types))
         (result (proof-proof-rewrite proof result zero '(1 1 1)))
         (a-type (library-library-type-of library a types))
         (addition (library-library-cite library "ADD-ZERO-LEFT" (list a) (list a-type)))
         (result (proof-proof-rewrite proof result addition '(1 1)))
         (result (proof-proof-tidy proof result))
         (reverse (proof-proof-symmetric proof result))
         (cut (proof-proof-cut proof reverse different)))
      (proof-proof-front proof cut test))))

(defun b2-logand-odd-lower-bound (library upper odd quotient quotient-type types)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((parts (b2-logand-weak-parts upper))
         (value (cadr parts))
         (doubled (caddr parts))
         (presumed (proof-eq value doubled))
         (yes (proof-proof-assume proof presumed t))
         (reciprocated (list *b2-products-recip* *b2-logand-two*))
         (equation (proof-proof-reflexive proof (b2-products-product value reciprocated)))
         (equation (proof-proof-rewrite proof equation yes '(1 2 1)))
         (associate (library-library-axiom library "ASSOCIATIVITY-OF-*"
                                            (list *b2-logand-two* quotient reciprocated)))
         (commute (library-library-axiom library "COMMUTATIVITY-OF-*"
                                          (list *b2-logand-two*
                                                (b2-products-product quotient reciprocated))))
         (reassociate (library-library-axiom library "ASSOCIATIVITY-OF-*"
                                              (list quotient reciprocated *b2-logand-two*)))
         (equation (proof-proof-chain proof equation (list associate commute reassociate)))
         (unit-two (b2-tactics-tactics-normalize
                    library (b2-products-product reciprocated *b2-logand-two*)
                    nil nil nil 1500 nil))
         (equation (if unit-two (proof-proof-rewrite proof equation unit-two '(1 2 2))
                     (b2-removal-first unit-two)))
         (commute (library-library-axiom library "COMMUTATIVITY-OF-*" (list quotient *proof-one*)))
         (numeric (library-library-number library quotient (list quotient-type)))
         (unit (b2-products-multiplicative-unit library quotient numeric))
         (unit (proof-proof-chain proof commute (list unit)))
         (equation (proof-proof-chain proof equation (list unit)))
         (typed (library-library-transport-argument library quotient-type equation 1))
         (opened (proof-proof-unfold proof (list *b2-logand-even* value)))
         (even (proof-proof-transport proof typed opened))
         (cut (proof-proof-cut proof even odd))
         (different (proof-proof-front proof cut (proof-neg presumed)))
         (smaller (b2-logand-distinct-bound library upper different types))
         (next-weak (b2-butlast-integer-after-successor library smaller types))
         (commuted (library-library-axiom library "COMMUTATIVITY-OF-+" (list *proof-one* doubled)))
         (rewritten (proof-proof-rewrite proof next-weak commuted '(1 1 2))))
      (proof-proof-tidy proof rewritten))))

(defun b2-logand-logand-bounds-consequent-leaf-branch-upper
    (library digit tests doubled doubled-weak bound quotient quotient-type types)
  (let ((proof (library-library-proof library)))
    (if (equal digit *proof-zero*)
        (proof-with-checked-results
            ((doubled-type (library-library-type-of library doubled types))
             (shorter (library-library-cite library "ADD-ZERO-RIGHT" (list doubled) (list doubled-type)))
             (chain (b2-logand-weak-chain library doubled-weak bound types))
             (reverse (proof-proof-symmetric proof shorter))
             (rewritten (proof-proof-rewrite proof chain reverse '(1 1 2))))
          (proof-proof-tidy proof rewritten))
      (proof-with-checked-results
          ((known (b2-tactics-tactics-evidence library tests))
           (odd (b2-powers-evidence-step known (proof-neg (list *b2-logand-even* *library-y*))))
           (lifted (b2-logand-odd-lower-bound library bound odd quotient quotient-type types))
           (shifted (b2-logand-weak-shift library doubled-weak *proof-one* types)))
        (b2-logand-weak-chain library shifted lifted types)))))

(defun b2-logand-logand-bounds-consequent-leaf-branch
    (tests library value doubled bit template types nonnegative doubled-weak bound quotient quotient-type)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((equation (b2-tactics-tactics-normalize library bit tests nil nil 1500 nil))
         (digit (b2-removal-right equation))
         (result (library-plus doubled digit))
         (integer-result (library-library-type-of library result types))
         (doubled-type (library-library-type-of library doubled types))
         (digit-type (library-library-type-of library digit nil))
         (digit-nonnegative (b2-tactics-tactics-solve
                             library (proof-neg (library-lt digit *proof-zero*)) nil nil nil 0 nil))
         (lower (library-library-cite library "NONNEGATIVE-SUM" (list digit doubled)
                                      (list doubled-type digit-type nonnegative digit-nonnegative)))
         (upper (b2-logand-logand-bounds-consequent-leaf-branch-upper
                 library digit tests doubled doubled-weak bound quotient quotient-type types))
         (goal (proof-subst template (list (cons *proof-result* result))))
         (step (b2-tactics-tactics-solve
                library goal (list integer-result lower upper) nil nil 0 nil))
         (reflexive (proof-proof-reflexive proof value))
         (body (proof-proof-rewrite proof reflexive equation '(1 2 2)))
         (reverse (proof-proof-symmetric proof body)))
      (proof-proof-rewrite-result proof step reverse template *proof-result*))))

(defun b2-logand-logand-bounds-branches
    (n library conditions replies value doubled bit template types nonnegative
       doubled-weak bound quotient quotient-type)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "b2-logand-logand-bounds-branches")
    (proof-with-checked-results ((result (b2-removal-tests library conditions replies nil)))
      (if (b2-removal-tests-request-p result)
          (let ((current (caddr result)))
            (proof-with-checked-results
                ((reply (b2-logand-logand-bounds-consequent-leaf-branch
                         (cadr result) current value doubled bit template
                         types nonnegative doubled-weak bound quotient quotient-type)))
              (b2-logand-logand-bounds-branches
               (1- n) library conditions (append replies (list (cons reply current))) value
               doubled bit template types nonnegative doubled-weak bound quotient quotient-type)))
        result))))

(defun b2-logand-logand-bounds-recursive-leaf
    (library value known template formula measure bindings quotient int-y ge-y)
  (let* ((proof (library-library-proof library))
         (pos-y (library-positive *library-y*))
         (zip-test (list *b2-powers-zip* *library-y*)))
    (proof-with-checked-results
        ((nonzip (b2-powers-evidence-step known (proof-neg zip-test)))
         (nonzero (b2-tactics-tactics-from-impossible
                   library (proof-neg (proof-eq *library-y* *proof-zero*)) nonzip nil
                   (list *b2-powers-zip*) nil 1500 nil))
         (assumed (proof-proof-assume proof pos-y nil))
         (zero (b2-powers-zero-from-signs library *library-y* int-y ge-y assumed))
         (cut (proof-proof-cut proof zero nonzero))
         (positive-y (proof-proof-front proof cut pos-y))
         (positive-two (b2-tactics-tactics-solve
                        library (library-positive *b2-logand-two*) nil nil nil 0 nil))
         (two-type (library-library-type-of library *b2-logand-two* nil))
         (one-less (b2-tactics-tactics-solve
                    library (library-lt *proof-one* *b2-logand-two*) nil nil nil 0 nil))
         (descent (b2-quotients-floor-descent library *library-y* *b2-logand-two*
                                              int-y two-type positive-y positive-two one-less))
         (library (cdr descent))
         (proof (library-library-proof library))
         (natural (caar descent))
         (less (cadar descent))
         (bound (caddar descent))
         (int-j (library-library-cite library "NATURAL-INTEGER" (list quotient) (list natural)))
         (ge-j (library-library-cite library "NATURAL-NONNEGATIVE" (list quotient) (list natural)))
         (count-y (b2-powers-integer-count library *library-y* int-y ge-y))
         (smaller (library-library-transport-argument library less count-y 2))
         (count-j (b2-powers-integer-count library quotient int-j ge-j))
         (smaller (library-library-transport-argument library smaller count-j 1))
         (comparison (library-library-ordinal-comparison library (list *library-count* quotient) measure))
         (smaller (proof-proof-transport proof smaller comparison))
         (hypothesis (b2-tactics-tactics-induction-hypothesis library formula measure bindings smaller))
         (child-proof (proof-proof-modus-ponens proof hypothesis natural))
         (child-parts (proof-proof-conjunct proof child-proof))
         (child-int (car child-parts))
         (bounds (proof-proof-conjunct proof (cadr child-parts)))
         (types (list int-y int-j child-int))
         (doubled-weak (b2-quotients-scaled library (cadr bounds) *b2-logand-two* positive-two types nil))
         (library (cdr doubled-weak))
         (nonnegative (b2-quotients-scaled library (car bounds) *b2-logand-two* positive-two types nil))
         (library (cdr nonnegative))
         (zero-product (b2-products-zero-product library *b2-logand-two*))
         (library (cdr zero-product))
         (proof (library-library-proof library))
         (nonnegative (proof-proof-rewrite proof (car nonnegative) (car zero-product) '(1 1 2)))
         (nonnegative (proof-proof-tidy proof nonnegative))
         (parts (proof-list-of-length value 3)))
      (b2-logand-logand-bounds-branches
       1000000 library (list (list *b2-logand-even* *library-x*) (list *b2-logand-even* *library-y*))
       nil value (cadr parts) (caddr parts) template types nonnegative
       (car doubled-weak) bound quotient int-j))))

(defun b2-logand-logand-bounds-consequent-leaf
    (value signed library template formula measure bindings quotient int-y ge-y)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((target (proof-subst template (list (cons *proof-result* value))))
         (assumptions (b2-removal-assumptions proof signed))
         (known (b2-tactics-tactics-evidence library assumptions)))
      (cond
       ((equal value *proof-zero*)
        (proof-with-checked-results
            ((step (b2-tactics-tactics-solve library target (list ge-y) nil nil 0 nil)))
          (cons step library)))
       ((equal value *library-y*)
        (proof-with-checked-results
            ((weak (library-library-cite library "WEAK-REFLEXIVE" (list *library-y*) (list int-y)))
             (step (b2-tactics-tactics-solve library target (list int-y ge-y weak) nil nil 0 nil)))
          (cons step library)))
       ((equal value *library-x*)
        (proof-with-checked-results
            ((same (b2-powers-evidence-step known (proof-eq *library-y* *proof-neg-one*)))
             (first (b2-removal-first ge-y))
             (false (b2-tactics-tactics-normalize library first (list same) nil nil 1500 nil))
             (rewritten (if false (proof-proof-rewrite proof ge-y false '(1))
                          (b2-removal-first false)))
             (contradiction (proof-proof-tidy proof rewritten))
             (step (proof-proof-subsume proof contradiction (cons target (proof-step-clause contradiction)))))
          (cons step library)))
       (t (b2-logand-logand-bounds-recursive-leaf
           library value known template formula measure bindings quotient int-y ge-y))))))

(defun b2-logand-logand-bounds-by-value
    (n library value template signed formula measure bindings quotient int-y ge-y)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof library)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "b2-logand-logand-bounds-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((parts (proof-list-of-length (cdr value) 3))
           (test (car parts))
           (yes (b2-logand-logand-bounds-by-value
                 (1- n) library (cadr parts) template (append signed (list (list test t)))
                 formula measure bindings quotient int-y ge-y))
           (no (b2-logand-logand-bounds-by-value
                (1- n) (cdr yes) (caddr parts) template (append signed (list (list test nil)))
                formula measure bindings quotient int-y ge-y))
           (library (cdr no))
           (step (proof-by-value-join (library-library-proof library) value template (car yes) (car no))))
        (cons step library)))
     ((and (proof-compound value) (endp value))
      '(:failure "tactic-rejected" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (opened (b2-removal-right equality))
           (body (b2-logand-logand-bounds-by-value
                  (1- n) library opened template signed formula measure bindings quotient int-y ge-y))
           (library (cdr body))
           (proof (library-library-proof library))
           (reverse (proof-proof-symmetric proof equality))
           (step (proof-proof-rewrite-result proof (car body) reverse template *proof-result*)))
        (cons step library)))
     (t
      (proof-with-checked-results
          ((result (b2-logand-logand-bounds-consequent-leaf
                    value signed library template formula measure bindings quotient int-y ge-y))
           (first (b2-removal-first (car result)))
           (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal first target) result '(:failure "tactic-rejected" "")))))))

(defun b2-logand-logand-bounds-consequent
    (natural-y library opened template formula measure bindings quotient)
  (proof-with-checked-results
      ((int-y (library-library-cite library "NATURAL-INTEGER" (list *library-y*) (list natural-y)))
       (ge-y (library-library-cite library "NATURAL-NONNEGATIVE" (list *library-y*) (list natural-y)))
       (rhs (b2-removal-right opened))
       (body (b2-logand-logand-bounds-by-value
              1000000 library rhs template nil formula measure bindings quotient int-y ge-y))
       (library (cdr body))
       (proof (library-library-proof library))
       (reverse (proof-proof-symmetric proof opened))
       (step (proof-proof-rewrite-result proof (car body) reverse template *proof-result*)))
    (cons step library)))

(defun b2-logand-logand-bounds (library)
  (let ((label (proof-sym "B2-LOGAND-BOUNDS" "ACL2"))
        (proof (library-library-proof library)))
    (if (assoc-equal label (proof-proof-facts proof))
        (cons label library)
      (let ((call (list *b2-logand-logand* *library-x* *library-y*))
            (condition (list *library-natp* *library-y*))
            (measure (list *library-count* *library-y*)))
        (proof-with-checked-results
            ((template (b2-powers-and-terms
                        (list (library-integer *proof-result*)
                              (proof-neg (library-lt *proof-result* *proof-zero*))
                              (library-le *proof-result* *library-y*))))
             (goal (proof-subst template (list (cons *proof-result* call))))
             (formula (list *library-implies* condition goal))
             (i (list *b2-quotients-floor* *library-x* *b2-logand-two*))
             (j (list *b2-quotients-floor* *library-y* *b2-logand-two*))
             (bindings (list (list *library-x* i) (list *library-y* j)))
             (opened (proof-proof-unfold proof call))
             (request (b2-tactics-tactics-implication library condition goal nil))
             (reply (b2-logand-logand-bounds-consequent
                     (nth 3 (car request)) (cdr request) opened template formula measure bindings j))
             (case-proof (b2-tactics-tactics-implication library condition goal reply))
             (library (cdr case-proof))
             (ordinal (library-library-builtin library 1 *library-y*))
             (step (proof-proof-induct (library-library-proof library)
                                       ordinal (car case-proof) formula measure (list bindings))))
          (b2-tactics-tactics-add-lemma library "LOGAND-BOUNDS" step :none))))))

(defun b2-logand-prove-logand-consequent (premise library helper name)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((values (b2-tactics-tactics-evidence library (list premise)))
         (typed (b2-powers-evidence-step values (library-integer *library-y*)))
         (nonnegative (b2-powers-evidence-step values (proof-neg (library-lt *library-y* *proof-zero*))))
         (natural (b2-quotients-natural-proof library *library-y* typed nonnegative))
         (law (proof-proof-fact proof helper nil))
         (eliminated (proof-proof-modus-ponens proof law natural))
         (conjuncts (proof-proof-conjunct proof eliminated))
         (bounds (proof-proof-conjunct proof (cadr conjuncts))))
      (cons (if (equal name (proof-sym "ONE" "ACL2")) (car bounds) (cadr bounds))
            library))))

(defun b2-logand-prove-logand (library name formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (test (cadr parts))
       (goal (caddr parts))
       (helper (b2-logand-logand-bounds library))
       (library (cdr helper))
       (request (b2-tactics-tactics-implication library test goal nil))
       (reply (b2-logand-prove-logand-consequent
               (nth 3 (car request)) (cdr request) (car helper) name)))
    (b2-tactics-tactics-implication library test goal reply)))
