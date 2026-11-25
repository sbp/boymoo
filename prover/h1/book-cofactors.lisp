(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-book-cofactors-cofactors* (proof-sym "H1-COFACTORS" "ACL2"))
(defconst *h1-book-cofactors-posp* (proof-sym "POSP" "ACL2"))
(defconst *h1-book-cofactors-lambda* (proof-cl "LAMBDA"))

(defun h1-book-cofactors-combine (terms)
  (cond ((endp terms) '(:failure "failure" ""))
        ((endp (cdr terms)) (car terms))
        (t (proof-with-checked-results
            ((rest (h1-book-cofactors-combine (cdr terms))))
            (proof-ite (car terms) rest *proof-false*)))))

(defun h1-book-cofactors-components-collect (n limit lib statement)
  (declare (xargs :measure (nfix n)))
  (cond
   ((eql limit 0) nil)
   ((zp n) '(:failure "fuel" "h1-book-cofactors-components-collect"))
   (t (proof-with-checked-results ((literal (proof-step-first statement)))
        (if (not (proof-is-call literal *proof-if*))
            (list statement)
          (proof-with-checked-results ((otherwise (proof-term-at literal 3)))
            (if (not (equal otherwise *proof-false*))
                (list statement)
              (proof-with-checked-results
                  ((parts (h1-propositions-propositional-proof-conjunct lib statement))
                   (rest (h1-book-cofactors-components-collect
                          (1- n) (if (eq limit :none) :none (1- limit)) lib (cadr parts))))
                (cons (car parts) rest)))))))))

(defun h1-book-cofactors-components (proof statement)
  (h1-book-cofactors-components-collect
   1000000 :none (h1-tactics-prover-library proof) statement))

(defun h1-book-cofactors-tuple-of (g a b)
  (list *proof-cons* g (list *proof-cons* a (list *proof-cons* b *proof-false*))))

(defun h1-book-cofactors-tuple-terms (value)
  (let* ((tail (list *library-cdr* value))
         (rest (list *library-cdr* tail)))
    (list (list *library-car* value) (list *library-car* tail) (list *library-car* rest))))

(defun h1-book-cofactors-positive-parts (proof statement)
  (let ((lib (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((literal (proof-step-first statement))
         (equation (proof-proof-unfold core literal))
         (rewritten (proof-proof-rewrite core statement equation '(1))))
      (h1-propositions-propositional-proof-conjunct lib rewritten))))

(defun h1-book-cofactors-positive-integer (proof term integral sign)
  (let ((lib (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((equation (proof-proof-unfold core (list *h1-book-cofactors-posp* term)))
         (literal (proof-step-first equation))
         (body (proof-term-at literal 2))
         (supplied (h1-propositions-propositional-proof-conjoin lib body integral sign)))
      (h1-propositions-proof-transport core supplied equation))))

(defun h1-book-cofactors-measure-of (a b)
  (library-plus (list *library-nfix* a) (list *library-nfix* b)))

(defun h1-book-cofactors-natural-measure (proof a b)
  (let ((lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((left (library-library-cite lib "NFIX-NATURAL" (list a) nil))
         (right (library-library-cite lib "NFIX-NATURAL" (list b) nil)))
      (library-library-cite lib "NATURAL-SUM"
                            (list (list *library-nfix* a) (list *library-nfix* b))
                            (list left right)))))

(defun h1-book-cofactors-measure-value-argument (term evidence index proof result)
  (let ((lib (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((parts (h1-book-cofactors-positive-parts proof evidence))
         (nonnegative (library-library-cite lib "POSITIVE-NONNEGATIVE" (list term) parts))
         (natural (library-library-cite lib "NATURAL-FROM-BOUNDS" (list term)
                                         (list (car parts) nonnegative)))
         (opened (proof-proof-unfold core (list *library-nfix* term)))
         (expansion (h1-propositions-select-value lib opened natural)))
      (proof-proof-rewrite core result expansion (list 1 2 index)))))

(defun h1-book-cofactors-measure-value-args (args evidence index proof result)
  (declare (xargs :measure (acl2-count args)))
  (cond ((failure-p result) result)
        ((or (endp args) (endp evidence))
         (proof-proof-tidy (h1-tactics-prover-proof proof) result))
        (t (h1-book-cofactors-measure-value-args
            (cdr args) (cdr evidence) (1+ index) proof
            (h1-book-cofactors-measure-value-argument
             (car args) (car evidence) index proof result)))))

(defun h1-book-cofactors-measure-value (proof args evidence)
  (if (not (equal (len args) 2))
      '(:failure "failure" "")
    (proof-with-checked-results
        ((result (h1-propositions-propositional-proof-reflexive
                  (h1-tactics-prover-library proof)
                  (h1-book-cofactors-measure-of (car args) (cadr args)))))
      (h1-book-cofactors-measure-value-args args evidence 1 proof result))))

(defun h1-book-cofactors-positive-difference (proof norm smaller greater bound)
  (proof-with-checked-results
      ((literal (proof-step-first bound))
       (relation (h1-book-order-by-difference
                  proof (library-positive (library-diff greater smaller)) literal
                  (h1-book-arithmetic-algebra-with-work norm 150)))
       (step (car relation))
       (positive (h1-propositions-proof-transport (h1-tactics-prover-proof proof) bound step)))
    (cons positive (cdr relation))))

(defun h1-book-cofactors-positive-pair (proof norm)
  (proof-with-checked-results
      ((left (h1-book-field-require norm (list *h1-book-cofactors-posp* *library-x*)))
       (right (h1-book-field-require (cdr left) (list *h1-book-cofactors-posp* *library-y*)))
       (left-parts (h1-book-cofactors-positive-parts proof (car left)))
       (right-parts (h1-book-cofactors-positive-parts proof (car right)))
       (updated (h1-book-field-remember (cdr right) (append left-parts right-parts))))
    (cons (list (car left) (car right)) updated)))

(defun h1-book-cofactors-child-positive (proof norm args pair)
  (proof-with-checked-results ((first (proof-term-at args 0)))
    (let* ((index (if (equal first *library-x*) 1 0))
           (smaller (if (equal index 1) *library-x* *library-y*))
           (larger (if (equal index 1) *library-y* *library-x*)))
      (proof-with-checked-results
          ((changed (proof-term-at args index))
           (bound (h1-book-field-require norm (library-lt smaller larger)))
           (sign (h1-book-cofactors-positive-difference proof (cdr bound)
                                                         smaller larger (car bound)))
           (integral (h1-book-field-require (cdr sign) (library-integer changed)))
           (child (h1-book-cofactors-positive-integer proof changed (car integral) (car sign))))
        (if (< index (len pair))
            (cons (list index (update-nth index child pair)) (cdr integral))
          '(:failure "failure" ""))))))

(defun h1-book-cofactors-rewrite-measures (core step measures index)
  (declare (xargs :measure (acl2-count measures)))
  (if (or (failure-p step) (endp measures))
      step
    (h1-book-cofactors-rewrite-measures
     core
     (proof-with-checked-results ((reversed (h1-propositions-proof-symmetric core (car measures))))
       (proof-proof-rewrite core step reversed (list 1 index)))
     (cdr measures) (1+ index))))

(defun h1-book-cofactors-descent-proof (proof call)
  (let ((lib (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof))
        (actuals (termination-call-actuals call))
        (parents (list *library-x* *library-y*)))
    (proof-with-checked-results
        ((norm (h1-book-field-field-normalizer proof (termination-call-tests call)))
         (pair (h1-book-cofactors-positive-pair proof norm))
         (child (h1-book-cofactors-child-positive proof (cdr pair) actuals (car pair))))
      (let ((decrease-by (if (equal (caar child) 1) *library-x* *library-y*)))
        (if (not (equal (len actuals) 2))
            '(:failure "failure" "")
          (proof-with-checked-results
              ((relation (h1-book-order-by-difference
                          proof
                          (library-lt (library-plus (car actuals) (cadr actuals))
                                      (library-plus *library-x* *library-y*))
                          (library-positive decrease-by)
                          (h1-book-arithmetic-algebra-with-work (cdr child) 150)))
               (comparison (car relation))
               (positive (h1-book-field-require (cdr relation) (library-positive decrease-by)))
               (smaller (h1-propositions-proof-transport core (car positive) comparison))
               (child-measure (h1-book-cofactors-measure-value proof actuals (cadar child)))
               (parent-measure (h1-book-cofactors-measure-value proof parents (car pair)))
               (decrease (h1-book-cofactors-rewrite-measures
                          core smaller (list child-measure parent-measure) 1))
               (literal (proof-step-first decrease))
               (measures (proof-list-of-length (cdr literal) 2))
               (child-natural (h1-book-cofactors-natural-measure proof (car actuals) (cadr actuals)))
               (early (library-library-cite lib "NATURAL-INTEGER"
                                            (list (car measures)) (list child-natural)))
               (parent-natural (h1-book-cofactors-natural-measure proof *library-x* *library-y*))
               (late (library-library-cite lib "NATURAL-INTEGER"
                                           (list (cadr measures)) (list parent-natural)))
               (order (library-library-cite lib "FINITE-ORDER" measures (list early late))))
            (h1-propositions-proof-transport core decrease order)))))))

(defun h1-book-cofactors-definition ()
  (let* ((local (proof-sym "H1-COFACTOR-TUPLE" "ACL2"))
         (components (h1-book-cofactors-tuple-terms local))
         (g (car components))
         (a (cadr components))
         (b (caddr components))
         (summed (library-plus a b))
         (left (list (list *h1-book-cofactors-lambda* (list local)
                           (h1-book-cofactors-tuple-of g a summed))
                     (list *h1-book-cofactors-cofactors* *library-x*
                           (library-diff *library-y* *library-x*))))
         (right (list (list *h1-book-cofactors-lambda* (list local)
                            (h1-book-cofactors-tuple-of g summed b))
                      (list *h1-book-cofactors-cofactors* (library-diff *library-x* *library-y*)
                            *library-y*)))
         (default (h1-book-cofactors-tuple-of *proof-one* *proof-one* *proof-one*))
         (branches (proof-ite (library-lt *library-x* *library-y*) left
                              (proof-ite (library-lt *library-y* *library-x*) right
                                         (h1-book-cofactors-tuple-of *library-x*
                                                                     *proof-one* *proof-one*))))
         (body (proof-ite (list *h1-book-cofactors-posp* *library-x*)
                          (proof-ite (list *h1-book-cofactors-posp* *library-y*) branches default)
                          default)))
    (list *h1-book-cofactors-cofactors* (list *library-x* *library-y*) body)))

(defun h1-book-cofactors-call-descents (calls proof reversed decrease)
  (declare (xargs :measure (acl2-count calls)))
  (cond ((failure-p decrease) decrease)
        ((endp calls) (reverse reversed))
        (t (let ((step (h1-book-cofactors-descent-proof proof (car calls))))
             (h1-book-cofactors-call-descents (cdr calls) proof
                                              (cons (list (car calls) step) reversed) step)))))

(defun h1-book-cofactors-descent-steps (descents)
  (if (endp descents)
      nil
    (cons (cadar descents) (h1-book-cofactors-descent-steps (cdr descents)))))

(defun h1-book-cofactors-measure-steps (proofs obligations core)
  (if (or (endp proofs) (endp obligations))
      nil
    (proof-with-checked-results
        ((step (proof-proof-subsume core (car proofs) (caar obligations)))
         (rest (h1-book-cofactors-measure-steps (cdr proofs) (cdr obligations) core)))
      (cons step rest))))

(defun h1-book-cofactors-define-cofactors (proof)
  (let* ((lib (h1-tactics-prover-library proof))
         (name *h1-book-cofactors-cofactors*)
         (definition (h1-book-cofactors-definition))
         (measure (h1-book-cofactors-measure-of *library-x* *library-y*))
         (measures (list (cons name measure))))
    (proof-with-checked-results
        ((natural (h1-book-cofactors-natural-measure proof *library-x* *library-y*))
         (ordinal (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural)))
         (calls (termination-recursive-calls *termination-all* (list definition)))
         (descents (h1-book-cofactors-call-descents calls proof nil nil))
         (obligations (termination-obligation-cases (list definition) measures calls))
         (defined (h1-tactics-prover-add-definition proof name (cadr definition) (caddr definition)))
         (source (proof-line "define" (list *termination-all* definition)))
         (steps (h1-book-cofactors-measure-steps
                 (cons ordinal (h1-book-cofactors-descent-steps descents))
                 obligations (h1-tactics-prover-proof defined)))
         (entry (proof-proof-entry "measure" name (list name measure) steps)))
      (cons (list ordinal descents)
            (h1-tactics-prover-with-library
             defined
             (library-library-with-entries
              (h1-tactics-prover-library defined)
              (append (library-library-entries lib)
                      (list (list "define" name nil source) entry))))))))

(defun h1-book-cofactors-aligned-integer (proof norm expression evidence)
  (proof-with-checked-results
      ((literal (proof-step-first evidence))
       (term (proof-term-at literal 1))
       (alignment (h1-book-arithmetic-algebra-equality
                   (h1-book-arithmetic-algebra-with-work norm 150) expression term))
       (equality (car alignment))
       (step (h1-propositions-library-transport-argument
              (h1-tactics-prover-library proof) evidence equality 1)))
    (cons step (cdr alignment))))

(defun h1-book-cofactors-denied-sign (proof norm sign bound)
  (proof-with-checked-results
      ((aligned (h1-book-order-by-difference
                 proof sign bound (h1-book-arithmetic-algebra-with-work norm 150)))
       (identity (car aligned))
       (known (h1-book-field-require (cdr aligned) (proof-neg bound)))
       (denied (h1-propositions-library-transport-argument
                (h1-tactics-prover-library proof) (car known) identity 1)))
    (cons denied (cdr known))))

(defun h1-book-cofactors-equal-from-bounds (proof norm)
  (let ((lib (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof))
        (difference (library-diff *library-y* *library-x*)))
    (proof-with-checked-results
        ((not-positive (h1-book-cofactors-denied-sign
                        proof norm (library-positive difference)
                        (library-lt *library-x* *library-y*)))
         (not-negative (h1-book-cofactors-denied-sign
                        proof (cdr not-positive) (library-lt difference *proof-zero*)
                        (library-lt *library-y* *library-x*)))
         (rational (h1-book-field-require (cdr not-negative)
                                          (h1-book-order-rational difference)))
         (zero (library-library-cite lib "ORDER-ZERO" (list difference)
                                     (list (car rational) (car not-positive) (car not-negative))))
         (identity (h1-propositions-propositional-proof-reflexive
                    lib (library-plus *library-x* difference)))
         (step (proof-proof-rewrite core identity zero '(1 2 2)))
         (first (h1-book-arithmetic-algebra-equality
                 (h1-book-arithmetic-algebra-with-work (cdr rational) 150) *library-y*
                 (library-plus *library-x* difference)))
         (first-step (car first))
         (literal (proof-step-first step))
         (last (h1-book-arithmetic-algebra-equality (cdr first) (caddr literal) *library-x*))
         (last-step (car last))
         (step (proof-proof-chain core first-step (list step last-step))))
      (cons step (cdr last)))))

(defun h1-book-cofactors-cofactors-spec (result)
  (let* ((components (h1-book-cofactors-tuple-terms result))
         (g (car components))
         (a (cadr components))
         (b (caddr components)))
    (list (list *h1-book-cofactors-posp* g)
          (list *h1-book-cofactors-posp* a)
          (list *h1-book-cofactors-posp* b)
          (proof-eq *library-x* (h1-book-order-product g a))
          (proof-eq *library-y* (h1-book-order-product g b))
          (library-integer (h1-book-order-product *library-z* g)))))

(defun h1-book-cofactors-tuple-equalities (formals projections body proof opened)
  (if (endp formals)
      nil
    (let ((lib (h1-tactics-prover-library proof))
          (core (h1-tactics-prover-proof proof)))
      (proof-with-checked-results
          ((head (proof-term-at body 1))
           (primitive (h1-tactics-prover-solve proof (proof-eq (car projections) head) nil 160))
           (identity (h1-propositions-propositional-proof-reflexive lib (car formals)))
           (through (h1-propositions-rewrite-value lib identity opened))
           (chain (proof-proof-chain core through (list primitive)))
           (equality (h1-propositions-proof-symmetric core chain))
           (tail (proof-term-at body 2))
           (rest (h1-book-cofactors-tuple-equalities
                  (cdr formals) (cdr projections) tail proof opened)))
        (cons equality rest)))))

(defun h1-book-cofactors-rewrite-projections (projections equalities core literal step)
  (if (or (endp projections) (endp equalities))
      (proof-with-checked-results ((actual (proof-step-first step)))
        (if (equal actual literal) step '(:failure "failure" "")))
    (proof-with-checked-results
        ((rewritten (proof-proof-rewrite-result core step (car equalities) literal
                                                (car projections))))
      (h1-book-cofactors-rewrite-projections
       (cdr projections) (cdr equalities) core literal rewritten))))

(defun h1-book-cofactors-expose-literals (literals evidence core projections equalities)
  (if (or (endp literals) (endp evidence))
      nil
    (proof-with-checked-results
        ((step (h1-book-cofactors-rewrite-projections
                projections equalities core (car literals) (car evidence)))
         (rest (h1-book-cofactors-expose-literals
                (cdr literals) (cdr evidence) core projections equalities)))
      (cons step rest))))

(defun h1-book-cofactors-expose-tuple-fact (proof opened literals evidence)
  (proof-with-checked-results
      ((literal (proof-step-first opened))
       (body (proof-term-at literal 2))
       (term (proof-term-at literal 1))
       (projections (h1-book-cofactors-tuple-terms term))
       (equalities (h1-book-cofactors-tuple-equalities
                    projections (h1-book-cofactors-tuple-terms body) body proof opened)))
    (h1-book-cofactors-expose-literals
     literals evidence (h1-tactics-prover-proof proof) projections equalities)))

(defun h1-book-cofactors-assume-tests (tests core)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((pair (proof-list-of-length (car tests) 2))
         (step (proof-proof-assume core (car pair) (cadr pair)))
         (rest (h1-book-cofactors-assume-tests (cdr tests) core)))
      (cons step rest))))

(defun h1-book-cofactors-select-tests (steps lib equation)
  (declare (xargs :measure (acl2-count steps)))
  (if (or (failure-p equation) (endp steps))
      equation
    (h1-book-cofactors-select-tests
     (cdr steps) lib (h1-propositions-select-value lib equation (car steps)))))

(defun h1-book-cofactors-prove-cofactor-spec-opened (norm tests proof call-term)
  (let ((lib (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((unfolded (proof-proof-unfold core call-term))
         (pair (h1-book-cofactors-positive-pair proof norm))
         (assumptions (h1-book-cofactors-assume-tests tests core))
         (selected (h1-book-cofactors-select-tests (append (car pair) assumptions) lib unfolded))
         (step (h1-propositions-beta-value lib selected)))
      (cons step (cdr pair)))))

(defun h1-book-cofactors-prove-cofactor-spec-finish (equation evidence proof conclusion facts formula)
  (let ((lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((component-steps (h1-book-cofactors-expose-tuple-fact proof equation facts evidence))
         (step (h1-arithmetic-conjunction lib conclusion component-steps)))
      (h1-propositions-propositional-proof-implies-from lib formula step))))

(defun h1-book-cofactors-discharge-parents (pair core decrease)
  (declare (xargs :measure (acl2-count pair)))
  (if (or (failure-p decrease) (endp pair))
      decrease
    (h1-book-cofactors-discharge-parents
     (cdr pair) core (proof-proof-discharge core decrease (car pair)))))

(defun h1-book-cofactors-prove-cofactor-spec-recursive
    (call decrease proof premise formula call-term facts conclusion)
  (let* ((lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (tests (cddr (termination-call-tests call)))
         (actuals (termination-call-actuals call))
         (parents (list *library-x* *library-y*))
         (product-x (h1-book-order-product *library-z* *library-x*))
         (product-y (h1-book-order-product *library-z* *library-y*)))
    (proof-with-checked-results
        ((norm (h1-book-field-field-normalizer proof (cons (list premise t) tests)))
         (pair (h1-book-cofactors-positive-pair proof norm))
         (child (h1-book-cofactors-child-positive proof (cdr pair) actuals (car pair)))
         (decrease (h1-book-cofactors-discharge-parents (car pair) core decrease))
         (child-formula (proof-subst formula (pairlis$ (take (min 2 (len actuals)) parents)
                                                      actuals)))
         (test (proof-step-first decrease))
         (hypothesis (proof-proof-assume core (proof-ite test child-formula *proof-true*) t))
         (smaller (h1-propositions-proof-prove-if core hypothesis decrease))
         (ia (h1-book-field-require (cdr child) (library-integer product-x)))
         (ib (h1-book-field-require (cdr ia) (library-integer product-y)))
         (a-literal (proof-step-first (car ia)))
         (b-literal (proof-step-first (car ib)))
         (a-product (proof-term-at a-literal 1))
         (b-product (proof-term-at b-literal 1)))
      (let* ((index (caar child))
             (difference (if (equal index 1)
                             (library-diff b-product a-product)
                           (library-diff a-product b-product))))
        (proof-with-checked-results
            ((integral (library-library-type-of lib difference (list (car ia) (car ib))))
             (scaled (h1-book-cofactors-aligned-integer
                      proof (cdr ib) (h1-book-order-product *library-z* (nth index actuals))
                      integral))
             (rational (h1-book-field-require (cdr scaled) (h1-book-order-rational *library-z*)))
             (supplied (h1-arithmetic-conjunction
                        lib (cadr child-formula)
                        (append (cadar child)
                                (cons (car rational)
                                      (update-nth index (car scaled) (list (car ia) (car ib)))))))
             (result (h1-propositions-propositional-proof-modus-ponens lib smaller supplied))
             (components (h1-book-cofactors-components-collect 1000000 7 lib result))
             (parts (proof-list-of-length components 6))
             (ga (h1-book-cofactors-positive-parts proof (nth 1 parts)))
             (gb (h1-book-cofactors-positive-parts proof (nth 2 parts)))
             (gg (h1-book-cofactors-positive-parts proof (car parts)))
             (norm (h1-book-field-remember (cdr rational) (append gg ga gb)))
             (a-literal (proof-step-first (nth 1 parts)))
             (a (proof-term-at a-literal 1))
             (b-literal (proof-step-first (nth 2 parts)))
             (b (proof-term-at b-literal 1))
             (int-sum (library-library-type-of lib (library-plus a b)
                                               (list (car ga) (car gb))))
             (sum-sign (h1-book-order-positive-sum proof a b (cadr ga) (cadr gb)))
             (sum-positive (h1-book-cofactors-positive-integer
                            proof (library-plus a b) int-sum sum-sign))
             (child-sum (if (equal (len actuals) 2)
                            (library-plus (car actuals) (cadr actuals))
                          '(:failure "failure" "")))
             (identity (h1-book-arithmetic-algebra-equality
                        (h1-book-arithmetic-algebra-with-work norm 150)
                        (nth index parents) child-sum))
             (original (car identity))
             (restored-a (proof-proof-rewrite core original (nth 3 parts) '(1 2 1)))
             (restored (proof-proof-rewrite core restored-a (nth 4 parts) '(1 2 2)))
             (g-literal (proof-step-first (car parts)))
             (g (proof-term-at g-literal 1))
             (restored-literal (proof-step-first restored))
             (aligned (h1-book-arithmetic-algebra-equality
                       (cdr identity) (caddr restored-literal)
                       (h1-book-order-product g (library-plus a b))))
             (aligned-step (car aligned))
             (factor (proof-proof-chain core restored (list aligned-step)))
             (equation (h1-book-cofactors-prove-cofactor-spec-opened
                        (cdr aligned) tests proof call-term))
             (branch (h1-book-cofactors-prove-cofactor-spec-finish
                      (car equation)
                      (append (list (car parts))
                              (update-nth index sum-positive (list (nth 1 parts) (nth 2 parts)))
                              (update-nth index factor (list (nth 3 parts) (nth 4 parts)))
                              (list (nth 5 parts)))
                      proof conclusion facts formula)))
          (list branch (seq-zip parents actuals)))))))

(defun h1-book-cofactors-spec-branches
    (descents proof premise formula call-term facts conclusion reversed branch)
  (declare (xargs :measure (acl2-count descents)))
  (cond
   ((failure-p branch) branch)
   ((endp descents) (reverse reversed))
   (t (let ((branch (proof-with-checked-results ((pair (proof-list-of-length (car descents) 2)))
                      (h1-book-cofactors-prove-cofactor-spec-recursive
                       (car pair) (cadr pair) proof premise formula call-term facts conclusion))))
        (h1-book-cofactors-spec-branches (cdr descents) proof premise formula
                                         call-term facts conclusion (cons branch reversed) branch)))))

(defun h1-book-cofactors-prove-cofactor-spec (proof ordinal descents)
  (let* ((lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (product-x (h1-book-order-product *library-z* *library-x*))
         (product-y (h1-book-order-product *library-z* *library-y*))
         (rational-z (h1-book-order-rational *library-z*))
         (premise (h1-book-cofactors-combine
                   (list (list *h1-book-cofactors-posp* *library-x*)
                         (list *h1-book-cofactors-posp* *library-y*)
                         rational-z (library-integer product-x) (library-integer product-y))))
         (call-term (list *h1-book-cofactors-cofactors* *library-x* *library-y*))
         (facts (h1-book-cofactors-cofactors-spec call-term))
         (conclusion (h1-book-cofactors-combine facts))
         (formula (list *library-implies* premise conclusion))
         (left-test (library-lt *library-x* *library-y*))
         (right-test (library-lt *library-y* *library-x*))
         (tests (list (list left-test nil) (list right-test nil))))
    (proof-with-checked-results
        ((branches (h1-book-cofactors-spec-branches
                    (take (min 3 (len descents)) descents) proof premise formula
                    call-term facts conclusion nil nil))
         (two-branches (proof-list-of-length branches 2))
         (norm (h1-book-field-field-normalizer proof (cons (list premise t) tests)))
         (pair (h1-book-cofactors-positive-pair proof norm))
         (exact (h1-book-cofactors-equal-from-bounds proof (cdr pair)))
         (identity (h1-book-arithmetic-algebra-equality
                    (cdr exact) (h1-book-order-product *library-x* *proof-one*) *library-x*))
         (identity-step (car identity))
         (unit (h1-propositions-proof-symmetric core identity-step))
         (second (proof-proof-chain core (car exact) (list unit)))
         (positive-one (h1-tactics-prover-solve
                        proof (list *h1-book-cofactors-posp* *proof-one*)
                        (list *h1-book-cofactors-posp*) 160))
         (equation (h1-book-cofactors-prove-cofactor-spec-opened
                    (cdr identity) tests proof call-term))
         (scaled (h1-book-field-require
                  (cdr equation) (library-integer product-x)))
         (at-equal (h1-book-cofactors-prove-cofactor-spec-finish
                    (car equation)
                    (list (caar pair) positive-one positive-one unit second (car scaled))
                    proof conclusion facts formula))
         (right (proof-proof-cases core right-test (caadr two-branches) at-equal))
         (step (proof-proof-cases core left-test (caar two-branches) right))
         (induction (proof-proof-induct core ordinal step formula
                                       (h1-book-cofactors-measure-of *library-x* *library-y*)
                                       (list (cadar two-branches) (cadadr two-branches))))
         (updated (library-library-lemma lib "POSITIVE-COFACTORS" formula induction nil)))
      (h1-tactics-prover-with-library proof updated))))

(defun h1-book-cofactors-install-cofactors (proof)
  (proof-with-checked-results
      ((defined (h1-book-cofactors-define-cofactors proof)))
    (h1-book-cofactors-prove-cofactor-spec (cdr defined) (caar defined) (cadar defined))))
