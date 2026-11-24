(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-book-scan-before* (proof-sym "NEWLINE-BEFORE" "ACL2"))
(defconst *h1-book-scan-after* (proof-sym "NEWLINE-AFTER" "ACL2"))
(defconst *h1-book-scan-diff-recursion* (proof-sym "FIRST-DIFF-POSITION-REC" "ACL2"))
(defconst *h1-book-scan-diff* (proof-sym "FIRST-DIFF-POSITION" "ACL2"))
(defconst *h1-book-scan-length* (proof-cl "LENGTH"))
(defconst *h1-book-scan-end* (proof-sym "END" "ACL2"))

(defun h1-book-scan-weak-reflexive (proof term)
  (let ((library (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((comparison (library-library-axiom library "<-ON-OTHERS" (list term term)))
         (inverse (library-library-axiom library "INVERSE-OF-+" (list term)))
         (comparison (proof-proof-rewrite core comparison inverse '(1 2 1)))
         (zero (library-library-axiom library "ZERO" nil)))
      (h1-propositions-library-transport-argument library zero comparison 1))))

(defun h1-book-scan-bound-across (proof start middle end left right integer-facts)
  (let ((library (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((left-claim (proof-step-first left))
         (start-type (library-library-type-of library start integer-facts))
         (middle-type (library-library-type-of library middle integer-facts))
         (end-type (library-library-type-of library end integer-facts))
         (transitive (library-library-cite
                      library (if (proof-is-call left-claim *proof-less*) "LESS-THEN-WEAK" "WEAK-THEN-LESS")
                      (list start middle end) (list start-type middle-type end-type left right))))
      (library-library-cite library "LESS-TO-WEAK" (list start end)
                            (list start-type end-type transitive)))))

(defun h1-book-scan-previous-natural (proof current previous typed sign)
  (let ((library (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((one-or-more (h1-arithmetic-discrete library typed sign))
         (normalizer (h1-book-field-field-normalizer proof nil))
         (normalizer (h1-book-field-remember normalizer (list typed)))
         (aligned (h1-book-order-by-difference proof (library-lt previous *proof-zero*)
                                              (library-lt current *proof-one*) normalizer))
         (shifted (car aligned))
         (previous-type (library-library-type-of library previous (list typed)))
         (bound (h1-propositions-library-transport-argument library one-or-more shifted 1)))
      (library-library-cite library "NATURAL-FROM-BOUNDS" (list previous)
                            (list previous-type bound)))))

(defund h1-book-scan-prove-natural-step (proof term)
  (let ((core (h1-tactics-prover-proof proof)))
    (if (equal term *proof-true*)
        (proof-proof-prove core term nil nil)
      (proof-with-checked-results
          ((equality (h1-book-list-size-simplify proof term nil (list *library-natp* *proof-not*)))
           (value (and equality (proof-rewritten-term equality))))
        (cond ((or (not equality) (equal value term)) '(:failure "failure" ""))
              ((equal value *proof-true*) (proof-proof-true-from-eq core equality))
              (t (list :transport value equality)))))))

(defun h1-book-scan-prove-natural-term (n proof term)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h1-book-scan-prove-natural-term")
    (let ((result (h1-book-scan-prove-natural-step proof term)))
      (if (eq (car result) :transport)
          (proof-with-checked-results
              ((step (h1-book-scan-prove-natural-term (1- n) proof (cadr result))))
            (h1-propositions-proof-transport (h1-tactics-prover-proof proof) step (caddr result)))
        result))))

(mutual-recursion
 (defun h1-book-scan-natural (proof term)
   (declare (xargs :measure (acl2-count term)))
   (let ((library (h1-tactics-prover-library proof)))
     (cond ((or (proof-is-call term *library-count*) (proof-is-call term *library-len*))
            (library-library-natural library term))
           ((proof-is-call term *proof-plus*)
            (proof-with-checked-results ((evidence (h1-book-scan-natural-arguments proof (cdr term))))
              (library-library-cite library "NATURAL-SUM" (cdr term) evidence)))
           (t (h1-book-scan-prove-natural-term 1000000 proof (list *library-natp* term))))))
 (defun h1-book-scan-natural-arguments (proof arguments)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (proof-with-checked-results
         ((first (h1-book-scan-natural proof (car arguments)))
          (rest (h1-book-scan-natural-arguments proof (cdr arguments))))
       (cons first rest)))))

(defun h1-book-scan-before-previous (value tests induction changes proof)
  (let ((library (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((rulers (h1-book-termination-rulers-init proof tests))
         (active (h1-book-termination-rulers-require rulers (proof-neg (list *h1-arithmetic-zp* *library-y*))))
         (positive (h1-book-modulo-positive-divisor proof *library-y* (car active)))
         (parts (h1-book-cofactors-positive-parts proof positive)))
      (let ((typed (car parts))
            (sign (cadr parts)))
        (if (equal value *library-y*)
            (proof-with-checked-results
                ((natural (h1-book-modulo-natural-from-positive proof typed sign))
                 (relation (h1-book-scan-weak-reflexive proof *library-y*)))
              (list natural relation))
          (proof-with-checked-results
              ((previous (let ((entry (assoc-equal *library-y* changes)))
                           (if entry (cdr entry)
                             '(:failure "failure" ""))))
               (previous-nat (h1-book-scan-previous-natural proof *library-y* previous typed sign))
               (hypothesis-parts (h1-propositions-propositional-proof-conjunct library induction))
               (weak (h1-propositions-propositional-proof-modus-ponens library (cadr hypothesis-parts) previous-nat))
               (result-type (library-library-cite library "NATURAL-INTEGER" (list value)
                                                  (list (car hypothesis-parts))))
               (previous-type (library-library-type-of library previous (list typed)))
               (normalizer (h1-book-field-field-normalizer proof nil))
               (normalizer (h1-book-field-remember normalizer (list typed)))
               (advance (library-library-cite library "SUCCESSOR-LARGER" (list previous) (list previous-type)))
               (successor (h1-book-list-size-step-at advance '(2)))
               (exact (h1-book-arithmetic-algebra-equality normalizer successor *library-y*))
               (equality (car exact))
               (smaller (proof-proof-rewrite core advance equality '(1 2)))
               (relation (h1-book-scan-bound-across proof value previous *library-y* weak smaller
                                                     (list typed previous-type result-type))))
            (list (car hypothesis-parts) relation)))))))

(defun h1-book-scan-install-before-bounds-leaf (value claim tests induction changes proof premise)
  (let ((library (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((bounds (if (equal value *proof-zero*)
                     (proof-with-checked-results
                         ((natural (h1-book-scan-natural proof *proof-zero*))
                          (given (h1-arithmetic-proof-assume core premise t))
                          (relation (library-library-cite library "NATURAL-NONNEGATIVE" (list *library-y*)
                                                          (list given))))
                       (list natural relation))
                   (h1-book-scan-before-previous value tests induction changes proof)))
         (consequent (proof-term-at claim 2))
         (bound (h1-propositions-propositional-proof-implies-from library consequent (cadr bounds))))
      (h1-propositions-propositional-proof-conjoin library claim (car bounds) bound))))

(defun h1-book-scan-after-next (value tests induction proof successor)
  (let ((library (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((rulers (h1-book-termination-rulers-init proof tests))
         (end-nat (h1-book-termination-rulers-require rulers (list *library-natp* *h1-book-scan-end*)))
         (current-nat (h1-book-termination-rulers-require (cdr end-nat) (list *library-natp* *library-y*)))
         (typed-end (library-library-cite library "NATURAL-INTEGER" (list *h1-book-scan-end*)
                                         (list (car end-nat))))
         (typed-current (library-library-cite library "NATURAL-INTEGER" (list *library-y*)
                                             (list (car current-nat))))
         (inside (h1-book-termination-rulers-require (cdr current-nat) (library-lt *library-y* *h1-book-scan-end*)))
         (weak-next (library-library-cite library "SUCCESSOR-WEAK-BOUND" (list *library-y* *h1-book-scan-end*)
                                          (list typed-current typed-end (car inside))))
         (strict-lower (library-library-cite library "SUCCESSOR-LARGER" (list *library-y*)
                                             (list typed-current)))
         (typed-next (library-library-type-of library successor (list typed-current))))
      (if (equal value successor)
          (proof-with-checked-results
              ((one-nat (h1-book-scan-natural proof *proof-one*))
               (result-nat (library-library-cite library "NATURAL-SUM" (list *proof-one* *library-y*)
                                                 (list one-nat (car current-nat))))
               (lower (library-library-cite library "LESS-TO-WEAK" (list *library-y* value)
                                            (list typed-current typed-next strict-lower))))
            (list result-nat lower weak-next))
        (proof-with-checked-results
            ((child (h1-propositions-propositional-proof-conjunct library induction))
             (result-nat (h1-propositions-propositional-proof-modus-ponens library (car child) (car end-nat)))
             (interval (h1-propositions-propositional-proof-modus-ponens library (cadr child) weak-next))
             (bounds (h1-propositions-propositional-proof-conjunct library interval))
             (typed-result (library-library-cite library "NATURAL-INTEGER" (list value) (list result-nat)))
             (lower (h1-book-scan-bound-across proof *library-y* successor value strict-lower (car bounds)
                                               (list typed-current typed-next typed-result))))
          (list result-nat lower (cadr bounds)))))))

(defun h1-book-scan-install-after-bounds-leaf
    (value claim tests induction changes proof nat-end allowed successor)
  (declare (ignore changes))
  (let ((library (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((bounds (if (equal value *h1-book-scan-end*)
                     (proof-with-checked-results
                         ((result-nat (h1-arithmetic-proof-assume core nat-end t))
                          (lower (h1-arithmetic-proof-assume core allowed t))
                          (upper (h1-book-scan-weak-reflexive proof *h1-book-scan-end*)))
                       (list result-nat lower upper))
                   (h1-book-scan-after-next value tests induction proof successor)))
         (natural-claim (proof-term-at claim 1))
         (first (h1-propositions-propositional-proof-implies-from library natural-claim (car bounds)))
         (interval-claim (proof-term-at claim 2))
         (bound-claim (proof-term-at interval-claim 2))
         (interval (h1-propositions-propositional-proof-conjoin library bound-claim (cadr bounds) (caddr bounds)))
         (second (h1-propositions-propositional-proof-implies-from library interval-claim interval)))
      (h1-propositions-propositional-proof-conjoin library claim first second))))

(defun h1-book-scan-diff-step-bound (library rulers typed-current end)
  (proof-with-checked-results
      ((value (proof-term-at end 1))
       (end-type (library-library-axiom library "H1-LENGTH-INTEGER" (list value)))
       (less (h1-book-termination-rulers-require rulers (library-lt *library-z* end)))
       (bound (library-library-cite library "SUCCESSOR-WEAK-BOUND" (list *library-z* end)
                                    (list typed-current end-type (car less)))))
    (cons bound (cdr less))))

(defun h1-book-scan-install-diff-bounds-leaf (value claim tests induction changes proof premise ends)
  (declare (ignore value changes))
  (let ((library (h1-tactics-prover-library proof)))
    (if (not induction)
        (proof-with-checked-results
            ((given (h1-arithmetic-proof-assume (h1-tactics-prover-proof proof) premise t)))
          (h1-propositions-propositional-proof-implies-from library claim given))
      (proof-with-checked-results
          ((rulers (h1-book-termination-rulers-init proof tests))
           (natural (h1-book-termination-rulers-require rulers (list *library-natp* *library-z*)))
           (typed-current (library-library-cite library "NATURAL-INTEGER" (list *library-z*)
                                               (list (car natural))))
           (first (h1-book-scan-diff-step-bound library (cdr natural) typed-current (car ends)))
           (second (h1-book-scan-diff-step-bound library (cdr first) typed-current (cadr ends)))
           (premises (h1-book-list-size-step-at induction '(1)))
           (evidence (h1-arithmetic-conjunction library premises (list (car first) (car second))))
           (child (h1-propositions-propositional-proof-modus-ponens library induction evidence)))
        (h1-propositions-propositional-proof-implies-from library claim child)))))

(defun h1-book-scan-diff-ends ()
  (list (list *h1-book-scan-length* *library-x*)
        (list *h1-book-scan-length* *library-y*)))

(defun h1-book-scan-diff-interval (ends index)
  (proof-ite (proof-neg (library-lt (car ends) index))
             (proof-neg (library-lt (cadr ends) index)) *proof-false*))

(defun h1-book-scan-prove-leaf (proof prove-leaf value actual tests hypothesis changes)
  (case prove-leaf
    (:before (h1-book-scan-install-before-bounds-leaf
              value actual tests hypothesis changes proof (list *library-natp* *library-y*)))
    (:after (h1-book-scan-install-after-bounds-leaf
             value actual tests hypothesis changes proof
             (list *library-natp* *h1-book-scan-end*)
             (proof-neg (library-lt *h1-book-scan-end* *library-y*))
             (library-plus *proof-one* *library-y*)))
    (:diff (let ((ends (h1-book-scan-diff-ends)))
             (h1-book-scan-install-diff-bounds-leaf
              value actual tests hypothesis changes proof
              (h1-book-scan-diff-interval ends *library-z*) ends)))
    (otherwise
     (let ((entry (assoc-equal (list value actual tests hypothesis changes) prove-leaf)))
       (if entry (cdr entry) '(:failure "failure" ""))))))

(defun h1-book-scan-changed-bindings (formals actuals)
  (if (or (endp formals) (endp actuals))
      nil
    (let* ((formal (car formals))
           (actual (car actuals))
           (changed (not (equal formal actual)))
           (tail (h1-book-scan-changed-bindings (cdr formals) (cdr actuals))))
      (if (not changed)
          tail
        (cons (list formal actual) tail)))))

(defun h1-book-scan-binding-table (bindings changes)
  (if (endp bindings)
      changes
    (h1-book-scan-binding-table
     (cdr bindings) (table-put changes (caar bindings) (cadar bindings)))))

(defun h1-book-scan-signed-clause (tests conclusion)
  (if (endp tests)
      (list conclusion)
    (proof-with-checked-results
        ((signed (proof-list-of-length (car tests) 2))
         (literal (if (cadr signed) (proof-neg (car signed)) (car signed)))
         (tail (h1-book-scan-signed-clause (cdr tests) conclusion)))
      (cons literal tail))))

(defun h1-book-scan-child-hypothesis (proof head value tests measure formula changes)
  (let ((core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((child-measure (proof-subst measure changes))
         (conclusion (list *proof-ordinal-less* child-measure measure))
         (clause (h1-book-scan-signed-clause tests conclusion))
         (smaller (h1-book-termination-prove-measure-clause
                   proof clause (termination-make-call head head (cdr value) tests)))
         (child (proof-subst formula changes))
         (given (h1-arithmetic-proof-assume core (proof-ite conclusion child *proof-true*) t)))
      (h1-propositions-proof-prove-if core given smaller))))

(defun h1-book-scan-scan-induction-leaf
    (value tests proof call template measure prove-leaf formula substitutions)
  (proof-with-checked-results
      ((head (proof-term-at call 0))
       (recursive (proof-is-call value head))
       (bindings (and recursive (h1-book-scan-changed-bindings (cdr call) (cdr value))))
       (changes (h1-book-scan-binding-table bindings nil))
       (hypothesis (and recursive
                        (h1-book-scan-child-hypothesis proof head value tests measure formula changes)))
       (substitutions (if recursive (table-put substitutions bindings nil) substitutions))
       (actual (proof-subst template (list (cons *proof-result* value))))
       (step (h1-book-scan-prove-leaf proof prove-leaf value actual tests hypothesis changes)))
    (cons step substitutions)))

(defun h1-book-scan-install-diff-wrapper-leaf (value tests proof)
  (declare (ignore tests))
  (h1-book-scan-natural proof value))

(defun h1-book-scan-rebuild-branch (proof step equality template)
  (let ((core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results ((reversed (h1-propositions-proof-symmetric core equality)))
      (proof-proof-rewrite-result core step reversed template *proof-result*))))

(defun h1-book-scan-measure-ordinal (proof measure)
  (let ((library (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((direct (descent-direct-builtin library (list (list *proof-ordinalp* measure)) nil)))
      (if (car direct)
          (car direct)
        (proof-with-checked-results ((head (proof-term-at measure 0)))
          (if (equal head *library-gap*)
              (library-library-cite library "GAP-ORDINAL" (cdr measure) nil)
            (proof-with-checked-results ((natural (h1-book-scan-natural proof measure)))
              (library-library-cite library "NATURAL-ORDINAL" (list measure) (list natural)))))))))

(defund h1-book-scan-value-branch (core value)
  (cond ((proof-is-call value *proof-if*)
         (proof-with-checked-results ((branches (proof-list-of-length (cdr value) 3)))
           (cons :if branches)))
        ((and (proof-compound value) (endp value))
         '(:failure "failure" ""))
        ((and (proof-compound value) (proof-compound (car value)))
         (proof-with-checked-results
             ((equality (proof-proof-beta core value))
              (opened (proof-rewritten-term equality)))
           (list :lambda equality opened)))
        (t (list :leaf))))

(defun h1-book-scan-by-value (n proof value template tests scan prove-leaf substitutions)
  (declare (xargs :measure (nfix n)))
  (let ((core (h1-tactics-prover-proof proof)))
    (if (zp n)
        '(:failure "Fuel" "h1-book-scan-by-value")
      (proof-with-checked-results ((branch (h1-book-scan-value-branch core value)))
        (case (car branch)
          (:if
           (let ((test (cadr branch)))
             (proof-with-checked-results
                 ((yes (h1-book-scan-by-value (1- n) proof (caddr branch) template
                                             (append tests (list (list test t))) scan prove-leaf substitutions))
                  (no (h1-book-scan-by-value (1- n) proof (cadddr branch) template
                                            (append tests (list (list test nil))) scan prove-leaf (cdr yes)))
                  (true-eq (h1-arithmetic-proof-if-true core value))
                  (yes-step (h1-book-scan-rebuild-branch proof (car yes) true-eq template))
                  (false-eq (h1-arithmetic-proof-if-false core value))
                  (no-step (h1-book-scan-rebuild-branch proof (car no) false-eq template))
                  (step (proof-proof-cases core test yes-step no-step)))
               (cons step (cdr no)))))
          (:lambda
           (proof-with-checked-results
               ((result (h1-book-scan-by-value (1- n) proof (caddr branch) template
                                              tests scan prove-leaf substitutions))
                (step (h1-book-scan-rebuild-branch proof (car result) (cadr branch) template)))
             (cons step (cdr result))))
          (otherwise
           (proof-with-checked-results
               ((result (if scan
                            (h1-book-scan-scan-induction-leaf value tests proof (car scan) template
                                                             (cadr scan) prove-leaf (caddr scan) substitutions)
                          (proof-with-checked-results
                              ((step (h1-book-scan-install-diff-wrapper-leaf value tests proof)))
                            (cons step substitutions))))
                (literal (proof-step-first (car result)))
                (claim (proof-subst template (list (cons *proof-result* value)))))
             (if (equal literal claim) result '(:failure "failure" "")))))))))

(defun h1-book-scan-scan-induction (proof call template measure prove-leaf)
  (let ((core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((expansion (proof-proof-unfold core call))
         (formula (proof-subst template (list (cons *proof-result* call))))
         (value (proof-rewritten-term expansion))
         (cases (h1-book-scan-by-value 1000000 proof value template nil
                                       (list call measure formula) prove-leaf nil))
         (reconstructed (h1-book-scan-rebuild-branch proof (car cases) expansion template))
         (ordinal (h1-book-scan-measure-ordinal proof measure)))
      (proof-proof-induct core ordinal reconstructed formula measure (table-keys (cdr cases))))))

(defun h1-book-scan-install-before-bounds (proof)
  (let* ((library (h1-tactics-prover-library proof))
         (call (list *h1-book-scan-before* *library-x* *library-y* *library-z*))
         (premise (list *library-natp* *library-y*))
         (bound (list *library-implies* premise (proof-neg (library-lt *library-y* *proof-result*))))
         (template (proof-ite (list *library-natp* *proof-result*) bound *proof-false*)))
    (proof-with-checked-results
        ((invariant (h1-book-scan-scan-induction proof call template (list *library-count* *library-y*) :before))
         (parts (h1-propositions-propositional-proof-conjunct library invariant))
         (record (h1-tactics-prover-record-formula proof "NEWLINE-BEFORE-BOUND" (cadr parts) nil)))
      (cdr record))))

(defun h1-book-scan-install-after-bounds (proof)
  (let* ((call (list *h1-book-scan-after* *library-x* *library-y* *library-z* *h1-book-scan-end*))
         (nat-end (list *library-natp* *h1-book-scan-end*))
         (allowed (proof-neg (library-lt *h1-book-scan-end* *library-y*)))
         (natural (list *library-implies* nat-end (list *library-natp* *proof-result*)))
         (interval (proof-ite (proof-neg (library-lt *proof-result* *library-y*))
                              (proof-neg (library-lt *h1-book-scan-end* *proof-result*)) *proof-false*))
         (template (proof-ite natural (list *library-implies* allowed interval) *proof-false*))
         (measure (list *library-gap* (library-plus *proof-one* *h1-book-scan-end*) *library-y*)))
    (proof-with-checked-results
        ((invariant (h1-book-scan-scan-induction proof call template measure :after))
         (claim (proof-step-first invariant))
         (library (library-library-lemma (h1-tactics-prover-library proof)
                                        "NEWLINE-AFTER-BOUNDS" claim invariant nil))
         (proof (h1-tactics-prover-with-library proof library))
         (core (h1-tactics-prover-proof proof))
         (cited (library-library-cite library "NEWLINE-AFTER-BOUNDS" nil nil))
         (parts (h1-propositions-propositional-proof-conjunct library cited))
         (given (h1-arithmetic-proof-assume core allowed t))
         (result (h1-propositions-propositional-proof-modus-ponens library (cadr parts) given))
         (bounds (h1-propositions-propositional-proof-conjunct library result))
         (claim (proof-step-first (car bounds)))
         (lower (h1-propositions-propositional-proof-implies-from
                 library (list *library-implies* allowed claim) (car bounds)))
         (record (h1-tactics-prover-record-formula proof "NEWLINE-AFTER-LOWER" lower nil))
         (proof (cdr record))
         (library (h1-tactics-prover-library proof))
         (claim (proof-step-first (cadr bounds)))
         (upper (h1-propositions-propositional-proof-implies-from
                 library (list *library-implies* allowed claim) (cadr bounds)))
         (record (h1-tactics-prover-record-formula proof "NEWLINE-AFTER-UPPER" upper nil)))
      (cdr record))))

(defun h1-book-scan-install-diff-bounds (proof)
  (let* ((ends (h1-book-scan-diff-ends))
         (call (list* *h1-book-scan-diff-recursion* *library-x* *library-y* *library-z* ends))
         (premise (h1-book-scan-diff-interval ends *library-z*))
         (interval (h1-book-scan-diff-interval ends *proof-result*))
         (template (list *library-implies* premise interval))
         (measure (list *library-gap* (car ends) *library-z*)))
    (proof-with-checked-results
        ((result (h1-book-scan-scan-induction proof call template measure :diff))
         (record (h1-tactics-prover-record-formula proof "FIRST-DIFF-RECURSION-BOUND" result nil)))
      (cdr record))))

(defun h1-book-scan-length-nonnegative (proof value)
  (let ((library (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof))
        (length (list *h1-book-scan-length* value)))
    (proof-with-checked-results
        ((equation (proof-proof-unfold core length))
         (result (proof-rewritten-term equation))
         (typed (h1-book-scan-by-value 1000000 proof result (list *library-natp* *proof-result*)
                                       nil nil nil nil))
         (natural (h1-propositions-library-transport-argument library (car typed) equation 1)))
      (library-library-cite library "NATURAL-NONNEGATIVE" (list length) (list natural)))))

(defun h1-book-scan-install-diff-wrapper (proof)
  (let ((library (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((wrapper (proof-proof-unfold core (list *h1-book-scan-diff* *library-x* *library-y*)))
         (recursive-bound (library-library-cite library "FIRST-DIFF-RECURSION-BOUND"
                                                (list *library-x* *library-y* *proof-zero*) nil))
         (left (h1-book-scan-length-nonnegative proof *library-x*))
         (right (h1-book-scan-length-nonnegative proof *library-y*))
         (premise (h1-book-list-size-step-at recursive-bound '(1)))
         (evidence (h1-propositions-propositional-proof-conjoin library premise left right))
         (bound (h1-propositions-propositional-proof-modus-ponens library recursive-bound evidence))
         (reversed (h1-propositions-proof-symmetric core wrapper))
         (bound (proof-proof-rewrite-first core bound reversed))
         (record (h1-tactics-prover-record-formula proof "FIRST-DIFF-BOUND" bound nil)))
      (cdr record))))
