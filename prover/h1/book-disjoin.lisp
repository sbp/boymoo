(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-book-disjoin-disjoin* (proof-sym "DISJOIN" "ACL2"))
(defconst *h1-book-disjoin-disjoin2* (proof-sym "DISJOIN2" "ACL2"))
(defconst *h1-book-disjoin-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *h1-book-disjoin-any* (proof-sym "H1-ANY-EVALUATED-TRUE" "ACL2"))
(defconst *h1-book-disjoin-quoted-false*
  (proof-quote (list *proof-quote* *proof-nil*)))
(defconst *h1-book-disjoin-quoted-true*
  (proof-quote (list *proof-quote* *proof-t*)))

(defun h1-book-disjoin-step-at (step place)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (h1-book-arithmetic-at literal place))))

(defun h1-book-disjoin-simplify-select (proof redex)
  (proof-with-checked-results ((test (proof-term-at redex 1)))
    (cond
     ((equal test *proof-false*)
      (proof-proof-fact proof "if-nil"
                        (seq-zip (list *library-y* *library-z*) (cddr redex))))
     ((equal test *proof-true*)
      (proof-with-checked-results
          ((step (proof-proof-fact proof "if-non-nil"
                                   (seq-zip (list *library-x* *library-y* *library-z*)
                                           (cdr redex))))
           (yes (proof-term-at redex 2))
           (selected (proof-proof-front proof step (proof-eq redex yes)))
           (computed (proof-proof-compute proof (proof-eq *proof-true* *proof-false*)
                                          *proof-nil*))
           (rewritten (proof-proof-rewrite proof selected computed '(2))))
        (proof-proof-tidy proof rewritten)))
     (t nil))))

; These simplifications use no evidence or definition openings.
(mutual-recursion
 (defun h1-book-disjoin-simplify-visit (n proof term)
   (declare (xargs :measure (nfix n)))
   (let* ((core (h1-tactics-prover-proof proof))
          (lib (h1-tactics-prover-library proof))
          (head (car term)))
     (cond
      ((zp n) '(:failure "fuel" "h1-book-disjoin-simplify-visit"))
      ((not (proof-compound term)) nil)
      ((not (consp term)) '(:failure "failure" ""))
      ((equal head *proof-quote*) nil)
      ((proof-compound head)
       (proof-with-checked-results
           ((first (proof-proof-beta core term))
            (value (h1-book-disjoin-step-at first '(2)))
            (rest (h1-book-disjoin-simplify-visit (1- n) proof value)))
         (proof-proof-chain core first (list rest))))
      ((equal head *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at term 1))
            (first (h1-book-disjoin-simplify-visit (1- n) proof test))
            (redex (if first
                       (proof-with-checked-results
                           ((value (h1-book-disjoin-step-at first '(2)))
                            (yes (proof-term-at term 2))
                            (no (proof-term-at term 3)))
                         (proof-ite value yes no))
                     term))
            (selected (h1-book-disjoin-simplify-select core redex))
            (selected
             (if first
                 (proof-with-checked-results
                     ((identity (h1-propositions-propositional-proof-reflexive lib term))
                      (rewritten (proof-proof-rewrite core identity first '(1 2 1))))
                   (proof-proof-chain core rewritten (list selected)))
               selected)))
         (if (not selected)
             nil
           (proof-with-checked-results ((value (h1-book-disjoin-step-at selected '(2))))
             (if (equal value redex)
                 selected
               (proof-with-checked-results
                   ((last (h1-book-disjoin-simplify-visit (1- n) proof value)))
                 (proof-proof-chain core selected (list last))))))))
      (t
       (proof-with-checked-results
           ((result (h1-book-disjoin-simplify-arguments (1- n) proof term (cdr term) 1 nil))
            (current (if result (h1-book-disjoin-step-at result '(2)) term))
            (constant (h1-tactics-prover-constant proof current)))
         (cond ((not constant) result)
               (result (proof-proof-chain core result (list constant)))
               (t constant)))))))

 (defun h1-book-disjoin-simplify-arguments (n proof term args index result)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h1-book-disjoin-simplify-arguments"))
    ((endp args) result)
    (t
     (proof-with-checked-results
         ((equality (h1-book-disjoin-simplify-visit (1- n) proof (car args)))
          (next
           (if equality
               (proof-with-checked-results
                   ((previous
                     (or result
                         (h1-propositions-propositional-proof-reflexive
                          (h1-tactics-prover-library proof) term))))
                 (proof-proof-rewrite (h1-tactics-prover-proof proof) previous equality
                                      (list 1 2 index)))
             result)))
       (h1-book-disjoin-simplify-arguments (1- n) proof term (cdr args)
                                          (+ 1 index) next))))))

(defun h1-book-disjoin-simplify (proof term)
  (h1-book-disjoin-simplify-visit 1000000 proof term))

(defun h1-book-disjoin-truth (value)
  (proof-ite value *proof-true* *proof-false*))

(defun h1-book-disjoin-eval-quoted (proof term)
  (let ((core (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((clause (h1-book-rewrite-equal-constraint
                  proof 2 (h1-book-rewrite-equal-evaluated term)))
         (conditions (h1-book-disjoin-step-at clause '(1)))
         (test (proof-term-at conditions 1))
         (computed (h1-tactics-prover-constant proof test))
         (cons-step
          (if computed
              (h1-propositions-computed-test lib computed)
            (h1-book-disjoin-step-at computed nil)))
         (head-test (h1-book-arithmetic-at conditions '(2 1)))
         (proof-head (h1-tactics-prover-constant proof head-test))
         (premise
          (if proof-head
              (h1-propositions-propositional-proof-conjoin lib conditions cons-step proof-head)
            (h1-book-disjoin-step-at proof-head nil)))
         (resolved (h1-propositions-propositional-proof-modus-ponens lib clause premise))
         (value (h1-book-disjoin-step-at resolved '(2)))
         (simplified (h1-book-disjoin-simplify proof value)))
      (proof-proof-chain core resolved (list simplified)))))

(defun h1-book-disjoin-eval-constructed-project (n proof result term)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h1-book-disjoin-eval-constructed-project"))
   ((proof-is-call term *proof-cons*)
    (proof-with-checked-results
        ((next (h1-book-rewrite-equal-projections proof result term))
         (tail (proof-term-at term 2)))
      (h1-book-disjoin-eval-constructed-project (1- n) proof next tail)))
   (t result)))

(defun h1-book-disjoin-eval-constructed (proof evaluator-rule term)
  (let ((lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((clause (h1-book-rewrite-equal-constraint
                  proof evaluator-rule (h1-book-rewrite-equal-evaluated term)))
         (conditions (h1-book-disjoin-step-at clause '(1)))
         (cons-step (h1-book-rewrite-equal-on-cons proof term))
         (args (h1-arithmetic-term-tail term))
         (head (library-library-axiom lib "CAR-CONS" args))
         (premise (h1-propositions-propositional-proof-conjoin lib conditions cons-step head))
         (result (h1-propositions-propositional-proof-modus-ponens lib clause premise)))
      (h1-book-disjoin-eval-constructed-project 1000000 proof result term))))

(defun h1-book-disjoin-quoted-truth-p (term)
  (or (equal term *h1-book-disjoin-quoted-false*)
      (equal term *h1-book-disjoin-quoted-true*)))

(defun h1-book-disjoin-disjoin2-value-tests (proof tests left right)
  (if (endp tests)
      (list left right)
    (proof-with-checked-results ((pair (proof-list-of-length (car tests) 2)))
      (let ((test (car pair))
            (holds (cadr pair))
            (core (h1-tactics-prover-proof proof))
            (lib (h1-tactics-prover-library proof)))
        (if (and holds (proof-is-call test *proof-equal*))
            (proof-with-checked-results ((value (proof-term-at test 2)))
              (if (h1-book-disjoin-quoted-truth-p value)
                  (proof-with-checked-results
                      ((constant (h1-book-disjoin-eval-quoted proof value))
                       (assumed (h1-arithmetic-proof-assume core test t))
                       (reversed (h1-propositions-proof-symmetric core assumed))
                       (known (proof-proof-rewrite core constant reversed '(1 1 1)))
                       (left (h1-propositions-rewrite-value lib left known))
                       (right (h1-propositions-rewrite-value lib right known)))
                    (h1-book-disjoin-disjoin2-value-tests proof (cdr tests) left right))
                (h1-book-disjoin-disjoin2-value-tests proof (cdr tests) left right)))
          (h1-book-disjoin-disjoin2-value-tests proof (cdr tests) left right))))))

(defun h1-book-disjoin-disjoin2-value-leaf (value tests proof target)
  (let* ((core (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (expression (h1-book-disjoin-truth (h1-book-rewrite-equal-evaluated value))))
    (proof-with-checked-results
        ((left (h1-propositions-propositional-proof-reflexive lib expression))
         (right (h1-propositions-propositional-proof-reflexive lib target))
         (left
          (cond
           ((h1-book-disjoin-quoted-truth-p value)
            (proof-with-checked-results ((evaluated (h1-book-disjoin-eval-quoted proof value)))
              (h1-propositions-rewrite-value lib left evaluated)))
           ((proof-is-call value *proof-cons*)
            (proof-with-checked-results
                ((evaluated (h1-book-disjoin-eval-constructed proof 10 value))
                 (left (h1-propositions-rewrite-value lib left evaluated))
                 (evaluated (h1-book-disjoin-eval-quoted proof *h1-book-disjoin-quoted-true*)))
              (h1-propositions-rewrite-value lib left evaluated)))
           (t left)))
         (sides (h1-book-disjoin-disjoin2-value-tests proof tests left right))
         (left-value (h1-book-disjoin-step-at (car sides) '(2)))
         (left-simplified (h1-book-disjoin-simplify proof left-value))
         (left (proof-proof-chain core (car sides) (list left-simplified)))
         (right-value (h1-book-disjoin-step-at (cadr sides) '(2)))
         (right-simplified (h1-book-disjoin-simplify proof right-value))
         (right (proof-proof-chain core (cadr sides) (list right-simplified)))
         (left-value (h1-book-disjoin-step-at left '(2)))
         (right-value (h1-book-disjoin-step-at right '(2)))
         (aligned (h1-tactics-prover-solve proof (proof-eq left-value right-value) nil 160))
         (reversed (h1-propositions-proof-symmetric core right)))
      (proof-proof-chain core left (list aligned reversed)))))

(defun h1-book-disjoin-disjoin2-value-branches (n proof value template tests target)
  (declare (xargs :measure (nfix n)))
  (let ((core (h1-tactics-prover-proof proof)))
    (cond
     ((zp n) '(:failure "fuel" "h1-book-disjoin-disjoin2-value-branches"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((parts (proof-list-of-length (cdr value) 3))
           (yes (h1-book-disjoin-disjoin2-value-branches
                 (1- n) proof (cadr parts) template
                 (append tests (list (list (car parts) t))) target))
           (no (h1-book-disjoin-disjoin2-value-branches
                (1- n) proof (caddr parts) template
                (append tests (list (list (car parts) nil))) target))
           (if-true (h1-arithmetic-proof-if-true core value))
           (reversed (h1-propositions-proof-symmetric core if-true))
           (yes (proof-proof-rewrite-result core yes reversed template *proof-result*))
           (if-false (h1-arithmetic-proof-if-false core value))
           (reversed (h1-propositions-proof-symmetric core if-false))
           (no (proof-proof-rewrite-result core no reversed template *proof-result*)))
        (proof-proof-cases core (car parts) yes no)))
     ((and (proof-compound value) (not (consp value)))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta core value))
           (body (h1-book-disjoin-step-at equality '(2)))
           (opened (h1-book-disjoin-disjoin2-value-branches
                    (1- n) proof body template tests target))
           (reversed (h1-propositions-proof-symmetric core equality)))
        (proof-proof-rewrite-result core opened reversed template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (h1-book-disjoin-disjoin2-value-leaf value tests proof target))
           (literal (proof-step-first step))
           (claim (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal claim) step '(:failure "failure" "")))))))

(defun h1-book-disjoin-disjoin2-value (proof)
  (let* ((core (h1-tactics-prover-proof proof))
         (term (list *h1-book-disjoin-disjoin2* *library-x* *library-y*))
         (target (proof-ite (h1-book-rewrite-equal-evaluated *library-x*)
                            *proof-true*
                            (h1-book-disjoin-truth
                             (h1-book-rewrite-equal-evaluated *library-y*))))
         (template (proof-eq (h1-book-disjoin-truth
                              (h1-book-rewrite-equal-evaluated *proof-result*))
                             target)))
    (proof-with-checked-results
        ((equation (proof-proof-unfold core term))
         (value (h1-book-disjoin-step-at equation '(2)))
         (branches (h1-book-disjoin-disjoin2-value-branches
                    1000000 proof value template nil target))
         (reversed (h1-propositions-proof-symmetric core equation)))
      (proof-proof-rewrite-result core branches reversed template *proof-result*))))

(defun h1-book-disjoin-define-truth-fold (proof)
  (let* ((term (list *h1-book-disjoin-any* (list *library-cdr* *library-x*)))
         (body (proof-ite (list *proof-consp* *library-x*)
                          (proof-ite (list *library-car* *library-x*) *proof-true* term)
                          *proof-false*))
         (formals (list *library-x*))
         (definition (list *h1-book-disjoin-any* formals body))
         (definitions (list definition)))
    (proof-with-checked-results
        ((calls (termination-recursive-calls *termination-all* definitions))
         (measure (h1-book-termination-termination-entry proof definitions calls nil))
         (proof (h1-tactics-prover-add-definition proof *h1-book-disjoin-any* formals body))
         (source (proof-line "define" (list *termination-all* definition))))
      (let* ((lib (h1-tactics-prover-library proof))
             (entry (list "define" *h1-book-disjoin-any* nil source))
             (entries (append (library-library-entries lib) (list entry measure))))
        (h1-tactics-prover-with-library proof (library-library-with-entries lib entries))))))

(defun h1-book-disjoin-any-evaluated (proof terms cons-step)
  (let ((core (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((literal (h1-book-disjoin-step-at cons-step nil))
         (rule (h1-book-rewrite-equal-constraint
                proof
                (if (equal literal (proof-neg (list *proof-consp* terms))) 4 5)
                (h1-book-rewrite-equal-evaluated-list terms)))
         (values (h1-propositions-propositional-proof-modus-ponens lib rule cons-step))
         (output (h1-book-disjoin-step-at values '(2)))
         (evidence (if (proof-is-call output *proof-cons*)
                       (h1-book-rewrite-equal-on-cons proof output)
                     (h1-tactics-prover-solve
                      proof (proof-neg (list *proof-consp* *proof-false*)) nil 160)))
         (opened (proof-proof-unfold core (list *h1-book-disjoin-any* output)))
         (evaluated-any (h1-propositions-select-value lib opened evidence))
         (evaluated-any (if (proof-is-call output *proof-cons*)
                            (h1-book-rewrite-equal-projections proof evaluated-any output)
                          evaluated-any))
         (reversed (h1-propositions-proof-symmetric core values)))
      (proof-proof-rewrite core evaluated-any reversed '(1 1 1)))))

(defun h1-book-disjoin-evaluated-disjoin-start (equation proof formula)
  (let ((lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((term (proof-term-at formula 1))
         (identity (h1-propositions-propositional-proof-reflexive lib term)))
      (h1-propositions-rewrite-value lib identity equation))))

(defun h1-book-disjoin-evaluated-disjoin (proof)
  (let* ((core (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (term (list *h1-book-disjoin-disjoin* *library-x*))
         (right (list *h1-book-disjoin-any*
                      (h1-book-rewrite-equal-evaluated-list *library-x*)))
         (formula (proof-eq (h1-book-disjoin-truth (h1-book-rewrite-equal-evaluated term))
                            right)))
    (proof-with-checked-results
        ((expansion (proof-proof-unfold core term))
         (endp-test (h1-book-disjoin-step-at expansion '(2 1)))
         (stop (h1-arithmetic-proof-assume core endp-test t))
         (empty (h1-propositions-select-value lib expansion stop))
         (left (h1-book-disjoin-evaluated-disjoin-start empty proof formula))
         (value (h1-book-disjoin-step-at empty '(2)))
         (evaluated (h1-book-disjoin-eval-quoted proof value))
         (left (h1-propositions-rewrite-value lib left evaluated))
         (value (h1-book-disjoin-step-at left '(2)))
         (simplified (h1-book-disjoin-simplify proof value))
         (left (proof-proof-chain core left (list simplified)))
         (noncons (h1-book-termination-endp-noncons proof stop))
         (empty-any (h1-book-disjoin-any-evaluated proof *library-x* noncons))
         (reversed (h1-propositions-proof-symmetric core empty-any))
         (first (proof-proof-chain core left (list reversed)))
         (more (h1-arithmetic-proof-assume core endp-test nil))
         (cons-step (h1-book-termination-cons-from-nonatom proof more))
         (nonempty (h1-propositions-select-value lib expansion more))
         (rest-test (h1-book-disjoin-step-at nonempty '(2 1)))
         (folded (h1-book-disjoin-any-evaluated proof *library-x* cons-step))
         (last (h1-arithmetic-proof-assume core rest-test t))
         (last-head (h1-propositions-select-value lib nonempty last))
         (tail-parts (h1-arithmetic-term-tail rest-test))
         (tail-parts (proof-list-of-length tail-parts 1))
         (tail (car tail-parts))
         (noncons (h1-book-termination-endp-noncons proof last))
         (tail-any (h1-book-disjoin-any-evaluated proof tail noncons))
         (without-tail (h1-propositions-rewrite-value lib folded tail-any))
         (left (h1-book-disjoin-evaluated-disjoin-start last-head proof formula))
         (reversed (h1-propositions-proof-symmetric core without-tail))
         (single (proof-proof-chain core left (list reversed)))
         (has-rest (h1-arithmetic-proof-assume core rest-test nil))
         (continue (h1-propositions-select-value lib nonempty has-rest))
         (left (h1-book-disjoin-evaluated-disjoin-start continue proof formula))
         (call (h1-book-disjoin-step-at continue '(2)))
         (args (h1-arithmetic-term-tail call))
         (pair (library-library-cite lib "EVAL-DISJOIN2" args nil))
         (left (proof-proof-chain core left (list pair)))
         (builtin (library-library-builtin lib 3 *library-x*))
         (descent (proof-proof-discharge core builtin cons-step))
         (decrease (proof-step-first descent))
         (claim (proof-subst formula (list (cons *library-x* tail))))
         (assumed (h1-arithmetic-proof-assume core (proof-ite decrease claim *proof-true*) t))
         (child (h1-propositions-proof-prove-if core assumed descent))
         (left (h1-propositions-rewrite-value lib left child))
         (reversed (h1-propositions-proof-symmetric core folded))
         (recursive (proof-proof-chain core left (list reversed)))
         (nonempty-case (proof-proof-cases core rest-test single recursive))
         (cases (proof-proof-cases core endp-test first nonempty-case))
         (measure (list *library-count* *library-x*))
         (ordinal (descent-measure-ordinal lib measure)))
      (proof-proof-induct core ordinal cases formula measure
                          (list (list (list *library-x* tail)))))))

(defun h1-book-disjoin-prove-rewrite-transfer (proof)
  (let* ((core (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (changed (list *h1-book-rewrite-equal-substitute* *proof-false*
                        *library-y* *library-z* *library-x*))
         (original (h1-book-rewrite-equal-evaluated (list *h1-book-disjoin-disjoin* *library-x*)))
         (replacement (h1-book-rewrite-equal-evaluated (list *h1-book-disjoin-disjoin* changed))))
    (proof-with-checked-results
        ((environment (proof-term-at original 2))
         (premise (h1-book-cofactors-combine
                   (list (list (proof-sym "PSEUDO-TERM-LISTP" "ACL2") *library-x*)
                         (list (proof-sym "ALISTP" "ACL2") environment)
                         (proof-eq (h1-book-rewrite-equal-evaluated *library-y*)
                                   (h1-book-rewrite-equal-evaluated *library-z*))
                         replacement)))
         (assumed (h1-arithmetic-proof-assume core premise t))
         (parts (h1-book-cofactors-components proof assumed))
         (parts (proof-list-of-length parts 4))
         (invariant (library-library-cite lib "EVAL-EXPRESSION-SUBSTITUTION" nil nil))
         (invariant-parts (h1-propositions-propositional-proof-conjunct lib invariant))
         (equality (h1-propositions-propositional-proof-modus-ponens
                    lib (cadr invariant-parts) (caddr parts)))
         (quoted (h1-tactics-prover-quoted-truth proof *proof-true*))
         (changed-value (h1-propositions-propositional-proof-conjoin
                         lib (h1-book-disjoin-truth replacement) (cadddr parts) quoted))
         (fold (library-library-cite lib "EVALUATED-DISJOIN" (list changed) nil))
         (changed-value (proof-proof-rewrite core changed-value fold '(1)))
         (restored (proof-proof-rewrite core changed-value equality '(1 1)))
         (fold (library-library-cite lib "EVALUATED-DISJOIN" (list *library-x*) nil))
         (original-value (h1-propositions-proof-transport core restored fold))
         (found (h1-propositions-propositional-proof-conjunct lib original-value)))
      (h1-propositions-propositional-proof-implies-from
       lib (list *library-implies* premise original) (car found)))))

(defun h1-book-disjoin-falsity-of-member (proof)
  (let* ((core (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (membership (list *h1-book-disjoin-member* *library-y* *library-x*))
         (disjunction (list *h1-book-disjoin-any*
                            (h1-book-rewrite-equal-evaluated-list *library-x*)))
         (goal (proof-neg (h1-book-rewrite-equal-evaluated *library-y*))))
    (proof-with-checked-results
        ((premise (h1-book-cofactors-combine (list (proof-neg disjunction) membership)))
         (formula (list *library-implies* premise goal))
         (assumed (h1-arithmetic-proof-assume core premise t))
         (parts (h1-propositions-propositional-proof-conjunct lib assumed))
         (clause-false (car parts))
         (member (cadr parts))
         (expansion (proof-proof-unfold core membership))
         (endp-test (h1-book-disjoin-step-at expansion '(2 1)))
         (stop (h1-arithmetic-proof-assume core endp-test t))
         (selected (h1-propositions-select-value lib expansion stop))
         (empty-member (proof-proof-rewrite core member selected '(1)))
         (subsume (proof-proof-subsume core empty-member
                                      (cons goal (cdr (proof-step-clause empty-member)))))
         (trivial (h1-propositions-propositional-proof-implies-from lib formula subsume))
         (more (h1-arithmetic-proof-assume core endp-test nil))
         (cons-step (h1-book-termination-cons-from-nonatom proof more))
         (shape (h1-book-disjoin-any-evaluated proof *library-x* cons-step))
         (reduced (proof-proof-rewrite core clause-false shape '(1 1)))
         (value (h1-book-disjoin-step-at shape '(2)))
         (head (proof-term-at value 1))
         (condition (h1-arithmetic-proof-assume core head t))
         (selected (h1-propositions-propositional-proof-select lib value condition))
         (impossible (proof-proof-rewrite core reduced selected '(1 1)))
         (quoted (h1-tactics-prover-quoted-truth proof *proof-true*))
         (contradiction (proof-proof-cut core quoted impossible))
         (head-false (proof-proof-front core contradiction (proof-neg head)))
         (selected (h1-propositions-propositional-proof-select lib value head-false))
         (tail-false (proof-proof-rewrite core reduced selected '(1 1)))
         (lookup (h1-propositions-select-value lib expansion more))
         (match-test (h1-book-disjoin-step-at lookup '(2 1)))
         (assumed (h1-arithmetic-proof-assume core match-test t))
         (reversed (h1-propositions-proof-symmetric core assumed))
         (matched (proof-proof-rewrite core head-false reversed '(1 1 1)))
         (assumed (h1-arithmetic-proof-assume core match-test nil))
         (selected (h1-propositions-select-value lib lookup assumed))
         (tail-member (proof-proof-rewrite core member selected '(1)))
         (builtin (library-library-builtin lib 3 *library-x*))
         (descent (proof-proof-discharge core builtin cons-step))
         (tail (list *library-cdr* *library-x*))
         (child (proof-subst formula (list (cons *library-x* tail))))
         (decrease (proof-step-first descent))
         (hypothesis (h1-arithmetic-proof-assume core (proof-ite decrease child *proof-true*) t))
         (child-premise (proof-term-at child 1))
         (evidence (h1-propositions-propositional-proof-conjoin
                    lib child-premise tail-false tail-member))
         (induction (h1-propositions-proof-prove-if core hypothesis descent))
         (recursive (h1-propositions-propositional-proof-modus-ponens lib induction evidence))
         (branch (proof-proof-cases core match-test matched recursive))
         (advanced (h1-propositions-propositional-proof-implies-from lib formula branch))
         (measure (list *library-count* *library-x*))
         (ordinal (descent-measure-ordinal lib measure))
         (cases (proof-proof-cases core endp-test trivial advanced)))
      (proof-proof-induct core ordinal cases formula measure
                          (list (list (list *library-x* tail)))))))

(defun h1-book-disjoin-add-lemma (proof label step)
  (proof-with-checked-results
      ((claim (proof-step-first step))
       (lib (library-library-lemma (h1-tactics-prover-library proof) label claim step nil)))
    (h1-tactics-prover-with-library proof lib)))

(defun h1-book-disjoin-install-disjunctions (proof)
  (proof-with-checked-results
      ((step (h1-book-disjoin-disjoin2-value proof))
       (proof (h1-book-disjoin-add-lemma proof "EVAL-DISJOIN2" step))
       (proof (h1-book-disjoin-define-truth-fold proof))
       (step (h1-book-disjoin-evaluated-disjoin proof))
       (proof (h1-book-disjoin-add-lemma proof "EVALUATED-DISJOIN" step))
       (transfer (h1-book-disjoin-prove-rewrite-transfer proof))
       (recorded (h1-tactics-prover-record-formula proof "REWRITE-CLAUSE-GENERAL" transfer nil))
       (proof (cdr recorded))
       (invariant (h1-book-disjoin-falsity-of-member proof)))
    (let ((core (h1-tactics-prover-proof proof))
          (lib (h1-tactics-prover-library proof)))
      (proof-with-checked-results
          ((premise (h1-book-cofactors-combine
                     (list (list (proof-sym "PSEUDO-TERM-LISTP" "ACL2") *library-x*)
                           (proof-neg
                            (h1-book-rewrite-equal-evaluated
                             (list *h1-book-disjoin-disjoin* *library-x*)))
                           (list *h1-book-disjoin-member* *library-y* *library-x*))))
           (assumed (h1-arithmetic-proof-assume core premise t))
           (parts (h1-book-cofactors-components proof assumed))
           (parts (proof-list-of-length parts 3))
           (false-value (h1-tactics-prover-false-equation proof (cadr parts)))
           (fold (library-library-cite lib "EVALUATED-DISJOIN" (list *library-x*) nil))
           (folded (proof-proof-rewrite core fold false-value '(1 1 1)))
           (value (h1-book-disjoin-step-at folded '(1)))
           (simplified (h1-book-disjoin-simplify proof value))
           (folded (proof-proof-rewrite core folded simplified '(1 1)))
           (not-nil (proof-proof-not-nil core))
           (reversed (h1-propositions-proof-symmetric core folded))
           (false-folded (h1-propositions-library-transport-argument
                          lib not-nil reversed 1))
           (condition (h1-book-disjoin-step-at invariant '(1)))
           (evidence (h1-propositions-propositional-proof-conjoin
                      lib condition false-folded (caddr parts)))
           (result (h1-propositions-propositional-proof-modus-ponens lib invariant evidence))
           (claim (proof-step-first result))
           (proved (h1-propositions-propositional-proof-implies-from
                    lib (list *library-implies* premise claim) result))
           (recorded (h1-tactics-prover-record-formula proof "FALSE-CLAUSE-MEMBER" proved nil)))
        (cdr recorded)))))
