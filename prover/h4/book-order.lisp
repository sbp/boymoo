(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-order-finite* (proof-sym "O-FINP" "ACL2"))
(defconst *h4-book-order-exponent* (proof-sym "O-FIRST-EXPT" "ACL2"))
(defconst *h4-book-order-coefficient* (proof-sym "O-FIRST-COEFF" "ACL2"))
(defconst *h4-book-order-rest* (proof-sym "O-RST" "ACL2"))
(defconst *h4-book-order-boolean* (proof-sym "BOOLEANP" "ACL2"))
(defconst *h4-book-order-fix* (proof-sym "FIX" "ACL2"))
(defconst *h4-book-order-obasics*
  (list *h4-book-order-finite* (proof-cl "ATOM") (proof-cl "=") *proof-not*))
(defconst *h4-book-order-order-self* (proof-sym "H4-ORDINAL-SELF-COMPARISON" "ACL2"))
(defconst *h4-book-order-order-bool* (proof-sym "H4-ORDINAL-COMPARISON-BOOLEAN" "ACL2"))
(defconst *h4-book-order-order-trans* (proof-sym "H4-ORDINAL-TRANSITIVITY" "ACL2"))
(defconst *h4-book-order-order-ties* (proof-sym "H4-ORDINAL-EQUALITY-FROM-ORDER" "ACL2"))
(defconst *h4-book-order-order-origin* (proof-sym "H4-ORDINAL-NONNEGATIVE" "ACL2"))
(defconst *h4-book-order-posp* (proof-sym "POSP" "ACL2"))
(defconst *h4-book-order-ocmp* (proof-sym "OCMP" "ACL2"))
(defconst *h4-book-order-selectors*
  (list *h4-book-order-exponent* *h4-book-order-coefficient* *h4-book-order-rest*))
(defconst *h4-book-order-omega* (proof-sym "OMEGA" "ACL2"))
(defconst *h4-book-order-omega-term* (proof-sym "OMEGA-TERM" "ACL2"))
(defconst *h4-book-order-make-ord* (proof-sym "MAKE-ORD" "ACL2"))

(defun h4-book-order-comparison-equality (formula)
  (and (proof-is-call formula *proof-equal*)
    (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
      (let ((left (cadr parts))
            (right (caddr parts)))
        (and (proof-is-call left *proof-equal*)
          (proof-with-checked-results ((call (proof-term-at left 1)))
            (and (and (proof-is-call call *h4-book-order-ocmp*)
                       (proof-is-call right *proof-ordinal-less*))
              (proof-with-checked-results ((comparison (proof-list-of-length left 3))
                                           (call-parts (proof-list-of-length call 3)))
                (let ((a (cadr call-parts))
                      (b (caddr call-parts))
                      (tag (caddr comparison)))
                  (and (or (and (equal tag (proof-quote (proof-sym "LT" "ACL2")))
                                 (equal (cdr right) (list a b)))
                            (and (equal tag (proof-quote (proof-sym "GT" "ACL2")))
                                 (equal (cdr right) (list b a))))
                    (list a b)))))))))))

(defun h4-book-order-relation-atom (term)
  (if (proof-is-call term *proof-not*)
      (proof-term-at term 1)
    term))

(defun h4-book-order-all-elementary-arguments (arguments)
  (if (endp arguments)
      t
    (and (or (equal (car arguments) *proof-zero*)
             (not (proof-compound (car arguments))))
         (h4-book-order-all-elementary-arguments (cdr arguments)))))

(defun h4-book-order-elementary-relation (term)
  (proof-with-checked-results ((atom (h4-book-order-relation-atom term)))
    (and (or (proof-is-call atom *proof-ordinal-less*)
             (proof-is-call atom *proof-ordinalp*)
             (proof-is-call atom *proof-equal*))
         (h4-book-order-all-elementary-arguments (cdr atom)))))

(defun h4-book-order-all-elementary-relations (terms)
  (if (endp terms)
      t
    (proof-with-checked-results ((elementary (h4-book-order-elementary-relation (car terms))))
      (and elementary
           (h4-book-order-all-elementary-relations (cdr terms))))))

(defun h4-book-order-boolean-order-equality (formula)
  (and (proof-is-call formula *proof-equal*)
    (proof-with-checked-results ((left (proof-term-at formula 1)))
      (and (proof-is-call left *proof-ordinal-less*)
        (proof-with-checked-results ((right (proof-term-at formula 2)))
          (and (proof-is-call right *proof-not*)
            (proof-with-checked-results ((atom (proof-term-at right 1)))
              (and (proof-is-call atom *proof-equal*)
                   (h4-book-order-all-elementary-relations (cdr formula))))))))))

(defun h4-book-order-all-calls (terms head)
  (if (endp terms)
      t
    (and (proof-is-call (car terms) head)
         (h4-book-order-all-calls (cdr terms) head))))

(defun h4-book-order-call-arguments (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results ((argument (proof-term-at (car terms) 1))
                                 (rest (h4-book-order-call-arguments (cdr terms))))
      (cons argument rest))))

(defun h4-book-order-some-compound (terms)
  (and (consp terms)
       (or (proof-compound (car terms))
           (h4-book-order-some-compound (cdr terms)))))

(defun h4-book-order-relation-atoms (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results ((atom (h4-book-order-relation-atom (car terms)))
                                 (rest (h4-book-order-relation-atoms (cdr terms))))
      (cons atom rest))))

(defun h4-book-order-call-in (term heads)
  (and (proof-compound term) (consp term) (member-equal (car term) heads)))

(defun h4-book-order-selector-guards (atoms)
  (if (endp atoms)
      t
    (and (h4-book-order-call-in (car atoms)
                              (list *proof-ordinal-less* *proof-less* *proof-ordinalp*
                                    *h4-book-order-finite* *proof-equal*))
         (h4-book-order-selector-guards (cdr atoms)))))

(defun h4-book-order-atom-arguments (atoms)
  (if (endp atoms)
      nil
    (append (cdar atoms) (h4-book-order-atom-arguments (cdr atoms)))))

(defun h4-book-order-selector-arguments (arguments subjects)
  (if (endp arguments)
      t
    (let ((argument (car arguments)))
      (cond ((member-equal argument subjects)
             (h4-book-order-selector-arguments (cdr arguments) subjects))
            ((h4-book-order-call-in argument *h4-book-order-selectors*)
             (proof-with-checked-results ((subject (proof-term-at argument 1)))
               (and (member-equal subject subjects)
                    (h4-book-order-selector-arguments (cdr arguments) subjects))))))))

(defun h4-book-order-selector-comparison-subjects (goal)
  (cond ((proof-is-call goal *proof-ordinal-less*) (cons t (cdr goal)))
        ((and (proof-is-call goal *proof-less*)
              (h4-book-order-all-calls (cdr goal) *h4-book-order-coefficient*))
         (proof-with-checked-results ((subjects (h4-book-order-call-arguments (cdr goal))))
           (cons t subjects)))))

(defun h4-book-order-selector-comparison (formula)
  (and (proof-is-call formula *library-implies*)
    (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2))
                                 (match (h4-book-order-selector-comparison-subjects (cadr parts))))
      (and match
        (let ((subjects (cdr match)))
          (proof-with-checked-results ((first (proof-term-at subjects 0))
                                       (second (proof-term-at subjects 1)))
            (and (not (or (equal first second) (h4-book-order-some-compound subjects)))
              (proof-with-checked-results ((guards (h4-book-list-types-conjuncts (car parts)))
                                           (atoms (h4-book-order-relation-atoms guards)))
                (and (h4-book-order-selector-guards atoms)
                  (let ((arguments (h4-book-order-atom-arguments atoms)))
                    (proof-with-checked-results
                        ((allowed (h4-book-order-selector-arguments arguments subjects)))
                      (and allowed (h4-book-order-some-compound arguments) subjects))))))))))))

(defun h4-book-order-selector-type-guards (remaining guards goal)
  (if (endp remaining)
      nil
    (let ((part (car remaining)))
      (proof-with-checked-results
          ((subject (and (proof-is-call part *proof-ordinalp*) (proof-term-at part 1))))
        (if (and (proof-is-call part *proof-ordinalp*) (not (proof-compound subject)))
            (let* ((ex (list *h4-book-order-exponent* subject))
                   (coeff (list *h4-book-order-coefficient* subject))
                   (finite (list *h4-book-order-finite* subject))
                   (exact (proof-eq ex *proof-zero*)))
              (if (or (and (equal guards (list part))
                           (member-equal goal
                                         (list (list *proof-ordinalp* ex)
                                               (list *library-natp* coeff)
                                               (proof-eq exact finite)
                                               (proof-eq (proof-eq coeff *proof-zero*)
                                                         (proof-eq subject *proof-zero*))
                                               (proof-eq (list *proof-consp* (list *library-car* subject))
                                                         (proof-neg finite)))))
                      (and (eql (len guards) 2) (member-equal exact guards)
                           (equal goal (list *library-natp* subject))))
                  subject
                (h4-book-order-selector-type-guards (cdr remaining) guards goal)))
          (h4-book-order-selector-type-guards (cdr remaining) guards goal))))))

(defun h4-book-order-selector-type (formula)
  (and (proof-is-call formula *library-implies*)
    (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2))
                                 (guards (h4-book-list-types-conjuncts (car parts))))
      (h4-book-order-selector-type-guards guards guards (cadr parts)))))

(defun h4-book-order-selector-count-match (goal subject selector path)
  (let ((arguments (list (list *library-count* (list selector subject))
                         (list *library-count* subject))))
    (and (or (equal goal (cons *proof-ordinal-less* arguments))
              (equal goal (cons *proof-less* arguments)))
      (list subject selector path))))

(defun h4-book-order-selector-count (formula)
  (and (proof-is-call formula *library-implies*)
    (proof-with-checked-results ((guard (proof-term-at formula 1)))
      (and (proof-is-call guard *proof-not*)
        (proof-with-checked-results ((finite (proof-term-at guard 1)))
          (and (proof-is-call finite *h4-book-order-finite*)
            (proof-with-checked-results ((subject (proof-term-at finite 1)))
              (and (not (proof-compound subject))
                (proof-with-checked-results ((goal (proof-term-at formula 2)))
                  (or (h4-book-order-selector-count-match
                       goal subject *h4-book-order-exponent*
                       (list *library-car* (list *library-car* subject)))
                      (h4-book-order-selector-count-match
                       goal subject *h4-book-order-rest* (list *library-cdr* subject))))))))))))

(defun h4-book-order-omega-comparison (formula)
  (and (proof-is-call formula *library-implies*)
    (proof-with-checked-results ((guard (proof-term-at formula 1)))
      (and (proof-is-call guard *proof-ordinalp*)
        (proof-with-checked-results ((parts (proof-list-of-length formula 3))
                                     (ordinal (proof-list-of-length guard 2)))
          (let ((subject (cadr ordinal)))
            (and (and (equal (caddr parts)
                              (proof-eq (list *proof-ordinal-less* subject (list *h4-book-order-omega*))
                                        (list *h4-book-order-finite* subject)))
                       (not (proof-compound subject)))
              subject)))))))

(defun h4-book-order-some-ordinal-comparison (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results ((atom (h4-book-order-relation-atom (car terms))))
      (or (proof-is-call atom *proof-ordinal-less*)
          (h4-book-order-some-ordinal-comparison (cdr terms))))))

(defun h4-book-order-candidate-relations (given goal)
  (proof-with-checked-results
      ((boolean (h4-book-order-boolean-order-equality goal))
       (wanted (if boolean (cdr goal) (h4-book-list-types-conjuncts goal))))
    (let ((parts (append given wanted)))
      (proof-with-checked-results ((elementary (h4-book-order-all-elementary-relations parts)))
        (and elementary
          (proof-with-checked-results ((strict (h4-book-order-some-ordinal-comparison parts)))
            (and strict
              (proof-with-checked-results ((atoms (h4-book-order-relation-atoms parts)))
                (<= (len (proof-unique (h4-book-order-atom-arguments atoms))) 3)))))))))

(defun h4-book-order-candidate-elementary (formula)
  (if (proof-is-call formula *library-implies*)
      (proof-with-checked-results ((guard (proof-term-at formula 1))
                                   (given (h4-book-list-types-conjuncts guard))
                                   (goal (proof-term-at formula 2)))
        (h4-book-order-candidate-relations given goal))
    (h4-book-order-candidate-relations nil formula)))

(defun h4-book-order-match-p (match)
  (and match (not (equal match 0)) (not (equal match ""))))

(defun h4-book-order-ordinal-candidate (formula)
  (proof-with-checked-results ((comparison (h4-book-order-comparison-equality formula)))
    (if comparison
        t
      (proof-with-checked-results ((selector (h4-book-order-selector-comparison formula)))
        (if selector
            t
          (proof-with-checked-results ((omega (h4-book-order-omega-comparison formula)))
            (if (h4-book-order-match-p omega)
                t
              (proof-with-checked-results ((type (h4-book-order-selector-type formula)))
                (if (h4-book-order-match-p type)
                    t
                  (proof-with-checked-results ((count (h4-book-order-selector-count formula)))
                    (if count t (h4-book-order-candidate-elementary formula))))))))))))

(defmacro h4-book-order-case (p formula test shape positive negative)
  `(let ((order-case-test ,test))
     (proof-with-checked-results
         ((,shape (proof-proof-assume (library-library-proof ,p) order-case-test t))
          (order-positive ,positive)
          (,shape (proof-proof-assume (library-library-proof ,p) order-case-test nil))
          (order-negative ,negative))
       (h4-tactics-tactics-case-of ,p ,formula order-case-test order-positive order-negative))))

(defun h4-book-order-sum-number (p term)
  (cond ((proof-is-call term *proof-plus*)
         (proof-with-checked-results
             ((closure (library-library-axiom p "CLOSURE" (cdr term)))
              (parts (h4-tactics-tactics-conjunct p closure)))
           (car parts)))
        ((proof-is-call term *proof-minus*)
         (proof-with-checked-results
             ((argument (proof-term-at term 1))
              (closure (library-library-axiom p "CLOSURE" (list argument *proof-zero*)))
              (parts (h4-tactics-tactics-conjunct p closure))
              (rest (h4-tactics-tactics-conjunct p (cadr parts)))
              (last (h4-tactics-tactics-conjunct p (cadr rest))))
           (car last)))
        (t '(:failure "failure" ""))))

(defun h4-book-order-zero-plus (p term)
  (proof-with-checked-results
      ((unity (library-library-axiom p "UNICITY-OF-0" (list term)))
       (number-proof (h4-book-order-sum-number p term))
       (fixed (h4-tactics-tactics-normalize p (list *h4-book-order-fix* term)
                                           (list number-proof) (list *h4-book-order-fix*) nil nil)))
    (proof-proof-chain (library-library-proof p) unity (list fixed))))

(defun h4-book-order-sum-differences (p first middle last)
  (let ((proof (library-library-proof p))
        (reverse-middle (library-minus middle))
        (reverse-last (library-minus last)))
    (proof-with-checked-results
        ((together (library-library-axiom p "ASSOCIATIVITY-OF-+"
                                          (list first reverse-middle (library-diff middle last))))
         (associativity (library-library-axiom p "ASSOCIATIVITY-OF-+"
                                               (list reverse-middle middle reverse-last)))
         (joined (proof-proof-symmetric proof associativity))
         (together (proof-proof-rewrite proof together joined '(1 2 2)))
         (commute (library-library-axiom p "COMMUTATIVITY-OF-+" (list reverse-middle middle)))
         (inverse (library-library-axiom p "INVERSE-OF-+" (list middle)))
         (cancel (proof-proof-chain proof commute (list inverse)))
         (together (proof-proof-rewrite proof together cancel '(1 2 2 1)))
         (unit (h4-book-order-zero-plus p reverse-last)))
      (proof-proof-rewrite proof together unit '(1 2 2)))))

(defun h4-book-order-positive-difference (p low high)
  (let* ((proof (library-library-proof p))
         (forward (library-diff low high))
         (reverse (library-diff high low))
         (negated (library-minus reverse)))
    (proof-with-checked-results
        ((sum (h4-book-order-sum-differences p low high low))
         (inverse (library-library-axiom p "INVERSE-OF-+" (list low)))
         (opposite (proof-proof-chain proof sum (list inverse)))
         (commute (library-library-axiom p "COMMUTATIVITY-OF-+" (list forward *proof-zero*)))
         (left-unit (h4-book-order-zero-plus p forward))
         (right-unit (proof-proof-chain proof commute (list left-unit)))
         (vacancy (proof-proof-symmetric proof right-unit))
         (inverse (library-library-axiom p "INVERSE-OF-+" (list reverse)))
         (insert (proof-proof-symmetric proof inverse))
         (restored (proof-proof-rewrite proof vacancy insert '(1 2 2)))
         (associativity (library-library-axiom p "ASSOCIATIVITY-OF-+" (list forward reverse negated)))
         (grouped (proof-proof-symmetric proof associativity))
         (restored (proof-proof-chain proof restored (list grouped)))
         (restored (proof-proof-rewrite proof restored opposite '(1 2 1)))
         (unit (h4-book-order-zero-plus p negated))
         (restored (proof-proof-chain proof restored (list unit)))
         (original (library-library-axiom p "<-ON-OTHERS" (list low high)))
         (original (proof-proof-rewrite proof original restored '(1 2 1)))
         (positive-view (library-library-axiom p "<-ON-OTHERS" (list *proof-zero* reverse)))
         (unit (h4-book-order-zero-plus p negated))
         (positive-view (proof-proof-rewrite proof positive-view unit '(1 2 1)))
         (reversed (proof-proof-symmetric proof positive-view)))
      (proof-proof-chain proof original (list reversed)))))

(defun h4-book-order-primitive-transitive (p first second)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((first-term (proof-step-first first))
         (first-parts (proof-list-of-length first-term 3))
         (second-term (proof-step-first second))
         (second-parts (proof-list-of-length second-term 3)))
      (let ((low (cadr first-parts))
            (middle (caddr first-parts))
            (high (caddr second-parts)))
        (if (not (equal (cadr second-parts) middle))
            '(:failure "failure" "")
          (proof-with-checked-results
              ((first-view (h4-book-order-positive-difference p low middle))
               (first-delta (proof-proof-rewrite proof first first-view '(1)))
               (second-view (h4-book-order-positive-difference p middle high))
               (second-delta (proof-proof-rewrite proof second second-view '(1)))
               (added (library-library-cite p "POSITIVE-SUM"
                                            (list (library-diff high middle) (library-diff middle low))
                                            (list second-delta first-delta)))
               (sum (h4-book-order-sum-differences p high middle low))
               (distance (proof-proof-rewrite proof added sum '(1 2)))
               (comparison (h4-book-order-positive-difference p low high)))
            (proof-proof-transport proof distance comparison)))))))

(defun h4-book-order-primitive-reflexive-value (p argument)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((original (library-library-axiom p "<-ON-OTHERS" (list argument argument)))
         (inverse (library-library-axiom p "INVERSE-OF-+" (list argument)))
         (original (proof-proof-rewrite proof original inverse '(1 2 1)))
         (value (proof-proof-compute proof (library-lt *proof-zero* *proof-zero*) *proof-nil*)))
      (proof-proof-chain proof original (list value)))))

(defun h4-book-order-order-view (p atom evidence expand)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof atom))
         (literal (proof-step-first opened))
         (right (proof-term-at literal 2))
         (body (h4-tactics-tactics-normalize p right evidence
                                            (append *h4-book-order-obasics* expand) nil nil)))
      (proof-proof-chain proof opened (list body)))))

(defun h4-book-order-self-order-value-stop (shape p term)
  (proof-with-checked-results
      ((original (h4-book-order-order-view p term (list shape) nil))
       (reflexive (h4-book-order-primitive-reflexive-value p *library-x*)))
    (proof-proof-chain (library-library-proof p) original (list reflexive))))

(defun h4-book-order-self-order-value-continue (shape hypothesis p term)
  (proof-with-checked-results
      ((original (h4-book-order-order-view p term (list shape) (list *h4-book-order-rest*))))
    (proof-proof-chain (library-library-proof p) original (list hypothesis))))

(defun h4-book-order-self-order-value (p)
  (let* ((proof (library-library-proof p))
         (term (list *proof-ordinal-less* *library-x* *library-x*))
         (goal (proof-eq term *proof-false*))
         (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((shape (proof-proof-assume proof test t))
         (hypothesis (h4-book-flatten-cdr-induction-recurse shape p goal *library-x* nil))
         (step (h4-book-order-self-order-value-continue shape hypothesis p term))
         (shape (proof-proof-assume proof test nil))
         (base (h4-book-order-self-order-value-stop shape p term)))
      (h4-book-flatten-cdr-induction p goal *library-x* base step nil))))

(defun h4-book-order-false-value (p equality)
  (proof-with-checked-results ((literal (proof-step-first equality))
                               (left (proof-term-at literal 1)))
    (h4-tactics-tactics-establish p (proof-neg left) nil (list *proof-not*) (list equality) nil)))

(defun h4-book-order-reflexive-reply (p reflexive argument)
  (let ((proof (library-library-proof p))
        (bindings (list (list *library-x* argument))))
    (case reflexive
      (:primitive (h4-book-order-primitive-reflexive-value p argument))
      (:ordinal (proof-proof-fact proof *h4-book-order-order-self* bindings))
      (otherwise
       (case (car reflexive)
         (:instantiate (proof-proof-instantiate proof (cadr reflexive) bindings))
         (:result (cadr reflexive))
         (otherwise '(:failure "failure" "")))))))

(defun h4-book-order-order-unequal (p strict reflexive)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((literal (proof-step-first strict))
                                 (parts (proof-list-of-length literal 3)))
      (let ((same (proof-eq (cadr parts) (caddr parts))))
        (proof-with-checked-results
            ((assumption (proof-proof-assume proof same t))
             (duplicate (proof-proof-rewrite proof strict assumption '(1 1)))
             (reflexivity (h4-book-order-reflexive-reply p reflexive (caddr parts)))
             (false (h4-book-order-false-value p reflexivity))
             (impossible (proof-proof-cut proof duplicate false)))
          (proof-proof-front proof impossible (proof-neg same)))))))

(defun h4-book-order-reflected-test (p test)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((literal (proof-step-first test)))
      (if (proof-is-call literal *proof-equal*)
          (proof-proof-symmetric proof test)
        (proof-with-checked-results
            ((negated (proof-list-of-length literal 2))
             (parts (proof-list-of-length (cadr negated) 3))
             (symmetry (proof-proof-fact proof (proof-sym "H4-EQUAL-SYMMETRY" "ACL2")
                                        (list (list *library-x* (cadr parts))
                                              (list *library-y* (caddr parts))))))
          (proof-proof-rewrite proof test symmetry '(1 1)))))))

(defun h4-book-order-index-steps (steps dictionary)
  (if (endp steps)
      dictionary
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (h4-book-order-index-steps (cdr steps) (table-put dictionary literal (car steps))))))

(defun h4-book-order-ordinal-components (p step shape)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (unfolded (h4-book-order-order-view p literal (list shape) (list (proof-cl "EQL"))))
       (rewritten (proof-proof-rewrite (library-library-proof p) step unfolded '(1)))
       (parts (h4-book-list-types-conjunct-proofs p rewritten)))
    (h4-book-order-index-steps parts nil)))

(defun h4-book-order-strict-chain (p first second)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((first-literal (proof-step-first first))
         (left (proof-list-of-length first-literal 3))
         (second-literal (proof-step-first second))
         (right (proof-list-of-length second-literal 3))
         (rules (proof-proof-fact proof *h4-book-order-order-trans*
                                  (list (list *library-x* (cadr left))
                                        (list *library-y* (caddr left))
                                        (list *library-z* (caddr right)))))
         (both (h4-book-division-conjunction p (list first second))))
      (h4-tactics-tactics-modus-ponens p rules both))))

(defun h4-book-order-from-ordinal-origin (p step)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (subject (proof-term-at literal 1))
       (rule (proof-proof-fact (library-library-proof p) *h4-book-order-order-origin*
                               (list (list *library-x* subject)))))
    (h4-tactics-tactics-modus-ponens p rule step)))

(defun h4-book-order-true-boolean-value (p positive boolean)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((literal (proof-step-first positive)))
      (let ((test (proof-eq literal *proof-true*)))
        (proof-with-checked-results
            ((type-term (proof-step-first boolean))
             (assumption (proof-proof-assume proof test nil))
             (reduced (h4-tactics-tactics-normalize p type-term (list assumption)
                                                   (list *h4-book-order-boolean* (proof-cl "EQ")) nil nil))
             (rewritten (proof-proof-rewrite proof boolean reduced '(1)))
             (value (proof-proof-rewrite proof positive rewritten '(1)))
             (tidied (proof-proof-tidy proof value)))
          (proof-proof-front proof tidied test))))))

(defun h4-book-order-true-order-value (p positive)
  (proof-with-checked-results
      ((literal (proof-step-first positive))
       (boolean (proof-proof-fact (library-library-proof p) *h4-book-order-order-bool*
                                  (seq-zip (list *library-x* *library-y*) (cdr literal)))))
    (h4-book-order-true-boolean-value p positive boolean)))

(defun h4-book-order-selector-bindings (function subjects)
  (if (endp subjects)
      nil
    (cons (list (car subjects) (list function (car subjects)))
          (h4-book-order-selector-bindings function (cdr subjects)))))

(defun h4-book-order-selector-hypothesis (p formula subjects shape function path)
  (let* ((proof (library-library-proof p))
         (primary (car subjects))
         (bindings (h4-book-order-selector-bindings function subjects))
         (child (list *library-count* (list function primary)))
         (smaller (list *proof-ordinal-less* (list *library-count* path)
                        (list *library-count* primary))))
    (proof-with-checked-results
        ((literal (proof-step-first shape))
         (evidence (descent-hypotheses-init p (list (list literal t)) (list shape)))
         (descent (descent-selector-decrease p smaller evidence))
         (selector (h4-book-order-order-view p (list function primary) (list shape) nil))
         (reversed (proof-proof-symmetric proof selector))
         (descent (proof-proof-rewrite proof (car descent) reversed '(1 1 1)))
         (comparison (proof-step-first descent))
         (instance (proof-subst formula (proof-bindings-table bindings nil)))
         (assumption (proof-proof-assume proof (proof-ite comparison instance *proof-true*) t))
         (step (proof-proof-prove-if proof assumption descent))
         (left (proof-term-at comparison 1)))
      (if (equal left child)
          step
        '(:failure "failure" "")))))

(defun h4-book-order-selector-hypotheses (p formula subjects shape)
  (proof-with-checked-results
      ((primary (proof-term-at subjects 0))
       (exponent (h4-book-order-selector-hypothesis
                  p formula subjects shape *h4-book-order-exponent*
                  (list *library-car* (list *library-car* primary))))
       (rest (h4-book-order-selector-hypothesis
              p formula subjects shape *h4-book-order-rest* (list *library-cdr* primary))))
    (list (cons *h4-book-order-exponent* exponent) (cons *h4-book-order-rest* rest))))

(defun h4-book-order-ordinal-induction-cons-case (shape p formula subjects)
  (proof-with-checked-results ((child (h4-book-order-selector-hypotheses p formula subjects shape)))
    (list shape child)))

(defun h4-book-order-ordinal-induction-finish (p formula subjects primary test yes no)
  (proof-with-checked-results
      ((cases (h4-tactics-tactics-case-of p formula test yes no))
       (ordinal (library-library-builtin p 1 primary)))
    (proof-proof-induct (library-library-proof p) ordinal cases formula
                        (list *library-count* primary)
                        (list (h4-book-order-selector-bindings *h4-book-order-exponent* subjects)
                              (h4-book-order-selector-bindings *h4-book-order-rest* subjects)))))

(defun h4-book-order-ordinal-induction-request-p (value)
  (and (consp value) (eq (car value) :call) (eq (cadr value) :ordinal-induction)))

(defun h4-book-order-ordinal-induction (p formula subjects build)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((primary (proof-term-at subjects 0)))
      (let ((test (list *proof-consp* primary)))
        (proof-with-checked-results
            ((shape (proof-proof-assume proof test t))
             (cons-arguments (h4-book-order-ordinal-induction-cons-case shape p formula subjects)))
          (if (endp build)
              (list* :call :ordinal-induction cons-arguments)
            (proof-with-checked-results ((yes (car build))
                                         (atom (proof-proof-assume proof test nil)))
              (if (endp (cdr build))
                  (list :call :ordinal-induction atom nil)
                (proof-with-checked-results ((no (cadr build)))
                  (h4-book-order-ordinal-induction-finish p formula subjects primary test yes no))))))))))

(defmacro h4-book-order-induct (p formula subjects shape child cons-case atom-case)
  `(let* ((order-subjects ,subjects)
          (order-primary (car order-subjects))
          (order-test (list *proof-consp* order-primary)))
     (proof-with-checked-results
         ((,shape (proof-proof-assume (library-library-proof ,p) order-test t))
          (,child (h4-book-order-selector-hypotheses ,p ,formula order-subjects ,shape))
          (order-cons-case ,cons-case)
          (,shape (proof-proof-assume (library-library-proof ,p) order-test nil))
          (order-atom-case ,atom-case))
       (h4-book-order-ordinal-induction-finish
        ,p ,formula order-subjects order-primary order-test order-cons-case order-atom-case))))

(defun h4-book-order-required-fact (key dictionary)
  (let ((entry (assoc-equal key dictionary)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun h4-book-order-boolean-order-leaf (value p child)
  (cond ((or (equal value *proof-true*) (equal value *proof-false*))
         (h4-tactics-tactics-establish p (list *h4-book-order-boolean* value) nil
                                      (list *h4-book-order-boolean* (proof-cl "EQ")) nil nil))
        ((proof-is-call value *proof-less*)
         (proof-proof-fact (library-library-proof p) "booleanp-<"
                           (seq-zip (list *library-x* *library-y*) (cdr value))))
        ((proof-is-call value *proof-ordinal-less*)
         (proof-with-checked-results ((argument (proof-term-at value 1))
                                      (selector (proof-term-at argument 0)))
           (h4-book-order-required-fact selector child)))
        (t '(:failure "failure" ""))))

(defun h4-book-order-boolean-leaf-replies (requests p child)
  (if (endp requests)
      nil
    (proof-with-checked-results
        ((step (h4-book-order-boolean-order-leaf (caar requests) p child))
         (replies (h4-book-order-boolean-leaf-replies (cdr requests) p child)))
      (cons (cons (car requests) step) replies))))

(defun h4-book-order-boolean-order-visit (y-shape p term x-shape child)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((equality (h4-book-order-order-view p term (list x-shape y-shape) nil))
         (literal (proof-step-first equality))
         (value (proof-term-at literal 2))
         (requests (proof-proof-by-value-leaves proof value nil))
         (replies (h4-book-order-boolean-leaf-replies requests p child))
         (result (proof-proof-by-value proof value (list *h4-book-order-boolean* *proof-result*) replies nil)))
      (library-library-transport-argument p result equality 1))))

(defun h4-book-order-boolean-order-build (x-shape child p term formula)
  (h4-book-order-case p formula (list *proof-consp* *library-y*) y-shape
    (h4-book-order-boolean-order-visit y-shape p term x-shape child)
    (h4-book-order-boolean-order-visit y-shape p term x-shape child)))

(defun h4-book-order-boolean-order (p)
  (let* ((term (list *proof-ordinal-less* *library-x* *library-y*))
         (formula (list *h4-book-order-boolean* term)))
    (h4-book-order-induct p formula (list *library-x* *library-y*) shape child
      (h4-book-order-boolean-order-build shape child p term formula)
      (h4-book-order-boolean-order-build shape nil p term formula))))

(defun h4-book-order-finite-equal (p left right no-forward no-backward integers)
  (let ((proof (library-library-proof p))
        (delta (library-diff right left)))
    (proof-with-checked-results
        ((delta-negative (library-library-axiom p "<-ON-OTHERS" (list right left)))
         (nonnegative (proof-proof-rewrite proof no-backward delta-negative '(1 1)))
         (comparison (library-library-comparison p left right integers))
         (nonpositive (proof-proof-rewrite proof no-forward comparison '(1 1)))
         (integral (library-library-type-of p delta integers))
         (natural (library-library-cite p "NATURAL-FROM-BOUNDS" (list delta)
                                        (list integral nonnegative)))
         (zero (proof-proof-use proof *h4-book-arithmetic-natural-nonpositive-zero*
                                (list (list *library-x* delta)) (list natural nonpositive)))
         (expanded (proof-proof-reflexive proof (library-plus delta left)))
         (collapsed (proof-proof-rewrite proof expanded zero '(1 2 1)))
         (expanded-literal (proof-step-first expanded))
         (sum (proof-term-at expanded-literal 1))
         (left-equality (library-library-linear-equal p sum right integers))
         (left-equality (proof-proof-symmetric proof left-equality))
         (collapsed-literal (proof-step-first collapsed))
         (unit (proof-term-at collapsed-literal 2))
         (right-equality (library-library-linear-equal p unit left integers))
         (restored (proof-proof-chain proof left-equality (list collapsed right-equality))))
      (proof-proof-symmetric proof restored))))

(defun h4-book-order-reconstruct-ordinal (p term shape head-shape)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((raw-axiom (library-library-axiom p "CAR-CDR-ELIM" (list term)))
         (raw (h4-tactics-tactics-modus-ponens p raw-axiom shape))
         (head-axiom (library-library-axiom p "CAR-CDR-ELIM" (list (list *library-car* term))))
         (head (h4-tactics-tactics-modus-ponens p head-axiom head-shape))
         (head-reversed (proof-proof-symmetric proof head))
         (raw (proof-proof-rewrite proof raw head-reversed '(1 1 1)))
         (ex (h4-book-order-order-view p (list *h4-book-order-exponent* term) (list shape) nil))
         (coeff (h4-book-order-order-view p (list *h4-book-order-coefficient* term) (list shape) nil))
         (tail (proof-proof-unfold proof (list *h4-book-order-rest* term)))
         (ex-reversed (proof-proof-symmetric proof ex))
         (raw (proof-proof-rewrite proof raw ex-reversed '(1 1 1 1)))
         (coeff-reversed (proof-proof-symmetric proof coeff))
         (raw (proof-proof-rewrite proof raw coeff-reversed '(1 1 1 2)))
         (tail-reversed (proof-proof-symmetric proof tail)))
      (proof-proof-rewrite proof raw tail-reversed '(1 1 2)))))

(defun h4-book-order-origin-bound-branch (shape p order premise formula hypothesis)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((value (h4-book-order-order-view p order (list shape) nil))
         (literal (proof-step-first value))
         (right (proof-term-at literal 2)))
      (if (equal right *proof-false*)
          (proof-with-checked-results ((false (h4-book-order-false-value p value)))
            (h4-tactics-tactics-imply p formula false))
        (proof-with-checked-results
            ((opened (h4-book-order-order-view p premise (list shape) nil))
             (natural (proof-proof-rewrite proof hypothesis opened '(1)))
             (nonnegative (library-library-cite p "NATURAL-NONNEGATIVE" (list *library-x*) (list natural)))
             (reversed (proof-proof-symmetric proof value))
             (result (proof-proof-rewrite proof nonnegative reversed '(1 1))))
          (h4-tactics-tactics-imply p formula result))))))

(defun h4-book-order-origin-bound (p)
  (let* ((order (list *proof-ordinal-less* *library-x* *proof-zero*))
         (premise (list *proof-ordinalp* *library-x*))
         (formula (list *library-implies* premise (proof-neg order))))
    (proof-with-checked-results ((hypothesis (proof-proof-assume (library-library-proof p) premise t)))
      (h4-book-order-case p formula (list *proof-consp* *library-x*) shape
        (h4-book-order-origin-bound-branch shape p order premise formula hypothesis)
        (h4-book-order-origin-bound-branch shape p order premise formula hypothesis)))))

(defun h4-book-order-transitive-order-show-order (value evidence p ac)
  (proof-with-checked-results ((opened (h4-book-order-order-view p ac evidence nil)))
    (proof-proof-transport (library-library-proof p) value opened)))

(defun h4-book-order-transitive-order-impossible (source evidence p ac)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first source))
         (opened (h4-book-order-order-view p literal evidence nil))
         (contradiction (proof-proof-rewrite proof source opened '(1)))
         (result (proof-step-first contradiction)))
      (if (equal result *proof-false*)
          (proof-proof-subsume proof contradiction (cons ac (cdr (proof-step-clause contradiction))))
        '(:failure "failure" "")))))

(defun h4-book-order-transitive-rewrite (p step term facts)
  (proof-with-checked-results ((opened (h4-book-order-order-view p term facts nil)))
    (proof-proof-rewrite (library-library-proof p) step opened '(1))))

(defun h4-book-order-transitive-combined (p first last ab bc facts ab-sign bc-sign same-ab same-bc
                                           function child)
  (let ((proof (library-library-proof p)))
    (cond
     (same-ab
      (proof-with-checked-results ((upper (h4-book-order-transitive-rewrite p last bc facts))
                                   (reversed (proof-proof-symmetric proof ab-sign)))
        (proof-proof-rewrite proof upper reversed '(1 1))))
     (same-bc
      (proof-with-checked-results ((lower (h4-book-order-transitive-rewrite p first ab facts)))
        (proof-proof-rewrite proof lower bc-sign '(1 2))))
     (t
      (proof-with-checked-results ((lower (h4-book-order-transitive-rewrite p first ab facts))
                                   (upper (h4-book-order-transitive-rewrite p last bc facts)))
        (if (equal function *h4-book-order-exponent*)
            (proof-with-checked-results
                ((hypothesis (h4-book-order-required-fact *h4-book-order-exponent* child))
                 (both (h4-book-division-conjunction p (list lower upper))))
              (h4-tactics-tactics-modus-ponens p hypothesis both))
          (h4-book-order-primitive-transitive p lower upper)))))))

(defun h4-book-order-transitive-tail (facts p child first last self-order ab bc ac)
  (declare (ignore self-order))
  (proof-with-checked-results
      ((low (h4-book-order-transitive-rewrite p first ab facts))
       (high (h4-book-order-transitive-rewrite p last bc facts))
       (hypothesis (h4-book-order-required-fact *h4-book-order-rest* child))
       (both (h4-book-division-conjunction p (list low high)))
       (tail (h4-tactics-tactics-modus-ponens p hypothesis both)))
    (h4-book-order-transitive-order-show-order tail facts p ac)))

(defun h4-book-order-transitive-distinct (ab-sign bc-sign p facts child first last self-order
                                                ab bc ac function same-ab same-bc)
  (proof-with-checked-results
      ((combined (h4-book-order-transitive-combined
                  p first last ab bc facts ab-sign bc-sign same-ab same-bc function child))
       (different (h4-book-order-order-unequal
                   p combined (if (equal function *h4-book-order-exponent*)
                                  (list :instantiate self-order)
                                :primitive))))
    (h4-book-order-transitive-order-show-order combined (append facts (list different)) p ac)))

(defmacro h4-book-order-transitive-order-branch
    (ab-sign bc-sign p facts child first last self-order ab bc ac function equal-ab equal-bc next)
  `(let ((field-facts (append ,facts (list ,ab-sign ,bc-sign))))
     (proof-with-checked-results ((ab-literal (proof-step-first ,ab-sign))
                                  (bc-literal (proof-step-first ,bc-sign)))
       (let ((same-ab (equal ab-literal ,equal-ab))
             (same-bc (equal bc-literal ,equal-bc)))
         (if (and same-ab same-bc)
             (proof-with-checked-results
                 ((equal-ac (proof-proof-chain (library-library-proof ,p) ,ab-sign (list ,bc-sign))))
               (,next (append field-facts (list equal-ac)) ,p ,child ,first ,last ,self-order ,ab ,bc ,ac))
           (h4-book-order-transitive-distinct
            ,ab-sign ,bc-sign ,p field-facts ,child ,first ,last ,self-order ,ab ,bc ,ac ,function same-ab same-bc))))))

(defmacro h4-book-order-transitive-order-second
    (sign p facts child first last self-order ab bc ac function equal-ab equal-bc next)
  `(h4-book-order-case ,p ,ac ,equal-bc bc-sign
     (h4-book-order-transitive-order-branch
      ,sign bc-sign ,p ,facts ,child ,first ,last ,self-order ,ab ,bc ,ac ,function ,equal-ab ,equal-bc ,next)
     (h4-book-order-transitive-order-branch
      ,sign bc-sign ,p ,facts ,child ,first ,last ,self-order ,ab ,bc ,ac ,function ,equal-ab ,equal-bc ,next)))

(defmacro h4-book-order-transitive-field-cases (function next facts p child first last self-order ab bc ac)
  `(let ((equal-ab (proof-eq (list ,function *library-x*) (list ,function *library-y*)))
         (equal-bc (proof-eq (list ,function *library-y*) (list ,function *library-z*))))
     (h4-book-order-case ,p ,ac equal-ab ab-sign
       (h4-book-order-transitive-order-second
        ab-sign ,p ,facts ,child ,first ,last ,self-order ,ab ,bc ,ac ,function equal-ab equal-bc ,next)
       (h4-book-order-transitive-order-second
        ab-sign ,p ,facts ,child ,first ,last ,self-order ,ab ,bc ,ac ,function equal-ab equal-bc ,next))))

(defun h4-book-order-transitive-coefficient (facts p child first last self-order ab bc ac)
  (h4-book-order-transitive-field-cases *h4-book-order-coefficient* h4-book-order-transitive-tail
                                        facts p child first last self-order ab bc ac))

(defun h4-book-order-transitive-order-field (rank facts p child first last self-order ab bc ac)
  (case rank
    (2 (h4-book-order-transitive-tail facts p child first last self-order ab bc ac))
    (1 (h4-book-order-transitive-coefficient facts p child first last self-order ab bc ac))
    (otherwise
     (h4-book-order-transitive-field-cases *h4-book-order-exponent* h4-book-order-transitive-coefficient
                                           facts p child first last self-order ab bc ac))))

(defun h4-book-order-transitive-order-compare-fields (child evidence p first last self-order ab bc ac)
  (h4-book-order-transitive-order-field 0 evidence p child first last self-order ab bc ac))

(defun h4-book-order-transitive-order-against-z (z-shape p x-shape y-shape child first last self-order
                                                    ab bc ac formula)
  (let ((evidence (list x-shape y-shape z-shape)))
    (proof-with-checked-results ((a-shape (proof-step-first x-shape))
                                 (b-shape (proof-step-first y-shape))
                                 (c-shape (proof-step-first z-shape)))
      (let ((a-cons (proof-is-call a-shape *proof-consp*))
            (b-cons (proof-is-call b-shape *proof-consp*))
            (c-cons (proof-is-call c-shape *proof-consp*)))
        (proof-with-checked-results
            ((result
              (cond ((and a-cons (not b-cons))
                     (h4-book-order-transitive-order-impossible first evidence p ac))
                    ((and b-cons (not c-cons))
                     (h4-book-order-transitive-order-impossible last evidence p ac))
                    ((and (not a-cons) c-cons)
                     (proof-with-checked-results ((opened (h4-book-order-order-view p ac evidence nil)))
                       (h4-tactics-tactics-non-nil p opened)))
                    (a-cons
                     (h4-book-order-transitive-order-compare-fields child evidence p first last self-order ab bc ac))
                    (t
                     (proof-with-checked-results
                         ((low (h4-book-order-transitive-rewrite p first ab evidence))
                          (high (h4-book-order-transitive-rewrite p last bc evidence))
                          (transitive (h4-book-order-primitive-transitive p low high)))
                       (h4-book-order-transitive-order-show-order transitive evidence p ac))))))
          (h4-tactics-tactics-imply p formula result))))))

(defun h4-book-order-transitive-order-against-y (y-shape p x-shape child first last self-order
                                                    ab bc ac formula)
  (h4-book-order-case p formula (list *proof-consp* *library-z*) z-shape
    (h4-book-order-transitive-order-against-z z-shape p x-shape y-shape child first last self-order
                                            ab bc ac formula)
    (h4-book-order-transitive-order-against-z z-shape p x-shape y-shape child first last self-order
                                            ab bc ac formula)))

(defun h4-book-order-transitive-order-build (x-shape child p first last self-order ab bc ac formula)
  (h4-book-order-case p formula (list *proof-consp* *library-y*) y-shape
    (h4-book-order-transitive-order-against-y y-shape p x-shape child first last self-order ab bc ac formula)
    (h4-book-order-transitive-order-against-y y-shape p x-shape child first last self-order ab bc ac formula)))

(defun h4-book-order-transitive-order (p)
  (let* ((proof (library-library-proof p))
         (ab (list *proof-ordinal-less* *library-x* *library-y*))
         (bc (list *proof-ordinal-less* *library-y* *library-z*))
         (ac (list *proof-ordinal-less* *library-x* *library-z*))
         (guard (proof-ite ab bc *proof-false*))
         (formula (list *library-implies* guard ac)))
    (proof-with-checked-results
        ((given (proof-proof-assume proof guard t))
         (conjuncts (h4-tactics-tactics-conjunct p given))
         (self-order (if (assoc-equal *h4-book-order-order-self* (proof-proof-facts proof))
                         (proof-proof-fact proof *h4-book-order-order-self* nil)
                       (h4-book-order-self-order-value p))))
      (let ((first (car conjuncts))
            (last (cadr conjuncts)))
        (h4-book-order-induct p formula (list *library-x* *library-y* *library-z*) shape child
          (h4-book-order-transitive-order-build shape child p first last self-order ab bc ac formula)
          (h4-book-order-transitive-order-build shape nil p first last self-order ab bc ac formula))))))

(defun h4-book-order-equal-when-unordered-restrict (step evidence p)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (atom (proof-term-at literal 1))
       (opened (h4-book-order-order-view p atom evidence nil)))
    (proof-proof-rewrite (library-library-proof p) step opened '(1 1))))

(defun h4-book-order-equal-when-unordered-components (function comparison p child x-parts y-parts
                                                         no-forward no-backward)
  (let ((a (list function *library-x*))
        (b (list function *library-y*)))
    (proof-with-checked-results
        ((hypothesis (h4-book-order-required-fact function child))
         (x-type (h4-book-order-required-fact (list *proof-ordinalp* a) x-parts))
         (y-type (h4-book-order-required-fact (list *proof-ordinalp* b) y-parts))
         (no-forward (h4-book-order-equal-when-unordered-restrict no-forward comparison p))
         (no-backward (h4-book-order-equal-when-unordered-restrict no-backward comparison p))
         (both (h4-book-division-conjunction p (list x-type y-type no-forward no-backward))))
      (h4-tactics-tactics-modus-ponens p hypothesis both))))

(defun h4-book-order-coefficient-type (p coefficient parts)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((positive (h4-book-order-required-fact (list *h4-book-order-posp* coefficient) parts))
         (literal (proof-step-first positive))
         (opened (proof-proof-unfold proof literal))
         (rewritten (proof-proof-rewrite proof positive opened '(1)))
         (types (h4-tactics-tactics-conjunct p rewritten)))
      (car types))))

(defun h4-book-order-equal-when-unordered-coeff-different (different p ex-evidence coeff-x coeff-y
                                                              x-parts y-parts no-forward no-backward)
  (proof-with-checked-results
      ((reflected (h4-book-order-reflected-test p different)))
    (let ((cases (append ex-evidence (list different reflected))))
      (proof-with-checked-results
          ((x-type (h4-book-order-coefficient-type p coeff-x x-parts))
           (y-type (h4-book-order-coefficient-type p coeff-y y-parts))
           (no-forward (h4-book-order-equal-when-unordered-restrict no-forward cases p))
           (no-backward (h4-book-order-equal-when-unordered-restrict no-backward cases p)))
        (h4-book-order-finite-equal p coeff-x coeff-y no-forward no-backward (list x-type y-type))))))

(defun h4-book-order-equal-when-unordered-identify (x-shape y-shape child p x-type y-type
                                                      no-forward no-backward)
  (let* ((proof (library-library-proof p))
         (evidence (list x-shape y-shape))
         (ex (list *h4-book-order-exponent* *library-x*))
         (ey (list *h4-book-order-exponent* *library-y*))
         (ex-test (proof-eq ex ey)))
    (proof-with-checked-results
        ((x-parts (h4-book-order-ordinal-components p x-type x-shape))
         (y-parts (h4-book-order-ordinal-components p y-type y-shape))
         (ex-equal
          (h4-book-order-case p ex-test ex-test same
            same
            (proof-with-checked-results ((reflected (h4-book-order-reflected-test p same)))
              (h4-book-order-equal-when-unordered-components
               *h4-book-order-exponent* (append evidence (list same reflected)) p child x-parts y-parts
               no-forward no-backward))))
         (ex-reversed (proof-proof-symmetric proof ex-equal)))
      (let* ((ex-evidence (append evidence (list ex-equal ex-reversed)))
             (coeff-x (list *h4-book-order-coefficient* *library-x*))
             (coeff-y (list *h4-book-order-coefficient* *library-y*))
             (coeff-test (proof-eq coeff-x coeff-y)))
        (proof-with-checked-results
            ((coeff-equal
              (h4-book-order-case p coeff-test coeff-test same
                same
                (h4-book-order-equal-when-unordered-coeff-different
                 same p ex-evidence coeff-x coeff-y x-parts y-parts no-forward no-backward)))
             (coeff-reversed (proof-proof-symmetric proof coeff-equal))
             (tail-equal
              (h4-book-order-equal-when-unordered-components
               *h4-book-order-rest* (append ex-evidence (list coeff-equal coeff-reversed))
               p child x-parts y-parts no-forward no-backward))
             (x-head (h4-book-order-required-fact (list *proof-consp* (list *library-car* *library-x*))
                                                   x-parts))
             (raw-x (h4-book-order-reconstruct-ordinal p *library-x* x-shape x-head))
             (y-head (h4-book-order-required-fact (list *proof-consp* (list *library-car* *library-y*))
                                                   y-parts))
             (raw-y (h4-book-order-reconstruct-ordinal p *library-y* y-shape y-head))
             (x-raw-literal (proof-step-first raw-x))
             (x-canonical (proof-term-at x-raw-literal 1))
             (canonical (proof-proof-reflexive proof x-canonical))
             (canonical (proof-proof-rewrite proof canonical ex-equal '(1 2 1 1)))
             (canonical (proof-proof-rewrite proof canonical coeff-equal '(1 2 1 2)))
             (canonical (proof-proof-rewrite proof canonical tail-equal '(1 2 2)))
             (raw-x-reversed (proof-proof-symmetric proof raw-x)))
          (proof-proof-chain proof raw-x-reversed (list canonical raw-y)))))))

(defun h4-book-order-ordinal-natural-integer (p subject step evidence)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (view (h4-book-order-order-view p literal evidence nil))
       (natural (proof-proof-rewrite (library-library-proof p) step view '(1))))
    (library-library-cite p "NATURAL-INTEGER" (list subject) (list natural))))

(defun h4-book-order-equal-when-unordered-against-y (y-shape p x-shape child formula xy yx
                                                        x-type y-type no-forward no-backward)
  (let ((proof (library-library-proof p))
        (evidence (list x-shape y-shape)))
    (proof-with-checked-results ((x-literal (proof-step-first x-shape))
                                 (y-literal (proof-step-first y-shape)))
      (let ((x-cons (proof-is-call x-literal *proof-consp*))
            (y-cons (proof-is-call y-literal *proof-consp*)))
        (proof-with-checked-results
            ((result
              (cond
               ((and x-cons y-cons)
                (h4-book-order-equal-when-unordered-identify x-shape y-shape child p x-type y-type
                                                            no-forward no-backward))
               ((or x-cons y-cons)
                (let ((order (if x-cons yx xy))
                      (contrary (if x-cons no-backward no-forward)))
                  (proof-with-checked-results
                      ((opened (h4-book-order-order-view p order evidence nil))
                       (truth (h4-tactics-tactics-non-nil p opened))
                       (impossible (proof-proof-cut proof truth contrary)))
                    (proof-proof-subsume proof impossible (cons (caddr formula) (proof-step-clause impossible))))))
               (t
                (proof-with-checked-results
                    ((x-integer (h4-book-order-ordinal-natural-integer p *library-x* x-type evidence))
                     (y-integer (h4-book-order-ordinal-natural-integer p *library-y* y-type evidence))
                     (no-forward (h4-book-order-equal-when-unordered-restrict no-forward evidence p))
                     (no-backward (h4-book-order-equal-when-unordered-restrict no-backward evidence p)))
                  (h4-book-order-finite-equal p *library-x* *library-y* no-forward no-backward
                                              (list x-integer y-integer)))))))
          (h4-tactics-tactics-imply p formula result))))))

(defun h4-book-order-equal-when-unordered-build (x-shape child p formula xy yx x-type y-type
                                                    no-forward no-backward)
  (h4-book-order-case p formula (list *proof-consp* *library-y*) y-shape
    (h4-book-order-equal-when-unordered-against-y y-shape p x-shape child formula xy yx x-type y-type
                                                 no-forward no-backward)
    (h4-book-order-equal-when-unordered-against-y y-shape p x-shape child formula xy yx x-type y-type
                                                 no-forward no-backward)))

(defun h4-book-order-equal-when-unordered (p)
  (let* ((proof (library-library-proof p))
         (op-x (list *proof-ordinalp* *library-x*))
         (op-y (list *proof-ordinalp* *library-y*))
         (xy (list *proof-ordinal-less* *library-x* *library-y*))
         (yx (list *proof-ordinal-less* *library-y* *library-x*))
         (guard (proof-ite op-x
                           (proof-ite op-y (proof-ite (proof-neg xy) (proof-neg yx) *proof-false*) *proof-false*)
                           *proof-false*))
         (formula (list *library-implies* guard (proof-eq *library-x* *library-y*))))
    (proof-with-checked-results
        ((given (proof-proof-assume proof guard t))
         (x-and-rest (h4-tactics-tactics-conjunct p given))
         (y-and-directions (h4-tactics-tactics-conjunct p (cadr x-and-rest)))
         (no-directions (h4-tactics-tactics-conjunct p (cadr y-and-directions))))
      (let ((x-type (car x-and-rest))
            (y-type (car y-and-directions))
            (no-forward (car no-directions))
            (no-backward (cadr no-directions)))
        (h4-book-order-induct p formula (list *library-x* *library-y*) shape child
          (h4-book-order-equal-when-unordered-build shape child p formula xy yx x-type y-type
                                                    no-forward no-backward)
          (h4-book-order-equal-when-unordered-build shape nil p formula xy yx x-type y-type
                                                    no-forward no-backward))))))

(defun h4-book-order-support-clauses (names facts)
  (if (endp names)
      nil
    (proof-with-checked-results ((clause (h4-book-order-required-fact (car names) facts))
                                 (clauses (h4-book-order-support-clauses (cdr names) facts)))
      (acons (car names) clause clauses))))

(defun h4-book-order-order-support (p)
  (proof-with-checked-results
      ((step (h4-book-order-self-order-value p))
       (result (h4-tactics-tactics-local-lemma p *h4-book-order-order-self* step))
       (p (cdr result))
       (step (h4-book-order-boolean-order p))
       (result (h4-tactics-tactics-local-lemma p *h4-book-order-order-bool* step))
       (p (cdr result))
       (step (h4-book-order-transitive-order p))
       (result (h4-tactics-tactics-local-lemma p *h4-book-order-order-trans* step))
       (p (cdr result))
       (step (h4-book-order-equal-when-unordered p))
       (result (h4-tactics-tactics-local-lemma p *h4-book-order-order-ties* step))
       (p (cdr result))
       (step (h4-book-order-origin-bound p))
       (result (h4-tactics-tactics-local-lemma p *h4-book-order-order-origin* step))
       (p (cdr result))
       (support (h4-book-order-support-clauses
                 (list *h4-book-order-order-self* *h4-book-order-order-bool* *h4-book-order-order-trans*
                       *h4-book-order-order-ties* *h4-book-order-order-origin*)
                 (proof-proof-facts (library-library-proof p)))))
    (cons support p)))

(defun h4-book-order-selector-views (selectors p subject evidence)
  (if (endp selectors)
      nil
    (proof-with-checked-results
        ((step (h4-book-order-order-view p (list (car selectors) subject) evidence nil))
         (rest (h4-book-order-selector-views (cdr selectors) p subject evidence)))
      (cons step rest))))

(defun h4-book-order-nonzero-subject (p subject shape)
  (let* ((proof (library-library-proof p))
         (same (proof-eq subject *proof-zero*)))
    (proof-with-checked-results
        ((assumption (proof-proof-assume proof same t))
         (clash (proof-proof-rewrite proof shape assumption '(1 1)))
         (computed (proof-proof-compute proof (list *proof-consp* *proof-zero*) *proof-nil*))
         (contradiction (proof-proof-rewrite proof clash computed '(1)))
         (tidied (proof-proof-tidy proof contradiction)))
      (proof-proof-front proof tidied (proof-neg same)))))

(defun h4-book-order-selector-types-finish (p formula goal subject shape support rewrites)
  (proof-with-checked-results
      ((needed (h4-book-order-index-steps support nil))
       (right (and (proof-is-call goal *proof-equal*) (proof-term-at goal 2)))
       (shape-literal (and (equal right (proof-eq subject *proof-zero*)) (proof-step-first shape)))
       (needed
        (if (proof-is-call shape-literal *proof-consp*)
            (proof-with-checked-results ((different (h4-book-order-nonzero-subject p subject shape))
                                         (literal (proof-step-first different)))
              (table-put needed literal different))
          needed))
       (result (h4-tactics-tactics-establish p goal (table-values needed)
                                             *h4-book-order-obasics* rewrites nil)))
    (h4-tactics-tactics-imply p formula result)))

(defun h4-book-order-selector-exponent-nonzero (p ex parts)
  (proof-with-checked-results
      ((no-zero (h4-book-order-required-fact (proof-neg (list (proof-cl "EQL") *proof-zero* ex)) parts))
       (negative (proof-step-first no-zero))
       (test (proof-term-at negative 1))
       (view (h4-tactics-tactics-normalize p test nil (list (proof-cl "EQL")) nil nil))
       (rewritten (proof-proof-rewrite (library-library-proof p) no-zero view '(1 1))))
    (h4-book-order-reflected-test p rewritten)))

(defun h4-book-order-coefficient-proofs (p coefficient parts)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((step (h4-book-order-required-fact (list *h4-book-order-posp* coefficient) parts))
         (literal (proof-step-first step))
         (opened (proof-proof-unfold proof literal))
         (rewritten (proof-proof-rewrite proof step opened '(1))))
      (h4-tactics-tactics-conjunct p rewritten))))

(defun h4-book-order-selector-types-cons (p formula goal subject ex coeff evidence ordinal shape)
  (let ((proof (library-library-proof p))
        (car-term (list *library-car* subject)))
    (proof-with-checked-results
        ((parts (h4-book-order-ordinal-components p ordinal shape))
         (different (h4-book-order-selector-exponent-nonzero p ex parts))
         (types (h4-book-order-coefficient-proofs p coeff parts))
         (nonnegative (library-library-cite p "POSITIVE-NONNEGATIVE" (list coeff) types))
         (natural (library-library-cite p "NATURAL-FROM-BOUNDS" (list coeff)
                                        (list (car types) nonnegative)))
         (nonzero (h4-book-order-order-unequal p (cadr types) :primitive))
         (reversed (h4-book-order-reflected-test p nonzero))
         (head-pair (h4-book-order-required-fact (list *proof-consp* car-term) parts))
         (boolean (proof-proof-fact proof "booleanp-consp" (list (list *library-x* car-term))))
         (rewrite (h4-book-order-true-boolean-value p head-pair boolean)))
      (let ((zero-ex (assoc-equal (proof-eq ex *proof-zero*) evidence)))
        (if zero-ex
            (proof-with-checked-results
                ((conflict (proof-proof-cut proof (cdr zero-ex) different))
                 (result (proof-proof-subsume proof conflict (cons goal (proof-step-clause conflict)))))
              (h4-tactics-tactics-imply p formula result))
          (h4-book-order-selector-types-finish
           p formula goal subject shape (cons shape (append (table-values parts) (list different natural reversed)))
           (list rewrite)))))))

(defun h4-book-order-selector-types-atom (p formula goal subject ordinal shape)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first ordinal))
         (opened (h4-book-order-order-view p literal (list shape) nil))
         (natural (proof-proof-rewrite proof ordinal opened '(1)))
         (zero (library-library-natural p *proof-zero*))
         (zero-ordinal (library-library-cite p "NATURAL-ORDINAL" (list *proof-zero*) (list zero)))
         (rewrites (h4-book-order-selector-views
                    (list *h4-book-order-exponent* *h4-book-order-coefficient*) p subject (list shape)))
         (finite (h4-book-order-order-view p (list *h4-book-order-finite* subject) (list shape) nil))
         (finite-literal (proof-step-first finite))
         (finite-value (proof-term-at finite-literal 2))
         (shape-value (h4-tactics-tactics-nil-value p shape))
         (truth (h4-tactics-tactics-normalize p finite-value nil (list *proof-not*) (list shape-value) nil))
         (finite-true (proof-proof-chain proof finite (list truth)))
         (completion (library-library-axiom p "COMPLETION-OF-CAR" (list subject)))
         (completion-literal (proof-step-first completion))
         (completion-body (proof-term-at completion-literal 2))
         (if-false (proof-proof-if-false proof completion-body))
         (atom-car (proof-proof-chain proof completion (list if-false)))
         (atom-car (proof-proof-discharge proof atom-car shape)))
      (h4-book-order-selector-types-finish
       p formula goal subject shape (list shape natural zero-ordinal)
       (append rewrites (list finite-true atom-car))))))

(defun h4-book-order-selector-types-proof-with-shape (shape p formula goal subject ex coeff evidence ordinal)
  (proof-with-checked-results ((literal (proof-step-first shape)))
    (if (proof-is-call literal *proof-consp*)
        (h4-book-order-selector-types-cons p formula goal subject ex coeff evidence ordinal shape)
      (h4-book-order-selector-types-atom p formula goal subject ordinal shape))))

(defun h4-book-order-selector-types-proof (p formula subject)
  (proof-with-checked-results
      ((parts (proof-list-of-length (cdr formula) 2))
       (assumption (proof-proof-assume (library-library-proof p) (car parts) t))
       (conjuncts (h4-book-list-types-conjunct-proofs p assumption))
       (evidence (h4-book-order-index-steps conjuncts nil))
       (ordinal (h4-book-order-required-fact (list *proof-ordinalp* subject) evidence)))
    (let ((goal (cadr parts))
          (ex (list *h4-book-order-exponent* subject))
          (coeff (list *h4-book-order-coefficient* subject)))
      (h4-book-order-case p formula (list *proof-consp* subject) shape
        (h4-book-order-selector-types-proof-with-shape shape p formula goal subject ex coeff evidence ordinal)
        (h4-book-order-selector-types-proof-with-shape shape p formula goal subject ex coeff evidence ordinal)))))

(defun h4-book-order-selector-count-primitive (p step)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (measures (proof-list-of-length (cdr literal) 2))
         (left-int (library-library-cite p "COUNT-INTEGER" (cdar measures) nil))
         (right-int (library-library-cite p "COUNT-INTEGER" (cdadr measures) nil))
         (finite-order (library-library-cite p "FINITE-ORDER" measures (list left-int right-int))))
      (proof-proof-rewrite proof step finite-order '(1)))))

(defun h4-book-order-selector-count-proof (p formula match)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((match (proof-list-of-length match 3))
                                 (guard (proof-term-at formula 1)))
      (let ((subject (car match))
            (selector (cadr match))
            (child (caddr match)))
        (proof-with-checked-results
            ((nonfinite (proof-proof-assume proof guard t))
             (atom (proof-proof-assume proof (list *proof-consp* subject) nil))
             (finite (h4-tactics-tactics-establish p (list *h4-book-order-finite* subject)
                                                   (list atom) *h4-book-order-obasics* nil nil))
             (shape-cut (proof-proof-cut proof finite nonfinite))
             (shape (proof-proof-front proof shape-cut (list *proof-consp* subject)))
             (hypotheses (descent-hypotheses-init p nil (list shape)))
             (descent (descent-selector-decrease
                       p (list *proof-ordinal-less* (list *library-count* child) (list *library-count* subject))
                       hypotheses))
             (selected (h4-book-order-order-view p (list selector subject) (list shape) nil))
             (reversed (proof-proof-symmetric proof selected))
             (step (proof-proof-rewrite proof (car descent) reversed '(1 1 1)))
             (goal (proof-term-at formula 2))
             (step (if (proof-is-call goal *proof-less*)
                       (h4-book-order-selector-count-primitive p step)
                     step)))
          (h4-tactics-tactics-imply p formula step))))))

(defun h4-book-order-positive-lower-bound (p positive integral)
  (proof-with-checked-results
      ((literal (proof-step-first positive))
       (value (proof-term-at literal 2))
       (discrete (proof-proof-fact (library-library-proof p) "integer-discrete"
                                   (list (list *library-x* value))))
       (both (h4-book-division-conjunction p (list integral positive))))
    (h4-tactics-tactics-modus-ponens p discrete both)))

(defun h4-book-order-nonzero-ordinal-lower-bound-branch (shape p comparison ordinal nonzero term)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((reduction (h4-book-order-order-view p comparison (list shape) nil))
         (shape-literal (proof-step-first shape)))
      (if (proof-is-call shape-literal *proof-consp*)
          (h4-book-order-false-value p reduction)
        (proof-with-checked-results
            ((ordinal-literal (proof-step-first ordinal))
             (view (h4-book-order-order-view p ordinal-literal (list shape) nil))
             (natural (proof-proof-rewrite proof ordinal view '(1)))
             (integral (library-library-cite p "NATURAL-INTEGER" (list term) (list natural)))
             (nonnegative (library-library-cite p "NATURAL-NONNEGATIVE" (list term) (list natural)))
             (positive (library-lt *proof-zero* term))
             (assumption (proof-proof-assume proof positive nil))
             (same (h4-book-order-finite-equal p term *proof-zero* nonnegative assumption (list integral)))
             (conflict (proof-proof-cut proof same nonzero))
             (lower (proof-proof-front proof conflict positive))
             (bound (h4-book-order-positive-lower-bound p lower integral))
             (reversed (proof-proof-symmetric proof reduction)))
          (proof-proof-rewrite proof bound reversed '(1 1)))))))

(defun h4-book-order-nonzero-ordinal-lower-bound (p ordinal nonzero)
  (proof-with-checked-results ((literal (proof-step-first ordinal))
                               (term (proof-term-at literal 1)))
    (let ((comparison (list *proof-ordinal-less* term *proof-one*)))
      (h4-book-order-case p (proof-neg comparison) (list *proof-consp* term) shape
        (h4-book-order-nonzero-ordinal-lower-bound-branch shape p comparison ordinal nonzero term)
        (h4-book-order-nonzero-ordinal-lower-bound-branch shape p comparison ordinal nonzero term)))))

(defun h4-book-order-omega-comparison-proof-leaf (value p rewrites)
  (proof-with-checked-results
      ((step (h4-tactics-tactics-normalize p value nil nil rewrites nil))
       (literal (proof-step-first step))
       (right (proof-term-at literal 2)))
    (if (equal right *proof-false*)
        step
      '(:failure "failure" ""))))

(defun h4-book-order-omega-leaf-replies (requests p rewrites)
  (if (endp requests)
      nil
    (proof-with-checked-results
        ((step (h4-book-order-omega-comparison-proof-leaf (caar requests) p rewrites))
         (replies (h4-book-order-omega-leaf-replies (cdr requests) p rewrites)))
      (cons (cons (car requests) step) replies))))

(defun h4-book-order-omega-proof-cons (p formula subject ordinal shape selectors compared finite)
  (let ((proof (library-library-proof p))
        (ex (list *h4-book-order-exponent* subject))
        (coeff (list *h4-book-order-coefficient* subject))
        (rest (list *h4-book-order-rest* subject)))
    (proof-with-checked-results
        ((parts (h4-book-order-ordinal-components p ordinal shape))
         (nonzero (h4-book-order-selector-exponent-nonzero p ex parts))
         (ex-type (h4-book-order-required-fact (list *proof-ordinalp* ex) parts))
         (ex-bound (h4-book-order-nonzero-ordinal-lower-bound p ex-type nonzero))
         (types (h4-book-order-coefficient-proofs p coeff parts))
         (coeff-bound (h4-book-order-positive-lower-bound p (cadr types) (car types)))
         (rest-type (h4-book-order-required-fact (list *proof-ordinalp* rest) parts))
         (rest-bound (h4-book-order-from-ordinal-origin p rest-type))
         (ex-value (h4-tactics-tactics-nil-value p ex-bound))
         (coeff-value (h4-tactics-tactics-nil-value p coeff-bound))
         (rest-value (h4-tactics-tactics-nil-value p rest-bound))
         (literal (proof-step-first compared))
         (body (proof-term-at literal 2))
         (requests (proof-proof-by-value-leaves proof body nil))
         (replies (h4-book-order-omega-leaf-replies requests p
                                                   (append selectors (list ex-value coeff-value rest-value))))
         (just-false (proof-proof-by-value proof body (proof-eq *proof-result* *proof-false*) replies nil))
         (finite-reversed (proof-proof-symmetric proof finite))
         (result (proof-proof-chain proof compared (list just-false finite-reversed))))
      (h4-tactics-tactics-imply p formula result))))

(defun h4-book-order-omega-comparison-proof-branch (shape p formula subject ordinal goal selectors left)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((left-literal (proof-step-first left))
         (left-value (proof-term-at left-literal 2))
         (opened (h4-book-order-order-view p left-value (list shape) nil))
         (opened-literal (proof-step-first opened))
         (opened-value (proof-term-at opened-literal 2))
         (reduced (h4-tactics-tactics-normalize p opened-value nil nil selectors nil))
         (compared (proof-proof-chain proof left (list opened reduced)))
         (finite-term (proof-term-at goal 2))
         (finite (h4-book-order-order-view p finite-term (list shape) nil))
         (shape-literal (proof-step-first shape)))
      (if (proof-is-call shape-literal *proof-consp*)
          (h4-book-order-omega-proof-cons p formula subject ordinal shape selectors compared finite)
        (proof-with-checked-results
            ((finite-literal (proof-step-first finite))
             (finite-value (proof-term-at finite-literal 2))
             (shape-value (h4-tactics-tactics-nil-value p shape))
             (truth (h4-tactics-tactics-normalize p finite-value nil (list *proof-not*) (list shape-value) nil))
             (finite (proof-proof-chain proof finite (list truth)))
             (finite-reversed (proof-proof-symmetric proof finite))
             (result (proof-proof-chain proof compared (list finite-reversed))))
          (h4-tactics-tactics-imply p formula result))))))

(defun h4-book-order-omega-comparison-proof (p formula subject)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((guard (proof-term-at formula 1))
         (ordinal (proof-proof-assume proof guard t))
         (goal (proof-term-at formula 2))
         (omega (h4-tactics-tactics-normalize
                 p (list *h4-book-order-omega*) nil
                 (list *h4-book-order-omega* *h4-book-order-omega-term* *h4-book-order-make-ord*) nil nil))
         (literal (proof-step-first omega))
         (value (proof-term-at literal 2))
         (selectors (h4-book-order-selector-views *h4-book-order-selectors* p value nil))
         (comparison (proof-term-at goal 1))
         (reflexive (proof-proof-reflexive proof comparison))
         (left (proof-proof-rewrite proof reflexive omega '(1 2 2))))
      (h4-book-order-case p formula (list *proof-consp* subject) shape
        (h4-book-order-omega-comparison-proof-branch shape p formula subject ordinal goal selectors left)
        (h4-book-order-omega-comparison-proof-branch shape p formula subject ordinal goal selectors left)))))

(defun h4-book-order-first-proof (literal steps)
  (if (endp steps)
      nil
    (proof-with-checked-results ((first (proof-step-first (car steps))))
      (if (equal first literal)
          (car steps)
        (h4-book-order-first-proof literal (cdr steps))))))

(defun h4-book-order-selector-shape-rewrites (p subject shape shapes)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((views (h4-book-order-selector-views
                 (list *h4-book-order-exponent* *h4-book-order-coefficient*) p subject shapes))
         (cdr-axiom (library-library-axiom p "COMPLETION-OF-CDR" (list subject)))
         (literal (proof-step-first cdr-axiom))
         (body (proof-term-at literal 2))
         (atom-case (proof-proof-if-false proof body))
         (tail (proof-proof-chain proof cdr-axiom (list atom-case)))
         (opened (proof-proof-unfold proof (list *h4-book-order-rest* subject)))
         (selected (proof-proof-discharge proof tail shape))
         (tail-view (proof-proof-chain proof opened (list selected))))
      (append views (list tail-view)))))

(defun h4-book-order-selector-shape-evidence (p subject shape typed)
  (if (not typed)
      nil
    (proof-with-checked-results
        ((parts (h4-book-order-ordinal-components p typed shape))
         (exponent (h4-book-order-required-fact
                    (list *proof-ordinalp* (list *h4-book-order-exponent* subject)) parts))
         (origin (h4-book-order-from-ordinal-origin p exponent)))
      (append (table-values parts) (list origin)))))

(defun h4-book-order-selector-shape (p subject shape shapes assumptions evidence rewrites)
  (proof-with-checked-results
      ((typed (h4-book-order-first-proof (list *proof-ordinalp* subject) assumptions))
       (literal (proof-step-first shape)))
    (if (proof-is-call literal *proof-consp*)
        (proof-with-checked-results ((more (h4-book-order-selector-shape-evidence p subject shape typed)))
          (list (append evidence more) rewrites))
      (proof-with-checked-results ((more (h4-book-order-selector-shape-rewrites p subject shape shapes)))
        (list evidence (append rewrites more))))))

(defun h4-book-order-selector-shapes (p subjects shapes assumptions)
  (proof-with-checked-results
      ((context (h4-book-order-selector-shape p (car subjects) (car shapes) shapes assumptions
                                             (append shapes assumptions) nil)))
    (h4-book-order-selector-shape p (cadr subjects) (cadr shapes) shapes assumptions
                                 (car context) (cadr context))))

(defun h4-book-order-selector-order-differences (p assumptions main-order)
  (if (endp assumptions)
      nil
    (let ((given (car assumptions)))
      (proof-with-checked-results ((test (proof-step-first given)))
        (if (or (proof-is-call test *proof-less*)
                (and (proof-is-call test *proof-ordinal-less*) (not (equal test main-order))))
            (proof-with-checked-results
                ((unequal (h4-book-order-order-unequal p given
                                                      (if (proof-is-call test *proof-less*) :primitive :ordinal)))
                 (rest (h4-book-order-selector-order-differences p (cdr assumptions) main-order)))
              (cons unequal rest))
          (h4-book-order-selector-order-differences p (cdr assumptions) main-order))))))

(defun h4-book-order-selector-order-reflections (p evidence)
  (if (endp evidence)
      nil
    (let ((given (car evidence)))
      (proof-with-checked-results ((literal (proof-step-first given))
                                   (atom (h4-book-order-relation-atom literal)))
        (if (proof-is-call atom *proof-equal*)
            (proof-with-checked-results
                ((reflected (h4-book-order-reflected-test p given))
                 (rest (h4-book-order-selector-order-reflections p (cdr evidence))))
              (cons reflected rest))
          (h4-book-order-selector-order-reflections p (cdr evidence)))))))

(defun h4-book-order-selector-order-proof-reduce (step p shapes rewrites)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (atom (h4-book-order-relation-atom literal))
       (equality (h4-tactics-tactics-normalize p atom shapes
                                               (append *h4-book-order-obasics* (list (proof-cl "EQL")))
                                               rewrites nil))
       (equation (proof-step-first equality))
       (left (proof-term-at equation 1))
       (right (proof-term-at equation 2)))
    (if (equal left right)
        step
      (proof-proof-rewrite (library-library-proof p) step equality
                           (if (proof-is-call literal *proof-not*) '(1 1) '(1))))))

(defun h4-book-order-selector-order-reductions (p evidence shapes rewrites)
  (if (endp evidence)
      nil
    (proof-with-checked-results
        ((step (h4-book-order-selector-order-proof-reduce (car evidence) p shapes rewrites))
         (rest (h4-book-order-selector-order-reductions p (cdr evidence) shapes rewrites)))
      (cons step rest))))

(defun h4-book-order-selector-order-open (p given main-order evidence rewrites)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof main-order))
         (literal (proof-step-first opened))
         (right (proof-term-at literal 2))
         (body (h4-tactics-tactics-normalize p right evidence *h4-book-order-obasics* rewrites nil))
         (equation (proof-proof-chain proof opened (list body))))
      (proof-proof-rewrite proof given equation '(1)))))

(defun h4-book-order-selector-order-reflexive-absence (p term)
  (proof-with-checked-results ((head (proof-term-at term 0)))
    (and (or (equal head *proof-less*) (equal head *proof-ordinal-less*))
         (proof-with-checked-results ((left (proof-term-at term 1))
                                      (right (proof-term-at term 2)))
           (and (equal left right)
                (proof-with-checked-results
                    ((equality (h4-book-order-reflexive-reply p
                                                              (if (equal head *proof-less*) :primitive :ordinal)
                                                              left)))
                  (h4-book-order-false-value p equality)))))))

(defun h4-book-order-selector-order-expand (p remaining main-order evidence rewrites)
  (declare (xargs :measure (acl2-count remaining)))
  (if (endp remaining)
      evidence
    (let ((given (car remaining)))
      (proof-with-checked-results
          ((literal (proof-step-first given))
           (opened (and (equal literal main-order)
                        (h4-book-order-selector-order-open p given main-order evidence rewrites)))
           (false (h4-book-order-selector-order-reflexive-absence p literal)))
        (h4-book-order-selector-order-expand
         p (cdr remaining) main-order (append evidence (if opened (list opened) nil) (if false (list false) nil))
         rewrites)))))

(defun h4-book-order-selector-order-conflict (p remaining known goal)
  (if (endp remaining)
      nil
    (let* ((literal (caar remaining))
           (step (cdar remaining))
           (opposite (assoc-equal (proof-neg literal) known))
           (proof (library-library-proof p)))
      (cond ((equal literal *proof-false*)
             (proof-proof-subsume proof step (cons goal (cdr (proof-step-clause step)))))
            (opposite
             (proof-with-checked-results ((conflict (proof-proof-cut proof step (cdr opposite))))
               (proof-proof-subsume proof conflict (cons goal (proof-step-clause conflict)))))
            (t (h4-book-order-selector-order-conflict p (cdr remaining) known goal))))))

(defun h4-book-order-selector-order-establish (p goal main-order evidence rewrites)
  (let ((proof (library-library-proof p)))
    (let ((result
           (if (equal goal main-order)
               (proof-with-checked-results
                   ((opened (proof-proof-unfold proof goal))
                    (literal (proof-step-first opened))
                    (body (proof-term-at literal 2))
                    (reduced (h4-tactics-tactics-establish p body evidence *h4-book-order-obasics* rewrites nil)))
                 (proof-proof-transport proof reduced opened))
             (h4-tactics-tactics-establish p goal evidence *h4-book-order-obasics* rewrites nil))))
      (if (and (failure-p result)
               (member-equal (cadr result) '("inapplicable-term" "value")))
          '(:failure "unproved" "")
        result))))

(defun h4-book-order-selector-order-proof-with-shapes (shapes p subjects assumptions main-order goal)
  (proof-with-checked-results
      ((context (h4-book-order-selector-shapes p subjects shapes assumptions))
       (differences (h4-book-order-selector-order-differences p assumptions main-order)))
    (let ((evidence (append (car context) differences))
          (rewrites (cadr context)))
      (proof-with-checked-results ((reflections (h4-book-order-selector-order-reflections p evidence)))
        (let ((evidence (append evidence reflections)))
          (proof-with-checked-results ((reductions (h4-book-order-selector-order-reductions p evidence shapes rewrites)))
            (let ((evidence (append evidence reductions)))
              (proof-with-checked-results
                  ((evidence (h4-book-order-selector-order-expand p evidence main-order evidence rewrites))
                   (known (h4-book-order-index-steps evidence nil))
                   (conflict (h4-book-order-selector-order-conflict p known known goal)))
                (if conflict
                    conflict
                  (h4-book-order-selector-order-establish p goal main-order evidence rewrites))))))))))

(defun h4-book-order-selector-order-proof-right (other p shape formula subjects assumptions main-order goal)
  (proof-with-checked-results
      ((step (h4-book-order-selector-order-proof-with-shapes
              (list shape other) p subjects assumptions main-order goal)))
    (h4-tactics-tactics-imply p formula step)))

(defun h4-book-order-selector-order-proof-left (shape p formula subjects assumptions main-order goal)
  (proof-with-checked-results ((subject (proof-term-at subjects 1)))
    (h4-book-order-case p formula (list *proof-consp* subject) other
      (h4-book-order-selector-order-proof-right other p shape formula subjects assumptions main-order goal)
      (h4-book-order-selector-order-proof-right other p shape formula subjects assumptions main-order goal))))

(defun h4-book-order-selector-order-proof (p formula subjects)
  (proof-with-checked-results
      ((parts (proof-list-of-length (cdr formula) 2))
       (given (proof-proof-assume (library-library-proof p) (car parts) t))
       (assumptions (h4-book-list-types-conjunct-proofs p given))
       (subject (proof-term-at subjects 0)))
    (let* ((main-order (cons *proof-ordinal-less* subjects))
           (goal (cadr parts))
           (result (h4-book-order-case p formula (list *proof-consp* subject) shape
                     (h4-book-order-selector-order-proof-left shape p formula subjects assumptions main-order goal)
                     (h4-book-order-selector-order-proof-left shape p formula subjects assumptions main-order goal))))
      (if (and (failure-p result) (equal (cadr result) "unproved"))
          nil
        result))))

(defun h4-book-order-ocmp-proof-choose-backward (second p first formula a forward backward)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((first-literal (proof-step-first first))
                                 (second-literal (proof-step-first second)))
      (if (and (equal first-literal forward) (equal second-literal backward))
          (proof-with-checked-results
              ((loop (h4-book-order-strict-chain p first second))
               (self-order (proof-proof-fact proof *h4-book-order-order-self* (list (list *library-x* a))))
               (false (h4-book-order-false-value p self-order))
               (conflict (proof-proof-cut proof loop false)))
            (proof-proof-subsume proof conflict (cons formula (proof-step-clause conflict))))
        (proof-with-checked-results
            ((atom (h4-book-order-relation-atom first-literal))
             (right (proof-term-at formula 2))
             (test (if (equal atom right) first second))
             (literal (proof-step-first test))
             (value (if (proof-is-call literal *proof-not*)
                        (h4-tactics-tactics-nil-value p test)
                      (h4-book-order-true-order-value p test))))
          (h4-tactics-tactics-establish p formula (list first second) (list *h4-book-order-ocmp*) (list value) nil))))))

(defun h4-book-order-ocmp-proof-choose-forward (first p formula a forward backward)
  (h4-book-order-case p formula backward second
    (h4-book-order-ocmp-proof-choose-backward second p first formula a forward backward)
    (h4-book-order-ocmp-proof-choose-backward second p first formula a forward backward)))

(defun h4-book-order-ocmp-proof (p formula subjects)
  (proof-with-checked-results ((parts (proof-list-of-length subjects 2)))
    (let* ((a (car parts))
           (b (cadr parts))
           (forward (list *proof-ordinal-less* a b))
           (backward (list *proof-ordinal-less* b a)))
      (h4-book-order-case p formula forward first
        (h4-book-order-ocmp-proof-choose-forward first p formula a forward backward)
        (h4-book-order-ocmp-proof-choose-forward first p formula a forward backward)))))

(defun h4-book-order-ordinal-consequences-make (p goal literals terms conflict)
  (list :h4-book-order-ordinal-consequences p goal literals terms conflict))

(defun h4-book-order-ordinal-consequences-p (object)
  (cadr object))

(defun h4-book-order-ordinal-consequences-goal (object)
  (caddr object))

(defun h4-book-order-ordinal-consequences-literals (object)
  (cadddr object))

(defun h4-book-order-ordinal-consequences-terms (object)
  (nth 4 object))

(defun h4-book-order-ordinal-consequences-conflict (object)
  (nth 5 object))

(defun h4-book-order-ordinal-consequences-add (object step)
  (let ((literals (h4-book-order-ordinal-consequences-literals object)))
    (proof-with-checked-results ((atom (proof-step-first step)))
      (if (assoc-equal atom literals)
          object
        (let* ((p (h4-book-order-ordinal-consequences-p object))
               (conflict (h4-book-order-ordinal-consequences-conflict object))
               (negative (proof-is-call atom *proof-not*))
               (literals (table-put literals atom step)))
          (proof-with-checked-results
              ((opposite (if negative (proof-term-at atom 1) (proof-neg atom)))
               (other (table-get literals opposite nil))
               (conflict (if (and other (not conflict))
                             (proof-proof-cut (library-library-proof p)
                                              (if negative other step) (if negative step other))
                           conflict)))
            (h4-book-order-ordinal-consequences-make
             p (h4-book-order-ordinal-consequences-goal object) literals
             (h4-book-order-ordinal-consequences-terms object) conflict)))))))

(defun h4-book-order-consequence-self-order (object terms)
  (declare (xargs :measure (acl2-count terms)))
  (if (or (endp terms) (failure-p object))
      object
    (let ((p (h4-book-order-ordinal-consequences-p object)))
      (h4-book-order-consequence-self-order
       (proof-with-checked-results
           ((equality (h4-book-order-reflexive-reply p :ordinal (car terms)))
            (false (h4-book-order-false-value p equality)))
         (h4-book-order-ordinal-consequences-add object false))
       (cdr terms)))))

(defun h4-book-order-consequence-zero-type (object p)
  (proof-with-checked-results
      ((natural (library-library-natural p *proof-zero*))
       (ordinal (library-library-cite p "NATURAL-ORDINAL" (list *proof-zero*) (list natural))))
    (h4-book-order-ordinal-consequences-add object ordinal)))

(defun h4-book-order-ordinal-consequences-init (p goal evidence)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literals (h4-book-order-index-steps evidence nil))
         (atoms (h4-book-order-relation-atoms (cons goal (table-keys literals)))))
      (let ((terms (proof-unique (h4-book-order-atom-arguments atoms))))
        (proof-with-checked-results
            ((negated-goal (if (proof-is-call goal *proof-not*)
                               (proof-with-checked-results ((atom (proof-term-at goal 1)))
                                 (proof-proof-assume proof atom t))
                             (proof-proof-assume proof goal nil)))
             (object (h4-book-order-ordinal-consequences-add
                      (h4-book-order-ordinal-consequences-make p goal literals terms nil) negated-goal))
             (object (if (member-equal *proof-zero* terms)
                         (h4-book-order-consequence-zero-type object p)
                       object)))
          (h4-book-order-consequence-self-order object terms))))))

(defun h4-book-order-consequence-no-jump (object first second i j no-jump)
  (let* ((p (h4-book-order-ordinal-consequences-p object))
         (proof (library-library-proof p))
         (no-i (proof-neg i))
         (no-j (proof-neg j)))
    (proof-with-checked-results
        ((object
          (if (and first (not (assoc-equal no-j (h4-book-order-ordinal-consequences-literals object))))
              (proof-with-checked-results
                  ((assumption (proof-proof-assume proof j t))
                   (chain (h4-book-order-strict-chain p first assumption))
                   (conflict (proof-proof-cut proof chain no-jump))
                   (result (proof-proof-front proof conflict no-j)))
                (h4-book-order-ordinal-consequences-add object result))
            object)))
      (if (and second (not (assoc-equal no-i (h4-book-order-ordinal-consequences-literals object))))
          (proof-with-checked-results
              ((assumption (proof-proof-assume proof i t))
               (chain (h4-book-order-strict-chain p assumption second))
               (conflict (proof-proof-cut proof chain no-jump))
               (result (proof-proof-front proof conflict no-i)))
            (h4-book-order-ordinal-consequences-add object result))
        object))))

(defun h4-book-order-ordinal-consequences-between (object a b c)
  (let* ((p (h4-book-order-ordinal-consequences-p object))
         (literals (h4-book-order-ordinal-consequences-literals object))
         (i (list *proof-ordinal-less* a b))
         (j (list *proof-ordinal-less* b c))
         (k (list *proof-ordinal-less* a c))
         (first (table-get literals i nil))
         (second (table-get literals j nil)))
    (proof-with-checked-results
        ((object
          (if (and first second (not (assoc-equal k literals)))
              (proof-with-checked-results ((chain (h4-book-order-strict-chain p first second)))
                (h4-book-order-ordinal-consequences-add object chain))
            object)))
      (let ((no-jump (table-get (h4-book-order-ordinal-consequences-literals object)
                                  (proof-neg k) nil)))
        (if no-jump
            (h4-book-order-consequence-no-jump object first second i j no-jump)
          object)))))

(defun h4-book-order-changed-arguments (arguments from to)
  (if (endp arguments)
      nil
    (cons (if (equal (car arguments) from) to (car arguments))
          (h4-book-order-changed-arguments (cdr arguments) from to))))

(defun h4-book-order-consequence-transfer-known (remaining object a b equality)
  (declare (xargs :measure (acl2-count remaining)))
  (if (or (endp remaining) (failure-p object))
      object
    (let* ((term (caar remaining))
           (known (cdar remaining))
           (p (h4-book-order-ordinal-consequences-p object)))
      (h4-book-order-consequence-transfer-known
       (cdr remaining)
       (proof-with-checked-results ((atom (h4-book-order-relation-atom term)))
         (if (member-equal a (cdr atom))
             (let* ((changed (cons (car atom) (h4-book-order-changed-arguments (cdr atom) a b)))
                    (literal (if (proof-is-call term *proof-not*) (proof-neg changed) changed)))
               (if (assoc-equal literal (h4-book-order-ordinal-consequences-literals object))
                   object
                 (proof-with-checked-results
                     ((result (proof-proof-rewrite-first (library-library-proof p) known equality)))
                   (h4-book-order-ordinal-consequences-add object result))))
           object))
       a b equality))))

(defun h4-book-order-consequence-transfer-equal (object p same a b)
  (let* ((literals (h4-book-order-ordinal-consequences-literals object))
         (equality (table-get literals same nil)))
    (if (not equality)
        object
      (proof-with-checked-results
          ((object
            (if (assoc-equal (proof-eq b a) literals)
                object
              (proof-with-checked-results ((symmetric (proof-proof-symmetric (library-library-proof p) equality)))
                (h4-book-order-ordinal-consequences-add object symmetric)))))
        (h4-book-order-consequence-transfer-known
         (h4-book-order-ordinal-consequences-literals object) object a b equality)))))

(defun h4-book-order-consequence-tie (object p same a b)
  (let* ((literals (h4-book-order-ordinal-consequences-literals object))
         (left (table-get literals (list *proof-ordinalp* a) nil))
         (right (table-get literals (list *proof-ordinalp* b) nil))
         (below (table-get literals (proof-neg (list *proof-ordinal-less* a b)) nil))
         (above (table-get literals (proof-neg (list *proof-ordinal-less* b a)) nil)))
    (if (and (not (assoc-equal same literals)) left right below above)
        (proof-with-checked-results
            ((rule (proof-proof-fact (library-library-proof p) *h4-book-order-order-ties*
                                      (list (list *library-x* a) (list *library-y* b))))
             (all (h4-book-division-conjunction p (list left right below above)))
             (equal (h4-tactics-tactics-modus-ponens p rule all)))
          (h4-book-order-ordinal-consequences-add object equal))
      object)))

(defun h4-book-order-ordinal-consequences-transfer (object a b)
  (let* ((p (h4-book-order-ordinal-consequences-p object))
         (same (proof-eq a b))
         (different (proof-neg same))
         (direct-order (list *proof-ordinal-less* a b)))
    (proof-with-checked-results
        ((object (h4-book-order-consequence-transfer-equal object p same a b))
         (literals (h4-book-order-ordinal-consequences-literals object))
         (direct (table-get literals direct-order nil))
         (object
          (if (and direct (not (assoc-equal different literals)))
              (proof-with-checked-results ((unequal (h4-book-order-order-unequal p direct :ordinal)))
                (h4-book-order-ordinal-consequences-add object unequal))
            object))
         (object (h4-book-order-consequence-tie object p same a b))
         (literals (h4-book-order-ordinal-consequences-literals object))
         (absent (table-get literals different nil)))
      (if (and absent (not (assoc-equal (proof-neg (proof-eq b a)) literals)))
          (proof-with-checked-results ((reflected (h4-book-order-reflected-test p absent)))
            (h4-book-order-ordinal-consequences-add object reflected))
        object))))

(defun h4-book-order-consequence-origins (object terms)
  (declare (xargs :measure (acl2-count terms)))
  (if (or (endp terms) (failure-p object))
      object
    (let* ((p (h4-book-order-ordinal-consequences-p object))
           (ordinal (table-get (h4-book-order-ordinal-consequences-literals object)
                                 (list *proof-ordinalp* (car terms)) nil)))
      (h4-book-order-consequence-origins
       (if ordinal
           (proof-with-checked-results ((origin (h4-book-order-from-ordinal-origin p ordinal)))
             (h4-book-order-ordinal-consequences-add object origin))
         object)
       (cdr terms)))))

(defun h4-book-order-consequence-between-all (object a b terms)
  (declare (xargs :measure (acl2-count terms)))
  (if (or (endp terms) (failure-p object))
      object
    (h4-book-order-consequence-between-all
     (h4-book-order-ordinal-consequences-between object a b (car terms)) a b (cdr terms))))

(defun h4-book-order-consequence-claim (object conflict)
  (let ((proof (library-library-proof (h4-book-order-ordinal-consequences-p object)))
        (goal (h4-book-order-ordinal-consequences-goal object))
        (clause (proof-step-clause conflict)))
    (if (member-equal goal clause)
        (proof-proof-front proof conflict goal)
      (proof-proof-subsume proof conflict (cons goal clause)))))

(defun h4-book-order-consequence-pair (object a b terms)
  (proof-with-checked-results
      ((object (if (equal a b) object (h4-book-order-ordinal-consequences-transfer object a b)))
       (object (h4-book-order-consequence-between-all object a b terms)))
    (let ((conflict (h4-book-order-ordinal-consequences-conflict object)))
      (proof-with-checked-results ((step (and conflict (h4-book-order-consequence-claim object conflict))))
        (cons step object)))))

(defun h4-book-order-consequence-pairs (result a remaining terms)
  (declare (xargs :measure (acl2-count remaining)))
  (if (or (endp remaining) (failure-p result) (car result))
      result
    (h4-book-order-consequence-pairs
     (h4-book-order-consequence-pair (cdr result) a (car remaining) terms)
     a (cdr remaining) terms)))

(defun h4-book-order-consequence-pass (result remaining terms)
  (declare (xargs :measure (acl2-count remaining)))
  (if (or (endp remaining) (failure-p result) (car result))
      result
    (h4-book-order-consequence-pass
     (h4-book-order-consequence-pairs result (car remaining) terms terms)
     (cdr remaining) terms)))

(defun h4-book-order-consequence-rounds (n result previous terms)
  (declare (xargs :measure (nfix n)))
  (let ((size (len (h4-book-order-ordinal-consequences-literals (cdr result)))))
    (cond ((or (failure-p result) (car result) (equal size previous)) result)
          ((zp n) '(:failure "fuel" "h4-book-order-consequence-rounds"))
          (t (h4-book-order-consequence-rounds
              (1- n) (h4-book-order-consequence-pass result terms terms) size terms)))))

(defun h4-book-order-ordinal-consequences-solve (n object)
  (if (zp n)
      '(:failure "fuel" "h4-book-order-ordinal-consequences-solve")
    (let ((terms (h4-book-order-ordinal-consequences-terms object)))
      (proof-with-checked-results
          ((object (if (member-equal *proof-zero* terms) (h4-book-order-consequence-origins object terms) object)))
        (h4-book-order-consequence-rounds n (cons nil object) nil terms)))))

(defun h4-book-order-solve-formula (p formula evidence)
  (proof-with-checked-results
      ((object (h4-book-order-ordinal-consequences-init p formula evidence))
       (solution (h4-book-order-ordinal-consequences-solve 1000000 object)))
    (car solution)))

(defun h4-book-order-order-formula (p formula evidence)
  (declare (xargs :measure (acl2-count formula)))
  (cond ((and (proof-is-call formula *proof-if*) (endp (cdddr formula)))
         '(:failure "failure" ""))
        ((and (proof-is-call formula *proof-if*) (equal (cadddr formula) *proof-false*))
         (proof-with-checked-results
             ((first (h4-book-order-order-formula p (cadr formula) evidence))
              (second (h4-book-order-order-formula p (caddr formula) evidence)))
           (and first second (h4-tactics-tactics-conjunction p formula first second))))
        (t (h4-book-order-solve-formula p formula evidence))))

(defun h4-book-order-order-value-opposite (p right assumption equal)
  (if equal
      (h4-tactics-tactics-normalize p right (list assumption) (list *proof-not*) nil nil)
    (proof-with-checked-results ((false (h4-tactics-tactics-nil-value p assumption)))
      (h4-tactics-tactics-normalize p right nil (list *proof-not*) (list false) nil))))

(defun h4-book-order-order-value-equality-branch (assumption p left right equality evidence)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((literal (proof-step-first assumption)))
      (let* ((equal (equal literal equality))
             (desired (if equal (proof-neg left) left)))
        (proof-with-checked-results
            ((direction (h4-book-order-order-formula p desired (append evidence (list assumption)))))
          (and direction
               (proof-with-checked-results
                   ((value (if equal
                               (h4-tactics-tactics-nil-value p direction)
                             (h4-book-order-true-order-value p direction)))
                    (opposite (h4-book-order-order-value-opposite p right assumption equal))
                    (reversed (proof-proof-symmetric proof opposite)))
                 (proof-proof-chain proof value (list reversed)))))))))

(defun h4-book-order-order-value-equality (p formula evidence)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2)))
      (let ((left (car parts))
            (right (cadr parts)))
        (proof-with-checked-results
            ((equality (proof-term-at right 1))
             (positive (proof-proof-assume proof equality t))
             (proved (h4-book-order-order-value-equality-branch positive p left right equality evidence))
             (negative (proof-proof-assume proof equality nil))
             (disproved (h4-book-order-order-value-equality-branch negative p left right equality evidence)))
          (and proved disproved (proof-proof-cases proof equality proved disproved)))))))

(defun h4-book-order-prove-relations (p formula goal evidence)
  (proof-with-checked-results
      ((boolean (h4-book-order-boolean-order-equality goal))
       (proof (if boolean
                  (h4-book-order-order-value-equality p goal evidence)
                (h4-book-order-order-formula p goal evidence))))
    (if (and proof (proof-is-call formula *library-implies*))
        (h4-tactics-tactics-imply p formula proof)
      proof)))

(defun h4-book-order-prove-elementary (p formula)
  (if (proof-is-call formula *library-implies*)
      (proof-with-checked-results
          ((guard (proof-term-at formula 1))
           (given (proof-proof-assume (library-library-proof p) guard t))
           (evidence (h4-book-list-types-conjunct-proofs p given))
           (goal (proof-term-at formula 2)))
        (h4-book-order-prove-relations p formula goal evidence))
    (h4-book-order-prove-relations p formula formula nil)))

(defun h4-book-order-prove-matched (p formula)
  (proof-with-checked-results ((subjects (h4-book-order-comparison-equality formula)))
    (if subjects
        (h4-book-order-ocmp-proof p formula subjects)
      (proof-with-checked-results ((subjects (h4-book-order-selector-comparison formula)))
        (if subjects
            (h4-book-order-selector-order-proof p formula subjects)
          (proof-with-checked-results ((subject (h4-book-order-omega-comparison formula)))
            (if (h4-book-order-match-p subject)
                (h4-book-order-omega-comparison-proof p formula subject)
              (proof-with-checked-results ((subject (h4-book-order-selector-type formula)))
                (if (h4-book-order-match-p subject)
                    (h4-book-order-selector-types-proof p formula subject)
                  (proof-with-checked-results ((match (h4-book-order-selector-count formula)))
                    (if match
                        (h4-book-order-selector-count-proof p formula match)
                      (h4-book-order-prove-elementary p formula))))))))))))

(defun h4-book-order-ordinal-proof (p formula support)
  (and support
       (proof-with-checked-results ((candidate (h4-book-order-ordinal-candidate formula)))
         (and candidate
              (let* ((proof (library-library-proof p))
                     (facts (table-update (proof-proof-facts proof) support))
                     (p (library-library-with-proof p (proof-proof-with-facts proof facts))))
                (h4-book-order-prove-matched p formula))))))
