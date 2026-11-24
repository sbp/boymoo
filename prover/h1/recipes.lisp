(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-recipes-true-listp* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *h1-recipes-character-listp* (proof-sym "CHARACTER-LISTP" "ACL2"))
(defconst *h1-recipes-rationalp* (proof-cl "RATIONALP"))
(defconst *h1-recipes-revappend* (proof-cl "REVAPPEND"))
(defconst *h1-recipes-expt* (proof-cl "EXPT"))
(defconst *h1-recipes-symbolp* (proof-cl "SYMBOLP"))
(defconst *h1-recipes-characterp* (proof-cl "CHARACTERP"))
(defconst *h1-recipes-i* (proof-sym "I" "ACL2"))
(defconst *h1-recipes-acc* (proof-sym "ACC" "ACL2"))
(defconst *h1-recipes-u* (proof-sym "U" "ACL2"))
(defconst *h1-recipes-v* (proof-sym "V" "ACL2"))

(defun h1-recipes-function (name p)
  (let ((acl2-name (proof-sym name "ACL2"))
        (proof (h1-tactics-prover-proof p)))
    (if (assoc-equal acl2-name (proof-proof-definitions proof))
        acl2-name
      (proof-cl name))))

(defun h1-recipes-openings-names (p names)
  (if (endp names)
      nil
    (cons (h1-recipes-function (car names) p)
          (h1-recipes-openings-names p (cdr names)))))

(defun h1-recipes-openings (p names)
  (h1-recipes-openings-names p (text-split names :none)))

(defun h1-recipes-conclusion (formula)
  (declare (xargs :measure (acl2-count formula)))
  (cond ((not (proof-is-call formula *library-implies*)) formula)
        ((and (consp formula) (consp (cdr formula)) (consp (cddr formula)))
         (h1-recipes-conclusion (caddr formula)))
        (t '(:failure "failure" ""))))

(defun h1-recipes-step-term-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h1-recipes-add-swap (p)
  (let ((lib (h1-tactics-prover-library p))
        (proof (h1-tactics-prover-proof p))
        (x *library-x*) (y *library-y*) (z *library-z*))
    (proof-with-checked-results
        ((assoc-step (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list x y z)))
         (result (h1-propositions-proof-symmetric proof assoc-step))
         (swap (library-library-axiom lib "COMMUTATIVITY-OF-+" (list x y)))
         (result (proof-proof-rewrite proof result swap '(1 2 1)))
         (assoc-step (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list y x z))))
      (proof-proof-chain proof result (list assoc-step)))))

(defun h1-recipes-distribute-minus-assoc (x y z p)
  (library-library-axiom (h1-tactics-prover-library p) "ASSOCIATIVITY-OF-+"
                         (list x y z)))

(defun h1-recipes-distribute-minus-commute (x y p)
  (library-library-axiom (h1-tactics-prover-library p) "COMMUTATIVITY-OF-+"
                         (list x y)))

(defun h1-recipes-distribute-minus-zero-plus (term numeric p)
  (let ((lib (h1-tactics-prover-library p))
        (proof (h1-tactics-prover-proof p)))
    (proof-with-checked-results
        ((identity (library-library-axiom lib "UNICITY-OF-0" (list term)))
         (right (h1-recipes-step-term-at identity 2))
         (simplified (h1-recursion-simplify
                      p right (list numeric) (list (proof-sym "FIX" "ACL2")))))
      (proof-proof-chain proof identity (list simplified)))))

(defun h1-recipes-distribute-minus (p)
  (let* ((lib (h1-tactics-prover-library p))
         (proof (h1-tactics-prover-proof p))
         (x *library-x*) (y *library-y*)
         (minus-x (library-minus x)) (minus-y (library-minus y))
         (a (library-plus x y)) (b (library-plus minus-x minus-y))
         (minus-a (library-minus a))
         (zero *proof-zero*))
    (proof-with-checked-results
        ((distribute (h1-recipes-distribute-minus-assoc x y b p))
         (swap (library-library-axiom lib "COMMUTATIVITY-2-OF-+"
                                      (list y minus-x minus-y)))
         (distribute (proof-proof-rewrite proof distribute swap '(1 2 2)))
         (associated (h1-recipes-distribute-minus-assoc
                      x minus-x (library-plus y minus-y) p))
         (reversed (h1-propositions-proof-symmetric proof associated))
         (distribute (proof-proof-chain proof distribute (list reversed)))
         (inverse-x (library-library-axiom lib "INVERSE-OF-+" (list x)))
         (distribute (proof-proof-rewrite proof distribute inverse-x '(1 2 1)))
         (inverse-y (library-library-axiom lib "INVERSE-OF-+" (list y)))
         (distribute (proof-proof-rewrite proof distribute inverse-y '(1 2 2)))
         (computed (proof-proof-compute proof (library-plus zero zero) 0))
         (zero-sum (proof-proof-chain proof distribute (list computed)))
         (closure (library-library-axiom lib "CLOSURE" (list x y)))
         (parts (h1-propositions-propositional-proof-conjunct lib closure))
         (tail (h1-propositions-propositional-proof-conjunct lib (cadr parts)))
         (unary (h1-propositions-propositional-proof-conjunct lib (cadr tail)))
         (b-numeric (proof-proof-instantiate
                     proof (car parts) (list (list x minus-x) (list y minus-y))))
         (a-negative-numeric (proof-proof-instantiate
                              proof (car unary) (list (list x a))))
         (commuted (h1-recipes-distribute-minus-commute minus-a a p))
         (inverse-a (library-library-axiom lib "INVERSE-OF-+" (list a)))
         (inverse (proof-proof-chain proof commuted (list inverse-a)))
         (identity (h1-recipes-distribute-minus-zero-plus b b-numeric p))
         (reversed (h1-propositions-proof-symmetric proof inverse))
         (rearranged (proof-proof-rewrite proof identity reversed '(1 1 1)))
         (reversed (h1-propositions-proof-symmetric proof rearranged))
         (associated (h1-recipes-distribute-minus-assoc minus-a a b p))
         (rearranged (proof-proof-chain proof reversed (list associated)))
         (rearranged (proof-proof-rewrite proof rearranged zero-sum '(1 2 2)))
         (commuted (h1-recipes-distribute-minus-commute minus-a zero p))
         (identity (h1-recipes-distribute-minus-zero-plus minus-a a-negative-numeric p))
         (result (proof-proof-chain proof rearranged (list commuted identity))))
      (h1-propositions-proof-symmetric proof result))))

(defun h1-recipes-changed-calls-children (left right place index pending)
  (if (endp left)
      pending
    (cons (list (append place (list index)) (car left) (car right))
          (h1-recipes-changed-calls-children
           (cdr left) (cdr right) place (1+ index) pending))))

;; Visit the pending calls in order, with each call's arguments before its siblings.
(defun h1-recipes-changed-calls-next (n pending)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "Fuel" "h1-recipes-changed-calls-next"))
   ((endp pending) (cons nil nil))
   (t
    (let* ((current (car pending))
           (place (car current))
           (original (cadr current))
           (target (caddr current))
           (rest (cdr pending)))
      (if (equal original target)
          (h1-recipes-changed-calls-next (1- n) rest)
        (let ((old (h1-tactics-call-head original))
              (new (h1-tactics-call-head target))
              (different '(:failure "Unproved" "")))
          (cond
           ((or (member-equal old (list :none *proof-quote*))
                (member-equal new (list :none *proof-quote*))
                (not (equal (len original) (len target))))
            different)
           ((not (equal old new))
            (if (equal (cdr original) (cdr target))
                (cons current rest)
              different))
           (t (h1-recipes-changed-calls-next
               (1- n)
               (h1-recipes-changed-calls-children
                (cdr original) (cdr target) place 1 rest))))))))))

(defun h1-recipes-changed-calls-collect (n pending reversed)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h1-recipes-changed-calls-collect")
    (proof-with-checked-results
        ((next (h1-recipes-changed-calls-next 1000000 pending)))
      (if (not (car next))
          (reverse reversed)
        (h1-recipes-changed-calls-collect
         (1- n) (cdr next) (cons (car next) reversed))))))

(defun h1-recipes-changed-calls (original target place)
  (h1-recipes-changed-calls-collect 1000000 (list (list place original target)) nil))

(defun h1-recipes-definition-equation (p formula functions)
  (let ((proof (h1-tactics-prover-proof p)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (opened (proof-proof-unfold proof (cadr parts)))
         (open-right (h1-recipes-step-term-at opened 2)))
      (let ((right (caddr parts)))
        (if (equal open-right right)
            opened
          (proof-with-checked-results
              ((solved (h1-tactics-prover-solve
                        p (proof-eq open-right right) functions 160)))
            (proof-proof-chain proof opened (list solved))))))))

(defun h1-recipes-both (terms)
  (cond ((endp terms) '(:failure "failure" ""))
        ((endp (cdr terms)) (car terms))
        (t (proof-ite (car terms) (h1-recipes-both (cdr terms)) *proof-false*))))

(defun h1-recipes-position-call (formula)
  (and
   (proof-is-call formula *library-implies*)
   (proof-with-checked-results ((premise (proof-term-at formula 1)))
     (and
      (proof-is-call premise *library-natp*)
      (proof-with-checked-results ((goal (proof-term-at formula 2)))
        (and
         (proof-is-call goal *proof-if*)
         (proof-with-checked-results
             ((test (proof-term-at goal 1))
              (yes (proof-term-at goal 2)))
           (and
            (equal test yes)
            (proof-is-call test *library-natp*)
            (proof-with-checked-results ((term (proof-term-at test 1)))
              (and
               (not (eq (h1-tactics-call-head term) :none))
               (proof-with-checked-results ((acc (proof-term-at premise 1)))
                 (and (equal (car (last term)) acc)
                      (proof-with-checked-results ((no (proof-term-at goal 3)))
                        (and (equal no (proof-eq term *proof-false*))
                             term))))))))))))))

(mutual-recursion
 (defun h1-recipes-calls-operator (term operator)
   (declare (xargs :measure (acl2-count term)))
   (let ((head (h1-tactics-call-head term)))
     (cond
      ((member-equal head (list :none *proof-quote*)) nil)
      ((equal head operator) t)
      ((and (consp term) (consp (car term)) (proof-is-call head (proof-cl "LAMBDA")))
       (if (not (and (consp (cdr (car term))) (consp (cddr (car term)))))
           '(:failure "failure" "")
         (proof-with-checked-results
             ((in-body (h1-recipes-calls-operator (caddr (car term)) operator)))
           (or in-body (h1-recipes-calls-operator-arguments (cdr term) operator)))))
      ((consp term) (h1-recipes-calls-operator-arguments (cdr term) operator)))))
 (defun h1-recipes-calls-operator-arguments (args operator)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((in-arg (h1-recipes-calls-operator (car args) operator)))
       (or in-arg (h1-recipes-calls-operator-arguments (cdr args) operator))))))

(defun h1-recipes-arguments-of-size (term stop size)
  (if (integerp term)
      '(:failure "failure" "")
    (proof-list-of-length (seq-slice term 1 stop) size)))

(defun h1-recipes-complex-equality-rewrite-component
    (p name agreement index first second)
  (let ((lib (h1-tactics-prover-library p))
        (proof (h1-tactics-prover-proof p)))
    (proof-with-checked-results
        ((first-arg (h1-recipes-step-term-at first 1))
         (second-arg (h1-recipes-step-term-at second 1))
         (axiom (library-library-axiom lib name (list first-arg second-arg)))
         (premise (h1-recipes-step-term-at axiom 1))
         (known (h1-propositions-propositional-proof-conjoin lib premise first second))
         (equality (h1-propositions-propositional-proof-modus-ponens lib axiom known)))
      (proof-proof-rewrite proof agreement equality (list 1 index)))))

(defun h1-recipes-complex-equality-component (part p c1 whole r1 i1 r2 i2)
  (let ((name (concatenate 'string part "-COMPLEX"))
        (head (proof-cl part))
        (lib (h1-tactics-prover-library p))
        (proof (h1-tactics-prover-proof p)))
    (proof-with-checked-results
        ((reflexive (h1-propositions-propositional-proof-reflexive lib (list head c1)))
         (agreement (proof-proof-rewrite proof reflexive whole '(1 2 1)))
         (agreement (h1-recipes-complex-equality-rewrite-component
                     p name agreement 1 r1 i1))
         (agreement (h1-recipes-complex-equality-rewrite-component
                     p name agreement 2 r2 i2)))
      (proof-proof-tidy proof agreement))))

(defun h1-recipes-complex-equality (p formula)
  (let ((lib (h1-tactics-prover-library p))
        (proof (h1-tactics-prover-proof p)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (goal-parts (h1-recipes-arguments-of-size (caddr parts) :none 2))
         (complexes (h1-recipes-arguments-of-size (car goal-parts) :none 2))
         (components (h1-recipes-arguments-of-size (cadr goal-parts) 3 2))
         (assumed (h1-arithmetic-proof-assume proof (cadr parts) t))
         (conjuncts (h1-propositions-propositional-proof-conjunct lib assumed))
         (rest (h1-propositions-propositional-proof-conjunct lib (cadr conjuncts)))
         (last (h1-propositions-propositional-proof-conjunct lib (cadr rest)))
         (whole (h1-arithmetic-proof-assume proof (car goal-parts) t)))
      (let ((goal (caddr parts))
            (equal-complex (car goal-parts))
            (equal-parts (cadr goal-parts))
            (c1 (car complexes))
            (real (car components))
            (imaginary (cadr components))
            (r1 (car conjuncts)) (i1 (car rest))
            (r2 (car last)) (i2 (cadr last)))
        (proof-with-checked-results
            ((real-equality (h1-recipes-complex-equality-component
                             "REALPART" p c1 whole r1 i1 r2 i2))
             (selected (h1-propositions-propositional-proof-select
                        lib equal-parts real-equality))
             (imag-equality (h1-recipes-complex-equality-component
                             "IMAGPART" p c1 whole r1 i1 r2 i2))
             (imag-true (h1-tactics-prover-equality-is-true p imag-equality))
             (rhs (proof-proof-chain proof selected (list imag-true)))
             (whole-true (h1-tactics-prover-equality-is-true p whole))
             (reversed (h1-propositions-proof-symmetric proof rhs))
             (yes (proof-proof-chain proof whole-true (list reversed)))
             (not-whole (h1-arithmetic-proof-assume proof equal-complex nil))
             (lhs (h1-tactics-prover-false-equation p not-whole))
             (false-branch (h1-arithmetic-proof-if-false proof equal-parts))
             (reversed (h1-propositions-proof-symmetric proof false-branch))
             (no-real (proof-proof-chain proof lhs (list reversed)))
             (true-branch (h1-arithmetic-proof-if-true proof equal-parts))
             (not-imaginary (h1-arithmetic-proof-assume proof imaginary nil))
             (false-equation (h1-tactics-prover-false-equation p not-imaginary))
             (branch (proof-proof-chain proof true-branch (list false-equation)))
             (reversed (h1-propositions-proof-symmetric proof branch))
             (no-imaginary (proof-proof-chain proof lhs (list reversed)))
             (both (h1-propositions-propositional-proof-reflexive lib c1))
             (assumed-real (h1-arithmetic-proof-assume proof real t))
             (both (proof-proof-rewrite proof both assumed-real '(1 2 1)))
             (assumed-imaginary (h1-arithmetic-proof-assume proof imaginary t))
             (both (proof-proof-rewrite proof both assumed-imaginary '(1 2 2)))
             (impossible (proof-proof-cut proof both not-whole))
             (impossible (proof-proof-subsume
                          proof impossible (cons goal (proof-step-clause impossible))))
             (imaginary-cases (proof-proof-cases proof imaginary impossible no-imaginary))
             (no (proof-proof-cases proof real imaginary-cases no-real))
             (cases (proof-proof-cases proof equal-complex yes no)))
          (h1-propositions-propositional-proof-implies-from lib formula cases))))))

(defun h1-recipes-nonempty-package (p formula)
  (let ((lib (h1-tactics-prover-library p))
        (proof (h1-tactics-prover-proof p))
        (x *library-x*)
        (zero *proof-zero*))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (goal (proof-list-of-length (caddr parts) 2))
         (empty-parts (h1-recipes-arguments-of-size (cadr goal) :none 2))
         (package (proof-term-at (car empty-parts) 0))
         (equal-blank (h1-arithmetic-proof-assume proof (cadr goal) t))
         (blank (proof-term-at (cadr empty-parts) 1))
         (zero-package (proof-proof-compute proof (list package zero) blank))
         (reversed (h1-propositions-proof-symmetric proof zero-package))
         (same-package (proof-proof-chain proof equal-blank (list reversed)))
         (axiom (library-library-axiom lib "INTERN-IN-PACKAGE-OF-SYMBOL-SYMBOL-NAME"
                                      (list x zero)))
         (premise (h1-recipes-step-term-at axiom 1))
         (symbol-step (h1-arithmetic-proof-assume proof (cadr parts) t))
         (known (h1-propositions-propositional-proof-conjoin
                 lib premise symbol-step same-package))
         (identity (h1-propositions-propositional-proof-modus-ponens lib axiom known))
         (call (h1-recipes-step-term-at identity 1))
         (completion (if (integerp call)
                         '(:failure "failure" "")
                       (library-library-axiom lib "COMPLETION-OF-INTERN-IN-PACKAGE-OF-SYMBOL"
                                              (cdr call))))
         (right (h1-recipes-step-term-at completion 2))
         (nil-value (h1-tactics-prover-solve p (proof-eq right *proof-false*) nil 160))
         (reversed (h1-propositions-proof-symmetric proof identity))
         (x-nil (proof-proof-chain proof reversed (list completion nil-value)))
         (reflexive (h1-propositions-propositional-proof-reflexive lib (car empty-parts)))
         (x-package (proof-proof-rewrite proof reflexive x-nil '(1 2 1)))
         (computed (proof-proof-compute proof (list package *proof-false*)
                                        '("str" "COMMON-LISP")))
         (x-package (proof-proof-chain proof x-package (list computed)))
         (distinct (proof-proof-rewrite proof equal-blank x-package '(1 1)))
         (literal (proof-step-first distinct))
         (constant (h1-tactics-prover-constant p literal))
         (rewritten (proof-proof-rewrite proof distinct constant '(1)))
         (contradiction (proof-proof-tidy proof rewritten))
         (front (proof-proof-front proof contradiction (caddr parts))))
      (h1-propositions-propositional-proof-implies-from lib formula front))))

(defun h1-recipes-add-rule (p step rewrite)
  (proof-with-checked-results
      ((rules (h1-tactics-rules-add (h1-tactics-prover-rules p) step t rewrite)))
    (h1-tactics-prover-with-rules p rules)))

(defun h1-recipes-package-imports (p formula)
  (let ((lib (h1-tactics-prover-library p))
        (proof (h1-tactics-prover-proof p))
        (x *library-x*))
    (proof-with-checked-results
        ((step (library-library-axiom lib "COMPLETION-OF-PKG-IMPORTS" (list x)))
         (condition (h1-arithmetic-proof-assume proof (list *h1-tactics-stringp* x) nil))
         (right (h1-recipes-step-term-at step 2))
         (selected (h1-propositions-propositional-proof-select lib right condition))
         (rule (proof-proof-chain proof step (list selected)))
         (p (h1-recipes-add-rule p rule t))
         (step (h1-tactics-prover-solve p formula nil 160)))
      (cons step p))))

(defun h1-recipes-checked-pair (result)
  (cond ((failure-p result) result)
        ((failure-p (car result)) (car result))
        (t result)))

(defun h1-recipes-reverse-property (p formula character-lists)
  (let* ((opened (if character-lists
                     "REVAPPEND TRUE-LISTP CHARACTER-LISTP"
                   "REVAPPEND TRUE-LISTP"))
         (openings (h1-recipes-openings p opened)))
    (h1-recipes-checked-pair
     (h1-recursion-prove-from-calls
      p formula openings nil (not character-lists)
      (and character-lists (list (list *h1-recipes-character-listp* *library-y*)))))))

(defun h1-recipes-true-list-helper (p)
  (if (assoc-equal (proof-sym "H1-TRUE-LIST-NIL" "ACL2")
                   (proof-proof-facts (h1-tactics-prover-proof p)))
      p
    (let* ((true-listp *h1-recipes-true-listp*)
           (x *library-x*)
           (formula (list *library-implies*
                          (list true-listp x)
                          (list true-listp (list *library-cdr* x)))))
      (proof-with-checked-results
          ((step (h1-tactics-prover-solve p (list true-listp *proof-false*)
                                         (list true-listp) 160))
           (helper (h1-tactics-prover-helper p "TRUE-LIST-NIL" step nil t))
           (p (cdr helper))
           (step (h1-tactics-prover-solve p formula (list (cons true-listp 2)) 160))
           (helper (h1-tactics-prover-helper p "TRUE-LIST-CDR" step nil t)))
        (cdr helper)))))

(defun h1-recipes-last-cdr (p formula)
  (let* ((true-listp *h1-recipes-true-listp*)
         (last (proof-cl "LAST"))
         (x *library-x*)
         (hypothesis (proof-ite (list true-listp x)
                                (proof-neg (list *proof-consp* x))
                                *proof-false*)))
    (proof-with-checked-results
        ((p (h1-recipes-true-list-helper p))
         (step (h1-tactics-prover-solve
                p (list *library-implies* hypothesis (proof-eq x *proof-false*))
                (list true-listp) 160))
         (helper (h1-tactics-prover-helper p "TRUE-LIST-ATOM" step nil t))
         (p (cdr helper))
         (premise (proof-term-at formula 1))
         (claim (list *library-implies* premise
                      (proof-eq (list *library-cdr* (list last x)) *proof-false*)))
         (proved (h1-recipes-checked-pair
                  (h1-recursion-prove-from-calls p claim (list last true-listp) nil :none nil)))
         (helper (h1-tactics-prover-helper (cdr proved) "LAST-TAIL-NIL" (car proved) nil t))
         (p (cdr helper))
         (step (h1-tactics-prover-solve p formula
                                       (list (proof-sym "LAST-CDR" "ACL2") true-listp)
                                       160)))
      (cons step p))))

(defun h1-recipes-pairlis-tail (p formula)
  (let* ((true-listp *h1-recipes-true-listp*)
         (revappend *h1-recipes-revappend*)
         (x *library-x*) (y *library-y*) (z *library-z*)
         (cons-xy (list *proof-cons* x y)))
    (proof-with-checked-results
        ((step (h1-tactics-prover-solve
                p (list *library-implies* (list true-listp x)
                        (proof-neg (list *h1-tactics-stringp* x)))
                (list true-listp) 160))
         (helper (h1-tactics-prover-helper p "TRUE-LIST-NOT-STRING" step nil t))
         (p (cdr helper))
         (step (h1-tactics-prover-solve
                p (list *library-implies* (list true-listp y) (list true-listp cons-xy))
                (list true-listp) 160))
         (helper (h1-tactics-prover-helper p "TRUE-LIST-CONS" step nil t))
         (p (cdr helper))
         (rev-cons (proof-eq (list revappend cons-xy z)
                             (list revappend y (list *proof-cons* x z))))
         (step (h1-recipes-definition-equation p rev-cons nil))
         (helper (h1-tactics-prover-helper p "REVAPPEND-CONS" step nil t)))
      (h1-recipes-checked-pair
       (h1-recursion-prove-from-calls
        (cdr helper) formula
        (list (proof-sym "PAIRLIS$-TAILREC" "ACL2") (proof-sym "PAIRLIS$" "ACL2")
              (proof-cl "REVERSE") revappend)
        nil t nil)))))

(defun h1-recipes-ordinals (p formula)
  (h1-recipes-checked-pair
   (h1-recursion-prove-from-calls
    p formula (h1-recipes-openings p "O-P O<G O-FINP NATP POSP")
    (h1-recipes-openings p "O-FIRST-EXPT O-RST O-FINP ATOM NOT")
    :none nil)))

(defun h1-recipes-substitute-type (p formula)
  (let* ((function (proof-sym "SUBSTITUTE-AC" "ACL2"))
         (helper-formula (list *h1-recipes-true-listp*
                               (list function
                                     (proof-sym "NEW" "ACL2")
                                     (proof-sym "OLD" "ACL2")
                                     (proof-sym "SEQ" "ACL2")
                                     *h1-recipes-acc*))))
    (proof-with-checked-results
        ((p (h1-recipes-true-list-helper p))
         (proved (h1-recipes-checked-pair
                  (h1-recursion-prove-from-calls p helper-formula (list function)
                                                 nil :none nil)))
         (helper (h1-tactics-prover-helper (cdr proved) "TRUE-LIST-SUBSTITUTE-AC"
                                          (car proved) nil t))
         (p (cdr helper))
         (step (h1-tactics-prover-solve p formula (list (proof-cl "SUBSTITUTE")) 160)))
      (cons step p))))

(defun h1-recipes-remove-duplicates-type (p formula)
  (let* ((function (proof-sym "REMOVE-DUPLICATES-EQUAL" "ACL2"))
         (pred *h1-recipes-character-listp*)
         (x *library-x*)
         (helper-formula (list *library-implies* (list pred x)
                               (list pred (list function x)))))
    (proof-with-checked-results
        ((proved (h1-recipes-checked-pair
                  (h1-recursion-prove-from-calls p helper-formula (list function pred)
                                                 nil :none nil)))
         (helper (h1-tactics-prover-helper
                  (cdr proved) "CHARACTER-LIST-REMOVE-DUPLICATES-EQUAL"
                  (car proved) nil t))
         (p (cdr helper))
         (step (h1-tactics-prover-solve p formula (list pred) 160)))
      (cons step p))))

(defun h1-recipes-recognizer-spine (p formula)
  (if (not (proof-is-call formula *library-implies*))
      nil
    (proof-with-checked-results ((premise (proof-term-at formula 1)))
      (if (not (proof-is-call premise *proof-if*))
          nil
        (proof-with-checked-results ((no (proof-term-at premise 3)))
          (if (not (equal no *proof-false*))
              nil
            (proof-with-checked-results ((args (h1-recipes-arguments-of-size formula :none 2)))
              (let* ((proof (h1-tactics-prover-proof p))
                     (definitions (proof-proof-definitions proof))
                     (goal (cadr args))
                     (goal-head (h1-tactics-call-head goal)))
                (if (not (and (assoc-equal goal-head definitions) (equal (len goal) 2)))
                    nil
                  (let* ((cons-test (list *proof-consp* (cadr goal)))
                         (left (cadr premise))
                         (right (caddr premise))
                         (test (if (equal left cons-test) right left))
                         (test-head (h1-tactics-call-head test)))
                    (and (or (equal left cons-test) (equal right cons-test))
                         (assoc-equal test-head definitions)
                         (equal (cdr test) (cdr goal))
                         (not (equal test-head goal-head))
                         (h1-tactics-prover-solve
                          p formula (list (cons test-head 1) (cons goal-head 2)
                                          (cons (proof-cl "ATOM") 2))
                          160))))))))))))

(defund h1-recipes-transfer-step-advance (p step pending equations)
  (let ((next (h1-recipes-changed-calls-next 1000000 pending)))
    (cond
     ((failure-p next) (list :done (cons next p)))
     ((not (car next))
      (list :done (cons (proof-proof-tidy (h1-tactics-prover-proof p) step) p)))
     (t
      (let* ((change (car next))
             (old (cadr change))
             (new (caddr change))
             (key (proof-eq old new))
             (found (assoc-equal key equations))
             (proved (if found
                         (cons (cdr found) p)
                       (h1-recursion-prove-from-calls
                        p key (list (car old) (car new)) nil :none nil))))
        (cond
         ((failure-p proved) (list :done (cons proved p)))
         ((failure-p (car proved)) (list :done proved))
         (t
          (let* ((equation (car proved))
                 (p (cdr proved))
                 (rewritten (proof-proof-rewrite
                             (h1-tactics-prover-proof p) step equation (car change))))
            (if (failure-p rewritten)
                (list :done (cons rewritten p))
              (list :continue p rewritten (cdr next)
                    (if found equations (table-put equations key equation))))))))))))

(defun h1-recipes-transfer-step-next (n p step pending equations)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons '(:failure "Fuel" "h1-recipes-transfer-step-next") p)
    (let ((advance (h1-recipes-transfer-step-advance p step pending equations)))
      (if (eq (car advance) :continue)
          (h1-recipes-transfer-step-next
           (1- n) (cadr advance) (caddr advance) (cadddr advance) (nth 4 advance))
        (cadr advance)))))

;; A retry of transfer keeps any facts added by its induction attempts.
(defun h1-recipes-transfer-step-result (p formula step)
  (let ((original (proof-step-first step)))
    (if (failure-p original)
        (cons original p)
      (h1-recipes-transfer-step-next
       1000000 p step (list (list (list 1) original formula)) nil))))

(defun h1-recipes-transfer-step (p formula step)
  (h1-recipes-checked-pair (h1-recipes-transfer-step-result p formula step)))

(defun h1-recipes-transfer-property (p formula earlier)
  (proof-with-checked-results
      ((step (proof-proof-fact (h1-tactics-prover-proof p) earlier nil)))
    (h1-recipes-transfer-step p formula step)))

(defun h1-recipes-arithmetic-answer (p request)
  (let* ((lib (h1-arithmetic-request-library request))
         (p (h1-tactics-prover-with-library p lib))
         (method (h1-arithmetic-request-method request))
         (args (h1-arithmetic-request-args request)))
    (case method
      (:solve
       (cons (h1-tactics-prover-solve p (car args) (cadr args) (caddr args)) p))
      (:helper
       (let ((result (h1-tactics-prover-helper
                      p (car args) (cadr args) (caddr args) (cadddr args))))
         (if (failure-p result)
             (cons result p)
           (let ((p (cdr result)))
             (cons (cons (car result) (h1-tactics-prover-library p)) p)))))
      (:rules-add
       (let ((rules (h1-tactics-rules-add
                     (h1-tactics-prover-rules p) (car args) (cadr args) (caddr args))))
         (if (failure-p rules)
             (cons rules p)
           (cons nil (h1-tactics-prover-with-rules p rules)))))
      (:rules-add-formula
       (let ((rules (h1-tactics-rules-add-formula
                     (h1-tactics-prover-rules p) (car args) (cadr args) (caddr args))))
         (if (failure-p rules)
             (cons rules p)
           (cons nil (h1-tactics-prover-with-rules p rules)))))
      (:by-induction
       ;; The exponentiation call omits the optional induction limit.
       (cons (h1-tactics-prover-by-induction
              p (car args) (cadr args) (caddr args) (cadddr args)
              (nth 4 args) :none (nth 6 args) (nth 7 args)
              (or (nth 8 args) :none))
             p))
      (otherwise (cons '(:failure "failure" "") p)))))

(defund h1-recipes-arithmetic-advance (recipe p lib args replies)
  (let ((result (h1-arithmetic-query recipe lib args replies)))
    (cond ((failure-p result) (list :done result))
          ((h1-arithmetic-request-p result)
           (let ((answer (h1-recipes-arithmetic-answer p result)))
             (list :continue (cdr answer)
                   (table-put replies (h1-arithmetic-request-key result) (car answer)))))
          (t (list :done (cons result p))))))

(defun h1-recipes-arithmetic-run (n recipe p lib args replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h1-recipes-arithmetic-run")
    (let ((advance (h1-recipes-arithmetic-advance recipe p lib args replies)))
      (if (eq (car advance) :continue)
          (h1-recipes-arithmetic-run (1- n) recipe (cadr advance) lib args (caddr advance))
        (cadr advance)))))

(defun h1-recipes-position-type (p formula)
  (proof-with-checked-results
      ((result (h1-recipes-arithmetic-run
                1000000 :natural-successor p (h1-tactics-prover-library p) nil nil))
       (p (h1-tactics-prover-with-library (cdr result) (car result)))
       (consequent (proof-term-at formula 2))
       (natural (proof-term-at consequent 1))
       (call (proof-term-at natural 1))
       (head (proof-term-at call 0)))
    (h1-recipes-checked-pair
     (h1-recursion-prove-from-calls
      p formula (list head (proof-sym "FIX" "ACL2") *library-natp*) nil t nil))))

(defun h1-recipes-character-at-index (p formula)
  (h1-recipes-arithmetic-run
   1000000 :character-at-index p (h1-tactics-prover-library p) (list formula) nil))

(defun h1-recipes-exponentiation (p formula nonzero)
  (proof-with-checked-results
      ((result (h1-recipes-arithmetic-run
                1000000 :exponentiation p (h1-tactics-prover-library p)
                (list formula nonzero) nil)))
    (cons (caar result)
          (h1-tactics-prover-with-library (cdr result) (cdar result)))))

(defun h1-recipes-basic-types-numeric-rule (p name)
  (let ((lib (h1-tactics-prover-library p))
        (proof (h1-tactics-prover-proof p)))
    (proof-with-checked-results
        ((source (proof-proof-fact proof name nil))
         (antecedent (h1-recipes-step-term-at source 1))
         (assumed (h1-arithmetic-proof-assume proof antecedent t))
         (tail (h1-propositions-propositional-proof-modus-ponens lib source assumed))
         (front (proof-proof-front proof tail (proof-neg antecedent))))
      (h1-recipes-add-rule p front t))))

(defun h1-recipes-basic-types-boolean-branch (p step)
  (let ((booleanp *h1-tactics-booleanp*))
    (proof-with-checked-results
        ((value (h1-recipes-step-term-at step 2))
         (boolean (h1-tactics-prover-solve p (list booleanp value) (list booleanp) 160)))
      (h1-propositions-library-transport-argument
       (h1-tactics-prover-library p) boolean step 1))))

(defun h1-recipes-basic-types (p formula)
  (let* ((label (proof-sym "SELF-POSITIVE-NONNEGATIVE" "ACL2"))
         (x *library-x*)
         (same (proof-eq x *library-y*))
         (numeric (list *library-numberp* x)))
    (proof-with-checked-results
        ((p (if (assoc-equal label (proof-proof-facts (h1-tactics-prover-proof p)))
                p
              (h1-recursion-build p)))
         (proof (h1-tactics-prover-proof p))
         (lib (h1-tactics-prover-library p))
         (step (proof-proof-fact proof label nil))
         (p (h1-recipes-add-rule p step t))
         (p (h1-recipes-basic-types-numeric-rule p "rationalp-acl2-numberp"))
         (p (h1-recipes-basic-types-numeric-rule p "complex-rationalp-acl2-numberp"))
         (opened (library-library-axiom lib "COMPLETION-OF-<" (list x *proof-zero*)))
         (search (h1-tactics-search-init p nil nil nil nil 160 nil))
         (right (h1-recipes-step-term-at opened 2))
         (solved (h1-tactics-search-prove
                  search (proof-eq right *proof-false*) (list (list numeric nil)) t))
         (step (proof-proof-chain proof opened (list (car solved))))
         (helper (h1-tactics-prover-helper p "NONNUMBER-LESS-THAN-ZERO"
                                          step (list numeric) t))
         (p (cdr helper))
         (proof (h1-tactics-prover-proof p))
         (assumed (h1-arithmetic-proof-assume proof same t))
         (yes (h1-tactics-prover-equality-is-true p assumed))
         (assumed (h1-arithmetic-proof-assume proof same nil))
         (no (h1-tactics-prover-false-equation p assumed))
         (yes (h1-recipes-basic-types-boolean-branch p yes))
         (no (h1-recipes-basic-types-boolean-branch p no))
         (step (proof-proof-cases proof same yes no))
         (helper (h1-tactics-prover-helper p "BOOLEANP-EQUAL" step nil t))
         (p (cdr helper))
         (step (h1-tactics-prover-solve p formula
                                       (h1-tactics-prover-functions-in p formula) 160)))
      (cons step p))))

(defund h1-recipes-natural-result-transfer (p formula name bindings)
  (let* ((proof (h1-tactics-prover-proof p))
         (fact (proof-proof-fact proof name nil))
         (step (if (failure-p fact)
                   fact
                 (proof-proof-instantiate proof fact (table-items bindings)))))
    (if (failure-p step)
        (cons step p)
      (h1-recipes-transfer-step-result p formula step))))

(defund h1-recipes-natural-result-match (clause application)
  (if (not (equal (len clause) 1))
      nil
    (proof-with-checked-results ((earlier (h1-recipes-position-call (car clause))))
      (and earlier
           (proof-with-checked-results ((head (proof-term-at application 0)))
             (and (not (equal (car earlier) head))
                  (equal (len earlier) (len application))
                  (let ((match (h1-tactics-match
                                earlier (cons (car earlier) (cdr application))
                                (h1-tactics-variables earlier) nil)))
                    (and (car match) match))))))))

(defun h1-recipes-natural-result-facts (p formula application facts size)
  (declare (xargs :measure (acl2-count facts)))
  (if (endp facts)
      (h1-recipes-position-type p formula)
    (proof-with-checked-results
        ((match (h1-recipes-natural-result-match (cdar facts) application)))
      (if (not match)
          (h1-recipes-natural-result-facts p formula application (cdr facts) size)
        (let* ((result (h1-recipes-natural-result-transfer p formula (caar facts) (cdr match)))
               (step (car result))
               (p (cdr result)))
          (if (and (failure-p step) (equal (cadr step) "Unproved"))
              (if (equal (len (proof-proof-facts (h1-tactics-prover-proof p))) size)
                  (h1-recipes-natural-result-facts p formula application (cdr facts) size)
                '(:failure "failure" ""))
            (h1-recipes-checked-pair result)))))))

(defun h1-recipes-natural-result (p formula application)
  (let ((facts (proof-proof-facts (h1-tactics-prover-proof p))))
    (h1-recipes-natural-result-facts p formula application facts (len facts))))

(defconst *h1-recipes-templates*
  (let* ((x *library-x*) (y *library-y*) (z *library-z*)
         (u *h1-recipes-u*) (v *h1-recipes-v*)
         (i *h1-recipes-i*) (acc *h1-recipes-acc*)
         (implies *library-implies*)
         (true-listp *h1-recipes-true-listp*)
         (character-listp *h1-recipes-character-listp*)
         (rationalp *h1-recipes-rationalp*)
         (revappend *h1-recipes-revappend*)
         (expt *h1-recipes-expt*)
         (complex (proof-cl "COMPLEX"))
         (rev (list revappend x y)))
    (list
     (list (proof-eq (library-plus x (library-plus y z))
                     (library-plus y (library-plus x z)))
           :add-swap)
     (list (proof-eq (library-minus (library-plus x y))
                     (library-plus (library-minus x) (library-minus y)))
           :distribute-minus)
     (list (list implies
                 (h1-recipes-both
                  (list (list rationalp x) (list rationalp y)
                        (list rationalp u) (list rationalp v)))
                 (proof-eq (proof-eq (list complex x y) (list complex u v))
                           (h1-recipes-both (list (proof-eq x u) (proof-eq y v)))))
           :complex-equality)
     (list (list implies (list *h1-recipes-symbolp* x)
                 (proof-neg
                  (proof-eq (list (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2") x)
                            (proof-quote '("str" "")))))
           :nonempty-package)
     (list (list implies (proof-neg (list *h1-tactics-stringp* x))
                 (proof-eq (list (proof-sym "PKG-IMPORTS" "ACL2") x) *proof-false*))
           :package-imports)
     (list (list implies (list *proof-ordinalp* x)
                 (list (proof-sym "O<G" "ACL2") x))
           :ordinals)
     (list (list implies
                 (h1-recipes-both
                  (list (list character-listp x)
                        (proof-neg (list *proof-less* i *proof-zero*))
                        (list *proof-less* i (list (proof-sym "LEN" "ACL2") x))))
                 (list *h1-recipes-characterp* (list (proof-cl "NTH") i x)))
           :character-at-index)
     (list (list implies (list true-listp y) (list true-listp rev))
           :reverse-true-list)
     (list (list implies (list true-listp x)
                 (proof-eq (list character-listp rev)
                           (h1-recipes-both
                            (list (list character-listp x) (list character-listp y)))))
           :reverse-character-list)
     (list (list implies (list true-listp acc)
                 (proof-eq (list (proof-sym "PAIRLIS$-TAILREC" "ACL2") x y acc)
                           (list revappend acc (list (proof-sym "PAIRLIS$" "ACL2") x y))))
           :pairlis-tail)
     (list (list implies (list true-listp x)
                 (proof-eq (list (proof-sym "LAST-CDR" "ACL2") x) *proof-false*))
           :last-cdr)
     (list (list implies (list rationalp x) (list rationalp (list expt x i)))
           :expt-rational)
     (list (list implies
                 (h1-recipes-both
                  (list (list *library-numberp* x) (proof-neg (proof-eq x *proof-zero*))))
                 (proof-neg (proof-eq (list expt x i) *proof-zero*)))
           :expt-nonzero)
     (list (list implies (proof-neg (list *h1-tactics-stringp* z))
                 (list true-listp (list (proof-cl "SUBSTITUTE") x y z)))
           :substitute-type))))

(defun h1-recipes-step-result (p step)
  (if (failure-p step) step (cons step p)))

(defun h1-recipes-template-step (plan p formula)
  (case plan
    (:add-swap (h1-recipes-step-result p (h1-recipes-add-swap p)))
    (:distribute-minus (h1-recipes-step-result p (h1-recipes-distribute-minus p)))
    (:complex-equality (h1-recipes-step-result p (h1-recipes-complex-equality p formula)))
    (:nonempty-package (h1-recipes-step-result p (h1-recipes-nonempty-package p formula)))
    (:package-imports (h1-recipes-package-imports p formula))
    (:ordinals (h1-recipes-ordinals p formula))
    (:character-at-index (h1-recipes-character-at-index p formula))
    (:reverse-true-list (h1-recipes-reverse-property p formula nil))
    (:reverse-character-list (h1-recipes-reverse-property p formula t))
    (:pairlis-tail (h1-recipes-pairlis-tail p formula))
    (:last-cdr (h1-recipes-last-cdr p formula))
    (:expt-rational (h1-recipes-exponentiation p formula nil))
    (:expt-nonzero (h1-recipes-exponentiation p formula t))
    (:substitute-type (h1-recipes-substitute-type p formula))
    (otherwise '(:failure "failure" ""))))

(defund h1-recipes-template-match (pattern formula)
  (h1-tactics-match pattern formula (h1-tactics-variables pattern) nil))

(defun h1-recipes-solve-templates-loop (p formula templates)
  (declare (xargs :measure (acl2-count templates)))
  (if (endp templates)
      (cons nil p)
    (let* ((pattern (caar templates))
           (match (h1-recipes-template-match pattern formula)))
      (if (not (car match))
          (h1-recipes-solve-templates-loop p formula (cdr templates))
        (proof-with-checked-results
            ((solved (h1-recipes-template-step (cadar templates) p pattern))
             (p (cdr solved))
             (step (proof-proof-instantiate (h1-tactics-prover-proof p)
                                            (car solved) (table-items (cdr match)))))
          (cons step p))))))

(defun h1-recipes-solve-templates (p formula)
  (h1-recipes-solve-templates-loop p formula *h1-recipes-templates*))

(defun h1-recipes-prove-true-list-call (p formula)
  (proof-with-checked-results
      ((p (h1-recipes-true-list-helper p))
       (goal (h1-recipes-conclusion formula))
       (arg (proof-term-at goal 1))
       (head (proof-term-at arg 0)))
    (h1-recipes-checked-pair
     (h1-recursion-prove-from-calls p formula (list head) nil :none nil))))

(defun h1-recipes-prove-keyword-value-list (p formula)
  (h1-recipes-checked-pair
   (h1-recursion-prove-from-calls
    p formula (list (cons (proof-sym "KEYWORD-VALUE-LISTP" "ACL2") 1)
                    (cons *h1-recipes-true-listp* 2))
    nil :none nil)))

(defun h1-recipes-shape-definition-equation (p formula goal)
  (proof-with-checked-results ((left (proof-term-at goal 1)))
    (let ((definitions (proof-proof-definitions (h1-tactics-prover-proof p))))
      (and (assoc-equal (h1-tactics-call-head left) definitions)
           (equal (len left) 2)
           (proof-is-call (cadr left) *proof-cons*)
           (proof-with-checked-results ((right (proof-term-at goal 2)))
             (h1-recipes-definition-equation
              p formula (h1-tactics-prover-functions-in p right)))))))

(defun h1-recipes-shape-list-proof (p formula goal)
  (cond
   ((proof-is-call goal *h1-recipes-true-listp*)
    (proof-with-checked-results ((arg (proof-term-at goal 1)))
      (cond ((member-equal (h1-tactics-call-head arg)
                           (list (proof-sym "FIRST-N-AC" "ACL2") (proof-cl "NTHCDR")))
             (h1-recipes-prove-true-list-call p formula))
            ((and (proof-is-call formula *library-implies*)
                  (proof-is-call (cadr formula) (proof-sym "KEYWORD-VALUE-LISTP" "ACL2")))
             (h1-recipes-prove-keyword-value-list p formula))
            (t nil))))
   ((and (proof-is-call goal *h1-recipes-character-listp*)
         (proof-is-call formula *library-implies*)
         (proof-is-call (cadr formula) *h1-recipes-character-listp*))
    (proof-with-checked-results
        ((arg (proof-term-at goal 1))
         (calls (h1-recipes-calls-operator arg (proof-sym "REMOVE-DUPLICATES-EQUAL" "ACL2"))))
      (and calls (h1-recipes-remove-duplicates-type p formula))))
   (t nil)))

(defun h1-recipes-shape-basic-types-p (formula)
  (and
   (proof-is-call formula *proof-if*)
   (proof-with-checked-results ((implication (proof-term-at formula 1)))
     (and
      (proof-is-call implication *library-implies*)
      (proof-with-checked-results ((premise (proof-term-at implication 1)))
        (and
         (proof-is-call premise *library-natp*)
         (proof-with-checked-results ((goal (proof-term-at implication 2)))
           (and
            (proof-is-call goal *proof-not*)
            (proof-with-checked-results ((test (proof-term-at goal 1)))
              (proof-is-call test (proof-cl "MINUSP")))))))))))

(defun h1-recipes-prove-other-shapes (p formula goal)
  (proof-with-checked-results
      ((equation (and (proof-is-call formula *proof-equal*)
                      (h1-recipes-shape-definition-equation p formula goal)))
       (list-proof (and (not equation)
                        (h1-recipes-shape-list-proof p formula goal)))
       (basic-types (and (not (or equation list-proof))
                         (h1-recipes-shape-basic-types-p formula))))
    (cond
     (equation (cons equation p))
     (list-proof list-proof)
     (basic-types (h1-recipes-basic-types p formula))
     (t
      (proof-with-checked-results ((application (h1-recipes-position-call formula)))
        (if (and application
                 (assoc-equal (h1-tactics-call-head application)
                              (proof-proof-definitions (h1-tactics-prover-proof p))))
            (h1-recipes-natural-result p formula application)
          (proof-with-checked-results ((step (h1-recipes-recognizer-spine p formula)))
            (if step
                (cons step p)
              '(:failure "Unproved" "")))))))))

(defun h1-recipes-prove-by-shape (p formula)
  (proof-with-checked-results ((solved (h1-recipes-solve-templates p formula)))
    (if (car solved)
        solved
      (proof-with-checked-results ((goal (h1-recipes-conclusion formula)))
        (h1-recipes-prove-other-shapes (cdr solved) formula goal)))))

(defun h1-recipes-prove (p name formula)
  (cond
   ((equal name "COMMUTATIVITY-2-OF-+")
    (h1-recipes-step-result p (h1-recipes-add-swap p)))
   ((equal name "FOLD-CONSTS-IN-+")
    (proof-with-checked-results
        ((assoc-step (library-library-axiom (h1-tactics-prover-library p)
                                            "ASSOCIATIVITY-OF-+"
                                            (list *library-x* *library-y* *library-z*)))
         (fact (h1-propositions-proof-symmetric (h1-tactics-prover-proof p) assoc-step))
         (p (h1-recipes-add-rule p fact nil)))
      (h1-recipes-checked-pair (h1-recursion-prove-automatically p formula))))
   ((equal name "DISTRIBUTIVITY-OF-MINUS-OVER-+")
    (h1-recipes-step-result p (h1-recipes-distribute-minus p)))
   ((equal name "BOOLEAN-LISTP-CONS")
    (h1-recipes-step-result
     p (h1-recipes-definition-equation p formula (list *h1-tactics-booleanp*))))
   ((equal name "BASIC-TAU-RULES") (h1-recipes-basic-types p formula))
   ((equal name "COMPLEX-EQUAL")
    (h1-recipes-step-result p (h1-recipes-complex-equality p formula)))
   ((equal name "DEFAULT-PKG-IMPORTS") (h1-recipes-package-imports p formula))
   ((equal name "SYMBOL-PACKAGE-NAME-OF-SYMBOL-IS-NOT-EMPTY-STRING")
    (h1-recipes-step-result p (h1-recipes-nonempty-package p formula)))
   ((equal name "O-P-IMPLIES-O<G") (h1-recipes-ordinals p formula))
   ((equal name "CHARACTERP-NTH") (h1-recipes-character-at-index p formula))
   ((member-equal name '("TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION"
                         "CHARACTER-LISTP-REVAPPEND"))
    (h1-recipes-reverse-property p formula (equal name "CHARACTER-LISTP-REVAPPEND")))
   ((member-equal name '("TRUE-LISTP-FIRST-N-AC-TYPE-PRESCRIPTION"
                         "TRUE-LISTP-NTHCDR-TYPE-PRESCRIPTION"))
    (h1-recipes-prove-true-list-call p formula))
   ((equal name "PAIRLIS$-TAILREC-IS-PAIRLIS$") (h1-recipes-pairlis-tail p formula))
   ((equal name "LAST-CDR-IS-NIL") (h1-recipes-last-cdr p formula))
   ((equal name "KEYWORD-VALUE-LISTP-FORWARD-TO-TRUE-LISTP")
    (h1-recipes-prove-keyword-value-list p formula))
   ((equal name "NATP-POSITION-AC-EQ-EXEC") (h1-recipes-position-type p formula))
   ((text-starts-with name "NATP-POSITION-")
    (h1-recipes-transfer-property p formula (proof-sym "NATP-POSITION-AC-EQ-EXEC" "ACL2")))
   ((member-equal name '("EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE"
                         "RATIONALP-EXPT-TYPE-PRESCRIPTION"))
    (h1-recipes-exponentiation p formula (equal name "EXPT-TYPE-PRESCRIPTION-NON-ZERO-BASE")))
   ((equal name "TRUE-LISTP-SUBSTITUTE-TYPE-PRESCRIPTION") (h1-recipes-substitute-type p formula))
   ((equal name "CHARACTER-LISTP-REMOVE-DUPLICATES") (h1-recipes-remove-duplicates-type p formula))
   (t (h1-recipes-checked-pair (h1-recursion-prove-automatically p formula)))))
