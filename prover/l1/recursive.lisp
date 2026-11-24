(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-recursive-user-application* (proof-sym "APPLY$-USERFN" "ACL2"))
(defconst *l1-recursive-local-agreement* (proof-sym "L1-RECURSIVE-AGREEMENT" "ACL2"))
(defconst *l1-recursive-step-comparison* (proof-sym "L1-RECURSIVE-COMPARISON" "ACL2"))
(defconst *l1-recursive-universal-agreement* (proof-sym "L1-RECURSIVE-INDUCTION" "ACL2"))
(defconst *l1-recursive-atom* (proof-cl "ATOM"))
(defconst *l1-recursive-control* (list *l1-recursive-atom* (proof-cl "ENDP") *proof-not*))

(mutual-recursion
 (defun l1-recursive-has-lambda (term)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
         ((endp term) '(:failure "failure" ""))
         ((proof-compound (car term)) t)
         (t (l1-recursive-arguments-have-lambda (cdr term)))))
 (defun l1-recursive-arguments-have-lambda (args)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (and (consp args)
        (proof-with-checked-results ((found (l1-recursive-has-lambda (car args))))
          (or found (l1-recursive-arguments-have-lambda (cdr args)))))))

(defun l1-recursive-definition (proof name)
  (let ((entry (assoc-equal name (proof-proof-definitions proof))))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun l1-recursive-primitive-names (table)
  (if (endp table)
      nil
    (proof-with-checked-results
        ((name (proof-term-at (car table) 0))
         (rest (l1-recursive-primitive-names (cdr table))))
      (cons name rest))))

(defun l1-recursive-possible-helpers (dependencies direct recursive)
  (if (endp dependencies)
      nil
    (let ((rest (l1-recursive-possible-helpers (cdr dependencies) direct recursive)))
      (if (or (equal (car dependencies) recursive) (member-equal (car dependencies) direct))
          rest
        (cons (car dependencies) rest)))))

(defun l1-recursive-direct-helpers (names definitions direct)
  (if (endp names)
      nil
    (let ((definition (assoc-equal (car names) definitions)))
      (proof-with-checked-results
          ((body (and definition (proof-term-at (cdr definition) 1)))
           (dependencies (and definition (l1-witness-dependencies body)))
           (eligible (and definition (subsetp-equal dependencies direct)))
           (rest (l1-recursive-direct-helpers (cdr names) definitions direct)))
        (if eligible
            (cons (car names) rest)
          rest)))))

(defun l1-recursive-primitive-helpers (proof body recursive)
  (proof-with-checked-results
      ((definition (l1-recursive-definition proof *l1-application-badge-primitive*))
       (table-body (proof-term-at definition 1))
       (application (proof-term-at table-body 1))
       (quoted-table (proof-term-at application 2))
       (table (proof-term-at quoted-table 1))
       (names (l1-recursive-primitive-names table))
       (direct (cons *proof-if* names))
       (dependencies (l1-witness-dependencies body))
       (candidates (seq-sorted (l1-recursive-possible-helpers dependencies direct recursive))))
    (l1-recursive-direct-helpers candidates (proof-proof-definitions proof) direct)))

(defun l1-recursive-introduce-implication (proof hypothesis result)
  (let ((schema (list *library-implies* *library-x* *library-y*))
        (definitions (list *library-implies*)))
    (proof-with-checked-results
        ((first (proof-step-first result))
         (binding (list (list *library-x* hypothesis) (list *library-y* first)))
         (x-yes (proof-proof-assume proof *library-x* t))
         (y-yes (proof-proof-assume proof *library-y* t))
         (yes (l1-application-proof-prove proof schema (list x-yes y-yes) definitions))
         (x-no (proof-proof-assume proof *library-x* nil))
         (no (l1-application-proof-prove proof schema (list x-no) definitions))
         (yes (proof-proof-instantiate proof yes binding))
         (supplied (proof-proof-discharge proof yes result))
         (no (proof-proof-instantiate proof no binding)))
      (proof-proof-cases proof hypothesis supplied no))))

(defun l1-recursive-list-wrapper-wrapper (argument cons proof function)
  (proof-with-checked-results
      ((step (proof-proof-unfold proof (list function argument)))
       (test (proof-proof-assume proof (list *proof-consp* argument) cons))
       (right (proof-rewritten-term step))
       (simplified (l1-application-proof-simplify proof right (list test) *l1-recursive-control*)))
    (proof-proof-chain proof step (list simplified))))

(defun l1-recursive-chain-with-branch (proof step term holds)
  (proof-with-checked-results
      ((branch (if holds (proof-proof-if-true proof term) (proof-proof-if-false proof term)))
       (reversed (proof-proof-symmetric proof branch)))
    (proof-proof-chain proof step (list reversed))))

(defun l1-recursive-list-result-p (value x helper tail)
  (and (proof-is-call value *proof-if*)
       (proof-with-checked-results ((test (proof-term-at value 1)))
         (and (equal test (list *proof-consp* x))
              (proof-with-checked-results ((yes (proof-term-at value 2)))
                (and (proof-is-call yes *proof-cons*)
                     (proof-with-checked-results ((child (proof-term-at yes 2)))
                       (and (equal child (list helper tail))
                            (proof-with-checked-results ((no (proof-term-at value 3)))
                              (equal no *proof-false*))))))))))

(defun l1-recursive-list-wrapper-equation (proof function x base helper tail opened value)
  (let* ((tail-test (list *proof-consp* tail))
         (tail-value (proof-ite tail-test (list function tail) *proof-false*)))
    (proof-with-checked-results
        ((wrapped (l1-recursive-list-wrapper-wrapper tail t proof function))
         (wrapped (proof-proof-symmetric proof wrapped))
         (wrapped (l1-recursive-chain-with-branch proof wrapped tail-value t))
         (empty (proof-proof-unfold proof (list helper tail)))
         (empty-value (proof-rewritten-term empty))
         (branch (proof-proof-if-false proof empty-value))
         (tail-false (proof-proof-if-false proof tail-value))
         (tail-false (proof-proof-symmetric proof tail-false))
         (empty (proof-proof-chain proof empty (list branch tail-false)))
         (tails (proof-proof-cases proof tail-test wrapped empty))
         (head (proof-term-at (caddr value) 1))
         (cons-value (list *proof-cons* head tail-value))
         (test (list *proof-consp* x))
         (definition (proof-ite test cons-value base))
         (cons (l1-recursive-list-wrapper-wrapper x t proof function))
         (value-true (proof-proof-if-true proof value))
         (cons (proof-proof-chain proof cons (list opened value-true)))
         (cons (proof-proof-rewrite proof cons tails '(1 2 2)))
         (yes (l1-recursive-chain-with-branch proof cons definition t))
         (base (l1-recursive-list-wrapper-wrapper x nil proof function))
         (no (l1-recursive-chain-with-branch proof base definition nil)))
      (proof-proof-cases proof test yes no))))

(defun l1-recursive-list-wrapper (proof function formals body)
  (if (or (not (equal (len formals) 1)) (not (proof-is-call body *proof-if*)))
      '(:failure "UnsupportedApplication" "")
    (proof-with-checked-results ((test (proof-term-at body 1)))
      (let ((x (car formals)))
        (if (not (equal test (list *l1-recursive-atom* x)))
            '(:failure "UnsupportedApplication" "")
          (proof-with-checked-results ((parts (proof-list-of-length body 4)))
            (let ((helper (cadddr parts))
                  (base (caddr parts))
                  (tail (list *library-cdr* x)))
              (if (not (and (proof-compound helper) (equal (cdr helper) (list x))))
                  '(:failure "UnsupportedApplication" "")
                (proof-with-checked-results
                    ((opened (proof-proof-unfold proof helper))
                     (value (proof-rewritten-term opened))
                     (valid (l1-recursive-list-result-p value x (car helper) tail)))
                  (if valid
                      (l1-recursive-list-wrapper-equation
                       proof function x base (car helper) tail opened value)
                    '(:failure "UnsupportedApplication" "")))))))))))

(defun l1-recursive-assumptions (proof tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((pair (proof-list-of-length (car tests) 2))
         (step (proof-proof-assume proof (car pair) (cadr pair)))
         (rest (l1-recursive-assumptions proof (cdr tests))))
      (cons step rest))))

(defun l1-recursive-scalar-wrapper-open-at (f arg tests proof other)
  (proof-with-checked-results
      ((step (proof-proof-unfold proof (list f arg other)))
       (evidence (l1-recursive-assumptions proof tests))
       (value (proof-rewritten-term step))
       (simpler (l1-application-proof-simplify proof value evidence *l1-recursive-control*)))
    (proof-proof-chain proof step (list simpler))))

(defun l1-recursive-scalar-wrapper-cons-result (arg proof name other)
  (proof-with-checked-results
      ((step (l1-recursive-scalar-wrapper-open-at
              name arg (list (list (list *proof-consp* arg) t)) proof other))
       (value (proof-rewritten-term step))
       (child (and (proof-is-call value *proof-cons*) (proof-term-at value 2))))
    (if (and (proof-is-call value *proof-cons*)
             (equal child (list name (list *library-cdr* arg) other)))
        step
      '(:failure "UnsupportedApplication" ""))))

(defun l1-recursive-scalar-wrapper-head-of (step cons proof)
  (proof-with-checked-results
      ((projected (proof-proof-rewrite proof step cons '(1 2 1)))
       (value (proof-rewritten-term cons))
       (head (proof-proof-fact proof (proof-sym "CAR-CONS" "ACL2")
                               (seq-zip (list *library-x* *library-y*) (cdr value)))))
    (proof-proof-chain proof projected (list head))))

(defun l1-recursive-scalar-wrapper-tail (proof function name tail other)
  (let* ((tail-test (list *proof-consp* tail))
         (tail-rest (list *library-cdr* tail))
         (child (list function tail other))
         (child-result (proof-ite tail-rest child (list *proof-cons* child *proof-false*))))
    (proof-with-checked-results
        ((tail-cons (l1-recursive-scalar-wrapper-cons-result tail proof name other))
         (nil-or-true (proof-proof-nil-or-true proof tail-rest))
         (single (proof-proof-rewrite proof tail-cons nil-or-true '(1 2 2 1)))
         (empty (l1-recursive-scalar-wrapper-open-at name *proof-false* nil proof other))
         (single (proof-proof-rewrite proof single empty '(1 2 2)))
         (first (l1-recursive-scalar-wrapper-open-at
                 function tail (list (list tail-test t) (list tail-rest nil)) proof other))
         (first (l1-recursive-scalar-wrapper-head-of first single proof))
         (first (proof-proof-symmetric proof first))
         (one (proof-proof-rewrite proof single first '(1 2 1)))
         (many (l1-recursive-scalar-wrapper-open-at
                function tail (list (list tail-test t) (list tail-rest t)) proof other))
         (many (proof-proof-symmetric proof many))
         (yes (l1-recursive-chain-with-branch proof many child-result t))
         (no (l1-recursive-chain-with-branch proof one child-result nil))
         (tail-choice (proof-proof-cases proof tail-rest yes no))
         (child-list (proof-ite tail-test child-result *proof-false*))
         (tail-empty (l1-recursive-scalar-wrapper-open-at
                      name tail (list (list tail-test nil)) proof other))
         (yes (l1-recursive-chain-with-branch proof tail-choice child-list t))
         (no (l1-recursive-chain-with-branch proof tail-empty child-list nil))
         (tail-equation (proof-proof-cases proof tail-test yes no)))
      (list child-list tail-equation))))

(defun l1-recursive-scalar-wrapper-equation (proof function name x other tail test)
  (proof-with-checked-results
      ((tail-result (l1-recursive-scalar-wrapper-tail proof function name tail other))
       (child-list (car tail-result))
       (tail-equation (cadr tail-result))
       (nonempty (l1-recursive-scalar-wrapper-cons-result x proof name other))
       (nonempty-value (proof-rewritten-term nonempty))
       (head (proof-term-at nonempty-value 1))
       (whole (l1-recursive-scalar-wrapper-open-at
               function x (list (list test t) (list tail t)) proof other))
       (whole (proof-proof-chain proof whole (list nonempty)))
       (whole (proof-proof-rewrite proof whole tail-equation '(1 2 2)))
       (scalar (l1-recursive-scalar-wrapper-open-at
                function x (list (list test t) (list tail nil)) proof other))
       (scalar (l1-recursive-scalar-wrapper-head-of scalar nonempty proof))
       (choices (proof-ite tail (list *proof-cons* head child-list) head))
       (yes (l1-recursive-chain-with-branch proof whole choices t))
       (no (l1-recursive-chain-with-branch proof scalar choices nil))
       (positive (proof-proof-cases proof tail yes no))
       (test-no (list (list test nil)))
       (base (l1-recursive-scalar-wrapper-open-at function x test-no proof other))
       (empty (l1-recursive-scalar-wrapper-open-at name x test-no proof other))
       (base (proof-proof-rewrite proof base empty '(1 2 1)))
       (base-value (proof-rewritten-term base))
       (simpler (l1-application-proof-simplify proof base-value nil nil))
       (base (proof-proof-chain proof base (list simpler)))
       (result (proof-ite test choices *proof-false*))
       (yes (l1-recursive-chain-with-branch proof positive result t))
       (no (l1-recursive-chain-with-branch proof base result nil)))
    (proof-proof-cases proof test yes no)))

(defun l1-recursive-scalar-wrapper-p (body helper formals test tail)
  (and (proof-compound helper) (equal (cdr helper) formals)
       (proof-with-checked-results ((no (proof-term-at body 3)))
         (and (equal no (list *library-car* helper))
              (proof-with-checked-results ((condition (proof-term-at body 1)))
                (equal condition (proof-ite test tail *proof-false*)))))))

(defun l1-recursive-scalar-wrapper (proof function formals body)
  (if (or (not (equal (len formals) 2)) (not (proof-is-call body *proof-if*)))
      '(:failure "UnsupportedApplication" "")
    (let* ((x (car formals))
           (other (cadr formals))
           (tail (list *library-cdr* x))
           (test (list *proof-consp* x)))
      (proof-with-checked-results
          ((helper (proof-term-at body 2))
           (valid (l1-recursive-scalar-wrapper-p body helper formals test tail)))
        (if valid
            (l1-recursive-scalar-wrapper-equation proof function (car helper) x other tail test)
          '(:failure "UnsupportedApplication" ""))))))

(defun l1-recursive-recurrence-proof (recurrence) (nth 1 recurrence))
(defun l1-recursive-recurrence-comparison (recurrence) (nth 2 recurrence))
(defun l1-recursive-recurrence-argument (recurrence) (nth 3 recurrence))
(defun l1-recursive-recurrence-badge (recurrence) (nth 4 recurrence))
(defun l1-recursive-recurrence-agreement (recurrence) (nth 5 recurrence))
(defun l1-recursive-recurrence-oracle (recurrence) (nth 6 recurrence))
(defun l1-recursive-recurrence-logical (recurrence) (nth 7 recurrence))
(defun l1-recursive-recurrence-function (recurrence) (nth 8 recurrence))
(defun l1-recursive-recurrence-open-logic (recurrence) (nth 9 recurrence))
(defun l1-recursive-recurrence-body (recurrence) (nth 10 recurrence))
(defun l1-recursive-recurrence-child (recurrence) (nth 11 recurrence))
(defun l1-recursive-recurrence-recursive-oracle (recurrence) (nth 12 recurrence))
(defun l1-recursive-recurrence-one-step (recurrence) (nth 13 recurrence))
(defun l1-recursive-recurrence-recurrence (recurrence) (nth 14 recurrence))
(defun l1-recursive-recurrence-parent (recurrence) (nth 15 recurrence))
(defun l1-recursive-recurrence-measure (recurrence) (nth 16 recurrence))
(defun l1-recursive-recurrence-smaller (recurrence) (nth 17 recurrence))
(defun l1-recursive-recurrence-agreement-child (recurrence) (nth 18 recurrence))
(defun l1-recursive-recurrence-child-requirement (recurrence) (nth 19 recurrence))

(defun l1-recursive-recurrence-with-proof (recurrence proof)
  (list* :recurrence proof (cddr recurrence)))

(defun l1-recursive-substitute-argument (term variable argument)
  (proof-subst term (list (cons variable argument))))

(defun l1-recursive-recurrence-at (recurrence term argument)
  (l1-recursive-substitute-argument term (l1-recursive-recurrence-argument recurrence) argument))

(mutual-recursion
 (defun l1-recursive-replace-call (term function oracle variable)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond ((proof-is-call term function)
          (l1-recursive-substitute-argument
           oracle variable (l1-primitive-cons-list (cdr term) *proof-false*)))
         ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) term)
         ((endp term) '(:failure "failure" ""))
         (t
          (proof-with-checked-results
              ((terms (l1-recursive-replace-arguments (cdr term) function oracle variable)))
            (cons (car term) terms)))))
 (defun l1-recursive-replace-arguments (terms function oracle variable)
   (declare (xargs :measure (* 2 (acl2-count terms))))
   (if (endp terms)
       nil
     (proof-with-checked-results
         ((term (l1-recursive-replace-call (car terms) function oracle variable))
          (rest (l1-recursive-replace-arguments (cdr terms) function oracle variable)))
       (cons term rest)))))

(defun l1-recursive-recurrence-replace-recursive-call (recurrence term)
  (l1-recursive-replace-call term (l1-recursive-recurrence-function recurrence)
                             (l1-recursive-recurrence-oracle recurrence)
                             (l1-recursive-recurrence-argument recurrence)))

(defun l1-recursive-pairs-to-map (pairs bindings)
  (if (endp pairs)
      bindings
    (l1-recursive-pairs-to-map
     (cdr pairs) (table-put bindings (caar pairs) (cadar pairs)))))

(defun l1-recursive-actual-lists (calls)
  (if (endp calls)
      nil
    (cons (termination-call-actuals (car calls)) (l1-recursive-actual-lists (cdr calls)))))

(defun l1-recursive-descent-position (formals call index)
  (if (endp formals)
      :none
    (proof-with-checked-results ((argument (proof-term-at call index)))
      (if (equal argument (list *library-cdr* (car formals)))
          index
        (l1-recursive-descent-position (cdr formals) call (1+ index))))))

(defun l1-recursive-substitute-actuals (actuals bindings)
  (if (endp actuals)
      nil
    (proof-with-checked-results
        ((term (proof-subst (car actuals) bindings))
         (rest (l1-recursive-substitute-actuals (cdr actuals) bindings)))
      (cons term rest))))

(defun l1-recursive-discover-recurrence (proof function formals body bindings open-logic calls)
  (if calls
      (list body open-logic calls)
    (let ((equation (l1-lexicographic-length-wrapper proof function formals body)))
      (proof-with-checked-results
          ((equation (if (and (failure-p equation)
                              (equal (cadr equation) "UnsupportedApplication"))
                         (if (equal (len formals) 1)
                             (l1-recursive-list-wrapper proof function formals body)
                           (l1-recursive-scalar-wrapper proof function formals body))
                       equation))
           (body (proof-rewritten-term equation))
           (open-logic (proof-proof-instantiate proof equation (table-items bindings)))
           (calls (termination-recursive-calls *termination-all*
                                               (list (list function formals body)))))
        (list body open-logic calls)))))

(defun l1-recursive-opening (proof function body)
  (proof-with-checked-results ((has-lambda (l1-recursive-has-lambda body)))
    (if has-lambda
        (proof-with-checked-results
            ((helpers (l1-recursive-primitive-helpers proof body function))
             (application (l1-application-application-init proof function nil helpers :default)))
          (l1-application-application-reduce application body))
      (l1-application-proof-simplify proof body nil (list *termination-return-last*)))))

(defun l1-recursive-open-logic (proof logical opening bindings)
  (proof-with-checked-results ((opened (proof-proof-unfold proof logical)))
    (if opening
        (proof-with-checked-results
            ((instantiated (proof-proof-instantiate proof opening (table-items bindings))))
          (proof-proof-chain proof opened (list instantiated)))
      opened)))

(defun l1-recursive-prepare-recurrence (proof function logical)
  (proof-with-checked-results
      ((definition (l1-recursive-definition proof function))
       (definition (proof-list-of-length definition 2))
       (formals (car definition))
       (opening (l1-recursive-opening proof function (cadr definition)))
       (body (if opening (proof-rewritten-term opening) (cadr definition)))
       (calls (termination-recursive-calls *termination-all*
                                           (list (list function formals body))))
       (bindings (l1-recursive-pairs-to-map (seq-zip formals (cdr logical)) nil))
       (open-logic (l1-recursive-open-logic proof logical opening bindings))
       (recursion (l1-recursive-discover-recurrence
                   proof function formals body bindings open-logic calls))
       (actuals (proof-unique (l1-recursive-actual-lists (caddr recursion)))))
    (if (not (equal (len actuals) 1))
        '(:failure "UnsupportedApplication" "")
      (proof-with-checked-results
          ((call (car actuals))
           (descent (l1-recursive-descent-position formals call 0)))
        (if (eq descent :none)
            '(:failure "UnsupportedApplication" "")
          (list (car recursion) (cadr recursion) call descent bindings))))))

(defun l1-recursive-finish-recurrence (proof comparison argument badge agreement oracle logical function)
  (proof-with-checked-results
      ((prepared (l1-recursive-prepare-recurrence proof function logical))
       (body (car prepared))
       (open-logic (cadr prepared))
       (call (caddr prepared))
       (descent (cadddr prepared))
       (actuals (l1-recursive-substitute-actuals call (nth 4 prepared)))
       (child (l1-primitive-cons-list actuals *proof-false*))
       (recursive-oracle (l1-recursive-substitute-argument oracle argument child))
       (logical-value (proof-rewritten-term open-logic))
       (one-step (l1-recursive-replace-call logical-value function oracle argument))
       (recurrence (proof-eq oracle one-step))
       (parent (proof-term-at logical (1+ descent)))
       (measure (list *library-count* parent))
       (child-measure (l1-recursive-substitute-argument measure argument child))
       (smaller (list *proof-ordinal-less* child-measure measure))
       (agreement-child (l1-recursive-substitute-argument agreement argument child))
       (child-requirement (proof-ite smaller agreement-child *proof-true*)))
    (list :recurrence proof comparison argument badge agreement oracle logical function
          open-logic body child recursive-oracle one-step recurrence parent measure
          smaller agreement-child child-requirement)))

(defun l1-recursive-recurrence-init (proof comparison badge-test)
  (proof-with-checked-results
      ((argument (l1-witness-comparison-argument comparison))
       (badge (proof-term-at badge-test 1))
       (agreement (proof-term-at badge-test 2))
       (sides (proof-list-of-length (cdr agreement) 2))
       (oracle (car sides))
       (logical (cadr sides))
       (function (proof-term-at logical 0)))
    (if (equal oracle (list *l1-recursive-user-application* (proof-quote function) argument))
        (l1-recursive-finish-recurrence
         proof comparison argument badge agreement oracle logical function)
      '(:failure "failure" ""))))

(defun l1-recursive-positive-cons-test (tests proof cons-test)
  (if (endp tests)
      nil
    (proof-with-checked-results ((pair (proof-list-of-length (car tests) 2)))
      (if (and (equal (car pair) cons-test) (cadr pair))
          (proof-proof-assume proof (car pair) t)
        (l1-recursive-positive-cons-test (cdr tests) proof cons-test)))))

(defun l1-recursive-negative-cons-test (proof test cons-test)
  (proof-with-checked-results
      ((not-cons (proof-proof-assume proof cons-test nil))
       (opened (l1-application-proof-simplify proof test (list not-cons) *l1-recursive-control*))
       (value (and opened (proof-rewritten-term opened))))
    (and (equal value *proof-true*)
         (proof-with-checked-results
             ((yes (proof-proof-true-from-eq proof opened))
              (no (proof-proof-assume proof test nil))
              (absurd (proof-proof-cut proof yes no)))
           (and (member-equal cons-test (proof-step-clause absurd))
                (proof-proof-front proof absurd cons-test))))))

(defun l1-recursive-negative-cons-tests (tests proof cons-test)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((pair (proof-list-of-length (car tests) 2))
         (step (and (not (cadr pair))
                    (l1-recursive-negative-cons-test proof (car pair) cons-test))))
      (or step (l1-recursive-negative-cons-tests (cdr tests) proof cons-test)))))

(defun l1-recursive-recurrence-child-agreement (recurrence tests)
  (let* ((proof (l1-recursive-recurrence-proof recurrence))
         (parent (l1-recursive-recurrence-parent recurrence))
         (cons-test (list *proof-consp* parent)))
    (proof-with-checked-results
        ((test-step (l1-recursive-positive-cons-test tests proof cons-test))
         (test-step (or test-step (l1-recursive-negative-cons-tests tests proof cons-test))))
      (if (not test-step)
          '(:failure "UnsupportedApplication" "")
        (proof-with-checked-results
            ((smaller (proof-proof-fact proof "built-in-clause-3"
                                        (list (list *library-x* parent))))
             (smaller (proof-proof-discharge proof smaller test-step))
             (reduction (l1-application-application-init
                         proof (l1-recursive-recurrence-function recurrence) nil nil :default))
             (projection (l1-recursive-recurrence-at
                          recurrence parent (l1-recursive-recurrence-child recurrence)))
             (projected (l1-application-application-reduce reduction projection))
             (reversed (if projected
                           (proof-proof-symmetric proof projected)
                         '(:failure "failure" "")))
             (smaller (proof-proof-rewrite proof smaller reversed '(1 1 1)))
             (smaller (proof-proof-tidy proof smaller))
             (step (proof-proof-assume proof (l1-recursive-recurrence-child-requirement recurrence) t))
             (child (proof-proof-prove-if proof step smaller))
             (first (proof-step-first child))
             (actuals (l1-application-application-arguments reduction first '(2))))
          (if actuals
              (proof-with-checked-results ((child (proof-proof-rewrite proof child actuals '(1))))
                (proof-proof-tidy proof child))
            child))))))

(defun l1-recursive-local-leaf (recurrence logical oracle left right tests)
  (let ((proof (l1-recursive-recurrence-proof recurrence)))
    (proof-with-checked-results
        ((step (if (equal left right)
                   oracle
                 (proof-with-checked-results
                     ((agreement (l1-recursive-recurrence-child-agreement recurrence tests))
                      (template (proof-eq (proof-sym "L1-UNCHANGED" "ACL2") right)))
                   (proof-proof-rewrite-result
                    proof oracle agreement template
                    (l1-recursive-recurrence-recursive-oracle recurrence)))))
         (reversed (proof-proof-symmetric proof logical))
         (step (proof-proof-chain proof step (list reversed)))
         (first (proof-step-first step)))
      (if (not (equal first (proof-eq (l1-recursive-recurrence-one-step recurrence)
                                      (l1-recursive-recurrence-logical recurrence))))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((reflexive (proof-proof-reflexive proof (l1-recursive-recurrence-recurrence recurrence)))
             (rewritten (proof-proof-rewrite proof reflexive step '(1 2 2))))
          (proof-proof-tidy proof rewritten))))))

(defund l1-recursive-local-branch (proof logical oracle left right test holds)
  (proof-with-checked-results
      ((evidence (proof-proof-assume proof test holds))
       (selected (proof-proof-select proof left evidence))
       (a (proof-proof-chain proof logical (list selected)))
       (selected (proof-proof-select proof right evidence))
       (b (proof-proof-chain proof oracle (list selected))))
    (list a b)))

(defund l1-recursive-local-case (recurrence logical oracle tests)
  (proof-with-checked-results
      ((left (proof-rewritten-term logical))
       (right (proof-rewritten-term oracle)))
    (if (not (proof-is-call left *proof-if*))
        (l1-recursive-local-leaf recurrence logical oracle left right tests)
      (proof-with-checked-results
          ((test (proof-term-at left 1))
           (right-head (proof-term-at right 0))
           (right-test (and (equal right-head *proof-if*) (proof-term-at right 1))))
        (if (and (equal right-head *proof-if*) (equal right-test test))
            (list :conditional left right test)
          '(:failure "failure" ""))))))

(defun l1-recursive-local-visit (n recurrence logical oracle tests)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "l1-recursive-local-visit")
    (let ((result (l1-recursive-local-case recurrence logical oracle tests)))
      (if (not (eq (car result) :conditional))
          result
        (let ((proof (l1-recursive-recurrence-proof recurrence))
              (left (cadr result))
              (right (caddr result))
              (test (cadddr result)))
          (proof-with-checked-results
              ((opened (l1-recursive-local-branch proof logical oracle left right test t))
               (yes (l1-recursive-local-visit
                     (1- n) recurrence (car opened) (cadr opened)
                     (append tests (list (list test t)))))
               (opened (l1-recursive-local-branch proof logical oracle left right test nil))
               (no (l1-recursive-local-visit
                    (1- n) recurrence (car opened) (cadr opened)
                    (append tests (list (list test nil))))))
            (proof-proof-cases proof test yes no)))))))

(defun l1-recursive-recurrence-local-agreement (recurrence logical oracle tests)
  (let ((logical (or logical (l1-recursive-recurrence-open-logic recurrence))))
    (proof-with-checked-results
        ((oracle (or oracle (proof-proof-reflexive
                             (l1-recursive-recurrence-proof recurrence)
                             (l1-recursive-recurrence-one-step recurrence)))))
      (l1-recursive-local-visit 1000000 recurrence logical oracle tests))))

(defun l1-recursive-step-term (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun l1-recursive-recurrence-comparison-equation (recurrence)
  (let ((proof (l1-recursive-recurrence-proof recurrence)))
    (proof-with-checked-results
        ((badge (proof-term-at (l1-recursive-recurrence-badge recurrence) 2))
         (results (l1-application-quoted-application
                   proof (l1-recursive-recurrence-function recurrence)
                   (l1-recursive-recurrence-argument recurrence) badge
                   (l1-recursive-recurrence-one-step recurrence)
                   (l1-recursive-recurrence-body recurrence)))
         (results (proof-list-of-length results 4))
         (oracle (caddr results))
         (body (cadddr results))
         (original-oracle (l1-recursive-step-term oracle 1))
         (original-body (l1-recursive-step-term body 1))
         (equation (proof-proof-reflexive proof (proof-eq original-oracle original-body)))
         (equation (proof-proof-rewrite proof equation oracle '(1 2 1)))
         (equation (proof-proof-rewrite proof equation body '(1 2 2)))
         (value (proof-rewritten-term equation)))
      (if (not (equal value (l1-recursive-recurrence-recurrence recurrence)))
          '(:failure "failure" "")
        (proof-with-checked-results ((step (proof-proof-tidy proof equation)))
          (list (car results) (cadr results) step))))))

(defun l1-recursive-recurrence-when-child-agrees (recurrence condition agreement)
  (let ((proof (l1-recursive-recurrence-proof recurrence)))
    (proof-with-checked-results
        ((branch (proof-proof-if-true proof condition))
         (yes (proof-proof-transport proof agreement branch))
         (truth (l1-application-proof-prove proof *proof-true* nil nil))
         (branch (proof-proof-if-false proof condition))
         (no (proof-proof-transport proof truth branch))
         (test (proof-term-at condition 1)))
      (proof-proof-cases proof test yes no))))

(defund l1-recursive-rewrite-necessity-at (proof first badge variable argument index)
  (proof-with-checked-results
      ((equation (proof-proof-use proof *l1-recursive-step-comparison*
                                  (list (list variable argument)) (list badge))))
    (proof-proof-rewrite proof first equation (list 1 index 1))))

(defun l1-recursive-rewrite-necessity (proof first badge variable arguments index)
  (declare (xargs :measure (acl2-count arguments)))
  (if (endp arguments)
      first
    (proof-with-checked-results
        ((next (l1-recursive-rewrite-necessity-at
                proof first badge variable (car arguments) index)))
      (l1-recursive-rewrite-necessity proof next badge variable (cdr arguments) (1+ index)))))

(defun l1-recursive-simplify-necessity (proof necessity)
  (proof-with-checked-results
      ((literal (proof-step-first necessity))
       (equation (l1-application-proof-simplify proof literal nil
                                               (list *termination-return-last*))))
    (if equation
        (proof-with-checked-results
            ((rewritten (proof-proof-rewrite proof necessity equation '(1))))
          (proof-proof-tidy proof rewritten))
      necessity)))

(defun l1-recursive-induction-necessity (proof left right selector argument picked badge)
  (let* ((parameters (l1-witness-choice-rule-parameters selector))
         (bindings (l1-recursive-pairs-to-map (seq-zip parameters (list left right)) nil))
         (bindings (table-put bindings (l1-witness-choice-rule-argument selector) argument)))
    (proof-with-checked-results
        ((necessity (l1-witness-choice-rule-counterexample-proof selector proof bindings))
         (necessity (l1-recursive-simplify-necessity proof necessity)))
      (l1-recursive-rewrite-necessity proof necessity badge argument (list argument picked) 1))))

(defun l1-recursive-recurrence-induct (recurrence left right selector picked)
  (let* ((proof (l1-recursive-recurrence-proof recurrence))
         (argument (l1-recursive-recurrence-argument recurrence))
         (relation (l1-recursive-recurrence-recurrence recurrence))
         (smaller (l1-recursive-recurrence-smaller recurrence))
         (child (l1-recursive-recurrence-child recurrence)))
    (proof-with-checked-results
        ((at-picked (l1-recursive-recurrence-at recurrence relation picked))
         (premise (proof-ite (l1-recursive-recurrence-badge recurrence) at-picked *proof-false*))
         (formula (list *library-implies* premise (l1-recursive-recurrence-agreement recurrence)))
         (assumed (proof-proof-assume proof premise t))
         (evidence (proof-proof-conjunct proof assumed))
         (necessity (l1-recursive-induction-necessity
                     proof left right selector argument picked (car evidence)))
         (failure (proof-proof-assume proof relation nil))
         (impossible (proof-proof-modus-ponens proof necessity failure))
         (current (proof-proof-cut proof (cadr evidence) impossible))
         (current (proof-proof-front proof current relation))
         (induction (l1-recursive-recurrence-at recurrence formula child))
         (hypothesis (proof-proof-assume proof (proof-ite smaller induction *proof-true*) t))
         (decrease (proof-proof-assume proof smaller t))
         (smaller-step (proof-proof-prove-if proof hypothesis decrease))
         (agrees (proof-proof-modus-ponens proof smaller-step assumed))
         (child-step (l1-recursive-recurrence-when-child-agrees
                      recurrence (l1-recursive-recurrence-child-requirement recurrence) agrees))
         (bridge (proof-proof-use proof *l1-recursive-local-agreement* nil (list child-step)))
         (value (proof-proof-rewrite proof current bridge '(1)))
         (value (proof-proof-tidy proof value))
         (case-step (l1-recursive-introduce-implication proof premise value))
         (ordinal (proof-proof-fact
                   proof "built-in-clause-1"
                   (list (list *library-x* (l1-recursive-recurrence-parent recurrence)))))
         (substitutions (list (list (list argument child))))
         (step (proof-proof-induct proof ordinal case-step formula
                                   (l1-recursive-recurrence-measure recurrence) substitutions)))
      (list premise step))))

(defun l1-recursive-local-failure (recurrence failure premise at-picked)
  (let ((proof (l1-recursive-recurrence-proof recurrence)))
    (proof-with-checked-results
        ((failure-step (proof-proof-assume proof failure t))
         (contract (proof-term-at failure 1))
         (required (proof-proof-if-true proof contract))
         (original-bad (proof-proof-rewrite proof failure-step required '(1 1)))
         (picked-proof (proof-proof-assume proof at-picked t))
         (selected (proof-proof-if-true proof premise))
         (if-local (proof-proof-transport proof picked-proof selected))
         (universal (proof-proof-fact proof *l1-recursive-universal-agreement* nil))
         (agrees (proof-proof-modus-ponens proof universal if-local))
         (local-bad (proof-proof-cut proof agrees original-bad)))
      (proof-proof-front proof local-bad (proof-neg at-picked)))))

(defun l1-recursive-selected-failure (recurrence picked local-bad)
  (let* ((proof (l1-recursive-recurrence-proof recurrence))
         (agreement (l1-recursive-recurrence-agreement recurrence))
         (argument (l1-recursive-recurrence-argument recurrence)))
    (proof-with-checked-results
        ((picked-child (l1-recursive-recurrence-at
                        recurrence (l1-recursive-recurrence-child recurrence) picked))
         (picked-agrees (l1-recursive-recurrence-at recurrence agreement picked))
         (child-agrees (l1-recursive-recurrence-at recurrence agreement picked-child))
         (condition (l1-recursive-recurrence-at
                     recurrence (l1-recursive-recurrence-child-requirement recurrence) picked))
         (evidence (proof-proof-assume proof child-agrees t))
         (child (l1-recursive-recurrence-when-child-agrees recurrence condition evidence))
         (bridge (proof-proof-use proof *l1-recursive-local-agreement*
                                  (list (list argument picked)) (list child)))
         (picked-proof (proof-proof-assume proof picked-agrees t))
         (contradiction (proof-proof-transport proof picked-proof bridge))
         (child-bad (proof-proof-cut proof contradiction local-bad))
         (child-bad (proof-proof-front proof child-bad (proof-neg child-agrees)))
         (candidate (proof-ite picked-agrees picked-child picked))
         (test (proof-neg agreement))
         (selected (proof-proof-if-true proof candidate))
         (selected (proof-proof-symmetric proof selected))
         (yes (proof-proof-rewrite-result proof child-bad selected test argument))
         (not-picked (proof-proof-assume proof picked-agrees nil))
         (selected (proof-proof-if-false proof candidate))
         (selected (proof-proof-symmetric proof selected))
         (no (proof-proof-rewrite-result proof not-picked selected test argument))
         (selected-bad (proof-proof-cases proof picked-agrees yes no)))
      (list candidate selected-bad))))

(defun l1-recursive-recurrence-locate (recurrence picked premise bad-argument bad-failure)
  (let* ((proof (l1-recursive-recurrence-proof recurrence))
         (failure (l1-witness-comparison-counterexample
                   (l1-recursive-recurrence-comparison recurrence)))
         (argument (l1-recursive-recurrence-argument recurrence))
         (badge (l1-recursive-recurrence-badge recurrence)))
    (proof-with-checked-results
        ((at-picked (l1-recursive-recurrence-at
                     recurrence (l1-recursive-recurrence-recurrence recurrence) picked))
         (local-bad (l1-recursive-local-failure recurrence failure premise at-picked))
         (selection (l1-recursive-selected-failure recurrence picked local-bad))
         (candidate (car selection))
         (selected-bad (cadr selection))
         (contract (proof-term-at failure 1))
         (instantiated (l1-recursive-recurrence-at recurrence contract candidate))
         (restored (proof-proof-if-true proof instantiated))
         (restored (proof-proof-symmetric proof restored))
         (restored (proof-proof-rewrite proof selected-bad restored '(1 1)))
         (restored (proof-proof-tidy proof restored))
         (chosen (proof-ite badge candidate bad-argument))
         (selected (proof-proof-if-true proof chosen))
         (selected (proof-proof-symmetric proof selected))
         (yes (proof-proof-rewrite-result proof restored selected failure argument))
         (selected (proof-proof-if-false proof chosen))
         (selected (proof-proof-symmetric proof selected))
         (no (proof-proof-rewrite-result proof bad-failure selected failure argument))
         (cases (proof-proof-cases proof badge yes no))
         (necessary (l1-recursive-introduce-implication proof failure cases)))
      (list chosen necessary))))

(defun l1-recursive-certificate-totals (entries source)
  (if (endp entries)
      (list 0 (length source) (list source))
    (let* ((entry (car entries))
           (text (caddr entry))
           (rest (l1-recursive-certificate-totals (cdr entries) source)))
      (list (+ (cadr entry) (car rest))
            (+ (length text) (cadr rest))
            (cons text (caddr rest))))))

(defun l1-recursive-collect-source (length)
  (if (> length 10000000)
      #+sbcl (gc$ :full t)
      #-sbcl (gc$)
    nil))

(defun l1-recursive-append-source (left right)
  (prog2$ (l1-recursive-collect-source (+ (length left) (length right)))
          (string-append left right)))

(defun l1-recursive-join-pairs (sources)
  (if (and (consp sources) (consp (cdr sources)))
      (cons (l1-recursive-append-source (car sources) (cadr sources))
            (l1-recursive-join-pairs (cddr sources)))
    sources))

(defun l1-recursive-join-sources (n sources)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "l1-recursive-join-sources"))
        ((endp sources) "")
        ((endp (cdr sources)) (car sources))
        (t (l1-recursive-join-sources (1- n) (l1-recursive-join-pairs sources)))))

(defun l1-recursive-witness-totals (entries count source)
  (let ((totals (l1-recursive-certificate-totals entries source)))
    (prog2$ (l1-recursive-collect-source (cadr totals))
            (proof-with-checked-results ((text (l1-recursive-join-sources 1000000 (caddr totals))))
              (list (+ count (car totals)) text)))))

(defund l1-recursive-witness-parts (proof comparison test selector bad-argument bad-failure)
  (proof-with-checked-results
      ((recurrence (l1-recursive-recurrence-init proof comparison test))
       (equation (l1-recursive-recurrence-comparison-equation recurrence))
       (left (car equation))
       (right (cadr equation))
       (picked (list (l1-witness-choice-rule-name selector) left right))
       (certificates (l1-primitive-certificates-init proof))
       (local (l1-recursive-recurrence-local-agreement recurrence nil nil nil))
       (first (proof-step-first local))
       (local (proof-proof-subsume proof local
                                  (list first (proof-neg
                                               (l1-recursive-recurrence-child-requirement recurrence)))))
       (added (l1-primitive-certificates-add certificates *l1-recursive-local-agreement* local))
       (dispatched (l1-primitive-discharge-primitives
                    (cdr added) (caddr equation) (l1-recursive-recurrence-badge recurrence)))
       (added (l1-primitive-certificates-add
               (cdr dispatched) *l1-recursive-step-comparison* (car dispatched)))
       (recurrence (l1-recursive-recurrence-with-proof
                    recurrence (l1-primitive-certificates-proof (cdr added))))
       (induction (l1-recursive-recurrence-induct recurrence left right selector picked))
       (added (l1-primitive-certificates-add
               (cdr added) *l1-recursive-universal-agreement* (cadr induction)))
       (certificates (cdr added))
       (proof (l1-primitive-certificates-proof certificates))
       (recurrence (l1-recursive-recurrence-with-proof recurrence proof))
       (selected (l1-recursive-recurrence-locate
                  recurrence picked (car induction) bad-argument bad-failure))
       (witness (l1-witness-witness-entry proof comparison (car selected) (cadr selected) "")))
    (if witness
        (cons (l1-primitive-certificates-entries certificates) witness)
      '(:failure "failure" ""))))

(defun l1-recursive-recursive-witness (proof comparison test selector bad-argument bad-failure)
  (proof-with-checked-results
      ((parts (l1-recursive-witness-parts proof comparison test selector bad-argument bad-failure)))
    (l1-recursive-witness-totals (car parts) (cadr parts) (caddr parts))))
