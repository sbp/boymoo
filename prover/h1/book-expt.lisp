(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-book-expt-numeric-equal* (proof-cl "="))

(mutual-recursion
 (defun h1-book-expt-base-factors (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((or (proof-is-call term *proof-times*)
              (proof-is-call term *h1-book-arithmetic-reciprocal*))
          (h1-book-expt-base-factors-arguments (cdr term)))
         ((proof-is-call term *proof-quote*) nil)
         (t (list term))))
 (defun h1-book-expt-base-factors-arguments (arguments)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (append (h1-book-expt-base-factors (car arguments))
             (h1-book-expt-base-factors-arguments (cdr arguments))))))

(defun h1-book-expt-checked-pair (result)
  (cond ((failure-p result) result)
        ((failure-p (car result)) (car result))
        (t result)))

(defun h1-book-expt-find (normalizer term)
  (proof-with-checked-results
      ((found (h1-book-expt-checked-pair
               (h1-tactics-context-find
                (h1-book-arithmetic-algebra-context normalizer) term))))
    (cons (car found)
          (h1-book-arithmetic-algebra-with-context normalizer (cdr found)))))

(defun h1-book-expt-open-power-numeric-evidence (lib test normalizer)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((expanded (proof-proof-unfold proof test))
         (literal (proof-step-first expanded))
         (right (proof-term-at literal 2))
         (value (h1-book-expt-checked-pair
                 (h1-book-arithmetic-algebra-normal normalizer right)))
         (selected (proof-proof-chain proof expanded (list (car value))))
         (literal (proof-step-first (car value)))
         (right (proof-term-at literal 2))
         (evidence
          (cond ((equal right *proof-true*)
                 (proof-proof-true-from-eq proof selected))
                ((equal right *proof-false*)
                 (proof-with-checked-results ((not-nil (proof-proof-not-nil proof)))
                   (h1-propositions-library-transport-argument lib not-nil selected 1)))
                (t nil))))
      (cons evidence (cdr value)))))

(defun h1-book-expt-open-power-evidence (lib test normalizer)
  (proof-with-checked-results
      ((yes (h1-book-expt-find normalizer test))
       (found (if (car yes)
                  yes
                (h1-book-expt-find (cdr yes) (proof-neg test)))))
    (if (and (not (car found)) (proof-is-call test *h1-book-expt-numeric-equal*))
        (h1-book-expt-open-power-numeric-evidence lib test (cdr found))
      found)))

(defun h1-book-expt-open-power-next (lib equation normalizer)
  (proof-with-checked-results
      ((literal (proof-step-first equation))
       (branch (proof-term-at literal 2)))
    (if (not (proof-is-call branch *proof-if*))
        (cons equation normalizer)
    (proof-with-checked-results
          ((test (proof-term-at branch 1))
           (found (h1-book-expt-open-power-evidence lib test normalizer)))
        (if (not (car found))
            '(:failure "unproved" "")
          (proof-with-checked-results
              ((choice (h1-propositions-propositional-proof-select lib branch (car found)))
               (next (proof-proof-chain (library-library-proof lib) equation (list choice))))
            (cons :continue (cons next (cdr found)))))))))

(defun h1-book-expt-open-power-branches (n lib next)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "h1-book-expt-open-power-branches"))
        ((eq (car next) :continue)
         (h1-book-expt-open-power-branches
          (1- n) lib (h1-book-expt-open-power-next lib (cadr next) (cddr next))))
        (t next)))

(defun h1-book-expt-open-power (proof term normalizer)
  (proof-with-checked-results
      ((equation (proof-proof-unfold (h1-tactics-prover-proof proof) term)))
    (h1-book-expt-open-power-branches
     1000000 (h1-tactics-prover-library proof) (cons :continue (cons equation normalizer)))))

(defun h1-book-expt-unfold-powers-one (proof term power result)
  (if (not (member-equal power (h1-tactics-subterms term)))
      result
    (proof-with-checked-results
        ((opened (h1-book-expt-open-power proof power (cdr result)))
         (literal (proof-step-first (car result)))
         (right (proof-term-at literal 2))
         (rewritten (proof-proof-rewrite-result
                     (h1-tactics-prover-proof proof) (car result) (car opened)
                     (proof-eq *proof-result* right) power)))
      (cons rewritten (cdr opened)))))

(defun h1-book-expt-unfold-powers-visit (proof term powers result)
  (declare (xargs :measure (acl2-count powers)))
  (if (or (endp powers) (failure-p result))
      result
    (h1-book-expt-unfold-powers-visit
     proof term (cdr powers) (h1-book-expt-unfold-powers-one proof term (car powers) result))))

(defun h1-book-expt-unfold-powers (proof term powers normalizer)
  (proof-with-checked-results
      ((result (h1-propositions-propositional-proof-reflexive
                (h1-tactics-prover-library proof) term)))
    (h1-book-expt-unfold-powers-visit proof term powers (cons result normalizer))))

(defun h1-book-expt-powers (terms)
  (cond ((endp terms) nil)
        ((proof-is-call (car terms) *h1-arithmetic-expt*)
         (cons (car terms) (h1-book-expt-powers (cdr terms))))
        (t (h1-book-expt-powers (cdr terms)))))

(defun h1-book-expt-exponents (powers)
  (declare (xargs :measure (acl2-count powers)))
  (if (endp powers)
      nil
    (proof-with-checked-results
        ((exponent (proof-term-at (car powers) 2))
         (rest (h1-book-expt-exponents (cdr powers))))
      (cons exponent rest))))

(mutual-recursion
 (defun h1-book-expt-contains-power (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((proof-is-call term *h1-arithmetic-expt*) t)
         ((or (not (consp term)) (not (proof-compound term))
              (proof-is-call term *proof-quote*)) nil)
         (t (h1-book-expt-contains-power-arguments (cdr term)))))
 (defun h1-book-expt-contains-power-arguments (terms)
   (declare (xargs :measure (acl2-count terms)))
   (and (consp terms)
        (or (h1-book-expt-contains-power (car terms))
            (h1-book-expt-contains-power-arguments (cdr terms))))))

(defun h1-book-expt-nested-powers (powers)
  (declare (xargs :measure (acl2-count powers)))
  (if (endp powers)
      nil
    (proof-with-checked-results ((base (proof-term-at (car powers) 1)))
      (or (h1-book-expt-contains-power base)
          (h1-book-expt-nested-powers (cdr powers))))))

(defun h1-book-expt-power-factors (powers)
  (declare (xargs :measure (acl2-count powers)))
  (if (endp powers)
      nil
    (proof-with-checked-results ((base (proof-term-at (car powers) 1)))
      (let ((factors (h1-book-expt-base-factors base)))
        (proof-with-checked-results ((rest (h1-book-expt-power-factors (cdr powers))))
          (append factors rest))))))

(defun h1-book-expt-zero-tests (factors)
  (if (endp factors)
      nil
    (cons (proof-eq (list *h1-book-arithmetic-fix* (car factors)) *proof-zero*)
          (h1-book-expt-zero-tests (cdr factors)))))

(defun h1-book-expt-arithmetic-reply (proof method args)
  (case method
    (:solve
     (cons (h1-tactics-prover-solve proof (car args) (cadr args) (caddr args)) proof))
    (:helper
     (let ((result (h1-tactics-prover-helper
                    proof (car args) (cadr args) (caddr args) (cadddr args))))
       (if (failure-p result)
           (cons result proof)
         (cons (cons (car result) (h1-tactics-prover-library (cdr result)))
               (cdr result)))))
    (otherwise
     (cons '(:failure "failure" "") proof))))

(defun h1-book-expt-arithmetic-next (recipe proof exponent library replies)
  (let ((result (if (eq recipe :signed-countdowns)
                    (h1-arithmetic-signed-countdowns library exponent replies)
                  (h1-arithmetic-zero-product-rules library replies))))
    (cond ((failure-p result) (cons result proof))
          ((h1-arithmetic-request-p result)
           (let* ((proof (h1-tactics-prover-with-library
                          proof (h1-arithmetic-request-library result)))
                  (reply (h1-book-expt-arithmetic-reply
                          proof (h1-arithmetic-request-method result)
                          (h1-arithmetic-request-args result))))
             (list :continue (cdr reply)
                   (table-put replies (h1-arithmetic-request-key result) (car reply)))))
          ((eq recipe :signed-countdowns)
           (cons (car result) (h1-tactics-prover-with-library proof (cdr result))))
          (t (cons nil (h1-tactics-prover-with-library proof result))))))

(defun h1-book-expt-arithmetic-loop (n recipe exponent library next)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) (cons '(:failure "fuel" "h1-book-expt-arithmetic-loop")
                      (if (eq (car next) :continue) (cadr next) (cdr next))))
        ((eq (car next) :continue)
         (h1-book-expt-arithmetic-loop
          (1- n) recipe exponent library
          (h1-book-expt-arithmetic-next recipe (cadr next) exponent library (caddr next))))
        (t next)))

(defun h1-book-expt-arithmetic (recipe proof exponent)
  (h1-book-expt-arithmetic-loop
   1000000 recipe exponent (h1-tactics-prover-library proof) (list :continue proof nil)))

(defun h1-book-expt-signed-countdowns (proof exponent)
  (h1-book-expt-arithmetic :signed-countdowns proof exponent))

(defun h1-book-expt-bind-induction (normalizer induction)
  (if (not induction)
      normalizer
    (proof-with-checked-results
        ((literal (proof-step-first induction))
         (parts (proof-list-of-length literal 3)))
      (let ((before (cadr parts))
            (after (caddr parts)))
        (if (member-equal before (h1-tactics-subterms after))
            normalizer
          (let* ((context (h1-book-arithmetic-algebra-context normalizer))
                 (bindings (h1-tactics-context-bindings context)))
            (h1-book-arithmetic-algebra-with-context
             normalizer (h1-tactics-context-with-bindings
                         context (table-put bindings before induction)))))))))

(defun h1-book-expt-unfold-operands (proof operands powers count result steps)
  (declare (xargs :measure (acl2-count operands)))
  (cond ((failure-p result) result)
        ((endp operands) (cons (reverse steps) (cdr result)))
        ((zp count) '(:failure "candidate-rejected" ""))
        (t (let ((next (h1-book-expt-unfold-powers proof (car operands) powers (cdr result))))
             (h1-book-expt-unfold-operands proof (cdr operands) powers (1- count)
                                          next (cons (car next) steps))))))

(defun h1-book-expt-power-equality-by-base (zero-tests tests induction proof formula powers)
  (if (endp zero-tests)
      (proof-with-checked-results
          ((normalizer (h1-book-field-field-normalizer proof tests))
           (normalizer (h1-book-expt-bind-induction normalizer induction))
           (unfolded (h1-book-expt-unfold-operands proof (cdr formula) powers 3 (cons nil normalizer) nil))
           (operands (proof-list-of-length (car unfolded) 2))
           (left (proof-step-first (car operands)))
           (right (proof-step-first (cadr operands)))
           (normalizer (h1-book-arithmetic-algebra-with-work (cdr unfolded) 150))
           (middle (h1-book-expt-checked-pair
                    (h1-book-arithmetic-algebra-equality normalizer (caddr left) (caddr right))))
           (reverse-right (h1-propositions-proof-symmetric
                           (h1-tactics-prover-proof proof) (cadr operands))))
        (proof-proof-chain (h1-tactics-prover-proof proof) (car operands)
                           (list (car middle) reverse-right)))
    (let ((test (car zero-tests)))
      (proof-with-checked-results
          ((yes (h1-book-expt-power-equality-by-base
                 (cdr zero-tests) (append tests (list (list test t))) induction proof formula powers))
           (no (h1-book-expt-power-equality-by-base
                (cdr zero-tests) (append tests (list (list test nil))) induction proof formula powers)))
        (proof-proof-cases (h1-tactics-prover-proof proof) test yes no)))))

(defun h1-book-expt-power-equality-after-shift (plan holds proof formula powers zero-tests zip-test exponent)
  (let ((core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((parts (proof-list-of-length plan 2))
         (child (proof-subst formula (proof-bindings-table (car parts) nil)))
         (decrease (proof-step-first (cadr parts)))
         (hypothesis (proof-proof-assume core (proof-ite decrease child *proof-true*) t))
         (given (h1-propositions-proof-prove-if core hypothesis (cadr parts))))
      (h1-book-expt-power-equality-by-base
       zero-tests (list (list zip-test nil) (list (library-positive exponent) holds))
       given proof formula powers))))

(defun h1-book-expt-power-equality-counted (proof formula powers zero-tests exponent measure countdowns)
  (let ((core (h1-tactics-prover-proof proof))
        (zip-test (list *h1-arithmetic-zip* exponent)))
    (proof-with-checked-results
        ((zero-case (h1-book-expt-power-equality-by-base
                     nil (list (list zip-test t)) nil proof formula powers))
         (down (h1-book-expt-power-equality-after-shift
                (car countdowns) t proof formula powers zero-tests zip-test exponent))
         (up (h1-book-expt-power-equality-after-shift
              (cadr countdowns) nil proof formula powers zero-tests zip-test exponent))
         (shifted (proof-proof-cases core (library-positive exponent) down up))
         (step (proof-proof-cases core zip-test zero-case shifted))
         (ordinal (descent-measure-ordinal (h1-tactics-prover-library proof) measure)))
      (proof-proof-induct core ordinal step formula measure (strip-cars countdowns)))))

(defun h1-book-expt-power-equality-setup (formula)
  (if (not (proof-is-call formula *proof-equal*))
      '(:failure "unproved" "")
    (let ((powers (proof-unique (h1-book-expt-powers (h1-tactics-subterms formula)))))
      (proof-with-checked-results ((exponents (h1-book-expt-exponents powers)))
        (let ((exponents (proof-unique exponents)))
          (proof-with-checked-results
              ((nested (and (equal (len exponents) 1) (h1-book-expt-nested-powers powers))))
            (cond ((or (not (equal (len exponents) 1)) nested)
                   '(:failure "unproved" ""))
                  ((not (eq (h1-tactics-call-head (car exponents)) :none))
                   '(:failure "unproved" ""))
                  (t (proof-with-checked-results ((factors (h1-book-expt-power-factors powers)))
                       (let ((factors (proof-unique factors)))
                         (if (< 2 (len factors))
                             '(:failure "unproved" "")
                           (list powers (car exponents) (h1-book-expt-zero-tests factors)))))))))))))

(defun h1-book-expt-power-equality (proof formula)
  (let ((setup (h1-book-expt-power-equality-setup formula)))
    (if (failure-p setup)
        (cons setup proof)
      (let ((counted (h1-book-expt-signed-countdowns proof (cadr setup))))
        (if (failure-p (car counted))
            counted
          (cons (h1-book-expt-power-equality-counted
                 (cdr counted) formula (car setup) (caddr setup) (cadr setup)
                 (caar counted) (cadar counted))
                (cdr counted)))))))

(defun h1-book-expt-install-powers (proof)
  (proof-with-checked-results
      ((zero-products (h1-book-expt-checked-pair
                       (h1-book-expt-arithmetic :zero-product-rules proof nil)))
       (proof (cdr zero-products))
       (call (list *h1-arithmetic-expt* *library-x* *library-y*))
       (typed (h1-tactics-prover-solve proof (list *library-numberp* call)
                                      (list *h1-arithmetic-expt*) 160))
       (installed (h1-tactics-prover-helper proof "EXPT-NUMBER" typed nil t))
       (proof (cdr installed))
       (one-exponent (list *h1-arithmetic-expt* *library-x* *proof-one*))
       (at-one (h1-tactics-prover-solve
                proof (proof-eq one-exponent (list *h1-book-arithmetic-fix* *library-x*))
                (list (cons *h1-arithmetic-expt* 2) (cons *h1-arithmetic-zip* 2)) 160))
       (installed (h1-tactics-prover-helper proof "EXPT-AT-ONE" at-one nil t))
       (proof (cdr installed))
       (one-base (list *h1-arithmetic-expt* *proof-one* *library-x*))
       (one-to-power (h1-book-expt-checked-pair
                      (h1-book-expt-power-equality proof (proof-eq one-base *proof-one*))))
       (installed (h1-tactics-prover-helper (cdr one-to-power) "ONE-TO-POWER" (car one-to-power) nil t)))
    (cdr installed)))
