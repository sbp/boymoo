(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-books-definition-tactics*
  (list (cons *h1-book-modulo-mod* 'h1-book-modulo-install-remainder)
        (cons *h1-book-euclid-gcd* 'h1-book-euclid-install-gcd)
        (cons *h1-book-euclid-multiplier1* 'h1-book-euclid-install-bezout)
        (cons *h1-book-scan-before* 'h1-book-scan-install-before-bounds)
        (cons *h1-book-scan-after* 'h1-book-scan-install-after-bounds)
        (cons *h1-book-scan-diff-recursion* 'h1-book-scan-install-diff-bounds)
        (cons *h1-book-scan-diff* 'h1-book-scan-install-diff-wrapper)))

(defconst *h1-books-constraint-tactics*
  (list (cons *h1-book-rewrite-equal-eval*
              '(h1-book-rewrite-equal-install-eval-substitution
                h1-book-disjoin-install-disjunctions
                h1-book-trigger-install-triggers))))

(defconst *h1-books-base-tactics*
  '(h1-book-arithmetic-install-arithmetic h1-book-field-install-field
    h1-book-order-install-order h1-book-expt-install-powers
    h1-book-expt-sum-install-power-addition h1-book-expt-composition-install-power-composition
    h1-book-expt-order-install-power-order h1-book-expt-parity-install-power-parity
    h1-book-fraction-install-fractions h1-book-list-size-install-list-sizes
    h1-book-modulo-install-subtraction h1-book-resize-install-resize-bounds
    h1-book-substitution-install-syntax h1-book-substitution-install-parallel-lookup
    h1-books-install-reverse))

(defconst *h1-books-newlines* (coerce (list #\Return #\Newline) 'string))
(defconst *h1-books-tab* (coerce (list #\Tab) 'string))
(defconst *h1-books-skip-reason* "no proof")

(defun h1-books-definition-tactic-list (definitions)
  (declare (xargs :measure (len definitions)))
  (if (endp definitions)
      nil
    (proof-with-checked-results
        ((name (proof-term-at (car definitions) 0))
         (install (table-get *h1-books-definition-tactics* name nil))
         (rest (h1-books-definition-tactic-list (cdr definitions))))
      (if install (cons install rest) rest))))

(defun h1-books-declaration-tactics (kind fields)
  (cond ((equal kind "define")
         (h1-books-definition-tactic-list (cdr fields)))
        ((equal kind "constrain")
         (proof-with-checked-results
             ((functions (proof-term-at fields 0))
              (function (proof-term-at functions 0))
              (name (proof-term-at function 0)))
           (table-get *h1-books-constraint-tactics* name nil)))
        (t nil)))

(defun h1-books-book-prover-evaluators (proof)
  (h1-tactics-prover-evaluators proof))

(defun h1-books-book-prover-with-search-work (proof search-work)
  (h1-tactics-prover-with-search-work proof search-work))

(defun h1-books-book-prover-with-case-limit (proof case-limit)
  (h1-tactics-prover-with-case-limit proof case-limit))

(defun h1-books-extend-available (proof names)
  (h1-tactics-prover-with-available
   proof (proof-unique (append (h1-tactics-prover-available proof) names))))

(defun h1-books-book-prover-init ()
  (proof-with-checked-results ((proof (h1-tactics-prover-init)))
    (let* ((core (h1-tactics-prover-proof proof))
           (definitions (table-keys (proof-proof-definitions core)))
           (primitives (proof-proof-primitives core)))
      (h1-tactics-prover-with-case-limit
       (h1-tactics-prover-with-search-work
        (h1-books-extend-available proof (append definitions primitives)) 3000)
       18))))

(defund h1-books-book-prover-add-definition (proof name formals body)
  (h1-tactics-prover-add-definition proof name formals body))

; The library recipes use H1 propositional inferences.
(defund h1-books-library-constant (proof term)
  (h1-tactics-prover-constant
   (h1-tactics-make-prover (library-library-init proof) nil nil nil :none 18)
   term))

(mutual-recursion
 (defun h1-books-library-simplify-visit (n proof term evidence definitions)
   (declare (xargs :measure (nfix n)))
   (let ((head (car term)))
     (cond
      ((zp n) '(:failure "fuel" "h1-books-library-simplify-visit"))
      ((or (not (proof-compound term)) (equal head *proof-quote*)) nil)
      ((endp term) '(:failure "failure" ""))
      ((or (proof-compound head) (member-equal head definitions))
       (proof-with-checked-results
           ((expansion (proof-simplify-expansion proof term))
            (next (h1-books-library-simplify-visit (1- n) proof (cadr expansion)
                                                  evidence definitions)))
         (proof-proof-chain proof (car expansion) (list next))))
      ((equal head *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at term 1))
            (first (h1-books-library-simplify-visit (1- n) proof test evidence definitions))
            (redex (proof-simplify-if-redex term first))
            (branch (h1-arithmetic-simplify-branch proof redex evidence))
            (selected (h1-arithmetic-simplify-chain proof term first branch))
            (right (and selected (proof-rewritten-term selected))))
         (if (or (not selected) (equal right redex))
             selected
           (proof-with-checked-results
               ((next (h1-books-library-simplify-visit (1- n) proof right evidence definitions)))
             (proof-proof-chain proof selected (list next))))))
      (t (proof-with-checked-results
             ((result (h1-books-library-simplify-args (1- n) proof term (cdr term) 1 nil
                                                    evidence definitions))
              (current (if result (proof-rewritten-term result) term))
              (constant (h1-books-library-constant proof current)))
           (cond ((not constant) result)
                 (result (proof-proof-chain proof result (list constant)))
                 (t constant)))))))
 (defun h1-books-library-simplify-args (n proof term args index result evidence definitions)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h1-books-library-simplify-args"))
    ((endp args) result)
    (t (proof-with-checked-results
           ((equality (h1-books-library-simplify-visit (1- n) proof (car args) evidence definitions))
            (next (if equality
                      (proof-with-checked-results
                          ((previous (or result (h1-arithmetic-proof-reflexive proof term))))
                        (proof-proof-rewrite proof previous equality (list 1 2 index)))
                    result)))
         (h1-books-library-simplify-args (1- n) proof term (cdr args) (1+ index) next
                                         evidence definitions))))))

(defund h1-books-library-simplify (proof term evidence definitions)
  (h1-books-library-simplify-visit 1000000 proof term evidence definitions))

(defun h1-books-library-simplify-first (proof step evidence definitions)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (equality (h1-books-library-simplify proof literal evidence definitions)))
    (if equality
        (proof-with-checked-results ((rewritten (proof-proof-rewrite proof step equality '(1))))
          (proof-proof-tidy proof rewritten))
      step)))

(defun h1-books-library-prove-visit (n proof term evidence definitions)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h1-books-library-prove-visit"))
   ((equal term *proof-true*) (proof-prove-step proof term evidence definitions))
   (t
    (proof-with-checked-results ((premise (proof-find-evidence evidence (list term))))
      (if premise
          premise
        (proof-with-checked-results
            ((equality (h1-books-library-simplify proof term evidence definitions))
             (right (and equality (proof-rewritten-term equality))))
          (cond ((or (not equality) (equal right term)) '(:failure "failure" ""))
                ((equal right *proof-true*) (proof-proof-true-from-eq proof equality))
                (t (proof-with-checked-results
                       ((step (h1-books-library-prove-visit (1- n) proof right evidence definitions)))
                     (h1-propositions-proof-transport proof step equality))))))))))

(defund h1-books-library-prove (proof term evidence definitions)
  (h1-books-library-prove-visit 1000000 proof term evidence definitions))

(defun h1-books-library-ints (library terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
     ((step (h1-arithmetic-proof-assume (library-library-proof library)
                                (library-integer (car terms)) t))
      (rest (h1-books-library-ints library (cdr terms))))
     (cons step rest))))

(mutual-recursion
 (defun h1-books-library-type-of (library term evidence)
   (declare (xargs :measure (acl2-count term)))
   (let ((literal (library-integer term)))
     (proof-with-checked-results ((premise (library-type-evidence literal evidence)))
       (cond
        (premise premise)
        ((atom term) (library-missing-integer term))
        ((and (proof-is-call term *proof-quote*) (endp (cdr term)))
         '(:failure "failure" ""))
        ((and (proof-is-call term *proof-quote*) (integerp (cadr term)))
         (h1-books-library-prove (library-library-proof library) literal nil nil))
        ((or (proof-is-call term *proof-plus*) (proof-is-call term *proof-times*))
         (proof-with-checked-results ((steps (h1-books-library-type-arguments library (cdr term) evidence)))
           (library-library-cite library
                                 (if (equal (car term) *proof-plus*)
                                     "INTEGER-SUM" "INTEGER-PRODUCT")
                                 (cdr term) steps)))
        ((proof-is-call term *proof-minus*)
         (if (endp (cdr term))
             '(:failure "failure" "")
           (proof-with-checked-results ((step (h1-books-library-type-of library (cadr term) evidence)))
             (library-library-cite library "INTEGER-NEGATION" (cdr term) (list step)))))
        ((proof-is-call term *library-count*)
         (library-library-cite library "COUNT-INTEGER" (cdr term) nil))
        ((proof-is-call term *library-len*)
         (library-library-cite library "LEN-INTEGER" (cdr term) nil))
        (t (library-missing-integer term))))))

 (defun h1-books-library-type-arguments (library args evidence)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((step (h1-books-library-type-of library (car args) evidence))
       (rest (h1-books-library-type-arguments library (cdr args) evidence)))
      (cons step rest)))))

(mutual-recursion
 (defun h1-books-library-natural (library term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term *library-count*)
     (library-library-cite library "COUNT-NATURAL" (cdr term) nil))
    ((proof-is-call term *library-len*)
     (library-library-cite library "LEN-NATURAL" (cdr term) nil))
    ((and (consp term) (proof-is-call term *proof-plus*))
     (proof-with-checked-results ((steps (h1-books-library-natural-arguments library (cdr term))))
       (library-library-cite library "NATURAL-SUM" (cdr term) steps)))
    (t (h1-books-library-prove (library-library-proof library)
                          (list *library-natp* term) nil (list *library-natp* *proof-not*)))))

 (defun h1-books-library-natural-arguments (library args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((step (h1-books-library-natural library (car args)))
       (rest (h1-books-library-natural-arguments library (cdr args))))
      (cons step rest)))))

(defun h1-books-library-rational (library term evidence)
  (proof-with-checked-results
   ((axiom (library-library-axiom library "INTEGER-IMPLIES-RATIONAL" (list term)))
    (type-step (h1-books-library-type-of library term evidence)))
   (h1-arithmetic-proof-modus-ponens (library-library-proof library) axiom type-step)))

(defun h1-books-library-number (library term evidence)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((fact (proof-proof-fact proof "rationalp-acl2-numberp" (list (list *library-x* term))))
      (rational (h1-books-library-rational library term evidence)))
     (h1-arithmetic-proof-modus-ponens proof fact rational))))

(defun h1-books-library-push-minus (n library term evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "h1-books-library-push-minus")
    (let ((proof (library-library-proof library)))
      (cond
       ((proof-is-call term *proof-plus*)
        (proof-with-checked-results
         ((result (h1-arithmetic-proof-reflexive proof term))
          (left (proof-term-at term 1))
          (left-step (h1-books-library-push-minus (1- n) library left evidence))
          (result (if left-step
                      (proof-proof-rewrite proof result left-step '(1 2 1))
                    result))
          (right (proof-term-at term 2))
          (right-step (h1-books-library-push-minus (1- n) library right evidence))
          (result (if right-step
                      (proof-proof-rewrite proof result right-step '(1 2 2))
                    result))
          (first (proof-step-first result))
          (right (proof-term-at first 2)))
         (if (equal right term) nil result)))
       ((proof-is-call term *proof-minus*)
        (proof-with-checked-results ((argument (proof-term-at term 1)))
          (if (proof-is-call argument *proof-quote*)
              (h1-books-library-constant proof term)
            (let ((facts (proof-proof-facts proof)))
              (proof-with-checked-results
               ((result
                 (cond
                  ((and (proof-is-call argument *proof-minus*)
                        (assoc-equal (library-lemma-name "DOUBLE-NEGATION") facts))
                   (proof-with-checked-results
                    ((item (proof-term-at argument 1))
                     (type-step (h1-books-library-type-of library item evidence)))
                    (library-library-cite library "DOUBLE-NEGATION"
                                          (list item) (list type-step))))
                  ((and (proof-is-call argument *proof-plus*)
                        (assoc-equal (library-lemma-name "NEGATE-SUM") facts))
                   (proof-with-checked-results
                    ((steps (h1-books-library-type-arguments library (cdr argument) evidence)))
                    (library-library-cite library "NEGATE-SUM" (cdr argument) steps)))
                  (t nil))))
               (if (not result)
                   nil
                 (proof-with-checked-results
                  ((first (proof-step-first result))
                   (right (proof-term-at first 2))
                   (rest (h1-books-library-push-minus (1- n) library right evidence)))
                  (proof-proof-chain proof result (list rest)))))))))
       (t nil)))))

(defun h1-books-library-linear-combine-pair (library a b)
  (let ((proof (library-library-proof library)))
    (cond
     ((and (proof-is-call a *proof-quote*) (proof-is-call b *proof-quote*))
      (h1-books-library-constant proof (library-plus a b)))
     ((equal b (library-minus a))
      (library-library-axiom library "INVERSE-OF-+" (list a)))
     ((equal a (library-minus b))
      (proof-with-checked-results
       ((swap (library-library-axiom library "COMMUTATIVITY-OF-+" (list a b)))
        (inverse (library-library-axiom library "INVERSE-OF-+" (list b))))
       (proof-proof-chain proof swap (list inverse))))
     (t nil))))

(defun h1-books-library-linear-remove-zero (library step name term place evidence)
  (proof-with-checked-results
   ((type-step (h1-books-library-type-of library term evidence))
    (zero-step (library-library-cite library name (list term) (list type-step))))
   (proof-proof-rewrite (library-library-proof library) step zero-step place)))

(defun h1-books-library-linear-combine (n library step place evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "h1-books-library-linear-combine")
    (proof-with-checked-results
     ((first (proof-step-first step))
      (node (library-linear-form-get first (cdr place))))
     (if (not (proof-is-call node *proof-plus*))
         (proof-proof-tidy (library-library-proof library) step)
       (proof-with-checked-results ((pair (proof-list-of-length (cdr node) 2)))
         (let* ((a (car pair))
                (rest (cadr pair))
                (suffix (proof-is-call rest *proof-plus*))
                (proof (library-library-proof library)))
           (proof-with-checked-results ((b (if suffix (proof-term-at rest 1) rest)))
             (cond
              ((equal a *proof-zero*)
               (proof-with-checked-results ((step (h1-books-library-linear-remove-zero library step "ADD-ZERO-LEFT"
                                                                rest place evidence)))
                 (h1-books-library-linear-combine (1- n) library step place evidence)))
              ((and (equal b *proof-zero*) (not suffix))
               (proof-with-checked-results ((step (h1-books-library-linear-remove-zero library step "ADD-ZERO-RIGHT"
                                                                a place evidence)))
                 (h1-books-library-linear-combine (1- n) library step place evidence)))
              (t
               (proof-with-checked-results ((combine (h1-books-library-linear-combine-pair library a b)))
                 (if (not combine)
                     (h1-books-library-linear-combine (1- n) library step (append place '(2)) evidence)
                   (proof-with-checked-results
                    ((step (if suffix
                               (proof-with-checked-results
                                ((tail (proof-term-at rest 2))
                                 (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+"
                                                                    (list a b tail)))
                                 (symmetric (h1-propositions-proof-symmetric proof assoc-step)))
                                (proof-proof-rewrite proof step symmetric place))
                             step))
                     (step (proof-proof-rewrite proof step combine
                                                (if suffix (append place '(1)) place))))
                    (h1-books-library-linear-combine (1- n) library step '(1 2) evidence)))))))))))))

(defun h1-books-library-linear-form (library term evidence)
  (proof-with-checked-results
   ((step (h1-books-library-push-minus 1000000 library term evidence))
    (step (if step step (h1-arithmetic-proof-reflexive (library-library-proof library) term)))
    (step (library-linear-reassociate 1000000 library step '(1 2)))
    (step (library-linear-sort 1000000 library step '(1 2) nil)))
   (h1-books-library-linear-combine 1000000 library step '(1 2) evidence)))

(defun h1-books-library-linear-equal (library left right integers)
  (proof-with-checked-results
   ((a (h1-books-library-linear-form library left integers))
    (b (h1-books-library-linear-form library right integers))
    (a-first (proof-step-first a))
    (b-first (proof-step-first b))
    (a-normal (proof-term-at a-first 2))
    (b-normal (proof-term-at b-first 2)))
   (if (equal a-normal b-normal)
       (let ((proof (library-library-proof library)))
         (proof-with-checked-results ((symmetric (h1-propositions-proof-symmetric proof b)))
           (proof-proof-chain proof a (list symmetric))))
     '(:failure "failure" ""))))

(defun h1-books-library-comparison (library a b integers)
  (proof-with-checked-results
   ((a-type (h1-books-library-type-of library a integers))
    (b-type (h1-books-library-type-of library b integers)))
   (library-library-cite library "LESS-DIFFERENCE" (list a b) (list a-type b-type))))

(defun h1-books-library-less-from-difference (library a b positive-difference integers)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((compare (h1-books-library-comparison library a b integers))
      (first (proof-step-first positive-difference))
      (term (proof-term-at first 2))
      (delta (h1-books-library-linear-equal library (library-diff b a) term integers))
      (compare (proof-proof-rewrite proof compare delta '(1 2 2))))
     (h1-propositions-proof-transport proof positive-difference compare))))

(defun h1-books-library-weak-from-difference (library a b nonnegative-difference integers)
  (proof-with-checked-results
   ((compare (library-library-axiom library "<-ON-OTHERS" (list b a)))
    (first (proof-step-first nonnegative-difference))
    (bound (proof-term-at first 1))
    (term (proof-term-at bound 1))
    (delta (h1-books-library-linear-equal library (library-diff b a) term integers))
    (compare (proof-proof-rewrite (library-library-proof library) compare delta '(1 2 1))))
   (h1-propositions-library-transport-argument library nonnegative-difference compare 1)))

(defun h1-books-library-additive-identities-inverse-unique (a b sum-zero integers library)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list (library-minus a) a)))
      (inverse (library-library-axiom library "INVERSE-OF-+" (list a)))
      (cancel (proof-proof-chain proof commute (list inverse)))
      (b-type (h1-books-library-type-of library b integers))
      (step (library-library-cite library "ADD-ZERO-LEFT" (list b) (list b-type)))
      (cancel (h1-propositions-proof-symmetric proof cancel))
      (step (proof-proof-rewrite proof step cancel '(1 1 1)))
      (step (h1-propositions-proof-symmetric proof step))
      (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+" (list (library-minus a) a b)))
      (step (proof-proof-chain proof step (list assoc-step)))
      (step (proof-proof-rewrite proof step sum-zero '(1 2 2)))
      (negative-type (h1-books-library-type-of library (library-minus a) integers))
      (zero-right (library-library-cite library "ADD-ZERO-RIGHT" (list (library-minus a))
                                        (list negative-type))))
     (proof-proof-chain proof step (list zero-right)))))

(defun h1-books-library-additive-identities (library)
  (let ((x *library-x*)
        (y *library-y*)
        (z *library-z*)
        (zero *proof-zero*)
        (fix (proof-sym "FIX" "ACL2")))
    (proof-with-checked-results
     ((ints (h1-books-library-ints library (list x)))
      (left-zero (library-library-axiom library "UNICITY-OF-0" (list x)))
      (x-number (h1-books-library-number library x ints))
      (fixed (library-inherited h1-books-library-simplify library (list fix x) (list x-number) (list fix)))
      (left-zero (library-inherited proof-proof-chain library left-zero (list fixed)))
      (library (library-library-lemma library "ADD-ZERO-LEFT" (proof-eq (library-plus zero x) x)
                                      left-zero (list (proof-neg (library-integer x)))))
      (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list x zero)))
      (right-zero (library-inherited proof-proof-chain library commute (list left-zero)))
      (library (library-library-lemma library "ADD-ZERO-RIGHT" (proof-eq (library-plus x zero) x)
                                      right-zero (list (proof-neg (library-integer x)))))
      (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+" (list x y z)))
      (step (library-inherited h1-propositions-proof-symmetric library assoc-step))
      (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list x y)))
      (step (library-inherited proof-proof-rewrite library step commute '(1 2 1)))
      (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+" (list y x z)))
      (step (library-inherited proof-proof-chain library step (list assoc-step)))
      (library (library-library-lemma library "ADD-SWAP"
                                      (proof-eq (library-plus x (library-plus y z))
                                                (library-plus y (library-plus x z))) step nil))

      (inverse (library-library-axiom library "INVERSE-OF-+" (list x)))
      (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list (library-minus x) x)))
      (reverse (library-inherited proof-proof-chain library commute (list inverse)))
      (involution (h1-books-library-additive-identities-inverse-unique (library-minus x) x reverse ints library))
      (involution (library-inherited h1-propositions-proof-symmetric library involution))
      (library (library-library-lemma library "DOUBLE-NEGATION"
                                      (proof-eq (library-minus (library-minus x)) x)
                                      involution (list (proof-neg (library-integer x)))))
      (ints (h1-books-library-ints library (list x y))))
     (let ((a (library-plus x y))
           (b (library-plus (library-minus x) (library-minus y))))
       (proof-with-checked-results
        ((zero-sum (h1-books-library-linear-equal library (library-plus a b) zero ints))
         (distribute (h1-books-library-additive-identities-inverse-unique a b zero-sum ints library))
         (distribute (library-inherited h1-propositions-proof-symmetric library distribute)))
        (library-library-lemma library "NEGATE-SUM" (proof-eq (library-minus a) b) distribute
                               (library-guards (list (library-integer x) (library-integer y)))))))))

(defun h1-books-library-as-weak (library strict)
  (proof-with-checked-results
   ((literal (proof-step-first strict))
    (literal (proof-list-of-length literal 3)))
    (let ((a (cadr literal))
          (b (caddr literal)))
      (proof-with-checked-results
       ((a-type (h1-books-library-type-of library a nil))
        (b-type (h1-books-library-type-of library b nil)))
        (library-library-cite library "LESS-TO-WEAK" (list a b)
                              (list a-type b-type strict))))))

(defun h1-books-library-ordinal-comparison (library a b)
  (proof-with-checked-results
   ((a-type (h1-books-library-type-of library a nil))
    (b-type (h1-books-library-type-of library b nil)))
    (library-library-cite library "FINITE-ORDER" (list a b) (list a-type b-type))))

(defun h1-books-library-tenfold-increase (library ix px)
  (let* ((proof (library-library-proof library))
         (nine (proof-quote 9))
         (ten (proof-quote 10))
         (times-x (list *proof-times* nine *library-x*))
         (fix (proof-sym "FIX" "ACL2")))
    (proof-with-checked-results
     ((rational-nine (h1-books-library-rational library nine nil))
      (rational-x (h1-books-library-rational library *library-x* (list ix)))
      (positive-nine (h1-books-library-prove proof (library-positive nine) nil nil))
      (pos-product (library-library-cite library "POSITIVE-PRODUCT"
                                         (list nine *library-x*)
                                         (list rational-nine rational-x positive-nine px)))
      (result (h1-books-library-less-from-difference
               library *library-x* (library-plus *library-x* times-x) pos-product (list ix)))
      (expansion (library-library-axiom library "COMMUTATIVITY-OF-*" (list ten *library-x*)))
      (sum-ten (proof-proof-compute proof (library-plus *proof-one* nine) 10))
      (ten-sum (h1-propositions-proof-symmetric proof sum-ten))
      (expansion (proof-proof-rewrite proof expansion ten-sum '(1 2 2)))
      (distributed (library-library-axiom library "DISTRIBUTIVITY"
                                          (list *library-x* *proof-one* nine)))
      (expansion (proof-proof-chain proof expansion (list distributed)))
      (one-x (library-library-axiom library "UNICITY-OF-1" (list *library-x*)))
      (number-x (h1-books-library-number library *library-x* (list ix)))
      (fixed (h1-books-library-simplify proof (list fix *library-x*) (list number-x) (list fix)))
      (one-x (proof-proof-chain proof one-x (list fixed)))
      (x-one (library-library-axiom library "COMMUTATIVITY-OF-*" (list *library-x* *proof-one*)))
      (x-one (proof-proof-chain proof x-one (list one-x)))
      (expansion (proof-proof-rewrite proof expansion x-one '(1 2 1)))
      (x-nine (library-library-axiom library "COMMUTATIVITY-OF-*" (list *library-x* nine)))
      (expansion (proof-proof-rewrite proof expansion x-nine '(1 2 2)))
      (step (h1-propositions-library-transport-argument library result expansion 2)))
     (library-library-lemma
      library "TENFOLD-LARGER" (library-lt *library-x* (list *proof-times* ten *library-x*))
      step (library-guards (list (library-integer *library-x*) (library-positive *library-x*)))))))

(defun h1-books-library-ordered-arithmetic (library)
  (let* ((x *library-x*)
         (y *library-y*)
         (integer-x (library-integer x))
         (integer-y (library-integer y))
         (positive-x (library-positive x))
         (positive-y (library-positive y))
         (negative-x (library-lt x *proof-zero*))
         (negative-y (library-lt y *proof-zero*))
         (difference (library-diff y x))
         (compare-xy (library-lt x y))
         (proof (library-library-proof library)))
    (proof-with-checked-results
     ((ints (h1-books-library-ints library (list x y)))
      (a (library-library-axiom library "<-ON-OTHERS" (list x y)))
      (b (library-library-axiom library "<-ON-OTHERS" (list *proof-zero* difference)))
      (delta (h1-books-library-linear-equal
              library (library-diff *proof-zero* difference) (library-diff x y) ints))
      (b (proof-proof-rewrite proof b delta '(1 2 1)))
      (b (h1-propositions-proof-symmetric proof b))
      (step (proof-proof-chain proof a (list b)))
      (library (library-library-lemma library "LESS-DIFFERENCE"
                                      (proof-eq compare-xy (library-positive difference))
                                      step (library-guards (list integer-x integer-y))))
      (proof (library-library-proof library))

      (px (h1-arithmetic-proof-assume proof positive-x t))
      (py (h1-arithmetic-proof-assume proof positive-y t))
      (positive (library-library-axiom library "POSITIVE" (list x y)))
      (parts (h1-arithmetic-proof-conjunct proof positive))
      (both-positive (proof-ite positive-x positive-y *proof-false*))
      (premise (h1-books-library-prove proof both-positive (list px py) nil))
      (step (h1-arithmetic-proof-modus-ponens proof (car parts) premise))
      (library (library-library-lemma library "POSITIVE-SUM"
                                      (library-positive (library-plus x y)) step
                                      (library-guards (list positive-x positive-y))))
      (proof (library-library-proof library))
      (r-x (list *library-rationalp* x))
      (r-y (list *library-rationalp* y))
      (rx (h1-arithmetic-proof-assume proof r-x t))
      (ry (h1-arithmetic-proof-assume proof r-y t))
      (both-rational-positive (proof-ite r-x (proof-ite r-y both-positive *proof-false*)
                                         *proof-false*))
      (premise (h1-books-library-prove proof both-rational-positive (list rx ry px py) nil))
      (step (h1-arithmetic-proof-modus-ponens proof (cadr parts) premise))
      (library (library-library-lemma library "POSITIVE-PRODUCT"
                                      (library-positive (list *proof-times* x y)) step
                                      (library-guards (list r-x r-y positive-x positive-y))))
      (proof (library-library-proof library))

      (ix (car ints))
      (iy (cadr ints))
      (trichotomy (library-library-axiom library "TRICHOTOMY" (list x)))
      (parts (h1-arithmetic-proof-conjunct proof trichotomy))
      (tri (car parts))
      (exclusive (cadr parts))
      (opposite (h1-books-library-comparison library x *proof-zero* (list ix)))
      (delta (h1-books-library-linear-equal library (library-diff *proof-zero* x)
                                           (library-minus x) (list ix)))
      (opposite (proof-proof-rewrite proof opposite delta '(1 2 2)))
      (exclusive-first (proof-step-first exclusive))
      (test (proof-term-at exclusive-first 1))
      (test-equality (h1-books-library-simplify proof test
                                           (list px) (list *proof-not*)))
      (exclusive (proof-proof-rewrite proof exclusive test-equality '(1 1)))
      (exclusive (h1-books-library-simplify-first proof exclusive nil nil))
      (step (h1-propositions-library-transport-argument library exclusive opposite 1))
      (library (library-library-lemma library "POSITIVE-NONNEGATIVE"
                                      (library-nonnegative x) step
                                      (library-guards (list integer-x positive-x))))
      (proof (library-library-proof library))

      (goal (library-positive (library-plus y x)))
      (good (library-library-cite library "POSITIVE-SUM" (list y x) (list py px)))
      (x-zero (proof-eq x *proof-zero*))
      (y-zero (library-library-cite library "ADD-ZERO-RIGHT" (list y) (list iy)))
      (zero-case (h1-propositions-library-transport-argument library py y-zero 2))
      (x-is-zero (h1-arithmetic-proof-assume proof x-zero t))
      (zero-x (h1-propositions-proof-symmetric proof x-is-zero))
      (zero-case (proof-proof-rewrite proof zero-case zero-x '(1 2 2)))
      (zero-case (proof-proof-tidy proof zero-case))
      (number-x (h1-books-library-number library x (list ix)))
      (disjunction (h1-arithmetic-proof-modus-ponens proof tri number-x))
      (x-not-positive (h1-arithmetic-proof-assume proof positive-x nil))
      (x-not-zero (h1-arithmetic-proof-assume proof x-zero nil))
      (negative-case (h1-books-library-simplify-first proof disjunction
                                                  (list x-not-positive x-not-zero) nil))
      (negative-case (h1-propositions-proof-transport proof negative-case opposite))
      (x-bound (h1-arithmetic-proof-assume proof negative-x nil))
      (contradiction (proof-proof-cut proof negative-case x-bound))
      (impossible (proof-proof-subsume proof contradiction
                                       (cons goal (proof-step-clause contradiction))))
      (branch (proof-proof-cases proof x-zero zero-case impossible))
      (step (proof-proof-cases proof positive-x good branch))
      (library (library-library-lemma library "POSITIVE-PLUS-NONNEGATIVE" goal step
                                      (list (proof-neg integer-x) (proof-neg integer-y)
                                            (proof-neg positive-y) negative-x)))
      (proof (library-library-proof library))

      (sum (library-plus y x))
      (goal (library-nonnegative sum))
      (y-bound (h1-arithmetic-proof-assume proof negative-y nil))
      (sum-type (h1-books-library-type-of library sum ints))
      (pos-sum (library-library-cite library "POSITIVE-PLUS-NONNEGATIVE"
                                      (list y x) (list iy ix px y-bound)))
      (commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list x y)))
      (pos-sum (proof-proof-rewrite proof pos-sum commute '(1 2)))
      (good (library-library-cite library "POSITIVE-NONNEGATIVE"
                                   (list sum) (list sum-type pos-sum)))
      (y-zero (library-library-cite library "ADD-ZERO-RIGHT" (list y) (list iy)))
      (zero-y (h1-propositions-proof-symmetric proof y-zero))
      (zero-case (proof-proof-rewrite proof y-bound zero-y '(1 1 1)))
      (zero-case (proof-proof-tidy proof zero-case))
      (x-is-zero (h1-arithmetic-proof-assume proof x-zero t))
      (zero-x (h1-propositions-proof-symmetric proof x-is-zero))
      (zero-case (proof-proof-rewrite proof zero-case zero-x '(1 1 1 2)))
      (zero-case (proof-proof-tidy proof zero-case))
      (impossible (proof-proof-subsume proof contradiction
                                       (cons goal (proof-step-clause contradiction))))
      (branch (proof-proof-cases proof x-zero zero-case impossible))
      (step (proof-proof-cases proof positive-x good branch))
      (library (library-library-lemma library "NONNEGATIVE-SUM" goal step
                                      (list (proof-neg integer-x) (proof-neg integer-y)
                                            negative-x negative-y)))
      (proof (library-library-proof library))

      (nx (h1-arithmetic-proof-assume proof (list *library-natp* x) t))
      (ny (h1-arithmetic-proof-assume proof (list *library-natp* y) t))
      (ix-nat (library-library-cite library "NATURAL-INTEGER" (list x) (list nx)))
      (iy-nat (library-library-cite library "NATURAL-INTEGER" (list y) (list ny)))
      (x-nat-bound (library-library-cite library "NATURAL-NONNEGATIVE" (list x) (list nx)))
      (y-nat-bound (library-library-cite library "NATURAL-NONNEGATIVE" (list y) (list ny)))
      (sum-nat-bound (library-library-cite library "NONNEGATIVE-SUM" (list y x)
                                           (list iy-nat ix-nat y-nat-bound x-nat-bound)))
      (sum (library-plus x y))
      (sum-type (h1-books-library-type-of library sum (list ix-nat iy-nat)))
      (sum-nat (library-library-cite library "NATURAL-FROM-BOUNDS" (list sum)
                                     (list sum-type sum-nat-bound)))
      (nat-x (proof-step-first nx))
      (nat-y (proof-step-first ny))
      (library (library-library-lemma library "NATURAL-SUM" (list *library-natp* sum)
                                      sum-nat (library-guards (list nat-x nat-y))))
      (proof (library-library-proof library))

      (pos-one (h1-books-library-prove proof (library-positive *proof-one*) nil nil))
      (one-type (h1-books-library-type-of library *proof-one* nil))
      (nonnegative-x (h1-arithmetic-proof-assume proof negative-x nil))
      (step (library-library-cite library "POSITIVE-PLUS-NONNEGATIVE" (list x *proof-one*)
                                   (list ix one-type pos-one nonnegative-x)))
      (one-plus-x (library-plus *proof-one* x))
      (library (library-library-lemma library "POSITIVE-ONE-PLUS" (library-positive one-plus-x)
                                      step (list (proof-neg integer-x) negative-x)))
      (step (h1-books-library-less-from-difference library x one-plus-x pos-one (list ix)))
      (library (library-library-lemma library "SUCCESSOR-LARGER" (library-lt x one-plus-x)
                                      step (list (proof-neg integer-x))))
      (proof (library-library-proof library))

      (nonless (h1-arithmetic-proof-assume proof compare-xy nil))
      (delta (library-diff x y))
      (offset (library-library-axiom library "<-ON-OTHERS" (list x y)))
      (nonneg-delta (proof-proof-rewrite proof nonless offset '(1 1)))
      (delta-type (h1-books-library-type-of library delta ints))
      (bound (library-library-cite library "POSITIVE-ONE-PLUS" (list delta)
                                    (list delta-type nonneg-delta)))
      (step (h1-books-library-less-from-difference library y one-plus-x bound ints))
      (library (library-library-lemma
                library "LESS-THAN-NEXT" (library-lt y one-plus-x) step
                (append (library-guards (list integer-x integer-y)) (list compare-xy)))))
     (h1-books-library-tenfold-increase library ix px))))

(defun h1-books-library-order-lemmas-delta-bound (a b strict library integers)
  (let ((proof (library-library-proof library)))
    (if strict
        (let ((less (library-lt a b)))
          (proof-with-checked-results
           ((step (h1-arithmetic-proof-assume proof less t))
            (comparison (h1-books-library-comparison library a b integers))
            (bound (proof-proof-rewrite proof step comparison '(1))))
            (list bound (proof-neg less))))
      (let ((less (library-lt b a)))
        (proof-with-checked-results
         ((step (h1-arithmetic-proof-assume proof less nil))
          (comparison (library-library-axiom library "<-ON-OTHERS" (list b a)))
          (bound (proof-proof-rewrite proof step comparison '(1 1))))
          (list bound less))))))

(defun h1-books-library-order-lemmas-transitivity (library name left-strict right-strict integers)
  (let ((x *library-x*)
        (y *library-y*)
        (z *library-z*))
    (proof-with-checked-results
     ((left (h1-books-library-order-lemmas-delta-bound x y left-strict library integers))
      (right (h1-books-library-order-lemmas-delta-bound y z right-strict library integers))
      (a (library-diff y x))
      (b (library-diff z y))
      (delta
       (if (and left-strict right-strict)
           (library-library-cite library "POSITIVE-SUM" (list a b)
                                 (list (car left) (car right)))
         (let ((known (car (if right-strict left right)))
               (positive-delta (car (if right-strict right left)))
               (low (if right-strict a b))
               (high (if right-strict b a)))
           (proof-with-checked-results
            ((low-type (h1-books-library-type-of library low integers))
             (high-type (h1-books-library-type-of library high integers)))
             (library-library-cite library "POSITIVE-PLUS-NONNEGATIVE" (list low high)
                                   (list low-type high-type positive-delta known))))))
      (step (h1-books-library-less-from-difference library x z delta integers)))
     (library-library-lemma
      library name (library-lt x z) step
      (append (library-guards (list (library-integer x) (library-integer y) (library-integer z)))
              (list (cadr left) (cadr right)))))))

(defun h1-books-library-order-lemmas (library)
  (let* ((proof (library-library-proof library))
         (x *library-x*)
         (y *library-y*)
         (z *library-z*)
         (less (library-lt x y))
         (integer-x (library-integer x))
         (integer-y (library-integer y))
         (integer-z (library-integer z))
         (difference (library-diff y x)))
    (proof-with-checked-results
     ((integers (h1-books-library-ints library (list x y z)))
      (xy (h1-arithmetic-proof-assume proof less t))
      (comparison (h1-books-library-comparison library x y integers))
      (delta (proof-proof-rewrite proof xy comparison '(1)))
      (difference-type (h1-books-library-type-of library difference integers))
      (bound (library-library-cite library "POSITIVE-NONNEGATIVE" (list difference)
                                   (list difference-type delta)))
      (step (h1-books-library-weak-from-difference library x y bound integers))
      (library (library-library-lemma library "LESS-TO-WEAK" (library-le x y) step
                                      (library-guards (list integer-x integer-y less))))

      (zero (library-library-axiom library "ZERO" nil))
      (step (h1-books-library-weak-from-difference library x x zero integers))
      (library (library-library-lemma library "WEAK-REFLEXIVE" (library-le x x) step
                                      (list (proof-neg integer-x))))
      (x-plus-z (library-plus x z))
      (y-plus-z (library-plus y z))
      (step (h1-books-library-less-from-difference library x-plus-z y-plus-z delta integers))
      (library (library-library-lemma library "LESS-SHIFT" (library-lt x-plus-z y-plus-z) step
                                      (library-guards (list integer-x integer-y integer-z less))))
      (library (h1-books-library-order-lemmas-transitivity library "LESS-TRANSITIVE" t t integers))
      (library (h1-books-library-order-lemmas-transitivity library "LESS-THEN-WEAK" t nil integers)))
     (h1-books-library-order-lemmas-transitivity library "WEAK-THEN-LESS" nil t integers))))

(defun h1-books-library-length-lemmas (library)
  (let* ((proof (library-library-proof library))
         (x *library-x*)
         (cdr-x (list *library-cdr* x))
         (length (list *library-len* x))
         (tail (list *library-len* cdr-x))
         (cons-test (list *proof-consp* x))
         (main (list *library-natp* length))
         (measure (list *library-count* x)))
    (proof-with-checked-results
     ((descent (library-library-builtin library 3 x))
      (descent-test (proof-step-first descent))
      (hypothesis (proof-ite descent-test (list *library-natp* tail) *proof-true*))
      (assumed (h1-arithmetic-proof-assume proof hypothesis t))
      (child-nat (h1-propositions-proof-prove-if proof assumed descent))
      (opened (proof-proof-unfold proof length))
      (opened-first (proof-step-first opened))
      (conditional (proof-term-at opened-first 2))
      (yes-equation (h1-arithmetic-proof-if-true proof conditional))
      (length-succ (proof-proof-chain proof opened (list yes-equation)))
      (no-equation (h1-arithmetic-proof-if-false proof conditional))
      (length-zero (proof-proof-chain proof opened (list no-equation)))
      (nat-one (h1-books-library-natural library *proof-one*))
      (successor (library-library-cite library "NATURAL-SUM" (list *proof-one* tail)
                                        (list nat-one child-nat)))
      (yes (h1-propositions-library-transport-argument library successor length-succ 1))
      (nat-zero (h1-books-library-natural library *proof-zero*))
      (no (h1-propositions-library-transport-argument library nat-zero length-zero 1))
      (ordinal (library-library-builtin library 1 x))
      (branches (proof-proof-cases proof cons-test yes no))
      (step (proof-proof-induct proof ordinal branches main measure
                                (list (list (list x cdr-x)))))
      (library (library-library-lemma library "LEN-NATURAL" main step nil))
      (nat-length (h1-books-library-natural library length))
      (step (library-library-cite library "NATURAL-INTEGER" (list length) (list nat-length)))
      (library (library-library-lemma library "LEN-INTEGER" (library-integer length) step nil))

      (tail-type (h1-books-library-type-of library tail nil))
      (less (library-library-cite library "SUCCESSOR-LARGER" (list tail) (list tail-type)))
      (less (h1-propositions-library-transport-argument library less length-succ 2)))
     (library-library-lemma library "LEN-CDR-LESS" (library-lt tail length) less
                           (list (proof-neg cons-test))))))

(defun h1-books-library-count-lemmas-numeric (leaf tests library integer-abs length)
  (declare (ignore tests))
  (cond
   ((proof-is-call leaf *proof-plus*)
    (library-library-cite library "SUM-NUMBER" (cdr leaf) nil))
   ((proof-is-call leaf *proof-minus*)
    (library-library-cite library "NEGATION-NUMBER" (cdr leaf) nil))
   ((or (proof-is-call leaf integer-abs) (proof-is-call leaf length))
    (library-library-cite library (if (equal (car leaf) integer-abs)
                                      "ABS-NUMBER" "LENGTH-NUMBER")
                          (cdr leaf) nil))
   (t
    (proof-with-checked-results
        ((evidence
          (if (equal leaf *library-x*)
              (proof-with-checked-results
                  ((integer-x (h1-arithmetic-proof-assume
                               (library-library-proof library) (library-integer *library-x*) t)))
                (list integer-x))
            nil)))
      (h1-books-library-number library leaf evidence)))))

(defun h1-books-library-count-visit (n library value template integer-abs length)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof library)))
    (cond
     ((zp n) '(:failure "fuel" "h1-books-library-count-visit"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((parts (proof-list-of-length (cdr value) 3))
           (yes (h1-books-library-count-visit (1- n) library (cadr parts)
                                               template integer-abs length))
           (no (h1-books-library-count-visit (1- n) library (caddr parts)
                                              template integer-abs length))
           (if-true (h1-arithmetic-proof-if-true proof value))
           (symmetric (h1-propositions-proof-symmetric proof if-true))
           (yes (proof-proof-rewrite-result proof yes symmetric template *proof-result*))
           (if-false (h1-arithmetic-proof-if-false proof value))
           (symmetric (h1-propositions-proof-symmetric proof if-false))
           (no (proof-proof-rewrite-result proof no symmetric template *proof-result*)))
        (proof-proof-cases proof (car parts) yes no)))
     ((and (proof-compound value) (endp value))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equation (proof-proof-beta proof value))
           (body (proof-rewritten-term equation))
           (step (h1-books-library-count-visit (1- n) library body template integer-abs length))
           (symmetric (h1-propositions-proof-symmetric proof equation)))
        (proof-proof-rewrite-result proof step symmetric template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (h1-books-library-count-lemmas-numeric value nil library integer-abs length))
           (first (proof-step-first step))
           (goal (proof-subst template (list (cons *proof-result* value)))))
        (if (equal first goal) step '(:failure "failure" "")))))))

(defun h1-books-library-count-lemmas-numeric-lemma (library function name integer-abs length)
  (let* ((proof (library-library-proof library))
         (call (list function *library-x*))
         (template (list *library-numberp* *proof-result*)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof call))
      (opened-first (proof-step-first opened))
      (body (proof-term-at opened-first 2))
      (step (h1-books-library-count-visit 1000000 library body template integer-abs length))
      (closed (h1-propositions-proof-symmetric proof opened))
      (step (proof-proof-rewrite-result proof step closed template *proof-result*)))
     (library-library-lemma library name (list *library-numberp* call) step nil))))

(defun h1-books-library-count-lemmas (library)
  (let* ((proof (library-library-proof library))
         (x *library-x*)
         (y *library-y*)
         (integer-abs (proof-sym "INTEGER-ABS" "ACL2"))
         (length (proof-cl "LENGTH"))
         (size (list *library-count* x)))
    (proof-with-checked-results
     ((closure (library-library-axiom library "CLOSURE" (list x y)))
      (parts (h1-arithmetic-proof-conjunct proof closure))
      (add (car parts))
      (parts (h1-arithmetic-proof-conjunct proof (cadr parts)))
      (parts (h1-arithmetic-proof-conjunct proof (cadr parts)))
      (minus-number (car parts))
      (library (library-library-lemma library "SUM-NUMBER"
                                      (list *library-numberp* (library-plus x y)) add nil))
      (library (library-library-lemma library "NEGATION-NUMBER"
                                      (list *library-numberp* (library-minus x)) minus-number nil))
      (library (h1-books-library-count-lemmas-numeric-lemma
                library integer-abs "ABS-NUMBER" integer-abs length))
      (library (h1-books-library-count-lemmas-numeric-lemma
                library length "LENGTH-NUMBER" integer-abs length))
      (library (h1-books-library-count-lemmas-numeric-lemma
                library *library-count* "COUNT-NUMBER" integer-abs length))
      (proof (library-library-proof library))
      (count-number (library-library-cite library "COUNT-NUMBER" (list x) nil))
      (is-finite (library-library-cite library "NUMBER-FINITE" (list size) (list count-number)))
      (ordinal (library-library-builtin library 1 x))
      (step (h1-books-library-simplify-first proof ordinal (list is-finite) (list *proof-ordinalp*)))
      (library (library-library-lemma library "COUNT-NATURAL" (list *library-natp* size) step nil))
      (natural-size (h1-books-library-natural library size))
      (step (library-library-cite library "NATURAL-INTEGER" (list size) (list natural-size))))
     (library-library-lemma library "COUNT-INTEGER" (library-integer size) step nil))))

(defun h1-books-library-weak-selectors-lemma (library head name number)
  (let* ((proof (library-library-proof library))
         (x *library-x*)
         (parent (list *library-count* x))
         (child (list *library-count* (list head x)))
         (cons-test (list *proof-consp* x)))
    (proof-with-checked-results
     ((descent (library-library-builtin library number x))
      (comparison (h1-books-library-ordinal-comparison library child parent))
      (strict (proof-proof-rewrite proof descent comparison '(1)))
      (yes (h1-books-library-as-weak library strict))
      (natural-parent (h1-books-library-natural library parent))
      (zero (library-library-cite library "NATURAL-NONNEGATIVE" (list parent)
                                  (list natural-parent)))
      (completion (library-library-axiom
                   library (concatenate 'string "COMPLETION-OF-" (caddr head)) (list x)))
      (completion-first (proof-step-first completion))
      (conditional (proof-term-at completion-first 2))
      (false-equation (h1-arithmetic-proof-if-false proof conditional))
      (completion (proof-proof-chain proof completion (list false-equation)))
      (child-zero (h1-arithmetic-proof-reflexive proof child))
      (child-zero (proof-proof-rewrite proof child-zero completion '(1 2 1)))
      (nil-size (h1-books-library-simplify proof (list *library-count* *proof-false*)
                                     nil (list *library-count*)))
      (child-zero (proof-proof-chain proof child-zero (list nil-size)))
      (zero-child (h1-propositions-proof-symmetric proof child-zero))
      (no (proof-proof-rewrite proof zero zero-child '(1 1 2)))
      (no (proof-proof-tidy proof no))
      (step (proof-proof-cases proof cons-test yes no)))
     (library-library-lemma library name (library-le child parent) step nil))))

(defun h1-books-library-weak-selectors (library)
  (proof-with-checked-results
   ((library (h1-books-library-weak-selectors-lemma library *library-car* "COUNT-CAR-WEAK" 2)))
    (h1-books-library-weak-selectors-lemma library *library-cdr* "COUNT-CDR-WEAK" 3)))

(defun h1-books-library-integer-measures (library)
  (let* ((proof (library-library-proof library))
         (x *library-x*)
         (y *library-y*)
         (z *library-z*)
         (positive-y (library-positive y))
         (x-less-y (library-lt x y))
         (mx (list *library-nfix* x))
         (my (list *library-nfix* y))
         (nat-x (list *library-natp* x)))
    (proof-with-checked-results
     ((integers (h1-books-library-ints library (list x y)))
      (ix (car integers))
      (iy (cadr integers))
      (pos-y (h1-arithmetic-proof-assume proof positive-y t))
      (xy (h1-arithmetic-proof-assume proof x-less-y t))
      (nonneg-y (library-library-cite library "POSITIVE-NONNEGATIVE" (list y) (list iy pos-y)))
      (nat-y (library-library-cite library "NATURAL-FROM-BOUNDS" (list y) (list iy nonneg-y)))
      (y-exact (h1-books-library-simplify proof my (list nat-y) (list *library-nfix*)))
      (x-is-natural (h1-arithmetic-proof-assume proof nat-x t))
      (x-exact (h1-books-library-simplify proof mx (list x-is-natural) (list *library-nfix*)))
      (x-not-natural (h1-arithmetic-proof-assume proof nat-x nil))
      (x-zero (h1-books-library-simplify proof mx (list x-not-natural) (list *library-nfix*)))
      (has-x (h1-propositions-library-transport-argument library xy x-exact 1))
      (has-x (h1-propositions-library-transport-argument library has-x y-exact 2))
      (lacks-x (h1-propositions-library-transport-argument library pos-y x-zero 1))
      (lacks-x (h1-propositions-library-transport-argument library lacks-x y-exact 2))
      (branch (proof-proof-cases proof nat-x has-x lacks-x))
      (fixed-x (library-library-cite library "NFIX-INTEGER" (list x) nil))
      (fixed-y (library-library-cite library "NFIX-INTEGER" (list y) nil))
      (ordinal-comparison (library-library-cite library "FINITE-ORDER" (list mx my)
                                                (list fixed-x fixed-y)))
      (step (h1-propositions-proof-transport proof branch ordinal-comparison))
      (library (library-library-lemma
                library "NFIX-DECREASE" (list *proof-ordinal-less* mx my) step
                (library-guards (list (library-integer x) (library-integer y)
                                      positive-y x-less-y))))
      (proof (library-library-proof library))

      (ints (h1-books-library-ints library (list x y z)))
      (y-less-x (library-lt y x))
      (y-less-z (library-lt y z))
      (inside (h1-arithmetic-proof-assume proof y-less-x t))
      (advance (h1-arithmetic-proof-assume proof y-less-z t))
      (before (library-diff x y))
      (after (library-diff x z))
      (comparison (h1-books-library-comparison library y x ints))
      (pos-before (proof-proof-rewrite proof inside comparison '(1)))
      (pos-before (proof-proof-tidy proof pos-before))
      (comparison (h1-books-library-comparison library y z ints))
      (length-lost (proof-proof-rewrite proof advance comparison '(1)))
      (length-lost (proof-proof-tidy proof length-lost))
      (smaller (h1-books-library-less-from-difference library after before length-lost ints))
      (after-type (h1-books-library-type-of library after ints))
      (before-type (h1-books-library-type-of library before ints))
      (step (library-library-cite library "NFIX-DECREASE" (list after before)
                                  (list after-type before-type pos-before smaller)))
      (after-gap (list *library-gap* x z))
      (before-gap (list *library-gap* x y))
      (unfolded (proof-proof-unfold proof after-gap))
      (step (h1-propositions-library-transport-argument library step unfolded 1))
      (unfolded (proof-proof-unfold proof before-gap))
      (step (h1-propositions-library-transport-argument library step unfolded 2)))
     (library-library-lemma
      library "GAP-DECREASE" (list *proof-ordinal-less* after-gap before-gap) step
      (library-guards (list (library-integer x) (library-integer y) (library-integer z)
                            y-less-x y-less-z))))))

(defun h1-books-library-build-after-count (library)
  (proof-with-checked-results ((library (h1-books-library-weak-selectors library)))
    (h1-books-library-integer-measures library)))

(defun h1-books-book-prover-build (proof)
  (proof-with-checked-results
      ((library (h1-propositions-propositional-proof-logic-and-types
                 (h1-tactics-prover-library proof)))
       (library (h1-books-library-additive-identities library))
       (library (h1-books-library-ordered-arithmetic library))
       (library (h1-books-library-order-lemmas library))
       (library (h1-books-library-length-lemmas library))
       (library (h1-books-library-count-lemmas library))
       (library (h1-books-library-build-after-count library)))
    (h1-books-extend-available
     (h1-tactics-prover-with-library proof library)
     (table-keys (proof-proof-definitions (library-library-proof library))))))

(defun h1-books-book-prover-index-fact (proof name formula)
  (proof-with-checked-results ((key (h1-tactics-fact-key formula)))
    (if (eq (car key) :none)
        proof
      (let* ((schemas (h1-tactics-prover-schemas proof))
             (prior (table-get schemas key nil))
             (record (list name formula (h1-tactics-variables formula))))
        (h1-tactics-prover-with-schemas
         proof (table-put schemas key (append prior (list record))))))))

(defun h1-books-book-prover-prior-fact (proof term)
  (h1-tactics-prover-prior-fact proof term))

(defun h1-books-book-prover-fork (proof)
  proof)

(defun h1-books-install-reverse (proof)
  (let* ((reverse-symbol (proof-cl "REVAPPEND"))
         (formula (proof-eq (list reverse-symbol (list *proof-cons* *library-x* *library-y*) *library-z*)
                            (list reverse-symbol *library-y* (list *proof-cons* *library-x* *library-z*)))))
    (proof-with-checked-results
        ((equation (h1-recipes-definition-equation proof formula nil))
         (helper (h1-tactics-prover-helper proof "REVAPPEND-CONS" equation nil t)))
      (cdr helper))))

(defund h1-books-install (proof install)
  (case install
    (h1-book-arithmetic-install-arithmetic (h1-book-arithmetic-install-arithmetic proof))
    (h1-book-field-install-field (h1-book-field-install-field proof))
    (h1-book-order-install-order (h1-book-order-install-order proof))
    (h1-book-expt-install-powers (h1-book-expt-install-powers proof))
    (h1-book-expt-sum-install-power-addition (h1-book-expt-sum-install-power-addition proof))
    (h1-book-expt-composition-install-power-composition
     (h1-book-expt-composition-install-power-composition proof))
    (h1-book-expt-order-install-power-order (h1-book-expt-order-install-power-order proof))
    (h1-book-expt-parity-install-power-parity (h1-book-expt-parity-install-power-parity proof))
    (h1-book-fraction-install-fractions (h1-book-fraction-install-fractions proof))
    (h1-book-list-size-install-list-sizes (h1-book-list-size-install-list-sizes proof))
    (h1-book-modulo-install-subtraction (h1-book-modulo-install-subtraction proof))
    (h1-book-resize-install-resize-bounds (h1-book-resize-install-resize-bounds proof))
    (h1-book-substitution-install-syntax (h1-book-substitution-install-syntax proof))
    (h1-book-substitution-install-parallel-lookup (h1-book-substitution-install-parallel-lookup proof))
    (h1-books-install-reverse (h1-books-install-reverse proof))
    (h1-book-modulo-install-remainder (h1-book-modulo-install-remainder proof))
    (h1-book-euclid-install-gcd (h1-book-euclid-install-gcd proof))
    (h1-book-euclid-install-bezout (h1-book-euclid-install-bezout proof))
    (h1-book-scan-install-before-bounds (h1-book-scan-install-before-bounds proof))
    (h1-book-scan-install-after-bounds (h1-book-scan-install-after-bounds proof))
    (h1-book-scan-install-diff-bounds (h1-book-scan-install-diff-bounds proof))
    (h1-book-scan-install-diff-wrapper (h1-book-scan-install-diff-wrapper proof))
    (h1-book-rewrite-equal-install-eval-substitution (h1-book-rewrite-equal-install-eval-substitution proof))
    (h1-book-disjoin-install-disjunctions (h1-book-disjoin-install-disjunctions proof))
    (h1-book-trigger-install-triggers (h1-book-trigger-install-triggers proof))
    (otherwise '(:failure "failure" ""))))

(defun h1-books-add-theorem (proof name formula)
  (let* ((library (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (facts (table-put (proof-proof-facts core) name (list formula)))
         (theorems (h1-tactics-prover-theorems proof))
         (library (library-library-with-proof library (proof-proof-with-facts core facts)))
         (proof (h1-tactics-prover-with-library proof library)))
    (if (assoc-equal formula theorems)
        proof
      (h1-tactics-prover-with-theorems proof (table-put theorems formula name)))))

(defun h1-books-register-theorem (proof name formula)
  (let ((proof (h1-books-add-theorem proof name formula)))
    (proof-with-checked-results ((local-name (proof-term-at name 2)))
      (if (or (<= 0 (text-find local-name "-EXEC-IS-"))
              (member-equal local-name
                            '("EQLABLEP-RECOG" "BOOLEAN-LISTP-CONS" "ALISTP-FORWARD-TO-TRUE-LISTP"
                              "TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION"
                              "PSEUDO-TERM-LISTP-FORWARD-TO-TRUE-LISTP" "STRING<-L-IRREFLEXIVE")))
          (proof-with-checked-results
              ((fact (proof-proof-fact (h1-tactics-prover-proof proof) name nil))
               (rules (h1-tactics-rules-add-formula (h1-tactics-prover-rules proof) fact t t)))
            (h1-tactics-prover-with-rules proof rules))
        proof))))

(defund h1-books-admit-definition (proof definition)
  (proof-with-checked-results ((definition (proof-list-of-length definition 3)))
    (h1-books-book-prover-add-definition
     proof (car definition) (cadr definition) (caddr definition))))

(defun h1-books-admit-definitions (proof definitions)
  (declare (xargs :measure (len definitions)))
  (if (endp definitions)
      proof
    (proof-with-checked-results ((proof (h1-books-admit-definition proof (car definitions))))
      (h1-books-admit-definitions proof (cdr definitions)))))

(defun h1-books-constrained-names (functions)
  (if (endp functions)
      nil
    (proof-with-checked-results
        ((function (proof-list-of-length (car functions) 2))
         (rest (h1-books-constrained-names (cdr functions))))
      (cons (car function) rest))))

(defund h1-books-admit-constraint-formula (proof fields)
  (proof-with-checked-results ((fields (proof-list-of-length fields 2)))
    (h1-books-book-prover-index-fact
     (h1-books-add-theorem proof (car fields) (cadr fields)) (car fields) (cadr fields))))

(defun h1-books-admit-constraint-formulas (proof formulas)
  (declare (xargs :measure (len formulas)))
  (if (endp formulas)
      proof
    (proof-with-checked-results
        ((proof (h1-books-admit-constraint-formula proof (car formulas))))
      (h1-books-admit-constraint-formulas proof (cdr formulas)))))

(defun h1-books-admit-constraint (proof fields)
  (proof-with-checked-results
      ((functions (proof-term-at fields 0))
       (names (h1-books-constrained-names functions))
       (proof (h1-books-extend-available proof names))
       (formulas (proof-term-at fields 1)))
    (if (equal formulas *proof-nil*)
        proof
      (proof-with-checked-results ((equations (h1-book-witness-evaluator-equations functions formulas)))
        (h1-books-admit-constraint-formulas
         (h1-tactics-prover-with-evaluators
          proof (table-update (h1-tactics-prover-evaluators proof) equations))
         formulas)))))

(defund h1-books-admit (proof kind fields register-theorem)
  (cond ((equal kind "define") (h1-books-admit-definitions proof (cdr fields)))
        ((member-equal kind '("theorem" "axiom"))
         (proof-with-checked-results
             ((fields (proof-list-of-length fields 2))
              (proof (if (eq register-theorem :register-theorem)
                         (h1-books-register-theorem proof (car fields) (cadr fields))
                       (table-get register-theorem (list proof (car fields) (cadr fields))
                                    '(:failure "failure" "")))))
           (h1-books-book-prover-index-fact proof (car fields) (cadr fields))))
        ((equal kind "constrain") (h1-books-admit-constraint proof fields))
        ((equal kind "choose")
         (proof-with-checked-results ((name (proof-term-at fields 0)))
           (h1-books-extend-available proof (list name))))
        (t proof)))

(defund h1-books-parse-line (raw)
  (proof-with-checked-results ((parsed (reader-reader-line (reader-reader-init raw))))
    (list (caar parsed) (proof-freeze (cadar parsed)))))

(defun h1-books-parse-measure-lines (lines measures)
  (declare (xargs :measure (len lines)))
  (if (endp lines)
      measures
    (let ((raw (car lines)))
      (if (text-starts-with raw "(measure ")
          (proof-with-checked-results
              ((parsed (h1-books-parse-line (text-strip-right raw *h1-books-newlines*)))
               (fields (proof-list-of-length (cadr parsed) 4)))
            (h1-books-parse-measure-lines
             (cdr lines) (table-put measures (car fields) (list (cadr fields) (caddr fields)))))
        (h1-books-parse-measure-lines (cdr lines) measures)))))

(defun h1-books-parse-measures (lines)
  (h1-books-parse-measure-lines lines nil))

(defun h1-books-make-certificate (entries facts reason)
  (list :h1-certificate entries facts reason))

(defun h1-books-certificate-entries (certificate)
  (cadr certificate))

(defun h1-books-certificate-facts (certificate)
  (caddr certificate))

(defun h1-books-certificate-reason (certificate)
  (cadddr certificate))

(defun h1-books-certificate-dependencies-present (dependencies facts)
  (or (endp dependencies)
      (and (equal (table-get facts (caar dependencies) :none) (cadar dependencies))
           (h1-books-certificate-dependencies-present (cdr dependencies) facts))))

(defun h1-books-certificate-can-reuse (certificate proof)
  (h1-books-certificate-dependencies-present
   (h1-books-certificate-facts certificate)
   (proof-proof-facts (h1-tactics-prover-proof proof))))

(defun h1-books-definition-names (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
        ((name (proof-term-at (car definitions) 0))
         (rest (h1-books-definition-names (cdr definitions))))
      (cons name rest))))

(defund h1-books-entry-names (entry)
  (proof-with-checked-results ((entry (proof-list-of-length entry 4)))
    (if (equal (car entry) "define")
        (proof-with-checked-results ((parsed (h1-books-parse-line (seq-slice (cadddr entry) 0 -1))))
          (h1-books-definition-names (cdr (cadr parsed))))
      (list (cadr entry)))))

(defun h1-books-local-name-character (char)
  (and (characterp char)
       (let ((code (char-code char)))
         (or (and (<= (char-code #\A) code) (<= code (char-code #\Z)))
             (and (<= (char-code #\0) code) (<= code (char-code #\9)))
             (member-equal char '(#\$ #\< #\> #\= #\+ #\* #\/ #\! #\? #\. #\_ #\-))))))

(defun h1-books-local-name-add (name needed)
  (if (endp name)
      needed
    (let ((string (coerce (reverse name) 'string)))
      (if (member-equal string needed) needed (cons string needed)))))

(defund h1-books-local-names-scan (chars name skip needed)
  (declare (xargs :measure (len chars)))
  (cond ((endp chars) (h1-books-local-name-add name needed))
        ((not (zp skip)) (h1-books-local-names-scan (cdr chars) name (1- skip) needed))
        (name (if (h1-books-local-name-character (car chars))
                  (h1-books-local-names-scan (cdr chars) (cons (car chars) name) 0 needed)
                (h1-books-local-names-scan (cdr chars) nil 0 (h1-books-local-name-add name needed))))
        ((and (eql (car chars) #\A)
              (equal (take 11 chars) (coerce "ACL2::SELF-" 'list))
              (h1-books-local-name-character (nth 11 chars)))
         (h1-books-local-names-scan (cdr chars) '(#\- #\F #\L #\E #\S) 10 needed))
        ((and (eql (car chars) #\A)
              (equal (take 9 chars) (coerce "ACL2::H1-" 'list))
              (h1-books-local-name-character (nth 9 chars)))
         (h1-books-local-names-scan (cdr chars) '(#\- #\1 #\H) 8 needed))
        (t (h1-books-local-names-scan (cdr chars) nil 0 needed))))

(defun h1-books-needed-entry (names needed)
  (if (endp names)
      nil
    (proof-with-checked-results ((local-name (proof-term-at (car names) 2)))
      (or (member-equal local-name needed)
          (h1-books-needed-entry (cdr names) needed)))))

(defund h1-books-need-entry-sources (entries needed)
  (if (endp entries)
      needed
    (proof-with-checked-results ((source (proof-term-at (car entries) 3)))
      (h1-books-need-entry-sources
       (cdr entries) (h1-books-local-names-scan (coerce source 'list) nil 0 needed)))))

(defund h1-books-used-entry-group (entry previous needed)
  (proof-with-checked-results
      ((kind (proof-term-at entry 0))
       (paired (equal kind "measure"))
       (group (if paired
                  (proof-with-checked-results ((name (proof-term-at entry 1)))
                    (if (equal (take 2 previous) (list "define" name))
                        (list previous entry)
                      '(:failure "failure" "")))
                (list entry)))
       (names (h1-books-entry-names (car group)))
       (selected (h1-books-needed-entry names needed)))
    (if selected
        (proof-with-checked-results ((needed (h1-books-need-entry-sources group needed)))
          (list paired group needed))
      (list paired nil needed))))

(defun h1-books-used-entries-select (entries needed selected)
  (declare (xargs :measure (len entries)))
  (if (endp entries)
      selected
    (proof-with-checked-results
        ((group (h1-books-used-entry-group (car entries) (cadr entries) needed)))
      (h1-books-used-entries-select
       (if (car group) (cddr entries) (cdr entries))
       (caddr group) (append (cadr group) selected)))))

(defun h1-books-used-entries (entries conclusion)
  (proof-with-checked-results ((needed (h1-books-need-entry-sources (list conclusion) nil)))
    (h1-books-used-entries-select (reverse entries) needed (list conclusion))))

(defun h1-books-entry-list-names (entries)
  (if (endp entries)
      nil
    (proof-with-checked-results
        ((names (h1-books-entry-names (car entries)))
         (rest (h1-books-entry-list-names (cdr entries))))
      (append names rest))))

(defun h1-books-entry-lines (chars reversed)
  (cond ((endp chars) (and reversed (list (coerce (reverse reversed) 'string))))
        ((and (eql (car chars) #\Return) (eql (cadr chars) #\Newline))
         (cons (coerce (reverse reversed) 'string) (h1-books-entry-lines (cddr chars) nil)))
        ((member-equal (car chars) '(#\Return #\Newline))
         (cons (coerce (reverse reversed) 'string) (h1-books-entry-lines (cdr chars) nil)))
        (t (h1-books-entry-lines (cdr chars) (cons (car chars) reversed)))))

(defund h1-books-external-facts (lines local facts dependencies)
  (declare (xargs :measure (len lines)))
  (if (endp lines)
      dependencies
    (if (text-starts-with (car lines) "(fact ")
        (proof-with-checked-results
            ((parsed (h1-books-parse-line (car lines)))
             (name (proof-term-at (cadr parsed) 0)))
          (if (member-equal name local)
              (h1-books-external-facts (cdr lines) local facts dependencies)
            (let ((fact (assoc-equal name facts)))
              (if fact
                  (h1-books-external-facts
                   (cdr lines) local facts (table-put dependencies name (cdr fact)))
                '(:failure "failure" "")))))
      (h1-books-external-facts (cdr lines) local facts dependencies))))

(defun h1-books-entry-dependencies (entries local facts dependencies)
  (declare (xargs :measure (len entries)))
  (if (endp entries)
      dependencies
    (proof-with-checked-results
        ((entry (proof-list-of-length (car entries) 4))
         (lines (h1-books-entry-lines (coerce (cadddr entry) 'list) nil))
         (dependencies (h1-books-external-facts lines local facts dependencies)))
      (h1-books-entry-dependencies (cdr entries) local facts dependencies))))

(defun h1-books-certificate (proof entry used-entries)
  (let ((available (library-library-entries (h1-tactics-prover-library proof))))
    (proof-with-checked-results
        ((entries (if (eq used-entries :used-entries)
                      (h1-books-used-entries available entry)
                    (table-get used-entries (list available entry)
                                 '(:failure "candidate-rejected" ""))))
         (local (h1-books-entry-list-names entries))
         (dependencies (h1-books-entry-dependencies
                        entries local (proof-proof-facts (h1-tactics-prover-proof proof)) nil)))
      (h1-books-make-certificate entries (table-items dependencies) ""))))

(defun h1-books-skip (name)
  (proof-with-checked-results ((source (proof-line "skip" (list name))))
    (h1-books-make-certificate
     (list (list "skip" name nil source)) nil *h1-books-skip-reason*)))

(defun h1-books-unproved (result)
  (and (failure-p result) (equal (cadr result) "unproved")))

(defun h1-books-proof-pair (proof result)
  (if (failure-p result) (cons result proof) result))

(defun h1-books-prior-theorem (proof formula)
  (proof-with-checked-results ((step (h1-books-book-prover-prior-fact proof formula)))
    (if (and (not step) (proof-is-call formula *library-implies*))
        (proof-with-checked-results
            ((conclusion (proof-term-at formula 2))
             (step (h1-books-book-prover-prior-fact proof conclusion)))
          (and step (h1-propositions-propositional-proof-implies-from
                     (h1-tactics-prover-library proof) formula step)))
      step)))

(defund h1-books-theorem-tactic (proof formula tactic)
  (case tactic
    (:algebraic (cons (h1-book-arithmetic-algebraic-proof proof formula) proof))
    (:boolean (cons (h1-book-order-boolean-equality proof formula) proof))
    (:field (cons (h1-book-field-field-proof proof formula) proof))
    (:power-addition (cons (h1-book-expt-sum-power-addition proof formula) proof))
    (:power-equality (h1-books-proof-pair proof (h1-book-expt-power-equality proof formula)))
    (:power-monotonicity (cons (h1-book-expt-order-power-monotonicity proof formula) proof))
    (:projected-association (cons (h1-book-structure-projected-association proof formula) proof))
    (:substitution (h1-book-substitution-substitution-proof-with-proof proof formula))
    (otherwise (cons (h1-book-witness-evaluator-proof
                      proof formula (h1-books-book-prover-evaluators proof)) proof))))

(defun h1-books-theorem-automatic (proof formula)
  (let* ((result (h1-books-proof-pair proof (h1-recursion-prove-automatically proof formula)))
         (first (car result))
         (proof (cdr result)))
    (if (h1-books-unproved first)
        (let ((step (h1-book-structure-tuple-induction proof formula)))
          (cons (if (h1-books-unproved step) first step) proof))
      result)))

(defun h1-books-try-theorem-tactics (proof formula tactics)
  (declare (xargs :measure (len tactics)))
  (if (endp tactics)
      (h1-books-theorem-automatic proof formula)
    (let ((result (h1-books-theorem-tactic proof formula (car tactics))))
      (if (h1-books-unproved (car result))
          (h1-books-try-theorem-tactics (cdr result) formula (cdr tactics))
        result))))

(defun h1-books-select-theorem-proof (proof formula)
  (let ((prior (h1-books-prior-theorem proof formula)))
    (if prior
        (cons prior proof)
      (h1-books-try-theorem-tactics
       proof formula '(:algebraic :boolean :field :power-addition :power-equality
                       :power-monotonicity :projected-association :substitution :evaluator)))))

(defun h1-books-theorem-entry-with-proof (proof fields)
  (let ((fields (proof-list-of-length fields 2)))
    (if (failure-p fields)
        (cons fields proof)
      (let* ((name (car fields))
             (formula (cadr fields))
             (selected (h1-books-select-theorem-proof proof formula))
             (proof (cdr selected))
             (entry (proof-with-checked-results
                        ((step (car selected))
                         (final (proof-proof-subsume (h1-tactics-prover-proof proof) step (list formula))))
                      (proof-proof-entry "theorem" name (list name) (list final)))))
        (cons entry proof)))))

(defun h1-books-theorem-entry (proof fields)
  (let ((result (h1-books-theorem-entry-with-proof proof fields)))
    (if (failure-p (car result)) (car result) result)))

(defun h1-books-obligation-plan (kind fields)
  (cond ((equal kind "theorem")
         (proof-with-checked-results ((name (proof-term-at fields 0)))
           (list :theorem name)))
        ((equal kind "define")
         (proof-with-checked-results
             ((extenders (proof-term-at fields 0))
              (definitions (cdr fields))
              (calls (termination-recursive-calls extenders definitions)))
           (and calls (list :define (caar definitions) definitions calls))))
        ((equal kind "constrain")
         (proof-with-checked-results ((formulas (proof-term-at fields 1)))
           (if (equal formulas *proof-nil*)
               nil
             (proof-with-checked-results
                 ((functions (proof-term-at fields 0))
                  (function (proof-term-at functions 0))
                  (name (proof-term-at function 0)))
               (list :constrain name)))))
        (t nil)))

(defun h1-books-reusable-certificate (candidates proof)
  (cond ((endp candidates) nil)
        ((h1-books-certificate-can-reuse (car candidates) proof) (car candidates))
        (t (h1-books-reusable-certificate (cdr candidates) proof))))

(defun h1-books-produce-obligation (proof raw fields measures plan)
  (case (car plan)
    (:theorem (h1-books-theorem-entry-with-proof proof fields))
    (:define (cons (h1-book-termination-termination-entry
                    proof (caddr plan) (cadddr plan) measures) proof))
    (otherwise (h1-books-proof-pair proof (h1-book-witness-witness-entry proof raw fields)))))

(defun h1-books-obligation-result (name certificate proof memo report)
  (cons (list name certificate) (list proof memo report)))

(defund h1-books-obligation (proof raw kind fields measures memo used-entries report)
  (proof-with-checked-results ((plan (h1-books-obligation-plan kind fields)))
    (if (not plan)
        (cons nil (list proof memo nil))
      (let* ((name (cadr plan))
             (bucket (assoc-equal raw memo))
             (candidates (cdr bucket))
             (memo (if bucket memo (table-put memo raw nil)))
             (reusable (h1-books-reusable-certificate candidates proof)))
        (if reusable
            (h1-books-obligation-result name reusable proof memo nil)
          (let* ((produced (h1-books-produce-obligation proof raw fields measures plan))
                 (proof (cdr produced))
                 (certificate (proof-with-checked-results ((entry (car produced)))
                                (h1-books-certificate proof entry used-entries))))
            (cond ((and (failure-p certificate)
                        (member-equal (cadr certificate) '("unproved" "candidate-rejected" "value")))
                   (proof-with-checked-results
                       ((row (if report
                                 (proof-with-checked-results ((written (proof-write name)))
                                   (list written *h1-books-skip-reason*))
                               nil))
                        (skipped (h1-books-skip name)))
                     (h1-books-obligation-result name skipped proof memo row)))
                  ((failure-p certificate) certificate)
                  (t (h1-books-obligation-result
                      name certificate proof
                      (if (equal (h1-books-certificate-reason certificate) "")
                          (table-put memo raw (append candidates (list certificate)))
                        memo)
                      nil)))))))))

(defun h1-books-aids-for (book aids)
  (h1-books-parse-measures (table-get aids book nil)))

(defund h1-books-install-list (proof installers)
  (declare (xargs :measure (len installers)))
  (if (endp installers)
      proof
    (proof-with-checked-results ((proof (h1-books-install proof (car installers))))
      (h1-books-install-list proof (cdr installers)))))

(defun h1-books-step-count (counts)
  (if (endp counts) 0 (+ (car counts) (h1-books-step-count (cdr counts)))))

(defun h1-books-emission (entries emitted parts steps size)
  (if (endp entries)
      (list emitted parts steps size)
    (proof-with-checked-results ((entry (proof-list-of-length (car entries) 4)))
      (let* ((key (list (car entry) (cadr entry)))
             (source (cadddr entry))
             (previous (assoc-equal key emitted)))
        (cond ((not previous)
               (h1-books-emission (cdr entries) (table-put emitted key source) (cons source parts)
                                  (+ steps (h1-books-step-count (caddr entry))) (+ size (length source))))
              ((equal (cdr previous) source)
               (h1-books-emission (cdr entries) emitted parts steps size))
              (t '(:failure "failure" "")))))))

(defun h1-books-book-row (book name steps size reason)
  (proof-with-checked-results ((written (proof-write name)))
    (concatenate 'string
                 (text-join *h1-books-tab*
                          (list book written (if (equal reason "") "proved" "skipped")
                                (decimal-text steps) (decimal-text size) reason))
                 (coerce (list #\Newline) 'string))))

; OUTPUT contains the rows, source parts, entry index and skip count for one book.
(defund h1-books-emit-obligation (book item output)
  (if (not item)
      output
    (let* ((name (car item))
           (certificate (cadr item))
           (reason (h1-books-certificate-reason certificate)))
      (proof-with-checked-results
          ((emission (h1-books-emission (h1-books-certificate-entries certificate)
                                        (caddr output) (cadr output) 0 0))
           (row (h1-books-book-row book name (caddr emission) (cadddr emission) reason)))
        (list (cons row (car output)) (cadr emission) (car emission)
              (+ (cadddr output) (if (equal reason "") 0 1)))))))

(defund h1-books-generate-statement (raw book proof seen measures memo
                                          register-theorem used-entries report output reports)
  (proof-with-checked-results ((parsed (h1-books-parse-line (seq-slice raw 0 -1))))
    (if (member-equal raw seen)
        (list proof seen memo output reports)
      (let ((kind (car parsed))
            (fields (cadr parsed)))
        (proof-with-checked-results
            ((obligation (h1-books-obligation proof raw kind fields measures memo used-entries report))
             (output (h1-books-emit-obligation book (car obligation) output))
             (proof (h1-books-admit (cadr obligation) kind fields register-theorem))
             (installers (h1-books-declaration-tactics kind fields))
             (proof (h1-books-install-list proof installers)))
          (list proof (cons raw seen) (caddr obligation) output
                (if (cadddr obligation) (cons (cadddr obligation) reports) reports)))))))

(defund h1-books-generate-statements (lines book proof seen measures memo
                                          register-theorem used-entries report output reports)
  (declare (xargs :measure (len lines)))
  (if (endp lines)
      (list output memo reports)
    (proof-with-checked-results
        ((next (h1-books-generate-statement (car lines) book proof seen measures memo
                                           register-theorem used-entries report output reports)))
      (h1-books-generate-statements (cdr lines) book (car next) (cadr next) measures (caddr next)
                                     register-theorem used-entries report (cadddr next) (nth 4 next)))))

(defund h1-books-generate-book (row statement-lines aid-lines base seen memo
                                    register-theorem used-entries report reports)
  (let ((book (car row))
        (expected (cadr row)))
    (proof-with-checked-results
        ((measures (h1-books-aids-for book aid-lines))
         (generated (h1-books-generate-statements
                     (table-get statement-lines book nil) book (h1-books-book-prover-fork base)
                     seen measures memo register-theorem used-entries report (list nil nil nil 0) reports)))
      (let* ((output (car generated))
             (rows (reverse (car output)))
             (actual (len rows)))
        (if (not (equal expected actual))
            '(:failure "failure" "")
          (proof-with-checked-results ((source (text-join "" (reverse (cadr output)))))
            (list (list book source rows (cadddr output)) (cadr generated) (caddr generated))))))))

