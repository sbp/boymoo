(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-recursion-atom* (proof-cl "ATOM"))

(defun h1-recursion-definition (proof name)
  (let ((entry (assoc-equal name (proof-proof-definitions (h1-tactics-prover-proof proof)))))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun h1-recursion-instance-updates (old actuals bindings updates)
  (if (or (endp old) (endp actuals))
      (cons t updates)
    (proof-with-checked-results ((new (proof-subst (car actuals) bindings)))
      (let* ((term (car old))
             (application (not (eq (h1-tactics-call-head term) :none)))
             (previous (and (not application) (assoc-equal term updates))))
        (cond ((and application (not (equal new term))) nil)
              ((and previous (not (equal (cdr previous) new))) nil)
              (t (h1-recursion-instance-updates
                  (cdr old) (cdr actuals) bindings
                  (if (or application previous)
                      updates
                    (table-put updates term new)))))))))

(defun h1-recursion-instance-pairs (updates)
  (if (endp updates)
      nil
    (let* ((entry (car updates))
           (old (car entry))
           (new (cdr entry)))
      (if (equal old new)
          (h1-recursion-instance-pairs (cdr updates))
        (cons (list old new) (h1-recursion-instance-pairs (cdr updates)))))))

(defun h1-recursion-instance-tests (tests bindings)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((test (proof-subst (caar tests) bindings))
         (rest (h1-recursion-instance-tests (cdr tests) bindings)))
      (cons (list test (cadar tests)) rest))))

(defund h1-recursion-record-instance (actuals tests arguments bindings instances)
  (proof-with-checked-results
      ((updates (h1-recursion-instance-updates arguments actuals bindings nil)))
    (if (not updates)
        :incompatible
      (proof-with-checked-results
          ((pairs (h1-recursion-instance-pairs (cdr updates)))
           (tests (h1-recursion-instance-tests tests bindings)))
        (if (assoc-equal pairs instances)
            instances
          (table-put instances pairs tests))))))

(defmacro h1-recursion-with-instances (bindings body)
  (if (endp bindings)
      body
    (let ((name (caar bindings)))
      `(let (,(car bindings))
         (if (or (failure-p ,name) (eq ,name :incompatible))
             ,name
           (h1-recursion-with-instances ,(cdr bindings) ,body))))))

; Visit calls in the order in which their instances are consumed.
(mutual-recursion
 (defun h1-recursion-instance-walk (term name tests env arguments bindings instances)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (proof-compound term)) instances)
    ((endp term) '(:failure "failure" ""))
    ((equal (car term) *proof-quote*) instances)
    (t
     (let ((head (car term))
           (args (cdr term)))
       (cond
        ((proof-compound head)
         (if (not (equal (len head) 3))
             (proof-list-of-length head 3)
           (h1-recursion-with-instances
               ((instances (h1-recursion-instance-walk-args
                            args name tests env arguments bindings instances))
                (lambda-env (termination-lambda-bindings (cadr head) args env nil)))
             (h1-recursion-instance-walk
              (caddr head) name tests lambda-env arguments bindings instances))))
        ((and (equal head *termination-return-last*) (endp args))
         '(:failure "failure" ""))
        ((and (equal head *termination-return-last*) (equal (car args) *termination-mbe*))
         (if (consp (cddr args))
             (h1-recursion-instance-walk
              (caddr args) name tests env arguments bindings instances)
           '(:failure "failure" "")))
        ((equal head *proof-if*)
         (if (not (equal (len args) 3))
             (proof-list-of-length args 3)
           (h1-recursion-with-instances
               ((instances (h1-recursion-instance-walk
                            (car args) name tests env arguments bindings instances))
                (literal (proof-subst (car args) env))
                (instances (h1-recursion-instance-walk
                            (cadr args) name (append tests (list (list literal t))) env
                            arguments bindings instances)))
             (h1-recursion-instance-walk
              (caddr args) name (append tests (list (list literal nil))) env
              arguments bindings instances))))
        (t
         (h1-recursion-with-instances
             ((instances
               (if (equal head name)
                   (proof-with-checked-results
                       ((actuals (termination-subst-actuals args env)))
                     (h1-recursion-record-instance actuals tests arguments bindings instances))
                 instances)))
           (h1-recursion-instance-walk-args
            args name tests env arguments bindings instances))))))))
 (defun h1-recursion-instance-walk-args (args name tests env arguments bindings instances)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       instances
     (h1-recursion-with-instances
         ((instances (h1-recursion-instance-walk
                      (car args) name tests env arguments bindings instances)))
       (h1-recursion-instance-walk-args
        (cdr args) name tests env arguments bindings instances)))))

(defun h1-recursion-recursive-instances (proof application)
  (proof-with-checked-results
      ((parts (proof-constant-call-parts application))
       (name (car parts))
       (definition (h1-recursion-definition proof name))
       (definition (proof-list-of-length definition 2))
       (formals (car definition))
       (body (cadr definition))
       (bindings (proof-bindings-table (seq-zip formals (cdr parts)) nil)))
    (let ((instances (h1-recursion-instance-walk body name nil nil (cdr parts) bindings nil)))
      (if (eq instances :incompatible) nil instances))))

(defun h1-recursion-selector-path-from (term variable path)
  (declare (xargs :measure (acl2-count term)))
  (let ((head (h1-tactics-call-head term)))
    (cond ((not (member-equal head *termination-selectors*))
           (and (equal term variable) path))
          ((endp (cdr term)) (proof-term-at term 1))
          (t (h1-recursion-selector-path-from
              (cadr term) variable (cons (list head (cadr term)) path))))))

(defun h1-recursion-selector-path (term variable)
  (h1-recursion-selector-path-from term variable nil))

(mutual-recursion
 (defun h1-recursion-simplify-visit (n proof term evidence definitions)
   (declare (xargs :measure (nfix n)))
   (let ((head (car term))
         (base (h1-tactics-prover-proof proof)))
     (cond
      ((zp n) '(:failure "fuel" "h1-recursion-simplify-visit"))
      ((or (not (proof-compound term)) (equal head *proof-quote*)) nil)
      ((endp term) '(:failure "failure" ""))
      ((or (proof-compound head) (member-equal head definitions))
       (proof-with-checked-results
           ((expansion (proof-simplify-expansion base term))
            (next (h1-recursion-simplify-visit (1- n) proof (cadr expansion) evidence definitions)))
         (proof-proof-chain base (car expansion) (list next))))
      ((equal head *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at term 1))
            (first (h1-recursion-simplify-visit (1- n) proof test evidence definitions))
            (redex (proof-simplify-if-redex term first))
            (branch (h1-arithmetic-simplify-branch base redex evidence))
            (selected (h1-arithmetic-simplify-chain base term first branch))
            (right (and selected (proof-rewritten-term selected))))
         (if (or (not selected) (equal right redex))
             selected
           (proof-with-checked-results
               ((next (h1-recursion-simplify-visit (1- n) proof right evidence definitions)))
             (proof-proof-chain base selected (list next))))))
      (t
       (proof-with-checked-results
           ((result (h1-recursion-simplify-arguments
                     (1- n) proof term (cdr term) 1 nil evidence definitions))
            (current (if result (proof-rewritten-term result) term))
            (constant (h1-tactics-prover-constant proof current)))
         (cond ((not constant) result)
               (result (proof-proof-chain base result (list constant)))
               (t constant)))))))

 (defun h1-recursion-simplify-arguments (n proof term args index result evidence definitions)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h1-recursion-simplify-arguments"))
    ((endp args) result)
    (t
     (proof-with-checked-results
         ((equality (h1-recursion-simplify-visit (1- n) proof (car args) evidence definitions))
          (next (if equality
                    (proof-with-checked-results
                        ((previous (or result (h1-propositions-propositional-proof-reflexive
                                               (h1-tactics-prover-library proof) term))))
                      (proof-proof-rewrite (h1-tactics-prover-proof proof)
                                           previous equality (list 1 2 index)))
                  result)))
       (h1-recursion-simplify-arguments (1- n) proof term (cdr args) (1+ index)
                                         next evidence definitions))))))

(defun h1-recursion-simplify (proof term evidence definitions)
  (h1-recursion-simplify-visit 1000000 proof term evidence definitions))

(defun h1-recursion-selector-equation (proof variable actual selector-openings)
  (if (not (member-equal (h1-tactics-call-head actual) selector-openings))
      nil
    (let ((base (h1-tactics-prover-proof proof)))
      (proof-with-checked-results
          ((consp-step (h1-arithmetic-proof-assume base (list *proof-consp* variable) t)))
        (h1-recursion-simplify proof actual (list consp-step) selector-openings)))))

(defun h1-recursion-selector-bound (proof selector variable)
  (library-library-builtin (h1-tactics-prover-library proof)
                          (if (equal selector *library-car*) 2 3)
                          variable))

(defun h1-recursion-consp-tests (path variable tests)
  (if (endp path)
      nil
    (let* ((term (cadar path))
           (consp-test (list (list *proof-consp* term) t)))
      (if (or (equal term variable)
              (member-equal consp-test tests)
              (member-equal (list (list *h1-recursion-atom* term) nil) tests))
          (cons consp-test (h1-recursion-consp-tests (cdr path) variable tests))
        (h1-recursion-consp-tests (cdr path) variable tests)))))

(defun h1-recursion-library-prover (proof)
  (h1-tactics-make-prover (library-library-init proof) nil nil nil :none
                         (if (eq (proof-proof-kind proof) :h1-library-book) 18 :none)))

(defun h1-recursion-library-constant (proof term)
  (h1-tactics-prover-constant (h1-recursion-library-prover proof) term))

(defun h1-recursion-library-simplify (proof term evidence definitions)
  (h1-recursion-simplify (h1-recursion-library-prover proof) term evidence definitions))
(defun h1-recursion-library-simplify-first (proof step evidence definitions)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (equality (h1-recursion-library-simplify proof literal evidence definitions)))
    (if equality
        (proof-with-checked-results ((rewritten (proof-proof-rewrite proof step equality '(1))))
          (proof-proof-tidy proof rewritten))
      step)))

(defun h1-recursion-library-prove-visit (n proof term evidence definitions)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "h1-recursion-library-prove-visit"))
   ((equal term *proof-true*) (proof-prove-step proof term evidence definitions))
   (t
    (proof-with-checked-results ((premise (proof-find-evidence evidence (list term))))
      (if premise
          premise
        (proof-with-checked-results
            ((equality (h1-recursion-library-simplify proof term evidence definitions))
             (right (and equality (proof-rewritten-term equality))))
          (cond ((or (not equality) (equal right term)) '(:failure "candidate-rejected" ""))
                ((equal right *proof-true*) (proof-proof-true-from-eq proof equality))
                (t (proof-with-checked-results
                       ((step (h1-recursion-library-prove-visit (1- n) proof right evidence definitions)))
                     (h1-propositions-proof-transport proof step equality))))))))))

(defun h1-recursion-library-prove (proof term evidence definitions)
  (h1-recursion-library-prove-visit 1000000 proof term evidence definitions))

(defun h1-recursion-library-ints (library terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
     ((step (h1-arithmetic-proof-assume (library-library-proof library)
                                (library-integer (car terms)) t))
      (rest (h1-recursion-library-ints library (cdr terms))))
     (cons step rest))))

(mutual-recursion
 (defun h1-recursion-library-type-of (library term evidence)
   (declare (xargs :measure (acl2-count term)))
   (let ((literal (library-integer term)))
     (proof-with-checked-results ((premise (library-type-evidence literal evidence)))
       (cond
        (premise premise)
        ((atom term) (library-missing-integer term))
        ((and (proof-is-call term *proof-quote*) (endp (cdr term)))
         '(:failure "failure" ""))
        ((and (proof-is-call term *proof-quote*) (integerp (cadr term)))
         (h1-recursion-library-prove (library-library-proof library) literal nil nil))
        ((or (proof-is-call term *proof-plus*) (proof-is-call term *proof-times*))
         (proof-with-checked-results ((steps (h1-recursion-library-type-arguments library (cdr term) evidence)))
           (library-library-cite library
                                 (if (equal (car term) *proof-plus*)
                                     "INTEGER-SUM" "INTEGER-PRODUCT")
                                 (cdr term) steps)))
        ((proof-is-call term *proof-minus*)
         (if (endp (cdr term))
             '(:failure "failure" "")
           (proof-with-checked-results ((step (h1-recursion-library-type-of library (cadr term) evidence)))
             (library-library-cite library "INTEGER-NEGATION" (cdr term) (list step)))))
        ((proof-is-call term *library-count*)
         (library-library-cite library "COUNT-INTEGER" (cdr term) nil))
        ((proof-is-call term *library-len*)
         (library-library-cite library "LEN-INTEGER" (cdr term) nil))
        (t (library-missing-integer term))))))

 (defun h1-recursion-library-type-arguments (library args evidence)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((step (h1-recursion-library-type-of library (car args) evidence))
       (rest (h1-recursion-library-type-arguments library (cdr args) evidence)))
      (cons step rest)))))

(mutual-recursion
 (defun h1-recursion-library-natural (library term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term *library-count*)
     (library-library-cite library "COUNT-NATURAL" (cdr term) nil))
    ((proof-is-call term *library-len*)
     (library-library-cite library "LEN-NATURAL" (cdr term) nil))
    ((and (consp term) (proof-is-call term *proof-plus*))
     (proof-with-checked-results ((steps (h1-recursion-library-natural-arguments library (cdr term))))
       (library-library-cite library "NATURAL-SUM" (cdr term) steps)))
    (t (h1-recursion-library-prove (library-library-proof library)
                          (list *library-natp* term) nil (list *library-natp* *proof-not*)))))

 (defun h1-recursion-library-natural-arguments (library args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
      ((step (h1-recursion-library-natural library (car args)))
       (rest (h1-recursion-library-natural-arguments library (cdr args))))
      (cons step rest)))))

(defun h1-recursion-library-rational (library term evidence)
  (proof-with-checked-results
   ((axiom (library-library-axiom library "INTEGER-IMPLIES-RATIONAL" (list term)))
    (type-step (h1-recursion-library-type-of library term evidence)))
   (h1-arithmetic-proof-modus-ponens (library-library-proof library) axiom type-step)))

(defun h1-recursion-library-number (library term evidence)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((fact (proof-proof-fact proof "rationalp-acl2-numberp" (list (list *library-x* term))))
      (rational (h1-recursion-library-rational library term evidence)))
     (h1-arithmetic-proof-modus-ponens proof fact rational))))

(defun h1-recursion-library-push-minus (n library term evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "h1-recursion-library-push-minus")
    (let ((proof (library-library-proof library)))
      (cond
       ((proof-is-call term *proof-plus*)
        (proof-with-checked-results
         ((result (h1-arithmetic-proof-reflexive proof term))
          (left (proof-term-at term 1))
          (left-step (h1-recursion-library-push-minus (1- n) library left evidence))
          (result (if left-step
                      (proof-proof-rewrite proof result left-step '(1 2 1))
                    result))
          (right (proof-term-at term 2))
          (right-step (h1-recursion-library-push-minus (1- n) library right evidence))
          (result (if right-step
                      (proof-proof-rewrite proof result right-step '(1 2 2))
                    result))
          (first (proof-step-first result))
          (right (proof-term-at first 2)))
         (if (equal right term) nil result)))
       ((proof-is-call term *proof-minus*)
        (proof-with-checked-results ((argument (proof-term-at term 1)))
          (if (proof-is-call argument *proof-quote*)
              (h1-recursion-library-constant proof term)
            (let ((facts (proof-proof-facts proof)))
              (proof-with-checked-results
               ((result
                 (cond
                  ((and (proof-is-call argument *proof-minus*)
                        (assoc-equal (library-lemma-name "DOUBLE-NEGATION") facts))
                   (proof-with-checked-results
                    ((item (proof-term-at argument 1))
                     (type-step (h1-recursion-library-type-of library item evidence)))
                    (library-library-cite library "DOUBLE-NEGATION"
                                          (list item) (list type-step))))
                  ((and (proof-is-call argument *proof-plus*)
                        (assoc-equal (library-lemma-name "NEGATE-SUM") facts))
                   (proof-with-checked-results
                    ((steps (h1-recursion-library-type-arguments library (cdr argument) evidence)))
                    (library-library-cite library "NEGATE-SUM" (cdr argument) steps)))
                  (t nil))))
               (if (not result)
                   nil
                 (proof-with-checked-results
                  ((first (proof-step-first result))
                   (right (proof-term-at first 2))
                   (rest (h1-recursion-library-push-minus (1- n) library right evidence)))
                  (proof-proof-chain proof result (list rest)))))))))
       (t nil)))))

(defun h1-recursion-library-linear-combine-pair (library a b)
  (let ((proof (library-library-proof library)))
    (cond
     ((and (proof-is-call a *proof-quote*) (proof-is-call b *proof-quote*))
      (h1-recursion-library-constant proof (library-plus a b)))
     ((equal b (library-minus a))
      (library-library-axiom library "INVERSE-OF-+" (list a)))
     ((equal a (library-minus b))
      (proof-with-checked-results
       ((swap (library-library-axiom library "COMMUTATIVITY-OF-+" (list a b)))
        (inverse (library-library-axiom library "INVERSE-OF-+" (list b))))
       (proof-proof-chain proof swap (list inverse))))
     (t nil))))

(defun h1-recursion-library-linear-remove-zero (library step name term place evidence)
  (proof-with-checked-results
   ((type-step (h1-recursion-library-type-of library term evidence))
    (zero-step (library-library-cite library name (list term) (list type-step))))
   (proof-proof-rewrite (library-library-proof library) step zero-step place)))

(defun h1-recursion-library-linear-combine (n library step place evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "h1-recursion-library-linear-combine")
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
               (proof-with-checked-results ((step (h1-recursion-library-linear-remove-zero library step "ADD-ZERO-LEFT"
                                                                rest place evidence)))
                 (h1-recursion-library-linear-combine (1- n) library step place evidence)))
              ((and (equal b *proof-zero*) (not suffix))
               (proof-with-checked-results ((step (h1-recursion-library-linear-remove-zero library step "ADD-ZERO-RIGHT"
                                                                a place evidence)))
                 (h1-recursion-library-linear-combine (1- n) library step place evidence)))
              (t
               (proof-with-checked-results ((combine (h1-recursion-library-linear-combine-pair library a b)))
                 (if (not combine)
                     (h1-recursion-library-linear-combine (1- n) library step (append place '(2)) evidence)
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
                    (h1-recursion-library-linear-combine (1- n) library step '(1 2) evidence)))))))))))))

(defun h1-recursion-library-linear-form (library term evidence)
  (proof-with-checked-results
   ((step (h1-recursion-library-push-minus 1000000 library term evidence))
    (step (if step step (h1-arithmetic-proof-reflexive (library-library-proof library) term)))
    (step (library-linear-reassociate 1000000 library step '(1 2)))
    (step (library-linear-sort 1000000 library step '(1 2) nil)))
   (h1-recursion-library-linear-combine 1000000 library step '(1 2) evidence)))

(defun h1-recursion-library-linear-equal (library left right integers)
  (proof-with-checked-results
   ((a (h1-recursion-library-linear-form library left integers))
    (b (h1-recursion-library-linear-form library right integers))
    (a-first (proof-step-first a))
    (b-first (proof-step-first b))
    (a-normal (proof-term-at a-first 2))
    (b-normal (proof-term-at b-first 2)))
   (if (equal a-normal b-normal)
       (let ((proof (library-library-proof library)))
         (proof-with-checked-results ((symmetric (h1-propositions-proof-symmetric proof b)))
           (proof-proof-chain proof a (list symmetric))))
     '(:failure "candidate-rejected" ""))))

(defun h1-recursion-library-comparison (library a b integers)
  (proof-with-checked-results
   ((a-type (h1-recursion-library-type-of library a integers))
    (b-type (h1-recursion-library-type-of library b integers)))
   (library-library-cite library "LESS-DIFFERENCE" (list a b) (list a-type b-type))))

(defun h1-recursion-library-less-from-difference (library a b positive-difference integers)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((compare (h1-recursion-library-comparison library a b integers))
      (first (proof-step-first positive-difference))
      (term (proof-term-at first 2))
      (delta (h1-recursion-library-linear-equal library (library-diff b a) term integers))
      (compare (proof-proof-rewrite proof compare delta '(1 2 2))))
     (h1-propositions-proof-transport proof positive-difference compare))))

(defun h1-recursion-library-weak-from-difference (library a b nonnegative-difference integers)
  (proof-with-checked-results
   ((compare (library-library-axiom library "<-ON-OTHERS" (list b a)))
    (first (proof-step-first nonnegative-difference))
    (bound (proof-term-at first 1))
    (term (proof-term-at bound 1))
    (delta (h1-recursion-library-linear-equal library (library-diff b a) term integers))
    (compare (proof-proof-rewrite (library-library-proof library) compare delta '(1 2 1))))
   (h1-propositions-library-transport-argument library nonnegative-difference compare 1)))

(defun h1-recursion-library-additive-identities-inverse-unique (a b sum-zero integers library)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((commute (library-library-axiom library "COMMUTATIVITY-OF-+" (list (library-minus a) a)))
      (inverse (library-library-axiom library "INVERSE-OF-+" (list a)))
      (cancel (proof-proof-chain proof commute (list inverse)))
      (b-type (h1-recursion-library-type-of library b integers))
      (step (library-library-cite library "ADD-ZERO-LEFT" (list b) (list b-type)))
      (cancel (h1-propositions-proof-symmetric proof cancel))
      (step (proof-proof-rewrite proof step cancel '(1 1 1)))
      (step (h1-propositions-proof-symmetric proof step))
      (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+" (list (library-minus a) a b)))
      (step (proof-proof-chain proof step (list assoc-step)))
      (step (proof-proof-rewrite proof step sum-zero '(1 2 2)))
      (negative-type (h1-recursion-library-type-of library (library-minus a) integers))
      (zero-right (library-library-cite library "ADD-ZERO-RIGHT" (list (library-minus a))
                                        (list negative-type))))
     (proof-proof-chain proof step (list zero-right)))))

(defun h1-recursion-library-additive-identities (library)
  (let ((x *library-x*)
        (y *library-y*)
        (z *library-z*)
        (zero *proof-zero*)
        (fix (proof-sym "FIX" "ACL2")))
    (proof-with-checked-results
     ((ints (h1-recursion-library-ints library (list x)))
      (left-zero (library-library-axiom library "UNICITY-OF-0" (list x)))
      (x-number (h1-recursion-library-number library x ints))
      (fixed (library-inherited h1-recursion-library-simplify library (list fix x) (list x-number) (list fix)))
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
      (involution (h1-recursion-library-additive-identities-inverse-unique (library-minus x) x reverse ints library))
      (involution (library-inherited h1-propositions-proof-symmetric library involution))
      (library (library-library-lemma library "DOUBLE-NEGATION"
                                      (proof-eq (library-minus (library-minus x)) x)
                                      involution (list (proof-neg (library-integer x)))))
      (ints (h1-recursion-library-ints library (list x y))))
     (let ((a (library-plus x y))
           (b (library-plus (library-minus x) (library-minus y))))
       (proof-with-checked-results
        ((zero-sum (h1-recursion-library-linear-equal library (library-plus a b) zero ints))
         (distribute (h1-recursion-library-additive-identities-inverse-unique a b zero-sum ints library))
         (distribute (library-inherited h1-propositions-proof-symmetric library distribute)))
        (library-library-lemma library "NEGATE-SUM" (proof-eq (library-minus a) b) distribute
                               (library-guards (list (library-integer x) (library-integer y)))))))))

(defun h1-recursion-library-as-weak (library strict)
  (proof-with-checked-results
   ((literal (proof-step-first strict))
    (literal (proof-list-of-length literal 3)))
    (let ((a (cadr literal))
          (b (caddr literal)))
      (proof-with-checked-results
       ((a-type (h1-recursion-library-type-of library a nil))
        (b-type (h1-recursion-library-type-of library b nil)))
        (library-library-cite library "LESS-TO-WEAK" (list a b)
                              (list a-type b-type strict))))))

(defun h1-recursion-library-ordinal-comparison (library a b)
  (proof-with-checked-results
   ((a-type (h1-recursion-library-type-of library a nil))
    (b-type (h1-recursion-library-type-of library b nil)))
    (library-library-cite library "FINITE-ORDER" (list a b) (list a-type b-type))))

(defun h1-recursion-library-tenfold-increase (library ix px)
  (let* ((proof (library-library-proof library))
         (nine (proof-quote 9))
         (ten (proof-quote 10))
         (times-x (list *proof-times* nine *library-x*))
         (fix (proof-sym "FIX" "ACL2")))
    (proof-with-checked-results
     ((rational-nine (h1-recursion-library-rational library nine nil))
      (rational-x (h1-recursion-library-rational library *library-x* (list ix)))
      (positive-nine (h1-recursion-library-prove proof (library-positive nine) nil nil))
      (pos-product (library-library-cite library "POSITIVE-PRODUCT"
                                         (list nine *library-x*)
                                         (list rational-nine rational-x positive-nine px)))
      (result (h1-recursion-library-less-from-difference
               library *library-x* (library-plus *library-x* times-x) pos-product (list ix)))
      (expansion (library-library-axiom library "COMMUTATIVITY-OF-*" (list ten *library-x*)))
      (sum-ten (proof-proof-compute proof (library-plus *proof-one* nine) 10))
      (ten-sum (h1-propositions-proof-symmetric proof sum-ten))
      (expansion (proof-proof-rewrite proof expansion ten-sum '(1 2 2)))
      (distributed (library-library-axiom library "DISTRIBUTIVITY"
                                          (list *library-x* *proof-one* nine)))
      (expansion (proof-proof-chain proof expansion (list distributed)))
      (one-x (library-library-axiom library "UNICITY-OF-1" (list *library-x*)))
      (number-x (h1-recursion-library-number library *library-x* (list ix)))
      (fixed (h1-recursion-library-simplify proof (list fix *library-x*) (list number-x) (list fix)))
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

(defun h1-recursion-library-ordered-arithmetic (library)
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
     ((ints (h1-recursion-library-ints library (list x y)))
      (a (library-library-axiom library "<-ON-OTHERS" (list x y)))
      (b (library-library-axiom library "<-ON-OTHERS" (list *proof-zero* difference)))
      (delta (h1-recursion-library-linear-equal
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
      (premise (h1-recursion-library-prove proof both-positive (list px py) nil))
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
      (premise (h1-recursion-library-prove proof both-rational-positive (list rx ry px py) nil))
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
      (opposite (h1-recursion-library-comparison library x *proof-zero* (list ix)))
      (delta (h1-recursion-library-linear-equal library (library-diff *proof-zero* x)
                                           (library-minus x) (list ix)))
      (opposite (proof-proof-rewrite proof opposite delta '(1 2 2)))
      (exclusive-first (proof-step-first exclusive))
      (test (proof-term-at exclusive-first 1))
      (test-equality (h1-recursion-library-simplify proof test
                                           (list px) (list *proof-not*)))
      (exclusive (proof-proof-rewrite proof exclusive test-equality '(1 1)))
      (exclusive (h1-recursion-library-simplify-first proof exclusive nil nil))
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
      (number-x (h1-recursion-library-number library x (list ix)))
      (disjunction (h1-arithmetic-proof-modus-ponens proof tri number-x))
      (x-not-positive (h1-arithmetic-proof-assume proof positive-x nil))
      (x-not-zero (h1-arithmetic-proof-assume proof x-zero nil))
      (negative-case (h1-recursion-library-simplify-first proof disjunction
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
      (sum-type (h1-recursion-library-type-of library sum ints))
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
      (sum-type (h1-recursion-library-type-of library sum (list ix-nat iy-nat)))
      (sum-nat (library-library-cite library "NATURAL-FROM-BOUNDS" (list sum)
                                     (list sum-type sum-nat-bound)))
      (nat-x (proof-step-first nx))
      (nat-y (proof-step-first ny))
      (library (library-library-lemma library "NATURAL-SUM" (list *library-natp* sum)
                                      sum-nat (library-guards (list nat-x nat-y))))
      (proof (library-library-proof library))

      (pos-one (h1-recursion-library-prove proof (library-positive *proof-one*) nil nil))
      (one-type (h1-recursion-library-type-of library *proof-one* nil))
      (nonnegative-x (h1-arithmetic-proof-assume proof negative-x nil))
      (step (library-library-cite library "POSITIVE-PLUS-NONNEGATIVE" (list x *proof-one*)
                                   (list ix one-type pos-one nonnegative-x)))
      (one-plus-x (library-plus *proof-one* x))
      (library (library-library-lemma library "POSITIVE-ONE-PLUS" (library-positive one-plus-x)
                                      step (list (proof-neg integer-x) negative-x)))
      (step (h1-recursion-library-less-from-difference library x one-plus-x pos-one (list ix)))
      (library (library-library-lemma library "SUCCESSOR-LARGER" (library-lt x one-plus-x)
                                      step (list (proof-neg integer-x))))
      (proof (library-library-proof library))

      (nonless (h1-arithmetic-proof-assume proof compare-xy nil))
      (delta (library-diff x y))
      (offset (library-library-axiom library "<-ON-OTHERS" (list x y)))
      (nonneg-delta (proof-proof-rewrite proof nonless offset '(1 1)))
      (delta-type (h1-recursion-library-type-of library delta ints))
      (bound (library-library-cite library "POSITIVE-ONE-PLUS" (list delta)
                                    (list delta-type nonneg-delta)))
      (step (h1-recursion-library-less-from-difference library y one-plus-x bound ints))
      (library (library-library-lemma
                library "LESS-THAN-NEXT" (library-lt y one-plus-x) step
                (append (library-guards (list integer-x integer-y)) (list compare-xy)))))
     (h1-recursion-library-tenfold-increase library ix px))))

(defun h1-recursion-library-order-lemmas-delta-bound (a b strict library integers)
  (let ((proof (library-library-proof library)))
    (if strict
        (let ((less (library-lt a b)))
          (proof-with-checked-results
           ((step (h1-arithmetic-proof-assume proof less t))
            (comparison (h1-recursion-library-comparison library a b integers))
            (bound (proof-proof-rewrite proof step comparison '(1))))
            (list bound (proof-neg less))))
      (let ((less (library-lt b a)))
        (proof-with-checked-results
         ((step (h1-arithmetic-proof-assume proof less nil))
          (comparison (library-library-axiom library "<-ON-OTHERS" (list b a)))
          (bound (proof-proof-rewrite proof step comparison '(1 1))))
          (list bound less))))))

(defun h1-recursion-library-order-lemmas-transitivity (library name left-strict right-strict integers)
  (let ((x *library-x*)
        (y *library-y*)
        (z *library-z*))
    (proof-with-checked-results
     ((left (h1-recursion-library-order-lemmas-delta-bound x y left-strict library integers))
      (right (h1-recursion-library-order-lemmas-delta-bound y z right-strict library integers))
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
            ((low-type (h1-recursion-library-type-of library low integers))
             (high-type (h1-recursion-library-type-of library high integers)))
             (library-library-cite library "POSITIVE-PLUS-NONNEGATIVE" (list low high)
                                   (list low-type high-type positive-delta known))))))
      (step (h1-recursion-library-less-from-difference library x z delta integers)))
     (library-library-lemma
      library name (library-lt x z) step
      (append (library-guards (list (library-integer x) (library-integer y) (library-integer z)))
              (list (cadr left) (cadr right)))))))

(defun h1-recursion-library-order-lemmas (library)
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
     ((integers (h1-recursion-library-ints library (list x y z)))
      (xy (h1-arithmetic-proof-assume proof less t))
      (comparison (h1-recursion-library-comparison library x y integers))
      (delta (proof-proof-rewrite proof xy comparison '(1)))
      (difference-type (h1-recursion-library-type-of library difference integers))
      (bound (library-library-cite library "POSITIVE-NONNEGATIVE" (list difference)
                                   (list difference-type delta)))
      (step (h1-recursion-library-weak-from-difference library x y bound integers))
      (library (library-library-lemma library "LESS-TO-WEAK" (library-le x y) step
                                      (library-guards (list integer-x integer-y less))))

      (zero (library-library-axiom library "ZERO" nil))
      (step (h1-recursion-library-weak-from-difference library x x zero integers))
      (library (library-library-lemma library "WEAK-REFLEXIVE" (library-le x x) step
                                      (list (proof-neg integer-x))))
      (x-plus-z (library-plus x z))
      (y-plus-z (library-plus y z))
      (step (h1-recursion-library-less-from-difference library x-plus-z y-plus-z delta integers))
      (library (library-library-lemma library "LESS-SHIFT" (library-lt x-plus-z y-plus-z) step
                                      (library-guards (list integer-x integer-y integer-z less))))
      (library (h1-recursion-library-order-lemmas-transitivity library "LESS-TRANSITIVE" t t integers))
      (library (h1-recursion-library-order-lemmas-transitivity library "LESS-THEN-WEAK" t nil integers)))
     (h1-recursion-library-order-lemmas-transitivity library "WEAK-THEN-LESS" nil t integers))))

(defun h1-recursion-library-length-lemmas (library)
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
      (nat-one (h1-recursion-library-natural library *proof-one*))
      (successor (library-library-cite library "NATURAL-SUM" (list *proof-one* tail)
                                        (list nat-one child-nat)))
      (yes (h1-propositions-library-transport-argument library successor length-succ 1))
      (nat-zero (h1-recursion-library-natural library *proof-zero*))
      (no (h1-propositions-library-transport-argument library nat-zero length-zero 1))
      (ordinal (library-library-builtin library 1 x))
      (branches (proof-proof-cases proof cons-test yes no))
      (step (proof-proof-induct proof ordinal branches main measure
                                (list (list (list x cdr-x)))))
      (library (library-library-lemma library "LEN-NATURAL" main step nil))
      (nat-length (h1-recursion-library-natural library length))
      (step (library-library-cite library "NATURAL-INTEGER" (list length) (list nat-length)))
      (library (library-library-lemma library "LEN-INTEGER" (library-integer length) step nil))

      (tail-type (h1-recursion-library-type-of library tail nil))
      (less (library-library-cite library "SUCCESSOR-LARGER" (list tail) (list tail-type)))
      (less (h1-propositions-library-transport-argument library less length-succ 2)))
     (library-library-lemma library "LEN-CDR-LESS" (library-lt tail length) less
                           (list (proof-neg cons-test))))))

(defun h1-recursion-library-count-lemmas-numeric (leaf tests library integer-abs length)
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
      (h1-recursion-library-number library leaf evidence)))))

(defun h1-recursion-library-count-visit (n library value template integer-abs length)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof library)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "h1-recursion-library-count-visit"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((parts (proof-list-of-length (cdr value) 3))
           (yes (h1-recursion-library-count-visit (1- n) library (cadr parts)
                                               template integer-abs length))
           (no (h1-recursion-library-count-visit (1- n) library (caddr parts)
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
           (step (h1-recursion-library-count-visit (1- n) library body template integer-abs length))
           (symmetric (h1-propositions-proof-symmetric proof equation)))
        (proof-proof-rewrite-result proof step symmetric template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (h1-recursion-library-count-lemmas-numeric value nil library integer-abs length))
           (first (proof-step-first step))
           (goal (proof-subst template (list (cons *proof-result* value)))))
        (if (equal first goal) step '(:failure "failure" "")))))))

(defun h1-recursion-library-count-lemmas-numeric-lemma (library function name integer-abs length)
  (let* ((proof (library-library-proof library))
         (call (list function *library-x*))
         (template (list *library-numberp* *proof-result*)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof call))
      (opened-first (proof-step-first opened))
      (body (proof-term-at opened-first 2))
      (step (h1-recursion-library-count-visit 1000000 library body template integer-abs length))
      (closed (h1-propositions-proof-symmetric proof opened))
      (step (proof-proof-rewrite-result proof step closed template *proof-result*)))
     (library-library-lemma library name (list *library-numberp* call) step nil))))

(defun h1-recursion-library-count-lemmas (library)
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
      (library (h1-recursion-library-count-lemmas-numeric-lemma
                library integer-abs "ABS-NUMBER" integer-abs length))
      (library (h1-recursion-library-count-lemmas-numeric-lemma
                library length "LENGTH-NUMBER" integer-abs length))
      (library (h1-recursion-library-count-lemmas-numeric-lemma
                library *library-count* "COUNT-NUMBER" integer-abs length))
      (proof (library-library-proof library))
      (count-number (library-library-cite library "COUNT-NUMBER" (list x) nil))
      (is-finite (library-library-cite library "NUMBER-FINITE" (list size) (list count-number)))
      (ordinal (library-library-builtin library 1 x))
      (step (h1-recursion-library-simplify-first proof ordinal (list is-finite) (list *proof-ordinalp*)))
      (library (library-library-lemma library "COUNT-NATURAL" (list *library-natp* size) step nil))
      (natural-size (h1-recursion-library-natural library size))
      (step (library-library-cite library "NATURAL-INTEGER" (list size) (list natural-size))))
     (library-library-lemma library "COUNT-INTEGER" (library-integer size) step nil))))

(defun h1-recursion-library-weak-selectors-lemma (library head name number)
  (let* ((proof (library-library-proof library))
         (x *library-x*)
         (parent (list *library-count* x))
         (child (list *library-count* (list head x)))
         (cons-test (list *proof-consp* x)))
    (proof-with-checked-results
     ((descent (library-library-builtin library number x))
      (comparison (h1-recursion-library-ordinal-comparison library child parent))
      (strict (proof-proof-rewrite proof descent comparison '(1)))
      (yes (h1-recursion-library-as-weak library strict))
      (natural-parent (h1-recursion-library-natural library parent))
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
      (nil-size (h1-recursion-library-simplify proof (list *library-count* *proof-false*)
                                     nil (list *library-count*)))
      (child-zero (proof-proof-chain proof child-zero (list nil-size)))
      (zero-child (h1-propositions-proof-symmetric proof child-zero))
      (no (proof-proof-rewrite proof zero zero-child '(1 1 2)))
      (no (proof-proof-tidy proof no))
      (step (proof-proof-cases proof cons-test yes no)))
     (library-library-lemma library name (library-le child parent) step nil))))

(defun h1-recursion-library-weak-selectors (library)
  (proof-with-checked-results
   ((library (h1-recursion-library-weak-selectors-lemma library *library-car* "COUNT-CAR-WEAK" 2)))
    (h1-recursion-library-weak-selectors-lemma library *library-cdr* "COUNT-CDR-WEAK" 3)))

(defun h1-recursion-library-integer-measures (library)
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
     ((integers (h1-recursion-library-ints library (list x y)))
      (ix (car integers))
      (iy (cadr integers))
      (pos-y (h1-arithmetic-proof-assume proof positive-y t))
      (xy (h1-arithmetic-proof-assume proof x-less-y t))
      (nonneg-y (library-library-cite library "POSITIVE-NONNEGATIVE" (list y) (list iy pos-y)))
      (nat-y (library-library-cite library "NATURAL-FROM-BOUNDS" (list y) (list iy nonneg-y)))
      (y-exact (h1-recursion-library-simplify proof my (list nat-y) (list *library-nfix*)))
      (x-is-natural (h1-arithmetic-proof-assume proof nat-x t))
      (x-exact (h1-recursion-library-simplify proof mx (list x-is-natural) (list *library-nfix*)))
      (x-not-natural (h1-arithmetic-proof-assume proof nat-x nil))
      (x-zero (h1-recursion-library-simplify proof mx (list x-not-natural) (list *library-nfix*)))
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

      (ints (h1-recursion-library-ints library (list x y z)))
      (y-less-x (library-lt y x))
      (y-less-z (library-lt y z))
      (inside (h1-arithmetic-proof-assume proof y-less-x t))
      (advance (h1-arithmetic-proof-assume proof y-less-z t))
      (before (library-diff x y))
      (after (library-diff x z))
      (comparison (h1-recursion-library-comparison library y x ints))
      (pos-before (proof-proof-rewrite proof inside comparison '(1)))
      (pos-before (proof-proof-tidy proof pos-before))
      (comparison (h1-recursion-library-comparison library y z ints))
      (length-lost (proof-proof-rewrite proof advance comparison '(1)))
      (length-lost (proof-proof-tidy proof length-lost))
      (smaller (h1-recursion-library-less-from-difference library after before length-lost ints))
      (after-type (h1-recursion-library-type-of library after ints))
      (before-type (h1-recursion-library-type-of library before ints))
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

(defun h1-recursion-library-build-after-count (library)
  (proof-with-checked-results ((library (h1-recursion-library-weak-selectors library)))
    (h1-recursion-library-integer-measures library)))

(defun h1-recursion-build (proof)
  (let* ((library (h1-tactics-prover-library proof))
         (core (library-library-proof library))
         (kind (proof-proof-kind core))
         (book (not (eq (h1-tactics-prover-case-limit proof) :none)))
         (core (proof-proof-with-kind core (if book :h1-library-book :h1-library-prover)))
         (library (library-library-with-proof library core)))
    (proof-with-checked-results
        ((library (h1-propositions-propositional-proof-logic-and-types library))
         (library (h1-recursion-library-additive-identities library))
         (library (h1-recursion-library-ordered-arithmetic library))
         (library (h1-recursion-library-order-lemmas library))
         (library (h1-recursion-library-length-lemmas library))
         (library (h1-recursion-library-count-lemmas library))
         (library (h1-recursion-library-build-after-count library)))
      (let* ((core (proof-proof-with-kind (library-library-proof library) kind))
             (library (library-library-with-proof library core))
             (proof (h1-tactics-prover-with-library proof library)))
        (if book
            (h1-tactics-prover-with-available
             proof (h1-tactics-ordered-set
                    (append (h1-tactics-prover-available proof)
                            (table-keys (proof-proof-definitions core)))))
          proof)))))

(defun h1-recursion-restore-selector (proof equation step)
  (if (not equation)
      step
    (let ((base (h1-tactics-prover-proof proof)))
      (proof-with-checked-results
          ((reverse-step (h1-propositions-proof-symmetric base equation))
           (rewritten (proof-proof-rewrite base step reverse-step '(1 1 1))))
        (proof-proof-tidy base rewritten)))))

(defun h1-recursion-selector-decrease (proof actual variable tests)
  (let ((lib (h1-tactics-prover-library proof))
        (base (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((hypotheses (descent-hypotheses-init lib tests nil))
         (opened (h1-recursion-simplify proof actual nil (list *termination-return-last*)))
         (actual (if opened (proof-rewritten-term opened) actual))
         (head (proof-term-at actual 0))
         (arg (and (member-equal head *termination-selectors*) (proof-term-at actual 1)))
         (step
          (if (and (member-equal head *termination-selectors*) (equal arg variable))
              (proof-with-checked-results
                  ((strict (h1-recursion-selector-bound proof head variable))
                   (found (descent-hypotheses-require hypotheses (list *proof-consp* variable))))
                (proof-proof-discharge base strict (car found)))
            (proof-with-checked-results
                ((bound (descent-selector-chain lib actual variable hypotheses))
                 (measure (library-library-ordinal-comparison
                           lib (list *library-count* actual) (list *library-count* variable))))
              (h1-propositions-proof-transport base (car bound) measure)))))
      (h1-recursion-restore-selector proof opened step))))

(defun h1-recursion-structural-descent-step (proof variable actual tests equation path)
  (if (endp (cdr path))
      (let ((step (h1-recursion-selector-bound proof (caar path) variable)))
        (cons (if (failure-p step) step (h1-recursion-restore-selector proof equation step))
              proof))
    (let* ((conses (h1-recursion-consp-tests path variable tests))
           (base (h1-tactics-prover-proof proof))
           (updated (if (assoc-equal (proof-sym "SELF-COUNT-INTEGER" "ACL2")
                                     (proof-proof-facts base))
                        proof
                      (h1-recursion-build proof))))
      (if (failure-p updated)
          (cons updated proof)
        (let ((step (h1-recursion-selector-decrease updated actual variable conses)))
          (cons (if (failure-p step) step (h1-recursion-restore-selector updated equation step))
                updated))))))

(defun h1-recursion-structural-descent (proof variable actual tests selector-openings)
  (let* ((equation (h1-recursion-selector-equation proof variable actual selector-openings))
         (actual (cond ((failure-p equation) equation)
                       (equation (proof-rewritten-term equation))
                       (t actual))))
    (if (failure-p actual)
        (cons actual proof)
      (let ((path (h1-recursion-selector-path actual variable)))
        (cond ((failure-p path) (cons path proof))
              ((endp path) (cons nil proof))
              (t (h1-recursion-structural-descent-step
                  proof variable actual tests equation path)))))))

(defun h1-recursion-descent-for (proof variable actual tests selector-openings)
  (let ((lib (h1-tactics-prover-library proof)))
    (cond ((equal actual (library-plus variable *proof-neg-one*))
           (cons (library-library-builtin lib 8 variable) proof))
          ((equal actual (library-plus *proof-neg-one* variable))
           (cons (library-library-builtin lib 9 variable) proof))
          (t (h1-recursion-structural-descent proof variable actual tests selector-openings)))))

(defun h1-recursion-project-tail (path tail)
  (if (endp path)
      tail
    (h1-recursion-project-tail (cdr path) (list (caar path) tail))))

(defun h1-recursion-project-formula (suffixes formula variable projections)
  (if (endp suffixes)
      projections
    (proof-with-checked-results
        ((tail (h1-recursion-project-tail suffixes variable))
         (projection (proof-subst formula (list (cons variable tail)))))
      (h1-recursion-project-formula (cdr suffixes) formula variable (cons projection projections)))))

(defun h1-recursion-projection-instance (proof formula variable pairs selector-openings plan)
  (let ((pair (car pairs)))
    (if (or (not (equal (len pairs) 1)) (not (equal (car pair) variable)))
        nil
      (proof-with-checked-results
          ((actual (proof-term-at pair 1))
           (equation (h1-recursion-selector-equation proof variable actual selector-openings))
           (term (if equation (proof-rewritten-term equation) actual))
           (path (h1-recursion-selector-path term variable)))
        (if (endp path)
            nil
          (proof-with-checked-results
              ((projections (h1-recursion-project-formula (cdr path) formula variable (car plan))))
            (cons projections (append (cdr plan) (strip-cars path)))))))))

(defun h1-recursion-projection-plan (proof formula variable instances selector-openings plan)
  (declare (xargs :measure (acl2-count instances)))
  (cond ((or (not plan) (failure-p plan)) plan)
        ((endp instances) (cons (reverse (car plan)) (cdr plan)))
        (t (h1-recursion-projection-plan
            proof formula variable (cdr instances) selector-openings
            (h1-recursion-projection-instance
             proof formula variable (caar instances) selector-openings plan)))))

(defun h1-recursion-strengthen (conjuncts)
  (if (endp (cdr conjuncts))
      (car conjuncts)
    (proof-ite (car conjuncts) (h1-recursion-strengthen (cdr conjuncts)) *proof-false*)))

(defun h1-recursion-projection-cases (proof variable selectors)
  (if (endp selectors)
      nil
    (let* ((head (car selectors))
           (pairs (list (list variable (list head variable)))))
      (proof-with-checked-results
          ((bound (h1-recursion-selector-bound proof head variable))
           (rest (h1-recursion-projection-cases proof variable (cdr selectors))))
        (cons (list pairs bound) rest)))))

(defun h1-recursion-extend-openings (selector-openings functions)
  (if (endp selector-openings)
      functions
    (let ((head (car selector-openings)))
      (h1-recursion-extend-openings
       (cdr selector-openings)
       (if (or (member-equal head *h1-tactics-translation*) (assoc-equal head functions))
           functions
         (table-put functions head 1))))))

(defun h1-recursion-prove-with-projections
    (proof formula variable instances openings selector-openings preserve)
  (proof-with-checked-results
      ((plan (h1-recursion-projection-plan proof formula variable instances
                                          selector-openings (cons nil nil))))
    (if (not (car plan))
        nil
      (let ((strengthened (h1-recursion-strengthen (cons formula (proof-unique (car plan))))))
        (proof-with-checked-results
            ((cases (h1-recursion-projection-cases proof variable (proof-unique (cdr plan))))
             (functions (h1-recursion-extend-openings
                         selector-openings (h1-tactics-opening-map openings)))
             (step (h1-tactics-prover-by-induction
                    proof strengthened (list *library-count* variable) cases
                    functions nil :none nil preserve (list *proof-consp* variable)))
             (conjuncts (h1-propositions-propositional-proof-conjunct
                         (h1-tactics-prover-library proof) step)))
          (car conjuncts))))))

(defun h1-recursion-induction-case (proof variable instance selector-openings cases)
  (let* ((pairs (car instance))
         (tests (cdr instance))
         (binding (assoc-equal variable pairs))
         (actual (if binding (cadr binding) variable))
         (result (h1-recursion-descent-for proof variable actual tests selector-openings))
         (descent (car result)))
    (if (or (not descent) (failure-p descent))
        (list nil descent (cdr result))
      (list t (cons (list pairs descent) cases) (cdr result)))))

(defun h1-recursion-induction-cases (variable instances selector-openings result)
  (declare (xargs :measure (acl2-count instances)))
  (cond ((not (car result)) (cons (cadr result) (caddr result)))
        ((endp instances) (cons (reverse (cadr result)) (caddr result)))
        (t (h1-recursion-induction-cases
            variable (cdr instances) selector-openings
            (h1-recursion-induction-case
             (caddr result) variable (car instances) selector-openings (cadr result))))))

(defun h1-recursion-unproved-p (result)
  (and (failure-p result) (equal (cadr result) "unproved")))

(defun h1-recursion-assume-premise (formula variable assume-premise)
  (if (not (eq assume-premise :none))
      assume-premise
    (and (proof-is-call formula *library-implies*)
         (proof-with-checked-results ((premise (proof-term-at formula 1)))
           (not (member-equal variable (h1-tactics-variables premise)))))))

; Each search visit returns the selected result, last failed induction,
; and the Prover containing any facts added to establish descent.
(defun h1-recursion-try-variable
    (proof formula variable instances openings selector-openings assume-premise preserve failure)
  (let ((strengthened (h1-recursion-prove-with-projections
                       proof formula variable instances openings selector-openings preserve)))
    (if (and strengthened (not (h1-recursion-unproved-p strengthened)))
        (list strengthened failure proof)
      (let* ((result (h1-recursion-induction-cases
                      variable instances selector-openings (list t nil proof)))
             (cases (car result))
             (proof (cdr result)))
        (cond
         ((or (not cases) (failure-p cases)) (list cases failure proof))
         (t
          (let ((given (h1-recursion-assume-premise formula variable assume-premise)))
            (if (failure-p given)
                (list given failure proof)
              (let ((step (h1-tactics-prover-by-induction
                           proof formula (list *library-count* variable) cases
                           openings nil :none given preserve :none)))
                (if (h1-recursion-unproved-p step)
                    (list nil step proof)
                  (list step failure proof)))))))))))

(defun h1-recursion-try-variables
    (formula variables instances openings selector-openings assume-premise preserve attempt)
  (declare (xargs :measure (acl2-count variables)))
  (if (or (endp variables) (car attempt))
      attempt
    (h1-recursion-try-variables
     formula (cdr variables) instances openings selector-openings assume-premise preserve
     (h1-recursion-try-variable
      (caddr attempt) formula (car variables) instances openings selector-openings
      assume-premise preserve (cadr attempt)))))

(defun h1-recursion-application-variables (arguments)
  (if (endp arguments)
      nil
    (if (eq (h1-tactics-call-head (car arguments)) :none)
        (cons (car arguments) (h1-recursion-application-variables (cdr arguments)))
      (h1-recursion-application-variables (cdr arguments)))))

(defun h1-recursion-try-application
    (proof formula application openings selector-openings assume-premise preserve failure)
  (let ((instances (h1-recursion-recursive-instances proof application)))
    (cond ((or (not instances) (failure-p instances)) (list instances failure proof))
          (t (h1-recursion-try-variables
              formula (proof-unique (h1-recursion-application-variables (cdr application)))
              instances openings selector-openings assume-premise preserve
              (list nil failure proof))))))

(defun h1-recursion-try-applications
    (formula head terms openings selector-openings assume-premise preserve attempt)
  (declare (xargs :measure (acl2-count terms)))
  (if (or (endp terms) (car attempt))
      attempt
    (h1-recursion-try-applications
     formula head (cdr terms) openings selector-openings assume-premise preserve
     (if (equal (h1-tactics-call-head (car terms)) head)
         (h1-recursion-try-application
          (caddr attempt) formula (car terms) openings selector-openings
          assume-premise preserve (cadr attempt))
       attempt))))

(defun h1-recursion-try-openings
    (formula heads terms openings selector-openings assume-premise preserve attempt)
  (declare (xargs :measure (acl2-count heads)))
  (if (or (endp heads) (car attempt))
      attempt
    (let* ((head (car heads))
           (base (h1-tactics-prover-proof (caddr attempt)))
           (defined (assoc-equal head (proof-proof-definitions base))))
      (h1-recursion-try-openings
       formula (cdr heads) terms openings selector-openings assume-premise preserve
       (if defined
           (h1-recursion-try-applications
            formula head terms openings selector-openings assume-premise preserve attempt)
         attempt)))))

(defun h1-recursion-prove-from-calls
    (proof formula openings selector-openings assume-premise preserve)
  (let* ((terms (proof-unique (h1-tactics-subterms formula)))
         (heads (if (h1-tactics-opening-map-p openings) (table-keys openings) openings))
         (attempt (h1-recursion-try-openings
                   formula heads terms openings selector-openings assume-premise preserve
                   (list nil nil proof)))
         (proof (caddr attempt))
         (result (or (car attempt)
                     (cadr attempt)
                     (h1-tactics-prover-solve proof formula openings 160))))
    (cons result proof)))

(defun h1-recursion-simple-calls-p (terms allowed)
  (if (endp terms)
      t
    (and (member-equal (h1-tactics-call-head (car terms)) allowed)
         (h1-recursion-simple-calls-p (cdr terms) allowed))))

(defun h1-recursion-simple-tests (proof heads allowed)
  (if (endp heads)
      nil
    (proof-with-checked-results
        ((definition (h1-recursion-definition proof (car heads)))
         (body (proof-term-at definition 1))
         (simple (h1-recursion-simple-calls-p (h1-tactics-subterms body) allowed))
         (rest (h1-recursion-simple-tests proof (cdr heads) allowed)))
      (if simple (cons (car heads) rest) rest))))

(defun h1-recursion-automatic-tests (proof heads allowed)
  (if (endp heads)
      nil
    (proof-with-checked-results
        ((definition (h1-recursion-definition proof (car heads)))
         (body (proof-term-at definition 1))
         (tests (h1-recursion-simple-tests proof (h1-tactics-prover-functions-in proof body) allowed))
         (rest (h1-recursion-automatic-tests proof (cdr heads) allowed)))
      (append tests rest))))

(defun h1-recursion-prove-automatically (proof formula)
  (let* ((heads (h1-tactics-prover-functions-in proof formula))
         (direct (h1-tactics-prover-solve proof formula heads 8)))
    (if (not (h1-recursion-unproved-p direct))
        (cons direct proof)
      (let* ((base (h1-tactics-prover-proof proof))
             (simple-calls (append (proof-proof-primitives base) *h1-tactics-translation*
                                   (list :none *proof-quote*)))
             (tests (h1-recursion-automatic-tests proof heads simple-calls)))
        (if (failure-p tests)
            (cons tests proof)
          (h1-recursion-prove-from-calls proof formula (proof-unique (append heads tests))
                                         nil :none nil))))))
