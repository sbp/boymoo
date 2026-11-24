(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-book-sums-prefix* "H3-BOOK-")
(defconst *h3-book-sums-add* (concatenate 'string *h3-book-sums-prefix* "FIXED-ADDEND"))
(defconst *h3-book-sums-add-inv* (concatenate 'string *h3-book-sums-prefix* "FIXED-NEGAND"))
(defconst *h3-book-sums-fixed* (concatenate 'string *h3-book-sums-prefix* "FIX-IS-NUMERIC"))
(defconst *h3-book-sums-double* (concatenate 'string *h3-book-sums-prefix* "DOUBLE-NEGATION"))
(defconst *h3-book-sums-negate* (concatenate 'string *h3-book-sums-prefix* "NEGATE-SUM"))

(defun h3-book-sums-step-argument (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h3-book-sums-add-cancellation (library term offset)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((equation (library-library-axiom library "ASSOCIATIVITY-OF-+"
                                       (list term offset (library-minus offset))))
      (inverse (library-library-axiom library "INVERSE-OF-+" (list offset)))
      (equation (proof-proof-rewrite proof equation inverse '(1 2 2)))
      (swap (library-library-axiom library "COMMUTATIVITY-OF-+" (list term *proof-zero*)))
      (zero (library-library-axiom library "UNICITY-OF-0" (list term))))
     (proof-proof-chain proof equation (list swap zero)))))

(defun h3-book-sums-cancel-addend (library equality first second offset)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((left (h3-book-sums-step-argument equality 1))
      (expr (library-plus left (library-minus offset)))
      (step (proof-proof-reflexive proof expr))
      (step (proof-proof-rewrite proof step equality '(1 2 1)))
      (left-cancellation (h3-book-sums-add-cancellation library first offset))
      (step (proof-proof-rewrite proof step left-cancellation '(1 1)))
      (right-cancellation (h3-book-sums-add-cancellation library second offset))
      (step (proof-proof-rewrite proof step right-cancellation '(1 2))))
     (proof-proof-tidy proof step))))

(defun h3-book-sums-inverse-unique (library term other sum-zero)
  (let ((proof (library-library-proof library))
        (opposite (library-minus term)))
    (proof-with-checked-results
     ((swap (library-library-axiom library "COMMUTATIVITY-OF-+" (list other term)))
      (inverse (library-library-axiom library "INVERSE-OF-+" (list term)))
      (inverse (proof-proof-symmetric proof inverse))
      (swap-back (library-library-axiom library "COMMUTATIVITY-OF-+" (list term opposite)))
      (equation (proof-proof-chain proof swap (list sum-zero inverse swap-back)))
      (step (h3-book-sums-cancel-addend library equation other opposite term))
      (numeric (h3-book-arithmetic-typed-number library opposite))
      (fixed (h3-book-arithmetic-fix-value library opposite numeric))
      (step (proof-proof-rewrite proof step fixed '(1 2))))
     (proof-proof-tidy proof step))))

(defun h3-book-sums-book-sums-lib (sums)
  (cadr sums))

(defun h3-book-sums-book-sums-types (sums)
  (caddr sums))

(defun h3-book-sums-book-sums-search (sums)
  (cadddr sums))

(defun h3-book-sums-book-sums-init (library)
  (proof-with-checked-results
   ((numeric-sums (h3-numeric-order-numeric-sums-init library))
    (rules (h3-rewrite-rules-init library
                                (list "rationalp-acl2-numberp"
                                      (proof-sym "INTEGER-IMPLIES-RATIONAL" "ACL2"))
                                nil)))
   (list :h3-book-sums library (h3-numeric-order-numeric-sums-types numeric-sums)
         (h3-rewrite-search-init library nil nil rules 150 nil))))

(defun h3-book-sums-book-sums-type-of (sums term evidence)
  (let ((library (h3-book-sums-book-sums-lib sums))
        (search (h3-book-sums-book-sums-search sums))
        (goal (list *library-numberp* term)))
    (if (proof-is-call term *h3-book-arithmetic-fix*)
        (library-library-cite library *h3-book-sums-fixed* (cdr term) nil)
      (proof-with-checked-results
       ((context (h3-rewrite-search-context search evidence))
        (known (h3-rewrite-search-known search goal context)))
       (if known
           known
         (let ((typed (h3-book-arithmetic-typed-number library term)))
           (if (h3-rewrite-unproved-p typed)
               (proof-with-checked-results ((context (h3-rewrite-search-context search evidence)))
                 (car (h3-rewrite-search-derive search goal context nil nil)))
             typed)))))))

(defun h3-book-sums-book-sums-constant (sums term)
  (h3-rewrite-primitive (h3-book-sums-book-sums-lib sums) term))

(mutual-recursion
 (defun h3-book-sums-book-sums-push-minus (n sums term evidence)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "h3-book-sums-book-sums-push-minus")
     (let* ((library (h3-book-sums-book-sums-lib sums))
            (proof (library-library-proof library)))
       (cond
        ((proof-is-call term *proof-plus*)
         (proof-with-checked-results
          ((step (proof-proof-reflexive proof term))
           (step (h3-book-sums-push-minus-children (1- n) sums (cdr term) evidence 1 step))
           (right (h3-book-sums-step-argument step 2)))
          (if (equal right term) nil step)))
        ((proof-is-call term *proof-minus*)
         (proof-with-checked-results ((arg (proof-term-at term 1)))
           (cond
            ((proof-is-call arg *proof-minus*)
             (proof-with-checked-results
              ((step (library-library-cite library *h3-book-sums-double* (cdr arg) nil))
               (value (proof-term-at arg 1))
               (numeric (h3-book-sums-book-sums-type-of sums value evidence))
               (fixed (h3-book-arithmetic-fix-value library value numeric))
               (step (proof-proof-chain proof step (list fixed)))
               (right (h3-book-sums-step-argument step 2))
               (rest (h3-book-sums-book-sums-push-minus (1- n) sums right evidence)))
              (proof-proof-chain proof step (list rest))))
            ((proof-is-call arg *proof-plus*)
             (proof-with-checked-results
              ((step (library-library-cite library *h3-book-sums-negate* (cdr arg) nil))
               (right (h3-book-sums-step-argument step 2))
               (rest (h3-book-sums-book-sums-push-minus (1- n) sums right evidence)))
              (proof-proof-chain proof step (list rest))))
            (t (h3-book-sums-book-sums-constant sums term)))))
        (t nil)))))
 (defun h3-book-sums-push-minus-children (n sums args evidence index step)
   (declare (xargs :measure (nfix n)))
   (cond
    ((endp args) step)
    ((not (o< (nfix (1- n)) (nfix n)))
     '(:failure "Fuel" "h3-book-sums-push-minus-children"))
    (t
     (proof-with-checked-results
      ((reduced (h3-book-sums-book-sums-push-minus (1- n) sums (car args) evidence))
       (step (if reduced
                 (proof-proof-rewrite (library-library-proof (h3-book-sums-book-sums-lib sums))
                                      step reduced (list 1 2 index))
               step)))
      (h3-book-sums-push-minus-children (1- n) sums (cdr args) evidence (1+ index) step))))))

(defun h3-book-sums-prepare-fix (sums term evidence step)
  (proof-with-checked-results ((value (proof-term-at term 1)))
    (let* ((library (h3-book-sums-book-sums-lib sums))
           (numeric (h3-book-sums-book-sums-type-of sums value evidence))
           (fixed (if (failure-p numeric) numeric
                    (h3-book-arithmetic-fix-value library value numeric))))
      (if (h3-rewrite-unproved-p fixed) step fixed))))

(defun h3-book-sums-prepare-addend (library step arg index)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((current (h3-book-sums-step-argument step 2))
      (head (proof-term-at current 0))
      (equation
       (cond
        ((equal head *proof-minus*)
         (library-library-cite library *h3-book-sums-add-inv* (list arg) nil))
        ((equal index 1)
         (library-library-cite library *h3-book-sums-add* (cdr current) nil))
        (t
         (proof-with-checked-results
          ((swap (library-library-axiom library "COMMUTATIVITY-OF-+" (cdr current)))
           (fixed (library-library-cite library *h3-book-sums-add* (reverse (cdr current)) nil))
           (left (proof-term-at current 1))
           (swap-back (library-library-axiom library "COMMUTATIVITY-OF-+"
                                             (list (list *h3-book-arithmetic-fix* arg) left))))
          (proof-proof-chain proof swap (list fixed swap-back)))))))
     (proof-proof-chain proof step (list equation)))))

(defun h3-book-sums-prepare-child (library step child arg index)
  (let* ((proof (library-library-proof library))
         (updated (proof-with-checked-results
                   ((child child)
                    (left (h3-book-sums-step-argument child 1))
                    (right (h3-book-sums-step-argument child 2)))
                   (if (equal left right)
                       step
                     (proof-proof-rewrite proof step child (list 1 2 index))))))
    (if (h3-rewrite-unproved-p updated)
        (h3-book-sums-prepare-addend library step arg index)
      updated)))

(mutual-recursion
 (defun h3-book-sums-book-sums-prepare (sums term evidence)
   (declare (xargs :measure (acl2-count term)))
   (let* ((library (h3-book-sums-book-sums-lib sums))
          (proof (library-library-proof library)))
     (proof-with-checked-results ((step (proof-proof-reflexive proof term)))
       (cond
        ((proof-is-call term *h3-book-arithmetic-fix*)
         (h3-book-sums-prepare-fix sums term evidence step))
        ((and (consp term)
              (or (proof-is-call term *proof-plus*)
                  (proof-is-call term *proof-minus*)))
         (proof-with-checked-results
          ((step (h3-book-sums-prepare-children sums (cdr term) evidence 1 step)))
          (proof-proof-tidy proof step)))
        (t
         (proof-with-checked-results ((numeric (h3-book-sums-book-sums-type-of sums term evidence)))
           step))))))
 (defun h3-book-sums-prepare-children (sums args evidence index step)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       step
     (let* ((arg (car args))
            (child (h3-book-sums-book-sums-prepare sums arg evidence))
            (library (h3-book-sums-book-sums-lib sums)))
       (proof-with-checked-results ((step (h3-book-sums-prepare-child library step child arg index)))
         (h3-book-sums-prepare-children sums (cdr args) evidence (1+ index) step))))))

(defun h3-book-sums-linear-remove-zero (sums step name term place evidence)
  (let ((library (h3-book-sums-book-sums-lib sums)))
    (proof-with-checked-results
     ((type-step (h3-book-sums-book-sums-type-of sums term evidence))
      (zero-step (h3-numeric-order-cite library name (list term) (list type-step))))
     (proof-proof-rewrite (library-library-proof library) step zero-step place))))

(defun h3-book-sums-linear-combine-pair (sums a b)
  (if (and (proof-is-call a *proof-quote*) (proof-is-call b *proof-quote*))
      (h3-book-sums-book-sums-constant sums (library-plus a b))
    (library-linear-combine-pair (h3-book-sums-book-sums-lib sums) a b)))

(defun h3-book-sums-linear-combine (n sums step place evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "h3-book-sums-linear-combine")
    (let* ((library (h3-book-sums-book-sums-lib sums))
           (proof (library-library-proof library)))
      (proof-with-checked-results
       ((first (proof-step-first step))
        (node (library-linear-form-get first (cdr place))))
       (if (not (proof-is-call node *proof-plus*))
           (proof-proof-tidy proof step)
         (proof-with-checked-results ((pair (proof-list-of-length (cdr node) 2)))
           (let* ((a (car pair))
                  (rest (cadr pair))
                  (suffix (proof-is-call rest *proof-plus*)))
             (proof-with-checked-results ((b (if suffix (proof-term-at rest 1) rest)))
               (cond
                ((equal a *proof-zero*)
                 (proof-with-checked-results
                  ((step (h3-book-sums-linear-remove-zero sums step "ADD-ZERO-LEFT"
                                                        rest place evidence)))
                  (h3-book-sums-linear-combine (1- n) sums step place evidence)))
                ((and (equal b *proof-zero*) (not suffix))
                 (proof-with-checked-results
                  ((step (h3-book-sums-linear-remove-zero sums step "ADD-ZERO-RIGHT"
                                                        a place evidence)))
                  (h3-book-sums-linear-combine (1- n) sums step place evidence)))
                (t
                 (proof-with-checked-results ((combine (h3-book-sums-linear-combine-pair sums a b)))
                   (if (not combine)
                       (h3-book-sums-linear-combine (1- n) sums step (append place '(2)) evidence)
                     (proof-with-checked-results
                      ((step (if suffix
                                 (proof-with-checked-results
                                  ((tail (proof-term-at rest 2))
                                   (assoc-step (library-library-axiom library "ASSOCIATIVITY-OF-+"
                                                                      (list a b tail)))
                                   (symmetric (proof-proof-symmetric proof assoc-step)))
                                  (proof-proof-rewrite proof step symmetric place))
                               step))
                       (step (proof-proof-rewrite proof step combine
                                                  (if suffix (append place '(1)) place))))
                      (h3-book-sums-linear-combine (1- n) sums step '(1 2) evidence))))))))))))))

(defun h3-book-sums-book-sums-linear-form (sums term evidence)
  (let* ((library (h3-book-sums-book-sums-lib sums))
         (proof (library-library-proof library)))
    (proof-with-checked-results
     ((step (h3-book-sums-book-sums-push-minus 1000000 sums term evidence))
      (step (if step step (proof-proof-reflexive proof term)))
      (step (library-linear-reassociate 1000000 library step '(1 2)))
      (step (library-linear-sort 1000000 library step '(1 2) nil)))
     (h3-book-sums-linear-combine 1000000 sums step '(1 2) evidence))))

(defun h3-book-sums-book-sums-linear-equal (sums left right evidence)
  (let ((proof (library-library-proof (h3-book-sums-book-sums-lib sums))))
    (proof-with-checked-results
     ((a (h3-book-sums-book-sums-linear-form sums left evidence))
      (b (h3-book-sums-book-sums-linear-form sums right evidence))
      (a-normal (h3-book-sums-step-argument a 2))
      (b-normal (h3-book-sums-step-argument b 2)))
     (if (equal a-normal b-normal)
         (proof-with-checked-results ((symmetric (proof-proof-symmetric proof b)))
           (proof-proof-chain proof a (list symmetric)))
       '(:failure "failure" "")))))

(defun h3-book-sums-book-sums-sum-form (sums term evidence)
  (let ((proof (library-library-proof (h3-book-sums-book-sums-lib sums))))
    (proof-with-checked-results
     ((step (h3-book-sums-book-sums-prepare sums term evidence))
      (right (h3-book-sums-step-argument step 2))
      (normalized (h3-book-sums-book-sums-linear-form sums right evidence)))
     (proof-proof-chain proof step (list normalized)))))

(defun h3-book-sums-lemmas-fixed (library test numeric normal zero)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((yes (library-library-transport-argument library numeric normal 1))
      (zero-type (h3-book-arithmetic-typed-number library *proof-zero*))
      (no (library-library-transport-argument library zero-type zero 1))
      (typed (proof-proof-cases proof test yes no))
      (claim (proof-step-first typed)))
     (library-library-lemma library *h3-book-sums-fixed* claim typed nil))))

(defun h3-book-sums-lemmas-fix-operation (library label term test other normal zero)
  (let ((proof (library-library-proof library))
        (addition (equal label *h3-book-sums-add*)))
    (proof-with-checked-results
     ((fixed (proof-proof-reflexive proof term))
      (normal-back (proof-proof-symmetric proof normal))
      (yes (proof-proof-rewrite proof fixed normal-back '(1 2 1)))
      (default (if addition
                   (library-library-axiom library "DEFAULT-+-1" (list *library-x* *library-y*))
                 (library-library-axiom library "DEFAULT-UNARY-MINUS" (list *library-x*))))
      (default (proof-proof-modus-ponens proof default other))
      (reduced (if addition
                   (library-library-axiom library "UNICITY-OF-0" (list *library-y*))
                 (proof-proof-compute proof (library-minus *proof-zero*) 0)))
      (fixed-x (list *h3-book-arithmetic-fix* *library-x*))
      (target (if addition
                  (library-plus fixed-x *library-y*)
                (library-minus fixed-x)))
      (replacement (proof-proof-reflexive proof target))
      (replacement (proof-proof-rewrite proof replacement zero '(1 2 1)))
      (replacement (proof-proof-chain proof replacement (list reduced)))
      (replacement (proof-proof-symmetric proof replacement))
      (no (proof-proof-chain proof default (list replacement)))
      (claim (proof-step-first yes))
      (step (proof-proof-cases proof test yes no)))
     (library-library-lemma library label claim step nil))))

(defun h3-book-sums-lemmas-double (library)
  (let* ((proof (library-library-proof library))
         (x *library-x*)
         (opposite (library-minus x)))
    (proof-with-checked-results
     ((swap (library-library-axiom library "COMMUTATIVITY-OF-+" (list opposite x)))
      (inverse (library-library-axiom library "INVERSE-OF-+" (list x)))
      (sum-zero (proof-proof-chain proof swap (list inverse)))
      (step (h3-book-sums-inverse-unique library opposite x sum-zero))
      (step (proof-proof-symmetric proof step))
      (claim (proof-step-first step)))
     (library-library-lemma library *h3-book-sums-double* claim step nil))))

(defun h3-book-sums-lemmas-negate (library)
  (let* ((proof (library-library-proof library))
         (term (library-plus *library-x* *library-y*))
         (other (library-plus (library-minus *library-x*) (library-minus *library-y*))))
    (proof-with-checked-results
     ((sums (h3-numeric-order-numeric-sums-init library))
      (sum-zero (h3-numeric-order-numeric-sums-linear-equal
                 sums (library-plus term other) *proof-zero* nil))
      (step (h3-book-sums-inverse-unique library term other sum-zero))
      (other-type (h3-book-arithmetic-typed-number library other))
      (fixed (h3-book-arithmetic-fix-value library other other-type))
      (step (proof-proof-rewrite proof step fixed '(1 1)))
      (step (proof-proof-tidy proof step))
      (distributed (proof-proof-symmetric proof step))
      (claim (proof-step-first distributed)))
     (library-library-lemma library *h3-book-sums-negate* claim distributed nil))))

(defmacro h3-book-sums-extend-library (library form rest)
  `(let ((extension ,form))
     (if (failure-p extension)
         (cons extension ,library)
       (let ((,library extension))
         ,rest))))

(defun h3-book-sums-lemmas-with-fixed-arguments (library test numeric other)
  (let ((normal-and-zero
         (proof-with-checked-results
          ((normal (h3-book-arithmetic-fix-value library *library-x* numeric))
           (zero (h3-book-arithmetic-fix-value library *library-x* other)))
          (list normal zero))))
    (if (failure-p normal-and-zero)
        (cons normal-and-zero library)
      (let ((normal (car normal-and-zero))
            (zero (cadr normal-and-zero)))
        (h3-book-sums-extend-library library
         (h3-book-sums-lemmas-fixed library test numeric normal zero)
         (h3-book-sums-extend-library library
          (h3-book-sums-lemmas-fix-operation library *h3-book-sums-add*
                                            (library-plus *library-x* *library-y*)
                                            test other normal zero)
          (h3-book-sums-extend-library library
           (h3-book-sums-lemmas-fix-operation library *h3-book-sums-add-inv*
                                             (library-minus *library-x*)
                                             test other normal zero)
           (h3-book-sums-extend-library library
            (h3-book-sums-lemmas-double library)
            (h3-book-sums-extend-library library
             (h3-book-sums-lemmas-negate library)
             (cons nil library))))))))))

(defun h3-book-sums-lemmas-with-library (library)
  (if (assoc-equal (library-lemma-name *h3-book-sums-negate*)
                   (proof-proof-facts (library-library-proof library)))
      (cons nil library)
    (h3-book-sums-extend-library library (h3-merges-arithmetic library)
     (let* ((test (list *library-numberp* *library-x*))
            (proof (library-library-proof library))
            (assumptions
             (proof-with-checked-results
              ((numeric (proof-proof-assume proof test t))
               (other (proof-proof-assume proof test nil)))
              (list numeric other))))
       (if (failure-p assumptions)
           (cons assumptions library)
         (let ((numeric (car assumptions))
               (other (cadr assumptions)))
           (h3-book-sums-extend-library library (h3-numeric-order-add-zero library numeric)
             (h3-book-sums-lemmas-with-fixed-arguments library test numeric other))))))))

(defun h3-book-sums-lemmas (library)
  (let ((result (h3-book-sums-lemmas-with-library library)))
    (if (failure-p (car result))
        (car result)
      (cdr result))))

(defun h3-book-sums-cancel-comparison (library sums p q evidence)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((left (library-library-axiom library "<-ON-OTHERS" (cdr p)))
      (right (library-library-axiom library "<-ON-OTHERS" (cdr q)))
      (left-comparison (h3-book-sums-step-argument left 2))
      (left-term (proof-term-at left-comparison 1))
      (left-form (h3-book-sums-book-sums-sum-form sums left-term evidence))
      (left (proof-proof-rewrite proof left left-form '(1 2 1)))
      (right-comparison (h3-book-sums-step-argument right 2))
      (right-term (proof-term-at right-comparison 1))
      (right-form (h3-book-sums-book-sums-sum-form sums right-term evidence))
      (right (proof-proof-rewrite proof right right-form '(1 2 1)))
      (left-result (h3-book-sums-step-argument left 2))
      (right-result (h3-book-sums-step-argument right 2)))
     (if (equal left-result right-result)
         (proof-with-checked-results ((right-back (proof-proof-symmetric proof right)))
           (proof-proof-chain proof left (list right-back)))
       *h3-rewrite-unproved*))))

(defun h3-book-sums-numeric-evidence (term numeric)
  (let ((entry (assoc-equal term numeric)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun h3-book-sums-cancel-equalities-transfer (step source target library numeric)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((literal (proof-step-first step))
      (pair (proof-list-of-length (cdr literal) 2))
      (y (cadr pair))
      (difference (h3-book-sums-step-argument target 1))
      (i (proof-term-at difference 1))
      (negative-j (proof-term-at difference 2))
      (j (proof-term-at negative-j 1))
      (inverse-y (library-library-axiom library "INVERSE-OF-+" (list y)))
      (back (proof-proof-symmetric proof step))
      (zero (proof-proof-rewrite proof inverse-y back '(1 1 1)))
      (zero (proof-proof-rewrite proof zero source '(1 1)))
      (back (proof-proof-symmetric proof target))
      (zero (proof-proof-rewrite proof zero back '(1 1)))
      (inverse-j (library-library-axiom library "INVERSE-OF-+" (list j)))
      (back (proof-proof-symmetric proof inverse-j))
      (equation (proof-proof-chain proof zero (list back)))
      (step (h3-book-sums-cancel-addend library equation i j (library-minus j)))
      (numeric-i (h3-book-sums-numeric-evidence i numeric))
      (fixed-i (h3-book-arithmetic-fix-value library i numeric-i))
      (step (proof-proof-rewrite proof step fixed-i '(1 1)))
      (numeric-j (h3-book-sums-numeric-evidence j numeric))
      (fixed-j (h3-book-arithmetic-fix-value library j numeric-j))
      (step (proof-proof-rewrite proof step fixed-j '(1 2))))
     (proof-proof-tidy proof step))))

(defun h3-book-sums-cancel-equalities-forward (step library numeric left right reversep)
  (proof-with-checked-results
   ((result (h3-book-sums-cancel-equalities-transfer step left right library numeric)))
   (if reversep
       (proof-proof-symmetric (library-library-proof library) result)
     result)))

(defun h3-book-sums-cancel-equalities-backward (step library numeric left right reversep)
  (proof-with-checked-results
   ((step (if reversep
              (proof-proof-symmetric (library-library-proof library) step)
            step)))
   (h3-book-sums-cancel-equalities-transfer step right left library numeric)))

(defun h3-book-sums-type-operands (sums args evidence numeric)
  (if (endp args)
      numeric
    (proof-with-checked-results
     ((step (h3-book-sums-book-sums-type-of sums (car args) evidence)))
     (h3-book-sums-type-operands sums (cdr args) evidence
                                (table-put numeric (car args) step)))))

(defun h3-book-sums-cancel-equalities (library sums p q evidence)
  (proof-with-checked-results
   ((p-args (proof-list-of-length (cdr p) 2))
    (q-args (proof-list-of-length (cdr q) 2))
    (numeric (h3-book-sums-type-operands sums (append p-args q-args) evidence nil))
    (left (h3-book-sums-book-sums-sum-form sums (library-diff (car p-args) (cadr p-args))
                                         evidence))
    (right (h3-book-sums-book-sums-sum-form sums (library-diff (car q-args) (cadr q-args))
                                          evidence))
    (left-result (h3-book-sums-step-argument left 2))
    (right-result (h3-book-sums-step-argument right 2))
    (reversep (not (equal left-result right-result)))
    (right (if reversep
               (h3-book-sums-book-sums-sum-form sums (library-diff (cadr q-args) (car q-args))
                                               evidence)
             right))
    (right-result (h3-book-sums-step-argument right 2)))
   (if (equal left-result right-result)
       (h3-book-arithmetic-with-equivalent-equalities
        library p q
        (h3-book-sums-cancel-equalities-forward library numeric left right reversep)
        (h3-book-sums-cancel-equalities-backward library numeric left right reversep))
     *h3-rewrite-unproved*)))

(defun h3-book-sums-conditional-equality-test (library sums p rhs test consequent evidence)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
     ((first (h3-book-sums-cancel-equalities library sums p test evidence))
      (second (h3-book-sums-cancel-equalities library sums p consequent evidence))
      (target (proof-proof-reflexive proof rhs))
      (back (proof-proof-symmetric proof first))
      (target (proof-proof-rewrite proof target back '(1 2 1)))
      (back (proof-proof-symmetric proof second))
      (target (proof-proof-rewrite proof target back '(1 2 2)))
      (right (h3-book-sums-step-argument target 2))
      (search (h3-rewrite-search-init library nil nil nil 150 nil))
      (reduced (car (h3-rewrite-search-prove search (proof-eq p right) evidence))))
     (library-library-transport-argument library reduced target 2))))

(defun h3-book-sums-conditional-equality-number (library sums p rhs test consequent evidence)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results ((operand (proof-term-at test 1)))
      (if (not (member-equal operand (cdr p)))
          *h3-rewrite-unproved*
        (proof-with-checked-results
         ((known (proof-proof-assume proof test t))
          (unknown (proof-proof-assume proof test nil))
          (explained (h3-book-sums-cancel-equalities library sums p consequent
                                                   (append evidence (list known))))
          (if-true (proof-proof-if-true proof rhs))
          (yes (library-library-transport-argument library explained if-true 2))
          (first (proof-term-at p 1))
          (index (if (equal first operand) 2 1))
          (other-term (proof-term-at p index))
          (other (h3-book-sums-book-sums-type-of sums other-term evidence))
          (equation (proof-proof-assume proof p t))
          (equation (if (equal index 2) (proof-proof-symmetric proof equation) equation))
          (rewritten (proof-proof-rewrite proof other equation '(1 1)))
          (contradiction (proof-proof-cut proof rewritten unknown))
          (impossible (proof-proof-front proof contradiction (proof-neg p)))
          (no (h3-rewrite-nil-value library impossible))
          (if-false (proof-proof-if-false proof rhs))
          (no (library-library-transport-argument library no if-false 2)))
         (proof-proof-cases proof test yes no))))))

(defun h3-book-sums-conditional-equality (library sums p rhs evidence)
  (proof-with-checked-results ((parts (proof-list-of-length (cdr rhs) 3)))
    (let ((test (car parts))
          (consequent (cadr parts))
          (alternative (caddr parts)))
      (cond
       ((not (and (equal alternative *proof-false*)
                  (proof-is-call p *proof-equal*)
                  (proof-is-call consequent *proof-equal*)))
        *h3-rewrite-unproved*)
       ((proof-is-call test *proof-equal*)
        (h3-book-sums-conditional-equality-test library sums p rhs test consequent evidence))
       ((proof-is-call test *library-numberp*)
        (h3-book-sums-conditional-equality-number library sums p rhs test consequent evidence))
       (t *h3-rewrite-unproved*)))))

(defun h3-book-sums-additive-terms-p (terms)
  (and (consp terms)
       (or (proof-is-call (car terms) *proof-plus*)
           (proof-is-call (car terms) *proof-minus*)
           (h3-book-sums-additive-terms-p (cdr terms)))))

(defun h3-book-sums-additive-has-shape (formula)
  (proof-with-checked-results
   ((target (if (proof-is-call formula *library-implies*)
                (proof-term-at formula 2)
              formula)))
   (and (proof-is-call target *proof-equal*)
        (proof-with-checked-results ((pair (proof-list-of-length (cdr target) 2)))
          (let ((p (car pair))
                (q (cadr pair)))
            (h3-book-sums-additive-terms-p
             (if (or (proof-is-call p *proof-equal*) (proof-is-call p *proof-less*))
                 (if (proof-is-call q (car p)) (append (cdr p) (cdr q)) (cdr p))
               pair)))))))

(defun h3-book-sums-additive-normal-forms (library sums p q evidence)
  (proof-with-checked-results
   ((left (h3-book-sums-book-sums-sum-form sums p evidence))
    (right (h3-book-sums-book-sums-sum-form sums q evidence))
    (left-result (h3-book-sums-step-argument left 2))
    (right-result (h3-book-sums-step-argument right 2)))
   (if (equal left-result right-result)
       (let ((proof (library-library-proof library)))
         (proof-with-checked-results ((back (proof-proof-symmetric proof right)))
           (proof-proof-chain proof left (list back))))
     *h3-rewrite-unproved*)))

(defun h3-book-sums-additive-proof (library guard p q)
  (let ((guarded (and guard (not (equal guard 0)) (not (equal guard "")))))
    (proof-with-checked-results
     ((sums (h3-book-sums-book-sums-init library))
      (evidence
       (and guarded
            (proof-with-checked-results
             ((assumption (proof-proof-assume (library-library-proof library) guard t))
              (context (h3-rewrite-search-context (h3-book-sums-book-sums-search sums)
                                                 (list assumption))))
             (table-values context))))
      (step
       (cond
        ((and (proof-is-call p *proof-less*) (proof-is-call q *proof-less*))
         (h3-book-sums-cancel-comparison library sums p q evidence))
        ((and (proof-is-call p *proof-equal*) (proof-is-call q *proof-equal*))
         (h3-book-sums-cancel-equalities library sums p q evidence))
        ((proof-is-call q *proof-if*)
         (h3-book-sums-conditional-equality library sums p q evidence))
        (t (h3-book-sums-additive-normal-forms library sums p q evidence)))))
     (if guarded
         (h3-rewrite-implication library guard step)
       step))))

(defun h3-book-sums-additive-theorem-with-library (library formula)
  (let ((parts
         (proof-with-checked-results
          ((target (if (proof-is-call formula *library-implies*)
                       (proof-list-of-length (cdr formula) 2)
                     (list nil formula)))
           (shape (h3-book-sums-additive-has-shape formula)))
          (and shape
               (proof-with-checked-results ((pair (proof-list-of-length (cdr (cadr target)) 2)))
                 (cons (car target) pair))))))
    (cond
     ((or (not parts) (failure-p parts)) (cons parts library))
     (t
      (let* ((lemmas (h3-book-sums-lemmas-with-library library))
             (result (car lemmas))
             (library (cdr lemmas)))
        (if (failure-p result)
            lemmas
          (cons (h3-book-sums-additive-proof library (car parts) (cadr parts) (caddr parts))
                library)))))))

(defun h3-book-sums-additive-theorem (library formula)
  (let ((result (h3-book-sums-additive-theorem-with-library library formula)))
    (if (failure-p (car result))
        (car result)
      result)))
