(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-arithmetic-two* (proof-quote 2))

(defun t3-arithmetic-double (term)
  (list *proof-times* *t3-arithmetic-two* term))

(defund t3-arithmetic-step-term (step index)
  (proof-with-checked-results ((first (proof-step-first step)))
    (proof-term-at first index)))

(defun t3-arithmetic-double-lemma (lib ix)
  (let ((proof (library-library-proof lib))
        (x *library-x*)
        (one *proof-one*))
    (proof-with-checked-results
        ((expand (library-library-axiom lib "COMMUTATIVITY-OF-*" (list *t3-arithmetic-two* x)))
         (compute (proof-proof-compute proof (library-plus one one) 2))
         (two-as-sum (proof-proof-symmetric proof compute))
         (expand (proof-proof-rewrite proof expand two-as-sum '(1 2 2)))
         (distribute (library-library-axiom lib "DISTRIBUTIVITY" (list x one one)))
         (expand (proof-proof-chain proof expand (list distribute)))
         (unit (library-library-axiom lib "UNICITY-OF-1" (list x)))
         (unit-term (t3-arithmetic-step-term unit 2))
         (number (t3-logic-libraryproofs-number lib x (list ix)))
         (head (proof-term-at unit-term 0))
         (simple (t3-logic-libraryproofs-simplify lib unit-term (list number) (list head)))
         (unit (proof-proof-chain proof unit (list simple)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list x one)))
         (unit (proof-proof-chain proof commute (list unit)))
         (expand (proof-proof-rewrite proof expand unit '(1 2 1)))
         (expand (proof-proof-rewrite proof expand unit '(1 2 2))))
      (library-library-lemma lib "T3-DOUBLE"
                            (proof-eq (t3-arithmetic-double x) (library-plus x x))
                            expand (list (proof-neg (library-integer x)))))))

(defun t3-arithmetic-natural-double-lemma (lib)
  (let ((proof (library-library-proof lib))
        (x *library-x*))
    (proof-with-checked-results
        ((natural (proof-proof-assume proof (list *library-natp* x) t))
         (integer (library-library-cite lib "NATURAL-INTEGER" (list x) (list natural)))
         (doubled (library-library-cite lib "T3-DOUBLE" (list x) (list integer)))
         (sum-nat (library-library-cite lib "NATURAL-SUM" (list x x) (list natural)))
         (transported (library-library-transport-argument lib sum-nat doubled 1))
         (literal (proof-step-first natural)))
      (library-library-lemma lib "T3-NATURAL-DOUBLE" (list *library-natp* (t3-arithmetic-double x))
                            transported (list (proof-neg literal))))))

(defun t3-arithmetic-one-below-lemma (lib ix)
  (let ((proof (library-library-proof lib))
        (x *library-x*))
    (proof-with-checked-results
        ((strict (proof-proof-assume proof (library-positive x) t))
         (discrete (proof-proof-fact proof "integer-discrete" nil))
         (test (t3-arithmetic-step-term discrete 1))
         (premise (t3-logic-libraryproofs-prove lib test (list ix strict) nil))
         (bound (proof-proof-modus-ponens proof discrete premise))
         (shifted (library-library-axiom lib "<-ON-OTHERS" (list x *proof-one*)))
         (bound (proof-proof-rewrite proof bound shifted '(1 1))))
      (library-library-lemma lib "T3-ONE-BELOW" (library-nonnegative (library-diff x *proof-one*))
                            bound (list (proof-neg (library-integer x))
                                        (proof-neg (library-positive x)))))))

(defun t3-arithmetic-positive-from-nonzero-lemma (lib ix)
  (let ((proof (library-library-proof lib))
        (x *library-x*)
        (zero *proof-zero*))
    (proof-with-checked-results
        ((axiom (library-library-axiom lib "TRICHOTOMY" (list x)))
         (tri (proof-proof-conjunct proof axiom))
         (no-zero (proof-proof-assume proof (proof-eq x zero) nil))
         (no-positive (proof-proof-assume proof (library-positive x) nil))
         (no-negative (proof-proof-assume proof (library-lt x zero) nil))
         (number (t3-logic-libraryproofs-number lib x (list ix)))
         (trichotomy (proof-proof-modus-ponens proof (car tri) number))
         (negative (t3-logic-libraryproofs-simplify-first lib trichotomy (list no-zero no-positive)
                                                         (list *proof-not*)))
         (compare (library-library-comparison lib x zero (list ix)))
         (identity (library-library-linear-equal lib (library-diff zero x) (library-minus x)
                                                (list ix)))
         (compare (proof-proof-rewrite proof compare identity '(1 2 2)))
         (negative (proof-proof-transport proof negative compare))
         (contradiction (proof-proof-cut proof negative no-negative))
         (conclusion (proof-proof-front proof contradiction (library-positive x))))
      (library-library-lemma lib "T3-POSITIVE-FROM-NONZERO" (library-positive x) conclusion
                            (list (proof-neg (library-integer x))
                                  (library-lt x zero) (proof-eq x zero))))))

(defun t3-arithmetic-build (lib)
  (proof-with-checked-results
      ((ints (library-library-ints lib (list *library-x*)))
       (lib (t3-arithmetic-double-lemma lib (car ints)))
       (lib (t3-arithmetic-natural-double-lemma lib))
       (lib (t3-arithmetic-one-below-lemma lib (car ints))))
    (t3-arithmetic-positive-from-nonzero-lemma lib (car ints))))

(defun t3-arithmetic-increment-coefficient (result atom increment)
  (table-put result atom (+ (table-get result atom 0) increment)))

(defun t3-arithmetic-quoted-coefficient (value weight result)
  (cond ((acl2-numberp value)
         (t3-arithmetic-increment-coefficient result *proof-zero* (* value weight)))
        ((eq value t)
         (t3-arithmetic-increment-coefficient result *proof-zero* weight))
        ((stringp value)
         '(:failure "failure" ""))
        (t '(:failure "failure" ""))))

(defun t3-arithmetic-coefficients-collect (expression weight result)
  (declare (xargs :measure (acl2-count expression)))
  (cond
   ((proof-is-call expression *proof-plus*)
    (cond ((not (consp (cdr expression))) (proof-term-at expression 1))
          (t (proof-with-checked-results
                 ((result (t3-arithmetic-coefficients-collect (cadr expression) weight result)))
               (if (consp (cddr expression))
                   (t3-arithmetic-coefficients-collect (caddr expression) weight result)
                 (proof-term-at expression 2))))))
   ((proof-is-call expression *proof-minus*)
    (if (consp (cdr expression))
        (t3-arithmetic-coefficients-collect (cadr expression) (- weight) result)
      (proof-term-at expression 1)))
   ((and (proof-is-call expression *proof-times*) (not (consp (cdr expression))))
    (proof-term-at expression 1))
   ((and (proof-is-call expression *proof-times*) (equal (cadr expression) *t3-arithmetic-two*))
    (if (consp (cddr expression))
        (t3-arithmetic-coefficients-collect (caddr expression) (* weight 2) result)
      (proof-term-at expression 2)))
   ((proof-is-call expression *proof-quote*)
    (proof-with-checked-results ((value (proof-term-at expression 1)))
      (t3-arithmetic-quoted-coefficient value weight result)))
   (t (t3-arithmetic-increment-coefficient result expression weight))))

(defun t3-arithmetic-nonzero-coefficients (coefficients)
  (cond ((endp coefficients) nil)
        ((equal (cdar coefficients) 0) (t3-arithmetic-nonzero-coefficients (cdr coefficients)))
        (t (cons (car coefficients) (t3-arithmetic-nonzero-coefficients (cdr coefficients))))))

(defun t3-arithmetic-coefficients (term)
  (proof-with-checked-results ((result (t3-arithmetic-coefficients-collect term 1 nil)))
    (t3-arithmetic-nonzero-coefficients result)))

(defun t3-arithmetic-type-of (lib term integers)
  (t3-logic-libraryproofs-type-of lib term integers))

(defun t3-arithmetic-negation-types (lib terms integers)
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((step (t3-arithmetic-type-of lib (car terms) integers))
         (rest (t3-arithmetic-negation-types lib (cdr terms) integers)))
      (cons step rest))))

(defund t3-arithmetic-negation-rule (lib argument integers)
  (let ((facts (proof-proof-facts (library-library-proof lib))))
    (cond
     ((and (proof-is-call argument *proof-minus*)
           (assoc-equal (proof-sym "SELF-DOUBLE-NEGATION" "ACL2") facts))
      (proof-with-checked-results ((body (proof-term-at argument 1))
                                   (type-step (t3-arithmetic-type-of lib body integers)))
        (library-library-cite lib "DOUBLE-NEGATION" (list body) (list type-step))))
     ((and (proof-is-call argument *proof-plus*)
           (assoc-equal (proof-sym "SELF-NEGATE-SUM" "ACL2") facts))
      (proof-with-checked-results ((steps (t3-arithmetic-negation-types lib (cdr argument) integers)))
        (library-library-cite lib "NEGATE-SUM" (cdr argument) steps)))
     (t nil))))

(defund t3-arithmetic-minus-sum-left (proof term)
  (proof-with-checked-results ((result (proof-proof-reflexive proof term))
                               (left (proof-term-at term 1)))
    (cons result left)))

(defund t3-arithmetic-minus-sum-right (proof term result step)
  (proof-with-checked-results
      ((result (if step (proof-proof-rewrite proof result step '(1 2 1)) result))
       (right (proof-term-at term 2)))
    (cons result right)))

(defund t3-arithmetic-minus-sum-finish (proof term result step)
  (proof-with-checked-results
      ((result (if step (proof-proof-rewrite proof result step '(1 2 2)) result))
       (next (t3-arithmetic-step-term result 2)))
    (and (not (equal next term)) result)))

(defund t3-arithmetic-minus-next (lib term integers)
  (proof-with-checked-results ((argument (proof-term-at term 1)))
    (if (proof-is-call argument *proof-quote*)
        (proof-with-checked-results ((constant (t3-logic-libraryproofs-constant lib term)))
          (cons nil constant))
      (proof-with-checked-results
          ((step (t3-arithmetic-negation-rule lib argument integers))
           (next (and step (t3-arithmetic-step-term step 2))))
        (cons step next)))))

(defun t3-arithmetic-push-minus (n lib term integers)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t3-arithmetic-push-minus"))
     ((proof-is-call term *proof-plus*)
      (proof-with-checked-results
          ((left (t3-arithmetic-minus-sum-left proof term))
           (step (t3-arithmetic-push-minus (1- n) lib (cdr left) integers))
           (right (t3-arithmetic-minus-sum-right proof term (car left) step))
           (step (t3-arithmetic-push-minus (1- n) lib (cdr right) integers)))
        (t3-arithmetic-minus-sum-finish proof term (car right) step)))
     ((proof-is-call term *proof-minus*)
      (proof-with-checked-results ((next (t3-arithmetic-minus-next lib term integers)))
        (if (not (car next))
            (cdr next)
          (proof-with-checked-results
              ((rest (t3-arithmetic-push-minus (1- n) lib (cdr next) integers)))
            (proof-proof-chain proof (car next) (list rest))))))
     (t nil))))

(defun t3-arithmetic-linear-remove-zero (lib step name term place integers)
  (proof-with-checked-results
      ((type-step (t3-arithmetic-type-of lib term integers))
       (zero-step (library-library-cite lib name (list term) (list type-step))))
    (proof-proof-rewrite (library-library-proof lib) step zero-step place)))

(defun t3-arithmetic-linear-combine-pair (lib left right)
  (if (and (proof-is-call left *proof-quote*) (proof-is-call right *proof-quote*))
      (t3-logic-libraryproofs-constant lib (library-plus left right))
    (library-linear-combine-pair lib left right)))

(defun t3-arithmetic-linear-reassociate-pair (lib step place left right rest)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((tail (proof-term-at rest 2))
         (association (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list left right tail)))
         (symmetric (proof-proof-symmetric proof association)))
      (proof-proof-rewrite proof step symmetric place))))

(defun t3-arithmetic-linear-next-pair (lib step place left rest integers)
  (let ((suffix (proof-is-call rest *proof-plus*)))
    (proof-with-checked-results ((right (if suffix (proof-term-at rest 1) rest)))
      (cond
       ((equal left *proof-zero*)
        (proof-with-checked-results
            ((step (t3-arithmetic-linear-remove-zero lib step "ADD-ZERO-LEFT" rest place integers)))
          (cons step place)))
       ((and (equal right *proof-zero*) (not suffix))
        (proof-with-checked-results
            ((step (t3-arithmetic-linear-remove-zero lib step "ADD-ZERO-RIGHT" left place integers)))
          (cons step place)))
       (t
        (proof-with-checked-results ((combine (t3-arithmetic-linear-combine-pair lib left right)))
          (if (not combine)
              (cons step (append place '(2)))
            (proof-with-checked-results
                ((step (if suffix
                           (t3-arithmetic-linear-reassociate-pair lib step place left right rest)
                         step))
                 (step (proof-proof-rewrite (library-library-proof lib) step combine
                                            (if suffix (append place '(1)) place))))
              (cons step '(1 2))))))))))

(defund t3-arithmetic-linear-next (lib step place integers)
  (proof-with-checked-results ((literal (proof-step-first step))
                               (node (library-linear-form-get literal (cdr place))))
    (and (proof-is-call node *proof-plus*)
         (proof-with-checked-results ((pair (proof-list-of-length (cdr node) 2)))
           (t3-arithmetic-linear-next-pair lib step place (car pair) (cadr pair) integers)))))

(defun t3-arithmetic-linear-combine (n lib step place integers)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t3-arithmetic-linear-combine")
    (proof-with-checked-results ((next (t3-arithmetic-linear-next lib step place integers)))
      (if next
          (t3-arithmetic-linear-combine (1- n) lib (car next) (cdr next) integers)
        (proof-proof-tidy (library-library-proof lib) step)))))

(defun t3-arithmetic-linear-form (lib term integers)
  (proof-with-checked-results
      ((step (t3-arithmetic-push-minus 1000000 lib term integers))
       (step (or step (proof-proof-reflexive (library-library-proof lib) term)))
       (step (library-linear-reassociate 1000000 lib step '(1 2)))
       (step (library-linear-sort 1000000 lib step '(1 2) nil)))
    (t3-arithmetic-linear-combine 1000000 lib step '(1 2) integers)))

(defun t3-arithmetic-linear-equal (lib left right integers)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((a (t3-arithmetic-linear-form lib left integers))
         (b (t3-arithmetic-linear-form lib right integers))
         (a-normal (t3-arithmetic-step-term a 2))
         (b-normal (t3-arithmetic-step-term b 2)))
      (if (equal a-normal b-normal)
          (proof-with-checked-results ((back (proof-proof-symmetric proof b)))
            (proof-proof-chain proof a (list back)))
        (proof-with-checked-results ((a-text (proof-write a-normal))
                                     (b-text (proof-write b-normal)))
          '(:failure "unproved" ""))))))

(defun t3-arithmetic-weak-from-difference (lib a b nonnegative-difference integers)
  (proof-with-checked-results
      ((compare (library-library-axiom lib "<-ON-OTHERS" (list b a)))
       (bound (t3-arithmetic-step-term nonnegative-difference 1))
       (term (proof-term-at bound 1))
       (delta (t3-arithmetic-linear-equal lib (library-diff b a) term integers))
       (compare (proof-proof-rewrite (library-library-proof lib) compare delta '(1 2 1))))
    (library-library-transport-argument lib nonnegative-difference compare 1)))

(defun t3-arithmetic-expand-current (lib current step integers)
  (let ((proof (library-library-proof lib)))
    (if (not (proof-is-call current *proof-times*))
        step
      (proof-with-checked-results ((scale (proof-term-at current 1)))
        (if (not (equal scale *t3-arithmetic-two*))
            step
          (proof-with-checked-results
              ((body (proof-term-at current 2))
               (integer (t3-arithmetic-type-of lib body integers))
               (expansion (library-library-cite lib "T3-DOUBLE" (list body) (list integer))))
            (if step (proof-proof-chain proof step (list expansion)) expansion)))))))

(mutual-recursion
 (defun t3-arithmetic-expand-doubles (lib term integers)
   (declare (xargs :measure (acl2-count term)))
   (if (or (atom term) (not (proof-compound term)) (proof-is-call term *proof-quote*))
       nil
     (proof-with-checked-results
         ((step (t3-arithmetic-expand-arguments lib term (cdr term) 1 nil integers))
          (current (if step (t3-arithmetic-step-term step 2) term)))
       (t3-arithmetic-expand-current lib current step integers))))

 (defun t3-arithmetic-expand-arguments (lib term args index step integers)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       step
     (let ((proof (library-library-proof lib)))
       (proof-with-checked-results
           ((expanded (t3-arithmetic-expand-doubles lib (car args) integers))
            (step (if expanded
                      (proof-with-checked-results
                          ((base (or step (proof-proof-reflexive proof term))))
                        (proof-proof-rewrite proof base expanded (list 1 2 index)))
                    step)))
         (t3-arithmetic-expand-arguments lib term (cdr args) (1+ index) step integers))))))

(defun t3-arithmetic-linear-identity-reduced (n term opened lib integers)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t3-arithmetic-linear-identity-reduced")
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((step (or opened (proof-proof-reflexive proof term)))
           (current (t3-arithmetic-step-term step 2))
           (pass-result (t3-arithmetic-linear-form lib current integers))
           (next (t3-arithmetic-step-term pass-result 2)))
        (if (equal next current)
            step
          (proof-with-checked-results ((chained (proof-proof-chain proof step (list pass-result))))
            (t3-arithmetic-linear-identity-reduced (1- n) term chained lib integers)))))))

(defun t3-arithmetic-linear-identity (lib left right integers)
  (let ((proof (library-library-proof lib)))
    (if (equal left right)
        (proof-proof-reflexive proof left)
      (proof-with-checked-results
          ((left-open (t3-arithmetic-expand-doubles lib left integers))
           (right-open (t3-arithmetic-expand-doubles lib right integers))
           (a (t3-arithmetic-linear-identity-reduced 1000000 left left-open lib integers))
           (b (t3-arithmetic-linear-identity-reduced 1000000 right right-open lib integers))
           (a-normal (t3-arithmetic-step-term a 2))
           (b-normal (t3-arithmetic-step-term b 2)))
        (if (equal a-normal b-normal)
            (proof-with-checked-results ((back (proof-proof-symmetric proof b)))
              (proof-proof-chain proof a (list back)))
          '(:failure "unsupported" ""))))))

(defun t3-arithmetic-term-keys (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results ((text (proof-write (car terms)))
                                 (rest (t3-arithmetic-term-keys (cdr terms))))
      (cons (cons text (car terms)) rest))))

(defun t3-arithmetic-insert-term-key (entry sorted)
  (if (or (endp sorted) (not (string< (caar sorted) (car entry))))
      (cons entry sorted)
    (cons (car sorted) (t3-arithmetic-insert-term-key entry (cdr sorted)))))

(defun t3-arithmetic-sort-term-keys (keyed-terms)
  (if (endp keyed-terms)
      nil
    (t3-arithmetic-insert-term-key (car keyed-terms)
                                  (t3-arithmetic-sort-term-keys (cdr keyed-terms)))))

(defun t3-arithmetic-sorted-terms (terms)
  (proof-with-checked-results ((keys (t3-arithmetic-term-keys terms)))
    (table-values (t3-arithmetic-sort-term-keys keys))))

(defun t3-arithmetic-known-integers (lib facts)
  (if (endp facts)
      nil
    (let ((term (caar facts))
          (step (cdar facts)))
      (proof-with-checked-results
          ((integer (cond ((proof-is-call term *proof-integerp*) step)
                          ((proof-is-call term *library-natp*)
                           (library-library-cite lib "NATURAL-INTEGER" (cdr term) (list step)))
                          (t nil)))
           (rest (t3-arithmetic-known-integers lib (cdr facts))))
        (if integer (cons integer rest) rest)))))

(defun t3-arithmetic-atoms (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results ((form (t3-arithmetic-coefficients (car terms)))
                                 (rest (t3-arithmetic-atoms (cdr terms))))
      (append (remove-equal *proof-zero* (table-keys form)) rest))))

(defun t3-arithmetic-inferred-integers (evidence atoms)
  (declare (xargs :measure (acl2-count atoms)))
  (if (endp atoms)
      (cons nil evidence)
    (proof-with-checked-results
        ((first (t3-logic-evidence-integer evidence (car atoms)))
         (rest (t3-arithmetic-inferred-integers (cdr first) (cdr atoms))))
      (cons (cons (car first) (car rest)) (cdr rest)))))

(defun t3-arithmetic-integer-facts (evidence terms)
  (proof-with-checked-results
      ((evidence (t3-logic-evidence-expand evidence))
       (known (t3-arithmetic-known-integers (t3-logic-evidence-lib evidence)
                                          (t3-logic-evidence-facts evidence)))
       (atoms (t3-arithmetic-atoms terms))
       (sorted (t3-arithmetic-sorted-terms (proof-unique atoms)))
       (inferred (t3-arithmetic-inferred-integers evidence sorted)))
    (cons (append known (car inferred)) (cdr inferred))))

(defun t3-arithmetic-recoverable-failure-p (result)
  (and (failure-p result) (member-equal (cadr result) '("unproved" "unsupported" "value"))))

(defmacro t3-arithmetic-with-evidence (evidence bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (failure-p ,name)
             (cons ,name ,evidence)
           (t3-arithmetic-with-evidence ,evidence ,(cdr bindings) ,result))))))

; Evidence records an assumption before normalizing it. A candidate that
; handles a failure retains the facts recorded up to the failing operation.
(mutual-recursion
 (defun t3-arithmetic-record-with-evidence (n evidence term holds step)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "fuel" "t3-arithmetic-record-with-evidence") evidence)
     (t3-arithmetic-with-evidence evidence
         ((updated (t3-logic-evidence-default evidence step)))
       (let ((result (if (proof-is-call term *proof-if*)
                         (t3-arithmetic-conditional-with-evidence (1- n) updated term holds step)
                       (cons nil updated))))
         (if (car result)
             result
           (t3-arithmetic-record-normalized (1- n) (cdr result) term holds step))))))

 (defun t3-arithmetic-conditional-with-evidence (n evidence term holds step)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "fuel" "t3-arithmetic-conditional-with-evidence") evidence)
     (t3-arithmetic-with-evidence evidence
         ((branches (proof-list-of-length (cdr term) 3)))
       (let* ((test (car branches))
              (yes (cadr branches))
              (no (caddr branches))
              (impossible (if holds *proof-false* *proof-true*))
              (branch (equal no impossible)))
         (if (or branch (equal yes impossible) (and (not holds) (equal yes test)))
             (t3-arithmetic-record-selected (1- n) evidence term holds step
                                            test branch (if branch yes no))
           (cons nil evidence))))))

 (defun t3-arithmetic-record-selected (n evidence term holds step test branch selected)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "fuel" "t3-arithmetic-record-selected") evidence)
     (let* ((lib (t3-logic-evidence-lib evidence))
            (proof (library-library-proof lib)))
       (t3-arithmetic-with-evidence evidence
           ((guard (t3-logic-evidence-conditional-guard lib term holds step test branch)))
         (let ((recorded (t3-arithmetic-record-with-evidence (1- n) evidence test branch guard)))
           (if (failure-p (car recorded))
               recorded
             (let ((evidence (cdr recorded)))
               (t3-arithmetic-with-evidence evidence
                   ((selected-proof (t3-logic-evidence-conditional-proof proof term holds step guard)))
                 (if (and (equal selected test) (equal holds branch))
                     (cons t evidence)
                   (let ((recorded (t3-arithmetic-record-with-evidence (1- n) evidence selected
                                                                     holds selected-proof)))
                     (if (failure-p (car recorded)) recorded (cons t (cdr recorded)))))))))))))

 (defun t3-arithmetic-record-normalized (n evidence term holds step)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "fuel" "t3-arithmetic-record-normalized") evidence)
     (let ((lib (t3-logic-evidence-lib evidence))
           (definitions (t3-logic-evidence-definitions evidence)))
       (t3-arithmetic-with-evidence evidence
           ((equation (t3-logic-libraryproofs-normalize lib term nil definitions))
            (right (and equation (t3-arithmetic-step-term equation 2))))
         (if (and equation (not (equal right term)))
             (t3-arithmetic-with-evidence evidence
                 ((rewritten (t3-logic-evidence-rewrite-test (library-library-proof lib)
                                                            step equation holds)))
               (t3-arithmetic-record-with-evidence (1- n) evidence right holds rewritten))
           (t3-arithmetic-record-related (1- n) evidence term holds step))))))

 (defun t3-arithmetic-record-related (n evidence term holds step)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "fuel" "t3-arithmetic-record-related") evidence)
     (let ((lib (t3-logic-evidence-lib evidence)))
       (t3-arithmetic-with-evidence evidence
           ((cons-proof (t3-logic-evidence-selector-proof lib term holds step))
            (literal (and cons-proof (proof-step-first cons-proof))))
         (let ((recorded (if cons-proof
                             (t3-arithmetic-record-with-evidence (1- n) evidence literal t cons-proof)
                           (cons nil evidence))))
           (if (or (failure-p (car recorded)) (not (proof-is-call term *proof-not*)))
               recorded
             (let ((evidence (cdr recorded)))
               (t3-arithmetic-with-evidence evidence
                   ((opposite (if holds step (t3-logic-evidence-double-negative lib term step)))
                    (arg (proof-term-at term 1)))
                 (t3-arithmetic-record-with-evidence (1- n) evidence arg (not holds) opposite))))))))))

(defund t3-arithmetic-record-signed-test (evidence signed)
  (let ((proof (library-library-proof (t3-logic-evidence-lib evidence))))
    (t3-arithmetic-with-evidence evidence
        ((signed (proof-list-of-length signed 2))
         (step (proof-proof-assume proof (car signed) (cadr signed))))
      (t3-arithmetic-record-with-evidence 1000000 evidence (car signed) (cadr signed) step))))

(defun t3-arithmetic-record-signed-tests (evidence tests)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      evidence
    (let ((recorded (t3-arithmetic-record-signed-test evidence (car tests))))
      (if (failure-p (car recorded))
          (cdr recorded)
        (t3-arithmetic-record-signed-tests (cdr recorded) (cdr tests))))))

(defun t3-arithmetic-find-after-failure (evidence term)
  (let ((tests (t3-logic-evidence-tests evidence))
        (proof (library-library-proof (t3-logic-evidence-lib evidence))))
    (if (or (t3-logic-evidence-expanded evidence)
            (t3-logic-evidence-test-assumption proof tests term))
        evidence
      (t3-arithmetic-record-signed-tests (t3-logic-evidence-with-expanded evidence) tests))))

(defun t3-arithmetic-find-with-evidence (evidence term)
  (let ((result (t3-logic-evidence-find evidence term)))
    (if (failure-p result)
        (cons result (if (t3-arithmetic-recoverable-failure-p result)
                         (t3-arithmetic-find-after-failure evidence term)
                       evidence))
      result)))

(defun t3-arithmetic-nonnegative-attempt (evidence term)
  (let ((direct (t3-arithmetic-find-with-evidence evidence (library-nonnegative term))))
    (if (car direct)
        direct
      (let ((natural (t3-arithmetic-find-with-evidence (cdr direct) (list *library-natp* term))))
        (if (failure-p (car natural))
            natural
          (let* ((evidence (cdr natural))
                 (lib (t3-logic-evidence-lib evidence))
                 (step (proof-with-checked-results
                           ((natural (or (car natural) (t3-logic-libraryproofs-natural lib term))))
                         (library-library-cite lib "NATURAL-NONNEGATIVE" (list term) (list natural)))))
            (cons step evidence)))))))

(defun t3-arithmetic-positive-atom (evidence atom)
  (proof-with-checked-results ((direct (t3-logic-evidence-find evidence (library-positive atom))))
    (if (car direct)
        direct
      (proof-with-checked-results
          ((nonzero (t3-logic-evidence-find (cdr direct) (proof-neg (proof-eq atom *proof-zero*)))))
        (if (not (car nonzero))
            nonzero
          (let* ((attempt (t3-arithmetic-nonnegative-attempt (cdr nonzero) atom))
                 (bound (car attempt))
                 (evidence (cdr attempt)))
            (if (t3-arithmetic-recoverable-failure-p bound)
                (cons nil evidence)
              (proof-with-checked-results
                  ((bound bound)
                   (integer (t3-logic-evidence-integer evidence atom))
                   (step (library-library-cite (t3-logic-evidence-lib (cdr integer))
                                               "T3-POSITIVE-FROM-NONZERO" (list atom)
                                               (list (car integer) bound (car nonzero)))))
                (cons step (cdr integer))))))))))

(defun t3-arithmetic-comparison (lib left right integers)
  (proof-with-checked-results ((left-type (t3-arithmetic-type-of lib left integers))
                               (right-type (t3-arithmetic-type-of lib right integers)))
    (library-library-cite lib "LESS-DIFFERENCE" (list left right) (list left-type right-type))))

(defun t3-arithmetic-add-positive (lib strict weak integers)
  (proof-with-checked-results
      ((a (t3-arithmetic-step-term strict 2))
       (weak-comparison (t3-arithmetic-step-term weak 1))
       (b (proof-term-at weak-comparison 1))
       (b-type (t3-arithmetic-type-of lib b integers))
       (a-type (t3-arithmetic-type-of lib a integers)))
    (library-library-cite lib "POSITIVE-PLUS-NONNEGATIVE" (list b a)
                          (list b-type a-type strict weak))))

(defun t3-arithmetic-weak-candidate (lib step comparison integers)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((args (proof-list-of-length (cdr comparison) 2))
         (axiom (library-library-axiom lib "<-ON-OTHERS" args))
         (weak (proof-proof-rewrite proof step axiom '(1 1)))
         (bound (t3-arithmetic-step-term weak 1))
         (value (proof-term-at bound 1))
         (integer (t3-arithmetic-type-of lib value integers)))
      (library-library-cite lib "POSITIVE-ONE-PLUS" (list value) (list integer weak)))))

(defun t3-arithmetic-fact-candidate (lib step integers)
  (proof-with-checked-results ((claim (proof-step-first step)))
    (cond ((proof-is-call claim *proof-less*)
           (proof-with-checked-results
               ((args (proof-list-of-length (cdr claim) 2))
                (comparison (t3-arithmetic-comparison lib (car args) (cadr args) integers)))
             (proof-proof-rewrite (library-library-proof lib) step comparison '(1))))
          ((proof-is-call claim *proof-not*)
           (proof-with-checked-results ((comparison (proof-term-at claim 1)))
             (if (proof-is-call comparison *proof-less*)
                 (t3-arithmetic-weak-candidate lib step comparison integers)
               nil)))
          (t nil))))

(defun t3-arithmetic-fact-candidates (lib facts integers)
  (if (endp facts)
      nil
    (let ((candidate (t3-arithmetic-fact-candidate lib (car facts) integers)))
      (proof-with-checked-results
          ((candidate (if (t3-arithmetic-recoverable-failure-p candidate) nil candidate))
           (rest (t3-arithmetic-fact-candidates lib (cdr facts) integers)))
        (if candidate (cons candidate rest) rest)))))

(defun t3-arithmetic-atom-candidates (evidence atoms form)
  (declare (xargs :measure (acl2-count atoms)))
  (if (endp atoms)
      (cons nil evidence)
    (let ((atom (car atoms)))
      (proof-with-checked-results
          ((candidate (if (and (not (equal atom *proof-zero*))
                               (< 0 (table-get form atom 0)))
                          (t3-arithmetic-positive-atom evidence atom)
                        (cons nil evidence)))
           (rest (t3-arithmetic-atom-candidates (cdr candidate) (cdr atoms) form)))
        (cons (if (car candidate) (cons (car candidate) (car rest)) (car rest))
              (cdr rest))))))

(defun t3-arithmetic-subtract-coefficients (remainder source copies)
  (declare (xargs :measure (acl2-count source)))
  (if (endp source)
      remainder
    (let ((next (t3-arithmetic-increment-coefficient remainder (caar source)
                                                    (- (* copies (cdar source))))))
      (t3-arithmetic-subtract-coefficients next (cdr source) copies))))

(defun t3-arithmetic-negative-atom-p (form)
  (and (consp form)
       (or (and (not (equal (caar form) *proof-zero*)) (< (cdar form) 0))
           (t3-arithmetic-negative-atom-p (cdr form)))))

(defun t3-arithmetic-base-bound (lib step value copies constant integers)
  (cond ((< constant 0)
         (proof-with-checked-results
             ((integer (t3-arithmetic-type-of lib value integers))
              (weak (library-library-cite lib "T3-ONE-BELOW" (list value) (list integer step))))
           (t3-arithmetic-add-positive lib step weak integers)))
        ((equal copies 2)
         (library-library-cite lib "POSITIVE-SUM" (list value value) (list step)))
        (t step)))

(defun t3-arithmetic-add-constant (lib bound constant)
  (if (< 0 constant)
      (proof-with-checked-results
          ((number (t3-logic-libraryproofs-prove lib (library-positive (proof-quote constant)) nil nil))
           (left (t3-arithmetic-step-term bound 2))
           (right (t3-arithmetic-step-term number 2)))
        (library-library-cite lib "POSITIVE-SUM" (list left right) (list bound number)))
    bound))

(defun t3-arithmetic-add-remainder-atom (copies lib bound atom evidence integers)
  (declare (xargs :measure (nfix copies)))
  (cond ((not (integerp copies))
         '(:failure "failure" ""))
        ((not (o< (nfix (1- copies)) (nfix copies))) (cons bound evidence))
        (t
         (let* ((attempt (t3-arithmetic-nonnegative-attempt evidence atom))
                (weak (car attempt))
                (evidence (cdr attempt))
                (next (if (failure-p weak) weak (t3-arithmetic-add-positive lib bound weak integers))))
           (cond ((t3-arithmetic-recoverable-failure-p next) (cons nil evidence))
                 ((failure-p next) next)
                 (t (t3-arithmetic-add-remainder-atom (1- copies) lib next atom evidence integers)))))))

(defun t3-arithmetic-add-remainder-atoms (lib bound atoms remainder evidence integers)
  (declare (xargs :measure (acl2-count atoms)))
  (if (endp atoms)
      (cons bound evidence)
    (proof-with-checked-results
        ((added (t3-arithmetic-add-remainder-atom (table-get remainder (car atoms) 0)
                                                 lib bound (car atoms) evidence integers)))
      (if (car added)
          (t3-arithmetic-add-remainder-atoms lib (car added) (cdr atoms) remainder (cdr added) integers)
        added))))

(defun t3-arithmetic-add-remainder (lib bound remainder evidence integers)
  (let ((atoms (t3-arithmetic-sorted-terms (table-keys remainder))))
    (cond ((t3-arithmetic-recoverable-failure-p atoms) (cons nil evidence))
          ((failure-p atoms) atoms)
          (t (t3-arithmetic-add-remainder-atoms lib bound atoms remainder evidence integers)))))

(defun t3-arithmetic-try-copies (lib step value source form copies evidence integers)
  (declare (xargs :measure (acl2-count copies)))
  (if (endp copies)
      (cons nil evidence)
    (let* ((count (car copies))
           (remainder (t3-arithmetic-subtract-coefficients form source count)))
      (if (t3-arithmetic-negative-atom-p remainder)
          (t3-arithmetic-try-copies lib step value source form (cdr copies) evidence integers)
        (let* ((constant-entry (assoc-equal *proof-zero* remainder))
               (constant (if constant-entry (cdr constant-entry) 0))
               (remainder (if constant-entry (table-delete remainder *proof-zero*) remainder)))
          (if (and (< constant 0) (not (and (equal constant -1) (equal count 2))))
              (t3-arithmetic-try-copies lib step value source form (cdr copies) evidence integers)
            (proof-with-checked-results
                ((bound (t3-arithmetic-base-bound lib step value count constant integers))
                 (bound (t3-arithmetic-add-constant lib bound constant))
                 (added (t3-arithmetic-add-remainder lib bound remainder evidence integers)))
              (if (car added)
                  added
                (t3-arithmetic-try-copies lib step value source form (cdr copies) (cdr added) integers)))))))))

(defun t3-arithmetic-try-candidates (lib candidates form evidence integers)
  (declare (xargs :measure (acl2-count candidates)))
  (if (endp candidates)
      (cons nil evidence)
    (let ((step (car candidates)))
      (proof-with-checked-results
          ((value (t3-arithmetic-step-term step 2))
           (source (t3-arithmetic-coefficients value))
           (attempt (t3-arithmetic-try-copies lib step value source form '(1 2) evidence integers)))
        (if (car attempt)
            attempt
          (t3-arithmetic-try-candidates lib (cdr candidates) form (cdr attempt) integers))))))

(defun t3-arithmetic-positive-difference (lib target evidence integers)
  (proof-with-checked-results ((form (t3-arithmetic-coefficients target)))
    (let ((constant (table-get form *proof-zero* 0)))
      (if (and (equal (table-keys form) (list *proof-zero*)) (< 0 constant))
          (proof-with-checked-results
              ((step (t3-logic-libraryproofs-prove lib (library-positive (proof-quote constant)) nil nil)))
            (cons step evidence))
        (let ((facts (table-values (t3-logic-evidence-facts evidence))))
          (proof-with-checked-results
              ((one (and (< 0 constant)
                         (t3-logic-libraryproofs-prove lib (library-positive *proof-one*) nil nil)))
               (from-facts (t3-arithmetic-fact-candidates lib facts integers))
               (atoms (t3-arithmetic-sorted-terms (table-keys form)))
               (from-atoms (t3-arithmetic-atom-candidates evidence atoms form))
               (candidates (append (if one (list one) nil) from-facts (car from-atoms)))
               (attempt (t3-arithmetic-try-candidates lib candidates form (cdr from-atoms) integers)))
            (if (car attempt)
                attempt
              (proof-with-checked-results ((text (proof-write target)))
                '(:failure "unsupported" "")))))))))

(defun t3-arithmetic-integer-comparison (lib left right evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((direct (t3-logic-evidence-find evidence (library-lt left right))))
      (if (car direct)
          direct
        (proof-with-checked-results
            ((integers (t3-arithmetic-integer-facts (cdr direct) (list left right)))
             (comparison (t3-arithmetic-comparison lib left right (car integers)))
             (comparison-rhs (t3-arithmetic-step-term comparison 2))
             (delta (proof-term-at comparison-rhs 2))
             (bound (t3-arithmetic-positive-difference lib delta (cdr integers) (car integers)))
             (bound-rhs (t3-arithmetic-step-term (car bound) 2))
             (identity (t3-arithmetic-linear-identity lib delta bound-rhs (car integers)))
             (comparison (proof-proof-rewrite proof comparison identity '(1 2 2)))
             (result (proof-proof-transport proof (car bound) comparison)))
          (cons result (cdr bound)))))))

(defun t3-arithmetic-clipped-descent (lib smaller larger evidence)
  (proof-with-checked-results
      ((old (proof-term-at larger 1))
       (new (proof-term-at smaller 1))
       (new-type (t3-logic-evidence-integer evidence new))
       (old-type (t3-logic-evidence-integer (cdr new-type) old))
       (positive (t3-arithmetic-integer-comparison lib *proof-zero* old (cdr old-type)))
       (decreases (t3-arithmetic-integer-comparison lib new old (cdr positive)))
       (step (library-library-cite lib "NFIX-DECREASE" (list new old)
                                   (list (car new-type) (car old-type) (car positive) (car decreases)))))
    (cons step (cdr decreases))))

(defun t3-arithmetic-gap-record-limit (lib old new limit old-type new-type advance evidence)
  (proof-with-checked-results ((upper (t3-logic-evidence-find evidence (library-le new limit))))
    (if (not (car upper))
        (cdr upper)
      (proof-with-checked-results ((known (t3-logic-evidence-find (cdr upper) (library-lt old limit))))
        (if (car known)
            (cdr known)
          (proof-with-checked-results
              ((limit-type (t3-logic-evidence-integer (cdr known) limit))
               (strict (library-library-cite lib "LESS-THEN-WEAK" (list old new limit)
                                              (list old-type new-type (car limit-type) advance (car upper))))
               (literal (proof-step-first strict)))
            (let ((evidence (cdr limit-type)))
              (t3-logic-evidence-with-facts evidence
                                           (table-put (t3-logic-evidence-facts evidence)
                                                        literal strict)))))))))

(defun t3-arithmetic-gap-limit (lib bound old new old-type new-type advance evidence)
  (if (not (proof-is-call bound *proof-plus*))
      evidence
    (proof-with-checked-results ((summand (proof-term-at bound 1)))
      (if (not (equal summand *proof-one*))
          evidence
        (proof-with-checked-results ((limit (proof-term-at bound 2)))
          (t3-arithmetic-gap-record-limit lib old new limit old-type new-type advance evidence))))))

(defun t3-arithmetic-gap-descent (lib smaller larger evidence)
  (proof-with-checked-results ((larger (proof-list-of-length larger 3))
                               (smaller (proof-list-of-length smaller 3)))
    (let ((bound (cadr larger))
          (old (caddr larger))
          (new (caddr smaller)))
      (if (not (equal (cadr smaller) bound))
          '(:failure "unsupported" "")
        (proof-with-checked-results
            ((bound-type (t3-logic-evidence-integer evidence bound))
             (old-type (t3-logic-evidence-integer (cdr bound-type) old))
             (new-type (t3-logic-evidence-integer (cdr old-type) new))
             (advance (t3-arithmetic-integer-comparison lib old new (cdr new-type)))
             (evidence (t3-arithmetic-gap-limit lib bound old new (car old-type) (car new-type)
                                                (car advance) (cdr advance)))
             (within (t3-arithmetic-integer-comparison lib old bound evidence))
             (result (library-library-cite lib "GAP-DECREASE" (list bound old new)
                                           (list (car bound-type) (car old-type) (car new-type)
                                                 (car within) (car advance)))))
          (cons result (cdr within)))))))

(defun t3-arithmetic-successor-bound (lib old new limit evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((integers (t3-arithmetic-integer-facts evidence (list old new limit)))
         (strict (t3-arithmetic-integer-comparison lib old limit (cdr integers)))
         (comparison (t3-arithmetic-comparison lib old limit (car integers)))
         (exceeds (proof-proof-rewrite proof (car strict) comparison '(1)))
         (delta (t3-arithmetic-step-term exceeds 2))
         (delta-type (t3-arithmetic-type-of lib delta (car integers)))
         (weak (library-library-cite lib "T3-ONE-BELOW" (list delta) (list delta-type exceeds)))
         (result (t3-arithmetic-weak-from-difference lib new limit weak (car integers))))
      (cons result (cdr strict)))))
