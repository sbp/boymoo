(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t2-book-logic-car* (proof-cl "CAR"))
(defconst *t2-book-logic-cdr* (proof-cl "CDR"))
(defconst *t2-book-logic-expt* (proof-cl "EXPT"))
(defconst *t2-book-logic-iff* (proof-sym "IFF" "ACL2"))
(defconst *t2-book-logic-fix* (proof-sym "FIX" "ACL2"))
(defconst *t2-book-logic-rfix* (proof-sym "RFIX" "ACL2"))
(defconst *t2-book-logic-divide* (proof-sym "UNARY-/" "ACL2"))
(defconst *t2-book-logic-zip* (proof-sym "ZIP" "ACL2"))
(defconst *t2-book-logic-zp* (proof-sym "ZP" "ACL2"))
(defconst *t2-book-logic-nfix* (proof-sym "NFIX" "ACL2"))
(defconst *t2-book-logic-ifix* (proof-sym "IFIX" "ACL2"))
(defconst *t2-book-logic-synp* (proof-sym "SYNP" "ACL2"))

(defconst *t2-book-logic-completion*
  (list (cons *t2-book-logic-car* "COMPLETION-OF-CAR")
        (cons *t2-book-logic-cdr* "COMPLETION-OF-CDR")
        (cons *proof-plus* "COMPLETION-OF-+")
        (cons *proof-times* "COMPLETION-OF-*")
        (cons *proof-minus* "COMPLETION-OF-UNARY-MINUS")
        (cons *t2-book-logic-divide* "COMPLETION-OF-UNARY-/")
        (cons (proof-cl "NUMERATOR") "COMPLETION-OF-NUMERATOR")
        (cons (proof-cl "DENOMINATOR") "COMPLETION-OF-DENOMINATOR")))

(defconst *t2-book-logic-boolean-axioms*
  (list (cons *proof-consp* "booleanp-consp")
        (cons *proof-integerp* "booleanp-integerp")
        (cons *library-rationalp* "booleanp-rationalp")
        (cons *library-numberp* "booleanp-acl2-numberp")
        (cons *proof-less* "booleanp-<")
        (cons (proof-cl "STRINGP") "booleanp-stringp")
        (cons (proof-cl "SYMBOLP") "booleanp-symbolp")))

(defconst *t2-book-logic-unfold*
  (list (proof-sym "BOOL-FIX" "ACL2")
        (proof-sym "BOOLEANP" "ACL2")
        (proof-sym "CASE-SPLIT" "ACL2")
        *t2-book-logic-fix*
        (proof-sym "FORCE" "ACL2")
        *t2-book-logic-iff*
        *t2-book-logic-ifix*
        *library-implies*
        (proof-sym "NATP" "ACL2")
        *t2-book-logic-nfix*
        (proof-sym "POSP" "ACL2")
        (proof-sym "REAL/RATIONALP" "ACL2")
        *termination-return-last*
        *t2-book-logic-rfix*
        *t2-book-logic-synp*
        (proof-sym "THE-CHECK" "ACL2")
        *t2-book-logic-zip*
        *t2-book-logic-zp*
        (proof-cl "=") (proof-cl "ABS") (proof-cl "ATOM")
        (proof-cl "ENDP") (proof-cl "EQ") (proof-cl "EQL")
        (proof-cl "MAX") (proof-cl "MIN") (proof-cl "MINUSP")
        *proof-not* (proof-cl "NULL") (proof-cl "PLUSP")))

(defun t2-book-logic-head (term)
  (and (consp term) (proof-compound term) (car term)))

(defun t2-book-logic-forwarded-arguments-p (args formals)
  (if (endp args)
      t
    (and (or (member-equal (car args) formals)
             (proof-is-call (car args) *proof-quote*))
         (t2-book-logic-forwarded-arguments-p (cdr args) formals))))

(defun t2-book-logic-wrapper-equation (lib term)
  (let* ((name (t2-book-logic-head term))
         (proof (library-library-proof lib))
         (definition (table-get (proof-proof-definitions proof) name nil)))
    (and definition
         (proof-with-checked-results ((parts (proof-list-of-length definition 2)))
           (let* ((formals (car parts))
                  (body (cadr parts))
                  (operator (t2-book-logic-head body)))
             (and operator
                  (not (member-equal operator (list *proof-if* *proof-quote* name)))
                  (not (proof-compound operator))
                  (t2-book-logic-forwarded-arguments-p (cdr body) formals)
                  (proof-proof-unfold proof term)))))))

(mutual-recursion
 (defun t2-book-logic-size (term)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))))
   (if (or (not (proof-compound term)) (proof-is-call term *proof-quote*))
       1
     (1+ (t2-book-logic-size-arguments (cdr term)))))
 (defun t2-book-logic-size-arguments (args)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       0
     (+ (t2-book-logic-size (car args))
        (t2-book-logic-size-arguments (cdr args))))))

; A set crosses the interface in the order of the serialized elements.
(mutual-recursion
 (defun t2-book-logic-variable-key (datum)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count datum)))))
   (cond ((consp datum)
          (concatenate 'string "(" (text-join " " (t2-book-logic-variable-keys datum)) ")"))
         ((stringp datum)
          (concatenate 'string "\"" (text-replace (text-replace datum "\\" "\\\\") "\"" "\\\"") "\""))
         ((rationalp datum)
          (if (integerp datum)
              (decimal-text datum)
            (concatenate 'string (decimal-text (numerator datum)) "/" (decimal-text (denominator datum)))))
         ((eq datum t) "t")
         (t "nil")))
 (defun t2-book-logic-variable-keys (data)
   (declare (xargs :measure (* 2 (acl2-count data))))
   (if (endp data)
       nil
     (cons (t2-book-logic-variable-key (car data))
           (t2-book-logic-variable-keys (cdr data))))))

(mutual-recursion
 (defun t2-book-logic-collect-variables (term variables)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))))
   (cond ((proof-is-call term *proof-quote*) variables)
         ((proof-compound term)
          (t2-book-logic-collect-argument-variables (cdr term) variables))
         ((member-equal term variables) variables)
         (t (cons term variables))))
 (defun t2-book-logic-collect-argument-variables (args variables)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       variables
     (t2-book-logic-collect-argument-variables
      (cdr args) (t2-book-logic-collect-variables (car args) variables)))))

(defun t2-book-logic-keyed-variables (variables)
  (if (endp variables)
      nil
    (cons (cons (t2-book-logic-variable-key (car variables)) (car variables))
          (t2-book-logic-keyed-variables (cdr variables)))))

(defun t2-book-logic-variables (term)
  (table-values
   (seq-sorted (t2-book-logic-keyed-variables (t2-book-logic-collect-variables term nil)))))

(mutual-recursion
 (defun t2-book-logic-match (pattern actual bindings)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count pattern)))))
   (cond ((not (proof-compound pattern))
          (let ((binding (assoc-equal pattern bindings)))
            (if binding
                (cons (equal (cdr binding) actual) bindings)
              (cons t (table-put bindings pattern actual)))))
         ((proof-is-call pattern *proof-quote*) (cons (equal pattern actual) bindings))
         ((and (proof-compound actual)
               (equal (len pattern) (len actual))
               (equal (t2-book-logic-head pattern) (t2-book-logic-head actual)))
          (t2-book-logic-match-arguments (cdr pattern) (cdr actual) bindings))
         (t (cons nil bindings))))
 (defun t2-book-logic-match-arguments (patterns actuals bindings)
   (declare (xargs :measure (* 2 (acl2-count patterns))))
   (if (or (endp patterns) (endp actuals))
       (cons t bindings)
     (let ((matched (t2-book-logic-match (car patterns) (car actuals) bindings)))
       (if (car matched)
           (t2-book-logic-match-arguments (cdr patterns) (cdr actuals) (cdr matched))
         matched)))))

(defun t2-book-logic-arithmetic-constant (datum)
  (cond ((integerp datum) datum)
        ((eq datum t) 1)
        ((null datum) '(:failure "MissingTermPart" ""))
        ((and (consp datum) (equal (car datum) "ratio"))
         (proof-with-checked-results ((num (proof-term-at datum 1)) (den (proof-term-at datum 2)))
           (cond ((not (and (rationalp num) (rationalp den)))
                  '(:failure "failure" ""))
                 ((zerop den)
                  '(:failure "failure" ""))
                 (t (/ num den)))))
        (t nil)))

(defun t2-book-logic-fraction-datum (value)
  (if (integerp value)
      value
    (list "ratio" (numerator value) (denominator value))))

(defun t2-book-logic-split-cons (datum)
  (if (and (proof-compound datum) (consp datum))
      (let ((rest (cdr datum)))
        (cond ((endp rest) (list (car datum) *proof-nil*))
              ((and (endp (cdr rest)) (null (car rest))) '(:failure "MissingTermPart" ""))
              ((and (endp (cdr rest)) (consp (car rest)) (equal (caar rest) "dot"))
               (proof-with-checked-results ((tail (proof-term-at (car rest) 1)))
                 (list (car datum) tail)))
              (t (list (car datum) rest))))
    (list *proof-nil* *proof-nil*)))

(defun t2-book-logic-cons-datum (first rest)
  (cond ((equal rest *proof-nil*) (list first))
        ((proof-compound rest) (cons first rest))
        (t (list first (list "dot" rest)))))

(defun t2-book-logic-arithmetic-constants (data)
  (if (endp data)
      nil
    (proof-with-checked-results
        ((value (t2-book-logic-arithmetic-constant (car data)))
         (rest (t2-book-logic-arithmetic-constants (cdr data))))
      (cons value rest))))

(defun t2-book-logic-has-complex-p (data)
  (if (endp data)
      nil
    (or (and (consp (car data)) (equal (caar data) "complex"))
        (t2-book-logic-has-complex-p (cdr data)))))

(defun t2-book-logic-compute-arithmetic (proof term operator args rational)
  (cond ((member-equal operator (list *library-numberp* (proof-cl "DENOMINATOR")
                                     (proof-cl "NUMERATOR")))
         (proof-with-checked-results ((first (proof-term-at rational 0)))
           (proof-proof-compute
            proof term
            (cond ((equal operator *library-numberp*)
                   (if (or first (and (consp (car args)) (equal (caar args) "complex")))
                       *proof-t* *proof-nil*))
                  ((equal operator (proof-cl "DENOMINATOR")) (if first (denominator first) 1))
                  (t (if first (numerator first) 0))))))
        ((and (member-equal operator (list *proof-plus* *proof-times* *proof-minus*
                                           *t2-book-logic-divide* *proof-less*))
              (not (t2-book-logic-has-complex-p args)))
         (proof-with-checked-results ((first (proof-term-at rational 0)))
           (let ((a (or first 0)))
             (cond ((equal operator *proof-minus*)
                    (proof-proof-compute proof term (t2-book-logic-fraction-datum (- a))))
                   ((equal operator *t2-book-logic-divide*)
                    (proof-proof-compute proof term
                                         (if (zerop a) 0 (t2-book-logic-fraction-datum (/ a)))))
                   (t (proof-with-checked-results ((second (proof-term-at rational 1)))
                        (let ((b (or second 0)))
                          (proof-proof-compute
                           proof term
                           (if (equal operator *proof-less*)
                               (if (< a b) *proof-t* *proof-nil*)
                             (t2-book-logic-fraction-datum
                              (if (equal operator *proof-plus*) (+ a b) (* a b))))))))))))
        (t nil)))

(defun t2-book-logic-constant (lib term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((existing (proof-proof-constant-base proof term)))
      (let ((operator (t2-book-logic-head term)))
        (if (or existing (not (member-equal operator (proof-proof-primitives proof)))
                (not (proof-all-quoted-p (cdr term))))
            existing
          (proof-with-checked-results ((args (proof-quoted-values (cdr term))))
            (cond ((equal operator *proof-cons*)
                   (if (equal (len args) 2)
                       (proof-proof-compute proof term (t2-book-logic-cons-datum (car args) (cadr args)))
                     '(:failure "failure" "")))
                  ((member-equal operator (list *t2-book-logic-car* *t2-book-logic-cdr*))
                   (proof-with-checked-results ((arg (proof-term-at args 0))
                                                (split (t2-book-logic-split-cons arg)))
                     (proof-proof-compute proof term (if (equal operator *t2-book-logic-car*)
                                                         (car split) (cadr split)))))
                  ((equal operator (proof-cl "SYMBOLP"))
                   (proof-with-checked-results ((arg (proof-term-at args 0)))
                     (cond ((null arg) '(:failure "MissingTermPart" ""))
                           ((and (consp arg) (equal (car arg) "sym"))
                            (proof-proof-compute proof term *proof-t*))
                           (t (proof-proof-compute proof term *proof-nil*)))))
                  (t (proof-with-checked-results ((rational (t2-book-logic-arithmetic-constants args)))
                       (t2-book-logic-compute-arithmetic proof term operator args rational))))))))))

(defun t2-book-logic-flattened (operator term)
  (declare (xargs :measure (acl2-count term)))
  (if (proof-is-call term operator)
      (if (endp (cddr term))
          '(:failure "MissingTermPart" "")
        (proof-with-checked-results ((left (t2-book-logic-flattened operator (cadr term)))
                                     (right (t2-book-logic-flattened operator (caddr term))))
          (append left right)))
    (list term)))

(defun t2-book-logic-simpler (a b)
  (let ((size-a (t2-book-logic-size a))
        (size-b (t2-book-logic-size b)))
    (or (< size-a size-b)
        (and (equal size-a size-b) (proof-is-call a *proof-quote*)
             (not (proof-is-call b *proof-quote*))))))

(defun t2-book-logic-step-term (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun t2-book-logic-add-bool-true (lib)
  (let* ((proof (library-library-proof lib))
         (bool-x (list (proof-sym "BOOLEANP" "ACL2") *library-x*)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof bool-x t))
         (definition (proof-proof-unfold proof bool-x))
         (opened (proof-proof-rewrite proof assumed definition '(1)))
         (alias (t2-book-logic-step-term opened 1))
         (not-alias (proof-proof-assume proof alias nil))
         (zero (proof-proof-prove-if proof opened not-alias))
         (x (proof-proof-assume proof *library-x* t))
         (zero-first (proof-step-first zero))
         (unfold-zero (proof-proof-unfold proof zero-first))
         (zero-opened (proof-proof-rewrite proof zero unfold-zero '(1)))
         (contradiction (proof-proof-rewrite proof x zero-opened '(1)))
         (tidied (proof-proof-tidy proof contradiction))
         (front (proof-proof-front proof tidied alias))
         (unfold-alias (proof-proof-unfold proof alias))
         (step (proof-proof-rewrite proof front unfold-alias '(1))))
      (library-library-lemma lib "BOOL-TRUE" (proof-eq *library-x* *proof-true*)
                             step (list (proof-neg bool-x) (proof-neg *library-x*))))))

(defun t2-book-logic-true-boolean (lib boolean positive)
  (proof-with-checked-results
      ((next-lib (if (assoc-equal (proof-sym "SELF-BOOL-TRUE" "ACL2")
                                  (proof-proof-facts (library-library-proof lib)))
                    lib
                  (t2-book-logic-add-bool-true lib)))
       (term (proof-step-first positive))
       (step (library-library-cite next-lib "BOOL-TRUE" (list term) (list boolean positive))))
    (cons step next-lib)))

(defun t2-book-logic-ac-descend (node place)
  (declare (xargs :measure (acl2-count place)))
  (if (endp place)
      node
    (proof-with-checked-results ((next (proof-term-at node (car place))))
      (t2-book-logic-ac-descend next (cdr place)))))

(defun t2-book-logic-ac-equal-normalize-current (place step)
  (proof-with-checked-results ((first (proof-step-first step)))
    (t2-book-logic-ac-descend first (cdr place))))

(defun t2-book-logic-ac-associate-next (lib step at operator assoc-name)
  (proof-with-checked-results ((current (t2-book-logic-ac-equal-normalize-current at step)))
    (if (not (proof-is-call current operator))
        step
      (proof-with-checked-results ((parts (proof-list-of-length (cdr current) 2)))
        (let ((left (car parts)) (right (cadr parts)))
          (if (proof-is-call left operator)
              (proof-with-checked-results
                  ((axiom (library-library-axiom lib assoc-name (append (cdr left) (list right))))
                   (next (proof-proof-rewrite (library-library-proof lib) step axiom at)))
                (list :t2-ac-associate next at))
            (list :t2-ac-associate step (append at '(2)))))))))

(defun t2-book-logic-ac-associate (n lib position operator assoc-name)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "t2-book-logic-ac-associate"))
        ((eq (car position) :t2-ac-associate)
         (t2-book-logic-ac-associate (1- n) lib
                                    (t2-book-logic-ac-associate-next
                                     lib (cadr position) (caddr position) operator assoc-name)
                                    operator assoc-name))
        (t position)))

(defun t2-book-logic-ac-swap (lib step at operator assoc-name comm-name left rest)
  (let ((proof (library-library-proof lib)))
    (if (proof-is-call rest operator)
        (proof-with-checked-results ((parts (proof-list-of-length (cdr rest) 2))
                                     (left-text (proof-write left))
                                     (right-text (proof-write (car parts))))
          (let ((right (car parts)) (tail (cadr parts)))
            (if (not (string< right-text left-text))
                step
              (proof-with-checked-results
                  ((association (library-library-axiom lib assoc-name (list left right tail)))
                   (reverse-association (proof-proof-symmetric proof association))
                   (commutation (library-library-axiom lib comm-name (list left right)))
                   (reordered (proof-proof-rewrite proof reverse-association commutation '(1 2 1)))
                   (reassociation (library-library-axiom lib assoc-name (list right left tail)))
                   (swap (proof-proof-chain proof reordered (list reassociation))))
                (proof-proof-rewrite proof step swap at)))))
      (proof-with-checked-results ((left-text (proof-write left)) (rest-text (proof-write rest)))
        (if (string< rest-text left-text)
            (proof-with-checked-results ((commutation (library-library-axiom lib comm-name (list left rest))))
              (proof-proof-rewrite proof step commutation at))
          step)))))

(defun t2-book-logic-ac-sort-next (lib step at operator assoc-name comm-name)
  (proof-with-checked-results ((current (t2-book-logic-ac-equal-normalize-current at step))
                               (parts (proof-list-of-length (cdr current) 2)))
    (t2-book-logic-ac-swap lib step at operator assoc-name comm-name (car parts) (cadr parts))))

(defun t2-book-logic-ac-sort-pass (n lib step at operator assoc-name comm-name)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (failure-p step))
      step
    (t2-book-logic-ac-sort-pass (1- n) lib (t2-book-logic-ac-sort-next lib step at operator assoc-name comm-name)
                                (append at '(2)) operator assoc-name comm-name)))

(defun t2-book-logic-ac-sort (remaining lib step operator assoc-name comm-name)
  (declare (xargs :measure (nfix remaining)))
  (if (or (zp remaining) (= remaining 1) (failure-p step))
      step
    (t2-book-logic-ac-sort (1- remaining) lib
                           (t2-book-logic-ac-sort-pass (1- remaining) lib step '(1 2) operator assoc-name comm-name)
                           operator assoc-name comm-name)))

(defun t2-book-logic-ac-equal-normalize (term lib operator leaves assoc-name comm-name)
  (proof-with-checked-results
      ((initial (proof-proof-reflexive (library-library-proof lib) term))
       (associated (t2-book-logic-ac-associate 1000000 lib (list :t2-ac-associate initial '(1 2)) operator assoc-name)))
    (t2-book-logic-ac-sort (len leaves) lib associated operator assoc-name comm-name)))

(defun t2-book-logic-ac-equal (lib first second)
  (let ((operator (t2-book-logic-head first)) (proof (library-library-proof lib)))
    (proof-with-checked-results ((a (t2-book-logic-flattened operator first))
                                 (b (t2-book-logic-flattened operator second)))
      (and (<= (len a) 12)
           (proof-with-checked-results ((a-text (proof-write-list a)) (b-text (proof-write-list b)))
             (and (equal (seq-sorted a-text) (seq-sorted b-text))
                  (let* ((suffix (if (equal operator *proof-plus*) "+" "*"))
                         (assoc-name (concatenate 'string "ASSOCIATIVITY-OF-" suffix))
                         (comm-name (concatenate 'string "COMMUTATIVITY-OF-" suffix)))
                    (proof-with-checked-results
                        ((left (t2-book-logic-ac-equal-normalize first lib operator a assoc-name comm-name))
                         (right (t2-book-logic-ac-equal-normalize second lib operator a assoc-name comm-name))
                         (reversed (proof-proof-symmetric proof right)))
                      (proof-proof-chain proof left (list reversed))))))))))

(defun t2-book-logic-rule-name (rule) (car rule))
(defun t2-book-logic-rule-pattern (rule) (cadr rule))
(defun t2-book-logic-rule-path (rule) (caddr rule))
(defun t2-book-logic-rule-reverse (rule) (cadddr rule))

(defun t2-book-logic-rules-make (lib goals equations indexed)
  (list :t2-rules lib goals equations indexed))

(defun t2-book-logic-rules-lib (rules) (cadr rules))
(defun t2-book-logic-rules-goals (rules) (caddr rules))
(defun t2-book-logic-rules-equations (rules) (cadddr rules))
(defun t2-book-logic-rules-indexed (rules) (car (cddddr rules)))

(defun t2-book-logic-rule-append (table name pattern path reverse-p)
  (let* ((operator (t2-book-logic-head pattern))
         (rule (list name pattern path reverse-p))
         (bucket (table-get table operator nil)))
    (table-put table operator (append bucket (list rule)))))

(defun t2-book-logic-rules-add-direction (rules name old new path reverse-p)
  (if (and (proof-compound old) (consp old)
           (not (proof-is-call old *proof-quote*))
           (subsetp-equal (t2-book-logic-collect-variables new nil)
                          (t2-book-logic-collect-variables old nil))
           (< (t2-book-logic-size new) (t2-book-logic-size old)))
      (t2-book-logic-rules-make
       (t2-book-logic-rules-lib rules) (t2-book-logic-rules-goals rules)
       (t2-book-logic-rule-append (t2-book-logic-rules-equations rules) name old path reverse-p)
       (t2-book-logic-rules-indexed rules))
    rules))

(defun t2-book-logic-rules-add (rules name formula path)
  (declare (xargs :measure (acl2-count formula)))
  (if (not (proof-compound formula))
      rules
    (let ((with-goal
           (t2-book-logic-rules-make
            (t2-book-logic-rules-lib rules)
            (t2-book-logic-rule-append (t2-book-logic-rules-goals rules) name formula path nil)
            (t2-book-logic-rules-equations rules) (t2-book-logic-rules-indexed rules))))
      (cond ((proof-is-call formula *library-implies*)
             (if (endp (cddr formula))
                 '(:failure "MissingTermPart" "")
               (t2-book-logic-rules-add with-goal name (caddr formula) (append path '("consequent")))))
            ((proof-is-call formula *proof-if*)
             (cond ((endp (cdddr formula)) '(:failure "MissingTermPart" ""))
                   ((equal (cadddr formula) *proof-false*)
                    (proof-with-checked-results
                        ((first (t2-book-logic-rules-add with-goal name (cadr formula)
                                                        (append path '("first")))))
                      (t2-book-logic-rules-add first name (caddr formula) (append path '("second")))))
                   (t with-goal)))
            ((proof-is-call formula *proof-equal*)
             (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2)))
               (let* ((left (car parts)) (right (cadr parts))
                      (forward (t2-book-logic-rules-add-direction with-goal name left right path nil)))
                 (t2-book-logic-rules-add-direction forward name right left path t))))
            (t with-goal)))))

(defun t2-book-logic-rules-update-facts (facts definitions rules)
  (declare (xargs :measure (acl2-count facts)))
  (if (endp facts)
      rules
    (let ((name (caar facts)) (clause (cdar facts))
          (indexed (t2-book-logic-rules-indexed rules)))
      (if (member-equal name indexed)
          (t2-book-logic-rules-update-facts (cdr facts) definitions rules)
        (let ((marked (t2-book-logic-rules-make
                       (t2-book-logic-rules-lib rules) (t2-book-logic-rules-goals rules)
                       (t2-book-logic-rules-equations rules) (append indexed (list name)))))
          (proof-with-checked-results
              ((next (if (and (consp clause) (not (assoc-equal name definitions)))
                         (t2-book-logic-rules-add marked name (car clause) nil)
                       marked)))
            (t2-book-logic-rules-update-facts (cdr facts) definitions next)))))))

(defun t2-book-logic-rules-update (rules lib)
  (let ((proof (library-library-proof lib)))
    (t2-book-logic-rules-update-facts
     (proof-proof-facts proof) (proof-proof-definitions proof)
     (t2-book-logic-rules-make lib (t2-book-logic-rules-goals rules)
                               (t2-book-logic-rules-equations rules) (t2-book-logic-rules-indexed rules)))))

(defun t2-book-logic-rules-init (lib)
  (t2-book-logic-rules-update (t2-book-logic-rules-make lib nil nil nil) lib))

(defun t2-book-logic-prefix-suffix (prefix lines)
  (cond ((endp prefix) (cons t lines))
        ((and (consp lines) (equal (car prefix) (car lines)))
         (t2-book-logic-prefix-suffix (cdr prefix) (cdr lines)))
        (t nil)))

; Keep each clause's contribution or the failure returned while indexing it.
; A later fact can replace a clause, and a definition can hide its rules.
(defun t2-book-logic-rules-fragments (facts definitions known)
  (declare (xargs :measure (acl2-count facts)))
  (if (endp facts)
      nil
    (let ((name (caar facts))
          (clause (cdar facts)))
      (if (and (consp clause) (not (assoc-equal name definitions)))
          (let* ((formula (car clause))
                 (previous (assoc-equal name known))
                 (fragment (if (and previous (equal formula (cadr previous)))
                               previous
                             (list name formula
                                   (t2-book-logic-rules-add
                                    (t2-book-logic-rules-make nil nil nil nil) name formula nil)))))
            (cons fragment (t2-book-logic-rules-fragments (cdr facts) definitions known)))
        (t2-book-logic-rules-fragments (cdr facts) definitions known)))))

(defun t2-book-logic-rules-merge-buckets (buckets table)
  (if (endp buckets)
      table
    (let* ((head (caar buckets))
           (rules (append (table-get table head nil) (cdar buckets))))
      (t2-book-logic-rules-merge-buckets (cdr buckets) (table-put table head rules)))))

(defun t2-book-logic-rules-assemble (fragments rules)
  (declare (xargs :measure (acl2-count fragments)))
  (if (endp fragments)
      rules
    (proof-with-checked-results ((fragment (caddr (car fragments))))
      (t2-book-logic-rules-assemble
       (cdr fragments)
       (t2-book-logic-rules-make
        (t2-book-logic-rules-lib rules)
        (t2-book-logic-rules-merge-buckets (t2-book-logic-rules-goals fragment)
                                          (t2-book-logic-rules-goals rules))
        (t2-book-logic-rules-merge-buckets (t2-book-logic-rules-equations fragment)
                                          (t2-book-logic-rules-equations rules))
        (t2-book-logic-rules-indexed rules))))))

(defun t2-book-logic-rules-prepare (lib)
  (let* ((proof (library-library-proof lib))
         (facts (proof-proof-facts proof))
         (fragments (t2-book-logic-rules-fragments facts (proof-proof-definitions proof) nil))
         (rules (t2-book-logic-rules-assemble
                 fragments (t2-book-logic-rules-make lib nil nil (table-keys facts)))))
    (list lib fragments rules)))

(defun t2-book-logic-rules-shadowed-p (definitions old-facts)
  (and (consp definitions)
       (or (assoc-equal (caar definitions) old-facts)
           (t2-book-logic-rules-shadowed-p (cdr definitions) old-facts))))

(defun t2-book-logic-rules-from-prepared (prepared lib)
  (let ((base (car prepared))
        (rules (caddr prepared)))
    (if (equal base lib)
        rules
      (let* ((given (library-library-proof base))
             (proof (library-library-proof lib))
             (old-facts (proof-proof-facts given))
             (facts (proof-proof-facts proof))
             (definitions (proof-proof-definitions proof))
             (more-facts (and (not (failure-p rules))
                              (t2-book-logic-prefix-suffix old-facts facts)))
             (more-definitions (and more-facts
                                    (t2-book-logic-prefix-suffix
                                     (proof-proof-definitions given) definitions))))
        (if (and more-definitions
                 (not (t2-book-logic-rules-shadowed-p (cdr more-definitions) old-facts)))
            (t2-book-logic-rules-update-facts
             (cdr more-facts) definitions
             (t2-book-logic-rules-make lib (t2-book-logic-rules-goals rules)
                                       (t2-book-logic-rules-equations rules)
                                       (t2-book-logic-rules-indexed rules)))
          (t2-book-logic-rules-assemble
           (t2-book-logic-rules-fragments facts definitions (cadr prepared))
           (t2-book-logic-rules-make lib nil nil (table-keys facts))))))))

(defun t2-book-logic-search-init (lib rules hints budget seeds)
  (list :t2-search lib rules (proof-unique hints) budget nil nil nil nil seeds nil nil))

(defun t2-book-logic-search-lib (search) (nth 1 search))
(defun t2-book-logic-search-rules (search) (nth 2 search))
(defun t2-book-logic-search-hints (search) (nth 3 search))
(defun t2-book-logic-search-budget (search) (nth 4 search))
(defun t2-book-logic-search-contexts (search) (nth 5 search))
(defun t2-book-logic-search-active (search) (nth 6 search))
(defun t2-book-logic-search-failed (search) (nth 7 search))
(defun t2-book-logic-search-premises (search) (nth 8 search))
(defun t2-book-logic-search-seeds (search) (nth 9 search))
(defun t2-book-logic-search-hooks (search) (nth 10 search))
(defun t2-book-logic-search-replies (search) (nth 11 search))

(defun t2-book-logic-search-with-hooks (search hooks replies)
  (update-nth 11 replies (update-nth 10 hooks search)))

(defun t2-book-logic-search-rebase-contexts (contexts before after)
  (if (endp contexts)
      nil
    (let* ((entry (car contexts))
           (context (cdr entry))
           (next (if (equal (t2-tactics-ruler-facts-proof context) before)
                     (t2-tactics-ruler-facts-with-proof context after)
                   context)))
      (cons (cons (car entry) next)
            (t2-book-logic-search-rebase-contexts (cdr contexts) before after)))))

(defun t2-book-logic-search-with-lib (search lib)
  (let ((before (t2-book-logic-search-lib search)) (rules (t2-book-logic-search-rules search)))
    (if (equal before lib)
        search
      (update-nth
       5 (t2-book-logic-search-rebase-contexts (t2-book-logic-search-contexts search) before lib)
       (update-nth
        2 (if (and rules (equal (t2-book-logic-rules-lib rules) before))
              (t2-book-logic-rules-make lib (t2-book-logic-rules-goals rules)
                                       (t2-book-logic-rules-equations rules) (t2-book-logic-rules-indexed rules))
            rules)
        (update-nth 1 lib search))))))

(defun t2-book-logic-search-with-context (search tests context)
  (update-nth 5 (table-put (t2-book-logic-search-contexts search) tests context) search))

(defun t2-book-logic-search-current-context (search tests)
  (table-get (t2-book-logic-search-contexts search) tests nil))

(defun t2-book-logic-search-request-p (value)
  (and (consp value) (eq (car value) :t2-book-logic-search-request)))

(defun t2-book-logic-search-request-method (request) (nth 1 request))
(defun t2-book-logic-search-request-term (request) (nth 2 request))
(defun t2-book-logic-search-request-context (request) (nth 3 request))
(defun t2-book-logic-search-request-depth (request) (nth 4 request))
(defun t2-book-logic-search-request-opened (request) (nth 5 request))
(defun t2-book-logic-search-request-lib (request) (nth 6 request))

(defund t2-book-logic-search-stopped-p (value)
  (or (failure-p value) (t2-book-logic-search-request-p value)))

; Search operations return their value and the state at that point.
(defmacro t2-book-logic-search-let (bindings body)
  (if (endp bindings)
      body
    (let ((name (caar bindings)) (form (cadar bindings)))
      `(let ((search-answer ,form))
         (if (t2-book-logic-search-stopped-p (car search-answer))
             search-answer
           (let ((,name (car search-answer)) (search (cdr search-answer)))
             (declare (ignorable ,name search))
             (t2-book-logic-search-let ,(cdr bindings) ,body)))))))

(defmacro t2-book-logic-search-check (bindings body)
  (if (endp bindings)
      body
    (let ((name (caar bindings)) (form (cadar bindings)))
      `(let ((,name ,form))
         (if (t2-book-logic-search-stopped-p ,name)
             (cons ,name search)
           (t2-book-logic-search-check ,(cdr bindings) ,body))))))

(defund t2-book-logic-search-hook (search method term tests depth opened)
  (if (not (member-eq method (t2-book-logic-search-hooks search)))
      (cons :base search)
    (let* ((replies (t2-book-logic-search-replies search))
           (reply (car replies)))
      (cond ((endp replies)
             (cons (list :t2-book-logic-search-request method term
                         (t2-book-logic-search-current-context search tests)
                         depth opened (t2-book-logic-search-lib search))
                   search))
            ((and (consp reply) (eq (car reply) :with-state))
             (cons (cadr reply)
                   (t2-book-logic-search-with-context
                    (t2-book-logic-search-with-lib (update-nth 11 (cdr replies) search) (caddr reply))
                    tests (cadddr reply))))
            (t (cons reply (update-nth 11 (cdr replies) search)))))))

(defund t2-book-logic-search-tick (search)
  (let* ((budget (1- (t2-book-logic-search-budget search)))
         (next (update-nth 4 budget search)))
    (cons (and (< budget 0) '(:failure "Unproved" "")) next)))

(defun t2-book-logic-search-proof-object (search)
  (library-library-proof (t2-book-logic-search-lib search)))

(defun t2-book-logic-search-context-open-next (lib context step term negated seen)
  (let ((operator (if (and (consp term) (proof-compound term)) (car term) :none))
        (proof (library-library-proof lib)))
    (if (member-equal operator seen)
        context
      (proof-with-checked-results ((equation (t2-book-logic-wrapper-equation lib term)))
        (if (not equation)
            context
          (proof-with-checked-results
              ((rewritten (proof-proof-rewrite proof step equation (if negated '(1 1) '(1))))
               (next-step (proof-proof-tidy proof rewritten))
               (next-context (t2-tactics-ruler-facts-learn context next-step))
               (next-term (t2-book-logic-step-term equation 2)))
            (list :t2-wrapper next-context next-step next-term (cons operator seen))))))))

(defun t2-book-logic-search-context-open (n lib position negated)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "t2-book-logic-search-context-open"))
        ((eq (car position) :t2-wrapper)
         (t2-book-logic-search-context-open
          (1- n) lib (t2-book-logic-search-context-open-next lib (nth 1 position) (nth 2 position)
                                                            (nth 3 position) negated (nth 4 position))
          negated))
        (t position)))

(defun t2-book-logic-search-context-open-premise (lib context step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (let ((negated (proof-is-call literal *proof-not*)))
      (proof-with-checked-results ((term (if negated (proof-term-at literal 1) literal)))
        (t2-book-logic-search-context-open 1000000 lib (list :t2-wrapper context step term nil) negated)))))

(defun t2-book-logic-search-context-open-premises (lib context steps)
  (declare (xargs :measure (acl2-count steps)))
  (if (or (endp steps) (failure-p context))
      context
    (t2-book-logic-search-context-open-premises
     lib (t2-book-logic-search-context-open-premise lib context (car steps)) (cdr steps))))

(defund t2-book-logic-search-context (search tests)
  (let ((entry (assoc-equal tests (t2-book-logic-search-contexts search)))
        (lib (t2-book-logic-search-lib search)))
    (if entry
        (cons (cdr entry) search)
      (t2-book-logic-search-check
          ((context (t2-tactics-ruler-facts-init lib tests nil))
           (premises (t2-tactics-ruler-facts-premises context))
           (next (t2-book-logic-search-context-open-premises lib (cdr premises) (car premises))))
        (cons next (t2-book-logic-search-with-context search tests next))))))

(defund t2-book-logic-search-find (search tests term)
  (t2-book-logic-search-check
      ((found (t2-tactics-ruler-facts-find (t2-book-logic-search-current-context search tests) term)))
    (cons (car found) (t2-book-logic-search-with-context search tests (cdr found)))))

(defun t2-book-logic-search-quoted-truth (search term)
  (let ((proof (t2-book-logic-search-proof-object search)))
    (if (equal term *proof-true*)
        (if (eq (proof-proof-kind proof) :slice)
            (t2-arithmetic-arithmetic-prove (t2-book-logic-search-lib search) *proof-true* nil nil)
          (proof-proof-prove proof *proof-true* nil nil))
      (proof-with-checked-results
          ((step (proof-proof-nil-or-true proof term))
           (computed (proof-proof-compute proof (proof-eq term *proof-false*) *proof-nil*))
           (rewritten (proof-proof-rewrite proof step computed '(1)))
           (tidied (proof-proof-tidy proof rewritten)))
        (proof-proof-front proof tidied term)))))

(defun t2-book-logic-condition-p (term)
  (and (proof-is-call term *proof-if*)
       (proof-with-checked-results ((no (proof-term-at term 3)))
         (equal no *proof-false*))))

(defun t2-book-logic-modus-ponens (lib step evidence)
  (let ((proof (library-library-proof lib)))
    (if (eq (proof-proof-kind proof) :slice)
        (t2-arithmetic-arithmetic-modus-ponens lib step evidence)
      (proof-proof-modus-ponens proof step evidence))))

(defun t2-book-logic-conjunct (lib step)
  (let ((proof (library-library-proof lib)))
    (if (eq (proof-proof-kind proof) :slice)
        (t2-arithmetic-arithmetic-conjunct lib step)
      (proof-proof-conjunct proof step))))

(defun t2-book-logic-rule-bound-p (literals keys)
  (if (endp literals)
      t
    (and (subsetp-equal (t2-book-logic-collect-variables (car literals) nil) keys)
         (t2-book-logic-rule-bound-p (cdr literals) keys))))

(defun t2-book-logic-opposite (term)
  (if (proof-is-call term *proof-not*) (proof-term-at term 1) (proof-neg term)))

(defun t2-book-logic-consequence (term)
  (declare (xargs :measure (acl2-count term)))
  (cond ((not (proof-is-call term *library-implies*)) term)
        ((endp (cddr term)) '(:failure "MissingTermPart" ""))
        (t (t2-book-logic-consequence (caddr term)))))

(defun t2-book-logic-seed-direction (seed term equations)
  (proof-with-checked-results ((first (proof-step-first seed))
                               (last (t2-book-logic-consequence first)))
    (if (not equations)
        (and (equal last term) :forward)
      (and (proof-is-call last *proof-equal*)
           (proof-with-checked-results ((left (proof-term-at last 1)) (right (proof-term-at last 2)))
             (cond ((equal left term) (and (t2-book-logic-simpler right term) :forward))
                   ((equal right term) (and (t2-book-logic-simpler left term) :reverse))
                   (t nil)))))))

(defun t2-book-logic-term-true-p (term)
  (and term (not (equal term "")) (not (equal term 0))))

(mutual-recursion
 (defun t2-book-logic-first-test (term)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count term)))))
   (cond ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
         ((proof-is-call term *proof-if*)
          (if (endp (cdr term))
              '(:failure "MissingTermPart" "")
            (proof-with-checked-results ((test (t2-book-logic-first-test (cadr term))))
              (if (t2-book-logic-term-true-p test) test (cadr term)))))
         (t (t2-book-logic-argument-test (cdr term)))))
 (defun t2-book-logic-argument-test (args)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (endp args)
       nil
     (proof-with-checked-results ((test (t2-book-logic-first-test (car args))))
       (if (t2-book-logic-term-true-p test)
           test
         (t2-book-logic-argument-test (cdr args)))))))

(defun t2-book-logic-search-first-test (search term)
  (declare (ignore search))
  (t2-book-logic-first-test term))

(defun t2-book-logic-search-assumptions (proof term premises)
  (declare (xargs :measure (acl2-count premises)))
  (if (endp premises)
      nil
    (proof-with-checked-results ((literal (proof-step-first (car premises))))
      (if (not (proof-is-call literal *proof-equal*))
          (t2-book-logic-search-assumptions proof term (cdr premises))
        (proof-with-checked-results ((sides (proof-list-of-length (cdr literal) 2)))
          (let ((a (car sides)) (b (cadr sides)))
            (cond ((and (equal a term) (t2-book-logic-simpler b a)) (car premises))
                  ((and (equal b term) (t2-book-logic-simpler a b))
                   (proof-proof-symmetric proof (car premises)))
                  (t (t2-book-logic-search-assumptions proof term (cdr premises))))))))))

(defun t2-book-logic-search-assumed-equality (search term tests)
  (t2-book-logic-search-check
      ((premises (t2-tactics-ruler-facts-premises (t2-book-logic-search-current-context search tests))))
    (cons (t2-book-logic-search-assumptions (t2-book-logic-search-proof-object search) term (car premises))
          (t2-book-logic-search-with-context search tests (cdr premises)))))

(defun t2-book-logic-count-head (head heads)
  (if (endp heads)
      0
    (+ (if (equal head (car heads)) 1 0) (t2-book-logic-count-head head (cdr heads)))))

(defun t2-book-logic-search-can-open (search term opened)
  (let ((operator (t2-book-logic-head term)))
    (cond ((equal operator *t2-book-logic-expt*)
           (proof-with-checked-results ((exponent (proof-term-at term 2)))
             (and (proof-is-call exponent *proof-quote*)
                  (proof-with-checked-results ((power (proof-term-at exponent 1)))
                    (and (or (integerp power) (eq power t))
                         (<= (abs (if (eq power t) 1 power)) 2)
                         (< (t2-book-logic-count-head *t2-book-logic-expt* opened) 3))))))
          ((member-equal operator opened) nil)
          ((or (member-equal operator *t2-book-logic-unfold*)
               (member-equal operator (t2-book-logic-search-hints search))) t)
          (t (let ((entry (assoc-equal operator (proof-proof-definitions
                                                (t2-book-logic-search-proof-object search)))))
               (if entry
                   (proof-with-checked-results ((body (proof-term-at (cdr entry) 1)))
                     (<= (t2-book-logic-size body) 23))
                 '(:failure "MissingBinding" "")))))))

(defund t2-book-logic-reflexive-goal (proof goal)
  (and (proof-is-call goal *proof-equal*)
       (proof-with-checked-results ((left (proof-term-at goal 1)) (right (proof-term-at goal 2)))
         (and (equal left right) (proof-proof-reflexive proof left)))))

(defund t2-book-logic-ac-goal (lib goal)
  (and (proof-is-call goal *proof-equal*)
       (proof-with-checked-results ((parts (proof-list-of-length (cdr goal) 2)))
         (let* ((first (car parts)) (second (cadr parts))
                (operator (t2-book-logic-head first)))
           (and (member-equal operator (list *proof-plus* *proof-times*))
                (equal operator (t2-book-logic-head second))
                (t2-book-logic-ac-equal lib first second))))))

(defun t2-book-logic-search-implication (proof goal test valid)
  (proof-with-checked-results
      ((opened (proof-proof-unfold proof goal))
       (body (t2-book-logic-step-term opened 2))
       (if-true (proof-proof-if-true proof body))
       (branch (proof-term-at body 2))
       (selected (proof-proof-select proof branch valid))
       (yes-chain (proof-proof-chain proof opened (list if-true selected)))
       (yes (proof-proof-true-from-eq proof yes-chain))
       (if-false (proof-proof-if-false proof body))
       (no-chain (proof-proof-chain proof opened (list if-false)))
       (no (proof-proof-true-from-eq proof no-chain)))
    (proof-proof-cases proof test yes no)))

(defund t2-book-logic-search-if-test (proof term equality)
  (and equality
       (proof-with-checked-results ((identity (proof-proof-reflexive proof term)))
         (proof-proof-rewrite proof identity equality '(1 2 1)))))

(defund t2-book-logic-search-rewrite-argument (proof original result equality index)
  (if equality
      (proof-with-checked-results ((before (or result (proof-proof-reflexive proof original))))
        (proof-proof-rewrite proof before equality (list 1 2 index)))
    result))

(defun t2-book-logic-search-false-branch (proof current)
  (proof-with-checked-results ((yes (proof-term-at current 2)) (no (proof-term-at current 3)))
    (proof-proof-fact proof "if-nil" (list (list *library-y* yes) (list *library-z* no)))))

(defund t2-book-logic-search-selection (search current test tests)
  (let ((proof (t2-book-logic-search-proof-object search)))
    (cond ((equal test *proof-false*) (cons (t2-book-logic-search-false-branch proof current) search))
          ((proof-is-call test *proof-quote*)
           (t2-book-logic-search-check ((truth (t2-book-logic-search-quoted-truth search test)))
             (cons (proof-proof-select proof current truth) search)))
          (t (t2-book-logic-search-let ((positive (t2-book-logic-search-find search tests test))
                                        (negative (t2-book-logic-search-find search tests (proof-neg test))))
               (let ((evidence (or positive negative)))
                 (cons (and evidence (proof-proof-select (t2-book-logic-search-proof-object search)
                                                         current evidence))
                       search)))))))

(defun t2-book-logic-search-positive-value (search term positive)
  (let* ((operator (t2-book-logic-head term)) (proof (t2-book-logic-search-proof-object search))
         (axiom (assoc-equal operator *t2-book-logic-boolean-axioms*)))
    (cond ((equal operator *proof-equal*)
           (t2-book-logic-search-check
               ((right (proof-term-at term 2))
                (same (proof-proof-fact proof "equal-same" (list (list *library-x* right))))
                (reversed (proof-proof-symmetric proof positive)))
             (cons (proof-proof-rewrite proof same reversed '(1 1 1)) search)))
          (axiom
           (t2-book-logic-search-check
               ((boolean (proof-proof-fact proof (cdr axiom) (seq-zip (list *library-x* *library-y*) (cdr term))))
                (result (t2-book-logic-true-boolean (t2-book-logic-search-lib search) boolean positive)))
             (cons (car result) (t2-book-logic-search-with-lib search (cdr result)))))
          (t (cons nil search)))))

(defun t2-book-logic-search-completion (search term tests opened)
  (let* ((operator (t2-book-logic-head term))
         (name (table-get *t2-book-logic-completion* operator nil))
         (lib (t2-book-logic-search-lib search)) (proof (library-library-proof lib)))
    (if (or (not name) (member-equal operator opened))
        (cons nil search)
      (t2-book-logic-search-check ((completion (library-library-axiom lib name (cdr term)))
                                   (body (t2-book-logic-step-term completion 2)))
        (if (not (proof-is-call body *proof-if*))
            (cons nil search)
          (t2-book-logic-search-check ((test (proof-term-at body 1)))
            (t2-book-logic-search-let ((bad (t2-book-logic-search-find search tests (proof-neg test))))
              (if (not bad)
                  (cons nil search)
                (t2-book-logic-search-check ((selected (proof-proof-select proof body bad)))
                  (cons (proof-proof-chain proof completion (list selected)) search))))))))))

(defun t2-book-logic-search-identity (lib term)
  (let ((operator (t2-book-logic-head term)))
    (and (member-equal operator (list *proof-plus* *proof-times*))
         (let* ((addition (equal operator *proof-plus*))
                (identity (if addition *proof-zero* *proof-one*))
                (unicity (if addition "UNICITY-OF-0" "UNICITY-OF-1")))
           (proof-with-checked-results ((left (proof-term-at term 1)) (right (proof-term-at term 2)))
             (cond ((equal left identity) (library-library-axiom lib unicity (list right)))
                   ((equal right identity)
                    (proof-with-checked-results
                        ((commuted (library-library-axiom lib (if addition "COMMUTATIVITY-OF-+"
                                                               "COMMUTATIVITY-OF-*") (cdr term)))
                         (unit (library-library-axiom lib unicity (list left))))
                      (proof-proof-chain (library-library-proof lib) commuted (list unit))))
                   (t nil)))))))

(defun t2-book-logic-search-unfold (search term tests depth opened)
  (let* ((proof (t2-book-logic-search-proof-object search)) (operator (t2-book-logic-head term)))
    (if (not (assoc-equal operator (proof-proof-definitions proof)))
        (cons nil search)
      (t2-book-logic-search-let ((reply (t2-book-logic-search-hook search :can-open term tests depth opened)))
        (t2-book-logic-search-check
            ((permitted (if (eq reply :base) (t2-book-logic-search-can-open search term opened) reply)))
          (cons (and permitted (proof-proof-unfold (t2-book-logic-search-proof-object search) term)) search))))))

(mutual-recursion
 (defun t2-book-logic-search-use-rule (n search rule bindings tests depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t2-book-logic-search-use-rule") search)
     (let* ((proof (t2-book-logic-search-proof-object search))
            (name (t2-book-logic-rule-name rule))
            (entry (assoc-equal name (proof-proof-facts proof))))
       (cond ((not entry) (cons '(:failure "MissingBinding" "") search))
             ((not (t2-book-logic-rule-bound-p (cdr entry) (table-keys bindings))) (cons nil search))
             (t (t2-book-logic-search-check ((step (proof-proof-fact proof name (table-items bindings))))
                  (t2-book-logic-search-rule-sides (1- n) search step (cdr (proof-step-clause step))
                                                  rule tests depth)))))))

 (defun t2-book-logic-search-rule-sides (n search step sides rule tests depth)
   (declare (xargs :measure (nfix n)))
   (cond ((not (o< (nfix (1- n)) (nfix n))) (cons '(:failure "Fuel" "t2-book-logic-search-rule-sides") search))
         ((endp sides)
          (t2-book-logic-search-rule-path (1- n) search step (t2-book-logic-rule-path rule)
                                         (t2-book-logic-rule-reverse rule) tests depth))
         (t (t2-book-logic-search-check ((opposite (t2-book-logic-opposite (car sides))))
              (t2-book-logic-search-let ((evidence (t2-book-logic-search-premise (1- n) search opposite tests (1- depth))))
                (if (not evidence)
                    (cons nil search)
                  (t2-book-logic-search-check
                      ((next (proof-proof-discharge (t2-book-logic-search-proof-object search) step evidence)))
                    (t2-book-logic-search-rule-sides (1- n) search next (cdr sides) rule tests depth))))))))

 (defun t2-book-logic-search-rule-path (n search step path reverse-p tests depth)
   (declare (xargs :measure (nfix n)))
   (cond ((not (o< (nfix (1- n)) (nfix n))) (cons '(:failure "Fuel" "t2-book-logic-search-rule-path") search))
         ((endp path) (cons (if reverse-p (proof-proof-symmetric (t2-book-logic-search-proof-object search) step) step)
                            search))
         ((equal (car path) "consequent")
          (t2-book-logic-search-check ((test (t2-book-logic-step-term step 1)))
            (t2-book-logic-search-let ((evidence (t2-book-logic-search-premise (1- n) search test tests (1- depth))))
              (if (not evidence)
                  (cons nil search)
                (t2-book-logic-search-check
                    ((next (t2-book-logic-modus-ponens (t2-book-logic-search-lib search) step evidence)))
                  (t2-book-logic-search-rule-path (1- n) search next (cdr path) reverse-p tests depth))))))
         (t (t2-book-logic-search-check ((parts (t2-book-logic-conjunct (t2-book-logic-search-lib search) step)))
              (t2-book-logic-search-rule-path (1- n) search (if (equal (car path) "first") (car parts) (cadr parts))
                                             (cdr path) reverse-p tests depth)))))

 (defun t2-book-logic-search-seed (n search step direction tests depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t2-book-logic-search-seed") search)
     (t2-book-logic-search-check ((literal (proof-step-first step)))
       (if (not (proof-is-call literal *library-implies*))
           (cons (if (eq direction :reverse) (proof-proof-symmetric (t2-book-logic-search-proof-object search) step) step)
                 search)
         (t2-book-logic-search-check ((test (proof-term-at literal 1)))
           (t2-book-logic-search-let ((evidence (t2-book-logic-search-premise (1- n) search test tests (1- depth))))
             (if (not evidence)
                 (cons nil search)
               (t2-book-logic-search-check
                   ((next (t2-book-logic-modus-ponens (t2-book-logic-search-lib search) step evidence)))
                 (t2-book-logic-search-seed (1- n) search next direction tests depth)))))))))

 (defun t2-book-logic-search-instance (n search term tests depth equations seeds)
   (declare (xargs :measure (nfix n)))
   (cond ((not (o< (nfix (1- n)) (nfix n))) (cons '(:failure "Fuel" "t2-book-logic-search-instance") search))
         ((endp seeds)
          (let ((rules (t2-book-logic-search-rules search)))
            (if (not rules)
                (cons '(:failure "failure" "") search)
              (t2-book-logic-search-instance-rules
               (1- n) search term tests depth
               (table-get (if equations (t2-book-logic-rules-equations rules) (t2-book-logic-rules-goals rules))
                            (t2-book-logic-head term) nil)))))
         (t (t2-book-logic-search-check ((direction (t2-book-logic-seed-direction (car seeds) term equations)))
              (t2-book-logic-search-let
                  ((step (if direction (t2-book-logic-search-seed (1- n) search (car seeds) direction tests depth)
                           (cons nil search))))
                (if step
                    (cons step search)
                  (t2-book-logic-search-instance (1- n) search term tests depth equations (cdr seeds))))))))

 (defun t2-book-logic-search-instance-rules (n search term tests depth rules)
   (declare (xargs :measure (nfix n)))
   (cond ((not (o< (nfix (1- n)) (nfix n))) (cons '(:failure "Fuel" "t2-book-logic-search-instance-rules") search))
         ((endp rules) (cons nil search))
         (t (t2-book-logic-search-check ((matched (t2-book-logic-match (t2-book-logic-rule-pattern (car rules)) term nil)))
              (t2-book-logic-search-let
                  ((step (if (not (car matched))
                             (cons nil search)
                           (t2-book-logic-search-let ((tick (t2-book-logic-search-tick search)))
                             (t2-book-logic-search-use-rule (1- n) search (car rules) (cdr matched) tests depth)))))
                (if step
                    (cons step search)
                  (t2-book-logic-search-instance-rules (1- n) search term tests depth (cdr rules))))))))

 (defun t2-book-logic-search-premise (n search goal tests depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t2-book-logic-search-premise") search)
     (t2-book-logic-search-let ((tick (t2-book-logic-search-tick search))
                                (known (t2-book-logic-search-find search tests goal)))
       (cond (known (cons known search))
             ((proof-is-call goal *proof-quote*)
              (cons (and (not (equal goal *proof-false*)) (t2-book-logic-search-quoted-truth search goal)) search))
             (t (let* ((key (list goal tests depth))
                       (premises (t2-book-logic-search-premises search))
                       (entry (assoc-equal key premises)))
                  (if (or (< depth 0) entry)
                      (cons (cdr entry) search)
                    (let* ((marked (update-nth 8 (table-put premises key nil) search))
                           (result (t2-book-logic-search-premise-body (1- n) marked goal tests depth))
                           (value (car result)) (after (cdr result)))
                      (if (t2-book-logic-search-stopped-p value)
                          result
                        (cons value (update-nth 8 (table-put (t2-book-logic-search-premises after) key value)
                                                after)))))))))))

 (defun t2-book-logic-search-premise-body (n search goal tests depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t2-book-logic-search-premise-body") search)
     (t2-book-logic-search-check ((conjunction (t2-book-logic-condition-p goal)))
       (cond (conjunction
              (t2-book-logic-search-let
                  ((left (t2-book-logic-search-premise (1- n) search (cadr goal) tests depth))
                   (right (if left (t2-book-logic-search-premise (1- n) search (caddr goal) tests depth)
                            (cons nil search))))
                (if (not right)
                    (cons nil search)
                  (let ((proof (t2-book-logic-search-proof-object search)))
                    (t2-book-logic-search-check ((selection (proof-proof-select proof goal left)))
                      (cons (proof-proof-transport proof right selection) search))))))
             ((proof-compound goal)
              (t2-book-logic-search-check
                  ((value (t2-book-logic-constant (t2-book-logic-search-lib search) goal))
                   (right (and value (t2-book-logic-step-term value 2))))
                (if (and value (equal right *proof-true*))
                    (cons (proof-proof-true-from-eq (t2-book-logic-search-proof-object search) value) search)
                  (t2-book-logic-search-instance (1- n) search goal tests (min depth 2) nil
                                                 (t2-book-logic-search-seeds search)))))
             (t (cons nil search)))))))

(defund t2-book-logic-search-replacement-unproved (n search term tests depth opened)
  (if (zp n)
      (cons '(:failure "Fuel" "t2-book-logic-search-replacement-unproved") search)
    (t2-book-logic-search-let ((known (t2-book-logic-search-assumed-equality search term tests)))
      (if known
          (cons known search)
        (t2-book-logic-search-let ((completion (t2-book-logic-search-completion search term tests opened)))
          (if completion
              (cons completion search)
            (t2-book-logic-search-check ((identity (t2-book-logic-search-identity (t2-book-logic-search-lib search) term)))
              (if identity
                  (cons identity search)
                (t2-book-logic-search-let
                    ((named (if (< depth 0) (cons nil search)
                              (t2-book-logic-search-instance (1- n) search term tests depth t
                                                             (t2-book-logic-search-seeds search)))))
                  (if named (cons named search) (t2-book-logic-search-unfold search term tests depth opened)))))))))))

(defund t2-book-logic-search-replacement-run (n search term tests depth opened)
  (if (zp n)
      (cons '(:failure "Fuel" "t2-book-logic-search-replacement-run") search)
    (t2-book-logic-search-let ((reply (t2-book-logic-search-hook search :replacement term tests depth opened)))
      (if (not (eq reply :base))
          (cons reply search)
        (t2-book-logic-search-check ((computed (t2-book-logic-constant (t2-book-logic-search-lib search) term)))
          (if computed
              (cons computed search)
            (t2-book-logic-search-let ((negative (t2-book-logic-search-find search tests (proof-neg term))))
              (if negative
                  (let ((proof (t2-book-logic-search-proof-object search)))
                    (t2-book-logic-search-check ((nil-or-true (proof-proof-nil-or-true proof term)))
                      (cons (proof-proof-discharge proof nil-or-true negative) search)))
                (t2-book-logic-search-let ((positive (t2-book-logic-search-find search tests term))
                                           (value (if positive (t2-book-logic-search-positive-value search term positive)
                                                    (cons nil search))))
                  (if value
                      (cons value search)
                    (t2-book-logic-search-replacement-unproved (1- n) search term tests depth opened)))))))))))

(mutual-recursion
 (defun t2-book-logic-search-normalize-run (n search term tests depth opened)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t2-book-logic-search-normalize-run") search)
     (t2-book-logic-search-let ((reply (t2-book-logic-search-hook search :normalize term tests depth opened)))
       (cond ((eq reply :base)
              (t2-book-logic-search-let ((tick (t2-book-logic-search-tick search)))
                (cond ((or (proof-is-call term *proof-quote*) (> (len opened) 9)) (cons nil search))
                      ((not (proof-compound term))
                       (t2-book-logic-search-let ((identity (t2-book-logic-search-assumed-equality search term tests)))
                         (if (not identity)
                             (cons nil search)
                           (t2-book-logic-search-check ((target (t2-book-logic-step-term identity 2)))
                             (t2-book-logic-search-normalize-follow (1- n) search identity nil target tests depth
                                                                    (append opened (list term)))))))
                      ((and (consp term) (proof-compound (t2-book-logic-head term)))
                       (t2-book-logic-search-check ((beta (proof-proof-beta (t2-book-logic-search-proof-object search) term))
                                                    (target (t2-book-logic-step-term beta 2)))
                         (t2-book-logic-search-normalize-follow (1- n) search beta nil target tests depth opened)))
                      ((proof-is-call term *proof-if*)
                       (t2-book-logic-search-normalize-if (1- n) search term tests depth opened))
                      (t (t2-book-logic-search-normalize-arguments (1- n) search term (cdr term) 1 nil tests depth opened)))))
             ((and (consp reply) (eq (car reply) :chain))
              (t2-book-logic-search-normalize-follow (1- n) search (cadr reply) nil (caddr reply)
                                                     tests depth (cadddr reply)))
             (t (cons reply search))))))

 (defun t2-book-logic-search-normalize-follow (n search prefix rest target tests depth opened)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t2-book-logic-search-normalize-follow") search)
     (t2-book-logic-search-let ((following (t2-book-logic-search-normalize-run (1- n) search target tests depth opened)))
       (cons (proof-proof-chain (t2-book-logic-search-proof-object search) prefix (append rest (list following))) search))))

 (defun t2-book-logic-search-normalize-if (n search term tests depth opened)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t2-book-logic-search-normalize-if") search)
     (t2-book-logic-search-check ((test (proof-term-at term 1)))
       (t2-book-logic-search-let ((test-eq (t2-book-logic-search-normalize-run (1- n) search test tests depth opened)))
         (t2-book-logic-search-check
             ((result (t2-book-logic-search-if-test (t2-book-logic-search-proof-object search) term test-eq))
              (current (if result (t2-book-logic-step-term result 2) term))
              (test (proof-term-at current 1)))
           (t2-book-logic-search-let ((selected (t2-book-logic-search-selection search current test tests)))
             (if (not selected)
                 (cons result search)
               (t2-book-logic-search-check
                   ((prefix (if result (proof-proof-chain (t2-book-logic-search-proof-object search) result (list selected))
                              selected))
                    (target (t2-book-logic-step-term selected 2)))
                 (t2-book-logic-search-normalize-follow (1- n) search prefix nil target tests depth opened)))))))))

 (defun t2-book-logic-search-normalize-arguments (n search term args index result tests depth opened)
   (declare (xargs :measure (nfix n)))
   (cond ((not (o< (nfix (1- n)) (nfix n))) (cons '(:failure "Fuel" "t2-book-logic-search-normalize-arguments") search))
         ((endp args)
          (t2-book-logic-search-check ((current (if result (t2-book-logic-step-term result 2) term)))
            (t2-book-logic-search-let ((replacement (t2-book-logic-search-replacement-run (1- n) search current tests depth opened)))
              (t2-book-logic-search-check ((target (and replacement (t2-book-logic-step-term replacement 2))))
                (if (and replacement (not (equal target current)))
                    (t2-book-logic-search-normalize-follow (1- n) search (or result replacement)
                                                           (list (and result replacement)) target tests depth
                                                           (append opened (list (t2-book-logic-head current))))
                  (cons (and result (proof-proof-tidy (t2-book-logic-search-proof-object search) result)) search))))))
         (t (t2-book-logic-search-let ((equality (t2-book-logic-search-normalize-run (1- n) search (car args) tests depth opened)))
              (t2-book-logic-search-check
                  ((next (t2-book-logic-search-rewrite-argument (t2-book-logic-search-proof-object search)
                                                               term result equality index)))
                (t2-book-logic-search-normalize-arguments (1- n) search term (cdr args) (1+ index)
                                                          next tests depth opened)))))))

(mutual-recursion
 (defun t2-book-logic-search-try (n search goal tests depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t2-book-logic-search-try") search)
     (t2-book-logic-search-let
         ((tick (t2-book-logic-search-tick search))
          (context (t2-book-logic-search-context search tests))
          (known (t2-book-logic-search-find search tests goal)))
       (cond (known (cons known search))
             ((proof-is-call goal *proof-quote*)
              (cons (and (not (equal goal *proof-false*)) (t2-book-logic-search-quoted-truth search goal)) search))
             (t (t2-book-logic-search-check
                    ((reflexive (t2-book-logic-reflexive-goal (t2-book-logic-search-proof-object search) goal)))
                  (if reflexive
                      (cons reflexive search)
                    (let ((key (list goal tests)) (failed-key (list goal tests depth))
                          (active (t2-book-logic-search-active search)))
                      (if (or (< depth 0) (member-equal key active)
                              (member-equal failed-key (t2-book-logic-search-failed search)))
                          (cons nil search)
                        (let* ((marked (update-nth 6 (append active (list key)) search))
                               (result (t2-book-logic-search-prove-active (1- n) marked goal tests depth))
                               (step (car result))
                               (finished (update-nth 6 active (cdr result))))
                          (cons step
                                (if step finished
                                  (update-nth 7 (append (t2-book-logic-search-failed finished) (list failed-key))
                                              finished)))))))))))))

 (defun t2-book-logic-search-prove-active (n search goal tests depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t2-book-logic-search-prove-active") search)
     (t2-book-logic-search-check ((identity (t2-book-logic-ac-goal (t2-book-logic-search-lib search) goal)))
       (if identity
           (cons identity search)
         (t2-book-logic-search-let
             ((named (t2-book-logic-search-instance (1- n) search goal tests depth nil (t2-book-logic-search-seeds search))))
           (if named
               (cons named search)
             (t2-book-logic-search-check ((wrapped (t2-book-logic-wrapper-equation (t2-book-logic-search-lib search) goal))
                                          (target (and wrapped (t2-book-logic-step-term wrapped 2))))
               (t2-book-logic-search-let
                   ((named (if wrapped (t2-book-logic-search-premise (1- n) search target tests (1- depth))
                             (cons nil search))))
                 (if named
                     (cons (proof-proof-transport (t2-book-logic-search-proof-object search) named wrapped) search)
                   (t2-book-logic-search-prove-active-form (1- n) search goal tests depth))))))))))

 (defun t2-book-logic-search-prove-active-form (n search goal tests depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t2-book-logic-search-prove-active-form") search)
     (t2-book-logic-search-check ((conjunction (t2-book-logic-condition-p goal)))
       (t2-book-logic-search-let ((both (if conjunction (t2-book-logic-search-premise (1- n) search goal tests depth)
                                        (cons nil search))))
         (cond (both (cons both search))
               ((proof-is-call goal *library-implies*)
                (t2-book-logic-search-check ((parts (proof-list-of-length (cdr goal) 2)))
                  (let ((test (car parts)) (consequence (cadr parts)))
                    (t2-book-logic-search-let
                        ((valid (t2-book-logic-search-try (1- n) search consequence (append tests (list (list test t))) depth)))
                      (cons (and valid (t2-book-logic-search-implication (t2-book-logic-search-proof-object search) goal test valid))
                            search)))))
               (t (t2-book-logic-search-let ((equality (t2-book-logic-search-normalize-run (1- n) search goal tests depth nil)))
                    (t2-book-logic-search-check ((current (if equality (t2-book-logic-step-term equality 2) goal)))
                      (t2-book-logic-search-let
                          ((step (if (equal current goal) (cons nil search)
                                   (t2-book-logic-search-try (1- n) search current tests depth))))
                        (cond (step (cons (proof-proof-transport (t2-book-logic-search-proof-object search) step equality) search))
                              ((equal depth 0) (cons nil search))
                              (t (t2-book-logic-search-split (1- n) search current equality tests depth))))))))))))

 (defun t2-book-logic-search-split (n search current equality tests depth)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t2-book-logic-search-split") search)
     (t2-book-logic-search-check ((test (t2-book-logic-search-first-test search current)))
       (if (not (t2-book-logic-term-true-p test))
           (cons nil search)
         (t2-book-logic-search-let
             ((positive (t2-book-logic-search-find search tests test))
              (negative (if positive (cons nil search) (t2-book-logic-search-find search tests (proof-neg test)))))
           (if (or positive negative)
               (cons nil search)
             (t2-book-logic-search-let
                 ((yes (t2-book-logic-search-try (1- n) search current (append tests (list (list test t))) (1- depth)))
                  (no (if yes (t2-book-logic-search-try (1- n) search current (append tests (list (list test nil))) (1- depth))
                        (cons nil search))))
               (if (not no)
                   (cons nil search)
                 (let ((proof (t2-book-logic-search-proof-object search)))
                   (t2-book-logic-search-check ((joined (proof-proof-cases proof test yes no)))
                     (cons (if equality (proof-proof-transport proof joined equality) joined) search))))))))))))


(defun t2-book-logic-search-try-prove (search goal tests depth)
  (t2-book-logic-search-try 1000000 search goal tests depth))

(defun t2-book-logic-search-proof (search goal tests depth)
  (let ((result (t2-book-logic-search-try-prove search goal tests depth)))
    (if (car result)
        result
      (cons '(:failure "Unproved" "") (cdr result)))))

(defun t2-book-logic-search-restore-context (before after tests old)
  (let ((contexts (t2-book-logic-search-contexts after)))
    (if (not old)
        (update-nth 5 (table-delete contexts tests) after)
      (let ((lib (t2-book-logic-search-lib after)) (context (cdr old)))
        (t2-book-logic-search-with-context
         after tests (if (equal (t2-tactics-ruler-facts-proof context) (t2-book-logic-search-lib before))
                         (t2-tactics-ruler-facts-with-proof context lib)
                       context))))))

(defun t2-book-logic-search-run-with-context (method search term context depth opened)
  (let* ((tests (t2-tactics-ruler-facts-tests context))
         (existing (assoc-equal tests (t2-book-logic-search-contexts search)))
         (with-context (t2-book-logic-search-with-context search tests context))
         (result (if (eq method :normalize)
                     (t2-book-logic-search-normalize-run 1000000 with-context term tests depth opened)
                   (t2-book-logic-search-replacement-run 1000000 with-context term tests depth opened)))
         (next (cdr result))
         (final-context (t2-book-logic-search-current-context next tests))
         (final-search (if (and existing (equal (cdr existing) context)) next
                         (t2-book-logic-search-restore-context search next tests existing))))
    (cons (car result) (cons final-search final-context))))

(defun t2-book-logic-search-normalize (search term context depth opened)
  (t2-book-logic-search-run-with-context :normalize search term context depth opened))

(defun t2-book-logic-search-replacement (search term context depth opened)
  (t2-book-logic-search-run-with-context :replacement search term context depth opened))
