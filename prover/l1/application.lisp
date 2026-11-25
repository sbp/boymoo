(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-application-apply* (proof-sym "APPLY$" "ACL2"))
(defconst *l1-application-apply-primitive* (proof-sym "APPLY$-PRIMP" "ACL2"))
(defconst *l1-application-badge* (proof-sym "BADGE" "ACL2"))
(defconst *l1-application-badge-primitive* (proof-sym "BADGE-PRIM" "ACL2"))

(defconst *l1-application-evaluator*
  (list *l1-application-apply*
        (proof-sym "APPLY$-LAMBDA" "ACL2")
        (proof-sym "ASSOC-EQUAL" "ACL2")
        (proof-sym "EV$" "ACL2")
        (proof-sym "EV$-LIST" "ACL2")
        (proof-sym "HONS-EQUAL" "ACL2")
        (proof-sym "LAMBDA-OBJECT-BODY" "ACL2")
        (proof-sym "LAMBDA-OBJECT-FORMALS" "ACL2")
        (proof-sym "PAIRLIS$" "ACL2")
        *termination-return-last*
        (proof-sym "SUITABLY-TAMEP-LISTP" "ACL2")
        (proof-sym "TAMEP" "ACL2")
        (proof-sym "ZP" "ACL2")
        (proof-cl "ATOM")
        (proof-cl "ENDP")
        (proof-cl "EQ")
        (proof-cl "EQL")
        *proof-not*
        (proof-cl "NULL")))

(defun l1-application-elements-visit (term items)
  (declare (xargs :measure (acl2-count term)))
  (cond ((proof-is-call term *proof-cons*)
         (if (consp (cddr term))
             (l1-application-elements-visit (caddr term) (cons (cadr term) items))
           '(:failure "failure" "")))
        ((equal term *proof-false*) (reverse items))
        (t :none)))

(defun l1-application-elements (term)
  (l1-application-elements-visit term nil))

(defun l1-application-consp-cons (proof test)
  (and (proof-is-call test *proof-consp*)
    (proof-with-checked-results ((argument (proof-term-at test 1)))
      (and (proof-is-call argument *proof-cons*)
        (proof-proof-fact proof "consp-cons"
                          (seq-zip (list *library-x* *library-y*) (cdr argument)))))))

; The set representation orders members by the text read by ACL2.
(mutual-recursion
 (defun l1-application-set-key (value)
   (declare (xargs :measure (1+ (* 2 (acl2-count value)))))
   (cond ((consp value)
          (concatenate 'string "(" (text-join " " (l1-application-set-keys value)) ")"))
         ((stringp value)
          (concatenate 'string "\""
                       (text-replace (text-replace value "\\" "\\\\") "\"" "\\\"")
                       "\""))
         ((integerp value) (decimal-text value))
         ((rationalp value)
          (concatenate 'string (decimal-text (numerator value)) "/" (decimal-text (denominator value))))
         ((eq value t) "t")
         (t "nil")))
 (defun l1-application-set-keys (values)
   (declare (xargs :measure (* 2 (acl2-count values))))
   (if (endp values)
       nil
     (cons (l1-application-set-key (car values))
           (l1-application-set-keys (cdr values))))))

(defun l1-application-set-members (pairs)
  (if (endp pairs)
      nil
    (cons (cadar pairs) (l1-application-set-members (cdr pairs)))))

(defun l1-application-set-order (members)
  (l1-application-set-members
   (seq-sorted (seq-zip (l1-application-set-keys members) members))))

(mutual-recursion
 (defun l1-application-value-functions-term (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
         ((endp term) '(:failure "failure" ""))
         ((proof-compound (car term))
          '(:failure "unsupported-application" ""))
         (t (proof-with-checked-results
                ((functions (l1-application-value-functions-arguments (cdr term))))
              (add-to-set-equal (car term) functions)))))
 (defun l1-application-value-functions-arguments (arguments)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (proof-with-checked-results
         ((first (l1-application-value-functions-term (car arguments)))
          (rest (l1-application-value-functions-arguments (cdr arguments))))
       (union-equal first rest)))))

(defun l1-application-value-functions (term)
  (proof-with-checked-results ((functions (l1-application-value-functions-term term)))
    (l1-application-set-order functions)))

(defun l1-application-application-init (proof function badges extra-definitions definitions)
  (let ((definitions (if (eq definitions :default) *l1-application-evaluator* definitions)))
    (list :l1-application proof (proof-quote function) badges
          (l1-application-set-order (union-equal definitions extra-definitions)) :base)))

(defun l1-application-application-proof (application)
  (cadr application))

(defun l1-application-application-function (application)
  (caddr application))

(defun l1-application-application-badges (application)
  (cadddr application))

(defun l1-application-application-definitions (application)
  (nth 4 application))

(defun l1-application-application-kind (application)
  (nth 5 application))

(defun l1-application-application-with-kind (application kind)
  (list :l1-application
        (l1-application-application-proof application)
        (l1-application-application-function application)
        (l1-application-application-badges application)
        (l1-application-application-definitions application)
        kind))

(defun l1-application-warrant-cdr (datum)
  (let ((tail (cdr datum)))
    (cond ((endp tail) *proof-nil*)
          ((and (endp (cdr tail)) (true-listp (car tail)))
           (proof-with-checked-results ((tag (proof-term-at (car tail) 0)))
             (if (equal tag "dot") (proof-term-at (car tail) 1) tail)))
          (t tail))))

(defun l1-application-warrant-constant (proof term)
  (proof-with-checked-results ((parts (proof-constant-call-parts term)))
    (let ((head (car parts))
          (args (cdr parts)))
      (if (not (and (equal (len args) 1) (proof-is-call (car args) *proof-quote*)))
          (proof-proof-constant-base proof term)
        (proof-with-checked-results ((datum (proof-term-at (car args) 1)))
          (cond
           ((equal head (proof-cl "SYMBOLP"))
            (proof-with-checked-results
                ((tag (and (true-listp datum) (proof-term-at datum 0))))
              (proof-proof-compute proof term
                                   (if (equal tag "sym") *proof-t* *proof-nil*))))
           ((member-equal head (list *library-car* *library-cdr*))
            (proof-with-checked-results
                ((value (cond ((not (proof-compound datum)) *proof-nil*)
                              ((equal head *library-car*) (proof-term-at datum 0))
                              (t (l1-application-warrant-cdr datum)))))
              (proof-proof-compute proof term value)))
           (t (proof-proof-constant-base proof term))))))))

(defun l1-application-proof-constant (proof term)
  (if (eq (proof-proof-kind proof) :l1-warrant)
      (l1-application-warrant-constant proof term)
    (proof-proof-constant proof term)))

(defconst *l1-application-warrant-tame-function* (proof-sym "TAMEP-FUNCTIONP" "ACL2"))
(defconst *l1-application-warrant-trivial-code*
  (proof-quote (list (proof-cl "LAMBDA") *proof-nil* *proof-false*)))
(defconst *l1-application-warrant-tame-example* (proof-sym "L1-TAME-EXAMPLE" "ACL2"))
(defconst *l1-application-warrant-definitions*
  (list *library-implies* *proof-not* *termination-return-last*
        (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "EQ")
        (proof-cl "EQL") (proof-cl "NULL")
        (proof-sym "LAMBDA-OBJECT-SHAPEP" "ACL2")
        (proof-sym "LAMBDA-OBJECT-FORMALS" "ACL2")
        (proof-sym "LAMBDA-OBJECT-BODY" "ACL2")
        (proof-sym "SYMBOL-LISTP" "ACL2")
        *l1-application-warrant-tame-function* (proof-sym "TAMEP" "ACL2")))

(mutual-recursion
 (defun l1-application-warrant-simplify-visit (n proof term evidence definitions)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "l1-application-warrant-simplify-visit"))
         ((proof-is-call term *l1-application-warrant-tame-function*)
          (proof-with-checked-results
              ((argument (proof-term-at term 1))
               (known (and (equal argument *l1-application-warrant-trivial-code*)
                           (equal (cdr (assoc-equal *l1-application-warrant-tame-example*
                                                    (proof-proof-facts proof)))
                                  (list (proof-eq term *proof-true*)))
                           (proof-proof-fact proof *l1-application-warrant-tame-example* nil)))
               (reduced (l1-application-warrant-simplify-visit
                         (1- n) proof argument evidence definitions))
               (value (and reduced (proof-rewritten-term reduced))))
            (cond
             (known known)
             ((equal value *l1-application-warrant-trivial-code*)
              (proof-with-checked-results
                  ((trivial (l1-application-warrant-simplify-visit
                             (1- n) proof
                             (list *l1-application-warrant-tame-function*
                                   *l1-application-warrant-trivial-code*)
                             nil *l1-application-warrant-definitions*))
                   (reversed (proof-proof-symmetric proof reduced))
                   (rewritten (proof-proof-rewrite proof trivial reversed '(1 1 1))))
                (proof-proof-tidy proof rewritten)))
             (t (l1-application-warrant-simplify-base (1- n) proof term evidence definitions)))))
         (t (l1-application-warrant-simplify-base (1- n) proof term evidence definitions))))
 (defun l1-application-warrant-simplify-base (n proof term evidence definitions)
   (declare (xargs :measure (nfix n)))
   (let ((head (car term)))
     (cond
      ((zp n) '(:failure "fuel" "l1-application-warrant-simplify-base"))
      ((or (not (proof-compound term)) (equal head *proof-quote*)) nil)
      ((endp term) '(:failure "failure" ""))
      ((or (proof-compound head) (member-equal head definitions))
       (proof-with-checked-results
           ((opened (proof-simplify-expansion proof term))
            (next (l1-application-warrant-simplify-visit
                   (1- n) proof (cadr opened) evidence definitions)))
         (proof-proof-chain proof (car opened) (list next))))
      ((equal head *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at term 1))
            (first (l1-application-warrant-simplify-visit (1- n) proof test evidence definitions))
            (path (proof-simplify-if-path proof term first evidence)))
         (if (eq (car path) :simplify)
             (proof-with-checked-results
                 ((next (l1-application-warrant-simplify-visit
                         (1- n) proof (caddr path) evidence definitions)))
               (proof-proof-chain proof (cadr path) (list next)))
           path)))
      (t
       (proof-with-checked-results
           ((result (l1-application-warrant-simplify-arguments
                     (1- n) proof term (cdr term) 1 nil evidence definitions))
            (current (if result (proof-rewritten-term result) term))
            (constant (l1-application-warrant-constant proof current)))
         (cond ((not constant) result)
               (result (proof-proof-chain proof result (list constant)))
               (t constant)))))))
 (defun l1-application-warrant-simplify-arguments (n proof term args index result evidence definitions)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "l1-application-warrant-simplify-arguments"))
         ((endp args) result)
         (t (proof-with-checked-results
                ((equality (l1-application-warrant-simplify-visit
                            (1- n) proof (car args) evidence definitions))
                 (next (proof-simplify-argument-result proof term index result equality)))
              (l1-application-warrant-simplify-arguments
               (1- n) proof term (cdr args) (1+ index) next evidence definitions))))))

(defun l1-application-proof-simplify (proof term evidence definitions)
  (if (eq (proof-proof-kind proof) :l1-warrant)
      (l1-application-warrant-simplify-visit 1000000 proof term evidence definitions)
    (proof-proof-simplify proof term evidence definitions)))

(defund l1-application-warrant-prove-step (proof term evidence definitions)
  (if (equal term *proof-true*)
      (proof-proof-prove proof term evidence definitions)
    (proof-with-checked-results ((premise (proof-find-evidence evidence (list term))))
      (if premise
          premise
        (proof-with-checked-results
            ((equality (l1-application-proof-simplify proof term evidence definitions))
             (value (and equality (proof-rewritten-term equality))))
          (cond ((or (not equality) (equal value term))
                 (proof-with-checked-results ((written (proof-write term)))
                   '(:failure "unproved" "")))
                ((equal value *proof-true*) (proof-proof-true-from-eq proof equality))
                (t (list :transport value equality))))))))

(defun l1-application-warrant-prove-visit (n proof term evidence definitions)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "l1-application-warrant-prove-visit")
    (let ((result (l1-application-warrant-prove-step proof term evidence definitions)))
      (if (eq (car result) :transport)
          (proof-with-checked-results
              ((step (l1-application-warrant-prove-visit
                      (1- n) proof (cadr result) evidence definitions)))
            (proof-proof-transport proof step (caddr result)))
        result))))

(defun l1-application-proof-prove (proof term evidence definitions)
  (if (eq (proof-proof-kind proof) :l1-warrant)
      (l1-application-warrant-prove-visit 1000000 proof term evidence definitions)
    (proof-proof-prove proof term evidence definitions)))

(defun l1-application-unproved-p (result)
  (and (failure-p result)
       (or (equal (cadr result) "unproved")
           (equal (cadr result) "value"))))

(defun l1-application-selector-fact (proof name arguments)
  (proof-proof-fact proof (proof-sym name "ACL2")
                    (seq-zip (list *library-x* *library-y*) arguments)))

(defun l1-application-application-selector (proof term head name)
  (and (proof-is-call term head)
    (proof-with-checked-results ((argument (proof-term-at term 1)))
      (and (proof-is-call argument *proof-cons*)
        (l1-application-selector-fact proof name (cdr argument))))))

(defun l1-application-application-badge-assumption (application term designator)
  (and (proof-is-call designator *proof-quote*)
    (proof-with-checked-results ((function (proof-term-at designator 1)))
      (let ((badge (assoc-equal function (l1-application-application-badges application))))
        (and badge
          (proof-proof-assume (l1-application-application-proof application)
                              (proof-eq term (proof-quote (cdr badge))) t))))))

(defun l1-application-application-apply-assumption (application term designator)
  (and (and (proof-is-call designator *proof-quote*)
             (not (equal designator (l1-application-application-function application))))
    (proof-with-checked-results ((function (proof-term-at designator 1)))
      (let ((badge (assoc-equal function (l1-application-application-badges application))))
        (and badge
          (proof-with-checked-results
              ((arguments (proof-term-at term 2))
               (actuals (l1-application-elements arguments)))
            (and (not (eq actuals :none))
              (proof-with-checked-results ((arity (proof-term-at (cdr badge) 1)))
                (and (equal (len actuals) arity)
                  (proof-proof-assume (l1-application-application-proof application)
                                      (proof-eq term (cons function actuals)) t))))))))))

(defun l1-application-application-base-initial (application term)
  (let ((proof (l1-application-application-proof application)))
    (proof-with-checked-results
        ((head (l1-application-application-selector proof term *library-car* "CAR-CONS"))
         (tail (if head
                   nil
                 (l1-application-application-selector proof term *library-cdr* "CDR-CONS"))))
      (cond (head head)
            (tail tail)
            ((equal term (list *l1-application-apply-primitive*
                               (l1-application-application-function application)))
             (proof-proof-nil-or-true proof term))
            (t
             (proof-with-checked-results
                 ((assumed
                   (cond ((proof-is-call term *l1-application-badge*)
                          (proof-with-checked-results ((designator (proof-term-at term 1)))
                            (l1-application-application-badge-assumption application term designator)))
                         ((proof-is-call term *l1-application-apply*)
                          (proof-with-checked-results ((designator (proof-term-at term 1)))
                            (l1-application-application-apply-assumption application term designator)))
                         (t nil))))
               (if assumed assumed (l1-application-proof-constant proof term))))))))

(defun l1-application-application-lambda-initial (application term)
  (let ((proof (l1-application-application-proof application)))
    (proof-with-checked-results ((argument (proof-term-at term 1)))
      (if (not (proof-is-call argument *proof-cons*))
          (l1-application-application-base-initial application term)
        (proof-with-checked-results
            ((cons-proof (proof-proof-fact proof "consp-cons"
                                           (seq-zip (list *library-x* *library-y*) (cdr argument))))
             (rule (proof-proof-fact proof "consp-not-symbolp"
                                     (list (list *library-x* argument))))
             (choice (proof-proof-nil-or-true proof term))
             (non-symbol (proof-proof-modus-ponens proof rule cons-proof)))
          (proof-proof-discharge proof choice non-symbol))))))

(defund l1-application-application-initial (application term)
  (if (and (eq (l1-application-application-kind application) :lambda)
           (proof-is-call term (proof-cl "SYMBOLP")))
      (l1-application-application-lambda-initial application term)
    (l1-application-application-base-initial application term)))

(defun l1-application-application-base-choose-branch (application term)
  (let ((proof (l1-application-application-proof application)))
    (proof-with-checked-results ((parts (proof-list-of-length (cdr term) 3)))
      (let ((test (car parts))
            (yes (cadr parts))
            (no (caddr parts)))
        (cond ((equal test *proof-true*) (l1-application-proof-simplify proof term nil nil))
              ((equal test *proof-false*)
               (proof-proof-fact proof "if-nil" (list (list *library-y* yes)
                                                     (list *library-z* no))))
              (t (proof-with-checked-results ((evidence (l1-application-consp-cons proof test)))
                   (and evidence (proof-proof-select proof term evidence)))))))))

(defund l1-application-application-choose-branch (application term)
  (if (not (eq (l1-application-application-kind application) :literal))
      (l1-application-application-base-choose-branch application term)
    (proof-with-checked-results ((test (proof-term-at term 1)))
      (if (and (proof-is-call test *proof-quote*)
               (not (member-equal test (list *proof-true* *proof-false*))))
          (let ((proof (l1-application-application-proof application)))
            (proof-with-checked-results
                ((found (proof-proof-nil-or-true proof test))
                 (literal (proof-step-first found))
                 (computed (proof-proof-compute proof literal *proof-nil*))
                 (rewritten (proof-proof-rewrite proof found computed '(1)))
                 (non-nil (proof-proof-tidy proof rewritten)))
              (proof-proof-select proof term non-nil)))
        (l1-application-application-base-choose-branch application term)))))

(mutual-recursion
 (defun l1-application-application-reduce-visit (n application term)
   (declare (xargs :measure (nfix n)))
   (let ((proof (l1-application-application-proof application)))
     (cond
      ((zp n) '(:failure "fuel" "l1-application-application-reduce-visit"))
      ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
      ((endp term) '(:failure "failure" ""))
      ((or (proof-compound (car term)) (proof-is-call term *termination-return-last*))
       (proof-with-checked-results
           ((expansion (proof-simplify-expansion proof term))
            (reduced (l1-application-application-reduce-visit (1- n) application (cadr expansion))))
         (proof-proof-chain proof (car expansion) (list reduced))))
      ((proof-is-call term *proof-if*)
       (proof-with-checked-results
           ((equality (l1-application-application-arguments-visit (1- n) application term '(1) nil))
            (current (if equality (proof-rewritten-term equality) term))
            (branch (l1-application-application-choose-branch application current))
            (reduced
             (if branch
                 (proof-with-checked-results
                     ((value (proof-rewritten-term branch))
                      (value-proof (l1-application-application-reduce-visit (1- n) application value)))
                   (proof-proof-chain proof branch (list value-proof)))
               (l1-application-application-arguments-visit (1- n) application current '(2 3) nil))))
         (if equality (proof-proof-chain proof equality (list reduced)) reduced)))
      (t
       (proof-with-checked-results
           ((positions (seq-range 1 (len term) 1))
            (equality (l1-application-application-arguments-visit (1- n) application term positions nil))
            (current (if equality (proof-rewritten-term equality) term))
            (initial (l1-application-application-initial application current))
            (reduced
             (if initial
                 initial
               (proof-with-checked-results ((head (proof-term-at current 0)))
                 (and (member-equal head (l1-application-application-definitions application))
                   (proof-with-checked-results
                       ((opened (proof-simplify-expansion proof current))
                        (rest (l1-application-application-reduce-visit
                               (1- n) application (cadr opened))))
                     (proof-proof-chain proof (car opened) (list rest))))))))
         (if equality (proof-proof-chain proof equality (list reduced)) reduced))))))
 (defun l1-application-application-arguments-visit (n application term positions step)
   (declare (xargs :measure (nfix n)))
   (let ((proof (l1-application-application-proof application)))
     (cond
      ((endp positions) (and step (proof-proof-tidy proof step)))
      ((zp n) '(:failure "fuel" "l1-application-application-arguments-visit"))
      (t
       (let* ((index (car positions))
              (actual-index (if (< index 0) (+ (len term) index) index)))
         (proof-with-checked-results
             ((arg (if (< actual-index 0)
                       '(:failure "failure" "")
                     (proof-term-at term actual-index)))
              (equality (l1-application-application-reduce-visit (1- n) application arg))
              (step (if (not equality)
                        step
                      (proof-with-checked-results
                          ((first (or step (proof-proof-reflexive proof term))))
                        (proof-proof-rewrite proof first equality (list 1 2 index))))))
           (l1-application-application-arguments-visit (1- n) application term
                                                       (cdr positions) step))))))))

(defun l1-application-application-reduce (application term)
  (l1-application-application-reduce-visit 1000000 application term))

(defun l1-application-application-arguments (application term positions)
  (l1-application-application-arguments-visit 1000000 application term positions nil))

(defun l1-application-select-args (args size)
  (declare (xargs :measure (nfix size)))
  (if (zp size)
      nil
    (cons (list *library-car* args)
          (l1-application-select-args (list *library-cdr* args) (1- size)))))

(defun l1-application-component (data index)
  (if (or (< index 0) (< 9223372036854775807 index))
      '(:failure "failure" "")
    (list *library-car* (lexer-tail data index))))

(defun l1-application-ones (n)
  (declare (xargs :measure (nfix n)))
  (if (zp n) nil (cons 1 (l1-application-ones (1- n)))))

(defun l1-application-select-component-tails (proof data depth step)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (proof-with-checked-results
          ((head (l1-application-selector-fact proof "CAR-CONS" (cdr data))))
        (proof-proof-chain proof step (list head)))
    (proof-with-checked-results
        ((tail (l1-application-selector-fact proof "CDR-CONS" (cdr data)))
         (rewritten (proof-proof-rewrite proof step tail
                                         (list* 1 2 (l1-application-ones depth))))
         (next (proof-term-at data 2)))
      (l1-application-select-component-tails proof next (1- depth) rewritten))))

(defun l1-application-select-component (proof data index)
  (proof-with-checked-results
      ((projection (l1-application-component data index))
       (step (proof-proof-reflexive proof projection)))
    (l1-application-select-component-tails proof data index step)))

(defun l1-application-lookup-definition (proof function)
  (let ((definition (assoc-equal function (proof-proof-definitions proof))))
    (if definition
        (cdr definition)
      '(:failure "failure" ""))))

(defun l1-application-primitive-table (proof)
  (proof-with-checked-results
      ((definition (l1-application-lookup-definition proof *l1-application-badge-primitive*))
       (body (proof-term-at definition 1))
       (first (proof-term-at body 1))
       (expression (proof-term-at first 2)))
    (proof-term-at expression 1)))

(defun l1-application-primitive-badges (table functions badges)
  (if (endp table)
      badges
    (proof-with-checked-results ((name (proof-term-at (car table) 0)))
      (l1-application-primitive-badges
       (cdr table) functions
       (if (member-equal name functions)
           (table-put badges name (cdar table))
         badges)))))

(defun l1-application-ordinary-badges-p (badges)
  (or (endp badges)
      (and (equal (nthcdr 3 (cdar badges)) (list (list "dot" *proof-t*)))
           (l1-application-ordinary-badges-p (cdr badges)))))

(defun l1-application-actual-bindings (formals actuals bindings)
  (if (or (endp formals) (endp actuals))
      bindings
    (l1-application-actual-bindings
     (cdr formals) (cdr actuals) (table-put bindings (car formals) (car actuals)))))

(defun l1-application-quoted-application-open (proof function args formals simpler)
  (proof-with-checked-results
      ((opened (proof-proof-unfold proof (cons function (l1-application-select-args args (len formals))))))
    (if (not simpler)
        opened
      (proof-with-checked-results
          ((literal (proof-step-first opened))
           (application (proof-term-at literal 1))
           (bindings (l1-application-actual-bindings formals (cdr application) nil))
           (instance (proof-proof-instantiate proof simpler (table-items bindings))))
        (proof-proof-chain proof opened (list instance))))))

(defun l1-application-quoted-application-match (proof evaluation right-step expected)
  (if (not right-step)
      '(:failure "failure" "")
    (proof-with-checked-results ((value (proof-rewritten-term right-step)))
      (if (equal value expected)
          right-step
        (proof-with-checked-results
            ((normal (l1-application-application-reduce evaluation expected))
             (reduced (l1-application-application-reduce evaluation value))
             (reversed (and normal (proof-proof-symmetric proof normal)))
             (right-step (proof-proof-chain proof right-step (list reduced reversed)))
             (value (proof-rewritten-term right-step)))
          (if (equal value expected) right-step '(:failure "failure" "")))))))

(defun l1-application-quoted-application (proof function args recursive-badge expected code)
  (let ((read-code (or (null code) (eq code :none)))
        (recursive (and recursive-badge (not (eq recursive-badge :none))))
        (check-result (and expected (not (eq expected :none)))))
    (proof-with-checked-results
        ((definition (l1-application-lookup-definition proof function))
         (parts (proof-list-of-length definition 2))
         (formals (car parts))
         (body (cadr parts))
         (simpler (and read-code
                       (l1-application-proof-simplify proof body nil (list *termination-return-last*))))
         (code (if read-code (if simpler (proof-rewritten-term simpler) body) code))
         (functions (l1-application-value-functions code))
         (functions (if (not recursive)
                        functions
                      (if (member-equal function functions)
                          (remove-equal function functions)
                        '(:failure "failure" ""))))
         (table (l1-application-primitive-table proof))
         (badges (l1-application-primitive-badges table functions nil)))
      (if (not (and (equal (len badges) (len functions))
                    (l1-application-ordinary-badges-p badges)))
          '(:failure "unsupported-application" "")
        (proof-with-checked-results
            ((badges (if recursive
                         (proof-with-checked-results ((badge (proof-term-at recursive-badge 1)))
                           (table-put badges function badge))
                       badges))
             (left (proof-quote function))
             (right (proof-quote (list (proof-cl "LAMBDA") (or formals *proof-nil*) code)))
             (evaluation (l1-application-application-init proof function badges nil :default))
             (left-step (l1-application-application-reduce evaluation
                                                           (list *l1-application-apply* left args)))
             (right-step (l1-application-application-reduce evaluation
                                                            (list *l1-application-apply* right args)))
             (right-step
              (if check-result
                  (l1-application-quoted-application-match proof evaluation right-step expected)
                (proof-with-checked-results
                    ((opened (l1-application-quoted-application-open proof function args formals simpler))
                     (reversed (proof-proof-symmetric proof opened)))
                  (if right-step
                      (proof-proof-chain proof right-step (list reversed))
                    '(:failure "failure" ""))))))
          (list left right left-step right-step))))))
