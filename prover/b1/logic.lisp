(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-logic-symbolp* (proof-cl "SYMBOLP"))
(defconst *b1-logic-stringp* (proof-cl "STRINGP"))
(defconst *b1-logic-symbol-name* (proof-cl "SYMBOL-NAME"))
(defconst *b1-logic-symbol-package* (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2"))
(defconst *b1-logic-atom* (proof-cl "ATOM"))
(defconst *b1-logic-endp* (proof-cl "ENDP"))
(defconst *b1-logic-eql* (proof-cl "EQL"))
(defconst *b1-logic-eq* (proof-cl "EQ"))
(defconst *b1-logic-return-last* (proof-sym "RETURN-LAST" "ACL2"))
(defconst *b1-logic-zp* (proof-sym "ZP" "ACL2"))
(defconst *b1-logic-the-check* (proof-sym "THE-CHECK" "ACL2"))

(defconst *b1-logic-ground-not-nil*
  (proof-proof-not-nil (proof-proof-init)))

(defconst *b1-logic-not-nil-premises*
  (let* ((proof (proof-proof-init))
         (facts (proof-proof-facts proof)))
    (list (assoc-equal *proof-not* (proof-proof-definitions proof))
          (assoc-equal *proof-not* facts)
          (assoc-equal '("str" "non-nil-true") facts))))

(defun b1-logic-proof-not-nil (proof)
  (let ((facts (proof-proof-facts proof))
        (definitions (proof-proof-definitions proof))
        (primitives (proof-proof-primitives proof)))
    (if (and (equal (assoc-equal *proof-not* definitions) (car *b1-logic-not-nil-premises*))
             (equal (assoc-equal *proof-not* facts) (cadr *b1-logic-not-nil-premises*))
             (equal (assoc-equal '("str" "non-nil-true") facts) (caddr *b1-logic-not-nil-premises*))
             (member-equal *proof-if* primitives)
             (member-equal *proof-equal* primitives))
        *b1-logic-ground-not-nil*
      (proof-proof-not-nil proof))))

(defun b1-logic-ascii-characters-p (chars)
  (or (endp chars)
      (and (<= (char-code (car chars)) 127)
           (b1-logic-ascii-characters-p (cdr chars)))))

(defun b1-logic-step-first (step)
  (cond ((failure-p step) step)
        ((proof-step-p step) (proof-step-first step))
        (t '(:failure "failure" ""))))

(defun b1-logic-step-at (step index)
  (proof-with-checked-results ((first (b1-logic-step-first step)))
    (proof-term-at first index)))

(mutual-recursion
 (defun b1-logic-match (pattern term bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (cond ((not (proof-compound pattern))
          (let ((previous (assoc-equal pattern bindings)))
            (if previous
                (cons (equal (cdr previous) term) bindings)
              (cons t (table-put bindings pattern term)))))
         ((proof-is-call pattern *proof-quote*)
          (cons (equal pattern term) bindings))
         ((or (not (proof-compound term)) (not (equal (len pattern) (len term))))
          (cons nil bindings))
         ((endp pattern) '(:failure "failure" ""))
         ((not (equal (car pattern) (car term))) (cons nil bindings))
         (t (b1-logic-match-arguments (cdr pattern) (cdr term) bindings))))
 (defun b1-logic-match-arguments (patterns terms bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (endp patterns)
       (cons t bindings)
     (let ((result (b1-logic-match (car patterns) (car terms) bindings)))
       (cond ((failure-p result) result)
             ((not (car result)) result)
             (t (b1-logic-match-arguments (cdr patterns) (cdr terms)
                                          (cdr result))))))))

(defun b1-logic-matching-candidates (candidates goal)
  (if (endp candidates)
      nil
    (let ((candidate (car candidates)))
      (if (cadddr candidate)
          (b1-logic-matching-candidates (cdr candidates) goal)
        (proof-with-checked-results
         ((match (b1-logic-match (caddr candidate) goal nil)))
         (if (car match)
             (cadr candidate)
           (b1-logic-matching-candidates (cdr candidates) goal)))))))

(defun b1-logic-general-claims (claims head)
  (let ((group (assoc-equal (list head :none) claims))
        (adapted (table-get claims (list head nil) nil)))
    (if group
        (cdr group)
      (and (eq (caar adapted) :rule) adapted))))

(defun b1-logic-matching-claim (claims goal)
  (if (endp claims)
      nil
    (proof-with-checked-results
     ((head (if (consp goal) (car goal) '(:failure "failure" ""))))
     (let* ((first (cadr goal))
            (specific (and (consp first) (proof-compound first)))
            (exact (if specific
                       (table-get claims (list head (car first)) nil)
                     (b1-logic-general-claims claims head))))
       (proof-with-checked-results
        ((matched (b1-logic-matching-candidates (reverse exact) goal)))
        (if (or matched (not specific))
            matched
          (b1-logic-matching-candidates
           (reverse (b1-logic-general-claims claims head)) goal)))))))

(defun b1-logic-equal-to (equality)
  (list :equal-to equality))

(defun b1-logic-equal-to-rule (term equality)
  (proof-with-checked-results ((left (b1-logic-step-at equality 1)))
    (and (equal term left) equality)))

(defun b1-logic-rational-value (value)
  (cond ((integerp value) value)
        ((eq value t) 1)
        ((null value) '(:failure "failure" ""))
        ((and (consp value) (equal (car value) "ratio"))
         (proof-with-checked-results
          ((num (proof-term-at value 1))
           (den (proof-term-at value 2)))
          (let ((num (if (eq num t) 1 num))
                (den (if (eq den t) 1 den)))
            (cond ((or (not (rationalp num)) (not (rationalp den)))
                   '(:failure "failure" ""))
                  ((equal den 0)
                   '(:failure "failure" ""))
                  (t (/ num den))))))
        (t nil)))

(defun b1-logic-rational-datum (value)
  (let ((value (if (eq value t) 1 value)))
    (cond ((not (rationalp value))
           '(:failure "failure" ""))
          ((equal (denominator value) 1) (numerator value))
          (t (list "ratio" (numerator value) (denominator value))))))

(defun b1-logic-bookproof-from-fact (lib name claim)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((fact (proof-proof-fact proof name nil))
      (literal (b1-logic-step-first fact))
      (match (b1-logic-match literal claim nil)))
     (if (car match)
         (proof-proof-instantiate proof fact (table-items (cdr match)))
       (proof-with-checked-results ((printed (proof-write claim)))
         '(:failure "unproved" ""))))))

(defun b1-logic-bookproof-rewrite-rule (lib name)
  (proof-with-checked-results
   ((fact (proof-proof-fact (library-library-proof lib) name nil))
    (left (b1-logic-step-at fact 1)))
   (list :rewrite-rule fact left)))

(defun b1-logic-bookproof-rewrite-rule-rule (term lib fact left)
  (proof-with-checked-results ((match (b1-logic-match left term nil)))
    (and (car match)
         (proof-proof-instantiate (library-library-proof lib) fact
                                  (table-items (cdr match))))))

(defun b1-logic-apply-rule (lib rule term)
  (case (car rule)
    (:equal-to (b1-logic-equal-to-rule term (cadr rule)))
    (:rewrite-rule (b1-logic-bookproof-rewrite-rule-rule
                    term lib (cadr rule) (caddr rule)))
    (otherwise '(:failure "failure" ""))))

(defun b1-logic-bookproof-prove-implication-premise (lib formula)
  (proof-with-checked-results ((formula (proof-list-of-length formula 3)))
    (proof-proof-assume (library-library-proof lib) (cadr formula) t)))

(defun b1-logic-bookproof-prove-implication-with-premise
    (lib formula premise consequence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((formula (proof-list-of-length formula 3))
      (first (b1-logic-step-first consequence)))
     (if (not (equal first (caddr formula)))
         '(:failure "rule-inapplicable" "")
       (proof-with-checked-results
        ((opened (proof-proof-unfold proof formula))
         (body (b1-logic-step-at opened 2))
         (selected (proof-proof-select proof body premise))
         (truth (proof-proof-prove proof *proof-true* nil nil))
         (selected-body (b1-logic-step-at selected 2))
         (inner (proof-proof-select proof selected-body consequence))
         (yes (proof-proof-transport proof truth inner))
         (yes (proof-proof-transport proof yes selected))
         (else (proof-proof-if-false proof body))
         (no (proof-proof-transport proof truth else))
         (both (proof-proof-cases proof (cadr formula) yes no)))
        (proof-proof-transport proof both opened))))))

(defun b1-logic-bookproof-prove-implication (lib formula consequence)
  (proof-with-checked-results
   ((premise (b1-logic-bookproof-prove-implication-premise lib formula)))
   (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-logic-bookproof-conjunction-p (step)
  (proof-with-checked-results ((first (b1-logic-step-first step)))
    (if (proof-is-call first *proof-if*)
        (proof-with-checked-results ((otherwise (proof-term-at first 3)))
          (equal otherwise *proof-false*))
      nil)))

(defun b1-logic-bookproof-split-conjuncts-first (lib step)
  (proof-with-checked-results
   ((conjunction (b1-logic-bookproof-conjunction-p step)))
   (if conjunction
       (proof-with-checked-results
        ((parts (proof-proof-conjunct (library-library-proof lib) step)))
        (car parts))
     step)))

(defun b1-logic-bookproof-split-conjuncts-visit (n proof step)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "b1-logic-bookproof-split-conjuncts-visit")
    (proof-with-checked-results
     ((conjunction (b1-logic-bookproof-conjunction-p step)))
     (if conjunction
         (proof-with-checked-results
          ((parts (proof-proof-conjunct proof step))
           (rest (b1-logic-bookproof-split-conjuncts-visit
                  (1- n) proof (cadr parts))))
          (cons (car parts) rest))
       (list step)))))

(defun b1-logic-bookproof-split-conjuncts (lib step)
  (b1-logic-bookproof-split-conjuncts-visit 1000000 (library-library-proof lib) step))

(defun b1-logic-bookproof-contradiction (lib positive negative goal)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((step (proof-proof-cut proof positive negative)))
      (proof-proof-subsume proof step (cons goal (proof-step-clause step))))))

(defun b1-logic-bookproof-true-constant (lib term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((step (proof-proof-nil-or-true proof term))
      (equality (proof-proof-compute proof (proof-eq term *proof-false*) *proof-nil*))
      (rewritten (proof-proof-rewrite proof step equality '(1))))
     (proof-proof-tidy proof rewritten))))

(defun b1-logic-bookproof-false-value (lib negative)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((term (b1-logic-step-at negative 1))
      (step (proof-proof-nil-or-true proof term))
      (front (proof-proof-front proof step term))
      (cut (proof-proof-cut proof front negative)))
     (proof-proof-front proof cut (proof-eq term *proof-false*)))))

(defun b1-logic-bookproof-boolean-value (lib step boolean)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((term (b1-logic-step-first step))
      (predicate (b1-logic-step-first boolean))
      (opened (proof-proof-unfold proof predicate))
      (body (b1-logic-step-at opened 2))
      (condition (proof-term-at body 1))
      (simplified (proof-proof-rewrite proof boolean opened '(1)))
      (opposite (proof-proof-assume proof condition nil))
      (no (proof-proof-prove-if proof simplified opposite))
      (first (b1-logic-step-first no))
      (opened (proof-proof-unfold proof first))
      (no (proof-proof-rewrite proof no opened '(1)))
      (not-nil (b1-logic-proof-not-nil proof))
      (reverse (proof-proof-symmetric proof no))
      (negative (proof-proof-rewrite proof not-nil reverse '(1 1)))
      (negative (proof-proof-tidy proof negative))
      (no (proof-proof-cut proof step negative))
      (no (proof-proof-front proof no condition))
      (opened (proof-proof-unfold proof condition)))
     (proof-proof-rewrite proof no opened '(1)))))

(defun b1-logic-bookproof-equality-true (lib step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((left (b1-logic-step-at step 1))
      (both (proof-proof-fact proof "equal-same" (list (list *library-x* left))))
      (rewritten (proof-proof-rewrite proof both step '(1 1 2))))
     (proof-proof-tidy proof rewritten))))

(defun b1-logic-rational-values (values)
  (if (endp values)
      nil
    (proof-with-checked-results
     ((value (b1-logic-rational-value (car values)))
      (rest (b1-logic-rational-values (cdr values))))
     (cons value rest))))

(defun b1-logic-constant-selector (head first)
  (cond ((not (and (proof-compound first) (consp first))) *proof-nil*)
        ((equal head *library-car*) (car first))
        ((and (equal (len first) 2) (or (consp (cadr first)) (null (cadr first))))
         (let ((tail (cadr first)))
           (proof-with-checked-results ((tag (proof-term-at tail 0)))
             (if (equal tag "dot") (proof-term-at tail 1) (cdr first)))))
        (t (or (cdr first) *proof-nil*))))

(defun b1-logic-constant-rational-part (head first)
  (proof-with-checked-results ((number (b1-logic-rational-value first)))
    (cond ((equal head (proof-cl "NUMERATOR")) (if number (numerator number) 0))
          ((equal head (proof-cl "DENOMINATOR")) (if number (denominator number) 1))
          ((not number) :none)
          (t (b1-logic-rational-datum (if (equal number 0) 0 (/ number)))))))

(defun b1-logic-constant-arithmetic (head values)
  (proof-with-checked-results ((numbers (b1-logic-rational-values values)))
    (cond ((member-eq nil numbers) :none)
          ((or (endp numbers) (and (not (equal head *proof-minus*))
                                   (endp (cdr numbers))))
           '(:failure "failure" ""))
          ((equal head *proof-less*)
           (if (< (car numbers) (cadr numbers)) *proof-t* *proof-nil*))
          (t (b1-logic-rational-datum
              (cond ((equal head *proof-plus*) (+ (car numbers) (cadr numbers)))
                    ((equal head *proof-times*) (* (car numbers) (cadr numbers)))
                    (t (- (car numbers)))))))))

(defun b1-logic-constant-value (head values)
  (let* ((first (if (consp values) (car values) :none))
         (tag (and (consp first) (car first))))
    (cond ((member-equal head (list *library-car* *library-cdr*))
           (b1-logic-constant-selector head first))
          ((member-equal head (list *b1-logic-symbolp* *b1-logic-stringp*))
           (if (equal tag (if (equal head *b1-logic-symbolp*) "sym" "str"))
               *proof-t* *proof-nil*))
          ((equal head *b1-logic-symbol-name*)
           (if (equal tag "sym")
               (proof-with-checked-results ((name (proof-term-at first 2)))
                 (list "str" name))
             '("str" "")))
          ((and (equal head *b1-logic-symbol-package*) (equal tag "sym"))
           (proof-with-checked-results ((package (proof-term-at first 1)))
             (if (member-equal package '("ACL2" "COMMON-LISP" "KEYWORD"))
                 (list "str" package)
               :none)))
          ((equal head *proof-cons*)
           (if (endp (cdr values))
               '(:failure "failure" "")
             (let ((tail (cadr values)))
               (cons first
                     (cond ((proof-compound tail) tail)
                           ((equal tail *proof-nil*) nil)
                           (t (list (list "dot" tail))))))))
          ((equal head *library-numberp*)
           (if (or (integerp first) (eq first t) (member-equal tag '("ratio" "complex")))
               *proof-t* *proof-nil*))
          ((member-equal head (list (proof-cl "NUMERATOR") (proof-cl "DENOMINATOR")
                                    (proof-sym "UNARY-/" "ACL2")))
           (b1-logic-constant-rational-part head first))
          ((member-equal head (list *proof-plus* *proof-times* *proof-minus* *proof-less*))
           (b1-logic-constant-arithmetic head values))
          (t :none))))

(defun b1-logic-bookproof-constant (lib term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((parent (proof-proof-constant-base proof term)))
      (if parent
          parent
        (let ((head (car term))
              (args (cdr term)))
          (if (and (member-equal head (proof-proof-primitives proof))
                   (proof-all-quoted-p args))
              (proof-with-checked-results
               ((values (proof-quoted-values args))
                (value (b1-logic-constant-value head values)))
               (if (eq value :none) nil (proof-proof-compute proof term value)))
            nil))))))

(defun b1-logic-call-p (result)
  (eq (car result) :b1-logic-call))

(defun b1-logic-call-id (request)
  (caddr request))

(defun b1-logic-call-library (request)
  (cadddr request))

(defun b1-logic-call-term (request)
  (car (cddddr request)))

(defun b1-logic-branch-p (result)
  (eq (car result) :b1-logic-branch))

(defun b1-logic-make-branch (test lib)
  (list :b1-logic-branch test lib))

(defun b1-logic-branch-test (result)
  (cadr result))

(defun b1-logic-branch-library (result)
  (caddr result))

(defun b1-logic-interrupted-p (value)
  (or (failure-p value) (b1-logic-call-p value) (b1-logic-branch-p value)))

; An internal computation carries its value, Library and unused callback replies.
(defmacro b1-logic-with-computation (names form body)
  (let ((value (car names))
        (lib (cadr names))
        (replies (caddr names)))
    `(let* ((b1-logic-result ,form)
            (,value (car b1-logic-result)))
       (if (b1-logic-interrupted-p ,value)
           b1-logic-result
         (let ((,lib (cadr b1-logic-result))
               (,replies (caddr b1-logic-result)))
           (declare (ignorable ,lib ,replies))
           ,body)))))

(defmacro b1-logic-with-proof (lib replies bindings body)
  (if (endp bindings)
      body
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (failure-p ,name)
             (list ,name ,lib ,replies)
           (b1-logic-with-proof ,lib ,replies ,(cdr bindings) ,body))))))

(defun b1-logic-computation-result (result)
  (let ((value (car result)))
    (if (b1-logic-interrupted-p value)
        value
      (cons value (cadr result)))))

(defun b1-logic-step-result (result)
  (cond ((failure-p result) result)
        ((b1-logic-branch-p result)
         '(:failure "failure" ""))
        ((b1-logic-call-p result)
         '(:failure "failure" ""))
        (t (car result))))

(defun b1-logic-callback (kind descriptor term lib replies)
  (if (endp replies)
      (list (list :b1-logic-call kind (cadr descriptor) lib term) lib nil)
    (let ((reply (car replies)))
      (cond ((b1-logic-branch-p reply)
             (list reply (b1-logic-branch-library reply) (cdr replies)))
            ((failure-p reply) (list reply lib (cdr replies)))
            (t (list (car reply) (cdr reply) (cdr replies)))))))

(defun b1-logic-normalize-known (evidence known)
  (if (endp evidence)
      known
    (proof-with-checked-results ((first (b1-logic-step-first (car evidence))))
      (b1-logic-normalize-known
       (cdr evidence) (table-put known first (car evidence))))))

(defun b1-logic-bookproof-normalize-equality-value (term lib known)
  (and (proof-is-call term *proof-equal*)
       (let ((positive (assoc-equal term known)))
         (if positive
             (b1-logic-bookproof-equality-true lib (cdr positive))
           (let ((negative (assoc-equal (proof-neg term) known)))
             (and negative (b1-logic-bookproof-false-value lib (cdr negative))))))))

(defun b1-logic-normalize-find-rule (rules term lib known replies)
  (if (endp rules)
      (list nil lib replies)
    (let ((rule (car rules)))
      (b1-logic-with-computation (step lib replies)
        (case (car rule)
          (:callback (b1-logic-callback :rule rule term lib replies))
          (:equality-value
           (list (b1-logic-bookproof-normalize-equality-value term lib known) lib replies))
          (otherwise (list (b1-logic-apply-rule lib rule term) lib replies)))
        (b1-logic-with-proof lib replies
          ((right (and step (b1-logic-step-at step 2))))
          (if (and step (not (equal term right)))
              (list step lib replies)
            (b1-logic-normalize-find-rule (cdr rules) term lib known replies)))))))

(defun b1-logic-normalize-equal-branches (proof term test)
  (proof-with-checked-results
   ((yes (proof-proof-if-true proof term))
    (no (proof-proof-if-false proof term)))
   (proof-proof-cases proof test yes no)))

(defun b1-logic-normalize-if-selected (current test yes no lib known condition replies)
  (let ((proof (library-library-proof lib)))
    (cond
     ((equal yes no)
      (list (b1-logic-normalize-equal-branches proof current test) lib replies))
     ((proof-is-call test *proof-quote*)
      (list (if (equal test *proof-false*)
                (proof-proof-fact proof "if-nil"
                                  (seq-zip (list *library-y* *library-z*) (cddr current)))
              (proof-with-checked-results
               ((selected (proof-proof-if-true proof current))
                (premise (b1-logic-bookproof-true-constant lib test)))
               (proof-proof-discharge proof selected premise)))
            lib replies))
     (t
      (let ((assumption (or (cdr (assoc-equal test known))
                            (cdr (assoc-equal (proof-neg test) known)))))
        (cond
         (assumption (list (proof-proof-select proof current assumption) lib replies))
         (condition
          (b1-logic-with-computation (premise lib replies)
            (b1-logic-callback :condition condition test lib replies)
            (list (and premise
                       (proof-proof-select (library-library-proof lib) current premise))
                  lib replies)))
         (t (list nil lib replies))))))))

(defun b1-logic-normalize-primitive (lib head current)
  (let ((proof (library-library-proof lib)))
    (if (member-equal head (list *library-car* *library-cdr* *proof-consp*))
        (proof-with-checked-results ((first (proof-term-at current 1)))
          (cond
           ((not (proof-is-call first *proof-cons*))
            (b1-logic-bookproof-constant lib current))
           ((equal head *proof-consp*)
            (proof-with-checked-results
             ((step (proof-proof-fact proof "consp-cons"
                                      (seq-zip (list *library-x* *library-y*) (cdr first))))
              (boolean (proof-proof-fact proof "booleanp-consp"
                                         (list (list *library-x* first)))))
             (b1-logic-bookproof-boolean-value lib step boolean)))
           (t (library-library-axiom
               lib (if (equal head *library-car*) "CAR-CONS" "CDR-CONS")
               (cdr first)))))
      (b1-logic-bookproof-constant lib current))))

(defun b1-logic-normalize-context (known rules split condition inspect-branches)
  (list known rules split condition inspect-branches))

(defun b1-logic-normalize-context-known (context)
  (car context))

(defun b1-logic-normalize-context-rules (context)
  (cadr context))

(defun b1-logic-normalize-context-split (context)
  (caddr context))

(defun b1-logic-normalize-context-condition (context)
  (cadddr context))

(defun b1-logic-normalize-context-inspect-branches (context)
  (car (cddddr context)))

(defun b1-logic-normalize-fuel (lib replies)
  (list '(:failure "fuel" "b1-logic-normalize-operations") lib replies))

; The pending operations keep the order of reductions and proof construction.
(defun b1-logic-normalize-start-chain (steps last openings lib replies pending)
  (b1-logic-with-proof lib replies ((right (b1-logic-step-at last 2)))
    (list nil lib replies
          (list* (list :reduce right openings) (list :chain steps) pending))))

(defun b1-logic-normalize-start-application (term openings lib context replies pending)
  (let ((proof (library-library-proof lib))
        (known (b1-logic-normalize-context-known context)))
    (b1-logic-with-proof lib replies ((head (proof-term-at term 0)))
      (cond
       ((proof-compound head)
        (b1-logic-with-proof lib replies ((step (proof-proof-beta proof term)))
          (b1-logic-normalize-start-chain (list step) step openings lib replies pending)))
       ((or (equal head *b1-logic-return-last*) (equal head *b1-logic-the-check*)
            (member-equal head openings))
        (b1-logic-with-proof lib replies ((step (proof-proof-unfold proof term)))
          (b1-logic-normalize-start-chain
           (list step) step (remove-equal head openings) lib replies pending)))
       (t
        (b1-logic-with-proof lib replies
          ((test (and (equal head *proof-if*) (proof-term-at term 1))))
          (let ((premise (and (equal head *proof-if*)
                              (or (cdr (assoc-equal test known))
                                  (cdr (assoc-equal (proof-neg test) known))))))
            (if premise
                (b1-logic-with-proof lib replies ((step (proof-proof-select proof term premise)))
                  (b1-logic-normalize-start-chain (list step) step openings lib replies pending))
              (b1-logic-with-proof lib replies ((result (proof-proof-reflexive proof term)))
                (list nil lib replies
                      (list* (list :arguments
                                   (if (equal head *proof-if*) (list test) (cdr term))
                                   1 result openings)
                             (list :after-arguments term head openings)
                             pending)))))))))))

(defun b1-logic-normalize-start-term (term openings lib context replies pending)
  (b1-logic-with-computation (step lib replies)
    (b1-logic-normalize-find-rule (b1-logic-normalize-context-rules context)
                                 term lib (b1-logic-normalize-context-known context) replies)
    (cond (step (b1-logic-normalize-start-chain (list step) step openings lib replies pending))
          ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
           (list (proof-proof-reflexive (library-library-proof lib) term) lib replies pending))
          (t (b1-logic-normalize-start-application term openings lib context replies pending)))))

(defun b1-logic-normalize-start-arguments (arguments index result openings lib replies pending)
  (if (endp arguments)
      (list result lib replies pending)
    (list nil lib replies
          (list* (list :reduce (car arguments) openings)
                 (list :argument-value arguments index result openings)
                 pending))))

(defun b1-logic-normalize-argument-value
    (simplified arguments index result openings lib replies pending)
  (let ((proof (library-library-proof lib)))
    (b1-logic-with-proof lib replies
      ((right (b1-logic-step-at simplified 2))
       (result (if (equal right (car arguments))
                   result
                 (proof-with-checked-results
                  ((rewritten (proof-proof-rewrite proof result simplified (list 1 2 index))))
                  (proof-proof-tidy proof rewritten)))))
      (b1-logic-normalize-start-arguments
       (cdr arguments) (1+ index) result openings lib replies pending))))

(defun b1-logic-normalize-finish-inspection (result test openings lib replies pending)
  (b1-logic-with-proof lib replies
    ((current (b1-logic-step-at result 2))
     (yes (proof-term-at current 2))
     (no (proof-term-at current 3)))
    (if (not (equal yes no))
        (list result lib replies pending)
      (b1-logic-with-proof lib replies
        ((selected (b1-logic-normalize-equal-branches (library-library-proof lib) current test)))
        (b1-logic-normalize-start-chain
         (list result selected) selected openings lib replies pending)))))

(defun b1-logic-normalize-start-if (current result openings lib context replies pending)
  (b1-logic-with-proof lib replies
    ((test (proof-term-at current 1))
     (yes (proof-term-at current 2))
     (no (proof-term-at current 3)))
    (b1-logic-with-computation (selected lib replies)
      (b1-logic-normalize-if-selected current test yes no lib
                                      (b1-logic-normalize-context-known context)
                                      (b1-logic-normalize-context-condition context)
                                      replies)
      (cond
       (selected (b1-logic-normalize-start-chain
                  (list result selected) selected openings lib replies pending))
       ((b1-logic-normalize-context-split context)
        (list (b1-logic-make-branch test lib) lib replies))
       ((b1-logic-normalize-context-inspect-branches context)
        (b1-logic-normalize-start-arguments (list yes no) 2 result openings lib replies
                                           (cons (list :inspected test openings) pending)))
       (t (list result lib replies pending))))))

(defun b1-logic-normalize-after-arguments (term head result openings lib context replies pending)
  (b1-logic-with-proof lib replies ((current (b1-logic-step-at result 2)))
    (b1-logic-with-computation (step lib replies)
      (if (or (not (equal head *proof-if*))
              (and (b1-logic-normalize-context-inspect-branches context)
                   (not (equal current term))))
          (b1-logic-normalize-find-rule (b1-logic-normalize-context-rules context)
                                       current lib (b1-logic-normalize-context-known context)
                                       replies)
        (list nil lib replies))
      (cond (step (b1-logic-normalize-start-chain
                   (list result step) step openings lib replies pending))
            ((equal head *proof-if*)
             (b1-logic-normalize-start-if current result openings lib context replies pending))
            (t
             (b1-logic-with-proof lib replies
               ((step (b1-logic-normalize-primitive lib head current)))
               (list (proof-proof-chain (library-library-proof lib) result (list step))
                     lib replies pending)))))))

(defun b1-logic-normalize-advance (value lib context replies pending)
  (let* ((operation (car pending))
         (args (cdr operation))
         (pending (cdr pending)))
    (case (car operation)
      (:reduce (b1-logic-normalize-start-term
                (car args) (cadr args) lib context replies pending))
      (:chain (let ((steps (car args)))
                (list (proof-proof-chain (library-library-proof lib) (car steps)
                                         (append (cdr steps) (list value)))
                      lib replies pending)))
      (:arguments (b1-logic-normalize-start-arguments
                   (car args) (cadr args) (caddr args) (cadddr args) lib replies pending))
      (:argument-value (b1-logic-normalize-argument-value
                        value (car args) (cadr args) (caddr args) (cadddr args)
                        lib replies pending))
      (:after-arguments (b1-logic-normalize-after-arguments
                         (car args) (cadr args) value (caddr args) lib context replies pending))
      (:inspected (b1-logic-normalize-finish-inspection
                   value (car args) (cadr args) lib replies pending))
      (otherwise (list '(:failure "rule-inapplicable" "") lib replies)))))

(defun b1-logic-normalize-operations (n context work)
  (declare (xargs :measure (nfix n)))
  (let ((value (car work)) (lib (cadr work)) (replies (caddr work)) (pending (cadddr work)))
    (cond ((or (b1-logic-interrupted-p value) (endp pending)) (list value lib replies))
          ((zp n) (b1-logic-normalize-fuel lib replies))
          (t (b1-logic-normalize-operations
              (1- n) context (b1-logic-normalize-advance value lib context replies pending))))))

(defun b1-logic-bookproof-normalize-reduce (n term openings lib context replies)
  (b1-logic-normalize-operations n context
                                 (list nil lib replies (list (list :reduce term openings)))))

(defun b1-logic-normalize-run
    (lib term evidence unfold rules split condition inspect-branches replies)
  (b1-logic-with-proof lib replies ((known (b1-logic-normalize-known evidence nil)))
    (let* ((rules (if split (append rules (list (list :equality-value))) rules))
           (context (b1-logic-normalize-context known rules split condition inspect-branches)))
      (if (equal term *proof-true*)
          (list (proof-proof-reflexive (library-library-proof lib) term) lib replies)
        (b1-logic-bookproof-normalize-reduce 1000000 term unfold lib context replies)))))

(defun b1-logic-bookproof-normalize-with-library
    (lib term evidence unfold rules split condition inspect-branches replies)
  (b1-logic-computation-result
   (b1-logic-normalize-run lib term evidence unfold rules split condition inspect-branches replies)))

(defun b1-logic-bookproof-normalize
    (lib term evidence unfold rules split condition inspect-branches)
  (b1-logic-step-result
   (b1-logic-bookproof-normalize-with-library
    lib term evidence unfold rules split condition inspect-branches nil)))

(defun b1-logic-find-evidence (goal evidence)
  (if (endp evidence)
      nil
    (proof-with-checked-results ((first (b1-logic-step-first (car evidence))))
      (if (equal first goal)
          (car evidence)
        (b1-logic-find-evidence goal (cdr evidence))))))

(defun b1-logic-normalize-proof-finish (lib goal evidence unfold rules split replies)
  (b1-logic-with-computation (equality lib replies)
    (b1-logic-normalize-run lib goal evidence unfold rules split nil nil replies)
    (let ((proof (library-library-proof lib)))
      (b1-logic-with-proof lib replies ((result (b1-logic-step-at equality 2)))
        (if (equal result *proof-true*)
            (list (proof-proof-true-from-eq proof equality) lib replies)
          (b1-logic-with-proof lib replies ((premise (b1-logic-find-evidence result evidence)))
            (if premise
                (list (proof-proof-transport proof premise equality) lib replies)
              (b1-logic-with-proof lib replies ((printed (proof-write result)))
                (list '(:failure "unproved" "")
                      lib replies)))))))))

(defun b1-logic-normalize-proof-conjunct (goal evidence)
  (if (proof-is-call goal *proof-if*)
      (proof-with-checked-results ((other (proof-term-at goal 3)))
        (and (equal other *proof-false*)
             (b1-logic-find-evidence (cadr goal) evidence)))
    nil))

(defun b1-logic-normalize-proof-run (n lib goal evidence unfold rules split replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list '(:failure "fuel" "b1-logic-normalize-proof-run") lib replies)
    (b1-logic-with-proof lib replies ((premise (b1-logic-find-evidence goal evidence)))
      (if premise
          (list premise lib replies)
        (b1-logic-with-proof lib replies ((premise (b1-logic-normalize-proof-conjunct goal evidence)))
          (if premise
              (b1-logic-with-computation (child lib replies)
                (b1-logic-normalize-proof-run
                 (1- n) lib (caddr goal) evidence unfold rules split replies)
                (let ((proof (library-library-proof lib)))
                  (b1-logic-with-proof lib replies
                    ((selected (proof-proof-select proof goal premise)))
                    (list (proof-proof-transport proof child selected) lib replies))))
            (b1-logic-normalize-proof-finish lib goal evidence unfold rules split replies)))))))

(defun b1-logic-bookproof-normalize-proof-with-library (lib goal evidence unfold rules split replies)
  (b1-logic-computation-result
   (b1-logic-normalize-proof-run 1000000 lib goal evidence unfold rules split replies)))

(defun b1-logic-bookproof-normalize-proof (lib goal evidence unfold rules split)
  (b1-logic-step-result
   (b1-logic-bookproof-normalize-proof-with-library lib goal evidence unfold rules split nil)))

(defun b1-logic-case-proof-start (lib goal evidence unfold rules depth replies pending)
  (let* ((result (b1-logic-normalize-proof-run 1000000 lib goal evidence unfold rules t replies))
         (value (car result))
         (lib (cadr result))
         (replies (caddr result)))
    (cond
     ((not (b1-logic-branch-p value)) (list value lib replies pending))
     ((equal depth 0) (list '(:failure "unproved" "")
                            lib replies))
     (t
      (let ((test (b1-logic-branch-test value)))
        (b1-logic-with-proof lib replies
          ((premise (proof-proof-assume (library-library-proof lib) test t)))
          (list nil lib replies
                (list* (list :prove (append evidence (list premise)) (1- depth))
                       (list :otherwise test evidence (1- depth))
                       pending))))))))

(defun b1-logic-case-proof-advance (value lib goal unfold rules replies pending)
  (let* ((operation (car pending))
         (args (cdr operation))
         (pending (cdr pending)))
    (case (car operation)
      (:prove (b1-logic-case-proof-start
               lib goal (car args) unfold rules (cadr args) replies pending))
      (:otherwise
       (let ((test (car args)) (evidence (cadr args)) (depth (caddr args)))
         (b1-logic-with-proof lib replies
           ((premise (proof-proof-assume (library-library-proof lib) test nil)))
           (list nil lib replies
                 (list* (list :prove (append evidence (list premise)) depth)
                        (list :join test value)
                        pending)))))
      (:join (list (proof-proof-cases (library-library-proof lib) (car args) (cadr args) value)
                   lib replies pending))
      (otherwise (list '(:failure "failure" "") lib replies)))))

(defun b1-logic-case-proof-operations (n goal unfold rules work)
  (declare (xargs :measure (nfix n)))
  (let ((value (car work)) (lib (cadr work)) (replies (caddr work)) (pending (cadddr work)))
    (cond ((or (b1-logic-interrupted-p value) (endp pending)) (list value lib replies))
          ((zp n) (list '(:failure "fuel" "b1-logic-case-proof-operations") lib replies))
          (t (b1-logic-case-proof-operations
              (1- n) goal unfold rules
              (b1-logic-case-proof-advance value lib goal unfold rules replies pending))))))

(defun b1-logic-case-proof-run (n lib goal evidence unfold rules depth replies)
  (b1-logic-case-proof-operations n goal unfold rules
                                  (list nil lib replies (list (list :prove evidence depth)))))

(defun b1-logic-bookproof-case-proof-with-library (lib goal evidence unfold rules depth replies)
  (b1-logic-computation-result
   (b1-logic-case-proof-run 1000000 lib goal evidence unfold rules depth replies)))

(defun b1-logic-bookproof-case-proof (lib goal evidence unfold rules depth)
  (b1-logic-step-result
   (b1-logic-bookproof-case-proof-with-library lib goal evidence unfold rules depth nil)))

(defun b1-logic-forces-run (lib goal assertion evidence unfold rules replies)
  (b1-logic-with-proof lib replies
    ((opposite (proof-proof-assume (library-library-proof lib) goal nil))
     (term (b1-logic-step-first assertion)))
    (b1-logic-with-computation (reduction lib replies)
      (b1-logic-normalize-run lib term (append evidence (list opposite)) unfold
                              rules nil nil nil replies)
      (b1-logic-with-proof lib replies ((right (b1-logic-step-at reduction 2)))
        (if (not (equal right *proof-false*))
            (list '(:failure "unproved" "") lib replies)
          (let ((proof (library-library-proof lib)))
            (b1-logic-with-proof lib replies
              ((not-nil (b1-logic-proof-not-nil proof))
               (reversed (proof-proof-symmetric proof reduction))
               (negative (proof-proof-rewrite proof not-nil reversed '(1 1)))
               (step (proof-proof-cut proof assertion negative)))
              (list (proof-proof-front proof step goal) lib replies))))))))

(defun b1-logic-bookproof-forces-with-library (lib goal assertion evidence unfold rules replies)
  (b1-logic-computation-result (b1-logic-forces-run lib goal assertion evidence unfold rules replies)))

(defun b1-logic-bookproof-forces (lib goal assertion evidence unfold rules)
  (b1-logic-step-result
   (b1-logic-bookproof-forces-with-library lib goal assertion evidence unfold rules nil)))

(defun b1-logic-bookproof-select-equivalent-test-outcome
    (a b lib y left right iff guard claim)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((left-test (proof-proof-assume proof *library-x* a))
      (right-test (proof-proof-assume proof y b)))
     (if (equal a b)
         (proof-with-checked-results
          ((left (proof-proof-select proof left left-test))
           (right (proof-proof-select proof right right-test))
           (reversed (proof-proof-symmetric proof right)))
          (proof-proof-chain proof left (list reversed)))
       (proof-with-checked-results
        ((reduced (b1-logic-bookproof-normalize
                   lib iff (list left-test right-test) (list (car iff)) nil nil nil nil))
         (rewritten (proof-proof-rewrite proof guard reduced '(1)))
         (impossible (proof-proof-tidy proof rewritten)))
        (proof-proof-subsume proof impossible (cons claim (proof-step-clause impossible))))))))

(defun b1-logic-install-equivalent-test (lib)
  (let* ((proof (library-library-proof lib))
         (y *library-y*)
         (on-true *library-z*)
         (on-false (proof-sym "W" "ACL2"))
         (left (proof-ite *library-x* on-true on-false))
         (right (proof-ite y on-true on-false))
         (iff (list (proof-sym "IFF" "ACL2") *library-x* y)))
    (proof-with-checked-results
     ((guard (proof-proof-assume proof iff t))
      (claim (proof-eq left right))
      (yes-yes (b1-logic-bookproof-select-equivalent-test-outcome
                t t lib y left right iff guard claim))
      (yes-no (b1-logic-bookproof-select-equivalent-test-outcome
               t nil lib y left right iff guard claim))
      (yes (proof-proof-cases proof y yes-yes yes-no))
      (no-yes (b1-logic-bookproof-select-equivalent-test-outcome
               nil t lib y left right iff guard claim))
      (no-no (b1-logic-bookproof-select-equivalent-test-outcome
              nil nil lib y left right iff guard claim))
      (no (proof-proof-cases proof y no-yes no-no))
      (step (proof-proof-cases proof *library-x* yes no)))
     (library-library-lemma lib "IF-EQUIVALENT-TEST" claim step (list (proof-neg iff))))))

(defun b1-logic-bookproof-select-equivalent-test (lib term equivalence)
  (let ((name (proof-sym "SELF-IF-EQUIVALENT-TEST" "ACL2"))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((lib (if (assoc-equal name (proof-proof-facts proof)) lib
             (b1-logic-install-equivalent-test lib)))
      (literal (b1-logic-step-first equivalence))
      (parts (proof-list-of-length literal 3))
      (test (proof-term-at term 1)))
     (if (not (equal test (cadr parts)))
         '(:failure "failure" "")
       (proof-with-checked-results
        ((step (proof-proof-use
                (library-library-proof lib) name
                (seq-zip (list *library-x* *library-y* *library-z* (proof-sym "W" "ACL2"))
                        (cons (cadr parts) (cons (caddr parts) (cddr term))))
                (list equivalence))))
        (cons step lib))))))
