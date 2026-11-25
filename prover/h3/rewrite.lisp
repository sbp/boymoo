(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-rewrite-characterp* (proof-cl "CHARACTERP"))
(defconst *h3-rewrite-symbolp* (proof-cl "SYMBOLP"))
(defconst *h3-rewrite-stringp* (proof-cl "STRINGP"))
(defconst *h3-rewrite-reciprocal* (proof-sym "UNARY-/" "ACL2"))
(defconst *h3-rewrite-return-last* (proof-sym "RETURN-LAST" "ACL2"))
(defconst *h3-rewrite-closed-definitions*
  (list (proof-cl "NTH") (proof-sym "MV-NTH" "ACL2") (proof-sym "ZP" "ACL2")
        *proof-not* (proof-cl "ATOM") (proof-cl "ENDP")))

(defconst *h3-rewrite-unproved* '(:failure "unproved" ""))

(defun h3-rewrite-unproved-p (value)
  (and (failure-p value) (equal (cadr value) "unproved")))

(defun h3-rewrite-arguments (term)
  (and (proof-compound term)
       (not (proof-is-call term *proof-quote*))
       (cdr term)))

(mutual-recursion
 (defun h3-rewrite-match (pattern term bindings)
   (declare (xargs :measure (1+ (* 2 (acl2-count pattern)))))
   (cond ((not (proof-compound pattern))
          (let ((entry (assoc-equal pattern bindings)))
            (if entry
                (cons (equal (cdr entry) term) bindings)
              (cons t (table-put bindings pattern term)))))
         ((proof-is-call pattern *proof-quote*) (cons (equal pattern term) bindings))
         ((not (proof-compound term)) (cons nil bindings))
         ((or (endp pattern) (endp term)) '(:failure "malformed-tactic-input" ""))
         ((and (equal (car pattern) (car term)) (equal (len pattern) (len term)))
          (h3-rewrite-match-arguments (cdr pattern) (cdr term) bindings))
         (t (cons nil bindings))))

 (defun h3-rewrite-match-arguments (patterns terms bindings)
   (declare (xargs :measure (* 2 (acl2-count patterns))))
   (if (endp patterns)
       (cons t bindings)
     (proof-with-checked-results
      ((answer (h3-rewrite-match (car patterns) (car terms) bindings)))
      (if (car answer)
          (h3-rewrite-match-arguments (cdr patterns) (cdr terms) (cdr answer))
        answer)))))

(defun h3-rewrite-implication (lib antecedent result)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((conclusion (proof-step-first result))
      (opened (proof-proof-unfold proof (list *library-implies* antecedent conclusion)))
      (opened-literal (proof-step-first opened))
      (conditional (proof-term-at opened-literal 2))
      (if-true (proof-proof-if-true proof conditional))
      (started-yes (proof-proof-chain proof opened (list if-true)))
      (yes-literal (proof-step-first started-yes))
      (yes-conditional (proof-term-at yes-literal 2))
      (selected (proof-proof-select proof yes-conditional result))
      (yes (proof-proof-chain proof started-yes (list selected)))
      (if-false (proof-proof-if-false proof conditional))
      (no (proof-proof-chain proof opened (list if-false)))
      (positive (proof-proof-true-from-eq proof yes))
      (negative (proof-proof-true-from-eq proof no)))
     (proof-proof-cases proof antecedent positive negative))))

(defun h3-rewrite-apply-implication (lib step guard)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first step))
      (conclusion (proof-term-at literal 2)))
     (if (not (equal conclusion *proof-false*))
         (proof-proof-modus-ponens proof step guard)
       (proof-with-checked-results
        ((unfolded (proof-proof-unfold proof literal))
         (opened (proof-proof-rewrite proof step unfolded '(1)))
         (reduced (proof-proof-prove-if proof opened guard))
         (reduced-literal (proof-step-first reduced))
         (if-false (proof-proof-if-false proof reduced-literal))
         (rewritten (proof-proof-rewrite proof reduced if-false '(1)))
         (contradiction (proof-proof-tidy proof rewritten)))
        (proof-proof-subsume proof contradiction
                             (cons *proof-false* (proof-step-clause contradiction))))))))

(defun h3-rewrite-nil-value (lib negative)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first negative))
      (term (proof-term-at literal 1))
      (nil-or-true (proof-proof-nil-or-true proof term))
      (cases (proof-proof-front proof nil-or-true term))
      (cut (proof-proof-cut proof cases negative)))
     (proof-proof-front proof cut (proof-eq term *proof-false*)))))

(defun h3-rewrite-negation (lib equality)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((not-nil (proof-proof-not-nil proof))
      (symmetric (proof-proof-symmetric proof equality))
      (rewritten (proof-proof-rewrite proof not-nil symmetric '(1 1))))
     (proof-proof-tidy proof rewritten))))

(defun h3-rewrite-double-negation (lib step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first step))
      (negative (proof-term-at literal 1))
      (term (proof-term-at negative 1))
      (excluded (proof-proof-excluded-middle proof term))
      (cases (proof-proof-front proof excluded (proof-neg term)))
      (cut (proof-proof-cut proof cases step)))
     (proof-proof-front proof cut term))))

(defun h3-rewrite-introduce-double-negation (lib step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first step))
      (opened (proof-proof-unfold proof (proof-neg literal)))
      (opened-literal (proof-step-first opened))
      (conditional (proof-term-at opened-literal 2))
      (selected (proof-proof-select proof conditional step))
      (equality (proof-proof-chain proof opened (list selected))))
     (h3-rewrite-negation lib equality))))

(defun h3-rewrite-nonnil-from-type (lib step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first step))
      (term (proof-term-at literal 1))
      (nil-case (proof-proof-assume proof (proof-eq term *proof-false*) t))
      (false-fact (proof-proof-rewrite proof step nil-case '(1 1)))
      (false-literal (proof-step-first false-fact))
      (value (proof-proof-compute proof false-literal *proof-nil*))
      (rewritten (proof-proof-rewrite proof false-fact value '(1)))
      (false-fact (proof-proof-tidy proof rewritten))
      (cases (proof-proof-nil-or-true proof term))
      (nil-literal (proof-step-first nil-case))
      (front (proof-proof-front proof false-fact (proof-neg nil-literal))))
     (proof-proof-cut proof cases front))))

(defun h3-rewrite-head-of (term)
  (if (proof-compound term)
      (proof-term-at term 0)
    nil))

(defun h3-rewrite-encode-rational (value)
  (cond ((eq value t) 1)
        ((equal (denominator value) 1) (numerator value))
        (t (list "ratio" (numerator value) (denominator value)))))

(defun h3-rewrite-integer-value-p (value)
  (or (integerp value) (eq value t)))

(defun h3-rewrite-integer-value (value)
  (if (eq value t) 1 value))

(defun h3-rewrite-ratio-value (parts)
  (let* ((top (h3-rewrite-integer-value (car parts)))
         (bottom (h3-rewrite-integer-value (cadr parts))))
    (cond ((endp parts) 0)
          ((endp (cdr parts))
           (if (rationalp top)
               top
             '(:failure "malformed-tactic-input" "")))
          ((consp (cddr parts))
           '(:failure "malformed-tactic-input" ""))
          ((not (and (rationalp top) (rationalp bottom)))
           '(:failure "malformed-tactic-input" ""))
          ((equal bottom 0)
           '(:failure "failure" ""))
          (t (/ top bottom)))))

(defun h3-rewrite-rational-value (value)
  (cond ((h3-rewrite-integer-value-p value) (h3-rewrite-integer-value value))
        ((null value) '(:failure "malformed-tactic-input" ""))
        ((and (consp value) (equal (car value) "ratio"))
         (h3-rewrite-ratio-value (cdr value)))
        (t nil)))

(defun h3-rewrite-rational-values (values)
  (if (endp values)
      nil
    (proof-with-checked-results
     ((number (h3-rewrite-rational-value (car values)))
      (rest (h3-rewrite-rational-values (cdr values))))
     (cons number rest))))

(defun h3-rewrite-primitive-numbers (head values)
  (proof-with-checked-results ((numbers (h3-rewrite-rational-values values)))
    (if (member-equal nil numbers)
        :none
      (let ((a (car numbers)))
        (cond ((equal head *proof-minus*) (h3-rewrite-encode-rational (- a)))
              ((equal head *h3-rewrite-reciprocal*)
               (if (equal a 0) 0 (h3-rewrite-encode-rational (/ a))))
              ((endp (cdr numbers)) '(:failure "malformed-tactic-input" ""))
              ((equal head *proof-plus*)
               (h3-rewrite-encode-rational (+ a (cadr numbers))))
              ((equal head *proof-times*)
               (h3-rewrite-encode-rational (* a (cadr numbers))))
              (t (if (< a (cadr numbers)) *proof-t* *proof-nil*)))))))

(defun h3-rewrite-primitive-cdr (x)
  (let ((rest (cdr x)))
    (cond ((endp rest) *proof-nil*)
          ((and (endp (cdr rest)) (null (car rest))) '(:failure "malformed-tactic-input" ""))
          ((and (endp (cdr rest)) (consp (car rest)) (equal (caar rest) "dot"))
           (proof-term-at (car rest) 1))
          (t rest))))

(defun h3-rewrite-primitive-value (head values)
  (if (endp values)
      '(:failure "malformed-tactic-input" "")
    (let* ((x (car values))
           (tag (and (consp x) (stringp (car x)) (car x))))
      (cond
       ((member-equal head (list *library-numberp* *h3-rewrite-characterp*
                                 *h3-rewrite-symbolp* *h3-rewrite-stringp*))
        (if (cond ((equal head *library-numberp*)
                   (or (h3-rewrite-integer-value-p x) (member-equal tag '("ratio" "complex"))))
                  ((equal head *h3-rewrite-characterp*) (equal tag "char"))
                  ((equal head *h3-rewrite-symbolp*) (equal tag "sym"))
                  (t (equal tag "str")))
            *proof-t* *proof-nil*))
       ((equal head *proof-if*)
        (let ((index (if (equal x *proof-nil*) 2 1)))
          (if (< index (len values)) (nth index values) '(:failure "malformed-tactic-input" ""))))
       ((and (member-equal head (list *library-car* *library-cdr*))
             (not (proof-compound x))) *proof-nil*)
       ((equal head *library-car*) (proof-term-at x 0))
       ((equal head *library-cdr*) (h3-rewrite-primitive-cdr x))
       ((equal head *proof-cons*)
        (if (endp (cdr values))
            '(:failure "malformed-tactic-input" "")
          (proof-constant-cons-value x (cadr values))))
       ((member-equal head (list (proof-cl "REALPART") (proof-cl "IMAGPART")))
        (let ((real-p (equal head (proof-cl "REALPART"))))
          (cond ((equal tag "complex") (proof-term-at x (if real-p 1 2)))
                (real-p (proof-with-checked-results ((number (h3-rewrite-rational-value x)))
                          (if number x 0)))
                (t 0))))
       ((equal head (proof-cl "CHAR-CODE"))
        (if (equal tag "char") (proof-term-at x 1) 0))
       ((equal head (proof-cl "CODE-CHAR"))
        (let ((code (h3-rewrite-integer-value x)))
          (list "char" (if (and (integerp code) (<= 0 code) (< code 256)) code 0))))
       ((equal head (proof-cl "COERCE"))
        (cond ((endp (cdr values)) '(:failure "malformed-tactic-input" ""))
              ((and (not (equal (cadr values) (proof-cl "LIST")))
                    (not (proof-compound x))) (list "str" ""))
              (t :none)))
       ((member-equal head (list *proof-plus* *proof-times* *proof-minus*
                                 *h3-rewrite-reciprocal* *proof-less*))
        (h3-rewrite-primitive-numbers head values))
       (t :none)))))

(defun h3-rewrite-primitive (lib call)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((direct (proof-proof-constant proof call)))
      (if direct
          direct
        (let ((head (car call))
              (args (cdr call)))
          (if (and (member-equal head (proof-proof-primitives proof))
                   (proof-all-quoted-p args))
              (proof-with-checked-results
               ((values (proof-quoted-values args))
                (value (h3-rewrite-primitive-value head values)))
               (if (eq value :none) nil (proof-proof-compute proof call value)))
            nil))))))

(defun h3-rewrite-rules (lib propositions equations)
  (list :h3-rules lib propositions equations))

(defun h3-rewrite-rules-lib (rules)
  (cadr rules))

(defun h3-rewrite-rules-propositions (rules)
  (caddr rules))

(defun h3-rewrite-rules-equations (rules)
  (cadddr rules))

(defun h3-rewrite-search-init (lib definitions calls rules budget deep)
  (list :h3-search lib (proof-unique definitions) (proof-unique calls)
        (or rules (h3-rewrite-rules lib nil nil)) budget deep nil))

(defun h3-rewrite-search-lib (search)
  (cadr search))

(defun h3-rewrite-search-definitions (search)
  (caddr search))

(defun h3-rewrite-search-calls (search)
  (cadddr search))

(defun h3-rewrite-search-rules (search)
  (nth 4 search))

(defun h3-rewrite-search-budget (search)
  (nth 5 search))

(defun h3-rewrite-search-deep (search)
  (nth 6 search))

(defun h3-rewrite-search-book (search)
  (nth 7 search))

(defun h3-rewrite-search-with-lib (search lib)
  (let* ((rules (h3-rewrite-search-rules search))
         (updated (update-nth 1 lib search)))
    (if (equal (h3-rewrite-rules-lib rules) (h3-rewrite-search-lib search))
        (update-nth 4 (update-nth 1 lib rules) updated)
      updated)))

(defun h3-rewrite-search-with-book-options (search inference-budget inside-first)
  (update-nth 7 (list inference-budget (* inference-budget 3)
                     (* inference-budget 35) inside-first)
              search))

(defun h3-rewrite-search-visit-term (search)
  (let ((book (h3-rewrite-search-book search)))
    (if (not book)
        (cons nil search)
      (let* ((remaining (1- (caddr book)))
             (updated (update-nth 7 (update-nth 2 remaining book) search)))
        (cons (and (< remaining 0) *h3-rewrite-unproved*)
              updated)))))

(defun h3-rewrite-search-spend-reduction (search)
  (let ((book (h3-rewrite-search-book search)))
    (if (not book)
        (cons nil search)
      (let* ((remaining (1- (cadr book)))
             (updated (update-nth 7 (update-nth 1 remaining book) search)))
        (cons (and (< remaining 0) *h3-rewrite-unproved*)
              updated)))))

(defun h3-rewrite-search-spend-inference (search active)
  (let ((book (h3-rewrite-search-book search)))
    (if (not book)
        (cons nil search)
      (let* ((remaining (1- (car book)))
             (updated (update-nth 7 (update-nth 0 remaining book) search)))
        (cons (and (or (< remaining 0) (> (len active) 14))
                   *h3-rewrite-unproved*)
              updated)))))

(defun h3-rewrite-search-rewrite-atom (search value evidence)
  (let ((negative (and (h3-rewrite-search-book search)
                       (table-get evidence (proof-neg value) nil))))
    (and negative
         (not (proof-compound value))
         (h3-rewrite-nil-value (h3-rewrite-search-lib search) negative))))

(defun h3-rewrite-nested-arguments-p (args)
  (and (consp args)
       (or (consp (h3-rewrite-arguments (car args)))
           (h3-rewrite-nested-arguments-p (cdr args)))))

(defun h3-rewrite-search-arguments-first (search term)
  (and (cadddr (h3-rewrite-search-book search))
       (h3-rewrite-nested-arguments-p (h3-rewrite-arguments term))))

(defun h3-rewrite-any-call-p (args head)
  (and (consp args)
       (or (proof-is-call (car args) head)
           (h3-rewrite-any-call-p (cdr args) head))))

(mutual-recursion
 (defun h3-rewrite-subterm-budget (term remaining)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (if (zp remaining)
       0
     (if (and (consp term) (proof-compound term)
              (not (proof-is-call term *proof-quote*)))
         (h3-rewrite-subterm-list-budget (cdr term) (1- remaining))
       (1- remaining))))

 (defun h3-rewrite-subterm-list-budget (args remaining)
   (declare (xargs :measure (* 2 (acl2-count args))))
   (if (or (zp remaining) (endp args))
       (nfix remaining)
     (h3-rewrite-subterm-list-budget
      (cdr args) (h3-rewrite-subterm-budget (car args) remaining)))))

(defun h3-rewrite-search-should-unfold (search term)
  (proof-with-checked-results ((head (proof-term-at term 0)))
    (let* ((args (cdr term))
           (calls (h3-rewrite-search-calls search))
           (closed (and (member-equal head *h3-rewrite-closed-definitions*)
                        (proof-all-quoted-p args))))
      (cond ((or (equal head *h3-rewrite-return-last*)
                 (member-equal term calls)
                 (member-equal head (h3-rewrite-search-definitions search))
                 closed) t)
            ((and (h3-rewrite-search-book search) calls)
             (let* ((lib (h3-rewrite-search-lib search))
                    (definition (assoc-equal head (proof-proof-definitions
                                                   (library-library-proof lib)))))
               (and definition
                    (or (h3-rewrite-any-call-p args *proof-cons*)
                        (proof-all-quoted-p args))
                    (< 0 (h3-rewrite-subterm-budget (caddr definition) 115)))))
            (t nil)))))

(defun h3-rewrite-character-data (chars)
  (if (endp chars)
      nil
    (cons (list "char" (char-code (car chars)))
          (h3-rewrite-character-data (cdr chars)))))

(defun h3-rewrite-book-evaluate (lib term)
  (let ((head (car term)))
    (proof-with-checked-results ((value (proof-term-at (cadr term) 1)))
      (let ((proof (library-library-proof lib)))
        (cond ((equal head (proof-cl "SYMBOL-NAME"))
               (proof-with-checked-results
                ((name (cond ((null value) '(:failure "malformed-tactic-input" ""))
                             ((and (consp value) (equal (car value) "sym"))
                              (proof-term-at value 2))
                             (t ""))))
                (proof-proof-compute proof term (list "str" name))))
              ((member-equal head (list (proof-cl "NUMERATOR") (proof-cl "DENOMINATOR")))
               (proof-with-checked-results ((number (h3-rewrite-rational-value value)))
                 (proof-proof-compute
                  proof term
                  (if (equal head (proof-cl "NUMERATOR"))
                      (if number (numerator number) 0)
                    (if number (denominator number) 1)))))
              ((equal head (proof-cl "COERCE"))
               (proof-with-checked-results
                ((arg (if (consp (cddr term)) (caddr term) '(:failure "malformed-tactic-input" "")))
                 (kind (proof-term-at arg 1)))
                (if (not (equal kind (proof-cl "LIST")))
                    nil
                  (proof-with-checked-results
                   ((chars (cond ((null value) '(:failure "malformed-tactic-input" ""))
                                 ((and (consp value) (equal (car value) "str"))
                                  (proof-with-checked-results
                                   ((text (proof-term-at value 1)))
                                   (h3-rewrite-character-data (coerce text 'list))))
                                 (t nil))))
                   (proof-proof-compute proof term (or chars *proof-nil*))))))
              (t nil))))))

(defun h3-rewrite-search-evaluate (search term)
  (let ((lib (h3-rewrite-search-lib search)))
    (proof-with-checked-results ((result (h3-rewrite-primitive lib term)))
      (if (or result
              (not (h3-rewrite-search-book search))
              (endp (cdr term))
              (not (proof-all-quoted-p (cdr term))))
          result
        (h3-rewrite-book-evaluate lib term)))))

(defun h3-rewrite-false-disjunction (proof current expression test)
  (if (< (len expression) 4)
      '(:failure "malformed-tactic-input" "")
    (proof-with-checked-results
     ((yes (proof-proof-if-true proof expression))
      (rewritten-yes (proof-proof-rewrite proof current yes '(1 1)))
      (negative-yes (proof-proof-tidy proof rewritten-yes))
      (not-test (proof-proof-subsume
                 proof negative-yes
                 (cons (proof-neg test) (cdr (proof-step-clause negative-yes)))))
      (no (proof-proof-if-false proof expression))
      (rewritten-no (proof-proof-rewrite proof current no '(1 1)))
      (negative-no (proof-proof-tidy proof rewritten-no))
      (discharged (proof-proof-discharge proof negative-no not-test)))
     (list discharged not-test))))

(defun h3-rewrite-expanded-evidence (lib current term)
  (let ((proof (library-library-proof lib)))
    (cond
     ((proof-is-call term *proof-if*)
      (proof-with-checked-results ((no (proof-term-at term 3)))
        (and (equal no *proof-false*)
             (proof-with-checked-results ((conjuncts (proof-proof-conjunct proof current)))
               (list (cadr conjuncts) (car conjuncts))))))
     ((proof-is-call term *proof-not*)
      (proof-with-checked-results ((expression (proof-term-at term 1)))
        (cond ((proof-is-call expression *proof-not*)
               (proof-with-checked-results ((positive (h3-rewrite-double-negation lib current)))
                 (list positive)))
              ((proof-is-call expression *proof-if*)
               (proof-with-checked-results
                ((test (proof-term-at expression 1))
                 (yes (proof-term-at expression 2)))
                (and (equal test yes)
                     (h3-rewrite-false-disjunction proof current expression test))))
              (t nil))))
     (t nil))))

(defun h3-rewrite-add-pending (n lib evidence pending)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) (cons '(:failure "fuel" "h3-rewrite-add-pending") evidence))
   ((endp pending) (cons nil evidence))
   (t
    (let* ((current (car pending))
           (term (proof-step-first current)))
      (cond
       ((failure-p term) (cons term evidence))
       ((assoc-equal term evidence)
        (h3-rewrite-add-pending (1- n) lib evidence (cdr pending)))
       (t
        (let* ((updated (table-put evidence term current))
               (expanded (h3-rewrite-expanded-evidence lib current term)))
          (if (failure-p expanded)
              (cons expanded updated)
            (h3-rewrite-add-pending (1- n) lib updated
                                    (append expanded (cdr pending)))))))))))

(defun h3-rewrite-add-evidence-result (search evidence proof)
  (h3-rewrite-add-pending 1000000 (h3-rewrite-search-lib search) evidence (list proof)))

(defun h3-rewrite-search-add-evidence (search evidence proof)
  (let ((result (h3-rewrite-add-evidence-result search evidence proof)))
    (or (car result) (cdr result))))

(defun h3-rewrite-search-context-extend (search proofs evidence)
  (if (endp proofs)
      evidence
    (proof-with-checked-results
     ((updated (h3-rewrite-search-add-evidence search evidence (car proofs))))
     (h3-rewrite-search-context-extend search (cdr proofs) updated))))

(defun h3-rewrite-search-context (search proofs)
  (h3-rewrite-search-context-extend search proofs nil))

(defun h3-rewrite-known-negative (lib argument term evidence)
  (let ((proof (library-library-proof lib)))
    (cond
     ((proof-is-call argument *proof-not*)
      (proof-with-checked-results ((term-inside (proof-term-at argument 1)))
        (let ((known (assoc-equal term-inside evidence)))
          (and known (h3-rewrite-introduce-double-negation lib (cdr known))))))
     ((proof-is-call argument *proof-equal*)
      (proof-with-checked-results ((args (proof-list-of-length (cdr argument) 2)))
        (let* ((a (car args)) (b (cadr args))
               (reverse (assoc-equal (proof-neg (proof-eq b a)) evidence)))
          (and reverse
               (proof-with-checked-results
                ((assumption (proof-proof-assume proof (proof-eq a b) t))
                 (reversed (proof-proof-symmetric proof assumption))
                 (contradiction (proof-proof-cut proof reversed (cdr reverse))))
                (proof-proof-front proof contradiction term))))))
     (t nil))))

(defun h3-rewrite-search-known (search term evidence)
  (let* ((known (assoc-equal term evidence))
         (lib (h3-rewrite-search-lib search))
         (proof (library-library-proof lib)))
    (cond
     (known (cdr known))
     ((equal term (proof-neg *proof-false*)) (proof-proof-not-nil proof))
     ((proof-is-call term *proof-not*)
      (proof-with-checked-results ((argument (proof-term-at term 1)))
        (h3-rewrite-known-negative lib argument term evidence)))
     ((proof-is-call term *proof-equal*)
      (proof-with-checked-results ((args (proof-list-of-length (cdr term) 2)))
        (let ((a (car args)) (b (cadr args)))
          (if (equal a b)
              (proof-proof-reflexive proof a)
            (let ((reverse (assoc-equal (proof-eq b a) evidence)))
              (and reverse (proof-proof-symmetric proof (cdr reverse))))))))
     ((and (proof-is-call term *proof-quote*) (not (equal term *proof-false*)))
      (proof-with-checked-results
       ((step (proof-proof-nil-or-true proof term))
        (computed (proof-proof-compute proof (proof-eq term *proof-false*) *proof-nil*))
        (rewritten (proof-proof-rewrite proof step computed '(1))))
       (proof-proof-tidy proof rewritten)))
     (t nil))))

(defun h3-rewrite-evidence-rewrites (evidence)
  (if (endp evidence)
      nil
    (let ((literal (caar evidence))
          (proof (cdar evidence)))
      (if (not (proof-is-call literal *proof-equal*))
          (h3-rewrite-evidence-rewrites (cdr evidence))
        (proof-with-checked-results
         ((args (proof-list-of-length (cdr literal) 2))
          (rest (h3-rewrite-evidence-rewrites (cdr evidence))))
         (let ((a (car args)) (b (cadr args)))
           (cond ((and (proof-is-call a *proof-quote*)
                       (not (proof-is-call b *proof-quote*)))
                  (cons (list b proof t) rest))
                 ((not (equal a b)) (cons (list a proof nil) rest))
                 (t rest))))))))

(defun h3-rewrite-right (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun h3-rewrite-contradiction (proof term items evidence)
  (if (endp items)
      nil
    (let ((negative (assoc-equal (proof-neg (caar items)) evidence)))
      (if negative
          (proof-with-checked-results
           ((contradiction (proof-proof-cut proof (cdar items) (cdr negative))))
           (proof-proof-subsume proof contradiction (cons term (proof-step-clause contradiction))))
        (h3-rewrite-contradiction proof term (cdr items) evidence)))))

(defmacro h3-rewrite-with-result (pattern form body)
  (let ((value (car pattern))
        (search (cadr pattern))
        (tests (caddr pattern)))
    `(let ((h3-rewrite-result ,form))
       (let (,@(and value `((,value (car h3-rewrite-result))))
             ,@(and search `((,search (cadr h3-rewrite-result))))
             ,@(and tests `((,tests (caddr h3-rewrite-result)))))
         ,body))))

(defmacro h3-rewrite-with-pair (pattern form body)
  `(let ((h3-rewrite-result ,form))
     (let ((,(car pattern) (car h3-rewrite-result))
           (,(cadr pattern) (cdr h3-rewrite-result)))
       ,body)))

(defmacro h3-rewrite-checked (bindings result failure-tail)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (failure-p ,name)
             (cons ,name ,failure-tail)
           (h3-rewrite-checked ,(cdr bindings) ,result ,failure-tail))))))

(defun h3-rewrite-derive-computed (search term)
  (let ((proof (library-library-proof (h3-rewrite-search-lib search))))
    (and (proof-compound term)
         (proof-with-checked-results ((head (proof-term-at term 0)))
           (and (member-equal head (proof-proof-primitives proof))
                (proof-with-checked-results ((evaluated (h3-rewrite-search-evaluate search term)))
                  (and evaluated
                       (proof-with-checked-results ((value (h3-rewrite-right evaluated)))
                         (and (equal value *proof-true*)
                              (proof-proof-true-from-eq proof evaluated))))))))))

(defun h3-rewrite-saturate-rewrite (search evidence step equality)
  (let ((proof (library-library-proof (h3-rewrite-search-lib search))))
    (h3-rewrite-checked
     ((rewritten (proof-proof-rewrite proof step equality '(1)))
      (tidied (proof-proof-tidy proof rewritten)))
     (h3-rewrite-add-evidence-result search evidence tidied)
     evidence)))

; Search carries the budgets through every attempted proof. Within the
; search, new tests are consed onto the reversed list of tests so far.
(mutual-recursion
 (defun h3-rewrite-rules-apply-fuel (n rules index term search evidence active)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "h3-rewrite-rules-apply-fuel") search)
     (h3-rewrite-checked
      ((head (h3-rewrite-head-of term)))
      (h3-rewrite-rules-apply-candidates
       (1- n) (table-get index head nil) term
       (library-library-proof (h3-rewrite-rules-lib rules)) rules search evidence active)
      search)))

 (defun h3-rewrite-rules-apply-candidates (n candidates term proof rules search evidence active)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "fuel" "h3-rewrite-rules-apply-candidates") search))
    ((endp candidates) (cons nil search))
    (t
     (h3-rewrite-checked
      ((matched (h3-rewrite-match (caar candidates) term nil)))
      (let ((attempt
             (if (not (car matched))
                 (cons nil search)
               (h3-rewrite-checked
                ((instance (proof-proof-instantiate
                            proof (cadar candidates) (table-items (cdr matched)))))
                (h3-rewrite-rules-apply-sides
                 (1- n) (cdr (proof-step-clause instance)) instance proof rules search evidence active)
                search))))
        (if (car attempt)
            attempt
          (h3-rewrite-rules-apply-candidates
           (1- n) (cdr candidates) term proof rules (cdr attempt) evidence active)))
      search))))

 (defun h3-rewrite-rules-apply-sides (n sides instance proof rules search evidence active)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "fuel" "h3-rewrite-rules-apply-sides") search))
    ((endp sides)
     (h3-rewrite-rules-apply-conclusion (1- n) instance rules search evidence active))
    (t
     (let ((side (car sides)))
       (h3-rewrite-checked
        ((guard (if (proof-is-call side *proof-not*)
                    (proof-term-at side 1)
                  (proof-neg side)))
         (known (h3-rewrite-search-known search guard evidence)))
        (h3-rewrite-with-pair
         (step search)
         (cond (known (cons known search))
               ((member-equal guard active) (cons nil search))
               (t (h3-rewrite-with-result
                   (derived search nil)
                   (h3-rewrite-search-derive-fuel
                    (1- n) search guard evidence (add-to-set-equal guard active) nil)
                   (cons (if (h3-rewrite-unproved-p derived) nil derived) search))))
         (cond ((or (not step) (failure-p step)) (cons step search))
               (t (h3-rewrite-checked
                   ((discharged (proof-proof-discharge proof instance step)))
                   (h3-rewrite-rules-apply-sides
                    (1- n) (cdr sides) discharged proof rules search evidence active)
                   search))))
        search)))))

 (defun h3-rewrite-rules-apply-conclusion (n instance rules search evidence active)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "h3-rewrite-rules-apply-conclusion") search)
     (h3-rewrite-checked
      ((first (proof-step-first instance)))
      (if (not (proof-is-call first *library-implies*))
          (cons instance search)
        (h3-rewrite-checked
         ((antecedent (proof-term-at first 1)))
         (if (member-equal antecedent active)
             (cons nil search)
           (h3-rewrite-with-result
            (guard search nil)
            (h3-rewrite-search-derive-fuel
             (1- n) search antecedent evidence (add-to-set-equal antecedent active) nil)
            (cons (cond ((h3-rewrite-unproved-p guard) nil)
                        ((failure-p guard) guard)
                        (t (h3-rewrite-apply-implication
                            (h3-rewrite-rules-lib rules) instance guard)))
                  search)))
         search))
      search)))

 (defun h3-rewrite-search-test-evidence-fuel (n search term evidence active)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "h3-rewrite-search-test-evidence-fuel") search)
     (h3-rewrite-search-test-literals
      (1- n) search (list term (proof-neg term)) term evidence active)))

 (defun h3-rewrite-search-test-literals (n search literals term evidence active)
   (declare (xargs :measure (nfix n)))
   (let* ((rules (h3-rewrite-search-rules search))
          (index (h3-rewrite-rules-propositions rules)))
     (cond
      ((zp n) (cons '(:failure "fuel" "h3-rewrite-search-test-literals") search))
      ((consp literals)
       (let* ((literal (car literals))
              (known (h3-rewrite-search-known search literal evidence)))
         (if known
             (cons known search)
           (let ((answer
                  (if (member-equal literal active)
                      (cons nil search)
                    (h3-rewrite-rules-apply-fuel
                     (1- n) rules index literal search evidence (add-to-set-equal literal active)))))
             (if (car answer)
                 answer
               (h3-rewrite-search-test-literals (1- n) (cdr answer) (cdr literals)
                                                term evidence active))))))
      ((proof-is-call term *proof-not*)
       (h3-rewrite-checked
        ((positive (proof-term-at term 1)))
        (h3-rewrite-with-pair
         (found search)
         (h3-rewrite-rules-apply-fuel
          (1- n) rules index positive search evidence (add-to-set-equal positive active))
         (cons (if (and found (not (failure-p found)))
                   (h3-rewrite-introduce-double-negation (h3-rewrite-search-lib search) found)
                 found)
               search))
        search))
      (t (cons nil search)))))

 (defun h3-rewrite-search-reduce-fuel (n search term evidence tests active)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-reduce-fuel") search tests)
     (h3-rewrite-with-pair
      (spent search) (h3-rewrite-search-spend-reduction search)
      (if spent
          (list spent search tests)
        (h3-rewrite-checked
         ((rewrites (h3-rewrite-evidence-rewrites evidence)))
         (h3-rewrite-search-reduce-visit (1- n) term nil search evidence tests active rewrites)
         (list search tests))))))

 (defun h3-rewrite-search-reduce-visit (n value opening search evidence tests active rewrites)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-reduce-visit") search tests)
     (h3-rewrite-with-pair
      (visited search) (h3-rewrite-search-visit-term search)
      (cond
       (visited (list visited search tests))
       ((> (len opening) 64)
        (list *h3-rewrite-unproved* search tests))
       ((or (member-equal value opening) (member-equal value active)) (list nil search tests))
       (t
        (let* ((lib (h3-rewrite-search-lib search))
               (proof (library-library-proof lib))
               (rewrite (assoc-equal value rewrites)))
          (cond
           (rewrite
            (h3-rewrite-checked
             ((equality (if (caddr rewrite)
                            (proof-proof-symmetric proof (cadr rewrite))
                          (cadr rewrite))))
             (h3-rewrite-search-reduce-follow
              (1- n) equality (add-to-set-equal value opening) search evidence tests active rewrites)
             (list search tests)))
           ((or (not (proof-compound value)) (proof-is-call value *proof-quote*))
            (list (h3-rewrite-search-rewrite-atom search value evidence) search tests))
           (t
            (h3-rewrite-checked
             ((negative (h3-rewrite-search-known search (proof-neg value) evidence)))
             (if negative
                 (list (h3-rewrite-nil-value lib negative) search tests)
               (h3-rewrite-search-reduce-visit-call
                (1- n) value opening search evidence tests active rewrites))
             (list search tests))))))))))

 (defun h3-rewrite-search-reduce-visit-call (n value opening search evidence tests active rewrites)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-reduce-visit-call") search tests)
     (let ((proof (library-library-proof (h3-rewrite-search-lib search))))
       (h3-rewrite-checked
        ((head (proof-term-at value 0)))
        (if (proof-compound head)
            (h3-rewrite-checked
             ((beta (proof-proof-beta proof value)))
             (h3-rewrite-search-reduce-follow
              (1- n) beta (add-to-set-equal value opening) search evidence tests active rewrites)
             (list search tests))
          (h3-rewrite-checked
           ((opening-allowed (h3-rewrite-search-should-unfold search value)))
           (cond ((and opening-allowed (not (h3-rewrite-search-arguments-first search value)))
                  (h3-rewrite-checked
                   ((unfolded (proof-proof-unfold proof value)))
                   (h3-rewrite-search-reduce-follow
                    (1- n) unfolded (add-to-set-equal value opening) search evidence tests active rewrites)
                   (list search tests)))
                 ((equal head *proof-if*)
                  (h3-rewrite-search-reduce-visit-if
                   (1- n) value opening search evidence tests active rewrites))
                 (t (h3-rewrite-search-reduce-visit-arguments
                     (1- n) value opening search evidence tests active rewrites opening-allowed)))
           (list search tests)))
        (list search tests)))))

 (defun h3-rewrite-search-reduce-visit-if (n value opening search evidence tests active rewrites)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-reduce-visit-if") search tests)
     (let ((proof (library-library-proof (h3-rewrite-search-lib search)))
           (test-active (union-equal active opening)))
       (h3-rewrite-checked
        ((test (proof-term-at value 1)))
        (h3-rewrite-with-pair
         (known search)
         (h3-rewrite-search-test-evidence-fuel (1- n) search test evidence test-active)
         (cond
          ((failure-p known) (list known search tests))
          (known (h3-rewrite-search-reduce-select-if
                  (1- n) value opening search evidence tests active rewrites test known nil))
          (t
           (h3-rewrite-with-result
            (test-eq search tests)
            (h3-rewrite-search-reduce-visit (1- n) test opening search evidence tests active rewrites)
            (cond
             ((failure-p test-eq) (list test-eq search tests))
             ((not test-eq)
              (h3-rewrite-search-reduce-select-if
               (1- n) value opening search evidence tests active rewrites test nil nil))
             (t
              (h3-rewrite-checked
               ((reflexive (proof-proof-reflexive proof value))
                (start (proof-proof-rewrite proof reflexive test-eq '(1 2 1)))
                (rewritten (h3-rewrite-right start))
                (new-test (proof-term-at rewritten 1)))
               (h3-rewrite-with-pair
                (new-known search)
                (h3-rewrite-search-test-evidence-fuel (1- n) search new-test evidence test-active)
                (if (failure-p new-known)
                    (list new-known search tests)
                  (h3-rewrite-search-reduce-select-if
                   (1- n) rewritten opening search evidence tests active rewrites new-test new-known start)))
               (list search tests))))))))
        (list search tests)))))

 (defun h3-rewrite-search-reduce-select-if
     (n value opening search evidence tests active rewrites test known start)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (list '(:failure "fuel" "h3-rewrite-search-reduce-select-if") search tests))
    ((or (equal test *proof-false*) known)
     (let ((proof (library-library-proof (h3-rewrite-search-lib search))))
       (h3-rewrite-checked
        ((selected (if (equal test *proof-false*)
                       (proof-with-checked-results ((false (proof-proof-if-false proof value)))
                         (proof-proof-tidy proof false))
                     (proof-proof-select proof value known)))
         (next (if start (proof-proof-chain proof start (list selected)) selected)))
        (h3-rewrite-search-reduce-follow (1- n) next opening search evidence tests active rewrites)
        (list search tests))))
    ((h3-rewrite-search-deep search)
     (h3-rewrite-search-reduce-inside
      (1- n) value opening start '(2 3) search evidence (cons test tests) active rewrites))
    (t (list start search (cons test tests)))))

 (defun h3-rewrite-search-reduce-visit-arguments
     (n value opening search evidence tests active rewrites opening-allowed)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-reduce-visit-arguments") search tests)
     (h3-rewrite-with-result
      (rewritten search tests)
      (h3-rewrite-search-reduce-inside
       (1- n) value opening nil (seq-range 1 (len value) 1) search evidence tests active rewrites)
      (h3-rewrite-checked
       ((step rewritten)
        (current (if step (h3-rewrite-right step) value)))
       (cond
        ((and step (not (equal current value)))
         (h3-rewrite-search-reduce-follow
          (1- n) step (add-to-set-equal value opening) search evidence tests active rewrites))
        (opening-allowed
         (let ((proof (library-library-proof (h3-rewrite-search-lib search))))
           (h3-rewrite-checked
            ((unfolded (proof-proof-unfold proof value)))
            (h3-rewrite-search-reduce-follow
             (1- n) unfolded (add-to-set-equal value opening) search evidence tests active rewrites)
            (list search tests))))
        (t
         (h3-rewrite-checked
          ((evaluated (h3-rewrite-search-evaluate search current)))
          (let* ((rules (h3-rewrite-search-rules search))
                 (answer (if evaluated
                             (cons evaluated search)
                           (h3-rewrite-rules-apply-fuel
                            (1- n) rules (h3-rewrite-rules-equations rules) current search evidence
                            (add-to-set-equal current (union-equal active opening))))))
            (h3-rewrite-search-reduce-finish
             (1- n) (car answer) step value current opening (cdr answer) evidence tests active rewrites))
          (list search tests))))
       (list search tests)))))

 (defun h3-rewrite-search-reduce-finish
     (n result rewritten value current opening search evidence tests active rewrites)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (list '(:failure "fuel" "h3-rewrite-search-reduce-finish") search tests))
    ((failure-p result) (list result search tests))
    ((not result) (list rewritten search tests))
    (t
     (h3-rewrite-checked
      ((literal (proof-step-first result))
       (left (proof-term-at literal 1))
       (right (proof-term-at literal 2)))
      (if (equal left right)
          (list rewritten search tests)
        (let ((proof (library-library-proof (h3-rewrite-search-lib search))))
          (h3-rewrite-checked
           ((next (if rewritten (proof-proof-chain proof rewritten (list result)) result)))
           (h3-rewrite-search-reduce-follow
            (1- n) next (add-to-set-equal value (add-to-set-equal current opening))
            search evidence tests active rewrites)
           (list search tests))))
      (list search tests)))))

 (defun h3-rewrite-search-reduce-inside
     (n value opening result positions search evidence tests active rewrites)
   (declare (xargs :measure (nfix n)))
   (let ((proof (library-library-proof (h3-rewrite-search-lib search))))
     (cond
      ((zp n) (list '(:failure "fuel" "h3-rewrite-search-reduce-inside") search tests))
      ((endp positions) (list (and result (proof-proof-tidy proof result)) search tests))
      (t
       (let ((index (car positions)))
         (h3-rewrite-checked
          ((argument (proof-term-at value index)))
          (h3-rewrite-with-result
           (arg-eq search tests)
           (h3-rewrite-search-reduce-visit (1- n) argument opening search evidence tests active rewrites)
           (h3-rewrite-checked
            ((equality arg-eq)
             (next (if equality
                       (proof-with-checked-results
                        ((start (or result (proof-proof-reflexive proof value))))
                        (proof-proof-rewrite proof start equality (list 1 2 index)))
                     result)))
            (h3-rewrite-search-reduce-inside
             (1- n) value opening next (cdr positions) search evidence tests active rewrites)
            (list search tests)))
          (list search tests)))))))

 (defun h3-rewrite-search-reduce-follow (n equality opening search evidence tests active rewrites)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-reduce-follow") search tests)
     (let ((proof (library-library-proof (h3-rewrite-search-lib search))))
       (h3-rewrite-checked
        ((target (h3-rewrite-right equality)))
        (h3-rewrite-with-result
         (visited search tests)
         (h3-rewrite-search-reduce-visit (1- n) target opening search evidence tests active rewrites)
         (h3-rewrite-checked
          ((rest visited))
          (list (proof-proof-chain proof equality (list rest)) search tests)
          (list search tests)))
        (list search tests)))))

 (defun h3-rewrite-search-derive-fuel (n search term evidence active tests)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-derive-fuel") search tests)
     (h3-rewrite-with-pair
      (spent search) (h3-rewrite-search-spend-inference search active)
      (cond
       (spent (list spent search tests))
       ((and (h3-rewrite-search-book search)
             (proof-is-call term *library-implies*)
             (not (assoc-equal term evidence))
             (not (member-equal term active)))
        (h3-rewrite-with-pair
         (attempt search)
         (h3-rewrite-search-prove-fuel (1- n) search term (table-values evidence))
         (if (h3-rewrite-unproved-p attempt)
             (h3-rewrite-search-derive-base (1- n) search term evidence active tests)
           (list attempt search tests))))
       (t (h3-rewrite-search-derive-base (1- n) search term evidence active tests))))))

 (defun h3-rewrite-search-derive-base (n search term evidence active tests)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-derive-base") search tests)
     (let ((known (h3-rewrite-search-known search term evidence)))
       (if known
           (list known search tests)
         (let* ((computed (h3-rewrite-derive-computed search term))
                (false (assoc-equal *proof-false* evidence))
                (lib (h3-rewrite-search-lib search))
                (proof (library-library-proof lib)))
           (cond
            (computed (list computed search tests))
            (false (list (proof-proof-subsume
                          proof (cdr false) (cons term (cdr (proof-step-clause (cdr false)))))
                         search tests))
            (t
             (let ((contradiction (h3-rewrite-contradiction proof term evidence evidence)))
               (if contradiction
                   (list contradiction search tests)
                 (h3-rewrite-with-pair
                  (conjunct search)
                  (h3-rewrite-search-derive-if (1- n) search term evidence active)
                  (if (and conjunct (not (h3-rewrite-unproved-p conjunct)))
                      (list conjunct search tests)
                    (h3-rewrite-search-derive-rules
                     (1- n) search term evidence active tests))))))))))))

 (defun h3-rewrite-search-derive-if (n search term evidence active)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "fuel" "h3-rewrite-search-derive-if") search))
    ((not (proof-is-call term *proof-if*)) (cons nil search))
    (t
     (h3-rewrite-checked
      ((no (proof-term-at term 3)))
      (if (not (equal no *proof-false*))
          (cons nil search)
        (h3-rewrite-with-result
         (test search nil)
         (h3-rewrite-search-derive-fuel (1- n) search (cadr term) evidence active nil)
         (h3-rewrite-checked
          ((condition test))
          (h3-rewrite-with-result
           (result search nil)
           (h3-rewrite-search-derive-fuel (1- n) search (caddr term) evidence active nil)
           (let ((proof (library-library-proof (h3-rewrite-search-lib search))))
             (h3-rewrite-checked
              ((step result)
               (selected (proof-proof-select proof term condition)))
              (cons (proof-proof-transport proof step selected) search)
              search)))
          search)))
      search))))

 (defun h3-rewrite-search-derive-rules (n search term evidence active tests)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-derive-rules") search tests)
     (let ((rules (h3-rewrite-search-rules search)))
       (h3-rewrite-with-pair
        (step search)
        (h3-rewrite-rules-apply-fuel
         (1- n) rules (h3-rewrite-rules-propositions rules) term search evidence active)
        (if step
            (list step search tests)
          (h3-rewrite-search-derive-premises (1- n) search term evidence active tests evidence))))))

 (defun h3-rewrite-search-derive-premises (n search term evidence active tests premises)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (list '(:failure "fuel" "h3-rewrite-search-derive-premises") search tests))
    ((endp premises)
     (h3-rewrite-search-derive-reduced (1- n) search term evidence active tests))
    ((not (proof-is-call (caar premises) *library-implies*))
     (h3-rewrite-search-derive-premises (1- n) search term evidence active tests (cdr premises)))
    (t
     (let ((premise (caar premises)))
       (h3-rewrite-checked
        ((conclusion (proof-term-at premise 2)))
        (let ((antecedent (cadr premise)))
          (h3-rewrite-with-pair
           (attempt search)
           (if (or (not (equal conclusion term)) (member-equal antecedent active))
               (cons nil search)
             (h3-rewrite-with-result
              (guard search nil)
              (h3-rewrite-search-derive-fuel
               (1- n) search antecedent evidence (add-to-set-equal antecedent active) nil)
              (h3-rewrite-checked
               ((step guard))
               (cons (h3-rewrite-apply-implication
                      (h3-rewrite-search-lib search) (cdar premises) step) search)
               search)))
           (if (and attempt (not (h3-rewrite-unproved-p attempt)))
               (list attempt search tests)
             (h3-rewrite-search-derive-premises
              (1- n) search term evidence active tests (cdr premises)))))
        (list search tests))))))

 (defun h3-rewrite-search-derive-reduced (n search term evidence active tests)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-derive-reduced") search tests)
     (h3-rewrite-with-result
      (reduced search tests)
      (h3-rewrite-search-reduce-fuel (1- n) search term evidence tests (remove-equal term active))
      (h3-rewrite-checked
       ((equality reduced)
        (target (and equality (h3-rewrite-right equality))))
       (if (and equality (not (equal target term)) (not (member-equal target active)))
           (h3-rewrite-with-result
            (result search tests)
            (h3-rewrite-search-derive-fuel
             (1- n) search target evidence (add-to-set-equal term active) tests)
            (h3-rewrite-checked
             ((step result))
             (list (proof-proof-transport (library-library-proof (h3-rewrite-search-lib search))
                                          step equality)
                   search tests)
             (list search tests)))
         (h3-rewrite-search-derive-negated (1- n) search term evidence active tests))
       (list search tests)))))

 (defun h3-rewrite-search-derive-negated (n search term evidence active tests)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (list '(:failure "fuel" "h3-rewrite-search-derive-negated") search tests))
    ((not (proof-is-call term *proof-not*))
     (list *h3-rewrite-unproved* search tests))
    (t
     (h3-rewrite-checked
      ((argument (proof-term-at term 1)))
      (h3-rewrite-with-result
       (reduced search tests)
       (h3-rewrite-search-reduce-fuel (1- n) search argument evidence tests active)
       (h3-rewrite-checked
        ((value reduced)
         (target (and value (h3-rewrite-right value))))
        (list (if (and value (equal target *proof-false*))
                  (h3-rewrite-negation (h3-rewrite-search-lib search) value)
                *h3-rewrite-unproved*)
              search tests)
        (list search tests)))
      (list search tests)))))

 (defun h3-rewrite-search-saturate-fuel (n search evidence tests)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-saturate-fuel") search evidence tests)
     (let* ((result (h3-rewrite-search-saturate-items (1- n) search evidence evidence tests))
            (updated (caddr result)))
       (if (or (car result) (equal (len updated) (len evidence)))
           result
         (h3-rewrite-search-saturate-fuel (1- n) (cadr result) updated (cadddr result))))))

 (defun h3-rewrite-search-saturate-items (n search items evidence tests)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (list '(:failure "fuel" "h3-rewrite-search-saturate-items") search evidence tests))
    ((endp items) (list nil search evidence tests))
    (t
     (let ((term (caar items))
           (step (cdar items)))
       (h3-rewrite-with-result
        (failed search evidence)
        (if (proof-is-call term *library-implies*)
            (h3-rewrite-search-saturate-implication (1- n) search term step evidence)
          (list nil search evidence))
        (if failed
            (list failed search evidence tests)
          (h3-rewrite-checked
           ((context (table-delete evidence term)))
           (h3-rewrite-with-result
            (reduced search tests)
            (h3-rewrite-search-reduce-fuel (1- n) search term context tests nil)
            (h3-rewrite-checked
             ((equality reduced)
              (target (and equality (h3-rewrite-right equality))))
             (let ((next (if (and equality (not (equal target term)))
                             (h3-rewrite-saturate-rewrite search evidence step equality)
                           (cons nil evidence))))
               (if (car next)
                   (list (car next) search (cdr next) tests)
                 (h3-rewrite-search-saturate-items (1- n) search (cdr items) (cdr next) tests)))
             (list search evidence tests)))
           (list search evidence tests))))))))

 (defun h3-rewrite-search-saturate-implication (n search term step evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (list '(:failure "fuel" "h3-rewrite-search-saturate-implication") search evidence)
     (h3-rewrite-checked
      ((conclusion (proof-term-at term 2)))
      (if (assoc-equal conclusion evidence)
          (list nil search evidence)
        (let ((antecedent (cadr term)))
          (h3-rewrite-with-result
           (guard search nil)
           (h3-rewrite-search-derive-fuel (1- n) search antecedent evidence (list antecedent) nil)
           (let ((result
                  (h3-rewrite-checked
                   ((guard guard)
                    (implied (h3-rewrite-apply-implication (h3-rewrite-search-lib search) step guard)))
                   (h3-rewrite-add-evidence-result search evidence implied)
                   evidence)))
             (list (and (not (h3-rewrite-unproved-p (car result))) (car result))
                   search (cdr result))))))
      (list search evidence))))

 (defun h3-rewrite-search-prove-fuel (n search term hypotheses)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "h3-rewrite-search-prove-fuel") search)
     (h3-rewrite-checked
      ((evidence (h3-rewrite-search-context search hypotheses)))
      (h3-rewrite-search-prove-solve (1- n) term evidence search)
      search)))

 (defun h3-rewrite-search-prove-solve (n goal context search)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "h3-rewrite-search-prove-solve") search)
     (let* ((budget (1- (h3-rewrite-search-budget search)))
            (search (update-nth 5 budget search)))
       (cond
        ((< budget 0) (cons *h3-rewrite-unproved* search))
        ((proof-is-call goal *library-implies*)
         (let* ((lib (h3-rewrite-search-lib search))
                (proof (library-library-proof lib)))
           (h3-rewrite-checked
            ((antecedent (proof-term-at goal 1))
             (assumed (proof-proof-assume proof antecedent t))
             (guarded (h3-rewrite-search-add-evidence search context assumed))
             (consequent (proof-term-at goal 2)))
            (h3-rewrite-with-pair
             (result search)
             (h3-rewrite-search-prove-solve (1- n) consequent guarded search)
             (h3-rewrite-checked
              ((step result)) (cons (h3-rewrite-implication lib antecedent step) search) search))
            search)))
        (t
         (let* ((saturated (h3-rewrite-search-saturate-fuel (1- n) search context nil))
                (search (cadr saturated))
                (context (caddr saturated))
                (tests (cadddr saturated)))
           (if (car saturated)
               (cons (car saturated) search)
             (h3-rewrite-with-result
              (result search goal-tests)
              (h3-rewrite-search-derive-fuel (1- n) search goal context nil nil)
              (if (not (h3-rewrite-unproved-p result))
                  (cons result search)
                (h3-rewrite-search-prove-tests
                 (1- n) (proof-unique (append (reverse tests) (reverse goal-tests)))
                 goal context search result))))))))))

 (defun h3-rewrite-search-prove-tests (n tests goal context search failure)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "fuel" "h3-rewrite-search-prove-tests") search))
    ((endp tests) (cons failure search))
    (t
     (let ((test (car tests)))
       (h3-rewrite-checked
        ((known (or (equal test *proof-false*)
                    (h3-rewrite-search-known search test context)
                    (h3-rewrite-search-known search (proof-neg test) context))))
        (if known
            (h3-rewrite-search-prove-tests (1- n) (cdr tests) goal context search failure)
          (h3-rewrite-checked
           ((test (if (proof-is-call test *proof-not*) (proof-term-at test 1) test)))
           (h3-rewrite-search-prove-split (1- n) test goal context search)
           search))
        search)))))

 (defun h3-rewrite-search-prove-split (n test goal context search)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "h3-rewrite-search-prove-split") search)
     (let ((proof (library-library-proof (h3-rewrite-search-lib search))))
       (h3-rewrite-checked
        ((positive (proof-proof-assume proof test t))
         (yes-context (h3-rewrite-search-add-evidence search context positive))
         (negative (proof-proof-assume proof test nil))
         (no-context (h3-rewrite-search-add-evidence search context negative)))
        (h3-rewrite-with-pair
         (yes search)
         (h3-rewrite-search-prove-solve (1- n) goal yes-context search)
         (h3-rewrite-checked
          ((yes yes))
          (h3-rewrite-with-pair
           (no search)
           (h3-rewrite-search-prove-solve (1- n) goal no-context search)
           (h3-rewrite-checked
            ((no no)) (cons (proof-proof-cases proof test yes no) search) search))
          search))
        search)))))

(defun h3-rewrite-search-reduce (search term evidence tests active)
  (h3-rewrite-with-result
   (value search tests)
   (h3-rewrite-search-reduce-fuel 1000000 search term evidence (reverse tests) active)
   (list value search (reverse tests))))

(defun h3-rewrite-search-derive (search term evidence active tests)
  (h3-rewrite-with-result
   (value search tests)
   (h3-rewrite-search-derive-fuel 1000000 search term evidence active (reverse tests))
   (list value search (reverse tests))))

(defun h3-rewrite-search-prove (search term hypotheses)
  (h3-rewrite-search-prove-fuel 1000000 search term hypotheses))

(defun h3-rewrite-rules-index (index head pattern fact)
  (table-put index head (append (table-get index head nil) (list (list pattern fact)))))

(defun h3-rewrite-rules-add-fact (lib name transparent propositions equations)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((fact (proof-proof-fact proof name nil))
      (first (proof-step-first fact))
      (conversion (and transparent
                       (car (h3-rewrite-search-reduce
                             (h3-rewrite-search-init lib transparent nil nil 150 nil)
                             first nil nil nil))))
      (fact (if conversion
                (proof-with-checked-results
                 ((rewritten (proof-proof-rewrite proof fact conversion '(1))))
                 (proof-proof-tidy proof rewritten))
              fact))
      (first (proof-step-first fact))
      (conclusion (if (proof-is-call first *library-implies*) (proof-term-at first 2) first))
      (conclusion-head (h3-rewrite-head-of conclusion)))
     (let ((propositions (h3-rewrite-rules-index propositions conclusion-head conclusion fact)))
       (if (not (proof-is-call conclusion *proof-equal*))
           (cons propositions equations)
         (proof-with-checked-results
          ((left (proof-term-at conclusion 1))
           (left-head (h3-rewrite-head-of left)))
          (cons propositions (h3-rewrite-rules-index equations left-head left fact))))))))

(defun h3-rewrite-rules-index-facts (lib names transparent propositions equations)
  (if (endp names)
      (h3-rewrite-rules lib propositions equations)
    (proof-with-checked-results
     ((indexed (h3-rewrite-rules-add-fact lib (car names) transparent propositions equations)))
     (h3-rewrite-rules-index-facts lib (cdr names) transparent (car indexed) (cdr indexed)))))

(defun h3-rewrite-rules-init (lib names transparent)
  (h3-rewrite-rules-index-facts lib names transparent nil nil))
