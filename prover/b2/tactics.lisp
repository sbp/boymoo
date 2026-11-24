(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-tactics-eq* (proof-cl "EQ"))
(defconst *b2-tactics-eql* (proof-cl "EQL"))
(defconst *b2-tactics-atom* (proof-cl "ATOM"))
(defconst *b2-tactics-endp* (proof-cl "ENDP"))
(defconst *b2-tactics-null* (proof-cl "NULL"))
(defconst *b2-tactics-symbolp* (proof-cl "SYMBOLP"))
(defconst *b2-tactics-characterp* (proof-cl "CHARACTERP"))
(defconst *b2-tactics-coerce* (proof-cl "COERCE"))
(defconst *b2-tactics-iff* (proof-sym "IFF" "ACL2"))
(defconst *b2-tactics-projections*
  (list (proof-sym "MV-NTH" "ACL2") (proof-cl "NTH")))
(defconst *b2-tactics-logic*
  (list *b2-tactics-iff* *library-implies* *termination-return-last*
        (proof-cl "=") *b2-tactics-atom* *b2-tactics-endp* *b2-tactics-eq*
        *b2-tactics-eql* *proof-not* *b2-tactics-null*))
(defconst *b2-tactics-boolean-heads*
  (list *library-numberp* *proof-less* *b2-tactics-characterp* *proof-consp*
        *proof-equal* *proof-integerp* *proof-not* (proof-cl "RATIONALP")
        (proof-cl "STRINGP") *b2-tactics-symbolp*))

(defun b2-tactics-unproved ()
  '(:failure "Unproved" ""))

(defun b2-tactics-unproved-p (value)
  (and (failure-p value) (equal (cadr value) "Unproved")))

(defun b2-tactics-tag (datum name)
  (and (consp datum) (equal (car datum) name)))

(defun b2-tactics-variable (term)
  (b2-tactics-tag term "sym"))

(defun b2-tactics-cons-parts (value)
  (cond ((or (not (proof-compound value)) (endp value))
         (list *proof-nil* *proof-nil*))
        ((endp (cdr value)) (list (car value) *proof-nil*))
        ((and (endp (cddr value)) (b2-tactics-tag (cadr value) "dot"))
         (proof-with-checked-results ((tail (proof-term-at (cadr value) 1)))
           (list (car value) tail)))
        (t (list (car value) (cdr value)))))

(defun b2-tactics-field-repeat (term index)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (list *library-car* term)
    (b2-tactics-field-repeat (list *library-cdr* term) (1- index))))

(defun b2-tactics-field (term index)
  (cond ((eq index t) (b2-tactics-field-repeat term 1))
        ((integerp index) (b2-tactics-field-repeat term index))
        (t '(:failure "tactic-rejected" ""))))

(defun b2-tactics-fraction (args)
  (cond ((endp args) 0)
        ((endp (cdr args))
         (cond ((eq (car args) t) 1)
               ((rationalp (car args)) (car args))
               (t '(:failure "tactic-rejected" ""))))
        ((consp (cddr args))
         '(:failure "tactic-rejected" ""))
        ((and (or (rationalp (car args)) (eq (car args) t))
              (or (rationalp (cadr args)) (eq (cadr args) t)))
         (let ((a (if (eq (car args) t) 1 (car args)))
               (b (if (eq (cadr args) t) 1 (cadr args))))
           (if (equal b 0)
               '(:failure "failure" "")
             (/ a b))))
        (t '(:failure "tactic-rejected" ""))))

(defun b2-tactics-rational-value (datum)
  (cond ((integerp datum) datum)
        ((eq datum t) 1)
        ((b2-tactics-tag datum "ratio") (b2-tactics-fraction (cdr datum)))
        (t nil)))

(defun b2-tactics-rational-datum (value)
  (cond ((eq value t) 1)
        ((integerp value) value)
        ((rationalp value) (list "ratio" (numerator value) (denominator value)))
        (t '(:failure "failure" ""))))

(mutual-recursion
 (defun b2-tactics-match (pattern term bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (cond ((b2-tactics-variable pattern)
          (let ((entry (assoc-equal pattern bindings)))
            (if entry
                (cons (equal (cdr entry) term) bindings)
              (cons t (table-put bindings pattern term)))))
         ((and (consp pattern) (proof-compound pattern)
               (not (equal (car pattern) *proof-quote*)))
          (if (and (proof-compound term) (equal (len pattern) (len term))
                   (equal (car pattern) (car term)))
              (b2-tactics-match-args (cdr pattern) (cdr term) bindings)
            (cons nil bindings)))
         (t (cons (equal pattern term) bindings))))

 (defun b2-tactics-match-args (patterns terms bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (endp patterns)
       (cons t bindings)
     (let ((result (b2-tactics-match (car patterns) (car terms) bindings)))
       (if (car result)
           (b2-tactics-match-args (cdr patterns) (cdr terms) (cdr result))
         result)))))

(mutual-recursion
 (defun b2-tactics-first-test-found (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) nil)
         ((endp term) '(:failure "tactic-rejected" ""))
         ((equal (car term) *proof-quote*) nil)
         ((equal (car term) *proof-if*)
          (proof-with-checked-results ((test (proof-term-at term 1)))
            (list test)))
         (t (b2-tactics-first-test-args (cdr term)))))

 (defun b2-tactics-first-test-args (args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (let ((test (b2-tactics-first-test-found (car args))))
       (if test test (b2-tactics-first-test-args (cdr args)))))))

(defun b2-tactics-first-test (term)
  (proof-with-checked-results ((found (b2-tactics-first-test-found term)))
    (car found)))

(mutual-recursion
 (defun b2-tactics-rename-calls (term names)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) term)
         ((endp term) '(:failure "failure" ""))
         ((equal (car term) *proof-quote*) term)
         (t
          (let ((head (car term)))
            (proof-with-checked-results
                ((new-head
                  (if (proof-compound head)
                      (if (and (consp head) (consp (cdr head)) (consp (cddr head)))
                          (proof-with-checked-results
                              ((body (b2-tactics-rename-calls (caddr head) names)))
                            (list (car head) (cadr head) body))
                        '(:failure "failure" ""))
                    (table-get names head head)))
                 (args (b2-tactics-rename-call-args (cdr term) names)))
              (cons new-head args))))))

 (defun b2-tactics-rename-call-args (args names)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results ((arg (b2-tactics-rename-calls (car args) names))
                                  (rest (b2-tactics-rename-call-args (cdr args) names)))
       (cons arg rest)))))

(defun b2-tactics-rebuild (lib value cons-step)
  (proof-with-checked-results
      ((axiom (library-library-axiom lib "CAR-CDR-ELIM" (list value))))
    (proof-proof-modus-ponens (library-library-proof lib) axiom cons-step)))

(defun b2-tactics-tactics-exact (lib name pattern target)
  (let ((matched (b2-tactics-match pattern target nil)))
    (if (car matched)
        (proof-proof-fact (library-library-proof lib) name (table-items (cdr matched)))
      (b2-tactics-unproved))))

(defun b2-tactics-tactics-add-lemma (lib name step clause)
  (let* ((name (proof-sym (concatenate 'string "B2-" name) "ACL2"))
         (clause (if (eq clause :none) (proof-step-clause step) clause))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step (proof-proof-subsume proof step clause))
         (entry (proof-proof-entry "lemma" name (cons name clause) (list step))))
      (let* ((entries (append (library-library-entries lib) (list entry)))
             (facts (table-put (proof-proof-facts proof) name clause))
             (proof (proof-proof-with-facts proof facts)))
        (cons name (library-make-library proof entries))))))

(defun b2-tactics-tactics-close-false (lib term evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((step (proof-proof-nil-or-true proof term))
                                 (step (proof-proof-discharge proof step evidence)))
      (proof-proof-tidy proof step))))

(defun b2-tactics-tactics-boolean-true (lib boolean premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((term (proof-step-first premise))
                                 (literal (proof-step-first boolean)))
      (if (not (equal literal (list (proof-sym "BOOLEANP" "ACL2") term)))
          '(:failure "tactic-rejected" "")
        (proof-with-checked-results
            ((opened (proof-proof-unfold proof literal))
             (body (proof-step-first opened))
             (body (proof-term-at body 2))
             (boolean (proof-proof-rewrite proof boolean opened '(1)))
             (test (proof-term-at body 1))
             (test (proof-proof-unfold proof test))
             (boolean (proof-proof-rewrite proof boolean test '(1 1)))
             (tail (proof-term-at body 3))
             (tail (proof-proof-unfold proof tail))
             (boolean (proof-proof-rewrite proof boolean tail '(1 3)))
             (boolean (proof-proof-tidy proof boolean))
             (true (proof-eq term *proof-true*))
             (no (proof-proof-assume proof true nil))
             (boolean (proof-proof-prove-if proof boolean no))
             (contradicted (proof-proof-rewrite proof premise boolean '(1)))
             (contradicted (proof-proof-tidy proof contradicted)))
          (proof-proof-front proof contradicted true))))))

(defun b2-tactics-truth-value-fact (lib term premise)
  (let* ((proof (library-library-proof lib))
         (facts (proof-proof-facts proof)))
    (proof-with-checked-results ((head (proof-term-at term 0))
                                 (head-name (proof-term-at head 2)))
      (let ((name (concatenate 'string "booleanp-" (text-lower head-name))))
        (if (assoc-equal (list "str" name) facts)
            (proof-with-checked-results
                ((boolean (proof-proof-fact proof name
                                           (seq-zip (list *library-x* *library-y*) (cdr term)))))
              (b2-tactics-tactics-boolean-true lib boolean premise))
          (let ((name (if (equal head *b2-tactics-characterp*)
                          (proof-sym "BOOLEANP-CHARACTERP" "ACL2")
                        (proof-sym (concatenate 'string "BOOL-" head-name) "ACL2"))))
            (if (not (assoc-equal name facts))
                nil
              (proof-with-checked-results
                  ((arg (proof-term-at term 1))
                   (boolean (proof-proof-fact proof name (list (list *library-x* arg)))))
                (b2-tactics-tactics-boolean-true lib boolean premise)))))))))

(defun b2-tactics-tactics-truth-value (lib term value premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((premise (if premise premise (proof-proof-assume proof term value))))
      (cond ((not value) (b2-tactics-tactics-close-false lib term premise))
            ((proof-is-call term *proof-equal*)
             (proof-with-checked-results
                 ((arg (proof-term-at term 1))
                  (same (proof-proof-fact proof "equal-same" (list (list *library-x* arg))))
                  (rewritten (proof-proof-rewrite proof same premise '(1 1 2))))
               (proof-proof-tidy proof rewritten)))
            ((proof-is-call term *proof-not*)
             (proof-with-checked-results
                 ((opened (proof-proof-unfold proof term))
                  (arg (proof-term-at term 1))
                  (selected (proof-proof-select proof (proof-ite arg *proof-false* *proof-true*)
                                                premise)))
               (proof-proof-chain proof opened (list selected))))
            (t (b2-tactics-truth-value-fact lib term premise))))))

(defun b2-tactics-evidence-if (proof step term)
  (if (not (proof-is-call term *proof-if*))
      nil
    (proof-with-checked-results ((no (proof-term-at term 3)))
      (cond ((equal no *proof-false*) (proof-proof-conjunct proof step))
            ((equal (caddr term) *proof-false*)
             (proof-with-checked-results
                 ((branch (proof-proof-if-true proof term))
                  (stopped (proof-proof-rewrite proof step branch '(1)))
                  (stopped (proof-proof-tidy proof stopped))
                  (stopped (proof-proof-front proof stopped (proof-neg (cadr term))))
                  (other (proof-proof-prove-if proof step stopped)))
               (list stopped other)))
            (t nil)))))

(defun b2-tactics-evidence-unfold (proof step inner place)
  (cond ((not (proof-compound inner)) nil)
        ((endp inner) '(:failure "tactic-rejected" ""))
        ((member-equal (car inner) (list *b2-tactics-atom* *b2-tactics-endp*
                                         *b2-tactics-eq* *b2-tactics-eql*
                                         *b2-tactics-null* (proof-cl "=")
                                         *termination-return-last*))
         (proof-with-checked-results
             ((opened (proof-proof-unfold proof inner))
              (rewritten (proof-proof-rewrite proof step opened place))
              (tidied (proof-proof-tidy proof rewritten)))
           (list tidied)))
        (t nil)))

(defun b2-tactics-evidence-not-if (proof step inner test)
  (if (endp (cdddr inner))
      '(:failure "tactic-rejected" "")
    (proof-with-checked-results
        ((branch (proof-proof-if-true proof inner))
         (conflict (proof-proof-rewrite proof step branch '(1 1)))
         (assumed (proof-proof-assume proof test t))
         (conflict (proof-proof-front proof conflict (proof-neg test)))
         (impossible (proof-proof-cut proof assumed conflict))
         (stopped (proof-proof-front proof impossible (proof-neg test)))
         (branch (proof-proof-if-false proof inner))
         (rest (proof-proof-rewrite proof step branch '(1 1)))
         (rest (proof-proof-tidy proof rest))
         (rest (proof-proof-discharge proof rest stopped)))
      (list stopped rest))))

(defun b2-tactics-evidence-not (proof step term inner)
  (cond
   ((proof-is-call inner *proof-not*)
    (proof-with-checked-results
        ((test (proof-term-at inner 1))
         (opened (proof-proof-unfold proof term))
         (body (proof-step-first opened))
         (body (proof-term-at body 2))
         (assumed (proof-proof-assume proof test nil))
         (selected (proof-proof-select proof body assumed))
         (chain (proof-proof-chain proof opened (list selected)))
         (exhausted (proof-proof-rewrite proof step chain '(1)))
         (exhausted (proof-proof-tidy proof exhausted))
         (derived (proof-proof-front proof exhausted test)))
      (list derived)))
   ((proof-is-call inner *proof-if*)
    (proof-with-checked-results ((test (proof-term-at inner 1))
                                 (yes (proof-term-at inner 2)))
      (if (equal test yes) (b2-tactics-evidence-not-if proof step inner test) nil)))
   (t (b2-tactics-evidence-unfold proof step inner '(1 1)))))

(defun b2-tactics-evidence-pending (n proof pending found)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-tactics-evidence-pending"))
   ((endp pending) found)
   (t
    (let ((step (car pending)))
      (proof-with-checked-results ((step step) (term (proof-step-first step)))
        (if (assoc-equal term found)
            (b2-tactics-evidence-pending (1- n) proof (cdr pending) found)
          (proof-with-checked-results
              ((found (table-put found term step))
               (conditional (b2-tactics-evidence-if proof step term))
               (rest (if (proof-is-call term *proof-not*)
                         (proof-with-checked-results ((inner (proof-term-at term 1)))
                           (b2-tactics-evidence-not proof step term inner))
                       (b2-tactics-evidence-unfold proof step term '(1)))))
            (b2-tactics-evidence-pending (1- n) proof
                                        (append (cdr pending) conditional rest) found))))))))

(defun b2-tactics-tactics-evidence (lib steps)
  (b2-tactics-evidence-pending 1000000 (library-library-proof lib) steps nil))

(defun b2-tactics-tactics-prove-ground (lib term)
  (if (and (proof-is-call term *proof-quote*) (not (equal term *proof-false*)))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((step (proof-proof-nil-or-true proof term))
             (equality (proof-proof-compute proof (proof-eq term *proof-false*) *proof-nil*))
             (rewritten (proof-proof-rewrite proof step equality '(1))))
          (proof-proof-tidy proof rewritten)))
    '(:failure "tactic-rejected" "")))

(defun b2-tactics-contradiction-scan (proof goal items evidence)
  (if (endp items)
      nil
    (let* ((literal (caar items))
           (step (cdar items))
           (opposite (assoc-equal (proof-neg literal) evidence)))
      (if (or (equal literal *proof-false*) opposite)
          (proof-with-checked-results
              ((conflict (if (equal literal *proof-false*)
                             (proof-proof-tidy proof step)
                           (proof-proof-cut proof step (cdr opposite)))))
            (proof-proof-subsume proof conflict (cons goal (proof-step-clause conflict))))
        (b2-tactics-contradiction-scan proof goal (cdr items) evidence)))))

(defun b2-tactics-tactics-contradiction (lib goal evidence)
  (b2-tactics-contradiction-scan (library-library-proof lib) goal evidence evidence))

(defun b2-tactics-list-at (values index)
  (if (< index (len values))
      (nth index values)
    '(:failure "tactic-rejected" "")))

(defun b2-tactics-rational-values (values)
  (if (endp values)
      nil
    (proof-with-checked-results ((number (b2-tactics-rational-value (car values)))
                                 (rest (b2-tactics-rational-values (cdr values))))
      (cons number rest))))

(defun b2-tactics-complex-value-p (values)
  (and (consp values)
       (or (b2-tactics-tag (car values) "complex")
           (b2-tactics-complex-value-p (cdr values)))))

(defun b2-tactics-constant-arithmetic (proof term values)
  (let ((head (car term)))
    (proof-with-checked-results ((numbers (b2-tactics-rational-values values)))
      (let ((part (member-equal head (list (proof-cl "NUMERATOR") (proof-cl "DENOMINATOR")))))
        (cond
         ((and part (endp numbers)) (b2-tactics-list-at numbers 0))
         ((and part (not (car numbers)))
          (proof-proof-compute proof term (if (equal head (proof-cl "DENOMINATOR")) 1 0)))
         ((b2-tactics-complex-value-p values) nil)
         (t
          (proof-with-checked-results
              ((first (b2-tactics-list-at numbers 0))
               (a (or first 0))
               (value
                (cond ((equal head (proof-cl "NUMERATOR")) (numerator a))
                      ((equal head (proof-cl "DENOMINATOR")) (denominator a))
                      ((equal head (proof-sym "UNARY-/" "ACL2"))
                       (if (equal a 0) 0 (b2-tactics-rational-datum (/ a))))
                      ((equal head *proof-minus*) (b2-tactics-rational-datum (- a)))
                      (t (proof-with-checked-results ((second (b2-tactics-list-at numbers 1)))
                           (let ((b (or second 0)))
                             (cond ((equal head *proof-less*)
                                    (if (< a b) *proof-t* *proof-nil*))
                                   ((equal head *proof-plus*) (b2-tactics-rational-datum (+ a b)))
                                   (t (b2-tactics-rational-datum (* a b))))))))))
            (proof-proof-compute proof term value))))))))

(defun b2-tactics-constant-characters (chars)
  (if (endp chars)
      nil
    (cons (list "char" (char-code (car chars)))
          (b2-tactics-constant-characters (cdr chars)))))

(defun b2-tactics-constant-coerce (proof term values)
  (proof-with-checked-results ((kind (b2-tactics-list-at values 1)))
    (if (not (equal kind (proof-cl "LIST")))
        nil
      (proof-with-checked-results
          ((datum (b2-tactics-list-at values 0))
           (value (if (b2-tactics-tag datum "str")
                      (proof-with-checked-results ((bytes (proof-term-at datum 1)))
                        (or (b2-tactics-constant-characters (coerce bytes 'list)) *proof-nil*))
                    *proof-nil*)))
        (proof-proof-compute proof term value)))))

(defun b2-tactics-constant-element (head datum)
  (cond
   ((member-equal head (list *library-car* *library-cdr*))
    (proof-with-checked-results ((parts (b2-tactics-cons-parts datum)))
      (if (equal head *library-cdr*) (cadr parts) (car parts))))
   ((equal head *b2-tactics-symbolp*) (if (b2-tactics-tag datum "sym") *proof-t* *proof-nil*))
   ((equal head *b2-tactics-characterp*) (if (b2-tactics-tag datum "char") *proof-t* *proof-nil*))
   ((equal head (proof-cl "CODE-CHAR"))
    (list "char" (if (or (eq datum t) (and (integerp datum) (<= 0 datum) (< datum 256))) datum 0)))
   ((equal head (proof-cl "CHAR-CODE"))
    (if (b2-tactics-tag datum "char") (proof-term-at datum 1) 0))
   ((equal head (proof-cl "SYMBOL-NAME"))
    (proof-with-checked-results ((name (if (b2-tactics-tag datum "sym") (proof-term-at datum 2) "")))
      (list "str" name)))
   ((equal head (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2"))
    (if (not (b2-tactics-tag datum "sym"))
        (list "str" "")
      (proof-with-checked-results ((package (proof-term-at datum 1)))
        (if (member-equal package '("COMMON-LISP" "ACL2" "KEYWORD"))
            (list "str" package)
          :none))))
   (t (proof-with-checked-results ((number (b2-tactics-rational-value datum)))
        (if (or number (b2-tactics-tag datum "complex")) *proof-t* *proof-nil*)))))

(defun b2-tactics-constant-ground (proof term values)
  (let ((head (car term)))
    (cond
     ((equal head *proof-cons*)
      (proof-with-checked-results ((pair (proof-list-of-length values 2)))
        (proof-proof-compute proof term (proof-constant-cons-value (car pair) (cadr pair)))))
     ((equal head *b2-tactics-coerce*) (b2-tactics-constant-coerce proof term values))
     ((member-equal head (list *proof-plus* *proof-times* *proof-minus* *proof-less*
                               (proof-cl "NUMERATOR") (proof-cl "DENOMINATOR")
                               (proof-sym "UNARY-/" "ACL2")))
      (b2-tactics-constant-arithmetic proof term values))
     ((member-equal head (list *library-car* *library-cdr* *b2-tactics-symbolp*
                               *b2-tactics-characterp* (proof-cl "CODE-CHAR") (proof-cl "CHAR-CODE")
                               (proof-cl "SYMBOL-NAME") (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2")
                               *library-numberp*))
      (proof-with-checked-results ((datum (b2-tactics-list-at values 0))
                                   (value (b2-tactics-constant-element head datum)))
        (if (eq value :none) nil (proof-proof-compute proof term value))))
     (t nil))))

(defun b2-tactics-tactics-constant (lib term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((native (proof-proof-constant-base proof term)))
      (cond (native native)
            ((not (proof-all-quoted-p (cdr term))) nil)
            (t (proof-with-checked-results ((values (proof-quoted-values (cdr term))))
                 (b2-tactics-constant-ground proof term values)))))))

(defun b2-tactics-step-result (step)
  (proof-with-checked-results ((first (proof-step-first step)))
    (proof-term-at first 2)))

(defun b2-tactics-normalize-equations (known)
  (if (endp known)
      nil
    (let ((step (cdar known)))
      (proof-with-checked-results
          ((first (proof-step-first step))
           (result (if (proof-is-call first *proof-equal*) (proof-term-at first 2) nil))
           (rest (b2-tactics-normalize-equations (cdr known))))
        (if (proof-is-call result *proof-quote*) (cons step rest) rest)))))

(defun b2-tactics-normalize-matching-rule (term equations)
  (if (endp equations)
      nil
    (proof-with-checked-results
        ((step (car equations))
         (first (proof-step-first step))
         (left (proof-term-at first 1))
         (right (if (equal left term) (proof-term-at first 2) term)))
      (if (and (equal left term) (not (equal right term)))
          step
        (b2-tactics-normalize-matching-rule term (cdr equations))))))

(defun b2-tactics-normalize-select (lib current parts known)
  (let ((proof (library-library-proof lib))
        (test (car parts))
        (yes (cadr parts))
        (no (caddr parts)))
    (cond
     ((proof-is-call test *proof-quote*)
      (if (equal test *proof-false*)
          (proof-proof-fact proof "if-nil" (list (list *library-y* yes) (list *library-z* no)))
        (proof-with-checked-results ((selected (proof-proof-if-true proof current))
                                     (ground (b2-tactics-tactics-prove-ground lib test)))
          (proof-proof-discharge proof selected ground))))
     ((or (assoc-equal test known) (assoc-equal (proof-neg test) known))
      (proof-proof-select proof current
                          (or (cdr (assoc-equal test known))
                              (cdr (assoc-equal (proof-neg test) known)))))
     ((equal yes no)
      (proof-with-checked-results ((selected-yes (proof-proof-if-true proof current))
                                   (selected-no (proof-proof-if-false proof current)))
        (proof-proof-cases proof test selected-yes selected-no)))
     (t nil))))

(defun b2-tactics-normalize-selector (lib head arg known)
  (let ((car-p (equal head *library-car*)))
    (cond
     ((proof-is-call arg *proof-cons*)
      (library-library-axiom lib (if car-p "CAR-CONS" "CDR-CONS") (cdr arg)))
     (t
      (let ((noncons (assoc-equal (proof-neg (list *proof-consp* arg)) known))
            (proof (library-library-proof lib)))
        (if (not noncons)
            nil
          (proof-with-checked-results
              ((completion (library-library-axiom lib
                                                   (if car-p "COMPLETION-OF-CAR" "COMPLETION-OF-CDR")
                                                   (list arg)))
               (result (b2-tactics-step-result completion))
               (branch (proof-proof-select proof result (cdr noncons))))
            (proof-proof-chain proof completion (list branch)))))))))

(defun b2-tactics-normalize-equal (proof current arg known)
  (let* ((opposite (proof-neg current))
         (negative (assoc-equal opposite known)))
    (cond
     (negative
      (proof-with-checked-results
          ((values (proof-proof-fact proof "equal-different"
                                    (seq-zip (list *library-x* *library-y*) (cdr current))))
           (front (proof-proof-front proof (cdr negative) opposite))
           (cut (proof-proof-cut proof values front)))
        (proof-proof-front proof cut (proof-eq current *proof-false*))))
     ((proof-is-call arg *proof-cons*)
      (proof-with-checked-results ((right (proof-term-at current 2)))
        (if (proof-is-call right *proof-cons*)
            (proof-proof-fact proof (proof-sym "CONS-EQUAL" "ACL2")
                              (seq-zip (list (proof-sym "X1" "ACL2") (proof-sym "Y1" "ACL2")
                                            (proof-sym "X2" "ACL2") (proof-sym "Y2" "ACL2"))
                                      (append (cdr arg) (cdr right))))
          nil)))
     (t nil))))

(defun b2-tactics-normalize-basic-step (lib head current known)
  (let ((proof (library-library-proof lib))
        (arg (cadr current)))
    (proof-with-checked-results
        ((step (b2-tactics-tactics-constant lib current))
         (step (if (and (not step) (member-equal head (list *library-car* *library-cdr*)))
                   (b2-tactics-normalize-selector lib head arg known)
                 step))
         (step (if (and (not step) (member-equal head *b2-tactics-boolean-heads*)
                        (assoc-equal current known))
                   (b2-tactics-tactics-truth-value lib current t (cdr (assoc-equal current known)))
                 step))
         (step (if (and (not step) (equal head *proof-consp*) (proof-is-call arg *proof-cons*))
                   (proof-with-checked-results
                       ((fact (proof-proof-fact proof "consp-cons"
                                                (seq-zip (list *library-x* *library-y*) (cdr arg)))))
                     (b2-tactics-tactics-truth-value lib current t fact))
                 step)))
      (if (and (not step) (equal head *proof-equal*))
          (b2-tactics-normalize-equal proof current arg known)
        step))))

(defun b2-tactics-normalize-want (head node current enabled blocked)
  (cond
   ((or (member-equal head *b2-tactics-logic*) (member-equal node enabled)
        (member-equal current enabled)
        (and (member-equal head enabled)
             (or (not (member-equal head blocked)) (proof-all-quoted-p (cdr current))))) t)
   ((and (member-equal head *b2-tactics-projections*) (member-equal head enabled))
    (proof-with-checked-results ((index (proof-term-at current 1)))
      (if (proof-is-call index *proof-quote*)
          (proof-with-checked-results ((value (proof-term-at index 1)))
            (or (eq value t) (and (integerp value) (<= 0 value) (<= value 4))))
        nil)))
   (t nil)))

; A successful visit carries the remaining rewrite budget in its cdr.
(mutual-recursion
 (defun b2-tactics-tactics-normalize-visit (n node blocked lib known equations enabled branches budget)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-tactics-tactics-normalize-visit"))
    ((< (1- budget) 0) (b2-tactics-unproved))
    (t
     (let ((budget (1- budget)))
       (if (proof-is-call node *proof-quote*)
           (cons nil budget)
         (proof-with-checked-results ((rule (b2-tactics-normalize-matching-rule node equations)))
           (cond
            (rule (b2-tactics-normalize-follow (1- n) rule nil blocked lib known equations enabled
                                               branches budget))
            ((not (proof-compound node))
             (let ((negative (assoc-equal (proof-neg node) known)))
               (proof-with-checked-results
                   ((step (and negative (b2-tactics-tactics-close-false lib node (cdr negative)))))
                 (cons step budget))))
            (t
             (proof-with-checked-results ((head (proof-term-at node 0)))
               (let ((negative (assoc-equal (proof-neg node) known))
                     (positive (assoc-equal node known))
                     (proof (library-library-proof lib)))
                 (cond
                  (negative
                   (proof-with-checked-results ((step (b2-tactics-tactics-close-false lib node (cdr negative))))
                     (cons step budget)))
                  ((and positive (not (member-equal head *b2-tactics-boolean-heads*)))
                   (cons nil budget))
                  (t
                   (proof-with-checked-results
                       ((truth (and positive (b2-tactics-tactics-truth-value lib node t (cdr positive)))))
                     (cond
                      (truth (cons truth budget))
                      ((or (proof-compound head) (equal head *termination-return-last*))
                       (proof-with-checked-results
                           ((step (if (proof-compound head)
                                      (proof-proof-beta proof node)
                                    (proof-proof-unfold proof node))))
                         (b2-tactics-normalize-follow (1- n) step nil blocked lib known equations
                                                       enabled branches budget)))
                      ((equal head *proof-if*)
                       (b2-tactics-normalize-if (1- n) node blocked lib known equations enabled
                                                 branches budget))
                      (t (b2-tactics-normalize-ordinary (1- n) node head blocked lib known equations
                                                         enabled branches budget))))))))))))))))

 (defun b2-tactics-tactics-normalize-rewrite-args (n node indexes blocked lib known equations
                                                    enabled branches budget step)
   (declare (xargs :measure (nfix n)))
   (let ((proof (library-library-proof lib)))
     (cond
      ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-tactics-tactics-normalize-rewrite-args"))
      ((endp indexes)
       (proof-with-checked-results ((result (and step (proof-proof-tidy proof step))))
         (cons result budget)))
      (t
       (let ((index (car indexes)))
         (proof-with-checked-results
             ((current (if step (b2-tactics-step-result step) node))
              (old (proof-term-at current index))
              (reduced (b2-tactics-tactics-normalize-visit (1- n) old blocked lib known equations
                                                            enabled branches budget))
              (step (if (car reduced)
                        (proof-with-checked-results ((start (or step (proof-proof-reflexive proof node))))
                          (proof-proof-rewrite proof start (car reduced) (list 1 2 index)))
                      step)))
           (b2-tactics-tactics-normalize-rewrite-args (1- n) node (cdr indexes) blocked lib known
                                                     equations enabled branches (cdr reduced) step)))))))

 (defun b2-tactics-normalize-follow (n step first blocked lib known equations enabled branches budget)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-tactics-normalize-follow")
     (let ((proof (library-library-proof lib)))
       (proof-with-checked-results
           ((result (b2-tactics-step-result step))
            (rest (b2-tactics-tactics-normalize-visit (1- n) result blocked lib known equations
                                                       enabled branches budget))
            (tail (proof-proof-chain proof step (list (car rest))))
            (combined (if first (proof-proof-chain proof first (list tail)) tail)))
         (cons combined (cdr rest))))))

 (defun b2-tactics-normalize-if (n node blocked lib known equations enabled branches budget)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-tactics-normalize-if")
     (let ((proof (library-library-proof lib)))
       (proof-with-checked-results
           ((test (proof-term-at node 1))
            (reduced (if (assoc-equal test known)
                         (cons nil budget)
                       (b2-tactics-tactics-normalize-rewrite-args
                        (1- n) node '(1) blocked lib known equations enabled branches budget nil)))
            (step (car reduced))
            (current (if step (b2-tactics-step-result step) node))
            (parts (proof-list-of-length (cdr current) 3))
            (selected (b2-tactics-normalize-select lib current parts known)))
         (cond
          (selected
           (proof-with-checked-results ((first (if step (proof-proof-chain proof step (list selected)) selected)))
             (b2-tactics-normalize-follow (1- n) first nil blocked lib known equations
                                           enabled branches (cdr reduced))))
          (branches
           (proof-with-checked-results
               ((arms (b2-tactics-tactics-normalize-rewrite-args
                       (1- n) current '(2 3) blocked lib known equations enabled branches (cdr reduced) nil))
                (result (cond ((not (car arms)) step)
                              (step (proof-proof-chain proof step (list (car arms))))
                              (t (car arms)))))
             (cons result (cdr arms))))
          (t reduced))))))

 (defun b2-tactics-normalize-ordinary (n node head blocked lib known equations enabled branches budget)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-tactics-normalize-ordinary")
     (proof-with-checked-results
         ((reduced (b2-tactics-tactics-normalize-rewrite-args
                    (1- n) node (seq-range 1 (len node) 1) blocked lib known equations enabled branches
                    budget nil))
          (first (car reduced))
          (current (if first (b2-tactics-step-result first) node))
          (rule (b2-tactics-normalize-matching-rule current equations)))
       (if rule
           (b2-tactics-normalize-follow (1- n) rule first blocked lib known equations enabled
                                         branches (cdr reduced))
         (proof-with-checked-results ((step (b2-tactics-normalize-basic-step lib head current known)))
           (if step
               (b2-tactics-normalize-follow (1- n) step first blocked lib known equations enabled
                                             branches (cdr reduced))
             (proof-with-checked-results ((want (b2-tactics-normalize-want head node current enabled blocked)))
               (if (not want)
                   reduced
                 (proof-with-checked-results
                     ((step (proof-proof-unfold (library-library-proof lib) current))
                      (value (b2-tactics-step-result step)))
                   (if (equal value current)
                       reduced
                     (b2-tactics-normalize-follow (1- n) step first (cons head blocked) lib known equations
                                                   enabled branches (cdr reduced)))))))))))))

(defun b2-tactics-tactics-normalize (lib term evidence unfold rules budget branches)
  (proof-with-checked-results
      ((known (b2-tactics-tactics-evidence lib evidence))
       (known-equations (b2-tactics-normalize-equations known))
       (result (b2-tactics-tactics-normalize-visit
                1000000 term nil lib known (append rules known-equations) unfold branches budget)))
    (car result)))

(defun b2-tactics-tactics-from-impossible (lib goal premise evidence unfold rules budget branches)
  (let ((proof (library-library-proof lib))
        (negative (proof-is-call goal *proof-not*)))
    (proof-with-checked-results
        ((test (if negative (proof-term-at goal 1) goal))
         (alternate (proof-proof-assume proof test (and negative t)))
         (first (proof-step-first premise))
         (equation (b2-tactics-tactics-normalize lib first (append evidence (list alternate))
                                                unfold rules budget branches))
         (value (and equation (b2-tactics-step-result equation))))
      (if (not (equal value *proof-false*))
          (b2-tactics-unproved)
        (proof-with-checked-results
            ((conflict (proof-proof-rewrite proof premise equation '(1)))
             (conflict (proof-proof-tidy proof conflict))
             (result (proof-proof-subsume proof conflict (cons goal (proof-step-clause conflict)))))
          (proof-proof-front proof result goal))))))

(defun b2-tactics-unresolved (normal)
  (proof-with-checked-results ((text (proof-write normal)))
    (b2-tactics-unproved)))

(defun b2-tactics-solve-split (n lib normal evidence unfold rules splits branches)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "b2-tactics-solve-split")
    (proof-with-checked-results ((known (b2-tactics-tactics-evidence lib evidence)))
      (let ((entry (assoc-equal normal known)))
        (if entry
            (cdr entry)
          (proof-with-checked-results ((conflict (b2-tactics-tactics-contradiction lib normal known)))
            (if conflict
                conflict
              (let ((proof (library-library-proof lib)))
                (proof-with-checked-results
                    ((reduction (b2-tactics-tactics-normalize lib normal evidence unfold rules 1500 branches))
                     (normal (if reduction (b2-tactics-step-result reduction) normal))
                     (step
                      (cond
                       ((and (proof-is-call normal *proof-quote*) (not (equal normal *proof-false*)))
                        (b2-tactics-tactics-prove-ground lib normal))
                       ((assoc-equal normal known) (cdr (assoc-equal normal known)))
                       (t
                        (proof-with-checked-results ((found (and (not (equal splits 0))
                                                                 (b2-tactics-first-test-found normal))))
                          (if (not found)
                              (b2-tactics-unresolved normal)
                            (proof-with-checked-results
                                ((test (car found))
                                 (affirm (proof-proof-assume proof test t))
                                 (yes (b2-tactics-solve-split (1- n) lib normal (append evidence (list affirm))
                                                            unfold rules (1- splits) branches))
                                 (deny (proof-proof-assume proof test nil))
                                 (no (b2-tactics-solve-split (1- n) lib normal (append evidence (list deny))
                                                           unfold rules (1- splits) branches)))
                              (proof-proof-cases proof test yes no))))))))
                  (if reduction (proof-proof-transport proof step reduction) step))))))))))

(defun b2-tactics-tactics-solve (lib goal evidence unfold rules splits branches)
  (b2-tactics-solve-split 1000000 lib goal evidence unfold rules
                         (if (eq splits t) 1 (ifix splits)) branches))

(defun b2-tactics-use-fact-premise (side evidence)
  (if (endp evidence)
      nil
    (proof-with-checked-results ((step (car evidence)) (first (proof-step-first step)))
      (if (or (equal (proof-neg first) side) (equal (proof-neg side) first))
          step
        (b2-tactics-use-fact-premise side (cdr evidence))))))

(defun b2-tactics-use-fact-discharge (proof sides evidence step)
  (if (endp sides)
      step
    (proof-with-checked-results
        ((premise (b2-tactics-use-fact-premise (car sides) evidence)))
      (if (not premise)
          (b2-tactics-unproved)
        (proof-with-checked-results ((step (proof-proof-discharge proof step premise)))
          (b2-tactics-use-fact-discharge proof (cdr sides) evidence step))))))

(defun b2-tactics-tactics-use-fact (lib name target evidence unfold rules splits branches)
  (let* ((proof (library-library-proof lib))
         (entry (assoc-equal name (proof-proof-facts proof))))
    (cond
     ((not entry) '(:failure "tactic-rejected" ""))
     ((endp (cdr entry)) '(:failure "inapplicable" ""))
     (t
      (let* ((formula (cadr entry))
             (implication (proof-is-call formula *library-implies*)))
        (proof-with-checked-results
            ((consequent (if implication (proof-term-at formula 2) formula))
             (step (b2-tactics-tactics-exact lib name consequent target))
             (step (b2-tactics-use-fact-discharge proof (cdr (proof-step-clause step)) evidence step)))
          (if (not implication)
              step
            (proof-with-checked-results
                ((first (proof-step-first step))
                 (antecedent (proof-term-at first 1))
                 (premise (b2-tactics-tactics-solve lib antecedent evidence unfold rules splits branches)))
              (proof-proof-modus-ponens proof step premise)))))))))

(defun b2-tactics-callback (lib reply kind arguments)
  (if reply reply (cons (list* :call kind lib arguments) lib)))

(defun b2-tactics-callback-pending-p (result)
  (or (failure-p (car result)) (eq (caar result) :call)))

(defun b2-tactics-choose-known (lib test evidence prove)
  (proof-with-checked-results ((known (b2-tactics-tactics-evidence lib evidence)))
    (let* ((positive (assoc-equal test known))
           (negative (and (not positive) (assoc-equal (proof-neg test) known))))
      (if (or positive negative)
          (b2-tactics-callback lib (car prove) :choose
                               (list (and positive t) (append evidence (list (cdr (or positive negative))))))
        (proof-with-checked-results
            ((affirm (proof-proof-assume (library-library-proof lib) test t))
             (yes (b2-tactics-callback lib (car prove) :choose (list t (append evidence (list affirm))))))
          (if (b2-tactics-callback-pending-p yes)
              yes
            (let* ((lib (cdr yes))
                   (proof (library-library-proof lib)))
              (proof-with-checked-results
                  ((deny (proof-proof-assume proof test nil))
                   (no (b2-tactics-callback lib (cadr prove) :choose (list nil (append evidence (list deny))))))
                (if (b2-tactics-callback-pending-p no)
                    no
                  (let ((lib (cdr no)))
                    (proof-with-checked-results
                        ((step (proof-proof-cases (library-library-proof lib) test (car yes) (car no))))
                      (cons step lib))))))))))))

(defun b2-tactics-choose (lib test evidence prove)
  (if (not (proof-is-call test *proof-equal*))
      (b2-tactics-choose-known lib test evidence prove)
    (proof-with-checked-results ((left (proof-term-at test 1)) (right (proof-term-at test 2)))
      (if (not (equal left right))
          (b2-tactics-choose-known lib test evidence prove)
        (proof-with-checked-results ((step (proof-proof-reflexive (library-library-proof lib) left)))
          (b2-tactics-callback lib (car prove) :choose (list t (append evidence (list step)))))))))

(defun b2-tactics-tactics-implication (lib antecedent consequent prove)
  (proof-with-checked-results
      ((positive (proof-proof-assume (library-library-proof lib) antecedent t))
       (outcome (b2-tactics-callback lib prove :implication (list positive))))
    (if (b2-tactics-callback-pending-p outcome)
        outcome
      (let* ((lib (cdr outcome))
             (proof (library-library-proof lib))
             (outcome (car outcome)))
        (proof-with-checked-results ((first (proof-step-first outcome)))
          (if (not (equal first consequent))
              '(:failure "tactic-rejected" "")
            (let ((formula (list *library-implies* antecedent consequent)))
              (proof-with-checked-results
                  ((opened (proof-proof-unfold proof formula))
                   (body (b2-tactics-step-result opened))
                   (if-true (proof-proof-if-true proof body))
                   (yes (proof-proof-chain proof opened (list if-true)))
                   (yes-body (b2-tactics-step-result yes))
                   (selected (proof-proof-select proof yes-body outcome))
                   (yes (proof-proof-chain proof yes (list selected)))
                   (if-false (proof-proof-if-false proof body))
                   (no (proof-proof-chain proof opened (list if-false)))
                   (yes (proof-proof-true-from-eq proof yes))
                   (no (proof-proof-true-from-eq proof no))
                   (step (proof-proof-cases proof antecedent yes no)))
                (cons step lib)))))))))

(defun b2-tactics-induction-bindings (pairs bindings)
  (if (endp pairs)
      bindings
    (proof-with-checked-results ((pair (proof-list-of-length (car pairs) 2)))
      (b2-tactics-induction-bindings (cdr pairs)
                                     (table-put bindings (car pair) (cadr pair))))))

(defun b2-tactics-tactics-induction-hypothesis (lib formula measure bindings smaller)
  (declare (ignore measure))
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((bindings (b2-tactics-induction-bindings bindings nil))
         (test (proof-step-first smaller))
         (body (proof-subst formula bindings))
         (conditional (proof-ite test body *proof-true*))
         (assumed (proof-proof-assume proof conditional t)))
      (proof-proof-prove-if proof assumed smaller))))

(defun b2-tactics-tactics-by-induction (lib formula variable test smaller bindings base advance advances-when)
  (let ((measure (list *library-count* variable)))
    (proof-with-checked-results
        ((hypothesis (b2-tactics-tactics-induction-hypothesis lib formula measure bindings smaller))
         (signed (proof-proof-assume (library-library-proof lib) test advances-when))
         (step (b2-tactics-callback lib advance :advance (list signed hypothesis))))
      (if (b2-tactics-callback-pending-p step)
          step
        (let ((lib (cdr step)))
          (proof-with-checked-results
              ((signed (proof-proof-assume (library-library-proof lib) test (not advances-when)))
               (stop (b2-tactics-callback lib base :base (list signed))))
            (if (b2-tactics-callback-pending-p stop)
                stop
              (let* ((lib (cdr stop))
                     (proof (library-library-proof lib))
                     (yes (if advances-when (car step) (car stop)))
                     (no (if advances-when (car stop) (car step))))
                (proof-with-checked-results
                    ((ordinal (library-library-builtin lib 1 variable))
                     (case-step (proof-proof-cases proof test yes no))
                     (result (proof-proof-induct proof ordinal case-step formula measure (list bindings))))
                  (cons result lib))))))))))

(defun b2-tactics-tactics-on-list (lib formula variable base advance extra)
  (proof-with-checked-results ((smaller (library-library-builtin lib 3 variable)))
    (b2-tactics-tactics-by-induction lib formula variable (list *proof-consp* variable) smaller
                                    (cons (list variable (list *library-cdr* variable)) extra) base advance t)))

; Arithmetic normalization uses the B2 constant evaluator.
(defun b2-tactics-push-minus-rule (lib argument evidence)
  (let ((facts (proof-proof-facts (library-library-proof lib))))
    (cond
     ((and (proof-is-call argument *proof-minus*)
           (assoc-equal (proof-sym "SELF-DOUBLE-NEGATION" "ACL2") facts))
      (proof-with-checked-results ((term (proof-term-at argument 1))
                                   (typed (library-library-type-of lib term evidence)))
        (library-library-cite lib "DOUBLE-NEGATION" (list term) (list typed))))
     ((and (proof-is-call argument *proof-plus*)
           (assoc-equal (proof-sym "SELF-NEGATE-SUM" "ACL2") facts))
      (proof-with-checked-results ((typed (library-type-arguments lib (cdr argument) evidence)))
        (library-library-cite lib "NEGATE-SUM" (cdr argument) typed)))
     (t nil))))

(defun b2-tactics-push-minus (n lib term evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "b2-tactics-push-minus")
    (let ((proof (library-library-proof lib)))
      (cond
       ((proof-is-call term *proof-plus*)
        (proof-with-checked-results
            ((step (proof-proof-reflexive proof term))
             (left (proof-term-at term 1))
             (left (b2-tactics-push-minus (1- n) lib left evidence))
             (step (if left (proof-proof-rewrite proof step left '(1 2 1)) step))
             (right (proof-term-at term 2))
             (right (b2-tactics-push-minus (1- n) lib right evidence))
             (step (if right (proof-proof-rewrite proof step right '(1 2 2)) step))
             (value (b2-tactics-step-result step)))
          (if (equal value term) nil step)))
       ((proof-is-call term *proof-minus*)
        (proof-with-checked-results ((argument (proof-term-at term 1)))
          (if (proof-is-call argument *proof-quote*)
              (b2-tactics-tactics-constant lib term)
            (proof-with-checked-results ((step (b2-tactics-push-minus-rule lib argument evidence)))
              (if (not step)
                  nil
                (proof-with-checked-results
                    ((value (b2-tactics-step-result step))
                     (rest (b2-tactics-push-minus (1- n) lib value evidence)))
                  (proof-proof-chain proof step (list rest))))))))
       (t nil)))))

(defun b2-tactics-linear-combine (n lib step place evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "b2-tactics-linear-combine")
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results ((first (proof-step-first step))
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
                      ((step (library-linear-remove-zero lib step "ADD-ZERO-LEFT" rest place evidence)))
                    (b2-tactics-linear-combine (1- n) lib step place evidence)))
                 ((and (equal b *proof-zero*) (not suffix))
                  (proof-with-checked-results
                      ((step (library-linear-remove-zero lib step "ADD-ZERO-RIGHT" a place evidence)))
                    (b2-tactics-linear-combine (1- n) lib step place evidence)))
                 (t
                  (proof-with-checked-results
                      ((combine (if (and (proof-is-call a *proof-quote*) (proof-is-call b *proof-quote*))
                                    (b2-tactics-tactics-constant lib (library-plus a b))
                                  (library-linear-combine-pair lib a b))))
                    (if (not combine)
                        (b2-tactics-linear-combine (1- n) lib step (append place '(2)) evidence)
                      (proof-with-checked-results
                          ((step (if suffix
                                     (proof-with-checked-results
                                         ((tail (proof-term-at rest 2))
                                          (assoc-step (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list a b tail)))
                                          (symmetric (proof-proof-symmetric proof assoc-step)))
                                       (proof-proof-rewrite proof step symmetric place))
                                   step))
                           (step (proof-proof-rewrite proof step combine
                                                      (if suffix (append place '(1)) place))))
                        (b2-tactics-linear-combine (1- n) lib step '(1 2) evidence))))))))))))))

(defun b2-tactics-base-linear-form (lib term evidence)
  (proof-with-checked-results
      ((step (b2-tactics-push-minus 1000000 lib term evidence))
       (step (or step (proof-proof-reflexive (library-library-proof lib) term)))
       (step (library-linear-reassociate 1000000 lib step '(1 2)))
       (step (library-linear-sort 1000000 lib step '(1 2) nil)))
    (b2-tactics-linear-combine 1000000 lib step '(1 2) evidence)))

(defun b2-tactics-linear-changed-p (step)
  (proof-with-checked-results ((first (proof-step-first step))
                               (left (proof-term-at first 1))
                               (right (proof-term-at first 2)))
    (not (equal left right))))

(defun b2-tactics-linear-repeat (n lib step evidence)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "b2-tactics-linear-repeat")
    (proof-with-checked-results ((changed (b2-tactics-linear-changed-p step)))
      (if (not changed)
          step
        (proof-with-checked-results ((term (b2-tactics-step-result step))
                                     (next (b2-tactics-base-linear-form lib term evidence))
                                     (changed (b2-tactics-linear-changed-p next)))
          (if (not changed)
              step
            (proof-with-checked-results
                ((step (proof-proof-chain (library-library-proof lib) step (list next))))
              (b2-tactics-linear-repeat (1- n) lib step evidence))))))))

(defun b2-tactics-tactics-linear-form (lib term evidence)
  (proof-with-checked-results ((step (b2-tactics-base-linear-form lib term evidence)))
    (b2-tactics-linear-repeat 1000000 lib step evidence)))

(defun b2-tactics-tactics-linear-equal (lib left right integers)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((left (b2-tactics-tactics-linear-form lib left integers))
                                 (right (b2-tactics-tactics-linear-form lib right integers))
                                 (a (b2-tactics-step-result left))
                                 (b (b2-tactics-step-result right)))
      (if (equal a b)
          (proof-with-checked-results ((right (proof-proof-symmetric proof right)))
            (proof-proof-chain proof left (list right)))
        (proof-with-checked-results ((a (proof-write a)) (b (proof-write b)))
          '(:failure "inapplicable" ""))))))

(defun b2-tactics-tactics-less-from-difference (lib a b positive-difference integers)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((compare (library-library-comparison lib a b integers))
         (value (b2-tactics-step-result positive-difference))
         (delta (b2-tactics-tactics-linear-equal lib (library-diff b a) value integers))
         (compare (proof-proof-rewrite proof compare delta '(1 2 2))))
      (proof-proof-transport proof positive-difference compare))))

(defun b2-tactics-tactics-weak-from-difference (lib a b nonnegative-difference integers)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((compare (library-library-axiom lib "<-ON-OTHERS" (list b a)))
         (first (proof-step-first nonnegative-difference))
         (bound (proof-term-at first 1))
         (value (proof-term-at bound 1))
         (delta (b2-tactics-tactics-linear-equal lib (library-diff b a) value integers))
         (compare (proof-proof-rewrite proof compare delta '(1 2 1))))
      (library-library-transport-argument lib nonnegative-difference compare 1))))

; Admit recipes that call the tactic functions in this book.
(b2-arithmetic-declare-events)
(b2-butlast-declare-events)
(b2-products-declare-events)
(b2-records-declare-events)
(b2-reversal-declare-events)
(b2-sorting-declare-events)
(b2-strict-order-declare-events)
