(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-tactics-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *h1-tactics-return-last* (proof-sym "RETURN-LAST" "ACL2"))
(defconst *h1-tactics-symbolp* (proof-cl "SYMBOLP"))
(defconst *h1-tactics-stringp* (proof-cl "STRINGP"))
(defconst *h1-tactics-characterp* (proof-cl "CHARACTERP"))
(defconst *h1-tactics-translation*
  (list *library-implies* *proof-not* *h1-tactics-return-last*
        (proof-sym "CONS-WITH-HINT" "ACL2")
        (proof-cl "=") (proof-cl "ATOM") (proof-cl "ENDP")
        (proof-cl "EQ") (proof-cl "EQL") (proof-cl "NULL")))

(defmacro h1-tactics-fuel-exhausted-p (n)
  `(not (o< (nfix (1- ,n)) (nfix ,n))))

(defmacro h1-tactics-list-finished-p (items)
  `(or (endp ,items)
       (not (o< (acl2-count (cdr ,items)) (acl2-count ,items)))))

(defun h1-tactics-call-head (term)
  (if (and (consp term) (proof-compound term))
      (car term)
    :none))

(defun h1-tactics-head-truthy-p (term)
  (let ((head (h1-tactics-call-head term)))
    (and (not (eq head :none)) head (not (equal head 0)) (not (equal head "")))))

(mutual-recursion
 (defun h1-tactics-variable-occurrences (term)
   (let ((head (h1-tactics-call-head term)))
     (cond ((equal head *proof-quote*) nil)
           ((eq head :none) (list term))
           (t (h1-tactics-argument-variables (cdr term))))))
 (defun h1-tactics-argument-variables (terms)
   (if (endp terms)
       nil
     (append (h1-tactics-variable-occurrences (car terms))
             (h1-tactics-argument-variables (cdr terms))))))

(mutual-recursion
 (defun h1-tactics-variable-text (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((stringp term)
          (concatenate 'string "\""
                       (text-replace (text-replace term "\\" "\\\\") "\"" "\\\"")
                       "\""))
         ((integerp term) (decimal-text term))
         ((rationalp term)
          (concatenate 'string (decimal-text (numerator term)) "/"
                       (decimal-text (denominator term))))
         ((eq term t) "t")
         ((consp term)
          (concatenate 'string "("
                       (text-join " " (cons (h1-tactics-variable-text (car term))
                                         (h1-tactics-variable-texts (cdr term))))
                       ")"))
         (t "()")))
 (defun h1-tactics-variable-texts (terms)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (cons (h1-tactics-variable-text (car terms))
           (h1-tactics-variable-texts (cdr terms))))))

(defun h1-tactics-ordered-set-keys (terms)
  (if (endp terms)
      nil
    (cons (list (h1-tactics-variable-text (car terms)) (car terms))
          (h1-tactics-ordered-set-keys (cdr terms)))))

(defun h1-tactics-ordered-set-values (keys)
  (if (endp keys)
      nil
    (cons (cadar keys) (h1-tactics-ordered-set-values (cdr keys)))))

(defun h1-tactics-ordered-set (terms)
  (h1-tactics-ordered-set-values
   (seq-sorted (h1-tactics-ordered-set-keys (proof-unique terms)))))

(defun h1-tactics-variables (term)
  (h1-tactics-ordered-set (h1-tactics-variable-occurrences term)))

(mutual-recursion
 (defun h1-tactics-subterms (term)
   (declare (xargs :measure (acl2-count term)))
   (if (and (consp term) (proof-compound term) (not (equal (car term) *proof-quote*)))
       (cons term (h1-tactics-argument-subterms (cdr term)))
     (list term)))
 (defun h1-tactics-argument-subterms (terms)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (append (h1-tactics-subterms (car terms))
             (h1-tactics-argument-subterms (cdr terms))))))

(defun h1-tactics-table-put-if-absent (table key value)
  (if (assoc-equal key table)
      table
    (table-put table key value)))

(mutual-recursion
 (defun h1-tactics-match (pattern term free bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (if (member-equal pattern free)
       (let ((prior (assoc-equal pattern bindings)))
         (if prior
             (cons (equal (cdr prior) term) bindings)
           (cons t (table-put bindings pattern term))))
     (let ((head (h1-tactics-call-head pattern)))
       (cond ((or (eq head :none) (equal head *proof-quote*))
              (cons (equal pattern term) bindings))
             ((and (equal (h1-tactics-call-head term) head)
                   (equal (len pattern) (len term)))
              (h1-tactics-match-arguments (cdr pattern) (cdr term) free bindings))
             (t (cons nil bindings))))))
 (defun h1-tactics-match-arguments (patterns terms free bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (endp patterns)
       (cons t bindings)
     (let ((matched (h1-tactics-match (car patterns) (car terms) free bindings)))
       (if (car matched)
           (h1-tactics-match-arguments (cdr patterns) (cdr terms) free (cdr matched))
         matched)))))

(defun h1-tactics-make-rule (step free)
  (list :h1-rule step free))

(defun h1-tactics-rule-step (rule)
  (cadr rule))

(defun h1-tactics-rule-free (rule)
  (caddr rule))

(defun h1-tactics-make-rules (library claims rewrites)
  (list :h1-rules library claims rewrites))

(defun h1-tactics-rules-library (rules)
  (cadr rules))

(defun h1-tactics-rules-claims (rules)
  (caddr rules))

(defun h1-tactics-rules-rewrites (rules)
  (cadddr rules))

(defun h1-tactics-rules-with-library (rules library)
  (update-nth 1 library rules))

(defun h1-tactics-make-prover (library rules theorems schemas search-work case-limit)
  (list :h1-prover library rules theorems schemas search-work case-limit))

(defun h1-tactics-prover-library (prover)
  (cadr prover))

(defun h1-tactics-prover-proof (prover)
  (library-library-proof (h1-tactics-prover-library prover)))

(defun h1-tactics-prover-rules (prover)
  (h1-tactics-rules-with-library (caddr prover) (h1-tactics-prover-library prover)))

(defun h1-tactics-prover-theorems (prover)
  (cadddr prover))

(defun h1-tactics-prover-schemas (prover)
  (nth 4 prover))

(defun h1-tactics-prover-search-work (prover)
  (nth 5 prover))

(defun h1-tactics-prover-case-limit (prover)
  (nth 6 prover))

(defun h1-tactics-prover-available (prover)
  (nth 7 prover))

(defun h1-tactics-prover-evaluators (prover)
  (nth 8 prover))

(defun h1-tactics-prover-with-library (prover library)
  (update-nth 1 library
              (update-nth 2 (h1-tactics-rules-with-library (caddr prover) library)
                          prover)))

(defun h1-tactics-prover-with-rules (prover rules)
  (update-nth 2
              (h1-tactics-rules-with-library rules (h1-tactics-prover-library prover))
              prover))

(defun h1-tactics-prover-with-theorems (prover theorems)
  (update-nth 3 theorems prover))

(defun h1-tactics-prover-with-schemas (prover schemas)
  (update-nth 4 schemas prover))

(defun h1-tactics-prover-with-search-work (prover work)
  (update-nth 5 work prover))

(defun h1-tactics-prover-with-case-limit (prover limit)
  (update-nth 6 limit prover))

(defun h1-tactics-prover-with-available (prover available)
  (update-nth 7 available prover))

(defun h1-tactics-prover-with-evaluators (prover evaluators)
  (update-nth 8 evaluators prover))

(defun h1-tactics-prover-add-definition (prover name formals body)
  (let* ((library (h1-tactics-prover-library prover))
         (proof (proof-proof-add-definition (h1-tactics-prover-proof prover)
                                            name formals body))
         (updated (h1-tactics-prover-with-library
                   prover (library-library-with-proof library proof)))
         (available (h1-tactics-prover-available updated)))
    (if (or (eq (h1-tactics-prover-case-limit prover) :none)
            (member-equal name available))
        updated
      (h1-tactics-prover-with-available updated (append available (list name))))))

(defun h1-tactics-rules-init (prover)
  (h1-tactics-make-rules (h1-tactics-prover-library prover) nil nil))

(defun h1-tactics-prover-init ()
  (proof-with-checked-results
      ((library (h1-propositions-propositional-proof-setup-propositions
                 (library-library-init (proof-proof-init)))))
    (h1-tactics-make-prover library (h1-tactics-make-rules library nil nil)
                           nil nil :none :none)))

(defun h1-tactics-step-at (step index)
  (proof-with-checked-results ((first (proof-step-first step)))
    (proof-term-at first index)))

(defun h1-tactics-index-append (index head pattern rule)
  (table-put index head
               (append (table-get index head nil) (list (list pattern rule)))))

(defun h1-tactics-rules-add (rules step general rewrite)
  (let* ((free (and general
                    (h1-tactics-ordered-set
                     (h1-tactics-argument-variables (proof-step-clause step)))))
         (rule (h1-tactics-make-rule step free)))
    (proof-with-checked-results
        ((first (proof-step-first step)))
      (let* ((claims (h1-tactics-index-append
                      (h1-tactics-rules-claims rules)
                      (h1-tactics-call-head first) first rule))
             (rewrites (h1-tactics-rules-rewrites rules))
             (library (h1-tactics-rules-library rules)))
        (if (and rewrite (proof-is-call first *proof-equal*))
            (proof-with-checked-results ((parts (proof-list-of-length first 3)))
              (let* ((left (cadr parts))
                     (right (caddr parts))
                     (head (h1-tactics-call-head left)))
                (h1-tactics-make-rules
                 library claims
                 (if (and (not (eq head :none))
                          (not (equal head *proof-quote*))
                          (subsetp-equal (h1-tactics-variable-occurrences right)
                                         (h1-tactics-variable-occurrences left)))
                     (h1-tactics-index-append rewrites head left rule)
                   rewrites))))
          (h1-tactics-make-rules library claims rewrites))))))

(defund h1-tactics-assume-conjunct (proof term)
  (h1-arithmetic-proof-assume proof term t))

(defun h1-tactics-conjunction-assumption (library term)
  (declare (xargs :measure (acl2-count term)))
  (let ((proof (library-library-proof library)))
    (cond ((not (and (consp term) (equal (car term) *proof-if*)))
           (h1-arithmetic-proof-assume proof term t))
          ((not (consp (cdddr term))) (proof-term-at term 3))
          ((not (equal (cadddr term) *proof-false*)) (h1-arithmetic-proof-assume proof term t))
          (t (proof-with-checked-results
                 ((left (h1-tactics-assume-conjunct proof (cadr term)))
                  (right (h1-tactics-conjunction-assumption library (caddr term))))
               (h1-propositions-propositional-proof-conjoin library term left right))))))

(defun h1-tactics-prover-conjunction-assumption (prover term)
  (h1-tactics-conjunction-assumption (h1-tactics-prover-library prover) term))

(defund h1-tactics-rules-add-formula-step (rules step general rewrite)
  (let* ((library (h1-tactics-rules-library rules))
         (proof (library-library-proof library)))
    (proof-with-checked-results ((first (proof-step-first step)))
      (if (proof-is-call first *library-implies*)
          (proof-with-checked-results ((premise (proof-term-at first 1)))
            (if (member-equal premise (cdr (proof-step-clause step)))
                rules
              (proof-with-checked-results
                  ((evidence (h1-tactics-conjunction-assumption library premise))
                   (next (h1-propositions-propositional-proof-modus-ponens
                          library step evidence)))
                (list :consequent next))))
        (proof-with-checked-results
            ((added (h1-tactics-rules-add rules step general rewrite))
             (no (if (proof-is-call first *proof-if*) (proof-term-at first 3) :none)))
          (cond ((equal no *proof-false*)
                 (proof-with-checked-results
                     ((conjuncts (h1-propositions-propositional-proof-conjunct library step)))
                   (list :conjuncts added (car conjuncts) (cadr conjuncts))))
                ((and (not (eq no :none)) (equal (cadr first) (caddr first)))
                 (proof-with-checked-results
                     ((on-false (h1-arithmetic-proof-if-false proof first))
                      (rewritten (proof-proof-rewrite proof step on-false '(1)))
                      (fallback (proof-proof-tidy proof rewritten)))
                   (h1-tactics-rules-add added fallback general rewrite)))
                (t added)))))))

(defun h1-tactics-rules-add-formula-loop (n rules step general rewrite)
  (declare (xargs :measure (nfix n)))
  (if (h1-tactics-fuel-exhausted-p n)
      '(:failure "Fuel" "h1-tactics-rules-add-formula-loop")
    (let ((result (h1-tactics-rules-add-formula-step rules step general rewrite)))
      (case (car result)
        (:consequent
         (h1-tactics-rules-add-formula-loop (1- n) rules (cadr result) general rewrite))
        (:conjuncts
         (proof-with-checked-results
             ((left (h1-tactics-rules-add-formula-loop
                     (1- n) (cadr result) (caddr result) general rewrite)))
           (h1-tactics-rules-add-formula-loop (1- n) left (cadddr result) general rewrite)))
        (otherwise result)))))

(defun h1-tactics-rules-add-formula (rules step general rewrite)
  (h1-tactics-rules-add-formula-loop 1000000 rules step general rewrite))

(defun h1-tactics-fact-key (term)
  (let ((head (h1-tactics-call-head term)))
    (proof-with-checked-results
        ((argument (cond ((member-equal head (list *proof-equal* *proof-not*))
                          (proof-term-at term 1))
                         ((equal head *library-implies*) (proof-term-at term 2))
                         (t :none))))
      (list head (if (eq argument :none) :none (h1-tactics-call-head argument))))))

(defun h1-tactics-prior-schema (proof term schemas)
  (if (endp schemas)
      nil
    (let* ((schema (car schemas))
           (matched (h1-tactics-match (cadr schema) term (caddr schema) nil)))
      (if (car matched)
          (proof-proof-fact proof (car schema) (table-items (cdr matched)))
        (h1-tactics-prior-schema proof term (cdr schemas))))))

(defun h1-tactics-prover-prior-fact (prover term)
  (let ((name (table-get (h1-tactics-prover-theorems prover) term nil))
        (proof (h1-tactics-prover-proof prover)))
    (cond (name (proof-proof-fact proof name nil))
          ((eq (h1-tactics-prover-case-limit prover) :none) nil)
          (t
           (proof-with-checked-results ((key (h1-tactics-fact-key term)))
             (let* ((schemas (h1-tactics-prover-schemas prover))
                    (matches (table-get schemas key nil)))
               (proof-with-checked-results
                   ((first (h1-tactics-prior-schema proof term matches)))
                 (if (or first (eq (cadr key) :none))
                     first
                   (h1-tactics-prior-schema
                    proof term (table-get schemas (list (car key) :none) nil))))))))))

(defun h1-tactics-prover-quoted-truth (prover term)
  (if (not (and (proof-is-call term *proof-quote*) (not (equal term *proof-false*))))
      '(:failure "failure" "")
    (let ((proof (h1-tactics-prover-proof prover)))
      (proof-with-checked-results
          ((nil-or-true (proof-proof-nil-or-true proof term))
           (computed (proof-proof-compute proof (proof-eq term *proof-false*) *proof-nil*))
           (rewritten (proof-proof-rewrite proof nil-or-true computed '(1))))
        (proof-proof-tidy proof rewritten)))))

(defun h1-tactics-prover-false-equation (prover evidence)
  (if (not evidence)
      nil
    (let ((proof (h1-tactics-prover-proof prover)))
      (proof-with-checked-results
          ((term (h1-tactics-step-at evidence 1))
           (nil-or-true (proof-proof-nil-or-true proof term)))
        (proof-proof-discharge proof nil-or-true evidence)))))

(defun h1-tactics-prover-equality-is-true (prover evidence)
  (let ((proof (h1-tactics-prover-proof prover)))
    (proof-with-checked-results
        ((right (h1-tactics-step-at evidence 2))
         (same (proof-proof-fact proof "equal-same" (list (list *library-x* right))))
         (reversed (h1-propositions-proof-symmetric proof evidence))
         (rewritten (proof-proof-rewrite proof same reversed '(1 1 1))))
      (proof-proof-tidy proof rewritten))))

(defun h1-tactics-constant-list-value (head datum)
  (cond ((not (proof-compound datum)) *proof-nil*)
        ((equal head *library-car*) (proof-term-at datum 0))
        ((endp (cdr datum)) *proof-nil*)
        ((and (equal (len datum) 2)
              (consp (cadr datum))
              (equal (caadr datum) "dot"))
         (proof-term-at (cadr datum) 1))
        (t (cdr datum))))

(defun h1-tactics-constant-extra (proof term)
  (let* ((head (car term))
         (args (cdr term))
         (realpart (proof-cl "REALPART"))
         (imagpart (proof-cl "IMAGPART")))
    (if (and (proof-all-quoted-p args)
             (member-equal head (list *h1-tactics-symbolp* *h1-tactics-characterp*
                                      *library-car* *library-cdr* realpart imagpart)))
        (proof-with-checked-results
            ((arg (if (consp args) (car args) (proof-list-index-error)))
             (datum (proof-term-at arg 1)))
          (cond ((member-equal head (list *h1-tactics-symbolp* *h1-tactics-characterp*))
                 (let ((category (if (equal head *h1-tactics-symbolp*) "sym" "char")))
                   (if (null datum)
                       (proof-term-at datum 0)
                     (proof-proof-compute proof term
                                          (if (and (consp datum)
                                                   (equal (car datum) category))
                                              *proof-t* *proof-nil*)))))
                ((member-equal head (list *library-car* *library-cdr*))
                 (proof-with-checked-results
                     ((value (h1-tactics-constant-list-value head datum)))
                   (proof-proof-compute proof term value)))
                ((or (integerp datum) (eq datum t))
                 (proof-proof-compute proof term (if (equal head realpart) datum 0)))
                (t nil)))
      nil)))

(defun h1-tactics-ratio-value (top bottom)
  (let ((numerator-value (if (eq top t) 1 top))
        (denominator-value (if (eq bottom t) 1 bottom)))
    (cond ((not (and (rationalp numerator-value) (rationalp denominator-value)))
           '(:failure "failure" ""))
          ((equal denominator-value 0) '(:failure "failure" ""))
          (t (/ numerator-value denominator-value)))))

(defun h1-tactics-rational-constant (term)
  (if (not (proof-is-call term *proof-quote*))
      nil
    (proof-with-checked-results ((value (proof-term-at term 1)))
      (cond ((integerp value) value)
            ((eq value t) 1)
            ((null value) (proof-term-at value 0))
            ((and (consp value) (equal (car value) "ratio"))
             (proof-with-checked-results
                 ((numerator (proof-term-at value 1))
                  (denominator (proof-term-at value 2)))
               (h1-tactics-ratio-value numerator denominator)))
            (t nil)))))

(defun h1-tactics-rational-arguments (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((value (h1-tactics-rational-constant (car terms)))
         (rest (h1-tactics-rational-arguments (cdr terms))))
      (cons value rest))))

(defun h1-tactics-rational-datum (value)
  (if (integerp value)
      value
    (list "ratio" (numerator value) (denominator value))))

(defun h1-tactics-compute-rational (prover term)
  (let* ((head (h1-tactics-call-head term))
         (reciprocal (proof-sym "UNARY-/" "ACL2"))
         (proof (h1-tactics-prover-proof prover)))
    (if (member-equal head (list *library-numberp* *proof-plus* *proof-times*
                                 *proof-minus* reciprocal *proof-less*))
        (proof-with-checked-results ((args (h1-tactics-rational-arguments (cdr term))))
          (if (member-equal nil args)
              nil
            (proof-with-checked-results ((left (proof-term-at args 0)))
              (cond ((equal head *library-numberp*) (proof-proof-compute proof term *proof-t*))
                    ((equal head *proof-minus*)
                     (proof-proof-compute proof term (h1-tactics-rational-datum (- left))))
                    ((equal head reciprocal)
                     (proof-proof-compute proof term
                                          (h1-tactics-rational-datum
                                           (if (equal left 0) 0 (/ left)))))
                    (t
                     (proof-with-checked-results ((right (proof-term-at args 1)))
                       (proof-proof-compute
                        proof term
                        (cond ((equal head *proof-less*)
                               (if (< left right) *proof-t* *proof-nil*))
                              ((equal head *proof-plus*)
                               (h1-tactics-rational-datum (+ left right)))
                              (t (h1-tactics-rational-datum (* left right)))))))))))
      nil)))

(defun h1-tactics-prover-constant (prover term)
  (let ((proof (h1-tactics-prover-proof prover)))
    (proof-with-checked-results
        ((base (proof-proof-constant-base proof term))
         (extra (if base base (h1-tactics-constant-extra proof term))))
      (if (or extra (eq (h1-tactics-prover-case-limit prover) :none))
          extra
        (h1-tactics-compute-rational prover term)))))

(defun h1-tactics-add-named-formulas (names rules acl2-names)
  (if (endp names)
      rules
    (let* ((library (h1-tactics-rules-library rules))
           (proof (library-library-proof library))
           (name (if acl2-names (proof-sym (car names) "ACL2") (car names))))
      (proof-with-checked-results
          ((step (proof-proof-fact proof name nil))
           (next (h1-tactics-rules-add-formula rules step t t)))
        (h1-tactics-add-named-formulas (cdr names) next acl2-names)))))

(defun h1-tactics-add-type-exclusions (names rules)
  (if (endp names)
      rules
    (let* ((library (h1-tactics-rules-library rules))
           (proof (library-library-proof library)))
      (proof-with-checked-results
          ((step (proof-proof-fact proof (car names) nil))
           (premise (h1-tactics-step-at step 1))
           (assumed (h1-arithmetic-proof-assume proof premise t))
           (forward (h1-propositions-propositional-proof-modus-ponens
                     library step assumed))
           (rules (h1-tactics-rules-add rules forward t t))
           (reverse (proof-proof-front proof forward (proof-neg premise)))
           (next (h1-tactics-rules-add rules reverse t t)))
        (h1-tactics-add-type-exclusions (cdr names) next)))))

(defun h1-tactics-prover-setup-rules (prover)
  (proof-with-checked-results
      ((axioms (h1-tactics-add-named-formulas
                '("CAR-CONS" "CDR-CONS" "CAR-CDR-ELIM" "CONS-EQUAL" "INTEGER-0"
                  "INTEGER-1" "STRINGP-SYMBOL-PACKAGE-NAME" "CHARACTER-LISTP-COERCE"
                  "INTEGER-IMPLIES-RATIONAL" "REALPART-COMPLEX" "IMAGPART-COMPLEX")
                (h1-tactics-prover-rules prover) t))
       (types (h1-tactics-add-named-formulas
               '("consp-cons" "integerp-char-code" "stringp-coerce"
                 "stringp-symbol-name" "booleanp-<" "rationalp-acl2-numberp"
                 "complex-rationalp-acl2-numberp")
               axioms nil))
       (rules (h1-tactics-add-type-exclusions
               '("consp-not-acl2-numberp" "consp-not-characterp" "consp-not-stringp"
                 "consp-not-symbolp" "acl2-numberp-not-characterp"
                 "acl2-numberp-not-stringp" "acl2-numberp-not-symbolp"
                 "characterp-not-stringp" "characterp-not-symbolp"
                 "stringp-not-symbolp" "complex-rationalp-not-rationalp")
               types)))
    (h1-tactics-prover-with-rules prover rules)))

(defun h1-tactics-definition-heads (terms definitions)
  (if (endp terms)
      nil
    (let ((head (h1-tactics-call-head (car terms))))
      (if (and (assoc-equal head definitions)
               (not (member-equal head *h1-tactics-translation*)))
          (cons head (h1-tactics-definition-heads (cdr terms) definitions))
        (h1-tactics-definition-heads (cdr terms) definitions)))))

(defun h1-tactics-prover-functions-in (prover formula)
  (proof-unique
   (h1-tactics-definition-heads
    (h1-tactics-subterms formula)
    (proof-proof-definitions (h1-tactics-prover-proof prover)))))

(defun h1-tactics-prover-helper (prover name step guards rewrite)
  (let* ((name (proof-sym (concatenate 'string "H1-" name) "ACL2"))
         (library (h1-tactics-prover-library prover))
         (proof (h1-tactics-prover-proof prover))
         (facts (proof-proof-facts proof)))
    (if (assoc-equal name facts)
        (proof-with-checked-results ((fact (proof-proof-fact proof name nil)))
          (cons fact prover))
      (proof-with-checked-results
          ((literal (proof-step-first step))
           (clause (cons literal guards))
           (subsumed (proof-proof-subsume proof step clause))
           (entry (proof-proof-entry "lemma" name (cons name clause) (list subsumed)))
           (with-entry (library-library-with-entries
                        library (append (library-library-entries library) (list entry))))
           (with-fact (proof-proof-with-facts proof (table-put facts name clause)))
           (updated (h1-tactics-prover-with-library
                     prover (library-library-with-proof with-entry with-fact)))
           (fact (proof-proof-fact with-fact name nil))
           (rules (h1-tactics-rules-add-formula
                   (h1-tactics-prover-rules updated) fact t rewrite)))
        (cons fact (h1-tactics-prover-with-rules updated rules))))))

(defun h1-tactics-prover-record-formula (prover label step rewrite)
  (proof-with-checked-results
      ((formula (proof-step-first step))
       (updated
        (if rewrite
            (proof-with-checked-results
                ((helper (h1-tactics-prover-helper prover label step nil t)))
              (cdr helper))
          (proof-with-checked-results
              ((library (library-library-lemma
                         (h1-tactics-prover-library prover) label formula step nil)))
            (h1-tactics-prover-with-library prover library))))
       (name (proof-sym (concatenate 'string (if rewrite "H1-" "SELF-") label)
                        "ACL2"))
       (key (h1-tactics-fact-key formula)))
    (let* ((schemas (h1-tactics-prover-schemas updated))
           (noted
            (if (eq (car key) :none)
                updated
              (h1-tactics-prover-with-schemas
               updated
               (table-put schemas key
                            (append (table-get schemas key nil)
                                    (list (list name formula (h1-tactics-variables formula))))))))
           (theorems (h1-tactics-prover-theorems noted)))
      (proof-with-checked-results
          ((fact (proof-proof-fact (h1-tactics-prover-proof noted) name nil)))
        (cons fact (h1-tactics-prover-with-theorems
                    noted (h1-tactics-table-put-if-absent theorems formula name)))))))

(defun h1-tactics-openings-from-names (names bound table)
  (if (endp names)
      table
    (h1-tactics-openings-from-names (cdr names) bound
                                   (table-put table (car names) bound))))

(defconst *h1-tactics-default-openings*
  (h1-tactics-openings-from-names *h1-tactics-translation* 12 nil))

(defun h1-tactics-opening-map-p (openings)
  (and (consp openings) (consp (car openings))
       (not (stringp (caar openings)))))

(defun h1-tactics-opening-map (openings)
  (if (h1-tactics-opening-map-p openings)
      openings
    (h1-tactics-openings-from-names openings 1 nil)))

(defun h1-tactics-search-init (prover openings local ambient protected limit rewrite-equalities)
  (list :h1-search prover (or local (h1-tactics-rules-init prover))
        (h1-tactics-ordered-set ambient) (h1-tactics-ordered-set protected)
        rewrite-equalities
        (table-update *h1-tactics-default-openings*
                        (h1-tactics-opening-map openings))
        limit (h1-tactics-prover-search-work prover)))

(defun h1-tactics-search-prover (search)
  (cadr search))

(defun h1-tactics-search-library (search)
  (h1-tactics-prover-library (h1-tactics-search-prover search)))

(defun h1-tactics-search-local (search)
  (caddr search))

(defun h1-tactics-search-ambient (search)
  (cadddr search))

(defun h1-tactics-search-protected (search)
  (nth 4 search))

(defun h1-tactics-search-rewrite-equalities (search)
  (nth 5 search))

(defun h1-tactics-search-openings (search)
  (nth 6 search))

(defun h1-tactics-search-remaining (search)
  (nth 7 search))

(defun h1-tactics-search-work (search)
  (nth 8 search))

(defun h1-tactics-search-with-remaining (search remaining)
  (update-nth 7 remaining search))

(defun h1-tactics-search-with-work (search work)
  (update-nth 8 work search))

(defun h1-tactics-context-search (context)
  (cadr context))

(defun h1-tactics-context-tests (context)
  (caddr context))

(defun h1-tactics-context-evidence (context)
  (cadddr context))

(defun h1-tactics-context-bindings (context)
  (nth 4 context))

(defun h1-tactics-context-active (context)
  (nth 5 context))

(defun h1-tactics-context-guards (context)
  (nth 6 context))

(defun h1-tactics-context-with-search (context search)
  (update-nth 1 search context))

(defun h1-tactics-context-with-evidence (context evidence)
  (update-nth 3 evidence context))

(defun h1-tactics-context-with-bindings (context bindings)
  (update-nth 4 bindings context))

(defun h1-tactics-context-with-active (context active)
  (update-nth 5 active context))

(defun h1-tactics-context-with-guards (context guards)
  (update-nth 6 guards context))

(defun h1-tactics-context-prover (context)
  (h1-tactics-search-prover (h1-tactics-context-search context)))

(defun h1-tactics-context-library (context)
  (h1-tactics-prover-library (h1-tactics-context-prover context)))

(defun h1-tactics-context-proof (context)
  (h1-tactics-prover-proof (h1-tactics-context-prover context)))

(defun h1-tactics-context-remember (context term step)
  (h1-tactics-context-with-evidence
   context (table-put (h1-tactics-context-evidence context) term step)))

(defun h1-tactics-context-remember-first (context term step)
  (h1-tactics-context-with-evidence
   context (h1-tactics-table-put-if-absent (h1-tactics-context-evidence context) term step)))

(defun h1-tactics-context-bind-equality-key (term)
  (proof-with-checked-results ((text (proof-write term)))
    (list (not (proof-is-call term *proof-quote*)) (length text) text)))

(defun h1-tactics-equality-key-less (left right)
  (if (iff (car left) (car right))
      (value-less (cdr left) (cdr right))
    (not (car left))))

(defun h1-tactics-context-bind-equality (context step)
  (proof-with-checked-results ((first (proof-step-first step)))
    (if (not (proof-is-call first *proof-equal*))
        context
      (proof-with-checked-results ((parts (proof-list-of-length first 3)))
        (let* ((left (cadr parts))
               (right (caddr parts))
               (expressed (h1-tactics-search-rewrite-equalities
                           (h1-tactics-context-search context))))
          (proof-with-checked-results
              ((flip (if expressed
                         (proof-with-checked-results
                             ((left-key (h1-tactics-context-bind-equality-key left))
                              (right-key (h1-tactics-context-bind-equality-key right)))
                           (h1-tactics-equality-key-less left-key right-key))
                       (proof-is-call left *proof-quote*)))
               (binding (if flip
                            (h1-propositions-proof-symmetric (h1-tactics-context-proof context)
                                                             step)
                          step)))
            (let ((source (if flip right left))
                  (target (if flip left right)))
              (if (and (not (equal source target))
                       (not (proof-is-call source *proof-quote*))
                       (or expressed (proof-is-call target *proof-quote*)))
                  (h1-tactics-context-with-bindings
                   context (h1-tactics-table-put-if-absent
                            (h1-tactics-context-bindings context) source binding))
                context))))))))

(defun h1-tactics-context-init-conjuncts (n context part)
  (declare (xargs :measure (nfix n)))
  (if (h1-tactics-fuel-exhausted-p n)
      '(:failure "Fuel" "h1-tactics-context-init-conjuncts")
    (proof-with-checked-results
        ((term (proof-step-first part))
         (no (if (proof-is-call term *proof-if*) (proof-term-at term 3) :none)))
      (if (not (equal no *proof-false*))
          context
        (proof-with-checked-results
            ((conjuncts (h1-propositions-propositional-proof-conjunct
                         (h1-tactics-context-library context) part))
             (left (car conjuncts))
             (right (cadr conjuncts))
             (left-term (proof-step-first left))
             (first (h1-tactics-context-remember-first context left-term left))
             (right-term (proof-step-first right))
             (both (h1-tactics-context-remember-first first right-term right))
             (bound-left (h1-tactics-context-bind-equality both left))
             (bound-both (h1-tactics-context-bind-equality bound-left right)))
          (h1-tactics-context-init-conjuncts (1- n) bound-both right))))))

(defun h1-tactics-context-init-nil-test (context test holds step)
  (let ((proof (h1-tactics-context-proof context)))
    (proof-with-checked-results
        ((right (if (proof-is-call test *proof-equal*) (proof-term-at test 2) :none)))
      (if (not (equal right *proof-false*))
          context
        (proof-with-checked-results
            ((evidence
              (if holds
                  (proof-with-checked-results
                      ((not-nil (proof-proof-not-nil proof))
                       (reversed (h1-propositions-proof-symmetric proof step)))
                    (proof-proof-rewrite proof not-nil reversed '(1 1)))
                (proof-with-checked-results
                    ((nil-or-true (proof-proof-nil-or-true proof (cadr test))))
                  (proof-proof-cut proof nil-or-true step))))
             (term (proof-step-first evidence)))
          (h1-tactics-context-remember context term evidence))))))

(defund h1-tactics-context-init-test (context signed)
  (let ((proof (h1-tactics-context-proof context)))
    (proof-with-checked-results
        ((signed (proof-list-of-length signed 2))
         (test (car signed))
         (holds (cadr signed))
         (step (h1-arithmetic-proof-assume proof test holds))
         (literal (proof-step-first step))
         (recorded (h1-tactics-context-remember context literal step))
         (bound (if holds
                    (proof-with-checked-results
                        ((context (h1-tactics-context-bind-equality recorded step)))
                      (h1-tactics-context-init-conjuncts 1000000 context step))
                  recorded)))
      (h1-tactics-context-init-nil-test bound test holds step))))

(defun h1-tactics-context-init-tests (context tests)
  (declare (xargs :measure (acl2-count tests)))
  (if (or (failure-p context) (h1-tactics-list-finished-p tests))
      context
    (h1-tactics-context-init-tests (h1-tactics-context-init-test context (car tests))
                                   (cdr tests))))

(defun h1-tactics-context-init (search tests)
  (h1-tactics-context-init-tests (list :h1-context search tests nil nil nil nil) tests))

(defun h1-tactics-unbound-variable-p (variables free bindings)
  (if (endp variables)
      nil
    (or (and (member-equal (car variables) free)
             (not (assoc-equal (car variables) bindings)))
        (h1-tactics-unbound-variable-p (cdr variables) free bindings))))

(defun h1-tactics-unbound-literal-p (literals free bindings)
  (if (endp literals)
      nil
    (or (h1-tactics-unbound-variable-p
         (h1-tactics-variable-occurrences (car literals)) free bindings)
        (h1-tactics-unbound-literal-p (cdr literals) free bindings))))

(defun h1-tactics-index-for (rules index)
  (cond ((equal index "claims") (h1-tactics-rules-claims rules))
        ((equal index "rewrites") (h1-tactics-rules-rewrites rules))
        (t '(:failure "failure" ""))))

(defun h1-tactics-derive-constant (context term)
  (let ((prover (h1-tactics-context-prover context))
        (proof (h1-tactics-context-proof context))
        (library (h1-tactics-context-library context)))
    (if (proof-is-call term *proof-not*)
        (proof-with-checked-results ((argument (proof-term-at term 1)))
          (cond ((equal argument *proof-false*) (proof-proof-not-nil proof))
                ((h1-tactics-head-truthy-p argument)
                 (proof-with-checked-results
                     ((constant (h1-tactics-prover-constant prover argument))
                      (value (if constant (h1-tactics-step-at constant 2) :none)))
                   (if (equal value *proof-false*)
                       (proof-with-checked-results ((not-nil (proof-proof-not-nil proof)))
                         (h1-propositions-library-transport-argument library not-nil constant 1))
                     nil)))
                (t nil)))
      (if (h1-tactics-head-truthy-p term)
          (proof-with-checked-results
              ((constant (h1-tactics-prover-constant prover term))
               (value (if constant (h1-tactics-step-at constant 2) :none)))
            (if (equal value *proof-true*) (proof-proof-true-from-eq proof constant) nil))
        nil))))

(defun h1-tactics-reduction-current (step term)
  (if step (h1-tactics-step-at step 2) term))

(defun h1-tactics-tidy-reduction (context step tests)
  (proof-with-checked-results
      ((tidied (if step (proof-proof-tidy (h1-tactics-context-proof context) step) nil)))
    (list tidied context tests)))

(defun h1-tactics-rewrite-argument (context step term equality place)
  (let ((proof (h1-tactics-context-proof context))
        (library (h1-tactics-context-library context)))
    (proof-with-checked-results
        ((original (if step step
                     (h1-propositions-propositional-proof-reflexive library term))))
      (proof-proof-rewrite proof original equality place))))

(defun h1-tactics-reduction-work (context depth)
  (let* ((search (h1-tactics-context-search context))
         (work (h1-tactics-search-work search)))
    (cond ((and (not (eq work :none)) (< (1- work) 0))
           '(:failure "Unproved" ""))
          ((> depth 160) '(:failure "Unproved" ""))
          ((eq work :none) context)
          (t (h1-tactics-context-with-search
              context (h1-tactics-search-with-work search (1- work)))))))

(defun h1-tactics-opening-fuel (head fuel)
  (table-get fuel head 0))

(defun h1-tactics-opening-available-p (head fuel)
  (not (equal (h1-tactics-opening-fuel head fuel) 0)))

(defun h1-tactics-decrease-opening (head fuel)
  (table-put fuel head (1- (h1-tactics-opening-fuel head fuel))))

(mutual-recursion
 (defun h1-tactics-context-find-loop (n context term)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-context-find-loop")
     (let ((known (assoc-equal term (h1-tactics-context-evidence context)))
           (active (h1-tactics-context-active context)))
       (cond (known (cons (cdr known) context))
             ((or (member-equal term active)
                  (>= (len active) 32)
                  (equal term *proof-false*))
              (cons nil context))
             (t
              (proof-with-checked-results
                  ((entered (h1-tactics-context-with-active context (cons term active)))
                   (derived (h1-tactics-context-derive-loop (1- n) entered term)))
                (cons (car derived)
                      (h1-tactics-context-remember
                       (h1-tactics-context-with-active (cdr derived) active)
                       term (car derived)))))))))

 (defun h1-tactics-context-derive-loop (n context term)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-context-derive-loop")
     (let ((prover (h1-tactics-context-prover context))
           (library (h1-tactics-context-library context)))
       (proof-with-checked-results ((earlier (h1-tactics-prover-prior-fact prover term)))
         (cond (earlier (cons earlier context))
               ((proof-is-call term *proof-quote*)
                (proof-with-checked-results
                    ((truth (h1-tactics-prover-quoted-truth prover term)))
                  (cons truth context)))
               (t
                (proof-with-checked-results
                    ((no (if (proof-is-call term *proof-if*) (proof-term-at term 3) :none))
                     (conjunction
                      (if (equal no *proof-false*)
                          (proof-with-checked-results
                              ((test (h1-tactics-context-find-loop (1- n) context
                                                                   (cadr term)))
                               (value (h1-tactics-context-find-loop (1- n) (cdr test)
                                                                    (caddr term)))
                               (step
                                (if (and (car test) (car value))
                                    (h1-propositions-propositional-proof-conjoin
                                     library term (car test) (car value))
                                  nil)))
                            (cons step (cdr value)))
                        (cons nil context))))
                  (if (car conjunction)
                      conjunction
                    (h1-tactics-context-derive-after-conjunction
                     (1- n) (cdr conjunction) term)))))))))

 (defun h1-tactics-context-derive-after-conjunction (n context term)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-context-derive-after-conjunction")
     (proof-with-checked-results
         ((right (if (proof-is-call term *proof-equal*) (proof-term-at term 2) :none))
          (step (if (and (not (eq right :none)) (equal (cadr term) right))
                    (h1-propositions-propositional-proof-reflexive
                     (h1-tactics-context-library context) right)
                  (h1-tactics-derive-constant context term))))
       (if step
           (cons step context)
         (h1-tactics-context-apply-loop (1- n) context "claims" term)))))

 (defun h1-tactics-context-find-signed (n context test)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-context-find-signed")
     (proof-with-checked-results
         ((positive (h1-tactics-context-find-loop (1- n) context test)))
       (if (car positive)
           positive
         (h1-tactics-context-find-loop (1- n) (cdr positive) (proof-neg test))))))

 (defun h1-tactics-context-select-loop (n context term)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-context-select-loop")
     (let ((proof (h1-tactics-context-proof context))
           (library (h1-tactics-context-library context))
           (prover (h1-tactics-context-prover context)))
       (proof-with-checked-results ((test (proof-term-at term 1)))
         (cond ((equal test *proof-false*)
                (proof-with-checked-results
                    ((selected (proof-proof-fact
                                proof "if-nil"
                                (seq-zip (list *library-y* *library-z*) (cddr term)))))
                  (cons selected context)))
               (t
                (proof-with-checked-results
                    ((evidence
                      (if (proof-is-call test *proof-quote*)
                          (proof-with-checked-results
                              ((truth (h1-tactics-prover-quoted-truth prover test)))
                            (cons truth context))
                        (h1-tactics-context-find-signed (1- n) context test)))
                     (selected
                      (if (car evidence)
                          (h1-propositions-propositional-proof-select library term (car evidence))
                        nil)))
                  (cons selected (cdr evidence)))))))))

 (defun h1-tactics-context-apply-loop (n context index term)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-context-apply-loop")
     (let* ((search (h1-tactics-context-search context))
            (global (h1-tactics-prover-rules (h1-tactics-context-prover context)))
            (head (h1-tactics-call-head term)))
       (proof-with-checked-results
           ((local (h1-tactics-index-for (h1-tactics-search-local search) index))
            (applied (h1-tactics-context-apply-candidates
                      (1- n) context (table-get local head nil) term)))
         (if (car applied)
             applied
           (proof-with-checked-results ((indexed (h1-tactics-index-for global index)))
             (h1-tactics-context-apply-candidates
              (1- n) (cdr applied) (table-get indexed head nil) term)))))))

 (defun h1-tactics-context-apply-candidates (n context candidates term)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-context-apply-candidates")
     (if (endp candidates)
         (cons nil context)
       (let* ((pattern (caar candidates))
              (rule (cadar candidates))
              (free (h1-tactics-rule-free rule))
              (original (h1-tactics-rule-step rule))
              (match (h1-tactics-match pattern term free nil))
              (bindings (cdr match)))
         (proof-with-checked-results
             ((applied
               (if (and (car match)
                        (not (h1-tactics-unbound-literal-p (proof-step-clause original)
                                                          free bindings)))
                   (proof-with-checked-results
                       ((step (proof-proof-instantiate
                               (h1-tactics-context-proof context) original
                               (table-items bindings))))
                     (h1-tactics-context-apply-sides
                      (1- n) context step (cdr (proof-step-clause step))))
                 (cons nil context))))
           (if (car applied)
               applied
             (h1-tactics-context-apply-candidates (1- n) (cdr applied)
                                                  (cdr candidates) term)))))))

 (defun h1-tactics-context-apply-sides (n context step sides)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-context-apply-sides")
     (if (endp sides)
         (cons step context)
       (let ((side (car sides))
             (ambient (h1-tactics-search-ambient (h1-tactics-context-search context))))
         (if (or (member-equal side ambient)
                 (not (member-equal side (cdr (proof-step-clause step)))))
             (h1-tactics-context-apply-sides (1- n) context step (cdr sides))
           (proof-with-checked-results
               ((candidate (if (proof-is-call side *proof-not*)
                               (proof-term-at side 1)
                             (proof-neg side)))
                (evidence (h1-tactics-context-guard-loop (1- n) context candidate)))
             (if (not (car evidence))
                 evidence
               (proof-with-checked-results
                   ((discharged (proof-proof-discharge
                                 (h1-tactics-context-proof context) step (car evidence))))
                 (h1-tactics-context-apply-sides (1- n) (cdr evidence)
                                                  discharged (cdr sides))))))))))

 (defun h1-tactics-context-guard-loop (n context term)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-context-guard-loop")
     (proof-with-checked-results ((found (h1-tactics-context-find-loop (1- n) context term)))
       (if (car found)
           found
         (let* ((context (cdr found))
                (guards (h1-tactics-context-guards context))
                (openings (h1-tactics-search-openings (h1-tactics-context-search context))))
           (proof-with-checked-results
               ((root (if (proof-is-call term *proof-not*) (proof-term-at term 1) term)))
             (if (or (not (assoc-equal (h1-tactics-call-head root) openings))
                     (member-equal term guards)
                     (>= (len guards) 4))
                 found
               (proof-with-checked-results
                   ((entered (h1-tactics-context-with-guards context (cons term guards)))
                    (reduced (h1-tactics-search-reduce-loop (1- n) term entered nil openings 0))
                    (equation (car reduced))
                    (known
                     (if equation
                         (proof-with-checked-results
                             ((value (h1-tactics-step-at equation 2)))
                           (h1-tactics-context-find-loop (1- n) (cadr reduced) value))
                       (cons nil (cadr reduced))))
                    (result
                     (if (car known)
                         (h1-propositions-proof-transport
                          (h1-tactics-context-proof context) (car known) equation)
                       nil)))
                 (cons result (h1-tactics-context-with-guards (cdr known) guards))))))))))

 (defun h1-tactics-search-reduce-follow (n step term context tests fuel depth)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-reduce-follow")
     (proof-with-checked-results ((value (h1-tactics-step-at step 2)))
       (if (equal value term)
           (list nil context tests)
         (proof-with-checked-results
             ((next (h1-tactics-search-reduce-loop (1- n) value context tests fuel (1+ depth)))
              (chained (proof-proof-chain (h1-tactics-context-proof context) step (list (car next)))))
           (list chained (cadr next) (caddr next)))))))

 (defun h1-tactics-search-reduce-rewrite (n current head context)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-reduce-rewrite")
     (proof-with-checked-results
         ((applied (h1-tactics-context-apply-loop (1- n) context "rewrites" current))
          (value (if (car applied) (h1-tactics-step-at (car applied) 2) current)))
       (if (not (equal value current))
           applied
         (proof-with-checked-results
             ((negative (h1-tactics-context-find-loop
                         (1- n) (cdr applied) (proof-neg current))))
           (cond ((car negative)
                  (proof-with-checked-results
                      ((equation (h1-tactics-prover-false-equation
                                  (h1-tactics-context-prover context) (car negative))))
                    (cons equation (cdr negative))))
                 ((equal head *proof-equal*)
                  (proof-with-checked-results
                      ((truth (h1-tactics-context-find-loop (1- n) (cdr negative) current))
                       (equation
                        (if (car truth)
                            (h1-tactics-prover-equality-is-true
                             (h1-tactics-context-prover context) (car truth))
                          nil)))
                    (cons equation (cdr truth))))
                 (t negative)))))))

 (defun h1-tactics-search-reduce-if (n term context tests fuel depth)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-reduce-if")
     (proof-with-checked-results ((selection (h1-tactics-context-select-loop (1- n) context term)))
       (if (car selection)
           (h1-tactics-search-reduce-follow (1- n) (car selection) term
                                             (cdr selection) tests fuel depth)
         (proof-with-checked-results
             ((test (proof-term-at term 1))
              (first (h1-tactics-search-reduce-loop (1- n) test (cdr selection)
                                                      tests fuel (1+ depth)))
              (opened (if (car first)
                          (h1-tactics-rewrite-argument (cadr first) nil term (car first) '(1 2 1))
                        nil))
              (current (h1-tactics-reduction-current opened term))
              (selected (h1-tactics-context-select-loop (1- n) (cadr first) current)))
           (if (car selected)
               (proof-with-checked-results
                   ((step (if opened
                              (proof-proof-chain (h1-tactics-context-proof context)
                                                 opened (list (car selected)))
                            (car selected))))
                 (h1-tactics-search-reduce-follow (1- n) step term (cdr selected)
                                                   (caddr first) fuel depth))
             (proof-with-checked-results ((test (proof-term-at current 1)))
               (list opened (cdr selected)
                     (h1-tactics-table-put-if-absent (caddr first) test nil)))))))))

 (defun h1-tactics-search-reduce-arguments (n arguments index term context tests fuel depth step)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-reduce-arguments")
     (if (endp arguments)
         (list step context tests)
       (proof-with-checked-results
           ((simplified (h1-tactics-search-reduce-loop (1- n) (car arguments) context
                                                         tests fuel (1+ depth)))
            (next (if (car simplified)
                      (h1-tactics-rewrite-argument
                       (cadr simplified) step term (car simplified) (list 1 2 index))
                    step)))
         (h1-tactics-search-reduce-arguments (1- n) (cdr arguments) (1+ index) term
                                             (cadr simplified) (caddr simplified)
                                             fuel depth next)))))

 (defun h1-tactics-search-reduce-selector (n head current context)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-reduce-selector")
     (proof-with-checked-results
         ((argument (proof-term-at current 1))
          (atom-step (h1-tactics-context-find-loop
                      (1- n) context (proof-neg (list *proof-consp* argument)))))
       (if (not (car atom-step))
           atom-step
         (let ((library (h1-tactics-context-library context))
               (proof (h1-tactics-context-proof context)))
           (proof-with-checked-results
               ((name (concatenate 'string "COMPLETION-OF-" (caddr head)))
                (complete (library-library-axiom library name (list argument)))
                (branch (h1-tactics-step-at complete 2))
                (selected (h1-propositions-propositional-proof-select library branch (car atom-step)))
                (chained (proof-proof-chain proof complete (list selected))))
             (cons chained (cdr atom-step))))))))

 (defun h1-tactics-search-reduce-after-arguments (n term head context tests fuel depth step)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-reduce-after-arguments")
     (proof-with-checked-results
         ((current (h1-tactics-reduction-current step term))
          (rewrite (if step
                       (h1-tactics-search-reduce-rewrite (1- n) current head context)
                     (cons nil context))))
       (let ((context (cdr rewrite))
             (equality (car rewrite)))
         (if (and (not equality)
                  (member-equal current
                                (h1-tactics-search-protected (h1-tactics-context-search context))))
             (h1-tactics-tidy-reduction context step tests)
           (proof-with-checked-results
               ((equality (or equality (h1-tactics-prover-constant
                                        (h1-tactics-context-prover context) current)))
                (known (if (and (not equality) (not (member-equal head *h1-tactics-translation*)))
                           (h1-tactics-context-find-loop (1- n) context current)
                         (cons nil context))))
             (if (car known)
                 (h1-tactics-tidy-reduction (cdr known) step tests)
               (proof-with-checked-results
                   ((completion
                     (if (and (not equality) (member-equal head (list *library-car* *library-cdr*)))
                         (h1-tactics-search-reduce-selector (1- n) head current (cdr known))
                       (cons equality (cdr known)))))
                 (h1-tactics-search-reduce-finish
                  (1- n) term head current (cdr completion) tests fuel depth step
                  (car completion))))))))))

 (defun h1-tactics-search-reduce-finish (n term head current context tests fuel depth step equality)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-reduce-finish")
     (if (and (not equality) (not (h1-tactics-opening-available-p head fuel)))
         (h1-tactics-tidy-reduction context step tests)
       (let ((proof (h1-tactics-context-proof context))
             (next-fuel (if equality fuel (h1-tactics-decrease-opening head fuel))))
         (proof-with-checked-results
             ((equation (or equality (proof-proof-unfold proof current)))
              (chained (if step (proof-proof-chain proof step (list equation)) equation)))
           (h1-tactics-search-reduce-follow (1- n) chained term context tests next-fuel depth))))))

 (defun h1-tactics-search-reduce-call (n term head context tests fuel depth)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-reduce-call")
     (proof-with-checked-results
         ((rewrite (h1-tactics-search-reduce-rewrite (1- n) term head context)))
       (let ((context (cdr rewrite)))
         (cond ((car rewrite)
                (h1-tactics-search-reduce-follow (1- n) (car rewrite) term context tests fuel depth))
               ((member-equal term (h1-tactics-search-protected (h1-tactics-context-search context)))
                (list nil context tests))
               (t
                (proof-with-checked-results
                    ((constant (h1-tactics-prover-constant (h1-tactics-context-prover context) term)))
                  (if constant
                      (h1-tactics-search-reduce-follow
                       (1- n) constant term context tests fuel depth)
                    (let ((translation (member-equal head *h1-tactics-translation*))
                          (proof (h1-tactics-context-proof context)))
                      (proof-with-checked-results
                          ((known (if translation (cons nil context)
                                    (h1-tactics-context-find-loop (1- n) context term))))
                        (cond ((car known) (list nil (cdr known) tests))
                              ((and translation (h1-tactics-opening-available-p head fuel))
                               (proof-with-checked-results ((unfolded (proof-proof-unfold proof term)))
                                 (h1-tactics-search-reduce-follow
                                  (1- n) unfolded term (cdr known) tests
                                  (h1-tactics-decrease-opening head fuel) depth)))
                              (t
                               (proof-with-checked-results
                                   ((arguments (h1-tactics-search-reduce-arguments
                                                (1- n) (cdr term) 1 term (cdr known)
                                                tests fuel depth nil)))
                                 (h1-tactics-search-reduce-after-arguments
                                  (1- n) term head (cadr arguments) (caddr arguments)
                                  fuel depth (car arguments)))))))))))))))

 (defun h1-tactics-search-reduce-loop (n term context tests fuel depth)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-reduce-loop")
     (proof-with-checked-results ((context (h1-tactics-reduction-work context depth)))
       (let* ((head (h1-tactics-call-head term))
              (binding (assoc-equal term (h1-tactics-context-bindings context))))
         (cond ((equal head *proof-quote*) (list nil context tests))
               (binding (h1-tactics-search-reduce-follow (1- n) (cdr binding) term
                                                           context tests fuel depth))
               ((proof-compound head)
                (proof-with-checked-results
                    ((beta (proof-proof-beta (h1-tactics-context-proof context) term)))
                  (h1-tactics-search-reduce-follow (1- n) beta term context tests fuel depth)))
               ((eq head :none)
                (proof-with-checked-results
                    ((negative (h1-tactics-context-find-loop (1- n) context (proof-neg term)))
                     (equation (h1-tactics-prover-false-equation
                                (h1-tactics-context-prover context) (car negative))))
                  (list equation (cdr negative) tests)))
               ((equal head *proof-if*)
                (h1-tactics-search-reduce-if (1- n) term context tests fuel depth))
               (t (h1-tactics-search-reduce-call (1- n) term head context tests fuel depth))))))))

(defun h1-tactics-context-find (context term)
  (h1-tactics-context-find-loop 1000000 context term))

(defun h1-tactics-context-derive (context term)
  (h1-tactics-context-derive-loop 1000000 context term))

(defun h1-tactics-context-select (context term)
  (h1-tactics-context-select-loop 1000000 context term))

(defun h1-tactics-context-apply (context index term)
  (h1-tactics-context-apply-loop 1000000 context index term))

(defun h1-tactics-context-guard (context term)
  (h1-tactics-context-guard-loop 1000000 context term))

(defun h1-tactics-search-reduce (search term context tests fuel depth)
  (h1-tactics-search-reduce-loop 1000000 term (h1-tactics-context-with-search context search)
                                  tests fuel depth))

(defun h1-tactics-context-if-consequences-final (context step test evidence)
  (let ((proof (h1-tactics-context-proof context))
        (library (h1-tactics-context-library context)))
    (if evidence
        (proof-with-checked-results
            ((branch (h1-propositions-proof-prove-if proof step evidence)))
          (cons (list branch) context))
      (proof-with-checked-results
          ((first (proof-step-first step))
           (no (proof-term-at first 3)))
        (cond ((equal no *proof-false*)
               (proof-with-checked-results
                   ((conjuncts (h1-propositions-propositional-proof-conjunct library step)))
                 (cons conjuncts context)))
              ((equal (caddr first) *proof-false*)
               (proof-with-checked-results
                   ((on-true (h1-arithmetic-proof-if-true proof first))
                    (rewritten (proof-proof-rewrite proof step on-true '(1)))
                    (contradicts (proof-proof-tidy proof rewritten))
                    (excluded (proof-proof-front proof contradicts (proof-neg test)))
                    (branch (h1-propositions-proof-prove-if proof step excluded)))
                 (cons (list excluded branch) context)))
              (t (cons nil context)))))))

(defun h1-tactics-context-if-consequences (context step)
  (proof-with-checked-results
      ((test (h1-tactics-step-at step 1))
       (known (h1-tactics-context-find-signed 1000000 context test)))
    (if (car known)
        (h1-tactics-context-if-consequences-final (cdr known) step test (car known))
      (let* ((context (cdr known))
             (openings (h1-tactics-search-openings (h1-tactics-context-search context)))
             (proof (h1-tactics-context-proof context)))
        (proof-with-checked-results
            ((normalized (h1-tactics-search-reduce-loop 1000000 test context nil openings 0)))
          (if (not (car normalized))
              (h1-tactics-context-if-consequences-final (cadr normalized) step test nil)
            (proof-with-checked-results
                ((rewritten (proof-proof-rewrite proof step (car normalized) '(1 1)))
                 (step (proof-proof-tidy proof rewritten))
                 (test (h1-tactics-step-at step 1))
                 (known (h1-tactics-context-find-signed 1000000 (cadr normalized) test)))
              (h1-tactics-context-if-consequences-final (cdr known) step test
                                                        (car known)))))))))

(defun h1-tactics-drop-missing-evidence (evidence)
  (if (endp evidence)
      nil
    (if (cdar evidence)
        (cons (car evidence) (h1-tactics-drop-missing-evidence (cdr evidence)))
      (h1-tactics-drop-missing-evidence (cdr evidence)))))

(defun h1-tactics-push-consequences (children may-open pending)
  (if (endp children)
      pending
    (h1-tactics-push-consequences (cdr children) may-open
                                   (cons (list (car children) may-open) pending))))

(defun h1-tactics-learn-equation (context term)
  (proof-with-checked-results
      ((applied (h1-tactics-context-apply context "rewrites" term)))
    (let* ((context (cdr applied))
           (head (h1-tactics-call-head term))
           (proof (h1-tactics-context-proof context))
           (openings (h1-tactics-search-openings (h1-tactics-context-search context))))
      (if (and (not (car applied))
               (assoc-equal head openings)
               (assoc-equal head (proof-proof-definitions proof)))
          (proof-with-checked-results ((equation (proof-proof-unfold proof term)))
            (cons equation context))
        applied))))

(defun h1-tactics-context-learn-loop (n context pending seen)
  (declare (xargs :measure (nfix n)))
  (if (h1-tactics-fuel-exhausted-p n)
      '(:failure "Fuel" "h1-tactics-context-learn-loop")
    (if (endp pending)
        context
      (let ((step (caar pending))
            (may-open (cadar pending))
            (rest (cdr pending)))
        (proof-with-checked-results
            ((term (if step (proof-step-first step)
                     '(:failure "failure" ""))))
          (if (or (member-equal term seen) (equal term *proof-false*))
              (h1-tactics-context-learn-loop (1- n) context rest seen)
            (let* ((evidence (h1-tactics-context-evidence context))
                   (context
                    (if (table-get evidence term nil)
                        context
                      (h1-tactics-context-with-evidence
                       context (table-put (h1-tactics-drop-missing-evidence evidence)
                                            term step))))
                   (seen (cons term seen))
                   (protected (h1-tactics-search-protected (h1-tactics-context-search context))))
              (cond ((proof-is-call term *proof-if*)
                     (proof-with-checked-results
                         ((children (h1-tactics-context-if-consequences context step)))
                       (h1-tactics-context-learn-loop
                        (1- n) (cdr children)
                        (h1-tactics-push-consequences (car children) may-open rest) seen)))
                    ((and may-open (not (member-equal term protected)))
                     (proof-with-checked-results
                         ((opened (h1-tactics-learn-equation context term))
                          (proof (h1-tactics-context-proof context))
                          (rewritten
                           (if (car opened)
                               (proof-with-checked-results
                                   ((step (proof-proof-rewrite proof step (car opened) '(1))))
                                 (proof-proof-tidy proof step))
                             nil)))
                       (h1-tactics-context-learn-loop
                        (1- n) (cdr opened)
                        (if rewritten (cons (list rewritten nil) rest) rest) seen)))
                    (t (h1-tactics-context-learn-loop (1- n) context rest seen))))))))))

(defun h1-tactics-context-learn (context premise)
  (let ((evidence (assoc-equal premise (h1-tactics-context-evidence context))))
    (if evidence
        (h1-tactics-context-learn-loop 1000000 context (list (list (cdr evidence) t)) nil)
      '(:failure "failure" ""))))

(defun h1-tactics-cut-on-signed-test (proof asserted contrary holds)
  (if holds
      (proof-proof-cut proof asserted contrary)
    (proof-proof-cut proof contrary asserted)))

(defun h1-tactics-search-contradict-reduced (context test holds signed)
  (let* ((search (h1-tactics-context-search context))
         (proof (h1-tactics-context-proof context))
         (library (h1-tactics-context-library context))
         (others (remove-equal signed (h1-tactics-context-tests context))))
    (proof-with-checked-results
        ((other (h1-tactics-context-init search others))
         (reduced (h1-tactics-search-reduce search test other nil
                                             (h1-tactics-search-openings search) 0))
         (value (h1-tactics-reduction-current (car reduced) test))
         (contrary (if (equal value test)
                       (cons nil (cadr reduced))
                     (h1-tactics-context-find (cadr reduced)
                                               (if holds (proof-neg value) value))))
         (context (h1-tactics-context-with-search
                   context (h1-tactics-context-search (cdr contrary)))))
      (if (not (car contrary))
          (cons nil context)
        (proof-with-checked-results
            ((transported (if holds
                              (h1-propositions-library-transport-argument
                               library (car contrary) (car reduced) 1)
                            (h1-propositions-proof-transport
                             proof (car contrary) (car reduced))))
             (statement (if holds test (proof-neg test)))
             (evidence (assoc-equal statement (h1-tactics-context-evidence context)))
             (asserted (if evidence (cdr evidence)
                         '(:failure "failure" "")))
             (cut (h1-tactics-cut-on-signed-test proof asserted transported holds)))
          (cons cut context))))))

(defund h1-tactics-search-contradiction-test (context signed)
  (let ((test (car signed))
        (holds (cadr signed))
        (proof (h1-tactics-context-proof context)))
    (proof-with-checked-results
        ((opposite (h1-tactics-context-find context (if holds (proof-neg test) test))))
      (if (car opposite)
          (proof-with-checked-results
              ((assumed (h1-arithmetic-proof-assume proof test holds))
               (step (h1-tactics-cut-on-signed-test proof assumed (car opposite) holds)))
            (cons step (cdr opposite)))
        (h1-tactics-search-contradict-reduced (cdr opposite) test holds signed)))))

(defun h1-tactics-search-contradiction-tests (context tests)
  (declare (xargs :measure (acl2-count tests)))
  (if (h1-tactics-list-finished-p tests)
      (cons nil context)
    (proof-with-checked-results
        ((result (h1-tactics-search-contradiction-test context (car tests))))
      (if (car result)
          result
        (h1-tactics-search-contradiction-tests (cdr result) (cdr tests))))))

(defun h1-tactics-search-contradiction (search context)
  (h1-tactics-search-contradiction-tests
   (h1-tactics-context-with-search context search) (h1-tactics-context-tests context)))

(defun h1-tactics-search-try-implication (context term tests)
  (if (not (proof-is-call term *library-implies*))
      (cons nil context)
    (let ((library (h1-tactics-context-library context)))
      (proof-with-checked-results
          ((parts (proof-list-of-length term 3))
           (premise (cadr parts))
           (conclusion (caddr parts))
           (refutation (h1-tactics-context-find context (proof-neg premise)))
           (context (cdr refutation)))
        (if (car refutation)
            (proof-with-checked-results
                ((step (h1-propositions-propositional-proof-false-premise
                        library term (car refutation))))
              (cons step context))
          (proof-with-checked-results
              ((given (h1-tactics-context-init (h1-tactics-context-search context)
                                               (append tests (list (list premise t)))))
               (learned (h1-tactics-context-learn given premise))
               (known (h1-tactics-context-guard learned conclusion))
               (step (if (car known)
                         (h1-propositions-propositional-proof-implies-from
                          library term (car known))
                       nil)))
            (cons step (h1-tactics-context-with-search
                        context (h1-tactics-context-search (cdr known))))))))))

(defun h1-tactics-search-try-contradiction (context term)
  (proof-with-checked-results
      ((contradiction (h1-tactics-search-contradiction
                       (h1-tactics-context-search context) context)))
    (if (not (car contradiction))
        contradiction
      (proof-with-checked-results
          ((step (proof-proof-subsume (h1-tactics-context-proof context)
                                       (car contradiction)
                                       (cons term (proof-step-clause (car contradiction))))))
        (cons step (cdr contradiction))))))

(mutual-recursion
 (defun h1-tactics-search-prove-loop (n search term tests split-and)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-prove-loop")
     (proof-with-checked-results
         ((context (h1-tactics-context-init search tests))
          (known (h1-tactics-context-find context term)))
       (if (car known)
           (cons (car known) (h1-tactics-context-search (cdr known)))
         (proof-with-checked-results
             ((implication (h1-tactics-search-try-implication (cdr known) term tests))
              (context (cdr implication))
              (search (h1-tactics-context-search context)))
           (if (car implication)
               (cons (car implication) search)
             (proof-with-checked-results
                 ((no (if (and split-and (proof-is-call term *proof-if*))
                          (proof-term-at term 3)
                        :none)))
               (if (equal no *proof-false*)
                   (proof-with-checked-results
                       ((first (h1-tactics-search-prove-loop (1- n) search (cadr term) tests t))
                        (second (h1-tactics-search-prove-loop (1- n) (cdr first)
                                                              (caddr term) tests t))
                        (step (h1-propositions-propositional-proof-conjoin
                               (h1-tactics-search-library search) term (car first) (car second))))
                     (cons step (cdr second)))
                 (h1-tactics-search-prove-reduced (1- n) context term tests)))))))))

 (defun h1-tactics-search-prove-reduced (n context term tests)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-prove-reduced")
     (let* ((search (h1-tactics-context-search context))
            (proof (h1-tactics-context-proof context)))
       (proof-with-checked-results
           ((reduced (h1-tactics-search-reduce search term context nil
                                              (h1-tactics-search-openings search) 0))
            (result (h1-tactics-reduction-current (car reduced) term))
            (known (h1-tactics-context-find (cadr reduced) result)))
         (if (car known)
             (proof-with-checked-results
                 ((step (if (car reduced)
                            (h1-propositions-proof-transport proof (car known) (car reduced))
                          (car known))))
               (cons step (h1-tactics-context-search (cdr known))))
           (proof-with-checked-results
               ((contradiction (if (equal result *proof-false*)
                                   (h1-tactics-search-try-contradiction (cdr known) term)
                                 known))
                (context (cdr contradiction))
                (search (h1-tactics-context-search context)))
             (cond ((car contradiction) (cons (car contradiction) search))
                   ((equal (h1-tactics-search-remaining search) 0)
                    '(:failure "Unproved" ""))
                   (t (h1-tactics-search-prove-pending
                       (1- n) context term result tests (caddr reduced))))))))))

 (defun h1-tactics-search-prove-pending (n context term result tests pending)
   (declare (xargs :measure (nfix n)))
   (if (h1-tactics-fuel-exhausted-p n)
       '(:failure "Fuel" "h1-tactics-search-prove-pending")
     (if (endp pending)
         (proof-with-checked-results
             ((contradiction (if (equal result *proof-false*)
                                 (cons nil context)
                               (h1-tactics-search-try-contradiction context term))))
           (if (car contradiction)
               (cons (car contradiction) (h1-tactics-context-search (cdr contradiction)))
             '(:failure "Unproved" "")))
       (let ((test (caar pending)))
         (proof-with-checked-results
             ((known (h1-tactics-context-find-signed 1000000 context test)))
           (if (car known)
               (h1-tactics-search-prove-pending (1- n) (cdr known) term result tests
                                                (cdr pending))
             (let* ((search (h1-tactics-context-search (cdr known)))
                    (remaining (1- (h1-tactics-search-remaining search)))
                    (search (h1-tactics-search-with-remaining search remaining)))
               (proof-with-checked-results
                   ((yes (h1-tactics-search-prove-loop
                          (1- n) search term (append tests (list (list test t))) nil))
                    (no (h1-tactics-search-prove-loop
                         (1- n) (cdr yes) term (append tests (list (list test nil))) nil))
                    (step (proof-proof-cases (h1-tactics-context-proof context)
                                             test (car yes) (car no))))
                 (cons step (cdr no)))))))))))

(defun h1-tactics-search-prove (search term tests split-and)
  (h1-tactics-search-prove-loop 1000000 search term tests split-and))

(defun h1-tactics-search-with-premise (search formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (result (h1-tactics-search-prove search (caddr parts) (list (list (cadr parts) t)) t))
       (step (h1-propositions-propositional-proof-implies-from
              (h1-tactics-search-library search) formula (car result))))
    (cons step (cdr result))))

(defun h1-tactics-prover-limit (prover limit)
  (let ((case-limit (h1-tactics-prover-case-limit prover)))
    (cond ((eq limit :none) (if (eq case-limit :none) 160 case-limit))
          ((eq case-limit :none) limit)
          (t (min limit case-limit)))))

(defun h1-tactics-prover-solve (prover formula openings limit)
  (let ((proof (h1-tactics-prover-proof prover))
        (limit (h1-tactics-prover-limit prover limit)))
    (proof-with-checked-results
        ((left (if (proof-is-call formula *proof-equal*) (proof-term-at formula 1) :none))
         (equation (if (and (not (eq left :none))
                            (assoc-equal (h1-tactics-call-head left)
                                         (proof-proof-definitions proof)))
                       (proof-proof-unfold proof left)
                     nil))
         (literal (if equation (proof-step-first equation) :none)))
      (if (equal literal formula)
          equation
        (proof-with-checked-results
            ((search (h1-tactics-search-init prover openings nil nil nil limit nil))
             (result (h1-tactics-search-prove search formula nil t)))
          (car result))))))

(defun h1-tactics-induction-anchors (pairs measured)
  (declare (xargs :measure (acl2-count pairs)))
  (if (h1-tactics-list-finished-p pairs)
      nil
    (proof-with-checked-results
        ((pair (proof-list-of-length (car pairs) 2))
         (actual (cadr pair))
         (anchor (or (proof-is-call actual *library-cdr*) (member-equal actual measured)))
         (rest (h1-tactics-induction-anchors (cdr pairs) measured)))
      (if anchor (cons actual rest) rest))))

(defun h1-tactics-induction-protected (terms parents defined anchors)
  (if (endp terms)
      nil
    (let* ((term (car terms))
           (protect (and (not (member-equal term parents))
                         (member-equal (h1-tactics-call-head term) defined)
                         (intersectp-equal anchors (h1-tactics-subterms term))))
           (remaining (h1-tactics-induction-protected (cdr terms) parents defined anchors)))
      (if protect (cons term remaining) remaining))))

(defun h1-tactics-induction-case (substitution prover formula parents defined cases)
  (let ((proof (h1-tactics-prover-proof prover)))
    (proof-with-checked-results
        ((substitution (proof-list-of-length substitution 2))
         (pairs (car substitution))
         (descent (cadr substitution))
         (child (proof-subst formula (proof-bindings-table pairs nil)))
         (smaller (proof-step-first descent))
         (hypothesis (proof-ite smaller child *proof-true*))
         (assumed (h1-arithmetic-proof-assume proof hypothesis t))
         (then (h1-propositions-proof-prove-if proof assumed descent))
         (added (h1-tactics-rules-add-formula (car cases) then nil t))
         (measure-child (proof-term-at smaller 1))
         (anchors (h1-tactics-induction-anchors pairs (h1-tactics-subterms measure-child)))
         (new-protected
          (h1-tactics-induction-protected (h1-tactics-subterms child) parents defined anchors)))
      (list added (cons (proof-neg hypothesis) (cadr cases))
            (append new-protected (caddr cases))))))

(defun h1-tactics-induction-cases (substitutions prover formula parents defined cases)
  (declare (xargs :measure (acl2-count substitutions)))
  (cond ((failure-p cases) cases)
        ((h1-tactics-list-finished-p substitutions)
         (list (car cases) (reverse (cadr cases)) (caddr cases)))
        (t (h1-tactics-induction-cases
            (cdr substitutions) prover formula parents defined
            (h1-tactics-induction-case (car substitutions) prover formula parents defined cases)))))

(defun h1-tactics-induction-bindings (substitutions)
  (if (endp substitutions)
      nil
    (cons (caar substitutions) (h1-tactics-induction-bindings (cdr substitutions)))))

(defun h1-tactics-induction-step (search formula assume-premise split-on)
  (cond ((not (eq split-on :none))
         (proof-with-checked-results
             ((yes (h1-tactics-search-prove search formula (list (list split-on t)) t))
              (no (h1-tactics-search-prove (cdr yes) formula (list (list split-on nil)) t)))
           (proof-proof-cases (h1-tactics-prover-proof (h1-tactics-search-prover search))
                              split-on (car yes) (car no))))
        (t (proof-with-checked-results
               ((step (if assume-premise
                          (h1-tactics-search-with-premise search formula)
                        (h1-tactics-search-prove search formula nil t))))
             (car step)))))

(defun h1-tactics-prover-by-induction (prover formula measure substitutions openings ordinal
                                             limit assume-premise preserve split-on)
  (let ((proof (h1-tactics-prover-proof prover))
        (library (h1-tactics-prover-library prover))
        (limit (h1-tactics-prover-limit prover limit)))
    (proof-with-checked-results
        ((cases (h1-tactics-induction-cases
                 substitutions prover formula (h1-tactics-subterms formula)
                 (set-difference-equal (table-keys (h1-tactics-opening-map openings))
                                       *h1-tactics-translation*)
                 (list (h1-tactics-rules-init prover) nil nil)))
         (ordination (if ordinal
                         (cons ordinal nil)
                       (descent-direct-builtin library (list (list *proof-ordinalp* measure)) nil))))
      (if (not (car ordination))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((search (h1-tactics-search-init prover openings (car cases) (cadr cases)
                                             (append (caddr cases) preserve) limit nil))
             (step (h1-tactics-induction-step search formula assume-premise split-on)))
          (proof-proof-induct proof (car ordination) step formula measure
                              (h1-tactics-induction-bindings substitutions)))))))
