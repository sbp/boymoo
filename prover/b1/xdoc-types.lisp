(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun b1-xdoc-types-xdoc (name)
  (proof-sym name "XDOC"))

(defconst *b1-xdoc-types-tree* (b1-xdoc-types-xdoc "TREEP"))
(defconst *b1-xdoc-types-trees* (b1-xdoc-types-xdoc "TREE-LISTP"))
(defconst *b1-xdoc-types-tag* (b1-xdoc-types-xdoc "TREE-TAGP"))
(defconst *b1-xdoc-types-tree-alist* (b1-xdoc-types-xdoc "KEYWORD-TREE-ALISTP"))
(defconst *b1-xdoc-types-make-tag* (b1-xdoc-types-xdoc "MAKE-TREE-TAG"))
(defconst *b1-xdoc-types-make-directive* (b1-xdoc-types-xdoc "MAKE-TREE-DIR/&&"))
(defconst *b1-xdoc-types-keywordp* (proof-cl "KEYWORDP"))
(defconst *b1-xdoc-types-acons* (proof-cl "ACONS"))
(defconst *b1-xdoc-types-alistp* (proof-sym "ALISTP" "ACL2"))
(defconst *b1-xdoc-types-string-constructors*
  (list (proof-sym "STRING-APPEND" "ACL2")
        (proof-sym "STRING-APPEND-LST" "ACL2")
        (proof-cl "STRING-DOWNCASE")
        (b1-xdoc-types-xdoc "STRING-DOWNCASE$")))

(defun b1-xdoc-types-step-argument (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b1-xdoc-types-list-type-implication-base-consequence (typed lib source goal atom)
  (let ((proof (library-library-proof lib))
        (unfold (list *b1-logic-atom* *b1-logic-eq* *proof-not*)))
    (proof-with-checked-results
        ((source-eq (b1-logic-bookproof-normalize lib source (list atom) (cons (car source) unfold)
                                                  nil nil nil nil))
         (goal-head (proof-term-at goal 0))
         (goal-eq (b1-logic-bookproof-normalize lib goal (list atom) (cons goal-head unfold)
                                                nil nil nil nil))
         (rewritten (proof-proof-rewrite proof typed source-eq (list 1))))
      (proof-proof-transport proof rewritten goal-eq))))

(defun b1-xdoc-types-list-type-implication-base (atom lib formula source goal)
  (proof-with-checked-results
      ((typed (b1-logic-bookproof-prove-implication-premise lib formula))
       (step (b1-xdoc-types-list-type-implication-base-consequence typed lib source goal atom)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula typed step)))

(defun b1-xdoc-types-list-type-implication-step-consequence (typed lib source goal xs cons induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-list lib source (list cons)))
         (rewritten (proof-proof-rewrite proof typed opened (list 1)))
         (parts (proof-proof-conjunct proof rewritten))
         (child (proof-proof-modus-ponens proof induction (cadr parts)))
         (goal-head (proof-term-at goal 0)))
      (if (equal goal-head *b1-printing-true-listp*)
          (proof-with-checked-results ((view (b1-revappend-open-list lib goal (list cons))))
            (proof-proof-transport proof child view))
        (proof-with-checked-results
            ((leaf (b1-logic-bookproof-normalize-proof lib
                    (list *b1-xdoc-types-tree* (list *library-car* xs))
                    (list (car parts)) (list *b1-xdoc-types-tree*) nil nil))
             (view (b1-revappend-open-list lib goal (list cons leaf))))
          (proof-proof-transport proof child view))))))

(defun b1-xdoc-types-list-type-implication-step (cons induction lib formula source goal xs)
  (proof-with-checked-results
      ((typed (b1-logic-bookproof-prove-implication-premise lib formula))
       (step (b1-xdoc-types-list-type-implication-step-consequence typed lib source goal xs cons induction)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula typed step)))

(defun b1-xdoc-types-list-type-implication (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (source (proof-list-of-length (cadr implication) 2))
       (goal (caddr implication))
       (xs (cadr source))
       (preparation (b1-revappend-list-induction-prepare lib formula xs nil))
       (step (b1-xdoc-types-list-type-implication-step
              (caddr preparation) (cadddr preparation) lib formula source goal xs))
       (atom (proof-proof-assume (library-library-proof lib) (cadr preparation) nil))
       (base (b1-xdoc-types-list-type-implication-base atom lib formula source goal)))
    (b1-revappend-list-induction lib preparation base step)))

(defun b1-xdoc-types-tree-cons (lib formula)
  (let ((proof (library-library-proof lib))
        (unfold (list *b1-xdoc-types-tree*)))
    (proof-with-checked-results
        ((equality (proof-list-of-length formula 3))
         (claim (proof-list-of-length (cadr equality) 2))
         (items (cadr claim))
         (tail (proof-term-at items 2))
         (cons (b1-revappend-cons-value lib items))
         (law (proof-proof-fact proof "consp-not-stringp" (list (list *library-x* items))))
         (not-string (proof-proof-modus-ponens proof law cons))
         (proper-cons (b1-revappend-open-list lib (list *b1-printing-true-listp* items) nil))
         (tail-test (list *b1-xdoc-types-trees* tail))
         (have (proof-proof-assume proof tail-test t))
         (miss (proof-proof-assume proof tail-test nil))
         (rule (b1-logic-bookproof-from-fact lib (b1-xdoc-types-xdoc "TRUE-LISTP-WHEN-TREE-LISTP")
                 (list *library-implies* tail-test (list *b1-printing-true-listp* tail))))
         (proper (proof-proof-modus-ponens proof rule have))
         (rules (list (b1-logic-equal-to proper-cons)))
         (yes (b1-logic-bookproof-case-proof lib formula (list not-string have proper) unfold rules 16))
         (false-equality (b1-logic-bookproof-false-value lib miss))
         (no (b1-logic-bookproof-case-proof lib formula (list not-string miss) unfold
                                           (append rules (list (b1-logic-equal-to false-equality))) 16)))
      (proof-proof-cases proof tail-test yes no))))

(defun b1-xdoc-types-tree-alist-cons (lib formula)
  (proof-with-checked-results ((claim (proof-term-at formula 1)))
    (b1-logic-bookproof-normalize lib claim nil
     (list *b1-xdoc-types-tree-alist* *b1-logic-atom* *proof-not*) nil nil nil t)))

(defun b1-xdoc-types-tree-constructor-tag-rules (lib call pair)
  (proof-with-checked-results ((head (proof-term-at call 0)))
    (if (equal head *b1-xdoc-types-make-tag*)
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results
              ((header (proof-term-at pair 1))
               (law (proof-proof-fact proof "consp-not-symbolp" (list (list *library-x* header))))
               (cons (b1-revappend-cons-value lib header))
               (symbol (proof-proof-modus-ponens proof law cons))
               (is-keyword (b1-logic-bookproof-normalize lib (list *b1-xdoc-types-keywordp* header)
                            (list symbol) (list *b1-xdoc-types-keywordp*) nil nil nil nil))
               (tag (b1-logic-bookproof-normalize lib (list *b1-xdoc-types-tag* header) nil
                     (list *b1-xdoc-types-tag*) nil nil nil t)))
            (list (b1-logic-equal-to is-keyword) (b1-logic-equal-to tag))))
      nil)))

(defun b1-xdoc-types-tree-constructor (lib formula)
  (let ((proof (library-library-proof lib))
        (implication (proof-is-call formula *library-implies*)))
    (proof-with-checked-results
        ((claim (if implication (proof-term-at formula 2) formula))
         (left (proof-term-at claim 1))
         (call (proof-term-at left 1))
         (made (proof-proof-unfold proof call))
         (pair (b1-xdoc-types-step-argument made 2))
         (name (b1-xdoc-types-xdoc "TREEP-OF-CONS"))
         (fact (proof-proof-fact proof name nil))
         (fact-left (b1-xdoc-types-step-argument fact 1))
         (pattern (proof-term-at fact-left 1))
         (tree-rule (proof-proof-fact proof name (seq-zip (cdr pattern) (cdr pair))))
         (initial-rules (list (b1-logic-equal-to made) (b1-logic-equal-to tree-rule)))
         (tag-rules (b1-xdoc-types-tree-constructor-tag-rules lib call pair))
         (rules (append initial-rules tag-rules)))
      (if implication
          (proof-with-checked-results
              ((guard (b1-logic-bookproof-prove-implication-premise lib formula))
               (step (b1-logic-bookproof-case-proof lib claim (list guard) nil rules 16)))
            (b1-logic-bookproof-prove-implication-with-premise lib formula guard step))
        (b1-logic-bookproof-case-proof lib claim nil nil rules 16)))))

(defun b1-xdoc-types-tree-tag-wrapper-support (lib actual keyword result)
  (let ((proof (library-library-proof lib))
        (target (list *b1-xdoc-types-tree* actual)))
    (proof-with-checked-results
        ((head (proof-term-at actual 0))
         (keyword-claim (proof-step-first keyword)))
      (if (equal head *b1-xdoc-types-make-tag*)
          (proof-with-checked-results
              ((name (b1-xdoc-types-xdoc "TREEP-OF-MAKE-TREE-TAG"))
               (quoted (b1-logic-bookproof-from-fact lib name
                        (proof-eq target (proof-ite keyword-claim result *proof-false*))))
               (conditional (b1-xdoc-types-step-argument quoted 2))
               (selected (proof-proof-select proof conditional keyword)))
            (proof-proof-chain proof quoted (list selected)))
        (proof-with-checked-results
            ((name (b1-xdoc-types-xdoc "TREEP-OF-MAKE-TREE-DIR/&&"))
             (fact (b1-logic-bookproof-from-fact lib name
                    (list *library-implies* keyword-claim (proof-eq target result)))))
          (proof-proof-modus-ponens proof fact keyword))))))

(defun b1-xdoc-types-tree-tag-wrapper-proof (lib formula call)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof call))
         (actual (b1-xdoc-types-step-argument opened 2))
         (header (proof-term-at actual 1))
         (keyword (b1-logic-bookproof-normalize-proof lib (list *b1-xdoc-types-keywordp* header)
                                                      nil (list *b1-xdoc-types-keywordp*) nil nil))
         (result (proof-term-at formula 2))
         (supported (b1-xdoc-types-tree-tag-wrapper-support lib actual keyword result))
         (reversed (proof-proof-symmetric proof opened)))
      (proof-proof-rewrite proof supported reversed '(1 1 1)))))

(defun b1-xdoc-types-tree-tag-wrapper-call (lib formula call)
  (if (not (true-listp call))
      nil
    (proof-with-checked-results ((head (proof-term-at call 0)))
      (let* ((proof (library-library-proof lib))
             (definition (assoc-equal head (proof-proof-definitions proof))))
        (if (not definition)
            nil
          (proof-with-checked-results ((parts (proof-list-of-length (cdr definition) 2)))
            (let ((body (cadr parts)))
              (and (or (proof-is-call body *b1-xdoc-types-make-tag*)
                       (proof-is-call body *b1-xdoc-types-make-directive*))
                   (b1-xdoc-types-tree-tag-wrapper-proof lib formula call)))))))))

(defun b1-xdoc-types-tree-tag-wrapper (lib formula)
  (if (not (proof-is-call formula *proof-equal*))
      nil
    (proof-with-checked-results ((claim (proof-term-at formula 1)))
      (and (proof-is-call claim *b1-xdoc-types-tree*)
           (proof-with-checked-results ((call (proof-term-at claim 1)))
             (b1-xdoc-types-tree-tag-wrapper-call lib formula call))))))

(defun b1-xdoc-types-evidence-from-cases (lib tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((pair (proof-list-of-length (car tests) 2))
         (fact (proof-proof-assume (library-library-proof lib) (car pair) (cadr pair)))
         (first (if (cadr pair) (b1-logic-bookproof-split-conjuncts lib fact) (list fact)))
         (rest (b1-xdoc-types-evidence-from-cases lib (cdr tests))))
      (append first rest))))

(defun b1-xdoc-types-by-value-restore (proof step equality template)
  (proof-with-checked-results ((reversed (proof-proof-symmetric proof equality)))
    (proof-proof-rewrite-result proof step reversed template *proof-result*)))

(defun b1-xdoc-types-by-value-cases (lib value template yes no)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((if-true (proof-proof-if-true proof value))
         (yes (b1-xdoc-types-by-value-restore proof yes if-true template))
         (if-false (proof-proof-if-false proof value))
         (no (b1-xdoc-types-by-value-restore proof no if-false template)))
      (proof-proof-cases proof (cadr value) yes no))))

(defun b1-xdoc-types-coerced-string (lib value)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((axiom (proof-proof-fact proof "stringp-coerce"
                                  (seq-zip (list *library-x* *library-y*) (cdr value))))
         (test (b1-xdoc-types-step-argument axiom 1))
         (typed (b1-logic-bookproof-normalize-proof lib test nil (list *proof-not*) nil nil)))
      (proof-proof-modus-ponens proof axiom typed))))

(mutual-recursion
 (defun b1-xdoc-types-string-value (n lib value evidence)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "b1-xdoc-types-string-value"))
         ((proof-is-call value *b1-printing-coerce*) (b1-xdoc-types-coerced-string lib value))
         (t (proof-with-checked-results ((head (proof-term-at value 0)))
              (if (member-equal head *b1-xdoc-types-string-constructors*)
                  (b1-xdoc-types-string-branches (1- n) lib value evidence)
                (b1-logic-bookproof-normalize-proof lib (list *b1-logic-stringp* value)
                                                    evidence nil nil nil))))))
 (defun b1-xdoc-types-string-branches (n lib call evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-xdoc-types-string-branches")
     (proof-with-checked-results
         ((head (proof-term-at call 0))
          (opened (b1-logic-bookproof-normalize
                   lib call evidence (list head *b1-logic-endp* *b1-logic-atom* *proof-not*)
                   nil nil nil t))
          (value (b1-xdoc-types-step-argument opened 2))
          (result (b1-xdoc-types-by-value (1- n) lib value (list *b1-logic-stringp* *proof-result*)
                                         nil (list :string evidence))))
       (library-library-transport-argument (cdr result) (car result) opened 1))))
 (defun b1-xdoc-types-string-branches-leaf (n value tests lib evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-xdoc-types-string-branches-leaf")
     (proof-with-checked-results ((cases (b1-xdoc-types-evidence-from-cases lib tests)))
       (b1-xdoc-types-string-value (1- n) lib value (append evidence cases)))))
 (defun b1-xdoc-types-mv-string-result-leaf (n items tests lib position)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-xdoc-types-mv-string-result-leaf")
     (proof-with-checked-results
         ((opened (b1-logic-bookproof-normalize lib items nil nil nil nil nil nil))
          (reduced (b1-structures-project-mv lib (list *b1-structures-mv-nth* position items) opened))
          (value (b1-xdoc-types-step-argument reduced 2))
          (evidence (b1-xdoc-types-evidence-from-cases lib tests))
          (typed (b1-xdoc-types-string-value (1- n) lib value evidence)))
       (library-library-transport-argument lib typed reduced 1))))
 (defun b1-xdoc-types-escaped-list-type-step-consequence-supported (n value lib predicate head child)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "b1-xdoc-types-escaped-list-type-step-consequence-supported"))
         ((equal predicate *b1-printing-characters*)
          (b1-printing-character-list lib value (list head child)))
         (t
          (proof-with-checked-results ((known (b1-xdoc-types-step-argument child 1)))
            (if (equal value known)
                (cons child lib)
              (proof-with-checked-results
                  ((first (proof-term-at value 1))
                   (element (b1-xdoc-types-string-value (1- n) lib first (list head)))
                   (tail (proof-term-at value 2))
                   (result (b1-xdoc-types-escaped-list-type-step-consequence-supported
                            (1- n) tail lib predicate head child))
                   (lib (cdr result))
                   (opened (b1-revappend-open-list lib (list predicate value) (list element)))
                   (step (proof-proof-transport (library-library-proof lib) (car result) opened)))
                (cons step lib)))))))
 (defun b1-xdoc-types-by-value-leaf (n lib value template tests leaf)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-xdoc-types-by-value-leaf")
     (proof-with-checked-results
         ((result (case (car leaf)
                    (:string
                     (proof-with-checked-results
                         ((step (b1-xdoc-types-string-branches-leaf (1- n) value tests lib (cadr leaf))))
                       (cons step lib)))
                    (:projection
                     (proof-with-checked-results
                         ((step (b1-xdoc-types-mv-string-result-leaf (1- n) value tests lib (cadr leaf))))
                       (cons step lib)))
                    (otherwise
                     (b1-xdoc-types-escaped-list-type-step-consequence-supported
                      (1- n) value lib (cadr leaf) (caddr leaf) (cadddr leaf)))))
          (claim (proof-step-first (car result)))
          (expected (proof-subst template (list (cons *proof-result* value)))))
       (if (equal claim expected)
           result
         '(:failure "failure" "")))))
 (defun b1-xdoc-types-by-value (n lib value template tests leaf)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "b1-xdoc-types-by-value"))
    ((proof-is-call value *proof-if*)
     (proof-with-checked-results
         ((branches (proof-list-of-length (cdr value) 3))
          (test (car branches))
          (yes (b1-xdoc-types-by-value (1- n) lib (cadr branches) template
                                      (append tests (list (list test t))) leaf))
          (no (b1-xdoc-types-by-value (1- n) (cdr yes) (caddr branches) template
                                     (append tests (list (list test nil))) leaf))
          (step (b1-xdoc-types-by-value-cases (cdr no) value template (car yes) (car no))))
       (cons step (cdr no))))
    ((and (proof-compound value) (endp value))
     '(:failure "failure" ""))
    ((and (proof-compound value) (proof-compound (car value)))
     (proof-with-checked-results
         ((equality (proof-proof-beta (library-library-proof lib) value))
          (opened (b1-xdoc-types-step-argument equality 2))
          (result (b1-xdoc-types-by-value (1- n) lib opened template tests leaf))
          (step (b1-xdoc-types-by-value-restore (library-library-proof (cdr result))
                                               (car result) equality template)))
       (cons step (cdr result))))
    (t (b1-xdoc-types-by-value-leaf (1- n) lib value template tests leaf)))))

(defun b1-xdoc-types-string-result-consequence (premise lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((source (proof-step-first premise))
         (items (proof-term-at source 1))
         (driver (list *proof-consp* items))
         (cons (proof-proof-assume proof driver t))
         (atom (proof-proof-assume proof driver nil))
         (opened (b1-revappend-open-list lib source (list cons)))
         (rewritten (proof-proof-rewrite proof premise opened (list 1)))
         (parts (proof-proof-conjunct proof rewritten))
         (goal (proof-term-at formula 2))
         (call (proof-term-at goal 1))
         (yes (b1-xdoc-types-string-branches 1000000 lib call (list cons (car parts))))
         (no (b1-xdoc-types-string-branches 1000000 lib call (list atom))))
      (proof-proof-cases proof driver yes no))))

(defun b1-xdoc-types-string-result (lib formula)
  (if (proof-is-call formula *library-implies*)
      (proof-with-checked-results
          ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
           (step (b1-xdoc-types-string-result-consequence premise lib formula)))
        (b1-logic-bookproof-prove-implication-with-premise lib formula premise step))
    (proof-with-checked-results ((call (proof-term-at formula 1)))
      (b1-xdoc-types-string-branches 1000000 lib call nil))))

(defun b1-xdoc-types-mv-string-result (lib formula)
  (let ((proof (library-library-proof lib))
        (implication (proof-is-call formula *library-implies*)))
    (proof-with-checked-results
        ((claim (if implication (proof-term-at formula 2) formula))
         (selector (proof-term-at claim 1))
         (call (proof-term-at selector 2))
         (head (proof-term-at call 0))
         (opened (b1-logic-bookproof-normalize lib call nil (list head) nil nil nil t))
         (position (proof-term-at selector 1))
         (template (list *b1-logic-stringp* (list *b1-structures-mv-nth* position *proof-result*)))
         (value (b1-xdoc-types-step-argument opened 2))
         (result (b1-xdoc-types-by-value 1000000 lib value template nil (list :projection position)))
         (step (b1-xdoc-types-by-value-restore proof (car result) opened template)))
      (if implication (b1-logic-bookproof-prove-implication lib formula step) step))))

(defun b1-xdoc-types-escaped-list-type-base-consequence (premise lib predicate call atom)
  (declare (ignore premise))
  (proof-with-checked-results
      ((opened (b1-revappend-open-list lib call (list atom)))
       (value (b1-logic-bookproof-normalize-proof
               lib (list predicate *proof-false*) nil
               (list predicate *b1-logic-atom* *b1-logic-eq* *proof-not*) nil nil)))
    (library-library-transport-argument lib value opened 1)))

(defun b1-xdoc-types-escaped-list-type-base (atom lib formula predicate call)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (step (b1-xdoc-types-escaped-list-type-base-consequence premise lib predicate call atom)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise step)))

(defun b1-xdoc-types-escaped-list-type-step-consequence (premise lib source predicate call cons induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((checked (b1-revappend-open-list lib source (list cons)))
         (rewritten (proof-proof-rewrite proof premise checked (list 1)))
         (parts (proof-proof-conjunct proof rewritten))
         (child (proof-proof-modus-ponens proof induction (cadr parts)))
         (opened (b1-revappend-open-list lib call (list cons)))
         (value (b1-xdoc-types-step-argument opened 2))
         (result (b1-xdoc-types-by-value 1000000 lib value (list predicate *proof-result*) nil
                                        (list :escaped predicate (car parts) child)))
         (lib (cdr result))
         (step (library-library-transport-argument lib (car result) opened 1)))
      (cons step lib))))

(defun b1-xdoc-types-escaped-list-type-step (cons induction lib formula source predicate call)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (result (b1-xdoc-types-escaped-list-type-step-consequence premise lib source predicate call cons induction))
       (step (b1-logic-bookproof-prove-implication-with-premise (cdr result) formula premise (car result))))
    (cons step (cdr result))))

(defun b1-xdoc-types-escaped-list-type (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (goal (proof-list-of-length (caddr implication) 2))
       (source (proof-list-of-length (cadr implication) 2))
       (xs (cadr source))
       (predicate (car goal))
       (call (cadr goal))
       (preparation (b1-revappend-list-induction-prepare lib formula xs nil))
       (result (b1-xdoc-types-escaped-list-type-step
                (caddr preparation) (cadddr preparation) lib formula source predicate call))
       (lib (cdr result))
       (atom (proof-proof-assume (library-library-proof lib) (cadr preparation) nil))
       (base (b1-xdoc-types-escaped-list-type-base atom lib formula predicate call))
       (preparation (cons (b1-induction-tree-induction-with-lib (car preparation) lib) (cdr preparation)))
       (step (b1-revappend-list-induction lib preparation base (car result))))
    (cons step lib)))

(defun b1-xdoc-types-find-claim (goal facts)
  (if (endp facts)
      nil
    (proof-with-checked-results ((literal (proof-step-first (car facts))))
      (if (equal literal goal)
          (car facts)
        (b1-xdoc-types-find-claim goal (cdr facts))))))

(defund b1-xdoc-types-partition-macro-args-open-value (lib value)
  (proof-with-checked-results
      ((view (b1-logic-bookproof-normalize lib value nil (list *b1-xdoc-types-acons*) nil nil nil nil))
       (pair (b1-xdoc-types-step-argument view 2))
       (tail (proof-term-at pair 2)))
    (list view pair tail)))

(defun b1-xdoc-types-partition-macro-args-type-value (n value predicate facts lib)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "b1-xdoc-types-partition-macro-args-type-value")
    (let ((goal (list predicate value)))
      (proof-with-checked-results ((known (b1-xdoc-types-find-claim goal facts)))
        (cond
         (known known)
         ((equal value *proof-false*)
          (b1-logic-bookproof-normalize-proof lib goal nil
           (list predicate *b1-logic-atom* *b1-logic-eq* *proof-not*) nil nil))
         (t
          (proof-with-checked-results
              ((parts (b1-xdoc-types-partition-macro-args-open-value lib value))
               (child (b1-xdoc-types-partition-macro-args-type-value (1- n) (caddr parts) predicate facts lib))
               (pair (cadr parts))
               (evidence (if (equal predicate *b1-xdoc-types-alistp*)
                             (proof-with-checked-results
                                 ((head (proof-term-at pair 1))
                                  (step (b1-revappend-cons-value lib head)))
                               (list step))
                           nil))
               (opened (b1-revappend-open-list lib (list predicate pair) evidence))
               (resolved (proof-proof-transport (library-library-proof lib) child opened)))
            (library-library-transport-argument lib resolved (car parts) 1))))))))

(defun b1-xdoc-types-partition-macro-args-field (lib call opened facts position predicate)
  (proof-with-checked-results
      ((selected (b1-structures-project-mv lib (list *b1-structures-mv-nth* position call) opened))
       (value (b1-xdoc-types-step-argument selected 2))
       (known (b1-xdoc-types-partition-macro-args-type-value 1000000 value predicate facts lib)))
    (library-library-transport-argument lib known selected 1)))

(defun b1-xdoc-types-partition-macro-args-branch (evidence child lib call claim)
  (proof-with-checked-results
      ((head (proof-term-at call 0))
       (opened (b1-logic-bookproof-normalize lib call evidence
                (list head *b1-logic-atom* *b1-logic-endp* *proof-not*) nil nil nil nil))
       (facts (if child (proof-proof-conjunct (library-library-proof lib) child) nil))
       (proper (b1-xdoc-types-partition-macro-args-field lib call opened facts *proof-zero*
                                                        *b1-printing-true-listp*))
       (alist (b1-xdoc-types-partition-macro-args-field lib call opened facts *proof-one*
                                                       *b1-xdoc-types-alistp*)))
    (b1-logic-bookproof-normalize-proof lib claim (list proper alist) nil nil nil)))

(defun b1-xdoc-types-partition-macro-args-lemma (lib call xs)
  (let* ((proof (library-library-proof lib))
         (proper (list *b1-printing-true-listp* (list *b1-structures-mv-nth* *proof-zero* call)))
         (alist (list *b1-xdoc-types-alistp* (list *b1-structures-mv-nth* *proof-one* call)))
         (claim (proof-ite proper alist *proof-false*))
         (driver (list *proof-consp* xs))
         (keyword (list *b1-xdoc-types-keywordp* (list *library-car* xs)))
         (tail (list *library-cdr* xs))
         (tail-test (list *proof-consp* tail))
         (driver-tests (list (list driver t)))
         (induction (b1-induction-tree-induction-init lib claim xs)))
    (proof-with-checked-results
        ((cons (proof-proof-assume proof driver t))
         (atom (proof-proof-assume proof driver nil))
         (child (b1-induction-tree-induction-hypothesis induction (list (cons xs tail)) driver-tests))
         (two-cells (b1-induction-tree-induction-hypothesis
                     (cdr child) (list (cons xs (list *library-cdr* tail)))
                     (append driver-tests (list (list tail-test t)))))
         (no-key (proof-proof-assume proof keyword nil))
         (ordinary (b1-xdoc-types-partition-macro-args-branch (list cons no-key) (car child) lib call claim))
         (with-key (proof-proof-assume proof keyword t))
         (with-tail (proof-proof-assume proof tail-test t))
         (bound (b1-xdoc-types-partition-macro-args-branch
                 (list cons with-key with-tail) (car two-cells) lib call claim))
         (no-tail (proof-proof-assume proof tail-test nil))
         (incomplete (b1-xdoc-types-partition-macro-args-branch (list cons with-key no-tail) nil lib call claim))
         (keyed (proof-proof-cases proof tail-test bound incomplete))
         (step (proof-proof-cases proof keyword keyed ordinary))
         (empty (b1-xdoc-types-partition-macro-args-branch (list atom) nil lib call claim))
         (cases (proof-proof-cases proof driver step empty))
         (step (b1-induction-tree-induction-finish (cdr two-cells) cases)))
      (library-library-lemma lib "PARTITION-MACRO-ARGS-TYPES" claim step nil))))

(defun b1-xdoc-types-partition-macro-args (lib formula)
  (let ((name (proof-sym "SELF-PARTITION-MACRO-ARGS-TYPES" "ACL2")))
    (proof-with-checked-results
        ((outer (proof-list-of-length formula 2))
         (selector (proof-list-of-length (cadr outer) 3))
         (call (proof-list-of-length (caddr selector) 3))
         (lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (b1-xdoc-types-partition-macro-args-lemma lib call (cadr call))))
         (proof (library-library-proof lib))
         (fact (proof-proof-fact proof name nil))
         (proper (b1-xdoc-types-step-argument fact 1))
         (projection (proof-term-at proper 1))
         (original (proof-term-at projection 2))
         (theorem (proof-proof-fact proof name (seq-zip (cdr original) (cdr call))))
         (parts (proof-proof-conjunct proof theorem))
         (step (b1-xdoc-types-find-claim formula parts)))
      (if step (cons step lib) '(:failure "failure" "")))))
