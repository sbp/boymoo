(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-xdoc-acons* (proof-cl "ACONS"))
(defconst *b2-xdoc-keywordp* (proof-cl "KEYWORDP"))
(defconst *b2-xdoc-stringp* (proof-cl "STRINGP"))
(defconst *b2-xdoc-coerce* (proof-cl "COERCE"))
(defconst *b2-xdoc-append-str* (proof-sym "STRING-APPEND" "ACL2"))
(defconst *b2-xdoc-append-strs* (proof-sym "STRING-APPEND-LST" "ACL2"))
(defconst *b2-xdoc-treep* (proof-sym "TREEP" "XDOC"))
(defconst *b2-xdoc-trees* (proof-sym "TREE-LISTP" "XDOC"))
(defconst *b2-xdoc-tree-tag* (proof-sym "TREE-TAGP" "XDOC"))
(defconst *b2-xdoc-cons-tree* (proof-sym "TREEP-OF-CONS" "XDOC"))
(defconst *b2-xdoc-make-tag* (proof-sym "MAKE-TREE-TAG" "XDOC"))
(defconst *b2-xdoc-list-true* (proof-sym "TRUE-LISTP-WHEN-TREE-LISTP" "XDOC"))
(defconst *b2-xdoc-tag-left*
  (proof-sym "STRINGP-OF-MV-NTH-0-KEYWORD-OR-TREE-TAG-TO-STRINGS" "XDOC"))
(defconst *b2-xdoc-tag-right*
  (proof-sym "STRINGP-OF-MV-NTH-1-KEYWORD-OR-TREE-TAG-TO-STRINGS" "XDOC"))
(defconst *b2-xdoc-partition-types*
  (list (proof-sym "ALISTP-OF-MV-NTH-1-PARTITION-MACRO-ARGS" "XDOC")
        (proof-sym "TRUE-LISTP-OF-MV-NTH-0-PARTITION-MACRO-ARGS" "XDOC")))
(defconst *b2-xdoc-xdoc-theorems*
  (list (car *b2-xdoc-partition-types*)
        (proof-sym "STRINGP-OF-DESC-THINGS-TO-STRING" "XDOC")
        *b2-xdoc-tag-left* *b2-xdoc-tag-right* *b2-xdoc-cons-tree*
        (proof-sym "TREEP-OF-MAKE-TREE-TAG" "XDOC")
        (cadr *b2-xdoc-partition-types*)))

(defun b2-xdoc-right (step)
  (if (null step)
      '(:failure "failure" "")
    (proof-with-checked-results ((first (proof-step-first step)))
      (proof-term-at first 2))))

(defun b2-xdoc-cons-type (library datum)
  (proof-with-checked-results
      ((head (proof-term-at datum 1))
       (tail (proof-term-at datum 2)))
    (proof-proof-fact (library-library-proof library) "consp-cons"
                      (list (list *library-x* head) (list *library-y* tail)))))

(defun b2-xdoc-cons-excludes (library predicate datum)
  (proof-with-checked-results ((spelling (proof-term-at predicate 2)))
    (if (not (stringp spelling))
        '(:failure "failure" "")
      (let ((proof (library-library-proof library))
            (name (concatenate 'string "consp-not-" (text-lower spelling))))
        (proof-with-checked-results
            ((conditional (proof-proof-fact proof name (list (list *library-x* datum))))
             (cons-step (b2-xdoc-cons-type library datum)))
          (proof-proof-modus-ponens proof conditional cons-step))))))

(defun b2-xdoc-argument-partition-hypothesis (library rest measure bindings formula cons-step)
  (proof-with-checked-results
      ((rulers (b2-measures-rulers-init library (list cons-step)))
       (smaller (b2-measures-rulers-selector-decrease
                 library (list *proof-ordinal-less* (list *library-count* rest) measure) rulers)))
    (b2-tactics-tactics-induction-hypothesis library formula measure bindings (car smaller))))

(defun b2-xdoc-argument-partition-prove-leaf (evidence library call index predicate)
  (proof-with-checked-results
      ((opened (b2-tactics-tactics-normalize library call evidence
                                             (list call *b2-xdoc-acons*) nil 1500 nil))
       (projection (if opened (b2-projections-projected-value library index opened evidence)
                     (b2-xdoc-right opened)))
       (library (cdr projection))
       (rhs (b2-xdoc-right (car projection)))
       (result (list predicate rhs))
       (translated (b2-tactics-tactics-solve library result evidence (list result) nil 0 nil))
       (step (library-library-transport-argument library translated (car projection) 1)))
    (cons step library)))

(defun b2-xdoc-argument-partition (library formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 2))
       (predicate (car parts))
       (projection (proof-list-of-length (cadr parts) 3))
       (quoted (proof-list-of-length (cadr projection) 2))
       (index (cadr quoted))
       (call (caddr projection))
       (application (proof-list-of-length call 3))
       (args (cadr application))
       (tail (list *library-cdr* args))
       (deeper (list *library-cdr* tail))
       (test (list *proof-consp* args))
       (signed (b2-bags-signed library test))
       (cons-step (car signed))
       (atom-step (cadr signed))
       (measure (list *library-count* args))
       (tail-bindings (list (list args tail)))
       (deeper-bindings (list (list args deeper)))
       (tail-hypothesis (b2-xdoc-argument-partition-hypothesis
                         library tail measure tail-bindings formula cons-step))
       (deeper-hypothesis (b2-xdoc-argument-partition-hypothesis
                           library deeper measure deeper-bindings formula cons-step))
       (key (list *b2-xdoc-keywordp* (list *library-car* args)))
       (key-signed (b2-bags-signed library key))
       (second (list *proof-consp* tail))
       (second-signed (b2-bags-signed library second))
       (taken (b2-xdoc-argument-partition-prove-leaf
               (list cons-step (car key-signed) (car second-signed) deeper-hypothesis)
               library call index predicate))
       (malformed (b2-xdoc-argument-partition-prove-leaf
                   (list cons-step (car key-signed) (cadr second-signed))
                   (cdr taken) call index predicate))
       (positional (b2-xdoc-argument-partition-prove-leaf
                    (list cons-step (cadr key-signed) tail-hypothesis)
                    (cdr malformed) call index predicate))
       (library (cdr positional))
       (proof (library-library-proof library))
       (key-case (proof-proof-cases proof second (car taken) (car malformed)))
       (cons-case (proof-proof-cases proof key key-case (car positional)))
       (atom-case (b2-xdoc-argument-partition-prove-leaf
                   (list atom-step) library call index predicate))
       (library (cdr atom-case))
       (proof (library-library-proof library))
       (ordered (proof-proof-cases proof test cons-case (car atom-case)))
       (ordinal (library-library-builtin library 1 args))
       (step (proof-proof-induct proof ordinal ordered formula measure
                                 (list tail-bindings deeper-bindings))))
    (cons step library)))

(defun b2-xdoc-trees-cons (library formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (call (cadr parts))
       (datum (proof-term-at call 1))
       (tail (proof-term-at datum 2))
       (typed (list *b2-xdoc-trees* tail))
       (signed (b2-bags-signed library typed))
       (nonstring (b2-xdoc-cons-excludes library *b2-xdoc-stringp* datum))
       (proper (b2-tactics-tactics-use-fact
                library *b2-xdoc-list-true*
                (list *b2-list-properties-true-list* tail) (list (car signed)) nil nil 0 nil))
       (opens (list call (list *b2-list-properties-true-list* datum)))
       (good (b2-tactics-tactics-solve library formula (list nonstring (car signed) proper)
                                      opens nil 3 t))
       (bad (b2-tactics-tactics-solve library formula (list nonstring (cadr signed))
                                     opens nil 3 t)))
    (proof-proof-cases (library-library-proof library) typed good bad)))

(defun b2-xdoc-make-tree-tag-establish
    (facts library formula nonsymbol openers construction cons-case)
  (b2-tactics-tactics-solve library formula (cons nonsymbol facts)
                           openers (list construction cons-case) 0 t))

(defun b2-xdoc-make-tree-tag (library formula)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (argument (proof-term-at (cadr parts) 1))
         (construction (proof-proof-unfold proof argument))
         (pair (b2-xdoc-right construction))
         (clause (let ((found (assoc-equal *b2-xdoc-cons-tree* (proof-proof-facts proof))))
                   (if found (cdr found)
                     '(:failure "tactic-rejected" ""))))
         (literal (proof-term-at clause 0))
         (pattern (proof-term-at literal 1))
         (cons-case (b2-tactics-tactics-exact
                     library *b2-xdoc-cons-tree* pattern (list *b2-xdoc-treep* pair)))
         (head (proof-term-at pair 1))
         (nonsymbol (b2-xdoc-cons-excludes library *b2-tactics-symbolp* head))
         (openers (list (list *b2-xdoc-keywordp* head) (list *b2-xdoc-tree-tag* head)))
         (expected (caddr parts))
         (key (proof-term-at expected 1))
         (expected-tail (proof-term-at expected 2))
         (attributes (proof-term-at expected-tail 1))
         (key-signed (b2-bags-signed library key))
         (attributes-signed (b2-bags-signed library attributes))
         (valid (b2-xdoc-make-tree-tag-establish
                 (list (car key-signed) (car attributes-signed))
                 library formula nonsymbol openers construction cons-case))
         (invalid (b2-xdoc-make-tree-tag-establish
                   (list (car key-signed) (cadr attributes-signed))
                   library formula nonsymbol openers construction cons-case))
         (present (proof-proof-cases proof attributes valid invalid))
         (missing (b2-xdoc-make-tree-tag-establish
                   (list (cadr key-signed)) library formula nonsymbol openers construction cons-case)))
      (proof-proof-cases proof key present missing))))

(defun b2-xdoc-assumptions (proof tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((test (proof-list-of-length (car tests) 2))
         (assumption (proof-proof-assume proof (car test) (cadr test)))
         (rest (b2-xdoc-assumptions proof (cdr tests))))
      (cons assumption rest))))

(mutual-recursion
 (defun b2-xdoc-string-result (n library value evidence)
   (declare (xargs :measure (nfix n)))
   (let ((goal (list *b2-xdoc-stringp* value))
         (proof (library-library-proof library)))
     (cond
      ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-xdoc-string-result"))
      ((proof-is-call value *proof-quote*)
       (proof-with-checked-results
           ((step (b2-tactics-tactics-solve library goal evidence nil nil 0 nil)))
         (cons step library)))
      ((proof-is-call value *b2-xdoc-coerce*)
       (proof-with-checked-results
           ((step (b2-tactics-tactics-use-fact
                   library '("str" "stringp-coerce") goal evidence nil nil 0 nil)))
         (cons step library)))
      ((proof-is-call value *b2-xdoc-append-str*)
       (proof-with-checked-results
           ((equation (b2-tactics-tactics-normalize library value evidence
                                                    (list value) nil 1500 nil))
            (rhs (b2-xdoc-right equation))
            (result (b2-xdoc-string-result (1- n) library rhs evidence))
            (library (cdr result))
            (step (library-library-transport-argument library (car result) equation 1)))
         (cons step library)))
      ((proof-is-call value *b2-xdoc-append-strs*)
       (let ((name (proof-sym "B2-STRINGP-STRING-APPEND-LST" "ACL2")))
         (proof-with-checked-results
             ((installed
               (if (assoc-equal name (proof-proof-facts proof))
                   (cons name library)
                 (let ((call (list *b2-xdoc-append-strs* *library-x*))
                       (template (list *b2-xdoc-stringp* *proof-result*)))
                   (proof-with-checked-results
                       ((equation (b2-tactics-tactics-normalize
                                   library call nil (list call) nil 1500 t))
                        (rhs (b2-xdoc-right equation))
                        (proved (b2-xdoc-string-result-by-value
                                 (1- n) library rhs template nil :none))
                        (library (cdr proved))
                        (proof (library-library-proof library))
                        (reverse (proof-proof-symmetric proof equation))
                        (support (proof-proof-rewrite-result proof (car proved) reverse
                                                             template *proof-result*)))
                     (b2-tactics-tactics-add-lemma library "STRINGP-STRING-APPEND-LST" support :none)))))
              (library (cdr installed))
              (argument (proof-term-at value 1))
              (step (proof-proof-fact (library-library-proof library) name
                                      (list (list *library-x* argument)))))
           (cons step library))))
      (t
       (proof-with-checked-results
           ((step (b2-tactics-tactics-solve library goal evidence nil nil 0 nil)))
         (cons step library))))))

 (defun b2-xdoc-string-result-by-value (n library value template tests index)
   (declare (xargs :measure (nfix n)))
   (let ((proof (library-library-proof library)))
     (cond
      ((not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-xdoc-string-result-by-value"))
      ((proof-is-call value *proof-if*)
       (proof-with-checked-results
           ((parts (proof-list-of-length (cdr value) 3))
            (test (car parts))
            (yes (b2-xdoc-string-result-by-value
                  (1- n) library (cadr parts) template (append tests (list (list test t))) index))
            (no (b2-xdoc-string-result-by-value
                 (1- n) (cdr yes) (caddr parts) template (append tests (list (list test nil))) index))
            (library (cdr no))
            (step (proof-by-value-join (library-library-proof library)
                                       value template (car yes) (car no))))
         (cons step library)))
      ((and (proof-compound value) (endp value))
       '(:failure "tactic-rejected" ""))
      ((and (proof-compound value) (proof-compound (car value)))
       (proof-with-checked-results
           ((equality (proof-proof-beta proof value))
            (opened (b2-xdoc-right equality))
            (result (b2-xdoc-string-result-by-value (1- n) library opened template tests index))
            (library (cdr result))
            (proof (library-library-proof library))
            (reverse (proof-proof-symmetric proof equality))
            (step (proof-proof-rewrite-result proof (car result) reverse template *proof-result*)))
         (cons step library)))
      (t
       (proof-with-checked-results
           ((result (if (eq index :none)
                        (b2-xdoc-string-result (1- n) library value nil)
                      (b2-xdoc-tag-strings-leaf (1- n) value tests library index)))
            (first (proof-step-first (car result)))
            (target (proof-subst template (list (cons *proof-result* value)))))
         (if (equal first target) result '(:failure "tactic-rejected" "")))))))

 (defun b2-xdoc-tag-strings-leaf (n value tests library index)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-xdoc-tag-strings-leaf")
     (proof-with-checked-results
         ((evidence (b2-xdoc-assumptions (library-library-proof library) tests))
          (field (b2-projections-mv-nth library index value))
          (library (cdr field))
          (rhs (b2-xdoc-right (car field)))
          (normalized (b2-tactics-tactics-normalize library rhs evidence nil nil 1500 nil))
          (opened (proof-proof-chain (library-library-proof library) (car field) (list normalized)))
          (rhs (b2-xdoc-right opened))
          (result (b2-xdoc-string-result (1- n) library rhs evidence))
          (library (cdr result))
          (step (library-library-transport-argument library (car result) opened 1)))
       (cons step library)))))

(defun b2-xdoc-tag-strings (library formula)
  (let ((conditional (proof-is-call formula *library-implies*)))
    (proof-with-checked-results
        ((condition (if conditional (proof-term-at formula 1) :none))
         (goal (if conditional (proof-term-at formula 2) formula))
         (parts (proof-list-of-length goal 2))
         (projection (proof-list-of-length (cadr parts) 3))
         (quoted (proof-list-of-length (cadr projection) 2))
         (index (cadr quoted))
         (call (caddr projection))
         (body (b2-tactics-tactics-normalize library call nil (list call) nil 1100 t))
         (template (list *b2-xdoc-stringp*
                         (list *b2-projections-mv-nth* (proof-quote index) *proof-result*)))
         (rhs (b2-xdoc-right body))
         (proved (b2-xdoc-string-result-by-value 1000000 library rhs template nil index))
         (library (cdr proved))
         (proof (library-library-proof library))
         (reverse (proof-proof-symmetric proof body))
         (actual (proof-proof-rewrite-result proof (car proved) reverse template *proof-result*)))
      (if conditional
          (b2-tactics-tactics-implication library condition goal (cons actual library))
        (cons actual library)))))

(defun b2-xdoc-description-branch (library call evidence)
  (proof-with-checked-results
      ((equation (b2-tactics-tactics-normalize library call evidence (list call) nil 1500 nil))
       (rhs (b2-xdoc-right equation))
       (proved (b2-xdoc-string-result 1000000 library rhs evidence))
       (library (cdr proved))
       (step (library-library-transport-argument library (car proved) equation 1)))
    (cons step library)))

(defun b2-xdoc-description-consequent
    (premise library condition call test has-tail cons-step atom-step longer single)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((head-equality (b2-tactics-tactics-normalize
                         library condition (list cons-step) (list condition) nil 1500 nil))
         (rewritten (if head-equality (proof-proof-rewrite proof premise head-equality '(1))
                      (b2-xdoc-right head-equality)))
         (tidied (proof-proof-tidy proof rewritten))
         (parts (proof-proof-conjunct proof tidied))
         (many (b2-xdoc-description-branch library call (list cons-step longer)))
         (one (b2-xdoc-description-branch (cdr many) call (list cons-step single (car parts))))
         (empty (b2-xdoc-description-branch (cdr one) call (list atom-step)))
         (library (cdr empty))
         (proof (library-library-proof library))
         (nonempty (proof-proof-cases proof has-tail (car many) (car one)))
         (step (proof-proof-cases proof test nonempty (car empty))))
      (cons step library))))

(defun b2-xdoc-description (library formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (condition (cadr parts))
       (goal (caddr parts))
       (call (proof-term-at goal 1))
       (application (proof-list-of-length call 2))
       (elements (cadr application))
       (test (list *proof-consp* elements))
       (signed (b2-bags-signed library test))
       (has-tail (list *proof-consp* (list *library-cdr* elements)))
       (tail-signed (b2-bags-signed library has-tail))
       (request (b2-tactics-tactics-implication library condition goal nil))
       (reply (b2-xdoc-description-consequent
               (nth 3 (car request)) (cdr request) condition call test has-tail
               (car signed) (cadr signed) (car tail-signed) (cadr tail-signed))))
    (b2-tactics-tactics-implication library condition goal reply)))

(defun b2-xdoc-xdoc-theorem (library name formula)
  (cond
   ((member-equal name *b2-xdoc-partition-types*)
    (b2-xdoc-argument-partition library formula))
   ((equal name *b2-xdoc-cons-tree*)
    (proof-with-checked-results ((step (b2-xdoc-trees-cons library formula)))
      (cons step library)))
   ((equal name (proof-sym "TREEP-OF-MAKE-TREE-TAG" "XDOC"))
    (proof-with-checked-results ((step (b2-xdoc-make-tree-tag library formula)))
      (cons step library)))
   ((member-equal name (list *b2-xdoc-tag-left* *b2-xdoc-tag-right*))
    (b2-xdoc-tag-strings library formula))
   (t (b2-xdoc-description library formula))))
