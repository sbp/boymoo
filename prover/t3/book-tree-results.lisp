(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-tree-results-tree* (proof-sym "TREEP" "XDOC"))
(defconst *t3-book-tree-results-tree-list* (proof-sym "TREE-LISTP" "XDOC"))
(defconst *t3-book-tree-results-tree-tag* (proof-sym "TREE-TAGP" "XDOC"))
(defconst *t3-book-tree-results-make-tag* (proof-sym "MAKE-TREE-TAG" "XDOC"))
(defconst *t3-book-tree-results-cons-rule* (proof-sym "TREEP-OF-CONS" "XDOC"))
(defconst *t3-book-tree-results-tag-rule* (proof-sym "TREEP-OF-MAKE-TREE-TAG" "XDOC"))
(defconst *t3-book-tree-results-keywordp* (proof-cl "KEYWORDP"))
(defconst *t3-book-tree-results-symbolp* (proof-cl "SYMBOLP"))
(defconst *t3-book-tree-results-pseudo-event* (proof-sym "PSEUDO-EVENT-FORMP" "ACL2"))

(defun t3-book-tree-results-identical-branches (lib value)
  (if (not (proof-is-call value *proof-if*))
      '(:failure "failure" "")
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
       ((yes-term (proof-term-at value 2))
        (no-term (proof-term-at value 3)))
       (if (not (equal yes-term no-term))
           '(:failure "failure" "")
         (proof-with-checked-results
          ((yes (proof-proof-if-true proof value))
           (no (proof-proof-if-false proof value)))
          (proof-proof-cases proof (cadr value) yes no)))))))

(defun t3-book-tree-results-tree-cons (lib formula)
  (let ((proof (library-library-proof lib))
        (formals (list *library-x* *library-y*)))
    (proof-with-checked-results
     ((sides (proof-list-of-length (cdr formula) 2))
      (value (proof-term-at (car sides) 1))
      (present (proof-proof-fact proof "consp-cons" (seq-zip formals (cdr value))))
      (denies-string (proof-proof-fact proof "consp-not-stringp" (list (list *library-x* value))))
      (denies-string (proof-proof-modus-ponens proof denies-string present))
      (opened (t3-book-spines-shallow lib (car sides) (list denies-string)))
      (proper (t3-book-spines-shallow lib (list *t3-book-lemmas-true-listp* value) nil))
      (head (t3-logic-libraryproofs-constant lib (list *library-car* value)))
      (opened (t3-book-spines-replace-value lib opened (list proper head)))
      (opened-body (proof-rewritten-term opened))
      (branch (proof-term-at opened-body 2)))
     (if (not (equal branch (cadr sides)))
         nil
       (proof-with-checked-results
        ((tail (proof-term-at value 2))
         (recognized (list *t3-book-tree-results-tree-list* tail))
         (tail-proper (t3-book-lemmas-implies-proper-list
                       lib (list *library-implies* recognized
                                 (list *t3-book-lemmas-true-listp* tail)) nil)))
        (and tail-proper
          (proof-with-checked-results
           ((assumed (proof-proof-assume proof recognized t))
            (guarded (proof-proof-modus-ponens proof tail-proper assumed))
            (branch (proof-proof-select proof opened-body guarded))
            (yes (proof-proof-chain proof opened (list branch)))
            (denied (proof-proof-assume proof recognized nil))
            (empty (t3-book-lemmas-nil-value lib denied))
            (right (proof-proof-reflexive proof (cadr sides)))
            (no-result (t3-book-spines-replace-value lib right (list empty)))
            (right-body (proof-rewritten-term no-result))
            (branch (t3-book-tree-results-identical-branches lib right-body))
            (no-result (proof-proof-chain proof no-result (list branch)))
            (no (t3-book-spines-replace-value lib opened (list no-result)))
            (no-body (proof-rewritten-term no))
            (branch (t3-book-tree-results-identical-branches lib no-body))
            (reversed (proof-proof-symmetric proof no-result))
            (no (proof-proof-chain proof no (list branch reversed))))
           (proof-proof-cases proof recognized yes no))))))))

(defun t3-book-tree-results-boolean-branch (lib step)
  (proof-with-checked-results
   ((value (proof-rewritten-term step))
    (boolean (t3-logic-libraryproofs-prove lib (list *t3-book-lemmas-booleanp* value) nil
                                         (list *t3-book-lemmas-booleanp* (proof-cl "EQ")))))
   (library-library-transport-argument lib boolean step 1)))

(defun t3-book-tree-results-proper-list-boolean (lib)
  (let* ((proof (library-library-proof lib))
         (value (list *t3-book-lemmas-true-listp* *library-x*))
         (formula (list *t3-book-lemmas-booleanp* value))
         (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
     ((cons-case (proof-proof-assume proof test t))
      (first (t3-list-bounds-tail-hypothesis lib formula cons-case))
      (cons-body (t3-book-spines-shallow lib value (list cons-case)))
      (first (library-library-transport-argument lib first cons-body 1))
      (atom-case (proof-proof-assume proof test nil))
      (empty (t3-book-spines-shallow lib value (list atom-case)))
      (equality (proof-rewritten-term empty))
      (true-case (proof-proof-assume proof equality t))
      (true-case (t3-book-lemmas-true-equality lib true-case))
      (false-case (proof-proof-assume proof equality nil))
      (false-case (t3-book-lemmas-nil-value lib false-case))
      (yes (t3-book-tree-results-boolean-branch lib true-case))
      (no (t3-book-tree-results-boolean-branch lib false-case))
      (cases (proof-proof-cases proof equality yes no))
      (second (library-library-transport-argument lib cases empty 1))
      (induction (t3-list-bounds-tail-induction lib formula first second)))
     (library-library-lemma lib "T3-TRUE-LISTP-BOOLEAN" formula induction nil))))

(defun t3-book-tree-results-swap-boolean-tests-common-result
    (first-holds second-holds lib body first second reverse-term opened types)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((a (proof-proof-assume proof first first-holds))
      (b (proof-proof-assume proof second second-holds))
      (left (proof-proof-select proof body a))
      (right (proof-proof-select proof reverse-term b))
      (left (if first-holds
                (proof-with-checked-results
                 ((q (if second-holds
                         (proof-with-checked-results ((type (proof-term-at types 1)))
                           (library-library-cite lib "T3-BOOLEAN-TRUE" (list second) (list type b)))
                       (t3-book-lemmas-nil-value lib b))))
                 (proof-proof-chain proof left (list q)))
              left))
      (right (if second-holds
                 (proof-with-checked-results
                  ((p (if first-holds
                          (proof-with-checked-results ((type (proof-term-at types 0)))
                            (library-library-cite lib "T3-BOOLEAN-TRUE" (list first) (list type a)))
                        (t3-book-lemmas-nil-value lib a))))
                  (proof-proof-chain proof right (list p)))
               right))
      (reversed (proof-proof-symmetric proof right)))
     (proof-proof-chain proof opened (list left reversed)))))

(defun t3-book-tree-results-swap-boolean-tests-case
    (holds lib body first second reverse-term opened types)
  (proof-with-checked-results
   ((yes (t3-book-tree-results-swap-boolean-tests-common-result
          holds t lib body first second reverse-term opened types))
    (no (t3-book-tree-results-swap-boolean-tests-common-result
         holds nil lib body first second reverse-term opened types)))
   (proof-proof-cases (library-library-proof lib) second yes no)))

(defun t3-book-tree-results-swap-boolean-tests (lib opened types)
  (proof-with-checked-results
   ((body (proof-rewritten-term opened))
    (tests (proof-list-of-length (seq-slice body 1 3) 2)))
   (let* ((first (car tests))
          (second (cadr tests))
          (reverse-term (proof-ite second first *proof-false*)))
     (proof-with-checked-results
      ((yes (t3-book-tree-results-swap-boolean-tests-case
             t lib body first second reverse-term opened types))
       (no (t3-book-tree-results-swap-boolean-tests-case
            nil lib body first second reverse-term opened types)))
      (proof-proof-cases (library-library-proof lib) first yes no)))))

(defun t3-book-tree-results-event-cons (lib formula)
  (proof-with-checked-results
   ((left (and (proof-is-call formula *proof-equal*) (proof-term-at formula 1)))
    (value (and (proof-is-call left *t3-book-tree-results-pseudo-event*)
                (proof-term-at left 1))))
   (if (not (proof-is-call value *proof-cons*))
       (cons nil lib)
     (proof-with-checked-results
      ((args (proof-list-of-length (cdr value) 2))
       (opened (t3-book-spines-shallow lib left nil))
       (proper (t3-book-spines-shallow lib (list *t3-book-lemmas-true-listp* value) nil))
       (opened (t3-book-spines-replace-value lib opened (list proper)))
       (body (proof-rewritten-term opened)))
      (let ((head (car args))
            (tail (cadr args)))
        (if (not (equal body (proof-ite (list *t3-book-lemmas-true-listp* tail)
                                        (list *t3-book-tree-results-symbolp* head) *proof-false*)))
            (cons nil lib)
          (proof-with-checked-results
           ((lib (t3-book-tree-results-proper-list-boolean lib))
            (proper-type (library-library-cite lib "T3-TRUE-LISTP-BOOLEAN" (list tail) nil))
            (symbol-type (proof-proof-fact (library-library-proof lib) "booleanp-symbolp"
                                           (list (list *library-x* head))))
            (result (t3-book-tree-results-swap-boolean-tests lib opened (list proper-type symbol-type)))
            (claim (proof-step-first result)))
           (cons (and (equal claim formula) result) lib))))))))

(defun t3-book-tree-results-instantiate-constructor (lib name values)
  (let* ((proof (library-library-proof lib))
         (fact (assoc-equal name (proof-proof-facts proof))))
    (if (not fact)
        '(:failure "failure" "")
      (proof-with-checked-results
       ((literal (proof-term-at (cdr fact) 0))
        (left (proof-term-at literal 1))
        (value (proof-term-at left 1)))
       (proof-proof-fact proof name (seq-zip (cdr value) values))))))

(defun t3-book-tree-results-same-choice-branch (lib equation wanted test holds)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((assumed (proof-proof-assume proof test holds))
      (evidence (list assumed))
      (value (proof-rewritten-term equation))
      (first (t3-book-spines-constructor-form lib value evidence *t3-book-spines-guards*))
      (first (proof-proof-chain proof equation (list first)))
      (second (t3-book-spines-constructor-form lib wanted evidence *t3-book-spines-guards*))
      (second (or second (proof-proof-reflexive proof wanted)))
      (first-body (proof-rewritten-term first))
      (second-body (proof-rewritten-term second)))
   (and (equal first-body second-body)
       (proof-with-checked-results ((reversed (proof-proof-symmetric proof second)))
         (proof-proof-chain proof first (list reversed)))))))

(defun t3-book-tree-results-same-choice (lib equation wanted test)
  (proof-with-checked-results
   ((yes (t3-book-tree-results-same-choice-branch lib equation wanted test t)))
   (and yes
     (proof-with-checked-results
      ((no (t3-book-tree-results-same-choice-branch lib equation wanted test nil)))
      (and no (proof-proof-cases (library-library-proof lib) test yes no))))))

(defun t3-book-tree-results-tree-tag (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((sides (proof-list-of-length (cdr formula) 2))
      (call (proof-term-at (car sides) 1))
      (args (proof-list-of-length (cdr call) 3))
      (body (proof-proof-unfold proof call))
      (equation (proof-proof-reflexive proof (car sides)))
      (equation (proof-proof-rewrite proof equation body '(1 2 1)))
      (tag (car args))
      (head (list *proof-cons* tag (cadr args)))
      (constructor (t3-book-tree-results-instantiate-constructor
                    lib *t3-book-tree-results-cons-rule* (list head (caddr args))))
      (equation (proof-proof-chain proof equation (list constructor)))
      (present (proof-proof-fact proof "consp-cons"
                                  (seq-zip (list *library-x* *library-y*) (cdr head))))
      (untyped (proof-proof-fact proof "consp-not-symbolp" (list (list *library-x* head))))
      (untyped (proof-proof-modus-ponens proof untyped present))
      (keyword (t3-logic-libraryproofs-normalize lib (list *t3-book-tree-results-keywordp* head)
                                                (list untyped) (list *t3-book-tree-results-keywordp*)))
      (definition (t3-book-spines-shallow lib (list *t3-book-tree-results-tree-tag* head) nil))
      (equation (t3-book-spines-replace-value lib equation (list keyword definition))))
     (t3-book-tree-results-same-choice lib equation (cadr sides)
                                       (list *t3-book-tree-results-keywordp* tag)))))

(defun t3-book-tree-results-keyword-proof (book term)
  (let* ((lib (t3-book-values-book-proofs-library book))
         (proof (library-library-proof lib))
         (definitions (list *t3-book-tree-results-keywordp*)))
    (proof-with-checked-results
     ((opened (t3-book-values-book-proofs-normalize book term nil definitions))
      (value (and opened (proof-rewritten-term opened))))
     (if (and opened (not (equal value term)))
         (proof-with-checked-results
          ((step (t3-logic-libraryproofs-prove-formula lib value definitions nil)))
          (proof-proof-transport proof step opened))
       (t3-logic-libraryproofs-prove-formula lib term definitions nil)))))

(defun t3-book-tree-results-rendered-tree-in-book (book formula)
  (let* ((lib (t3-book-values-book-proofs-library book))
         (proof (library-library-proof lib))
         (facts (proof-proof-facts proof)))
    (proof-with-checked-results
     ((left (and (proof-is-call formula *proof-equal*) (proof-term-at formula 1))))
     (and (proof-is-call left *t3-book-tree-results-tree*)
       (proof-with-checked-results ((call (proof-term-at left 1)))
         (cond
          ((proof-is-call call *proof-cons*)
           (t3-book-tree-results-tree-cons lib formula))
          ((proof-is-call call *t3-book-tree-results-make-tag*)
           (and (assoc-equal *t3-book-tree-results-cons-rule* facts)
                (t3-book-tree-results-tree-tag lib formula)))
          ((not (proof-compound call)) nil)
          (t (proof-with-checked-results ((head (proof-term-at call 0)))
               (and (assoc-equal head (proof-proof-definitions proof))
                    (assoc-equal *t3-book-tree-results-tag-rule* facts)
                 (proof-with-checked-results
                  ((alias (proof-proof-unfold proof call))
                   (tag (proof-rewritten-term alias))
                   (tag-name (and (proof-is-call tag *t3-book-tree-results-make-tag*)
                                  (proof-term-at tag 1))))
                  (and (proof-is-call tag-name *proof-quote*)
                    (proof-with-checked-results
                     ((reflexive (proof-proof-reflexive proof left))
                      (equation (proof-proof-rewrite proof reflexive alias '(1 2 1)))
                      (rule (t3-book-tree-results-instantiate-constructor
                             lib *t3-book-tree-results-tag-rule* (cdr tag)))
                      (rule-body (proof-rewritten-term rule))
                      (guard (proof-term-at rule-body 1))
                      (keyword (t3-book-tree-results-keyword-proof book guard))
                      (selected (proof-proof-select proof rule-body keyword))
                      (result (proof-proof-chain proof equation (list rule selected)))
                      (claim (proof-step-first result)))
                     (and (equal claim formula) result)))))))))))))

(defun t3-book-tree-results-rendered-tree (lib formula)
  (t3-book-tree-results-rendered-tree-in-book
   (t3-book-values-make-book-proofs
    lib nil '("COMMON-LISP" "ACL2-INPUT-CHANNEL" "ACL2-OUTPUT-CHANNEL" "ACL2" "KEYWORD"))
   formula))
