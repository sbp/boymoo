(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-list-types-min* (proof-cl "MIN"))
(defconst *b1-list-types-max* (proof-cl "MAX"))
(defconst *b1-list-types-maxlist* (proof-sym "MAXLIST" "ACL2"))
(defconst *b1-list-types-natural-list* (proof-sym "NATURAL-LISTP" "ACL2"))

(defun b1-list-types-typed-head-and-tail (lib list-type cons)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((call (proof-step-first list-type))
         (equation (b1-revappend-open-list lib call (list cons)))
         (opened (proof-proof-rewrite proof list-type equation '(1))))
      (proof-proof-conjunct proof opened))))

(defun b1-list-types-typed-cons (lib predicate pair head tail)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equation (b1-revappend-open-list lib (list predicate pair) nil))
         (goal (proof-rewritten-term equation))
         (result (b1-logic-bookproof-normalize-proof lib goal (list head tail) nil nil nil)))
      (proof-proof-transport proof result equation))))

(defun b1-list-types-typed-empty (lib predicate)
  (b1-logic-bookproof-normalize-proof
   lib (list predicate *proof-false*) nil
   (list predicate *b1-logic-atom* *proof-not* *b1-logic-eq*) nil nil))

(defun b1-list-types-numeric-fold-type-step-inside-leaf (value lib predicate element smaller)
  (let ((goal (list predicate value)))
    (proof-with-checked-results ((element-type (proof-step-first element)))
      (if (equal element-type goal)
          element
        (proof-with-checked-results ((smaller-type (proof-step-first smaller)))
          (if (equal smaller-type goal)
              smaller
            (b1-arithmetic-known-type lib predicate value (list element smaller))))))))

(defun b1-list-types-numeric-insert-type-consequence-leaf
    (pair lib predicate item xs item-type list-type head child)
  (proof-with-checked-results ((fields (proof-list-of-length (cdr pair) 2)))
    (if (and (equal (car fields) item) (equal (cadr fields) xs))
        (b1-list-types-typed-cons lib predicate pair item-type list-type)
      (b1-list-types-typed-cons lib predicate pair head child))))

(defun b1-list-types-by-value (n lib value template leaf)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((zp n) '(:failure "fuel" "b1-list-types-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (yes (b1-list-types-by-value (1- n) lib (cadr branches) template leaf))
           (no (b1-list-types-by-value (1- n) lib (caddr branches) template leaf)))
        (proof-by-value-join proof value template yes no)))
     ((and (proof-compound value) (not (consp value)))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (opened (proof-rewritten-term equality))
           (step (b1-list-types-by-value (1- n) lib opened template leaf))
           (reversed (proof-proof-symmetric proof equality)))
        (proof-proof-rewrite-result proof step reversed template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (if (eq (car leaf) :fold)
                     (b1-list-types-numeric-fold-type-step-inside-leaf
                      value lib (cadr leaf) (caddr leaf) (cadddr leaf))
                   (b1-list-types-numeric-insert-type-consequence-leaf
                    value lib (cadr leaf) (caddr leaf) (cadddr leaf) (nth 4 leaf)
                    (nth 5 leaf) (nth 6 leaf) (nth 7 leaf))))
           (literal (proof-step-first step))
           (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal target) step '(:failure "failure" "")))))))

(defun b1-list-types-numeric-fold-type-step-inside
    (tail-cons lib predicate call template element tail-type cons hypothesis)
  (let* ((proof (library-library-proof lib))
         (evidence (if tail-cons (list tail-type tail-cons) (list tail-type))))
    (proof-with-checked-results
        ((literal (proof-step-first hypothesis))
         (guard (proof-term-at literal 1))
         (smaller-guard (b1-logic-bookproof-normalize-proof lib guard evidence nil nil nil))
         (smaller (proof-proof-modus-ponens proof hypothesis smaller-guard))
         (args (if tail-cons (list cons tail-cons) (list cons)))
         (reduction (b1-revappend-open-list lib call args))
         (right (proof-rewritten-term reduction))
         (arithmetic (b1-logic-bookproof-normalize
                      lib right nil (list *b1-list-types-min* *b1-list-types-max*) nil nil nil nil))
         (value (proof-rewritten-term arithmetic))
         (typed (b1-list-types-by-value 1000000 lib value template
                                       (list :fold predicate element smaller)))
         (arithmetic (proof-proof-chain proof reduction (list arithmetic))))
      (library-library-transport-argument lib typed arithmetic 1))))

(defun b1-list-types-numeric-fold-type-step
    (list-type cons lib predicate call xs need-cons induction)
  (let* ((proof (library-library-proof lib))
         (cons-test (list *proof-consp* xs))
         (tail (list *library-cdr* xs))
         (head (list *library-car* xs))
         (tail-test (list *proof-consp* tail))
         (template (list predicate *proof-result*)))
    (proof-with-checked-results
        ((types (b1-list-types-typed-head-and-tail lib list-type cons))
         (element (car types))
         (tail-type (cadr types))
         (actual-head (list predicate head))
         (present-head (proof-step-first element))
         (element (if (equal present-head actual-head)
                      element
                    (proof-with-checked-results ((view (proof-proof-unfold proof actual-head)))
                      (proof-proof-transport proof element view))))
         (hypothesis (b1-induction-tree-induction-hypothesis
                      induction (list (cons xs tail)) (list (list cons-test t))))
         (induction (cdr hypothesis))
         (hypothesis (car hypothesis))
         (result
          (if (not need-cons)
              (b1-list-types-numeric-fold-type-step-inside
               nil lib predicate call template element tail-type cons hypothesis)
            (proof-with-checked-results
                ((tail-atom (proof-proof-assume proof tail-test nil))
                 (short (b1-revappend-open-list lib call (list cons tail-atom)))
                 (short (library-library-transport-argument lib element short 1))
                 (tail-cons (proof-proof-assume proof tail-test t))
                 (long (b1-list-types-numeric-fold-type-step-inside
                        tail-cons lib predicate call template element tail-type cons hypothesis)))
              (proof-proof-cases proof tail-test long short)))))
      (cons result induction))))

(defun b1-list-types-numeric-fold-type-consequence
    (premise lib predicate call xs need-cons induction)
  (let* ((proof (library-library-proof lib))
         (cons-test (list *proof-consp* xs)))
    (if need-cons
        (proof-with-checked-results
            ((types (proof-proof-conjunct proof premise))
             (cons (cadr types))
             (result (b1-list-types-numeric-fold-type-step
                      (car types) cons lib predicate call xs need-cons induction))
             (step (proof-proof-discharge proof (car result) cons)))
          (cons step (cdr result)))
      (proof-with-checked-results
          ((cons (proof-proof-assume proof cons-test t))
           (atom (proof-proof-assume proof cons-test nil))
           (zero (b1-arithmetic-known-type lib predicate *proof-zero* nil))
           (empty (b1-revappend-open-list lib call (list atom)))
           (base (library-library-transport-argument lib zero empty 1))
           (result (b1-list-types-numeric-fold-type-step
                    premise cons lib predicate call xs need-cons induction))
           (step (proof-proof-cases proof cons-test (car result) base)))
        (cons step (cdr result))))))

(defun b1-list-types-numeric-fold-type (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (guard (cadr implication))
       (claim (proof-list-of-length (caddr implication) 2))
       (predicate (car claim))
       (call (proof-list-of-length (cadr claim) 2))
       (xs (cadr call))
       (need-cons (proof-is-call guard *proof-if*))
       (induction (b1-induction-tree-induction-init lib formula xs))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (case (b1-list-types-numeric-fold-type-consequence
              premise lib predicate call xs need-cons induction))
       (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car case))))
    (b1-induction-tree-induction-finish (cdr case) step)))

(defun b1-list-types-natural-excess-consequence (premise lib name xs call test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((cons (proof-proof-assume proof test t))
         (maximum (proof-proof-fact proof name (list (list *library-x* xs))))
         (literal (proof-step-first maximum))
         (guard (proof-term-at literal 1))
         (satisfied (b1-logic-bookproof-normalize-proof lib guard (list premise cons) nil nil nil))
         (maximum (proof-proof-modus-ponens proof maximum satisfied))
         (total (b1-revappend-open-list lib call (list cons)))
         (right (proof-rewritten-term total))
         (one (library-library-natural lib *proof-one*))
         (grown (library-library-cite lib "NATURAL-SUM" (cdr right) (list one maximum)))
         (yes (library-library-transport-argument lib grown total 1))
         (atom (proof-proof-assume proof test nil))
         (empty (b1-revappend-open-list lib call (list atom)))
         (zero (library-library-natural lib *proof-zero*))
         (no (library-library-transport-argument lib zero empty 1))
         (cases (proof-proof-cases proof test yes no))
         (unfolded (proof-proof-unfold proof (list *library-natp* call))))
      (proof-proof-rewrite proof cases unfolded '(1)))))

(defun b1-list-types-natural-excess (lib formula)
  (let ((name (proof-sym "SELF-MAXLIST-NATURAL" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (let* ((assumption (proof-ite (list *b1-list-types-natural-list* *library-x*)
                                              (list *proof-consp* *library-x*) *proof-false*))
                       (claim (list *library-implies* assumption
                                    (list *library-natp* (list *b1-list-types-maxlist* *library-x*)))))
                  (proof-with-checked-results ((step (b1-list-types-numeric-fold-type lib claim)))
                    (library-library-lemma lib "MAXLIST-NATURAL" claim step nil)))))
         (guard (proof-term-at formula 1))
         (xs (proof-term-at guard 1))
         (claim (proof-term-at formula 2))
         (result (proof-term-at claim 1))
         (call (proof-term-at result 1))
         (test (list *proof-consp* xs))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-list-types-natural-excess-consequence premise lib name xs call test))
         (proof (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))
      (cons proof lib))))

(defun b1-list-types-numeric-insert-type-consequence
    (premise lib predicate call item xs cons-test induction)
  (let* ((proof (library-library-proof lib))
         (template (list predicate *proof-result*)))
    (proof-with-checked-results
        ((types (proof-proof-conjunct proof premise))
         (item-type (car types))
         (list-type (cadr types))
         (cons (proof-proof-assume proof cons-test t))
         (atom (proof-proof-assume proof cons-test nil))
         (types (b1-list-types-typed-head-and-tail lib list-type cons))
         (head (car types))
         (tail (cadr types))
         (smaller (b1-induction-tree-induction-hypothesis
                   induction (list (cons xs (list *library-cdr* xs))) (list (list cons-test t))))
         (induction (cdr smaller))
         (smaller (car smaller))
         (literal (proof-step-first smaller))
         (guard (proof-term-at literal 1))
         (known (b1-logic-bookproof-normalize-proof lib guard (list item-type tail) nil nil nil))
         (child (proof-proof-modus-ponens proof smaller known))
         (expanded (b1-revappend-open-list lib call (list cons)))
         (value (proof-rewritten-term expanded))
         (typed (b1-list-types-by-value 1000000 lib value template
                                       (list :insert predicate item xs item-type list-type head child)))
         (yes (library-library-transport-argument lib typed expanded 1))
         (empty (b1-revappend-open-list lib call (list atom)))
         (pair (proof-rewritten-term empty))
         (empty-type (b1-list-types-typed-empty lib predicate))
         (no (b1-list-types-typed-cons lib predicate pair item-type empty-type))
         (no (library-library-transport-argument lib no empty 1))
         (result (proof-proof-cases proof cons-test yes no)))
      (cons result induction))))

(defun b1-list-types-numeric-insert-type (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr implication) 2))
       (predicate (car claim))
       (call (proof-list-of-length (cadr claim) 3))
       (item (cadr call))
       (xs (caddr call))
       (cons-test (list *proof-consp* xs))
       (induction (b1-induction-tree-induction-init lib formula xs))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (case (b1-list-types-numeric-insert-type-consequence
              premise lib predicate call item xs cons-test induction))
       (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car case))))
    (b1-induction-tree-induction-finish (cdr case) step)))

(defun b1-list-types-numeric-sort-type-consequence
    (list-type lib predicate call xs cons-test induction)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((cons (proof-proof-assume proof cons-test t))
         (atom (proof-proof-assume proof cons-test nil))
         (types (b1-list-types-typed-head-and-tail lib list-type cons))
         (head (car types))
         (tail (cadr types))
         (hypothesis (b1-induction-tree-induction-hypothesis
                      induction (list (cons xs (list *library-cdr* xs))) (list (list cons-test t))))
         (induction (cdr hypothesis))
         (sorted-tail (proof-proof-modus-ponens proof (car hypothesis) tail))
         (expanded (b1-revappend-open-list lib call (list cons)))
         (index (proof-sym "REAL/RATIONAL-LISTP-NUMERIC-INSERT" "ACL2"))
         (head-type (proof-step-first head))
         (sorted-type (proof-step-first sorted-tail))
         (guard (proof-ite head-type sorted-type *proof-false*))
         (value (proof-rewritten-term expanded))
         (law (b1-logic-bookproof-from-fact lib index
                                           (list *library-implies* guard (list predicate value))))
         (known (b1-logic-bookproof-normalize-proof lib guard (list head sorted-tail) nil nil nil))
         (inserted (proof-proof-modus-ponens proof law known))
         (yes (library-library-transport-argument lib inserted expanded 1))
         (empty-type (b1-list-types-typed-empty lib predicate))
         (empty (b1-revappend-open-list lib call (list atom)))
         (no (library-library-transport-argument lib empty-type empty 1))
         (result (proof-proof-cases proof cons-test yes no)))
      (cons result induction))))

(defun b1-list-types-numeric-sort-type (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr implication) 2))
       (predicate (car claim))
       (call (proof-list-of-length (cadr claim) 2))
       (xs (cadr call))
       (cons-test (list *proof-consp* xs))
       (induction (b1-induction-tree-induction-init lib formula xs))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (case (b1-list-types-numeric-sort-type-consequence
              premise lib predicate call xs cons-test induction))
       (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise (car case))))
    (b1-induction-tree-induction-finish (cdr case) step)))
