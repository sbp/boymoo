(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *list-preservation-append* (proof-sym "BINARY-APPEND" "ACL2"))
(defconst *list-preservation-revappend* (proof-cl "REVAPPEND"))
(defconst *list-preservation-list-combiners*
  (list *list-preservation-append* *list-preservation-revappend*))
(defconst *list-preservation-true-list-fix* (proof-sym "TRUE-LIST-FIX" "ACL2"))

(defun list-preservation-combine-type-rule-proof (lib predicate operation cons-type)
  (let* ((proof (library-library-proof lib))
         (target (list operation *library-x* *library-y*))
         (left (list predicate target))
         (right (list predicate *library-y*))
         (test (list *proof-consp* *library-x*))
         (definitions (list operation *rulers-atom* *rulers-endp* (proof-cl "NOT"))))
    (proof-with-checked-results
        ((hypothesis (proof-proof-assume proof (list predicate *library-x*) t))
         (hypothesis-term (proof-step-first hypothesis))
         (formula (list *library-implies* hypothesis-term (proof-eq left right)))
         (induction (book-logic-tree-induction-init lib formula *library-x*))
         (yes (proof-proof-assume proof test t))
         (no (proof-proof-assume proof test nil))
         (base-value (proper-lists-reduce lib target (list no) definitions nil 36 100)))
      (and base-value
           (proof-with-checked-results ((base-right (proper-lists-first-right base-value)))
             (and (equal base-right *library-y*)
                  (proof-with-checked-results
                      ((identity (proof-proof-reflexive proof left))
                       (base (proof-proof-rewrite proof identity base-value '(1 2 1)))
                       (head (list *library-car* *library-x*))
                       (tail (list *library-cdr* *library-x*))
                       (car-cdr (library-library-axiom lib "CAR-CDR-ELIM" (list *library-x*)))
                       (rebuilt (proof-proof-modus-ponens proof car-cdr yes))
                       (cons-value (library-library-transport-argument lib hypothesis rebuilt 1))
                       (cons-law (library-library-cite lib cons-type (list head tail) nil))
                       (rewritten (proof-proof-rewrite proof cons-value cons-law '(1)))
                       (view (proof-proof-tidy proof rewritten))
                       (view-term (proof-step-first view))
                       (parts (if (proof-is-call view-term *proof-if*)
                                  (proof-proof-conjunct proof view)
                                (list nil view)))
                       (revappend-p (equal operation *list-preservation-revappend*))
                       (recursive-acc (if revappend-p
                                          (list *proof-cons* head *library-y*)
                                        *library-y*))
                       (bound (library-library-builtin lib 3 *library-x*))
                       (smaller (proof-proof-discharge proof bound yes))
                       (bindings (and revappend-p (list (list *library-y* recursive-acc))))
                       (descent (book-logic-tree-induction-at induction tail smaller bindings))
                       (instance (car descent))
                       (fact (proof-proof-modus-ponens proof instance (cadr parts)))
                       (child (list operation tail recursive-acc))
                       (combine (library-library-cite
                                 lib cons-type
                                 (list head (if revappend-p *library-y* child)) nil))
                       (combine
                        (if (car parts)
                            (proof-with-checked-results
                                ((test (proper-lists-first-right combine))
                                 (selected (proof-proof-select proof test (car parts))))
                              (proof-proof-chain proof combine (list selected)))
                          combine))
                       (contents (if revappend-p
                                     (proof-proof-chain proof fact (list combine))
                                   (proof-proof-chain proof combine (list fact))))
                       (step (proper-lists-reduce lib target (list yes) definitions nil 42 100)))
                    (and step
                         (proof-with-checked-results
                             ((value (proper-lists-first-right step))
                              (content-formula (proof-step-first contents)))
                           (and (equal (list predicate value) (cadr content-formula))
                                (proof-with-checked-results
                                    ((identity (proof-proof-reflexive proof left))
                                     (folded (proof-proof-rewrite proof identity step '(1 2 1)))
                                     (step (proof-proof-chain proof folded (list contents)))
                                     (both (proof-proof-cases proof test step base))
                                     (implication (witnesses-prove-implication lib formula
                                                                               hypothesis both)))
                                  (book-logic-tree-induction-finish (cdr descent)
                                                                   implication))))))))))))

(defun list-preservation-combine-type-rule (lib predicate operation)
  (let* ((result (proper-lists-cons-type-rule lib predicate))
         (cons-type (car result))
         (lib (cdr result)))
    (cond ((or (not cons-type) (failure-p cons-type)) result)
          ((< (len operation) 3)
           (cons '(:failure "failure" "") lib))
          (t
           (let ((label (concatenate 'string cons-type "-" (caddr operation))))
             (if (proper-lists-known-lemma-p lib label)
                 (cons label lib)
               (let ((step (list-preservation-combine-type-rule-proof lib predicate operation
                                                                      cons-type)))
                 (if (or (not step) (failure-p step))
                     (cons step lib)
                   (let ((formula (proof-step-first step)))
                     (if (failure-p formula)
                         (cons formula lib)
                       (proper-lists-add-rule lib label formula step)))))))))))

(defun list-preservation-preserve-list-type (lib formula)
  (let ((bad-formula (proper-lists-check-arity formula 2))
        (predicate (car formula))
        (expression (cadr formula)))
    (cond (bad-formula (cons bad-formula lib))
          ((not (member-equal (car expression) *list-preservation-list-combiners*))
           (let ((operator (proof-term-at expression 0)))
             (cons (and (failure-p operator) operator) lib)))
          (t
           (let ((bad-expression (proper-lists-check-arity expression 3)))
             (if bad-expression
                 (cons bad-expression lib)
               (let* ((result (list-preservation-combine-type-rule lib predicate (car expression)))
                      (rule (car result))
                      (lib (cdr result))
                      (left (cadr expression))
                      (right (caddr expression)))
                 (if (or (not rule) (failure-p rule))
                     result
                   (cons (list :call (list predicate left) nil
                               (list :first predicate left right rule))
                         lib)))))))))

(defun list-preservation-preserve-list-type-resume (lib continuation answer)
  (cond ((terms-unproved-p answer) (cons nil lib))
        ((failure-p answer) (cons answer lib))
        (t
         (let ((predicate (cadr continuation))
               (left (caddr continuation))
               (right (cadddr continuation))
               (rule (nth 4 continuation)))
           (if (eq (car continuation) :first)
               (cons (list :call (list predicate right) nil
                           (list :second predicate left right rule answer))
                     lib)
             (let ((proof (library-library-proof lib)))
               (cons
                (proof-with-checked-results
                    ((cited (library-library-cite lib rule (list left right) nil))
                     (equation (proof-proof-modus-ponens proof cited (nth 5 continuation))))
                  (proof-proof-transport proof answer equation))
                lib)))))))

(defun list-preservation-equate-conditions (lib left right tests evidence)
  (declare (xargs :measure (acl2-count tests)))
  (let ((proof (library-library-proof lib)))
    (cond ((equal left right) (proof-proof-reflexive proof left))
          ((endp tests)
           (let ((result (proof-proof-prove proof (proof-eq left right) evidence nil)))
             (if (terms-proof-fallback-p result)
                 *terms-unproved*
               result)))
          (t
           (let ((test (car tests))
                 (rest (cdr tests)))
             (proof-with-checked-results
                 ((yes-premise (proof-proof-assume proof test t))
                  (yes (list-preservation-equate-conditions lib left right rest
                                                           (append evidence (list yes-premise))))
                  (no-premise (proof-proof-assume proof test nil))
                  (no (list-preservation-equate-conditions lib left right rest
                                                          (append evidence (list no-premise)))))
               (proof-proof-cases proof test yes no)))))))

(defun list-preservation-combine-list-equation-left (lib expanded-left reverse-p ih rule
                                                       item second child)
  (let ((proof (library-library-proof lib)))
    (if reverse-p
        (proof-with-checked-results
            ((expanded-left (proof-proof-chain proof expanded-left (list ih)))
             (cons-law (library-library-cite lib rule (list item second) nil)))
          (proof-proof-rewrite-first proof expanded-left cons-law))
      (proof-with-checked-results
          ((cons-law (library-library-cite lib rule (list item child) nil))
           (expanded-left (proof-proof-chain proof expanded-left (list cons-law))))
        (proof-proof-rewrite-first proof expanded-left ih)))))

(defun list-preservation-combine-list-equation-step (lib formula predicate call right test
                                                       rule yes base expanded-input item tail rest)
  (let* ((proof (library-library-proof lib))
         (operation (car call))
         (first (cadr call))
         (second (caddr call))
         (left (list predicate call))
         (definitions (list operation *rulers-atom* *rulers-endp* *proof-not*)))
    (proof-with-checked-results
        ((identity (proof-proof-reflexive proof test))
         (input-test (proof-proof-rewrite proof identity expanded-input '(1 2 1)))
         (cons-law (library-library-cite lib rule (list item rest) nil))
         (input-test (proof-proof-chain proof input-test (list cons-law)))
         (identity (proof-proof-reflexive proof right))
         (expanded-right (proof-proof-rewrite proof identity input-test '(1 2 1)))
         (reverse-p (equal operation *list-preservation-revappend*))
         (acc (if reverse-p (list *proof-cons* item second) second))
         (child (list operation tail acc))
         (expected (if reverse-p child (list *proof-cons* item child)))
         (step-value (proper-lists-reduce lib call (list yes) definitions nil 42 145)))
      (and step-value
           (proof-with-checked-results ((step-right (proper-lists-first-right step-value)))
             (and (equal step-right expected)
                  (proof-with-checked-results
                      ((induction (book-logic-tree-induction-init lib formula first))
                       (bound (library-library-builtin lib 3 first))
                       (smaller (proof-proof-discharge proof bound yes))
                       (bindings (and reverse-p (list (list second acc))))
                       (descent (book-logic-tree-induction-at induction tail smaller bindings))
                       (instance (car descent))
                       (identity (proof-proof-reflexive proof left))
                       (expanded-left (proof-proof-rewrite proof identity step-value '(1 2 1)))
                       (expanded-left (list-preservation-combine-list-equation-left
                                       lib expanded-left reverse-p instance rule item second child))
                       (test-value (proper-lists-first-right input-test))
                       (parts (cons (list predicate rest)
                                    (and (proof-is-call test-value *proof-if*)
                                         (list (cadr test-value)))))
                       (left-value (proper-lists-first-right expanded-left))
                       (right-value (proper-lists-first-right expanded-right))
                       (joined (list-preservation-equate-conditions lib left-value right-value
                                                                    parts nil))
                       (reversed (proof-proof-symmetric proof expanded-right))
                       (step (proof-proof-chain proof expanded-left (list joined reversed)))
                       (both (proof-proof-cases proof (list *proof-consp* first) step base)))
                    (book-logic-tree-induction-finish (cdr descent) both))))))))

(defun list-preservation-combine-list-equation-proof (lib formula left right rule)
  (let* ((proof (library-library-proof lib))
         (predicate (car left))
         (call (cadr left))
         (operation (car call))
         (first (cadr call))
         (second (caddr call))
         (test (cadr right))
         (fixed (list *list-preservation-true-list-fix* first))
         (condition (list *proof-consp* first))
         (definitions (list operation *rulers-atom* *rulers-endp* *proof-not*)))
    (proof-with-checked-results
        ((yes (proof-proof-assume proof condition t))
         (no (proof-proof-assume proof condition nil))
         (base-value (proper-lists-reduce lib call (list no) definitions nil 35 100)))
      (and base-value
           (proof-with-checked-results ((value (proper-lists-first-right base-value)))
             (and (equal value second)
                  (proof-with-checked-results
                      ((identity (proof-proof-reflexive proof left))
                       (base (proof-proof-rewrite proof identity base-value '(1 2 1)))
                       (reducer (book-logic-reducer-init
                                 lib (list no)
                                 (list predicate *list-preservation-true-list-fix*
                                       *rulers-atom* *rulers-endp* *proof-not*
                                       (proof-cl "NULL") (proof-cl "EQ"))
                                 t 48 150 nil nil))
                       (base-test (car (book-logic-reducer-prove reducer test)))
                       (selected (proof-proof-select proof right base-test))
                       (reversed (proof-proof-symmetric proof selected))
                       (base (proof-proof-chain proof base (list reversed)))
                       (item (list *library-car* first))
                       (tail (list *library-cdr* first)))
                    (if (equal (cadr test) first)
                        (proof-with-checked-results
                            ((law (library-library-axiom lib "CAR-CDR-ELIM" (list first)))
                             (rebuilt (proof-proof-modus-ponens proof law yes))
                             (expanded-input (proof-proof-symmetric proof rebuilt)))
                          (list-preservation-combine-list-equation-step
                           lib formula predicate call right test rule yes base expanded-input
                           item tail tail))
                      (proof-with-checked-results
                          ((expanded-input (proper-lists-reduce
                                            lib fixed (list yes)
                                            (list *list-preservation-true-list-fix*) nil 30 130))
                           (rest (list *list-preservation-true-list-fix* tail)))
                        (and expanded-input
                             (proof-with-checked-results
                                 ((value (proper-lists-first-right expanded-input)))
                               (and (equal value (list *proof-cons* item rest))
                                    (list-preservation-combine-list-equation-step
                                     lib formula predicate call right test rule yes base
                                     expanded-input item tail rest)))))))))))))

(defun list-preservation-combine-list-equation (lib formula)
  (let ((left (cadr formula))
        (right (caddr formula)))
    (cond ((not (proof-is-call formula *proof-equal*)) (cons nil lib))
          ((not (equal (len formula) 3))
           (cons (proper-lists-check-arity (cdr formula) 2) lib))
          ((not (and (proof-compound left) (equal (len left) 2)
                     (proof-compound (cadr left))))
           (cons nil lib))
          ((endp (cadr left))
           (cons '(:failure "failure" "") lib))
          ((not (and (member-equal (caadr left) *list-preservation-list-combiners*)
                     (proof-is-call right *proof-if*)))
           (cons nil lib))
          ((< (len right) 4) (cons '(:failure "failure" "") lib))
          ((not (equal (cadddr right) *proof-false*)) (cons nil lib))
          (t
           (let* ((predicate (car left))
                  (call (cadr left))
                  (first (cadr call))
                  (second (caddr call))
                  (test (cadr right)))
             (cond ((not (equal (len call) 3))
                    (cons (proper-lists-check-arity call 3) lib))
                   ((or (proof-compound first) (proof-compound second) (equal first second)
                        (not (equal (caddr right) (list predicate second)))
                        (not (or (equal test (list predicate first))
                                 (equal test (list predicate
                                                   (list *list-preservation-true-list-fix* first))))))
                    (cons nil lib))
                   (t
                    (let* ((result (proper-lists-cons-type-rule lib predicate))
                           (rule (car result))
                           (lib (cdr result)))
                      (if (or (not rule) (failure-p rule))
                          result
                        (cons (list-preservation-combine-list-equation-proof
                               lib formula left right rule)
                              lib))))))))))
