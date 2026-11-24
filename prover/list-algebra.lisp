(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *list-algebra-associative* "BINARY-APPEND-ASSOCIATIVE")
(defconst *list-algebra-associativity*
  (proof-eq (list *list-preservation-append*
                  (list *list-preservation-append* *library-x* *library-y*) *library-z*)
            (list *list-preservation-append*
                  *library-x* (list *list-preservation-append* *library-y* *library-z*))))

(defun list-algebra-append-associativity-branch-reduce (term lib evidence)
  (proper-lists-reduce lib term (list evidence)
                       (list *list-preservation-append* *rulers-atom* *rulers-endp* *proof-not*)
                       nil 100 175))

(defun list-algebra-append-associativity-selectors (lib step args laws)
  (declare (xargs :measure (acl2-count laws)))
  (if (endp laws)
      step
    (proof-with-checked-results
        ((law (library-library-axiom lib (car laws) args))
         (rewritten (proof-proof-rewrite-first (library-library-proof lib) step law)))
      (list-algebra-append-associativity-selectors lib rewritten args (cdr laws)))))

(defun list-algebra-append-associativity-branch-recursive (lib left inner recursive evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (proper-lists-first-right left))
         (opened (list-algebra-append-associativity-branch-reduce value lib evidence))
         (left (proof-proof-chain proof left (list opened)))
         (inner-value (proper-lists-first-right inner))
         (left (list-algebra-append-associativity-selectors
                lib left (cdr inner-value) '("CAR-CONS" "CDR-CONS"))))
      (proof-proof-rewrite-first proof left recursive))))

(defun list-algebra-append-associativity-branch (evidence recursive lib)
  (let ((proof (library-library-proof lib))
        (before (cadr *list-algebra-associativity*))
        (after (caddr *list-algebra-associativity*)))
    (proof-with-checked-results
        ((inner (list-algebra-append-associativity-branch-reduce (cadr before) lib evidence))
         (identity (proof-proof-reflexive proof before))
         (left (if inner
                   (proof-proof-rewrite proof identity inner '(1 2 1))
                 '(:failure "failure" "")))
         (left (if recursive
                   (list-algebra-append-associativity-branch-recursive
                    lib left inner recursive evidence)
                 left))
         (right (list-algebra-append-associativity-branch-reduce after lib evidence)))
      (if (not right)
          *terms-unproved*
        (proof-with-checked-results
            ((left-value (proper-lists-first-right left))
             (right-value (proper-lists-first-right right)))
          (if (not (equal left-value right-value))
              *terms-unproved*
            (proof-with-checked-results ((reversed (proof-proof-symmetric proof right)))
              (proof-proof-chain proof left (list reversed)))))))))

(defun list-algebra-append-associativity-proof (lib)
  (let ((proof (library-library-proof lib))
        (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((induction (book-logic-tree-induction-init lib *list-algebra-associativity* *library-x*))
         (when-cons (proof-proof-assume proof test t))
         (bound (library-library-builtin lib 3 *library-x*))
         (smaller (proof-proof-discharge proof bound when-cons))
         (descent (book-logic-tree-induction-at induction (list *library-cdr* *library-x*)
                                               smaller nil))
         (hypothesis (car descent))
         (yes (list-algebra-append-associativity-branch when-cons hypothesis lib))
         (when-atom (proof-proof-assume proof test nil))
         (no (list-algebra-append-associativity-branch when-atom nil lib))
         (branches (proof-proof-cases proof test yes no)))
      (book-logic-tree-induction-finish (cdr descent) branches))))

(defun list-algebra-append-associativity (lib first second last)
  (let* ((result (if (proper-lists-known-lemma-p lib *list-algebra-associative*)
                     (cons *list-algebra-associative* lib)
                   (let ((step (list-algebra-append-associativity-proof lib)))
                     (if (failure-p step)
                         (cons step lib)
                       (proper-lists-add-rule lib *list-algebra-associative*
                                              *list-algebra-associativity* step)))))
         (name (car result))
         (lib (cdr result)))
    (if (failure-p name)
        result
      (cons (library-library-cite lib name (list first second last) nil) lib))))

(defun list-algebra-list-algebra-recursion (choices opening flattened auxiliary traversal
                                                   tree accumulator)
  (declare (xargs :measure (acl2-count choices)))
  (if (endp choices)
      nil
    (let* ((outer (caar choices))
           (inner (cadar choices))
           (child (list outer tree))
           (nested (list inner tree))
           (child-call (list traversal child))
           (nested-call (list traversal nested))
           (call (list auxiliary nested accumulator)))
      (proof-with-checked-results ((value (proper-lists-first-right opening)))
        (proof-with-checked-results
            ((matches
              (and (equal value (list auxiliary child call))
                   (proof-with-checked-results ((flattened-value (proper-lists-first-right flattened)))
                     (equal flattened-value
                            (list *list-preservation-append* child-call nested-call))))))
          (if matches
              (list outer inner child nested child-call nested-call call)
            (list-algebra-list-algebra-recursion (cdr choices) opening flattened
                                                 auxiliary traversal tree accumulator)))))))

(defun list-algebra-list-algebra-traversal (lib formula left right)
  (let ((auxiliary (car left))
        (tree (cadr left))
        (accumulator (caddr left))
        (traversal (caadr right))
        (source (cadadr right)))
    (if (or (proof-compound tree) (proof-compound accumulator) (equal tree accumulator)
            (not (equal source tree)) (not (equal (caddr right) accumulator))
            (not (assoc-equal auxiliary (proper-lists-definitions lib)))
            (not (assoc-equal traversal (proper-lists-definitions lib))))
        nil
      (let ((proof (library-library-proof lib))
            (test (list *proof-consp* tree)))
        (proof-with-checked-results
            ((when-cons (proof-proof-assume proof test t))
             (reducer (book-logic-reducer-init
                       lib (list when-cons)
                       (list auxiliary traversal *rulers-atom* *rulers-endp* *proof-not*)
                       nil 80 185 nil nil))
             (opening-result (book-logic-reducer-reduce reducer left nil))
             (opening (car opening-result))
             (flattened (car (book-logic-reducer-reduce
                              (cdr opening-result) (list traversal tree) nil))))
          (and opening flattened
               (proof-with-checked-results
                   ((recursion (list-algebra-list-algebra-recursion
                                (list (list *library-cdr* *library-car*)
                                      (list *library-car* *library-cdr*))
                                opening flattened auxiliary traversal tree accumulator)))
                 (and recursion
                      (proof-with-checked-results ((when-atom (proof-proof-assume proof test nil)))
                        (list :call formula (list when-atom)
                              (list formula right tree accumulator when-cons
                                    opening flattened recursion)))))))))))

(defun list-algebra-list-algebra (lib formula)
  (let ((left (cadr formula))
        (right (caddr formula)))
    (cond ((not (proof-is-call formula *proof-equal*)) (cons nil lib))
          ((not (equal (len formula) 3))
           (cons (proper-lists-check-arity (cdr formula) 2) lib))
          ((not (proof-is-call right *list-preservation-append*)) (cons nil lib))
          (t
           (let ((matched (book-logic-match *list-algebra-associativity* formula nil)))
             (cond ((failure-p matched) (cons matched lib))
                   ((failure-p (car matched)) (cons (car matched) lib))
                   ((car matched)
                    (let ((bindings (cdr matched)))
                      (list-algebra-append-associativity
                       lib (cdr (assoc-equal *library-x* bindings))
                       (cdr (assoc-equal *library-y* bindings))
                       (cdr (assoc-equal *library-z* bindings)))))
                   ((< (len right) 2)
                    (cons (and (proof-compound left) (equal (len left) 3)
                               '(:failure "failure" ""))
                          lib))
                   ((not (and (proof-compound left) (equal (len left) 3)
                              (proof-compound (cadr right)) (equal (len (cadr right)) 2)))
                    (cons nil lib))
                   ((and (< (len right) 3)
                         (not (or (proof-compound (cadr left))
                                  (proof-compound (caddr left))
                                  (equal (cadr left) (caddr left))
                                  (not (equal (cadadr right) (cadr left))))))
                    (cons '(:failure "failure" "") lib))
                   (t (cons (list-algebra-list-algebra-traversal lib formula left right)
                            lib))))))))

(defun list-algebra-list-algebra-fold (lib formula tree accumulator when-cons opening recursion)
  (let ((proof (library-library-proof lib))
        (outer (car recursion))
        (inner (cadr recursion))
        (child (caddr recursion))
        (nested (cadddr recursion))
        (call (nth 6 recursion)))
    (proof-with-checked-results
        ((induction (book-logic-tree-induction-init lib formula tree))
         (inner-size (library-library-builtin lib (if (equal inner *library-car*) 2 3) tree))
         (inner-bound (proof-proof-discharge proof inner-size when-cons))
         (outer-size (library-library-builtin lib (if (equal outer *library-car*) 2 3) tree))
         (outer-bound (proof-proof-discharge proof outer-size when-cons))
         (descent (book-logic-tree-induction-at induction child outer-bound
                                               (list (list accumulator call))))
         (instance (car descent))
         (folded (proof-proof-chain proof opening (list instance)))
         (descent (book-logic-tree-induction-at (cdr descent) nested inner-bound nil))
         (instance (car descent))
         (rewritten (proof-proof-rewrite proof folded instance '(1 2 2)))
         (folded (proof-proof-tidy proof rewritten)))
      (cons folded (cdr descent)))))

(defun list-algebra-list-algebra-finish (lib folded association induction right flattened test base)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assoc-reversed (proof-proof-symmetric proof association))
         (joined (proof-proof-chain proof folded (list assoc-reversed)))
         (identity (proof-proof-reflexive proof right))
         (target (proof-proof-rewrite proof identity flattened '(1 2 1)))
         (target-reversed (proof-proof-symmetric proof target))
         (step (proof-proof-chain proof joined (list target-reversed)))
         (branches (proof-proof-cases proof test step base)))
      (book-logic-tree-induction-finish induction branches))))

(defun list-algebra-list-algebra-resume (lib continuation answer)
  (if (failure-p answer)
      (cons answer lib)
    (let* ((formula (car continuation))
           (right (cadr continuation))
           (tree (caddr continuation))
           (accumulator (cadddr continuation))
           (when-cons (nth 4 continuation))
           (opening (nth 5 continuation))
           (flattened (nth 6 continuation))
           (recursion (nth 7 continuation))
           (fold (list-algebra-list-algebra-fold lib formula tree accumulator
                                                 when-cons opening recursion)))
      (if (failure-p fold)
          (cons fold lib)
        (let* ((result (list-algebra-append-associativity lib (nth 4 recursion)
                                                          (nth 5 recursion) accumulator))
               (association (car result))
               (lib (cdr result)))
          (if (failure-p association)
              result
            (cons (list-algebra-list-algebra-finish lib (car fold) association (cdr fold)
                                                    right flattened (list *proof-consp* tree)
                                                    answer)
                  lib)))))))
