(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-name-bounds-name-total* (proof-sym "T3-NAME-CAPACITY-TOTAL" "ACL2"))
(defconst *t3-name-bounds-member-equal* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *t3-name-bounds-member-name* (proof-sym "MEMBER-SYMBOL-NAME" "ACL2"))
(defconst *t3-name-bounds-symbol-name* (proof-cl "SYMBOL-NAME"))

(defun t3-name-bounds-name-capacity (string)
  (t3-digit-capacity-capacity (t3-list-bounds-string-to-chars string)))

(defun t3-name-bounds-symbol-capacity (symbol)
  (t3-name-bounds-name-capacity (list *t3-name-bounds-symbol-name* symbol)))

(defun t3-name-bounds-name-total (symbols)
  (list *t3-name-bounds-name-total* symbols))

(defun t3-name-bounds-total-natural (lib symbols)
  (library-library-cite lib "T3-NAME-TOTAL-NATURAL" (list symbols) nil))

(defun t3-name-bounds-total-integer (lib symbols)
  (proof-with-checked-results ((natural (t3-name-bounds-total-natural lib symbols)))
    (library-library-cite lib "NATURAL-INTEGER" (list (t3-name-bounds-name-total symbols))
                          (list natural))))

(defun t3-name-bounds-total-branch (lib symbols test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equation (proof-proof-unfold proof (t3-name-bounds-name-total symbols)))
         (body (t3-book-term-collections-step-term-at equation 2))
         (selected (proof-proof-select proof body test)))
      (proof-proof-chain proof equation (list selected)))))

(defun t3-name-bounds-total-fold (lib)
  (let* ((carrier (list *library-car* *library-x*))
         (rest-total (t3-name-bounds-name-total *t3-list-bounds-tail*))
         (fold-body (library-plus (t3-name-bounds-symbol-capacity carrier) rest-total))
         (formula (list *library-natp* (t3-name-bounds-name-total *library-x*)))
         (word (list *t3-name-bounds-symbol-name* carrier))
         (head (t3-name-bounds-name-capacity word)))
    (proof-with-checked-results
        ((lib (t3-list-bounds-define-fold lib *t3-name-bounds-name-total* fold-body *proof-zero*))
         (proof (library-library-proof lib))
         (present (proof-proof-assume proof *t3-list-bounds-cons-x* t))
         (ih (t3-list-bounds-tail-hypothesis lib formula present))
         (types (t3-digit-capacity-capacity-type lib (t3-list-bounds-string-to-chars word)))
         (nonnegative (library-library-cite lib "POSITIVE-NONNEGATIVE" (list head) types))
         (natural (library-library-cite lib "NATURAL-FROM-BOUNDS" (list head)
                                        (list (car types) nonnegative)))
         (total (library-library-cite lib "NATURAL-SUM" (list head rest-total) (list natural ih)))
         (branch (t3-name-bounds-total-branch lib *library-x* present))
         (step (library-library-transport-argument lib total branch 1))
         (zero (t3-logic-libraryproofs-natural lib *proof-zero*))
         (absent (proof-proof-assume proof *t3-list-bounds-cons-x* nil))
         (branch (t3-name-bounds-total-branch lib *library-x* absent))
         (base (library-library-transport-argument lib zero branch 1))
         (proved (t3-list-bounds-tail-induction lib formula step base)))
      (library-library-lemma lib "T3-NAME-TOTAL-NATURAL" formula proved nil))))

(defun t3-name-bounds-membership-cap-hit (tests lib by-name found head tail integers)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (proof-term-at (car (last tests)) 0))
         (match (proof-proof-assume proof test t))
         (reflexive (proof-proof-reflexive proof found))
         (names-equal (proof-proof-rewrite proof reflexive match
                                         (if by-name '(1 2 1 1) '(1 2 1 1 1))))
         (natural-tail (t3-name-bounds-total-natural lib *t3-list-bounds-tail*))
         (tail-nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE" (list tail)
                                                 (list natural-tail)))
         (head-bound (t3-size-sum-at-least lib head tail-nonnegative integers t))
         (names-back (proof-proof-symmetric proof names-equal)))
      (proof-proof-rewrite proof head-bound names-back '(1 1 2)))))

(defun t3-name-bounds-membership-cap-miss
    (value lib predicate formula present word head tail integers)
  (if (not (proof-is-call value predicate))
      '(:failure "failure" "")
    (proof-with-checked-results ((child-tail (proof-term-at value 2)))
      (if (not (equal child-tail *t3-list-bounds-tail*))
          '(:failure "failure" "")
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results
              ((ih (t3-list-bounds-tail-hypothesis lib formula present))
               (member-step (proof-proof-assume proof value t))
               (child-bound (proof-proof-prove-if proof ih member-step))
               (types (t3-digit-capacity-capacity-type lib (t3-list-bounds-string-to-chars word)))
               (head-nonnegative (library-library-cite lib "POSITIVE-NONNEGATIVE" (list head) types))
               (tail-bound (t3-size-sum-at-least lib tail head-nonnegative integers nil)))
            (t3-size-chain lib child-bound tail-bound integers)))))))

(defund t3-name-bounds-membership-cap-leaf
    (value tests lib template formula predicate by-name present word found head tail integers structure)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((goal (proof-subst template (list (cons *proof-result* value))))
         (result (if (equal value *library-x*)
                     (t3-name-bounds-membership-cap-hit tests lib by-name found head tail integers)
                   (t3-name-bounds-membership-cap-miss
                    value lib predicate formula present word head tail integers)))
         (structure-back (proof-proof-symmetric proof structure))
         (result (proof-proof-rewrite proof result structure-back '(1 1 1)))
         (result (proof-proof-tidy proof result)))
      (t3-scan-conclusion lib goal result))))

(defun t3-name-bounds-membership-cap-leaves
    (n request lib template formula predicate by-name present word found head tail integers structure)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "t3-name-bounds-membership-cap-leaves"))
   ((failure-p request) request)
   ((not (eq (car request) :t3-book-term-collections-leaf)) request)
   (t (proof-with-checked-results
          ((step (t3-name-bounds-membership-cap-leaf
                  (cadr request) (caddr request) lib template formula predicate by-name present
                  word found head tail integers structure))
           (next (t3-book-term-collections-by-value-resume lib template request step)))
        (t3-name-bounds-membership-cap-leaves
         (1- n) next lib template formula predicate by-name present word found head tail integers structure)))))

(defun t3-name-bounds-membership-cap (lib predicate)
  (let* ((proof (library-library-proof lib))
         (by-name (equal predicate *t3-name-bounds-member-name*))
         (member-term (list predicate *library-y* *library-x*))
         (found (if by-name (t3-name-bounds-name-capacity *library-y*)
                  (t3-name-bounds-symbol-capacity *library-y*)))
         (template (proof-ite *proof-result*
                               (library-le found (t3-name-bounds-name-total *library-x*))
                               *proof-true*))
         (word (list *t3-name-bounds-symbol-name* (list *library-car* *library-x*)))
         (head (t3-name-bounds-name-capacity word))
         (tail (t3-name-bounds-name-total *t3-list-bounds-tail*))
         (found-word (if by-name *library-y* (list *t3-name-bounds-symbol-name* *library-y*))))
    (proof-with-checked-results
        ((formula (proof-subst template (list (cons *proof-result* member-term))))
         (present (proof-proof-assume proof *t3-list-bounds-cons-x* t))
         (types (t3-digit-capacity-capacity-type lib (t3-list-bounds-string-to-chars word)))
         (int-tail (t3-name-bounds-total-integer lib *t3-list-bounds-tail*))
         (found-type (t3-digit-capacity-capacity-type lib (t3-list-bounds-string-to-chars found-word)))
         (int-total (t3-name-bounds-total-integer lib *library-x*))
         (integers (list (car types) int-tail (car found-type) int-total))
         (structure (t3-name-bounds-total-branch lib *library-x* present))
         (recursive (t3-list-bounds-endp-branch lib member-term present))
         (body (t3-book-term-collections-step-term-at recursive 2))
         (request (t3-book-term-collections-by-value-start lib body nil))
         (step (t3-name-bounds-membership-cap-leaves
                1000000 request lib template formula predicate by-name present word found
                head tail integers structure))
         (recursive-back (proof-proof-symmetric proof recursive))
         (step (proof-proof-rewrite-result proof step recursive-back template *proof-result*))
         (absent (proof-proof-assume proof *t3-list-bounds-cons-x* nil))
         (atomic (t3-list-bounds-endp-branch lib member-term absent))
         (base-goal (proof-subst template (list (cons *proof-result* *proof-false*))))
         (base (t3-logic-libraryproofs-prove-formula lib base-goal nil nil))
         (atomic-back (proof-proof-symmetric proof atomic))
         (base (proof-proof-rewrite-result proof base atomic-back template *proof-result*))
         (label (if by-name "T3-NAME-MEMBER-CAPACITY" "T3-SYMBOL-MEMBER-CAPACITY"))
         (proved (t3-list-bounds-tail-induction lib formula step base)))
      (library-library-lemma lib label formula proved nil))))

(defun t3-name-bounds-available-member-bound (lib step)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (parts (proof-list-of-length literal 3))
       (label (if (equal (car parts) *t3-name-bounds-member-name*)
                  "T3-NAME-MEMBER-CAPACITY" "T3-SYMBOL-MEMBER-CAPACITY"))
       (rule (library-library-cite lib label (list (caddr parts) (cadr parts)) nil)))
    (proof-proof-prove-if (library-library-proof lib) rule step)))

(defun t3-name-bounds-build (lib)
  (proof-with-checked-results
      ((lib (t3-name-bounds-total-fold lib))
       (lib (t3-name-bounds-membership-cap lib *t3-name-bounds-member-equal*)))
    (t3-name-bounds-membership-cap lib *t3-name-bounds-member-name*)))
