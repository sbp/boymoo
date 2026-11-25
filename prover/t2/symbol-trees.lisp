(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t2-symbol-trees-treep* (proof-sym "SYMBOL-BTREEP" "ACL2"))
(defconst *t2-symbol-trees-update* (proof-sym "SYMBOL-BTREE-UPDATE" "ACL2"))
(defconst *t2-symbol-trees-find* (proof-sym "SYMBOL-BTREE-FIND" "ACL2"))
(defconst *t2-symbol-trees-to-alist* (proof-sym "SYMBOL-BTREE-TO-ALIST" "ACL2"))
(defconst *t2-symbol-trees-with-acc* (proof-sym "SYMBOL-BTREE-TO-ALIST-AUX" "ACL2"))
(defconst *t2-symbol-trees-find-depth-acc* (proof-sym "SYMBOL-BTREE-FIND/DEPTH-AUX" "ACL2"))
(defconst *t2-symbol-trees-find-depth* (proof-sym "SYMBOL-BTREE-FIND/DEPTH" "ACL2"))
(defconst *t2-symbol-trees-update-depth* (proof-sym "SYMBOL-BTREE-UPDATE/DEPTH" "ACL2"))
(defconst *t2-symbol-trees-update-find-depth* (proof-sym "SYMBOL-BTREE-UPDATE/FIND/DEPTH" "ACL2"))
(defconst *t2-symbol-trees-key-depth* (proof-sym "SYMBOL-BTREE-KEY-DEPTH" "ACL2"))
(defconst *t2-symbol-trees-symbolp* (proof-cl "SYMBOLP"))

(defconst *t2-symbol-trees-depth-positions*
  (list (cons *t2-symbol-trees-find-depth-acc* 2)
        (cons *t2-symbol-trees-find-depth* 2)
        (cons *t2-symbol-trees-update-depth* 3)
        (cons *t2-symbol-trees-update-find-depth* 3)))

; A binding marked :library obtains its value and the updated Library from
; a pair. A failure is paired with the Library as it stands at that point.
(defmacro t2-symbol-trees-with-results (bindings result)
  (if (endp bindings)
      result
    (let ((name (caar bindings))
          (form (cadar bindings))
          (rest (cdr bindings)))
      (if (eq (caddar bindings) :library)
          `(let ((t2-symbol-trees-paired-result ,form))
             (if (failure-p t2-symbol-trees-paired-result)
                 (cons t2-symbol-trees-paired-result lib)
               (let ((,name (car t2-symbol-trees-paired-result))
                     (lib (cdr t2-symbol-trees-paired-result)))
                 (if (failure-p ,name)
                     t2-symbol-trees-paired-result
                   (t2-symbol-trees-with-results ,rest ,result)))))
        `(let ((,name ,form))
           (if (failure-p ,name)
               (cons ,name lib)
             (t2-symbol-trees-with-results ,rest ,result)))))))

; The caller can continue after an unproved case with the Library produced
; by normalization. Use the Reduction hooks with the Search result pair.
(defund t2-symbol-trees-normalize-attempt (lib reduction search goal context replies)
  (let* ((configured (t2-book-logic-search-with-hooks
                      search '(:normalize :replacement :can-open) replies))
         (result (t2-book-logic-search-normalize configured goal context -1 nil)))
    (if (failure-p result)
        (cons result lib)
      (let* ((value (car result))
             (lib (t2-book-logic-search-lib (cadr result))))
        (cond ((t2-book-logic-search-request-p value)
               (let ((lib (t2-book-logic-search-request-lib value)))
                 (t2-symbol-trees-with-results
                  ((reply (t2-structural-proof-reduction-reply reduction value)))
                  (list :reply lib reply))))
              ((failure-p value) (cons value lib))
              (t (t2-symbol-trees-with-results
                  ((step (or value (t2-arithmetic-arithmetic-reflexive lib goal))))
                  (cons (list step (cddr result)) lib))))))))

(defun t2-symbol-trees-normalize-case (n lib reduction search goal context replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (cons '(:failure "fuel" "t2-symbol-trees-normalize-case") lib)
    (let ((result (t2-symbol-trees-normalize-attempt lib reduction search goal context replies)))
      (if (eq (car result) :reply)
          (t2-symbol-trees-normalize-case
           (1- n) (cadr result) reduction search goal context
           (append replies (list (caddr result))))
        result))))

(defun t2-symbol-trees-normal-form (lib goal expand tests premises equations)
  (t2-symbol-trees-with-results
   ((reduction (t2-structural-proof-reduction-init lib expand tests premises equations))
    (search (t2-book-logic-search-init lib nil nil
                                      (t2-structural-proof-reduction-budget reduction) nil)))
   (t2-symbol-trees-normalize-case 1000000 lib reduction search goal
                                   (t2-structural-proof-reduction-facts reduction) nil)))

(defun t2-symbol-trees-components (lib premise tests count)
  (t2-symbol-trees-with-results
   ((term (proof-step-first premise))
    (normal (t2-symbol-trees-normal-form lib term (list (list :term term)) tests nil nil)
            :library)
    (opened (library-inherited proof-proof-rewrite lib premise (car normal) '(1)))
    (parts (t2-power-conjuncts lib opened count)))
   (cons parts lib)))

(defund t2-symbol-trees-close-case (lib goal expand tests premises equations may-split)
  (t2-symbol-trees-with-results
   ((normal (t2-symbol-trees-normal-form lib goal expand tests premises equations) :library)
    (normalized (car normal))
    (literal (proof-step-first normalized))
    (target (proof-term-at literal 2)))
   (if (equal target *proof-true*)
       (t2-symbol-trees-with-results
        ((step (library-inherited proof-proof-true-from-eq lib normalized)))
        (cons step lib))
     (t2-symbol-trees-with-results
      ((known (t2-tactics-ruler-facts-find (cadr normal) target))
       (aligned (cond ((car known) (car known))
                      ((proof-is-call target *proof-equal*)
                       (proof-with-checked-results
                        ((terms (proof-list-of-length (cdr target) 2)))
                        (t2-structural-proof-congruence lib (car terms) (cadr terms)))))))
      (if aligned
          (t2-symbol-trees-with-results
           ((step (library-inherited proof-proof-transport lib aligned normalized)))
           (cons step lib))
        (t2-symbol-trees-with-results
         ((test (t2-book-logic-search-first-test nil target)))
         (if (or (not test) (equal test 0) (equal test "") (not may-split))
             (t2-symbol-trees-with-results
              ((text (proof-write target)))
              (cons '(:failure "unproved" "")
                    lib))
           (list :split test lib))))))))

(defun t2-symbol-trees-solve (lib goal expand tests premises equations depth)
  (declare (xargs :measure (nfix depth)))
  (let* ((may-split (o< (nfix (1- depth)) (nfix depth)))
         (result (t2-symbol-trees-close-case lib goal expand tests premises equations may-split)))
    (if (and may-split (eq (car result) :split))
        (let ((test (cadr result))
              (lib (caddr result)))
          (t2-symbol-trees-with-results
           ((left (t2-symbol-trees-solve lib goal expand (append tests (list (list test t)))
                                        premises equations (1- depth))
                  :library)
            (right (t2-symbol-trees-solve lib goal expand (append tests (list (list test nil)))
                                         premises equations (1- depth))
                   :library)
            (step (library-inherited proof-proof-cases lib test left right)))
           (cons step lib)))
      result)))

(defun t2-symbol-trees-children (tree)
  (let ((tail (list *t2-book-logic-cdr* tree)))
    (list (list *t2-book-logic-car* tail) (list *t2-book-logic-cdr* tail))))

(defun t2-symbol-trees-update-hypothesis
    (lib formula tree child tests type-fact key-type)
  (proof-with-checked-results
   ((instance (t2-structural-proof-smaller lib formula tree child tests nil nil))
    (premise (t2-power-join lib (list type-fact key-type)))
    (updated (t2-arithmetic-arithmetic-modus-ponens lib (car instance) premise)))
   (list updated (cadr instance))))

(defun t2-symbol-trees-update-preserves-type (lib formula)
  (t2-symbol-trees-with-results
   ((terms (proof-list-of-length (cdr formula) 2))
    (domain (car terms))
    (result (cadr terms))
    (update (proof-term-at result 1))
    (arguments (proof-list-of-length (cdr update) 3))
    (key (car arguments))
    (tree (caddr arguments))
    (branch (list *proof-consp* tree))
    (assumed (library-inherited proof-proof-assume lib domain t))
    (types (t2-arithmetic-arithmetic-conjunct lib assumed))
    (tree-type (car types))
    (key-type (cadr types))
    (tree-literal (proof-step-first tree-type))
    (shape (if (equal tree-literal (list *t2-symbol-trees-treep* tree))
               (proof-with-checked-results
                ((key-literal (proof-step-first key-type)))
                (if (equal key-literal (list *t2-symbol-trees-symbolp* key))
                    t
                  '(:failure "recipe-mismatch" "")))
             '(:failure "recipe-mismatch" "")))
    (tests (list (list branch shape)))
    (parts (t2-symbol-trees-components lib tree-type tests 5) :library)
    (children (t2-symbol-trees-children tree))
    (left (t2-symbol-trees-update-hypothesis
           lib formula tree (car children) tests (nth 3 parts) key-type))
    (right (t2-symbol-trees-update-hypothesis
            lib formula tree (cadr children) tests (nth 4 parts) key-type))
    (expand (list (list :arg *t2-symbol-trees-update* -1 tree)
                  (list :constructed *t2-symbol-trees-treep* 1)))
    (cons-case (t2-symbol-trees-solve
                lib result expand tests
                (append (cons key-type parts) (list (car left) (car right))) nil 10)
               :library)
    (atom-case (t2-symbol-trees-solve lib result expand (list (list branch nil))
                                         (list key-type) nil 10)
               :library)
    (cases (library-inherited proof-proof-cases lib branch cons-case atom-case))
    (proof (t2-power-implication lib domain cases))
    (step (t2-structural-proof-induct lib formula tree proof (list (cadr left) (cadr right)))))
   (cons step lib)))

(defun t2-symbol-trees-rewrite-equations (lib steps equality)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      nil
    (proof-with-checked-results
     ((step (library-inherited proof-proof-rewrite-first lib (car steps) equality))
      (rest (t2-symbol-trees-rewrite-equations lib (cdr steps) equality)))
     (cons step rest))))

(defun t2-symbol-trees-lookup-after-update-solve-test
    (same lib formula tree branch nonempty same-key steps)
  (let ((equations (if nonempty steps nil))
        (expand (list (list :arg *t2-symbol-trees-update* -1 tree)
                      (list :arg *t2-symbol-trees-find* -1 tree)
                      (list :constructed *t2-symbol-trees-find* -1))))
    (t2-symbol-trees-with-results
     ((equations
       (if same
           (proof-with-checked-results
            ((equality (library-inherited proof-proof-assume lib same-key t))
             (rest (t2-symbol-trees-rewrite-equations lib equations equality)))
            (cons equality rest))
         equations))
      (step (t2-symbol-trees-solve
             lib formula expand (list (list branch nonempty) (list same-key same))
             nil equations 10)
            :library))
     (cons step lib))))

(defun t2-symbol-trees-lookup-branch (lib formula tree branch same-key steps nonempty)
  (t2-symbol-trees-with-results
   ((yes (t2-symbol-trees-lookup-after-update-solve-test
          t lib formula tree branch nonempty same-key steps) :library)
    (no (t2-symbol-trees-lookup-after-update-solve-test
         nil lib formula tree branch nonempty same-key steps) :library)
    (step (library-inherited proof-proof-cases lib same-key yes no)))
   (cons step lib)))

(defun t2-symbol-trees-lookup-after-update (lib formula)
  (t2-symbol-trees-with-results
   ((terms (proof-list-of-length (cdr formula) 2))
    (left (car terms))
    (right (cadr terms))
    (lookup (proof-list-of-length (cdr left) 2))
    (changes (cadr lookup))
    (update (proof-list-of-length (cdr changes) 3))
    (key (car update))
    (tree (caddr update))
    (same-key (proof-eq (car lookup) key))
    (test (proof-term-at right 1))
    (same-test (if (equal test same-key) test '(:failure "recipe-mismatch" "")))
    (branch (list *proof-consp* tree))
    (tests (list (list branch t)))
    (children (t2-symbol-trees-children tree))
    (first (t2-structural-proof-smaller lib formula tree (car children) tests nil nil))
    (second (t2-structural-proof-smaller lib formula tree (cadr children) tests nil nil))
    (steps (list (car first) (car second)))
    (yes (t2-symbol-trees-lookup-branch lib formula tree branch same-test steps t) :library)
    (no (t2-symbol-trees-lookup-branch lib formula tree branch same-test steps nil) :library)
    (cases (library-inherited proof-proof-cases lib branch yes no))
    (step (t2-structural-proof-induct lib formula tree cases (list (cadr first) (cadr second)))))
   (cons step lib)))

(defun t2-symbol-trees-accumulator-branch
    (lib formula tree accumulator left right branch head-type
         right-instance associativity expand has-entry)
  (let* ((head (list *t2-book-logic-car* tree))
         (raw-right (list *t2-symbol-trees-with-acc* right accumulator))
         (next-acc (if has-entry (list *proof-cons* head raw-right) raw-right)))
    (t2-symbol-trees-with-results
     ((instance (t2-structural-proof-smaller lib formula tree left branch nil
                                             (list (list accumulator next-acc))))
      (to-right (list *t2-symbol-trees-to-alist* right))
      (trailing (if has-entry (list *proof-cons* head to-right) to-right))
      (regroup (library-library-cite lib associativity
                                     (list (list *t2-symbol-trees-to-alist* left)
                                           trailing accumulator) nil))
      (rewritten (library-inherited proof-proof-rewrite-first lib (car instance) right-instance))
      (equations (list (car instance) rewritten right-instance regroup))
      (step (t2-symbol-trees-solve
             lib formula expand (append branch (list (list head-type has-entry)))
             nil equations 10)
            :library))
     (cons (list step (cadr instance)) lib))))

(defun t2-symbol-trees-alist-accumulator (lib formula)
  (t2-symbol-trees-with-results
   ((conversion (proof-term-at formula 1))
    (args (proof-list-of-length (cdr conversion) 2))
    (tree (car args))
    (accumulator (cadr args))
    (root-type (list *proof-consp* tree))
    (head-type (list *proof-consp* (list *t2-book-logic-car* tree)))
    (children (t2-symbol-trees-children tree))
    (left (car children))
    (right (cadr children))
    (branch (list (list root-type t)))
    (right-instance (t2-structural-proof-smaller lib formula tree right branch nil nil))
    (associativity (t2-structural-lists-append-associativity lib) :library)
    (expand (list (list :arg *t2-symbol-trees-with-acc* 1 tree)
                  (list :arg *t2-symbol-trees-to-alist* 1 tree)
                  (list :constructed *t2-structural-lists-append* 1)))
    (with-entry (t2-symbol-trees-accumulator-branch
                 lib formula tree accumulator left right branch head-type
                 (car right-instance) associativity expand t)
                :library)
    (without-entry (t2-symbol-trees-accumulator-branch
                    lib formula tree accumulator left right branch head-type
                    (car right-instance) associativity expand nil)
                   :library)
    (yes (library-inherited proof-proof-cases lib head-type (car with-entry) (car without-entry)))
    (no (t2-symbol-trees-solve lib formula expand (list (list root-type nil)) nil nil 10)
        :library)
    (cases (library-inherited proof-proof-cases lib root-type yes no))
    (substitutions (list (cadr right-instance) (cadr with-entry) (cadr without-entry)))
    (step (t2-structural-proof-induct lib formula tree cases substitutions)))
   (cons step lib)))

(defun t2-symbol-trees-alist-type-hypothesis (lib formula tree child tests typed facts index)
  (proof-with-checked-results
   ((instance (t2-structural-proof-smaller lib formula tree child tests nil nil))
    (step (if typed
              (t2-arithmetic-arithmetic-modus-ponens lib (car instance) (nth (+ 3 index) facts))
            (car instance))))
   (list step (cadr instance))))

(defun t2-symbol-trees-alist-type-expansion (conversion predicate)
  (list (list :term conversion)
        (list :constructed predicate 1)
        (list :constructed *t2-structural-lists-append* 1)))

(defun t2-symbol-trees-alist-type-case
    (has-entry lib result conversion predicate tree tests entry facts smaller-types name first remainder)
  (let* ((expand (t2-symbol-trees-alist-type-expansion conversion predicate))
         (extra (append tests (list (list entry has-entry))))
         (rest (if has-entry
                   (list *proof-cons* (list *t2-book-logic-car* tree) remainder)
                 remainder))
         (fields (take (min 2 (len facts)) facts)))
    (t2-symbol-trees-with-results
     ((cdr-type
       (if has-entry
           (t2-symbol-trees-solve lib (list predicate rest) expand extra
                                     (append fields (list (cadr smaller-types))) nil 10)
         (cons (cadr smaller-types) lib))
       :library)
      (preserves (library-library-cite lib name (list first rest) nil))
      (conjunction (t2-power-join lib (list (car smaller-types) cdr-type)))
      (combined (t2-arithmetic-arithmetic-modus-ponens lib preserves conjunction))
      (step (t2-symbol-trees-solve lib result expand extra (append fields (list combined)) nil 10)
            :library))
     (cons step lib))))

(defun t2-symbol-trees-alist-type-positive
    (lib typed result conversion predicate tree tests entry facts smaller-types name first remainder)
  (t2-symbol-trees-with-results
   ((yes (t2-symbol-trees-alist-type-case t lib result conversion predicate tree tests
                                         entry facts smaller-types name first remainder)
         :library))
   (if typed
       (t2-symbol-trees-with-results
        ((step (if (member-equal (proof-neg entry) (proof-step-clause yes))
                   (library-inherited proof-proof-discharge lib yes (car facts))
                 yes)))
        (cons step lib))
     (t2-symbol-trees-with-results
      ((no (t2-symbol-trees-alist-type-case nil lib result conversion predicate tree tests
                                           entry facts smaller-types name first remainder)
           :library)
       (step (library-inherited proof-proof-cases lib entry yes no)))
      (cons step lib)))))

(defun t2-symbol-trees-alist-type (lib formula)
  (t2-symbol-trees-with-results
   ((terms (if (proof-is-call formula *library-implies*)
               (proof-list-of-length (cdr formula) 2)
             (list :none formula)))
    (domain (car terms))
    (typed (not (eq domain :none)))
    (result (cadr terms))
    (fields (proof-list-of-length result 2))
    (predicate (car fields))
    (conversion (cadr fields))
    (tree (proof-term-at conversion 1))
    (branch (list *proof-consp* tree))
    (entry (list *proof-consp* (list *t2-book-logic-car* tree)))
    (tests (list (list branch t)))
    (facts (if typed
               (proof-with-checked-results
                ((assumed (library-inherited proof-proof-assume lib domain t)))
                (t2-symbol-trees-components lib assumed tests 5))
             (cons nil lib))
           :library)
    (children (t2-symbol-trees-children tree))
    (left (t2-symbol-trees-alist-type-hypothesis lib formula tree (car children) tests typed facts 0))
    (right (t2-symbol-trees-alist-type-hypothesis lib formula tree (cadr children) tests typed facts 1))
    (smaller-types (list (car left) (car right)))
    (name (t2-structural-lists-preserve-list-predicate lib *t2-structural-lists-append* predicate)
          :library)
    (first (cadr (proof-step-first (car smaller-types))))
    (remainder (cadr (proof-step-first (cadr smaller-types))))
    (yes (t2-symbol-trees-alist-type-positive lib typed result conversion predicate tree tests
                                             entry facts smaller-types name first remainder)
         :library)
    (expand (t2-symbol-trees-alist-type-expansion conversion predicate))
    (no (t2-symbol-trees-solve lib result expand (list (list branch nil)) nil nil 10) :library)
    (conclusion (library-inherited proof-proof-cases lib branch yes no))
    (conclusion (if typed (t2-power-implication lib domain conclusion) conclusion))
    (step (t2-structural-proof-induct lib formula tree conclusion (list (cadr left) (cadr right)))))
   (cons step lib)))

(defun t2-symbol-trees-aligned-depth-positions (source tree-index)
  (table-update (list (cons source tree-index))
                  (list (cons *t2-symbol-trees-find* 2)
                        (cons *t2-symbol-trees-update* 3)
                        (cons *t2-symbol-trees-key-depth* 2))))

(defun t2-symbol-trees-depth-expansion (positions tree)
  (declare (xargs :measure (acl2-count positions)))
  (if (endp positions)
      nil
    (cons (list :arg (caar positions) (cdar positions) tree)
          (t2-symbol-trees-depth-expansion (cdr positions) tree))))

(defun t2-symbol-trees-aligned-depth (lib formula)
  (t2-symbol-trees-with-results
   ((left (proof-term-at formula 1))
    (source (t2-book-logic-head left))
    (position (assoc-equal source *t2-symbol-trees-depth-positions*))
    (tree-index (if position
                    (cdr position)
                  (table-delete *t2-symbol-trees-depth-positions* source)))
    (tree (proof-term-at left tree-index))
    (branch (list *proof-consp* tree))
    (tests (list (list branch t)))
    (accumulator (if (equal source *t2-symbol-trees-find-depth-acc*)
                     (proof-with-checked-results
                      ((acc (proof-term-at left 3)))
                      (list (list acc (library-plus *proof-one* acc))))
                   nil))
    (children (t2-symbol-trees-children tree))
    (first (t2-structural-proof-smaller lib formula tree (car children) tests nil accumulator))
    (second (t2-structural-proof-smaller lib formula tree (cadr children) tests nil accumulator))
    (expand (t2-symbol-trees-depth-expansion
             (t2-symbol-trees-aligned-depth-positions source tree-index) tree))
    (yes (t2-symbol-trees-solve lib formula expand tests nil (list (car first) (car second)) 10)
         :library)
    (no (t2-symbol-trees-solve lib formula expand (list (list branch nil)) nil nil 10) :library)
    (cases (library-inherited proof-proof-cases lib branch yes no))
    (step (t2-structural-proof-induct lib formula tree cases (list (cadr first) (cadr second)))))
   (cons step lib)))

(defun t2-symbol-trees-prove-implication (lib formula)
  (t2-symbol-trees-with-results
   ((result (proof-term-at formula 2))
    (head (t2-book-logic-head result)))
   (cond ((equal head *t2-symbol-trees-treep*)
          (t2-symbol-trees-with-results
           ((update (proof-term-at result 1)))
           (if (proof-is-call update *t2-symbol-trees-update*)
               (t2-symbol-trees-update-preserves-type lib formula)
             (cons nil lib))))
         ((equal head *t2-structural-lists-symbol-alistp*)
          (t2-symbol-trees-with-results
           ((conversion (proof-term-at result 1)))
           (if (proof-is-call conversion *t2-symbol-trees-to-alist*)
               (t2-symbol-trees-alist-type lib formula)
             (cons nil lib))))
         (t (cons nil lib)))))

(defun t2-symbol-trees-prove-equality (lib formula)
  (t2-symbol-trees-with-results
   ((terms (proof-list-of-length (cdr formula) 2))
    (left (car terms))
    (right (cadr terms))
    (lookup-update (if (proof-is-call left *t2-symbol-trees-find*)
                       (proof-with-checked-results
                        ((changes (proof-term-at left 2)))
                        (and (proof-is-call changes *t2-symbol-trees-update*)
                             (proof-is-call right *proof-if*)))
                     nil)))
   (cond (lookup-update (t2-symbol-trees-lookup-after-update lib formula))
         ((and (proof-is-call left *t2-symbol-trees-with-acc*)
               (proof-is-call right *t2-structural-lists-append*))
          (t2-symbol-trees-alist-accumulator lib formula))
         ((and (assoc-equal (t2-book-logic-head left) *t2-symbol-trees-depth-positions*)
               (proof-is-call right *proof-cons*))
          (t2-symbol-trees-aligned-depth lib formula))
         (t (cons nil lib)))))

(defun t2-symbol-trees-prove (lib formula)
  (cond ((proof-is-call formula *library-implies*)
         (t2-symbol-trees-prove-implication lib formula))
        ((proof-is-call formula *proof-equal*)
         (t2-symbol-trees-prove-equality lib formula))
        ((proof-is-call formula *t2-structural-lists-true-listp*)
         (t2-symbol-trees-with-results
          ((conversion (proof-term-at formula 1)))
          (if (proof-is-call conversion *t2-symbol-trees-to-alist*)
              (t2-symbol-trees-alist-type lib formula)
            (cons nil lib))))
        (t (cons nil lib))))
