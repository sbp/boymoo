(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-constructors-stringp* (proof-cl "STRINGP"))
(defconst *t4-constructors-symbolp* (proof-cl "SYMBOLP"))
(defconst *t4-constructors-keywordp* (proof-cl "KEYWORDP"))
(defconst *t4-constructors-coerce* (proof-cl "COERCE"))
(defconst *t4-constructors-null* (proof-cl "NULL"))
(defconst *t4-constructors-eq* (proof-cl "EQ"))
(defconst *t4-constructors-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *t4-constructors-tree* (proof-sym "TREEP" "XDOC"))
(defconst *t4-constructors-tree-list* (proof-sym "TREE-LISTP" "XDOC"))
(defconst *t4-constructors-tree-tag* (proof-sym "TREE-TAGP" "XDOC"))
(defconst *t4-constructors-make-tag* (proof-sym "MAKE-TREE-TAG" "XDOC"))
(defconst *t4-constructors-make-direct* (proof-sym "MAKE-TREE-DIR/&&" "XDOC"))

(defun t4-constructors-request-p (result)
  (eq (car result) :t4-request))

(defun t4-constructors-failure-p (result)
  (eq (car result) :t4-constructors-failure))

(defun t4-constructors-keep-error (value lib)
  (if (failure-p value)
      (list :t4-constructors-failure value lib)
    value))

(defun t4-constructors-finish (result lib keep-library)
  (cond ((t4-constructors-failure-p result)
         (if keep-library (cons (cadr result) (caddr result)) (cadr result)))
        ((and keep-library (failure-p result)) (cons result lib))
        (t result)))

(defun t4-constructors-query (operation arguments lib replies)
  (if (endp replies)
      (list :t4-request operation arguments lib)
    (let ((reply (car replies)))
      (if (failure-p reply)
          reply
        (list (car reply) (cdr reply) (cdr replies))))))

; Paired and tripled results thread the Library and the unused replies.
(defmacro t4-constructors-with (bindings body &optional library)
  (if (endp bindings)
      (if library `(t4-constructors-keep-error ,body ,library) body)
    (let* ((binding (car bindings))
           (target (car binding))
           (value (if (consp target) (car target) target))
           (failure (if library `(t4-constructors-keep-error ,value ,library) value))
           (next `(t4-constructors-with ,(cdr bindings) ,body ,library)))
      `(let ((,value ,(cadr binding)))
         (cond
          ((failure-p ,value) ,failure)
          ((or (t4-constructors-request-p ,value) (t4-constructors-failure-p ,value)) ,value)
          (t
           ,(if (consp target)
                `(let ((,value (car ,value))
                        (,(cadr target) ,(if (cddr target) `(cadr ,value) `(cdr ,value)))
                        ,@(and (cddr target) `((,(caddr target) (caddr ,value)))))
                   (declare (ignorable ,@target))
                   (cond
                    ((failure-p ,value) ,failure)
                    ((or (t4-constructors-request-p ,value) (t4-constructors-failure-p ,value)) ,value)
                    (t ,next)))
              next)))))))

(defmacro t4-constructors-with-library (bindings body)
  `(t4-constructors-with ,bindings ,body lib))

(defun t4-constructors-term-path (term indices)
  (declare (xargs :measure (acl2-count indices)))
  (if (endp indices)
      term
    (proof-with-checked-results ((part (proof-term-at term (car indices))))
      (t4-constructors-term-path part (cdr indices)))))

(defmacro t4-constructors-at (term &rest indices)
  `(t4-constructors-term-path ,term ',indices))

(defun t4-constructors-step-path (step indices)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((first (proof-step-first step)))
      (t4-constructors-term-path first indices))))

(defmacro t4-constructors-first (step &rest indices)
  `(t4-constructors-step-path ,step ',indices))

(defun t4-constructors-defined-p (lib name)
  (if (assoc-equal name (proof-proof-definitions (library-library-proof lib))) t nil))

(defun t4-constructors-has-lemma-p (lib name)
  (if (assoc-equal (proof-sym (concatenate 'string "SELF-" name) "ACL2")
                   (proof-proof-facts (library-library-proof lib)))
      t
    nil))

(defun t4-constructors-implied (formula)
  (if (proof-is-call formula *library-implies*)
      (proof-list-of-length (cdr formula) 2)
    (list :none formula)))

(defun t4-constructors-known-or-fact (lib term evidence replies)
  (t4-constructors-with-library
      (((answer lib replies)
        (t4-constructors-query :known (list term evidence) lib replies)))
    (if (car answer)
        (list (car answer) lib replies)
      (t4-constructors-with-library
          (((answer lib replies)
            (t4-constructors-query :fact-proof (list term (cdr answer)) lib replies)))
        (list (car answer) lib replies)))))

(defun t4-constructors-scalar-result-open (n lib goal openings)
  (declare (xargs :measure (nfix n)))
  (cond ((not (acl2::o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-constructors-scalar-result-open"))
        ((not (proof-compound goal)) (cons goal openings))
        (t
         (proof-with-checked-results ((head (t4-constructors-at goal 0)))
           (if (proof-compound head)
               (proof-with-checked-results
                   ((opening (library-inherited proof-proof-beta lib goal))
                    (body (t4-constructors-first opening 2)))
                 (t4-constructors-scalar-result-open
                  (1- n) lib body (cons opening openings)))
             (cons goal openings))))))

(defun t4-constructors-scalar-result-transport (lib step openings)
  (declare (xargs :measure (acl2-count openings)))
  (if (endp openings)
      step
    (proof-with-checked-results
        ((step (library-inherited proof-proof-transport lib step (car openings))))
      (t4-constructors-scalar-result-transport lib step (cdr openings)))))

(defun t4-constructors-scalar-result-coerce-p (predicate value)
  (if (and (equal predicate *t4-constructors-stringp*)
           (proof-is-call value *t4-constructors-coerce*))
      (proof-with-checked-results ((kind (t4-constructors-at value 2)))
        (and (proof-is-call kind *proof-quote*)
             (not (equal kind (proof-quote (proof-cl "LIST"))))))
    nil))

(defun t4-constructors-scalar-result-coerce (lib value replies)
  (t4-constructors-with-library
      ((different-term (proof-neg (proof-eq (caddr value) (proof-quote (proof-cl "LIST")))))
       ((different lib replies)
        (t4-constructors-query :prove (list different-term nil (list *proof-not*)) lib replies))
       (fact (library-inherited proof-proof-fact lib "stringp-coerce"
                               (seq-zip (list *library-x* *library-y*) (cdr value))))
       (step (library-inherited proof-proof-modus-ponens lib fact different)))
    (list step lib replies)))

(defun t4-constructors-scalar-result-field-p (value)
  (if (proof-is-call value *t4-results-mv-nth*)
      (proof-with-checked-results ((index (t4-constructors-at value 1)))
        (proof-is-call index *proof-quote*))
    nil))

(defun t4-constructors-scalar-result-lift
    (lib step opening template)
  (proof-with-checked-results
      ((reverse (library-inherited proof-proof-symmetric lib opening)))
    (library-inherited proof-proof-rewrite-result lib step reverse template *proof-result*)))

(defun t4-constructors-scalar-result-case (lib value template yes no)
  (proof-with-checked-results
      ((yes-opening (library-inherited proof-proof-if-true lib value))
       (yes (t4-constructors-scalar-result-lift lib yes yes-opening template))
       (no-opening (library-inherited proof-proof-if-false lib value))
       (no (t4-constructors-scalar-result-lift lib no no-opening template)))
    (library-inherited proof-proof-cases lib (cadr value) yes no)))

(mutual-recursion
 (defun t4-constructors-scalar-result-visit
     (n value tests opened predicate lib budget replies)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (acl2::o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-constructors-scalar-result-visit"))
    ((zp budget) '(:failure "search-miss" ""))
    (t
     (let ((budget (1- budget))
           (expected (list predicate value))
           (template (list predicate *proof-result*)))
       (t4-constructors-with-library
           ((evidence (t4-structural-evidence-init lib tests nil))
            ((premise lib replies) (t4-constructors-known-or-fact lib expected evidence replies)))
         (if premise
             (list (cons premise budget) lib replies)
           (t4-constructors-with-library
               ((coerce-p (t4-constructors-scalar-result-coerce-p predicate value)))
             (cond
              (coerce-p
               (t4-constructors-with-library
                   (((step lib replies) (t4-constructors-scalar-result-coerce lib value replies)))
                 (list (cons step budget) lib replies)))
              ((proof-is-call value *proof-quote*)
               (t4-constructors-with-library
                   (((step lib replies) (t4-constructors-query :prove (list expected nil nil) lib replies)))
                 (list (cons step budget) lib replies)))
              ((proof-is-call value *proof-if*)
               (t4-constructors-scalar-result-by-value
                (1- n) value tests template opened predicate nil lib budget replies))
              ((and (equal predicate *proof-integerp*) (proof-compound value))
               (t4-constructors-with-library ((head (t4-constructors-at value 0)))
                 (cond
                  ((member-equal head (list *proof-plus* *proof-times* *proof-minus*))
                   (t4-constructors-with-library
                       (((parts lib replies)
                         (t4-constructors-scalar-result-visit-arguments
                          (1- n) (cdr value) tests opened predicate lib budget replies))
                        (step (t4-ordinals-ordinals-type-of lib value (car parts))))
                     (list (cons step (cdr parts)) lib replies)))
                  ((member-equal head (list *library-count* *library-len*))
                   (t4-constructors-with-library ((step (t4-ordinals-ordinals-type-of lib value nil)))
                     (list (cons step budget) lib replies)))
                  (t (t4-constructors-scalar-result-follow
                      (1- n) value tests opened predicate lib budget replies)))))
              (t (t4-constructors-scalar-result-follow
                  (1- n) value tests opened predicate lib budget replies))))))))))
 (defun t4-constructors-scalar-result-visit-arguments
     (n arguments tests opened predicate lib budget replies)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (acl2::o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-constructors-scalar-result-visit-arguments"))
    ((endp arguments) (list (cons nil budget) lib replies))
    (t
     (t4-constructors-with-library
         (((first lib replies)
           (t4-constructors-scalar-result-visit
            (1- n) (car arguments) tests opened predicate lib budget replies))
          ((rest lib replies)
           (t4-constructors-scalar-result-visit-arguments
            (1- n) (cdr arguments) tests opened predicate lib (cdr first) replies)))
       (list (cons (cons (car first) (car rest)) (cdr rest)) lib replies)))))
 (defun t4-constructors-scalar-result-follow
     (n value tests opened predicate lib budget replies)
   (declare (xargs :measure (nfix n)))
   (if (not (acl2::o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t4-constructors-scalar-result-follow")
     (t4-constructors-with-library
         ((field (t4-constructors-scalar-result-field-p value))
          ((selected lib) (if field (t4-results-projection lib value) (cons nil lib))))
       (let ((template (list predicate *proof-result*)))
         (if selected
             (t4-constructors-with-library
                 ((body (t4-constructors-first selected 2))
                  ((inner lib replies)
                   (t4-constructors-scalar-result-visit
                    (1- n) body tests opened predicate lib budget replies))
                  (step (t4-constructors-scalar-result-lift lib (car inner) selected template)))
               (list (cons step (cdr inner)) lib replies))
           (t4-constructors-with-library
               ((call (if field (t4-constructors-at value 2) value))
                (head (and (proof-compound call) (t4-constructors-at call 0))))
             (if (or (not (proof-compound call))
                     (not (t4-constructors-defined-p lib head))
                     (member-equal head opened))
                 '(:failure "search-miss" "")
               (let* ((index (and field (cadr value)))
                      (shape (if field
                                 (list predicate (list *t4-results-mv-nth* index *proof-result*))
                               template)))
                 (t4-constructors-with-library
                     ((equation (library-inherited proof-proof-unfold lib call))
                      (body (t4-constructors-first equation 2))
                      ((inner lib replies)
                       (t4-constructors-scalar-result-by-value
                        (1- n) body tests shape (cons head opened) predicate index lib budget replies))
                      (step (t4-constructors-scalar-result-lift lib (car inner) equation shape)))
                   (list (cons step (cdr inner)) lib replies))))))))))
 (defun t4-constructors-scalar-result-by-value
     (n value tests template opened predicate index lib budget replies)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (acl2::o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t4-constructors-scalar-result-by-value"))
    ((proof-is-call value *proof-if*)
     (t4-constructors-with-library
         ((parts (proof-list-of-length (cdr value) 3))
          (test (car parts))
          ((yes lib replies)
           (t4-constructors-scalar-result-by-value
            (1- n) (cadr parts) (append tests (list (list test t)))
            template opened predicate index lib budget replies))
          ((no lib replies)
           (t4-constructors-scalar-result-by-value
            (1- n) (caddr parts) (append tests (list (list test nil)))
            template opened predicate index lib (cdr yes) replies))
          (step (t4-constructors-scalar-result-case lib value template (car yes) (car no))))
       (list (cons step (cdr no)) lib replies)))
    (t
     (t4-constructors-with-library ((head (and (proof-compound value) (t4-constructors-at value 0))))
       (if (and (proof-compound value) (proof-compound head))
           (t4-constructors-with-library
               ((opening (library-inherited proof-proof-beta lib value))
                (body (t4-constructors-first opening 2))
                ((inner lib replies)
                 (t4-constructors-scalar-result-by-value
                  (1- n) body tests template opened predicate index lib budget replies))
                (step (t4-constructors-scalar-result-lift lib (car inner) opening template)))
             (list (cons step (cdr inner)) lib replies))
         (t4-constructors-with-library
             ((wrapped (if index (list *t4-results-mv-nth* index value) value))
              ((inner lib replies)
               (t4-constructors-scalar-result-visit
                (1- n) wrapped tests opened predicate lib budget replies))
              (literal (proof-step-first (car inner)))
              (expected (proof-subst template (list (cons *proof-result* value)))))
           (if (equal literal expected)
               (list inner lib replies)
             '(:failure "inference-mismatch" "")))))))))

(defun t4-constructors-scalar-result-attempt (lib formula replies)
  (t4-constructors-with-library
      ((parts (t4-constructors-implied formula))
       (guard (car parts))
       (opened (t4-constructors-scalar-result-open 1000000 lib (cadr parts) nil))
       (goal (car opened)))
    (if (not (and (proof-compound goal) (equal (len goal) 2)
                  (member-equal (car goal) (list *t4-constructors-stringp* *proof-integerp*))
                  (proof-compound (cadr goal))))
        (cons nil lib)
      (t4-constructors-with-library
          (((ignored lib replies) (t4-constructors-query :use-arithmetic nil lib replies))
           (guarded (and (not (eq guard :none)) guard))
           ((inner lib replies)
            (t4-constructors-scalar-result-visit
             1000000 (cadr goal) (and guarded (list (list guard t))) nil (car goal) lib 75 replies))
           (proof (t4-constructors-scalar-result-transport lib (car inner) (cdr opened)))
           (step (if guarded (t4-ordinals-ordinals-imply lib guard proof) proof)))
        (cons step lib)))))

(defun t4-constructors-collapse-identical-loop (n lib equation)
  (declare (xargs :measure (nfix n)))
  (if (not (acl2::o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t4-constructors-collapse-identical-loop")
    (t4-constructors-with ((body (t4-constructors-first equation 2)))
      (if (not (proof-is-call body *proof-if*))
          equation
        (t4-constructors-with
            ((yes (t4-constructors-at body 2))
             (no (t4-constructors-at body 3)))
          (if (not (equal yes no))
              equation
            (t4-constructors-with
                ((test (cadr body))
                 (yes-proof (library-inherited proof-proof-if-true lib body))
                 (no-proof (library-inherited proof-proof-if-false lib body))
                 (equality (library-inherited proof-proof-cases lib test yes-proof no-proof))
                 (chained (library-inherited proof-proof-chain lib equation (list equality))))
              (t4-constructors-collapse-identical-loop (1- n) lib chained))))))))

(defun t4-constructors-collapse-identical (lib equation)
  (t4-constructors-collapse-identical-loop 1000000 lib equation))

(defun t4-constructors-tree-cons-proper (lib right known replies)
  (let ((name "TREE-LIST-IS-PROPER"))
    (t4-constructors-with-library
        (((ignored lib replies)
          (if (t4-constructors-has-lemma-p lib name)
              (list nil lib replies)
            (let ((implication (list *library-implies*
                                     (list *t4-constructors-tree-list* *library-x*)
                                     (list *t4-results-true-list* *library-x*))))
              (t4-constructors-with-library
                  (((step lib replies)
                    (t4-constructors-query :recognizer-implication (list implication) lib replies)))
                (if (not step)
                    '(:failure "search-miss" "")
                  (t4-constructors-with-library
                      ((lib (library-library-lemma lib name implication step nil)))
                    (list nil lib replies)))))))
         (fact (library-library-cite lib name (list right) nil))
         (step (library-inherited proof-proof-modus-ponens lib fact known)))
      (list step lib replies))))

(defun t4-constructors-tree-cons (lib term target replies)
  (t4-constructors-with-library
      ((tree (t4-constructors-at term 1))
       (right (t4-constructors-at tree 2))
       (pair (library-inherited proof-proof-fact lib "consp-cons"
                               (seq-zip (list *library-x* *library-y*) (cdr tree))))
       (not-string (library-inherited proof-proof-fact lib "consp-not-stringp"
                                     (list (list *library-x* tree))))
       (denied (library-inherited proof-proof-modus-ponens lib not-string pair))
       (definition (library-inherited proof-proof-unfold lib term))
       (unfolded (t4-syntax-lists-choose lib definition denied))
       (known-list (t4-results-true-list-cons lib tree))
       (unfold-list (library-inherited proof-proof-rewrite lib unfolded known-list '(1 2 1)))
       (true-list (list *t4-results-true-list* right))
       (typed (list *t4-constructors-tree-list* right))
       (list-branch (t4-constructors-first unfold-list 2 2))
       (no-list-test (library-inherited proof-proof-select lib list-branch pair))
       (arranged (library-inherited proof-proof-rewrite lib unfold-list no-list-test '(1 2 2)))
       (arranged (t4-syntax-lists-projections lib arranged tree))
       (body (t4-constructors-first arranged 2)))
    (if (not (equal (cdr body) (list true-list target *proof-false*)))
        '(:failure "inference-mismatch" "")
      (t4-constructors-with-library
          ((known (library-inherited proof-proof-assume lib typed t))
           (evidence (t4-structural-evidence-init lib nil (list known)))
           ((answer lib replies)
            (t4-constructors-query :fact-proof (list true-list evidence) lib replies))
           ((proper lib replies)
            (if (car answer)
                (list (car answer) lib replies)
              (t4-constructors-tree-cons-proper lib right known replies)))
           (yes (t4-syntax-lists-choose lib arranged proper))
           (denial (library-inherited proof-proof-assume lib typed nil))
           (nil-or-true (library-inherited proof-proof-nil-or-true lib typed))
           (front (library-inherited proof-proof-front lib nil-or-true typed))
           (empty (library-inherited proof-proof-cut lib front denial))
           (stripped (library-inherited proof-proof-rewrite lib arranged empty '(1 2 2 2)))
           (branch (t4-constructors-first stripped 2 2))
           (branch (library-inherited proof-proof-reflexive lib branch))
           (branch (t4-constructors-collapse-identical lib branch))
           (stripped (library-inherited proof-proof-rewrite lib stripped branch '(1 2 2)))
           (stripped (t4-constructors-collapse-identical lib stripped))
           (other (library-inherited proof-proof-reflexive lib target))
           (other (library-inherited proof-proof-rewrite lib other empty '(1 2 2)))
           (other (t4-constructors-collapse-identical lib other))
           (reverse (library-inherited proof-proof-symmetric lib other))
           (no (library-inherited proof-proof-chain lib stripped (list reverse)))
           (step (library-inherited proof-proof-cases lib typed yes no)))
        (list step lib replies)))))

(defun t4-constructors-tree-constructor-branch (sign lib test start target)
  (t4-constructors-with
      ((condition (library-inherited proof-proof-assume lib test sign))
       (branch (t4-constructors-first start 2 1))
       (opened (library-inherited proof-proof-select lib branch condition))
       (branch-start (library-inherited proof-proof-rewrite lib start opened '(1 2 1)))
       (branch-start
        (if sign
            branch-start
          (t4-constructors-with ((not-nil (library-inherited proof-proof-not-nil lib)))
            (t4-syntax-lists-choose lib branch-start not-nil))))
       (wanted-term (t4-constructors-at target 2))
       (wanted (library-inherited proof-proof-select lib wanted-term condition))
       (reverse (library-inherited proof-proof-symmetric lib wanted)))
    (library-inherited proof-proof-chain lib branch-start (list reverse))))

(defun t4-constructors-tree-constructor-tag (lib start constructor target replies)
  (t4-constructors-with-library
      ((entry (t4-constructors-at constructor 1))
       (pair (library-inherited proof-proof-fact lib "consp-cons"
                               (seq-zip (list *library-x* *library-y*) (cdr entry))))
       (fact (library-inherited proof-proof-fact lib "consp-not-symbolp"
                               (list (list *library-x* entry))))
       (not-symbol (library-inherited proof-proof-modus-ponens lib fact pair))
       (unfolded (library-inherited proof-proof-unfold lib (list *t4-constructors-keywordp* entry)))
       (not-keyword (t4-syntax-lists-choose lib unfolded not-symbol))
       (body (t4-constructors-first start 2))
       (slot (t4-constructors-first not-keyword 1))
       (start (library-inherited proof-proof-rewrite-result lib start not-keyword
                                (proof-eq *proof-result* body) slot))
       (test (t4-constructors-first start 2 1))
       (not-nil (library-inherited proof-proof-not-nil lib))
       (picked (library-inherited proof-proof-select lib test not-nil))
       (start (library-inherited proof-proof-rewrite lib start picked '(1 2 1)))
       (test (t4-constructors-first start 2 1))
       ((typed lib) (t4-syntax-lists-constructed-view lib test entry))
       (start (library-inherited proof-proof-rewrite lib start typed '(1 2 1)))
       (test (t4-constructors-first typed 2 1))
       (yes (t4-constructors-tree-constructor-branch t lib test start target))
       (no (t4-constructors-tree-constructor-branch nil lib test start target))
       (step (library-inherited proof-proof-cases lib test yes no)))
    (list step lib replies)))

(defun t4-constructors-tree-constructor-direct (lib start original guard replies)
  (t4-constructors-with-library ((argument (t4-constructors-at original 1)))
    (if (not (equal guard (list *t4-constructors-keywordp* argument)))
        (list nil lib replies)
      (t4-constructors-with-library
          ((known (library-inherited proof-proof-assume lib guard t))
           (test (t4-constructors-first start 2 1))
           (selected (library-inherited proof-proof-select lib test known))
           (rewritten (library-inherited proof-proof-rewrite lib start selected '(1 2 1)))
           (proof (t4-syntax-lists-choose lib rewritten known))
           (step (t4-ordinals-ordinals-imply lib guard proof)))
        (list step lib replies)))))

(defun t4-constructors-tree-constructor-wrapper (lib start constructor target replies)
  (cond
   ((not (or (proof-is-call constructor *t4-constructors-make-tag*)
             (proof-is-call constructor *t4-constructors-make-direct*)))
    (list nil lib replies))
   (t
    (t4-constructors-with-library ((argument (t4-constructors-at constructor 1)))
      (if (not (proof-is-call argument *proof-quote*))
          (list nil lib replies)
        (t4-constructors-with-library
            ((typed (list *t4-constructors-keywordp* argument))
             ((known lib replies)
              (t4-constructors-query
               :prove (list typed nil (list *t4-constructors-keywordp* *proof-not*)) lib replies))
             (body (t4-constructors-first start 2))
             (evidence (t4-structural-evidence-init lib nil (list known)))
             ((answer lib replies)
              (t4-constructors-query :equation (list body evidence) lib replies)))
          (if (not (car answer))
              (list nil lib replies)
            (t4-constructors-with-library
                ((result (library-inherited proof-proof-chain lib start (list (car answer))))
                 (right (t4-constructors-first result 2))
                 (wanted (t4-constructors-at target 2))
                 (step (if (equal right wanted) result (t4-syntax-lists-choose lib result known))))
              (list step lib replies)))))))))

(defun t4-constructors-tree-constructor-open (lib original test target guard replies)
  (t4-constructors-with-library
      ((start (library-inherited proof-proof-reflexive lib test))
       (equation (library-inherited proof-proof-unfold lib original))
       (start (library-inherited proof-proof-rewrite lib start equation '(1 2 1)))
       (constructor (t4-constructors-first start 2 1)))
    (if (or (proof-is-call original *t4-constructors-make-tag*)
            (proof-is-call original *t4-constructors-make-direct*))
        (t4-constructors-with-library
            ((body (t4-constructors-first start 2))
             (evidence (t4-structural-evidence-init lib nil nil))
             ((answer lib replies) (t4-constructors-query :equation (list body evidence) lib replies)))
          (if (not (car answer))
              (list nil lib replies)
            (t4-constructors-with-library
                ((start (library-inherited proof-proof-chain lib start (list (car answer)))))
              (if (proof-is-call original *t4-constructors-make-direct*)
                  (t4-constructors-tree-constructor-direct lib start original guard replies)
                (t4-constructors-tree-constructor-tag lib start constructor target replies)))))
      (t4-constructors-tree-constructor-wrapper lib start constructor target replies))))

(defun t4-constructors-tree-constructor-attempt (lib formula replies)
  (t4-constructors-with-library ((parts (t4-constructors-implied formula)))
    (let ((guard (car parts))
          (target (cadr parts)))
      (if (not (proof-is-call target *proof-equal*))
          (cons nil lib)
        (t4-constructors-with-library ((test (t4-constructors-at target 1)))
          (if (not (proof-is-call test *t4-constructors-tree*))
              (cons nil lib)
            (t4-constructors-with-library
                ((original (t4-constructors-at test 1))
                 (head (and (proof-compound original) (t4-constructors-at original 0))))
              (if (or (not (proof-compound original))
                      (not (or (t4-constructors-defined-p lib head) (equal head *proof-cons*))))
                  (cons nil lib)
                (t4-constructors-with-library
                    (((ignored lib replies) (t4-constructors-query :use-arithmetic nil lib replies))
                     ((step lib replies)
                      (cond
                       ((and (proof-is-call original *proof-cons*) (eq guard :none))
                        (t4-constructors-with-library ((wanted (t4-constructors-at target 2)))
                          (t4-constructors-tree-cons lib test wanted replies)))
                       ((proof-is-call original *proof-quote*) (list nil lib replies))
                       (t (t4-constructors-tree-constructor-open lib original test target guard replies)))))
                  (cons step lib))))))))))

(defun t4-constructors-boolean-equality-reduce (lib equation replies)
  (t4-constructors-with-library
      ((value (t4-constructors-first equation 2))
       ((reduced lib replies)
        (t4-constructors-query
         :prove (list (list *t4-constructors-booleanp* value)
                      nil (list *t4-constructors-booleanp* *t4-constructors-eq* *proof-not*))
         lib replies))
       (reverse (library-inherited proof-proof-symmetric lib equation))
       (step (library-inherited proof-proof-rewrite lib reduced reverse '(1 1))))
    (list step lib replies)))

(defun t4-constructors-boolean-equality (lib test replies)
  (t4-constructors-with-library
      ((expected (list *t4-constructors-booleanp* test))
       (assumption (library-inherited proof-proof-assume lib test t))
       (left (t4-constructors-at test 1))
       (right (t4-constructors-at test 2)))
    (if (equal left right)
        (t4-constructors-query
         :prove (list expected nil (list *t4-constructors-booleanp* *t4-constructors-eq* *proof-not*))
         lib replies)
      (t4-constructors-with-library
          ((same (library-inherited proof-proof-fact lib "equal-same" (list (list *library-x* left))))
           (yes (library-inherited proof-proof-rewrite lib same assumption '(1 1 2)))
           (denied (library-inherited proof-proof-assume lib test nil))
           (nil-or-true (library-inherited proof-proof-nil-or-true lib test))
           (front (library-inherited proof-proof-front lib nil-or-true test))
           (no (library-inherited proof-proof-cut lib front denied))
           ((yes lib replies) (t4-constructors-boolean-equality-reduce lib yes replies))
           ((no lib replies) (t4-constructors-boolean-equality-reduce lib no replies))
           (step (library-inherited proof-proof-cases lib test yes no)))
        (list step lib replies)))))

(defun t4-constructors-proper-list-boolean (lib value replies)
  (let ((name "PROPER-LIST-RESULT-BOOLEAN"))
    (t4-constructors-with-library
        (((ignored lib replies)
          (if (t4-constructors-has-lemma-p lib name)
              (list nil lib replies)
            (t4-constructors-with-library
                ((predicate (list *t4-results-true-list* *library-x*))
                 (claim (list *t4-constructors-booleanp* predicate))
                 (shape (list *proof-consp* *library-x*))
                 (cons-step (library-inherited proof-proof-assume lib shape t))
                 (atom-step (library-inherited proof-proof-assume lib shape nil))
                 (recursion (t4-syntax-lists-recur lib claim *library-x* *library-cdr* 3))
                 ((yes-value lib) (t4-syntax-lists-spine lib predicate cons-step))
                 ((no-value lib) (t4-syntax-lists-spine lib predicate atom-step))
                 (yes-back (library-inherited proof-proof-symmetric lib yes-value))
                 (yes (library-inherited proof-proof-rewrite lib (car recursion) yes-back '(1 1)))
                 (atom-test (t4-constructors-first no-value 2))
                 (equation (if (proof-is-call atom-test *t4-constructors-eq*)
                               (library-inherited proof-proof-unfold lib atom-test)
                             (library-inherited proof-proof-reflexive lib atom-test)))
                 (right (t4-constructors-first equation 2))
                 ((no lib replies) (t4-constructors-boolean-equality lib right replies))
                 (back (library-inherited proof-proof-symmetric lib equation))
                 (no (library-inherited proof-proof-rewrite lib no back '(1 1)))
                 (no-back (library-inherited proof-proof-symmetric lib no-value))
                 (no (library-inherited proof-proof-rewrite lib no no-back '(1 1)))
                 (cases (library-inherited proof-proof-cases lib shape yes no))
                 (ordinal (library-library-builtin lib 1 *library-x*))
                 (proof (library-inherited proof-proof-induct
                                           lib ordinal cases claim (t4-structural-count *library-x*)
                                           (list (cadr recursion))))
                 (lib (library-library-lemma lib name claim proof nil)))
              (list nil lib replies))))
         (step (library-library-cite lib name (list value) nil)))
      (list step lib replies))))

(defun t4-constructors-reordered-recognizer-branch (a b lib first second shown target head tail replies)
  (t4-constructors-with-library
      ((p (library-inherited proof-proof-assume lib first a))
       (q (library-inherited proof-proof-assume lib second b))
       (left (t4-syntax-lists-choose lib shown q))
       (right (library-inherited proof-proof-select lib target p))
       ((pair lib replies)
        (cond
         ((and a b)
          (t4-constructors-with-library
              ((boolean (library-inherited proof-proof-fact lib "booleanp-symbolp"
                                           (list (list *library-x* head))))
               ((truth lib) (t4-ordinals-ordinals-true-boolean lib boolean p))
               (left (library-inherited proof-proof-chain lib left (list truth)))
               ((proper lib replies) (t4-constructors-proper-list-boolean lib tail replies))
               ((truth lib) (t4-ordinals-ordinals-true-boolean lib proper q))
               (right (library-inherited proof-proof-chain lib right (list truth))))
            (list (cons left right) lib replies)))
         ((or a b)
          (let ((denied (if a q p))
                (value (if a second first)))
            (t4-constructors-with-library
                ((nil-or-true (library-inherited proof-proof-nil-or-true lib value))
                 (front (library-inherited proof-proof-front lib nil-or-true value))
                 (erased (library-inherited proof-proof-cut lib front denied))
                 (left (if a left (library-inherited proof-proof-chain lib left (list erased))))
                 (right (if a (library-inherited proof-proof-chain lib right (list erased)) right)))
              (list (cons left right) lib replies))))
         (t (list (cons left right) lib replies))))
       (reverse (library-inherited proof-proof-symmetric lib (cdr pair)))
       (step (library-inherited proof-proof-chain lib (car pair) (list reverse))))
    (list step lib replies)))

(defun t4-constructors-reordered-recognizer-match-p (lib call pair target)
  (and (t4-constructors-defined-p lib (car call))
       (proof-is-call pair *proof-cons*)
       (proof-is-call target *proof-if*)
       (t4-constructors-with ((no (t4-constructors-at target 3)))
         (and (equal no *proof-false*)
              (proof-is-call (cadr target) *t4-constructors-symbolp*)
              (proof-is-call (caddr target) *t4-results-true-list*)))))

(defun t4-constructors-reordered-recognizer-proof (lib call pair target replies)
  (t4-constructors-with-library
      (((ignored lib replies) (t4-constructors-query :use-arithmetic nil lib replies))
       (parts (proof-list-of-length (cdr pair) 2))
       (head (car parts))
       (tail (cadr parts))
       ((shown lib) (t4-syntax-lists-constructed-view lib call pair))
       (unless-step (t4-results-true-list-cons lib pair))
       (body (t4-constructors-first shown 2))
       (slot (t4-constructors-first unless-step 1))
       (shown (library-inherited proof-proof-rewrite-result lib shown unless-step
                                (proof-eq *proof-result* body) slot))
       (first (list *t4-constructors-symbolp* head))
       (second (list *t4-results-true-list* tail))
       (body (t4-constructors-first shown 2)))
    (if (not (and (equal body (proof-ite second first *proof-false*))
                  (equal target (proof-ite first second *proof-false*))))
        (cons nil lib)
      (t4-constructors-with-library
          (((yes-yes lib replies)
            (t4-constructors-reordered-recognizer-branch t t lib first second shown target head tail replies))
           ((yes-no lib replies)
            (t4-constructors-reordered-recognizer-branch t nil lib first second shown target head tail replies))
           (yes (library-inherited proof-proof-cases lib second yes-yes yes-no))
           ((no-yes lib replies)
            (t4-constructors-reordered-recognizer-branch nil t lib first second shown target head tail replies))
           ((no-no lib replies)
            (t4-constructors-reordered-recognizer-branch nil nil lib first second shown target head tail replies))
           (no (library-inherited proof-proof-cases lib second no-yes no-no))
           (step (library-inherited proof-proof-cases lib first yes no)))
        (cons step lib)))))

(defun t4-constructors-reordered-recognizer-attempt (lib formula replies)
  (if (not (proof-is-call formula *proof-equal*))
      (cons nil lib)
    (t4-constructors-with-library ((test (t4-constructors-at formula 1)))
      (if (not (and (proof-compound test) (equal (len test) 2)))
          (cons nil lib)
        (t4-constructors-with-library
            ((parts (proof-list-of-length (cdr formula) 2))
             (call (car parts))
             (target (cadr parts))
             (pair (cadr call))
             (matches (t4-constructors-reordered-recognizer-match-p lib call pair target)))
          (if matches
              (t4-constructors-reordered-recognizer-proof lib call pair target replies)
            (cons nil lib)))))))

(defun t4-constructors-optional-definition (lib term)
  (if (not (and (proof-compound term)
                (equal (len term) 2)
                (t4-constructors-defined-p lib (car term))))
      nil
    (t4-constructors-with
        ((view (t4-syntax-lists-open-body lib term))
         (body (t4-constructors-first view 2)))
      (if (not (proof-is-call body *proof-if*))
          nil
        (t4-constructors-with ((test (t4-constructors-at body 1))
                               (yes (t4-constructors-at body 2))
                               (no (and (equal test yes) (t4-constructors-at body 3))))
          (and (equal test yes)
               (equal no (list *t4-constructors-null* (cadr term)))
               view))))))

(defun t4-constructors-optional-recognizer-implication (lib formula)
  (t4-constructors-with-library
      ((parts (proof-list-of-length (cdr formula) 2))
       (premise (car parts))
       (optional (t4-constructors-optional-definition lib (cadr parts)))
       (test (and optional (t4-constructors-first optional 2 1))))
    (if (not (and optional (equal test premise)))
        (cons nil lib)
      (t4-constructors-with-library
          ((assumed (library-inherited proof-proof-assume lib premise t))
           (selected (t4-syntax-lists-choose lib optional assumed))
           (proof (library-inherited proof-proof-transport lib assumed selected))
           (step (t4-ordinals-ordinals-imply lib premise proof)))
        (cons step lib)))))

(defun t4-constructors-optional-recognizer-boolean (lib formula replies)
  (t4-constructors-with-library
      ((term (t4-constructors-at formula 1))
       (view (t4-constructors-optional-definition lib term)))
    (if (not view)
        (cons nil lib)
      (t4-constructors-with-library
          ((constructor (t4-constructors-first view 2))
           ((ignored lib replies) (t4-constructors-query :use-arithmetic nil lib replies))
           (yes-term (t4-constructors-at constructor 2))
           (evidence (t4-structural-evidence-init lib nil nil))
           ((answer lib replies)
            (t4-constructors-query
             :fact-proof (list (list *t4-constructors-booleanp* yes-term) evidence) lib replies)))
        (if (not (car answer))
            (cons nil lib)
          (t4-constructors-with-library
              ((no-term (t4-constructors-at constructor 3))
               (other (library-inherited proof-proof-unfold lib no-term))
               (other-value (t4-constructors-first other 2))
               (equation (if (proof-is-call other-value *t4-constructors-eq*)
                             (library-inherited proof-proof-unfold lib other-value)
                           (library-inherited proof-proof-reflexive lib other-value)))
               (equal-value (t4-constructors-first equation 2))
               ((last-step lib replies) (t4-constructors-boolean-equality lib equal-value replies))
               (chain (library-inherited proof-proof-chain lib other (list equation)))
               (reverse (library-inherited proof-proof-symmetric lib chain))
               (last-step (library-inherited proof-proof-rewrite lib last-step reverse '(1 1)))
               (yes-opening (library-inherited proof-proof-if-true lib constructor))
               (yes-back (library-inherited proof-proof-symmetric lib yes-opening))
               (yes (library-inherited proof-proof-rewrite lib (car answer) yes-back '(1 1)))
               (no-opening (library-inherited proof-proof-if-false lib constructor))
               (no-back (library-inherited proof-proof-symmetric lib no-opening))
               (no (library-inherited proof-proof-rewrite lib last-step no-back '(1 1)))
               (test (t4-constructors-at constructor 1))
               (cases (library-inherited proof-proof-cases lib test yes no))
               (view-back (library-inherited proof-proof-symmetric lib view))
               (step (library-inherited proof-proof-rewrite lib cases view-back '(1 1))))
            (cons step lib)))))))

(defun t4-constructors-optional-recognizer-typing-replies
    (n lib predicate term evidence used replies)
  (declare (xargs :measure (nfix n)))
  (if (not (acl2::o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "t4-constructors-optional-recognizer-typing-replies")
    (let ((result (t4-list-types-query-with-library
                   :constructor-type lib (list predicate term evidence) (reverse used))))
      (cond ((failure-p result) result)
            ((not (t4-constructors-request-p result))
             (if (failure-p (car result))
                 (t4-constructors-keep-error (car result) (cadr result))
               (list (car result) (cadr result) replies)))
            ((endp replies) result)
            (t
             (t4-constructors-optional-recognizer-typing-replies
              (1- n) lib predicate term evidence (cons (car replies) used) (cdr replies)))))))

(defun t4-constructors-optional-recognizer-check-typing (operator term lib evidence replies)
  (t4-constructors-optional-recognizer-typing-replies 1000000 lib operator term evidence nil replies))

(mutual-recursion
 (defun t4-constructors-optional-recognizer-check
     (n value tests opened lib predicate mandatory replies)
   (declare (xargs :measure (nfix n)))
   (if (not (acl2::o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t4-constructors-optional-recognizer-check")
     (let ((target (list predicate value)))
       (t4-constructors-with-library ((match (t4-constructors-optional-definition lib target)))
         (cond
          ((equal value *proof-false*)
           (t4-constructors-query
            :prove (list target nil (list predicate mandatory *t4-constructors-null*
                                          *t4-constructors-eq* *proof-not*))
            lib replies))
          ((proof-is-call value *proof-cons*)
           (t4-constructors-with-library
               ((evidence (t4-structural-evidence-init lib tests nil))
                ((valid lib replies)
                 (t4-constructors-optional-recognizer-check-typing mandatory value lib evidence replies))
                (selected (if match (t4-syntax-lists-choose lib match valid)
                            '(:failure "failure" "")))
                (step (library-inherited proof-proof-transport lib valid selected)))
             (list step lib replies)))
          (t
           (t4-constructors-with-library ((head (and (proof-compound value) (t4-constructors-at value 0))))
             (if (not (and (proof-compound value)
                           (t4-constructors-defined-p lib head)
                           (not (member-equal head opened))))
                 '(:failure "search-miss" "")
               (let ((template (list predicate *proof-result*)))
                 (t4-constructors-with-library
                     ((equation (library-inherited proof-proof-unfold lib value))
                      (body (t4-constructors-first equation 2))
                      ((checked lib replies)
                       (t4-constructors-optional-recognizer-by-value
                        (1- n) body tests (append opened (list head)) lib predicate mandatory replies))
                      (step (t4-constructors-scalar-result-lift lib checked equation template)))
                   (list step lib replies)))))))))))
 (defun t4-constructors-optional-recognizer-by-value
     (n value tests opened lib predicate mandatory replies)
   (declare (xargs :measure (nfix n)))
   (if (not (acl2::o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t4-constructors-optional-recognizer-by-value")
     (let ((template (list predicate *proof-result*)))
       (if (proof-is-call value *proof-if*)
           (t4-constructors-with-library
               ((parts (proof-list-of-length (cdr value) 3))
                (test (car parts))
                ((yes lib replies)
                 (t4-constructors-optional-recognizer-by-value
                  (1- n) (cadr parts) (append tests (list (list test t))) opened lib predicate mandatory replies))
                ((no lib replies)
                 (t4-constructors-optional-recognizer-by-value
                  (1- n) (caddr parts) (append tests (list (list test nil))) opened lib predicate mandatory replies))
                (step (t4-constructors-scalar-result-case lib value template yes no)))
             (list step lib replies))
         (t4-constructors-with-library ((head (and (proof-compound value) (t4-constructors-at value 0))))
           (if (and (proof-compound value) (proof-compound head))
               (t4-constructors-with-library
                   ((opening (library-inherited proof-proof-beta lib value))
                    (body (t4-constructors-first opening 2))
                    ((inner lib replies)
                     (t4-constructors-optional-recognizer-by-value
                      (1- n) body tests opened lib predicate mandatory replies))
                    (step (t4-constructors-scalar-result-lift lib inner opening template)))
                 (list step lib replies))
             (t4-constructors-with-library
                 (((step lib replies)
                   (t4-constructors-optional-recognizer-check
                    (1- n) value tests opened lib predicate mandatory replies))
                  (literal (proof-step-first step))
                  (expected (proof-subst template (list (cons *proof-result* value)))))
               (if (equal literal expected)
                   (list step lib replies)
                 '(:failure "inference-mismatch" ""))))))))))

(defun t4-constructors-optional-recognizer-result (lib formula recursive replies)
  (if (not (and (proof-compound formula) (equal (len formula) 2) (proof-compound (cadr formula))))
      (cons nil lib)
    (t4-constructors-with-library
        ((predicate (car formula))
         (root (cadr formula))
         (head (t4-constructors-at root 0)))
      (if (or (not (t4-constructors-defined-p lib head)) (member-equal head recursive))
          (cons nil lib)
        (t4-constructors-with-library ((view (t4-constructors-optional-definition lib formula)))
          (if (not view)
              (cons nil lib)
            (t4-constructors-with-library
                ((mandatory (t4-constructors-first view 2 1 0))
                 ((ignored lib replies) (t4-constructors-query :use-arithmetic nil lib replies))
                 (template (list predicate *proof-result*))
                 (equation (library-inherited proof-proof-unfold lib root))
                 (body (t4-constructors-first equation 2))
                 ((typed lib replies)
                  (t4-constructors-optional-recognizer-by-value
                   1000000 body nil nil lib predicate mandatory replies))
                 (step (t4-constructors-scalar-result-lift lib typed equation template)))
              (cons step lib))))))))

(defun t4-constructors-optional-recognizer-attempt (lib formula recursive replies)
  (cond ((proof-is-call formula *library-implies*)
         (t4-constructors-optional-recognizer-implication lib formula))
        ((proof-is-call formula *t4-constructors-booleanp*)
         (t4-constructors-optional-recognizer-boolean lib formula replies))
        (t (t4-constructors-optional-recognizer-result lib formula recursive replies))))

(defun t4-constructors-scalar-result-with-library (lib formula replies)
  (t4-constructors-finish (t4-constructors-scalar-result-attempt lib formula replies) lib t))

(defun t4-constructors-tree-constructor-with-library (lib formula replies)
  (t4-constructors-finish (t4-constructors-tree-constructor-attempt lib formula replies) lib t))

(defun t4-constructors-reordered-recognizer-with-library (lib formula replies)
  (t4-constructors-finish (t4-constructors-reordered-recognizer-attempt lib formula replies) lib t))

(defun t4-constructors-optional-recognizer-with-library (lib formula recursive replies)
  (t4-constructors-finish
   (t4-constructors-optional-recognizer-attempt lib formula recursive replies) lib t))
