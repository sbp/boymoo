(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-recipes-character-list* (proof-sym "CHARACTER-LISTP" "ACL2"))
(defconst *t3-book-recipes-conjoin-equalities* (proof-sym "CONJOIN-EQUALITIES" "ACL2"))
(defconst *t3-book-recipes-identity-cp* (proof-sym "IDENTITY-CP" "FLAG"))
(defconst *t3-book-recipes-lambda* (proof-cl "LAMBDA"))
(defconst *t3-book-recipes-lambdap* (proof-sym "LAMBDAP" "ACL2"))
(defconst *t3-book-recipes-lambda-logic* (proof-sym "LAMBDA-LOGIC-FNSP" "ACL2"))
(defconst *t3-book-recipes-macro-args* (proof-sym "MACRO-REQUIRED-ARGS+-AUX" "ACL2"))
(defconst *t3-book-recipes-macro-alias* (proof-sym "DEREF-MACRO-NAME" "ACL2"))
(defconst *t3-book-recipes-macro-symbol* (proof-sym "MACRO-SYMBOLP" "ACL2"))
(defconst *t3-book-recipes-make-calls* (proof-sym "MAKE-MV-NTH-CALLS" "ACL2"))
(defconst *t3-book-recipes-primitive* (proof-sym "PRIMITIVEP" "ACL2"))
(defconst *t3-book-recipes-pseudo-fn* (proof-sym "PSEUDO-TERMFNP" "ACL2"))
(defconst *t3-book-recipes-real-fn* (proof-sym "TERMFNP" "ACL2"))
(defconst *t3-book-recipes-term* *t3-book-substitution-term*)
(defconst *t3-book-recipes-list* *t3-book-substitution-list*)

(defun t3-book-recipes-subject (term)
  (if (and (proof-compound term) (consp (cdr term)))
      (cadr term)
    :none))

(defun t3-book-recipes-beta-body (term)
  (proof-with-checked-results ((operator (t3-book-theorems-head term)))
    (if (proof-is-call operator *t3-book-recipes-lambda*)
        (proof-with-checked-results
            ((parts (proof-list-of-length operator 3)))
          (let ((formals (cadr parts)))
            (if (integerp formals)
                '(:failure "MalformedLambdaFormals" "")
              (proof-subst (caddr parts)
                           (proof-bindings-table
                            (seq-zip (if (equal formals *proof-nil*) nil formals)
                                    (cdr term))
                            nil)))))
      term)))

(defun t3-book-recipes-false-tail-p (term)
  (if (proof-is-call term *proof-if*)
      (proof-with-checked-results ((tail (proof-term-at term 3)))
        (equal tail *proof-false*))
    nil))

(defun t3-book-recipes-sublis-tactic (call)
  (and (proof-is-call call *t3-book-substitution-mv-nth*)
    (proof-with-checked-results ((index (proof-term-at call 1)))
      (if (equal index *proof-one*)
          (proof-with-checked-results
              ((source (proof-term-at call 2))
               (operator (t3-book-theorems-head source)))
            (and (member-equal operator (list *t3-book-substitution-sublis*
                                               *t3-book-substitution-sublis-list*))
              (list 't3-book-substitution-substitution *t3-book-substitution-sublis*)))
        nil))))

(defun t3-book-recipes-traversal-tactic (guard goal has-lambda)
  (proof-with-checked-results
      ((conditional (t3-book-recipes-false-tail-p goal))
       (goal (if conditional (cadr goal) goal))
       (goal-head (t3-book-theorems-head goal)))
    (if (not (member-equal goal-head (list *t3-book-recipes-term*
                                           *t3-book-recipes-list*)))
        nil
      (proof-with-checked-results
          ((call (proof-term-at goal 1))
           (operator (if has-lambda (t3-book-theorems-head call) nil)))
        (if (and has-lambda
                 (member-equal operator (list *t3-book-remove-progn-remove*
                                               *t3-book-remove-progn-remove-list*)))
            '(t3-book-remove-progn-removal)
          (proof-with-checked-results ((sublis (t3-book-recipes-sublis-tactic call)))
            (if sublis
                sublis
              (proof-with-checked-results ((operator (t3-book-theorems-head call)))
                (cond
                 ((member-equal operator (list *t3-book-substitution-subcor*
                                                *t3-book-substitution-subcor-list*))
                  (list 't3-book-substitution-substitution *t3-book-substitution-subcor*))
                 ((and has-lambda
                       (member-equal operator (list *t3-book-substitution-fast-sublis*
                                                     *t3-book-substitution-fast-sublis-list*)))
                  (list 't3-book-substitution-substitution *t3-book-substitution-fast-sublis*))
                 (t
                  (proof-with-checked-results ((guard-head (t3-book-theorems-head guard)))
                    (cond
                     ((and (equal guard-head *t3-book-recipes-term*)
                           (equal operator *t3-book-term-collections-if-leaves*))
                      '(t3-book-term-collections-leaf-types))
                     ((or (and (equal goal-head *t3-book-recipes-list*)
                               (equal operator *t3-book-term-collections-equalities*))
                          (and (equal goal-head *t3-book-recipes-term*)
                               (equal operator *t3-book-recipes-conjoin-equalities*)))
                      '(t3-book-term-collections-equality-types))
                     ((and has-lambda (equal operator *t3-book-indexed-calls-aux*)
                           (equal goal-head *t3-book-recipes-list*))
                      '(t3-book-indexed-calls-indexed-type))
                     (t nil)))))))))))))

(defun t3-book-recipes-lookup-conditional (guard goal)
  (proof-with-checked-results ((table (t3-book-theorems-head (caddr guard))))
    (let ((test (cadr guard)))
      (proof-with-checked-results
          ((by-cdr (if (and (equal table *t3-book-associations-fixnat-table*)
                            (proof-is-call test *library-car*))
                       (proof-term-at test 1)
                     nil)))
        (cond
         ((or (and (equal table *t3-book-associations-nat-table*)
                   (proof-is-call test *t3-book-associations-by-cdr*))
              (proof-is-call by-cdr *t3-book-associations-by-cdr*))
          (list 't3-book-associations-associate table))
         ((proof-is-call goal *t3-book-associations-symbolp*)
          (proof-with-checked-results ((value (proof-term-at goal 1)))
            (and (proof-is-call value *t3-book-recipes-macro-alias*)
              (list 't3-book-associations-associate *t3-book-associations-symbol-table*))))
         (t nil))))))

(defun t3-book-recipes-lookup-tactic (guard goal)
  (proof-with-checked-results
      ((conditional (t3-book-recipes-false-tail-p guard))
       (recipe (if conditional (t3-book-recipes-lookup-conditional guard goal) nil)))
    (or recipe
        (and (proof-is-call guard *t3-book-recipes-list*)
             (proof-with-checked-results ((values (proof-term-at guard 1)))
               (and (proof-is-call values *t3-book-associations-strip-cdrs*)
                    (proof-is-call goal *t3-book-recipes-term*)
                    (proof-with-checked-results ((call (proof-term-at goal 1)))
                      (and (proof-is-call call *library-cdr*)
                           (proof-with-checked-results ((lookup (proof-term-at call 1)))
                             (and (proof-is-call lookup *t3-book-associations-assoc*)
                               (list 't3-book-associations-associate
                                     *t3-book-recipes-list*)))))))))))

(defun t3-book-recipes-recognizer-tactic (guard goal)
  (proof-with-checked-results
      ((tested (t3-book-theorems-conjuncts guard))
       (input-type (t3-book-theorems-head (car tested)))
       (output-type (t3-book-theorems-head goal)))
    (let ((result (t3-book-recipes-subject goal)))
      (cond
       ((and (proof-is-call result *library-car*)
             (equal input-type *t3-book-recipes-term*)
             (equal output-type *t3-book-lambdas-pseudo-lambda*)
             (equal (len tested) 3))
        '(t3-book-lambdas-extract-lambda))
       ((and (proof-is-call result *library-car*)
             (equal input-type *t3-book-lambdas-real-term*)
             (equal output-type *t3-book-recipes-lambdap*))
        '(t3-book-lambdas-extract-real-lambda))
       ((and (proof-is-call result *library-car*)
             (equal input-type *t3-book-lambdas-real-term*)
             (equal output-type *t3-book-recipes-real-fn*))
        '(t3-book-function-terms-fn-from-term))
       ((and (proof-is-call result *library-car*)
             (equal input-type *t3-book-recipes-term*)
             (equal output-type *t3-book-recipes-pseudo-fn*))
        '(t3-book-function-terms-pseudo-fn-from-term))
       ((and (proof-is-call result *proof-cons*)
             (equal input-type *t3-book-lambdas-pseudo-lambda*)
             (equal output-type *t3-book-recipes-term*))
        '(t3-book-lambdas-construct-lambda))
       ((and (proof-is-call result *proof-cons*)
             (equal input-type *t3-book-recipes-lambdap*)
             (equal output-type *t3-book-lambdas-real-term*))
        '(t3-book-lambdas-construct-real-lambda))
       ((and (proof-is-call result *proof-cons*)
             (or (and (equal input-type *t3-book-recipes-pseudo-fn*)
                      (equal output-type *t3-book-recipes-term*))
                 (and (equal input-type *t3-book-recipes-real-fn*)
                      (equal output-type *t3-book-lambdas-real-term*))))
        '(t3-book-function-terms-from-function))
       ((and (equal input-type *t3-book-lambdas-pseudo-lambda*)
             (equal output-type *t3-book-recipes-pseudo-fn*))
        '(t3-book-function-terms-fn-from-lambda))
       ((equal output-type *t3-book-world-symbolp*)
        (cond ((equal input-type *t3-book-recipes-macro-symbol*)
               '(t3-book-world-macro-symbol))
              ((and (proof-is-call guard *t3-book-recipes-primitive*)
                    (equal (t3-book-recipes-subject guard) result))
               '(t3-book-symbol-tables-primitive-symbol))
              (t nil)))
       (t nil)))))

(defun t3-book-recipes-processor-p (call)
  (proof-with-checked-results ((operator (t3-book-theorems-head call)))
    (if (member-equal operator (list *t3-book-clause-processors-process*
                                     *t3-book-recipes-identity-cp*))
        t
      nil)))

(defun t3-book-recipes-processor-premise (guard)
  (declare (xargs :measure (acl2-count guard)))
  (proof-with-checked-results ((conditional (t3-book-recipes-false-tail-p guard)))
    (cond
     ((and conditional (consp guard))
      (or (t3-book-recipes-processor-premise (cadr guard))
          (t3-book-recipes-processor-premise (caddr guard))))
     ((proof-is-call guard *t3-book-clause-processors-ev*)
      (proof-with-checked-results ((arg (proof-term-at guard 1)))
        (and (proof-is-call arg *t3-book-clause-processors-conjoin-clauses*)
          (proof-with-checked-results
              ((call (proof-term-at arg 1))
               (processor (t3-book-recipes-processor-p call)))
            (and processor '(t3-book-clause-processors-processor-correct))))))
     (t nil))))

(defun t3-book-recipes-processor-tactic (guard goal)
  (cond
   ((proof-is-call goal *t3-book-clause-processors-logic-nested*)
    (proof-with-checked-results
        ((call (proof-term-at goal 1))
         (processor (t3-book-recipes-processor-p call)))
      (and processor '(t3-book-clause-processors-wellformed))))
   ((proof-is-call goal *t3-book-clause-processors-ev*)
    (proof-with-checked-results ((value (proof-term-at goal 1)))
      (and (proof-is-call value *t3-book-clause-processors-disjoin*)
        (t3-book-recipes-processor-premise guard))))
   (t nil)))

(defun t3-book-recipes-count-evens-p (items)
  (if (endp items)
      t
    (and (proof-is-call (car items) *t3-book-merges-occurrences*)
         (proof-with-checked-results ((list-term (proof-term-at (car items) 2)))
           (and (proof-is-call list-term *t3-book-merges-evens*)
                (t3-book-recipes-count-evens-p (cdr items)))))))

(defun t3-book-recipes-count-tactic (guard left right)
  (proof-with-checked-results
      ((operation (if (proof-is-call left *t3-book-merges-occurrences*)
                      (proof-with-checked-results ((list-term (proof-term-at left 2)))
                        (t3-book-theorems-head list-term))
                    nil)))
    (cond
     ((equal operation *t3-book-merges-merge*) '(t3-book-merges-merge-count))
     ((equal operation *t3-book-merges-sort*) '(t3-book-merges-sort-count))
     ((and guard (not (eq guard :none)) (proof-is-call right *t3-book-merges-occurrences*)
           (proof-is-call left *proof-plus*))
      (proof-with-checked-results ((evens (t3-book-recipes-count-evens-p (cdr left))))
        (and evens '(t3-book-merges-split-count))))
     (t nil))))

(defun t3-book-recipes-nested-call-p (term head)
  (proof-with-checked-results ((value (proof-term-at term 1)))
    (proof-is-call value head)))

(defun t3-book-recipes-sorting-equivalence-p (goal)
  (proof-with-checked-results ((tested (t3-book-theorems-conjuncts goal)))
    (and (equal (len tested) 4)
         (proof-is-call (car tested) *t3-book-lambdas-booleanp*)
         (proof-with-checked-results
             ((perm (t3-book-recipes-nested-call-p (car tested) *t3-book-permutations-perm*)))
           (and perm (proof-is-call (cadr tested) *t3-book-permutations-perm*)
                (proof-is-call (caddr tested) *library-implies*)
                (proof-is-call (cadddr tested) *library-implies*))))))

(defun t3-book-recipes-sorting-tactic (guard goal)
  (proof-with-checked-results
      ((ordered (if (and (eq guard :none) (proof-is-call goal *t3-book-sorted-lists-ordered*))
                    (t3-book-recipes-nested-call-p goal *t3-book-merges-sort*)
                  nil)))
    (if ordered
        '(t3-book-sorted-lists-ordered-sort)
      (proof-with-checked-results
          ((conditional (if (eq guard :none) (t3-book-recipes-false-tail-p goal) nil))
           (equivalence (if conditional (t3-book-recipes-sorting-equivalence-p goal) nil)))
        (cond
         (equivalence '(t3-book-permutations-equivalence))
         ((proof-is-call goal *proof-equal*)
          (proof-with-checked-results ((left (proof-term-at goal 1)))
            (and (proof-is-call left *proof-equal*)
              (proof-with-checked-results ((right (proof-term-at goal 2)))
                (and (proof-is-call right *t3-book-permutations-perm*)
                  (proof-with-checked-results ((parts (proof-list-of-length (cdr left) 2)))
                    (and (and guard (not (eq guard :none)))
                      (proof-with-checked-results ((tested (t3-book-theorems-conjuncts guard)))
                        (let ((a (car parts))
                              (b (cadr parts)))
                          (and (equal tested
                                       (list (list *t3-book-sorted-lists-true-listp* a)
                                             (list *t3-book-sorted-lists-true-listp* b)
                                             (list *t3-book-sorted-lists-ordered* a)
                                             (list *t3-book-sorted-lists-ordered* b)))
                            '(t3-book-sorted-lists-ordered-perms)))))))))))
         (t nil))))))

(defun t3-book-recipes-guarded-tactic (guard goal has-lambda)
  (or (t3-book-recipes-traversal-tactic guard goal has-lambda)
      (t3-book-recipes-lookup-tactic guard goal)
      (t3-book-recipes-recognizer-tactic guard goal)
      (t3-book-recipes-processor-tactic guard goal)
      (and (and (proof-is-call guard *t3-book-merges-true-listp*)
                 (proof-is-call goal *t3-book-merges-true-listp*))
        (proof-with-checked-results
            ((sorted (t3-book-recipes-nested-call-p goal *t3-book-merges-sort*)))
          (and sorted '(t3-book-merges-sort-proper))))))

(defun t3-book-recipes-unguarded-tactic (goal has-lambda)
  (cond
   ((and (not has-lambda) (proof-is-call goal *t3-book-recipes-character-list*))
    (proof-with-checked-results
        ((arg (proof-term-at goal 1))
         (operator (t3-book-theorems-head arg)))
      (and (member-equal operator (list *t3-book-character-lists-pack-list*
                                         *t3-book-character-lists-pack-tree*))
        '(t3-book-character-lists-packed-characters))))
   (has-lambda
    (proof-with-checked-results
        ((boolean (if (proof-is-call goal *t3-book-lambdas-booleanp*)
                      (t3-book-recipes-nested-call-p goal *t3-book-recipes-lambda-logic*)
                    nil)))
      (if boolean
          '(t3-book-lambdas-lambda-boolean)
        (and (proof-is-call goal *t3-book-world-symbol-list*)
          (proof-with-checked-results
              ((macro-args (t3-book-recipes-nested-call-p goal *t3-book-recipes-macro-args*)))
            (and macro-args '(t3-book-world-required-symbols)))))))
   (t nil)))

(defun t3-book-recipes-length-tactic (left)
  (proof-with-checked-results ((value (proof-term-at left 1)))
    (cond ((proof-is-call value *t3-book-indexed-calls-aux*)
           '(t3-book-indexed-calls-indexed-length))
          ((proof-is-call value *t3-book-recipes-make-calls*)
           '(t3-book-indexed-calls-full-length))
          (t nil))))

(defun t3-book-recipes-evaluator-tactic (guard left right)
  (proof-with-checked-results
      ((recurs (if (and guard (not (eq guard :none)))
                    (t3-book-recipes-nested-call-p left *t3-book-mv-nth-recurse*)
                  nil)))
    (cond (recurs '(t3-book-mv-nth-recurrence))
          ((proof-is-call right *t3-book-evaluators-eval*)
           (proof-with-checked-results
               ((optimized (t3-book-recipes-nested-call-p right *t3-book-mv-nth-optimize*)))
             (and optimized '(t3-book-mv-nth-correctness))))
          (t nil))))

(defun t3-book-recipes-equality-tactic (formula guard left right has-lambda)
  (or (and (and has-lambda (proof-is-call left *library-len*))
        (t3-book-recipes-length-tactic left))
      (and (proof-is-call left *t3-book-evaluators-eval*)
        (t3-book-recipes-evaluator-tactic guard left right))
      (and (proof-is-call left *t3-book-defpun-result*)
        (proof-with-checked-results ((state-term (proof-term-at left 1)))
          (and (equal formula (t3-book-defpun-recursion-equation state-term))
            '(t3-book-defpun-defpun))))
      (and (proof-is-call left *t3-book-permutations-perm*)
        (cond
         ((equal formula (t3-book-counterexamples-list-statement *library-x* *library-y*))
          '(t3-book-counterexamples-counterexample))
         ((equal formula (t3-book-counterexamples-statement *library-x* *library-y*))
          '(t3-book-counterexamples-convert))
         (t nil)))
      (t3-book-recipes-count-tactic guard left right)))

(defun t3-book-recipes-theorem-tactic (formula)
  (proof-with-checked-results
      ((parts (if (proof-is-call formula *library-implies*)
                  (proof-list-of-length (cdr formula) 2)
                (list :none formula)))
       (goal (t3-book-recipes-beta-body (cadr parts)))
       (operator (t3-book-theorems-head (cadr parts))))
    (let ((guard (car parts))
          (has-lambda (proof-is-call operator *t3-book-recipes-lambda*)))
      (or (if (and guard (not (eq guard :none)))
              (t3-book-recipes-guarded-tactic guard goal has-lambda)
            (t3-book-recipes-unguarded-tactic goal has-lambda))
          (proof-with-checked-results ((sorting (t3-book-recipes-sorting-tactic guard goal)))
            (cond
             ((and sorting (not has-lambda)) sorting)
             ((proof-is-call goal *proof-equal*)
              (proof-with-checked-results ((sides (proof-list-of-length (cdr goal) 2)))
                (t3-book-recipes-equality-tactic
                 formula guard (car sides) (cadr sides) has-lambda)))
             (t nil)))))))

(defun t3-book-recipes-entry (tactic lib name formula)
  (case tactic
    (t3-book-indexed-calls-indexed-type
     (t3-book-indexed-calls-indexed-type lib name formula))
    (t3-book-indexed-calls-indexed-length
     (t3-book-indexed-calls-indexed-length lib name formula))
    (t3-book-indexed-calls-full-length
     (t3-book-indexed-calls-full-length lib name formula))
    (t3-book-lambdas-extract-lambda
     (t3-book-lambdas-extract-lambda lib name formula))
    (t3-book-lambdas-construct-lambda
     (t3-book-lambdas-construct-lambda lib name formula))
    (t3-book-function-terms-fn-from-term
     (t3-book-function-terms-fn-from-term lib name formula))
    (t3-book-function-terms-pseudo-fn-from-term
     (t3-book-function-terms-pseudo-fn-from-term lib name formula))
    (t3-book-function-terms-fn-from-lambda
     (t3-book-function-terms-fn-from-lambda lib name formula))
    (t3-book-world-required-symbols
     (t3-book-world-required-symbols lib name formula))
    (t3-book-mv-nth-correctness
     (t3-book-mv-nth-correctness lib name formula))
    (t3-book-counterexamples-counterexample
     (t3-book-counterexamples-counterexample lib name formula))
    (t3-book-counterexamples-convert
     (t3-book-counterexamples-convert lib name formula))
    (otherwise '(:failure "Unsupported" ""))))

(defun t3-book-recipes-apply-in-book (tactic lib name formula)
  (case (car tactic)
    (t3-book-remove-progn-removal
     (t3-book-remove-progn-removal lib name formula))
    (t3-book-substitution-substitution
     (t3-book-substitution-substitution lib name formula (cadr tactic)))
    (t3-book-term-collections-leaf-types
     (t3-book-term-collections-leaf-types lib name formula))
    (t3-book-term-collections-equality-types
     (t3-book-term-collections-equality-types lib name formula))
    (t3-book-associations-associate
     (t3-book-associations-associate lib name formula (cadr tactic)))
    (t3-book-lambdas-extract-real-lambda
     (t3-book-lambdas-extract-real-lambda lib name formula))
    (t3-book-lambdas-construct-real-lambda
     (t3-book-lambdas-construct-real-lambda lib name formula))
    (t3-book-function-terms-from-function
     (t3-book-function-terms-from-function lib name formula))
    (t3-book-world-macro-symbol
     (t3-book-world-macro-symbol lib name formula))
    (t3-book-symbol-tables-primitive-symbol
     (t3-book-symbol-tables-primitive-symbol lib name formula))
    (t3-book-clause-processors-wellformed
     (t3-book-clause-processors-wellformed lib name formula))
    (t3-book-clause-processors-processor-correct
     (t3-book-clause-processors-processor-correct lib name formula))
    (t3-book-merges-merge-count
     (t3-book-merges-merge-count lib name formula))
    (t3-book-merges-sort-count
     (t3-book-merges-sort-count lib name formula))
    (t3-book-merges-split-count
     (t3-book-merges-split-count lib name formula))
    (t3-book-sorted-lists-ordered-sort
     (t3-book-sorted-lists-ordered-sort lib name formula))
    (t3-book-permutations-equivalence
     (t3-book-permutations-equivalence lib name formula))
    (t3-book-sorted-lists-ordered-perms
     (t3-book-sorted-lists-ordered-perms lib name formula))
    (t3-book-merges-sort-proper
     (t3-book-merges-sort-proper lib name formula))
    (t3-book-character-lists-packed-characters
     (t3-book-character-lists-packed-characters lib name formula))
    (t3-book-lambdas-lambda-boolean
     (t3-book-lambdas-lambda-boolean lib name formula))
    (t3-book-mv-nth-recurrence
     (t3-book-mv-nth-recurrence lib name formula))
    (t3-book-defpun-defpun
     (t3-book-defpun-defpun lib name formula))
    (otherwise
     (proof-with-checked-results ((entry (t3-book-recipes-entry (car tactic) lib name formula)))
       (cons entry lib)))))

(defun t3-book-recipes-apply (tactic lib name formula)
  (let ((kind (proof-proof-kind (library-library-proof lib))))
    (proof-with-checked-results
        ((result (t3-book-recipes-apply-in-book
                  tactic (t3-logic-libraryproofs-for-book lib) name formula)))
      (let* ((library (cdr result))
             (proof (proof-proof-with-kind (library-library-proof library) kind)))
        (cons (car result) (library-library-with-proof library proof))))))
