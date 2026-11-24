(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *constraint-proofs-iff* (proof-sym "IFF" "ACL2"))

(defmacro constraint-proofs-let* (bindings body)
  (if (endp bindings)
      body
    (let ((binding (car bindings)))
      `(let (,binding)
         (if (failure-p ,(car binding))
             ,(car binding)
           (constraint-proofs-let* ,(cdr bindings) ,body))))))

(mutual-recursion
 (defun constraint-proofs-set-key (value)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count value)))))
   (cond ((null value) "nil")
         ((eq value t) "t")
         ((integerp value) (decimal-text value))
         ((rationalp value)
          (concatenate 'string (decimal-text (numerator value)) "/" (decimal-text (denominator value))))
         ((stringp value)
          (let* ((escaped (text-replace value "\\" "\\\\"))
                 (escaped (text-replace escaped "\"" "\\\"")))
            (concatenate 'string "\"" escaped "\"")))
         ((consp value)
          (concatenate 'string "(" (text-join " " (constraint-proofs-set-keys value)) ")"))
         (t "")))
 (defun constraint-proofs-set-keys (items)
   (declare (xargs :measure (* 2 (acl2-count items))))
   (if (endp items)
       nil
     (cons (constraint-proofs-set-key (car items)) (constraint-proofs-set-keys (cdr items))))))

(defun constraint-proofs-variable-order (items)
  (if (endp items)
      nil
    (cons (list (constraint-proofs-set-key (car items)) (car items))
          (constraint-proofs-variable-order (cdr items)))))

(defun constraint-proofs-variable-terms (ordered)
  (if (endp ordered)
      nil
    (cons (cadar ordered) (constraint-proofs-variable-terms (cdr ordered)))))

(mutual-recursion
 (defun constraint-proofs-variable-list (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) (list term))
         ((or (atom term) (proof-is-call term *proof-quote*)) nil)
         (t (constraint-proofs-argument-variables (cdr term)))))
 (defun constraint-proofs-argument-variables (args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (append (constraint-proofs-variable-list (car args))
             (constraint-proofs-argument-variables (cdr args))))))

(defun constraint-proofs-variables (term)
  (constraint-proofs-variable-terms
   (seq-sorted (constraint-proofs-variable-order (proof-unique (constraint-proofs-variable-list term))))))

(defun constraint-proofs-atomic-formals-p (formals)
  (if (endp formals)
      t
    (and (not (proof-compound (car formals)))
         (constraint-proofs-atomic-formals-p (cdr formals)))))

(defun constraint-proofs-equational-option (function arity call body forbidden)
  (let ((formals (cdr call)))
    (if (and (proof-is-call call function)
             (equal (len call) (+ 1 arity))
             (equal (len (proof-unique formals)) arity)
             (constraint-proofs-atomic-formals-p formals)
             (subsetp-equal (constraint-proofs-variables body) formals))
        (constraint-proofs-let* ((replaced (terms-replace-calls body forbidden)))
          (if (equal replaced body) (list (list formals body)) nil))
      nil)))

(defun constraint-proofs-equational-options (function arity formulas forbidden)
  (if (endp formulas)
      nil
    (constraint-proofs-let* ((head (proof-search-head (car formulas))))
      (if (not (member-equal head (list *proof-equal* *constraint-proofs-iff*)))
          (constraint-proofs-equational-options function arity (cdr formulas) forbidden)
        (constraint-proofs-let*
         ((operands (evaluator-proofs-fields-of-size (cdar formulas) 2))
          (left (car operands))
          (right (cadr operands))
          (forward (constraint-proofs-equational-option function arity left right forbidden))
          (backward (constraint-proofs-equational-option function arity right left forbidden))
          (rest (constraint-proofs-equational-options function arity (cdr formulas) forbidden)))
         (append forward backward rest))))))

(defun constraint-proofs-fixer-requirement (formula predicate call value)
  (cond ((not (proof-is-call formula *library-implies*)) nil)
        ((not (consp (cddr formula))) '(:failure "failure" ""))
        ((not (equal (caddr formula) (list (car predicate) call))) nil)
        (t (let ((requirement (cadr formula)))
             (cond ((not (proof-is-call requirement (car predicate))) nil)
                   ((not (consp (cdr requirement))) '(:failure "failure" ""))
                   ((constraint-proofs-variables (cadr requirement)) nil)
                   (t (list (list value) (proof-ite predicate value (cadr requirement)))))))))

(defun constraint-proofs-fixer-type-options (formulas predicate call value)
  (if (endp formulas)
      nil
    (constraint-proofs-let*
     ((option (constraint-proofs-fixer-requirement (car formulas) predicate call value))
      (rest (constraint-proofs-fixer-type-options (cdr formulas) predicate call value)))
     (if option (cons option rest) rest))))

(defun constraint-proofs-fixer-orientation (function formulas predicate call value)
  (if (and (equal call (list function value))
           (not (proof-compound value))
           (proof-compound predicate)
           (equal (len predicate) 2)
           (equal (cadr predicate) value))
      (constraint-proofs-fixer-type-options formulas predicate call value)
    nil))

(defun constraint-proofs-fixer-scan (function all remaining)
  (if (endp remaining)
      nil
    (let ((formula (car remaining)))
      (cond ((not (proof-is-call formula *library-implies*))
             (constraint-proofs-fixer-scan function all (cdr remaining)))
            ((not (consp (cddr formula))) '(:failure "failure" ""))
            ((not (proof-is-call (caddr formula) *proof-equal*))
             (constraint-proofs-fixer-scan function all (cdr remaining)))
            (t (constraint-proofs-let*
                ((parts (evaluator-proofs-fields-of-size (cdr formula) 2))
                 (predicate (car parts))
                 (sides (evaluator-proofs-fields-of-size (cdadr parts) 2))
                 (left (car sides))
                 (right (cadr sides))
                 (yes (constraint-proofs-fixer-orientation function all predicate left right))
                 (no (constraint-proofs-fixer-orientation function all predicate right left))
                 (rest (constraint-proofs-fixer-scan function all (cdr remaining))))
                (append yes no rest)))))))

(defun constraint-proofs-fixer-options (function formulas)
  (constraint-proofs-fixer-scan function formulas formulas))

(defun constraint-proofs-example (rule facts formals)
  (if (proof-search-rule-expose rule)
      nil
    (let* ((name (proof-search-rule-name rule))
           (fact (assoc-equal name facts))
           (pattern (proof-search-rule-pattern rule)))
      (cond ((not fact) '(:failure "failure" ""))
            ((not (and (equal (len (cdr fact)) 1) (equal (len pattern) 2))) nil)
            (t (let ((example (cadr pattern)))
                 (if (or (proof-is-call example *proof-quote*)
                         (and (proof-compound example) (equal (len example) 1)))
                     (list formals example)
                   nil)))))))

(defun constraint-proofs-example-rules (rules facts formals)
  (if (endp rules)
      nil
    (constraint-proofs-let*
     ((option (constraint-proofs-example (car rules) facts formals))
      (rest (constraint-proofs-example-rules (cdr rules) facts formals)))
     (if option (cons option rest) rest))))

(defun constraint-proofs-example-scan (function formulas rules facts formals)
  (if (endp formulas)
      nil
    (constraint-proofs-let*
     ((target (proof-search-conclusion (car formulas)))
      (head (proof-search-head target))
      (examples (and head (equal (len target) 2) (proof-is-call (cadr target) function)
                     (constraint-proofs-example-rules
                      (cdr (assoc-equal (list (car target) nil) rules)) facts formals)))
      (rest (constraint-proofs-example-scan function (cdr formulas) rules facts formals)))
     (append examples rest))))

(defun constraint-proofs-example-options (lib index function formulas formals)
  (constraint-proofs-example-scan
   function formulas (proof-search-fact-index-rules index)
   (proof-proof-facts (library-library-proof lib)) formals))

(defun constraint-proofs-formals (count position)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      nil
    (cons (proof-sym (concatenate 'string "T1-ARGUMENT-" (decimal-text position)) "ACL2")
          (constraint-proofs-formals (1- count) (1+ position)))))

(defun constraint-proofs-options (lib index function arity formulas forbidden)
  (constraint-proofs-let*
   ((arity (evaluator-proofs-argument-index arity))
    (formals (constraint-proofs-formals arity 1))
    (equations (constraint-proofs-equational-options function arity formulas forbidden))
    (fixers (and (equal arity 1) (constraint-proofs-fixer-options function formulas)))
    (examples (constraint-proofs-example-options lib index function formulas formals)))
   (append equations fixers examples (list (list formals *proof-false*)
                                          (list formals *proof-true*)
                                          (list formals *proof-zero*)))))

(defun constraint-proofs-define-candidate (lib functions names definitions)
  (declare (xargs :measure (acl2-count functions)))
  (cond ((atom functions) (cons nil lib))
        ((atom names) (cons nil lib))
        ((atom definitions) (cons nil lib))
        (t (let* ((function (evaluator-proofs-fields-of-size (car functions) 2))
                  (definition (if (failure-p function)
                                  function
                                (evaluator-proofs-fields-of-size (car definitions) 2))))
             (cond ((failure-p definition) (cons definition lib))
                   ((not (equal (len (car definition)) (cadr function)))
                    (cons '(:failure "failure" "") lib))
                   (t (let ((updated (library-library-definition lib (car names)
                                                                (car definition) (cadr definition))))
                        (if (failure-p updated)
                            (cons updated lib)
                          (constraint-proofs-define-candidate
                           updated (cdr functions) (cdr names) (cdr definitions))))))))))

(defun constraint-proofs-index-with-lib (index previous lib)
  (if (equal (proof-search-fact-index-lib index) previous)
      (proof-search-fact-index-with-lib index lib)
    index))

(defun constraint-proofs-search-goal (lib index goal rewriting)
  (let* ((search (proof-search-search-init lib index 48 rewriting nil))
         (result (proof-search-search-prove search goal nil 2)))
    (if (failure-p result)
        (cons result lib)
      (cons (car result) (proof-search-search-lib (cdr result))))))

(defun constraint-proofs-candidate-goal (lib index goal)
  (let* ((result (constraint-proofs-search-goal lib index goal nil))
         (step (car result))
         (updated (cdr result)))
    (if (terms-unproved-p step)
        (constraint-proofs-search-goal
         updated (constraint-proofs-index-with-lib index lib updated) goal t)
      result)))

(defun constraint-proofs-candidate-proofs (lib index formulas names)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      (cons nil lib)
    (let ((goal (terms-replace-calls (car formulas) names)))
      (if (failure-p goal)
          (cons goal lib)
        (let* ((result (constraint-proofs-candidate-goal lib index goal))
               (step (car result))
               (updated (cdr result)))
          (if (failure-p step)
              result
            (let* ((index (constraint-proofs-index-with-lib index lib updated))
                   (rest (constraint-proofs-candidate-proofs updated index (cdr formulas) names)))
              (if (failure-p (car rest))
                  rest
                (cons (cons (list (list goal) step) (car rest)) (cdr rest))))))))))

(defun constraint-proofs-forget-entries (lib entries)
  (declare (xargs :measure (acl2-count entries)))
  (if (endp entries)
      (cons nil lib)
    (let* ((entry (car entries))
           (kind (car entry))
           (name (cadr entry))
           (proof (library-library-proof lib))
           (facts (proof-proof-facts proof))
           (definitions (proof-proof-definitions proof)))
      (if (not (assoc-equal name facts))
          (cons '(:failure "failure" "") lib)
        (let* ((facts (table-delete facts name))
               (proof (proof-proof-with-facts proof facts))
               (lib (library-library-with-proof lib proof)))
          (if (not (equal kind "define"))
              (constraint-proofs-forget-entries lib (cdr entries))
            (if (not (assoc-equal name definitions))
                (cons '(:failure "failure" "") lib)
              (let* ((definitions (table-delete definitions name))
                     (updated (proof-make-proof facts definitions (proof-proof-primitives proof)))
                     (updated (proof-proof-with-kind updated (proof-proof-kind proof))))
                (constraint-proofs-forget-entries (library-library-with-proof lib updated)
                                                 (cdr entries))))))))))

(defun constraint-proofs-undo-candidate (lib start)
  (let* ((entries (library-library-entries lib))
         (result (constraint-proofs-forget-entries lib (nthcdr start entries))))
    (if (car result)
        result
      (cons nil (library-library-with-entries (cdr result) (seq-slice entries 0 start))))))

(defun constraint-proofs-reused-obligations (obligations not-nil)
  (if (or (endp obligations) (not not-nil))
      nil
    (let ((rest (constraint-proofs-reused-obligations (cdr obligations) not-nil)))
      (if (equal (cadar obligations) not-nil)
          (cons (car obligations) rest)
        rest))))

(defun constraint-proofs-finish-obligations (proof obligations not-nil shared)
  (if (endp obligations)
      nil
    (let* ((obligation (car obligations))
           (reused (and not-nil (equal (cadr obligation) not-nil))))
      (constraint-proofs-let*
       ((step (if reused (car shared)
                (proof-proof-subsume proof (cadr obligation) (car obligation))))
        (rest (constraint-proofs-finish-obligations
               proof (cdr obligations) not-nil (if reused (cdr shared) shared))))
       (cons step rest)))))

(defun constraint-proofs-share-obligations (lib obligations forbidden)
  ;; Each constraint is proved by a fresh Search. The library's proof of
  ;; (not 'nil) can be reused as a conclusion across those searches.
  (let* ((proof (library-library-proof lib))
         (not-nil (and (assoc-equal (list (proof-neg *proof-false*)) obligations)
                       (proof-proof-not-nil proof)))
         (not-nil (and (proof-step-p not-nil) not-nil))
         (reused (constraint-proofs-reused-obligations obligations not-nil))
         (shared (lemmas-slice-library-share-proofs lib reused forbidden)))
    (cond ((failure-p shared) (cons shared lib))
          ((failure-p (car shared)) shared)
          (t (let* ((lib (cdr shared))
                    (steps (constraint-proofs-finish-obligations
                            (library-library-proof lib) obligations not-nil (car shared))))
               (cons steps lib))))))

(defun constraint-proofs-candidate-entry (lib index functions formulas names)
  (let ((result (constraint-proofs-candidate-proofs lib index formulas names)))
    (if (failure-p (car result))
        result
      (let* ((lib (cdr result))
             (shared (constraint-proofs-share-obligations lib (car result) (table-keys names))))
        (cond ((failure-p (car shared)) shared)
              ((not (and (consp functions) (consp (car functions))))
               (cons '(:failure "failure" "") (cdr shared)))
              (t (let* ((first (caar functions))
                        (fields (cons first (table-values names)))
                        (entry (proof-proof-entry "witness" first fields (car shared))))
                   (cons entry (cdr shared)))))))))

(defun constraint-proofs-witness-candidate (lib index functions formulas names definitions)
  (let* ((start (len (library-library-entries lib)))
         (defined (constraint-proofs-define-candidate
                   lib functions (table-values names) definitions)))
    (if (car defined)
        defined
      (let* ((updated (cdr defined))
             (index (constraint-proofs-index-with-lib index lib updated))
             (result (constraint-proofs-candidate-entry updated index functions formulas names)))
        (if (terms-unproved-p (car result))
            (constraint-proofs-undo-candidate (cdr result) start)
          result)))))

(defun constraint-proofs-witness-names (functions digest position names)
  (if (endp functions)
      names
    (constraint-proofs-let* ((function (evaluator-proofs-fields-of-size (car functions) 2)))
      (let* ((label (concatenate 'string "T1-BOOK-WITNESS-" digest "-" (decimal-text position)))
             (name (proof-sym label "ACL2")))
        (constraint-proofs-witness-names
         (cdr functions) digest (1+ position) (table-put names (car function) name))))))

(defun constraint-proofs-choices (lib index functions formulas names)
  (if (endp functions)
      nil
    (constraint-proofs-let*
     ((function (evaluator-proofs-fields-of-size (car functions) 2))
      (options (constraint-proofs-options lib index (car function) (cadr function) formulas names))
      (unique (proof-unique options))
      (rest (constraint-proofs-choices lib index (cdr functions) formulas names)))
     (cons unique rest))))

(mutual-recursion
 (defun constraint-proofs-try-choices (choices selected lib index functions formulas names)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count choices)))))
   (if (endp choices)
       (constraint-proofs-witness-candidate lib index functions formulas names (reverse selected))
     (constraint-proofs-try-options (car choices) (cdr choices) selected lib index
                                    functions formulas names)))
 (defun constraint-proofs-try-options (options choices selected lib index functions formulas names)
   (declare (xargs :measure (* 2 (+ (acl2-count options) (acl2-count choices)))))
   (if (endp options)
       (cons nil lib)
     (let* ((result (constraint-proofs-try-choices choices (cons (car options) selected)
                                                  lib index functions formulas names))
            (updated (cdr result)))
       (if (car result)
           result
         (constraint-proofs-try-options (cdr options) choices selected updated
                                        (constraint-proofs-index-with-lib index lib updated)
                                        functions formulas names))))))

(defun constraint-proofs-all-arity (functions arity)
  (if (endp functions)
      t
    (constraint-proofs-let* ((function (evaluator-proofs-fields-of-size (car functions) 2)))
      (and (equal (cadr function) arity) (constraint-proofs-all-arity (cdr functions) arity)))))

(defun constraint-proofs-choice-witness-error (functions formulas)
  (constraint-proofs-let*
   ((arity-zero (and (equal (len functions) 2) (equal (len formulas) 2)
                     (constraint-proofs-all-arity functions 0))))
   (let* ((witness (caar functions))
          (predicate (caadr functions))
          (definition (car formulas))
          (necessity (cadr formulas)))
     (cond
      ((not (and arity-zero (proof-is-call definition *proof-equal*)))
       *terms-unproved*)
      ((not (consp (cdr definition))) '(:failure "failure" ""))
      ((not (and (equal (cadr definition) (list predicate))
                 (proof-is-call necessity *library-implies*)))
       *terms-unproved*)
      ((not (consp (cdr necessity))) '(:failure "failure" ""))
      ((not (equal (cadr necessity) (list predicate)))
       *terms-unproved*)
      ((not (consp (cddr definition))) '(:failure "failure" ""))
      (t (constraint-proofs-let*
          ((body (caddr definition))
           (replaced (terms-replace-calls body (list (cons witness (proof-sym "T1-WITNESS" "ACL2"))))))
          *terms-unproved*))))))

(defun constraint-proofs-run-choices (lib index data functions named-formulas)
  (let ((inputs
         (constraint-proofs-let*
          ((formulas (evaluator-proofs-formulas named-formulas))
           (source (proof-write data))
           (digest (text-upper (seq-slice (siphash-hexdigest source) 0 16)))
           (names (constraint-proofs-witness-names functions digest 1 nil))
           (choices (constraint-proofs-choices lib index functions formulas names)))
          (list formulas names choices))))
    (if (failure-p inputs)
        (cons inputs lib)
      (let* ((formulas (car inputs))
             (names (cadr inputs))
             (choices (caddr inputs))
             (result (constraint-proofs-try-choices choices nil lib index functions formulas names)))
        (if (car result)
            result
          (cons (constraint-proofs-choice-witness-error functions formulas) (cdr result)))))))

(defun constraint-proofs-construct-witnesses (lib index data)
  (let ((data (evaluator-proofs-fields-of-size data 2)))
    (if (failure-p data)
        (cons data lib)
      (let* ((functions (car data))
             (named-formulas (cadr data))
             (evaluator-arities (and (equal (len functions) 2)
                                     (constraint-proofs-all-arity functions 2))))
        (cond ((failure-p evaluator-arities) (cons evaluator-arities lib))
              ((and evaluator-arities (<= 9 (len named-formulas)))
               (evaluator-proofs-evaluator-witnesses lib data))
              ((or (< 2 (len functions)) (< 4 (len named-formulas)))
               (cons *terms-unproved* lib))
              (t (constraint-proofs-run-choices lib index data functions named-formulas)))))))
