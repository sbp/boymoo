(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-algebra-fix* (proof-sym "FIX" "ACL2"))
(defconst *t4-algebra-reciprocal* (proof-sym "UNARY-/" "ACL2"))
(defconst *t4-algebra-operations*
  (list (cons *proof-plus* "+") (cons *proof-times* "*")))
(defconst *t4-algebra-unit*
  (list (cons *proof-plus* *proof-zero*) (cons *proof-times* *proof-one*)))

(defun t4-algebra-interrupted-p (value)
  (or (failure-p value)
      (and (consp value) (eq (car value) :call))))

;; A library binding carries the proof result and the Library at that point.
;; Inference bindings carry just their result. Both forms propagate a request
;; or a failure with the resulting Library.
(defmacro t4-algebra-with-library (lib bindings body)
  (if (endp bindings)
      body
    (let* ((binding (car bindings))
           (name (car binding))
           (form (cadr binding))
           (rest `(t4-algebra-with-library ,lib ,(cdr bindings) ,body)))
      (if (eq (caddr binding) :library)
          `(let* ((t4-algebra-outcome ,form)
                  (,name (car t4-algebra-outcome)))
             (if (t4-algebra-interrupted-p ,name)
                 t4-algebra-outcome
               (let ((,lib (cdr t4-algebra-outcome)))
                 ,rest)))
        `(let ((t4-algebra-value ,form))
           (if (t4-algebra-interrupted-p t4-algebra-value)
               (cons t4-algebra-value ,lib)
             (let ((,name t4-algebra-value))
               ,rest)))))))

(defun t4-algebra-public-result (result)
  (if (failure-p (car result)) (car result) result))

(defun t4-algebra-search-miss-p (value)
  (and (failure-p value) (member-equal (cadr value) '("SearchMiss" "value"))))

(defun t4-algebra-query (kind lib args replies)
  (let* ((request (list* :call kind lib args))
         (reply (assoc-equal request replies)))
    (if reply (cdr reply) (cons request lib))))

(defun t4-algebra-fact-present-p (lib name)
  (assoc-equal (proof-sym (concatenate 'string "SELF-" name) "ACL2")
               (proof-proof-facts (library-library-proof lib))))

(defun t4-algebra-cite-result (lib name args)
  (cons (library-library-cite lib name args nil) lib))

(defun t4-algebra-lookup (operator dictionary)
  (let ((entry (assoc-equal operator dictionary)))
    (if entry
        (cdr entry)
      '(:failure "MissingProofInput" ""))))

(defun t4-algebra-binary-operands (args)
  (if (equal (len args) 2)
      args
    '(:failure "failure" "")))

(defun t4-algebra-first (step)
  (if (null step)
      '(:failure "failure" "")
    (proof-step-first step)))

(defun t4-algebra-side (step index)
  (proof-with-checked-results ((literal (t4-algebra-first step)))
    (proof-term-at literal index)))

(defun t4-algebra-find-premise (premises goal)
  (if (endp premises)
      nil
    (proof-with-checked-results ((literal (t4-algebra-first (car premises))))
      (if (equal literal goal)
          (car premises)
        (t4-algebra-find-premise (cdr premises) goal)))))

(defun t4-algebra-ratio-argument-p (args)
  (and (consp args)
       (or (equal (car (cadar args)) "ratio")
           (t4-algebra-ratio-argument-p (cdr args)))))

(defun t4-algebra-constant (lib term replies)
  (let ((head (car term))
        (arg (cadr term))
        (symbolp (proof-cl "SYMBOLP")))
    (if (or (and (member-equal head (list *library-car* *library-cdr* symbolp))
                 (or (endp (cdr term)) (proof-is-call arg *proof-quote*)))
            (and (member-equal head (list *library-car* *library-cdr* *proof-consp*))
                 (or (endp (cdr term)) (proof-is-call arg *proof-cons*)))
            (and (proof-all-quoted-p (cdr term))
                 (or (member-equal head
                                  (list *proof-cons* (proof-cl "CHARACTERP")
                                        (proof-cl "SYMBOL-NAME")
                                        (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2")))
                     (and (member-equal head
                                        (list *proof-plus* *proof-times*
                                              *proof-minus* *proof-less*))
                          (t4-algebra-ratio-argument-p (cdr term))))))
        (t4-algebra-query :constant lib (list term) replies)
      (cons (if (null term)
                '(:failure "failure" "")
              (proof-proof-constant-base (library-library-proof lib) term))
            lib))))

(defun t4-algebra-choose (lib equality condition)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((body (t4-algebra-side equality 2))
         (selection (proof-proof-select proof body condition)))
      (proof-proof-chain proof equality (list selection)))))

(defun t4-algebra-fixed (lib value typed)
  (proof-with-checked-results
      ((opening (proof-proof-unfold (library-library-proof lib)
                                   (list *t4-algebra-fix* value))))
    (t4-algebra-choose lib opening typed)))

(defun t4-algebra-unit-axiom (operator)
  (if (equal operator *proof-plus*) "UNICITY-OF-0" "UNICITY-OF-1"))

(defun t4-algebra-commuted (lib operator a b)
  (proof-with-checked-results
      ((operation (t4-algebra-lookup operator *t4-algebra-operations*)))
    (library-library-axiom lib (concatenate 'string "COMMUTATIVITY-OF-" operation)
                           (list a b))))

(defun t4-algebra-associated (lib operator a b c)
  (proof-with-checked-results
      ((operation (t4-algebra-lookup operator *t4-algebra-operations*)))
    (library-library-axiom lib (concatenate 'string "ASSOCIATIVITY-OF-" operation)
                           (list a b c))))

(defun t4-algebra-number-from-type (lib value premises predicate replies)
  (let ((goal (list predicate value)))
    (t4-algebra-with-library lib
        ((known (t4-algebra-find-premise premises goal))
         (constant (if (and (not known) (proof-is-call value *proof-quote*))
                       (t4-algebra-constant lib goal replies)
                     (cons nil lib))
                   :library)
         (answer (and constant (t4-algebra-side constant 2)))
         (typed (if (and constant (equal answer *proof-true*))
                    (proof-proof-true-from-eq (library-library-proof lib) constant)
                  known)))
      (if (not typed)
          (cons nil lib)
        (let ((proof (library-library-proof lib)))
          (t4-algebra-with-library lib
              ((rational (if (equal predicate *proof-integerp*)
                             (proof-with-checked-results
                                 ((axiom (library-library-axiom
                                          lib "INTEGER-IMPLIES-RATIONAL" (list value))))
                               (proof-proof-modus-ponens proof axiom typed))
                           typed))
               (implication (proof-proof-fact proof "rationalp-acl2-numberp"
                                              (list (list *library-x* value)))))
            (cons (proof-proof-modus-ponens proof implication rational) lib)))))))

(defun t4-algebra-number-typed (lib value premises predicates replies)
  (declare (xargs :measure (acl2-count predicates)))
  (if (endp predicates)
      (t4-algebra-with-library lib
          ((evidence (t4-structural-evidence-init lib nil premises))
           (typed (t4-algebra-query :fact-proof lib
                                   (list (list *library-numberp* value) evidence)
                                   replies)
                  :library))
        (cons (or typed '(:failure "SearchMiss" ""))
              lib))
    (let ((result (t4-algebra-number-from-type lib value premises (car predicates) replies)))
      (if (car result)
          result
        (t4-algebra-number-typed (cdr result) value premises (cdr predicates) replies)))))

(defun t4-algebra-closure (lib operator value)
  (proof-with-checked-results
      ((args (if (assoc-equal operator *t4-algebra-operations*)
                 (proof-list-of-length (cdr value) 2)
               (proof-with-checked-results ((argument (proof-term-at value 1)))
                 (list argument *proof-zero*))))
       (axiom (library-library-axiom lib "CLOSURE" args))
       (pieces (t4-division-pieces lib axiom)))
    (proof-term-at
     pieces
     (cond ((equal operator *proof-plus*) 0)
           ((equal operator *proof-times*) 1)
           ((equal operator *proof-minus*) 2)
           (t 3)))))

(defun t4-algebra-number-visit (n lib value premises replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (cons '(:failure "Fuel" "t4-algebra-number-visit") lib)
    (t4-algebra-with-library lib
        ((given (t4-algebra-find-premise premises (list *library-numberp* value))))
      (cond
       (given (cons given lib))
       ((proof-is-call value *t4-algebra-fix*)
        (let ((name "NUMBER-OF-FIX"))
          (if (t4-algebra-fact-present-p lib name)
              (t4-algebra-cite-result lib name (cdr value))
            (let ((proof (library-library-proof lib))
                  (target (list *library-numberp* (list *t4-algebra-fix* *library-x*))))
              (t4-algebra-with-library lib
                  ((raw (proof-proof-unfold proof (cadr target)))
                   (conditional (t4-algebra-side raw 2))
                   (test (proof-term-at conditional 1))
                   (assumed (proof-proof-assume proof test t))
                   (taken (proof-proof-if-true proof conditional))
                   (path (proof-proof-chain proof raw (list taken)))
                   (yes (library-library-transport-argument lib assumed path 1))
                   (zero (t4-algebra-number-visit (1- n) lib *proof-zero* nil replies)
                         :library)
                   (otherwise (proof-proof-if-false (library-library-proof lib) conditional))
                   (path (proof-proof-chain (library-library-proof lib) raw (list otherwise)))
                   (no (library-library-transport-argument lib zero path 1))
                   (cases (proof-proof-cases (library-library-proof lib) test yes no))
                   (lib (library-library-lemma lib name target cases nil)))
                (t4-algebra-cite-result lib name (cdr value)))))))
       ((and (proof-compound value) (endp value))
        (cons '(:failure "failure" "") lib))
       ((and (proof-compound value)
             (member-equal (car value) (list *proof-plus* *proof-times* *proof-minus*
                                             *t4-algebra-reciprocal*)))
        (cons (t4-algebra-closure lib (car value) value) lib))
       (t (t4-algebra-number-typed lib value premises
                                  (list *proof-integerp* *library-rationalp*) replies))))))

(defun t4-algebra-number-with-replies (lib value premises replies)
  (t4-algebra-number-visit 1000000 lib value premises replies))

(defun t4-algebra-number (lib value premises)
  (t4-algebra-public-result (t4-algebra-number-with-replies lib value premises nil)))

(defun t4-algebra-fixed-value (lib value premises replies)
  (t4-algebra-with-library lib
      ((typed (t4-algebra-number-with-replies lib value premises replies) :library))
    (cons (t4-algebra-fixed lib value typed) lib)))

(defun t4-algebra-unit-with-replies (lib operator value premises replies)
  (t4-algebra-with-library lib
      ((rule (library-library-axiom lib (t4-algebra-unit-axiom operator) (list value))))
    (let* ((fixed (t4-algebra-fixed-value lib value premises replies))
           (lib (cdr fixed))
           (value (car fixed))
           (result (if (t4-algebra-interrupted-p value)
                       value
                     (proof-proof-chain (library-library-proof lib) rule (list value)))))
      (cons (if (t4-algebra-search-miss-p result) rule result) lib))))

(defun t4-algebra-unit (lib operator value premises)
  (t4-algebra-public-result (t4-algebra-unit-with-replies lib operator value premises nil)))

(defun t4-algebra-binary-fix-first (lib operator a b replies)
  (let ((name (if (equal operator *proof-plus*) "SUM-OF-FIX" "PRODUCT-OF-FIX")))
    (if (t4-algebra-fact-present-p lib name)
        (t4-algebra-cite-result lib name (list a b))
      (let ((proof (library-library-proof lib))
            (term (list operator (list *t4-algebra-fix* *library-x*) *library-y*))
            (middle (list operator *library-x* *library-y*)))
        (t4-algebra-with-library lib
            ((rule (library-library-axiom lib (t4-algebra-unit-axiom operator)
                                          (list *library-x*)))
             (from-fix (proof-proof-symmetric proof rule))
             (initial (proof-proof-reflexive proof term))
             (beginning (proof-proof-rewrite proof initial from-fix '(1 2 1)))
             (unit (t4-algebra-lookup operator *t4-algebra-unit*))
             (rearranged (t4-algebra-associated lib operator unit *library-x* *library-y*))
             (unit-proof (t4-algebra-unit-with-replies lib operator middle nil replies)
                         :library)
             (step (proof-proof-chain (library-library-proof lib) beginning
                                      (list rearranged unit-proof)))
             (claim (t4-algebra-first step))
             (lib (library-library-lemma lib name claim step nil)))
          (t4-algebra-cite-result lib name (list a b)))))))

(defun t4-algebra-binary-fix-with-replies (lib operator a b index replies)
  (if (equal index 2)
      (t4-algebra-with-library lib
          ((move (t4-algebra-commuted lib operator b (list *t4-algebra-fix* a)))
           (removed (t4-algebra-binary-fix-first lib operator a b replies) :library)
           (returned (t4-algebra-commuted lib operator a b)))
        (cons (proof-proof-chain (library-library-proof lib) move (list removed returned))
              lib))
    (t4-algebra-binary-fix-first lib operator a b replies)))

(defun t4-algebra-binary-fix (lib operator a b index)
  (t4-algebra-public-result (t4-algebra-binary-fix-with-replies lib operator a b index nil)))

(defun t4-algebra-adjacent-result (lib operator a b c)
  (let ((name (if (equal operator *proof-plus*) "ADD-SWAP" "MULTIPLY-SWAP")))
    (if (t4-algebra-fact-present-p lib name)
        (t4-algebra-cite-result lib name (list a b c))
      (let ((proof (library-library-proof lib)))
        (t4-algebra-with-library lib
            ((association (t4-algebra-associated lib operator *library-x* *library-y* *library-z*))
             (first (proof-proof-symmetric proof association))
             (swap (t4-algebra-commuted lib operator *library-x* *library-y*))
             (first (proof-proof-rewrite proof first swap '(1 2 1)))
             (association (t4-algebra-associated lib operator *library-y* *library-x* *library-z*))
             (first (proof-proof-chain proof first (list association)))
             (claim (t4-algebra-first first))
             (lib (library-library-lemma lib name claim first nil)))
          (t4-algebra-cite-result lib name (list a b c)))))))

(defun t4-algebra-adjacent (lib operator a b c)
  (t4-algebra-public-result (t4-algebra-adjacent-result lib operator a b c)))

(defun t4-algebra-negative-inverse (lib term)
  (proof-with-checked-results
      ((commuted (t4-algebra-commuted lib *proof-plus* (library-minus term) term))
       (inverse (library-library-axiom lib "INVERSE-OF-+" (list term))))
    (proof-proof-chain (library-library-proof lib) commuted (list inverse))))

(defun t4-algebra-clear-addend-with-replies (lib a b replies)
  (let ((proof (library-library-proof lib)))
    (t4-algebra-with-library lib
        ((associated (t4-algebra-associated lib *proof-plus* (library-minus b) b a))
         (original (proof-proof-symmetric proof associated))
         (inverse (t4-algebra-negative-inverse lib b))
         (original (proof-proof-rewrite proof original inverse '(1 2 1)))
         (unit (t4-algebra-unit-with-replies lib *proof-plus* a nil replies) :library))
      (cons (proof-proof-chain (library-library-proof lib) original (list unit)) lib))))

(defun t4-algebra-clear-addend (lib a b)
  (t4-algebra-public-result (t4-algebra-clear-addend-with-replies lib a b nil)))

(defun t4-algebra-under-operation (lib premise template)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (t4-algebra-first premise))
         (sides (proof-list-of-length (cdr literal) 2))
         (before (proof-subst template (list (cons *proof-result* (car sides)))))
         (initial (proof-proof-reflexive proof before)))
      (proof-proof-rewrite-result proof initial premise
                                  (proof-eq *proof-false* template) *proof-result*))))

(defun t4-algebra-additive-inverse-with-replies (lib equation replies)
  (t4-algebra-with-library lib
      ((summed (t4-algebra-side equation 1))
       (summands (proof-list-of-length summed 3)))
    (let* ((a (cadr summands))
           (b (caddr summands))
           (negative (library-minus a)))
      (t4-algebra-with-library lib
          ((shifted (t4-algebra-under-operation lib equation
                                               (library-plus negative *proof-result*)))
           (removal (t4-algebra-clear-addend-with-replies lib b a replies) :library)
           (reduced (t4-algebra-side removal 2))
           (removal (if (proof-is-call reduced *t4-algebra-fix*)
                        (t4-algebra-with-library lib
                            ((fixed (t4-algebra-fixed-value lib b nil replies) :library))
                          (cons (proof-proof-chain (library-library-proof lib) removal (list fixed))
                                lib))
                      (cons removal lib))
                    :library)
           (move (t4-algebra-commuted lib *proof-plus* negative *proof-zero*))
           (unit (t4-algebra-unit-with-replies lib *proof-plus* negative nil replies) :library)
           (remaining (proof-proof-chain (library-library-proof lib) move (list unit)))
           (start (proof-proof-symmetric (library-library-proof lib) removal)))
        (cons (proof-proof-chain (library-library-proof lib) start (list shifted remaining))
              lib)))))

(defun t4-algebra-additive-inverse (lib equation)
  (t4-algebra-public-result (t4-algebra-additive-inverse-with-replies lib equation nil)))

(defun t4-algebra-multiply-zero-with-replies (lib value replies)
  (let ((name "PRODUCT-WITH-ZERO"))
    (if (t4-algebra-fact-present-p lib name)
        (t4-algebra-cite-result lib name (list value))
      (let* ((term (list *proof-times* *library-x* *proof-zero*))
             (added (library-plus (library-minus term) term)))
        (t4-algebra-with-library lib
            ((expansion (library-library-axiom lib "DISTRIBUTIVITY"
                                               (list *library-x* *proof-zero* *proof-zero*)))
             (zero (t4-algebra-constant lib (library-plus *proof-zero* *proof-zero*)
                                        replies) :library)
             (expansion (proof-proof-rewrite (library-library-proof lib) expansion zero '(1 1 2)))
             (initial (proof-proof-reflexive (library-library-proof lib) added))
             (shifted (proof-proof-rewrite (library-library-proof lib) initial expansion '(1 2 2)))
             (cancellation (t4-algebra-clear-addend-with-replies lib term term replies) :library)
             (inverse (t4-algebra-negative-inverse lib term))
             (inverse (proof-proof-symmetric (library-library-proof lib) inverse))
             (equality (proof-proof-chain (library-library-proof lib) inverse
                                          (list shifted cancellation)))
             (left (t4-algebra-commuted lib *proof-times* *proof-zero* *library-x*))
             (equality (proof-proof-symmetric (library-library-proof lib) equality))
             (equality (proof-proof-chain (library-library-proof lib) left (list equality)))
             (claim (t4-algebra-first equality))
             (lib (library-library-lemma lib name claim equality nil)))
          (t4-algebra-cite-result lib name (list value)))))))

(defun t4-algebra-multiply-zero (lib value)
  (t4-algebra-public-result (t4-algebra-multiply-zero-with-replies lib value nil)))

(defun t4-algebra-negate-product-lemma (lib name replies)
  (if (t4-algebra-fact-present-p lib name)
      (cons nil lib)
    (t4-algebra-with-library lib
        ((distributive (library-library-axiom lib "DISTRIBUTIVITY"
                                             (list *library-x* *library-y*
                                                   (library-minus *library-y*))))
         (inverse (library-library-axiom lib "INVERSE-OF-+" (list *library-y*)))
         (zero (proof-proof-rewrite (library-library-proof lib) distributive inverse '(1 1 2)))
         (start (t4-algebra-commuted lib *proof-times* *library-x* *proof-zero*))
         (end (t4-algebra-multiply-zero-with-replies lib *library-x* replies) :library)
         (product (proof-proof-chain (library-library-proof lib) start (list end)))
         (back (proof-proof-symmetric (library-library-proof lib) zero))
         (zero-sum (proof-proof-chain (library-library-proof lib) back (list product)))
         (step (t4-algebra-additive-inverse-with-replies lib zero-sum replies) :library)
         (claim (t4-algebra-first step))
         (lib (library-library-lemma lib name claim step nil)))
      (cons nil lib))))

(defun t4-algebra-negate-product-with-replies (lib a b index replies)
  (let* ((name "NEGATIVE-FACTOR")
         (built (t4-algebra-negate-product-lemma lib name replies)))
    (if (t4-algebra-interrupted-p (car built))
        built
      (let ((lib (cdr built)))
        (if (equal index 2)
            (t4-algebra-cite-result lib name (list a b))
          (t4-algebra-with-library lib
              ((move (t4-algebra-commuted lib *proof-times* (library-minus b) a))
               (instance (library-library-cite lib name (list a b) nil))
               (swap (t4-algebra-commuted lib *proof-times* a b))
               (negative (t4-algebra-under-operation lib swap (library-minus *proof-result*))))
            (cons (proof-proof-chain (library-library-proof lib) move (list instance negative))
                  lib)))))))

(defun t4-algebra-negate-product (lib a b index)
  (t4-algebra-public-result (t4-algebra-negate-product-with-replies lib a b index nil)))

(defun t4-algebra-double-negative-with-replies (lib value replies)
  (let ((name "DOUBLE-NEGATIVE-FIX"))
    (if (t4-algebra-fact-present-p lib name)
        (t4-algebra-cite-result lib name (list value))
      (let* ((proof (library-library-proof lib))
             (negative (library-minus *library-x*))
             (again (library-minus negative)))
        (t4-algebra-with-library lib
            ((expanded (t4-algebra-associated lib *proof-plus* *library-x* negative again))
             (inverse (library-library-axiom lib "INVERSE-OF-+" (list *library-x*)))
             (expanded (proof-proof-rewrite proof expanded inverse '(1 1 1)))
             (inverse (library-library-axiom lib "INVERSE-OF-+" (list negative)))
             (expanded (proof-proof-rewrite proof expanded inverse '(1 2 2)))
             (move (t4-algebra-commuted lib *proof-plus* *library-x* *proof-zero*))
             (unit (t4-algebra-unit-with-replies lib *proof-plus* *library-x* nil replies)
                   :library)
             (remainder (proof-proof-chain (library-library-proof lib) move (list unit)))
             (unit (t4-algebra-unit-with-replies lib *proof-plus* again nil replies) :library)
             (start (proof-proof-symmetric (library-library-proof lib) unit))
             (equation (proof-proof-chain (library-library-proof lib) start (list expanded remainder)))
             (claim (t4-algebra-first equation))
             (lib (library-library-lemma lib name claim equation nil)))
          (t4-algebra-cite-result lib name (list value)))))))

(defun t4-algebra-double-negative (lib value)
  (t4-algebra-public-result (t4-algebra-double-negative-with-replies lib value nil)))

(defun t4-algebra-value-of (test lib step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((literal (t4-algebra-first step)))
      (cond
       ((equal literal test)
        (proof-with-checked-results
            ((args (proof-list-of-length (cdr test) 2))
             (same (proof-proof-fact proof "equal-same" (list (list *library-x* (car args))))))
          (if (equal (car args) (cadr args))
              same
            (proof-with-checked-results
                ((rewritten (proof-proof-rewrite proof same step '(1 1 2))))
              (proof-proof-tidy proof rewritten)))))
       ((not (equal literal (proof-neg test)))
        '(:failure "InferenceMismatch" ""))
       (t
        (proof-with-checked-results
            ((boolean (proof-proof-nil-or-true proof test))
             (positive (proof-proof-front proof boolean test))
             (resolved (proof-proof-cut proof positive step)))
          (proof-proof-front proof resolved (proof-eq test *proof-false*))))))))

(defun t4-algebra-equality-tests (lib a b forward backward)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof a t))
         (left (t4-algebra-value-of a lib assumed))
         (right (t4-algebra-value-of b lib forward))
         (right (proof-proof-symmetric proof right))
         (yes (proof-proof-chain proof left (list right)))
         (denied (proof-proof-assume proof a nil))
         (denied (proof-proof-cut proof backward denied))
         (denied (proof-proof-front proof denied (proof-neg b)))
         (assumption (proof-proof-assume proof a nil))
         (left (t4-algebra-value-of a lib assumption))
         (right (t4-algebra-value-of b lib denied))
         (right (proof-proof-symmetric proof right))
         (no (proof-proof-chain proof left (list right))))
      (proof-proof-cases proof a yes no))))

(defun t4-algebra-rejected-part (lib guard contrary part)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((denied (t4-algebra-first contrary))
         (affirmed (t4-algebra-first part)))
      (cond
       ((equal denied (proof-neg affirmed))
        (proof-with-checked-results ((resolved (proof-proof-cut proof part contrary)))
          (proof-proof-front proof resolved (proof-neg guard))))
       ((equal affirmed (proof-neg denied))
        (proof-with-checked-results ((resolved (proof-proof-cut proof contrary part)))
          (proof-proof-front proof resolved (proof-neg guard))))
       (t nil)))))

(defun t4-algebra-rejected-guard-parts (n lib guard contrary conjunction)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-algebra-rejected-guard-parts")
    (proof-with-checked-results
        ((literal (t4-algebra-first conjunction))
         (head (and (proof-compound literal) (proof-term-at literal 0)))
         (otherwise (and (equal head *proof-if*) (proof-term-at literal 3))))
      (if (equal otherwise *proof-false*)
          (proof-with-checked-results
              ((parts (proof-proof-conjunct (library-library-proof lib) conjunction))
               (answer (t4-algebra-rejected-part lib guard contrary (car parts))))
            (or answer
                (t4-algebra-rejected-guard-parts (1- n) lib guard contrary (cadr parts))))
        (or (t4-algebra-rejected-part lib guard contrary conjunction)
            '(:failure "SearchMiss" ""))))))

(defun t4-algebra-rejected-guard (lib guard contrary)
  (proof-with-checked-results
      ((assumed (proof-proof-assume (library-library-proof lib) guard t)))
    (t4-algebra-rejected-guard-parts 1000000 lib guard contrary assumed)))

(defun t4-algebra-inverse-zero (lib operator value rejected)
  (let ((name (if (equal operator *proof-minus*)
                  "COMPLETION-OF-UNARY-MINUS"
                "COMPLETION-OF-UNARY-/")))
    (proof-with-checked-results
        ((raw (library-library-axiom lib name (list value)))
         (body (t4-algebra-side raw 2))
         (guard (proof-term-at body 1))
         (literal (t4-algebra-first rejected))
         (denied (if (equal literal (proof-neg guard))
                     rejected
                   (t4-algebra-rejected-guard lib guard rejected))))
      (t4-algebra-choose lib raw denied))))

(defun t4-algebra-unary-fix-with-replies (lib operator value replies)
  (let ((name (if (equal operator *proof-minus*) "NEGATION-OF-FIX" "RECIPROCAL-OF-FIX")))
    (if (t4-algebra-fact-present-p lib name)
        (t4-algebra-cite-result lib name (list value))
      (let ((proof (library-library-proof lib))
            (test (list *library-numberp* *library-x*))
            (claim (list operator (list *t4-algebra-fix* *library-x*))))
        (t4-algebra-with-library lib
            ((affirmed (proof-proof-assume proof test t))
             (denied (proof-proof-assume proof test nil))
             (yes (proof-proof-reflexive proof claim))
             (selected (t4-algebra-fixed lib *library-x* affirmed))
             (yes (proof-proof-rewrite proof yes selected '(1 2 1)))
             (no (proof-proof-reflexive proof claim))
             (selected (t4-algebra-fixed lib *library-x* denied))
             (no (proof-proof-rewrite proof no selected '(1 2 1)))
             (at-zero (if (equal operator *proof-minus*)
                          (t4-algebra-constant lib (library-minus *proof-zero*) replies)
                        (cons (proof-with-checked-results
                                  ((refl (proof-proof-reflexive proof *proof-zero*)))
                                (t4-algebra-inverse-zero lib operator *proof-zero* refl))
                              lib))
                      :library)
             (invalid (t4-algebra-inverse-zero lib operator *library-x* denied))
             (back (proof-proof-symmetric (library-library-proof lib) invalid))
             (no (proof-proof-chain (library-library-proof lib) no (list at-zero back)))
             (target (t4-algebra-first yes))
             (cases (proof-proof-cases (library-library-proof lib) test yes no))
             (lib (library-library-lemma lib name target cases nil)))
          (t4-algebra-cite-result lib name (list value)))))))

(defun t4-algebra-unary-fix (lib operator value)
  (t4-algebra-public-result (t4-algebra-unary-fix-with-replies lib operator value nil)))

(defun t4-algebra-nonzero-reciprocal-with-replies (lib reciprocal product replies)
  (let ((test (proof-eq reciprocal *proof-zero*)))
    (t4-algebra-with-library lib
        ((same (proof-proof-assume (library-library-proof lib) test t))
         (calculated (proof-proof-rewrite (library-library-proof lib) product same '(1 1 2)))
         (lhs (t4-algebra-side product 1))
         (operand (proof-term-at lhs 1))
         (zero (t4-algebra-multiply-zero-with-replies lib operand replies) :library)
         (move (t4-algebra-commuted lib *proof-times* operand *proof-zero*))
         (zero (proof-proof-chain (library-library-proof lib) move (list zero)))
         (impossible (proof-proof-rewrite (library-library-proof lib) calculated zero '(1 1)))
         (literal (t4-algebra-first impossible))
         (constant (t4-algebra-constant lib literal replies) :library)
         (impossible (proof-proof-rewrite (library-library-proof lib) impossible constant '(1))))
      (cons (proof-proof-front (library-library-proof lib) impossible (proof-neg test))
            lib))))

(defun t4-algebra-nonzero-reciprocal (lib reciprocal product)
  (t4-algebra-public-result (t4-algebra-nonzero-reciprocal-with-replies lib reciprocal product nil)))

(defun t4-algebra-denied-zero (lib term opposite premises)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((denied (t4-algebra-find-premise premises (proof-neg opposite))))
      (if denied
          denied
        (proof-with-checked-results
            ((reverse (t4-algebra-find-premise premises (proof-neg (proof-eq *proof-zero* term)))))
          (and reverse
            (proof-with-checked-results
                ((assumed (proof-proof-assume proof opposite t))
                 (reversed (proof-proof-symmetric proof assumed))
                 (cut (proof-proof-cut proof reversed reverse)))
              (proof-proof-front proof cut (proof-neg opposite)))))))))

(defun t4-algebra-product-inverse-with-replies (lib term premises replies)
  (t4-algebra-with-library lib
      ((denied (t4-algebra-denied-zero lib term (proof-eq term *proof-zero*) premises)))
    (if (not denied)
        (cons nil lib)
      (t4-algebra-with-library lib
          ((typed (t4-algebra-number-with-replies lib term premises replies) :library)
           (argument (t4-division-combine lib (list typed denied)))
           (axiom (library-library-axiom lib "INVERSE-OF-*" (list term))))
        (cons (proof-proof-modus-ponens (library-library-proof lib) axiom argument)
              lib)))))

(defun t4-algebra-product-inverse (lib term premises)
  (t4-algebra-public-result (t4-algebra-product-inverse-with-replies lib term premises nil)))

(defun t4-algebra-double-reciprocal-invalid-result (why number-assumption value-at-zero lib again)
  (let ((proof (library-library-proof lib)))
    (t4-algebra-with-library lib
        ((first (proof-proof-reflexive proof again))
         (invalid (t4-algebra-inverse-zero lib *t4-algebra-reciprocal* *library-x* why))
         (first (proof-proof-rewrite proof first invalid '(1 2 1)))
         (zero (proof-proof-reflexive proof *proof-zero*))
         (invalid (t4-algebra-inverse-zero lib *t4-algebra-reciprocal* *proof-zero* zero))
         (first (proof-proof-chain proof first (list invalid)))
         (fixed (t4-algebra-fixed lib *library-x* number-assumption))
         (wanted (proof-proof-chain proof fixed (list value-at-zero)))
         (wanted (proof-proof-symmetric proof wanted)))
      (cons (proof-proof-chain proof first (list wanted)) lib))))

(defun t4-algebra-double-reciprocal-invalid (why number-assumption value-at-zero lib again)
  (t4-algebra-public-result
   (t4-algebra-double-reciprocal-invalid-result why number-assumption value-at-zero lib again)))

(defun t4-algebra-double-reciprocal-with-replies (lib value replies)
  (let ((name "DOUBLE-RECIPROCAL-FIX"))
    (if (t4-algebra-fact-present-p lib name)
        (t4-algebra-cite-result lib name (list value))
      (let* ((proof (library-library-proof lib))
             (number-test (list *library-numberp* *library-x*))
             (zero-test (proof-eq *library-x* *proof-zero*))
             (rec (list *t4-algebra-reciprocal* *library-x*))
             (again (list *t4-algebra-reciprocal* rec)))
        (t4-algebra-with-library lib
            ((isnum (proof-proof-assume proof number-test t))
             (notnum (proof-proof-assume proof number-test nil))
             (zx (proof-proof-assume proof zero-test t))
             (nzx (proof-proof-assume proof zero-test nil))
             (zero-case (t4-algebra-double-reciprocal-invalid-result zx isnum zx lib again)
                        :library)
             (nonnumeric (t4-algebra-double-reciprocal-invalid-result notnum notnum nil lib again)
                         :library)
             (product (t4-algebra-product-inverse-with-replies lib *library-x* (list isnum nzx) replies)
                      :library)
             (nzrec (t4-algebra-nonzero-reciprocal-with-replies lib rec product replies) :library)
             (reciprocal-product (t4-algebra-product-inverse-with-replies lib rec (list nzrec)
                                                                        replies) :library)
             (equation (t4-algebra-associated lib *proof-times* *library-x* rec again))
             (equation (proof-proof-rewrite (library-library-proof lib) equation product '(1 1 1)))
             (equation (proof-proof-rewrite (library-library-proof lib) equation reciprocal-product
                                            '(1 2 2)))
             (unit (t4-algebra-unit-with-replies lib *proof-times* again nil replies) :library)
             (beginning (proof-proof-symmetric (library-library-proof lib) unit))
             (moved (t4-algebra-commuted lib *proof-times* *library-x* *proof-one*))
             (unit (t4-algebra-unit-with-replies lib *proof-times* *library-x* (list isnum) replies)
                   :library)
             (fixed (t4-algebra-fixed lib *library-x* isnum))
             (ending (proof-proof-symmetric (library-library-proof lib) fixed))
             (result (proof-proof-chain (library-library-proof lib) beginning
                                        (list equation moved unit ending)))
             (numeric (proof-proof-cases (library-library-proof lib) zero-test zero-case result))
             (result (proof-proof-cases (library-library-proof lib) number-test numeric nonnumeric))
             (lib (library-library-lemma lib name (proof-eq again (list *t4-algebra-fix* *library-x*))
                                          result nil)))
          (t4-algebra-cite-result lib name (list value)))))))

(defun t4-algebra-double-reciprocal (lib value)
  (t4-algebra-public-result (t4-algebra-double-reciprocal-with-replies lib value nil)))

(defun t4-algebra-branch-value (lib term equation premises)
  (if (endp premises)
      equation
    (let ((premise (car premises)))
      (proof-with-checked-results ((literal (t4-algebra-first premise)))
        (if (and (or (equal literal term) (equal literal (proof-neg term)))
                 (proof-is-call term *proof-equal*))
            (proof-with-checked-results ((value (t4-algebra-value-of term lib premise)))
              (proof-proof-chain (library-library-proof lib) equation (list value)))
          (t4-algebra-branch-value lib term equation (cdr premises)))))))

(defun t4-algebra-opposite (operator)
  (if (equal operator *proof-plus*) *proof-minus* *t4-algebra-reciprocal*))

(defun t4-algebra-element-key (term operator)
  (cond
   ((proof-is-call term *proof-quote*)
    (proof-with-checked-results ((text (proof-write term)))
      (list 0 text 0)))
   ((proof-is-call term (t4-algebra-opposite operator))
    (proof-with-checked-results ((argument (proof-term-at term 1))
                                 (text (proof-write argument)))
      (list 1 text 1)))
   (t (proof-with-checked-results ((text (proof-write term)))
        (list 1 text 0)))))

(defun t4-algebra-operand-indices (term indices)
  (if (endp indices)
      term
    (let* ((index (car indices))
           (offset (if (< index 0) (+ (len term) index) index)))
      (proof-with-checked-results
          ((value (if (and (< offset 0) (not (integerp term)))
                      '(:failure "failure" "")
                    (proof-term-at term offset))))
        (t4-algebra-operand-indices value (cdr indices))))))

(defun t4-algebra-operand-at (step place)
  (proof-with-checked-results ((literal (t4-algebra-first step)))
    (t4-algebra-operand-indices literal (cdr place))))

(defun t4-algebra-adjacent-reduction-with-replies (lib operator a b premises replies)
  (t4-algebra-with-library lib
      ((constant (t4-algebra-constant lib (list operator a b) replies) :library))
    (if constant
        (cons constant lib)
      (t4-algebra-with-library lib
          ((unit (t4-algebra-lookup operator *t4-algebra-unit*)))
        (cond
         ((equal a unit)
          (t4-algebra-unit-with-replies lib operator b premises replies))
         ((equal b unit)
          (t4-algebra-with-library lib
              ((move (t4-algebra-commuted lib operator a b))
               (identity (t4-algebra-unit-with-replies lib operator a premises replies) :library))
            (cons (proof-proof-chain (library-library-proof lib) move (list identity)) lib)))
         ((and (equal operator *proof-times*)
               (or (equal a *proof-zero*) (equal b *proof-zero*)))
          (let ((left-zero (equal a *proof-zero*)))
            (t4-algebra-with-library lib
                ((zero (t4-algebra-multiply-zero-with-replies lib (if left-zero b a) replies)
                       :library))
              (if left-zero
                  (cons zero lib)
                (t4-algebra-with-library lib
                    ((move (t4-algebra-commuted lib operator a b)))
                  (cons (proof-proof-chain (library-library-proof lib) move (list zero)) lib))))))
         ((not (equal b (list (t4-algebra-opposite operator) a)))
          (cons nil lib))
         ((equal operator *proof-plus*)
          (cons (library-library-axiom lib "INVERSE-OF-+" (list a)) lib))
         (t (t4-algebra-product-inverse-with-replies lib a premises replies)))))))

(defun t4-algebra-adjacent-reduction (lib operator a b premises)
  (t4-algebra-public-result
   (t4-algebra-adjacent-reduction-with-replies lib operator a b premises nil)))

(defun t4-algebra-associate-right (n lib step operator place)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-algebra-associate-right")
    (proof-with-checked-results ((operand (t4-algebra-operand-at step place)))
      (if (not (proof-is-call operand operator))
          step
        (proof-with-checked-results ((parts (proof-list-of-length operand 3)))
          (let ((left (cadr parts))
                (right (caddr parts)))
            (if (not (proof-is-call left operator))
                (t4-algebra-associate-right (1- n) lib step operator (append place '(2)))
              (proof-with-checked-results
                  ((args (t4-algebra-binary-operands (cdr left)))
                   (swap (t4-algebra-associated lib operator (car args) (cadr args) right))
                   (step (proof-proof-rewrite (library-library-proof lib) step swap place)))
                (t4-algebra-associate-right (1- n) lib step operator place)))))))))

(defun t4-algebra-swap-adjacent (lib operator a b suffix rest)
  (if suffix
      (t4-algebra-with-library lib ((c (proof-term-at rest 2)))
        (t4-algebra-adjacent-result lib operator a b c))
    (cons (t4-algebra-commuted lib operator a b) lib)))

(defun t4-algebra-association-sort-pass (n lib step operator place changed)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (cons '(:failure "Fuel" "t4-algebra-association-sort-pass") lib)
    (t4-algebra-with-library lib ((operand (t4-algebra-operand-at step place)))
      (if (not (proof-is-call operand operator))
          (cons (list step changed) lib)
        (t4-algebra-with-library lib ((parts (proof-list-of-length operand 3)))
          (let* ((a (cadr parts))
                 (rest (caddr parts))
                 (suffix (proof-is-call rest operator))
                 (next-place (append place '(2))))
            (t4-algebra-with-library lib
                ((b (if suffix (proof-term-at rest 1) rest))
                 (a-key (t4-algebra-element-key a operator))
                 (b-key (t4-algebra-element-key b operator)))
              (if (value-less b-key a-key)
                  (t4-algebra-with-library lib
                      ((swap (t4-algebra-swap-adjacent lib operator a b suffix rest) :library)
                       (step (proof-proof-rewrite (library-library-proof lib) step swap place)))
                    (t4-algebra-association-sort-pass (1- n) lib step operator next-place t))
                (t4-algebra-association-sort-pass (1- n) lib step operator next-place changed)))))))))

(defun t4-algebra-association-sort (n lib step operator)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (cons '(:failure "Fuel" "t4-algebra-association-sort") lib)
    (t4-algebra-with-library lib
        ((pass (t4-algebra-association-sort-pass 1000000 lib step operator '(1 2) nil)
               :library))
      (if (cadr pass)
          (t4-algebra-association-sort (1- n) lib (car pass) operator)
        (cons (car pass) lib)))))

(defun t4-algebra-normalize-association-with-replies (lib step operator replies)
  (declare (ignore replies))
  (t4-algebra-with-library lib
      ((step (t4-algebra-associate-right 1000000 lib step operator '(1 2))))
    (t4-algebra-association-sort 1000000 lib step operator)))

(defun t4-algebra-normalize-association (lib step operator)
  (t4-algebra-public-result (t4-algebra-normalize-association-with-replies lib step operator nil)))

(defun t4-algebra-association-regroup (lib step operator a b rest place)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((last (proof-term-at rest 2))
         (grouped (t4-algebra-associated lib operator a b last))
         (grouped (proof-proof-symmetric proof grouped)))
      (proof-proof-rewrite proof step grouped place))))

(defun t4-algebra-reduce-association-from (n lib step operator premises place replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (cons '(:failure "Fuel" "t4-algebra-reduce-association-from") lib)
    (t4-algebra-with-library lib ((operand (t4-algebra-operand-at step place)))
      (if (not (proof-is-call operand operator))
          (cons step lib)
        (t4-algebra-with-library lib ((parts (proof-list-of-length operand 3)))
          (let* ((a (cadr parts))
                 (rest (caddr parts))
                 (suffix (proof-is-call rest operator)))
            (t4-algebra-with-library lib
                ((b (if suffix (proof-term-at rest 1) rest))
                 (unit (t4-algebra-lookup operator *t4-algebra-unit*)))
              (if (or (equal a unit)
                      (and (equal operator *proof-times*) (equal a *proof-zero*)))
                  (t4-algebra-with-library lib
                      ((reduced (t4-algebra-adjacent-reduction-with-replies
                                 lib operator a rest premises replies) :library)
                       (step (proof-proof-rewrite (library-library-proof lib) step reduced place)))
                    (t4-algebra-reduce-association-from (1- n) lib step operator premises place
                                                        replies))
                (t4-algebra-with-library lib
                    ((reduction (t4-algebra-adjacent-reduction-with-replies
                                 lib operator a b premises replies) :library))
                  (if (not reduction)
                      (t4-algebra-reduce-association-from (1- n) lib step operator premises
                                                          (append place '(2)) replies)
                    (t4-algebra-with-library lib
                        ((step (if suffix
                                   (t4-algebra-association-regroup
                                    lib step operator a b rest place)
                                 step))
                         (step (proof-proof-rewrite (library-library-proof lib) step reduction
                                                     (if suffix (append place '(1)) place))))
                      (t4-algebra-reduce-association-from (1- n) lib step operator premises
                                                          '(1 2) replies))))))))))))

(defun t4-algebra-reduce-association-with-replies (lib step operator premises replies)
  (t4-algebra-reduce-association-from 1000000 lib step operator premises '(1 2) replies))

(defun t4-algebra-reduce-association (lib step operator premises)
  (t4-algebra-public-result
   (t4-algebra-reduce-association-with-replies lib step operator premises nil)))

(defun t4-algebra-remove-operand-fixes (lib step operator indices replies)
  (declare (xargs :measure (acl2-count indices)))
  (if (not (o< (acl2-count (cdr indices)) (acl2-count indices)))
      (cons step lib)
    (let ((index (car indices)))
      (t4-algebra-with-library lib
          ((term (t4-algebra-side step 2))
           (args (cdr term))
           (arg (proof-term-at args (1- index)))
           (step (if (proof-is-call arg *t4-algebra-fix*)
                     (t4-algebra-with-library lib
                         ((raw (proof-term-at arg 1))
                          (other (proof-term-at args (- 2 index)))
                          (replacement (t4-algebra-binary-fix-with-replies lib operator raw other
                                                                          index replies) :library))
                       (cons (proof-proof-chain (library-library-proof lib) step (list replacement))
                             lib))
                   (cons step lib))
                 :library))
        (t4-algebra-remove-operand-fixes lib step operator (cdr indices) replies)))))

(defun t4-algebra-negative-operand (step indices)
  (if (endp indices)
      nil
    (let ((index (car indices)))
      (proof-with-checked-results
          ((term (t4-algebra-side step 2))
           (arg (proof-term-at (cdr term) (1- index))))
        (if (proof-is-call arg *proof-minus*)
            (proof-with-checked-results
                ((other (proof-term-at (cdr term) (- 2 index)))
                 (raw (proof-term-at arg 1)))
              (list other raw index))
          (t4-algebra-negative-operand step (cdr indices)))))))

(defun t4-algebra-normal-fixed (lib step reduced premises replies)
  (let* ((fixed (t4-algebra-with-library lib
                    ((argument (proof-term-at reduced 1)))
                  (t4-algebra-fixed-value lib argument premises replies)))
         (lib (cdr fixed))
         (value (car fixed))
         (result (if (t4-algebra-interrupted-p value)
                     value
                   (proof-proof-chain (library-library-proof lib) step (list value)))))
    (cons (if (t4-algebra-search-miss-p result) step result) lib)))

(defun t4-algebra-normal-constant (lib step reduced premises replies)
  (t4-algebra-with-library lib
      ((constant (t4-algebra-constant lib reduced replies) :library))
    (if constant
        (cons (proof-proof-chain (library-library-proof lib) step (list constant)) lib)
      (t4-algebra-with-library lib
          ((branched (t4-algebra-branch-value lib reduced step premises)))
        (cons (proof-proof-tidy (library-library-proof lib) branched) lib)))))

(mutual-recursion
 (defun t4-algebra-normal-visit (n lib term premises replies)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t4-algebra-normal-visit") lib)
     (if (or (not (proof-compound term)) (proof-is-call term *proof-quote*))
         (cons (proof-proof-reflexive (library-library-proof lib) term) lib)
       (t4-algebra-with-library lib
           ((head (proof-term-at term 0))
            (step (proof-proof-reflexive (library-library-proof lib) term))
            (step (t4-algebra-normal-children (1- n) lib step (cdr term) 1 premises replies)
                  :library)
            (reduced (t4-algebra-side step 2)))
         (cond
          ((assoc-equal head *t4-algebra-operations*)
           (t4-algebra-normal-binary (1- n) lib head step premises replies))
          ((member-equal head (list *proof-minus* *t4-algebra-reciprocal*))
           (t4-algebra-normal-unary (1- n) lib head step reduced premises replies))
          ((equal head *t4-algebra-fix*)
           (t4-algebra-normal-fixed lib step reduced premises replies))
          ((equal head *proof-less*)
           (t4-algebra-normal-less (1- n) lib step reduced premises replies))
          (t (t4-algebra-normal-constant lib step reduced premises replies)))))))

 (defun t4-algebra-normal-children (n lib step children index premises replies)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n)))
     (cons '(:failure "Fuel" "t4-algebra-normal-children") lib))
    ((endp children) (cons step lib))
    (t (t4-algebra-with-library lib
           ((known (t4-algebra-normal-visit (1- n) lib (car children) premises replies)
                   :library)
            (left (t4-algebra-side known 1))
            (right (t4-algebra-side known 2))
            (step (if (equal left right)
                      step
                    (proof-proof-rewrite (library-library-proof lib) step known
                                         (list 1 2 index)))))
         (t4-algebra-normal-children (1- n) lib step (cdr children) (1+ index) premises replies)))))

 (defun t4-algebra-normal-binary (n lib head step premises replies)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t4-algebra-normal-binary") lib)
     (t4-algebra-with-library lib
         ((step (t4-algebra-remove-operand-fixes lib step head '(1 2) replies) :library)
          (factor (and (equal head *proof-times*)
                       (t4-algebra-negative-operand step '(2 1)))))
       (if factor
           (t4-algebra-with-library lib
               ((signed (t4-algebra-negate-product-with-replies lib (car factor) (cadr factor)
                                                               (caddr factor) replies) :library)
                (result (t4-algebra-side signed 2))
                (normalized (t4-algebra-normal-visit (1- n) lib result premises replies) :library))
             (cons (proof-proof-chain (library-library-proof lib) step (list signed normalized))
                   lib))
         (t4-algebra-with-library lib
             ((step (t4-algebra-normalize-association-with-replies lib step head replies) :library)
              (step (t4-algebra-reduce-association-with-replies lib step head premises replies)
                    :library))
           (cons (proof-proof-tidy (library-library-proof lib) step) lib))))))

 (defun t4-algebra-normal-unary (n lib head step reduced premises replies)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t4-algebra-normal-unary") lib)
     (t4-algebra-with-library lib ((operand (proof-term-at reduced 1)))
       (cond
        ((proof-is-call operand *t4-algebra-fix*)
         (t4-algebra-with-library lib
             ((argument (proof-term-at operand 1))
              (replacement (t4-algebra-unary-fix-with-replies lib head argument replies)
                           :library))
           (cons (proof-proof-chain (library-library-proof lib) step (list replacement)) lib)))
        ((proof-is-call operand head)
         (t4-algebra-with-library lib
             ((argument (proof-term-at operand 1))
              (removed (if (equal head *proof-minus*)
                           (t4-algebra-double-negative-with-replies lib argument replies)
                         (t4-algebra-double-reciprocal-with-replies lib argument replies))
                       :library)
              (result (t4-algebra-side removed 2))
              (normalized (t4-algebra-normal-visit (1- n) lib result premises replies) :library))
           (cons (proof-proof-chain (library-library-proof lib) step (list removed normalized))
                 lib)))
        ((and (equal head *proof-minus*) (proof-is-call operand *proof-plus*))
         (t4-algebra-with-library lib
             ((args (t4-algebra-binary-operands (cdr operand)))
              (expanded (t4-algebra-negate-sum-visit (1- n) lib (car args) (cadr args) replies)
                        :library)
              (result (t4-algebra-side expanded 2))
              (normalized (t4-algebra-normal-visit (1- n) lib result premises replies) :library))
           (cons (proof-proof-chain (library-library-proof lib) step (list expanded normalized))
                 lib)))
        ((and (equal head *t4-algebra-reciprocal*) (equal operand *proof-zero*))
         (t4-algebra-with-library lib
             ((refl (proof-proof-reflexive (library-library-proof lib) *proof-zero*))
              (zero (t4-algebra-inverse-zero lib head *proof-zero* refl)))
           (cons (proof-proof-chain (library-library-proof lib) step (list zero)) lib)))
        (t (t4-algebra-normal-constant lib step reduced premises replies))))))

 (defun t4-algebra-normal-less (n lib step reduced premises replies)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t4-algebra-normal-less") lib)
     (t4-algebra-with-library lib
         ((constant (t4-algebra-constant lib reduced replies) :library))
       (if constant
           (cons (proof-proof-chain (library-library-proof lib) step (list constant)) lib)
         (t4-algebra-with-library lib
             ((difference (library-library-axiom lib "<-ON-OTHERS" (cdr reduced)))
              (body (t4-algebra-side difference 2))
              (delta (proof-term-at body 1))
              (delta (t4-algebra-normal-visit (1- n) lib delta premises replies) :library)
              (moved (proof-proof-rewrite (library-library-proof lib) difference delta '(1 2 1)))
              (result (t4-algebra-side moved 2))
              (constant (t4-algebra-constant lib result replies) :library))
           (cons (proof-proof-chain (library-library-proof lib) step (list moved constant))
                 lib))))))

 (defun t4-algebra-negate-sum-visit (n lib a b replies)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t4-algebra-negate-sum-visit") lib)
     (let ((name "NEGATIVE-OF-SUM"))
       (if (t4-algebra-fact-present-p lib name)
           (t4-algebra-cite-result lib name (list a b))
         (let* ((positive (library-plus *library-x* *library-y*))
                (negative (library-plus (library-minus *library-x*)
                                        (library-minus *library-y*)))
                (sum (library-plus positive negative)))
           (t4-algebra-with-library lib
               ((summed (t4-algebra-normal-visit (1- n) lib sum nil replies) :library)
                (inverse (t4-algebra-additive-inverse-with-replies lib summed replies) :library)
                (step (proof-proof-symmetric (library-library-proof lib) inverse))
                (claim (t4-algebra-first step))
                (lib (library-library-lemma lib name claim step nil)))
             (t4-algebra-cite-result lib name (list a b)))))))))

(defun t4-algebra-normal-with-replies (lib term premises replies)
  (t4-algebra-normal-visit 1000000 lib term premises replies))

(defun t4-algebra-normal (lib term premises)
  (t4-algebra-public-result (t4-algebra-normal-with-replies lib term premises nil)))

(defun t4-algebra-negate-sum-with-replies (lib a b replies)
  (t4-algebra-negate-sum-visit 1000000 lib a b replies))

(defun t4-algebra-negate-sum (lib a b)
  (t4-algebra-public-result (t4-algebra-negate-sum-with-replies lib a b nil)))

(mutual-recursion
 (defun t4-algebra-has-arithmetic (term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (proof-compound term)) nil)
    ((endp term) '(:failure "failure" ""))
    ((proof-is-call term *proof-quote*) nil)
    ((or (assoc-equal (car term) *t4-algebra-operations*)
         (member-equal (car term) (list *proof-minus* *t4-algebra-reciprocal* *t4-algebra-fix*)))
     t)
    (t (t4-algebra-has-arithmetic-in-args (cdr term)))))

 (defun t4-algebra-has-arithmetic-in-args (args)
   (declare (xargs :measure (acl2-count args)))
   (and (consp args)
        (or (t4-algebra-has-arithmetic (car args))
            (t4-algebra-has-arithmetic-in-args (cdr args))))))

(defun t4-algebra-formula-parts (formula)
  (if (proof-is-call formula *library-implies*)
      (proof-list-of-length (cdr formula) 2)
    (list :none formula)))

(defun t4-algebra-has-guard-p (guard)
  (not (or (eq guard :none) (not guard) (equal guard 0) (equal guard ""))))

(defun t4-algebra-guard-premises (lib guard)
  (if (not (t4-algebra-has-guard-p guard))
      nil
    (proof-with-checked-results
        ((assumed (proof-proof-assume (library-library-proof lib) guard t)))
      (t4-division-pieces lib assumed))))

(defun t4-algebra-normal-sides (lib parts premises replies)
  (if (endp parts)
      (cons '(:failure "SearchMiss" "") lib)
    (t4-algebra-with-library lib
        ((left (t4-algebra-normal-with-replies lib (car parts) premises replies) :library))
      (if (endp (cdr parts))
          (cons '(:failure "SearchMiss" "") lib)
        (t4-algebra-with-library lib
            ((right (t4-algebra-normal-with-replies lib (cadr parts) premises replies) :library))
          (if (endp (cddr parts))
              (cons (list left right) lib)
            (let ((third (t4-algebra-normal-with-replies lib (caddr parts) premises replies)))
              (if (t4-algebra-interrupted-p (car third))
                  third
                (cons '(:failure "SearchMiss" "") (cdr third))))))))))

(defun t4-algebra-arithmetic-identity-proof (lib guard goal replies)
  (t4-algebra-with-library lib
      ((premises (t4-algebra-guard-premises lib guard))
       (sides (t4-algebra-normal-sides lib (cdr goal) premises replies) :library)
       (left (t4-algebra-side (car sides) 2))
       (right (t4-algebra-side (cadr sides) 2)))
    (if (not (equal left right))
        (cons nil lib)
      (let ((proof (library-library-proof lib)))
        (t4-algebra-with-library lib
            ((back (proof-proof-symmetric proof (cadr sides)))
             (step (proof-proof-chain proof (car sides) (list back))))
          (cons (if (t4-algebra-has-guard-p guard)
                    (t4-division-imply lib guard step)
                  step)
                lib))))))

(defun t4-algebra-arithmetic-identity-with-replies (lib formula replies)
  (t4-algebra-with-library lib
      ((parts (t4-algebra-formula-parts formula))
       (arithmetic (and (proof-is-call (cadr parts) *proof-equal*)
                        (t4-algebra-has-arithmetic (cadr parts)))))
    (if (not arithmetic)
        (cons nil lib)
      (let ((built (t4-algebra-query :arithmetic lib nil replies)))
        (if (t4-algebra-interrupted-p (car built))
            built
          (t4-algebra-arithmetic-identity-proof (cdr built) (car parts) (cadr parts) replies))))))

(defun t4-algebra-arithmetic-identity (lib formula)
  (t4-algebra-public-result (t4-algebra-arithmetic-identity-with-replies lib formula nil)))

(defun t4-algebra-normalize-arguments (lib terms premises replies)
  (declare (xargs :measure (acl2-count terms)))
  (if (not (o< (acl2-count (cdr terms)) (acl2-count terms)))
      (cons nil lib)
    (t4-algebra-with-library lib
        ((step (t4-algebra-normal-with-replies lib (car terms) premises replies) :library)
         (rest (t4-algebra-normalize-arguments lib (cdr terms) premises replies) :library))
      (cons (cons step rest) lib))))

(defun t4-algebra-orient-rewrites (lib step initial)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left (proof-term-at initial 0))
         (rewritten (proof-proof-rewrite proof step left '(1 1)))
         (right (proof-term-at initial 1)))
      (proof-proof-rewrite proof rewritten right '(1 2)))))

(defun t4-algebra-orient-normalized-with-replies (lib step goal premises replies)
  (t4-algebra-with-library lib
      ((literal (t4-algebra-first step))
       (initial (t4-algebra-normalize-arguments lib (cdr literal) premises replies) :library)
       (candidate (t4-algebra-orient-rewrites lib step initial))
       (sides (t4-algebra-normal-sides lib (cdr goal) premises replies) :library)
       (actual (t4-algebra-first candidate))
       (right (t4-algebra-side (cadr sides) 2))
       (left (t4-algebra-side (car sides) 2))
       (candidate (if (equal (cdr actual) (list right left))
                      (proof-proof-symmetric (library-library-proof lib) candidate)
                    candidate))
       (actual (t4-algebra-first candidate)))
    (if (not (equal (cdr actual) (list left right)))
        (cons '(:failure "SearchMiss" "") lib)
      (t4-algebra-with-library lib
          ((reversed (proof-proof-symmetric (library-library-proof lib) (cadr sides))))
        (cons (proof-proof-chain (library-library-proof lib) (car sides)
                                 (list candidate reversed))
              lib)))))

(defun t4-algebra-orient-normalized (lib step goal premises)
  (t4-algebra-public-result
   (t4-algebra-orient-normalized-with-replies lib step goal premises nil)))

(defun t4-algebra-with-fixed-operand (lib head arg index result equality replies)
  (t4-algebra-with-library lib
      ((current (t4-algebra-side result 2))
       (fix-eq (if (assoc-equal head *t4-algebra-operations*)
                   (t4-algebra-with-library lib
                       ((other (t4-algebra-operand-indices (cdr current) (list (- 2 index)))))
                     (t4-algebra-binary-fix-with-replies lib head arg other index replies))
                 (t4-algebra-unary-fix-with-replies lib head arg replies))
               :library)
       (inverse (proof-proof-symmetric (library-library-proof lib) fix-eq))
       (result (proof-proof-chain (library-library-proof lib) result (list inverse))))
    (cons (proof-proof-rewrite (library-library-proof lib) result equality (list 1 2 index))
          lib)))

(mutual-recursion
 (defun t4-algebra-replace-fixed-visit (n lib term equality replies)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       (cons '(:failure "Fuel" "t4-algebra-replace-fixed-visit") lib)
     (t4-algebra-with-library lib ((left (t4-algebra-side equality 1)))
       (if (equal term left)
           (cons equality lib)
         (t4-algebra-with-library lib
             ((result (proof-proof-reflexive (library-library-proof lib) term)))
           (if (or (not (proof-compound term)) (proof-is-call term *proof-quote*))
               (cons result lib)
             (t4-algebra-with-library lib
                 ((head (proof-term-at term 0))
                  (raw (if (proof-is-call left *t4-algebra-fix*)
                           (proof-term-at left 1)
                         :none))
                  (result (t4-algebra-replace-fixed-arguments
                           (1- n) lib (cdr term) head raw 1 result equality replies) :library))
               (cons (proof-proof-tidy (library-library-proof lib) result) lib))))))))

 (defun t4-algebra-replace-fixed-arguments (n lib args head raw index result equality replies)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n)))
     (cons '(:failure "Fuel" "t4-algebra-replace-fixed-arguments") lib))
    ((endp args) (cons result lib))
    (t
     (let ((arg (car args)))
       (t4-algebra-with-library lib
           ((result
             (if (and (equal arg raw)
                      (or (assoc-equal head *t4-algebra-operations*)
                          (member-equal head (list *proof-minus* *t4-algebra-reciprocal*))))
                 (t4-algebra-with-fixed-operand lib head arg index result equality replies)
               (t4-algebra-with-library lib
                   ((change (t4-algebra-replace-fixed-visit (1- n) lib arg equality replies)
                            :library)
                    (left (t4-algebra-side change 1))
                    (right (t4-algebra-side change 2)))
                 (cons (if (equal left right)
                           result
                         (proof-proof-rewrite (library-library-proof lib) result change
                                              (list 1 2 index)))
                       lib)))
             :library))
         (t4-algebra-replace-fixed-arguments (1- n) lib (cdr args) head raw (1+ index)
                                             result equality replies)))))))

(defun t4-algebra-replace-fixed-with-replies (lib term equality replies)
  (t4-algebra-replace-fixed-visit 1000000 lib term equality replies))

(defun t4-algebra-replace-fixed (lib term equality)
  (t4-algebra-public-result (t4-algebra-replace-fixed-with-replies lib term equality nil)))

(defun t4-algebra-replace-sides (lib parts equality replies)
  (if (endp parts)
      (cons '(:failure "SearchMiss" "") lib)
    (t4-algebra-with-library lib
        ((left (t4-algebra-replace-fixed-with-replies lib (car parts) equality replies) :library))
      (if (endp (cdr parts))
          (cons '(:failure "SearchMiss" "") lib)
        (t4-algebra-with-library lib
            ((right (t4-algebra-replace-fixed-with-replies lib (cadr parts) equality replies)
                    :library))
          (if (endp (cddr parts))
              (cons (list left right) lib)
            (let ((third (t4-algebra-replace-fixed-with-replies lib (caddr parts) equality replies)))
              (if (t4-algebra-interrupted-p (car third))
                  third
                (cons '(:failure "SearchMiss" "") (cdr third))))))))))

(defun t4-algebra-normalize-endpoint (lib step premises replies)
  (t4-algebra-with-library lib
      ((end (t4-algebra-side step 2))
       (normalized (t4-algebra-normal-with-replies lib end premises replies) :library))
    (cons (proof-proof-chain (library-library-proof lib) step (list normalized)) lib)))

(defun t4-algebra-equal-from-fix-with-replies (lib proposition equality premises replies)
  (t4-algebra-with-library lib
      ((sides (t4-algebra-replace-sides lib (cdr proposition) equality replies) :library)
       (a (t4-algebra-normalize-endpoint lib (car sides) premises replies) :library)
       (b (t4-algebra-normalize-endpoint lib (cadr sides) premises replies) :library)
       (left (t4-algebra-side a 2))
       (right (t4-algebra-side b 2)))
    (if (not (equal left right))
        (cons '(:failure "SearchMiss" "") lib)
      (t4-algebra-with-library lib
          ((reverse (proof-proof-symmetric (library-library-proof lib) b)))
        (cons (proof-proof-chain (library-library-proof lib) a (list reverse)) lib)))))

(defun t4-algebra-equal-from-fix (lib proposition equality premises)
  (t4-algebra-public-result
   (t4-algebra-equal-from-fix-with-replies lib proposition equality premises nil)))

(defun t4-algebra-any-call-p (args head)
  (and (consp args)
       (or (proof-is-call (car args) head)
           (t4-algebra-any-call-p (cdr args) head))))

(defun t4-algebra-zero-or-call-p (term operator)
  (or (proof-is-call term operator) (equal term *proof-zero*)))

(defun t4-algebra-summand-transfers (summands)
  (if (endp summands)
      nil
    (cons (library-plus (library-minus (car summands)) *proof-result*)
          (t4-algebra-summand-transfers (cdr summands)))))

(defun t4-algebra-cancellation-candidates (left right factor)
  (if (not (eq factor :none))
      (list (list *proof-times* (list *t4-algebra-reciprocal* factor) *proof-result*))
    (append
     (if (and (t4-algebra-zero-or-call-p left *proof-minus*)
              (t4-algebra-zero-or-call-p right *proof-minus*))
         (list (library-minus *proof-result*))
       nil)
     (if (and (t4-algebra-zero-or-call-p left *t4-algebra-reciprocal*)
              (t4-algebra-zero-or-call-p right *t4-algebra-reciprocal*))
         (list (list *t4-algebra-reciprocal* *proof-result*))
       nil)
     (if (proof-is-call left *proof-plus*)
         (t4-algebra-summand-transfers (cdr left))
       nil)
     (if (proof-is-call right *proof-plus*)
         (t4-algebra-summand-transfers (cdr right))
       nil))))

(defun t4-algebra-cancellation-backward (lib first equalities premises replies)
  (declare (xargs :measure (acl2-count equalities)))
  (if (endp equalities)
      (cons nil lib)
    (let ((answer (t4-algebra-equal-from-fix-with-replies lib first (car equalities)
                                                        premises replies)))
      (if (t4-algebra-search-miss-p (car answer))
          (t4-algebra-cancellation-backward (cdr answer) first (cdr equalities) premises
                                           replies)
        answer))))

(defun t4-algebra-cancellation-transfer (lib first second transfer premises backward replies)
  (t4-algebra-with-library lib
      ((assumed (proof-proof-assume (library-library-proof lib) first t))
       (shifted (t4-algebra-under-operation lib assumed transfer))
       (forward (t4-algebra-orient-normalized-with-replies lib shifted second premises replies)
                :library))
    (cons (t4-algebra-equality-tests lib first second forward backward) lib)))

(defun t4-algebra-cancellation-forward (lib first second candidates premises backward replies)
  (declare (xargs :measure (acl2-count candidates)))
  (if (endp candidates)
      (cons nil lib)
    (let ((answer (t4-algebra-cancellation-transfer lib first second (car candidates)
                                                    premises backward replies)))
      (if (t4-algebra-search-miss-p (car answer))
          (t4-algebra-cancellation-forward (cdr answer) first second (cdr candidates)
                                           premises backward replies)
        answer))))

(defun t4-algebra-arithmetic-cancellation-with-replies (lib first second premises factor replies)
  (if (not (and (proof-is-call first *proof-equal*)
                (proof-is-call second *proof-equal*)
                (t4-algebra-any-call-p (cdr second) *t4-algebra-fix*)))
      (cons nil lib)
    (t4-algebra-with-library lib ((sides (proof-list-of-length (cdr first) 2)))
      (let ((candidates (t4-algebra-cancellation-candidates (car sides) (cadr sides) factor))
            (proof (library-library-proof lib)))
        (if (endp candidates)
            (cons nil lib)
          (t4-algebra-with-library lib
              ((source (proof-proof-assume proof second t))
               (reversed (proof-proof-symmetric proof source))
               (backward (t4-algebra-cancellation-backward lib first (list source reversed)
                                                          premises replies) :library))
            (if (not backward)
                (cons nil lib)
              (t4-algebra-cancellation-forward lib first second (proof-unique candidates)
                                               premises backward replies))))))))

(defun t4-algebra-arithmetic-cancellation (lib first second premises factor)
  (t4-algebra-public-result
   (t4-algebra-arithmetic-cancellation-with-replies lib first second premises factor nil)))

(defun t4-algebra-nonzero-fix (lib obj rejected)
  (let ((proof (library-library-proof lib))
        (typed (list *library-numberp* obj)))
    (proof-with-checked-results
        ((denied (proof-proof-assume proof typed nil))
         (opened (t4-algebra-fixed lib obj denied))
         (moved (proof-proof-rewrite proof rejected opened '(1 1 1)))
         (zero (proof-proof-reflexive proof *proof-zero*))
         (cut (proof-proof-cut proof zero moved))
         (number-case (proof-proof-front proof cut typed))
         (fixed (t4-algebra-fixed lib obj number-case))
         (missing-zero (proof-proof-rewrite proof rejected fixed '(1 1 1)))
         (missing-zero (proof-proof-tidy proof missing-zero)))
      (list number-case missing-zero))))

(defun t4-algebra-product-operand-p (sides obj)
  (and (consp sides)
       (or (and (proof-is-call (car sides) *proof-times*)
                (member-equal obj (cdar sides)))
           (t4-algebra-product-operand-p (cdr sides) obj))))

(defun t4-algebra-product-cancellation-shape (first second)
  (and (proof-is-call first *proof-equal*) (proof-is-call second *proof-if*)
    (proof-with-checked-results ((other (proof-term-at second 3)))
      (and (proof-is-call other *proof-equal*)
        (proof-with-checked-results ((test (proof-term-at second 1)))
          (and (proof-is-call test *proof-equal*) (member-equal *proof-zero* (cdr test))
            (proof-with-checked-results ((true-branch (proof-term-at second 2)))
              (and (or (equal true-branch *proof-true*) (equal true-branch test))
                (proof-with-checked-results
                    ((left (proof-term-at test 1))
                     (value (if (equal left *proof-zero*) (proof-term-at test 2) left)))
                  (and (proof-is-call value *t4-algebra-fix*)
                    (proof-with-checked-results ((obj (proof-term-at value 1)))
                      (and (t4-algebra-product-operand-p (cdr first) obj)
                        (list test value obj other (equal left *proof-zero*))))))))))))))

(defun t4-algebra-product-cancellation-denied (lib test value left-zero)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((denied (proof-proof-assume proof test nil)))
      (if (not left-zero)
          denied
        (let ((reverse (proof-eq value *proof-zero*)))
          (proof-with-checked-results
              ((reversed (proof-proof-assume proof reverse t))
               (reversed (proof-proof-symmetric proof reversed))
               (denied (proof-proof-cut proof reversed denied)))
            (proof-proof-front proof denied (proof-neg reverse))))))))

(defun t4-algebra-product-cancellation-result (lib first second shape replies)
  (let ((test (car shape))
        (value (cadr shape))
        (obj (caddr shape))
        (otherwise (cadddr shape))
        (left-zero (car (cddddr shape))))
    (t4-algebra-with-library lib
        ((known (proof-proof-assume (library-library-proof lib) test t))
         (right (proof-term-at test 2))
         (dropped (if (equal right *proof-zero*)
                      known
                    (proof-proof-symmetric (library-library-proof lib) known)))
         (opened (t4-algebra-replace-fixed-with-replies lib first dropped replies) :library)
         (opened (t4-algebra-normalize-endpoint lib opened nil replies) :library)
         (result (t4-algebra-side opened 2)))
      (if (not (equal result *proof-true*))
          (cons nil lib)
        (t4-algebra-with-library lib
            ((matches (proof-proof-select (library-library-proof lib) second known))
             (result (t4-algebra-side matches 2))
             (matches (if (equal result test)
                          (proof-with-checked-results ((truth (t4-algebra-value-of test lib known)))
                            (proof-proof-chain (library-library-proof lib) matches (list truth)))
                        matches))
             (reversed (proof-proof-symmetric (library-library-proof lib) matches))
             (yes (proof-proof-chain (library-library-proof lib) opened (list reversed)))
             (denied (t4-algebra-product-cancellation-denied lib test value left-zero))
             (premises (t4-algebra-nonzero-fix lib obj denied))
             (cancelled (t4-algebra-arithmetic-cancellation-with-replies
                         lib first otherwise premises obj replies) :library))
          (if (not cancelled)
              (cons nil lib)
            (let ((proof (library-library-proof lib)))
              (t4-algebra-with-library lib
                  ((branch (proof-proof-if-false proof second))
                   (branch (proof-proof-symmetric proof branch))
                   (no (proof-proof-rewrite proof cancelled branch '(1 2))))
                (cons (proof-proof-cases proof test yes no) lib)))))))))

(defun t4-algebra-product-cancellation-with-replies (lib first second replies)
  (t4-algebra-with-library lib
      ((shape (t4-algebra-product-cancellation-shape first second)))
    (if shape
        (t4-algebra-product-cancellation-result lib first second shape replies)
      (cons nil lib))))

(defun t4-algebra-product-cancellation (lib first second)
  (t4-algebra-public-result
   (t4-algebra-product-cancellation-with-replies lib first second nil)))

(defun t4-algebra-test-applicable-p (goal)
  (and (proof-is-call goal *proof-equal*)
    (proof-with-checked-results ((left (proof-term-at goal 1)))
      (and (proof-is-call left *proof-equal*)
           (t4-algebra-has-arithmetic goal)))))

(defun t4-algebra-arithmetic-test-proof (lib guard goal replies)
  (t4-algebra-with-library lib
      ((premises (t4-algebra-guard-premises lib guard))
       (sides (proof-list-of-length (cdr goal) 2))
       (step (t4-algebra-arithmetic-cancellation-with-replies lib (car sides) (cadr sides)
                                                             premises :none replies)
             :library)
       (step (if step
                 (cons step lib)
               (t4-algebra-product-cancellation-with-replies lib (car sides) (cadr sides) replies))
             :library))
    (cons (if (and step (t4-algebra-has-guard-p guard))
              (t4-division-imply lib guard step)
            step)
          lib)))

(defun t4-algebra-arithmetic-test-with-replies (lib formula replies)
  (t4-algebra-with-library lib
      ((parts (t4-algebra-formula-parts formula))
       (applicable (t4-algebra-test-applicable-p (cadr parts))))
    (if (not applicable)
        (cons nil lib)
      (let ((built (t4-algebra-query :arithmetic lib nil replies)))
        (if (t4-algebra-interrupted-p (car built))
            built
          (t4-algebra-arithmetic-test-proof (cdr built) (car parts) (cadr parts) replies))))))

(defun t4-algebra-arithmetic-test (lib formula)
  (t4-algebra-public-result (t4-algebra-arithmetic-test-with-replies lib formula nil)))
