(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-term-trees-type-term* '("sym" "ACL2" "TERM-LIST-TO-TYPE-TERM"))

(defconst *b2-term-trees-tree-openers*
  '(("sym" "ACL2" "BINARY-OP_TREE-OPENER")
    ("sym" "ACL2" "BINARY-OP_TREE-SIMPLE-OPENER")))

(defconst *b2-term-trees-tree-types*
  '(("sym" "ACL2" "PSEUDO-TERM-LISTP-BINARY-OP_FRINGE")
    ("sym" "ACL2" "PSEUDO-TERMP-TERM-LIST-TO-TYPE-TERM")
    ("sym" "ACL2" "PSUEDO-TERMP-BINARY-OP_TREE")))

(defmacro b2-term-trees-solve (lib goal evidence unfold)
  `(b2-tactics-tactics-solve ,lib ,goal ,evidence ,unfold nil 0 nil))

(defmacro b2-term-trees-use-fact (lib name goal evidence)
  `(b2-tactics-tactics-use-fact ,lib ,name ,goal ,evidence nil nil 0 nil))

(defun b2-term-trees-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b2-term-trees-evidence-at (known term)
  (let ((entry (assoc-equal term known)))
    (if entry
        (cdr entry)
      '(:failure "tactic-rejected" ""))))

(defun b2-term-trees-tree-opener-positive (lib successor sequence cons-step call head)
  (if (equal head *b2-meta-fold-tree*)
      (let ((test (list *proof-consp* (list *library-cdr* sequence)))
            (proof (library-library-proof lib)))
        (proof-with-checked-results
            ((signs (b2-bags-signed lib test))
             (yes (b2-term-trees-solve lib successor
                                      (list cons-step (car signs)) (list call)))
             (no (b2-term-trees-solve lib successor
                                     (list cons-step (cadr signs)) (list call))))
          (proof-proof-cases proof test yes no)))
    (b2-term-trees-solve lib successor (list cons-step) (list call))))

(defun b2-term-trees-tree-opener (lib formula)
  (if (integerp formula)
      '(:failure "tactic-rejected" "")
    (proof-with-checked-results
        ((parts (proof-list-of-length (seq-slice formula 1 3) 2))
         (base (proof-list-of-length (car parts) 3))
         (absence-argument (proof-term-at (cadr base) 1))
         (sequence (proof-term-at absence-argument 1)))
      (let ((absence (cadr base))
            (equation (caddr base))
            (successor (cadr parts))
            (proof (library-library-proof lib)))
        (proof-with-checked-results
            ((request (b2-tactics-tactics-implication lib absence equation nil))
             (left (proof-term-at equation 1))
             (established (b2-term-trees-solve lib equation
                            (list (cadddr (car request))) (list left)))
             (empty (b2-tactics-tactics-implication lib absence equation
                                                   (cons established lib))))
          (let ((test (list *proof-consp* sequence)))
            (proof-with-checked-results
                ((signs (b2-bags-signed lib test))
                 (call (proof-term-at successor 1))
                 (head (proof-term-at call 0))
                 (positive (b2-term-trees-tree-opener-positive
                            lib successor sequence (car signs) call head))
                 (negative (b2-term-trees-solve
                            lib successor (list (cadr signs)) (list call)))
                 (constructed (proof-proof-cases proof test positive negative)))
              (b2-term-trees-solve lib formula (list (car empty) constructed) nil))))))))

(defun b2-term-trees-typed-list-add (lib arguments result)
  (declare (xargs :measure (len arguments)))
  (if (not (o< (len (cdr arguments)) (len arguments)))
      result
    (let ((typed (car arguments))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((element (b2-term-trees-step-at typed 1))
           (tail (b2-term-trees-step-at result 1)))
        (let* ((list-term (list *proof-cons* element tail))
               (node (list *b2-list-properties-pseudo-list* list-term)))
          (proof-with-checked-results
              ((typed-node (b2-term-trees-solve lib node (list typed result) (list node)))
               (value (b2-tactics-tactics-normalize lib list-term nil nil nil 1500 nil))
               (next (if value
                         (proof-with-checked-results
                             ((rewritten (proof-proof-rewrite proof typed-node value '(1 1))))
                           (proof-proof-tidy proof rewritten))
                       typed-node)))
            (b2-term-trees-typed-list-add lib (cdr arguments) next)))))))

(defun b2-term-trees-typed-list (lib arguments)
  (proof-with-checked-results
      ((empty (b2-term-trees-solve lib
                (list *b2-list-properties-pseudo-list* *proof-false*)
                nil (list *b2-list-properties-pseudo-list*))))
    (b2-term-trees-typed-list-add lib (reverse arguments) empty)))

(defun b2-term-trees-application (lib function arguments evidence)
  (proof-with-checked-results
      ((types (b2-term-trees-typed-list lib arguments))
       (args (b2-term-trees-step-at types 1)))
    (let ((term (list *b2-association-pseudo-term* (list *proof-cons* function args)))
          (same (proof-eq function (proof-quote *proof-quote*)))
          (proof (library-library-proof lib)))
      (proof-with-checked-results ((known (b2-tactics-tactics-evidence lib evidence)))
        (if (or (assoc-equal (proof-neg same) known) (not (equal (len arguments) 1)))
            (b2-term-trees-solve lib term (append evidence (list types)) (list term))
          (proof-with-checked-results
              ((signs (b2-bags-signed lib same))
               (yes (b2-term-trees-solve lib term
                                       (append evidence (list (car signs))) (list term)))
               (no (b2-term-trees-solve lib term
                                      (append evidence (list types (cadr signs))) (list term))))
            (proof-proof-cases proof same yes no)))))))

(defun b2-term-trees-argument-types (lib sequence-type term)
  (proof-with-checked-results
      ((tail (b2-term-trees-use-fact lib *b2-pseudo-terms-list-cdr*
               (list *b2-list-properties-pseudo-list* (list *library-cdr* term))
               (list sequence-type)))
       (head (b2-term-trees-use-fact lib *b2-pseudo-terms-term-car*
               (list *b2-association-pseudo-term* (list *library-car* term))
               (list sequence-type))))
    (list head tail)))

(defun b2-term-trees-list-tree-type-base-finish (premise lib atom-step goal call seq is-type-term)
  (proof-with-checked-results
      ((known (b2-tactics-tactics-evidence lib (list premise))))
    (let ((evidence (table-values known))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((evidence
            (if is-type-term
                (proof-with-checked-results
                    ((expanded (b2-tactics-tactics-evidence lib evidence))
                     (typed (b2-term-trees-evidence-at
                             expanded (list *b2-list-properties-pseudo-list* seq)))
                     (literal (proof-step-first typed))
                     (equation (b2-tactics-tactics-normalize
                                lib literal (list atom-step) (list literal) nil 1500 nil))
                     (rewritten (if equation
                                    (proof-proof-rewrite proof typed equation '(1))
                                  '(:failure "failure" "")))
                     (new-type (proof-proof-tidy proof rewritten)))
                  (append evidence (list new-type)))
              evidence)))
        (b2-term-trees-solve lib goal (append evidence (list atom-step))
                             (list call *b2-association-pseudo-term*))))))

(defun b2-term-trees-list-tree-type-base (atom-step lib condition goal call seq is-type-term)
  (proof-with-checked-results
      ((request (b2-tactics-tactics-implication lib condition goal nil))
       (step (b2-term-trees-list-tree-type-base-finish
              (cadddr (car request)) lib atom-step goal call seq is-type-term))
       (reply (b2-tactics-tactics-implication lib condition goal (cons step lib))))
    (car reply)))

(defun b2-term-trees-list-tree-type-advance-finish-attach (typed facts lib goal evidence call)
  (b2-term-trees-solve lib goal (append evidence facts (list typed)) (list call)))

(defun b2-term-trees-advance-type-term (lib goal call seq remaining cons-step head subtree evidence)
  (let ((atom-tail (proof-eq remaining *proof-false*))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((nonempty (b2-tactics-tactics-from-impossible
                    lib (proof-neg (proof-eq seq *proof-false*)) cons-step nil nil nil 1500 nil))
         (evidence (append evidence (list nonempty)))
         (signs (b2-bags-signed lib atom-tail))
         (function (proof-term-at call 1))
         (singleton (b2-term-trees-application lib function (list head) evidence))
         (quoted (b2-term-trees-solve lib
                   (list *b2-association-pseudo-term*
                         (proof-quote (list *proof-quote* *proof-nil*)))
                   nil (list *b2-association-pseudo-term*)))
         (node (b2-term-trees-application lib (proof-quote *proof-if*)
                 (list singleton subtree quoted) nil))
         (yes (b2-term-trees-list-tree-type-advance-finish-attach
                singleton (list (car signs)) lib goal evidence call))
         (no (b2-term-trees-list-tree-type-advance-finish-attach
               node (list (cadr signs)) lib goal evidence call)))
      (proof-proof-cases proof atom-tail yes no))))

(defun b2-term-trees-advance-binary-tree (lib goal call remaining head tail subtree evidence)
  (let ((test (list *proof-consp* remaining))
        (test-two (list *proof-consp* (list *library-cdr* remaining)))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((signs (b2-bags-signed lib test))
         (fixer (proof-term-at call 3))
         (singleton (b2-term-trees-application lib fixer (list head) evidence))
         (two-signs (b2-bags-signed lib test-two))
         (second-types (b2-term-trees-argument-types lib tail remaining))
         (function (proof-term-at call 1))
         (stop (b2-term-trees-application lib function (list head (car second-types)) evidence))
         (recur (b2-term-trees-application lib function (list head subtree) evidence))
         (longer (b2-term-trees-list-tree-type-advance-finish-attach
                   recur (list (car signs) (car two-signs)) lib goal evidence call))
         (exactly-two (b2-term-trees-list-tree-type-advance-finish-attach
                       stop (list (car signs) (cadr two-signs)) lib goal evidence call))
         (more (proof-proof-cases proof test-two longer exactly-two))
         (single (b2-term-trees-list-tree-type-advance-finish-attach
                   singleton (list (cadr signs)) lib goal evidence call)))
      (proof-proof-cases proof test more single))))

(defun b2-term-trees-list-tree-type-advance-finish
    (premise lib cons-step induction goal call seq remaining is-type-term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((known (b2-tactics-tactics-evidence lib (list premise)))
         (typed (b2-term-trees-evidence-at known (list *b2-list-properties-pseudo-list* seq)))
         (parts (b2-term-trees-argument-types lib typed seq))
         (evidence (cons cons-step (table-values known)))
         (hypothesis (b2-term-trees-step-at induction 1))
         (guard-step (b2-term-trees-solve lib hypothesis
                       (append evidence (list (cadr parts))) nil))
         (subtree (proof-proof-modus-ponens proof induction guard-step)))
      (if is-type-term
          (b2-term-trees-advance-type-term
           lib goal call seq remaining cons-step (car parts) subtree evidence)
        (b2-term-trees-advance-binary-tree
         lib goal call remaining (car parts) (cadr parts) subtree evidence)))))

(defun b2-term-trees-list-tree-type-advance
    (cons-step induction lib condition goal call seq remaining is-type-term)
  (proof-with-checked-results
      ((request (b2-tactics-tactics-implication lib condition goal nil))
       (step (b2-term-trees-list-tree-type-advance-finish
              (cadddr (car request)) lib cons-step induction goal call seq remaining is-type-term))
       (reply (b2-tactics-tactics-implication lib condition goal (cons step lib))))
    (car reply)))

(defun b2-term-trees-list-tree-type (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (call (proof-term-at (caddr parts) 1))
       (seq (proof-term-at call (1- (len call))))
       (head (proof-term-at call 0)))
    (let ((condition (cadr parts))
          (goal (caddr parts))
          (remaining (list *library-cdr* seq))
          (is-type-term (equal head *b2-term-trees-type-term*)))
      (proof-with-checked-results
          ((advance-request (b2-tactics-tactics-on-list lib formula seq nil nil nil))
           (advance (b2-term-trees-list-tree-type-advance
                     (cadddr (car advance-request)) (nth 4 (car advance-request))
                     lib condition goal call seq remaining is-type-term))
           (base-request (b2-tactics-tactics-on-list lib formula seq nil (cons advance lib) nil))
           (base (b2-term-trees-list-tree-type-base
                  (cadddr (car base-request)) lib condition goal call seq is-type-term))
           (result (b2-tactics-tactics-on-list
                    lib formula seq (cons base lib) (cons advance lib) nil)))
        (car result)))))

(defun b2-term-trees-fringe-hypotheses (lib formula measure cons-step children bindings)
  (declare (xargs :measure (len children)))
  (if (or (not (o< (len (cdr children)) (len children))) (endp bindings))
      nil
    (let ((goal (list *proof-ordinal-less* (list *library-count* (car children)) measure)))
      (proof-with-checked-results
          ((rulers (b2-measures-rulers-init lib (list cons-step)))
           (decrease (b2-measures-rulers-selector-decrease lib goal rulers))
           (hypothesis (b2-tactics-tactics-induction-hypothesis
                        lib formula measure (car bindings) (car decrease)))
           (rest (b2-term-trees-fringe-hypotheses
                  lib formula measure cons-step (cdr children) (cdr bindings))))
        (cons hypothesis rest)))))

(defun b2-term-trees-fringe-values (lib facts children hypotheses rules)
  (declare (xargs :measure (len children)))
  (if (or (not (o< (len (cdr children)) (len children)))
          (endp hypotheses) (endp rules))
      nil
    (let ((proof (library-library-proof lib))
          (hypothesis (car hypotheses)))
      (proof-with-checked-results
          ((child-type (b2-term-trees-use-fact lib (car rules)
                        (list *b2-association-pseudo-term* (car children)) facts))
           (target (b2-term-trees-step-at hypothesis 1))
           (guard-step (b2-term-trees-solve lib target (append facts (list child-type)) nil))
           (value (proof-proof-modus-ponens proof hypothesis guard-step))
           (rest (b2-term-trees-fringe-values
                  lib facts (cdr children) (cdr hypotheses) (cdr rules))))
        (cons value rest)))))

(defun b2-term-trees-fringe-type-finish
    (premise lib goal call term operation test same signs matches children hypotheses)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((known (b2-tactics-tactics-evidence lib (list premise)))
         (typed (b2-term-trees-evidence-at known (list *b2-association-pseudo-term* term)))
         (singleton (b2-term-trees-typed-list lib (list typed)))
         (wrong (b2-term-trees-solve lib goal
                  (list (car signs) (cadr matches) singleton) (list call)))
         (empty (b2-term-trees-solve lib goal (list (cadr signs) singleton) (list call)))
         (fact (b2-term-trees-evidence-at known (proof-neg (proof-eq operation (proof-quote *proof-quote*)))))
         (reverse-match (proof-proof-symmetric proof (car matches)))
         (rewritten (proof-proof-rewrite proof fact reverse-match '(1 1 1)))
         (head-nonquote (proof-proof-tidy proof rewritten))
         (tail-type (b2-term-trees-use-fact lib (proof-sym "PSEUDO-TERM-LISTP-CDR" "ACL2")
                      (list *b2-list-properties-pseudo-list* (list *library-cdr* term))
                      (list typed head-nonquote)))
         (facts (append (table-values known) (list tail-type)))
         (values (b2-term-trees-fringe-values lib facts children hypotheses
                   (list *b2-pseudo-terms-term-car*
                         (proof-sym "PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP" "ACL2"))))
         (left (b2-term-trees-step-at (car values) 1))
         (right (b2-term-trees-step-at (cadr values) 1))
         (joined (b2-term-trees-use-fact lib (proof-sym "PSEUDO-TERM-LISTP-APPEND" "ACL2")
                   (list *b2-list-properties-pseudo-list* (list *b2-bags-append* left right)) values))
         (valid (b2-term-trees-solve lib goal (list (car signs) (car matches) joined) (list call)))
         (cons-result (proof-proof-cases proof same valid wrong)))
      (proof-proof-cases proof test cons-result empty))))

(defun b2-term-trees-fringe-type (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (application (proof-term-at (caddr parts) 1))
       (call (proof-list-of-length application 3)))
    (let* ((condition (cadr parts))
           (goal (caddr parts))
           (operation (cadr call))
           (term (caddr call))
           (test (list *proof-consp* term))
           (same (proof-eq (list *library-car* term) operation))
           (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((signs (b2-bags-signed lib test))
           (matches (b2-bags-signed lib same)))
        (let* ((measure (list *library-count* term))
               (children (list (b2-tactics-field term 1) (b2-tactics-field term 2)))
               (bindings (list (list (list term (car children)))
                               (list (list term (cadr children))))))
          (proof-with-checked-results
              ((hypotheses (b2-term-trees-fringe-hypotheses
                            lib formula measure (car signs) children bindings))
               (request (b2-tactics-tactics-implication lib condition goal nil))
               (finish (b2-term-trees-fringe-type-finish
                        (cadddr (car request)) lib goal call term operation
                        test same signs matches children hypotheses))
               (result (b2-tactics-tactics-implication lib condition goal (cons finish lib)))
               (ordinal (library-library-builtin lib 1 term)))
            (proof-proof-induct proof ordinal (car result) formula measure bindings)))))))

(defun b2-term-trees-prove-tree (lib name formula)
  (if (member-equal name *b2-term-trees-tree-openers*)
      (b2-term-trees-tree-opener lib formula)
    (proof-with-checked-results
        ((goal (proof-term-at formula 2))
         (call (proof-term-at goal 1))
         (head (proof-term-at call 0)))
      (if (equal head *b2-bags-fringe*)
          (b2-term-trees-fringe-type lib formula)
        (b2-term-trees-list-tree-type lib formula)))))
