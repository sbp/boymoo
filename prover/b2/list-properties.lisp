(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-list-properties-true-list* '("sym" "ACL2" "TRUE-LISTP"))
(defconst *b2-list-properties-pseudo-list* '("sym" "ACL2" "PSEUDO-TERM-LISTP"))
(defconst *b2-list-properties-symbol-list* '("sym" "ACL2" "SYMBOL-LISTP"))
(defconst *b2-list-properties-character-list* '("sym" "ACL2" "CHARACTER-LISTP"))
(defconst *b2-list-properties-strings* '("sym" "ACL2" "STRING-LISTP"))
(defconst *b2-list-properties-recognizers*
  (list *b2-list-properties-character-list* *b2-list-properties-pseudo-list*
        *b2-list-properties-strings* *b2-list-properties-symbol-list*
        *b2-list-properties-true-list*))

(defun b2-list-properties-selector-evidence-derived (lib known remaining predicates)
  (if (endp remaining)
      nil
    (let ((literal (caar remaining)))
      (proof-with-checked-results
          ((head (and (proof-compound literal) (proof-term-at literal 0)))
           (arg (and (proof-compound literal) (member-equal head predicates)
                     (proof-term-at literal 1)))
           (cons-step (and (proof-compound literal) (member-equal head predicates)
                           (cdr (assoc-equal (list *proof-consp* arg) known))))
           (equation (and cons-step
                          (b2-tactics-tactics-normalize
                           lib literal (list cons-step) (list literal) nil 1500 nil)))
           (rewritten (and equation
                           (proof-proof-rewrite
                            (library-library-proof lib) (cdar remaining)
                            equation '(1))))
           (derived (and rewritten
                         (proof-proof-tidy (library-library-proof lib) rewritten)))
           (rest (b2-list-properties-selector-evidence-derived
                  lib known (cdr remaining) predicates)))
        (if derived (cons derived rest) rest)))))

(defun b2-list-properties-selector-evidence (lib evidence predicates)
  (proof-with-checked-results
      ((known (b2-tactics-tactics-evidence lib evidence))
       (derived (b2-list-properties-selector-evidence-derived
                 lib known known predicates))
       (all (b2-tactics-tactics-evidence lib (append evidence derived))))
    (table-values all)))

(defun b2-list-properties-argument-at (arguments position)
  (let ((index (if (< position 0) (+ (len arguments) position) position)))
    (if (< index 0)
        '(:failure "tactic-rejected" "")
      (proof-term-at arguments index))))

(defun b2-list-properties-variables-p (arguments)
  (or (endp arguments)
      (and (b2-tactics-variable (car arguments))
           (b2-list-properties-variables-p (cdr arguments)))))

(defun b2-list-properties-recognizer-p (head definitions)
  (and (assoc-equal head definitions)
       (proof-with-checked-results ((name (proof-term-at head 2)))
         (if (stringp name)
             (text-ends-with name "P")
           '(:failure "failure" "")))))

(defun b2-list-properties-preservation-plan-predicates
    (guards definitions arguments predicates)
  (if (endp guards)
      predicates
    (let ((clause (car guards)))
      (proof-with-checked-results
          ((recognizer (and (proof-compound clause) (equal (len clause) 2)
                            (b2-list-properties-recognizer-p (car clause) definitions))))
        (b2-list-properties-preservation-plan-predicates
         (cdr guards) definitions arguments
         (if (and recognizer (member-equal (cadr clause) arguments)
                  (not (member-equal (car clause) predicates)))
             (cons (car clause) predicates)
           predicates))))))

(defun b2-list-properties-preservation-plan-guarded-argument-p (predicate arguments guards)
  (and (consp arguments)
       (or (member-equal (list predicate (car arguments)) guards)
           (b2-list-properties-preservation-plan-guarded-argument-p
            predicate (cdr arguments) guards))))

(defun b2-list-properties-preservation-plan-guarded-p (predicates arguments guards)
  (and (consp predicates)
       (or (b2-list-properties-preservation-plan-guarded-argument-p
            (car predicates) arguments guards)
           (b2-list-properties-preservation-plan-guarded-p
            (cdr predicates) arguments guards))))

(defun b2-list-properties-dump-string (string)
  (concatenate 'string "\""
               (text-replace (text-replace string "\\" "\\\\") "\"" "\\\"")
               "\""))

(defun b2-list-properties-preservation-plan-predicate-keys (predicates)
  (if (endp predicates)
      nil
    (let ((predicate (car predicates)))
      (cons (list (b2-list-properties-dump-string (car predicate))
                  (b2-list-properties-dump-string (cadr predicate))
                  (b2-list-properties-dump-string (caddr predicate))
                  predicate)
            (b2-list-properties-preservation-plan-predicate-keys (cdr predicates))))))

(defun b2-list-properties-preservation-plan-sorted-predicates (entries)
  (if (endp entries)
      nil
    (cons (cadddr (car entries))
          (b2-list-properties-preservation-plan-sorted-predicates (cdr entries)))))

(defun b2-list-properties-preservation-plan-select (condition predicate call definitions)
  (let ((arguments (cdr call))
        (definition (cdr (assoc-equal (car call) definitions))))
    (if (or (not (b2-list-properties-variables-p arguments))
            (not (equal (len (proof-unique arguments)) (len arguments))))
        nil
      (proof-with-checked-results
          ((pair (proof-list-of-length definition 2))
           (size (b2-search-size (cadr pair) 95)))
        (if (>= size 95)
            nil
          (let ((definitions-for-call (list (cons (car call) pair))))
            (proof-with-checked-results
                ((calls (termination-recursive-calls *termination-all* definitions-for-call)))
              (if (or (endp calls) (> (len calls) 3))
                  nil
                (proof-with-checked-results
                    ((selected (termination-selector-plan definitions-for-call calls)))
                  (if (endp selected)
                      nil
                    (proof-with-checked-results
                        ((guards (b2-search-guards condition))
                         (predicates (b2-list-properties-preservation-plan-predicates
                                      guards definitions arguments (list predicate))))
                      (and (b2-list-properties-preservation-plan-guarded-p
                            predicates arguments guards)
                           (let ((position (seq-index (car pair)
                                                     (cdr (assoc-equal (car call)
                                                                       selected)))))
                             (if (failure-p position)
                                 '(:failure "inapplicable" "")
                               (list position
                                     (b2-list-properties-preservation-plan-sorted-predicates
                                      (seq-sorted
                                       (b2-list-properties-preservation-plan-predicate-keys
                                        predicates))))))))))))))))))

(defun b2-list-properties-preservation-plan (lib formula)
  (if (not (proof-is-call formula *library-implies*))
      nil
    (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2)))
      (let* ((condition (car parts))
             (result (cadr parts))
             (definitions (proof-proof-definitions (library-library-proof lib))))
        (proof-with-checked-results
            ((recognizer (and (proof-compound result) (equal (len result) 2)
                              (b2-list-properties-recognizer-p
                               (car result) definitions))))
          (and recognizer
            (let ((call (cadr result)))
              (proof-with-checked-results
                  ((head (and (proof-compound call) (proof-term-at call 0))))
                (and (proof-compound call) (assoc-equal head definitions)
                     (b2-list-properties-preservation-plan-select
                      condition (car result) call definitions))))))))))

(defun b2-list-properties-step-argument (step index)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun b2-list-properties-preserve-list-consequent-leaf-bind (arguments actuals)
  (if (or (endp arguments) (endp actuals))
      nil
    (if (equal (car arguments) (car actuals))
        (b2-list-properties-preserve-list-consequent-leaf-bind (cdr arguments) (cdr actuals))
      (cons (list (car arguments) (car actuals))
            (b2-list-properties-preserve-list-consequent-leaf-bind
             (cdr arguments) (cdr actuals))))))

(defun b2-list-properties-preserve-list-consequent-leaf-rule (proof rules goal)
  (if (endp rules)
      nil
    (let* ((name (car rules))
           (facts (proof-proof-facts proof))
           (entry (assoc-equal name facts)))
      (proof-with-checked-results
          ((claim (if entry
                      (proof-term-at (cdr entry) 0)
                    '(:failure "tactic-rejected" "")))
           (implies-p (proof-is-call claim *library-implies*))
           (target (if implies-p (proof-term-at claim 2) claim))
           (bindings (b2-tactics-match target goal nil)))
        (if (car bindings)
            (proof-with-checked-results
                ((step (proof-proof-fact proof name (table-items (cdr bindings)))))
              (cons step implies-p))
          (b2-list-properties-preserve-list-consequent-leaf-rule proof (cdr rules) goal))))))

(defun b2-list-properties-preserve-list-consequent-leaf-reduction
    (lib goal predicate term evidence)
  (proof-with-checked-results
      ((special (and (proof-is-call goal predicate)
                     (or (proof-is-call term *proof-cons*) (proof-is-call term *proof-quote*))
                     (b2-tactics-tactics-normalize lib goal evidence (list goal) nil 1500 t)))
       (special-result (and special (b2-list-properties-step-argument special 2))))
    (if (and special (not (equal special-result goal)))
        (cons special special-result)
      (proof-with-checked-results
          ((equation (b2-tactics-tactics-normalize lib goal evidence nil nil 1500 nil))
           (result (and equation (b2-list-properties-step-argument equation 2))))
        (and equation (not (equal result goal)) (cons equation result))))))

; Progress records the substitutions, selector hypotheses, and proof search.
(defun b2-list-properties-preserve-list-consequent-leaf-prove
    (n goal lib formula position rules predicate call arguments measure known progress)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "b2-list-properties-preserve-list-consequent-leaf-prove")
    (let ((established (assoc-equal goal known))
          (proof (library-library-proof lib)))
      (if established
          (cons (cdr established) progress)
        (proof-with-checked-results
            ((otherwise (and (proof-is-call goal *proof-if*) (proof-term-at goal 3))))
          (if (and (proof-is-call goal *proof-if*) (equal otherwise *proof-false*))
              (proof-with-checked-results
                  ((test (b2-list-properties-preserve-list-consequent-leaf-prove
                          (1- n) (cadr goal) lib formula position rules predicate call
                          arguments measure known progress))
                   (yes (b2-list-properties-preserve-list-consequent-leaf-prove
                         (1- n) (caddr goal) lib formula position rules predicate call
                         arguments measure known (cdr test)))
                   (equation (proof-proof-select proof goal (car test)))
                   (step (proof-proof-transport proof (car yes) equation)))
                (cons step (cdr yes)))
            (proof-with-checked-results
                ((term (and (proof-is-call goal predicate) (proof-term-at goal 1))))
              (if (and (proof-is-call goal predicate) (proof-is-call term (car call)))
                  (let* ((actuals (cdr term))
                         (binding (b2-list-properties-preserve-list-consequent-leaf-bind
                                   arguments actuals))
                         (substitutions (car progress))
                         (substitutions (if (member-equal binding substitutions)
                                            substitutions
                                          (append substitutions (list binding)))))
                    (proof-with-checked-results
                        ((arg (b2-list-properties-argument-at actuals position))
                         (smaller (list *proof-ordinal-less* (list *library-count* arg) measure))
                         (descent (b2-measures-rulers-selector-decrease
                                   lib smaller (cadr progress)))
                         (rec (b2-tactics-tactics-induction-hypothesis
                               lib formula measure binding (car descent)))
                         (premise (b2-list-properties-step-argument rec 1))
                         (established (b2-list-properties-preserve-list-consequent-leaf-prove
                                       (1- n) premise lib formula position rules predicate call
                                       arguments measure known
                                       (list substitutions (cdr descent) (caddr progress))))
                         (step (proof-proof-modus-ponens proof rec (car established))))
                      (cons step (cdr established))))
                (proof-with-checked-results
                    ((rule (b2-list-properties-preserve-list-consequent-leaf-rule
                            proof rules goal)))
                  (if rule
                      (if (cdr rule)
                          (proof-with-checked-results
                              ((premise (b2-list-properties-step-argument (car rule) 1))
                               (established (b2-list-properties-preserve-list-consequent-leaf-prove
                                             (1- n) premise lib formula position rules predicate
                                             call arguments measure known progress))
                               (step (proof-proof-modus-ponens proof (car rule) (car established))))
                            (cons step (cdr established)))
                        (cons (car rule) progress))
                    (let ((evidence (table-values known))
                          (search (caddr progress)))
                      (proof-with-checked-results
                          ((reduction (b2-list-properties-preserve-list-consequent-leaf-reduction
                                       lib goal predicate term evidence)))
                        (cond
                         (reduction
                          (proof-with-checked-results
                              ((established (b2-list-properties-preserve-list-consequent-leaf-prove
                                             (1- n) (cdr reduction) lib formula position rules
                                             predicate call arguments measure known progress))
                               (step (proof-proof-transport proof (car established) (car reduction))))
                            (cons step (cdr established))))
                         (search
                          (proof-with-checked-results
                              ((found (b2-search-search-prove search goal evidence 2 1))
                               (step (car found)))
                            (list step (car progress) (cadr progress) (cdr found))))
                         (t
                          (proof-with-checked-results
                              ((step (b2-tactics-tactics-solve lib goal evidence nil nil 0 nil)))
                            (cons step progress))))))))))))))))

(defun b2-list-properties-preserve-list-consequent-leaf-assumptions (proof signed)
  (if (endp signed)
      nil
    (proof-with-checked-results
        ((assumption (proof-proof-assume proof (caar signed) (cadar signed)))
         (rest (b2-list-properties-preserve-list-consequent-leaf-assumptions
                proof (cdr signed))))
      (cons assumption rest))))

(defun b2-list-properties-preserve-list-consequent-leaf-known (steps known)
  (if (endp steps)
      known
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (b2-list-properties-preserve-list-consequent-leaf-known
       (cdr steps) (table-put known literal (car steps))))))

(defun b2-list-properties-preserve-list-consequent-leaf
    (value signed lib premise formula position rules predicates predicate call
           arguments measure substitutions search)
  (proof-with-checked-results
      ((assumptions (b2-list-properties-preserve-list-consequent-leaf-assumptions
                     (library-library-proof lib) signed))
       (evidence (b2-list-properties-selector-evidence lib (cons premise assumptions) predicates))
       (known (b2-list-properties-preserve-list-consequent-leaf-known evidence nil))
       (rulers (b2-measures-rulers-init lib (table-values known)))
       (result (b2-list-properties-preserve-list-consequent-leaf-prove
                1000000 (list predicate value) lib formula position rules predicate
                call arguments measure known (list substitutions rulers search))))
    (list (car result) (cadr result) (cadddr result))))

(defun b2-list-properties-preserve-list-consequent-visit
    (n lib value template signed premise formula position rules predicates predicate
       call arguments measure substitutions search)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n)))
      '(:failure "fuel" "b2-list-properties-preserve-list-consequent-visit"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (yes (b2-list-properties-preserve-list-consequent-visit
                 (1- n) lib (cadr branches) template (append signed (list (list (car branches) t)))
                 premise formula position rules predicates predicate call arguments measure
                 substitutions search))
           (no (b2-list-properties-preserve-list-consequent-visit
                (1- n) lib (caddr branches) template (append signed (list (list (car branches) nil)))
                premise formula position rules predicates predicate call arguments measure
                (cadr yes) (caddr yes)))
           (step (proof-by-value-join proof value template (car yes) (car no))))
        (cons step (cdr no))))
     ((null value) '(:failure "tactic-rejected" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (body (b2-list-properties-step-argument equality 2))
           (opened (b2-list-properties-preserve-list-consequent-visit
                    (1- n) lib body template signed premise formula position rules
                    predicates predicate call arguments measure substitutions search))
           (reverse (proof-proof-symmetric proof equality))
           (step (proof-proof-rewrite-result proof (car opened) reverse template *proof-result*)))
        (cons step (cdr opened))))
     (t
      (proof-with-checked-results
          ((leaf (b2-list-properties-preserve-list-consequent-leaf
                  value signed lib premise formula position rules predicates predicate
                  call arguments measure substitutions search))
           (literal (proof-step-first (car leaf)))
           (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal target) leaf '(:failure "tactic-rejected" "")))))))

(defun b2-list-properties-preserve-list-consequent
    (premise lib opened template formula position rules predicates predicate call
             arguments measure search)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (b2-list-properties-step-argument opened 2))
         (results (b2-list-properties-preserve-list-consequent-visit
                   1000000 lib value template nil premise formula position rules predicates
                   predicate call arguments measure nil search))
         (reverse (proof-proof-symmetric proof opened))
         (step (proof-proof-rewrite-result proof (car results) reverse template *proof-result*)))
      (cons step (cdr results)))))

(defun b2-list-properties-preserve-list-open (proof call)
  (proof-with-checked-results
      ((opened (proof-proof-unfold proof call))
       (body (b2-list-properties-step-argument opened 2)))
    (if (proof-is-call body *termination-return-last*)
        (proof-with-checked-results ((second (proof-proof-unfold proof body)))
          (proof-proof-chain proof opened (list second)))
      opened)))

(defun b2-list-properties-preserve-list-with-search (lib formula position rules predicates search)
  (if (not (proof-is-call formula *library-implies*))
      '(:failure "unproved" "")
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (result (proof-list-of-length (caddr parts) 2))
         (call (cadr result))
         (arguments (if (integerp call)
                        '(:failure "tactic-rejected" "")
                      (cdr call)))
         (x (b2-list-properties-argument-at arguments position)))
      (if (or (not (b2-list-properties-variables-p arguments))
              (not (equal (len (proof-unique arguments)) (len arguments))))
          '(:failure "unproved" "")
        (let* ((proof (library-library-proof lib))
               (condition (cadr parts))
               (goal (caddr parts))
               (predicate (car result))
               (measure (list *library-count* x))
               (template (list predicate *proof-result*)))
          (proof-with-checked-results
              ((opened (b2-list-properties-preserve-list-open proof call))
               (request (b2-tactics-tactics-implication lib condition goal nil))
               (call-request (car request))
               (consequent (b2-list-properties-preserve-list-consequent
                            (cadddr call-request) lib opened template formula position rules
                            predicates predicate call arguments measure search))
               (answer (b2-tactics-tactics-implication
                        lib condition goal (cons (car consequent) lib)))
               (case-step (car answer))
               (ordinal (library-library-builtin lib 1 x))
               (step (proof-proof-induct proof ordinal case-step formula measure (cadr consequent))))
            (cons step (caddr consequent))))))))

(defun b2-list-properties-preserve-list (lib formula position rules predicates search)
  (proof-with-checked-results
      ((result (b2-list-properties-preserve-list-with-search
                lib formula position rules predicates search)))
    (car result)))
