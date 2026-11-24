(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-evaluator-a* (proof-sym "A" "ACL2"))
(defconst *b2-evaluator-b* (proof-sym "B" "ACL2"))
(defconst *b2-evaluator-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *b2-evaluator-pairlis* (proof-sym "PAIRLIS$" "ACL2"))
(defconst *b2-evaluator-kwote* (proof-sym "KWOTE" "ACL2"))
(defconst *b2-evaluator-kwotes* (proof-sym "KWOTE-LST" "ACL2"))

(defun b2-evaluator-arities (functions)
  (if (consp functions)
      (proof-with-checked-results
          ((function (proof-list-of-length (car functions) 2))
           (rest (b2-evaluator-arities (cdr functions))))
        (cons (cadr function) rest))
    (if (integerp functions)
        '(:failure "failure" "")
      nil)))

(defun b2-evaluator-evaluator-equations (functions formulas)
  (proof-with-checked-results ((arities (b2-evaluator-arities functions)))
    (cond
     ((not (equal arities '(2 2))) nil)
     ((integerp formulas) '(:failure "failure" ""))
     ((< (len formulas) 8) nil)
     (t
      (let* ((ev (caar functions))
             (evl (caadr functions))
             (quoted-arguments
              (list *b2-evaluator-kwotes*
                    (list evl (list *library-cdr* *library-x*) *b2-evaluator-a*)))
             (replay (list ev (list *proof-cons* (list *library-car* *library-x*)
                                    quoted-arguments)
                           *proof-false*)))
        (proof-with-checked-results ((formula (proof-term-at (car formulas) 1)))
          (and (proof-is-call formula *library-implies*)
               (proof-with-checked-results ((goal (proof-term-at formula 2)))
                 (equal goal (proof-eq (list ev *library-x* *b2-evaluator-a*)
                                       replay))))))))))

(defun b2-evaluator-make-evaluator (lib name label ev evl goals operations arity)
  (list :b2-evaluator lib name label ev evl goals operations arity))

(defun b2-evaluator-evaluator-library (evaluator)
  (cadr evaluator))

(defun b2-evaluator-evaluator-name (evaluator)
  (caddr evaluator))

(defun b2-evaluator-evaluator-label (evaluator)
  (cadddr evaluator))

(defun b2-evaluator-evaluator-ev (evaluator)
  (nth 4 evaluator))

(defun b2-evaluator-evaluator-evl (evaluator)
  (nth 5 evaluator))

(defun b2-evaluator-evaluator-goals (evaluator)
  (nth 6 evaluator))

(defun b2-evaluator-evaluator-operations (evaluator)
  (nth 7 evaluator))

(defun b2-evaluator-evaluator-arity (evaluator)
  (nth 8 evaluator))

(defun b2-evaluator-with-library (evaluator lib)
  (b2-evaluator-make-evaluator
   lib (b2-evaluator-evaluator-name evaluator)
   (b2-evaluator-evaluator-label evaluator)
   (b2-evaluator-evaluator-ev evaluator) (b2-evaluator-evaluator-evl evaluator)
   (b2-evaluator-evaluator-goals evaluator)
   (b2-evaluator-evaluator-operations evaluator)
   (b2-evaluator-evaluator-arity evaluator)))

(defun b2-evaluator-field-index (arg count)
  (cond
   ((proof-is-call arg *library-cdr*)
    (if (consp (cdr arg))
        (b2-evaluator-field-index (cadr arg) (1+ count))
      '(:failure "failure" "")))
   ((and (equal arg *library-x*) (<= 1 count) (<= count 5)) count)
   (t (b2-tactics-unproved))))

(mutual-recursion
 (defun b2-evaluator-evaluator-field-count (evaluator term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term (b2-evaluator-evaluator-ev evaluator))
     (proof-with-checked-results ((env (proof-term-at term 2)))
       (if (not (equal env *b2-evaluator-a*))
           (b2-tactics-unproved)
         (proof-with-checked-results ((selection (proof-term-at term 1)))
           (if (proof-is-call selection *library-car*)
               (proof-with-checked-results ((arg (proof-term-at selection 1)))
                 (b2-evaluator-field-index arg 0))
             (b2-tactics-unproved))))))
    ((not (proof-compound term)) 0)
    ((endp term) '(:failure "failure" ""))
    ((equal (car term) *proof-quote*) 0)
    (t (b2-evaluator-field-count-arguments evaluator (cdr term)))))
 (defun b2-evaluator-field-count-arguments (evaluator args)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       0
     (proof-with-checked-results
         ((first (b2-evaluator-evaluator-field-count evaluator (car args)))
          (rest (b2-evaluator-field-count-arguments evaluator (cdr args))))
       (max first rest)))))

(defun b2-evaluator-dispatch-operation (evaluator premise equation)
  (proof-with-checked-results
      ((matches
        (and (proof-is-call premise *proof-if*)
             (proof-with-checked-results
                 ((test (proof-term-at premise 1)))
               (and (equal test (list *proof-consp* *library-x*))
                    (proof-with-checked-results ((condition (proof-term-at premise 2)))
                      (and (proof-is-call condition *proof-equal*)
                           (proof-with-checked-results ((head (proof-term-at condition 1)))
                             (and (equal head (list *library-car* *library-x*))
                                  (proof-with-checked-results
                                      ((operation (proof-term-at condition 2)))
                                    (and (proof-is-call operation *proof-quote*)
                                         (proof-is-call equation *proof-equal*)
                                         (proof-with-checked-results
                                             ((left (proof-term-at equation 1)))
                                           (equal left
                                                  (list (b2-evaluator-evaluator-ev evaluator)
                                                        *library-x* *b2-evaluator-a*))))))))))))))
    (if matches
        (proof-with-checked-results ((result (proof-term-at equation 2)))
          (list (caddr (caddr premise)) result))
      (b2-tactics-unproved))))

(defun b2-evaluator-dispatch-goals (goals evaluator operations arity)
  (if (endp goals)
      (list (reverse operations) arity)
    (let ((clause (car goals)))
      (if (not (proof-is-call clause *library-implies*))
          (b2-tactics-unproved)
        (proof-with-checked-results
            ((parts (proof-list-of-length clause 3))
             (operation (b2-evaluator-dispatch-operation evaluator (cadr parts) (caddr parts)))
             (width (b2-evaluator-evaluator-field-count evaluator (cadr operation))))
          (b2-evaluator-dispatch-goals (cdr goals) evaluator
                                      (cons operation operations) (max arity width)))))))

(defun b2-evaluator-evaluator-dispatch (evaluator)
  (b2-evaluator-dispatch-goals (nthcdr 8 (b2-evaluator-evaluator-goals evaluator))
                              evaluator nil 0))

(defun b2-evaluator-rename-goals (formulas names)
  (if (endp formulas)
      nil
    (proof-with-checked-results
        ((named (proof-list-of-length (car formulas) 2))
         (goal (b2-tactics-rename-calls (cadr named) names))
         (rest (b2-evaluator-rename-goals (cdr formulas) names)))
      (cons goal rest))))

(defun b2-evaluator-evaluator-init (lib functions formulas)
  (proof-with-checked-results ((matches (b2-evaluator-evaluator-equations functions formulas)))
    (if (not matches)
        (b2-tactics-unproved)
      (let ((name (caar functions))
            (list-name (caadr functions)))
        (proof-with-checked-results
            ((label (proof-term-at name 2))
             (list-label (proof-term-at list-name 2)))
          (let* ((ev (proof-sym (concatenate 'string "B2-" label) "ACL2"))
                 (evl (proof-sym (concatenate 'string "B2-" list-label) "ACL2"))
                 (names (table-put (list (cons name ev)) list-name evl)))
            (proof-with-checked-results
                ((goals (b2-evaluator-rename-goals formulas names))
                 (evaluator (b2-evaluator-make-evaluator lib name label ev evl goals nil 0))
                 (dispatch (b2-evaluator-evaluator-dispatch evaluator)))
              (b2-evaluator-make-evaluator lib name label ev evl goals
                                           (car dispatch) (cadr dispatch)))))))))

(defun b2-evaluator-dispatch-body (operations head fallback)
  (if (endp operations)
      fallback
    (let ((operation (car operations)))
      (b2-evaluator-dispatch-body
       (cdr operations) head
       (proof-ite (proof-eq head (car operation)) (cadr operation) fallback)))))

(defun b2-evaluator-add-definitions (definitions proof)
  (if (endp definitions)
      proof
    (let ((definition (car definitions)))
      (proof-with-checked-results
          ((next (proof-proof-add-definition proof (car definition)
                                             (cadr definition) (caddr definition))))
        (b2-evaluator-add-definitions (cdr definitions) next)))))

(defun b2-evaluator-evaluator-install (evaluator)
  (let* ((lib (b2-evaluator-evaluator-library evaluator))
         (ev (b2-evaluator-evaluator-ev evaluator))
         (evl (b2-evaluator-evaluator-evl evaluator))
         (x *library-x*)
         (a *b2-evaluator-a*)
         (head (list *library-car* x))
         (args (list *library-cdr* x))
         (eval-lambda
          (list ev (b2-tactics-field head 2)
                (list *b2-evaluator-pairlis* (b2-tactics-field head 1) (list evl args a))))
         (env-lookup (proof-ite x (list *library-cdr* (list *b2-evaluator-assoc* x a))
                               *proof-false*))
         (on-cons (b2-evaluator-dispatch-body
                   (reverse (b2-evaluator-evaluator-operations evaluator)) head
                   (proof-ite (list *proof-consp* head) eval-lambda *proof-false*)))
         (ev-body (proof-ite (list *proof-consp* x)
                             (proof-ite (proof-eq head (proof-quote *proof-quote*))
                                        (b2-tactics-field args 0) on-cons)
                             (proof-ite (list *b2-tactics-symbolp* x) env-lookup *proof-false*)))
         (evl-body (proof-ite (list *proof-consp* x)
                              (list *proof-cons* (list ev head a) (list evl args a))
                              *proof-false*))
         (definitions (list (list ev (list x a) ev-body) (list evl (list x a) evl-body))))
    (proof-with-checked-results
        ((line (proof-line "define" (cons *termination-all* definitions)))
         (lib (library-library-with-entries
               lib (append (library-library-entries lib) (list (list "define" ev nil line)))))
         (measure (list *library-count* x))
         (measures (table-put (list (cons ev measure)) evl measure))
         (calls (termination-recursive-calls *termination-all* definitions))
         (proved (b2-measures-prove-measure lib definitions calls measures))
         (lib (cdr proved))
         (lib (library-library-with-entries
               lib (append (library-library-entries lib) (list (car proved)))))
         (proof (b2-evaluator-add-definitions definitions (library-library-proof lib))))
      (b2-evaluator-with-library evaluator (library-library-with-proof lib proof)))))

(defun b2-evaluator-evaluator-remember (evaluator name step)
  (let ((lib (b2-evaluator-evaluator-library evaluator))
        (label (b2-evaluator-evaluator-label evaluator)))
    (proof-with-checked-results
        ((added (b2-tactics-tactics-add-lemma
                 lib (concatenate 'string label "-" name) step :none)))
      (cons (car added) (b2-evaluator-with-library evaluator (cdr added))))))

(defun b2-evaluator-evaluator-quote-arguments-base
    (atom-step lib goal evaluated encoded repeated)
  (b2-tactics-tactics-solve lib goal (list atom-step)
                            (list evaluated encoded repeated) nil 0 nil))

(defun b2-evaluator-evaluator-quote-arguments-advance
    (cons-step hypothesis lib goal evaluated encoded repeated ev quoted)
  (let ((head (list ev (list *library-car* *library-x*) *b2-evaluator-a*)))
    (proof-with-checked-results
        ((inner (proof-proof-fact (library-library-proof lib) quoted
                                 (list (list *library-x* head)
                                       (list *b2-evaluator-a* *b2-evaluator-b*)))))
      (b2-tactics-tactics-solve lib goal (list cons-step)
                                (list evaluated encoded repeated) (list inner hypothesis)
                                0 nil))))

(defun b2-evaluator-evaluator-quote-arguments (evaluator)
  (let* ((lib (b2-evaluator-evaluator-library evaluator))
         (ev (b2-evaluator-evaluator-ev evaluator))
         (evl (b2-evaluator-evaluator-evl evaluator))
         (x *library-x*)
         (raw (list ev (list *b2-evaluator-kwote* x) *b2-evaluator-a*)))
    (proof-with-checked-results
        ((proof (b2-tactics-tactics-solve lib (proof-eq raw x) nil
                                         (list raw *b2-evaluator-kwote*) nil 0 nil))
         (saved (b2-evaluator-evaluator-remember evaluator "QUOTED" proof)))
      (let* ((evaluator (cdr saved))
             (lib (b2-evaluator-evaluator-library evaluator))
             (evaluated (list evl x *b2-evaluator-a*))
             (encoded (list *b2-evaluator-kwotes* evaluated))
             (repeated (list evl encoded *b2-evaluator-b*))
             (goal (proof-eq repeated evaluated)))
        (proof-with-checked-results
            ((advance (b2-tactics-tactics-on-list lib goal x nil nil nil))
             (args (car advance))
             (advance-step
              (b2-evaluator-evaluator-quote-arguments-advance
               (cadddr args) (nth 4 args) (cdr advance)
               goal evaluated encoded repeated ev (car saved)))
             (advance-reply (cons advance-step (cdr advance)))
             (base (b2-tactics-tactics-on-list lib goal x nil advance-reply nil))
             (base-step
              (b2-evaluator-evaluator-quote-arguments-base
               (cadddr (car base)) (cdr base) goal evaluated encoded repeated))
             (proved (b2-tactics-tactics-on-list lib goal x
                                                 (cons base-step (cdr base))
                                                 advance-reply nil)))
          (b2-evaluator-evaluator-remember
           (b2-evaluator-with-library evaluator (cdr proved))
           "QUOTED-ARGUMENTS" (car proved)))))))

(defun b2-evaluator-projection-step (index evaluator names)
  (let* ((lib (b2-evaluator-evaluator-library evaluator))
         (proof (library-library-proof lib))
         (ev (b2-evaluator-evaluator-ev evaluator))
         (evlist (list (b2-evaluator-evaluator-evl evaluator) *library-x* *b2-evaluator-a*))
         (goal (proof-eq (b2-tactics-field evlist index)
                         (list ev (b2-tactics-field *library-x* index) *b2-evaluator-a*)))
         (test (list *proof-consp* *library-x*))
         (unfold (list evlist (list ev *proof-false* *b2-evaluator-a*))))
    (proof-with-checked-results
        ((yes (proof-proof-assume proof test t))
         (no (proof-proof-assume proof test nil))
         (previous (and (consp names)
                        (proof-proof-fact proof (car names)
                                          (list (list *library-x*
                                                      (list *library-cdr* *library-x*))))))
         (nonempty (b2-tactics-tactics-solve lib goal (list yes) unfold
                                             (and previous (list previous)) 0 nil))
         (empty (b2-tactics-tactics-solve lib goal (list no) unfold nil 0 nil))
         (cases (proof-proof-cases proof test nonempty empty)))
      (b2-evaluator-evaluator-remember
       evaluator (concatenate 'string "ARGUMENT-" (decimal-text index)) cases))))

(defun b2-evaluator-projection-steps (indices evaluator names)
  (declare (xargs :measure (acl2-count indices)))
  (if (endp indices)
      (cons (reverse names) evaluator)
    (proof-with-checked-results
        ((saved (b2-evaluator-projection-step (car indices) evaluator names)))
      (b2-evaluator-projection-steps (cdr indices) (cdr saved)
                                     (cons (car saved) names)))))

(defun b2-evaluator-evaluator-projections (evaluator)
  (proof-with-checked-results
      ((indices (seq-range 0 (b2-evaluator-evaluator-arity evaluator) 1)))
    (b2-evaluator-projection-steps indices evaluator nil)))

(defun b2-evaluator-evidence-step (facts term)
  (let ((entry (assoc-equal term facts)))
    (if entry (cdr entry)
      '(:failure "failure" ""))))

(defun b2-evaluator-evaluator-quote-invariance-expand
    (evidence assumed-head lib left right head encoded)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((lhs (b2-tactics-tactics-normalize lib left evidence (list left) nil 1500 nil))
         (rhs (b2-tactics-tactics-normalize lib right evidence (list right) nil 1500 nil))
         (car-arg (if (eq assumed-head :none) head assumed-head))
         (cdr-cons (library-library-axiom lib "CDR-CONS" (list car-arg encoded)))
         (rhs (if rhs (proof-proof-rewrite-first proof rhs cdr-cons)
                '(:failure "failure" ""))))
      (list lhs rhs))))

(defun b2-evaluator-replay-projections (lemmas lhs lib args env encoded unfolded)
  (declare (xargs :measure (acl2-count lemmas)))
  (if (endp lemmas)
      lhs
    (let ((proof (library-library-proof lib))
          (lemma (car lemmas))
          (x *library-x*)
          (a *b2-evaluator-a*))
      (proof-with-checked-results
          ((original (proof-proof-fact proof lemma (list (list x args) (list a env))))
           (replayed (proof-proof-fact proof lemma (list (list x encoded) (list a *proof-false*))))
           (replayed (proof-proof-rewrite-first proof replayed unfolded))
           (back (proof-proof-symmetric proof original))
           (identity (proof-proof-chain proof back (list replayed)))
           (lhs (if lhs (proof-proof-rewrite-first proof lhs identity)
                  '(:failure "failure" ""))))
        (b2-evaluator-replay-projections (cdr lemmas) lhs lib args env encoded unfolded)))))

(defun b2-evaluator-evaluator-quote-invariance-dispatch
    (operations failed evaluator argument-projections base goal left right head args env
                encoded unfolded lambda-form lm-yes lm-no)
  (declare (xargs :measure (acl2-count operations)))
  (let* ((lib (b2-evaluator-evaluator-library evaluator))
         (proof (library-library-proof lib)))
    (if (endp operations)
        (proof-with-checked-results
            ((expanded (b2-evaluator-evaluator-quote-invariance-expand
                        (append base failed (list lm-yes)) :none lib left right head encoded))
             (rhs (proof-proof-rewrite-first proof (cadr expanded) unfolded))
             (rhs-back (proof-proof-symmetric proof rhs))
             (when-lambda (proof-proof-chain proof (car expanded) (list rhs-back)))
             (irrelevant (b2-tactics-tactics-solve lib goal (append base failed (list lm-no))
                                                   (list left right) nil 0 nil)))
          (proof-proof-cases proof lambda-form when-lambda irrelevant))
      (let* ((operation (caar operations))
             (result (cadar operations))
             (test (proof-eq head operation)))
        (proof-with-checked-results
            ((matches (proof-proof-assume proof test t))
             (different (proof-proof-assume proof test nil))
             (expanded (b2-evaluator-evaluator-quote-invariance-expand
                        (append base (list matches)) operation lib left right head encoded))
             (count (b2-evaluator-evaluator-field-count evaluator result))
             (lhs (b2-evaluator-replay-projections (seq-slice argument-projections 0 count) (car expanded)
                                                   lib args env encoded unfolded))
             (rhs-back (proof-proof-symmetric proof (cadr expanded)))
             (matches-result (proof-proof-chain proof lhs (list rhs-back)))
             (misses-result
              (b2-evaluator-evaluator-quote-invariance-dispatch
               (cdr operations) (append failed (list different))
               evaluator argument-projections base goal left right head args env
               encoded unfolded lambda-form lm-yes lm-no)))
          (proof-proof-cases proof test matches-result misses-result))))))

(defun b2-evaluator-evaluator-quote-invariance-consequent
    (premise evaluator argument-projections goal left right expr env head args encoded unfolded
             lambda-form)
  (let* ((lib (b2-evaluator-evaluator-library evaluator))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((facts (b2-tactics-tactics-evidence lib (list premise)))
         (cons-expr (b2-evaluator-evidence-step facts (list *proof-consp* expr)))
         (unquoted (b2-evaluator-evidence-step facts (proof-neg (proof-eq head (proof-quote *proof-quote*)))))
         (lm-yes (proof-proof-assume proof lambda-form t))
         (lm-no (proof-proof-assume proof lambda-form nil)))
      (b2-evaluator-evaluator-quote-invariance-dispatch
       (b2-evaluator-evaluator-operations evaluator) nil evaluator argument-projections
       (list cons-expr unquoted) goal left right head args env encoded unfolded
       lambda-form lm-yes lm-no))))

(defun b2-evaluator-evaluator-quote-invariance (evaluator quoted-arguments argument-projections)
  (let* ((lib (b2-evaluator-evaluator-library evaluator))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((formula (proof-term-at (b2-evaluator-evaluator-goals evaluator) 0))
         (parts (proof-list-of-length formula 3))
         (equation (proof-list-of-length (caddr parts) 3))
         (subject (proof-list-of-length (cadr equation) 3)))
      (let* ((predicate (cadr parts))
             (goal (caddr parts))
             (left (cadr equation))
             (right (caddr equation))
             (expr (cadr subject))
             (env (caddr subject))
             (head (list *library-car* expr))
             (args (list *library-cdr* expr))
             (evaluated (list (b2-evaluator-evaluator-evl evaluator) args env))
             (encoded (list *b2-evaluator-kwotes* evaluated))
             (lambda-form (list *proof-consp* head)))
        (proof-with-checked-results
            ((unfolded (proof-proof-fact proof quoted-arguments
                                        (list (list *library-x* args)
                                              (list *b2-evaluator-a* env)
                                              (list *b2-evaluator-b* *proof-false*))))
             (request (b2-tactics-tactics-implication lib predicate goal nil))
             (outcome (b2-evaluator-evaluator-quote-invariance-consequent
                       (cadddr (car request)) evaluator argument-projections
                       goal left right expr env head args encoded unfolded lambda-form))
             (proved (b2-tactics-tactics-implication lib predicate goal (cons outcome lib))))
          (car proved))))))

(defun b2-evaluator-noncons (lib term typed)
  (let* ((proof (library-library-proof lib))
         (test (list *proof-consp* term)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof "consp-not-symbolp" (list (list *library-x* term))))
         (given (proof-proof-assume proof test t))
         (other (proof-proof-modus-ponens proof fact given))
         (cut (proof-proof-cut proof typed other)))
      (proof-proof-front proof cut (proof-neg test)))))

(defun b2-evaluator-operation-tags (operations)
  (if (endp operations)
      nil
    (cons (caar operations) (b2-evaluator-operation-tags (cdr operations)))))

(defun b2-evaluator-impossible-tags (tags lib head known kind)
  (if (endp tags)
      nil
    (proof-with-checked-results
        ((given (b2-evaluator-evidence-step known kind))
         (denial (b2-tactics-tactics-from-impossible
                  lib (proof-neg (proof-eq head (car tags))) given nil nil nil 1500 nil))
         (rest (b2-evaluator-impossible-tags (cdr tags) lib head known kind)))
      (cons denial rest))))

(defun b2-evaluator-evaluator-ordinary-constraints-consequent
    (assumption evaluator index goal left)
  (let ((lib (b2-evaluator-evaluator-library evaluator)))
    (proof-with-checked-results
        ((known (b2-tactics-tactics-evidence lib (list assumption)))
         (subject (proof-term-at left 1)))
      (let ((head (list *library-car* subject)))
        (proof-with-checked-results
            ((noncons (and (eql index 1) (b2-evaluator-noncons lib subject assumption)))
             (denials
              (and (member-equal index '(3 7))
                   (b2-evaluator-impossible-tags
                    (cons (proof-quote *proof-quote*)
                          (b2-evaluator-operation-tags (b2-evaluator-evaluator-operations evaluator)))
                    lib head known
                    (if (eql index 3) (list *proof-consp* head)
                      (proof-neg (list *b2-tactics-symbolp* head)))))))
          (b2-tactics-tactics-solve lib goal
                                    (append (table-values known)
                                            (and noncons (list noncons)) denials)
                                    (list left) nil 0 nil))))))

(defun b2-evaluator-ordinary-steps (goals index evaluator)
  (declare (xargs :measure (acl2-count goals)))
  (if (endp goals)
      nil
    (let ((lib (b2-evaluator-evaluator-library evaluator)))
      (proof-with-checked-results
          ((parts (proof-list-of-length (car goals) 3))
           (premise (cadr parts))
           (goal (caddr parts))
           (left (proof-term-at goal 1))
           (request (b2-tactics-tactics-implication lib premise goal nil))
           (outcome (b2-evaluator-evaluator-ordinary-constraints-consequent
                     (cadddr (car request)) evaluator index goal left))
           (proved (b2-tactics-tactics-implication lib premise goal (cons outcome lib)))
           (rest (b2-evaluator-ordinary-steps (cdr goals) (1+ index) evaluator)))
        (cons (car proved) rest)))))

(defun b2-evaluator-evaluator-ordinary-constraints (evaluator)
  (b2-evaluator-ordinary-steps (cdr (b2-evaluator-evaluator-goals evaluator)) 1 evaluator))

(defun b2-evaluator-evaluator-prove (evaluator)
  (proof-with-checked-results
      ((installed (b2-evaluator-evaluator-install evaluator))
       (quoted (b2-evaluator-evaluator-quote-arguments installed))
       (projections (b2-evaluator-evaluator-projections (cdr quoted)))
       (evaluator (cdr projections))
       (invariance (b2-evaluator-evaluator-quote-invariance evaluator (car quoted) (car projections)))
       (ordinary (b2-evaluator-evaluator-ordinary-constraints evaluator))
       (name (b2-evaluator-evaluator-name evaluator))
       (fields (list name (b2-evaluator-evaluator-ev evaluator) (b2-evaluator-evaluator-evl evaluator)))
       (entry (proof-proof-entry "witness" name fields (cons invariance ordinary))))
    (cons entry evaluator)))

(defun b2-evaluator-witness (lib functions formulas)
  (proof-with-checked-results
      ((evaluator (b2-evaluator-evaluator-init lib functions formulas))
       (proved (b2-evaluator-evaluator-prove evaluator)))
    (cons (car proved) (b2-evaluator-evaluator-library (cdr proved)))))
