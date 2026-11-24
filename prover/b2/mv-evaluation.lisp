(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-mv-evaluation-nth* '("sym" "COMMON-LISP" "NTH"))
(defconst *b2-mv-evaluation-ev* '("sym" "ACL2" "EVAL-FOR-MV-NTH"))
(defconst *b2-mv-evaluation-rec* '("sym" "ACL2" "MV-NTH-EVAL-REC"))
(defconst *b2-mv-evaluation-meta* '("sym" "ACL2" "MV-NTH-EVAL-FN"))
(defconst *b2-mv-evaluation-rec-correct* '("sym" "ACL2" "EVAL-FOR-MV-NTH-REC-THM"))
(defconst *b2-mv-evaluation-meta-correct* '("sym" "ACL2" "MV-NTH-CONS-META"))
(defconst *b2-mv-evaluation-mv-evaluation*
  (list *b2-mv-evaluation-rec-correct* *b2-mv-evaluation-meta-correct*))
(defconst *b2-mv-evaluation-n* '("sym" "ACL2" "N"))

(defun b2-mv-evaluation-step-argument (step index)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun b2-mv-evaluation-index-equivalence-base (atom lib goal mv-call nth-call)
  (b2-tactics-tactics-solve lib goal (list atom) (list mv-call nth-call) nil 0 nil))

(defun b2-mv-evaluation-index-equivalence-step-choose
    (n lib test evidence goal mv-call nth-call induction replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "b2-mv-evaluation-index-equivalence-step-choose")
    (proof-with-checked-results
        ((choice (b2-tactics-choose lib test evidence replies))
         (result (car choice)))
      (if (and (consp result) (eq (car result) :call))
          (proof-with-checked-results
              ((reply (b2-tactics-tactics-solve
                       (cdr choice) goal (car (cddddr result)) (list mv-call nth-call)
                       (list induction) 0 nil)))
            (b2-mv-evaluation-index-equivalence-step-choose
             (1- n) lib test evidence goal mv-call nth-call induction
             (append replies (list (cons reply (cdr choice))))))
        choice))))

(defun b2-mv-evaluation-index-equivalence-step
    (nonempty induction lib goal mv-call nth-call)
  (b2-mv-evaluation-index-equivalence-step-choose
   1000000 lib (list *b2-projections-zp* *b2-mv-evaluation-n*) (list nonempty)
   goal mv-call nth-call induction nil))

(defun b2-mv-evaluation-index-equivalence-lemma (lib)
  (let* ((n *b2-mv-evaluation-n*)
         (x *library-x*)
         (mv-call (list *b2-projections-mv-nth* n x))
         (nth-call (list *b2-mv-evaluation-nth* n x))
         (goal (proof-eq mv-call nth-call))
         (extra (list (list n (library-plus *proof-neg-one* n)))))
    (proof-with-checked-results
        ((request (b2-tactics-tactics-on-list lib goal x nil nil extra))
         (advance-call (car request))
         (advance (b2-mv-evaluation-index-equivalence-step
                   (cadddr advance-call) (car (cddddr advance-call)) (cdr request)
                   goal mv-call nth-call))
         (request (b2-tactics-tactics-on-list lib goal x nil advance extra))
         (base-call (car request))
         (base (b2-mv-evaluation-index-equivalence-base (cadddr base-call)
                                                      (cdr request) goal mv-call nth-call))
         (result (b2-tactics-tactics-on-list lib goal x (cons base (cdr request)) advance extra))
         (step (car result))
         (entry (b2-tactics-tactics-add-lemma (cdr result) "MV-NTH-IS-NTH" step :none))
         (name (car entry)))
      (cdr entry))))

(defun b2-mv-evaluation-index-equivalence (lib index values)
  (let ((name (proof-sym "B2-MV-NTH-IS-NTH" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (b2-mv-evaluation-index-equivalence-lemma lib)))
         (step (proof-proof-fact (library-library-proof lib) name
                                 (list (list *b2-mv-evaluation-n* index)
                                       (list *library-x* values)))))
      (cons step lib))))

(defun b2-mv-evaluation-ev-quote (lib term env evidence)
  (let ((target (proof-eq (list *b2-mv-evaluation-ev* term env)
                          (b2-tactics-field term 1)))
        (rule (proof-sym "EVAL-FOR-MV-NTH-CONSTRAINT-2" "ACL2")))
    (b2-tactics-tactics-use-fact lib rule target evidence nil nil 0 nil)))

(defun b2-mv-evaluation-ev-binary (lib term env operation evidence)
  (let* ((is-cons (equal operation *proof-cons*))
         (operator (if is-cons *proof-cons* *b2-projections-mv-nth*))
         (rule (proof-sym (if is-cons "EVAL-FOR-MV-NTH-CONSTRAINT-9"
                            "EVAL-FOR-MV-NTH-CONSTRAINT-8")
                          "ACL2"))
         (ev *b2-mv-evaluation-ev*)
         (args (list (list ev (b2-tactics-field term 1) env)
                     (list ev (b2-tactics-field term 2) env)))
         (target (proof-eq (list ev term env) (cons operator args))))
    (b2-tactics-tactics-use-fact lib rule target evidence nil nil 0 nil)))

(defun b2-mv-evaluation-assumptions (proof signed)
  (if (endp signed)
      nil
    (proof-with-checked-results
        ((first (proof-proof-assume proof (caar signed) (cadar signed)))
         (rest (b2-mv-evaluation-assumptions proof (cdr signed))))
      (cons first rest))))

(defun b2-mv-evaluation-recursive-evaluation-establish-leaf-cons
    (lib value term env index projected facts target)
  (proof-with-checked-results
      ((literal (b2-mv-evaluation-ev-quote lib value env facts))
       (origin (b2-mv-evaluation-ev-quote lib term env facts))
       (datum (b2-tactics-field term 1))
       (cell (proof-term-at value 2))
       (element (proof-term-at cell 1)))
    (let ((rules (list literal origin)))
      (if (proof-is-call element *b2-mv-evaluation-nth*)
          (proof-with-checked-results
              ((equivalence (b2-mv-evaluation-index-equivalence
                             lib index datum))
               (lib (cdr equivalence))
               (step (b2-tactics-tactics-solve
                      lib target facts nil (append rules (list (car equivalence))) 0 nil)))
            (cons step lib))
        (proof-with-checked-results
            ((step (b2-tactics-tactics-solve lib target facts (list projected) rules 0 nil)))
          (cons step lib))))))

(defun b2-mv-evaluation-recursive-evaluation-establish-leaf-rec
    (lib index facts formula measure binding premise equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((ruler (b2-measures-rulers-init lib facts))
         (smaller (library-library-builtin lib 14 index))
         (typed (b2-measures-rulers-require ruler (list *proof-integerp* index)))
         (smaller (proof-proof-discharge proof smaller (car typed)))
         (positive (b2-measures-rulers-require (cdr typed) (library-lt *proof-zero* index)))
         (smaller (proof-proof-discharge proof smaller (car positive)))
         (hyp (b2-tactics-tactics-induction-hypothesis lib formula measure binding smaller))
         (changed (if equation
                      (proof-proof-rewrite proof premise equation '(1 2))
                    '(:failure "failure" "")))
         (antecedent (proof-proof-tidy proof changed))
         (result (proof-proof-modus-ponens proof hyp antecedent))
         (reverse (proof-proof-symmetric proof equation))
         (rewritten (proof-proof-rewrite proof result reverse '(1 2)))
         (step (proof-proof-tidy proof rewritten)))
      (cons step lib))))

(defun b2-mv-evaluation-recursive-evaluation-establish-leaf (value signed lib context)
  (let ((premise (nth 0 context))
        (index (nth 1 context))
        (term (nth 2 context))
        (original (nth 3 context))
        (env (nth 4 context))
        (projected (nth 5 context))
        (formula (nth 6 context))
        (measure (nth 7 context))
        (binding (nth 8 context))
        (proof (library-library-proof lib)))
    (if (equal value original)
        (cons premise lib)
      (proof-with-checked-results ((facts (b2-mv-evaluation-assumptions proof signed)))
        (if (proof-is-call value *proof-cons*)
            (b2-mv-evaluation-recursive-evaluation-establish-leaf-cons
             lib value term env index projected facts
             (proof-eq (list *b2-mv-evaluation-ev* value env) projected))
          (proof-with-checked-results
              ((original-cons (b2-mv-evaluation-ev-binary lib term env *proof-cons* facts))
               (equation (b2-tactics-tactics-normalize
                          lib projected facts (list projected) (list original-cons) 1500 nil)))
            (cond
             ((equal value (b2-tactics-field term 1))
              (proof-with-checked-results
                  ((step (if equation
                             (proof-proof-symmetric proof equation)
                           '(:failure "failure" ""))))
                (cons step lib)))
             ((not (proof-is-call value *b2-mv-evaluation-rec*))
              '(:failure "Unproved" ""))
             (t (b2-mv-evaluation-recursive-evaluation-establish-leaf-rec
                 lib index facts formula measure binding premise equation)))))))))

(defun b2-mv-evaluation-mv-meta-leaf (value signed lib term env original)
  (let ((proof (library-library-proof lib)))
    (if (equal value term)
        (proof-proof-reflexive proof original)
      (proof-with-checked-results
          ((facts (b2-mv-evaluation-assumptions proof signed))
           (actual (b2-mv-evaluation-ev-binary lib term env *b2-projections-mv-nth* facts))
           (first (b2-mv-evaluation-ev-quote lib (b2-tactics-field term 1) env facts))
           (actual (proof-proof-rewrite proof actual first '(1 2 1)))
           (actual (proof-proof-tidy proof actual))
           (rhs (b2-mv-evaluation-step-argument actual 2))
           (correct (b2-tactics-tactics-use-fact
                     lib *b2-mv-evaluation-rec-correct*
                     (proof-eq (list *b2-mv-evaluation-ev* value env) rhs)
                     (list actual) nil nil 0 nil))
           (reverse (proof-proof-symmetric proof correct)))
        (proof-proof-chain proof actual (list reverse))))))

(defun b2-mv-evaluation-by-value-leaf (value signed lib recipe context)
  (if (eq recipe :recursive)
      (b2-mv-evaluation-recursive-evaluation-establish-leaf value signed lib context)
    (proof-with-checked-results
        ((step (b2-mv-evaluation-mv-meta-leaf value signed lib (car context)
                                             (cadr context) (caddr context))))
      (cons step lib))))

(defun b2-mv-evaluation-by-value (n lib value template signed recipe context)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-mv-evaluation-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (yes (b2-mv-evaluation-by-value
                 (1- n) lib (cadr branches) template (append signed (list (list (car branches) t)))
                 recipe context))
           (no (b2-mv-evaluation-by-value
                (1- n) (cdr yes) (caddr branches) template
                (append signed (list (list (car branches) nil))) recipe context))
           (step (proof-by-value-join (library-library-proof (cdr no)) value template
                                       (car yes) (car no))))
        (cons step (cdr no))))
     ((null value) '(:failure "tactic-rejected" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (body (b2-mv-evaluation-step-argument equality 2))
           (opened (b2-mv-evaluation-by-value (1- n) lib body template signed recipe context))
           (proof (library-library-proof (cdr opened)))
           (reverse (proof-proof-symmetric proof equality))
           (step (proof-proof-rewrite-result proof (car opened) reverse template *proof-result*)))
        (cons step (cdr opened))))
     (t
      (proof-with-checked-results
          ((leaf (b2-mv-evaluation-by-value-leaf value signed lib recipe context))
           (literal (proof-step-first (car leaf)))
           (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal target) leaf '(:failure "tactic-rejected" "")))))))

(defun b2-mv-evaluation-recursive-evaluation-establish
    (premise lib opened template index term original env projected formula measure binding)
  (proof-with-checked-results
      ((value (b2-mv-evaluation-step-argument opened 2))
       (body (b2-mv-evaluation-by-value
              1000000 lib value template nil :recursive
              (list premise index term original env projected formula measure binding)))
       (proof (library-library-proof (cdr body)))
       (reverse (proof-proof-symmetric proof opened))
       (step (proof-proof-rewrite-result proof (car body) reverse template *proof-result*)))
    (cons step (cdr body))))

(defun b2-mv-evaluation-recursive-evaluation (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (condition (cadr parts))
       (goal (caddr parts))
       (lhs (proof-term-at goal 1))
       (lhs (proof-list-of-length lhs 3))
       (recursion (cadr lhs))
       (env (caddr lhs))
       (recursion-parts (proof-list-of-length recursion 4))
       (index (cadr recursion-parts))
       (term (caddr recursion-parts))
       (original (cadddr recursion-parts))
       (goal-parts (proof-list-of-length goal 3))
       (projected (caddr goal-parts))
       (template (proof-eq (list *b2-mv-evaluation-ev* *proof-result* env) projected))
       (measure (list *library-count* index))
       (binding (list (list index (library-plus *proof-neg-one* index))
                      (list term (b2-tactics-field term 2))))
       (opened (b2-tactics-tactics-normalize lib recursion nil (list recursion) nil 1500 t))
       (request (b2-tactics-tactics-implication lib condition goal nil))
       (call (car request))
       (body (b2-mv-evaluation-recursive-evaluation-establish
              (cadddr call) (cdr request) opened template index term original env projected
              formula measure binding))
       (result (b2-tactics-tactics-implication lib condition goal body))
       (step (car result))
       (next (cdr result))
       (ordinal (library-library-builtin next 1 index))
       (step (proof-proof-induct (library-library-proof next) ordinal step formula measure
                                  (list binding))))
    (cons step next)))

(defun b2-mv-evaluation-mv-meta (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (lhs (proof-list-of-length (cadr parts) 3))
       (rhs (proof-list-of-length (caddr parts) 3))
       (term (cadr lhs))
       (env (caddr lhs))
       (call (cadr rhs))
       (original (list *b2-mv-evaluation-ev* term env))
       (template (proof-eq original (list *b2-mv-evaluation-ev* *proof-result* env)))
       (opened (b2-tactics-tactics-normalize lib call nil (list call) nil 1500 t))
       (value (b2-mv-evaluation-step-argument opened 2))
       (result (b2-mv-evaluation-by-value
                1000000 lib value template nil :meta (list term env original)))
       (proof (library-library-proof lib))
       (reverse (proof-proof-symmetric proof opened)))
    (proof-proof-rewrite-result proof (car result) reverse template *proof-result*)))

(defun b2-mv-evaluation-mv-evaluation-theorem (lib name formula)
  (if (equal name *b2-mv-evaluation-rec-correct*)
      (b2-mv-evaluation-recursive-evaluation lib formula)
    (proof-with-checked-results ((step (b2-mv-evaluation-mv-meta lib formula)))
      (cons step lib))))
