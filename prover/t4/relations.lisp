(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-relations-booleanp* (proof-sym "BOOLEANP" "ACL2"))

(defun t4-relations-request-p (value)
  (and (consp value) (eq (car value) :t4-request)))

(defmacro t4-relations-with-results (bindings result)
  (if (endp bindings)
      result
    (let ((name (caar bindings)))
      `(let (,(car bindings))
         (if (or (failure-p ,name) (t4-relations-request-p ,name))
             ,name
           (t4-relations-with-results ,(cdr bindings) ,result))))))

(defun t4-relations-recipe-request (context operation arguments)
  (let ((replies (cdr context)))
    (if (endp replies)
        (list :t4-request operation arguments (car context))
      (let ((reply (car replies)))
        (if (failure-p reply)
            reply
          (cons (car reply) (cons (cdr reply) (cdr replies))))))))

(defun t4-relations-recipe-result (result)
  (t4-relations-with-results ((answer result))
    (cons (car answer) (cadr answer))))

(defun t4-relations-step-right (step)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal 2)))

(defun t4-relations-by-value-rewrite (proof step equality template)
  (proof-with-checked-results ((reversed (proof-proof-symmetric proof equality)))
    (proof-proof-rewrite-result proof step reversed template *proof-result*)))

(defun t4-relations-by-value-if (proof value template yes no)
  (proof-with-checked-results
      ((true-view (proof-proof-if-true proof value))
       (yes-proof (t4-relations-by-value-rewrite proof yes true-view template))
       (false-view (proof-proof-if-false proof value))
       (no-proof (t4-relations-by-value-rewrite proof no false-view template)))
    (proof-proof-cases proof (cadr value) yes-proof no-proof)))

(defun t4-relations-substitution (bindings)
  (if (endp bindings)
      nil
    (cons (cons (caar bindings) (cadar bindings))
          (t4-relations-substitution (cdr bindings)))))

(defun t4-relations-paired-view (lib call)
  (let ((proof (library-library-proof lib)))
    (if (or (not (proof-compound call))
            (not (equal (len call) 3))
            (not (assoc-equal (car call) (proof-proof-definitions proof))))
        nil
      (proof-with-checked-results
          ((opening (proof-proof-unfold proof call))
           (body (t4-relations-step-right opening)))
        (let* ((relation (car call))
               (x (cadr call))
               (y (caddr call))
               (a (list *proof-consp* x))
               (b (list *proof-consp* y)))
          (if (not (proof-is-call body *proof-if*))
              nil
            (proof-with-checked-results ((test (proof-term-at body 1)))
              (if (not (equal test (proof-ite a b *proof-false*)))
                  nil
                (proof-with-checked-results ((atoms (proof-term-at body 3)))
                  (let ((pairs (caddr body)))
                    (and (equal atoms (proof-ite (proof-neg a) (proof-neg b) *proof-false*))
                         (proof-is-call pairs *proof-if*)
                         (equal (cddr pairs)
                                (list (list relation (list *library-cdr* x)
                                            (list *library-cdr* y))
                                      *proof-false*))
                         (proof-compound (cadr pairs))
                         (equal (cdadr pairs) (list (list *library-car* x)
                                                     (list *library-car* y)))
                         opening)))))))))))

(defun t4-relations-paired-branch (lib opening left right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((body (if opening
                   (t4-relations-step-right opening)
                 '(:failure "failure" "")))
         (branches (proof-list-of-length (cdr body) 3))
         (reduced-test (proof-proof-select proof (car branches) left))
         (left-literal (proof-step-first left))
         (left-test (proof-term-at (car branches) 1)))
      (let ((test (car branches))
            (atoms (caddr branches)))
        (if (equal left-literal (proof-neg left-test))
            (proof-with-checked-results
                ((not-nil (proof-proof-not-nil proof))
                 (reverse-test (proof-proof-symmetric proof reduced-test))
                 (denied (proof-proof-rewrite proof not-nil reverse-test '(1 1)))
                 (selected (proof-proof-select proof body denied))
                 (atom-case (proof-proof-select proof atoms left)))
              (proof-proof-chain proof opening (list selected atom-case)))
          (proof-with-checked-results
              ((right-literal (if right
                                  (proof-step-first right)
                                '(:failure "failure" "")))
               (right-test (proof-term-at test 2))
               (reverse-test (proof-proof-symmetric proof reduced-test)))
            (let ((both-cons (equal right-literal right-test)))
              (proof-with-checked-results
                  ((test-proof (proof-proof-rewrite proof right reverse-test
                                                     (if both-cons '(1) '(1 1))))
                   (chosen (proof-proof-select proof body test-proof))
                   (selected (proof-proof-chain proof opening (list chosen))))
                (if both-cons
                    selected
                  (proof-with-checked-results
                      ((atom-test (proof-term-at atoms 1))
                       (left-is-cons (proof-proof-prove proof (proof-neg atom-test)
                                                       (list left) (list *proof-not*)))
                       (atom-case (proof-proof-select proof atoms left-is-cons)))
                    (proof-proof-chain proof selected (list atom-case))))))))))))

(defun t4-relations-any-compound (terms)
  (and (consp terms)
       (or (proof-compound (car terms))
           (t4-relations-any-compound (cdr terms)))))

(defun t4-relations-cdr-bindings (trail)
  (if (endp trail)
      nil
    (cons (list (car trail) (list *library-cdr* (car trail)))
          (t4-relations-cdr-bindings (cdr trail)))))

(defun t4-relations-list-equivalence-trail (goal guard)
  (let ((relation (car goal))
        (x (cadr goal))
        (z (caddr goal)))
    (cond ((and (eq guard :none) (equal x z)) (list x))
          ((equal guard (list relation z x)) (list z x))
          ((proof-is-call guard *proof-if*)
           (proof-with-checked-results ((otherwise (proof-term-at guard 3)))
             (if (not (and (equal otherwise *proof-false*)
                           (proof-is-call (cadr guard) relation)))
                 nil
               (proof-with-checked-results ((y (proof-term-at (cadr guard) 2)))
                 (and (equal (cadr guard) (list relation x y))
                      (equal (caddr guard) (list relation y z))
                      (not (proof-compound y))
                      (list x y z))))))
          (t nil))))

(defun t4-relations-shape (shapes arg)
  (let ((entry (assoc-equal arg shapes)))
    (if entry (cdr entry)
      '(:failure "missing-proof-input" ""))))

(defun t4-relations-infer-shape (lib premise equation left b)
  (let* ((proof (library-library-proof lib))
         (cons-test (list *proof-consp* b)))
    (proof-with-checked-results
        ((absent (proof-proof-assume proof cons-test nil))
         (branch (t4-relations-paired-branch lib equation left absent))
         (reduced (proof-proof-rewrite proof premise branch '(1)))
         (clash (proof-proof-tidy proof reduced)))
      (proof-proof-front proof clash cons-test))))

(defun t4-relations-list-equivalence-premises
    (premises lib positive shapes heads tails)
  (if (endp premises)
      (list shapes (reverse heads) (reverse tails))
    (let ((premise (car premises))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((literal (proof-step-first premise))
           (parts (proof-list-of-length literal 3))
           (equation (t4-relations-paired-view lib literal))
           (left (t4-relations-shape shapes (cadr parts))))
        (let* ((b (caddr parts))
               (known (assoc-equal b shapes)))
          (if positive
              (proof-with-checked-results
                  ((right (if known (cdr known)
                            (t4-relations-infer-shape lib premise equation left b)))
                   (branch (t4-relations-paired-branch lib equation left right))
                   (reduced (proof-proof-rewrite proof premise branch '(1)))
                   (conjuncts (proof-proof-conjunct proof reduced)))
                (t4-relations-list-equivalence-premises
                 (cdr premises) lib positive (if known shapes (table-put shapes b right))
                 (cons (car conjuncts) heads) (cons (cadr conjuncts) tails)))
            (proof-with-checked-results
                ((branch (t4-relations-paired-branch lib equation left nil))
                 (reduced (proof-proof-rewrite proof premise branch '(1))))
              (t4-relations-list-equivalence-premises
               (cdr premises) lib positive (if known shapes (table-put shapes b reduced))
               heads tails))))))))

(defun t4-relations-equivalence-head-goal (claim heads)
  (proof-with-checked-results ((goal (proof-term-at claim 1)))
    (if (endp heads)
        goal
      (proof-with-checked-results
          ((first (proof-step-first (car heads)))
           (test (if (endp (cdr heads))
                     first
                   (proof-with-checked-results ((second (proof-step-first (cadr heads))))
                     (proof-ite first second *proof-false*)))))
        (list *library-implies* test goal)))))

(defun t4-relations-list-equivalence-positive
    (selected guard heads tails guarded decrease smaller context)
  (t4-relations-with-results
      ((claim (t4-relations-step-right selected))
       (head-goal (t4-relations-equivalence-head-goal claim heads))
       (evidence (t4-structural-evidence-init (car context) nil nil))
       (answer (t4-relations-recipe-request context :fact-proof (list head-goal evidence))))
    (let* ((head (caar answer))
           (context (cdr answer))
           (proof (library-library-proof (car context))))
      (if (not head)
          '(:failure "search-miss" "")
        (proof-with-checked-results
            ((head-proof
              (if (endp heads)
                  head
                (proof-with-checked-results
                    ((antecedent (proof-proof-prove proof (cadr head-goal) heads nil)))
                  (proof-proof-modus-ponens proof head antecedent))))
             (hypothesis (proof-proof-assume proof guarded t))
             (tail (proof-proof-prove-if proof hypothesis decrease))
             (tail-proof
              (if (eq guard :none)
                  tail
                (proof-with-checked-results
                    ((condition (proof-term-at smaller 1))
                     (antecedent (proof-proof-prove proof condition tails nil)))
                  (proof-proof-modus-ponens proof tail antecedent))))
             (result (proof-proof-prove proof claim (list head-proof tail-proof) nil)))
          (cons result context))))))

(defun t4-relations-list-equivalence-branch
    (positive context opening x z guard obj cons-test decrease smaller guarded)
  (let* ((lib (car context))
         (proof (library-library-proof lib)))
    (t4-relations-with-results
        ((shape (proof-proof-assume proof cons-test positive))
         (premises
          (if (eq guard :none)
              nil
            (proof-with-checked-results ((guard-proof (proof-proof-assume proof guard t)))
              (if (proof-is-call guard *proof-if*)
                  (proof-proof-conjunct proof guard-proof)
                (list guard-proof)))))
         (known (t4-relations-list-equivalence-premises
                 premises lib positive (list (cons obj shape)) nil nil))
         (left (t4-relations-shape (car known) x))
         (right (and positive (t4-relations-shape (car known) z)))
         (selected (t4-relations-paired-branch lib opening left right))
         (result (t4-relations-shape (car known) z))
         (branch
          (if positive
              (t4-relations-list-equivalence-positive
               selected guard (cadr known) (caddr known) guarded decrease smaller context)
            (cons result context))))
      (let* ((context (cdr branch))
             (proof (library-library-proof (car context))))
        (proof-with-checked-results
            ((transported (proof-proof-transport proof (car branch) selected))
             (result (if (eq guard :none) transported
                       (t4-ordinals-ordinals-imply (car context) guard transported))))
          (cons result context))))))

(defun t4-relations-list-equivalence-query (lib formula replies)
  (let ((implies (proof-is-call formula *library-implies*)))
    (t4-relations-with-results
        ((parts (if implies (proof-list-of-length (cdr formula) 2)
                  (list :none formula)))
         (opening (t4-relations-paired-view lib (cadr parts))))
      (let* ((guard (car parts))
             (goal (cadr parts))
             (trail (and opening (not (t4-relations-any-compound (cdr goal)))
                         (t4-relations-list-equivalence-trail goal guard))))
        (t4-relations-with-results ((trail trail))
          (if (not trail)
              (cons nil lib)
            (let* ((x (cadr goal))
                   (z (caddr goal))
                   (obj (car trail))
                   (bindings (t4-relations-cdr-bindings (proof-unique trail)))
                   (cons-test (list *proof-consp* obj)))
              (t4-relations-with-results
                  ((decrease (library-library-builtin lib 3 obj))
                   (smaller (proof-subst formula (t4-relations-substitution bindings)))
                   (literal (proof-step-first decrease))
                   (guarded (proof-ite literal smaller *proof-true*))
                   (yes (t4-relations-list-equivalence-branch
                         t (cons lib replies) opening x z guard obj cons-test decrease smaller guarded))
                   (no (t4-relations-list-equivalence-branch
                        nil (cdr yes) opening x z guard obj cons-test decrease smaller guarded)))
                (let* ((lib (cadr no))
                       (proof (library-library-proof lib)))
                  (proof-with-checked-results
                      ((cases (proof-proof-cases proof cons-test (car yes) (car no)))
                       (ordinal (library-library-builtin lib 1 obj))
                       (step (proof-proof-induct proof ordinal cases formula
                                                 (t4-structural-count obj) (list bindings))))
                    (cons step lib)))))))))))

(mutual-recursion
 (defun t4-relations-paired-boolean-by-value
     (n value tests lib template x tail guarded decrease)
   (declare (xargs :measure (nfix n)))
   (let ((proof (library-library-proof lib)))
     (cond
      ((zp n) '(:failure "fuel" "t4-relations-paired-boolean-by-value"))
      ((proof-is-call value *proof-if*)
       (proof-with-checked-results
           ((parts (proof-list-of-length (cdr value) 3))
            (yes (t4-relations-paired-boolean-by-value
                  (1- n) (cadr parts) (append tests (list (list (car parts) t)))
                  lib template x tail guarded decrease))
            (no (t4-relations-paired-boolean-by-value
                 (1- n) (caddr parts) (append tests (list (list (car parts) nil)))
                 lib template x tail guarded decrease)))
         (t4-relations-by-value-if proof value template yes no)))
      ((and (proof-compound value) (not (consp value)))
       (proof-term-at value 0))
      ((and (proof-compound value) (proof-compound (car value)))
       (proof-with-checked-results
           ((equality (proof-proof-beta proof value))
            (opened (t4-relations-step-right equality))
            (step (t4-relations-paired-boolean-by-value
                   (1- n) opened tests lib template x tail guarded decrease)))
         (t4-relations-by-value-rewrite proof step equality template)))
      (t (proof-with-checked-results
             ((step (t4-relations-paired-boolean-leaf
                     (1- n) value tests lib template x tail guarded decrease))
              (literal (proof-step-first step))
              (expected (proof-subst template (list (cons *proof-result* value)))))
           (if (equal literal expected) step '(:failure "inference-mismatch" "")))))))

 (defun t4-relations-paired-boolean-leaf
     (n value tests lib template x tail guarded decrease)
   (declare (xargs :measure (nfix n)))
   (let ((proof (library-library-proof lib)))
     (cond
      ((zp n) '(:failure "fuel" "t4-relations-paired-boolean-leaf"))
      ((or (equal value *proof-true*) (equal value *proof-false*))
       (proof-proof-prove proof (list *t4-relations-booleanp* value) nil
                          (list *t4-relations-booleanp* (proof-cl "EQ"))))
      ((proof-is-call value *proof-not*)
       (proof-with-checked-results
           ((view (proof-proof-unfold proof value))
            (opened (t4-relations-step-right view))
            (step (t4-relations-paired-boolean-by-value
                   (1- n) opened tests lib template x tail guarded decrease)))
         (t4-relations-by-value-rewrite proof step view template)))
      ((equal value tail)
       (proof-with-checked-results
           ((evidence (t4-structural-evidence-init lib tests nil))
            (known (t4-structural-evidence-find evidence (list *proof-consp* x)))
            (hypothesis (proof-proof-assume proof guarded t))
            (smaller (if (car known) (proof-proof-discharge proof decrease (car known))
                       '(:failure "failure" ""))))
         (proof-proof-prove-if proof hypothesis smaller)))
      (t '(:failure "search-miss" ""))))))

(defun t4-relations-paired-boolean (lib formula opening)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((call (proof-term-at formula 1))
         (objects (proof-list-of-length (cdr call) 2)))
      (let* ((x (car objects))
             (bindings (t4-relations-cdr-bindings (proof-unique objects)))
             (template (list *t4-relations-booleanp* *proof-result*)))
        (proof-with-checked-results
            ((tail (proof-subst call (t4-relations-substitution bindings)))
             (decrease (library-library-builtin lib 3 x))
             (literal (proof-step-first decrease))
             (guarded (proof-ite literal (list *t4-relations-booleanp* tail) *proof-true*))
             (value (t4-relations-step-right opening))
             (step (t4-relations-paired-boolean-by-value
                    1000000 value nil lib template x tail guarded decrease))
             (proved (t4-relations-by-value-rewrite proof step opening template))
             (ordinal (library-library-builtin lib 1 x)))
          (proof-proof-induct proof ordinal proved formula
                              (t4-structural-count x) (list bindings)))))))

(defun t4-relations-equivalence-conjunction-combine (n claim context)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "t4-relations-equivalence-conjunction-combine"))
   (t
    (t4-relations-with-results
        ((otherwise (and (proof-is-call claim *proof-if*) (proof-term-at claim 3))))
      (if (equal otherwise *proof-false*)
          (t4-relations-with-results
              ((yes (t4-relations-equivalence-conjunction-combine (1- n) (cadr claim) context))
               (no (t4-relations-equivalence-conjunction-combine (1- n) (caddr claim) (cdr yes)))
               (step (proof-proof-prove (library-library-proof (cadr no))
                                        claim (list (car yes) (car no)) nil)))
            (cons step (cdr no)))
        (t4-relations-with-results
            ((evidence (t4-structural-evidence-init (car context) nil nil))
             (fact (t4-relations-recipe-request context :fact-proof (list claim evidence))))
          (if (caar fact)
              (cons (caar fact) (cdr fact))
            '(:failure "search-miss" ""))))))))

(defun t4-relations-equivalence-conjunction-query (lib formula replies)
  (t4-relations-with-results
      ((otherwise (and (proof-is-call formula *proof-if*) (proof-term-at formula 3))))
    (if (not (and (equal otherwise *proof-false*)
                  (proof-is-call (cadr formula) *t4-relations-booleanp*)))
        (cons nil lib)
      (t4-relations-with-results
          ((goal (proof-term-at (cadr formula) 1))
           (opening (t4-relations-paired-view lib goal)))
        (if (or (not opening) (t4-relations-any-compound (cdr goal)))
            (cons nil lib)
          (t4-relations-with-results
              ((laws (t4-relations-equivalence-conjunction-combine
                      1000000 (caddr formula) (cons lib replies)))
               (boolean (t4-relations-paired-boolean (cadr laws) (cadr formula) opening)))
            (let ((lib (cadr laws)))
              (proof-with-checked-results
                  ((step (proof-proof-prove (library-library-proof lib)
                                            formula (list boolean (car laws)) nil)))
                (cons step lib)))))))))

(defun t4-relations-query (recipe lib formula replies)
  (case recipe
    (:list-equivalence (t4-relations-list-equivalence-query lib formula replies))
    (:equivalence-conjunction (t4-relations-equivalence-conjunction-query lib formula replies))
    (otherwise '(:failure "search-miss" ""))))
