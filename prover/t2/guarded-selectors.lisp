(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t2-guarded-selectors-selectors* (list *library-car* *library-cdr*))

(defun t2-guarded-selectors-arithmetic-p (lib)
  (eq (proof-proof-kind (descent-proof lib)) :slice))

; Arithmetic uses the base constant rule and cites its reflexivity lemma.
(mutual-recursion
 (defun t2-guarded-selectors-simplify-term (n proof term evidence definitions)
   (declare (xargs :measure (nfix n)))
   (let ((head (proof-datum-head term)))
     (cond
      ((not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t2-guarded-selectors-simplify-term"))
      ((or (not (proof-compound term)) (equal head *proof-quote*)) nil)
      ((endp term) '(:failure "missing-term-part" ""))
      ((or (proof-compound head) (member-equal head definitions))
       (proof-with-checked-results
        ((expansion (proof-simplify-expansion proof term))
         (next (t2-guarded-selectors-simplify-term (1- n) proof (cadr expansion) evidence definitions)))
        (proof-proof-chain proof (car expansion) (list next))))
      ((equal head *proof-if*)
       (proof-with-checked-results
        ((test (proof-term-at term 1))
         (first (t2-guarded-selectors-simplify-term (1- n) proof test evidence definitions))
         (path (proof-simplify-if-path proof term first evidence)))
        (if (eq (car path) :simplify)
            (proof-with-checked-results
             ((next (t2-guarded-selectors-simplify-term (1- n) proof (caddr path) evidence definitions)))
             (proof-proof-chain proof (cadr path) (list next)))
          path)))
      (t (proof-with-checked-results
          ((result (t2-guarded-selectors-simplify-arguments
                    (1- n) proof term (cdr term) 1 nil evidence definitions))
           (current (if result (proof-rewritten-term result) term))
           (constant (proof-proof-constant-base proof current)))
          (cond ((not constant) result)
                (result (proof-proof-chain proof result (list constant)))
                (t constant)))))))
 (defun t2-guarded-selectors-simplify-arguments (n proof term args index result evidence definitions)
   (declare (xargs :measure (nfix n)))
   (cond ((not (o< (nfix (1- n)) (nfix n)))
          '(:failure "fuel" "t2-guarded-selectors-simplify-arguments"))
         ((endp args) result)
         (t (proof-with-checked-results
             ((equality (t2-guarded-selectors-simplify-term (1- n) proof (car args) evidence definitions))
              (next (proof-simplify-argument-result proof term index result equality)))
             (t2-guarded-selectors-simplify-arguments
              (1- n) proof term (cdr args) (1+ index) next evidence definitions))))))

(defun t2-guarded-selectors-simplify (proof term evidence definitions)
  (t2-guarded-selectors-simplify-term 1000000 proof term evidence definitions))

(defun t2-guarded-selectors-simplify-first (proof step evidence definitions)
  (proof-with-checked-results
   ((literal (proof-step-first step))
    (equation (t2-guarded-selectors-simplify proof literal evidence definitions)))
   (if equation
       (proof-with-checked-results ((rewritten (proof-proof-rewrite proof step equation '(1))))
         (proof-proof-tidy proof rewritten))
     step)))

(defun t2-guarded-selectors-prove-visit (n proof term evidence definitions)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t2-guarded-selectors-prove-visit"))
   ((equal term *proof-true*)
    (let ((name (proof-sym "SELF-TRUE" "ACL2")))
      (if (and (eq (proof-proof-kind proof) :slice) (assoc-equal name (proof-proof-facts proof)))
          (proof-proof-fact proof name nil)
        (proof-proof-prove proof term evidence definitions))))
   (t (proof-with-checked-results ((premise (proof-find-evidence evidence (list term))))
        (if premise
            premise
          (proof-with-checked-results
           ((equation (t2-guarded-selectors-simplify proof term evidence definitions))
            (right (and equation (proof-rewritten-term equation))))
           (cond ((or (not equation) (equal right term)) (proof-prove-unproved-term term))
                 ((equal right *proof-true*) (proof-proof-true-from-eq proof equation))
                 (t (proof-with-checked-results
                     ((step (t2-guarded-selectors-prove-visit (1- n) proof right evidence definitions)))
                     (proof-proof-transport proof step equation))))))))))

(defun t2-guarded-selectors-library-prove (lib term evidence definitions)
  (t2-guarded-selectors-prove-visit 1000000 (descent-proof lib) term evidence definitions))

(mutual-recursion
 (defun t2-guarded-selectors-library-natural (lib term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (t2-guarded-selectors-arithmetic-p lib)) (library-library-natural lib term))
    ((proof-is-call term (proof-sym "NFIX" "ACL2"))
     (proof-with-checked-results
      ((natural (library-library-cite lib "NFIX-NATURAL" (cdr term) nil))
       (identity (library-library-cite lib "LIBRARY-NFIX" (cdr term) nil)))
      (library-library-transport-argument lib natural identity 1)))
    ((proof-is-call term (proof-cl "LENGTH"))
     (library-library-cite lib "LENGTH-NATURAL" (cdr term) nil))
    ((proof-is-call term *proof-plus*)
     (proof-with-checked-results ((steps (t2-guarded-selectors-natural-arguments lib (cdr term))))
       (library-library-cite lib "NATURAL-SUM" (cdr term) steps)))
    ((proof-is-call term *library-count*)
     (library-library-cite lib "COUNT-NATURAL" (cdr term) nil))
    ((proof-is-call term *library-len*)
     (library-library-cite lib "LEN-NATURAL" (cdr term) nil))
    (t (t2-guarded-selectors-library-prove lib (list *library-natp* term) nil
                                          (list *library-natp* *proof-not*)))))
 (defun t2-guarded-selectors-natural-arguments (lib terms)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (proof-with-checked-results
      ((first (t2-guarded-selectors-library-natural lib (car terms)))
       (rest (t2-guarded-selectors-natural-arguments lib (cdr terms))))
      (cons first rest)))))

(mutual-recursion
 (defun t2-guarded-selectors-library-type-of (lib term evidence)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (t2-guarded-selectors-arithmetic-p lib)) (library-library-type-of lib term evidence))
    ((or (proof-is-call term (proof-sym "NFIX" "ACL2"))
         (proof-is-call term (proof-cl "LENGTH")))
     (proof-with-checked-results ((natural (t2-guarded-selectors-library-natural lib term)))
       (library-library-cite lib "NATURAL-INTEGER" (list term) (list natural))))
    ((proof-is-call term (proof-sym "IFIX" "ACL2"))
     (library-library-cite lib "IFIX-INTEGER" (cdr term) nil))
    (t (proof-with-checked-results ((premise (library-type-evidence (library-integer term) evidence)))
         (cond
          (premise premise)
          ((or (proof-is-call term *proof-plus*) (proof-is-call term *proof-times*))
           (proof-with-checked-results ((steps (t2-guarded-selectors-type-arguments lib (cdr term) evidence)))
             (library-library-cite lib
              (if (equal (car term) *proof-plus*) "INTEGER-SUM" "INTEGER-PRODUCT")
              (cdr term) steps)))
          ((proof-is-call term *proof-minus*)
           (if (endp (cdr term))
               '(:failure "missing-term-part" "")
             (proof-with-checked-results
              ((step (t2-guarded-selectors-library-type-of lib (cadr term) evidence)))
              (library-library-cite lib "INTEGER-NEGATION" (cdr term) (list step)))))
          (t (library-library-type-of lib term nil)))))))
 (defun t2-guarded-selectors-type-arguments (lib terms evidence)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (proof-with-checked-results
      ((first (t2-guarded-selectors-library-type-of lib (car terms) evidence))
       (rest (t2-guarded-selectors-type-arguments lib (cdr terms) evidence)))
      (cons first rest)))))

(defun t2-guarded-selectors-library-compare-chain (lib left right)
  (if (not (t2-guarded-selectors-arithmetic-p lib))
      (library-library-compare-chain lib left right)
    (proof-with-checked-results
     ((p (proof-step-first left)) (q (proof-step-first right))
      (p-strict (proof-is-call p *proof-less*)) (q-strict (proof-is-call q *proof-less*))
      (p-args (library-compare-chain-arguments p p-strict))
      (q-args (library-compare-chain-arguments q q-strict)))
     (let ((a (car p-args)) (b (cadr p-args)) (c (cadr q-args)))
       (if (not (equal b (car q-args)))
           '(:failure "recipe-mismatch" "")
         (proof-with-checked-results
          ((types (t2-guarded-selectors-type-arguments lib (list a b c) nil)))
          (library-library-cite lib
           (cond ((and p-strict q-strict) "LESS-TRANSITIVE")
                 (p-strict "LESS-THEN-WEAK")
                 (q-strict "WEAK-THEN-LESS")
                 (t "WEAK-TRANSITIVE"))
           (list a b c) (append types (list left right)))))))))

(defun t2-guarded-selectors-library-ordinal-comparison (lib a b)
  (proof-with-checked-results
   ((a-type (t2-guarded-selectors-library-type-of lib a nil))
    (b-type (t2-guarded-selectors-library-type-of lib b nil)))
   (library-library-cite lib "FINITE-ORDER" (list a b) (list a-type b-type))))

(defun t2-guarded-selectors-selector-call-p (term)
  (or (proof-is-call term *library-car*) (proof-is-call term *library-cdr*)))

(defun t2-guarded-selectors-path-end (term)
  (declare (xargs :measure (acl2-count term)))
  (cond ((not (t2-guarded-selectors-selector-call-p term)) term)
        ((endp (cdr term)) '(:failure "missing-term-part" ""))
        (t (t2-guarded-selectors-path-end (cadr term)))))

(defun t2-guarded-selectors-selector-path (term source)
  (and (t2-guarded-selectors-selector-call-p term)
       (proof-with-checked-results ((end (t2-guarded-selectors-path-end term)))
         (equal end source))))

(mutual-recursion
 (defun t2-guarded-selectors-selector-tree (term source)
   (declare (xargs :measure (acl2-count term)))
   (if (proof-is-call term *proof-if*)
       (t2-guarded-selectors-selector-branches (cddr term) source)
     (or (equal term *proof-false*) (t2-guarded-selectors-selector-path term source))))
 (defun t2-guarded-selectors-selector-branches (branches source)
   (declare (xargs :measure (acl2-count branches)))
   (if (endp branches)
       t
     (proof-with-checked-results
      ((branch (t2-guarded-selectors-selector-tree (car branches) source)))
      (and branch (t2-guarded-selectors-selector-branches (cdr branches) source))))))

(defun t2-guarded-selectors-guarded-selector (lib term source)
  (and (proof-compound term)
       (let ((proof (library-library-proof lib)))
         (proof-with-checked-results ((head (proof-term-at term 0)))
           (and (assoc-equal head (proof-proof-definitions proof))
                (proof-with-checked-results
                 ((equation (proof-proof-unfold proof term))
                  (body (proof-rewritten-term equation))
                  (simple (t2-guarded-selectors-simplify proof body nil (list *termination-return-last*)))
                  (equation (proof-proof-chain proof equation (list simple)))
                  (body (proof-rewritten-term equation))
                  (valid (t2-guarded-selectors-selector-tree body source)))
                 (and valid equation)))))))

(defun t2-guarded-selectors-nonempty-case (lib equality position term quoted)
  (and (proof-is-call quoted *proof-quote*)
       (not (equal quoted *proof-false*))
       (proof-compound term)
       (equal (len term) 2)
       (let* ((proof (library-library-proof lib))
              (source (cadr term))
              (cons-test (list *proof-consp* source)))
         (proof-with-checked-results
          ((atom-step (proof-proof-assume proof cons-test nil))
           (nil-case
            (if (member-equal (car term) *t2-guarded-selectors-selectors*)
                (proof-with-checked-results
                 ((law (library-library-axiom lib
                         (concatenate 'string "COMPLETION-OF-" (caddar term)) (list source)))
                  (body (proof-rewritten-term law))
                  (selected (proof-proof-select proof body atom-step)))
                 (proof-proof-chain proof law (list selected)))
              (proof-with-checked-results
               ((guarded (t2-guarded-selectors-guarded-selector lib term source)))
               (and guarded (t2-guarded-selectors-simplify proof term (list atom-step)
                                                           (list (car term) *termination-return-last*))))))
           (value (and nil-case (proof-rewritten-term nil-case))))
          (and nil-case (equal value *proof-false*)
               (proof-with-checked-results
                ((contradiction (proof-proof-rewrite proof equality nil-case (list 1 position)))
                 (simplified (t2-guarded-selectors-simplify-first proof contradiction nil nil)))
                (proof-proof-front proof simplified cons-test)))))))

(defun t2-guarded-selectors-nonempty-source (lib equality)
  (proof-with-checked-results
   ((literal (proof-step-first equality))
    (parts (proof-list-of-length literal 3))
    (left (t2-guarded-selectors-nonempty-case lib equality 1 (cadr parts) (caddr parts))))
   (or left (t2-guarded-selectors-nonempty-case lib equality 2 (caddr parts) (cadr parts)))))

(defun t2-guarded-selectors-library-conjunct (lib step)
  (let ((proof (descent-proof lib)))
    (if (not (t2-guarded-selectors-arithmetic-p lib))
        (proof-proof-conjunct proof step)
      (proof-with-checked-results
       ((literal (proof-step-first step))
        (no (proof-term-at literal 3)))
       (if (not (equal no *proof-false*))
           '(:failure "recipe-mismatch" "")
         (let* ((arguments (list (cadr literal) (caddr literal)))
                (bindings (seq-zip (list *library-x* *library-y*) arguments)))
           (proof-with-checked-results
            ((first (proof-proof-use proof (proof-sym "SELF-CONJUNCTION-FIRST" "ACL2")
                                     bindings (list step)))
             (second (proof-proof-use proof (proof-sym "SELF-CONJUNCTION-SECOND" "ACL2")
                                      bindings (list step))))
            (list first second))))))))

(defun t2-guarded-selectors-ruler-p (context)
  (eq (car context) :t2-ruler-facts))

(defun t2-guarded-selectors-context-hypotheses (context)
  (if (t2-guarded-selectors-ruler-p context) (cadr context) context))

(defun t2-guarded-selectors-context-from-hypotheses (hypotheses derived)
  (list :t2-ruler-facts hypotheses derived))

(defun t2-guarded-selectors-context-derived (context)
  (and (t2-guarded-selectors-ruler-p context) (caddr context)))

(defun t2-guarded-selectors-context-with-hypotheses (context hypotheses)
  (if (t2-guarded-selectors-ruler-p context)
      (t2-guarded-selectors-context-from-hypotheses
       hypotheses (t2-guarded-selectors-context-derived context))
    hypotheses))

(defun t2-guarded-selectors-context-init (lib tests extra ruler-facts)
  (proof-with-checked-results ((hypotheses (descent-hypotheses-init lib tests extra)))
    (if ruler-facts
        (t2-guarded-selectors-context-from-hypotheses hypotheses nil)
      hypotheses)))

(defun t2-guarded-selectors-context-with-library (context lib)
  (t2-guarded-selectors-context-with-hypotheses
   context (descent-hypotheses-with-proof (t2-guarded-selectors-context-hypotheses context) lib)))

(defun t2-guarded-selectors-remember (hypotheses term step overwrite)
  (let ((found (descent-hypotheses-found hypotheses)))
    (if (or overwrite (not (assoc-equal term found)))
        (descent-hypotheses-with-found hypotheses (table-put found term step))
      hypotheses)))

(defun t2-guarded-selectors-find-conjunct (prefix tail term step lib hypotheses)
  (if (endp prefix)
      (let ((next (t2-guarded-selectors-remember hypotheses tail step nil)))
        (cons (table-get (descent-hypotheses-found next) term nil) next))
    (proof-with-checked-results ((parts (t2-guarded-selectors-library-conjunct lib step)))
      (let* ((literal (car prefix))
             (next (t2-guarded-selectors-remember hypotheses literal (car parts) nil)))
        (if (equal term literal)
            (cons (table-get (descent-hypotheses-found next) term nil) next)
          (t2-guarded-selectors-find-conjunct (cdr prefix) tail term (cadr parts) lib next))))))

(defun t2-guarded-selectors-find-tests (tests term lib hypotheses)
  (if (endp tests)
      (cons nil hypotheses)
    (let ((proof (descent-proof lib)))
      (proof-with-checked-results ((test (proof-list-of-length (car tests) 2)))
        (let ((literal (car test))
              (holds (cadr test)))
          (cond ((equal term (if holds literal (proof-neg literal)))
                 (proof-with-checked-results ((step (proof-proof-assume proof literal holds)))
                   (cons step (t2-guarded-selectors-remember hypotheses term step t))))
                ((not holds)
                 (t2-guarded-selectors-find-tests (cdr tests) term lib hypotheses))
                (t (proof-with-checked-results ((parts (descent-conjuncts literal nil)))
                     (if (or (member-equal term (car parts)) (equal term (cdr parts)))
                         (proof-with-checked-results
                          ((step (proof-proof-assume proof literal t)))
                          (t2-guarded-selectors-find-conjunct
                           (car parts) (cdr parts) term step lib hypotheses))
                       (t2-guarded-selectors-find-tests (cdr tests) term lib hypotheses))))))))))

(defconst *t2-guarded-selectors-test-definitions*
  (list *termination-return-last* (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "NULL")
        (proof-cl "EQ") (proof-cl "EQL") (proof-cl "=") (proof-sym "ZP" "ACL2")
        (proof-sym "ZIP" "ACL2") (proof-sym "POSP" "ACL2") *library-natp*))

(defun t2-guarded-selectors-context-learn-extra (context step)
  (let* ((hypotheses (t2-guarded-selectors-context-hypotheses context))
         (lib (descent-hypotheses-proof hypotheses)))
    (proof-with-checked-results
     ((next (descent-hypotheses-init
             lib (descent-hypotheses-tests hypotheses)
             (append (table-values (descent-hypotheses-extra hypotheses)) (list step)))))
     (t2-guarded-selectors-context-with-hypotheses
      context (descent-hypotheses-with-found next (descent-hypotheses-found hypotheses))))))

(mutual-recursion
 (defun t2-guarded-selectors-context-learn (n context step)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t2-guarded-selectors-context-learn")
     (let* ((hypotheses (t2-guarded-selectors-context-hypotheses context))
            (lib (descent-hypotheses-proof hypotheses))
            (proof (descent-proof lib)))
       (proof-with-checked-results ((literal (proof-step-first step)))
         (if (assoc-equal literal (descent-hypotheses-extra hypotheses))
             context
           (proof-with-checked-results
            ((context (t2-guarded-selectors-context-learn-extra context step))
             (holds (not (proof-is-call literal *proof-not*)))
             (test (if holds literal (proof-term-at literal 1))))
            (cond
             ((proof-is-call test *proof-not*)
              (proof-with-checked-results
               ((inner (proof-term-at test 1))
                (assumption (proof-proof-assume proof inner nil))
                (joined (proof-proof-cut proof assumption step))
                (derived (proof-proof-front proof joined inner)))
               (t2-guarded-selectors-context-learn (1- n) context derived)))
             ((proof-is-call test *proof-if*)
              (proof-with-checked-results ((parts (proof-list-of-length (cdr test) 3)))
                (let ((condition (car parts)) (yes (cadr parts)) (no (caddr parts)))
                  (cond
                   ((and holds (equal no *proof-false*))
                    (proof-with-checked-results
                     ((parts (t2-guarded-selectors-library-conjunct lib step)))
                     (t2-guarded-selectors-context-learn-steps (1- n) context parts)))
                   ((and (not holds) (or (equal yes condition) (equal yes *proof-true*)))
                    (proof-with-checked-results
                     ((selected (proof-proof-if-true proof test))
                      (branch (if (equal yes *proof-true*)
                                  (t2-guarded-selectors-library-prove lib *proof-true* nil nil)
                                (proof-proof-assume proof condition t)))
                      (when-true (proof-proof-transport proof branch selected))
                      (cut (proof-proof-cut proof when-true step))
                      (false-test (proof-proof-front proof cut (proof-neg condition)))
                      (context (t2-guarded-selectors-context-learn (1- n) context false-test))
                      (selection (proof-proof-select proof test false-test))
                      (rewritten (proof-proof-rewrite proof step selection '(1 1)))
                      (result (proof-proof-tidy proof rewritten)))
                     (t2-guarded-selectors-context-learn (1- n) context result)))
                   ((and (not holds) (equal no *proof-true*))
                    (proof-with-checked-results
                     ((truth (t2-guarded-selectors-library-prove lib *proof-true* nil nil))
                      (selected (proof-proof-if-false proof test))
                      (when-false (proof-proof-transport proof truth selected))
                      (cut (proof-proof-cut proof when-false step))
                      (true-test (proof-proof-front proof cut condition))
                      (context (t2-guarded-selectors-context-learn (1- n) context true-test))
                      (selection (proof-proof-select proof test true-test))
                      (rewritten (proof-proof-rewrite proof step selection '(1 1)))
                      (result (proof-proof-tidy proof rewritten)))
                     (t2-guarded-selectors-context-learn (1- n) context result)))
                   (t context)))))
             ((and (proof-compound test) (member-equal (car test) *t2-guarded-selectors-test-definitions*))
              (proof-with-checked-results
               ((equation (proof-proof-unfold proof test))
                (rewritten (proof-proof-rewrite proof step equation (if holds '(1) '(1 1))))
                (result (proof-proof-tidy proof rewritten)))
               (t2-guarded-selectors-context-learn (1- n) context result)))
             ((and (not holds) (proof-is-call test *proof-equal*))
              (proof-with-checked-results ((right (proof-term-at test 2)))
                (if (not (equal right *proof-false*))
                    context
                  (proof-with-checked-results
                   ((left (proof-term-at test 1))
                    (nil-test (proof-proof-nil-or-true proof left))
                    (cut (proof-proof-cut proof nil-test step))
                    (result (proof-proof-front proof cut left)))
                   (t2-guarded-selectors-context-learn (1- n) context result)))))
             ((and holds (proof-is-call test *proof-equal*))
              (proof-with-checked-results ((cons-step (t2-guarded-selectors-nonempty-source lib step)))
                (if cons-step
                    (t2-guarded-selectors-context-learn (1- n) context cons-step)
                  context)))
             ((and holds (proof-is-call test *proof-consp*))
              (proof-with-checked-results
               ((argument (proof-term-at test 1))
                (nil-test (proof-proof-nil-or-true proof argument))
                (rewritten (proof-proof-rewrite proof step nil-test '(1 1)))
                (simplified (t2-guarded-selectors-simplify-first proof rewritten nil nil))
                (result (proof-proof-front proof simplified argument)))
               (t2-guarded-selectors-context-learn (1- n) context result)))
             ((and holds (t2-guarded-selectors-selector-call-p test))
              (proof-with-checked-results
               ((base (proof-term-at test 1))
                (completion (library-library-axiom lib
                              (concatenate 'string "COMPLETION-OF-" (caddar test)) (list base)))
                (body (proof-rewritten-term completion))
                (selection (proof-proof-if-false proof body))
                (atom-value (proof-proof-chain proof completion (list selection)))
                (rewritten (proof-proof-rewrite proof step atom-value '(1)))
                (tidied (proof-proof-tidy proof rewritten))
                (result (proof-proof-front proof tidied (list *proof-consp* base))))
               (t2-guarded-selectors-context-learn (1- n) context result)))
             (t context))))))))
 (defun t2-guarded-selectors-context-learn-steps (n context steps)
   (declare (xargs :measure (nfix n)))
   (cond ((endp steps) context)
         ((not (o< (nfix (1- n)) (nfix n)))
          '(:failure "fuel" "t2-guarded-selectors-context-learn-steps"))
         (t (proof-with-checked-results
             ((context (t2-guarded-selectors-context-learn (1- n) context (car steps))))
             (t2-guarded-selectors-context-learn-steps (1- n) context (cdr steps)))))))

(defun t2-guarded-selectors-context-learn-step (context step)
  (t2-guarded-selectors-context-learn 1000000 context step))

(defun t2-guarded-selectors-context-learn-tests (tests context proof)
  (if (endp tests)
      context
    (proof-with-checked-results
     ((parts (proof-list-of-length (car tests) 2))
      (step (proof-proof-assume proof (car parts) (cadr parts)))
      (context (t2-guarded-selectors-context-learn 1000000 context step)))
     (t2-guarded-selectors-context-learn-tests (cdr tests) context proof))))

(defun t2-guarded-selectors-context-premises (context)
  (let ((hypotheses (t2-guarded-selectors-context-hypotheses context)))
    (proof-with-checked-results
     ((context (if (and (t2-guarded-selectors-ruler-p context)
                        (not (t2-guarded-selectors-context-derived context)))
                   (t2-guarded-selectors-context-learn-tests
                    (descent-hypotheses-tests hypotheses)
                    (t2-guarded-selectors-context-from-hypotheses hypotheses t)
                    (descent-proof (descent-hypotheses-proof hypotheses)))
                 context)))
     (cons (table-values (descent-hypotheses-extra
                           (t2-guarded-selectors-context-hypotheses context)))
           context))))

(defun t2-guarded-selectors-context-find (context term)
  (let* ((hypotheses (t2-guarded-selectors-context-hypotheses context))
         (existing (or (assoc-equal term (descent-hypotheses-extra hypotheses))
                       (assoc-equal term (descent-hypotheses-found hypotheses)))))
    (if existing
        (cons (cdr existing) context)
      (proof-with-checked-results
       ((found (t2-guarded-selectors-find-tests (descent-hypotheses-tests hypotheses) term
                                               (descent-hypotheses-proof hypotheses) hypotheses))
        (context (t2-guarded-selectors-context-with-hypotheses context (cdr found))))
       (if (or (car found) (not (t2-guarded-selectors-ruler-p context)))
           (cons (car found) context)
         (proof-with-checked-results ((premises (t2-guarded-selectors-context-premises context)))
           (let ((extra (descent-hypotheses-extra
                         (t2-guarded-selectors-context-hypotheses (cdr premises)))))
             (cons (table-get extra term nil) (cdr premises)))))))))

(defun t2-guarded-selectors-context-require (context term)
  (proof-with-checked-results ((found (t2-guarded-selectors-context-find context term)))
    (if (car found) found (descent-missing-hypothesis term))))

(defun t2-guarded-selectors-selector-chain-steps (edges lib step context)
  (if (endp edges)
      (proof-with-checked-results ((first (proof-step-first step)) (head (proof-term-at first 0)))
        (if (equal head *proof-less*)
            (cons step context)
          '(:failure "recipe-mismatch" "")))
    (let* ((edge (car edges)) (head (car edge)) (base (cadr edge)))
      (proof-with-checked-results
       ((evidence (t2-guarded-selectors-context-find context (list *proof-consp* base)))
        (bound (descent-selector-edge lib head base (car evidence)))
        (combined (if step (t2-guarded-selectors-library-compare-chain lib bound step) bound)))
       (t2-guarded-selectors-selector-chain-steps (cdr edges) lib combined (cdr evidence))))))

(defun t2-guarded-selectors-selector-step (lib actual parent context)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((head (proof-term-at actual 0))
      (selector (member-equal head *t2-guarded-selectors-selectors*))
      (argument (and selector (proof-term-at actual 1)))
      (base (proof-term-at parent 1)))
     (if (and selector (equal argument base))
         (proof-with-checked-results
          ((structural (library-library-builtin lib (if (equal head *library-car*) 2 3) base))
           (evidence (t2-guarded-selectors-context-require context (list *proof-consp* base)))
           (step (proof-proof-discharge proof structural (car evidence))))
          (cons step (cdr evidence)))
       (proof-with-checked-results ((edges (descent-selector-chain-edges actual base nil)))
         (if (not edges)
             (proof-with-checked-results ((text (proof-write base)))
               '(:failure "recipe-mismatch" ""))
           (proof-with-checked-results
            ((decrease (t2-guarded-selectors-selector-chain-steps edges lib nil context))
             (order (t2-guarded-selectors-library-ordinal-comparison lib (list *library-count* actual) parent))
             (step (proof-proof-transport proof (car decrease) order)))
            (cons step (cdr decrease)))))))))

(defun t2-guarded-selectors-context-selector-decrease (lib goal context)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length goal 3))
      (child-head (proof-term-at (cadr parts) 0))
      (parent-head (and (equal child-head *library-count*) (proof-term-at (caddr parts) 0))))
     (if (not (equal parent-head *library-count*))
         '(:failure "recipe-mismatch" "")
       (proof-with-checked-results
        ((raw (proof-term-at (cadr parts) 1))
         (opened (t2-guarded-selectors-simplify proof raw nil (list *termination-return-last*)))
         (actual (if opened (proof-rewritten-term opened) raw))
         (result (t2-guarded-selectors-selector-step lib actual (caddr parts) context)))
        (if (not opened)
            result
          (proof-with-checked-results
           ((reversed (proof-proof-symmetric proof opened))
            (rewritten (proof-proof-rewrite proof (car result) reversed '(1 1 1)))
            (step (proof-proof-tidy proof rewritten)))
           (cons step (cdr result)))))))))

(defun t2-guarded-selectors-nil-descent (lib parent cons-step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((argument (proof-term-at parent 1))
      (tail (list *library-count* (list *library-cdr* argument)))
      (builtin (library-library-builtin lib 3 argument))
      (decreased (proof-proof-discharge proof builtin cons-step))
      (comparison (t2-guarded-selectors-library-ordinal-comparison lib tail parent))
      (order (proof-proof-rewrite proof decreased comparison '(1)))
      (natural (t2-guarded-selectors-library-natural lib tail))
      (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE" (list tail) (list natural)))
      (result (t2-guarded-selectors-library-compare-chain lib nonnegative order))
      (base (list *library-count* *proof-false*))
      (simplified (t2-guarded-selectors-simplify proof base nil (list *library-count*)))
      (result (library-library-transport-argument lib result simplified 1))
      (comparison (t2-guarded-selectors-library-ordinal-comparison lib base parent)))
     (proof-proof-transport proof result comparison))))

(defun t2-guarded-selectors-guarded-decrease-leaf (term tests lib parent hypotheses)
  (let ((base (t2-guarded-selectors-context-hypotheses hypotheses)))
    (proof-with-checked-results
     ((all-tests (append (descent-hypotheses-tests base) tests))
      (premises (if (t2-guarded-selectors-ruler-p hypotheses)
                    (t2-guarded-selectors-context-premises hypotheses)
                  '(:failure "failure" "")))
      (context (t2-guarded-selectors-context-init
                lib all-tests (car premises) (t2-guarded-selectors-ruler-p hypotheses)))
      (result
       (if (equal term *proof-false*)
           (proof-with-checked-results
            ((argument (proof-term-at parent 1))
             (evidence (t2-guarded-selectors-context-require context (list *proof-consp* argument))))
            (t2-guarded-selectors-nil-descent lib parent (car evidence)))
         (proof-with-checked-results
          ((decrease (t2-guarded-selectors-context-selector-decrease
                      lib (list *proof-ordinal-less* (list *library-count* term) parent) context)))
          (car decrease)))))
     (cons result (cdr premises)))))

(defun t2-guarded-selectors-guarded-decrease-visit (n value tests lib parent template hypotheses)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((zp n) '(:failure "fuel" "t2-guarded-selectors-guarded-decrease-visit"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
       ((branches (proof-list-of-length (cdr value) 3))
        (test (car branches))
        (yes (t2-guarded-selectors-guarded-decrease-visit
              (1- n) (cadr branches) (append tests (list (list test t))) lib parent template hypotheses))
        (no (t2-guarded-selectors-guarded-decrease-visit
             (1- n) (caddr branches) (append tests (list (list test nil))) lib parent template (cdr yes)))
        (joined (proof-by-value-join proof value template (car yes) (car no))))
       (cons joined (cdr no))))
     ((and (proof-compound value) (endp value)) '(:failure "missing-term-part" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
       ((equation (proof-proof-beta proof value))
        (body (proof-rewritten-term equation))
        (result (t2-guarded-selectors-guarded-decrease-visit
                 (1- n) body tests lib parent template hypotheses))
        (symmetric (proof-proof-symmetric proof equation))
        (step (proof-proof-rewrite-result proof (car result) symmetric template *proof-result*)))
       (cons step (cdr result))))
     (t (proof-with-checked-results
         ((result (t2-guarded-selectors-guarded-decrease-leaf value tests lib parent hypotheses))
          (literal (proof-step-first (car result)))
          (target (proof-subst template (list (cons *proof-result* value)))))
         (if (equal literal target) result '(:failure "recipe-mismatch" "")))))))

(defun t2-guarded-selectors-guarded-decrease (lib goal hypotheses)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length goal 3))
      (child (proof-term-at (cadr parts) 1))
      (parent (proof-term-at (caddr parts) 1))
      (opened (t2-guarded-selectors-guarded-selector lib child parent)))
     (if (not opened)
         (cons nil hypotheses)
       (proof-with-checked-results
        ((body (proof-rewritten-term opened))
         (template (list *proof-ordinal-less* (list *library-count* *proof-result*) (caddr parts)))
         (value (t2-guarded-selectors-guarded-decrease-visit
                 1000000 body nil lib (caddr parts) template hypotheses))
         (reversed (proof-proof-symmetric proof opened))
         (rewritten (proof-proof-rewrite proof (car value) reversed '(1 1 1)))
         (tidied (proof-proof-tidy proof rewritten)))
        (cons tidied (cdr value)))))))
