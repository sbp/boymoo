(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-projections-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *t3-book-projections-alistp* (proof-sym "ALISTP" "ACL2"))
(defconst *t3-book-projections-acons* (proof-cl "ACONS"))

(defund t3-book-projections-project-cell (lib index value)
  (let ((proof (library-library-proof lib))
        (term (list *t3-book-projections-mv-nth* (proof-quote index) value)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof term))
      (first (proof-step-first opened))
      (body (proof-term-at first 2))
      (cells (proof-proof-fact proof "consp-cons"
                               (seq-zip (list *library-x* *library-y*) (cdr value))))
      (test (proof-term-at body 1))
      (nonempty (t3-logic-libraryproofs-prove-formula
                 lib (proof-neg test) (list *t3-logic-atom* *proof-not*) (list cells)))
      (selected (proof-proof-select proof body nonempty))
      (opened (proof-proof-chain proof opened (list selected)))
      (first (proof-step-first opened))
      (body (proof-term-at first 2))
      (test (proof-term-at body 1))
      (tested (t3-logic-libraryproofs-prove-formula
               lib (if (equal index 0) test (proof-neg test))
               (list *t3-logic-zp* *proof-not*) nil))
      (selected (proof-proof-select proof body tested))
      (step (proof-proof-chain proof opened (list selected))))
     (if (equal index 0)
         (proof-with-checked-results
          ((head (t3-logic-libraryproofs-constant lib (list *library-car* value))))
          (proof-proof-chain proof step (list head)))
       (proof-with-checked-results
        ((first (proof-step-first step))
         (right (proof-term-at first 2))
         (subtraction (proof-term-at right 1))
         (decreased (proof-proof-compute proof subtraction (1- index)))
         (step (proof-proof-rewrite proof step decreased '(1 2 1)))
         (tail (t3-logic-libraryproofs-constant lib (list *library-cdr* value))))
        (proof-proof-rewrite proof step tail '(1 2 2)))))))

(defun t3-book-projections-project-run (n lib index value)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((zp n) '(:failure "fuel" "t3-book-projections-project"))
     ((not (proof-is-call value *proof-cons*))
      (let ((term (list *t3-book-projections-mv-nth* (proof-quote index) value)))
        (if (proof-is-call value *proof-quote*)
            (t3-logic-libraryproofs-normalize
             lib term nil (list *t3-book-projections-mv-nth*
                                *t3-logic-atom* *t3-logic-zp* *proof-not*))
          (proof-proof-reflexive proof term))))
     (t
      (proof-with-checked-results
       ((step (t3-book-projections-project-cell lib index value)))
       (if (equal index 0)
           step
         (proof-with-checked-results
          ((argument (proof-term-at value 2))
           (rest (t3-book-projections-project-run (1- n) lib (1- index) argument)))
          (proof-proof-chain proof step (list rest)))))))))

(defun t3-book-projections-project (lib index value)
  (t3-book-projections-project-run 1000000 lib index value))

(defun t3-book-projections-changed-arguments (old new)
  (if (or (endp old) (endp new))
      nil
    (let ((rest (t3-book-projections-changed-arguments (cdr old) (cdr new))))
      (if (equal (car old) (car new))
          rest
        (cons (list (car old) (car new)) rest)))))

(defun t3-book-projections-unique-argument-p (value arguments found)
  (if (endp arguments)
      found
    (if (equal value (car arguments))
        (and (not found)
             (t3-book-projections-unique-argument-p value (cdr arguments) t))
      (t3-book-projections-unique-argument-p value (cdr arguments) found))))

(defun t3-book-projections-cdr-path-p (path)
  (or (endp path)
      (and (equal (caar path) *library-cdr*)
           (t3-book-projections-cdr-path-p (cdr path)))))

(defun t3-book-projections-recursive-tails-collect (calls arguments mapping children)
  (declare (xargs :measure (acl2-count calls)))
  (if (endp calls)
      (and (consp children) (endp (cdr children))
           (list (caar children) (cdar children)))
    (proof-with-checked-results
     ((actuals (proof-subst-arguments (termination-call-actuals (car calls)) mapping))
      (pairs (t3-book-projections-changed-arguments arguments actuals)))
     (if (not (equal (len pairs) 1))
         nil
       (let ((old (caar pairs))
             (new (cadar pairs)))
         (proof-with-checked-results
          ((path (t3-size-selector-path new old)))
          (and (not (proof-compound old))
               (t3-book-projections-unique-argument-p old arguments nil)
               (consp path)
               (t3-book-projections-cdr-path-p path)
               (t3-book-projections-recursive-tails-collect
                (cdr calls) arguments mapping
                (table-put children old
                             (table-put (table-get children old nil) new pairs))))))))))

(defun t3-book-projections-recursive-tails (lib call)
  (if (not (proof-compound call))
      nil
    (proof-with-checked-results
     ((head (proof-term-at call 0)))
     (let ((definition (assoc-equal head (proof-proof-definitions (library-library-proof lib)))))
       (if (not definition)
           nil
         (let* ((formals (cadr definition))
                (body (caddr definition))
                (actuals (cdr call))
                (mapping (proof-bindings-table (seq-zip formals actuals) nil)))
           (proof-with-checked-results
            ((calls (termination-recursive-calls *termination-all*
                                                 (list (list head formals body)))))
            (t3-book-projections-recursive-tails-collect calls actuals mapping nil))))))))

(defund t3-book-projections-projected-list-tail-step (selector lib step evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((first (proof-step-first step))
      (equation (proof-proof-unfold proof first))
      (equality (proof-step-first equation))
      (body (proof-term-at equality 2))
      (argument (proof-term-at selector 1))
      (evidence-step (t3-logic-evidence-require evidence (list *proof-consp* argument)))
      (branch (proof-proof-select proof body (car evidence-step)))
      (selected (proof-proof-chain proof equation (list branch)))
      (changed (proof-proof-rewrite proof step selected '(1)))
      (step (proof-proof-tidy proof changed)))
     (cons step (cdr evidence-step)))))

(defun t3-book-projections-projected-list-tail-steps (path lib step evidence)
  (declare (xargs :measure (acl2-count path)))
  (if (endp path)
      (cons step evidence)
    (proof-with-checked-results
     ((next (t3-book-projections-projected-list-tail-step (car path) lib step evidence)))
     (t3-book-projections-projected-list-tail-steps (cdr path) lib (car next) (cdr next)))))

(defun t3-book-projections-projected-list-leaf-tail-proof (value lib variable accepted evidence)
  (proof-with-checked-results
   ((path (t3-size-selector-path value variable)))
   (if (eq path :none)
       '(:failure "failure" "")
     (t3-book-projections-projected-list-tail-steps (reverse path) lib accepted evidence))))

(defun t3-book-projections-projected-list-leaf-recognize
    (n value lib observed variable accepted predicate measure formula evidence)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t3-book-projections-projected-list-leaf-recognize")
    (let ((proof (library-library-proof lib))
          (entry (assoc-equal value observed))
          (target (list predicate value)))
      (cond
       (entry
        (let* ((child (cadr entry))
               (pairs (caddr entry))
               (smaller (list *library-count* child))
               (decreases (list *proof-ordinal-less* smaller measure)))
          (proof-with-checked-results
           ((instance (proof-subst formula (proof-bindings-table pairs nil)))
            (hypothesis (proof-proof-assume proof (proof-ite decreases instance *proof-true*) t))
            (decrease (t3-size-count-descent lib smaller measure evidence))
            (result (proof-proof-prove-if proof hypothesis (car decrease))))
           (if accepted
               (proof-with-checked-results
                ((tail (t3-book-projections-projected-list-leaf-tail-proof
                        child lib variable accepted (cdr decrease)))
                 (step (proof-proof-modus-ponens proof result (car tail))))
                (cons step (cdr tail)))
             (cons result (cdr decrease))))))
       (t
        (proof-with-checked-results
         ((path (if (and accepted (proof-is-call value *library-cdr*))
                    (t3-size-selector-path value variable)
                  :none)))
         (cond
          ((consp path)
           (t3-book-projections-projected-list-leaf-tail-proof value lib variable accepted evidence))
          ((proof-is-call value *proof-quote*)
           (proof-with-checked-results
            ((step (t3-logic-libraryproofs-prove-formula
                    lib target (list predicate *t3-logic-atom* (proof-cl "EQ") *proof-not*) nil)))
            (cons step evidence)))
          ((proof-is-call value *t3-book-projections-acons*)
           (proof-with-checked-results
            ((opened (proof-proof-unfold proof value))
             (equality (proof-step-first opened))
             (body (proof-term-at equality 2))
             (result (t3-book-projections-projected-list-leaf-recognize
                      (1- n) body lib observed variable accepted predicate measure formula evidence))
             (step (library-library-transport-argument lib (car result) opened 1)))
            (cons step (cdr result))))
          ((proof-is-call value *proof-cons*)
           (proof-with-checked-results
            ((rule (t3-book-spines-shallow lib target nil))
             (tail (proof-term-at value 2))
             (rest (t3-book-projections-projected-list-leaf-recognize
                    (1- n) tail lib observed variable accepted predicate measure formula evidence))
             (recognized
              (if (equal predicate *t3-book-projections-alistp*)
                  (proof-with-checked-results
                   ((first (proof-step-first (car rest)))
                    (equality (proof-step-first rule))
                    (right (proof-term-at equality 2)))
                   (if (equal first right)
                       (car rest)
                     (proof-with-checked-results
                      ((head-value (proof-term-at value 1))
                       (head (t3-logic-libraryproofs-prove-formula
                              lib (list *proof-consp* head-value) nil nil)))
                      (t3-scan-typed-pair lib head (car rest)))))
                (car rest)))
             (step (proof-proof-transport proof recognized rule)))
            (cons step (cdr rest))))
          (t '(:failure "unsupported" "")))))))))

(defun t3-book-projections-projected-list-leaf
    (value tests lib index observed variable accepted predicate measure formula)
  (proof-with-checked-results
   ((evidence (t3-logic-evidence-init lib tests nil nil))
    (index-value (proof-term-at index 1))
    (selection (t3-book-projections-project lib index-value value))
    (equality (proof-step-first selection))
    (selected (proof-term-at equality 2))
    (result (t3-book-projections-projected-list-leaf-recognize
             1000000 selected lib observed variable accepted predicate measure formula evidence)))
   (library-library-transport-argument lib (car result) selection 1)))

(defun t3-book-projections-projected-list-leaves
    (requests lib index observed variable accepted predicate measure formula)
  (if (endp requests)
      nil
    (let* ((request (car requests))
           (step (t3-book-projections-projected-list-leaf
                  (car request) (cadr request) lib index observed variable accepted
                  predicate measure formula)))
      (cons (cons request step)
            (if (failure-p step)
                nil
              (t3-book-projections-projected-list-leaves
               (cdr requests) lib index observed variable accepted predicate measure formula))))))

(defun t3-book-projections-projected-list-observed (children projection observed)
  (declare (xargs :measure (acl2-count children)))
  (if (endp children)
      observed
    (let* ((child (caar children))
           (pairs (cdar children)))
      (proof-with-checked-results
       ((term (proof-subst projection (proof-bindings-table pairs nil))))
       (t3-book-projections-projected-list-observed
        (cdr children) projection (table-put observed term (list child pairs)))))))

(defun t3-book-projections-projected-list-induction
    (lib formula guard predicate projection index call variable children)
  (if (and (not (eq guard :none))
           (not (equal guard (list *t3-book-lemmas-true-listp* variable))))
      nil
    (let* ((proof (library-library-proof lib))
           (measure (list *library-count* variable))
           (template (list predicate (list *t3-book-projections-mv-nth* index *proof-result*))))
      (proof-with-checked-results
       ((observed (t3-book-projections-projected-list-observed children projection nil))
        (accepted (if (eq guard :none) nil (proof-proof-assume proof guard t)))
        (opened (proof-proof-unfold proof call))
        (first (proof-step-first opened))
        (body (proof-term-at first 2))
        (requests (t3-logic-libraryproofs-by-value-leaves lib body nil))
        (leaves (t3-book-projections-projected-list-leaves
                 requests lib index observed variable accepted predicate measure formula))
        (result (t3-logic-libraryproofs-by-value lib body template leaves nil))
        (reversed (proof-proof-symmetric proof opened))
        (result (proof-proof-rewrite-result proof result reversed template *proof-result*))
        (step (if (eq guard :none) result (t3-book-lemmas-implication lib formula result)))
        (ordinal (library-library-builtin lib 1 variable)))
       (proof-proof-induct proof ordinal step formula measure (table-values children))))))

(defun t3-book-projections-project-induction-call (lib formula guarded predicate projection)
  (proof-with-checked-results
   ((parts (proof-list-of-length (cdr projection) 2)))
   (let ((index (car parts))
         (call (cadr parts)))
     (if (not (proof-is-call index *proof-quote*))
         nil
       (proof-with-checked-results
        ((index-value (proof-term-at index 1)))
        (if (not (and (integerp index-value) (<= 0 index-value) (<= index-value 8)
                      (proof-compound call)))
            nil
          (proof-with-checked-results
           ((recursive (t3-book-projections-recursive-tails lib call)))
           (if (not recursive)
               nil
             (proof-with-checked-results
              ((guard (if guarded (proof-term-at formula 1) :none)))
              (t3-book-projections-projected-list-induction
               lib formula guard predicate projection index call
               (car recursive) (cadr recursive)))))))))))

(defun t3-book-projections-projected-list (lib formula)
  (let ((guarded (proof-is-call formula *library-implies*)))
    (proof-with-checked-results
     ((goal (if guarded (proof-term-at formula 2) formula)))
     (if (not (or (proof-is-call goal *t3-book-lemmas-true-listp*)
                  (proof-is-call goal *t3-book-projections-alistp*)))
         nil
       (proof-with-checked-results
        ((projection (proof-term-at goal 1)))
        (if (proof-is-call projection *t3-book-projections-mv-nth*)
            (t3-book-projections-project-induction-call lib formula guarded (car goal) projection)
          nil))))))
