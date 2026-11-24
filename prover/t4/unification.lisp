(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-unification-unify* (proof-sym "ONE-WAY-UNIFY1" "ACL2"))
(defconst *t4-unification-unify-list* (proof-sym "ONE-WAY-UNIFY1-LST" "ACL2"))
(defconst *t4-unification-unify-equal1* (proof-sym "ONE-WAY-UNIFY1-EQUAL1" "ACL2"))
(defconst *t4-unification-unify-equal* (proof-sym "ONE-WAY-UNIFY1-EQUAL" "ACL2"))
(defconst *t4-unification-quoted-subproblems*
  (proof-sym "ONE-WAY-UNIFY1-QUOTEP-SUBPROBLEMS" "ACL2"))
(defconst *t4-unification-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *t4-unification-zp* (proof-sym "ZP" "ACL2"))
(defconst *t4-unification-pairs*
  (list *t4-unification-unify-equal1* *t4-unification-unify-equal*))
(defconst *t4-unification-small* (proof-sym "T4-UNIFICATION-SUBPROBLEMS-SMALL" "ACL2"))
(defconst *t4-unification-fields* (list *proof-zero* (proof-quote 2)))

(defund t4-unification-measures-measure (name formals)
  (proof-with-checked-results ((first (proof-term-at formals 0)))
    (let ((a (t4-structural-count first)))
      (if (member-equal name *t4-unification-pairs*)
          (proof-with-checked-results ((second (proof-term-at formals 1)))
            (let ((b (t4-structural-count second))
                  (phase (proof-quote (if (equal name *t4-unification-unify-equal1*) 1 2))))
              (proof-ite (library-lt a b)
                         (t4-ordinals-phase-measure b phase)
                         (t4-ordinals-phase-measure a phase))))
        (t4-ordinals-phase-measure a *proof-zero*)))))

(defun t4-unification-measures-visit (definitions measures)
  (if (endp definitions)
      measures
    (proof-with-checked-results
        ((definition (proof-list-of-length (car definitions) 3))
         (measure (t4-unification-measures-measure (car definition) (cadr definition))))
      (t4-unification-measures-visit
       (cdr definitions) (table-put measures (car definition) measure)))))

(defun t4-unification-measures (definitions)
  (t4-unification-measures-visit definitions nil))

(defun t4-unification-boolean-count-bound (lib value obj evidence equality)
  (proof-with-checked-results
      ((bound (t4-structural-structural-count-bound
               lib value obj (t4-structural-evidence-with-proof evidence lib) t))
       (proof (library-library-proof (cadr bound)))
       (reverse (proof-proof-symmetric proof equality))
       (rewrite (proof-proof-rewrite proof (car bound) reverse '(1 1 1)))
       (step (proof-proof-tidy proof rewrite)))
    (list step (cadr bound) (caddr bound))))

(defun t4-unification-boolean-count-with-evidence (lib test obj evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof test))
         (assumed (proof-proof-assume proof test t))
         (evidence-true (proof-proof-rewrite proof assumed opened '(1)))
         (truth (proof-step-first evidence-true))
         (rhs (proof-term-at truth 2))
         (same (proof-proof-fact proof "equal-same" (list (list *library-x* rhs))))
         (reverse (proof-proof-symmetric proof evidence-true))
         (yes-rewritten (proof-proof-rewrite proof same reverse '(1 1 1)))
         (yes-value (library-library-transport-argument lib yes-rewritten opened 1))
         (nil-or-true (proof-proof-nil-or-true proof test))
         (front (proof-proof-front proof nil-or-true test))
         (denied (proof-proof-assume proof test nil))
         (no-value (proof-proof-cut proof front denied))
         (yes (t4-unification-boolean-count-bound lib *proof-true* obj evidence yes-value))
         (no (t4-unification-boolean-count-bound
              (cadr yes) *proof-false* obj (caddr yes) no-value))
         (step (proof-proof-cases (library-library-proof (cadr no)) test
                                  (car yes) (car no))))
      (list step (cadr no) (caddr no)))))

(defun t4-unification-boolean-count (lib test obj evidence)
  (proof-with-checked-results
      ((result (t4-unification-boolean-count-with-evidence lib test obj evidence)))
    (cons (car result) (cadr result))))

(defun t4-unification-subproblem-bound-result-value (fields)
  (if (endp fields)
      *proof-false*
    (list *proof-cons* (car fields)
          (t4-unification-subproblem-bound-result-value (cdr fields)))))

(defund t4-unification-subproblem-bound-cell-proof (lib index fields result-value)
  (let ((projection (list *t4-unification-mv-nth* index result-value)))
    (proof-with-checked-results
        ((reduced (t4-ordinals-ordinals-simplify
                   lib projection nil (list *t4-unification-mv-nth* *t4-unification-zp*
                                            *t4-structural-atom* *proof-not*)))
         (lib (cdr reduced))
         (proof (library-library-proof lib))
         (field (nth (cadr index) fields))
         (bound (proof-proof-assume proof (library-lt (t4-structural-count field)
                                                     (t4-structural-count *library-x*)) t))
         (reverse (proof-proof-symmetric proof (car reduced)))
         (rewritten (proof-proof-rewrite proof bound reverse '(1 1 1)))
         (step (proof-proof-tidy proof rewritten)))
      (cons step lib))))

(defun t4-unification-subproblem-bound-cell-proofs (lib indices fields result-value)
  (declare (xargs :measure (acl2-count indices)))
  (if (endp indices)
      (cons nil lib)
    (proof-with-checked-results
        ((result (t4-unification-subproblem-bound-cell-proof lib (car indices) fields result-value))
         (rest (t4-unification-subproblem-bound-cell-proofs
                (cdr result) (cdr indices) fields result-value)))
      (cons (cons (car result) (car rest)) (cdr rest)))))

(defun t4-unification-subproblem-bound-cell-guards (indices fields)
  (if (endp indices)
      nil
    (cons (proof-neg (library-lt (t4-structural-count (nth (cadar indices) fields))
                                (t4-structural-count *library-x*)))
          (t4-unification-subproblem-bound-cell-guards (cdr indices) fields))))

(defun t4-unification-subproblem-bound-cells (lib fields)
  (let* ((result-value (t4-unification-subproblem-bound-result-value fields))
         (claim (list *t4-unification-small* result-value *library-x*)))
    (proof-with-checked-results
        ((definition (proof-proof-unfold (library-library-proof lib) claim))
         (literal (proof-step-first definition))
         (cell-proofs (t4-unification-subproblem-bound-cell-proofs
                       lib *t4-unification-fields* fields result-value))
         (lib (cdr cell-proofs))
         (proved-body (t4-ordinals-ordinals-prove lib (caddr literal) (car cell-proofs) nil))
         (lib (cdr proved-body))
         (proved-cell (proof-proof-transport (library-library-proof lib) (car proved-body) definition)))
      (library-library-lemma lib "UNIFICATION-SUBPROBLEM-CELLS" claim proved-cell
                             (t4-unification-subproblem-bound-cell-guards
                              *t4-unification-fields* fields)))))

(defun t4-unification-subproblem-bound-contents (value)
  (if (proof-is-call value *proof-cons*)
      (proof-with-checked-results
          ((args (proof-list-of-length (cdr value) 2))
           (rest (t4-unification-subproblem-bound-contents (caddr value))))
        (cons (car args) rest))
    (if (equal value *proof-false*) nil '(:failure "InferenceMismatch" ""))))

(defund t4-unification-subproblem-bound-leaf-proof (lib child evidence)
  (if (proof-is-call child *t4-structural-eq*)
      (t4-unification-boolean-count-with-evidence lib child *library-x* evidence)
    (t4-structural-structural-count-bound
     lib child *library-x* (t4-structural-evidence-with-proof evidence lib) t)))

(defun t4-unification-subproblem-bound-leaf-proofs (lib indices contents evidence)
  (declare (xargs :measure (acl2-count indices)))
  (if (endp indices)
      (cons nil lib)
    (let ((child (nth (cadar indices) contents)))
      (proof-with-checked-results
          ((step (t4-unification-subproblem-bound-leaf-proof lib child evidence))
           (rest (t4-unification-subproblem-bound-leaf-proofs
                  (cadr step) (cdr indices) contents (caddr step))))
        (cons (cons (car step) (car rest)) (cdr rest))))))

(defun t4-unification-subproblem-bound-leaf (value lib cons-step fields)
  (proof-with-checked-results
      ((facts (t4-structural-evidence-init lib nil (list cons-step)))
       (contents (t4-unification-subproblem-bound-contents value)))
    (if (not (equal (len contents) (len fields)))
        '(:failure "InferenceMismatch" "")
      (proof-with-checked-results
          ((steps (t4-unification-subproblem-bound-leaf-proofs
                   lib *t4-unification-fields* contents facts))
           (lib (cdr steps))
           (step (proof-proof-use (library-library-proof lib)
                                  (proof-sym "SELF-UNIFICATION-SUBPROBLEM-CELLS" "ACL2")
                                  (seq-zip fields contents) (car steps))))
        (cons step lib)))))

(defun t4-unification-subproblem-bound-branches (n result cons-step fields)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-unification-subproblem-bound-branches")
    (proof-with-checked-results ((result result))
      (if (t4-structural-branch-request-p (car result))
          (proof-with-checked-results
              ((reply (t4-unification-subproblem-bound-leaf
                       (t4-structural-branch-request-node (car result))
                       (cdr result) cons-step fields)))
            (t4-unification-subproblem-bound-branches
             (1- n) (t4-structural-branch-results-resume (car result) reply) cons-step fields))
        result))))

(defun t4-unification-subproblem-bound-generic-bound (index)
  (library-lt (t4-structural-count (list *t4-unification-mv-nth* index *library-y*))
              (t4-structural-count *library-x*)))

(defun t4-unification-subproblem-bound-lemma (lib)
  (let* ((proof (library-library-proof lib))
         (call (list *t4-unification-quoted-subproblems* *library-x* *library-y*))
         (template (list *t4-unification-small* *proof-result* *library-x*))
         (fields (list (proof-sym "T4-RESULT-FIELD-0" "ACL2")
                       (proof-sym "T4-RESULT-FIELD-1" "ACL2")
                       (proof-sym "T4-RESULT-FIELD-2" "ACL2")
                       (proof-sym "T4-RESULT-FIELD-3" "ACL2"))))
    (proof-with-checked-results
        ((shape (list *proof-consp* *library-x*))
         (cons-step (proof-proof-assume proof shape t))
         (opened (proof-proof-unfold proof call))
         (literal (proof-step-first opened))
         (lib (library-library-definition
               lib *t4-unification-small* (list *library-y* *library-x*)
               (proof-ite (t4-unification-subproblem-bound-generic-bound (car *t4-unification-fields*))
                          (t4-unification-subproblem-bound-generic-bound (cadr *t4-unification-fields*))
                          *proof-false*)))
         (lib (t4-unification-subproblem-bound-cells lib fields))
         (branches (t4-structural-branch-results-start
                    lib "UNIFICATION-SUBPROBLEMS-SMALL-IF" (caddr literal) template))
         (result (t4-unification-subproblem-bound-branches 1000000 branches cons-step fields))
         (lib (cdr result))
         (proof (library-library-proof lib))
         (reversed (proof-proof-symmetric proof opened))
         (step (proof-proof-rewrite-result proof (car result) reversed template *proof-result*)))
      (library-library-lemma lib "UNIFICATION-SUBPROBLEMS-SMALL"
                             (list *t4-unification-small* call *library-x*) step
                             (list (proof-neg shape))))))

(defun t4-unification-subproblem-bound (lib field parent evidence)
  (proof-with-checked-results
      ((projection (proof-list-of-length field 3))
       (call (proof-list-of-length (caddr projection) 3)))
    (let ((index (cadr projection))
          (pat (cadr call))
          (obj (caddr call))
          (name "UNIFICATION-SUBPROBLEMS-SMALL"))
      (if (not (equal pat parent))
          '(:failure "InferenceMismatch" "")
        (proof-with-checked-results
            ((lib (if (assoc-equal (proof-sym "SELF-UNIFICATION-SUBPROBLEMS-SMALL" "ACL2")
                                  (proof-proof-facts (library-library-proof lib)))
                      lib
                    (t4-unification-subproblem-bound-lemma lib)))
             (cons-step (t4-structural-evidence-require
                         (t4-structural-evidence-with-proof evidence lib)
                         (list *proof-consp* pat)))
             (step (library-library-cite lib name (list pat obj) (list (car cons-step))))
             (literal (proof-step-first step))
             (proof (library-library-proof lib))
             (opened (proof-proof-unfold proof literal))
             (rewritten (proof-proof-rewrite proof step opened '(1)))
             (pieces (proof-proof-conjunct proof rewritten)))
          (cond ((equal index (car *t4-unification-fields*)) (cons (car pieces) lib))
                ((equal index (cadr *t4-unification-fields*)) (cons (cadr pieces) lib))
                (t '(:failure "SearchMiss" ""))))))))

(defun t4-unification-descent-pattern (measure)
  (proof-with-checked-results
      ((coefficient (proof-term-at measure 2))
       (size (proof-term-at coefficient 2)))
    (proof-term-at size 1)))

(defun t4-unification-descent-pair-bound (evidence child parent)
  (let ((a (t4-structural-count child))
        (b (t4-structural-count parent)))
    (proof-with-checked-results
        ((strict (t4-structural-evidence-find evidence (library-lt a b))))
      (if (car strict)
          strict
        (t4-structural-evidence-require (cdr strict) (library-le a b))))))

(defun t4-unification-descent-leaf (left right evidence lib call)
  (proof-with-checked-results
      ((child (t4-unification-descent-pattern left))
       (parent (t4-unification-descent-pattern right)))
    (cond
     ((equal child parent)
      (t4-ordinals-ordinals-phase-decrease lib left right nil))
     ((member-equal (termination-call-caller call) *t4-unification-pairs*)
      (proof-with-checked-results
          ((bound (t4-unification-descent-pair-bound evidence child parent)))
        (t4-ordinals-ordinals-phase-decrease lib left right (car bound))))
     ((proof-is-call child *t4-unification-mv-nth*)
      (proof-with-checked-results
          ((bound (t4-unification-subproblem-bound lib child parent evidence)))
        (t4-ordinals-ordinals-phase-decrease (cdr bound) left right (car bound))))
     (t (proof-with-checked-results
            ((bound (t4-structural-structural-count-bound lib child parent evidence t)))
          (t4-ordinals-ordinals-phase-decrease (cadr bound) left right (car bound)))))))

(defun t4-unification-descent-compare (n lib goal tests call replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-unification-descent-compare")
    (proof-with-checked-results
        ((result (t4-ordinals-ordinals-compare-measures lib goal tests replies)))
      (if (t4-ordinals-request-p result)
          (proof-with-checked-results
              ((reply (t4-unification-descent-leaf
                       (t4-ordinals-request-left result) (t4-ordinals-request-right result)
                       (t4-ordinals-request-evidence result)
                       (t4-ordinals-request-library result) call)))
            (t4-unification-descent-compare
             (1- n) lib goal tests call (append replies (list reply))))
        result))))

(defun t4-unification-descent (lib goal call)
  (t4-unification-descent-compare 1000000 lib goal (termination-call-tests call) call nil))
