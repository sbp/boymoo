(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-application-apply* (proof-sym "APPLY$" "ACL2"))
(defconst *t4-application-apply-lambda* (proof-sym "APPLY$-LAMBDA" "ACL2"))
(defconst *t4-application-ev* (proof-sym "EV$" "ACL2"))
(defconst *t4-application-primitive* (proof-sym "APPLY$-PRIMP" "ACL2"))
(defconst *t4-application-tame-function* (proof-sym "TAMEP-FUNCTIONP" "ACL2"))
(defconst *t4-application-badge* (proof-sym "BADGE" "ACL2"))
(defconst *t4-application-specials* (list *t4-application-apply* *t4-application-ev*))

(defun t4-application-application-measure (name first second)
  (let* ((phase (cond ((equal name *t4-application-apply*) 2)
                      ((equal name *t4-application-apply-lambda*) 1)
                      (t 0)))
         (plain (t4-ordinals-phase-measure (t4-structural-count first) (proof-quote phase))))
    (if (equal name *t4-application-apply*)
        (let* ((special (t4-ordinals-phase-measure
                         (t4-structural-count (list *library-car* second)) (proof-quote 3)))
               (applicable (proof-ite (list *t4-application-primitive* first) plain special)))
          (proof-ite (proof-eq first (proof-quote *t4-application-apply*))
                     applicable
                     (proof-ite (proof-eq first (proof-quote *t4-application-ev*))
                                applicable plain)))
      plain)))

(defun t4-application-measures-collect (definitions measures)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      measures
    (proof-with-checked-results
        ((definition (proof-list-of-length (car definitions) 3))
         (formals (proof-list-of-length (cadr definition) 2)))
      (let* ((name (car definition))
             (measure (t4-application-application-measure name (car formals) (cadr formals))))
        (t4-application-measures-collect (cdr definitions) (table-put measures name measure))))))

(defun t4-application-measures (definitions)
  (t4-application-measures-collect definitions nil))

(defun t4-application-tame-contradiction (lib tame nonprimitive same code goal)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((rewritten (proof-proof-rewrite proof nonprimitive same '(1 1 1)))
         (ground-primp (proof-proof-tidy proof rewritten))
         (simplified
          (t4-ordinals-ordinals-simplify
           lib (list *t4-application-tame-function* code) (list ground-primp)
           (list *t4-application-tame-function* *t4-application-badge*
                 *t4-structural-eq* *termination-return-last*))))
      (let* ((lib (cdr simplified))
             (proof (library-library-proof lib))
             (ground-tame (car simplified)))
        (if (not ground-tame)
            '(:failure "failure" "")
          (proof-with-checked-results
              ((literal (proof-step-first ground-tame))
               (right (proof-term-at literal 2)))
            (if (not (equal right *proof-false*))
                '(:failure "InferenceMismatch" "")
              (proof-with-checked-results
                  ((grounded (proof-proof-rewrite proof tame same '(1 1)))
                   (denied (proof-proof-rewrite proof grounded ground-tame '(1)))
                   (impossible (proof-proof-tidy proof denied))
                   (result (proof-proof-subsume proof impossible
                                                (cons goal (proof-step-clause impossible)))))
                (cons result lib)))))))))

(defund t4-application-special-match (obj evidence code)
  (t4-structural-evidence-find evidence (proof-eq obj code)))

(defun t4-application-update-evidence (evidence lib updated)
  (if (equal (t4-structural-evidence-proof evidence) lib)
      (t4-structural-evidence-with-proof evidence updated)
    evidence))

(defun t4-application-tame-specials (lib obj evidence goal tame nonprimitive specials)
  (declare (xargs :measure (acl2-count specials)))
  (if (endp specials)
      (cons (list nil evidence) lib)
    (let ((code (proof-quote (car specials))))
      (proof-with-checked-results
          ((match (t4-application-special-match obj evidence code)))
        (let ((same (car match))
              (evidence (cdr match)))
          (if same
              (proof-with-checked-results
                  ((result (t4-application-tame-contradiction lib tame nonprimitive same code goal)))
                (let ((updated (cdr result)))
                  (cons (list (car result) (t4-application-update-evidence evidence lib updated))
                        updated)))
            (t4-application-tame-specials lib obj evidence goal tame nonprimitive (cdr specials))))))))

(defun t4-application-close-tame-branch (lib obj evidence goal)
  (proof-with-checked-results
      ((tame (t4-structural-evidence-find evidence (list *t4-application-tame-function* obj)))
       (nonprimitive (t4-structural-evidence-find
                      (cdr tame) (proof-neg (list *t4-application-primitive* obj)))))
    (if (and (car tame) (car nonprimitive))
        (t4-application-tame-specials lib obj (cdr nonprimitive) goal
                                      (car tame) (car nonprimitive) *t4-application-specials*)
      (cons (list nil (cdr nonprimitive)) lib))))

(defun t4-application-measure-size (measure-term)
  (proof-with-checked-results
      ((coefficient (proof-term-at measure-term 2))
       (size (proof-term-at coefficient 2)))
    (proof-term-at size 1)))

(defun t4-application-compare-sizes (lib normalized right child parent evidence weak left-eq)
  (proof-with-checked-results
      ((bound (if (equal child parent)
                  (list nil lib evidence)
                (t4-structural-structural-count-bound lib child parent evidence (not weak))))
       (result (t4-ordinals-ordinals-phase-decrease (cadr bound) normalized right (car bound))))
    (if left-eq
        (proof-with-checked-results
            ((transported (library-library-transport-argument (cdr result) (car result) left-eq 1)))
          (cons transported (cdr result)))
      result)))

(defun t4-application-descent-compare (left right evidence lib call)
  (proof-with-checked-results
      ((simplified (t4-ordinals-ordinals-simplify lib left nil nil))
       (left-eq (car simplified))
       (left-literal (and left-eq (proof-step-first left-eq)))
       (normalized (if left-eq (proof-term-at left-literal 2) left))
       (child (t4-application-measure-size normalized))
       (parent (t4-application-measure-size right))
       (phase (and (equal (termination-call-callee call) *t4-application-apply*)
                   (equal (termination-call-caller call) *t4-application-apply*)
                   (proof-term-at normalized 3))))
    (let* ((evidence (t4-application-update-evidence evidence lib (cdr simplified)))
           (lib (cdr simplified))
           (weak (equal (termination-call-caller call) *t4-application-apply-lambda*)))
      (if (equal phase (proof-quote 3))
          (proof-with-checked-results
              ((obj (proof-term-at (termination-call-actuals call) 0))
               (closed (t4-application-close-tame-branch
                        lib obj evidence (list *proof-ordinal-less* left right))))
            (let ((result (caar closed))
                  (evidence (cadar closed))
                  (lib (cdr closed)))
              (if result
                  (cons result lib)
                (t4-application-compare-sizes lib normalized right child parent
                                               evidence weak left-eq))))
        (t4-application-compare-sizes lib normalized right child parent evidence weak left-eq)))))

(defun t4-application-descent-visit (n lib goal call replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-application-descent-visit")
    (let ((result (t4-ordinals-ordinals-compare-measures
                   lib goal (termination-call-tests call) replies)))
      (if (t4-ordinals-request-p result)
          (proof-with-checked-results
              ((reply (t4-application-descent-compare
                       (t4-ordinals-request-left result)
                       (t4-ordinals-request-right result)
                       (t4-ordinals-request-evidence result)
                       (t4-ordinals-request-library result)
                       call)))
            (t4-application-descent-visit (1- n) lib goal call (append replies (list reply))))
        result))))

(defun t4-application-descent (lib goal call)
  (t4-application-descent-visit 1000000 lib goal call nil))
