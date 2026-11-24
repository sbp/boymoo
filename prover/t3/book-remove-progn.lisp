(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-remove-progn-remove* (proof-sym "REMOVE-PROGN" "ACL2"))
(defconst *t3-book-remove-progn-remove-list* (proof-sym "REMOVE-PROGN-LST" "ACL2"))
(defconst *t3-book-remove-progn-lambda-shape* (proof-sym "SELF-T3-PROGN-LAMBDA-SHAPE" "ACL2"))

(defun t3-book-remove-progn-remove-progn-init (lib)
  (t3-book-substitution-term-traversal-init
   lib (list (list *t3-book-remove-progn-remove* *library-x*)
             (list *t3-book-remove-progn-remove-list* *library-x*))
   *proof-true* nil))

(defun t3-book-remove-progn-cdr-path-p (path)
  (or (endp path)
      (and (equal (caar path) *library-cdr*)
           (t3-book-remove-progn-cdr-path-p (cdr path)))))

(defund t3-book-remove-progn-argument-components (lib rest)
  (t3-book-substitution-total-list-components lib rest))

(defun t3-book-remove-progn-argument-type (lib path rest)
  (declare (xargs :measure (acl2-count path)))
  (proof-with-checked-results ((parts (t3-book-remove-progn-argument-components lib rest)))
    (if (consp (cdr path))
        (t3-book-remove-progn-argument-type lib (cdr path) (cadr parts))
      (car parts))))

(defun t3-book-remove-progn-rebuild-lambda (lib typed new-head source-head updated length known original transformed fields nonsymbol args)
  (let ((proof (library-library-proof lib))
        (true-listp *t3-book-lemmas-true-listp*))
    (proof-with-checked-results
        ((proper (t3-logic-libraryproofs-prove-formula
                  lib (list true-listp new-head) (list true-listp (proof-cl "EQ")) nil))
         (length-check (t3-logic-libraryproofs-prove-formula
                        lib (proof-eq (list *library-len* new-head) (proof-quote 3))
                        (list *library-len*) nil))
         (equation (t3-book-lambdas-inspect lib (list *t3-book-remove-progn-lambda-shape* new-head)
                                             (list proper length-check)))
         (derived (proof-step-first transformed))
         (tests (proof-rewritten-term equation))
         (required (t3-book-lambdas-required lib tests (table-put fields derived transformed)))
         (lambda-type (proof-proof-transport proof required equation))
         (literal (proof-step-first typed))
         (recognized (t3-book-lambdas-inspect lib literal (append known (list original nonsymbol))))
         (tests (proof-proof-rewrite proof typed recognized '(1)))
         (tests (proof-proof-tidy proof tests))
         (components (t3-book-associations-components lib tests))
         (original-lengths (t3-book-function-terms-fact-table components nil))
         (arity (t3-book-lambdas-required
                 lib (proof-eq (list *library-len* (list *library-cdr* *library-x*))
                               (list *library-len* (list *library-car* (list *library-cdr* source-head))))
                 original-lengths))
         (arity (proof-proof-chain proof length (list arity))))
      (t3-book-lambdas-application-with-lambda
       lib lambda-type updated arity (list *t3-book-substitution-term* (list *proof-cons* new-head args))))))

(defun t3-book-remove-progn-remove-progn-term-result-head (new-head tests self typed updated length known original args evidence)
  (let ((lib (t3-book-substitution-term-traversal-lib self))
        (source-head (list *library-car* *library-x*)))
    (if (equal new-head source-head)
        (proof-with-checked-results
            ((result (t3-book-substitution-rebuild
                      lib (list *proof-cons* new-head args) typed updated length
                      (append known (list original)))))
          (cons result self))
      (proof-with-checked-results
          ((signed (t3-logic-evidence-init lib (append (t3-logic-evidence-tests evidence) tests) nil nil))
           (nonsymbol (t3-logic-evidence-require signed (proof-neg (list *t3-book-lambdas-symbolp* source-head))))
           (old-lambda (t3-book-lambdas-pseudo-lambda-from-term
                        lib typed (car known) (cadr known) (car nonsymbol)
                        (list *t3-book-remove-progn-lambda-shape* source-head)))
           (fields (t3-book-function-terms-lambda-components lib old-lambda)))
        (let ((body (list *library-car* (list *library-cdr* (list *library-cdr* source-head)))))
          (proof-with-checked-results
              ((accepted (t3-book-function-terms-fact-at fields (list *t3-book-substitution-term* body)))
               (transformed (t3-book-substitution-term-traversal-smaller-at self body 0 accepted (cdr nonsymbol)))
               (result (t3-book-remove-progn-rebuild-lambda
                        lib typed new-head source-head updated length known original
                        (car transformed) fields (car nonsymbol) args)))
            (cons result (cadr transformed))))))))

(defund t3-book-remove-progn-head-advance (request self typed updated length known original args evidence template)
  (proof-with-checked-results
      ((result (t3-book-remove-progn-remove-progn-term-result-head
                (cadr request) (caddr request) self typed updated length known original args evidence))
       (next (t3-book-term-collections-by-value-resume
              (t3-book-substitution-term-traversal-lib (cdr result)) template request (car result))))
    (cons next (cdr result))))

(defun t3-book-remove-progn-head-visit (n request self typed updated length known original args evidence template)
  (declare (xargs :measure (nfix n)))
  (cond
   ((failure-p request) request)
   ((not (eq (car request) :t3-book-term-collections-leaf)) (cons request self))
   ((zp n) '(:failure "Fuel" "t3-book-remove-progn-remove-progn-term-result"))
   (t
    (proof-with-checked-results
        ((advanced (t3-book-remove-progn-head-advance
                    request self typed updated length known original args evidence template)))
      (t3-book-remove-progn-head-visit
       (1- n) (car advanced) (cdr advanced) typed updated length known original args evidence template)))))

(defun t3-book-remove-progn-term-child (self value original evidence)
  (proof-with-checked-results
      ((child (proof-term-at value 1))
       (path (t3-size-selector-path child *library-x*)))
    (if (and (consp path)
             (equal (caar path) *library-car*)
             (t3-book-remove-progn-cdr-path-p (cdr path)))
        (proof-with-checked-results
            ((accepted (t3-book-remove-progn-argument-type
                        (t3-book-substitution-term-traversal-lib self) (cdr path) original)))
          (t3-book-substitution-term-traversal-smaller-at self child 0 accepted evidence))
      '(:failure "Unsupported" ""))))

(defun t3-book-remove-progn-term-cons (self value typed known original evidence)
  (let ((lib (t3-book-substitution-term-traversal-lib self)))
    (proof-with-checked-results
        ((smaller (t3-book-substitution-term-traversal-smaller self *library-cdr* 1 original evidence))
         (parts (proof-proof-conjunct (library-library-proof lib) (car smaller)))
         (args (proof-term-at value 2))
         (operator (proof-term-at value 1))
         (request (t3-book-term-collections-by-value-start
                   (t3-book-substitution-term-traversal-lib (cadr smaller)) operator nil))
         (result (t3-book-remove-progn-head-visit
                  1000000 request (cadr smaller) typed (car parts) (cadr parts)
                  known original args (caddr smaller)
                  (list *t3-book-substitution-term* (list *proof-cons* *proof-result* args)))))
      (list (car result) (cdr result) (caddr smaller)))))

(defun t3-book-remove-progn-remove-progn-term-result (self value typed evidence)
  (if (equal value *library-x*)
      (list typed self evidence)
    (let ((lib (t3-book-substitution-term-traversal-lib self)))
      (proof-with-checked-results
          ((observed (t3-book-substitution-original-arguments lib typed evidence)))
        (let ((known (caar observed))
              (original (cadar observed))
              (evidence (cdr observed)))
          (cond
           ((proof-is-call value *t3-book-remove-progn-remove*)
            (t3-book-remove-progn-term-child self value original evidence))
           ((proof-is-call value *proof-cons*)
            (t3-book-remove-progn-term-cons self value typed known original evidence))
           (t '(:failure "Unsupported" ""))))))))

(defund t3-book-remove-progn-prove-next (traversal label replies)
  (proof-with-checked-results
      ((result (t3-book-substitution-term-traversal-prove traversal label replies)))
    (if (eq (car result) :t3-book-substitution-term-result)
        (let ((args (cddr result)))
          (proof-with-checked-results
              ((reply (t3-book-remove-progn-remove-progn-term-result
                       (cadr result) (car args) (cadr args) (caddr args))))
            (list :progn-reply (table-put replies args reply))))
      result)))

(defun t3-book-remove-progn-prove (n traversal label replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t3-book-remove-progn-prove")
    (let ((result (t3-book-remove-progn-prove-next traversal label replies)))
      (if (eq (car result) :progn-reply)
          (t3-book-remove-progn-prove (1- n) traversal label (cadr result))
        result))))

(defun t3-book-remove-progn-lambda-body-checks (checks recognized)
  (if (endp checks)
      recognized
    (proof-ite (car checks)
               (t3-book-remove-progn-lambda-body-checks (cdr checks) recognized)
               *proof-false*)))

(defun t3-book-remove-progn-removal-finish (lib label name formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((target (proof-term-at formula 2))
         (opened (proof-proof-beta proof target))
         (guard (proof-term-at formula 1))
         (accepted (proof-proof-assume proof guard t))
         (literal (proof-step-first accepted))
         (rule (library-library-cite lib label (cdr literal) nil))
         (truth (t3-logic-libraryproofs-prove lib *proof-true* nil nil))
         (both (proof-proof-prove-if proof rule truth))
         (parts (proof-proof-conjunct proof both))
         (operator (proof-term-at literal 0))
         (branch (if (equal operator *t3-book-substitution-list*) (cadr parts) (car parts)))
         (result (proof-proof-prove-if proof branch accepted))
         (transported (proof-proof-transport proof result opened))
         (entry (t3-book-function-terms-finish lib name formula transported)))
      (cons entry lib))))

(defun t3-book-remove-progn-removal (lib name formula)
  (let* ((formals (list *library-car* (list *library-cdr* *library-x*)))
         (body (list *library-car* (list *library-cdr* (list *library-cdr* *library-x*))))
         (checks (list (list *t3-book-lemmas-true-listp* *library-x*)
                       (proof-eq (list *library-len* *library-x*) (proof-quote 3))
                       (proof-eq (list *library-car* *library-x*) (proof-quote (proof-cl "LAMBDA")))
                       (list (proof-sym "SYMBOL-LISTP" "ACL2") formals)))
         (recognized (t3-book-remove-progn-lambda-body-checks checks (list *t3-book-substitution-term* body)))
         (label "T3-REMOVE-PROGN-INVARIANT"))
    (proof-with-checked-results
        ((lib (library-library-definition lib *t3-book-remove-progn-lambda-shape* (list *library-x*) recognized))
         (operation (t3-book-remove-progn-remove-progn-init lib))
         (operation (t3-book-remove-progn-prove 1000000 operation label nil)))
      (t3-book-remove-progn-removal-finish
       (t3-book-substitution-term-traversal-lib operation) label name formula))))
