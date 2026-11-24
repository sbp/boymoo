(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t3-book-witnesses-iff* (proof-sym "IFF" "ACL2"))

(defun t3-book-witnesses-identity (remaining index)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      nil
    (cons (proof-sym (concatenate 'string "T3-ARG-" (decimal-text index)) "ACL2")
          (t3-book-witnesses-identity (1- remaining) (1+ index)))))

(defun t3-book-witnesses-subset-p (items available)
  (or (endp items)
      (and (member-equal (car items) available)
           (t3-book-witnesses-subset-p (cdr items) available))))

(defun t3-book-witnesses-declared-call-p (terms declared)
  (if (endp terms)
      nil
    (proof-with-checked-results ((head (t3-book-theorems-head (car terms))))
      (or (member-equal head declared)
          (t3-book-witnesses-declared-call-p (cdr terms) declared)))))

(defun t3-book-witnesses-guard-premises (premises condition head formals body)
  (if (endp premises)
      nil
    (proof-with-checked-results
     ((premise-head (t3-book-theorems-head (car premises)))
      (vars (and (equal premise-head head) (t3-book-theorems-variables (car premises))))
      (alternative (if (and (equal premise-head head) (not vars))
                       (proof-term-at (car premises) 1)
                     :none))
      (rest (t3-book-witnesses-guard-premises (cdr premises) condition head formals body)))
     (if (eq alternative :none)
         rest
       (cons (list formals (proof-ite condition body alternative)) rest)))))

(defund t3-book-witnesses-guard-projections (projections condition head call formals body)
  (if (endp projections)
      nil
    (let ((result (caar projections))
          (premises (caddar projections)))
      (proof-with-checked-results
       ((result-head (t3-book-theorems-head result))
        (options (and (equal result-head head) (equal (cdr result) (list call))
                      (t3-book-witnesses-guard-premises premises condition head formals body)))
        (rest (t3-book-witnesses-guard-projections (cdr projections) condition head call formals body)))
       (append options rest)))))

(defun t3-book-witnesses-guard-formulas (formulas condition head call formals body)
  (if (endp formulas)
      nil
    (proof-with-checked-results
     ((named (proof-list-of-length (car formulas) 2))
      (projections (t3-book-theorems-projections (cadr named) nil nil))
      (options (t3-book-witnesses-guard-projections projections condition head call formals body))
      (rest (t3-book-witnesses-guard-formulas (cdr formulas) condition head call formals body)))
     (append options rest))))

(defund t3-book-witnesses-equation-body (call body formula guards function arity formulas declared)
  (if (or (not (proof-is-call call function)) (not (equal (len call) (1+ arity))))
      nil
    (let ((formals (cdr call)))
      (proof-with-checked-results ((vars (t3-book-theorems-variables call)))
        (if (or (not (equal (len vars) arity)) (not (t3-book-witnesses-subset-p formals vars)))
            nil
          (proof-with-checked-results ((vars (t3-book-theorems-variables body)))
            (if (not (t3-book-witnesses-subset-p vars formals))
                nil
              (proof-with-checked-results
               ((terms (t3-book-theorems-terms body))
                (declared-call (t3-book-witnesses-declared-call-p terms declared)))
               (if declared-call
                   nil
                 (let ((body (if (proof-is-call formula *t3-book-witnesses-iff*)
                                 (proof-ite body *proof-true* *proof-false*)
                               body)))
                   (cond
                    ((endp guards) (list (list formals body)))
                    ((and (equal (len guards) 1) (member-equal body formals))
                     (proof-with-checked-results ((head (t3-book-theorems-head (car guards))))
                       (and head (t3-book-witnesses-guard-formulas formulas (car guards) head call formals body))))
                    (t nil))))))))))))

(defund t3-book-witnesses-equation-projections (projections function arity formulas declared)
  (if (endp projections)
      nil
    (let ((term (caar projections))
          (guards (caddar projections)))
      (proof-with-checked-results
       ((options
         (and (or (proof-is-call term *proof-equal*) (proof-is-call term *t3-book-witnesses-iff*))
              (proof-with-checked-results
               ((parts (proof-list-of-length (cdr term) 2))
                (forward (t3-book-witnesses-equation-body (car parts) (cadr parts) term guards
                                                          function arity formulas declared))
                (backward (t3-book-witnesses-equation-body (cadr parts) (car parts) term guards
                                                           function arity formulas declared)))
               (append forward backward))))
        (rest (t3-book-witnesses-equation-projections (cdr projections) function arity formulas declared)))
       (append options rest)))))

(defun t3-book-witnesses-equation-formulas (remaining function arity formulas declared)
  (if (endp remaining)
      nil
    (proof-with-checked-results
     ((named (proof-list-of-length (car remaining) 2))
      (projections (t3-book-theorems-projections (cadr named) nil nil))
      (options (t3-book-witnesses-equation-projections projections function arity formulas declared))
      (rest (t3-book-witnesses-equation-formulas (cdr remaining) function arity formulas declared)))
     (append options rest))))

(defun t3-book-witnesses-types-in-projections (projections function types)
  (if (endp projections)
      types
    (let ((term (caar projections)))
      (proof-with-checked-results ((head (t3-book-theorems-head term)))
        (t3-book-witnesses-types-in-projections
         (cdr projections) function
         (if (and head (equal (len term) 2) (proof-is-call (cadr term) function))
             (cons head types)
           types))))))

(defun t3-book-witnesses-types (formulas function types)
  (if (endp formulas)
      types
    (proof-with-checked-results
     ((named (proof-list-of-length (car formulas) 2))
      (projections (t3-book-theorems-projections (cadr named) nil nil))
      (types (t3-book-witnesses-types-in-projections projections function types)))
     (t3-book-witnesses-types (cdr formulas) function types))))

(defun t3-book-witnesses-typed-examples (facts types identity)
  (if (endp facts)
      nil
    (let ((clause (cdar facts)))
      (proof-with-checked-results
       ((head (and (equal (len clause) 1) (t3-book-theorems-head (car clause))))
        (usable (and (equal (len clause) 1)
                     (member-equal head types)
                     (equal (len (car clause)) 2)))
        (vars (and usable (t3-book-theorems-variables (cadar clause))))
        (rest (t3-book-witnesses-typed-examples (cdr facts) types identity)))
       (if (and usable (not vars))
           (cons (list identity (cadar clause)) rest)
         rest)))))

(defund t3-book-witnesses-candidate-bodies (lib function arity formulas declared)
  (let ((arity (cond ((eq arity t) 1)
                     ((null arity) 0)
                     (t arity))))
    (if (not (integerp arity))
        (t3-book-evaluators-argument-selectors nil arity)
      (let ((identity (t3-book-witnesses-identity arity 0)))
        (proof-with-checked-results
         ((equations (t3-book-witnesses-equation-formulas formulas function arity formulas declared))
          (types (t3-book-witnesses-types formulas function nil))
          (examples (and types (t3-book-witnesses-typed-examples
                                (proof-proof-facts (library-library-proof lib)) types identity))))
         (append equations examples
                 (if (equal arity 1)
                     (list (list identity (car identity))
                           (list identity (proof-eq (car identity) *proof-false*)))
                   nil)
                 (list (list identity *proof-false*) (list identity *proof-true*))))))))

(defun t3-book-witnesses-declared-names (declarations)
  (if (endp declarations)
      nil
    (proof-with-checked-results
     ((declaration (proof-list-of-length (car declarations) 2))
      (rest (t3-book-witnesses-declared-names (cdr declarations))))
     (cons (car declaration) rest))))

(defun t3-book-witnesses-candidates (lib declarations formulas declared)
  (if (endp declarations)
      nil
    (proof-with-checked-results
     ((bodies (t3-book-witnesses-candidate-bodies lib (caar declarations) (cadar declarations) formulas declared))
      (rest (t3-book-witnesses-candidates lib (cdr declarations) formulas declared)))
     (cons (proof-unique bodies) rest))))

(defun t3-book-witnesses-define-candidates (lib names definitions)
  (declare (xargs :measure (acl2-count names)))
  (if (or (endp names) (endp definitions) (failure-p lib))
      lib
    (t3-book-witnesses-define-candidates
     (library-library-definition lib (car names) (caar definitions) (cadar definitions))
     (cdr names) (cdr definitions))))

(defund t3-book-witnesses-prove-goal (search goal)
  (t3-book-theorems-prove-formula search goal 400 nil))

(defun t3-book-witnesses-prove-goals (search goals proofs)
  (declare (xargs :measure (acl2-count goals)))
  (if (endp goals)
      (cons (reverse proofs) search)
    (let* ((found (t3-book-witnesses-prove-goal search (car goals)))
           (step (car found))
           (search (cdr found)))
      (cond ((and (failure-p step) (equal (cadr step) "Unsupported"))
             (cons :retry search))
            ((failure-p step) step)
            (t (t3-book-witnesses-prove-goals search (cdr goals) (cons step proofs)))))))

(defund t3-book-witnesses-try-definitions (lib search definitions names goals declared)
  (let ((level (len (library-library-entries lib))))
    (proof-with-checked-results
     ((lib (t3-book-witnesses-define-candidates lib names definitions))
      (search (t3-book-theorems-with-library search lib))
      (result (t3-book-witnesses-prove-goals search goals nil)))
     (let* ((search (cdr result))
            (lib (t3-book-theorems-library search)))
       (if (eq (car result) :retry)
           (proof-with-checked-results ((lib (t3-logic-libraryproofs-discard-entries lib level)))
             (list :retry lib (t3-book-theorems-with-library search lib)))
         (proof-with-checked-results
          ((first (proof-term-at declared 0))
           (entry (proof-proof-entry "witness" first (cons first names) (car result))))
          (list entry lib search)))))))

(mutual-recursion
 (defun t3-book-witnesses-try-product (n lib search candidates reverse-definitions names goals declared)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "t3-book-witnesses-witness-proof"))
         ((endp candidates)
          (t3-book-witnesses-try-definitions lib search (reverse reverse-definitions) names goals declared))
         (t (t3-book-witnesses-try-options (1- n) lib search (car candidates) (cdr candidates)
                                           reverse-definitions names goals declared))))
 (defun t3-book-witnesses-try-options (n lib search options candidates reverse-definitions names goals declared)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "Fuel" "t3-book-witnesses-witness-proof"))
         ((endp options) (list :retry lib search))
         (t (proof-with-checked-results
             ((found (t3-book-witnesses-try-product (1- n) lib search candidates
                                                    (cons (car options) reverse-definitions) names goals declared)))
             (if (eq (car found) :retry)
                 (t3-book-witnesses-try-options (1- n) (cadr found) (caddr found) (cdr options)
                                                 candidates reverse-definitions names goals declared)
               found))))))

(defun t3-book-witnesses-witness-proof (lib search declarations formulas)
  (proof-with-checked-results
   ((declared (t3-book-witnesses-declared-names declarations))
    (names (t3-tactics-witness-names declarations))
    (candidates (t3-book-witnesses-candidates lib declarations formulas declared))
    (goals (t3-book-evaluators-witness-goals formulas names))
    (found (t3-book-witnesses-try-product 1000000 lib search candidates nil (table-values names) goals declared)))
   (if (eq (car found) :retry)
       '(:failure "Unsupported" "")
     found)))
