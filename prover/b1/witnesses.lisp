(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-witnesses-witnesses*
  '(("E1" . b1-witnesses-identity-witness)
    ("G16-WITNESS" . b1-witnesses-successor-witness)
    ("DOMAIN-ELEM-TYPE" . b1-witnesses-alist-type-witness)
    ("ELEM-TYPE00" . b1-witnesses-list-type-witness)
    ("ELEM-TYPE10" . b1-witnesses-list-type-witness)
    ("ELEM-TYPE11" . b1-witnesses-list-type-witness)
    ("EVAL-FOR-MV-NTH" . b1-witnesses-evaluator-witness)
    ("FLAG-IS-CP-EV" . b1-witnesses-evaluator-witness)))

(defmacro b1-witnesses-with-library-results (lib bindings result)
  (if (endp bindings)
      result
    (let ((name (caar bindings))
          (form (cadar bindings))
          (rest (cdr bindings)))
      (if (eq name lib)
          `(let ((b1-witnesses-updated-library ,form))
             (if (failure-p b1-witnesses-updated-library)
                 (cons b1-witnesses-updated-library ,lib)
               (let ((,lib b1-witnesses-updated-library))
                 (b1-witnesses-with-library-results ,lib ,rest ,result))))
        `(let ((,name ,form))
           (if (failure-p ,name)
               (cons ,name ,lib)
             (b1-witnesses-with-library-results ,lib ,rest ,result)))))))

(defun b1-witnesses-recipe-result (result)
  (if (failure-p (car result)) (car result) result))

(mutual-recursion
 (defun b1-witnesses-rename-calls (term names)
   (declare (xargs :measure (acl2-count term)))
   (cond ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
          term)
         ((endp term)
          '(:failure "failure" ""))
         ((proof-compound (car term))
          (if (consp (cddar term))
              (proof-with-checked-results
                  ((body (b1-witnesses-rename-calls (caddar term) names))
                   (arguments (b1-witnesses-rename-arguments (cdr term) names)))
                (cons (list (caar term) (cadar term) body) arguments))
            '(:failure "failure" "")))
         (t
          (proof-with-checked-results
              ((head (table-get names (car term) (car term)))
               (arguments (b1-witnesses-rename-arguments (cdr term) names)))
            (cons head arguments)))))
 (defun b1-witnesses-rename-arguments (arguments names)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (proof-with-checked-results
         ((first (b1-witnesses-rename-calls (car arguments) names))
          (rest (b1-witnesses-rename-arguments (cdr arguments) names)))
       (cons first rest)))))

(defun b1-witnesses-renaming (functions names renaming)
  (if (or (endp functions) (endp names))
      renaming
    (b1-witnesses-renaming (cdr functions) (cdr names)
                           (table-put renaming (car functions) (car names)))))

(defun b1-witnesses-renamed-formulas (formulas names)
  (if (endp formulas)
      nil
    (proof-with-checked-results
        ((formula (proof-list-of-length (car formulas) 2))
         (target (b1-witnesses-rename-calls (cadr formula) names))
         (other (b1-witnesses-renamed-formulas (cdr formulas) names)))
      (cons target other))))

(defund b1-witnesses-identity-proof (lib formula functions identity)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 2))
       (original (proof-term-at functions 0))
       (target (b1-witnesses-rename-calls (cadr formula) (list (cons original identity))))
       (rule (b1-logic-bookproof-rewrite-rule lib identity)))
    (b1-logic-bookproof-normalize-proof lib target nil nil (list rule) nil)))

(defun b1-witnesses-identity-proofs (lib formulas functions identity)
  (if (endp formulas)
      nil
    (proof-with-checked-results
        ((step (b1-witnesses-identity-proof lib (car formulas) functions identity))
         (other (b1-witnesses-identity-proofs lib (cdr formulas) functions identity)))
      (cons step other))))

(defun b1-witnesses-identity-witness (lib functions formulas)
  (let ((identity (proof-sym "G14" "ACL2")))
    (proof-with-checked-results
        ((proofs (b1-witnesses-identity-proofs lib formulas functions identity)))
      (cons (list (list identity) proofs) lib))))

(defun b1-witnesses-successor-witness-with-library (lib functions formulas)
  (let* ((successor (proof-sym "B1-SUCCESSOR" "ACL2"))
         (always (proof-sym "B1-ALWAYS-TRUE" "ACL2"))
         (names (list successor always))
         (formals (list *library-x*)))
    (b1-witnesses-with-library-results lib
        ((lib (library-library-definition lib successor formals (library-plus *proof-one* *library-x*)))
         (lib (library-library-definition lib always formals *proof-true*))
         (renamed (b1-witnesses-renamed-formulas formulas (b1-witnesses-renaming functions names nil)))
         (pair (proof-list-of-length renamed 2))
         (larger (b1-integer-successor-is-larger lib *library-x*))
         (larger-claim (proof-step-first larger))
         (boolean (proof-proof-fact (library-library-proof lib) "booleanp-<"
                                    (seq-zip (list *library-x* *library-y*) (cdr larger-claim))))
         (equality (b1-logic-bookproof-boolean-value lib larger boolean))
         (definition (b1-logic-bookproof-normalize-proof
                      lib (car pair) nil (list successor always (proof-sym "G15" "ACL2"))
                      (list (b1-logic-equal-to equality)) nil))
         (premise (b1-logic-bookproof-prove-implication-premise lib (cadr pair)))
         (claim (proof-term-at (cadr pair) 2))
         (consequence (b1-logic-bookproof-normalize-proof lib claim nil (list always) nil nil))
         (sufficiency (b1-logic-bookproof-prove-implication-with-premise
                       lib (cadr pair) premise consequence)))
      (cons (list names (list definition sufficiency)) lib))))

(defun b1-witnesses-successor-witness (lib functions formulas)
  (b1-witnesses-recipe-result (b1-witnesses-successor-witness-with-library lib functions formulas)))

(defun b1-witnesses-recognizer-witness-proofs-consequence (atom lib claim recognizer null-name)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first atom))
         (opened (proof-proof-unfold proof literal))
         (noncons (proof-proof-rewrite proof atom opened (list 1)))
         (goal (proof-term-at claim 2)))
      (b1-logic-bookproof-normalize-proof
       lib goal (list atom noncons) (list recognizer null-name *b1-logic-eq* *proof-not*) nil nil))))

(defun b1-witnesses-recognizer-claim (lib claim)
  (let ((proof (library-library-proof lib))
        (unfold (list *b1-logic-atom* *b1-logic-eq* *proof-not*)))
    (cond
     ((proof-is-call claim *b1-revappend-iff*)
      (proof-with-checked-results
          ((left (proof-term-at claim 1))
           (equation (proof-proof-unfold proof left)))
        (b1-logic-bookproof-case-proof lib claim nil (cons *b1-revappend-iff* unfold)
                                       (list (b1-logic-equal-to equation)) 16)))
     ((proof-is-call claim *library-implies*)
      (proof-with-checked-results
          ((conclusion (proof-term-at claim 2))
           (call (proof-term-at conclusion 1))
           (recognizer (proof-term-at call 0))
           (premise (b1-logic-bookproof-prove-implication-premise lib claim))
           (consequence (b1-witnesses-recognizer-witness-proofs-consequence
                         premise lib claim recognizer (proof-cl "NULL"))))
        (b1-logic-bookproof-prove-implication-with-premise lib claim premise consequence)))
     (t
      (let ((proper (proof-sym "TRUE-LISTP" "ACL2")))
        (proof-with-checked-results
            ((equation (if (proof-is-call claim *proof-if*) (proof-term-at claim 2) claim))
             (left (proof-term-at equation 1))
             (head (proof-term-at left 0))
             (opened (b1-logic-bookproof-normalize lib left nil (cons head unfold) nil nil nil nil))
             (empty (b1-logic-bookproof-normalize lib (list proper *proof-false*) nil
                                                 (list proper *b1-logic-eq*) nil nil nil nil)))
          (b1-logic-bookproof-case-proof lib claim nil unfold
                                         (list (b1-logic-equal-to opened) (b1-logic-equal-to empty))
                                         16)))))))

(defund b1-witnesses-recognizer-witness-proof (lib formula names wrappers)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 2))
       (target (b1-witnesses-rename-calls (cadr formula) names))
       (expansion (b1-logic-bookproof-normalize lib target nil wrappers nil nil nil t))
       (equation (proof-step-first expansion))
       (claim (proof-term-at equation 2))
       (step (b1-witnesses-recognizer-claim lib claim)))
    (proof-proof-transport (library-library-proof lib) step expansion)))

(defun b1-witnesses-recognizer-witness-proofs (lib formulas names wrappers)
  (if (endp formulas)
      nil
    (proof-with-checked-results
        ((step (b1-witnesses-recognizer-witness-proof lib (car formulas) names wrappers))
         (other (b1-witnesses-recognizer-witness-proofs lib (cdr formulas) names wrappers)))
      (cons step other))))

(defun b1-witnesses-alist-type-witness-with-library (lib functions formulas)
  (let* ((universal (proof-sym "B1-ALIST-ELEMENT" "ACL2"))
         (proper (proof-sym "TRUE-LISTP" "ACL2"))
         (alist (proof-sym "ALISTP" "ACL2"))
         (chosen (list universal proper universal proper alist)))
    (b1-witnesses-with-library-results lib
        ((lib (library-library-definition lib universal (list *library-x*) *proof-true*))
         (proofs (b1-witnesses-recognizer-witness-proofs
                  lib formulas (b1-witnesses-renaming functions chosen nil) (list universal))))
      (cons (list chosen proofs) lib))))

(defun b1-witnesses-alist-type-witness (lib functions formulas)
  (b1-witnesses-recipe-result (b1-witnesses-alist-type-witness-with-library lib functions formulas)))

(defun b1-witnesses-list-type-name (function)
  (proof-with-checked-results ((name (proof-term-at function 2)))
    (proof-sym (concatenate 'string "B1-" name) "ACL2")))

(defun b1-witnesses-list-type-names (functions)
  (if (endp functions)
      (proof-list-of-length functions 2)
    (proof-with-checked-results ((element (b1-witnesses-list-type-name (car functions))))
      (if (endp (cdr functions))
          (proof-list-of-length functions 2)
        (proof-with-checked-results ((wrapper (b1-witnesses-list-type-name (cadr functions))))
          (if (endp (cddr functions))
              (list element wrapper)
            (proof-with-checked-results ((extra (b1-witnesses-list-type-name (caddr functions))))
              (proof-list-of-length functions 2))))))))

(defun b1-witnesses-list-type-witness-with-library (lib functions formulas)
  (b1-witnesses-with-library-results lib
      ((chosen (b1-witnesses-list-type-names functions))
       (first (proof-term-at formulas 0))
       (formula (proof-list-of-length first 2))
       (implication (proof-list-of-length (cadr formula) 3))
       (left (proof-term-at (caddr implication) 1))
       (driver (proof-term-at left 1))
       (lib (library-library-definition lib (car chosen) (cdr (cadr implication)) *proof-true*))
       (lib (library-library-definition lib (cadr chosen) (cdr (cadr implication))
                                        (list (proof-sym "TRUE-LISTP" "ACL2") driver)))
       (proofs (b1-witnesses-recognizer-witness-proofs
                lib formulas (b1-witnesses-renaming functions chosen nil) chosen)))
    (cons (list chosen proofs) lib)))

(defun b1-witnesses-list-type-witness (lib functions formulas)
  (b1-witnesses-recipe-result (b1-witnesses-list-type-witness-with-library lib functions formulas)))

(defund b1-witnesses-evaluator-proof (formula evaluator names index)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 2))
       (target (b1-witnesses-rename-calls (cadr formula) names)))
    (b1-evaluators-evaluator-constraint evaluator index target)))

(defun b1-witnesses-evaluator-proofs (formulas evaluator names index)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      (cons nil evaluator)
    (let ((result (b1-witnesses-evaluator-proof (car formulas) evaluator names index)))
      (if (failure-p result)
          (cons result evaluator)
        (let ((other (b1-witnesses-evaluator-proofs (cdr formulas) (cdr result) names (1+ index))))
          (if (failure-p (car other))
              other
            (cons (cons (car result) (car other)) (cdr other))))))))

(defun b1-witnesses-evaluator-witness-with-library (lib functions formulas)
  (let ((evaluator (b1-evaluators-evaluator-init lib functions formulas)))
    (if (failure-p evaluator)
        (cons evaluator lib)
      (let* ((chosen (b1-evaluators-evaluator-functions evaluator))
             (result (b1-witnesses-evaluator-proofs formulas evaluator
                                                   (b1-witnesses-renaming functions chosen nil) 0))
             (value (car result))
             (lib (b1-evaluators-evaluator-lib (cdr result))))
        (cons (if (failure-p value) value (list chosen value)) lib)))))

(defun b1-witnesses-evaluator-witness (lib functions formulas)
  (b1-witnesses-recipe-result (b1-witnesses-evaluator-witness-with-library lib functions formulas)))

(defun b1-witnesses-numbered-names (indices prefix)
  (if (endp indices)
      nil
    (cons (proof-sym (concatenate 'string prefix (decimal-text (car indices))) "ACL2")
          (b1-witnesses-numbered-names (cdr indices) prefix))))

(defun b1-witnesses-formals (functions)
  (if (endp functions)
      nil
    (proof-with-checked-results
        ((function (proof-list-of-length (car functions) 2))
         (arity (cadr function))
         (indices (cond ((integerp arity) (seq-range 0 arity 1))
                        ((eq arity t) (list 0))
                        ((null arity) nil)
                        (t '(:failure "failure" ""))))
         (other (b1-witnesses-formals (cdr functions))))
      (cons (b1-witnesses-numbered-names indices "B1-ARG-") other))))

(defun b1-witnesses-function-symbols (functions)
  (if (endp functions)
      nil
    (proof-with-checked-results
        ((function (proof-list-of-length (car functions) 2))
         (other (b1-witnesses-function-symbols (cdr functions))))
      (cons (car function) other))))

(defun b1-witnesses-unproved-p (value)
  (and (failure-p value)
       (member-equal (cadr value) '("unproved" "search-budget-exhausted"))))

(defund b1-witnesses-small-witnesses-prove-formula (world formula index names)
  (let ((attempt (b1-search-attempt-init world index 90 names nil)))
    (proof-with-checked-results ((result (b1-search-attempt-prove attempt formula nil nil 3)))
      (let ((step (car result))
            (world (b1-search-attempt-lib (cdr result))))
        (if (b1-witnesses-unproved-p step)
            (proof-with-checked-results
                ((fallback (b1-logic-bookproof-case-proof
                            world formula nil (union-equal *b1-search-small-definitions* names) nil 5)))
              (cons fallback world))
          (if (failure-p step) step (cons step world)))))))

(defun b1-witnesses-prove-trial (lib formulas names index)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      (cons nil lib)
    (proof-with-checked-results
        ((result (b1-witnesses-small-witnesses-prove-formula lib (car formulas) index names))
         (other (b1-witnesses-prove-trial (cdr result) (cdr formulas) names index)))
      (cons (cons (car result) (car other)) (cdr other)))))

(defund b1-witnesses-install-definition (lib name specification)
  (library-library-definition lib name (car specification) (cadr specification)))

(defun b1-witnesses-install-trial (lib names trial)
  (declare (xargs :measure (acl2-count names)))
  (if (or (endp names) (endp trial))
      lib
    (proof-with-checked-results
        ((lib (b1-witnesses-install-definition lib (car names) (car trial))))
      (b1-witnesses-install-trial lib (cdr names) (cdr trial)))))

(defun b1-witnesses-trial-clauses-p (proofs formulas)
  (or (endp proofs)
      (endp formulas)
      (and (equal (proof-step-clause (car proofs)) (list (car formulas)))
           (b1-witnesses-trial-clauses-p (cdr proofs) (cdr formulas)))))

(defund b1-witnesses-try (lib names translated index trial)
  (proof-with-checked-results ((temporary (b1-witnesses-install-trial lib names trial)))
    (let ((result (b1-witnesses-prove-trial temporary translated names index)))
      (cond ((b1-witnesses-unproved-p result) nil)
            ((failure-p result) result)
            ((b1-witnesses-trial-clauses-p (car result) translated)
             (cons (list names (car result)) (cdr result)))
            (t nil)))))

(defun b1-witnesses-noncompound-p (terms)
  (or (endp terms)
      (and (not (proof-compound (car terms)))
           (b1-witnesses-noncompound-p (cdr terms)))))

(defun b1-witnesses-variables-in-p (terms formals)
  (or (endp terms)
      (and (or (proof-compound (car terms)) (member-equal (car terms) formals))
           (b1-witnesses-variables-in-p (cdr terms) formals))))

(defund b1-witnesses-definition-trial (formula symbol formals rename)
  (if (not (or (proof-is-call formula *proof-equal*) (proof-is-call formula *b1-revappend-iff*)))
      nil
    (proof-with-checked-results ((equation (proof-list-of-length formula 3)))
      (let* ((left (cadr equation))
             (right (caddr equation))
             (arguments (cdr left))
             (subterms (b1-search-subterms right)))
        (if (and (proof-is-call left symbol)
                 (equal (len arguments) (len formals))
                 (b1-witnesses-noncompound-p arguments)
                 (no-duplicatesp-equal arguments)
                 (b1-witnesses-variables-in-p subterms arguments))
            (proof-with-checked-results ((renamed (b1-witnesses-rename-calls right rename)))
              (and (equal renamed right) (list (list arguments right))))
          nil)))))

(defun b1-witnesses-definition-trials (formulas lib symbol formals rename names translated index)
  (if (endp formulas)
      nil
    (proof-with-checked-results
        ((trial (b1-witnesses-definition-trial (cadar formulas) symbol formals rename))
         (result (and trial (b1-witnesses-try lib names translated index trial))))
      (or result (b1-witnesses-definition-trials (cdr formulas) lib symbol formals rename
                                                  names translated index)))))

(defun b1-witnesses-constant-trial (formals value)
  (if (endp formals)
      nil
    (cons (list (car formals) value) (b1-witnesses-constant-trial (cdr formals) value))))

(defun b1-witnesses-nonempty-formals-p (formals)
  (or (endp formals)
      (and (consp (car formals)) (b1-witnesses-nonempty-formals-p (cdr formals)))))

(defun b1-witnesses-identity-trial (formals)
  (if (endp formals)
      nil
    (cons (list (car formals) (caar formals)) (b1-witnesses-identity-trial (cdr formals)))))

(defun b1-witnesses-list-trials (arguments lib formals names translated index)
  (if (endp arguments)
      nil
    (let* ((trial (list (list (car formals) *proof-true*)
                        (list (cadr formals) (list (proof-sym "TRUE-LISTP" "ACL2") (car arguments)))))
           (result (b1-witnesses-try lib names translated index trial)))
      (or result (b1-witnesses-list-trials (cdr arguments) lib formals names translated index)))))

(defun b1-witnesses-small-witnesses-candidates (lib formulas symbols formals rename
                                                   names translated index)
  (or (and (equal (len symbols) 1)
           (b1-witnesses-definition-trials formulas lib (car symbols) (car formals) rename
                                           names translated index))
      (b1-witnesses-try lib names translated index (b1-witnesses-constant-trial formals *proof-false*))
      (b1-witnesses-try lib names translated index (b1-witnesses-constant-trial formals *proof-true*))
      (and (b1-witnesses-nonempty-formals-p formals)
           (b1-witnesses-try lib names translated index (b1-witnesses-identity-trial formals)))
      (and (equal (len symbols) 2)
           (member-equal (len (cadr formals)) '(1 2))
           (b1-witnesses-list-trials (cadr formals) lib formals names translated index))))

(defun b1-witnesses-small-witnesses (lib functions formulas index)
  (proof-with-checked-results ((symbols (b1-witnesses-function-symbols functions)))
    (if (< 8 (len formulas))
        '(:failure "unproved" "")
      (proof-with-checked-results
          ((formals (b1-witnesses-formals functions))
           (source (proof-write symbols))
           (tag (text-upper (seq-slice (siphash-hexdigest source) 0 12)))
           (names (b1-witnesses-numbered-names (seq-range 0 (len symbols) 1)
                                              (concatenate 'string "B1-WITNESS-" tag "-")))
           (rename (b1-witnesses-renaming symbols names nil))
           (translated (b1-witnesses-renamed-formulas formulas rename)))
        (or (b1-witnesses-small-witnesses-candidates lib formulas symbols formals rename
                                                   names translated index)
            '(:failure "unproved" ""))))))
