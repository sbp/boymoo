(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *witnesses-atom* (proof-cl "ATOM"))
(defconst *witnesses-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *witnesses-characterp* (proof-cl "CHARACTERP"))
(defconst *witnesses-endp* (proof-cl "ENDP"))
(defconst *witnesses-eq* (proof-cl "EQ"))
(defconst *witnesses-null* (proof-cl "NULL"))
(defconst *witnesses-symbolp* (proof-cl "SYMBOLP"))
(defconst *witnesses-constrained-to-df* (proof-sym "CONSTRAINED-TO-DF" "ACL2"))
(defconst *witnesses-to-df* (proof-sym "TO-DF" "ACL2"))
(defconst *witnesses-dfp* (proof-sym "DFP" "ACL2"))
(defconst *witnesses-character-fix* (proof-sym "T1-CHARACTER-FIX" "ACL2"))
(defconst *witnesses-rational-fix* (proof-sym "T1-RATIONAL-FIX" "ACL2"))

(defconst *witnesses-constants*
  (list (cons "NIL" *proof-false*)
        (cons "ZERO" *proof-zero*)
        (cons "EMPTY-STRING" (proof-quote '("str" "")))))

(defconst *witnesses-witnesses*
  (list (list "ALPHA-CHAR-P-NON-STANDARD" "NIL" "NIL" "NIL"
              *witnesses-character-fix* *witnesses-character-fix*)
        (list "CONSTRAINED-DF-STRING" "EMPTY-STRING")
        (list "CONSTRAINED-TO-DF" *witnesses-rational-fix*)
        (list "DF-ROUND" *witnesses-to-df*)
        (list "CONSTRAINED-DF-RATIONALIZE" *witnesses-to-df*)
        (list "EV-FNCALL+-FNS" "NIL")
        (list "CONJOIN-CLAUSE-SETS-BOUND" "ZERO")
        (list "DOPPELGANGER-BADGE-USERFN" "NIL")
        (list "DOPPELGANGER-APPLY$-USERFN" "NIL")
        (cons "CONSTRAINED-DF-EXPT-FN" (make-list-ac 19 "ZERO" nil))))

(defun witnesses-formals (indices)
  (if (endp indices)
      nil
    (cons (proof-sym (concatenate 'string "ARG-" (decimal-text (car indices))) "ACL2")
          (witnesses-formals (cdr indices)))))

(defun witnesses-define (lib name formals body)
  (proof-with-checked-results
   ((lib (if (assoc-equal name (proof-proof-definitions (library-library-proof lib)))
             lib
           (library-library-definition lib name formals body))))
   (cons name lib)))

(defun witnesses-witness (lib recipe arity)
  (cond
   ((equal recipe *witnesses-to-df*) (cons recipe lib))
   ((equal recipe *witnesses-character-fix*)
    (witnesses-define lib recipe (list *library-x*)
                      (proof-ite (list *witnesses-characterp* *library-x*) *library-x*
                                 (proof-quote '("char" 0)))))
   ((equal recipe *witnesses-rational-fix*)
    (witnesses-define lib recipe (list *library-x*)
                      (proof-ite (list *library-rationalp* *library-x*) *library-x* *proof-zero*)))
   (t
    (let ((name (proof-sym (concatenate 'string "T1-CONSTANT-"
                                       (if (stringp recipe) recipe (proof-datum-text recipe))
                                       "-" (decimal-text arity))
                           "ACL2")))
      (proof-with-checked-results ((indices (seq-range 1 (1+ arity) 1)))
        (let ((constant (assoc-equal recipe *witnesses-constants*)))
          (if constant
              (witnesses-define lib name (witnesses-formals indices) (cdr constant))
            '(:failure "failure" ""))))))))

(mutual-recursion
 (defun witnesses-conditional-test-option (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((or (not (consp term)) (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
         ((proof-is-call term *proof-if*)
          (if (consp (cdr term))
              (proof-with-checked-results ((inner (witnesses-conditional-test-option (cadr term))))
                (if (and (car inner) (not (equal (car inner) 0)) (not (equal (car inner) "")))
                    inner
                  (list (cadr term))))
            '(:failure "failure" "")))
         (t (witnesses-conditional-test-arguments (cdr term)))))

 (defun witnesses-conditional-test-arguments (arguments)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (proof-with-checked-results ((test (witnesses-conditional-test-option (car arguments))))
       (or test (witnesses-conditional-test-arguments (cdr arguments)))))))

(defun witnesses-rational-negation (lib term evidence)
  (if (not (proof-is-call term *library-rationalp*))
      nil
    (proof-with-checked-results ((argument (proof-term-at term 1)))
      (if (not (proof-is-call argument *proof-minus*))
          nil
        (proof-with-checked-results
         ((value (proof-term-at argument 1))
          (premise (proof-find-evidence evidence (list (list *library-rationalp* value)))))
         (if (not premise)
             nil
           (let ((proof (library-library-proof lib)))
             (proof-with-checked-results
              ((axiom (proof-proof-fact proof "rationalp-unary--" (list (list *library-x* value)))))
              (proof-proof-modus-ponens proof axiom premise)))))))))

(defun witnesses-if-selected-test (proof term evidence definitions)
  (if (not (proof-is-call term *proof-if*))
      nil
    (proof-with-checked-results
     ((test (proof-term-at term 1))
      (yes (proof-term-at term 2)))
     (if (not (equal test yes))
         nil
       (proof-with-checked-results
        ((simplified (proof-proof-simplify proof test evidence definitions)))
        (if (not (and simplified (equal (caddr (proof-step-first simplified)) *proof-true*)))
            nil
          (proof-with-checked-results
           ((known (proof-proof-true-from-eq proof simplified))
            (no (proof-term-at term 3))
            (rule (proof-proof-fact proof (proof-sym "SELF-IF-RETURNS-TRUE-TEST" "ACL2")
                                    (list (list *library-x* test) (list *library-y* no))))
            (cut (proof-proof-cut proof known rule)))
           (proof-proof-front proof cut term))))))))

(defund witnesses-formula-reduction (lib term definitions evidence)
  (let ((proof (library-library-proof lib)))
    (if (equal term *proof-true*)
        (proof-proof-prove proof *proof-true* nil nil)
      (proof-with-checked-results
       ((premise (proof-find-evidence evidence (list term)))
        (premise (or premise (witnesses-rational-negation lib term evidence)))
        (premise (or premise (witnesses-if-selected-test proof term evidence definitions))))
       (if premise
           premise
         (proof-with-checked-results
          ((reduction (proof-proof-simplify proof term evidence definitions))
           (reduced-term (if reduction (caddr (proof-step-first reduction)) term)))
          (if (and reduction (not (equal reduced-term term)))
              (if (equal reduced-term *proof-true*)
                  (proof-proof-true-from-eq proof reduction)
                (list :reduce reduced-term reduction))
            (proof-with-checked-results ((test-option (witnesses-conditional-test-option term)))
              (let ((test (car test-option)))
                (proof-with-checked-results
                 ((known (and test-option (proof-find-evidence evidence (list test (proof-neg test))))))
                 (if (or (not test-option) known)
                     *terms-unproved*
                   (proof-with-checked-results
                    ((known (witnesses-rational-negation lib test evidence)))
                    (if known
                        (list :known known)
                      (list :split test))))))))))))))

(defund witnesses-branch-evidence (proof evidence test holds)
  (proof-with-checked-results ((assumption (proof-proof-assume proof test holds)))
    (append evidence (list assumption))))

(defun witnesses-prove-formula (n lib term definitions evidence)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "witnesses-prove-formula")
    (let ((reduction (witnesses-formula-reduction lib term definitions evidence))
          (proof (library-library-proof lib)))
      (case (car reduction)
        (:reduce
         (proof-with-checked-results
          ((reduced (witnesses-prove-formula (1- n) lib (cadr reduction) definitions evidence)))
          (proof-proof-transport proof reduced (caddr reduction))))
        (:known
         (witnesses-prove-formula (1- n) lib term definitions (append evidence (cdr reduction))))
        (:split
         (let ((test (cadr reduction)))
           (proof-with-checked-results
            ((yes-evidence (witnesses-branch-evidence proof evidence test t))
             (yes (witnesses-prove-formula (1- n) lib term definitions yes-evidence))
             (no-evidence (witnesses-branch-evidence proof evidence test nil))
             (no (witnesses-prove-formula (1- n) lib term definitions no-evidence)))
            (proof-proof-cases proof test yes no))))
        (otherwise reduction)))))

(mutual-recursion
 (defun witnesses-df-fact-locations (term path)
   (declare (xargs :measure (acl2-count term)))
   (if (or (not (consp term)) (not (proof-compound term)) (proof-is-call term *proof-quote*))
       nil
     (append (witnesses-df-fact-argument-locations (cdr term) path 1)
             (if (proof-is-call term *witnesses-constrained-to-df*) (list path) nil))))

 (defun witnesses-df-fact-argument-locations (arguments path index)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (append (witnesses-df-fact-locations (car arguments) (append path (list index)))
             (witnesses-df-fact-argument-locations (cdr arguments) path (1+ index))))))

(defun witnesses-term-at-path (term path)
  (declare (xargs :measure (acl2-count path)))
  (if (endp path)
      term
    (proof-with-checked-results ((arg (proof-term-at term (car path))))
      (witnesses-term-at-path arg (cdr path)))))

(defun witnesses-df-fact-rewrite (proof step paths)
  (declare (xargs :measure (acl2-count paths)))
  (if (endp paths)
      (proof-proof-tidy proof step)
    (let ((path (car paths)))
      (proof-with-checked-results
       ((literal (proof-step-first step))
        (term (witnesses-term-at-path literal (cdr path)))
        (expansion (proof-proof-unfold proof (cons *witnesses-to-df* (cdr term))))
        (inverse (proof-proof-symmetric proof expansion))
        (step (proof-proof-rewrite proof step inverse path)))
       (witnesses-df-fact-rewrite proof step (cdr paths))))))

(defun witnesses-df-fact (lib name bindings)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((step (proof-proof-fact proof (proof-sym name "ACL2") bindings))
      (literal (proof-step-first step)))
     (witnesses-df-fact-rewrite proof step (witnesses-df-fact-locations literal '(1))))))

(defun witnesses-dfp-proof (lib value rational fixed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((expansion (proof-proof-unfold proof (list *witnesses-dfp* value)))
      (selected (proof-proof-select proof (caddr (proof-step-first expansion)) rational))
      (equality (proof-proof-unfold proof (caddr (proof-step-first selected))))
      (chain (proof-proof-chain proof expansion (list selected equality))))
     (proof-proof-transport proof fixed chain))))

(defun witnesses-dfp-fixed-point (lib premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first premise))
      (opened (proof-proof-unfold proof literal))
      (step (proof-proof-rewrite proof premise opened '(1)))
      (conjuncts (proof-proof-conjunct proof step))
      (numeric-equal (cadr conjuncts))
      (literal (proof-step-first numeric-equal))
      (opened (proof-proof-unfold proof literal))
      (step (proof-proof-rewrite proof numeric-equal opened '(1))))
     (proof-proof-tidy proof step))))

(defun witnesses-prove-implication (lib term premise consequence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof term))
      (body (caddr (proof-step-first opened)))
      (selected-premise (proof-proof-select proof body premise))
      (selected-consequence (proof-proof-select proof (caddr body) consequence))
      (selected (proof-proof-chain proof opened (list selected-premise selected-consequence)))
      (yes (proof-proof-true-from-eq proof selected))
      (not-premise (proof-proof-if-false proof body))
      (rejected (proof-proof-chain proof opened (list not-premise)))
      (no (proof-proof-true-from-eq proof rejected))
      (test (proof-term-at term 1)))
     (proof-proof-cases proof test yes no))))

(defun witnesses-rounding-formula (lib name term)
  (let ((proof (library-library-proof lib)))
    (cond
     ((text-starts-with name "RATIONALP-")
      (proof-with-checked-results
       ((value (proof-term-at term 1))
        (argument (proof-term-at value 1)))
       (witnesses-df-fact lib "RATIONALP-CONSTRAINED-TO-DF" (list (list *library-x* argument)))))
     ((equal name "DF-ROUND-MONOTONICITY")
      (witnesses-df-fact lib "CONSTRAINED-TO-DF-MONOTONICITY" nil))
     ((equal name "DFP-DF-ROUND")
      (proof-with-checked-results
       ((value (proof-term-at term 1))
        (argument (proof-term-at value 1))
        (bindings (list (list *library-x* argument)))
        (rational (witnesses-df-fact lib "RATIONALP-CONSTRAINED-TO-DF" bindings))
        (fixed (witnesses-df-fact lib "CONSTRAINED-TO-DF-IDEMPOTENT" bindings)))
       (witnesses-dfp-proof lib value rational fixed)))
     (t
      (proof-with-checked-results
       ((test (proof-term-at term 1))
        (premise (proof-proof-assume proof test t))
        (fixed (witnesses-dfp-fixed-point lib premise))
        (fixed (if (equal name "TO-DF-OF-CONSTRAINED-DF-RATIONALIZE")
                   (proof-with-checked-results
                    ((value (proof-term-at test 1))
                     (idem (witnesses-df-fact lib "CONSTRAINED-TO-DF-IDEMPOTENT"
                                              (list (list *library-x* value))))
                     (rewritten (proof-proof-rewrite proof idem fixed '(1 2))))
                    (proof-proof-tidy proof rewritten))
                 fixed)))
       (witnesses-prove-implication lib term premise fixed))))))

(defun witnesses-zero-dfp (lib term)
  (let ((proof (library-library-proof lib))
        (fact (proof-sym "SELF-DFP-ZERO" "ACL2")))
    (proof-with-checked-results
     ((lib (if (assoc-equal fact (proof-proof-facts proof))
               lib
             (proof-with-checked-results
              ((fixed (witnesses-df-fact lib "CONSTRAINED-TO-DF-0" nil))
               (rational (proof-proof-prove proof (list *library-rationalp* *proof-zero*) nil nil))
               (step (witnesses-dfp-proof lib *proof-zero* rational fixed)))
              (library-library-lemma lib "DFP-ZERO" (list *witnesses-dfp* *proof-zero*) step nil))))
      (proof (library-library-proof lib))
      (step (proof-proof-fact proof fact nil))
      (value (proof-term-at term 1))
      (unfolded (proof-proof-unfold proof value))
      (step (library-library-transport-argument lib step unfolded 1)))
     (cons step lib))))

(defun witnesses-make-witnesses (lib functions recipes)
  (declare (xargs :measure (acl2-count functions)))
  (cond
   ((endp functions) (cons nil lib))
   ((endp recipes) (cons nil lib))
   (t
    (proof-with-checked-results
     ((function (proof-list-of-length (car functions) 2))
      (witness (witnesses-witness lib (car recipes) (cadr function)))
      (rest (witnesses-make-witnesses (cdr witness) (cdr functions) (cdr recipes))))
     (cons (cons (car witness) (car rest)) (cdr rest))))))

(defun witnesses-name-bindings (functions witnesses bindings)
  (declare (xargs :measure (acl2-count functions)))
  (cond ((endp functions) bindings)
        ((endp witnesses) bindings)
        (t (witnesses-name-bindings (cdr functions) (cdr witnesses)
                                   (table-put bindings (caar functions) (car witnesses))))))

(defun witnesses-prove-goal (lib formula-name goal definitions witnesses witnessed)
  (let ((known (assoc-equal goal witnessed)))
    (cond
     (known (cons (cdr known) lib))
     ((equal witnesses (list *witnesses-to-df*))
      (proof-with-checked-results
       ((name (proof-term-at formula-name 2))
        (step (witnesses-rounding-formula lib name goal)))
       (cons step lib)))
     ((proof-is-call goal *witnesses-dfp*) (witnesses-zero-dfp lib goal))
     (t
      (proof-with-checked-results
       ((step (witnesses-prove-formula 1000000 lib goal (append definitions witnesses) nil)))
       (cons step lib))))))

(defun witnesses-formula-proofs (lib formulas names definitions witnesses witnessed)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      (cons nil lib)
    (proof-with-checked-results
     ((formula (proof-list-of-length (car formulas) 2))
      (goal (terms-replace-calls (cadr formula) names))
      (result (witnesses-prove-goal lib (car formula) goal definitions witnesses witnessed))
      (rest (witnesses-formula-proofs (cdr result) (cdr formulas) names definitions witnesses
                                      (table-put witnessed goal (car result)))))
     (cons (cons (list (list goal) (car result)) (car rest)) (cdr rest)))))

(defun witnesses-witness-proofs (lib data)
  (proof-with-checked-results
   ((data (proof-list-of-length data 2))
    (first (proof-term-at (car data) 0))
    (name (proof-term-at first 0))
    (label (proof-term-at name 2)))
   (let* ((recipe-entry (assoc-equal label *witnesses-witnesses*))
          (functions (car data))
          (formulas (cadr data)))
     (if (not recipe-entry)
         '(:failure "failure" "")
       (let ((recipes (cdr recipe-entry)))
         (proof-with-checked-results ((result (witnesses-make-witnesses lib functions recipes)))
           (let ((witnesses (car result))
                 (lib (cdr result)))
             (if (not (and (equal (len witnesses) (len recipes))
                           (equal (len recipes) (len functions))))
                 '(:failure "failure" "")
               (let ((names (witnesses-name-bindings functions witnesses nil))
                     (definitions (list *library-implies* *proof-not* *witnesses-booleanp*
                                        *witnesses-eq* *witnesses-null* *witnesses-atom* *witnesses-endp*
                                        *library-natp* *termination-return-last*
                                        (proof-sym "ALL-FUNCTION-SYMBOLPS" "ACL2")
                                        (proof-sym "SUBSETP-EQUAL" "ACL2"))))
                 (proof-with-checked-results
                  ((proved (witnesses-formula-proofs lib formulas names definitions witnesses nil))
                   (finished (lemmas-slice-library-share-proofs (cdr proved) (car proved) names))
                   (entry (proof-proof-entry "witness" name (cons name witnesses) (car finished))))
                  (cons (list entry "witness substitution") (cdr finished))))))))))))
