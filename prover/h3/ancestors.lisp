(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h3-ancestors-commutes* (proof-sym "EQUAL-MOD-COMMUTING" "ACL2"))
(defconst *h3-ancestors-member* (proof-sym "MEMBER-EQUAL-MOD-COMMUTING" "ACL2"))
(defconst *h3-ancestors-strip* (proof-sym "STRIP-ANCESTOR-LITERALS" "ACL2"))
(defconst *h3-ancestors-check* (proof-sym "ANCESTORS-CHECK1" "ACL2"))
(defconst *h3-ancestors-builtin-check* (proof-sym "ANCESTORS-CHECK-BUILTIN" "ACL2"))

(defun h3-ancestors-step-term (step index)
  (if (null step)
      '(:failure "MalformedTacticInput" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun h3-ancestors-symmetry (library)
  (let* ((proof (library-library-proof library))
         (name (proof-sym "SELF-H3-EQUAL-MOD-COMMUTING-SYMMETRIC" "ACL2")))
    (if (assoc-equal name (proof-proof-facts proof))
        (cons name library)
      (proof-with-checked-results
          ((left (list *h3-ancestors-commutes* *library-x* *library-y* *proof-false*))
           (right (list *h3-ancestors-commutes* *library-y* *library-x* *proof-false*))
           (claim (list *library-implies* left right))
           (definitions (append *h3-lists-list-definitions*
                                (list *h3-ancestors-commutes* (proof-sym "MEMBER-EQUAL" "ACL2"))))
           (rules (h3-rewrite-rules-init library *h3-lists-selectors* nil))
           (search (h3-rewrite-search-init library definitions nil rules 500 nil))
           (step (car (h3-rewrite-search-prove search claim nil)))
           (library (library-library-lemma library "H3-EQUAL-MOD-COMMUTING-SYMMETRIC"
                                           claim step nil)))
        (cons name library)))))

(defun h3-ancestors-member-cons (library)
  (let* ((proof (library-library-proof library))
         (name (proof-sym "SELF-H3-MEMBER-COMMUTING-CONS" "ACL2")))
    (if (assoc-equal name (proof-proof-facts proof))
        (cons name library)
      (proof-with-checked-results
          ((cons-term (list *proof-cons* *library-y* *library-z*))
           (call (list *h3-ancestors-member* *library-x* cons-term *proof-false*))
           (test (list *h3-ancestors-commutes* *library-x* *library-y* *proof-false*))
           (rest (list *h3-ancestors-member* *library-x* *library-z* *proof-false*))
           (claim (proof-eq call (proof-ite test cons-term rest)))
           (rules (h3-rewrite-rules-init library *h3-lists-selectors* nil))
           (search (h3-rewrite-search-init library *h3-lists-list-definitions* (list call) rules 150 t))
           (step (car (h3-rewrite-search-prove search claim nil)))
           (library (library-library-lemma library "H3-MEMBER-COMMUTING-CONS" claim step nil)))
        (cons name library)))))

(defun h3-ancestors-assumptions (tests proof)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((step (proof-proof-assume proof (caar tests) (cadar tests)))
         (rest (h3-ancestors-assumptions (cdr tests) proof)))
      (cons step rest))))

(defun h3-ancestors-check-membership-prove-case-leaf
    (value tests template evidence library definitions ancestors rules)
  (proof-with-checked-results
      ((formula (proof-subst template (list (cons *proof-result* value))))
       (assumptions (h3-ancestors-assumptions tests (library-library-proof library)))
       (hypotheses (append evidence assumptions))
       (search (h3-rewrite-search-init library definitions
                                      (list (list *h3-ancestors-strip* ancestors)) rules 65 nil)))
    (car (h3-rewrite-search-prove search formula hypotheses))))

(defun h3-ancestors-check-membership-prove-case-leaves
    (requests template evidence library definitions ancestors rules)
  (if (endp requests)
      nil
    (proof-with-checked-results
        ((request (car requests))
         (step (h3-ancestors-check-membership-prove-case-leaf
                (car request) (cadr request) template evidence library definitions ancestors rules))
         (rest (h3-ancestors-check-membership-prove-case-leaves
                (cdr requests) template evidence library definitions ancestors rules)))
      (cons (cons request step) rest))))

(defun h3-ancestors-check-membership-prove-case (evidence library names translated result ancestors)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((rules (h3-rewrite-rules-init library names nil))
         (definitions (append *h3-lists-list-definitions* (list (proof-sym "HIDE" "ACL2"))))
         (normalizer (h3-rewrite-search-init library definitions nil nil 150 t))
         (right (h3-ancestors-step-term translated 2))
         (context (h3-rewrite-search-context normalizer evidence))
         (reduced (car (h3-rewrite-search-reduce normalizer right context nil nil)))
         (normal (proof-proof-chain proof translated (list reduced)))
         (template (list *library-implies*
                         (proof-ite (list *h3-counts-mv-nth* *proof-zero* *proof-result*)
                                    (list *h3-counts-mv-nth* *proof-one* *proof-result*)
                                    *proof-false*)
                         result))
         (right (h3-ancestors-step-term normal 2))
         (requests (proof-proof-by-value-leaves proof right nil))
         (replies (h3-ancestors-check-membership-prove-case-leaves
                   requests template evidence library definitions ancestors rules))
         (case-step (proof-proof-by-value proof right template replies nil))
         (symmetric (proof-proof-symmetric proof normal)))
      (proof-proof-rewrite-result proof case-step symmetric template *proof-result*))))

(defun h3-ancestors-check-membership-induct
    (n library claim ancestors replacements names translated result replies induction-result)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "h3-ancestors-check-membership-induct"))
        ((h3-induction-request-p induction-result)
         (let* ((reply (h3-ancestors-check-membership-prove-case
                        (h3-induction-request-evidence induction-result)
                        library names translated result ancestors))
                (replies (append replies (list reply)))
                (next (if (failure-p reply)
                          reply
                        (h3-induction-structural-induction library claim ancestors replacements replies))))
           (h3-ancestors-check-membership-induct
            (1- n) library claim ancestors replacements names translated result replies next)))
        (t induction-result)))

(defun h3-ancestors-check-formals (proof)
  (let ((entry (assoc-equal *h3-ancestors-check* (proof-proof-definitions proof))))
    (if entry
        (proof-term-at (cdr entry) 0)
      '(:failure "MissingProofData" ""))))

(defun h3-ancestors-check-membership (library names)
  (let* ((proof (library-library-proof library))
         (name (proof-sym "SELF-H3-ANCESTOR-MEMBERSHIP" "ACL2")))
    (proof-with-checked-results
        ((formals (h3-ancestors-check-formals proof))
         (literal (proof-term-at formals 1))
         (ancestors (proof-term-at formals (- (len formals) 2)))
         (call (cons *h3-ancestors-check* formals))
         (antecedent (proof-ite (list *h3-counts-mv-nth* *proof-zero* call)
                                (list *h3-counts-mv-nth* *proof-one* call) *proof-false*))
         (result (list *h3-ancestors-member* literal (list *h3-ancestors-strip* ancestors) *proof-false*))
         (claim (list *library-implies* antecedent result))
         (translated (proof-proof-unfold proof call))
         (binding (cons ancestors (list *library-cdr* ancestors)))
         (replacements (list (list (list binding) 3)))
         (initial (h3-induction-structural-induction library claim ancestors replacements nil))
         (step (h3-ancestors-check-membership-induct
                1000000 library claim ancestors replacements names translated result nil initial))
         (library (library-library-lemma library "H3-ANCESTOR-MEMBERSHIP" claim step nil)))
      (cons name library))))

(defun h3-ancestors-ancestors-check-leaf (value tests template hypothesis library rules)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((claim (proof-subst template (list (cons *proof-result* value))))
         (literal (proof-step-first hypothesis)))
      (if (equal claim literal)
          hypothesis
        (proof-with-checked-results
            ((context (h3-ancestors-assumptions tests proof))
             (search (h3-rewrite-search-init library *h3-lists-list-definitions* nil rules 24 nil)))
          (car (h3-rewrite-search-prove search claim context)))))))

(defun h3-ancestors-ancestors-check-leaves (requests template hypothesis library rules)
  (if (endp requests)
      nil
    (proof-with-checked-results
        ((request (car requests))
         (step (h3-ancestors-ancestors-check-leaf
                (car request) (cadr request) template hypothesis library rules))
         (rest (h3-ancestors-ancestors-check-leaves (cdr requests) template hypothesis library rules)))
      (cons (cons request step) rest))))

(defun h3-ancestors-ancestors-check-by-value (expanded template hypothesis library rules)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((right (h3-ancestors-step-term expanded 2))
         (requests (proof-proof-by-value-leaves proof right nil))
         (replies (h3-ancestors-ancestors-check-leaves requests template hypothesis library rules)))
      (proof-proof-by-value proof right template replies nil))))

(defun h3-ancestors-ancestors-check-finish (library source-eq goal actual expanded hypothesis rules template)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((instantiated (proof-subst template (list (cons *proof-result* actual)))))
      (let ((leaves (and (equal instantiated goal)
                         (h3-ancestors-ancestors-check-by-value expanded template hypothesis library rules))))
        (cond ((or (null leaves) (h3-rewrite-unproved-p leaves))
               (proof-with-checked-results
                   ((search (h3-rewrite-search-init library *h3-lists-list-definitions* nil rules 150 nil))
                    (result (car (h3-rewrite-search-prove search goal (list expanded hypothesis))))
                    (step (proof-proof-transport proof result source-eq)))
                 (cons step library)))
              ((failure-p leaves) leaves)
              (t (proof-with-checked-results
                     ((symmetric (proof-proof-symmetric proof expanded))
                      (result (proof-proof-rewrite-result proof leaves symmetric template *proof-result*))
                      (step (proof-proof-transport proof result source-eq)))
                   (cons step library))))))))

(defun h3-ancestors-ancestors-check (library formula)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof "consp-cons" nil))
         (cons-step (h3-rewrite-nonnil-from-type library fact))
         (claim (proof-step-first cons-step))
         (library (library-library-lemma library "H3-CONS-NON-NIL" claim cons-step nil))
         (indexed (h3-counts-indexed-selectors library 1))
         (symmetric (h3-ancestors-symmetry (cdr indexed)))
         (membership (h3-ancestors-member-cons (cdr symmetric)))
         (names (append *h3-lists-selectors* (car indexed)
                        (list (car symmetric) (car membership) (proof-sym "SELF-H3-CONS-NON-NIL" "ACL2"))))
         (property (h3-ancestors-check-membership (cdr membership) names))
         (library (cdr property))
         (proof (library-library-proof library))
         (search (h3-rewrite-search-init library nil nil nil 150 nil))
         (source-eq (car (h3-rewrite-search-reduce search formula nil nil nil)))
         (goal (h3-ancestors-step-term source-eq 2))
         (antecedent (proof-term-at goal 1))
         (test (proof-term-at antecedent 1))
         (actual (proof-term-at test 2))
         (head (proof-term-at actual 0)))
      (if (not (equal head *h3-ancestors-builtin-check*))
          '(:failure "ProofMismatch" "")
        (proof-with-checked-results
            ((definitions (list *h3-ancestors-builtin-check* (proof-sym "HIDE" "ACL2")))
             (normalizer (h3-rewrite-search-init library definitions nil nil 150 t))
             (expanded (car (h3-rewrite-search-reduce normalizer actual nil nil nil)))
             (right (h3-ancestors-step-term expanded 2))
             (recursive (proof-term-at right 3))
             (head (proof-term-at recursive 0)))
          (if (not (equal head *h3-ancestors-check*))
              '(:failure "ProofMismatch" "")
            (proof-with-checked-results
                ((formals (h3-ancestors-check-formals proof))
                 (hypothesis (proof-proof-fact proof (car property) (seq-zip formals (cdr recursive))))
                 (rules (h3-rewrite-rules-init library names nil))
                 (result (proof-term-at goal 2))
                 (template (list *library-implies*
                                 (proof-ite (list *h3-counts-mv-nth* *proof-zero* *proof-result*)
                                            (list *h3-counts-mv-nth* *proof-one* *proof-result*)
                                            *proof-false*)
                                 result)))
              (h3-ancestors-ancestors-check-finish
               library source-eq goal actual expanded hypothesis rules template))))))))
