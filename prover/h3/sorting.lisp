(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-sorting-evens* (proof-sym "EVENS" "ACL2"))
(defconst *h3-sorting-odds* (proof-sym "ODDS" "ACL2"))
(defconst *h3-sorting-merge* (proof-sym "STRICT-MERGE-SYMBOL<" "ACL2"))
(defconst *h3-sorting-revappend* (proof-cl "REVAPPEND"))
(defconst *h3-sorting-symbolp* (proof-cl "SYMBOLP"))

(defun h3-sorting-register (lib label claim step guards)
  (proof-with-checked-results
   ((lib (library-library-lemma lib (concatenate 'string "H3-" label) claim step guards)))
   (cons (proof-sym (concatenate 'string "SELF-H3-" label) "ACL2") lib)))

(defun h3-sorting-symbol-list-rules (lib)
  (let* ((cons-test (list *h3-lists-symbol-listp*
                          (list *proof-cons* *library-x* *library-y*)))
         (body (proof-ite (list *h3-sorting-symbolp* *library-x*)
                          (list *h3-lists-symbol-listp* *library-y*) *proof-false*))
         (source (list *h3-lists-symbol-listp* *library-x*))
         (empty (list *h3-lists-symbol-listp* *proof-false*))
         (head-rule (list *library-implies* source (list *h3-sorting-symbolp*
                                                         (list *library-car* *library-x*)))))
    (proof-with-checked-results
     ((tail (h3-lists-list-tail-rule lib *h3-lists-symbol-listp*))
      (lib (cdr tail))
      (common (append *h3-lists-selectors* (list (car tail))))
      (rules (h3-rewrite-rules-init lib common nil))
      (step (car (h3-rewrite-search-prove
                  (h3-rewrite-search-init lib *h3-lists-list-definitions*
                                          (list cons-test) rules 150 t)
                  (proof-eq cons-test body) nil)))
      (cons-rule (proof-step-first step))
      (constructor (h3-sorting-register lib "SYMBOL-LIST-CONS" cons-rule step nil))
      (head-search (h3-rewrite-search-with-lib
                    (h3-rewrite-search-init lib *h3-lists-list-definitions*
                                            (list source) rules 150 nil)
                    (cdr constructor)))
      (head (car (h3-rewrite-search-prove head-search head-rule nil)))
      (head-name (h3-sorting-register (cdr constructor) "SYMBOL-LIST-CAR" head-rule head nil))
      (nil-search (h3-rewrite-search-with-lib
                   (h3-rewrite-search-init lib *h3-lists-list-definitions*
                                           (list empty) rules 150 nil)
                   (cdr head-name)))
      (step (car (h3-rewrite-search-prove nil-search empty nil)))
      (nil-name (h3-sorting-register (cdr head-name) "SYMBOL-LIST-NIL" empty step nil)))
     (cons (append common (list (car constructor) (car head-name) (car nil-name)))
           (cdr nil-name)))))

(defund h3-sorting-symbol-list-reverse-prove-case (evidence lib rev names claim)
  (proof-with-checked-results ((rules (h3-rewrite-rules-init lib names nil)))
    (car (h3-rewrite-search-prove
          (h3-rewrite-search-init lib *h3-lists-list-definitions* (list rev) rules 150 nil)
          claim evidence))))

(defund h3-sorting-structural-induction-result (lib claim replacements replies)
  (h3-induction-structural-induction lib claim *library-x* replacements replies))

(defun h3-sorting-reverse-induction (n lib rev names claim replacements replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h3-sorting-reverse-induction")
    (let ((step (h3-sorting-structural-induction-result lib claim replacements replies)))
      (if (h3-induction-request-p step)
          (proof-with-checked-results
           ((case-step (h3-sorting-symbol-list-reverse-prove-case
                        (h3-induction-request-evidence step) lib rev names claim)))
           (h3-sorting-reverse-induction
            (1- n) lib rev names claim replacements (append replies (list case-step))))
        step))))

(defun h3-sorting-symbol-list-reverse (lib names)
  (let* ((rev (list *h3-sorting-revappend* *library-x* *library-y*))
         (x-type (list *h3-lists-symbol-listp* *library-x*))
         (y-type (list *h3-lists-symbol-listp* *library-y*))
         (hypothesis (proof-ite x-type y-type *proof-false*))
         (claim (list *library-implies* hypothesis (list *h3-lists-symbol-listp* rev)))
         (mapping (list (cons *library-x* (list *library-cdr* *library-x*))
                        (cons *library-y* (list *proof-cons*
                                                (list *library-car* *library-x*) *library-y*)))))
    (proof-with-checked-results
     ((step (h3-sorting-reverse-induction 1000000 lib rev names claim (list (list mapping 3)) nil)))
     (h3-sorting-register lib "SYMBOL-LIST-REVAPPEND" claim step nil))))

(defun h3-sorting-skips-one (lib variable)
  (let* ((source (list *library-count* variable))
         (target (list *library-count* (list *library-cdr* (list *library-cdr* variable))))
         (consp-test (list *proof-consp* variable)))
    (proof-with-checked-results
     ((hypotheses (descent-hypotheses-init lib (list (list consp-test t)) nil))
      (step (descent-selector-decrease lib (list *proof-ordinal-less* target source) hypotheses)))
     (car step))))

(defund h3-sorting-evens-types-prove-case (evidence lib call names claim)
  (proof-with-checked-results ((rules (h3-rewrite-rules-init lib names nil)))
    (car (h3-rewrite-search-prove
          (h3-rewrite-search-init lib *h3-lists-list-definitions*
                                  (list call (list *h3-lists-symbol-listp* *proof-false*))
                                  rules 150 nil)
          claim evidence))))

(defun h3-sorting-evens-type-induction (n lib call names claim replacements replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h3-sorting-evens-type-induction")
    (let ((step (h3-sorting-structural-induction-result lib claim replacements replies)))
      (if (h3-induction-request-p step)
          (proof-with-checked-results
           ((case-step (h3-sorting-evens-types-prove-case
                        (h3-induction-request-evidence step) lib call names claim)))
           (h3-sorting-evens-type-induction
            (1- n) lib call names claim replacements (append replies (list case-step))))
        step))))

(defun h3-sorting-evens-types (lib names)
  (let* ((call (list *h3-sorting-evens* *library-x*))
         (claim (list *library-implies* (list *h3-lists-symbol-listp* *library-x*)
                      (list *h3-lists-symbol-listp* call)))
         (mapping (list (cons *library-x* (list *library-cdr* (list *library-cdr* *library-x*))))))
    (proof-with-checked-results
     ((decrease (h3-sorting-skips-one lib *library-x*))
      (step (h3-sorting-evens-type-induction
             1000000 lib call names claim (list (list mapping decrease)) nil)))
     (h3-sorting-register lib "SYMBOL-LIST-EVENS" claim step nil))))

(defun h3-sorting-evens-bound-length-after-opening (term lib)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof (list *library-len* term)))
      (value (proof-rewritten-term opened))
      (selected (proof-proof-if-true proof value)))
     (proof-proof-chain proof opened (list selected)))))

(defun h3-sorting-evens-bound-strong (weak-child lib tail second left-cons right-cons)
  (proof-with-checked-results
   ((assumption (proof-proof-assume (library-library-proof lib) second t))
    (adjacent (library-library-cite lib "LEN-CDR-LESS" (list tail) (list assumption)))
    (strict (library-library-compare-chain lib weak-child adjacent))
    (strict (descent-shift lib strict *proof-one* t))
    (strict (library-library-transport-argument lib strict left-cons 1)))
   (library-library-transport-argument lib strict right-cons 2)))

(defund h3-sorting-bound-step-p (step)
  (proof-with-checked-results
   ((literal (proof-step-first step))
    (head (proof-term-at literal 0)))
   (and (equal head *proof-not*)
        (proof-with-checked-results
         ((comparison (proof-term-at literal 1))
          (head (proof-term-at comparison 0)))
         (equal head *proof-less*)))))

(defun h3-sorting-inherited-bound (evidence)
  (if (endp evidence)
      nil
    (proof-with-checked-results
     ((bound (h3-sorting-bound-step-p (car evidence))))
     (if bound
         (car evidence)
       (h3-sorting-inherited-bound (cdr evidence))))))

(defund h3-sorting-evens-bound-prove-case
    (evidence lib tail second left-cons right-cons evens length rule claim)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((inherited (h3-sorting-inherited-bound evidence))
      (rules (h3-rewrite-rules-init lib (append *h3-lists-selectors* (list rule)) nil))
      (search (h3-rewrite-search-init
               lib *h3-lists-list-definitions*
               (list evens length (list *library-len* tail) (list *library-len* *proof-false*)
                     (list *h3-sorting-evens* *proof-false*))
               rules 150 nil)))
     (if inherited
         (proof-with-checked-results
          ((strict (h3-sorting-evens-bound-strong inherited lib tail second left-cons right-cons))
           (yes (library-library-as-weak lib strict))
           (not-second (proof-proof-assume proof second nil))
           (no (car (h3-rewrite-search-prove search claim (append evidence (list not-second))))))
          (proof-proof-cases proof second yes no))
       (car (h3-rewrite-search-prove search claim evidence))))))

(defun h3-sorting-evens-bound-induction
    (n lib tail second left-cons right-cons evens length rule claim replacements replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h3-sorting-evens-bound-induction")
    (let ((step (h3-sorting-structural-induction-result lib claim replacements replies)))
      (if (h3-induction-request-p step)
          (proof-with-checked-results
           ((case-step (h3-sorting-evens-bound-prove-case
                        (h3-induction-request-evidence step)
                        lib tail second left-cons right-cons evens length rule claim)))
           (h3-sorting-evens-bound-induction
            (1- n) lib tail second left-cons right-cons evens length rule claim replacements
            (append replies (list case-step))))
        step))))

(defun h3-sorting-evens-bound (lib)
  (let* ((tail (list *library-cdr* *library-x*))
         (child (list *library-cdr* tail))
         (first (list *proof-consp* *library-x*))
         (second (list *proof-consp* tail))
         (length (list *library-len* *library-x*))
         (evens (list *h3-sorting-evens* *library-x*))
         (left (list *library-len* evens))
         (length-cons (list *library-len* (list *proof-cons* *library-x* *library-y*))))
    (proof-with-checked-results
     ((rules (h3-rewrite-rules-init lib *h3-lists-selectors* nil))
      (length-equality (car (h3-rewrite-search-prove
                             (h3-rewrite-search-init lib nil (list length-cons) rules 150 nil)
                             (proof-eq length-cons (library-plus *proof-one* (list *library-len* *library-y*)))
                             nil)))
      (length-rule (proof-step-first length-equality))
      (registered (h3-sorting-register lib "LEN-CONS" length-rule length-equality nil))
      (rule (car registered))
      (lib (cdr registered))
      (proof (library-library-proof lib))
      (evens-cons (proof-proof-unfold proof evens))
      (opened (proof-rewritten-term evens-cons))
      (selected (proof-proof-if-false proof opened))
      (evens-cons (proof-proof-chain proof evens-cons (list selected)))
      (contains (proof-proof-assume proof first t))
      (endp (proof-term-at (proof-step-clause evens-cons) 1))
      (no-endp (car (h3-rewrite-search-prove
                     (h3-rewrite-search-init lib *h3-lists-list-definitions* nil nil 150 nil)
                     (proof-neg endp) (list contains))))
      (evens-cons (proof-proof-discharge proof evens-cons no-endp))
      (left-cons (proof-proof-reflexive proof left))
      (left-cons (proof-proof-rewrite proof left-cons evens-cons '(1 2 1)))
      (length-cons-step (proof-proof-fact
                         proof rule (list (list *library-x* (list *library-car* *library-x*))
                                          (list *library-y* (list *h3-sorting-evens* child)))))
      (left-cons (proof-proof-chain proof left-cons (list length-cons-step)))
      (right-cons (h3-sorting-evens-bound-length-after-opening *library-x* lib))
      (claim (library-le left length))
      (decrease (h3-sorting-skips-one lib *library-x*))
      (weak (h3-sorting-evens-bound-induction
             1000000 lib tail second left-cons right-cons evens length rule claim
             (list (list (list (cons *library-x* child)) decrease)) nil))
      (registered (h3-sorting-register lib "EVENS-LENGTH-BOUND" claim weak nil))
      (weak-name (car registered))
      (lib (cdr registered))
      (weak-child (proof-proof-fact (library-library-proof lib) weak-name
                                   (list (list *library-x* child))))
      (strict (h3-sorting-evens-bound-strong weak-child lib tail second left-cons right-cons)))
     (cons (list weak-name strict) lib))))

(defun h3-sorting-sort-hypothesis (terms)
  (if (endp terms)
      *proof-false*
    (let ((hypothesis (h3-sorting-sort-hypothesis (cdr terms)))
          (predicate (list *h3-lists-symbol-listp* (car terms))))
      (if (equal hypothesis *proof-false*)
          predicate
        (proof-ite predicate hypothesis *proof-false*)))))

(defund h3-sorting-sort-replacement (lib variable measure term step)
  (proof-with-checked-results
   ((ordinal (library-library-ordinal-comparison lib (list *library-len* term) measure))
    (transported (proof-proof-transport (library-library-proof lib) step ordinal)))
   (list (list (cons variable term)) transported)))

(defun h3-sorting-sort-replacements (lib variable measure terms steps)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      nil
    (proof-with-checked-results
     ((replacement (h3-sorting-sort-replacement lib variable measure (car terms) (car steps)))
      (rest (h3-sorting-sort-replacements lib variable measure (cdr terms) (cdr steps))))
     (cons replacement rest))))

(defund h3-sorting-symbol-sort-prove-case (evidence lib names merge-name formula)
  (proof-with-checked-results
   ((result (proof-term-at formula 2))
    (call (proof-term-at result 1))
    (rules (h3-rewrite-rules-init lib (append names (list merge-name)) nil)))
   (car (h3-rewrite-search-prove
         (h3-rewrite-search-init lib (append *h3-lists-list-definitions* (list *h3-sorting-odds*))
                                 (list call) rules 150 nil)
         formula evidence))))

(defund h3-sorting-well-founded-result (lib formula measure ordinal replacements replies)
  (h3-induction-well-founded lib formula measure ordinal replacements replies))

(defun h3-sorting-sort-induction (n lib formula measure ordinal replacements names merge-name replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h3-sorting-sort-induction")
    (let ((step (h3-sorting-well-founded-result lib formula measure ordinal replacements replies)))
      (if (h3-induction-request-p step)
          (proof-with-checked-results
           ((case-step (h3-sorting-symbol-sort-prove-case
                        (h3-induction-request-evidence step) lib names merge-name formula)))
           (h3-sorting-sort-induction
            (1- n) lib formula measure ordinal replacements names merge-name
            (append replies (list case-step))))
        step))))

(defun h3-sorting-sort-final (lib formula names merge-name weak-name even-strict variable)
  (let* ((proof (library-library-proof lib))
         (even (list *h3-sorting-evens* variable))
         (odd (list *h3-sorting-odds* variable))
         (measure (list *library-len* variable))
         (rest (list *library-cdr* variable)))
    (proof-with-checked-results
     ((weak-odd (proof-proof-fact proof weak-name (list (list *library-x* rest))))
      (contains (proof-proof-assume proof (list *proof-consp* variable) t))
      (tail-strict (library-library-cite lib "LEN-CDR-LESS" (list variable) (list contains)))
      (odd-strict (library-library-compare-chain lib weak-odd tail-strict))
      (opened (proof-proof-unfold proof odd))
      (symmetric (proof-proof-symmetric proof opened))
      (odd-strict (proof-proof-rewrite proof odd-strict symmetric '(1 1 1)))
      (odd-strict (proof-proof-tidy proof odd-strict))
      (replacements (h3-sorting-sort-replacements
                     lib variable measure (list even odd) (list even-strict odd-strict)))
      (natural (library-library-natural lib measure))
      (ordinal (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural)))
      (step (h3-sorting-sort-induction
             1000000 lib formula measure ordinal replacements names merge-name nil)))
     (cons step lib))))

(defun h3-sorting-symbol-sort (lib formula)
  (proof-with-checked-results
   ((lib (h3-merges-arithmetic lib))
    (rules (h3-sorting-symbol-list-rules lib))
    (names (car rules))
    (reverse-rule (h3-sorting-symbol-list-reverse (cdr rules) names))
    (evens-rule (h3-sorting-evens-types (cdr reverse-rule) names))
    (lib (cdr evens-rule))
    (names (append names (list (car reverse-rule) (car evens-rule))))
    (entry (or (assoc-equal *h3-sorting-merge* (proof-proof-definitions (library-library-proof lib)))
               '(:failure "missing-proof-data" "")))
    (merge (cons *h3-sorting-merge* (cadr entry)))
    (claim (list *library-implies* (h3-sorting-sort-hypothesis (cdr merge))
                 (list *h3-lists-symbol-listp* merge)))
    (result (h3-merges-two-list-merge lib claim names))
    (registered (h3-sorting-register (cdr result) "SYMBOL-LIST-STRICT-MERGE" claim (car result) nil))
    (bound (h3-sorting-evens-bound (cdr registered)))
    (antecedent (proof-term-at formula 1))
    (variable (proof-term-at antecedent 1)))
   (if (equal variable *library-x*)
       (h3-sorting-sort-final
        (cdr bound) formula names (car registered) (caar bound) (cadar bound) variable)
     '(:failure "proof-mismatch" ""))))
