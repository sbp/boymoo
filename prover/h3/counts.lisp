(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-counts-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *h3-counts-evg-type* (proof-sym "FN-COUNT-EVG-REC-TYPE-PRESCRIPTION" "ACL2"))

(mutual-recursion
 (defun h3-counts-nested-calls (value head)
   (declare (xargs :measure (acl2-count value)))
   (if (atom value)
       nil
     (append (if (proof-is-call value head) (list value) nil)
             (if (consp (h3-rewrite-arguments value))
                 (h3-counts-nested-call-args (cdr value) head)
               nil))))
 (defun h3-counts-nested-call-args (args head)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (append (h3-counts-nested-calls (car args) head)
             (h3-counts-nested-call-args (cdr args) head)))))

(defund h3-counts-indexed-selectors-prove-case (evidence lib rev goal)
  (car (h3-rewrite-search-prove
        (h3-rewrite-search-init lib *h3-lists-list-definitions* rev nil 150 nil)
        goal evidence)))

(defund h3-counts-induction-result (lib formula variable replacements replies)
  (h3-induction-structural-induction lib formula variable replacements replies))

(defun h3-counts-mv-nth-induction (n lib goal variable replacements rev replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h3-counts-mv-nth-induction")
    (let ((result (h3-counts-induction-result lib goal variable replacements replies)))
      (if (h3-induction-request-p result)
          (proof-with-checked-results
           ((step (h3-counts-indexed-selectors-prove-case
                   (h3-induction-request-evidence result) lib rev goal)))
           (h3-counts-mv-nth-induction
            (1- n) lib goal variable replacements rev (append replies (list step))))
        result))))

(defun h3-counts-register-mv-nth (lib mv-eq)
  (if (assoc-equal mv-eq (proof-proof-facts (library-library-proof lib)))
      lib
    (let* ((index (proof-sym "N" "ACL2"))
           (rev (list (list *h3-counts-mv-nth* index *library-x*)
                      (list *h3-lists-nth* index *library-x*)))
           (goal (proof-eq (car rev) (cadr rev)))
           (mapping (list (cons index (library-plus *proof-neg-one* index))
                          (cons *library-x* (list *library-cdr* *library-x*)))))
      (proof-with-checked-results
       ((step (h3-counts-mv-nth-induction
               1000000 lib goal index (list (list mapping 9)) rev nil)))
       (library-library-lemma lib "H3-MV-NTH-EQUAL-NTH" goal step nil)))))

(defun h3-counts-define-indexed-selector (lib index label)
  (let* ((argument (list *proof-cons* *library-x* *library-y*))
         (call (list *h3-lists-nth* (proof-quote index) argument))
         (goal (proof-eq call (list *h3-lists-nth* (proof-quote (1- index)) *library-y*))))
    (proof-with-checked-results
     ((rules (h3-rewrite-rules-init lib *h3-lists-selectors* nil))
      (step (car (h3-rewrite-search-prove
                  (h3-rewrite-search-init
                   lib (append *h3-lists-list-definitions* (list *h3-lists-zp* *proof-not*))
                   (list call) rules 150 nil)
                  goal nil))))
     (library-library-lemma lib label goal step nil))))

(defund h3-counts-indexed-selector (lib index)
  (proof-with-checked-results
   ((text (decimal-text index))
    (label (concatenate 'string "H3-NTH-" text "-CONS"))
    (name (proof-sym (concatenate 'string "SELF-" label) "ACL2"))
    (lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
             lib
           (h3-counts-define-indexed-selector lib index label))))
   (cons name lib)))

(defun h3-counts-more-indexed-selectors (remaining index lib names)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      (cons (reverse names) lib)
    (proof-with-checked-results
     ((result (h3-counts-indexed-selector lib index)))
     (h3-counts-more-indexed-selectors
      (1- remaining) (1+ index) (cdr result) (cons (car result) names)))))

(defun h3-counts-indexed-selectors (lib last)
  (let ((mv-eq (proof-sym "SELF-H3-MV-NTH-EQUAL-NTH" "ACL2")))
    (proof-with-checked-results ((lib (h3-counts-register-mv-nth lib mv-eq)))
      (if (integerp last)
          (h3-counts-more-indexed-selectors last 1 lib (list (proof-sym "NTH-0-CONS" "ACL2") mv-eq))
        '(:failure "malformed-tactic-input" "")))))

(defun h3-counts-car-at-zero (lib)
  (let* ((label "H3-NTH-0-IS-CAR")
         (name (proof-sym (concatenate 'string "SELF-" label) "ACL2"))
         (proof (library-library-proof lib)))
    (if (assoc-equal name (proof-proof-facts proof))
        (cons name lib)
      (let* ((call (list *h3-lists-nth* *proof-zero* *library-x*))
             (target (list *library-car* *library-x*))
             (goal (proof-eq call target)))
        (proof-with-checked-results
         ((rules (h3-rewrite-rules-init lib *h3-lists-selectors* nil))
          (step (car (h3-rewrite-search-prove
                      (h3-rewrite-search-init lib
                                              (append *h3-lists-list-definitions*
                                                      (list *h3-lists-zp* *proof-not*))
                                              (list call) rules 150 nil)
                      goal nil)))
          (symmetric (proof-proof-symmetric proof step))
          (lib (library-library-lemma lib label (proof-eq target call) symmetric nil)))
         (cons name lib))))))

(defun h3-counts-changed-actuals (original actuals changes)
  (if (or (endp original) (endp actuals))
      changes
    (h3-counts-changed-actuals
     (cdr original) (cdr actuals)
     (if (equal (car original) (car actuals))
         changes
       (table-put changes (car original) (car actuals))))))

(defund h3-counts-count-replacement (lib call recursive measure rulers)
  (proof-with-checked-results
   ((actual (proof-term-at recursive 2))
    (smaller (list *proof-ordinal-less* (list *library-count* actual) measure))
    (edge (descent-selector-decrease lib smaller rulers))
    (changes (h3-counts-changed-actuals (cdr call) (cdr recursive) nil)))
   (cons (list changes (car edge)) (cdr edge))))

(defun h3-counts-count-replacements (lib call recursive measure rulers)
  (declare (xargs :measure (acl2-count recursive)))
  (if (endp recursive)
      nil
    (proof-with-checked-results
     ((result (h3-counts-count-replacement lib call (car recursive) measure rulers))
      (rest (h3-counts-count-replacements lib call (cdr recursive) measure (cdr result))))
     (cons (car result) rest))))

(defun h3-counts-count-assumptions (proof tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
     ((test (proof-list-of-length (car tests) 2))
      (step (proof-proof-assume proof (car test) (cadr test)))
      (rest (h3-counts-count-assumptions proof (cdr tests))))
     (cons step rest))))

(defund h3-counts-indexed-count-prove-case-leaf (value tests lib template rules evidence integer)
  (proof-with-checked-results
   ((tests (h3-counts-count-assumptions (library-library-proof lib) tests))
    (goal (proof-subst template (list (cons *proof-result* value)))))
   (car (h3-rewrite-search-prove
         (h3-rewrite-search-init lib *h3-lists-list-definitions*
                                 (list (list *library-natp* *proof-zero*)) rules 90 nil)
         goal (append evidence (cons integer tests))))))

(defund h3-counts-count-leaf-proof (value tests lib template rules evidence integer)
  (proof-with-checked-results
   ((step (h3-counts-indexed-count-prove-case-leaf value tests lib template rules evidence integer))
    (literal (proof-step-first step))
    (claim (proof-subst template (list (cons *proof-result* value)))))
   (if (equal literal claim) step '(:failure "proof-mismatch" ""))))

(defund h3-counts-open-value (proof value)
  (proof-with-checked-results
   ((equality (proof-proof-beta proof value))
    (opened (proof-rewritten-term equality)))
   (cons opened equality)))

(defun h3-counts-count-by-value (n lib value template tests rules evidence integer)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((zp n) '(:failure "fuel" "h3-counts-count-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
       ((branches (proof-list-of-length (cdr value) 3))
        (test (car branches))
        (yes (h3-counts-count-by-value (1- n) lib (cadr branches) template
                                      (append tests (list (list test t))) rules evidence integer))
        (no (h3-counts-count-by-value (1- n) lib (caddr branches) template
                                     (append tests (list (list test nil))) rules evidence integer)))
       (proof-by-value-join proof value template yes no)))
     ((and (proof-compound value) (endp value))
      '(:failure "malformed-tactic-input" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
       ((opened (h3-counts-open-value proof value))
        (step (h3-counts-count-by-value (1- n) lib (car opened) template tests rules evidence integer))
        (symmetric (proof-proof-symmetric proof (cdr opened))))
       (proof-proof-rewrite-result proof step symmetric template *proof-result*)))
     (t
      (h3-counts-count-leaf-proof value tests lib template rules evidence integer)))))

(defund h3-counts-indexed-count-prove-case (evidence lib antecedent template rules normal)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((integer (proof-proof-assume proof antecedent t))
      (value (proof-rewritten-term normal))
      (step (h3-counts-count-by-value 1000000 lib value template nil rules evidence integer))
      (symmetric (proof-proof-symmetric proof normal))
      (step (proof-proof-rewrite-result proof step symmetric template *proof-result*)))
     (h3-rewrite-implication lib antecedent step))))

(defun h3-counts-count-induction
    (n lib formula variable replacements antecedent template rules normal replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h3-counts-count-induction")
    (let ((step (h3-counts-induction-result lib formula variable replacements replies)))
      (if (h3-induction-request-p step)
          (proof-with-checked-results
           ((case-step (h3-counts-indexed-count-prove-case
                        (h3-induction-request-evidence step) lib antecedent template rules normal)))
           (h3-counts-count-induction
            (1- n) lib formula variable replacements antecedent template rules normal
            (append replies (list case-step))))
        step))))

(defun h3-counts-indexed-count (lib formula)
  (proof-with-checked-results
   ((parts (proof-list-of-length formula 3))
    (index-call (proof-term-at (caddr parts) 1))
    (index-call (proof-list-of-length index-call 3)))
   (let* ((antecedent (cadr parts))
          (index (cadr index-call))
          (call (caddr index-call))
          (head (car call))
          (variable (caddr call))
          (measure (list *library-count* variable)))
     (cond
      ((integerp call) '(:failure "malformed-tactic-input" ""))
      ((< (len call) 3)
       '(:failure "malformed-tactic-input" ""))
      (t
       (proof-with-checked-results
        ((lib (h3-merges-arithmetic lib))
         (proof (library-library-proof lib))
         (normal (proof-proof-unfold proof call))
         (value (proof-rewritten-term normal))
         (reduced (car (h3-rewrite-search-reduce
                        (h3-rewrite-search-init lib nil nil nil 150 t)
                        value nil nil nil)))
         (normal (proof-proof-chain proof normal (list reduced)))
         (rulers (descent-hypotheses-init lib (list (list (list *proof-consp* variable) t)) nil))
         (value (proof-rewritten-term normal))
         (recursive (proof-unique (h3-counts-nested-calls value head)))
         (replacements (h3-counts-count-replacements lib call recursive measure rulers))
         (last (proof-term-at index 1))
         (indexed (h3-counts-indexed-selectors lib last))
         (lib (cdr indexed))
         (names (append (car indexed)
                        (list *h3-counts-evg-type* (proof-sym "SELF-NATURAL-INTEGER" "ACL2")
                              "integerp-binary-+")))
         (rules (h3-rewrite-rules-init lib names nil))
         (template (list *proof-integerp* (list *h3-lists-nth* index *proof-result*)))
         (step (h3-counts-count-induction
                1000000 lib formula variable replacements antecedent template rules normal nil)))
        (cons step lib)))))))

(defund h3-counts-tuple-accumulator (lib call accumulator index)
  (let* ((label (concatenate 'string "H3-FN-COUNT-INTEGER-RESULT-" (decimal-text index)))
         (claim (list *library-implies* (library-integer accumulator)
                      (library-integer (list *h3-lists-nth* (proof-quote index) call)))))
    (proof-with-checked-results
     ((result (h3-counts-indexed-count lib claim))
      (lib (library-library-lemma (cdr result) label claim (car result) nil)))
     (cons (proof-sym (concatenate 'string "SELF-" label) "ACL2") lib))))

(defun h3-counts-tuple-accumulators (lib call accumulators index names)
  (declare (xargs :measure (acl2-count accumulators)))
  (if (endp accumulators)
      (cons (reverse names) lib)
    (proof-with-checked-results
     ((result (h3-counts-tuple-accumulator lib call (car accumulators) index)))
     (h3-counts-tuple-accumulators
      (cdr result) call (cdr accumulators) (1+ index) (cons (car result) names)))))

(defun h3-counts-count-tuple (lib formula)
  (proof-with-checked-results
   ((parts (proof-list-of-length (cdr formula) 2))
    (first (proof-term-at (cadr parts) 1))
    (first (proof-term-at first 1))
    (call (proof-term-at first 1))
    (indexed (h3-counts-indexed-selectors lib 1))
    (at-zero (h3-counts-car-at-zero (cdr indexed)))
    (result (h3-counts-tuple-accumulators
             (cdr at-zero) call (cdddr call) 0
             (cons (car at-zero) (reverse (car indexed)))))
    (lib (cdr result))
    (rules (h3-rewrite-rules-init lib (car result) nil))
    (step (car (h3-rewrite-search-prove
                (h3-rewrite-search-init lib nil nil rules 150 nil) formula nil))))
   (cons step lib)))
