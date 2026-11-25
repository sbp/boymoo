(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h3-merges-arithmetic (lib)
  (if (assoc-equal (proof-sym "SELF-LEN-NATURAL" "ACL2")
                   (proof-proof-facts (library-library-proof lib)))
      lib
    (library-library-build lib)))

(defun h3-merges-termination-edges (lib variables mapping current index smaller)
  (if (endp variables)
      smaller
    (let ((variable (car variables)))
      (if (not (assoc-equal variable mapping))
          (h3-merges-termination-edges lib (cdr variables) mapping current (1+ index) smaller)
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results
              ((cons-proof (proof-proof-assume proof (list *proof-consp* variable) t))
               (bound (library-library-cite lib "LEN-CDR-LESS" (list variable)
                                            (list cons-proof)))
               (edge (descent-shift lib bound (nth (- 1 index) current) (equal index 1)))
               (smaller (if smaller (library-library-compare-chain lib edge smaller) edge))
               (literal (proof-step-first edge))
               (left (proof-term-at literal 1))
               (first (proof-term-at left 1))
               (second (proof-term-at left 2)))
            (h3-merges-termination-edges lib (cdr variables) mapping (list first second)
                                         (1+ index) smaller)))))))

(defun h3-merges-merge-termination (lib call mapping)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((terms (if (integerp call)
                    '(:failure "malformed-tactic-input" "")
                  (proof-list-of-length (seq-slice call 1 3) 2)))
         (first (list *library-len* (car terms)))
         (second (list *library-len* (cadr terms)))
         (measure (library-plus first second))
         (target (proof-subst measure mapping))
         (smaller (h3-merges-termination-edges lib terms mapping (list first second) 0 nil))
         (comparison (library-library-ordinal-comparison lib target measure)))
      (if smaller
          (proof-proof-transport proof smaller comparison)
        (proof-with-checked-results ((reversed (proof-proof-symmetric proof comparison)))
          '(:failure "malformed-tactic-input" ""))))))

(defun h3-merges-bind-arguments (keys values entries)
  (if (or (endp keys) (endp values))
      entries
    (h3-merges-bind-arguments (cdr keys) (cdr values)
                        (table-put entries (car keys) (car values)))))

(defun h3-merges-substitution-map (arguments actuals bindings entries)
  (if (or (endp arguments) (endp actuals))
      entries
    (proof-with-checked-results ((value (proof-subst (car actuals) bindings)))
      (h3-merges-substitution-map (cdr arguments) (cdr actuals) bindings
                                  (table-put entries (car arguments) value)))))

(defun h3-merges-changed-bindings (mapping)
  (cond ((endp mapping) nil)
        ((equal (caar mapping) (cdar mapping))
         (h3-merges-changed-bindings (cdr mapping)))
        (t (cons (car mapping) (h3-merges-changed-bindings (cdr mapping))))))

(defun h3-merges-replacements (lib call formals recursive-calls)
  (if (endp recursive-calls)
      nil
    (let* ((arguments (cdr call))
           (bindings (h3-merges-bind-arguments formals arguments nil))
           (actuals (termination-call-actuals (car recursive-calls))))
      (proof-with-checked-results
          ((mapping (h3-merges-substitution-map arguments actuals bindings nil))
           (mapping (h3-merges-changed-bindings mapping))
           (decrease (h3-merges-merge-termination lib call mapping))
           (replacements (h3-merges-replacements lib call formals (cdr recursive-calls))))
        (cons (list mapping decrease) replacements)))))

(defun h3-merges-two-list-merge-prove-case (evidence lib call rules formula)
  (proof-with-checked-results
      ((rules (h3-rewrite-rules-init lib (append *h3-lists-selectors* rules) nil)))
    (let ((search (h3-rewrite-search-init
                   lib *h3-lists-list-definitions* (list call) rules 350 nil)))
      (car (h3-rewrite-search-prove search formula evidence)))))

(defun h3-merges-induction (n lib formula measure ordinal replacements call rules result-and-replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h3-merges-induction")
    (let ((result (car result-and-replies)))
      (if (h3-induction-request-p result)
          (h3-merges-induction
           (1- n) lib formula measure ordinal replacements call rules
           (let ((reply (h3-merges-two-list-merge-prove-case
                         (h3-induction-request-evidence result) lib call rules formula)))
             (if (failure-p reply)
                 (list reply)
               (let ((replies (append (cdr result-and-replies) (list reply))))
                 (cons (h3-induction-well-founded lib formula measure ordinal replacements replies)
                       replies)))))
        result))))

(defun h3-merges-two-list-merge (lib formula rules)
  (proof-with-checked-results
      ((lib (h3-merges-arithmetic lib))
       (conclusion (proof-term-at formula 2))
       (call (proof-term-at conclusion 1))
       (call (proof-list-of-length call 4)))
    (let* ((head (car call))
           (x (cadr call))
           (y (caddr call))
           (definition (assoc-equal head (proof-proof-definitions (library-library-proof lib)))))
      (if (not definition)
          '(:failure "missing-proof-data" "")
        (let ((formals (cadr definition))
              (body (caddr definition)))
          (proof-with-checked-results
              ((recursive-calls (termination-recursive-calls
                                 *termination-all* (list (list head formals body))))
               (replacements (h3-merges-replacements lib call formals recursive-calls))
               (measure (library-plus (list *library-len* x) (list *library-len* y)))
               (natural (library-library-natural lib measure))
               (ordinal (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural)))
               (result (h3-induction-well-founded lib formula measure ordinal replacements nil))
               (step (h3-merges-induction
                      1000000 lib formula measure ordinal replacements call rules (list result))))
            (cons step lib)))))))

(defun h3-merges-merge-lexorder (lib formula)
  (proof-with-checked-results ((tail (h3-lists-list-tail-rule lib *h3-lists-true-listp*)))
    (h3-merges-two-list-merge
     (cdr tail) formula
     (list (proof-sym "TRUE-LISTP-REVAPPEND-TYPE-PRESCRIPTION" "ACL2") (car tail)))))
