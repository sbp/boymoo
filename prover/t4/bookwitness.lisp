(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(mutual-recursion
 (defun t4-bookwitness-replace-functions (term names)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((not (proof-compound term)) term)
    ((endp term) '(:failure "failure" ""))
    ((equal (car term) *proof-quote*) term)
    (t (proof-with-checked-results
           ((head (if (proof-compound (car term))
                      (if (consp (cddar term))
                          (proof-with-checked-results
                              ((body (t4-bookwitness-replace-functions (caddar term) names)))
                            (list (caar term) (cadar term) body))
                        '(:failure "failure" ""))
                    (table-get names (car term) (car term))))
            (args (t4-bookwitness-replace-arguments (cdr term) names)))
         (cons head args)))))
 (defun t4-bookwitness-replace-arguments (terms names)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (proof-with-checked-results
         ((first (t4-bookwitness-replace-functions (car terms) names))
          (rest (t4-bookwitness-replace-arguments (cdr terms) names)))
       (cons first rest)))))

(defun t4-bookwitness-prepend-value (value tails)
  (if (endp tails)
      nil
    (cons (cons value (car tails))
          (t4-bookwitness-prepend-value value (cdr tails)))))

(defun t4-bookwitness-constant-product (functions)
  (if (endp functions)
      (list nil)
    (let ((tails (t4-bookwitness-constant-product (cdr functions))))
      (append (t4-bookwitness-prepend-value *proof-false* tails)
              (t4-bookwitness-prepend-value *proof-true* tails)
              (t4-bookwitness-prepend-value *proof-zero* tails)))))

(defun t4-bookwitness-repeat-value (value functions)
  (if (endp functions)
      nil
    (cons value (t4-bookwitness-repeat-value value (cdr functions)))))

(defun t4-bookwitness-constant-values (functions)
  (if (<= (len functions) 3)
      (t4-bookwitness-constant-product functions)
    (list (t4-bookwitness-repeat-value *proof-false* functions)
          (t4-bookwitness-repeat-value *proof-true* functions)
          (t4-bookwitness-repeat-value *proof-zero* functions))))

(defun t4-bookwitness-existing-values (functions)
  (if (and (consp functions) (endp (cdr functions)))
      (proof-with-checked-results ((arity (proof-term-at (car functions) 1)))
        (cond ((or (equal arity 1) (eq arity t))
               (list (list (proof-cl "CONSP")) (list (proof-cl "INTEGERP"))
                     (list (proof-cl "SYMBOLP")) (list *proof-not*)
                     (list (proof-cl "CAR")) (list (proof-cl "CDR"))
                     (list (proof-sym "IDENTITY" "ACL2"))
                     (list (proof-sym "NATP" "ACL2"))))
              ((equal arity 2)
               (list (list *proof-equal*) (list *proof-less*)
                     (list (proof-sym "IFF" "ACL2"))
                     (list (proof-sym "LEXORDER" "ACL2"))))
              (t nil)))
    nil))

(defun t4-bookwitness-candidate-values (functions)
  (proof-with-checked-results ((existing (t4-bookwitness-existing-values functions)))
    (append (t4-bookwitness-constant-values functions) existing)))

(defun t4-bookwitness-request-p (value)
  (and (consp value) (eq (car value) :call)
       (member-eq (cadr value) '(:solve :used-prelude))))

(defun t4-bookwitness-symbols (count prefix index)
  (declare (xargs :measure (nfix count)))
  (if (not (o< (nfix (1- count)) (nfix count)))
      nil
    (cons (proof-sym (concatenate 'string prefix (decimal-text index)) "ACL2")
          (t4-bookwitness-symbols (1- count) prefix (1+ index)))))

(defun t4-bookwitness-defined-p (proof value)
  (or (assoc-equal value (proof-proof-definitions proof))
      (member-equal value (proof-proof-primitives proof))))

(defun t4-bookwitness-available-p (proof values)
  (or (endp values)
      (and (or (proof-compound (car values))
               (t4-bookwitness-defined-p proof (car values)))
           (t4-bookwitness-available-p proof (cdr values)))))

(defun t4-bookwitness-formals (arity)
  (cond ((integerp arity) (t4-bookwitness-symbols arity "T4-FORMAL-" 0))
        ((eq arity t) (t4-bookwitness-symbols 1 "T4-FORMAL-" 0))
        ((stringp arity) '(:failure "failure" ""))
        (t '(:failure "failure" ""))))

(defun t4-bookwitness-prepare (proof functions names values)
  (if (or (endp functions) (endp names) (endp values))
      (list nil nil proof)
    (proof-with-checked-results
        ((function (proof-list-of-length (car functions) 2)))
      (let ((own (car names)) (value (car values)))
        (if (t4-bookwitness-defined-p proof value)
            (proof-with-checked-results
                ((rest (t4-bookwitness-prepare proof (cdr functions) (cdr names) (cdr values))))
              (list (cons value (car rest)) (cadr rest) (caddr rest)))
          (proof-with-checked-results
              ((labels (t4-bookwitness-formals (cadr function)))
               (updated (proof-proof-add-definition proof own labels value))
               (rest (t4-bookwitness-prepare updated (cdr functions) (cdr names) (cdr values))))
            (list (cons own (car rest))
                  (cons (list own (or labels *proof-nil*) value) (cadr rest))
                  (caddr rest))))))))

(defun t4-bookwitness-replacements (functions available names)
  (if (or (endp functions) (endp available))
      names
    (t4-bookwitness-replacements (cdr functions) (cdr available)
                                 (table-put names (caar functions) (car available)))))

(defun t4-bookwitness-definition-lines (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
        ((line (proof-line "define" (list *proof-nil* (car definitions))))
         (rest (t4-bookwitness-definition-lines (cdr definitions))))
      (cons line rest))))

(defun t4-bookwitness-finish (lib name available definitions steps replies)
  (let ((target (proof-proof-entry "witness" name (cons name available) (reverse steps))))
    (cond
     ((failure-p target) (list target lib replies))
     ((endp replies)
      (list (list :call :used-prelude (library-library-entries lib) target) lib nil))
     (t
      (let ((value (proof-with-checked-results
                       ((prelude (car replies))
                        (prelude (proof-list-of-length prelude 2))
                        (lines (t4-bookwitness-definition-lines definitions)))
                     (list (car prelude) (text-join "" (append lines (cdr prelude)))))))
        (list value lib (cdr replies)))))))

(defun t4-bookwitness-formula-goal (formula replacements)
  (proof-with-checked-results ((fields (proof-list-of-length formula 2)))
    (t4-bookwitness-replace-functions (cadr fields) replacements)))

(defun t4-bookwitness-prove-formulas
    (formulas lib name available definitions replacements steps replies)
  (if (endp formulas)
      (t4-bookwitness-finish lib name available definitions steps replies)
    (let ((goal (t4-bookwitness-formula-goal (car formulas) replacements)))
      (cond
       ((failure-p goal) (list goal lib replies))
       ((endp replies) (list (list :call :solve lib goal) lib nil))
       (t (let* ((reply (car replies))
                 (lib (cdr reply))
                 (step (proof-with-checked-results ((step (car reply)))
                         (proof-proof-subsume (library-library-proof lib) step (list goal)))))
            (if (failure-p step)
                (list step lib (cdr replies))
              (t4-bookwitness-prove-formulas
               (cdr formulas) lib name available definitions replacements
               (cons step steps) (cdr replies)))))))))

(defun t4-bookwitness-forget (definitions proof)
  (if (endp definitions)
      proof
    (let* ((name (caar definitions))
           (facts (proof-proof-facts proof))
           (known (proof-proof-definitions proof)))
      (if (not (and (assoc-equal name facts) (assoc-equal name known)))
          '(:failure "failure" "")
        (t4-bookwitness-forget
         (cdr definitions)
         (proof-proof-with-kind
          (proof-make-proof (table-delete facts name) (table-delete known name)
                            (proof-proof-primitives proof))
          (proof-proof-kind proof)))))))

(defun t4-bookwitness-trial-failure-p (value)
  (and (failure-p value)
       (member-equal (cadr value)
                     '("SearchMiss" "InferenceMismatch" "value" "assertion" "recursion"
                       "coding" "decoding" "encoding"
                       "translating" "Unproved" "MissingProof"))))

(defun t4-bookwitness-search (candidates lib name functions formulas names replies)
  (if (endp candidates)
      (list nil lib replies)
    (let ((proof (library-library-proof lib))
          (values (car candidates)))
      (if (not (t4-bookwitness-available-p proof values))
          (t4-bookwitness-search (cdr candidates) lib name functions formulas names replies)
        (proof-with-checked-results
            ((prepared (t4-bookwitness-prepare proof functions names values)))
          (let* ((available (car prepared))
                 (definitions (cadr prepared))
                 (lib (library-library-with-proof lib (caddr prepared)))
                 (replacements (t4-bookwitness-replacements functions available nil))
                 (trial (t4-bookwitness-prove-formulas
                         formulas lib name available definitions replacements nil replies))
                 (value (car trial))
                 (lib (cadr trial))
                 (replies (caddr trial)))
            (if (t4-bookwitness-request-p value)
                trial
              (proof-with-checked-results
                  ((cleaned (t4-bookwitness-forget definitions (library-library-proof lib))))
                (let ((lib (library-library-with-proof lib cleaned)))
                  (cond ((t4-bookwitness-trial-failure-p value)
                         (t4-bookwitness-search
                          (cdr candidates) lib name functions formulas names replies))
                        ((failure-p value) value)
                        (t (list value lib replies))))))))))))

(defun t4-bookwitness-simple-witness (api tactic name data suffix)
  (proof-with-checked-results ((data (proof-list-of-length data 2)))
    (let* ((functions (car data))
           (formulas (cadr data))
           (names (t4-bookwitness-symbols
                   (len functions) (concatenate 'string "T4-BOOK-WITNESS-" suffix "-") 0)))
      (proof-with-checked-results
          ((result (t4-bookwitness-search (t4-bookwitness-constant-values functions)
                                         tactic name functions formulas names api))
           (result (if (car result)
                       result
                     (proof-with-checked-results
                         ((existing (t4-bookwitness-existing-values functions)))
                       (t4-bookwitness-search existing (cadr result) name functions
                                              formulas names (caddr result))))))
        (cons (car result) (cadr result))))))
