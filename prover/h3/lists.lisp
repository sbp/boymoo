(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-lists-atom* (proof-cl "ATOM"))
(defconst *h3-lists-endp* (proof-cl "ENDP"))
(defconst *h3-lists-eq* (proof-cl "EQ"))
(defconst *h3-lists-null* (proof-cl "NULL"))
(defconst *h3-lists-nth* (proof-cl "NTH"))
(defconst *h3-lists-posp* (proof-sym "POSP" "ACL2"))
(defconst *h3-lists-zp* (proof-sym "ZP" "ACL2"))
(defconst *h3-lists-true-listp* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *h3-lists-symbol-listp* (proof-sym "SYMBOL-LISTP" "ACL2"))
(defconst *h3-lists-eqlablep* (proof-sym "EQLABLEP" "ACL2"))
(defconst *h3-lists-eqlable-listp* (proof-sym "EQLABLE-LISTP" "ACL2"))

(defconst *h3-lists-list-definitions*
  (list *h3-lists-atom* *h3-lists-endp* *h3-lists-eq* *h3-lists-null*))

(defconst *h3-lists-selectors*
  '("consp-cons" ("sym" "ACL2" "CAR-CONS") ("sym" "ACL2" "CDR-CONS")
    ("sym" "ACL2" "DEFAULT-CAR") ("sym" "ACL2" "DEFAULT-CDR")))

(defun h3-lists-cdr-induction-prove-case (evidence lib definitions calls names formula)
  (proof-with-checked-results
      ((rules (h3-rewrite-rules-init lib (append *h3-lists-selectors* names) nil)))
    (let ((search (h3-rewrite-search-init
                   lib (append *h3-lists-list-definitions* definitions) calls rules 150 nil)))
      (car (h3-rewrite-search-prove search formula evidence)))))

(defun h3-lists-eqlable-nth-prove-case (evidence lib calls formula)
  (proof-with-checked-results ((rules (h3-rewrite-rules-init lib *h3-lists-selectors* nil)))
    (let ((search (h3-rewrite-search-init lib *h3-lists-list-definitions* calls rules 150 nil)))
      (car (h3-rewrite-search-prove search formula evidence)))))

(defun h3-lists-resize-list-prove-case (evidence lib executable logical rules formula)
  (proof-with-checked-results ((logical-call (proof-term-at logical 2)))
    (let ((search (h3-rewrite-search-init
                   lib (append *h3-lists-list-definitions* (list *h3-lists-zp* (proof-cl "REVERSE")))
                   (list executable logical-call) rules 300 nil)))
      (car (h3-rewrite-search-prove search formula evidence)))))

(defun h3-lists-induction (n lib formula variable replacements kind arguments result-and-replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h3-lists-induction")
    (let ((result (car result-and-replies)))
      (if (h3-induction-request-p result)
          (h3-lists-induction
           (1- n) lib formula variable replacements kind arguments
           (let* ((evidence (h3-induction-request-evidence result))
                  (reply (case kind
                           (:cdr (h3-lists-cdr-induction-prove-case
                                  evidence lib (car arguments) (cadr arguments)
                                  (caddr arguments) formula))
                           (:nth (h3-lists-eqlable-nth-prove-case
                                  evidence lib (car arguments) formula))
                           (otherwise (h3-lists-resize-list-prove-case
                                       evidence lib (car arguments) (cadr arguments)
                                       (caddr arguments) formula)))))
             (if (failure-p reply)
                 (list reply)
               (let ((replies (append (cdr result-and-replies) (list reply))))
                 (cons (h3-induction-structural-induction lib formula variable replacements replies)
                       replies)))))
        result))))

(defun h3-lists-prove-induction (lib formula variable replacements kind arguments)
  (let ((result (h3-induction-structural-induction lib formula variable replacements nil)))
    (h3-lists-induction 1000000 lib formula variable replacements kind arguments (list result))))

(defun h3-lists-cdr-induction (lib formula variable names definitions calls)
  (let ((mapping (list (cons variable (list *library-cdr* variable)))))
    (h3-lists-prove-induction lib formula variable (list (list mapping 3))
                              :cdr (list definitions calls names))))

(defun h3-lists-recognizer-implication (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (antecedent (cadr parts))
       (result (caddr parts))
       (variable (proof-term-at antecedent 1))
       (head (proof-term-at result 0)))
    (h3-lists-cdr-induction lib formula variable nil (list *h3-lists-posp*)
                            (list antecedent result (list head *proof-false*)))))

(defun h3-lists-list-tail-rule (lib predicate)
  (proof-with-checked-results ((predicate-name (proof-term-at predicate 2)))
    (let* ((label (concatenate 'string "H3-" predicate-name "-CDR"))
           (name (proof-sym (concatenate 'string "SELF-" label) "ACL2"))
           (proof (library-library-proof lib)))
      (if (assoc-equal name (proof-proof-facts proof))
          (cons name lib)
        (let* ((source (list predicate *library-x*))
               (return-type (list predicate (list *library-cdr* *library-x*)))
               (formula (list *library-implies* source return-type))
               (calls (list source (list predicate *proof-false*))))
          (proof-with-checked-results
              ((rules (h3-rewrite-rules-init lib *h3-lists-selectors* nil))
               (search (h3-rewrite-search-init lib *h3-lists-list-definitions* calls rules 150 nil))
               (step (car (h3-rewrite-search-prove search formula nil)))
               (lib (library-library-lemma lib label formula step nil)))
            (cons name lib)))))))

(defun h3-lists-association-cdr (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (antecedent (cadr parts))
       (conclusion (proof-list-of-length (caddr parts) 2))
       (consequent (proof-list-of-length (cadr conclusion) 2))
       (call (cadr consequent))
       (variable (proof-term-at antecedent 1))
       (cdr-cons (list *h3-lists-symbol-listp* (list *library-car* variable))))
    (h3-lists-cdr-induction lib formula variable nil nil
                            (list antecedent call cdr-cons
                                  (list *h3-lists-symbol-listp* *proof-false*)))))

(defun h3-lists-eqlable-nth (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (antecedent (cadr parts))
       (conclusion (caddr parts))
       (nth-call (proof-term-at conclusion 1))
       (operands (if (integerp nth-call)
                     '(:failure "MalformedTacticInput" "")
                   (proof-list-of-length (cdr nth-call) 2)))
       (index (car operands))
       (source (cadr operands))
       (mapping (table-put (list (cons index (list *proof-plus* *proof-neg-one* index)))
                              source (list *library-cdr* source)))
       (calls (list antecedent nth-call (list *h3-lists-eqlablep* *proof-false*)
                    (list *h3-lists-eqlable-listp* *proof-false*))))
    (h3-lists-prove-induction lib formula index (list (list mapping 9)) :nth (list calls))))

(defun h3-lists-true-list-cons (lib)
  (let* ((name (proof-sym "SELF-H3-TRUE-LIST-CONS" "ACL2"))
         (proof (library-library-proof lib)))
    (if (assoc-equal name (proof-proof-facts proof))
        (cons name lib)
      (let ((call (list *h3-lists-true-listp* (list *proof-cons* *library-x* *library-y*))))
        (proof-with-checked-results
            ((rules (h3-rewrite-rules-init lib *h3-lists-selectors* nil))
             (formula (proof-eq call (list *h3-lists-true-listp* *library-y*)))
             (search (h3-rewrite-search-init
                      lib *h3-lists-list-definitions* (list call) rules 150 nil))
             (step (car (h3-rewrite-search-prove search formula nil)))
             (lib (library-library-lemma lib "H3-TRUE-LIST-CONS" formula step nil)))
          (cons name lib))))))

(defun h3-lists-character-list-rule (lib name)
  (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
      lib
    (let ((implies (list *library-implies*
                         (list (proof-sym "CHARACTER-LISTP" "ACL2") *library-x*)
                         (list *h3-lists-true-listp* *library-x*))))
      (proof-with-checked-results ((step (h3-lists-recognizer-implication lib implies)))
        (library-library-lemma lib "H3-CHARACTER-LIST-TRUE-LIST" implies step nil)))))

(defun h3-lists-explode-atom (lib formula)
  (let ((name (proof-sym "SELF-H3-CHARACTER-LIST-TRUE-LIST" "ACL2")))
    (proof-with-checked-results
        ((lib (h3-lists-character-list-rule lib name))
         (cons-rule (h3-lists-true-list-cons lib))
         (lib (cdr cons-rule))
         (names (append *h3-lists-selectors*
                        (list name (car cons-rule))
                        '(("sym" "ACL2" "CHARACTER-LISTP-COERCE")
                          ("sym" "ACL2" "TRUE-LISTP-APPEND")
                          ("sym" "ACL2" "TRUE-LISTP-EXPLODE-NONNEGATIVE-INTEGER"))))
         (rules (h3-rewrite-rules-init lib names nil))
         (call (proof-term-at formula 1))
         (calls (list call (list *h3-lists-true-listp* *proof-false*)
                      (list *h3-lists-true-listp* (list *proof-quote* '(("char" 41))))))
         (search (h3-rewrite-search-init lib *h3-lists-list-definitions* calls rules 150 nil))
         (step (car (h3-rewrite-search-prove search formula nil))))
      (cons step lib))))

(defun h3-lists-explode-rule (lib lemma)
  (let ((proof (library-library-proof lib)))
    (if (assoc-equal lemma (proof-proof-facts proof))
        lib
      (let* ((explode (proof-sym "EXPLODE-ATOM" "ACL2"))
             (definition (assoc-equal explode (proof-proof-definitions proof))))
        (if (not definition)
            '(:failure "MissingProofData" "")
          (let ((shape (list *h3-lists-true-listp* (cons explode (cadr definition)))))
            (proof-with-checked-results ((result (h3-lists-explode-atom lib shape)))
              (library-library-lemma (cdr result) "H3-EXPLODE-TRUE-LIST" shape
                                     (car result) nil))))))))

(defun h3-lists-printed-phrase (lib formula)
  (let ((lemma (proof-sym "SELF-H3-EXPLODE-TRUE-LIST" "ACL2")))
    (proof-with-checked-results
        ((call (proof-term-at formula 1))
         (variable (proof-term-at call 1))
         (lib (h3-lists-explode-rule lib lemma))
         (cons-rule (h3-lists-true-list-cons lib))
         (lib (cdr cons-rule))
         (names (list (proof-sym "TRUE-LISTP-APPEND" "ACL2") lemma (car cons-rule)))
         (step (h3-lists-cdr-induction lib formula variable names nil
                                       (list call (list *h3-lists-true-listp* *proof-false*)))))
      (cons step lib))))

(defun h3-lists-revappend-rule (lib lemma tail)
  (if (assoc-equal lemma (proof-proof-facts (library-library-proof lib)))
      lib
    (let* ((x *library-x*)
           (y *library-y*)
           (z *library-z*)
           (call (list tail (list *proof-cons* x y) z))
           (claim (proof-eq call (list tail y (list *proof-cons* x z)))))
      (proof-with-checked-results
          ((rules (h3-rewrite-rules-init lib *h3-lists-selectors* nil))
           (search (h3-rewrite-search-init
                    lib *h3-lists-list-definitions* (list call) rules 150 nil))
           (step (car (h3-rewrite-search-prove search claim nil))))
        (library-library-lemma lib "H3-REVAPPEND-CONS" claim step nil)))))

(defun h3-lists-resize-list (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (conclusion (caddr parts))
       (operands (if (integerp conclusion)
                     '(:failure "MalformedTacticInput" "")
                   (proof-list-of-length (cdr conclusion) 2)))
       (executable (car operands))
       (logical (cadr operands))
       (call (proof-list-of-length executable 5))
       (source (cadr call))
       (index (caddr call))
       (default (cadddr call))
       (acc (nth 4 call))
       (tail (proof-cl "REVAPPEND"))
       (atom (list *h3-lists-atom* source))
       (next-source (proof-ite atom source (list *library-cdr* source)))
       (entry (proof-ite atom default (list *library-car* source)))
       (mapping (table-put
                 (table-put (list (cons source next-source))
                              index (list *proof-plus* *proof-neg-one* index))
                 acc (list *proof-cons* entry acc)))
       (lemma (proof-sym "SELF-H3-REVAPPEND-CONS" "ACL2"))
       (lib (h3-lists-revappend-rule lib lemma tail))
       (cons-rule (h3-lists-true-list-cons lib))
       (nonstring (h3-state-true-list-not-string (cdr cons-rule)))
       (lib (cdr nonstring))
       (rules (h3-rewrite-rules-init
               lib (append *h3-lists-selectors* (list (car cons-rule) (car nonstring) lemma)) nil))
       (step (h3-lists-prove-induction lib formula index (list (list mapping 9))
                                       :resize (list executable logical rules))))
    (cons step lib)))
