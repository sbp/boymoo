(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-typed-alists-alist* (proof-sym "ALIST-TYPE" "ACL2"))
(defconst *b1-typed-alists-domain* (proof-sym "DOMAIN-ELEM-TYPE" "ACL2"))
(defconst *b1-typed-alists-range* (proof-sym "RANGE-ELEM-TYPE" "ACL2"))
(defconst *b1-typed-alists-bind* (proof-sym "BIND-EQUAL" "ACL2"))
(defconst *b1-typed-alists-alist-defun* (proof-sym "ALIST-TYPE-DEFUN" "ACL2"))
(defconst *b1-typed-alists-alist-cons*
  (proof-sym "DOMAIN-ELEM-TYPE constraint 5" "ACL2"))
(defconst *b1-typed-alists-domain-list-rule*
  (proof-sym "DOMAIN-TYPE-DOMAIN-ELEM-TYPE" "ACL2"))
(defconst *b1-typed-alists-range-list-rule*
  (proof-sym "RANGE-TYPE-RANGE-ELEM-TYPE" "ACL2"))
(defconst *b1-typed-alists-l* (proof-sym "L" "ACL2"))

(defun b1-typed-alists-first-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defmacro b1-typed-alists-prove-implication (lib formula premise consequence)
  `(proof-with-checked-results
       ((,premise (b1-logic-bookproof-prove-implication-premise ,lib ,formula))
        (typed-alists-consequence ,consequence))
     (b1-logic-bookproof-prove-implication-with-premise
      ,lib ,formula ,premise typed-alists-consequence)))

(defun b1-typed-alists-alist-body (lib items evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((law (proof-proof-fact proof *b1-typed-alists-alist-defun*
                               (list (list *b1-typed-alists-l* items))))
         (body (b1-typed-alists-first-at law 2))
         (reduced (b1-logic-bookproof-normalize
                   lib body evidence
                   (list *b1-logic-atom* *b1-logic-eq* *proof-not*)
                   nil nil nil nil)))
      (proof-proof-rewrite proof law reduced '(1 2)))))

(defun b1-typed-alists-alist-parts (lib typed cell)
  (proof-with-checked-results
      ((items (b1-typed-alists-first-at typed 1))
       (opened (b1-typed-alists-alist-body lib items (list cell)))
       (body (b1-typed-alists-first-at opened 2))
       (result (b1-logic-bookproof-forces
                lib body opened (list typed) (list *b1-revappend-iff*) nil)))
    (b1-logic-bookproof-split-conjuncts lib result)))

(defun b1-typed-alists-empty-alist (lib)
  (proof-with-checked-results
      ((rule (b1-typed-alists-alist-body lib *proof-false* nil))
       (claim (b1-typed-alists-first-at rule 1)))
    (b1-logic-bookproof-forces lib claim rule nil (list *b1-revappend-iff*) nil)))

(defun b1-typed-alists-alist-cons (lib pair fields)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((args (if (integerp pair)
                   (proof-term-at pair 0)
                 (proof-list-of-length (cdr pair) 2)))
         (rule (proof-proof-fact proof *b1-typed-alists-alist-cons*
                                (list (list *library-x* (car args))
                                      (list *b1-typed-alists-l* (cadr args)))))
         (body (b1-typed-alists-first-at rule 2))
         (opened (b1-logic-bookproof-normalize lib body nil nil nil nil nil nil))
         (reduced (b1-typed-alists-first-at opened 2))
         (proven (b1-logic-bookproof-normalize-proof lib reduced fields nil nil nil))
         (result (proof-proof-transport proof proven opened)))
      (proof-proof-transport proof result rule))))

(defun b1-typed-alists-alist-type-is-alist-base-consequence (typed lib xs atom result)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((rule (b1-typed-alists-alist-body lib xs (list atom)))
         (body (b1-typed-alists-first-at rule 2))
         (empty (b1-logic-bookproof-forces
                 lib body rule (list typed) (list *b1-revappend-iff*) nil))
         (opened (b1-logic-bookproof-normalize
                  lib result (list atom)
                  (list (car result) *b1-logic-atom* *b1-logic-eq* *proof-not*)
                  nil nil nil nil)))
      (proof-proof-transport proof empty opened))))

(defun b1-typed-alists-alist-type-is-alist-base (atom lib formula xs result)
  (b1-typed-alists-prove-implication
   lib formula typed
   (b1-typed-alists-alist-type-is-alist-base-consequence typed lib xs atom result)))

(defun b1-typed-alists-alist-type-is-alist-step-consequence (typed lib cell induction result)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (b1-typed-alists-alist-parts lib typed cell))
         (fields (proof-list-of-length parts 4))
         (smaller (proof-proof-modus-ponens proof induction (cadddr fields)))
         (opened (b1-revappend-open-list lib result (list cell (car fields)))))
      (proof-proof-transport proof smaller opened))))

(defun b1-typed-alists-alist-type-is-alist-step (cell induction lib formula result)
  (b1-typed-alists-prove-implication
   lib formula typed
   (b1-typed-alists-alist-type-is-alist-step-consequence typed lib cell induction result)))

(defun b1-typed-alists-alist-type-is-alist (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (result (proof-list-of-length (caddr implication) 2)))
    (let ((xs (cadr result))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((prep (b1-revappend-list-induction-prepare lib formula xs nil))
           (step (b1-typed-alists-alist-type-is-alist-step
                  (caddr prep) (cadddr prep) lib formula result))
           (atom (proof-proof-assume proof (cadr prep) nil))
           (base (b1-typed-alists-alist-type-is-alist-base atom lib formula xs result)))
        (b1-revappend-list-induction lib prep base step)))))

(defun b1-typed-alists-alist-type-acons-consequence (premise lib pair opened)
  (proof-with-checked-results
      ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
       (fields (proof-list-of-length conjuncts 3))
       (entry (proof-term-at pair 1))
       (cell (b1-revappend-cons-value lib entry))
       (constructed (b1-typed-alists-alist-cons
                     lib pair (list cell (cadr fields) (caddr fields) (car fields)))))
    (library-library-transport-argument lib constructed opened 1)))

(defun b1-typed-alists-alist-type-acons (lib formula)
  (proof-with-checked-results
      ((claim (proof-term-at formula 2))
       (parts (proof-list-of-length claim 2))
       (opened (b1-revappend-open-list lib (cadr parts) nil))
       (pair (b1-typed-alists-first-at opened 2)))
    (b1-typed-alists-prove-implication
     lib formula premise
     (b1-typed-alists-alist-type-acons-consequence premise lib pair opened))))

(defun b1-typed-alists-induction-guard (lib tail key value)
  (proof-with-checked-results
      ((tail-type (proof-step-first tail))
       (key-type (proof-step-first key))
       (value-type (proof-step-first value)))
    (let ((test (proof-ite tail-type (proof-ite key-type value-type *proof-false*)
                           *proof-false*)))
      (b1-logic-bookproof-normalize-proof lib test (list tail key value) nil nil nil))))

(defun b1-typed-alists-known-step (known value)
  (let ((entry (assoc-equal value known)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun b1-typed-alists-typed-alist-recursion-cases-leaf (value tests lib known fields head remaining)
  (declare (ignore tests))
  (let ((proof (library-library-proof lib)))
    (cond
     ((assoc-equal value known) (b1-typed-alists-known-step known value))
     ((proof-is-call value *b1-typed-alists-bind*)
      (proof-with-checked-results
          ((parts (if (eq fields :none)
                      '(:failure "failure" "")
                    (proof-list-of-length fields 3)))
           (tail (proof-term-at value 3))
           (child (b1-typed-alists-known-step known tail))
           (guard (b1-typed-alists-induction-guard lib child (cadr parts) (caddr parts)))
           (test (proof-step-first guard))
           (rule (b1-logic-bookproof-from-fact
                  lib (proof-sym "ALIST-TYPE-BIND-EQUAL" "ACL2")
                  (list *library-implies* test (list *b1-typed-alists-alist* value)))))
        (proof-proof-modus-ponens proof rule guard)))
     (t
      (proof-with-checked-results
          ((parts (proof-list-of-length value 3)))
        (let ((entry (cadr parts))
              (tail (caddr parts)))
          (proof-with-checked-results
              ((row-type (if (equal entry head)
                             (if (eq fields :none)
                                 '(:failure "failure" "")
                               fields)
                           (proof-with-checked-results
                               ((cell (b1-revappend-cons-value lib entry)))
                             (cons cell remaining))))
               (tail-type (b1-typed-alists-known-step known tail)))
            (b1-typed-alists-alist-cons lib value (append row-type (list tail-type))))))))))

(defun b1-typed-alists-typed-alist-recursion-by-value (n lib value template known fields head remaining tests)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((zp n) '(:failure "Fuel" "b1-typed-alists-typed-alist-recursion-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (yes (b1-typed-alists-typed-alist-recursion-by-value
                 (1- n) lib (cadr branches) template known fields head remaining
                 (append tests (list (list (car branches) t)))))
           (no (b1-typed-alists-typed-alist-recursion-by-value
                (1- n) lib (caddr branches) template known fields head remaining
                (append tests (list (list (car branches) nil))))))
        (proof-by-value-join proof value template yes no)))
     ((and (proof-compound value) (endp value)) '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (body (b1-typed-alists-first-at equality 2))
           (opened (b1-typed-alists-typed-alist-recursion-by-value
                    (1- n) lib body template known fields head remaining tests))
           (reverse-equality (proof-proof-symmetric proof equality)))
        (proof-proof-rewrite-result proof opened reverse-equality template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (b1-typed-alists-typed-alist-recursion-cases-leaf
                  value tests lib known fields head remaining))
           (literal (proof-step-first step))
           (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal target)
            step
          '(:failure "failure" "")))))))

(defun b1-typed-alists-typed-alist-recursion-smaller (lib source cell induction remaining known)
  (if (not induction)
      (list :none known)
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((parts (b1-typed-alists-alist-parts lib source cell)))
        (let ((fields (butlast parts 1))
              (tail (car (last parts))))
          (proof-with-checked-results
              ((child-test (b1-typed-alists-first-at induction 1))
               (child-premise (b1-logic-bookproof-normalize-proof
                               lib child-test (cons tail remaining) nil nil nil))
               (child (proof-proof-modus-ponens proof induction child-premise))
               (child-key (b1-typed-alists-first-at child 1))
               (known (table-put known child-key child))
               (tail-key (b1-typed-alists-first-at tail 1)))
            (list fields (table-put known tail-key tail))))))))

(defun b1-typed-alists-typed-alist-recursion-cases (cell premise induction lib call head template binding)
  (proof-with-checked-results
      ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
       (empty (b1-typed-alists-empty-alist lib))
       (source-key (b1-typed-alists-first-at (car conjuncts) 1)))
    (let* ((source (car conjuncts))
           (remaining (cdr conjuncts))
           (known (table-put (list (cons *proof-false* empty)) source-key source)))
      (proof-with-checked-results
          ((known (if (and (not binding) remaining)
                      (proof-with-checked-results
                          ((key (b1-typed-alists-first-at (car remaining) 1)))
                        (table-put known key (car remaining)))
                    known))
           (smaller (b1-typed-alists-typed-alist-recursion-smaller
                     lib source cell induction remaining known))
           (opened (b1-revappend-open-list lib call (list cell)))
           (body (b1-typed-alists-first-at opened 2))
           (result (b1-typed-alists-typed-alist-recursion-by-value
                    1000000 lib body template (cadr smaller) (car smaller) head remaining nil)))
        (library-library-transport-argument lib result opened 1)))))

(defun b1-typed-alists-typed-alist-recursion-base (atom lib formula call head template binding)
  (b1-typed-alists-prove-implication
   lib formula premise
   (b1-typed-alists-typed-alist-recursion-cases
    atom premise nil lib call head template binding)))

(defun b1-typed-alists-typed-alist-recursion-step (cell induction lib formula call head template binding)
  (b1-typed-alists-prove-implication
   lib formula premise
   (b1-typed-alists-typed-alist-recursion-cases
    cell premise induction lib call head template binding)))

(defun b1-typed-alists-typed-alist-recursion (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr implication) 2)))
    (let ((call (cadr claim))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((operation (proof-term-at call 0))
           (driver (if (or (equal operation *b1-revappend-append*)
                           (equal operation (proof-sym "BIND-PAIRS-EQUAL" "ACL2")))
                       (proof-term-at call 1)
                     (car (last call)))))
        (let ((head (list *library-car* driver))
              (template (list *b1-typed-alists-alist* *proof-result*))
              (binding (equal operation *b1-typed-alists-bind*)))
          (proof-with-checked-results
              ((prep (b1-revappend-list-induction-prepare lib formula driver nil))
               (step (b1-typed-alists-typed-alist-recursion-step
                      (caddr prep) (cadddr prep) lib formula call head template binding))
               (atom (proof-proof-assume proof (cadr prep) nil))
               (base (b1-typed-alists-typed-alist-recursion-base
                      atom lib formula call head template binding)))
            (b1-revappend-list-induction lib prep base step)))))))

(defun b1-typed-alists-typed-alist-lookup-base-consequence
    (premise lib query atom range-result claim)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((empty (b1-revappend-open-list lib query (list atom))))
      (if range-result
          (proof-with-checked-results
              ((parts (proof-proof-conjunct proof premise))
               (missing (proof-proof-rewrite proof (cadr parts) empty '(1)))
               (not-nil-step (b1-logic-proof-not-nil proof)))
            (b1-logic-bookproof-contradiction lib missing not-nil-step claim))
        (b1-logic-bookproof-normalize-proof
         lib claim nil (list *proof-not*) (list (b1-logic-equal-to empty)) nil)))))

(defun b1-typed-alists-typed-alist-lookup-base (atom lib formula query range-result claim)
  (b1-typed-alists-prove-implication
   lib formula premise
   (b1-typed-alists-typed-alist-lookup-base-consequence premise lib query atom range-result claim)))

(defun b1-typed-alists-typed-alist-lookup-step-consequence
    (premise lib cell induction test range-result query claim)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-proof-conjunct proof premise))
         (alist-fields (b1-typed-alists-alist-parts lib (car parts) cell))
         (fields (proof-list-of-length alist-fields 4))
         (hit (proof-proof-assume proof test t))
         (miss (proof-proof-assume proof test nil)))
      (let ((assumed (cadr parts))
            (domain (cadr fields))
            (range-step (caddr fields))
            (smaller (cadddr fields)))
        (if range-result
            (proof-with-checked-results
                ((opened (b1-revappend-open-list lib query (list cell hit)))
                 (reversed (proof-proof-symmetric proof opened))
                 (yes (proof-proof-rewrite proof range-step reversed '(1 1 1)))
                 (opened (b1-revappend-open-list lib query (list cell miss)))
                 (exists (proof-proof-rewrite proof assumed opened '(1)))
                 (child-test (b1-typed-alists-first-at induction 1))
                 (child-premise (b1-logic-bookproof-normalize-proof
                                 lib child-test (list smaller exists) nil nil nil))
                 (child (proof-proof-modus-ponens proof induction child-premise))
                 (opened (b1-revappend-open-list lib query (list cell miss)))
                 (reversed (proof-proof-symmetric proof opened))
                 (no (proof-proof-rewrite proof child reversed '(1 1 1))))
              (proof-proof-cases proof test yes no))
          (proof-with-checked-results
              ((reversed (proof-proof-symmetric proof hit))
               (matched (proof-proof-rewrite proof domain reversed '(1 1)))
               (yes (b1-logic-bookproof-contradiction lib matched assumed claim))
               (child-test (b1-typed-alists-first-at induction 1))
               (child-premise (b1-logic-bookproof-normalize-proof
                               lib child-test (list smaller assumed) nil nil nil))
               (child (proof-proof-modus-ponens proof induction child-premise))
               (opened (b1-revappend-open-list lib query (list cell miss)))
               (no (library-library-transport-argument lib child opened 1)))
            (proof-proof-cases proof test yes no)))))))

(defun b1-typed-alists-typed-alist-lookup-step
    (cell induction lib formula test range-result query claim)
  (b1-typed-alists-prove-implication
   lib formula premise
   (b1-typed-alists-typed-alist-lookup-step-consequence
    premise lib cell induction test range-result query claim)))

(defun b1-typed-alists-typed-alist-lookup (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (claim-head (proof-term-at (caddr implication) 0))
       (target (proof-term-at (caddr implication) 1)))
    (let ((claim (caddr implication))
          (range-result (equal claim-head *b1-typed-alists-range*))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((query (if range-result (proof-term-at target 1) target))
           (parts (proof-list-of-length query 3)))
        (let* ((xs (caddr parts))
               (entry (list *library-car* xs))
               (test (proof-eq (cadr parts) (list *library-car* entry))))
          (proof-with-checked-results
              ((prep (b1-revappend-list-induction-prepare lib formula xs nil))
               (step (b1-typed-alists-typed-alist-lookup-step
                      (caddr prep) (cadddr prep) lib formula test range-result query claim))
               (atom (proof-proof-assume proof (cadr prep) nil))
               (base (b1-typed-alists-typed-alist-lookup-base atom lib formula query range-result claim)))
            (b1-revappend-list-induction lib prep base step)))))))

(defun b1-typed-alists-alist-bound-requires-key-consequence (premise lib assoc-term claim query)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (proof-step-first premise))
         (law (b1-logic-bookproof-from-fact
               lib (proof-sym "ALIST-TYPE-ASSOC-EQUAL" "ACL2")
               (list *library-implies* test (proof-neg assoc-term))))
         (missing (proof-proof-modus-ponens proof law premise))
         (empty (b1-logic-bookproof-false-value lib missing)))
      (b1-logic-bookproof-normalize-proof
       lib claim nil (list *proof-not*)
       (list (b1-logic-equal-to query) (b1-logic-equal-to empty)) nil))))

(defun b1-typed-alists-alist-bound-requires-key (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (claim (caddr implication))
       (bound (proof-term-at claim 1))
       (query (b1-revappend-open-list lib bound nil))
       (body (b1-typed-alists-first-at query 2))
       (assoc-term (proof-term-at body 1)))
    (b1-typed-alists-prove-implication
     lib formula premise
     (b1-typed-alists-alist-bound-requires-key-consequence premise lib assoc-term claim query))))

(defun b1-typed-alists-range-of-association (lib formula)
  (let ((name (proof-sym "SELF-RANGE-OF-ASSOCIATION" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (let* ((lookup (list (proof-sym "ASSOC-EQUAL" "ACL2")
                                     *library-x* *b1-typed-alists-l*))
                       (guard (proof-ite (list *b1-typed-alists-alist* *b1-typed-alists-l*)
                                         lookup *proof-false*))
                       (claim (list *library-implies* guard
                                    (list *b1-typed-alists-range* (list *library-cdr* lookup)))))
                  (proof-with-checked-results
                      ((step (b1-typed-alists-typed-alist-lookup lib claim)))
                    (library-library-lemma lib "RANGE-OF-ASSOCIATION" claim step nil)))))
         (step (b1-logic-bookproof-from-fact lib name formula)))
      (cons step lib))))

(defun b1-typed-alists-alist-type-binding-consequence (premise lib opened)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-proof-conjunct proof premise))
         (exists-term (proof-step-first (cadr parts)))
         (unfolded (b1-revappend-open-list lib exists-term nil))
         (found (proof-proof-rewrite proof (cadr parts) unfolded '(1)))
         (known (b1-revappend-cons-is-nonempty lib found))
         (typed-term (proof-step-first (car parts)))
         (known-term (proof-step-first known))
         (guard (proof-ite typed-term known-term *proof-false*))
         (body (b1-typed-alists-first-at opened 2))
         (range-result
          (b1-typed-alists-range-of-association
           lib (list *library-implies* guard (list *b1-typed-alists-range* body)))))
      (let* ((lib (cdr range-result))
             (proof (library-library-proof lib)))
        (proof-with-checked-results
            ((guard-step (b1-logic-bookproof-normalize-proof
                          lib guard (list (car parts) known) nil nil nil))
             (result (proof-proof-modus-ponens proof (car range-result) guard-step))
             (step (library-library-transport-argument lib result opened 1)))
          (cons step lib))))))

(defun b1-typed-alists-alist-type-binding (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (call (proof-term-at (caddr implication) 1))
       (opened (b1-revappend-open-list lib call nil))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (result (b1-typed-alists-alist-type-binding-consequence premise lib opened))
       (step (b1-logic-bookproof-prove-implication-with-premise
              (cdr result) formula premise (car result))))
    (cons step (cdr result))))

(defun b1-typed-alists-alist-projection-type-opened (cell evidence lib view)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((call (b1-typed-alists-first-at view 2))
         (opened (b1-revappend-open-list lib call (cons cell evidence))))
      (proof-proof-chain proof view (list opened)))))

(defun b1-typed-alists-alist-projection-type-base (atom lib formula name view)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof name nil))
         (parts (proof-proof-conjunct proof fact)))
      (b1-typed-alists-prove-implication
       lib formula premise
       (proof-with-checked-results
           ((opened (b1-typed-alists-alist-projection-type-opened atom nil lib view)))
         (library-library-transport-argument lib (car parts) opened 1))))))

(defun b1-typed-alists-alist-projection-type-step-consequence
    (premise lib cell induction domain name view)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (b1-typed-alists-alist-parts lib premise cell))
         (fields (proof-list-of-length parts 4))
         (result (proof-proof-modus-ponens proof induction (cadddr fields)))
         (call (b1-typed-alists-first-at result 1))
         (unfolded (proof-proof-unfold proof call))
         (recursive (proof-proof-rewrite proof result unfolded '(1 1)))
         (actual (b1-typed-alists-alist-projection-type-opened cell (list (car fields)) lib view))
         (body (b1-typed-alists-first-at actual 2))
         (args (proof-list-of-length (cdr body) 2))
         (fact (proof-proof-fact proof name (list (list *library-x* (car args))
                                                 (list *b1-typed-alists-l* (cadr args)))))
         (conjuncts (proof-proof-conjunct proof fact))
         (law (cadr conjuncts))
         (test (b1-typed-alists-first-at law 2))
         (typed (b1-logic-bookproof-normalize-proof
                 lib test (list (if domain (cadr fields) (caddr fields)) recursive) nil nil nil))
         (transported (proof-proof-transport proof typed law)))
      (library-library-transport-argument lib transported actual 1))))

(defun b1-typed-alists-alist-projection-type-step (cell induction lib formula domain name view)
  (b1-typed-alists-prove-implication
   lib formula premise
   (b1-typed-alists-alist-projection-type-step-consequence
    premise lib cell induction domain name view)))

(defun b1-typed-alists-alist-projection-type (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((implication (proof-list-of-length formula 3))
         (claim (proof-list-of-length (caddr implication) 2))
         (parts (proof-list-of-length (cadr claim) 2)))
      (let* ((xs (cadr parts))
             (domain (equal (car claim) (proof-sym "DOMAIN-TYPE" "ACL2")))
             (name (if domain *b1-typed-alists-domain-list-rule* *b1-typed-alists-range-list-rule*)))
        (proof-with-checked-results
            ((view (proof-proof-unfold proof (cadr claim)))
             (prep (b1-revappend-list-induction-prepare lib formula xs nil))
             (step (b1-typed-alists-alist-projection-type-step
                    (caddr prep) (cadddr prep) lib formula domain name view))
             (atom (proof-proof-assume proof (cadr prep) nil))
             (base (b1-typed-alists-alist-projection-type-base atom lib formula name view)))
          (b1-revappend-list-induction lib prep base step))))))

(defun b1-typed-alists-element-list-fields (lib typed cell name)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((xs (b1-typed-alists-first-at typed 1)))
      (let* ((head (list *library-car* xs))
             (tail (list *library-cdr* xs))
             (pair (list *proof-cons* head tail)))
        (proof-with-checked-results
            ((test (proof-step-first cell))
             (law (b1-logic-bookproof-from-fact
                   lib (proof-sym "CAR-CDR-ELIM" "ACL2")
                   (list *library-implies* test (proof-eq pair xs))))
             (expanded (proof-proof-modus-ponens proof law cell))
             (typed (library-library-transport-argument lib typed expanded 1))
             (fact (proof-proof-fact proof name (list (list *library-x* head)
                                                     (list *b1-typed-alists-l* tail))))
             (parts (proof-proof-conjunct proof fact))
             (opened (proof-proof-rewrite proof typed (cadr parts) '(1))))
          (proof-proof-conjunct proof opened))))))

(defun b1-typed-alists-element-list-cons (lib head tail name)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((item (b1-typed-alists-first-at head 1))
         (rest (b1-typed-alists-first-at tail 1))
         (fact (proof-proof-fact proof name (list (list *library-x* item)
                                                 (list *b1-typed-alists-l* rest))))
         (parts (proof-proof-conjunct proof fact))
         (claim (b1-typed-alists-first-at (cadr parts) 2))
         (body (b1-logic-bookproof-normalize-proof lib claim (list head tail) nil nil nil)))
      (proof-proof-transport proof body (cadr parts)))))

(defun b1-typed-alists-key-type-when-bound (lib typed bound)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((key (b1-typed-alists-first-at bound 1)))
      (let ((goal (list *b1-typed-alists-domain* key)))
        (proof-with-checked-results
            ((negative (proof-proof-assume proof goal nil))
             (typed-term (proof-step-first typed))
             (negative-term (proof-step-first negative))
             (guard (proof-ite typed-term negative-term *proof-false*))
             (bound-term (proof-step-first bound))
             (law (b1-logic-bookproof-from-fact
                   lib (proof-sym "ALIST-TYPE-BOUND?-EQUAL" "ACL2")
                   (list *library-implies* guard (proof-neg bound-term))))
             (guard-step (b1-logic-bookproof-normalize-proof
                          lib guard (list typed negative) nil nil nil))
             (contradiction (proof-proof-modus-ponens proof law guard-step))
             (cut (proof-proof-cut proof bound contradiction)))
          (proof-proof-front proof cut goal))))))

(defun b1-typed-alists-types-of-bound-entries-base (atom lib formula call rule-name)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof rule-name nil))
         (parts (proof-proof-conjunct proof fact)))
      (b1-typed-alists-prove-implication
       lib formula premise
       (proof-with-checked-results ((opened (b1-revappend-open-list lib call (list atom))))
         (library-library-transport-argument lib (car parts) opened 1))))))

(defun b1-typed-alists-types-of-bound-entries-step-consequence
    (typed lib cell induction test key-result rule-name call)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((tail (proof-proof-modus-ponens proof induction typed))
         (hit (proof-proof-assume proof test t))
         (miss (proof-proof-assume proof test nil))
         (head (if key-result
                   (b1-typed-alists-key-type-when-bound lib typed hit)
                 (proof-with-checked-results
                     ((typed-term (proof-step-first typed))
                      (hit-term (proof-step-first hit))
                      (guard (proof-ite typed-term hit-term *proof-false*))
                      (element (list *b1-typed-alists-range*
                                     (cons (proof-sym "BINDING-EQUAL" "ACL2") (cdr test))))
                      (law (b1-logic-bookproof-from-fact
                            lib (proof-sym "ALIST-TYPE-BINDING-EQUAL" "ACL2")
                            (list *library-implies* guard element)))
                      (guard-step (b1-logic-bookproof-normalize-proof
                                   lib guard (list typed hit) nil nil nil)))
                   (proof-proof-modus-ponens proof law guard-step))))
         (combined (b1-typed-alists-element-list-cons lib head tail rule-name))
         (opened (b1-revappend-open-list lib call (list cell hit)))
         (yes (library-library-transport-argument lib combined opened 1))
         (opened (b1-revappend-open-list lib call (list cell miss)))
         (no (library-library-transport-argument lib tail opened 1)))
      (proof-proof-cases proof test yes no))))

(defun b1-typed-alists-types-of-bound-entries-step
    (cell induction lib formula test key-result rule-name call)
  (b1-typed-alists-prove-implication
   lib formula typed
   (b1-typed-alists-types-of-bound-entries-step-consequence
    typed lib cell induction test key-result rule-name call)))

(defun b1-typed-alists-types-of-bound-entries (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((implication (proof-list-of-length formula 3))
         (claim (proof-list-of-length (caddr implication) 2))
         (call (proof-list-of-length (cadr claim) 3)))
      (let* ((queries (cadr call))
             (source (caddr call))
             (key-result (equal (car claim) (proof-sym "DOMAIN-TYPE" "ACL2")))
             (rule-name (if key-result *b1-typed-alists-domain-list-rule*
                          *b1-typed-alists-range-list-rule*))
             (test (list (proof-sym "BOUND?-EQUAL" "ACL2") (list *library-car* queries) source)))
        (proof-with-checked-results
            ((prep (b1-revappend-list-induction-prepare lib formula queries nil))
             (step (b1-typed-alists-types-of-bound-entries-step
                    (caddr prep) (cadddr prep) lib formula test key-result rule-name call))
             (atom (proof-proof-assume proof (cadr prep) nil))
             (base (b1-typed-alists-types-of-bound-entries-base atom lib formula call rule-name)))
          (b1-revappend-list-induction lib prep base step))))))

(defun b1-typed-alists-all-bound-requires-keys-base-consequence (premise lib atom proper)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
         (parts (proof-list-of-length conjuncts 3))
         (pred (proof-term-at proper 0))
         (reduction (b1-logic-bookproof-normalize
                     lib proper (list atom) (list pred *b1-logic-eq*) nil nil nil nil))
         (equality (proof-proof-rewrite proof (cadr parts) reduction '(1)))
         (fact (proof-proof-fact proof *b1-typed-alists-domain-list-rule* nil))
         (fields (proof-proof-conjunct proof fact)))
      (library-library-transport-argument lib (car fields) equality 1))))

(defun b1-typed-alists-all-bound-requires-keys-base (atom lib claim proper)
  (b1-typed-alists-prove-implication
   lib claim premise
   (b1-typed-alists-all-bound-requires-keys-base-consequence premise lib atom proper)))

(defun b1-typed-alists-all-bound-requires-keys-step-consequence
    (premise lib cell induction call queries)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
         (parts (proof-list-of-length conjuncts 3))
         (opened (b1-revappend-open-list lib call (list cell)))
         (keys (proof-proof-rewrite proof (caddr parts) opened '(1)))
         (split (proof-proof-conjunct proof keys))
         (head (b1-typed-alists-key-type-when-bound lib (car parts) (car split)))
         (tail-type (b1-structures-true-list-tail lib (cadr parts) cell))
         (test (b1-typed-alists-first-at induction 1))
         (guard (b1-logic-bookproof-normalize-proof
                 lib test (list (car parts) tail-type (cadr split)) nil nil nil))
         (tail (proof-proof-modus-ponens proof induction guard))
         (result (b1-typed-alists-element-list-cons lib head tail *b1-typed-alists-domain-list-rule*))
         (cell-test (proof-step-first cell))
         (cons-term (b1-typed-alists-first-at result 1))
         (rule (b1-logic-bookproof-from-fact
                lib (proof-sym "CAR-CDR-ELIM" "ACL2")
                (list *library-implies* cell-test (proof-eq cons-term queries))))
         (equality (proof-proof-modus-ponens proof rule cell)))
      (proof-proof-rewrite proof result equality '(1 1)))))

(defun b1-typed-alists-all-bound-requires-keys-step (cell induction lib claim call queries)
  (b1-typed-alists-prove-implication
   lib claim premise
   (b1-typed-alists-all-bound-requires-keys-step-consequence premise lib cell induction call queries)))

(defun b1-typed-alists-all-bound-requires-keys-consequence (premise lib claim call theorem denied)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
         (parts (proof-list-of-length conjuncts 3))
         (all-bound (proof-proof-assume proof call t))
         (guard (b1-logic-bookproof-normalize-proof
                 lib (cadr claim) (list (car parts) (cadr parts) all-bound) nil nil nil))
         (known (proof-proof-modus-ponens proof theorem guard))
         (cut (proof-proof-cut proof known (caddr parts))))
      (proof-proof-front proof cut denied))))

(defun b1-typed-alists-all-bound-requires-keys (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((implication (proof-list-of-length formula 3))
         (call (proof-term-at (caddr implication) 1))
         (args (proof-list-of-length call 3))
         (typed (proof-term-at (cadr implication) 1))
         (tests (proof-term-at (cadr implication) 2))
         (proper (proof-term-at tests 1))
         (negative (proof-term-at tests 2))
         (domain (proof-term-at negative 1)))
      (let* ((queries (cadr args))
             (denied (caddr implication))
             (claim (list *library-implies*
                          (proof-ite typed (proof-ite proper call *proof-false*) *proof-false*)
                          domain)))
        (proof-with-checked-results
            ((prep (b1-revappend-list-induction-prepare lib claim queries nil))
             (step (b1-typed-alists-all-bound-requires-keys-step
                    (caddr prep) (cadddr prep) lib claim call queries))
             (atom (proof-proof-assume proof (cadr prep) nil))
             (base (b1-typed-alists-all-bound-requires-keys-base atom lib claim proper))
             (theorem (b1-revappend-list-induction lib prep base step)))
          (b1-typed-alists-prove-implication
           lib formula premise
           (b1-typed-alists-all-bound-requires-keys-consequence
            premise lib claim call theorem denied)))))))

(defun b1-typed-alists-paired-alist-type-consequence-aligned-lengths
    (lib sizes cons-a cons-b atom-b claim more-a more-b)
  (let ((proof (library-library-proof lib))
        (unfold (list *b1-logic-eql* *b1-logic-eq*)))
    (proof-with-checked-results
        ((size-test (proof-step-first sizes))
         (normalized (b1-logic-bookproof-normalize lib size-test nil unfold nil nil nil nil))
         (before (proof-proof-rewrite proof sizes normalized '(1)))
         (length-step (b1-revappend-positive-length lib cons-a))
         (positive (proof-proof-rewrite proof length-step before '(1 2)))
         (right-term (b1-typed-alists-first-at before 2))
         (opened (b1-revappend-open-list lib right-term (list atom-b)))
         (impossible (proof-proof-rewrite proof positive opened '(1 2)))
         (zero (library-library-axiom lib "ZERO" nil))
         (mismatch (b1-logic-bookproof-contradiction lib impossible zero claim))
         (left-term (b1-typed-alists-first-at before 1))
         (left (b1-revappend-open-list lib left-term (list cons-a)))
         (right (b1-revappend-open-list lib right-term (list cons-b)))
         (opened (proof-proof-rewrite proof before left '(1 1)))
         (opened (proof-proof-rewrite proof opened right '(1 2)))
         (term (b1-typed-alists-first-at opened 1))
         (summed (proof-proof-reflexive proof (library-plus *proof-neg-one* term)))
         (summed (proof-proof-rewrite proof summed opened '(1 2 2)))
         (sum-left (b1-typed-alists-first-at summed 1))
         (smaller-left (library-library-linear-equal lib sum-left (list *library-len* more-a) nil))
         (sum-right (b1-typed-alists-first-at summed 2))
         (smaller-right (library-library-linear-equal lib sum-right (list *library-len* more-b) nil))
         (reversed (proof-proof-symmetric proof smaller-left))
         (equal-tail (proof-proof-chain proof reversed (list summed smaller-right)))
         (head (proof-term-at size-test 0))
         (literal (proof-step-first equal-tail))
         (reduced (b1-logic-bookproof-normalize
                   lib (cons head (cdr literal)) nil unfold nil nil nil nil))
         (smaller (proof-proof-transport proof equal-tail reduced)))
      (list mismatch smaller))))

(defun b1-typed-alists-paired-alist-type-range-evidence
    (lib pairs fields sizes fallback call claim cons-a cons-b atom-b more-a more-b)
  (if pairs
      (proof-with-checked-results
          ((aligned (b1-typed-alists-paired-alist-type-consequence-aligned-lengths
                     lib sizes cons-a cons-b atom-b claim more-a more-b))
           (proper (b1-structures-true-list-tail lib (car fields) cons-a)))
        (list (car aligned) (list proper) (list (cadr aligned))))
    (proof-with-checked-results
        ((opened (b1-revappend-open-list lib call (list cons-a atom-b)))
         (miss-value (library-library-transport-argument lib fallback opened 1)))
      (list miss-value nil (list fallback)))))

(defun b1-typed-alists-paired-alist-type-output (lib pairs next-step key value tail)
  (let ((proof (library-library-proof lib)))
    (if pairs
        (proof-with-checked-results
            ((pair (b1-typed-alists-first-at next-step 2))
             (entry (proof-term-at pair 1))
             (cell (b1-revappend-cons-value lib entry)))
          (b1-typed-alists-alist-cons lib pair (list cell key value tail)))
      (proof-with-checked-results
          ((guard (b1-typed-alists-induction-guard lib tail key value))
           (test (proof-step-first guard))
           (call (b1-typed-alists-first-at next-step 2))
           (rule (b1-logic-bookproof-from-fact
                  lib (proof-sym "ALIST-TYPE-BIND-EQUAL" "ACL2")
                  (list *library-implies* test (list *b1-typed-alists-alist* call)))))
        (proof-proof-modus-ponens proof rule guard)))))

(defun b1-typed-alists-paired-alist-type-consequence
    (premise lib claim call keys values test-a test-b more-a more-b induction pairs)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((cons-a (proof-proof-assume proof test-a t))
         (cons-b (proof-proof-assume proof test-b t))
         (atom-a (proof-proof-assume proof test-a nil))
         (atom-b (proof-proof-assume proof test-b nil))
         (fields (b1-logic-bookproof-split-conjuncts lib premise))
         (parts (if pairs (proof-list-of-length fields 4) fields))
         (domain-type (proof-term-at parts (if pairs 1 0)))
         (range-type (proof-term-at parts (if pairs 2 1)))
         (sizes (if pairs (cadddr parts) nil))
         (fallback (if pairs (b1-typed-alists-empty-alist lib) (proof-term-at fields 2)))
         (opened (b1-revappend-open-list lib call (list atom-a)))
         (empty (library-library-transport-argument lib fallback opened 1))
         (evidence (b1-typed-alists-paired-alist-type-range-evidence
                    lib pairs fields sizes fallback call claim cons-a cons-b atom-b more-a more-b))
         (keys-type (b1-typed-alists-element-list-fields
                     lib domain-type cons-a *b1-typed-alists-domain-list-rule*))
         (values-type (b1-typed-alists-element-list-fields
                       lib range-type cons-b *b1-typed-alists-range-list-rule*))
         (hypothesis (b1-induction-tree-induction-hypothesis
                      induction (table-put (list (cons keys more-a)) values more-b)
                      (list (list test-a t))))
         (test (b1-typed-alists-first-at (car hypothesis) 1))
         (guard (b1-logic-bookproof-normalize-proof
                 lib test (append (cadr evidence)
                                  (list (cadr keys-type) (cadr values-type))
                                  (caddr evidence))
                 nil nil nil))
         (tail (proof-proof-modus-ponens proof (car hypothesis) guard))
         (next-step (b1-revappend-open-list lib call (list cons-a cons-b)))
         (output (b1-typed-alists-paired-alist-type-output
                  lib pairs next-step (car keys-type) (car values-type) tail))
         (matched (library-library-transport-argument lib output next-step 1))
         (both (proof-proof-cases proof test-b matched (car evidence)))
         (result (proof-proof-cases proof test-a both empty)))
      (cons result (cdr hypothesis)))))

(defun b1-typed-alists-paired-alist-type (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (claim (caddr implication))
       (call (proof-term-at claim 1))
       (parts (cond ((integerp call) (proof-list-of-length call 3))
                    ((< (len call) 3)
                     '(:failure "failure" ""))
                    (t call))))
    (let* ((keys (cadr parts))
           (values (caddr parts))
           (test-a (list *proof-consp* keys))
           (test-b (list *proof-consp* values))
           (more-a (list *library-cdr* keys))
           (more-b (list *library-cdr* values))
           (induction (b1-induction-tree-induction-init lib formula keys))
           (pairs (not (cdddr call))))
      (proof-with-checked-results
          ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
           (result (b1-typed-alists-paired-alist-type-consequence
                    premise lib claim call keys values test-a test-b more-a more-b induction pairs))
           (step (b1-logic-bookproof-prove-implication-with-premise
                  lib formula premise (car result))))
        (b1-induction-tree-induction-finish (cdr result) step)))))
