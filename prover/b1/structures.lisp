(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-structures-read-oracle* (proof-sym "READ-ACL2-ORACLE" "ACL2"))
(defconst *b1-structures-update-oracle* (proof-sym "UPDATE-ACL2-ORACLE" "ACL2"))
(defconst *b1-structures-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *b1-structures-global-table* (proof-sym "GLOBAL-TABLE" "ACL2"))
(defconst *b1-structures-get-global* (proof-sym "GET-GLOBAL" "ACL2"))
(defconst *b1-structures-nth* (proof-cl "NTH"))
(defconst *b1-structures-length* (proof-cl "LENGTH"))
(defconst *b1-structures-true-listp* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *b1-structures-symbol-listp* (proof-sym "SYMBOL-LISTP" "ACL2"))
(defconst *b1-structures-pseudo* (proof-sym "PSEUDO-TERMP" "ACL2"))
(defconst *b1-structures-pseudo-list* (proof-sym "PSEUDO-TERM-LISTP" "ACL2"))
(defconst *b1-structures-projection-unfold*
  (list *b1-logic-atom* *b1-logic-eq* *proof-not* *b1-logic-zp*
        (proof-sym "NFIX" "ACL2")))

(defun b1-structures-project-mv-field (lib result)
  (proof-with-checked-results ((term (b1-logic-step-at result 2)))
    (if (proof-is-call term *b1-structures-mv-nth*)
        (proof-with-checked-results ((items (proof-term-at term 2)))
          (if (and (not (proof-is-call items *proof-cons*))
                   (not (proof-is-call items *proof-quote*)))
              result
            (proof-with-checked-results
                ((field (b1-logic-bookproof-normalize
                         lib term nil
                         (list *b1-structures-mv-nth* *b1-logic-atom*
                               *b1-logic-zp* *proof-not*) nil nil nil nil))
                 (right (b1-logic-step-at field 2))
                 (left (b1-logic-step-at field 1)))
              (if (equal right left)
                  result
                (proof-with-checked-results
                    ((next (proof-proof-chain (library-library-proof lib)
                                              result (list field))))
                  (cons :continue next))))))
      result)))

(defun b1-structures-project-mv-fields (n lib pending)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "b1-structures-project-mv-fields"))
        ((eq (car pending) :continue)
         (b1-structures-project-mv-fields
          (1- n) lib (b1-structures-project-mv-field lib (cdr pending))))
        (t pending)))

(defun b1-structures-project-mv (lib selector equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reflexive (proof-proof-reflexive proof selector))
         (result (proof-proof-rewrite proof reflexive equation '(1 2 2))))
      (b1-structures-project-mv-fields
       1000000 lib (b1-structures-project-mv-field lib result)))))

(defun b1-structures-proper-list-is-not-string (lib proper)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((items (b1-logic-step-at proper 1)))
      (let ((test (list *proof-consp* items)))
        (proof-with-checked-results
            ((some-cons (proof-proof-assume proof test t))
             (atom-case (proof-proof-assume proof test nil))
             (fact (proof-proof-fact proof "consp-not-stringp"
                                     (list (list *library-x* items))))
             (yes (proof-proof-modus-ponens proof fact some-cons))
             (fixed (b1-logic-bookproof-normalize
                     lib (b1-logic-step-first proper) (list atom-case)
                     (list *b1-structures-true-listp* *b1-logic-eq*) nil nil nil nil))
             (empty (proof-proof-rewrite proof proper fixed '(1)))
             (empty-type (b1-logic-bookproof-normalize-proof
                          lib (proof-neg (list *b1-logic-stringp* *proof-false*))
                          nil (list *proof-not*) nil nil))
             (same (proof-proof-symmetric proof empty))
             (no (proof-proof-rewrite proof empty-type same '(1 1 1))))
          (proof-proof-cases proof test yes no))))))

(defun b1-structures-oracle-projection-mv-projection (term lib)
  (if (not (proof-is-call term *b1-structures-mv-nth*))
      nil
    (proof-with-checked-results ((index (proof-term-at term 1)))
      (if (not (proof-is-call index *proof-quote*))
          nil
        (proof-with-checked-results ((items (proof-term-at term 2)))
          (if (not (proof-is-call items *proof-cons*))
              nil
            (let ((proof (library-library-proof lib)))
              (proof-with-checked-results
                  ((opened (proof-proof-unfold proof term))
                   (body (b1-logic-step-at opened 2))
                   (reduction (b1-logic-bookproof-normalize
                               lib body nil *b1-structures-projection-unfold*
                               nil nil nil nil)))
                (proof-proof-chain proof opened (list reduction))))))))))

(defun b1-structures-oracle-projection-normalize (n lib formula unfold rules replies result)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "b1-structures-oracle-projection-normalize"))
        ((failure-p result) result)
        ((not (b1-logic-call-p result)) (car result))
        (t
         (let* ((current (b1-logic-call-library result))
                (term (b1-logic-call-term result))
                (step (b1-structures-oracle-projection-mv-projection term current))
                (reply (if (failure-p step) step (cons step current)))
                (replies (append replies (list reply))))
           (b1-structures-oracle-projection-normalize
            (1- n) lib formula unfold rules replies
            (b1-logic-bookproof-normalize-proof-with-library
             lib formula nil unfold rules nil replies))))))

(defun b1-structures-oracle-projection (lib formula)
  (proof-with-checked-results
      ((left (proof-term-at formula 1))
       (field (proof-term-at left 0))
       (update-rule (b1-logic-bookproof-rewrite-rule
                     lib (proof-sym "NTH-UPDATE-NTH" "ACL2"))))
    (let* ((unfold (list* field *b1-structures-read-oracle* *b1-structures-update-oracle*
                          *b1-structures-get-global* *b1-structures-global-table*
                          *b1-structures-projection-unfold*))
           (rules (list '(:callback :b1-structures-mv-projection) update-rule)))
      (b1-structures-oracle-projection-normalize
       1000000 lib formula unfold rules nil
       (b1-logic-bookproof-normalize-proof-with-library lib formula nil unfold rules nil nil)))))

(defun b1-structures-pseudo-tail-consequence (premise lib formula)
  (proof-with-checked-results
      ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
       (parts (proof-list-of-length conjuncts 3))
       (goal (proof-term-at formula 2)))
    (b1-logic-bookproof-forces
     lib goal (car parts) (cdr parts)
     (list *b1-structures-pseudo* *b1-logic-atom* *b1-logic-eq* *proof-not*) nil)))

(defun b1-structures-pseudo-tail (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-structures-pseudo-tail-consequence premise lib formula)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-structures-length-of-list (lib step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((term (b1-logic-step-at step 1)))
      (let ((test (list *proof-consp* term)))
        (proof-with-checked-results
            ((fact (proof-proof-fact proof "consp-not-stringp"
                                     (list (list *library-x* term))))
             (some-cons (proof-proof-assume proof test t))
             (yes (proof-proof-modus-ponens proof fact some-cons))
             (noncons (proof-proof-assume proof test nil))
             (term-nil (proof-proof-simplify-first
                        proof step (list noncons)
                        (list *b1-structures-true-listp* *b1-logic-eq*)))
             (nil-not-string (b1-logic-bookproof-normalize-proof
                              lib (proof-neg (list *b1-logic-stringp* *proof-false*))
                              nil (list *proof-not*) nil nil))
             (same (proof-proof-symmetric proof term-nil))
             (no (proof-proof-rewrite proof nil-not-string same '(1 1 1)))
             (bound (proof-proof-cases proof test yes no)))
          (b1-logic-bookproof-normalize lib (list *b1-structures-length* term)
                                       (list bound) (list *b1-structures-length*)
                                       nil nil nil nil))))))

(defun b1-structures-symbol-list-implies-list-consequence
    (premise lib formula induction test tail)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((noncons (proof-proof-assume proof test nil))
         (some-cons (proof-proof-assume proof test t))
         (opened (proof-proof-simplify-first
                  proof premise (list some-cons)
                  (list *b1-structures-symbol-listp* *b1-logic-atom* *proof-not*)))
         (parts (proof-proof-conjunct proof opened))
         (hypothesis (b1-induction-tree-induction-hypothesis
                      induction (list (cons *library-x* tail)) (list (list test t))))
         (tail-is-list (proof-proof-modus-ponens proof (car hypothesis) (cadr parts)))
         (yes (b1-logic-bookproof-normalize-proof
               lib (caddr formula) (list some-cons tail-is-list)
               (list *b1-structures-true-listp*) nil nil))
         (base (proof-proof-simplify-first
                proof premise (list noncons)
                (list *b1-structures-symbol-listp* *b1-logic-atom* *proof-not*
                      *b1-logic-eq*)))
         (no (b1-logic-bookproof-normalize-proof
              lib (caddr formula) (list noncons base)
              (list *b1-structures-true-listp* *b1-logic-eq*) nil nil))
         (consequence (proof-proof-cases proof test yes no)))
      (cons consequence (cdr hypothesis)))))

(defun b1-structures-symbol-list-implies-list (lib)
  (let ((name (proof-sym "SELF-SYMBOL-LIST-IS-TRUE-LIST" "ACL2")))
    (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
        (cons name lib)
      (let* ((formula (list *library-implies* (list *b1-structures-symbol-listp* *library-x*)
                            (list *b1-structures-true-listp* *library-x*)))
             (induction (b1-induction-tree-induction-init lib formula *library-x*))
             (test (list *proof-consp* *library-x*))
             (tail (list *library-cdr* *library-x*)))
        (proof-with-checked-results
            ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
             (consequence (b1-structures-symbol-list-implies-list-consequence
                           premise lib formula induction test tail))
             (step (b1-logic-bookproof-prove-implication-with-premise
                    lib formula premise (car consequence)))
             (finished (b1-induction-tree-induction-finish (cdr consequence) step))
             (updated (library-library-lemma lib "SYMBOL-LIST-IS-TRUE-LIST"
                                             formula finished nil)))
          (cons name updated))))))

(mutual-recursion
 (defun b1-structures-wrappers (term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((proof-is-call term *termination-return-last*)
          (if (consp (cdddr term))
              (proof-with-checked-results ((tail (b1-structures-wrappers (cadddr term))))
                (cons term tail))
            '(:failure "failure" "")))
         ((and (consp term) (proof-compound term) (not (proof-is-call term *proof-quote*)))
          (b1-structures-wrappers-arguments (cdr term)))
         (t nil)))
 (defun b1-structures-wrappers-arguments (args)
   (declare (xargs :measure (acl2-count args)))
   (if (consp args)
       (proof-with-checked-results
           ((head (b1-structures-wrappers (car args)))
            (tail (b1-structures-wrappers-arguments (cdr args))))
         (append head tail))
     nil)))

(defun b1-structures-pseudo-lambda-open-wrappers (proof body wrappers)
  (declare (xargs :measure (acl2-count wrappers)))
  (if (or (failure-p body) (endp wrappers))
      body
    (let ((next (proof-with-checked-results
                    ((opened (proof-proof-unfold proof (car wrappers))))
                  (proof-proof-rewrite-first proof body opened))))
      (b1-structures-pseudo-lambda-open-wrappers proof next (cdr wrappers)))))

(defun b1-structures-pseudo-lambda-open-lengths (lib body proofs)
  (declare (xargs :measure (acl2-count proofs)))
  (if (or (failure-p body) (endp proofs))
      body
    (let* ((proof (library-library-proof lib))
           (next (proof-with-checked-results
                     ((length-of-list (b1-structures-length-of-list lib (car proofs)))
                      (symmetric (proof-proof-symmetric proof length-of-list)))
                   (proof-proof-rewrite-first proof body symmetric))))
      (b1-structures-pseudo-lambda-open-lengths lib next (cdr proofs)))))

(defun b1-structures-pseudo-lambda-consequence (premise lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((conjuncts (b1-logic-bookproof-split-conjuncts lib premise))
         (parts (proof-list-of-length conjuncts 3))
         (tree (b1-logic-step-at (car parts) 1)))
      (let* ((assertion (car parts))
             (some-cons (cadr parts))
             (nonsymbol (caddr parts))
             (head (list *library-car* tree))
             (tail (list *library-cdr* tree))
             (quoted (proof-quote (proof-cl "QUOTE")))
             (quote-test (proof-eq head quoted)))
        (proof-with-checked-results
            ((symbol-type (b1-logic-bookproof-normalize-proof
                           lib (list *b1-logic-symbolp* quoted) nil nil nil nil))
             (is-quote (proof-proof-assume proof quote-test t))
             (quote-head (proof-proof-symmetric proof is-quote))
             (symbol-type (proof-proof-rewrite proof symbol-type quote-head '(1 1)))
             (contradiction (proof-proof-cut proof symbol-type nonsymbol))
             (unquoted (proof-proof-front proof contradiction (proof-neg quote-test)))
             (tail-formula (proof-proof-fact
                            proof (proof-sym "PSEUDO-TERMP-IMPLIES-PSEUDO-TERM-LISTP-CDR"
                                             "ACL2") nil))
             (guard-term (b1-logic-step-at tail-formula 1))
             (guard-proof (b1-logic-bookproof-normalize-proof
                           lib guard-term (list assertion some-cons unquoted) nil nil nil))
             (tail-pseudo (proof-proof-modus-ponens proof tail-formula guard-proof))
             (forward (proof-proof-fact
                       proof (proof-sym "PSEUDO-TERM-LISTP-FORWARD-TO-TRUE-LISTP" "ACL2")
                       (list (list *library-x* tail))))
             (tail-list (proof-proof-modus-ponens proof forward tail-pseudo))
             (reduction (b1-logic-bookproof-normalize
                         lib (b1-logic-step-first assertion)
                         (list some-cons unquoted tail-pseudo nonsymbol)
                         (list *b1-structures-pseudo* *b1-logic-eq* *b1-logic-atom*
                               *proof-not*) nil nil nil nil))
             (body (proof-proof-rewrite proof assertion reduction '(1)))
             (body-term (b1-logic-step-first body))
             (wrappers (b1-structures-wrappers body-term))
             (body (b1-structures-pseudo-lambda-open-wrappers proof body (proof-unique wrappers)))
             (facts (b1-logic-bookproof-split-conjuncts lib body))
             (lemma (b1-structures-symbol-list-implies-list lib)))
          (let* ((updated (cdr lemma))
                 (proof (library-library-proof updated)))
            (if (not (consp (cdddr facts)))
                '(:failure "failure" "")
              (proof-with-checked-results
                  ((formals (b1-logic-step-at (cadddr facts) 1))
                   (symbol-list (proof-proof-fact proof (car lemma)
                                                  (list (list *library-x* formals))))
                   (formals-is-list (proof-proof-modus-ponens proof symbol-list (cadddr facts)))
                   (body (b1-structures-pseudo-lambda-open-lengths
                          updated body (list (car facts) formals-is-list tail-list)))
                   (goal (proof-term-at formula 2))
                   (consequence (proof-proof-front proof body goal)))
                (cons consequence updated)))))))))

(defun b1-structures-pseudo-lambda (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-structures-pseudo-lambda-consequence premise lib formula))
       (step (b1-logic-bookproof-prove-implication-with-premise
              (cdr consequence) formula premise (car consequence))))
    (cons step (cdr consequence))))

(defun b1-structures-noncons-selector (lib selector noncons)
  (let ((proof (library-library-proof lib))
        (name (if (equal selector *library-car*) "COMPLETION-OF-CAR" "COMPLETION-OF-CDR")))
    (proof-with-checked-results
        ((negated (b1-logic-step-at noncons 1))
         (term (proof-term-at negated 1))
         (opened (library-library-axiom lib name (list term)))
         (body (b1-logic-step-at opened 2))
         (selected (proof-proof-select proof body noncons)))
      (proof-proof-chain proof opened (list selected)))))

(defun b1-structures-open-mv-nth-consequence (premise lib call branches atom-test)
  (declare (ignore premise))
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof call))
         (body (b1-logic-step-at opened 2))
         (on-cons (proof-proof-if-false proof body))
         (on-cons (proof-proof-chain proof opened (list on-cons)))
         (is-atom (proof-proof-assume proof atom-test t))
         (atom-equation (proof-proof-unfold proof atom-test))
         (noncons (proof-proof-rewrite proof is-atom atom-equation '(1)))
         (tail (b1-structures-noncons-selector lib *library-cdr* noncons))
         (head (b1-structures-noncons-selector lib *library-car* noncons))
         (recursive (proof-term-at branches 3))
         (identity (proof-proof-reflexive proof recursive))
         (reduced (proof-proof-rewrite proof identity tail '(1 2 2)))
         (reduced-recursion (b1-logic-step-at reduced 2))
         (normalized (b1-logic-bookproof-normalize
                      lib reduced-recursion nil
                      (list *b1-structures-mv-nth* *b1-logic-atom* *proof-not*)
                      nil nil nil nil))
         (reduced (proof-proof-chain proof reduced (list normalized)))
         (choice (b1-logic-bookproof-normalize
                  lib branches nil nil
                  (list (b1-logic-equal-to head) (b1-logic-equal-to reduced)) nil nil t))
         (selected (proof-proof-select proof body is-atom))
         (reversed (proof-proof-symmetric proof choice))
         (on-atom (proof-proof-chain proof opened (list selected reversed))))
      (proof-proof-cases proof atom-test on-atom on-cons))))

(defun b1-structures-open-mv-nth (lib formula)
  (proof-with-checked-results
      ((claim (proof-term-at formula 2))
       (sides (if (integerp claim)
                  '(:failure "failure" "")
                (proof-list-of-length (cdr claim) 2)))
       (items (proof-term-at (car sides) 2))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-structures-open-mv-nth-consequence
                     premise lib (car sides) (cadr sides) (list *b1-logic-atom* items))))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-structures-true-list-tail (lib step some-cons)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (b1-logic-step-first step))
         (opened (proof-proof-unfold proof literal))
         (body (b1-logic-step-at opened 2))
         (selected (proof-proof-select proof body some-cons))
         (equality (proof-proof-chain proof opened (list selected))))
      (proof-proof-rewrite proof step equality '(1)))))

(defun b1-structures-option-entry-tail-consequence-leaf (value tests call head recursive head-tail)
  (declare (ignore tests))
  (cond ((proof-is-call value (car call)) recursive)
        ((equal value head) head-tail)
        (t '(:failure "failure" ""))))

(defun b1-structures-option-entry-tail-leaves (requests call head recursive head-tail)
  (declare (xargs :measure (acl2-count requests)))
  (if (endp requests)
      nil
    (let* ((request (car requests))
           (step (b1-structures-option-entry-tail-consequence-leaf
                  (car request) (cadr request) call head recursive head-tail)))
      (proof-with-checked-results
          ((rest (b1-structures-option-entry-tail-leaves
                  (cdr requests) call head recursive head-tail)))
        (cons (cons request step) rest)))))

(defun b1-structures-option-entry-tail-consequence
    (premise lib call xs head tail test induction template empty)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((lookup (proof-proof-unfold proof call))
         (lookup-body (b1-logic-step-at lookup 2))
         (is-atom (proof-proof-assume proof test t))
         (empty-lookup (proof-proof-select proof lookup-body is-atom))
         (closed-empty-lookup (proof-proof-symmetric proof empty-lookup))
         (base (proof-proof-rewrite-result proof empty closed-empty-lookup
                                           template *proof-result*))
         (some-cons (proof-proof-assume proof test nil))
         (premise-literal (b1-logic-step-first premise))
         (opened (proof-proof-unfold proof premise-literal))
         (opened-body (b1-logic-step-at opened 2))
         (chosen (proof-proof-select proof opened-body some-cons))
         (opened (proof-proof-chain proof opened (list chosen)))
         (opened-premise (proof-proof-rewrite proof premise opened '(1)))
         (conjuncts (b1-logic-bookproof-split-conjuncts lib opened-premise))
         (parts (proof-list-of-length conjuncts 2))
         (element-literal (b1-logic-step-first (car parts)))
         (beta (proof-proof-beta proof element-literal))
         (element (proof-proof-rewrite proof (car parts) beta '(1))))
      (let ((head-test (list *proof-consp* head)))
        (proof-with-checked-results
            ((head-cons (proof-proof-assume proof head-test t))
             (opened-type (b1-logic-bookproof-normalize
                           lib (b1-logic-step-first element) (list head-cons)
                           (list *b1-logic-atom* *proof-not*) nil nil nil nil))
             (opened-element (proof-proof-rewrite proof element opened-type '(1)))
             (head-types (proof-proof-conjunct proof opened-element))
             (proper-tail (b1-structures-true-list-tail lib (car head-types) head-cons))
             (head-noncons (proof-proof-assume proof head-test nil))
             (tail-nil (b1-structures-noncons-selector lib *library-cdr* head-noncons))
             (empty-tail (b1-logic-bookproof-normalize-proof
                          lib (list *b1-structures-true-listp* *proof-false*) nil
                          (list *b1-structures-true-listp* *b1-logic-eq*) nil nil))
             (head-empty (library-library-transport-argument lib empty-tail tail-nil 1))
             (head-tail (proof-proof-cases proof head-test proper-tail head-empty))
             (smaller (b1-induction-tree-induction-hypothesis
                       induction (list (cons xs tail)) (list (list test nil))))
             (recursive (proof-proof-modus-ponens proof (car smaller) (cadr parts)))
             (selection (proof-proof-select proof lookup-body some-cons))
             (value (b1-logic-step-at selection 2))
             (requests (proof-proof-by-value-leaves proof value nil))
             (leaves (b1-structures-option-entry-tail-leaves
                      requests call head recursive head-tail))
             (step (proof-proof-by-value proof value template leaves nil))
             (closed-selection (proof-proof-symmetric proof selection))
             (step (proof-proof-rewrite-result proof step closed-selection template *proof-result*))
             (cases (proof-proof-cases proof test base step))
             (closed-lookup (proof-proof-symmetric proof lookup))
             (result (proof-proof-rewrite-result proof cases closed-lookup template *proof-result*)))
          (cons result (cdr smaller)))))))

(defun b1-structures-option-entry-tail (lib formula)
  (proof-with-checked-results
      ((result (proof-term-at formula 2))
       (parts (proof-list-of-length result 2))
       (call (proof-term-at (cadr parts) 1))
       (xs (proof-term-at call 2)))
    (let* ((head (list *library-car* xs))
           (tail (list *library-cdr* xs))
           (test (list *b1-logic-atom* xs))
           (induction (b1-induction-tree-induction-init lib formula xs))
           (template (list *b1-structures-true-listp* (list *library-cdr* *proof-result*))))
      (proof-with-checked-results
          ((empty (b1-logic-bookproof-normalize-proof
                   lib (list *b1-structures-true-listp* (list *library-cdr* *proof-false*))
                   nil (list *b1-structures-true-listp* *b1-logic-eq*) nil nil))
           (premise (b1-logic-bookproof-prove-implication-premise lib formula))
           (consequence (b1-structures-option-entry-tail-consequence
                         premise lib call xs head tail test induction template empty))
           (step (b1-logic-bookproof-prove-implication-with-premise
                  lib formula premise (car consequence))))
        (b1-induction-tree-induction-finish (cdr consequence) step)))))
