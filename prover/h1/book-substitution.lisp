(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-book-substitution-term* (proof-sym "PSEUDO-TERMP" "ACL2"))
(defconst *h1-book-substitution-terms* (proof-sym "PSEUDO-TERM-LISTP" "ACL2"))
(defconst *h1-book-substitution-cons-term* (proof-sym "CONS-TERM" "ACL2"))
(defconst *h1-book-substitution-cons-term1* (proof-sym "CONS-TERM1" "ACL2"))
(defconst *h1-book-substitution-cons-term2* (proof-sym "CONS-TERM1-MV2" "ACL2"))
(defconst *h1-book-substitution-kwote* (proof-sym "KWOTE" "ACL2"))
(defconst *h1-book-substitution-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *h1-book-substitution-strip-cdrs* (proof-sym "STRIP-CDRS" "ACL2"))
(defconst *h1-book-substitution-eq* (proof-cl "EQ"))
(defconst *h1-book-substitution-quote-name* (proof-quote *proof-quote*))

(defun h1-book-substitution-add-lemma (proof name claim step conditions)
  (proof-with-checked-results
      ((lib (library-library-lemma (h1-tactics-prover-library proof)
                                    name claim step conditions)))
    (h1-tactics-prover-with-library proof lib)))

(defun h1-book-substitution-note (proof name step)
  (proof-with-checked-results
      ((claim (proof-step-first step))
       (updated (h1-book-substitution-add-lemma proof name claim step (cdr (proof-step-clause step))))
       (citation (library-library-cite (h1-tactics-prover-library updated) name nil nil)))
    (cons citation updated)))

(defun h1-book-substitution-tuple-result (proof value)
  (if (not (proof-is-call value *proof-cons*))
      '(:failure "unproved" "")
    (proof-with-checked-results ((tail (proof-term-at value 2)))
      (if (not (proof-is-call tail *proof-cons*))
          '(:failure "unproved" "")
        (proof-with-checked-results ((end (proof-term-at tail 2)))
          (if (not (equal end *proof-false*))
              '(:failure "unproved" "")
            (library-library-cite (h1-tactics-prover-library proof) "TUPLE-RESULT"
                                  (list (cadr value) (cadr tail)) nil)))))))

(defun h1-book-substitution-term-choice (proof value typed-yes typed-no)
  (if (integerp value)
      '(:failure "failure" "")
    (library-library-cite (h1-tactics-prover-library proof) "TERM-IF" (cdr value)
                          (list typed-yes typed-no))))

(defun h1-book-substitution-typed-value (n proof value known)
  (declare (xargs :measure (nfix n)))
  (let ((lib (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof))
        (entry (assoc-equal value known)))
    (cond
     ((zp n) '(:failure "fuel" "h1-book-substitution-typed-value"))
     (entry (cdr entry))
     ((proof-is-call value *h1-book-substitution-kwote*)
      (library-library-cite lib "QUOTED-TERM" (cdr value) nil))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((parts (proof-list-of-length value 4))
           (yes (h1-book-substitution-typed-value (1- n) proof (caddr parts) known))
           (no (h1-book-substitution-typed-value (1- n) proof (cadddr parts) known)))
        (h1-book-substitution-term-choice proof value yes no)))
     ((proof-compound (h1-tactics-call-head value))
      (proof-with-checked-results
          ((equation (proof-proof-beta core value))
           (opened (proof-rewritten-term equation))
           (typed (h1-book-substitution-typed-value (1- n) proof opened known)))
        (h1-propositions-library-transport-argument lib typed equation 1)))
     (t '(:failure "unproved" "")))))

(defun h1-book-substitution-list-selector-type (proof label selector typed empty no test predicate)
  (let ((lib (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((completion (library-library-axiom
                      lib (concatenate 'string "COMPLETION-OF-" (caddr selector))
                      (list *library-x*)))
         (default (h1-propositions-select-value lib completion no))
         (at-atom (h1-propositions-library-transport-argument lib empty default 1))
         (step (proof-proof-cases core test typed at-atom))
         (claim (proof-step-first step)))
      (h1-book-substitution-add-lemma proof label claim step (list (proof-neg predicate))))))

(defun h1-book-substitution-list-types (proof)
  (let* ((lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (predicate (list *h1-book-substitution-terms* *library-x*))
         (test (list *proof-consp* *library-x*))
         (value (list *proof-cons* *library-x* *library-y*))
         (term (list *h1-book-substitution-terms* value)))
    (proof-with-checked-results
        ((assumption (h1-arithmetic-proof-assume core predicate t))
         (yes (h1-arithmetic-proof-assume core test t))
         (no (h1-arithmetic-proof-assume core test nil))
         (opened (h1-book-structure-container-case proof predicate yes))
         (rewrite (proof-proof-rewrite core assumption opened '(1)))
         (parts (h1-propositions-propositional-proof-conjunct lib rewrite))
         (empty-term (library-library-cite lib "TERM-NIL" nil nil))
         (empty-list (library-library-cite lib "TERM-LIST-NIL" nil nil))
         (proof (h1-book-substitution-list-selector-type
                 proof "TERM-LIST-CAR" *library-car* (car parts) empty-term no test predicate))
         (proof (h1-book-substitution-list-selector-type
                 proof "TERM-LIST-CDR" *library-cdr* (cadr parts) empty-list no test predicate))
         (lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (cons-step (proof-proof-fact core "consp-cons" nil))
         (equation (h1-book-structure-container-case proof term cons-step))
         (car-cons (library-library-axiom lib "CAR-CONS" (list *library-x* *library-y*)))
         (equation (h1-propositions-rewrite-value lib equation car-cons))
         (cdr-cons (library-library-axiom lib "CDR-CONS" (list *library-x* *library-y*)))
         (equation (h1-propositions-rewrite-value lib equation cdr-cons))
         (body (proof-rewritten-term equation))
         (premises (h1-tactics-prover-conjunction-assumption proof body))
         (step (h1-propositions-proof-transport core premises equation))
         (noted (h1-book-substitution-note proof "TERM-LIST-CONS" step)))
      (cdr noted))))

(defun h1-book-substitution-syntax-body (proof term cons-evidence not-quote parts)
  (let ((lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((equation (h1-book-structure-container-case
                    proof (list *h1-book-substitution-term* term) cons-evidence))
         (equation
          (if parts
              (proof-with-checked-results
                  ((head (library-library-axiom lib "CAR-CONS" parts))
                   (equation (h1-propositions-rewrite-value lib equation head))
                   (tail (library-library-axiom lib "CDR-CONS" parts)))
                (h1-propositions-rewrite-value lib equation tail))
            equation)))
      (h1-propositions-select-value lib equation not-quote))))

(defun h1-book-substitution-after-argument-test (proof value typed-arguments)
  (let ((lib (h1-tactics-prover-library proof))
        (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((test (proof-term-at value 1))
         (opened (proof-proof-unfold core test))
         (equation (h1-propositions-select-value lib opened typed-arguments))
         (not-nil (proof-proof-not-nil core)))
      (h1-propositions-library-transport-argument lib not-nil equation 1))))

(defun h1-book-substitution-unfold-return-last (terms proof step in-value)
  (if (endp terms)
      step
    (proof-with-checked-results
        ((step (if (proof-is-call (car terms) *termination-return-last*)
                   (let ((core (h1-tactics-prover-proof proof)))
                     (proof-with-checked-results ((opened (proof-proof-unfold core (car terms))))
                       (if in-value
                           (h1-propositions-rewrite-value (h1-tactics-prover-library proof)
                                                          step opened)
                         (proof-proof-rewrite-first core step opened))))
                 step)))
      (h1-book-substitution-unfold-return-last (cdr terms) proof step in-value))))

(defun h1-book-substitution-logical-header (proof equation)
  (proof-with-checked-results ((body (proof-rewritten-term equation)))
    (h1-book-substitution-unfold-return-last (h1-tactics-subterms body) proof equation t)))

(defun h1-book-substitution-replacement-arguments (proof)
  (let* ((core (h1-tactics-prover-proof proof))
         (head (list *library-car* *library-x*))
         (tail (list *library-cdr* *library-x*))
         (quoted (list *h1-book-substitution-eq* head *h1-book-substitution-quote-name*))
         (terms (list *h1-book-substitution-terms* tail)))
    (proof-with-checked-results
        ((cons-step (h1-arithmetic-proof-assume core (list *proof-consp* *library-x*) t))
         (not-quote (h1-arithmetic-proof-assume core quoted nil))
         (opened (h1-book-substitution-syntax-body proof *library-x* cons-step not-quote nil))
         (typed (h1-arithmetic-proof-assume core (list *h1-book-substitution-term* *library-x*) t))
         (old-typed (proof-proof-rewrite core typed opened '(1)))
         (old-body (proof-step-first old-typed))
         (yes (h1-arithmetic-proof-if-true core old-body))
         (rewritten (proof-proof-rewrite core old-typed yes '(1)))
         (tidied (proof-proof-tidy core rewritten))
         (not-denied (proof-proof-front core tidied (proof-neg (cadr old-body))))
         (not-terms (h1-arithmetic-proof-assume core terms nil))
         (cut (proof-proof-cut core not-terms not-denied))
         (old-arguments (proof-proof-front core cut terms))
         (noted (h1-book-substitution-note proof "TERM-ARGUMENTS" old-arguments))
         (proof (cdr noted))
         (lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (header (h1-propositions-proof-prove-if core old-typed not-denied))
         (literal (proof-step-first header))
         (header (h1-book-substitution-unfold-return-last (h1-tactics-subterms literal)
                                                          proof header nil))
         (assumed-cons (proof-proof-fact core "consp-cons"
                                        (list (list *library-x* head) (list *library-y* *library-y*))))
         (new-form (h1-book-substitution-syntax-body proof (list *proof-cons* head *library-y*)
                                                    assumed-cons not-quote (list head *library-y*)))
         (typed-arguments (h1-arithmetic-proof-assume
                           core (list *h1-book-substitution-terms* *library-y*) t))
         (new-body (proof-rewritten-term new-form))
         (known-no (h1-book-substitution-after-argument-test proof new-body typed-arguments))
         (selected (h1-propositions-select-value lib new-form known-no))
         (new-form (h1-book-substitution-logical-header proof selected))
         (length (h1-arithmetic-proof-assume core (proof-eq (list *library-len* *library-y*)
                                                           (list *library-len* tail)) t))
         (new-form (h1-propositions-rewrite-value lib new-form length))
         (step (h1-propositions-proof-transport core header new-form))
         (noted (h1-book-substitution-note proof "TERM-REPLACE-ARGUMENTS" step)))
      (cdr noted))))

(defun h1-book-substitution-nonquote-from-path (proof value tests)
  (let* ((lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (head (list *library-car* value))
         (direct (list *h1-book-substitution-eq* head *h1-book-substitution-quote-name*))
         (reverse (list *h1-book-substitution-eq* *h1-book-substitution-quote-name* head)))
    (cond
     ((member-equal (list direct nil) tests)
      (h1-arithmetic-proof-assume core direct nil))
     ((not (member-equal (list reverse nil) tests))
      '(:failure "unproved" ""))
     (t (proof-with-checked-results
            ((symmetry (library-library-axiom lib "H1-EQUALITY-SYMMETRIC-VALUE"
                                              (list head *h1-book-substitution-quote-name*)))
             (direct-eq (proof-proof-unfold core direct))
             (reverse-eq (proof-proof-unfold core reverse))
             (reverse-eq (h1-propositions-proof-symmetric core reverse-eq))
             (same (proof-proof-chain core direct-eq (list symmetry reverse-eq)))
             (known (h1-arithmetic-proof-assume core reverse nil)))
          (h1-propositions-library-transport-argument lib known same 1))))))

(defun h1-book-substitution-substitution-proof-object (self) (nth 1 self))
(defun h1-book-substitution-substitution-family (self) (nth 2 self))
(defun h1-book-substitution-substitution-projected (self) (nth 5 self))
(defun h1-book-substitution-substitution-hypothesis (self) (nth 7 self))
(defun h1-book-substitution-substitution-assumption (self) (nth 8 self))
(defun h1-book-substitution-substitution-term-call (self) (nth 9 self))
(defun h1-book-substitution-substitution-list-call (self) (nth 10 self))
(defun h1-book-substitution-substitution-term-claim (self) (nth 11 self))
(defun h1-book-substitution-substitution-list-claim (self) (nth 12 self))
(defun h1-book-substitution-substitution-consequent (self) (nth 14 self))
(defun h1-book-substitution-substitution-claim (self) (nth 15 self))

(defun h1-book-substitution-returned-value (expression projected)
  (if projected
      (list *h1-book-substitution-mv-nth* *proof-one* expression)
    expression))

(defun h1-book-substitution-substitution-init (proof family)
  (let* ((term (proof-sym family "ACL2"))
         (terms (proof-sym (concatenate 'string family "-LST") "ACL2"))
         (projected (equal family "SUBLIS-VAR1"))
         (parameters (if projected (list *library-y*) (list *library-y* *library-z*)))
         (hypothesis (cond (projected (list *h1-book-substitution-terms*
                                            (list *h1-book-substitution-strip-cdrs* *library-y*)))
                           ((equal family "SUBCOR-VAR") (list *h1-book-substitution-terms* *library-z*))
                           (t (list *h1-book-substitution-term* *library-y*)))))
    (proof-with-checked-results
        ((assumption (h1-arithmetic-proof-assume (h1-tactics-prover-proof proof) hypothesis t)))
      (let* ((term-call (cons term (append parameters (list *library-x*))))
             (list-call (cons terms (append parameters (list *library-x*))))
             (term-result (h1-book-substitution-returned-value term-call projected))
             (list-result (h1-book-substitution-returned-value list-call projected))
             (term-claim (list *library-implies* (list *h1-book-substitution-term* *library-x*)
                               (list *h1-book-substitution-term* term-result)))
             (list-claim (list *library-implies* (list *h1-book-substitution-terms* *library-x*)
                               (list *h1-book-substitution-terms* list-result)))
             (length (proof-eq (list *library-len* list-result) (list *library-len* *library-x*)))
             (consequent (proof-ite term-claim (proof-ite list-claim length *proof-false*)
                                    *proof-false*))
             (claim (list *library-implies* hypothesis consequent)))
        (list :h1-substitution proof family term terms projected parameters hypothesis assumption
              term-call list-call term-claim list-claim length consequent claim)))))

(defun h1-book-substitution-substitution-result (self expression)
  (h1-book-substitution-returned-value expression
                                      (h1-book-substitution-substitution-projected self)))

(defun h1-book-substitution-substitution-projection (self expression)
  (let ((proof (h1-book-substitution-substitution-proof-object self)))
    (if (h1-book-substitution-substitution-projected self)
        (h1-book-substitution-tuple-result proof expression)
      (h1-propositions-propositional-proof-reflexive
       (h1-tactics-prover-library proof) expression))))

(defun h1-book-substitution-substitution-subcase (self selector)
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (actual (list selector *library-x*))
         (builtin (if (equal selector *library-car*) 2 3)))
    (proof-with-checked-results
        ((decrease (library-library-builtin lib builtin *library-x*))
         (test (proof-step-first decrease))
         (claim (proof-subst (h1-book-substitution-substitution-claim self)
                             (list (cons *library-x* actual))))
         (hypothesis (h1-arithmetic-proof-assume core (proof-ite test claim *proof-true*) t))
         (selected (h1-propositions-proof-prove-if core hypothesis decrease))
         (smaller (h1-propositions-propositional-proof-modus-ponens
                   lib selected (h1-book-substitution-substitution-assumption self)))
         (first (h1-propositions-propositional-proof-conjunct lib smaller))
         (rest (h1-propositions-propositional-proof-conjunct lib (cadr first))))
      (cons (car first) rest))))

;; Simplification uses the prover's constant rules in arguments and branch tests.
(mutual-recursion
 (defun h1-book-substitution-simplify (n proof term definitions)
   (declare (xargs :measure (nfix n)))
   (let ((core (h1-tactics-prover-proof proof))
         (head (car term)))
     (cond
      ((zp n) '(:failure "fuel" "h1-book-substitution-simplify"))
      ((or (not (proof-compound term)) (equal head *proof-quote*)) nil)
      ((endp term) '(:failure "failure" ""))
      ((or (proof-compound head) (member-equal head definitions))
       (proof-with-checked-results
           ((opened (proof-simplify-expansion core term))
            (next (h1-book-substitution-simplify (1- n) proof (cadr opened) definitions)))
         (proof-proof-chain core (car opened) (list next))))
      ((equal head *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at term 1))
            (first (h1-book-substitution-simplify (1- n) proof test definitions))
            (redex (proof-simplify-if-redex term first))
            (branch (proof-simplify-if-select core redex nil))
            (selected (h1-arithmetic-simplify-chain core term first branch))
            (right (and selected (proof-rewritten-term selected))))
         (if (or (not selected) (equal right redex))
             selected
           (proof-with-checked-results
               ((next (h1-book-substitution-simplify (1- n) proof right definitions)))
             (proof-proof-chain core selected (list next))))))
      (t (proof-with-checked-results
             ((result (h1-book-substitution-simplify-arguments
                       (1- n) proof term (cdr term) 1 nil definitions))
              (current (if result (proof-rewritten-term result) term))
              (constant (h1-tactics-prover-constant proof current)))
           (cond ((not constant) result)
                 (result (proof-proof-chain core result (list constant)))
                 (t constant)))))))
 (defun h1-book-substitution-simplify-arguments (n proof term args index result definitions)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "h1-book-substitution-simplify-arguments"))
    ((endp args) result)
    (t (proof-with-checked-results
           ((equality (h1-book-substitution-simplify (1- n) proof (car args) definitions))
            (next (if equality
                      (let ((core (h1-tactics-prover-proof proof)))
                        (proof-with-checked-results
                            ((previous (or result (h1-arithmetic-proof-reflexive core term))))
                          (proof-proof-rewrite core previous equality (list 1 2 index))))
                    result)))
         (h1-book-substitution-simplify-arguments (1- n) proof term (cdr args) (1+ index)
                                                  next definitions))))))

(defun h1-book-substitution-atomic-term-decision (self value typed-input)
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (lib (h1-tactics-prover-library proof))
         (assumption (h1-book-substitution-substitution-assumption self))
         (family (h1-book-substitution-substitution-family self)))
    (cond
     ((equal value *library-x*) typed-input)
     ((and (equal family "SUBST-VAR") (equal value *library-y*)) assumption)
     ((and (equal family "SUBCOR-VAR")
           (equal value (list (proof-sym "SUBCOR-VAR1" "ACL2") *library-y* *library-z* *library-x*)))
      (proof-with-checked-results
          ((theorem (library-library-cite lib "PARALLEL-LOOKUP-TERM" nil nil))
           (literal (proof-step-first theorem))
           (premise (proof-term-at literal 1))
           (supplied (h1-propositions-propositional-proof-conjoin lib premise assumption typed-input)))
        (h1-propositions-propositional-proof-modus-ponens lib theorem supplied)))
     (t
      (proof-with-checked-results
          ((alternate (h1-book-substitution-simplify 1000000 proof value
                                                     (list *termination-return-last*))))
        (cond
         (alternate
          (proof-with-checked-results ((actual (proof-rewritten-term alternate)))
            (list :simplified actual alternate)))
         ((and (h1-book-substitution-substitution-projected self)
               (equal value (list *library-cdr*
                                  (list (proof-sym "ASSOC-EQUAL" "ACL2") *library-x* *library-y*))))
          (let ((formula (list *library-implies*
                               (h1-book-substitution-substitution-hypothesis self)
                               (list *h1-book-substitution-term* value))))
            (proof-with-checked-results
                ((prior (h1-tactics-prover-prior-fact proof formula))
                 (theorem (or prior (h1-book-structure-projected-association proof formula))))
              (h1-propositions-propositional-proof-modus-ponens lib theorem assumption))))
         (t '(:failure "unproved" ""))))))))

(defun h1-book-substitution-atomic-term-continue (n self typed-input decision)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "h1-book-substitution-atomic-term-continue"))
   ((eq (car decision) :simplified)
    (proof-with-checked-results
        ((typed (h1-book-substitution-atomic-term-continue
                 (1- n) self typed-input
                 (and (< 1 n)
                      (h1-book-substitution-atomic-term-decision
                       self (cadr decision) typed-input)))))
      (h1-propositions-library-transport-argument
       (h1-tactics-prover-library (h1-book-substitution-substitution-proof-object self))
       typed (caddr decision) 1)))
   (t decision)))

(defun h1-book-substitution-substitution-atomic-term (n self value typed-input)
  (h1-book-substitution-atomic-term-continue
   n self typed-input
   (and (not (zp n)) (h1-book-substitution-atomic-term-decision self value typed-input))))

(defun h1-book-substitution-constructor-types-at-return (leaf tests proof candidate folded typed-input)
  (declare (ignore tests))
  (let ((known (table-put (list (cons candidate folded)) *library-z* typed-input)))
    (proof-with-checked-results
        ((projection (h1-book-substitution-tuple-result proof leaf))
         (actual (proof-rewritten-term projection))
         (typed (h1-book-substitution-typed-value 1000000 proof actual known)))
      (h1-propositions-library-transport-argument (h1-tactics-prover-library proof)
                                                 typed projection 1))))

(defun h1-book-substitution-install-syntax-leaf (leaf tests proof)
  (declare (ignore tests))
  (h1-arithmetic-proof-assume (h1-tactics-prover-proof proof)
                              (list *h1-book-substitution-term* leaf) t))

(defun h1-book-substitution-term-proof-application (self actual tests typed-input cons-evidence tail)
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((not-quote (h1-book-substitution-nonquote-from-path proof *library-x* tests))
         (original (library-library-cite lib "TERM-ARGUMENTS" (list *library-x*)
                                         (list typed-input cons-evidence not-quote)))
         (tail-type (proof-term-at tail 1))
         (arguments (h1-propositions-propositional-proof-modus-ponens lib tail-type original))
         (actual-tail (proof-term-at actual 2))
         (tail-length (proof-term-at tail 2))
         (replaced (library-library-cite lib "TERM-REPLACE-ARGUMENTS"
                                         (list *library-x* actual-tail)
                                         (list typed-input cons-evidence not-quote
                                               arguments tail-length))))
      (library-library-cite lib "TYPED-CONS-TERM" (cdr actual) (list replaced)))))

(defun h1-book-substitution-substitution-term-proof-leaf
    (value tests self typed-input cons-evidence tail)
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (lib (h1-tactics-prover-library proof))
         (projected (h1-book-substitution-substitution-projected self)))
    (if (and projected (proof-is-call value *h1-book-substitution-cons-term2*))
        (library-library-cite lib "TYPED-CONS-TERM-MV" (cdr value) (list typed-input))
      (proof-with-checked-results
          ((projection (h1-book-substitution-substitution-projection self value))
           (actual (proof-rewritten-term projection))
           (typed
            (cond
             ((or (not tail) (equal actual *library-x*))
              (h1-book-substitution-substitution-atomic-term 1000000 self actual typed-input))
             ((proof-is-call actual *h1-book-substitution-cons-term*)
              (proof-with-checked-results ((head (proof-term-at actual 1)))
                (if (equal head (list *library-car* *library-x*))
                    (h1-book-substitution-term-proof-application self actual tests typed-input
                                                                 cons-evidence tail)
                  '(:failure "unproved" ""))))
             (t '(:failure "unproved" "")))))
        (if projected
            (h1-propositions-library-transport-argument lib typed projection 1)
          typed)))))

(defun h1-book-substitution-substitution-list-proof-leaf (value tests self typed-input head new-types)
  (declare (ignore tests))
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((projection (h1-book-substitution-substitution-projection self value))
         (actual (proof-rewritten-term projection))
         (typed
          (cond ((equal actual *library-x*) typed-input)
                ((equal actual *proof-false*)
                 (library-library-cite lib "TERM-LIST-NIL" nil nil))
                ((and head (proof-is-call actual *proof-cons*))
                 (library-library-cite lib "TERM-LIST-CONS" (cdr actual) new-types))
                (t '(:failure "unproved" "")))))
      (if (h1-book-substitution-substitution-projected self)
          (h1-propositions-library-transport-argument lib typed projection 1)
        typed))))

(defun h1-book-substitution-length-proof-cons (self actual before tail)
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((actual-cons (proof-proof-fact core "consp-cons"
                                        (seq-zip (list *library-x* *library-y*) (cdr actual))))
         (opened (h1-book-structure-container-case proof (list *library-len* actual) actual-cons))
         (cdr-cons (library-library-axiom lib "CDR-CONS" (cdr actual)))
         (opened (h1-propositions-rewrite-value lib opened cdr-cons))
         (tail-length (proof-term-at tail 2))
         (length (h1-propositions-rewrite-value lib opened tail-length))
         (symmetric (h1-propositions-proof-symmetric core before)))
      (proof-proof-chain core length (list symmetric)))))

(defun h1-book-substitution-substitution-length-proof-leaf (value tests self before tail)
  (declare (ignore tests))
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((projection (h1-book-substitution-substitution-projection self value))
         (actual (proof-rewritten-term projection))
         (length
          (cond
           ((equal actual *library-x*)
            (h1-propositions-propositional-proof-reflexive lib (list *library-len* *library-x*)))
           ((equal actual *proof-false*)
            (proof-with-checked-results
                ((closed (h1-book-substitution-simplify
                          1000000 proof (list *library-len* *proof-false*) (list *library-len*)))
                 (symmetric (h1-propositions-proof-symmetric core before)))
              (proof-proof-chain core closed (list symmetric))))
           ((and tail (proof-is-call actual *proof-cons*))
            (h1-book-substitution-length-proof-cons self actual before tail))
           (t '(:failure "unproved" "")))))
      (if (h1-book-substitution-substitution-projected self)
          (proof-with-checked-results
              ((symmetric (h1-propositions-proof-symmetric core projection))
               (rewritten (proof-proof-rewrite core length symmetric '(1 1 1))))
            (proof-proof-tidy core rewritten))
        length))))

(defun h1-book-substitution-by-value-leaf (value tests proof kind environment)
  (case kind
    (:constructor
     (h1-book-substitution-constructor-types-at-return
      value tests proof (car environment) (cadr environment) (caddr environment)))
    (:syntax (h1-book-substitution-install-syntax-leaf value tests proof))
    (:term
     (h1-book-substitution-substitution-term-proof-leaf
      value tests (car environment) (cadr environment) (caddr environment) (cadddr environment)))
    (:list
     (h1-book-substitution-substitution-list-proof-leaf
      value tests (car environment) (cadr environment) (caddr environment) (cadddr environment)))
    (:length
     (h1-book-substitution-substitution-length-proof-leaf
      value tests (car environment) (cadr environment) (caddr environment)))
    (otherwise
     (let ((entry (assoc-equal (list value tests) environment)))
       (if entry (cdr entry) '(:failure "failure" ""))))))

(defun h1-book-substitution-by-value (n proof value template kind environment tests)
  (declare (xargs :measure (nfix n)))
  (let ((core (h1-tactics-prover-proof proof)))
    (cond
     ((zp n) '(:failure "fuel" "h1-book-substitution-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((parts (proof-list-of-length (cdr value) 3))
           (yes (h1-book-substitution-by-value
                 (1- n) proof (cadr parts) template kind environment
                 (append tests (list (list (car parts) t)))))
           (no (h1-book-substitution-by-value
                (1- n) proof (caddr parts) template kind environment
                (append tests (list (list (car parts) nil)))))
           (if-true (h1-arithmetic-proof-if-true core value))
           (true-eq (h1-propositions-proof-symmetric core if-true))
           (yes (proof-proof-rewrite-result core yes true-eq template *proof-result*))
           (if-false (h1-arithmetic-proof-if-false core value))
           (false-eq (h1-propositions-proof-symmetric core if-false))
           (no (proof-proof-rewrite-result core no false-eq template *proof-result*)))
        (proof-proof-cases core (car parts) yes no)))
     ((and (proof-compound value) (null value))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equation (proof-proof-beta core value))
           (body (proof-rewritten-term equation))
           (opened (h1-book-substitution-by-value (1- n) proof body template kind environment tests))
           (symmetric (h1-propositions-proof-symmetric core equation)))
        (proof-proof-rewrite-result core opened symmetric template *proof-result*)))
     (t
      (proof-with-checked-results
          ((step (h1-book-substitution-by-value-leaf value tests proof kind environment))
           (literal (proof-step-first step))
           (claim (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal claim) step '(:failure "failure" "")))))))

(defun h1-book-substitution-substitution-result-cases-with-leaf
    (self application known template kind environment)
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (core (h1-tactics-prover-proof proof)))
    (proof-with-checked-results
        ((equation (h1-book-structure-container-case proof application known))
         (body (proof-rewritten-term equation))
         (typed (h1-book-substitution-by-value 1000000 proof body template kind environment nil))
         (symmetric (h1-propositions-proof-symmetric core equation)))
      (proof-proof-rewrite-result core typed symmetric template *proof-result*))))

(defun h1-book-substitution-substitution-term-proof (self cons-evidence tail)
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (template (list *h1-book-substitution-term*
                         (h1-book-substitution-substitution-result self *proof-result*))))
    (proof-with-checked-results
        ((typed-input (h1-arithmetic-proof-assume core (list *h1-book-substitution-term* *library-x*) t))
         (step (h1-book-substitution-substitution-result-cases-with-leaf
                self (h1-book-substitution-substitution-term-call self) cons-evidence template :term
                (list self typed-input cons-evidence tail))))
      (h1-propositions-propositional-proof-implies-from
       lib (h1-book-substitution-substitution-term-claim self) step))))

(defun h1-book-substitution-substitution-list-proof (self cons-evidence head tail)
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (template (list *h1-book-substitution-terms*
                         (h1-book-substitution-substitution-result self *proof-result*))))
    (proof-with-checked-results
        ((typed-input (h1-arithmetic-proof-assume core (list *h1-book-substitution-terms* *library-x*) t))
         (new-types
          (and head
               (proof-with-checked-results
                   ((original-head (library-library-cite lib "TERM-LIST-CAR" (list *library-x*)
                                                          (list typed-input)))
                    (original-tail (library-library-cite lib "TERM-LIST-CDR" (list *library-x*)
                                                          (list typed-input)))
                    (head-step (proof-term-at head 0))
                    (new-head (h1-propositions-propositional-proof-modus-ponens
                               lib head-step original-head))
                    (tail-step (proof-term-at tail 1))
                    (new-tail (h1-propositions-propositional-proof-modus-ponens
                               lib tail-step original-tail)))
                 (list new-head new-tail))))
         (step (h1-book-substitution-substitution-result-cases-with-leaf
                self (h1-book-substitution-substitution-list-call self) cons-evidence template :list
                (list self typed-input head new-types))))
      (h1-propositions-propositional-proof-implies-from
       lib (h1-book-substitution-substitution-list-claim self) step))))

(defun h1-book-substitution-substitution-length-proof (self cons-evidence tail)
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (original (list *library-len* *library-x*))
         (template (proof-eq (list *library-len*
                                   (h1-book-substitution-substitution-result self *proof-result*))
                             original)))
    (proof-with-checked-results
        ((before (h1-book-structure-container-case proof original cons-evidence)))
      (h1-book-substitution-substitution-result-cases-with-leaf
       self (h1-book-substitution-substitution-list-call self) cons-evidence template :length
       (list self before tail)))))

(defun h1-book-substitution-substitution-prove-branch (known hd tl self)
  (let* ((lib (h1-tactics-prover-library (h1-book-substitution-substitution-proof-object self)))
         (consequent (h1-book-substitution-substitution-consequent self)))
    (proof-with-checked-results
        ((a (h1-book-substitution-substitution-term-proof self known tl))
         (b (h1-book-substitution-substitution-list-proof self known hd tl))
         (c (h1-book-substitution-substitution-length-proof self known tl))
         (both (h1-propositions-propositional-proof-conjoin lib (caddr consequent) b c))
         (step (h1-propositions-propositional-proof-conjoin lib consequent a both)))
      (h1-propositions-propositional-proof-implies-from
       lib (h1-book-substitution-substitution-claim self) step))))

(defun h1-book-substitution-substitution-prove (self)
  (let* ((proof (h1-book-substitution-substitution-proof-object self))
         (lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (test (list *proof-consp* *library-x*))
         (measure (list *library-count* *library-x*))
         (cases (list (list (list *library-x* (list *library-car* *library-x*)))
                      (list (list *library-x* (list *library-cdr* *library-x*))))))
    (proof-with-checked-results
        ((cons-step (h1-arithmetic-proof-assume core test t))
         (atom-step (h1-arithmetic-proof-assume core test nil))
         (head (h1-book-substitution-substitution-subcase self *library-car*))
         (tail (h1-book-substitution-substitution-subcase self *library-cdr*))
         (yes (h1-book-substitution-substitution-prove-branch cons-step head tail self))
         (no (h1-book-substitution-substitution-prove-branch atom-step nil nil self))
         (step (proof-proof-cases core test yes no))
         (ordinal (descent-measure-ordinal lib measure)))
      (proof-proof-induct core ordinal step (h1-book-substitution-substitution-claim self)
                          measure cases))))

(defun h1-book-substitution-constructor-mv-type (proof candidate folded)
  (let* ((lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (call (list *h1-book-substitution-cons-term2* *library-x* *library-y* *library-z*))
         (template (list *h1-book-substitution-term*
                         (list *h1-book-substitution-mv-nth* *proof-one* *proof-result*))))
    (proof-with-checked-results
        ((opened (proof-proof-unfold core call))
         (equation (h1-propositions-beta-value lib opened))
         (returned (proof-rewritten-term equation))
         (test (and (proof-is-call returned *proof-if*) (proof-term-at returned 1))))
      (if (not (and (proof-is-call returned *proof-if*) (equal test candidate)))
          '(:failure "unproved" "")
        (proof-with-checked-results
            ((typed-input (h1-arithmetic-proof-assume core (list *h1-book-substitution-term*
                                                                 *library-z*) t))
             (result (h1-book-substitution-by-value
                      1000000 proof returned template :constructor (list candidate folded typed-input) nil))
             (symmetric (h1-propositions-proof-symmetric core equation))
             (step (proof-proof-rewrite-result core result symmetric template *proof-result*))
             (noted (h1-book-substitution-note proof "TYPED-CONS-TERM-MV" step)))
          (cdr noted))))))

(defun h1-book-substitution-constructor-types (proof)
  (let* ((lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (old (list *proof-cons* *library-x* *library-y*)))
    (proof-with-checked-results
        ((empty (library-library-cite lib "TERM-NIL" nil nil))
         (typed-old (h1-arithmetic-proof-assume core (list *h1-book-substitution-term* old) t))
         (equation (proof-proof-unfold core (list *h1-book-substitution-cons-term1*
                                                 *library-x* *library-y*)))
         (opened (h1-propositions-beta-value lib equation))
         (value (proof-rewritten-term opened))
         (candidate (proof-term-at value 1)))
      (if (not (and (proof-is-call value *proof-if*) (equal (cddr value) (list candidate old))))
          '(:failure "unproved" "")
        (proof-with-checked-results
            ((tested (h1-book-substitution-typed-value
                      1000000 proof candidate (list (cons *proof-false* empty))))
             (folded (h1-book-substitution-note proof "FOLDED-TERM" tested))
             (proof (cdr folded))
             (lib (h1-tactics-prover-library proof))
             (core (h1-tactics-prover-proof proof))
             (optimized (h1-book-substitution-term-choice proof value (car folded) typed-old))
             (optimized (h1-propositions-library-transport-argument lib optimized opened 1))
             (choice (proof-proof-unfold core (list *h1-book-substitution-cons-term*
                                                   *library-x* *library-y*)))
             (choice-value (proof-rewritten-term choice))
             (cons-term (h1-book-substitution-term-choice proof choice-value optimized typed-old))
             (step (h1-propositions-library-transport-argument lib cons-term choice 1))
             (noted (h1-book-substitution-note proof "TYPED-CONS-TERM" step)))
          (h1-book-substitution-constructor-mv-type (cdr noted) candidate (car folded)))))))

(defun h1-book-substitution-install-syntax (proof)
  (let* ((term-nil (list *h1-book-substitution-term* *proof-false*))
         (list-nil (list *h1-book-substitution-terms* *proof-false*))
         (value (proof-ite *library-x* *library-y* *library-z*))
         (template (list *h1-book-substitution-term* *proof-result*))
         (quoted (list *h1-book-substitution-term* (list *h1-book-substitution-kwote* *library-x*)))
         (tuple (list *proof-cons* *library-x* (list *proof-cons* *library-y* *proof-false*)))
         (tuple-equation (proof-eq (list *h1-book-substitution-mv-nth* *proof-one* tuple) *library-y*)))
    (proof-with-checked-results
        ((empty-term (h1-tactics-prover-solve proof term-nil (list *h1-book-substitution-term*) 160))
         (proof (h1-book-substitution-add-lemma proof "TERM-NIL" term-nil empty-term nil))
         (empty-list (h1-tactics-prover-solve proof list-nil (list *h1-book-substitution-terms*) 160))
         (proof (h1-book-substitution-add-lemma proof "TERM-LIST-NIL" list-nil empty-list nil))
         (claim (h1-book-substitution-by-value 1000000 proof value template :syntax nil nil))
         (literal (proof-step-first claim))
         (proof (h1-book-substitution-add-lemma
                 proof "TERM-IF" literal claim
                 (list (proof-neg (list *h1-book-substitution-term* *library-y*))
                       (proof-neg (list *h1-book-substitution-term* *library-z*)))))
         (typed (h1-tactics-prover-solve proof quoted (list *h1-book-substitution-term*
                                                            *h1-book-substitution-kwote*) 160))
         (proof (h1-book-substitution-add-lemma proof "QUOTED-TERM" quoted typed nil))
         (projected (h1-tactics-prover-solve
                     proof tuple-equation
                     (list (cons *h1-book-substitution-mv-nth* 2)
                           (cons (proof-sym "ZP" "ACL2") 2))
                     160))
         (proof (h1-book-substitution-add-lemma proof "TUPLE-RESULT" tuple-equation projected nil))
         (proof (h1-book-substitution-constructor-types proof))
         (proof (h1-book-substitution-list-types proof)))
      (h1-book-substitution-replacement-arguments proof))))

(defun h1-book-substitution-install-parallel-lookup (proof)
  (let* ((lib (h1-tactics-prover-library proof))
         (core (h1-tactics-prover-proof proof))
         (lookup (proof-sym "SUBCOR-VAR1" "ACL2"))
         (call (list lookup *library-y* *library-z* *library-x*))
         (parameters (proof-ite (list *h1-book-substitution-terms* *library-z*)
                                (list *h1-book-substitution-term* *library-x*) *proof-false*))
         (formula (list *library-implies* parameters (list *h1-book-substitution-term* call)))
         (test (list *proof-consp* *library-y*))
         (tail-y (list *library-cdr* *library-y*))
         (tail-z (list *library-cdr* *library-z*))
         (pairs (list (list *library-y* tail-y) (list *library-z* tail-z)))
         (measure (list *library-count* *library-y*)))
    (proof-with-checked-results
        ((assumption (h1-arithmetic-proof-assume core parameters t))
         (types (h1-propositions-propositional-proof-conjunct lib assumption))
         (yes (h1-arithmetic-proof-assume core test t))
         (no (h1-arithmetic-proof-assume core test nil))
         (atom (h1-book-structure-container-case proof call no))
         (miss-all (h1-propositions-library-transport-argument lib (cadr types) atom 1))
         (opened (h1-book-structure-container-case proof call yes))
         (body (proof-rewritten-term opened))
         (compare (proof-term-at body 1))
         (found (library-library-cite lib "TERM-LIST-CAR" (list *library-z*) (list (car types))))
         (matches (h1-arithmetic-proof-assume core compare t))
         (selected (h1-propositions-select-value lib opened matches))
         (at-match (h1-propositions-library-transport-argument lib found selected 1))
         (decrease (library-library-builtin lib 3 *library-y*))
         (smaller (proof-subst formula (list (cons *library-y* tail-y) (cons *library-z* tail-z))))
         (ordinal-less (proof-step-first decrease))
         (hypothesis (h1-arithmetic-proof-assume core (proof-ite ordinal-less smaller *proof-true*) t))
         (recursive (h1-propositions-proof-prove-if core hypothesis decrease))
         (tail (library-library-cite lib "TERM-LIST-CDR" (list *library-z*) (list (car types))))
         (supplied (h1-propositions-propositional-proof-conjoin lib (cadr smaller) tail (cadr types)))
         (recursive (h1-propositions-propositional-proof-modus-ponens lib recursive supplied))
         (unmatched (h1-arithmetic-proof-assume core compare nil))
         (missed (h1-propositions-select-value lib opened unmatched))
         (at-miss (h1-propositions-library-transport-argument lib recursive missed 1))
         (branch (proof-proof-cases core compare at-match at-miss))
         (on-cons (h1-propositions-propositional-proof-implies-from lib formula branch))
         (on-atom (h1-propositions-propositional-proof-implies-from lib formula miss-all))
         (step (proof-proof-cases core test on-cons on-atom))
         (ordinal (descent-measure-ordinal lib measure))
         (induction (proof-proof-induct core ordinal step formula measure (list pairs)))
         (noted (h1-book-substitution-note proof "PARALLEL-LOOKUP-TERM" induction)))
      (cdr noted))))

(defun h1-book-substitution-family-matches (name family)
  (or (equal name (proof-sym family "ACL2"))
      (equal name (proof-sym (concatenate 'string family "-LST") "ACL2"))))

(defun h1-book-substitution-application-family (name)
  (cond ((h1-book-substitution-family-matches name "SUBCOR-VAR") "SUBCOR-VAR")
        ((h1-book-substitution-family-matches name "SUBST-VAR") "SUBST-VAR")
        ((h1-book-substitution-family-matches name "SUBLIS-VAR1") "SUBLIS-VAR1")
        (t nil)))

(defun h1-book-substitution-proof-plan (formula)
  (if (not (proof-is-call formula *library-implies*))
      '(:failure "unproved" "")
    (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
      (let* ((conclusion (caddr parts))
             (is-term (proof-is-call conclusion *h1-book-substitution-term*)))
        (if (not (or is-term (proof-is-call conclusion *h1-book-substitution-terms*)))
            '(:failure "unproved" "")
          (proof-with-checked-results
              ((application (proof-term-at conclusion 1))
               (is-projection (and (proof-is-call application *h1-book-substitution-mv-nth*)
                                   (proof-term-at application 1)))
               (application
                (if (equal is-projection *proof-one*) (proof-term-at application 2) application)))
            (let* ((head (h1-tactics-call-head application))
                   (family (h1-book-substitution-application-family head)))
              (cond ((not family) '(:failure "unproved" ""))
                    ((or (not (equal (equal is-projection *proof-one*)
                                     (equal family "SUBLIS-VAR1")))
                         (not (equal is-term (equal head (proof-sym family "ACL2")))))
                     '(:failure "unproved" ""))
                    (t (list family (cadr parts) is-term application))))))))))

(defun h1-book-substitution-install-family (proof family lemma)
  (let* ((core (h1-tactics-prover-proof proof))
         (name (proof-sym (concatenate 'string "SELF-" lemma) "ACL2")))
    (if (assoc-equal name (proof-proof-facts core))
        proof
      (proof-with-checked-results
          ((substitution (h1-book-substitution-substitution-init proof family))
           (step (h1-book-substitution-substitution-prove substitution))
           (noted (h1-book-substitution-note proof lemma step)))
        (cdr noted)))))

(defun h1-book-substitution-apply-family (proof formula lemma premise is-term application)
  (let* ((lib (h1-tactics-prover-library proof))
         (target (car (last application)))
         (params (butlast (cdr application) 1)))
    (proof-with-checked-results
        ((theorem (library-library-cite lib lemma (cons target params) nil))
         (search (h1-tactics-search-init proof nil nil nil nil 160 nil))
         (context (h1-tactics-context-init search (list (list premise t))))
         (literal (proof-step-first theorem))
         (required (proof-term-at literal 1))
         (assumption (h1-tactics-context-find context required)))
      (if (not (car assumption))
          '(:failure "unproved" "")
        (proof-with-checked-results
            ((statement (h1-propositions-propositional-proof-modus-ponens
                         lib theorem (car assumption)))
             (components (h1-propositions-propositional-proof-conjunct lib statement))
             (lemma (if is-term
                        (car components)
                      (proof-with-checked-results
                          ((rest (h1-propositions-propositional-proof-conjunct lib (cadr components))))
                        (car rest))))
             (literal (proof-step-first lemma))
             (required (proof-term-at literal 1))
             (input-type (h1-tactics-context-find (cdr assumption) required)))
          (if (not (car input-type))
              '(:failure "unproved" "")
            (proof-with-checked-results
                ((step (h1-propositions-propositional-proof-modus-ponens lib lemma (car input-type))))
              (h1-propositions-propositional-proof-implies-from lib formula step))))))))

(defun h1-book-substitution-substitution-proof-with-proof (proof formula)
  (let ((plan (h1-book-substitution-proof-plan formula)))
    (if (failure-p plan)
        (cons plan proof)
      (let* ((family (car plan))
             (lemma (concatenate 'string "SUBSTITUTION-" family))
             (updated (h1-book-substitution-install-family proof family lemma)))
        (if (failure-p updated)
            (cons updated proof)
          (cons (h1-book-substitution-apply-family
                 updated formula lemma (cadr plan) (caddr plan) (cadddr plan))
                updated))))))

