(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-pseudo-terms-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *b2-pseudo-terms-subst* (proof-sym "PSEUDO-TERM-SUBSTP" "ACL2"))
(defconst *b2-pseudo-terms-vals* (proof-sym "PSEUDO-TERM-VAL-ALISTP" "ACL2"))
(defconst *b2-pseudo-terms-list-cdr* (proof-sym "PSEUDO-TERMP-LIST-CDR" "ACL2"))
(defconst *b2-pseudo-terms-term-car* (proof-sym "PSEUDO-TERMP-CAR" "ACL2"))

(defconst *b2-pseudo-terms-pseudo-theorems*
  (seq-sorted
   (list (proof-sym "PSEUDO-TERM-LISTP-CDR" "ACL2")
         (proof-sym "PSEUDO-TERMP-OPENER" "ACL2")
         (proof-sym "PSEUDO-TERM-LISTP-OF-ATOM" "ACL2")
         (proof-sym "PSEUDO-TERM-LISTP-OF-CONS" "ACL2")
         *b2-pseudo-terms-list-cdr*
         *b2-pseudo-terms-term-car*
         (proof-sym "PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP" "ACL2")
         (proof-sym "PSEUDO-TERM-LISTP-APPEND" "ACL2")
         (proof-sym "PSEUDO-TERMP-OF-LOOKUP-IN-SUBST" "ACL2")
         (proof-sym "PSEUDO-TERM-SUBSTP-OF-ACONS" "ACL2")
         (proof-sym "PSEUDO-TERM-SUBSTP-OF-ATOM" "ACL2")
         (proof-sym "PSEUDO-TERM-SUBSTP-OF-PAIRLIS" "ACL2")
         (proof-sym "PSEUDO-TERM-SUBSTP-OF-APPEND" "ACL2")
         (proof-sym "PSEUDO-TERMP-OF-LOOKUP-IN-PSEUDO-TERM-VAL-ALISTP" "ACL2")
         (proof-sym "PSEUDO-TERM-VAL-ALISTP-OF-ACONS" "ACL2")
         (proof-sym "PSEUDO-TERM-VAL-ALISTP-OF-ATOM" "ACL2")
         (proof-sym "PSEUDO-TERM-VAL-ALISTP-OF-PAIRLIS" "ACL2")
         (proof-sym "PSEUDO-TERM-VAL-ALISTP-OF-APPEND" "ACL2"))))

(defun b2-pseudo-terms-first (step)
  (if (null step)
      '(:failure "failure" "")
    (proof-step-first step)))

(defun b2-pseudo-terms-result (step)
  (proof-with-checked-results ((literal (b2-pseudo-terms-first step)))
    (proof-term-at literal 2)))

(defun b2-pseudo-terms-lookup (dictionary key)
  (let ((entry (assoc-equal key dictionary)))
    (if entry
        (cdr entry)
      '(:failure "tactic-rejected" ""))))

(defun b2-pseudo-terms-definition-equation (lib formula)
  (if (proof-is-call formula *library-implies*)
      (proof-with-checked-results
          ((parts (proof-list-of-length formula 3))
           (call (proof-term-at (caddr parts) 1))
           (request (b2-tactics-tactics-implication lib (cadr parts) (caddr parts) nil))
           (pending (car request))
           (step (b2-tactics-tactics-solve
                  (caddr pending) (caddr parts) (list (cadddr pending)) (list call) nil 0 nil))
           (answer (b2-tactics-tactics-implication
                    lib (cadr parts) (caddr parts) (cons step (caddr pending)))))
        (car answer))
    (proof-with-checked-results ((call (proof-term-at formula 1)))
      (b2-tactics-tactics-solve lib formula nil (list call) nil 0 t))))

(defun b2-pseudo-terms-list-boolean-bool-output (value lib)
  (proof-with-checked-results
      ((right (b2-pseudo-terms-result value))
       (step (b2-tactics-tactics-solve
              lib (list *b2-pseudo-terms-booleanp* right)
              nil (list *b2-pseudo-terms-booleanp*) nil 0 nil)))
    (library-library-transport-argument lib step value 1)))

(defun b2-pseudo-terms-list-boolean-bool-value (term lib)
  (if (proof-is-call term *proof-quote*)
      (b2-tactics-tactics-solve lib (list *b2-pseudo-terms-booleanp* term)
                               nil (list *b2-pseudo-terms-booleanp*) nil 0 nil)
    (proof-with-checked-results
        ((yes (b2-tactics-tactics-truth-value lib term t nil))
         (no (b2-tactics-tactics-truth-value lib term nil nil))
         (positive (b2-pseudo-terms-list-boolean-bool-output yes lib))
         (negative (b2-pseudo-terms-list-boolean-bool-output no lib)))
      (proof-proof-cases (library-library-proof lib) term positive negative))))

(defun b2-pseudo-terms-list-boolean-base (atom lib call)
  (proof-with-checked-results
      ((equation (b2-tactics-tactics-normalize lib call (list atom) (list call) nil 1500 nil))
       (value (b2-pseudo-terms-result equation))
       (typed (b2-pseudo-terms-list-boolean-bool-value value lib)))
    (library-library-transport-argument lib typed equation 1)))

(defun b2-pseudo-terms-list-boolean-advance-leaf (value lib hypothesis)
  (proof-with-checked-results
      ((literal (b2-pseudo-terms-first hypothesis))
       (argument (proof-term-at literal 1)))
    (if (equal value argument)
        hypothesis
      (b2-pseudo-terms-list-boolean-bool-value value lib))))

(defund b2-pseudo-terms-list-boolean-advance-node (proof value)
  (cond
   ((proof-is-call value *proof-if*)
    (proof-with-checked-results ((branches (proof-list-of-length (cdr value) 3)))
      (cons :if branches)))
   ((and (proof-compound value) (not (consp value)))
    '(:failure "tactic-rejected" ""))
   ((and (proof-compound value) (proof-compound (car value)))
    (proof-with-checked-results
        ((equality (proof-proof-beta proof value))
         (opened (b2-pseudo-terms-result equality)))
      (list :lambda equality opened)))
   (t nil)))

(defun b2-pseudo-terms-list-boolean-advance-by-value (n lib value template hypothesis)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "b2-pseudo-terms-list-boolean-advance-by-value")
    (let* ((proof (library-library-proof lib))
           (node (b2-pseudo-terms-list-boolean-advance-node proof value)))
      (cond
       ((eq (car node) :if)
        (proof-with-checked-results
            ((yes (b2-pseudo-terms-list-boolean-advance-by-value
                   (1- n) lib (caddr node) template hypothesis))
             (no (b2-pseudo-terms-list-boolean-advance-by-value
                  (1- n) lib (cadddr node) template hypothesis))
             (if-true (proof-proof-if-true proof value))
             (syes (proof-proof-symmetric proof if-true))
             (yes-proof (proof-proof-rewrite-result proof yes syes template *proof-result*))
             (if-false (proof-proof-if-false proof value))
             (sno (proof-proof-symmetric proof if-false))
             (no-proof (proof-proof-rewrite-result proof no sno template *proof-result*)))
          (proof-proof-cases proof (cadr node) yes-proof no-proof)))
       ((eq (car node) :lambda)
        (proof-with-checked-results
            ((step (b2-pseudo-terms-list-boolean-advance-by-value
                    (1- n) lib (caddr node) template hypothesis))
             (reversed (proof-proof-symmetric proof (cadr node))))
          (proof-proof-rewrite-result proof step reversed template *proof-result*)))
       ((failure-p node) node)
       (t
        (proof-with-checked-results
            ((step (b2-pseudo-terms-list-boolean-advance-leaf value lib hypothesis))
             (literal (b2-pseudo-terms-first step))
             (expected (proof-subst template (list (cons *proof-result* value)))))
          (if (equal literal expected)
              step
            '(:failure "tactic-rejected" ""))))))))

(defun b2-pseudo-terms-list-boolean-advance (cons-step hypothesis lib call template)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equation (b2-tactics-tactics-normalize lib call (list cons-step) (list call) nil 1500 nil))
         (value (b2-pseudo-terms-result equation))
         (step (b2-pseudo-terms-list-boolean-advance-by-value
                1000000 lib value template hypothesis))
         (reversed (proof-proof-symmetric proof equation)))
      (proof-proof-rewrite-result proof step reversed template *proof-result*))))

(defun b2-pseudo-terms-list-boolean-proof (lib)
  (let* ((call (list *b2-list-properties-pseudo-list* *library-x*))
         (formula (list *b2-pseudo-terms-booleanp* call))
         (template (list *b2-pseudo-terms-booleanp* *proof-result*)))
    (proof-with-checked-results
        ((request (b2-tactics-tactics-on-list lib formula *library-x* nil nil nil))
         (pending (car request))
         (advance (b2-pseudo-terms-list-boolean-advance
                   (cadddr pending) (nth 4 pending) (caddr pending) call template))
         (advance-reply (cons advance (caddr pending)))
         (request-base (b2-tactics-tactics-on-list
                        lib formula *library-x* nil advance-reply nil))
         (pending-base (car request-base))
         (base (b2-pseudo-terms-list-boolean-base
                (cadddr pending-base) (caddr pending-base) call))
         (base-reply (cons base (caddr pending-base)))
         (answer (b2-tactics-tactics-on-list lib formula *library-x* base-reply advance-reply nil))
         (step (car answer)))
      (b2-tactics-tactics-add-lemma (cdr answer) "PSEUDO-TERM-LIST-BOOLEAN" step :none))))

(defun b2-pseudo-terms-list-boolean (lib argument)
  (let* ((label (proof-sym "B2-PSEUDO-TERM-LIST-BOOLEAN" "ACL2"))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((lib (if (assoc-equal label (proof-proof-facts proof))
                  lib
                (proof-with-checked-results
                    ((added (b2-pseudo-terms-list-boolean-proof lib)))
                  (cdr added))))
         (step (proof-proof-fact (library-library-proof lib) label
                                (list (list *library-x* argument)))))
      (cons step lib))))

(defun b2-pseudo-terms-pterm-opener-consequent (given lib goal term args)
  (proof-with-checked-results
      ((known (b2-tactics-tactics-evidence lib (list given)))
       (evidence (table-values known))
       (argument (proof-term-at args 1))
       (truth-result (b2-pseudo-terms-list-boolean lib argument)))
    (let* ((lib (cdr truth-result))
           (truth (car truth-result))
           (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((yes (proof-proof-assume proof args t))
           (no (proof-proof-assume proof args nil))
           (positive (b2-tactics-tactics-boolean-true lib truth yes))
           (a (b2-tactics-tactics-solve
               lib goal (append evidence (list yes)) (list term) (list positive) 0 nil))
           (negative (b2-tactics-tactics-close-false lib args no))
           (b (b2-tactics-tactics-solve
               lib goal (append evidence (list no)) (list term) (list negative) 0 nil))
           (step (proof-proof-cases proof args a b)))
        (cons step lib)))))

(defun b2-pseudo-terms-pterm-opener (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (goal (caddr parts))
       (terms (proof-list-of-length goal 3))
       (request (b2-tactics-tactics-implication lib (cadr parts) goal nil))
       (pending (car request))
       (reply (b2-pseudo-terms-pterm-opener-consequent
               (cadddr pending) (caddr pending) goal (cadr terms) (caddr terms)))
       (answer (b2-tactics-tactics-implication lib (cadr parts) goal reply))
       (step (car answer)))
    (cons step (cdr answer))))

(defun b2-pseudo-terms-term-tail-consequent (given lib goal x test cons-step atom)
  (proof-with-checked-results
      ((facts (b2-tactics-tactics-evidence lib (list given)))
       (same (proof-neg (proof-eq (list *library-car* x) (proof-quote *proof-quote*))))
       (typed (b2-pseudo-terms-lookup facts (list *b2-association-pseudo-term* x)))
       (nonquote (b2-pseudo-terms-lookup facts same))
       (good (b2-substitution-original-tail lib x typed cons-step nonquote))
       (empty (b2-tactics-tactics-solve lib goal (list atom) (list goal) nil 0 nil)))
    (proof-proof-cases (library-library-proof lib) test good empty)))

(defun b2-pseudo-terms-term-tail (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (goal (caddr parts))
       (argument (proof-term-at goal 1))
       (x (proof-term-at argument 1)))
    (let ((test (list *proof-consp* x))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((cons-step (proof-proof-assume proof test t))
           (atom (proof-proof-assume proof test nil))
           (request (b2-tactics-tactics-implication lib (cadr parts) goal nil))
           (pending (car request))
           (step (b2-pseudo-terms-term-tail-consequent
                  (cadddr pending) (caddr pending) goal x test cons-step atom))
           (answer (b2-tactics-tactics-implication
                    lib (cadr parts) goal (cons step (caddr pending)))))
        (car answer)))))

(defun b2-pseudo-terms-list-selector-consequent (given lib condition goal test cons-step atom)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equation (b2-tactics-tactics-normalize
                    lib condition (list cons-step) (list condition) nil 1500 nil))
         (literal (b2-pseudo-terms-first equation))
         (rewritten (proof-proof-rewrite proof given equation '(1)))
         (tidied (proof-proof-tidy proof rewritten))
         (conjuncts (proof-proof-conjunct proof tidied))
         (head (b2-pseudo-terms-first (car conjuncts)))
         (tail (b2-pseudo-terms-first (cadr conjuncts)))
         (parts (table-put (list (cons head (car conjuncts))) tail (cadr conjuncts)))
         (empty (b2-tactics-tactics-solve lib goal (list atom) (list goal) nil 0 nil))
         (step (b2-pseudo-terms-lookup parts goal)))
      (proof-proof-cases proof test step empty))))

(defun b2-pseudo-terms-list-selector (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (condition (cadr parts))
       (goal (caddr parts))
       (x (proof-term-at condition 1)))
    (let ((test (list *proof-consp* x))
          (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((cons-step (proof-proof-assume proof test t))
           (atom (proof-proof-assume proof test nil))
           (request (b2-tactics-tactics-implication lib condition goal nil))
           (pending (car request))
           (step (b2-pseudo-terms-list-selector-consequent
                  (cadddr pending) (caddr pending) condition goal test cons-step atom))
           (answer (b2-tactics-tactics-implication lib condition goal (cons step (caddr pending)))))
        (car answer)))))

(defun b2-pseudo-terms-cadr-lookup-consequent (given lib goal)
  (proof-with-checked-results
      ((argument (proof-term-at goal 1))
       (tail (proof-term-at argument 1))
       (step (b2-tactics-tactics-use-fact lib *b2-pseudo-terms-list-cdr*
                                         (list *b2-list-properties-pseudo-list* tail)
                                         (list given) nil nil 0 nil)))
    (b2-tactics-tactics-use-fact lib *b2-pseudo-terms-term-car* goal (list step) nil nil 0 nil)))

(defun b2-pseudo-terms-cadr-lookup (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (condition (cadr parts))
       (goal (caddr parts))
       (request (b2-tactics-tactics-implication lib condition goal nil))
       (pending (car request))
       (step (b2-pseudo-terms-cadr-lookup-consequent (cadddr pending) (caddr pending) goal))
       (answer (b2-tactics-tactics-implication lib condition goal (cons step (caddr pending)))))
    (car answer)))

(defun b2-pseudo-terms-alist-lookup (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (source (cadr parts))
       (argument (proof-term-at (caddr parts) 1))
       (original (proof-term-at argument 1))
       (equation (b2-tactics-tactics-normalize lib original nil nil nil 1500 nil))
       (lookup (b2-pseudo-terms-result equation)))
    (let* ((proof (library-library-proof lib))
           (plain (list *library-implies* source
                        (list *b2-association-pseudo-term* (list *library-cdr* lookup)))))
      (proof-with-checked-results
          ((step (b2-association-lookup-property
                  lib plain lookup source nil (list *b2-association-pseudo-term*) nil))
           (reversed (proof-proof-symmetric proof equation)))
        (proof-proof-rewrite-first proof step reversed)))))

(defun b2-pseudo-terms-typed-options-entry-type (lib records typed-entries)
  (let* ((proof (library-library-proof lib))
         (record (list *library-car* records))
         (test (list *proof-consp* record)))
    (proof-with-checked-results
        ((entries (proof-proof-conjunct proof typed-entries))
         (valid (car entries))
         (yes (proof-proof-assume proof test t))
         (no (proof-proof-assume proof test nil))
         (valid-first (b2-pseudo-terms-first valid))
         (opened (b2-tactics-tactics-normalize lib valid-first (list yes) nil nil 1500 nil))
         (opened-first (b2-pseudo-terms-first opened))
         (rewritten (proof-proof-rewrite proof valid opened '(1)))
         (tidied (proof-proof-tidy proof rewritten))
         (record-types (proof-proof-conjunct proof tidied))
         (typed-record (car record-types))
         (literal (b2-pseudo-terms-first typed-record))
         (equation (b2-tactics-tactics-normalize lib literal (list yes) (list literal) nil 1500 nil))
         (equation-first (b2-pseudo-terms-first equation))
         (reduced (proof-proof-rewrite proof typed-record equation '(1)))
         (tail (proof-proof-tidy proof reduced))
         (empty (b2-tactics-tactics-solve
                 lib (list *b2-list-properties-true-list* (list *library-cdr* record))
                 (list no) (list *b2-list-properties-true-list*) nil 0 nil))
         (step (proof-proof-cases proof test tail empty)))
      (list step))))

(defun b2-pseudo-terms-typed-options (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (source (cadr parts))
       (argument (proof-term-at (caddr parts) 1))
       (lookup (proof-term-at argument 1))
       (base-calls (list *b2-list-properties-true-list*))
       (request (b2-association-lookup-property lib formula lookup source nil base-calls :request)))
    (if (eq (car request) :b2-association-entry-evidence)
        (proof-with-checked-results
            ((reply (b2-pseudo-terms-typed-options-entry-type lib (cadr request) (caddr request))))
          (b2-association-lookup-property lib formula lookup source nil base-calls (list :reply reply)))
      request)))

(defun b2-pseudo-terms-preserve-pseudo-plain (lib name formula)
  (cond
   ((or (equal name *b2-pseudo-terms-list-cdr*) (equal name *b2-pseudo-terms-term-car*))
    (b2-pseudo-terms-list-selector lib formula))
   ((equal name (proof-sym "PSEUDO-TERMP-CADR-FROM-PSEUDO-TERM-LISTP" "ACL2"))
    (b2-pseudo-terms-cadr-lookup lib formula))
   ((or (equal name (proof-sym "PSEUDO-TERMP-OF-LOOKUP-IN-SUBST" "ACL2"))
        (equal name (proof-sym "PSEUDO-TERMP-OF-LOOKUP-IN-PSEUDO-TERM-VAL-ALISTP" "ACL2")))
    (b2-pseudo-terms-alist-lookup lib formula))
   (t
    (proof-with-checked-results ((text (proof-term-at name 2)))
      (cond
       ((integerp text)
        '(:failure "failure" ""))
       ((not (stringp text))
        '(:failure "failure" ""))
       ((text-ends-with text '("-APPEND" "-PAIRLIS"))
        (let ((rules (if (text-ends-with text "-PAIRLIS")
                         (list *b2-pseudo-terms-term-car* *b2-pseudo-terms-list-cdr*)
                       nil)))
          (b2-list-properties-preserve-list
           lib formula 0 rules (append *b2-list-properties-recognizers*
                                       (list *b2-pseudo-terms-subst* *b2-pseudo-terms-vals*))
           nil)))
       (t (b2-pseudo-terms-definition-equation lib formula)))))))

(defun b2-pseudo-terms-preserve-pseudo (lib name formula)
  (cond
   ((equal name (proof-sym "PSEUDO-TERM-LISTP-CDR" "ACL2"))
    (proof-with-checked-results ((step (b2-pseudo-terms-term-tail lib formula)))
      (cons step lib)))
   ((equal name (proof-sym "PSEUDO-TERMP-OPENER" "ACL2"))
    (b2-pseudo-terms-pterm-opener lib formula))
   (t
    (proof-with-checked-results ((step (b2-pseudo-terms-preserve-pseudo-plain lib name formula)))
      (cons step lib)))))
