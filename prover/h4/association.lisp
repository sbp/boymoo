(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-association-implies-elimination* (proof-sym "H4-IMPLIES-ELIMINATION" "ACL2"))
(defconst *h4-association-implies-conclusion* (proof-sym "H4-IMPLIES-FROM-CONCLUSION" "ACL2"))
(defconst *h4-association-implies-false-premise*
  (proof-sym "H4-IMPLIES-FROM-FALSE-PREMISE" "ACL2"))
(defconst *h4-association-first-conjunct* (proof-sym "H4-FIRST-CONJUNCT" "ACL2"))
(defconst *h4-association-second-conjunct* (proof-sym "H4-SECOND-CONJUNCT" "ACL2"))
(defconst *h4-association-return-last* (proof-sym "RETURN-LAST" "ACL2"))

(defun h4-association-step-at (step index)
  (proof-with-checked-results ((first (proof-step-first step)))
    (proof-term-at first index)))

(defun h4-association-local-lemma (p label step)
  (let* ((proof (library-library-proof p))
         (facts (proof-proof-facts proof))
         (name (if (stringp label)
                   (proof-sym (concatenate 'string "H4-" label) "ACL2")
                 label))
         (clause (proof-step-clause step)))
    (if (assoc-equal name facts)
        '(:failure "inapplicable-step" "")
      (proof-with-checked-results
       ((entry (proof-proof-entry "lemma" name (cons name clause) (list step))))
       (cons name
             (library-make-library
              (proof-proof-with-facts proof (table-put facts name clause))
              (append (library-library-entries p) (list entry))))))))

(defun h4-association-conjunction (p formula first second)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((a (proof-step-first first))
      (b (proof-step-first second)))
     (if (equal formula (proof-ite a b *proof-false*))
         (proof-with-checked-results ((selected (proof-proof-select proof formula first)))
           (proof-proof-transport proof second selected))
       '(:failure "inapplicable-step" "")))))

(defun h4-association-conjunct (p step)
  (let ((proof (library-library-proof p)))
    (if (not (assoc-equal *h4-association-first-conjunct* (proof-proof-facts proof)))
        (proof-proof-conjunct proof step)
      (proof-with-checked-results
       ((first (proof-step-first step))
        (parts (proof-list-of-length first 4)))
       (if (and (equal (car parts) *proof-if*) (equal (cadddr parts) *proof-false*))
           (let ((bindings (list (list *library-x* (cadr parts))
                                 (list *library-y* (caddr parts)))))
             (proof-with-checked-results
              ((first (proof-proof-fact proof *h4-association-first-conjunct* bindings))
               (left (proof-proof-discharge proof first step))
               (second (proof-proof-fact proof *h4-association-second-conjunct* bindings))
               (right (proof-proof-discharge proof second step)))
              (list left right)))
         '(:failure "inapplicable-step" ""))))))

(defun h4-association-modus-ponens (p step evidence)
  (let ((proof (library-library-proof p)))
    (if (not (assoc-equal *h4-association-implies-elimination* (proof-proof-facts proof)))
        (proof-proof-modus-ponens proof step evidence)
      (proof-with-checked-results
       ((first (proof-step-first step))
        (parts (proof-list-of-length first 3))
        (premise (proof-step-first evidence)))
       (if (and (equal (car parts) *library-implies*) (equal (cadr parts) premise))
           (proof-with-checked-results
            ((claim (proof-proof-fact
                     proof *h4-association-implies-elimination*
                     (list (list *library-x* premise) (list *library-y* (caddr parts)))))
             (discharged (proof-proof-discharge proof claim step)))
            (proof-proof-discharge proof discharged evidence))
         '(:failure "inapplicable-step" ""))))))

(defun h4-association-imply (p formula conclusion)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (first (proof-step-first conclusion)))
     (let ((premise (cadr parts))
           (result (caddr parts)))
       (cond
        ((not (and (equal (car parts) *library-implies*) (equal result first)))
         '(:failure "inapplicable-step" ""))
        ((assoc-equal *h4-association-implies-conclusion* (proof-proof-facts proof))
         (let ((bindings (list (list *library-x* premise) (list *library-y* result))))
           (proof-with-checked-results
            ((claim (proof-proof-fact proof *h4-association-implies-conclusion* bindings))
             (yes (proof-proof-discharge proof claim conclusion))
             (no (proof-proof-fact proof *h4-association-implies-false-premise* bindings)))
            (proof-proof-cases proof premise yes no))))
        (t
         (proof-with-checked-results
          ((opened (proof-proof-unfold proof formula))
           (outer (h4-association-step-at opened 2))
           (inner (proof-term-at outer 2))
           (true (proof-proof-prove proof *proof-true* nil nil))
           (selected (proof-proof-select proof inner conclusion))
           (yes (proof-proof-transport proof true selected))
           (outer-true (proof-proof-if-true proof outer))
           (yes (proof-proof-transport proof yes outer-true))
           (true (proof-proof-prove proof *proof-true* nil nil))
           (outer-false (proof-proof-if-false proof outer))
           (no (proof-proof-transport proof true outer-false))
           (cases (proof-proof-cases proof premise yes no)))
          (proof-proof-transport proof cases opened))))))))

(defun h4-association-case-of (p formula test yes no)
  (proof-with-checked-results
   ((yes yes)
    (no no)
    (yes-first (proof-step-first yes))
    (no-first (proof-step-first no)))
   (if (and (equal yes-first no-first) (equal no-first formula))
       (proof-proof-cases (library-library-proof p) test yes no)
     '(:failure "inapplicable-step" ""))))

(defun h4-association-nil-value (p negative)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((first (proof-step-first negative)))
      (if (not (proof-is-call first *proof-not*))
          '(:failure "inapplicable-step" "")
        (proof-with-checked-results
         ((term (proof-term-at first 1))
          (partition (proof-proof-nil-or-true proof term))
          (front (proof-proof-front proof partition term)))
         (proof-proof-cut proof front negative))))))

(defun h4-association-non-nil (proof equality)
  (proof-with-checked-results
   ((first (proof-step-first equality))
    (parts (proof-list-of-length first 3)))
   (let ((term (cadr parts))
         (value (caddr parts)))
     (if (and (proof-is-call value *proof-quote*) (not (equal value *proof-false*)))
         (proof-with-checked-results
          ((partition (proof-proof-nil-or-true proof term))
           (partition (proof-proof-rewrite proof partition equality '(1 1)))
           (computed (proof-proof-compute proof (proof-eq value *proof-false*) *proof-nil*))
           (partition (proof-proof-rewrite proof partition computed '(1))))
          (proof-proof-tidy proof partition))
       '(:failure "inapplicable-step" "")))))

(defun h4-association-select-literal (proof term)
  (proof-with-checked-results ((parts (proof-list-of-length (cdr term) 3)))
    (let* ((test (car parts))
           (yes (cadr parts))
           (no (caddr parts))
           (branch (if (equal test *proof-false*) no yes)))
      (cond
       ((proof-all-quoted-p parts)
        (proof-with-checked-results ((value (proof-term-at branch 1)))
          (proof-proof-compute proof term value)))
       ((equal test *proof-false*)
        (proof-proof-fact proof "if-nil" (list (list *library-y* yes) (list *library-z* no))))
       (t
        (proof-with-checked-results
         ((identity (proof-proof-reflexive proof test))
          (evidence (h4-association-non-nil proof identity)))
         (proof-proof-select proof term evidence)))))))

(defun h4-association-constant-argument (args index)
  (if (< index (len args))
      (proof-term-at (nth index args) 1)
    '(:failure "missing-term-part" "")))

(defun h4-association-constant (proof term)
  (let ((head (car term))
        (args (cdr term)))
    (cond
     ((not (proof-all-quoted-p args)) (proof-proof-constant-base proof term))
     ((member-equal head (list *library-car* *library-cdr* *proof-cons*))
      (proof-constant-book-list proof term))
     ((equal head (proof-cl "SYMBOLP"))
      (proof-with-checked-results ((value (h4-association-constant-argument args 0)))
        (proof-proof-compute proof term (if (equal (car value) "sym") *proof-t* *proof-nil*))))
     ((equal head (proof-cl "SYMBOL-NAME"))
      (proof-with-checked-results
       ((value (h4-association-constant-argument args 0))
        (name (if (equal (car value) "sym") (proof-term-at value 2) "")))
       (proof-proof-compute proof term (list "str" name))))
     ((equal head (proof-cl "CHAR-CODE"))
      (proof-with-checked-results
       ((value (h4-association-constant-argument args 0))
        (code (if (equal (car value) "char") (proof-term-at value 1) 0)))
       (proof-proof-compute proof term code)))
     ((equal head (proof-cl "COERCE"))
      (proof-with-checked-results ((kind (h4-association-constant-argument args 1)))
        (if (equal kind (proof-cl "LIST"))
            (proof-with-checked-results
             ((value (h4-association-constant-argument args 0))
              (chars (proof-constant-coerced-value value kind)))
             (proof-proof-compute proof term chars))
          (proof-proof-constant-base proof term))))
     (t (proof-proof-constant-base proof term)))))

(defun h4-association-step-map (steps index entries)
  (if (endp steps)
      entries
    (proof-with-checked-results
     ((key (if index
               (h4-association-step-at (car steps) index)
             (proof-step-first (car steps)))))
     (h4-association-step-map (cdr steps) index (table-put entries key (car steps))))))

(defun h4-association-normalize-redex (p term known rules expand)
  (let* ((proof (library-library-proof p))
         (direct (cdr (assoc-equal term rules))))
    (cond
     (direct direct)
     ((assoc-equal term known) nil)
     ((assoc-equal (proof-neg term) known)
      (h4-association-nil-value p (cdr (assoc-equal (proof-neg term) known))))
     ((member-equal (car term) expand) (proof-proof-unfold proof term))
     ((proof-is-call term *proof-equal*)
      (proof-with-checked-results
       ((a (proof-term-at term 1))
        (b (proof-term-at term 2)))
       (cond ((equal a b) (proof-proof-fact proof "equal-same" (list (list *library-x* a))))
             ((member-equal (car term) (proof-proof-primitives proof))
              (h4-association-constant proof term))
             (t nil))))
     ((member-equal (car term) (proof-proof-primitives proof))
      (h4-association-constant proof term))
     (t nil))))

(mutual-recursion
 (defun h4-association-normalize-visit (n p value known rules expand)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "h4-association-normalize-visit")
     (let* ((proof (library-library-proof p))
            (rule (assoc-equal value rules))
            (negative (assoc-equal (proof-neg value) known)))
       (cond
        (rule
         (proof-with-checked-results ((right (h4-association-step-at (cdr rule) 2)))
           (if (equal right value)
               (cdr rule)
             (proof-with-checked-results
              ((rest (h4-association-normalize-visit (1- n) p right known rules expand)))
              (proof-proof-chain proof (cdr rule) (list rest))))))
        ((and negative (not (equal value *proof-false*)))
         (h4-association-nil-value p (cdr negative)))
        ((or (assoc-equal value known) (not (proof-compound value))
             (proof-is-call value *proof-quote*))
         nil)
        ((endp value) '(:failure "missing-term-part" ""))
        ((or (proof-compound (car value)) (equal (car value) *h4-association-return-last*))
         (proof-with-checked-results
          ((step (if (proof-compound (car value))
                     (proof-proof-beta proof value)
                   (proof-proof-unfold proof value)))
           (right (h4-association-step-at step 2))
           (rest (h4-association-normalize-visit (1- n) p right known rules expand)))
          (proof-proof-chain proof step (list rest))))
        ((proof-is-call value *proof-if*)
         (proof-with-checked-results
          ((parts (proof-list-of-length (cdr value) 3))
           (test (car parts))
           (reduction (if (or (assoc-equal test known) (assoc-equal (proof-neg test) known))
                          nil
                        (h4-association-normalize-visit (1- n) p test known rules expand)))
           (initial (and reduction (proof-proof-reflexive proof value)))
           (step (and reduction (proof-proof-rewrite proof initial reduction '(1 2 1))))
           (test (if reduction (h4-association-step-at reduction 2) test))
           (redex (proof-ite test (cadr parts) (caddr parts)))
           (premise (or (cdr (assoc-equal test known)) (cdr (assoc-equal (proof-neg test) known))))
           (choice (cond (premise (proof-proof-select proof redex premise))
                         ((proof-is-call test *proof-quote*)
                          (h4-association-select-literal proof redex))
                         (t nil))))
          (if (not choice)
              step
            (proof-with-checked-results
             ((right (h4-association-step-at choice 2))
              (rest (h4-association-normalize-visit (1- n) p right known rules expand)))
             (proof-proof-chain proof (or step choice) (list (and step choice) rest))))))
        (t
         (proof-with-checked-results
          ((step (h4-association-normalize-arguments (1- n) p (cdr value) 1 value nil
                                                     known rules expand))
           (redex (if step (h4-association-step-at step 2) value))
           (direct (h4-association-normalize-redex p redex known rules expand)))
          (if (not direct)
              step
            (proof-with-checked-results
             ((right (h4-association-step-at direct 2))
              (rest (if (equal right redex)
                        nil
                      (h4-association-normalize-visit (1- n) p right known rules expand))))
             (proof-proof-chain proof (or step direct) (list (and step direct) rest))))))))))
 (defun h4-association-normalize-arguments (n p args index value step known rules expand)
   (declare (xargs :measure (nfix n)))
   (cond
    ((endp args) step)
    ((zp n) '(:failure "fuel" "h4-association-normalize-arguments"))
    (t
     (let ((proof (library-library-proof p)))
       (proof-with-checked-results
        ((change (h4-association-normalize-visit (1- n) p (car args) known rules expand))
         (initial (if (and change (not step)) (proof-proof-reflexive proof value) step))
         (step (if change (proof-proof-rewrite proof initial change (list 1 2 index)) step)))
        (h4-association-normalize-arguments (1- n) p (cdr args) (1+ index) value step
                                             known rules expand)))))))

(defun h4-association-normalize (p term evidence expand rewrites)
  (proof-with-checked-results
   ((known (h4-association-step-map evidence nil nil))
    (rules (h4-association-step-map rewrites 1 nil))
    (result (h4-association-normalize-visit 1000000 p term known rules expand)))
   (or result (proof-proof-reflexive (library-library-proof p) term))))

(defun h4-association-establish (p formula evidence expand rewrites)
  (let ((proof (library-library-proof p)))
    (if (equal formula *proof-true*)
        (proof-proof-prove proof *proof-true* nil nil)
      (proof-with-checked-results ((known (proof-find-evidence evidence (list formula))))
        (if known
            known
          (proof-with-checked-results
           ((equality (h4-association-normalize p formula evidence expand rewrites))
            (value (h4-association-step-at equality 2))
            (known (proof-find-evidence evidence (list value))))
           (cond (known (proof-proof-transport proof known equality))
                 ((and (proof-is-call value *proof-quote*) (not (equal value *proof-false*)))
                  (h4-association-non-nil proof equality))
                 (t '(:failure "inapplicable-term" "")))))))))

(defun h4-association-rational (p term evidence)
  (proof-with-checked-results
   ((axiom (library-library-axiom p "INTEGER-IMPLIES-RATIONAL" (list term)))
    (integer-step (library-library-type-of p term evidence)))
   (h4-association-modus-ponens p axiom integer-step)))

(defun h4-association-number (p term evidence)
  (proof-with-checked-results
   ((fact (proof-proof-fact (library-library-proof p) "rationalp-acl2-numberp"
                           (list (list *library-x* term))))
    (rational (h4-association-rational p term evidence)))
   (h4-association-modus-ponens p fact rational)))

(defun h4-association-arity-or-logic-select-lookup (ending matching p lookup)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof lookup))
      (right (h4-association-step-at opened 2))
      (selected (proof-proof-select proof right ending))
      (result (proof-proof-chain proof opened (list selected))))
     (if matching
         (proof-with-checked-results
          ((right (h4-association-step-at result 2))
           (selected (proof-proof-select proof right matching)))
          (proof-proof-chain proof result (list selected)))
       result))))

(defun h4-association-arity-or-logic-transport-goal (step equality p arity-goal)
  (if (not arity-goal)
      step
    (let ((proof (library-library-proof p)))
      (proof-with-checked-results ((symmetric (proof-proof-symmetric proof equality)))
        (proof-proof-rewrite proof step symmetric '(1 2 1))))))

(defun h4-association-arity-or-logic-empty (ending p entry lookup goal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((reduction (h4-association-arity-or-logic-select-lookup ending nil p lookup))
      (impossible (proof-proof-rewrite proof entry reduction '(1))))
     (proof-proof-subsume proof impossible (cons goal (cdr (proof-step-clause impossible)))))))

(defun h4-association-arity-or-logic-nonempty-head
    (matching p ending arity logic arity-goal lookup)
  (let ((proof (library-library-proof p))
        (fact (if arity-goal arity logic))
        (place (if arity-goal '(1 1 1) '(1 1))))
    (proof-with-checked-results
     ((symmetric (proof-proof-symmetric proof matching))
      (rewritten (proof-proof-rewrite proof fact symmetric place))
      (reduction (h4-association-arity-or-logic-select-lookup ending matching p lookup)))
     (h4-association-arity-or-logic-transport-goal rewritten reduction p arity-goal))))

(defun h4-association-arity-or-logic-nonempty-tail
    (nonmatching p ending lookup entry induction-case descent child tail-ok arity-goal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((reduction (h4-association-arity-or-logic-select-lookup ending nonmatching p lookup))
      (tail-entry (proof-proof-rewrite proof entry reduction '(1)))
      (assumed (proof-proof-assume proof induction-case t))
      (discharged (proof-proof-discharge proof descent ending))
      (hypothesis (proof-proof-prove-if proof assumed discharged))
      (premise (proof-term-at child 1))
      (evidence (h4-association-conjunction p premise tail-ok tail-entry))
      (result (h4-association-modus-ponens p hypothesis evidence)))
     (h4-association-arity-or-logic-transport-goal result reduction p arity-goal))))

(defun h4-association-arity-or-logic-nonempty
    (ending p ok arities-ok arity-goal lookup entry induction-case descent child key-matches goal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof arities-ok))
      (opened (proof-proof-rewrite proof ok opened '(1)))
      (opened (proof-proof-prove-if proof opened ending))
      (conjuncts (h4-association-conjunct p opened))
      (rest (h4-association-conjunct p (cadr conjuncts)))
      (matching (proof-proof-assume proof key-matches t))
      (yes (h4-association-arity-or-logic-nonempty-head
            matching p ending (car conjuncts) (car rest) arity-goal lookup))
      (nonmatching (proof-proof-assume proof key-matches nil))
      (no (h4-association-arity-or-logic-nonempty-tail
           nonmatching p ending lookup entry induction-case descent child (cadr rest) arity-goal)))
     (h4-association-case-of p goal key-matches yes no))))

(defun h4-association-arity-or-logic (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((parts (proof-list-of-length formula 3))
      (premise (proof-list-of-length (cadr parts) 4))
      (goal (caddr parts))
      (arities-ok (cadr premise))
      (table (proof-term-at arities-ok 1))
      (lookup-equation (h4-association-normalize p (caddr premise) nil nil nil))
      (lookup (h4-association-step-at lookup-equation 2))
      (fn (proof-term-at lookup 1))
      (head (proof-term-at goal 0))
      (arity-goal (equal head *proof-equal*))
      (left (and arity-goal (proof-term-at goal 1)))
      (goal (if arity-goal (proof-eq left (list *library-cdr* lookup)) goal))
      (premise (proof-ite arities-ok lookup *proof-false*))
      (canonical (list *library-implies* premise goal))
      (assumed (proof-proof-assume proof premise t))
      (conjuncts (h4-association-conjunct p assumed))
      (ok (car conjuncts))
      (entry (cadr conjuncts))
      (endp-test (list (proof-cl "ENDP") table))
      (head-key (list *library-car* (list *library-car* table)))
      (key-matches (proof-eq fn head-key))
      (measure (list *library-count* table))
      (substitution (list (list table (list *library-cdr* table))))
      (child (proof-subst canonical (list (cons table (list *library-cdr* table)))))
      (descent (library-library-builtin p 7 table))
      (decrease (proof-step-first descent))
      (induction-case (proof-ite decrease child *proof-true*))
      (ending (proof-proof-assume proof endp-test t))
      (yes (h4-association-arity-or-logic-empty ending p entry lookup goal))
      (ending (proof-proof-assume proof endp-test nil))
      (no (h4-association-arity-or-logic-nonempty
           ending p ok arities-ok arity-goal lookup entry induction-case descent child key-matches goal))
      (proof-cases (h4-association-case-of p goal endp-test yes no))
      (case-step (h4-association-imply p canonical proof-cases))
      (ordinal (library-library-builtin p 1 table))
      (proven (proof-proof-induct proof ordinal case-step canonical measure (list substitution)))
      (symmetric (proof-proof-symmetric proof lookup-equation))
      (proven (proof-proof-rewrite proof proven symmetric '(1 1 2)))
      (symmetric (and arity-goal (proof-proof-symmetric proof lookup-equation)))
      (proven (if arity-goal (proof-proof-rewrite proof proven symmetric '(1 2 2 1)) proven))
      (first (proof-step-first proven)))
     (if (equal first formula)
         (proof-proof-tidy proof proven)
       '(:failure "failure" "")))))
