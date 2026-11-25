(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-tactics-return-last* (proof-sym "RETURN-LAST" "ACL2"))
(defconst *h4-tactics-symbolp* (proof-cl "SYMBOLP"))
(defconst *h4-tactics-symbol-name* (proof-cl "SYMBOL-NAME"))
(defconst *h4-tactics-coerce* (proof-cl "COERCE"))
(defconst *h4-tactics-implies-elimination* (proof-sym "H4-IMPLIES-ELIMINATION" "ACL2"))
(defconst *h4-tactics-implies-conclusion* (proof-sym "H4-IMPLIES-FROM-CONCLUSION" "ACL2"))
(defconst *h4-tactics-implies-false-premise* (proof-sym "H4-IMPLIES-FROM-FALSE-PREMISE" "ACL2"))
(defconst *h4-tactics-first-conjunct* (proof-sym "H4-FIRST-CONJUNCT" "ACL2"))
(defconst *h4-tactics-second-conjunct* (proof-sym "H4-SECOND-CONJUNCT" "ACL2"))

(defun h4-tactics-car-data (value)
  (if (and (proof-compound value) (consp value)) (car value) *proof-nil*))

(defun h4-tactics-cdr-data (value)
  (cond ((or (not (proof-compound value)) (endp (cdr value))) *proof-nil*)
        ((and (endp (cddr value)) (equal (proof-datum-head (cadr value)) "dot"))
         (proof-term-at (cadr value) 1))
        (t (cdr value))))

(mutual-recursion
 (defun h4-tactics-match-term (pattern term bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (cond ((not (proof-compound pattern))
          (let ((existing (assoc-equal pattern bindings)))
            (if existing
                (cons (equal (cdr existing) term) bindings)
              (cons t (table-put bindings pattern term)))))
         ((proof-is-call pattern *proof-quote*) (cons (equal pattern term) bindings))
         ((or (not (proof-compound term)) (not (equal (len pattern) (len term))))
          (cons nil bindings))
         ((endp pattern) '(:failure "failure" ""))
         ((not (equal (car pattern) (car term))) (cons nil bindings))
         (t (h4-tactics-match-term-arguments (cdr pattern) (cdr term) bindings))))
 (defun h4-tactics-match-term-arguments (patterns terms bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (endp patterns)
       (cons t bindings)
     (proof-with-checked-results
         ((matched (h4-tactics-match-term (car patterns) (car terms) bindings)))
       (if (car matched)
           (h4-tactics-match-term-arguments (cdr patterns) (cdr terms) (cdr matched))
         matched)))))

(defun h4-tactics-tactics-add-definitions (definitions proof)
  (if (endp definitions)
      proof
    (proof-with-checked-results
        ((definition (proof-list-of-length (car definitions) 3))
         (next (proof-proof-add-definition proof (car definition)
                                          (cadr definition) (caddr definition))))
      (h4-tactics-tactics-add-definitions (cdr definitions) next))))

(defun h4-tactics-tactics-add-constraint-facts (constraints facts)
  (if (endp constraints)
      facts
    (proof-with-checked-results ((entry (proof-list-of-length (car constraints) 2)))
      (h4-tactics-tactics-add-constraint-facts
       (cdr constraints) (table-put facts (car entry) (list (cadr entry)))))))

(defun h4-tactics-tactics-add-statement (p kind fields)
  (let* ((proof (library-library-proof p))
         (facts (proof-proof-facts proof)))
    (cond ((equal kind "define")
           (proof-with-checked-results
               ((next (h4-tactics-tactics-add-definitions (cdr fields) proof)))
             (library-library-with-proof p next)))
          ((member-equal kind '("theorem" "axiom"))
           (proof-with-checked-results ((parts (proof-list-of-length fields 2)))
             (library-library-with-proof
              p (proof-proof-with-facts proof
                                        (table-put facts (car parts) (list (cadr parts)))))))
          ((equal kind "constrain")
           (proof-with-checked-results ((constraints (proof-term-at fields 1)))
             (if (equal constraints *proof-nil*)
                 p
               (proof-with-checked-results
                   ((next (h4-tactics-tactics-add-constraint-facts constraints facts)))
                 (library-library-with-proof p (proof-proof-with-facts proof next))))))
          (t p))))

(defun h4-tactics-tactics-local-lemma (p label step)
  (let* ((name (if (stringp label)
                   (proof-sym (concatenate 'string "H4-" label) "ACL2")
                 label))
         (proof (library-library-proof p))
         (facts (proof-proof-facts proof)))
    (if (assoc-equal name facts)
        '(:failure "failure" "")
      (let* ((clause (proof-step-clause step))
             (proof (proof-proof-with-facts proof (table-put facts name clause))))
        (proof-with-checked-results
            ((entry (proof-proof-entry "lemma" name (cons name clause) (list step))))
          (cons name (library-library-with-entries
                      (library-library-with-proof p proof)
                      (append (library-library-entries p) (list entry)))))))))

(defun h4-tactics-tactics-modus-ponens (p step evidence)
  (let ((proof (library-library-proof p)))
    (if (not (assoc-equal *h4-tactics-implies-elimination* (proof-proof-facts proof)))
        (proof-proof-modus-ponens proof step evidence)
      (proof-with-checked-results
          ((literal (proof-step-first step))
           (parts (proof-list-of-length literal 3)))
        (if (not (equal (car parts) *library-implies*))
            '(:failure "inapplicable-step" "")
          (proof-with-checked-results ((premise (proof-step-first evidence)))
            (if (not (equal (cadr parts) premise))
                '(:failure "inapplicable-step" "")
              (proof-with-checked-results
                  ((claim (proof-proof-fact proof *h4-tactics-implies-elimination*
                                            (list (list *library-x* premise)
                                                  (list *library-y* (caddr parts)))))
                   (discharged (proof-proof-discharge proof claim step)))
                (proof-proof-discharge proof discharged evidence)))))))))

(defun h4-tactics-tactics-fact-instance-known (evidence known)
  (if (endp evidence)
      known
    (proof-with-checked-results ((first (proof-step-first (car evidence))))
      (h4-tactics-tactics-fact-instance-known (cdr evidence)
                                             (table-put known first (car evidence))))))

(defun h4-tactics-tactics-fact-instance-conclusion (conclusion)
  (declare (xargs :measure (acl2-count conclusion)))
  (cond ((not (proof-is-call conclusion *library-implies*)) conclusion)
        ((endp (cddr conclusion)) '(:failure "failure" ""))
        (t (h4-tactics-tactics-fact-instance-conclusion (caddr conclusion)))))

(defun h4-tactics-tactics-fact-instance-apply (n p step known)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "h4-tactics-tactics-fact-instance-apply")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (if (not (proof-is-call literal *library-implies*))
          step
        (proof-with-checked-results ((premise (proof-term-at literal 1)))
          (let ((hypothesis (table-get known premise nil)))
            (if (not hypothesis)
                nil
              (proof-with-checked-results ((next (h4-tactics-tactics-modus-ponens p step hypothesis)))
                (h4-tactics-tactics-fact-instance-apply (1- n) p next known)))))))))

(defun h4-tactics-tactics-fact-instance-try (p name term known rewrite)
  (let* ((proof (library-library-proof p))
         (clause (table-get (proof-proof-facts proof) name nil)))
    (if (not (equal (len clause) 1))
        nil
      (proof-with-checked-results
          ((conclusion (h4-tactics-tactics-fact-instance-conclusion (car clause))))
        (if (and rewrite (not (proof-is-call conclusion *proof-equal*)))
            nil
          (proof-with-checked-results
              ((target (if rewrite (proof-term-at conclusion 1) conclusion)))
            (if (not (proof-compound target))
                nil
              (proof-with-checked-results ((matched (h4-tactics-match-term target term nil)))
                (if (not (car matched))
                    nil
                  (proof-with-checked-results
                      ((step (proof-proof-fact proof name (table-items (cdr matched)))))
                    (h4-tactics-tactics-fact-instance-apply 1000000 p step known)))))))))))

(defun h4-tactics-tactics-fact-instance-search (names p term known rewrite)
  (if (endp names)
      nil
    (let ((result (h4-tactics-tactics-fact-instance-try p (car names) term known rewrite)))
      (or result (h4-tactics-tactics-fact-instance-search (cdr names) p term known rewrite)))))

(defun h4-tactics-tactics-fact-instance (p term evidence names rewrite)
  (proof-with-checked-results ((known (h4-tactics-tactics-fact-instance-known evidence nil)))
    (h4-tactics-tactics-fact-instance-search
     (if (eq names :none) (table-keys (proof-proof-facts (library-library-proof p))) names)
     p term known rewrite)))

(defun h4-tactics-quote-argument (args index)
  (if (< index (len args))
      (proof-term-at (nth index args) 1)
    '(:failure "failure" "")))

(defun h4-tactics-tactics-constant-quoted (proof term)
  (proof-with-checked-results ((parts (proof-constant-call-parts term)))
    (let ((head (car parts))
          (args (cdr parts)))
      (cond ((member-equal head (list *library-car* *library-cdr* *h4-tactics-symbolp*
                                     *h4-tactics-symbol-name* (proof-cl "CHAR-CODE")))
             (proof-with-checked-results
                 ((value (h4-tactics-quote-argument args 0))
                  (result
                   (cond ((equal head *library-car*) (h4-tactics-car-data value))
                         ((equal head *library-cdr*) (h4-tactics-cdr-data value))
                         ((equal head *h4-tactics-symbolp*)
                          (if (equal (proof-datum-head value) "sym") *proof-t* *proof-nil*))
                         ((equal head *h4-tactics-symbol-name*)
                          (proof-with-checked-results
                              ((name (if (equal (proof-datum-head value) "sym")
                                         (proof-term-at value 2) "")))
                            (list "str" name)))
                         ((equal (proof-datum-head value) "char") (proof-term-at value 1))
                         (t 0))))
               (proof-proof-compute proof term result)))
            ((equal head *h4-tactics-coerce*)
             (proof-with-checked-results ((kind (h4-tactics-quote-argument args 1)))
               (if (not (equal kind (proof-cl "LIST")))
                   (proof-proof-constant-base proof term)
                 (proof-with-checked-results
                     ((value (h4-tactics-quote-argument args 0))
                      (chars (if (equal (proof-datum-head value) "str")
                                 (proof-with-checked-results ((contents (proof-term-at value 1)))
                                   (proof-constant-character-data (coerce contents 'list)))
                               nil)))
                   (proof-proof-compute proof term (or chars *proof-nil*))))))
            ((equal head *proof-cons*)
             (proof-with-checked-results
                 ((values (proof-quoted-values (seq-slice args :none 3)))
                  (pair (proof-list-of-length values 2)))
               (proof-proof-compute proof term (proof-constant-cons-value (car pair) (cadr pair)))))
            (t (proof-proof-constant-base proof term))))))

(defun h4-tactics-tactics-constant (p term)
  (let ((proof (library-library-proof p)))
    (cond ((eq term t) '(:failure "failure" ""))
          ((integerp term)
           '(:failure "failure" ""))
          ((and (stringp term) (not (equal term ""))) nil)
          ((proof-all-quoted-p (cdr term)) (h4-tactics-tactics-constant-quoted proof term))
          (t (proof-proof-constant-base proof term)))))

(defun h4-tactics-tactics-case-of (p formula test yes no)
  (proof-with-checked-results
      ((yes yes) (no no)
       (yes-first (proof-step-first yes))
       (no-first (proof-step-first no)))
    (if (and (equal yes-first no-first) (equal no-first formula))
        (proof-proof-cases (library-library-proof p) test yes no)
      '(:failure "inapplicable-step" ""))))

(defun h4-tactics-tactics-imply-opened (proof formula premise conclusion)
  (proof-with-checked-results
      ((opened (proof-proof-unfold proof formula))
       (outer (proof-rewritten-term opened))
       (inner (proof-term-at outer 2))
       (true-proof (proof-proof-prove proof *proof-true* nil nil))
       (selected (proof-proof-select proof inner conclusion))
       (yes (proof-proof-transport proof true-proof selected))
       (when-true (proof-proof-if-true proof outer))
       (yes (proof-proof-transport proof yes when-true))
       (true-proof (proof-proof-prove proof *proof-true* nil nil))
       (when-false (proof-proof-if-false proof outer))
       (no (proof-proof-transport proof true-proof when-false))
       (cases (proof-proof-cases proof premise yes no)))
    (proof-proof-transport proof cases opened)))

(defun h4-tactics-tactics-imply (p formula conclusion)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
      (if (not (equal (car parts) *library-implies*))
          '(:failure "inapplicable-step" "")
        (proof-with-checked-results ((result (proof-step-first conclusion)))
          (let ((premise (cadr parts)))
            (cond ((not (equal (caddr parts) result)) '(:failure "inapplicable-step" ""))
                  ((assoc-equal *h4-tactics-implies-conclusion* (proof-proof-facts proof))
                   (let ((bindings (list (list *library-x* premise) (list *library-y* result))))
                     (proof-with-checked-results
                         ((fact (proof-proof-fact proof *h4-tactics-implies-conclusion* bindings))
                          (yes (proof-proof-discharge proof fact conclusion))
                          (no (proof-proof-fact proof *h4-tactics-implies-false-premise* bindings)))
                       (proof-proof-cases proof premise yes no))))
                  (t (h4-tactics-tactics-imply-opened proof formula premise conclusion)))))))))

(defun h4-tactics-tactics-conjunct (p step)
  (let ((proof (library-library-proof p)))
    (if (not (assoc-equal *h4-tactics-first-conjunct* (proof-proof-facts proof)))
        (proof-proof-conjunct proof step)
      (proof-with-checked-results
          ((literal (proof-step-first step))
           (parts (proof-list-of-length literal 4)))
        (if (not (and (equal (car parts) *proof-if*) (equal (cadddr parts) *proof-false*)))
            '(:failure "inapplicable-step" "")
          (let ((bindings (list (list *library-x* (cadr parts)) (list *library-y* (caddr parts)))))
            (proof-with-checked-results
                ((first (proof-proof-fact proof *h4-tactics-first-conjunct* bindings))
                 (left (proof-proof-discharge proof first step))
                 (second (proof-proof-fact proof *h4-tactics-second-conjunct* bindings))
                 (right (proof-proof-discharge proof second step)))
              (list left right))))))))

(defun h4-tactics-tactics-propositional-lemmas-append (p lemmas)
  (declare (xargs :measure (acl2-count lemmas)))
  (if (endp lemmas)
      p
    (proof-with-checked-results
        ((step (proof-proof-tidy (library-library-proof p) (cdar lemmas)))
         (entry (h4-tactics-tactics-local-lemma p (caar lemmas) step)))
      (h4-tactics-tactics-propositional-lemmas-append (cdr entry) (cdr lemmas)))))

(defun h4-tactics-tactics-propositional-lemmas (p)
  (let* ((proof (library-library-proof p))
         (formula (list *library-implies* *library-x* *library-y*))
         (conjunction (proof-ite *library-x* *library-y* *proof-false*)))
    (proof-with-checked-results
        ((given (proof-proof-assume proof formula t))
         (premise (proof-proof-assume proof *library-x* t))
         (conclusion (h4-tactics-tactics-modus-ponens p given premise))
         (result (proof-proof-assume proof *library-y* t))
         (positive (h4-tactics-tactics-imply p formula result))
         (opened (proof-proof-unfold proof formula))
         (true-proof (proof-proof-prove proof *proof-true* nil nil))
         (outer (proof-rewritten-term opened))
         (selected (proof-proof-if-false proof outer))
         (equation (proof-proof-chain proof opened (list selected)))
         (negative (proof-proof-transport proof true-proof equation))
         (both (proof-proof-assume proof conjunction t))
         (parts (h4-tactics-tactics-conjunct p both)))
      (h4-tactics-tactics-propositional-lemmas-append
       p (list (cons *h4-tactics-implies-elimination* conclusion)
               (cons *h4-tactics-implies-conclusion* positive)
               (cons *h4-tactics-implies-false-premise* negative)
               (cons *h4-tactics-first-conjunct* (car parts))
               (cons *h4-tactics-second-conjunct* (cadr parts)))))))

(defun h4-tactics-tactics-conjunction (p formula first second)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((first-claim (proof-step-first first))
         (second-claim (proof-step-first second)))
      (if (not (equal formula (proof-ite first-claim second-claim *proof-false*)))
          '(:failure "inapplicable-step" "")
        (proof-with-checked-results ((selected (proof-proof-select proof formula first)))
          (proof-proof-transport proof second selected))))))

(defun h4-tactics-tactics-guarded (p test conclusion holds)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((proved (proof-proof-prove proof *proof-true* nil nil)))
      (let ((yes (if holds conclusion proved))
            (no (if holds proved conclusion)))
        (proof-with-checked-results
            ((yes-first (proof-step-first yes))
             (no-first (proof-step-first no))
             (formula (proof-ite test yes-first no-first))
             (when-true (proof-proof-if-true proof formula))
             (left (proof-proof-transport proof yes when-true))
             (when-false (proof-proof-if-false proof formula))
             (right (proof-proof-transport proof no when-false)))
          (proof-proof-cases proof test left right))))))

(defun h4-tactics-tactics-nil-value (p negative)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first negative))
         (head (proof-term-at literal 0)))
      (if (not (equal head *proof-not*))
          '(:failure "inapplicable-step" "")
        (proof-with-checked-results
            ((term (proof-term-at literal 1))
             (partition (proof-proof-nil-or-true proof term))
             (fronted (proof-proof-front proof partition term)))
          (proof-proof-cut proof fronted negative))))))

(defun h4-tactics-tactics-non-nil (p equality)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first equality))
         (parts (proof-list-of-length literal 3)))
      (let ((term (cadr parts))
            (value (caddr parts)))
        (if (not (and (proof-is-call value *proof-quote*) (not (equal value *proof-false*))))
            '(:failure "inapplicable-step" "")
          (proof-with-checked-results
              ((nil-or-true (proof-proof-nil-or-true proof term))
               (partition (proof-proof-rewrite proof nil-or-true equality '(1 1)))
               (computed (proof-proof-compute proof (proof-eq value *proof-false*) *proof-nil*))
               (rewritten (proof-proof-rewrite proof partition computed '(1))))
            (proof-proof-tidy proof rewritten)))))))

(defun h4-tactics-tactics-from-contrapositive (p step evidence)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (premise (proof-term-at literal 1))
         (hypothesis (proof-term-at premise 1))
         (assumed (proof-proof-assume proof hypothesis nil))
         (negative (h4-tactics-tactics-modus-ponens p step assumed))
         (result (proof-proof-cut proof evidence negative)))
      (proof-proof-front proof result hypothesis))))

(defun h4-tactics-tactics-select-literal (p term)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((parts (proof-list-of-length (cdr term) 3)))
      (let* ((test (car parts))
             (false-test (equal test *proof-false*))
             (branch (if false-test (caddr parts) (cadr parts))))
        (cond ((proof-all-quoted-p parts)
               (proof-with-checked-results ((value (proof-term-at branch 1)))
                 (proof-proof-compute proof term value)))
              (false-test
               (proof-proof-fact proof "if-nil" (list (list *library-y* (cadr parts))
                                                    (list *library-z* (caddr parts)))))
              (t (proof-with-checked-results
                     ((reflexive (proof-proof-reflexive proof test))
                      (non-nil (h4-tactics-tactics-non-nil p reflexive)))
                   (proof-proof-select proof term non-nil))))))))

(defun h4-tactics-tactics-rewrite-context-replace (path equality p term result)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((next (if (and (not result) (endp path))
                   equality
                 (proof-with-checked-results
                     ((prior (or result (proof-proof-reflexive proof term))))
                   (proof-proof-rewrite proof prior equality (append '(1 2) path)))))
         (value (proof-rewritten-term equality)))
      (cons value next))))

(mutual-recursion
 (defun h4-tactics-tactics-rewrite-context-visit (n value path p term expand result)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "h4-tactics-tactics-rewrite-context-visit"))
         ((proof-is-call value *proof-quote*) (cons value result))
         ((not (proof-compound value))
          (if (eq expand :none)
              (cons value result)
            '(:failure "inapplicable-term" "")))
         (t
          (proof-with-checked-results
              ((redex (h4-tactics-tactics-rewrite-context-redex
                       (1- n) value path p term expand result)))
            (if (eq (car redex) :done)
                (cdr redex)
              (proof-with-checked-results
                  ((next (h4-tactics-tactics-rewrite-context-replace
                          path (car redex) p term (cdr redex))))
                (h4-tactics-tactics-rewrite-context-visit
                 (1- n) (car next) path p term expand (cdr next))))))))
 (defun h4-tactics-tactics-rewrite-context-redex (n value path p term expand result)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "h4-tactics-tactics-rewrite-context-redex")
     (let ((proof (library-library-proof p)))
       (proof-with-checked-results ((head (proof-term-at value 0)))
         (cond
          ((proof-compound head)
           (proof-with-checked-results ((equality (proof-proof-beta proof value)))
             (cons equality result)))
          ((equal head *h4-tactics-return-last*)
           (proof-with-checked-results ((equality (proof-proof-unfold proof value)))
             (cons equality result)))
          ((and (equal head *proof-if*) (not (eq expand :none)))
           (proof-with-checked-results
               ((test (proof-term-at value 1))
                (next (h4-tactics-tactics-rewrite-context-visit
                       (1- n) test (append path '(1)) p term expand result))
                (yes (proof-term-at value 2))
                (no (proof-term-at value 3))
                (equality (h4-tactics-tactics-select-literal p (proof-ite (car next) yes no))))
             (cons equality (cdr next))))
          (t
           (proof-with-checked-results
               ((args (h4-tactics-tactics-rewrite-context-arguments
                       (1- n) (cdr value) path 1 p term expand result)))
             (let ((call (cons head (car args))))
               (if (eq expand :none)
                   (cons :done (cons call (cdr args)))
                 (proof-with-checked-results
                     ((equality (if (member-equal head expand)
                                    (proof-proof-unfold proof call)
                                  (h4-tactics-tactics-constant p call))))
                   (if equality
                       (cons equality (cdr args))
                     '(:failure "inapplicable-term" ""))))))))))))
 (defun h4-tactics-tactics-rewrite-context-arguments (n args path index p term expand result)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "h4-tactics-tactics-rewrite-context-arguments"))
         ((endp args) (cons nil result))
         (t
          (proof-with-checked-results
              ((first (h4-tactics-tactics-rewrite-context-visit
                       (1- n) (car args) (append path (list index)) p term expand result))
               (rest (h4-tactics-tactics-rewrite-context-arguments
                      (1- n) (cdr args) path (1+ index) p term expand (cdr first))))
            (cons (cons (car first) (car rest)) (cdr rest)))))))

(defun h4-tactics-tactics-rewrite-context (p term expand initial)
  (proof-with-checked-results
      ((visited (h4-tactics-tactics-rewrite-context-visit 1000000 term nil p term expand initial)))
    (or (cdr visited) (proof-proof-reflexive (library-library-proof p) term))))

(defun h4-tactics-tactics-evaluate-closed (p term expand)
  (h4-tactics-tactics-rewrite-context p term expand nil))

(defun h4-tactics-request-p (result)
  (and (consp result) (eq (car result) :h4-tactics-request)))

(defun h4-tactics-request-term (request)
  (cadr request))

(defmacro h4-tactics-with-normalization-results (bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (or (failure-p ,name) (h4-tactics-request-p ,name))
             ,name
           (h4-tactics-with-normalization-results ,(cdr bindings) ,result))))))

(defun h4-tactics-constructor-provider (consp-cons)
  (list :h4-tactics-constructors consp-cons))

(defun h4-tactics-constructor-reduction (term p consp-cons)
  (proof-with-checked-results ((head (proof-term-at term 0)))
    (if (not (member-equal head (list *library-car* *library-cdr* *proof-consp*)))
        nil
      (proof-with-checked-results ((argument (proof-term-at term 1)))
        (if (not (proof-is-call argument *proof-cons*))
            nil
          (if (equal head *proof-consp*)
              (proof-proof-instantiate (library-library-proof p) consp-cons
                                       (seq-zip (list *library-x* *library-y*) (cdr argument)))
            (library-library-axiom p (if (equal head *library-car*) "CAR-CONS" "CDR-CONS")
                                    (cdr argument))))))))

(defun h4-tactics-tactics-normalize-provider (p term visit-state)
  (let* ((provide (car visit-state))
         (kind (car provide)))
    (case kind
      (:h4-tactics-constructors
       (proof-with-checked-results
           ((reply (h4-tactics-constructor-reduction term p (cadr provide))))
         (cons reply visit-state)))
      (:h4-tactics-provider
       (let ((reply (assoc-equal term (cdr provide))))
         (if reply
             (proof-with-checked-results ((value (cdr reply))) (cons value visit-state))
           (list :h4-tactics-request term))))
      (:h4-tactics-ordered-provider
       (if (endp (cdr provide))
           (list :h4-tactics-request term)
         (proof-with-checked-results ((reply (cadr provide)))
           (cons reply (cons (cons kind (cddr provide)) (cdr visit-state))))))
      (otherwise
       (proof-with-checked-results ((reply (table-get provide term nil)))
         (cons reply visit-state))))))

(defun h4-tactics-tactics-normalize-rules (rewrites rules)
  (if (endp rewrites)
      rules
    (proof-with-checked-results
        ((first (proof-step-first (car rewrites)))
         (left (proof-term-at first 1)))
      (h4-tactics-tactics-normalize-rules (cdr rewrites)
                                         (table-put rules left (car rewrites))))))

(defun h4-tactics-tactics-normalize-lift (proof term step reduction place)
  (if (not reduction)
      step
    (proof-with-checked-results ((prior (or step (proof-proof-reflexive proof term))))
      (proof-proof-rewrite proof prior reduction place))))

(defun h4-tactics-tactics-normalize-choice (p test yes no known)
  (let ((redex (proof-ite test yes no))
        (premise (or (table-get known test nil)
                     (table-get known (proof-neg test) nil))))
    (cond (premise (proof-proof-select (library-library-proof p) redex premise))
          ((proof-is-call test *proof-quote*) (h4-tactics-tactics-select-literal p redex))
          (t nil))))

(defun h4-tactics-tactics-normalize-default (p redex expand)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((head (proof-term-at redex 0))
         (direct (cond ((member-equal head expand) (proof-proof-unfold proof redex))
                       ((proof-is-call redex *proof-equal*)
                        (proof-with-checked-results
                            ((left (proof-term-at redex 1)) (right (proof-term-at redex 2)))
                          (if (equal left right)
                              (proof-proof-fact proof "equal-same" (list (list *library-x* left)))
                            nil)))
                       (t nil))))
      (if (and (not direct) (member-equal head (proof-proof-primitives proof)))
          (h4-tactics-tactics-constant p redex)
        direct))))

(defun h4-tactics-tactics-normalize-reduction (p redex known expand rules visit-state)
  (let ((rule (table-get rules redex nil))
        (negative (table-get known (proof-neg redex) nil)))
    (cond (rule (cons rule visit-state))
          ((assoc-equal redex known) (cons nil visit-state))
          (negative
           (proof-with-checked-results ((step (h4-tactics-tactics-nil-value p negative)))
             (cons step visit-state)))
          (t (h4-tactics-with-normalization-results
                 ((provided (h4-tactics-tactics-normalize-provider p redex visit-state)))
               (if (car provided)
                   provided
                 (proof-with-checked-results
                     ((direct (h4-tactics-tactics-normalize-default p redex expand)))
                   (cons direct (cdr provided)))))))))

(mutual-recursion
 (defun h4-tactics-tactics-normalize-visit (n value p known expand rules visit-state)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "h4-tactics-tactics-normalize-visit")
     (let* ((ordered (eq (caar visit-state) :h4-tactics-ordered-provider))
            (previous (and ordered (assoc-equal value (cdr visit-state)))))
       (if previous
           (cons (cdr previous) visit-state)
         (h4-tactics-with-normalization-results
             ((result (h4-tactics-tactics-normalize-visit-value
                       (1- n) value p known expand rules visit-state)))
           (if ordered
               (cons (car result) (cons (cadr result) (acons value (car result) (cddr result))))
             result))))))
 (defun h4-tactics-tactics-normalize-visit-value (n value p known expand rules visit-state)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "h4-tactics-tactics-normalize-visit-value")
     (let ((proof (library-library-proof p))
           (rule (assoc-equal value rules))
           (negative (table-get known (proof-neg value) nil)))
       (cond
        (rule
         (proof-with-checked-results ((right (proof-rewritten-term (cdr rule))))
           (if (equal right value)
               (cons (cdr rule) visit-state)
             (h4-tactics-with-normalization-results
                 ((rest (h4-tactics-tactics-normalize-visit
                         (1- n) right p known expand rules visit-state))
                  (step (proof-proof-chain proof (cdr rule) (list (car rest)))))
               (cons step (cdr rest))))))
        ((and negative (not (equal value *proof-false*)))
         (proof-with-checked-results ((step (h4-tactics-tactics-nil-value p negative)))
           (cons step visit-state)))
        ((or (assoc-equal value known)
             (not (proof-compound value))
             (proof-is-call value *proof-quote*))
         (cons nil visit-state))
        (t
         (proof-with-checked-results ((head (proof-term-at value 0)))
           (cond ((or (proof-compound head) (equal head *h4-tactics-return-last*))
                  (h4-tactics-with-normalization-results
                      ((step (if (proof-compound head)
                                 (proof-proof-beta proof value)
                               (proof-proof-unfold proof value)))
                       (right (proof-rewritten-term step))
                       (rest (h4-tactics-tactics-normalize-visit
                              (1- n) right p known expand rules visit-state))
                       (step (proof-proof-chain proof step (list (car rest)))))
                    (cons step (cdr rest))))
                 ((equal head *proof-if*)
                  (h4-tactics-tactics-normalize-if (1- n) value p known expand rules visit-state))
                 (t (h4-tactics-tactics-normalize-call (1- n) value p known expand rules visit-state)))))))))
 (defun h4-tactics-tactics-normalize-if (n value p known expand rules visit-state)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "h4-tactics-tactics-normalize-if")
     (let ((proof (library-library-proof p)))
       (h4-tactics-with-normalization-results
           ((parts (proof-list-of-length (cdr value) 3))
            (test (car parts))
            (reduction (if (or (assoc-equal test known) (assoc-equal (proof-neg test) known))
                           (cons nil visit-state)
                         (h4-tactics-tactics-normalize-visit
                          (1- n) test p known expand rules visit-state)))
            (step (h4-tactics-tactics-normalize-lift proof value nil (car reduction) '(1 2 1)))
            (test (if (car reduction) (proof-rewritten-term (car reduction)) test))
            (choice (h4-tactics-tactics-normalize-choice p test (cadr parts) (caddr parts) known)))
         (if (not choice)
             (cons step (cdr reduction))
           (h4-tactics-with-normalization-results
               ((right (proof-rewritten-term choice))
                (rest (h4-tactics-tactics-normalize-visit
                       (1- n) right p known expand rules (cdr reduction)))
                (chained (proof-proof-chain proof (or step choice)
                                            (list (and step choice) (car rest)))))
             (cons chained (cdr rest))))))))
 (defun h4-tactics-tactics-normalize-call (n value p known expand rules visit-state)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "h4-tactics-tactics-normalize-call")
     (let ((proof (library-library-proof p)))
       (h4-tactics-with-normalization-results
           ((arguments (h4-tactics-tactics-normalize-arguments
                        (1- n) (cdr value) 1 nil value p known expand rules visit-state))
            (step (car arguments))
            (redex (if step (proof-rewritten-term step) value))
            (reduction (h4-tactics-tactics-normalize-reduction p redex known expand rules (cdr arguments)))
            (direct (car reduction)))
         (if (not direct)
             (cons step (cdr reduction))
           (h4-tactics-with-normalization-results
               ((right (proof-rewritten-term direct))
                (rest (if (equal right redex)
                          (cons nil (cdr reduction))
                        (h4-tactics-tactics-normalize-visit
                         (1- n) right p known expand rules (cdr reduction))))
                (chained (proof-proof-chain proof (or step direct)
                                            (list (and step direct) (car rest)))))
             (cons chained (cdr rest))))))))
 (defun h4-tactics-tactics-normalize-arguments (n args index step value p known expand rules visit-state)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "h4-tactics-tactics-normalize-arguments"))
         ((endp args) (cons step visit-state))
         (t
          (h4-tactics-with-normalization-results
              ((reduction (h4-tactics-tactics-normalize-visit
                           (1- n) (car args) p known expand rules visit-state))
               (next (h4-tactics-tactics-normalize-lift
                      (library-library-proof p) value step (car reduction) (list 1 2 index))))
            (h4-tactics-tactics-normalize-arguments
             (1- n) (cdr args) (1+ index) next value p known expand rules (cdr reduction)))))))

(defun h4-tactics-tactics-normalize (p term evidence expand rewrites provide)
  (h4-tactics-with-normalization-results
      ((known (h4-tactics-tactics-fact-instance-known evidence nil))
       (rules (h4-tactics-tactics-normalize-rules rewrites nil))
       (result (h4-tactics-tactics-normalize-visit
                1000000 term p known expand rules (cons provide nil))))
    (or (car result) (proof-proof-reflexive (library-library-proof p) term))))

(defun h4-tactics-tactics-establish (p formula evidence expand rewrites provide)
  (let ((proof (library-library-proof p)))
    (if (equal formula *proof-true*)
        (proof-proof-prove proof *proof-true* nil nil)
      (h4-tactics-with-normalization-results ((premise (proof-find-evidence evidence (list formula))))
        (if premise
            premise
          (h4-tactics-with-normalization-results
              ((equality (h4-tactics-tactics-normalize p formula evidence expand rewrites provide))
               (value (proof-rewritten-term equality))
               (premise (proof-find-evidence evidence (list value))))
            (cond (premise (proof-proof-transport proof premise equality))
                  ((and (proof-is-call value *proof-quote*) (not (equal value *proof-false*)))
                   (h4-tactics-tactics-non-nil p equality))
                  (t '(:failure "inapplicable-term" "")))))))))
