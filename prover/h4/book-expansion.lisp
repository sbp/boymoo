(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-expansion-e0-ordinal* (proof-sym "E0-ORDINALP" "ACL2"))
(defconst *h4-book-expansion-e0-less* (proof-sym "E0-ORD-<" "ACL2"))
(defconst *h4-book-expansion-copy* (proof-sym "COPYN" "ACL2"))
(defconst *h4-book-expansion-ctoa* (proof-sym "CTOA" "ACL2"))
(defconst *h4-book-expansion-element* (proof-sym "ELEMENT" "ACL2"))
(defconst *h4-book-expansion-first-count* (proof-sym "FIRST-COUNT" "ACL2"))
(defconst *h4-book-expansion-second-count* (proof-sym "SECOND-COUNT" "ACL2"))
(defconst *h4-book-expansion-expansion-order* (proof-sym "H4-EXPANDED-ORDINAL-ORDER" "ACL2"))

(defun h4-book-expansion-part (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h4-book-expansion-component (pieces literal)
  (let ((entry (assoc-equal literal pieces)))
    (if entry (cdr entry)
      '(:failure "failure" ""))))

(defun h4-book-expansion-copy-append (element count tail)
  (list *h4-book-flatten-append* (list *h4-book-expansion-copy* element count) tail))

(defun h4-book-expansion-copied-prefix (p element count tail test)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((copy-step (h4-book-updates-select-result
                     p (list *h4-book-expansion-copy* element count) test))
         (joined (h4-book-flatten-rewrite-argument
                  p (h4-book-expansion-copy-append element count tail) 1 copy-step))
         (prefix (h4-book-expansion-part copy-step 2))
         (call (h4-book-expansion-part joined 2)))
      (if (equal prefix *proof-false*)
          (proof-with-checked-results ((opened (h4-book-flatten-unfold-on-list p call prefix nil)))
            (proof-proof-chain proof joined (list opened)))
        (proof-with-checked-results
            ((opened (proof-proof-unfold proof call))
             (shape (proof-proof-fact proof "consp-cons"
                                      (seq-zip (list *library-x* *library-y*) (cdr prefix))))
             (opened-body (h4-book-expansion-part opened 2))
             (test (proof-term-at opened-body 1))
             (endp-step (proof-proof-unfold proof test))
             (atom-body (h4-book-expansion-part endp-step 2))
             (atom-step (proof-proof-unfold proof atom-body))
             (inverse-body (h4-book-expansion-part atom-step 2))
             (inverse (proof-proof-unfold proof inverse-body))
             (inverse-if (h4-book-expansion-part inverse 2))
             (chosen (proof-proof-select proof inverse-if shape))
             (stopped (proof-proof-chain proof endp-step (list atom-step inverse chosen)))
             (false-step (h4-book-order-false-value p stopped))
             (chosen (proof-proof-select proof opened-body false-step))
             (selected (proof-proof-chain proof opened (list chosen)))
             (head (library-library-axiom p "CAR-CONS" (cdr prefix)))
             (selected (proof-proof-rewrite proof selected head '(1 2 1)))
             (rest (library-library-axiom p "CDR-CONS" (cdr prefix)))
             (selected (proof-proof-rewrite proof selected rest '(1 2 2 1))))
          (proof-proof-chain proof joined (list selected)))))))

(defun h4-book-expansion-active-count (p positive)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first positive))
         (count (proof-term-at literal 1))
         (opened (proof-proof-unfold proof literal))
         (rewritten (proof-proof-rewrite proof positive opened '(1)))
         (bounds (h4-tactics-tactics-conjunct p rewritten))
         (stop (list *h4-book-arithmetic-zp* count))
         (stopped (proof-proof-assume proof stop t))
         (impossible (h4-tactics-tactics-normalize
                      p stop bounds (list *h4-book-arithmetic-zp* *proof-not*) nil nil))
         (value (h4-book-expansion-part impossible 2)))
      (if (not (equal value *proof-false*))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((rewritten (proof-proof-rewrite proof stopped impossible '(1)))
             (tidy (proof-proof-tidy proof rewritten)))
          (proof-proof-front proof tidy (proof-neg stop)))))))

(defun h4-book-expansion-converted-pair (p initial pieces)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((value (h4-book-expansion-part initial 2))
         (append-call (proof-list-of-length value 3))
         (copy-call (proof-list-of-length (cadr append-call) 3))
         (positive (h4-book-expansion-component
                    pieces (list *h4-book-order-posp* (caddr copy-call))))
         (active (h4-book-expansion-active-count p positive))
         (prefix (h4-book-expansion-copied-prefix
                  p (cadr copy-call) (caddr copy-call) (caddr append-call) active)))
      (proof-proof-chain proof initial (list prefix)))))

(defun h4-book-expansion-e0-irreflexive-hypothesis (p shape goal index substitution)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((builtin (library-library-builtin p index *library-x*))
         (smaller (proof-proof-discharge proof builtin shape))
         (instance (proof-subst goal (list (cons (caar substitution) (cadar substitution)))))
         (measure (proof-step-first smaller))
         (assumed (proof-proof-assume proof (proof-ite measure instance *proof-true*) t)))
      (proof-proof-prove-if proof assumed smaller))))

(defun h4-book-expansion-e0-irreflexive-pair (shape p goal term bindings)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((head (h4-book-expansion-e0-irreflexive-hypothesis p shape goal 2 (car bindings)))
         (tail (h4-book-expansion-e0-irreflexive-hypothesis p shape goal 3 (cadr bindings)))
         (unfolded (h4-book-order-order-view p term (list shape) nil))
         (value (h4-book-expansion-part unfolded 2))
         (reduced (h4-tactics-tactics-normalize p value nil nil (list head tail) nil)))
      (proof-proof-chain proof unfolded (list reduced)))))

(defun h4-book-expansion-e0-irreflexive-atom (shape p term)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((unfolded (h4-book-order-order-view p term (list shape) nil))
         (value (h4-book-expansion-part unfolded 2))
         (argument (proof-term-at value 1))
         (reflexive (h4-book-order-primitive-reflexive-value p argument)))
      (proof-proof-chain proof unfolded (list reflexive)))))

(defun h4-book-expansion-e0-irreflexive (p)
  (let* ((proof (library-library-proof p))
         (term (list *h4-book-expansion-e0-less* *library-x* *library-x*))
         (goal (proof-eq term *proof-false*))
         (bindings (list (list (list *library-x* (list *library-car* *library-x*)))
                         (list (list *library-x* (list *library-cdr* *library-x*)))))
         (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((ordinal (library-library-builtin p 1 *library-x*))
         (pair (proof-proof-assume proof test t))
         (yes (h4-book-expansion-e0-irreflexive-pair pair p goal term bindings))
         (atom-case (proof-proof-assume proof test nil))
         (no (h4-book-expansion-e0-irreflexive-atom atom-case p term))
         (cases (h4-tactics-tactics-case-of p goal test yes no)))
      (proof-proof-induct proof ordinal cases goal (list *library-count* *library-x*) bindings))))

(defun h4-book-expansion-prefix-boundary (element tail)
  (let ((head (list *library-car* tail)))
    (proof-ite (list *proof-consp* tail)
               (proof-ite (list *h4-book-expansion-e0-less* head element)
                          (proof-ite (proof-neg (list *h4-book-expansion-e0-less* element head))
                                     (proof-neg (proof-eq element head)) *proof-false*)
                          *proof-false*)
               *proof-true*)))

(defun h4-book-expansion-e0-view-rewrite (proof lifted equations index)
  (declare (xargs :measure (acl2-count equations)))
  (if (or (failure-p lifted) (endp equations))
      lifted
    (h4-book-expansion-e0-view-rewrite
     proof (proof-proof-rewrite proof lifted (car equations) (list 1 2 index))
     (cdr equations) (1+ index))))

(defun h4-book-expansion-e0-view (p term argument-equations evidence rewrites provide)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((initial (proof-proof-reflexive proof term))
         (lifted (h4-book-expansion-e0-view-rewrite proof initial argument-equations 1))
         (call (h4-book-expansion-part lifted 2))
         (opened (proof-proof-unfold proof call))
         (value (h4-book-expansion-part opened 2))
         (reduced (h4-tactics-tactics-normalize p value evidence (list *proof-not*) rewrites provide)))
      (proof-proof-chain proof lifted (list opened reduced)))))

(defun h4-book-expansion-predecessor-comparison (p first second integers)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((previous (library-library-comparison p (h4-book-arithmetic-predecessor first)
                                                (h4-book-arithmetic-predecessor second) integers))
         (current (library-library-comparison p first second integers))
         (previous-value (h4-book-expansion-part previous 2))
         (previous-delta (proof-term-at previous-value 2))
         (current-value (h4-book-expansion-part current 2))
         (current-delta (proof-term-at current-value 2))
         (delta (library-library-linear-equal p previous-delta current-delta integers))
         (rewritten (proof-proof-rewrite proof previous delta '(1 2 2)))
         (reversed (proof-proof-symmetric proof current)))
      (proof-proof-chain proof rewritten (list reversed)))))

(defun h4-book-expansion-opposite-order (p strict)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first strict))
         (parts (proof-list-of-length literal 3))
         (backward (list *proof-ordinal-less* (caddr parts) (cadr parts)))
         (assumed (proof-proof-assume proof backward t))
         (loop-step (h4-book-order-strict-chain p strict assumed))
         (self (proof-proof-fact proof *h4-book-order-order-self*
                                 (list (list *library-x* (cadr parts)))))
         (false-step (h4-book-order-false-value p self))
         (impossible (proof-proof-cut proof loop-step false-step)))
      (proof-proof-front proof impossible (proof-neg backward)))))

(defun h4-book-expansion-smaller-field-project (p subject field shape tail-shape field-head)
  (let ((proof (library-library-proof p)))
    (if (equal field-head *h4-book-order-rest*)
        (proof-with-checked-results ((projection (proof-proof-unfold proof field)))
          (list (list *library-cdr* subject) projection))
      (proof-with-checked-results ((field-subject (proof-term-at field 1)))
        (if (equal field-subject subject)
            (proof-with-checked-results ((view (h4-book-order-order-view p field (list shape) nil)))
              (list (list *library-car* (list *library-car* subject)) view))
          (proof-with-checked-results
              ((initial (h4-book-order-order-view p field (list tail-shape) nil))
               (rest (proof-proof-unfold proof (list *h4-book-order-rest* subject)))
               (projection (proof-proof-rewrite proof initial rest '(1 2 1 1))))
            (list (list *library-car* (list *library-car* (list *library-cdr* subject)))
                  projection)))))))

(defun h4-book-expansion-smaller-field (p subject field shape tail-shape)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((head (proof-term-at field 0))
         (project (h4-book-expansion-smaller-field-project p subject field shape tail-shape head))
         (goal (list *proof-ordinal-less* (list *library-count* (car project))
                     (list *library-count* subject)))
         (available (descent-hypotheses-init p nil (list shape)))
         (less (descent-selector-decrease p goal available))
         (reversed (proof-proof-symmetric proof (cadr project))))
      (proof-proof-rewrite proof (car less) reversed '(1 1 1)))))

(defun h4-book-expansion-ordinal-expansion-ordinal (view) (nth 1 view))
(defun h4-book-expansion-ordinal-expansion-subject (view) (nth 2 view))
(defun h4-book-expansion-ordinal-expansion-shape (view) (nth 3 view))
(defun h4-book-expansion-ordinal-expansion-is-pair (view) (nth 4 view))
(defun h4-book-expansion-ordinal-expansion-converted (view) (nth 5 view))
(defun h4-book-expansion-ordinal-expansion-power (view) (nth 6 view))
(defun h4-book-expansion-ordinal-expansion-count (view) (nth 7 view))
(defun h4-book-expansion-ordinal-expansion-rest (view) (nth 8 view))
(defun h4-book-expansion-ordinal-expansion-element (view) (nth 9 view))
(defun h4-book-expansion-ordinal-expansion-suffix (view) (nth 10 view))
(defun h4-book-expansion-ordinal-expansion-opened (view) (nth 11 view))
(defun h4-book-expansion-ordinal-expansion-pieces (view) (nth 12 view))
(defun h4-book-expansion-ordinal-expansion-spine (view) (nth 13 view))

(defun h4-book-expansion-ordinal-expansion-init (p ordinal shape)
  (proof-with-checked-results
      ((subject (h4-book-expansion-part ordinal 1))
       (shape-literal (proof-step-first shape))
       (is-pair (proof-is-call shape-literal *proof-consp*))
       (converted (list *h4-book-expansion-ctoa* subject))
       (power (list *h4-book-order-exponent* subject))
       (count (list *h4-book-order-coefficient* subject))
       (rest (list *h4-book-order-rest* subject))
       (element (list *h4-book-expansion-ctoa* power))
       (suffix (list *h4-book-expansion-ctoa* rest))
       (opened (h4-book-order-order-view p converted (list shape) nil))
       (pieces (if is-pair (h4-book-order-ordinal-components p ordinal shape) nil))
       (spine (if is-pair (h4-book-expansion-converted-pair p opened pieces) opened)))
    (list :h4-ordinal-expansion ordinal subject shape is-pair
          converted power count rest element suffix opened pieces spine)))

(defun h4-book-expansion-ordinal-expansion-rational-if-finite (view p)
  (let ((proof (library-library-proof p))
        (ordinal (h4-book-expansion-ordinal-expansion-ordinal view))
        (subject (h4-book-expansion-ordinal-expansion-subject view))
        (shape (h4-book-expansion-ordinal-expansion-shape view)))
    (proof-with-checked-results
        ((literal (proof-step-first ordinal))
         (opened (h4-book-order-order-view p literal (list shape) nil))
         (natural (proof-proof-rewrite proof ordinal opened '(1)))
         (integral (library-library-cite p "NATURAL-INTEGER" (list subject) (list natural)))
         (axiom (library-library-axiom p "INTEGER-IMPLIES-RATIONAL" (list subject)))
         (evidence (library-library-type-of p subject (list integral))))
      (h4-tactics-tactics-modus-ponens p axiom evidence))))

(defun h4-book-expansion-ordinal-expansion-power-type (view)
  (h4-book-expansion-component (h4-book-expansion-ordinal-expansion-pieces view)
                               (list *proof-ordinalp* (h4-book-expansion-ordinal-expansion-power view))))

(defun h4-book-expansion-ordinal-expansion-rest-type (view)
  (h4-book-expansion-component (h4-book-expansion-ordinal-expansion-pieces view)
                               (list *proof-ordinalp* (h4-book-expansion-ordinal-expansion-rest view))))

(defun h4-book-expansion-ordinal-expansion-natural-count (view p)
  (let ((proof (library-library-proof p))
        (count (h4-book-expansion-ordinal-expansion-count view)))
    (proof-with-checked-results
        ((positive (h4-book-expansion-component (h4-book-expansion-ordinal-expansion-pieces view)
                                                (list *h4-book-order-posp* count)))
         (literal (proof-step-first positive))
         (opened (proof-proof-unfold proof literal))
         (rewritten (proof-proof-rewrite proof positive opened '(1)))
         (bounds (h4-tactics-tactics-conjunct p rewritten))
         (nonnegative (library-library-cite p "POSITIVE-NONNEGATIVE" (list count) bounds)))
      (library-library-cite p "NATURAL-FROM-BOUNDS" (list count) (list (car bounds) nonnegative)))))

(defun h4-book-expansion-comparison-forms (left right)
  (proof-eq (list *h4-book-expansion-e0-less* (list *h4-book-expansion-ctoa* left)
                  (list *h4-book-expansion-ctoa* right))
            (list *proof-ordinal-less* left right)))

(defun h4-book-expansion-expansion-shape-order (guard goal)
  (and (proof-is-call goal *proof-equal*)
    (proof-with-checked-results ((expected (proof-term-at goal 2)))
      (and (proof-is-call expected *proof-ordinal-less*)
        (proof-with-checked-results ((subjects (proof-list-of-length (cdr expected) 2)))
          (let ((left (car subjects)) (right (cadr subjects)))
            (and (not (proof-compound left)) (not (proof-compound right))
                 (equal goal (h4-book-expansion-comparison-forms left right))
                 (equal guard (proof-ite (list *proof-ordinalp* left)
                                         (list *proof-ordinalp* right) *proof-false*))
                 subjects)))))))

(defun h4-book-expansion-expansion-shape (formula)
  (and (proof-is-call formula *library-implies*)
    (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2)))
      (let ((guard (car parts)) (goal (cadr parts)))
        (if (proof-is-call guard *proof-ordinalp*)
            (proof-with-checked-results ((subject (proof-term-at guard 1)))
              (if (and (equal goal (list *h4-book-expansion-e0-ordinal*
                                         (list *h4-book-expansion-ctoa* subject)))
                       (not (proof-compound subject)))
                  (list subject)
                (h4-book-expansion-expansion-shape-order guard goal)))
          (h4-book-expansion-expansion-shape-order guard goal))))))

(defun h4-book-expansion-compare-expansions (p theorem first second)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((left (h4-book-expansion-part first 1))
         (right (h4-book-expansion-part second 1))
         (rule (proof-proof-instantiate proof theorem (list (list *library-x* left)
                                                            (list *library-y* right))))
         (evidence (h4-book-division-conjunction p (list first second)))
         (concluded (h4-tactics-tactics-modus-ponens p rule evidence)))
      (h4-tactics-tactics-conjunct p concluded))))

(defun h4-book-expansion-expansion-proofs-init ()
  (list :h4-expansion-proofs nil nil))

(defun h4-book-expansion-expansion-proofs-reflexive (expansions)
  (cadr expansions))

(defun h4-book-expansion-expansion-proofs-order (expansions)
  (caddr expansions))

(defun h4-book-expansion-copy-comparison-both-active
    (tests opened p formula substitutions boundaries comparison reflexive provide integers)
  (let ((proof (library-library-proof p))
        (element *h4-book-expansion-element*)
        (n *h4-book-expansion-first-count*)
        (m *h4-book-expansion-second-count*))
    (proof-with-checked-results
        ((builtin (library-library-builtin p 9 n))
         (smaller (proof-proof-discharge proof builtin (car tests)))
         (child (proof-subst formula (list (cons n (cadar substitutions))
                                          (cons m (cadadr substitutions)))))
         (decrease (proof-step-first smaller))
         (assumed (proof-proof-assume proof (proof-ite decrease child *proof-true*) t))
         (induction (proof-proof-prove-if proof assumed smaller))
         (natural-n (proof-proof-use proof *h4-book-updates-predecessor-natural*
                                     (list (list *library-x* n)) (list (car tests))))
         (natural-m (proof-proof-use proof *h4-book-updates-predecessor-natural*
                                     (list (list *library-x* m)) (list (cadr tests))))
         (guard (h4-book-division-conjunction p (cons natural-n (cons natural-m boundaries))))
         (learned (h4-tactics-tactics-modus-ponens p induction guard))
         (self (proof-proof-instantiate proof reflexive (list (list *library-x* element))))
         (physical (h4-book-expansion-e0-view p comparison opened nil (list self) provide))
         (restored (proof-proof-chain proof physical (list learned)))
         (same (proof-proof-use proof *h4-book-updates-equal-predecessors*
                                (list (list *library-x* n) (list *library-y* m)) integers))
         (restored (proof-proof-rewrite proof restored same '(1 2 1)))
         (shifted (h4-book-expansion-predecessor-comparison p n m integers)))
      (proof-proof-rewrite proof restored shifted '(1 2 3)))))

(defun h4-book-expansion-copy-comparison-one-active-branch
    (shape p boundary comparison opened provide arithmetic)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first shape))
         (boundary-facts (if (proof-is-call literal *proof-consp*)
                             (proof-with-checked-results
                                 ((conjuncts (proof-proof-prove-if proof boundary shape)))
                               (h4-book-list-types-conjunct-proofs p conjuncts))
                           nil))
         (physical (h4-book-expansion-e0-view
                    p comparison opened (cons shape boundary-facts) nil provide))
         (expected (proof-proof-symmetric proof arithmetic)))
      (proof-proof-chain proof physical (list expected)))))

(defun h4-book-expansion-copy-comparison-one-active
    (tests opened left-active p result goal naturals boundaries comparison provide)
  (let* ((proof (library-library-proof p))
         (n *h4-book-expansion-first-count*)
         (m *h4-book-expansion-second-count*)
         (count (if left-active n m))
         (other (if left-active m n))
         (other-natural (if left-active (cadr naturals) (car naturals)))
         (active-test (if left-active (car tests) (cadr tests)))
         (stop-test (if left-active (cadr tests) (car tests))))
    (proof-with-checked-results
        ((past-zero (proof-proof-use proof (proof-sym "H4-COUNTDOWN-POSITIVE" "ACL2")
                                     (list (list *library-x* count)) (list active-test)))
         (zero (proof-proof-use proof *h4-book-arithmetic-natural-countdown-zero*
                                (list (list *library-x* other)) (list other-natural stop-test)))
         (reversed (proof-proof-symmetric proof zero))
         (strict (proof-proof-rewrite proof past-zero reversed '(1 1)))
         (distinct (h4-book-order-order-unequal p strict :primitive))
         (distinct (if left-active (h4-book-order-reflected-test p distinct) distinct))
         (value (if left-active
                    (proof-with-checked-results
                        ((nonnegative (library-library-cite p "NATURAL-NONNEGATIVE"
                                                            (list n) (list (car naturals))))
                         (reversed (proof-proof-symmetric proof zero))
                         (not-less (proof-proof-rewrite proof nonnegative reversed '(1 1 2))))
                      (h4-tactics-tactics-nil-value p not-less))
                  (proof-with-checked-results
                      ((boolean (proof-proof-fact proof "booleanp-<"
                                                  (list (list *library-x* n) (list *library-y* m)))))
                    (h4-book-order-true-boolean-value p strict boolean))))
         (arithmetic (h4-tactics-tactics-normalize
                      p result (list distinct) (list *proof-not*) (list value) nil)))
      (let* ((tail (if left-active *library-y* *library-x*))
             (boundary (if left-active (cadr boundaries) (car boundaries)))
             (test (list *proof-consp* tail)))
        (proof-with-checked-results
            ((pair (proof-proof-assume proof test t))
             (yes (h4-book-expansion-copy-comparison-one-active-branch
                   pair p boundary comparison opened provide arithmetic))
             (atom-case (proof-proof-assume proof test nil))
             (no (h4-book-expansion-copy-comparison-one-active-branch
                  atom-case p boundary comparison opened provide arithmetic)))
          (h4-tactics-tactics-case-of p goal test yes no))))))

(defun h4-book-expansion-copy-comparison-stopped (p tests opened naturals comparison result)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((zero-n (proof-proof-use proof *h4-book-arithmetic-natural-countdown-zero*
                                  (list (list *library-x* *h4-book-expansion-first-count*))
                                  (list (car naturals) (car tests))))
         (zero-m (proof-proof-use proof *h4-book-arithmetic-natural-countdown-zero*
                                  (list (list *library-x* *h4-book-expansion-second-count*))
                                  (list (cadr naturals) (cadr tests))))
         (original (proof-proof-reflexive proof comparison))
         (original (h4-book-expansion-e0-view-rewrite proof original opened 1))
         (reduced (h4-tactics-tactics-normalize p result nil nil (list zero-n zero-m) nil))
         (reversed (proof-proof-symmetric proof reduced)))
      (proof-proof-chain proof original (list reversed)))))

(defun h4-book-expansion-copy-comparison-choose-both
    (first second p formula substitutions comparison result goal naturals boundaries reflexive provide integers)
  (let ((element *h4-book-expansion-element*)
        (tests (list first second)))
    (proof-with-checked-results
        ((opened-n (h4-book-expansion-copied-prefix
                    p element *h4-book-expansion-first-count* *library-x* first))
         (opened-m (h4-book-expansion-copied-prefix
                    p element *h4-book-expansion-second-count* *library-y* second))
         (first-literal (proof-step-first first))
         (second-literal (proof-step-first second)))
      (let ((opened (list opened-n opened-m))
            (left-active (not (proof-is-call first-literal *h4-book-arithmetic-zp*)))
            (right-active (not (proof-is-call second-literal *h4-book-arithmetic-zp*))))
        (proof-with-checked-results
            ((result-proof
              (cond
               ((and left-active right-active)
                (h4-book-expansion-copy-comparison-both-active
                 tests opened p formula substitutions boundaries comparison reflexive provide integers))
               ((or left-active right-active)
                (h4-book-expansion-copy-comparison-one-active
                 tests opened left-active p result goal naturals boundaries comparison provide))
               (t (h4-book-expansion-copy-comparison-stopped p tests opened naturals comparison result)))))
          (h4-tactics-tactics-imply p formula result-proof))))))

(defun h4-book-expansion-copy-comparison-left-right
    (second first p formula substitutions comparison result goal naturals boundaries reflexive provide integers)
  (h4-book-expansion-copy-comparison-choose-both
   first second p formula substitutions comparison result goal naturals boundaries reflexive provide integers))

(defun h4-book-expansion-copy-comparison-left
    (first p formula substitutions comparison result goal naturals boundaries reflexive provide integers)
  (let ((proof (library-library-proof p))
        (test (list *h4-book-arithmetic-zp* *h4-book-expansion-second-count*)))
    (proof-with-checked-results
        ((stopped (proof-proof-assume proof test t))
         (yes (h4-book-expansion-copy-comparison-left-right
               stopped first p formula substitutions comparison result goal naturals boundaries
               reflexive provide integers))
         (active (proof-proof-assume proof test nil))
         (no (h4-book-expansion-copy-comparison-left-right
              active first p formula substitutions comparison result goal naturals boundaries
              reflexive provide integers)))
      (h4-tactics-tactics-case-of p formula test yes no))))

(defun h4-book-expansion-copy-comparison-integer (p natural)
  (proof-with-checked-results ((count (h4-book-expansion-part natural 1)))
    (library-library-cite p "NATURAL-INTEGER" (list count) (list natural))))

(defun h4-book-expansion-copy-comparison (p reflexive)
  (let* ((proof (library-library-proof p))
         (a *h4-book-expansion-element*)
         (n *h4-book-expansion-first-count*)
         (m *h4-book-expansion-second-count*)
         (comparison (list *h4-book-expansion-e0-less*
                           (h4-book-expansion-copy-append a n *library-x*)
                           (h4-book-expansion-copy-append a m *library-y*)))
         (result (proof-ite (proof-eq n m) (list *h4-book-expansion-e0-less* *library-x* *library-y*)
                            (library-lt n m)))
         (goal (proof-eq comparison result))
         (guard (proof-ite (list *library-natp* n)
                           (proof-ite (list *library-natp* m)
                                      (proof-ite (h4-book-expansion-prefix-boundary a *library-x*)
                                                 (h4-book-expansion-prefix-boundary a *library-y*)
                                                 *proof-false*)
                                      *proof-false*)
                           *proof-false*))
         (formula (list *library-implies* guard goal))
         (test (list *h4-book-arithmetic-zp* n))
         (substitutions (list (list n (h4-book-arithmetic-predecessor n))
                              (list m (h4-book-arithmetic-predecessor m)))))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof guard t))
         (parts (h4-book-list-types-conjunct-proofs p assumed))
         (parts (proof-list-of-length parts 4))
         (integer-n (h4-book-expansion-copy-comparison-integer p (car parts)))
         (integer-m (h4-book-expansion-copy-comparison-integer p (cadr parts)))
         (provide (h4-book-finite-reduction-provider p))
         (stopped (proof-proof-assume proof test t))
         (yes (h4-book-expansion-copy-comparison-left
               stopped p formula substitutions comparison result goal (take 2 parts) (cddr parts)
               reflexive provide (list integer-n integer-m)))
         (active (proof-proof-assume proof test nil))
         (no (h4-book-expansion-copy-comparison-left
              active p formula substitutions comparison result goal (take 2 parts) (cddr parts)
              reflexive provide (list integer-n integer-m)))
         (cases (h4-tactics-tactics-case-of p formula test yes no))
         (ordinal (library-library-builtin p 1 n)))
      (proof-proof-induct proof ordinal cases formula (list *library-count* n) (list substitutions)))))

(defun h4-book-expansion-expansion-orders-compare-child
    (index left-type right-type tail-shape p substitutions formula shape)
  (let ((proof (library-library-proof p))
        (bindings (nth index substitutions)))
    (proof-with-checked-results
        ((smaller (h4-book-expansion-smaller-field p *library-x* (cadar bindings) shape tail-shape))
         (instance (proof-subst formula (list (cons *library-x* (cadar bindings))
                                             (cons *library-y* (cadadr bindings)))))
         (measure (proof-step-first smaller))
         (assumed (proof-proof-assume proof (proof-ite measure instance *proof-true*) t))
         (induction (proof-proof-prove-if proof assumed smaller))
         (evidence (h4-book-division-conjunction p (list left-type right-type)))
         (result (h4-tactics-tactics-modus-ponens p induction evidence)))
      (h4-tactics-tactics-conjunct p result))))

(defun h4-book-expansion-prefix-bound-comparisons (tail shape p comparisons)
  (proof-with-checked-results
      ((power-type (h4-book-expansion-ordinal-expansion-power-type tail)))
    (case (car comparisons)
      (:left
       (h4-book-expansion-expansion-orders-compare-child
        2 power-type (nth 1 comparisons) shape p (nth 2 comparisons)
        (nth 3 comparisons) (nth 4 comparisons)))
      (:right
       (proof-with-checked-results
           ((result (h4-book-expansion-expansion-orders-compare-child
                     3 (nth 1 comparisons) power-type nil p (nth 2 comparisons)
                     (nth 3 comparisons) (nth 4 comparisons))))
         (reverse result)))
      (otherwise
       (h4-book-expansion-compare-expansions p (nth 1 comparisons) power-type (nth 2 comparisons))))))

(defun h4-book-expansion-prefix-bound-atom (shape p suffix goal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (h4-book-order-order-view p suffix (list shape) nil))
         (reversed (proof-proof-symmetric proof opened))
         (negative (proof-proof-rewrite proof shape reversed '(1 1 1))))
      (h4-tactics-tactics-establish p goal (list negative) nil nil nil))))

(defun h4-book-expansion-prefix-bound-pair (shape p ordinal comparisons less reflexive suffix)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((tail (h4-book-expansion-ordinal-expansion-init p ordinal shape))
         (bounds (h4-book-expansion-prefix-bound-comparisons tail shape p comparisons))
         (bounds (proof-list-of-length bounds 2))
         (direct (proof-proof-transport proof less (car bounds)))
         (opposite (h4-book-expansion-opposite-order p less))
         (backward (proof-proof-symmetric proof (cadr bounds)))
         (reverse (proof-proof-rewrite proof opposite backward '(1 1)))
         (different (h4-book-order-order-unequal p direct (list :instantiate reflexive)))
         (negative (h4-book-order-reflected-test p different))
         (combined (h4-book-division-conjunction p (list direct reverse negative)))
         (pair-eq (h4-book-expansion-part (h4-book-expansion-ordinal-expansion-spine tail) 2))
         (head (library-library-axiom p "CAR-CONS" (cdr pair-eq)))
         (access (h4-book-flatten-rewrite-argument
                  p (list *library-car* suffix) 1 (h4-book-expansion-ordinal-expansion-spine tail)))
         (head (proof-proof-chain proof access (list head)))
         (reversed (proof-proof-symmetric proof head))
         (combined (proof-proof-rewrite-first proof combined reversed)))
      (h4-tactics-tactics-guarded p (list *proof-consp* suffix) combined t))))

(defun h4-book-expansion-prefix-bound (p ordinal power less comparisons reflexive)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((subject (h4-book-expansion-part ordinal 1)))
      (let* ((suffix (list *h4-book-expansion-ctoa* subject))
             (element (list *h4-book-expansion-ctoa* power))
             (goal (h4-book-expansion-prefix-boundary element suffix))
             (test (list *proof-consp* subject)))
        (proof-with-checked-results
            ((pair (proof-proof-assume proof test t))
             (yes (h4-book-expansion-prefix-bound-pair pair p ordinal comparisons less reflexive suffix))
             (atom-case (proof-proof-assume proof test nil))
             (no (h4-book-expansion-prefix-bound-atom atom-case p suffix goal)))
          (h4-tactics-tactics-case-of p goal test yes no))))))

(defun h4-book-expansion-expansion-orders-compare-base (left right p evidence provide)
  (let ((proof (library-library-proof p))
        (original (h4-book-expansion-comparison-forms
                   (h4-book-expansion-ordinal-expansion-subject left)
                   (h4-book-expansion-ordinal-expansion-subject right))))
    (proof-with-checked-results
        ((actual (h4-book-expansion-e0-view
                  p (cadr original) (list (h4-book-expansion-ordinal-expansion-spine left)
                                         (h4-book-expansion-ordinal-expansion-spine right))
                  evidence nil provide))
         (expected (h4-book-order-order-view p (caddr original) evidence nil))
         (reversed (proof-proof-symmetric proof expected)))
      (proof-proof-chain proof actual (list reversed)))))

(defun h4-book-expansion-expansion-orders-compare-unequal-side-order-evidence
    (p logical other equality opposite-comparison reflexive)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((literal (proof-step-first logical)))
      (if (proof-is-call literal *proof-not*)
          (proof-with-checked-results
              ((reversed (proof-proof-symmetric proof equality))
               (physical (proof-proof-rewrite proof logical reversed '(1 1)))
               (flipped (proof-proof-transport proof other opposite-comparison))
               (different (h4-book-order-order-unequal p flipped (list :instantiate reflexive)))
               (negative (h4-book-order-reflected-test p different))
               (value (h4-tactics-tactics-nil-value p logical)))
            (list (list physical negative) value))
        (proof-with-checked-results
            ((physical (proof-proof-transport proof logical equality))
             (value (h4-book-order-true-order-value p logical)))
          (list (list physical) value))))))

(defun h4-book-expansion-expansion-orders-compare-unequal-side-order-finish
    (left right logical other equality opposite-comparison different p reflexive evidence provide)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((physical (h4-book-expansion-expansion-orders-compare-unequal-side-order-evidence
                    p logical other equality opposite-comparison reflexive))
         (original (h4-book-expansion-comparison-forms
                    (h4-book-expansion-ordinal-expansion-subject left)
                    (h4-book-expansion-ordinal-expansion-subject right)))
         (actual (h4-book-expansion-e0-view
                  p (cadr original) (list (h4-book-expansion-ordinal-expansion-spine left)
                                         (h4-book-expansion-ordinal-expansion-spine right))
                  (append evidence (car physical)) nil provide))
         (expected (h4-book-order-order-view p (caddr original) (append evidence (list different)) nil))
         (composed (proof-proof-chain proof expected (list (cadr physical))))
         (reversed (proof-proof-symmetric proof composed)))
      (proof-proof-chain proof actual (list reversed)))))

(defun h4-book-expansion-expansion-orders-compare-unequal-side-order
    (direction p comparison sign x y power-types power-order reflexive evidence provide)
  (proof-with-checked-results
      ((literal (proof-step-first direction))
       (opposite (if (equal literal comparison)
                     (h4-book-expansion-opposite-order p direction)
                   (h4-book-order-order-formula
                    p (list *proof-ordinal-less* (h4-book-expansion-ordinal-expansion-power y)
                            (h4-book-expansion-ordinal-expansion-power x))
                    (cons sign (cons direction power-types)))))
       (first (h4-book-expansion-expansion-orders-compare-unequal-side-order-finish
               x y direction opposite (car power-order) (cadr power-order) sign
               p reflexive evidence provide))
       (inverted (h4-book-order-reflected-test p sign))
       (second (h4-book-expansion-expansion-orders-compare-unequal-side-order-finish
                y x opposite direction (cadr power-order) (car power-order) inverted
                p reflexive evidence provide)))
    (h4-book-division-conjunction p (list first second))))

(defun h4-book-expansion-expansion-orders-compare-unequal
    (sign p goal x y power-types power-order reflexive evidence provide)
  (let ((proof (library-library-proof p))
        (comparison (list *proof-ordinal-less* (h4-book-expansion-ordinal-expansion-power x)
                          (h4-book-expansion-ordinal-expansion-power y))))
    (proof-with-checked-results
        ((strict (proof-proof-assume proof comparison t))
         (yes (h4-book-expansion-expansion-orders-compare-unequal-side-order
               strict p comparison sign x y power-types power-order reflexive evidence provide))
         (not-strict (proof-proof-assume proof comparison nil))
         (no (h4-book-expansion-expansion-orders-compare-unequal-side-order
              not-strict p comparison sign x y power-types power-order reflexive evidence provide)))
      (h4-tactics-tactics-case-of p goal comparison yes no))))

(defun h4-book-expansion-expansion-orders-compare-equal-rank-operand
    (p stage operand is-y element-eq index)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((stage (proof-proof-rewrite proof stage (h4-book-expansion-ordinal-expansion-opened operand)
                                    (list 1 2 index))))
      (if is-y
          (proof-with-checked-results ((reversed (proof-proof-symmetric proof element-eq)))
            (proof-proof-rewrite proof stage reversed (list 1 2 index 1 1)))
        stage))))

(defun h4-book-expansion-expansion-orders-compare-equal-rank-compare-count
    (sign p original evidence equal-power actual)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((expected (h4-book-order-order-view p (caddr original)
                                           (append evidence (list equal-power sign)) nil))
         (value (h4-book-expansion-part actual 2))
         (reduced (h4-tactics-tactics-normalize p value (list sign) nil nil nil))
         (reversed (proof-proof-symmetric proof expected)))
      (proof-proof-chain proof actual (list reduced reversed)))))

(defun h4-book-expansion-expansion-orders-compare-equal-rank
    (left right counts boundaries equal-power rest-comparison p x left-is-y element-eq runs evidence)
  (let ((proof (library-library-proof p))
        (original (h4-book-expansion-comparison-forms
                   (h4-book-expansion-ordinal-expansion-subject left)
                   (h4-book-expansion-ordinal-expansion-subject right)))
        (n (h4-book-expansion-ordinal-expansion-count left))
        (m (h4-book-expansion-ordinal-expansion-count right)))
    (proof-with-checked-results
        ((stage (proof-proof-reflexive proof (cadr original)))
         (stage (h4-book-expansion-expansion-orders-compare-equal-rank-operand
                 p stage left left-is-y element-eq 1))
         (stage (h4-book-expansion-expansion-orders-compare-equal-rank-operand
                 p stage right (not left-is-y) element-eq 2))
         (rule (proof-proof-instantiate
                proof runs (list (list *h4-book-expansion-element*
                                       (h4-book-expansion-ordinal-expansion-element x))
                                (list *library-x* (h4-book-expansion-ordinal-expansion-suffix left))
                                (list *library-y* (h4-book-expansion-ordinal-expansion-suffix right))
                                (list *h4-book-expansion-first-count* n)
                                (list *h4-book-expansion-second-count* m))))
         (available (h4-book-division-conjunction p (append counts boundaries)))
         (value (h4-tactics-tactics-modus-ponens p rule available))
         (actual (proof-proof-chain proof stage (list value)))
         (actual (proof-proof-rewrite proof actual rest-comparison '(1 2 2)))
         (test (proof-eq n m))
         (same (proof-proof-assume proof test t))
         (yes (h4-book-expansion-expansion-orders-compare-equal-rank-compare-count
               same p original evidence equal-power actual))
         (different (proof-proof-assume proof test nil))
         (no (h4-book-expansion-expansion-orders-compare-equal-rank-compare-count
              different p original evidence equal-power actual)))
      (h4-tactics-tactics-case-of p original test yes no))))

(defun h4-book-expansion-expansion-orders-compare-equal
    (sign p x y power-types formula substitutions reflexive runs evidence)
  (let* ((proof (library-library-proof p))
         (shape (h4-book-expansion-ordinal-expansion-shape x))
         (ex-x (h4-book-expansion-ordinal-expansion-power x))
         (ex-y (h4-book-expansion-ordinal-expansion-power y))
         (tail-power-x (list *h4-book-order-exponent* (h4-book-expansion-ordinal-expansion-rest x)))
         (tail-power-y (list *h4-book-order-exponent* (h4-book-expansion-ordinal-expansion-rest y))))
    (proof-with-checked-results
        ((element-eq (h4-book-flatten-rewrite-argument
                      p (h4-book-expansion-ordinal-expansion-element x) 1 sign))
         (bound-x (h4-book-expansion-component (h4-book-expansion-ordinal-expansion-pieces x)
                                               (list *proof-ordinal-less* tail-power-x ex-x)))
         (bound-x (proof-proof-rewrite proof bound-x sign '(1 2)))
         (bound-y (h4-book-expansion-component (h4-book-expansion-ordinal-expansion-pieces y)
                                               (list *proof-ordinal-less* tail-power-y ex-y)))
         (reversed (proof-proof-symmetric proof sign))
         (bound-y (proof-proof-rewrite proof bound-y reversed '(1 2)))
         (rest-x (h4-book-expansion-ordinal-expansion-rest-type x))
         (bx (h4-book-expansion-prefix-bound
              p rest-x ex-y bound-x (list :left (cadr power-types) substitutions formula shape) reflexive))
         (reversed (proof-proof-symmetric proof element-eq))
         (bx (proof-proof-rewrite-first proof bx reversed))
         (rest-y (h4-book-expansion-ordinal-expansion-rest-type y))
         (by (h4-book-expansion-prefix-bound
              p rest-y ex-x bound-y (list :right (car power-types) substitutions formula shape) reflexive))
         (rest-order (h4-book-expansion-expansion-orders-compare-child
                      1 rest-x rest-y nil p substitutions formula shape))
         (nx (h4-book-expansion-ordinal-expansion-natural-count x p))
         (ny (h4-book-expansion-ordinal-expansion-natural-count y p))
         (first (h4-book-expansion-expansion-orders-compare-equal-rank
                 x y (list nx ny) (list bx by) sign (car rest-order) p x nil element-eq runs evidence))
         (reflected (proof-proof-symmetric proof sign))
         (second (h4-book-expansion-expansion-orders-compare-equal-rank
                  y x (list ny nx) (list by bx) reflected (cadr rest-order) p x t element-eq runs evidence)))
      (h4-book-division-conjunction p (list first second)))))

(defun h4-book-expansion-expansion-orders-compare (x y p substitutions formula goal reflexive runs provide)
  (let* ((proof (library-library-proof p))
         (shape-x (h4-book-expansion-ordinal-expansion-shape x))
         (shape-y (h4-book-expansion-ordinal-expansion-shape y))
         (pair-x (h4-book-expansion-ordinal-expansion-is-pair x))
         (pair-y (h4-book-expansion-ordinal-expansion-is-pair y))
         (evidence (list shape-x shape-y)))
    (if (and pair-x pair-y)
        (proof-with-checked-results
            ((x-type (h4-book-expansion-ordinal-expansion-power-type x))
             (y-type (h4-book-expansion-ordinal-expansion-power-type y))
             (power-types (list x-type y-type))
             (power-order (h4-book-expansion-expansion-orders-compare-child
                           0 x-type y-type nil p substitutions formula shape-x))
             (test (proof-eq (h4-book-expansion-ordinal-expansion-power x)
                             (h4-book-expansion-ordinal-expansion-power y)))
             (same (proof-proof-assume proof test t))
             (yes (h4-book-expansion-expansion-orders-compare-equal
                   same p x y power-types formula substitutions reflexive runs evidence))
             (different (proof-proof-assume proof test nil))
             (no (h4-book-expansion-expansion-orders-compare-unequal
                  different p goal x y power-types power-order reflexive evidence provide)))
          (h4-tactics-tactics-case-of p goal test yes no))
      (proof-with-checked-results
          ((evidence (if (or pair-x pair-y) evidence
                       (proof-with-checked-results
                           ((rational-x (h4-book-expansion-ordinal-expansion-rational-if-finite x p))
                            (rational-y (h4-book-expansion-ordinal-expansion-rational-if-finite y p)))
                         (append evidence (list rational-x rational-y)))))
           (forward (h4-book-expansion-expansion-orders-compare-base x y p evidence provide))
           (backward (h4-book-expansion-expansion-orders-compare-base y x p evidence provide)))
        (h4-book-division-conjunction p (list forward backward))))))

(defun h4-book-expansion-expansion-orders-first-second
    (other p x type-y substitutions formula goal reflexive runs provide)
  (proof-with-checked-results
      ((y (h4-book-expansion-ordinal-expansion-init p type-y other))
       (compared (h4-book-expansion-expansion-orders-compare
                  x y p substitutions formula goal reflexive runs provide)))
    (h4-tactics-tactics-imply p formula compared)))

(defun h4-book-expansion-expansion-orders-first
    (shape p type-x type-y substitutions formula goal reflexive runs provide)
  (let ((proof (library-library-proof p))
        (test (list *proof-consp* *library-y*)))
    (proof-with-checked-results
        ((x (h4-book-expansion-ordinal-expansion-init p type-x shape))
         (pair (proof-proof-assume proof test t))
         (yes (h4-book-expansion-expansion-orders-first-second
               pair p x type-y substitutions formula goal reflexive runs provide))
         (atom-case (proof-proof-assume proof test nil))
         (no (h4-book-expansion-expansion-orders-first-second
              atom-case p x type-y substitutions formula goal reflexive runs provide)))
      (h4-tactics-tactics-case-of p formula test yes no))))

(defun h4-book-expansion-expansion-orders (p reflexive runs)
  (let* ((proof (library-library-proof p))
         (x *library-x*) (y *library-y*)
         (forward (h4-book-expansion-comparison-forms x y))
         (backward (h4-book-expansion-comparison-forms y x))
         (guard (proof-ite (list *proof-ordinalp* x) (list *proof-ordinalp* y) *proof-false*))
         (goal (proof-ite forward backward *proof-false*))
         (formula (list *library-implies* guard goal))
         (ex-x (list *h4-book-order-exponent* x))
         (ex-y (list *h4-book-order-exponent* y))
         (rest-x (list *h4-book-order-rest* x))
         (rest-y (list *h4-book-order-rest* y))
         (tail-power-x (list *h4-book-order-exponent* rest-x))
         (tail-power-y (list *h4-book-order-exponent* rest-y))
         (substitutions (list (list (list x ex-x) (list y ex-y))
                              (list (list x rest-x) (list y rest-y))
                              (list (list x tail-power-x) (list y ex-y))
                              (list (list x ex-x) (list y tail-power-y))))
         (test (list *proof-consp* x)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof guard t))
         (types (h4-tactics-tactics-conjunct p assumed))
         (provide (h4-book-finite-reduction-provider p))
         (pair (proof-proof-assume proof test t))
         (yes (h4-book-expansion-expansion-orders-first
               pair p (car types) (cadr types) substitutions formula goal reflexive runs provide))
         (atom-case (proof-proof-assume proof test nil))
         (no (h4-book-expansion-expansion-orders-first
              atom-case p (car types) (cadr types) substitutions formula goal reflexive runs provide))
         (cases (h4-tactics-tactics-case-of p formula test yes no))
         (ordinal (library-library-builtin p 1 x)))
      (proof-proof-induct proof ordinal cases formula (list *library-count* x) substitutions))))

(defun h4-book-expansion-same-or-smaller-boundary (element tail)
  (proof-ite (list *proof-consp* tail)
             (proof-neg (list *h4-book-expansion-e0-less* element (list *library-car* tail)))
             *proof-true*))

(defun h4-book-expansion-ordered-prefix-add (shape p opened evidence compatible provide)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first shape))
         (facts (if (proof-is-call literal *proof-consp*)
                    (proof-with-checked-results ((bound (proof-proof-prove-if proof compatible shape)))
                      (append evidence (list shape bound)))
                  (append evidence (list shape))))
         (value (h4-book-expansion-part opened 2))
         (body (h4-tactics-tactics-establish p value facts (list (proof-cl "ATOM") *proof-not*) nil provide)))
      (proof-proof-transport proof body opened))))

(defun h4-book-expansion-ordered-prefix (p element-type nonzero tail-type compatible provide)
  (let ((proof (library-library-proof p))
        (evidence (list element-type nonzero tail-type)))
    (proof-with-checked-results
        ((element (h4-book-expansion-part element-type 1))
         (tail (h4-book-expansion-part tail-type 1))
         (term (list *h4-book-expansion-e0-ordinal* (list *proof-cons* element tail)))
         (opened (proof-proof-unfold proof term))
         (test (list *proof-consp* tail))
         (pair (proof-proof-assume proof test t))
         (yes (h4-book-expansion-ordered-prefix-add pair p opened evidence compatible provide))
         (atom-case (proof-proof-assume proof test nil))
         (no (h4-book-expansion-ordered-prefix-add atom-case p opened evidence compatible provide)))
      (h4-tactics-tactics-case-of p term test yes no))))

(defun h4-book-expansion-copy-preserves-type-done (test p tail-type)
  (proof-with-checked-results
      ((opened (h4-book-expansion-copied-prefix
                p *h4-book-expansion-element* *h4-book-expansion-first-count* *library-y* test)))
    (library-library-transport-argument p tail-type opened 1)))

(defun h4-book-expansion-copy-preserves-type-step-boundary
    (p tail shortened compatible child-test reflexive)
  (let ((proof (library-library-proof p))
        (element *h4-book-expansion-element*))
    (proof-with-checked-results ((literal (proof-step-first child-test)))
      (if (proof-is-call literal *h4-book-arithmetic-zp*)
          (proof-with-checked-results ((reversed (proof-proof-symmetric proof shortened)))
            (proof-proof-rewrite-first proof compatible reversed))
        (proof-with-checked-results
            ((prefix (h4-book-expansion-part shortened 2))
             (head (library-library-axiom p "CAR-CONS" (cdr prefix)))
             (access (h4-book-flatten-rewrite-argument p (list *library-car* tail) 1 shortened))
             (head (proof-proof-chain proof access (list head)))
             (test (proof-neg (list *h4-book-expansion-e0-less* element (list *library-car* tail))))
             (self (proof-proof-instantiate proof reflexive (list (list *library-x* element))))
             (no-strict (h4-tactics-tactics-establish p test nil (list *proof-not*) (list head self) nil)))
          (h4-tactics-tactics-guarded p (list *proof-consp* tail) no-strict t))))))

(defun h4-book-expansion-copy-preserves-type-step-finish
    (child-test p smaller tail compatible reflexive exp-type nonzero typed-tail provide full)
  (proof-with-checked-results
      ((shortened (h4-book-expansion-copied-prefix p *h4-book-expansion-element* smaller *library-y* child-test))
       (guard (h4-book-expansion-copy-preserves-type-step-boundary
               p tail shortened compatible child-test reflexive))
       (result (h4-book-expansion-ordered-prefix p exp-type nonzero typed-tail guard provide)))
    (library-library-transport-argument p result full 1)))

(defun h4-book-expansion-copy-preserves-type-step
    (test p formula goal given smaller exp-type nonzero compatible reflexive provide)
  (let ((proof (library-library-proof p))
        (element *h4-book-expansion-element*)
        (n *h4-book-expansion-first-count*))
    (proof-with-checked-results
        ((full (h4-book-expansion-copied-prefix p element n *library-y* test))
         (prefix (h4-book-expansion-part full 2))
         (tail (proof-term-at prefix 2))
         (builtin (library-library-builtin p 9 n))
         (less (proof-proof-discharge proof builtin test))
         (child (proof-subst formula (list (cons n smaller))))
         (measure (proof-step-first less))
         (assumed (proof-proof-assume proof (proof-ite measure child *proof-true*) t))
         (induction (proof-proof-prove-if proof assumed less))
         (typed-tail (h4-tactics-tactics-modus-ponens p induction given))
         (test (list *h4-book-arithmetic-zp* smaller))
         (stopped (proof-proof-assume proof test t))
         (yes (h4-book-expansion-copy-preserves-type-step-finish
               stopped p smaller tail compatible reflexive exp-type nonzero typed-tail provide full))
         (active (proof-proof-assume proof test nil))
         (no (h4-book-expansion-copy-preserves-type-step-finish
              active p smaller tail compatible reflexive exp-type nonzero typed-tail provide full)))
      (h4-tactics-tactics-case-of p goal test yes no))))

(defun h4-book-expansion-copy-preserves-type (p reflexive)
  (let* ((proof (library-library-proof p))
         (a *h4-book-expansion-element*)
         (n *h4-book-expansion-first-count*)
         (tail *library-y*)
         (boundary (h4-book-expansion-same-or-smaller-boundary a tail))
         (guard (proof-ite (list *h4-book-expansion-e0-ordinal* a)
                           (proof-ite (proof-neg (proof-eq a *proof-zero*))
                                      (proof-ite (list *h4-book-expansion-e0-ordinal* tail) boundary *proof-false*)
                                      *proof-false*)
                           *proof-false*))
         (goal (list *h4-book-expansion-e0-ordinal* (h4-book-expansion-copy-append a n tail)))
         (formula (list *library-implies* guard goal))
         (test (list *h4-book-arithmetic-zp* n))
         (smaller (h4-book-arithmetic-predecessor n))
         (bindings (list (list n smaller))))
    (proof-with-checked-results
        ((given (proof-proof-assume proof guard t))
         (parts (h4-book-list-types-conjunct-proofs p given))
         (parts (proof-list-of-length parts 4))
         (provide (h4-book-finite-reduction-provider p))
         (stopped (proof-proof-assume proof test t))
         (yes (h4-book-expansion-copy-preserves-type-done stopped p (caddr parts)))
         (active (proof-proof-assume proof test nil))
         (no (h4-book-expansion-copy-preserves-type-step
              active p formula goal given smaller (car parts) (cadr parts) (cadddr parts) reflexive provide))
         (cases (h4-tactics-tactics-case-of p goal test yes no))
         (ordinal (library-library-builtin p 1 n))
         (implied (h4-tactics-tactics-imply p formula cases)))
      (proof-proof-induct proof ordinal implied formula (list *library-count* n) (list bindings)))))

(defun h4-book-expansion-expansion-nonzero-pair (p view)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((pair (h4-book-expansion-part (h4-book-expansion-ordinal-expansion-spine view) 2))
         (nonempty (proof-proof-fact proof "consp-cons"
                                         (seq-zip (list *library-x* *library-y*) (cdr pair))))
         (empty (proof-eq pair *proof-zero*))
         (assumed (proof-proof-assume proof empty t))
         (impossible (proof-proof-rewrite proof nonempty assumed '(1 1)))
         (computed (proof-proof-compute proof (list *proof-consp* *proof-zero*) *proof-nil*))
         (false-step (proof-proof-rewrite proof impossible computed '(1)))
         (tidied (proof-proof-tidy proof false-step)))
      (proof-proof-front proof tidied (proof-neg empty)))))

(defun h4-book-expansion-expansion-nonzero-branch (shape p ordinal different)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((view (h4-book-expansion-ordinal-expansion-init p ordinal shape))
         (nonzero (if (h4-book-expansion-ordinal-expansion-is-pair view)
                      (h4-book-expansion-expansion-nonzero-pair p view)
                    different))
         (reversed (proof-proof-symmetric proof (h4-book-expansion-ordinal-expansion-spine view))))
      (proof-proof-rewrite proof nonzero reversed '(1 1 1)))))

(defun h4-book-expansion-expansion-nonzero (p ordinal different)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((subject (h4-book-expansion-part ordinal 1)))
      (let ((goal (proof-neg (proof-eq (list *h4-book-expansion-ctoa* subject) *proof-zero*)))
            (test (list *proof-consp* subject)))
        (proof-with-checked-results
            ((pair (proof-proof-assume proof test t))
             (yes (h4-book-expansion-expansion-nonzero-branch pair p ordinal different))
             (atom-case (proof-proof-assume proof test nil))
             (no (h4-book-expansion-expansion-nonzero-branch atom-case p ordinal different)))
          (h4-tactics-tactics-case-of p goal test yes no))))))

(defun h4-book-expansion-expansion-type-case-positive (shape p stronger boundary)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((conjuncts (proof-proof-prove-if proof stronger shape))
         (obtained (h4-book-list-types-conjunct-proofs p conjuncts))
         (backward (proof-term-at obtained 1))
         (choice (proof-proof-if-true proof boundary)))
      (proof-proof-transport proof backward choice))))

(defun h4-book-expansion-expansion-type-case-atom (p formula ordinal assumed shape subject)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first assumed))
         (opened (h4-book-order-order-view p literal (list shape) nil))
         (natural (proof-proof-rewrite proof assumed opened '(1)))
         (literal (proof-step-first natural))
         (unfolded (proof-proof-unfold proof literal))
         (natural (proof-proof-rewrite proof natural unfolded '(1)))
         (type-view (h4-book-order-order-view p (list *h4-book-expansion-e0-ordinal* subject) (list shape) nil))
         (typed (proof-proof-transport proof natural type-view))
         (typed (library-library-transport-argument p typed (h4-book-expansion-ordinal-expansion-spine ordinal) 1)))
      (h4-tactics-tactics-imply p formula typed))))

(defun h4-book-expansion-expansion-type-case-pair (p formula ordinal children copy-type order reflexive)
  (let ((proof (library-library-proof p))
        (power (h4-book-expansion-ordinal-expansion-power ordinal))
        (rest (h4-book-expansion-ordinal-expansion-rest ordinal))
        (pieces (h4-book-expansion-ordinal-expansion-pieces ordinal)))
    (proof-with-checked-results
        ((exponent (h4-book-expansion-ordinal-expansion-power-type ordinal))
         (tail (h4-book-expansion-ordinal-expansion-rest-type ordinal))
         (nonzero (h4-book-expansion-component pieces (proof-neg (list (proof-cl "EQL") *proof-zero* power))))
         (nonzero-test (h4-book-expansion-part nonzero 1))
         (strict (h4-tactics-tactics-normalize p nonzero-test nil (list (proof-cl "EQL")) nil nil))
         (changed (proof-proof-rewrite proof nonzero strict '(1 1)))
         (different (h4-book-order-reflected-test p changed))
         (stays-nonzero (h4-book-expansion-expansion-nonzero p exponent different))
         (exponent-child (h4-book-expansion-component children *h4-book-order-exponent*))
         (element-type (h4-tactics-tactics-modus-ponens p exponent-child exponent))
         (rest-child (h4-book-expansion-component children *h4-book-order-rest*))
         (suffix-type (h4-tactics-tactics-modus-ponens p rest-child tail))
         (bound (h4-book-expansion-component pieces (list *proof-ordinal-less*
                                                         (list *h4-book-order-exponent* rest) power)))
         (stronger (h4-book-expansion-prefix-bound p tail power bound (list :expansions order exponent) reflexive))
         (element (h4-book-expansion-ordinal-expansion-element ordinal))
         (suffix (h4-book-expansion-ordinal-expansion-suffix ordinal))
         (head-test (list *proof-consp* suffix))
         (boundary (h4-book-expansion-same-or-smaller-boundary element suffix))
         (pair (proof-proof-assume proof head-test t))
         (positive (h4-book-expansion-expansion-type-case-positive pair p stronger boundary))
         (atom-case (proof-proof-assume proof head-test nil))
         (negative (h4-tactics-tactics-establish p boundary (list atom-case) nil nil nil))
         (compatible (h4-tactics-tactics-case-of p boundary head-test positive negative))
         (rule (proof-proof-instantiate proof copy-type
                                       (list (list *h4-book-expansion-element* element)
                                             (list *library-y* suffix)
                                             (list *h4-book-expansion-first-count*
                                                   (h4-book-expansion-ordinal-expansion-count ordinal)))))
         (evidence (h4-book-division-conjunction p (list element-type stays-nonzero suffix-type compatible)))
         (valid (h4-tactics-tactics-modus-ponens p rule evidence))
         (result (library-library-transport-argument
                  p valid (h4-book-expansion-ordinal-expansion-opened ordinal) 1)))
      (h4-tactics-tactics-imply p formula result))))

(defun h4-book-expansion-expansion-type-case
    (shape children p assumed formula subject copy-type order reflexive)
  (proof-with-checked-results
      ((ordinal (h4-book-expansion-ordinal-expansion-init p assumed shape)))
    (if (h4-book-expansion-ordinal-expansion-is-pair ordinal)
        (h4-book-expansion-expansion-type-case-pair p formula ordinal children copy-type order reflexive)
      (h4-book-expansion-expansion-type-case-atom p formula ordinal assumed shape subject))))

(defun h4-book-expansion-expansion-type (p formula order reflexive)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((guard (proof-term-at formula 1))
         (assumed (proof-proof-assume proof guard t))
         (subject (h4-book-expansion-part assumed 1))
         (subjects (list subject))
         (copy-type (h4-book-expansion-copy-preserves-type p reflexive))
         (pair (h4-book-order-ordinal-induction p formula subjects nil)))
      (if (h4-book-order-ordinal-induction-request-p pair)
          (proof-with-checked-results
              ((yes (h4-book-expansion-expansion-type-case
                     (caddr pair) (cadddr pair) p assumed formula subject copy-type order reflexive))
               (atom-case (h4-book-order-ordinal-induction p formula subjects (list yes))))
            (if (h4-book-order-ordinal-induction-request-p atom-case)
                (proof-with-checked-results
                    ((no (h4-book-expansion-expansion-type-case
                          (caddr atom-case) (cadddr atom-case) p assumed formula subject copy-type order reflexive)))
                  (h4-book-order-ordinal-induction p formula subjects (list yes no)))
              atom-case))
        pair))))

(defun h4-book-expansion-with-facts (p facts)
  (library-library-with-proof p (proof-proof-with-facts (library-library-proof p) facts)))

(defun h4-book-expansion-expansion-proofs-prepare (expansions p)
  (let ((order (h4-book-expansion-expansion-proofs-order expansions))
        (label *h4-book-expansion-expansion-order*))
    (if order
        (list expansions
              (h4-book-expansion-with-facts p (table-put (proof-proof-facts (library-library-proof p))
                                                           label (proof-step-clause order))))
      (proof-with-checked-results
          ((reflexive (h4-book-expansion-e0-irreflexive p))
           (runs (h4-book-expansion-copy-comparison p reflexive))
           (lemma (h4-book-expansion-expansion-orders p reflexive runs))
           (added (h4-tactics-tactics-local-lemma p label lemma))
           (library (cdr added))
           (order (proof-proof-fact (library-library-proof library) label nil)))
        (list (list :h4-expansion-proofs reflexive order) library)))))

(defun h4-book-expansion-expansion-proofs-prove-order (p formula order match)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((rule (proof-proof-instantiate proof order (seq-zip (list *library-x* *library-y*) match)))
         (guard (proof-term-at formula 1))
         (assumed (proof-proof-assume proof guard t))
         (conclusion (h4-tactics-tactics-modus-ponens p rule assumed))
         (conjuncts (h4-tactics-tactics-conjunct p conclusion)))
      (h4-tactics-tactics-imply p formula (car conjuncts)))))

(defun h4-book-expansion-expansion-proofs-prove (expansions p formula support)
  (proof-with-checked-results ((match (h4-book-expansion-expansion-shape formula)))
    (if (and match support)
        (let* ((previous (proof-proof-facts (library-library-proof p)))
               (available (h4-book-expansion-with-facts p (table-update previous support))))
          (proof-with-checked-results
              ((prepared (h4-book-expansion-expansion-proofs-prepare expansions available))
               (expansions (car prepared))
               (library (cadr prepared))
               (order (h4-book-expansion-expansion-proofs-order expansions))
               (result (if (endp (cdr match))
                           (h4-book-expansion-expansion-type
                            library formula order (h4-book-expansion-expansion-proofs-reflexive expansions))
                         (h4-book-expansion-expansion-proofs-prove-order library formula order match))))
            (list result expansions (h4-book-expansion-with-facts library previous))))
      (list nil expansions p))))
