(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-fixtypes-hard-error* (proof-sym "HARD-ERROR" "ACL2"))
(defconst *b1-fixtypes-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *b1-fixtypes-symbol-listp* (proof-sym "SYMBOL-LISTP" "ACL2"))
(defconst *b1-fixtypes-true-listp* (proof-sym "TRUE-LISTP" "ACL2"))

(defun b1-fixtypes-product-selector-selected (evidence lib lookup pair axiom first rest)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-list lib pair evidence))
         (moved (b1-revappend-lift-argument lib lookup opened 1))
         (equality (library-library-axiom lib axiom (list first rest))))
      (proof-proof-chain proof moved (list equality)))))

(defun b1-fixtypes-product-selector (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (lookup (cadr parts))
         (result (caddr parts))
         (selection (proof-list-of-length lookup 2))
         (selector (car selection))
         (pair (cadr selection))
         (fields (proof-list-of-length pair 3))
         (first (cadr fields))
         (rest (caddr fields))
         (axiom (if (equal selector *library-car*) "CAR-CONS" "CDR-CONS"))
         (no-first (proof-proof-assume proof first nil))
         (no-rest (proof-proof-assume proof rest nil))
         (opened (b1-revappend-open-list lib pair (list no-first no-rest)))
         (empty (b1-revappend-lift-argument lib lookup opened 1))
         (right (proof-rewritten-term empty))
         (value (b1-logic-bookproof-constant lib right))
         (empty (proof-proof-chain proof empty (list value)))
         (missing (if (equal result first) no-first no-rest))
         (false-value (b1-logic-bookproof-false-value lib missing))
         (reversed (proof-proof-symmetric proof false-value))
         (empty (proof-proof-chain proof empty (list reversed)))
         (has-first (proof-proof-assume proof first t))
         (yes (b1-fixtypes-product-selector-selected (list has-first) lib lookup pair axiom first rest))
         (has-rest (proof-proof-assume proof rest t))
         (only-rest (b1-fixtypes-product-selector-selected
                     (list no-first has-rest) lib lookup pair axiom first rest))
         (no (proof-proof-cases proof rest only-rest empty)))
      (proof-proof-cases proof first yes no))))

(defun b1-fixtypes-product-reconstruction-consequence (premise lib pair xs test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((cons (proof-proof-assume proof test t))
         (atom (proof-proof-assume proof test nil))
         (literal (proof-step-first premise))
         (expanded (b1-revappend-open-list lib literal (list cons)))
         (asserted (proof-proof-rewrite proof premise expanded '(1)))
         (right (proof-rewritten-term expanded))
         (first (proof-term-at right 1))
         (either (b1-logic-bookproof-forces lib first asserted nil nil nil))
         (nonempty (b1-revappend-open-list lib pair (list either)))
         (right (proof-rewritten-term nonempty))
         (law (b1-logic-bookproof-from-fact
               lib (proof-sym "CAR-CDR-ELIM" "ACL2")
               (list *library-implies* test (proof-eq right xs))))
         (actual (proof-proof-modus-ponens proof law cons))
         (yes (proof-proof-chain proof nonempty (list actual)))
         (head (proof-term-at literal 0))
         (normal (b1-logic-bookproof-normalize lib literal (list atom) (list head) nil nil nil nil))
         (nil-like (proof-proof-rewrite proof premise normal '(1)))
         (missing (b1-logic-bookproof-false-value lib nil-like))
         (car-empty (b1-structures-noncons-selector lib *library-car* atom))
         (cdr-empty (b1-structures-noncons-selector lib *library-cdr* atom))
         (pair-head (proof-term-at pair 0))
         (reduced (b1-logic-bookproof-normalize
                   lib pair nil (list pair-head)
                   (list (b1-logic-equal-to car-empty) (b1-logic-equal-to cdr-empty)) nil nil nil))
         (reversed (proof-proof-symmetric proof missing))
         (no (proof-proof-chain proof reduced (list reversed))))
      (proof-proof-cases proof test yes no))))

(defun b1-fixtypes-product-reconstruction (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr implication) 3))
       (pair (cadr claim))
       (xs (caddr claim))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-fixtypes-product-reconstruction-consequence
                     premise lib pair xs (list *proof-consp* xs))))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-fixtypes-product-equality-consequence-extracted (selector value tag lib pair is-equal)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step (b1-logic-bookproof-from-fact lib (proof-sym tag "STD")
                                            (proof-eq (list selector pair) value)))
         (reversed (proof-proof-symmetric proof is-equal)))
      (proof-proof-rewrite proof step reversed '(1 1 1)))))

(defun b1-fixtypes-product-equality-consequence
    (premise lib claim same pair xs head tail is-equal unequal product)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((head-equality (b1-fixtypes-product-equality-consequence-extracted
                         *library-car* (cadr product) "CAR-OF-PROD-CONS" lib pair is-equal))
         (tail-equality (b1-fixtypes-product-equality-consequence-extracted
                         *library-cdr* (caddr product) "CDR-OF-PROD-CONS" lib pair is-equal))
         (yes (b1-logic-bookproof-case-proof lib claim (list is-equal head-equality tail-equality)
                                            nil nil 16))
         (test (proof-step-first premise))
         (rebuild (proof-eq (list (car product) (list *library-car* xs) (list *library-cdr* xs)) xs))
         (rule (b1-logic-bookproof-from-fact
                lib (proof-sym "PROD-CONS-OF-CAR/CDR" "STD") (list *library-implies* test rebuild)))
         (reconstructed (proof-proof-modus-ponens proof rule premise))
         (a (proof-proof-assume proof head t))
         (b (proof-proof-assume proof tail t))
         (same-product (proof-proof-rewrite proof reconstructed a '(1 1 1)))
         (same-product (proof-proof-rewrite proof same-product b '(1 1 2)))
         (reversed (proof-proof-symmetric proof same-product))
         (impossible (b1-logic-bookproof-contradiction lib reversed unequal claim))
         (no-head (proof-proof-assume proof head nil))
         (missing-head (b1-logic-bookproof-case-proof lib claim (list unequal no-head) nil nil 16))
         (no-tail (proof-proof-assume proof tail nil))
         (missing-tail (b1-logic-bookproof-case-proof lib claim (list unequal a no-tail) nil nil 16))
         (tail-cases (proof-proof-cases proof tail impossible missing-tail))
         (no (proof-proof-cases proof head tail-cases missing-head)))
      (proof-proof-cases proof same yes no))))

(defun b1-fixtypes-product-equality (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((implication (proof-list-of-length formula 3))
         (claim (proof-list-of-length (caddr implication) 3))
         (same (cadr claim))
         (sides (proof-list-of-length same 3))
         (xs (cadr sides))
         (pair (caddr sides))
         (fields (proof-list-of-length (caddr claim) 4))
         (head (cadr fields))
         (tail (caddr fields))
         (product (proof-list-of-length pair 3))
         (is-equal (proof-proof-assume proof same t))
         (unequal (proof-proof-assume proof same nil))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-fixtypes-product-equality-consequence
                       premise lib claim same pair xs head tail is-equal unequal product)))
      (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))))

(defun b1-fixtypes-product-against-cons-consequence (premise lib product other)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (b1-revappend-open-list lib product (list premise)))
         (right (proof-rewritten-term value))
         (core (b1-revappend-cons-equality lib right other))
         (reversed (proof-proof-symmetric proof value)))
      (proof-proof-rewrite proof core reversed '(1 1 1)))))

(defun b1-fixtypes-product-against-cons (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr implication) 3))
       (sides (proof-list-of-length (cadr claim) 3))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-fixtypes-product-against-cons-consequence
                     premise lib (cadr sides) (caddr sides))))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-fixtypes-product-size-bound (lib a b cons total is-cons builtin selector)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((clause (library-library-builtin lib builtin cons))
         (size (proof-proof-discharge proof clause is-cons))
         (child (list *library-count* (list selector cons)))
         (comparison (library-library-ordinal-comparison lib child total))
         (size (proof-proof-rewrite proof size comparison '(1)))
         (axiom (library-library-axiom lib (if (equal selector *library-car*) "CAR-CONS" "CDR-CONS")
                                      (list a b)))
         (size (proof-proof-rewrite proof size axiom '(1 1 1)))
         (sums (b1-arithmetic-number-sums-init lib))
         (bound (b1-arithmetic-number-sums-weaken sums size nil)))
      (cons bound (b1-arithmetic-number-sums-library sums)))))

(defun b1-fixtypes-product-size-absent (step term lib empty)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((contradiction (proof-proof-cut proof step empty)))
      (proof-proof-front proof contradiction (proof-neg term)))))

(defun b1-fixtypes-product-size (lib formula)
  (proof-with-checked-results
      ((outer (proof-term-at formula 1))
       (comparison (proof-term-at outer 1))
       (count (proof-term-at comparison 1))
       (pair (proof-term-at count 1))
       (fields (proof-list-of-length pair 3))
       (a (cadr fields))
       (b (caddr fields))
       (proof (library-library-proof lib))
       (pair-test (proof-ite a a b))
       (have (proof-proof-assume proof pair-test t))
       (empty (proof-proof-assume proof pair-test nil))
       (cons (list *proof-cons* a b))
       (total (list *library-count* cons))
       (pair-eq (b1-revappend-open-list lib pair (list have)))
       (is-cons (proof-proof-fact proof "consp-cons" (list (list *library-x* a) (list *library-y* b))))
       (a-bound (b1-fixtypes-product-size-bound lib a b cons total is-cons 2 *library-car*))
       (b-bound (b1-fixtypes-product-size-bound (cdr a-bound) a b cons total is-cons 3 *library-cdr*))
       (lib (cdr b-bound))
       (proof (library-library-proof lib))
       (yes (b1-logic-bookproof-normalize-proof
             lib formula (list (car a-bound) (car b-bound)) nil (list (b1-logic-equal-to pair-eq)) nil))
       (first (proof-proof-assume proof a t))
       (second (proof-proof-assume proof b t))
       (selected (proof-proof-select proof pair-test first))
       (positive-a (proof-proof-transport proof first selected))
       (no-a (b1-fixtypes-product-size-absent positive-a a lib empty))
       (selected (proof-proof-select proof pair-test no-a))
       (present-b (proof-proof-transport proof second selected))
       (no-b (b1-fixtypes-product-size-absent present-b b lib empty))
       (empty-pair (b1-revappend-open-list lib pair (list empty)))
       (absent-a (b1-logic-bookproof-false-value lib no-a))
       (absent-b (b1-logic-bookproof-false-value lib no-b))
       (no (b1-logic-bookproof-case-proof lib formula nil (list *library-count* *proof-not*)
                                         (list (b1-logic-equal-to empty-pair)
                                               (b1-logic-equal-to absent-a)
                                               (b1-logic-equal-to absent-b)) 16))
       (result (proof-proof-cases proof pair-test yes no)))
    (cons result lib)))

(defun b1-fixtypes-product-empty-consequence-impossible (evidence lib pair a b noncons claim)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reduction (b1-revappend-open-list lib pair evidence))
         (fact (proof-proof-fact proof "consp-cons" (list (list *library-x* a) (list *library-y* b))))
         (yes (library-library-transport-argument lib fact reduction 1)))
      (b1-logic-bookproof-contradiction lib yes noncons claim))))

(defun b1-fixtypes-product-empty-consequence (noncons lib pair a b claim a-yes a-no b-yes b-no)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((neither (b1-logic-bookproof-normalize-proof lib claim (list a-no b-no)
                                                     (list *proof-not*) nil nil))
         (with-a (b1-fixtypes-product-empty-consequence-impossible
                  (list a-yes) lib pair a b noncons claim))
         (with-b (b1-fixtypes-product-empty-consequence-impossible
                  (list a-no b-yes) lib pair a b noncons claim))
         (without-a (proof-proof-cases proof b with-b neither)))
      (proof-proof-cases proof a with-a without-a))))

(defun b1-fixtypes-product-empty (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((implication (proof-list-of-length formula 3))
         (claim (caddr implication))
         (test (proof-term-at (cadr implication) 1))
         (pair (proof-term-at test 1))
         (fields (proof-list-of-length pair 3))
         (a (cadr fields))
         (b (caddr fields))
         (a-yes (proof-proof-assume proof a t))
         (a-no (proof-proof-assume proof a nil))
         (b-yes (proof-proof-assume proof b t))
         (b-no (proof-proof-assume proof b nil))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-fixtypes-product-empty-consequence
                       premise lib pair a b claim a-yes a-no b-yes b-no)))
      (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))))

(defun b1-fixtypes-tag-implies-cons-consequence (premise lib lookup test atom)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-list lib lookup nil))
         (selector (b1-structures-noncons-selector lib *library-car* atom))
         (absent (proof-proof-chain proof opened (list selector)))
         (reduced (proof-proof-rewrite proof premise absent '(1)))
         (not-nil (b1-logic-proof-not-nil proof))
         (impossible (b1-logic-bookproof-contradiction lib reduced not-nil test))
         (positive (proof-proof-assume proof test t)))
      (proof-proof-cases proof test positive impossible))))

(defun b1-fixtypes-tag-implies-cons (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((implication (proof-list-of-length formula 3))
         (test (caddr implication))
         (atom (proof-proof-assume proof test nil))
         (premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-fixtypes-tag-implies-cons-consequence
                       premise lib (cadr implication) test atom)))
      (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))))

(defconst *b1-fixtypes-identity-processor-wellformed-tests*
  (list (proof-sym "TERM-LIST-LISTP" "ACL2") (proof-sym "LOGIC-FNS-LIST-LISTP" "ACL2")))
(defconst *b1-fixtypes-identity-processor-correct-choose* (proof-sym "CONJOIN" "ACL2"))
(defconst *b1-fixtypes-identity-processor-correct-map-clauses* (proof-sym "DISJOIN-LST" "ACL2"))

(defun b1-fixtypes-lookup-result-type-leaf-quoted-list (term lib)
  (and (proof-is-call term *b1-fixtypes-symbol-listp*)
    (proof-with-checked-results ((argument (proof-term-at term 1)))
      (and (proof-is-call argument *proof-quote*)
        (proof-proof-unfold (library-library-proof lib) term)))))

(defun b1-fixtypes-identity-processor-wellformed-empty (term lib)
  (proof-with-checked-results ((head (proof-term-at term 0)))
    (and (member-equal head *b1-fixtypes-identity-processor-wellformed-tests*)
      (proof-with-checked-results ((argument (proof-term-at term 1)))
        (and (equal argument *proof-false*)
          (b1-logic-bookproof-normalize lib term nil
                                       (list head *b1-logic-atom* *b1-logic-endp* *proof-not*)
                                       nil nil nil nil))))))

(defun b1-fixtypes-identity-processor-correct-empty (term lib)
  (and (proof-is-call term *b1-fixtypes-identity-processor-correct-map-clauses*)
    (proof-with-checked-results ((argument (proof-term-at term 1)))
      (and (equal argument *proof-false*)
        (b1-logic-bookproof-normalize
         lib term nil
         (list *b1-fixtypes-identity-processor-correct-map-clauses*
               *b1-logic-endp* *b1-logic-atom* *proof-not*) nil nil nil nil)))))

(defun b1-fixtypes-normalize-with-rule-compute (lib term evidence unfold rule prove replies)
  (let ((rules (list (list :callback rule))))
    (if prove
        (b1-logic-bookproof-normalize-proof-with-library lib term evidence unfold rules nil replies)
      (b1-logic-bookproof-normalize-with-library lib term evidence unfold rules nil nil nil replies))))

(defun b1-fixtypes-normalize-with-rule-answer (request)
  (let ((term (b1-logic-call-term request))
        (lib (b1-logic-call-library request)))
    (proof-with-checked-results
        ((step (case (b1-logic-call-id request)
                 (:quoted-list (b1-fixtypes-lookup-result-type-leaf-quoted-list term lib))
                 (:empty-types (b1-fixtypes-identity-processor-wellformed-empty term lib))
                 (:empty-disjunction (b1-fixtypes-identity-processor-correct-empty term lib))
                 (otherwise nil))))
      (cons step lib))))

(defun b1-fixtypes-normalize-with-rule-next (lib term evidence unfold rule prove request replies)
  (let ((answer (b1-fixtypes-normalize-with-rule-answer request)))
    (if (failure-p answer)
        (cons answer replies)
      (let ((replies (append replies (list answer))))
        (cons (b1-fixtypes-normalize-with-rule-compute lib term evidence unfold rule prove replies)
              replies)))))

(defun b1-fixtypes-normalize-with-rule-resume (n lib term evidence unfold rule prove computation)
  (declare (xargs :measure (nfix n)))
  (let ((result (car computation)))
    (cond ((zp n) '(:failure "Fuel" "b1-fixtypes-normalize-with-rule-resume"))
          ((failure-p result) result)
          ((b1-logic-call-p result)
           (if (equal n 1)
               (proof-with-checked-results ((answer (b1-fixtypes-normalize-with-rule-answer result)))
                 '(:failure "Fuel" "b1-fixtypes-normalize-with-rule-resume"))
             (b1-fixtypes-normalize-with-rule-resume
              (1- n) lib term evidence unfold rule prove
              (b1-fixtypes-normalize-with-rule-next
               lib term evidence unfold rule prove result (cdr computation)))))
          ((b1-logic-branch-p result) '(:failure "failure" ""))
          (t (car result)))))

(defun b1-fixtypes-normalize-with-rule (lib term evidence unfold rule prove)
  (b1-fixtypes-normalize-with-rule-resume
   1000000 lib term evidence unfold rule prove
   (cons (b1-fixtypes-normalize-with-rule-compute lib term evidence unfold rule prove nil) nil)))

(defun b1-fixtypes-lookup-result-type-leaf-evidence (tests lib)
  (if (endp tests)
      nil
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((test (caar tests))
           (holds (cadar tests))
           (assumed (proof-proof-assume proof test holds))
           (fields (if holds (b1-logic-bookproof-split-conjuncts lib assumed) (list assumed)))
           (rest (b1-fixtypes-lookup-result-type-leaf-evidence (cdr tests) lib)))
        (append fields rest)))))

(defun b1-fixtypes-lookup-result-type-leaf (value tests lib template boolean-result)
  (proof-with-checked-results ((goal (proof-subst template (list (cons *proof-result* value)))))
    (if boolean-result
        (b1-logic-bookproof-normalize-proof lib goal nil nil nil nil)
      (proof-with-checked-results ((evidence (b1-fixtypes-lookup-result-type-leaf-evidence tests lib)))
        (b1-fixtypes-normalize-with-rule lib goal evidence
                                         (list *b1-logic-atom* *b1-logic-eq* *proof-not*)
                                         :quoted-list t)))))

(defun b1-fixtypes-lookup-result-type-by-value (n lib value template tests boolean-result)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((zp n) '(:failure "Fuel" "b1-fixtypes-lookup-result-type-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (yes (b1-fixtypes-lookup-result-type-by-value
                 (1- n) lib (cadr branches) template (append tests (list (list (car branches) t)))
                 boolean-result))
           (no (b1-fixtypes-lookup-result-type-by-value
                (1- n) lib (caddr branches) template (append tests (list (list (car branches) nil)))
                boolean-result)))
        (proof-by-value-join proof value template yes no)))
     ((and (proof-compound value) (not (consp value)))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (opened (proof-rewritten-term equality))
           (step (b1-fixtypes-lookup-result-type-by-value (1- n) lib opened template tests boolean-result))
           (reversed (proof-proof-symmetric proof equality)))
        (proof-proof-rewrite-result proof step reversed template *proof-result*)))
     (t (proof-with-checked-results
            ((step (b1-fixtypes-lookup-result-type-leaf value tests lib template boolean-result))
             (literal (proof-step-first step))
             (target (proof-subst template (list (cons *proof-result* value)))))
          (if (equal literal target) step '(:failure "failure" "")))))))

(defun b1-fixtypes-lookup-result-type (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((head (proof-term-at formula 0))
         (boolean-result (not (equal head *b1-fixtypes-symbol-listp*)))
         (subject (proof-term-at formula 1))
         (call (if boolean-result (proof-term-at subject 1) subject))
         (template (if boolean-result
                       (let ((is-true (proof-eq *proof-result* *proof-true*)))
                         (proof-ite is-true is-true (proof-eq *proof-result* *proof-false*)))
                     (list *b1-fixtypes-symbol-listp* *proof-result*)))
         (head (proof-term-at call 0))
         (expanded (b1-logic-bookproof-normalize
                    lib call nil (list head *b1-fixtypes-hard-error* *proof-not*) nil nil nil t))
         (value (proof-rewritten-term expanded))
         (step (b1-fixtypes-lookup-result-type-by-value 1000000 lib value template nil boolean-result))
         (reversed (proof-proof-symmetric proof expanded)))
      (proof-proof-rewrite-result proof step reversed template *proof-result*))))

(defun b1-fixtypes-mv-nth-of-cons (lib formula)
  (proof-with-checked-results
      ((claim (proof-term-at formula 2))
       (call (proof-term-at claim 1))
       (equation (b1-logic-bookproof-normalize
                  lib call nil (list *b1-fixtypes-mv-nth* *b1-logic-atom* *proof-not*) nil nil nil t)))
    (b1-logic-bookproof-prove-implication lib formula equation)))

(defun b1-fixtypes-split-result-proper-prove-case (equation known lib projection)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((selected (b1-structures-project-mv lib projection equation))
         (value (proof-rewritten-term selected))
         (goal (list *b1-fixtypes-true-listp* value))
         (reduced (if (proof-is-call value *proof-cons*)
                      (b1-revappend-open-list lib goal nil)
                    (proof-proof-reflexive proof goal)))
         (actual (proof-rewritten-term reduced))
         (result (if (equal actual (list *b1-fixtypes-true-listp* *proof-false*))
                     (proof-with-checked-results
                         ((empty (b1-logic-bookproof-normalize-proof
                                  lib actual nil (list *b1-fixtypes-true-listp* *b1-logic-eq*) nil nil)))
                       (proof-proof-transport proof empty reduced))
                   (if (null known)
                       '(:failure "failure" "")
                     (proof-proof-transport proof known reduced)))))
      (library-library-transport-argument lib result selected 1))))

(defun b1-fixtypes-split-result-proper-base-consequence-reduce (has-value lib atom split split-unfold)
  (b1-logic-bookproof-normalize lib split (list atom has-value) split-unfold nil nil nil nil))

(defun b1-fixtypes-split-result-proper-base-consequence (lib atom split xs projection split-unfold)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((present (proof-proof-assume proof xs t))
         (reduced (b1-fixtypes-split-result-proper-base-consequence-reduce
                   present lib atom split split-unfold))
         (yes (b1-fixtypes-split-result-proper-prove-case reduced nil lib projection))
         (absent (proof-proof-assume proof xs nil))
         (reduced (b1-fixtypes-split-result-proper-base-consequence-reduce
                   absent lib atom split split-unfold))
         (no (b1-fixtypes-split-result-proper-prove-case reduced nil lib projection)))
      (proof-proof-cases proof xs yes no))))

(defun b1-fixtypes-split-result-proper-judgment (consequence lib formula guarded premise)
  (if guarded
      (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)
    consequence))

(defun b1-fixtypes-split-result-proper-base (atom lib formula guarded split xs projection split-unfold)
  (proof-with-checked-results
      ((premise (if guarded (b1-logic-bookproof-prove-implication-premise lib formula) nil))
       (consequence (b1-fixtypes-split-result-proper-base-consequence
                     lib atom split xs projection split-unfold)))
    (b1-fixtypes-split-result-proper-judgment consequence lib formula guarded premise)))

(defun b1-fixtypes-split-result-proper-step-consequence
    (premise lib cons induction guarded split projection split-unfold)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((present (b1-revappend-cons-is-nonempty lib cons))
         (equation (b1-logic-bookproof-normalize
                    lib split (list cons present) split-unfold nil nil nil nil))
         (right (proof-rewritten-term equation))
         (separator (proof-term-at right 1))
         (here (proof-proof-assume proof separator t))
         (there (proof-proof-assume proof separator nil))
         (selected (proof-proof-select proof right here))
         (on-hit (proof-proof-chain proof equation (list selected)))
         (selected (proof-proof-select proof right there))
         (on-miss (proof-proof-chain proof equation (list selected)))
         (value (proof-rewritten-term on-miss))
         (normalized (b1-logic-bookproof-normalize lib value nil nil nil nil nil nil))
         (on-miss (proof-proof-chain proof on-miss (list normalized)))
         (known-tail (if guarded (b1-structures-true-list-tail lib premise cons) nil))
         (child (if guarded (proof-proof-modus-ponens proof induction known-tail) induction))
         (yes (b1-fixtypes-split-result-proper-prove-case on-hit known-tail lib projection))
         (no (b1-fixtypes-split-result-proper-prove-case on-miss child lib projection)))
      (proof-proof-cases proof separator yes no))))

(defun b1-fixtypes-split-result-proper-step
    (cons induction lib formula guarded split projection split-unfold)
  (proof-with-checked-results
      ((premise (if guarded (b1-logic-bookproof-prove-implication-premise lib formula) nil))
       (consequence (b1-fixtypes-split-result-proper-step-consequence
                     premise lib cons induction guarded split projection split-unfold)))
    (b1-fixtypes-split-result-proper-judgment consequence lib formula guarded premise)))

(defun b1-fixtypes-split-result-proper (lib formula)
  (let ((proof (library-library-proof lib))
        (guarded (proof-is-call formula *library-implies*)))
    (proof-with-checked-results
        ((claim (if guarded (proof-term-at formula 2) formula))
         (projection (proof-term-at claim 1))
         (split (proof-term-at projection 2))
         (xs (proof-term-at split 2))
         (split-unfold (list (car split) *b1-fixtypes-hard-error* *b1-logic-atom* *proof-not*))
         (prep (b1-revappend-list-induction-prepare lib formula xs nil))
         (step (b1-fixtypes-split-result-proper-step
                (caddr prep) (cadddr prep) lib formula guarded split projection split-unfold))
         (atom (proof-proof-assume proof (cadr prep) nil))
         (base (b1-fixtypes-split-result-proper-base atom lib formula guarded split xs projection split-unfold)))
      (b1-revappend-list-induction lib prep base step))))

(defun b1-fixtypes-identity-processor-wellformed-consequence (premise lib claim wrapper)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first premise))
         (opened (proof-proof-unfold proof literal))
         (fields (proof-proof-rewrite proof premise opened '(1)))
         (evidence (proof-proof-conjunct proof fields))
         (recognizer (proof-term-at claim 0))
         (unfold (append (list wrapper recognizer) *b1-fixtypes-identity-processor-wellformed-tests*
                         (list *b1-logic-atom* *b1-logic-endp* *proof-not*))))
      (b1-fixtypes-normalize-with-rule lib claim evidence unfold :empty-types t))))

(defun b1-fixtypes-identity-processor-wellformed (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (claim (caddr implication))
       (subject (proof-term-at claim 1))
       (wrapper (proof-term-at subject 0))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-fixtypes-identity-processor-wellformed-consequence premise lib claim wrapper)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))

(defun b1-fixtypes-identity-processor-correct-consequence (premise lib combined)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-proof-conjunct proof premise))
         (inner (proof-proof-conjunct proof (cadr parts)))
         (result (cadr inner))
         (equation (proof-proof-unfold proof combined))
         (argument (proof-term-at combined 1))
         (opened (proof-proof-unfold proof argument))
         (equation (proof-proof-rewrite proof equation opened '(1 2 1 1)))
         (right (proof-rewritten-term equation))
         (mapping (proof-term-at right 1))
         (mapped (b1-fixtypes-normalize-with-rule
                  lib mapping nil
                  (list *b1-fixtypes-identity-processor-correct-map-clauses*
                        *b1-logic-endp* *b1-logic-atom* *proof-not*) :empty-disjunction nil))
         (equation (proof-proof-rewrite proof equation mapped '(1 2 1)))
         (right (proof-rewritten-term equation))
         (normalized (b1-logic-bookproof-normalize
                      lib right nil (list *b1-fixtypes-identity-processor-correct-choose*
                                          *b1-logic-endp* *b1-logic-atom* *proof-not*) nil nil nil nil))
         (equation (proof-proof-chain proof equation (list normalized))))
      (proof-proof-rewrite proof result equation '(1 1)))))

(defun b1-fixtypes-identity-processor-correct (lib formula)
  (proof-with-checked-results
      ((implication (proof-list-of-length formula 3))
       (inner (proof-term-at (cadr implication) 2))
       (evaluation (proof-term-at inner 2))
       (combined (proof-term-at evaluation 1))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-fixtypes-identity-processor-correct-consequence premise lib combined)))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))
