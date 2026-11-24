(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-bit-length-length* (proof-cl "INTEGER-LENGTH"))
(defconst *b1-bit-length-logcdr* (proof-sym "LOGCDR$INLINE" "ACL2"))
(defconst *b1-bit-length-ifloor* (proof-sym "IFLOOR$INLINE" "ACL2"))

(defun b1-bit-length-open-length (lib term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof (list *b1-bit-length-length* term)))
         (opened-first (proof-step-first opened))
         (outer (proof-term-at opened-first 2))
         (outer-false (proof-proof-if-false proof outer))
         (inner (proof-proof-chain proof opened (list outer-false)))
         (inner-first (proof-step-first inner))
         (second (proof-term-at inner-first 2))
         (outer-true (proof-proof-if-true proof outer))
         (base (proof-proof-chain proof opened (list outer-true)))
         (inner-true (proof-proof-if-true proof second))
         (negative-unit (proof-proof-chain proof inner (list inner-true)))
         (inner-false (proof-proof-if-false proof second))
         (body (proof-proof-chain proof inner (list inner-false)))
         (zero-test (proof-term-at outer 1))
         (unit-test (proof-term-at second 1)))
      (list zero-test unit-test base negative-unit body))))

(defun b1-bit-length-natural-bit-length-install (lib)
  (let* ((x *library-x*)
         (claim (list *library-natp* (list *b1-bit-length-length* x)))
         (half (list *b1-quotient-floor* x *b1-bitwise-two*))
         (bindings (list (cons x half))))
    (proof-with-checked-results
        ((branches (b1-bit-length-open-length lib x))
         (descent-name (b1-bitwise-floor-half-descent lib)))
      (let* ((lib (cdr descent-name))
             (proof (library-library-proof lib))
             (zero-test (car branches))
             (unit-test (cadr branches)))
        (proof-with-checked-results
            ((descent (proof-proof-fact proof (car descent-name) nil))
             (no-zero (proof-proof-assume proof zero-test nil))
             (no-unit (proof-proof-assume proof unit-test nil))
             (opened-unit (proof-proof-unfold proof unit-test))
             (no-unit (proof-proof-rewrite proof no-unit opened-unit '(1 1)))
             (descent (proof-proof-discharge proof descent no-zero))
             (descent (proof-proof-discharge proof descent no-unit))
             (descent-test (proof-step-first descent))
             (smaller (proof-subst claim bindings))
             (hypothesis (proof-proof-assume
                          proof (proof-ite descent-test smaller *proof-true*) t))
             (natural-half (proof-proof-prove-if proof hypothesis descent))
             (natural-one (library-library-natural lib *proof-one*))
             (succ (library-library-cite lib "NATURAL-SUM"
                                         (list *proof-one*
                                               (list *b1-bit-length-length* half))
                                         (list natural-one natural-half)))
             (induction (library-library-transport-argument
                         lib succ (car (cddddr branches)) 1))
             (natural-zero (library-library-natural lib *proof-zero*))
             (one-case (library-library-transport-argument
                        lib natural-zero (cadddr branches) 1))
             (no-case (proof-proof-cases proof unit-test one-case induction))
             (zero-case (library-library-transport-argument
                         lib natural-zero (caddr branches) 1))
             (cases (proof-proof-cases proof zero-test zero-case no-case))
             (ordinal (library-library-builtin lib 1 x))
             (inducted (proof-proof-induct
                        proof ordinal cases claim (list *library-count* x)
                        (list (list (list x half))))))
          (library-library-lemma lib "INTEGER-LENGTH-NATURAL" claim inducted nil))))))

(defund b1-bit-length-natural-bit-length (lib term)
  (let ((name (proof-sym "SELF-INTEGER-LENGTH-NATURAL" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (b1-bit-length-natural-bit-length-install lib)))
         (step (proof-proof-fact (library-library-proof lib)
                                 name (list (list *library-x* term)))))
      (cons step lib))))

(defun b1-bit-length-fixed-integer-when-zero (lib term zero)
  (let* ((proof (library-library-proof lib))
         (test (library-integer term))
         (ifix (list *b1-quotient-ifix* term)))
    (proof-with-checked-results
        ((integral (proof-proof-assume proof test t))
         (zero-test (b1-logic-step-first zero))
         (normalized (b1-logic-bookproof-normalize
                      lib zero-test (list integral)
                      (list *b1-quotient-zip* *b1-quotient-numeric-eq*)
                      nil nil nil nil))
         (exact (proof-proof-rewrite proof zero normalized '(1)))
         (fixed (b1-logic-bookproof-normalize
                 lib ifix (list integral) (list *b1-quotient-ifix*) nil nil nil nil))
         (fixed (proof-proof-chain proof fixed (list exact)))
         (noninteger (proof-proof-assume proof test nil))
         (no (b1-logic-bookproof-normalize
              lib ifix (list noninteger) (list *b1-quotient-ifix*) nil nil nil nil)))
      (proof-proof-cases proof test fixed no))))

(defun b1-bit-length-high-bits-at-fixed-point (lib term fixed)
  (let* ((proof (library-library-proof lib))
         (high (list *b1-bit-length-logcdr* term)))
    (proof-with-checked-results
        ((opened (b1-logic-bookproof-normalize
                  lib high nil
                  (list *b1-bit-length-logcdr* *b1-bit-length-ifloor* *b1-quotient-ifix*)
                  (list (b1-logic-equal-to fixed)) nil nil nil))
         (opened-first (proof-step-first opened))
         (opened-value (proof-term-at opened-first 2))
         (normalized (b1-logic-bookproof-normalize
                      lib opened-value nil
                      (list *b1-quotient-floor* *b1-quotient-niq* *b1-quotient-ifix*
                            (proof-sym "NFIX" "ACL2") *b1-quotient-numeric-eq*
                            *b1-quotient-zip* *proof-not*)
                      nil nil nil nil))
         (high-bits (proof-proof-chain proof opened (list normalized)))
         (length-step (proof-proof-reflexive proof (list *b1-bit-length-length* high)))
         (length-step (proof-proof-rewrite proof length-step high-bits '(1 2 1)))
         (length-first (proof-step-first length-step))
         (length-value (proof-term-at length-first 2))
         (normalized-length (b1-logic-bookproof-normalize
                             lib length-value nil
                             (list *b1-bit-length-length* *b1-quotient-zip*
                                   *b1-quotient-numeric-eq*)
                             nil nil nil nil)))
      (proof-proof-chain proof length-step (list normalized-length)))))

(defun b1-bit-length-length-halving-cases-recursive (lib term zero step)
  (let* ((proof (library-library-proof lib))
         (high-bits (list *b1-bit-length-logcdr* term)))
    (proof-with-checked-results
        ((no-zero (proof-proof-assume proof zero nil))
         (integral (b1-logic-bookproof-forces
                    lib (library-integer term) no-zero nil
                    (list *b1-quotient-zip* *b1-quotient-numeric-eq* *proof-not*) nil))
         (high (b1-logic-bookproof-normalize
                lib high-bits (list integral)
                (list *b1-bit-length-logcdr* *b1-bit-length-ifloor* *b1-quotient-ifix*)
                nil nil nil nil))
         (reverse-high (proof-proof-symmetric proof high))
         (parent (proof-proof-rewrite proof step reverse-high '(1 2 2 1)))
         (child (proof-proof-reflexive proof (list *b1-bit-length-length* high-bits))))
      (list :b1-bit-length-case parent child t))))

(defun b1-bit-length-length-halving-cases-unit (lib term unit base)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((unit-test (proof-proof-assume proof unit t))
         (opened (proof-proof-unfold proof unit))
         (raw-unit (proof-proof-rewrite proof unit-test opened '(1)))
         (fixed-unit (b1-logic-bookproof-normalize
                      lib (list *b1-quotient-ifix* term) nil (list *b1-quotient-ifix*)
                      (list (b1-logic-equal-to raw-unit)) nil nil nil))
         (child (b1-bit-length-high-bits-at-fixed-point lib term fixed-unit)))
      (list :b1-bit-length-case base child nil))))

(defund b1-bit-length-length-halving-cases (lib term replies)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((branches (b1-bit-length-open-length lib term))
         (at-zero (proof-proof-assume proof (car branches) t))
         (fixed-zero (b1-bit-length-fixed-integer-when-zero lib term at-zero))
         (child (b1-bit-length-high-bits-at-fixed-point lib term fixed-zero)))
      (if (endp replies)
          (cons (list :b1-bit-length-case (caddr branches) child nil) lib)
        (proof-with-checked-results
            ((zero-reply (car replies))
             (unit-call (b1-bit-length-length-halving-cases-unit
                         (cdr zero-reply) term (cadr branches) (cadddr branches))))
          (if (endp (cdr replies))
              (cons unit-call (cdr zero-reply))
            (proof-with-checked-results
                ((unit-reply (cadr replies))
                 (recursive-call (b1-bit-length-length-halving-cases-recursive
                                  (cdr unit-reply) term
                                  (car branches) (car (cddddr branches)))))
              (if (endp (cddr replies))
                  (cons recursive-call (cdr unit-reply))
                (proof-with-checked-results ((recursive-reply (caddr replies)))
                  (let* ((lib (cdr recursive-reply))
                         (proof (library-library-proof lib)))
                    (proof-with-checked-results
                        ((nonzero (proof-proof-cases
                                   proof (cadr branches) (car unit-reply)
                                   (car recursive-reply)))
                         (step (proof-proof-cases proof (car branches)
                                                 (car zero-reply) nonzero)))
                      (cons step lib))))))))))))

(defun b1-bit-length-sum-naturals (lib lengths)
  (declare (xargs :measure (len lengths)))
  (if (endp lengths)
      (cons nil lib)
    (proof-with-checked-results
        ((term (proof-term-at (car lengths) 1))
         (natural (b1-bit-length-natural-bit-length lib term))
         (rest (b1-bit-length-sum-naturals (cdr natural) (cdr lengths))))
      (cons (cons (car natural) (car rest)) (cdr rest)))))

(defun b1-bit-length-bit-length-sum-ordinal (lib measure)
  (if (integerp measure)
      '(:failure "failure" "")
    (proof-with-checked-results
        ((naturals (b1-bit-length-sum-naturals lib (cdr measure)))
         (sum (library-library-cite (cdr naturals) "NATURAL-SUM"
                                    (cdr measure) (car naturals)))
         (ordinal (library-library-cite (cdr naturals) "NATURAL-ORDINAL"
                                        (list measure) (list sum))))
      (cons ordinal (cdr naturals)))))

(defund b1-bit-length-paired-bit-length-descent-integer (lib length)
  (proof-with-checked-results
      ((term (proof-term-at length 1))
       (natural (b1-bit-length-natural-bit-length lib term))
       (integral (library-library-cite (cdr natural) "NATURAL-INTEGER"
                                       (list length) (list (car natural)))))
    (cons integral (cdr natural))))

(defun b1-bit-length-paired-bit-length-descent-integers (lib lengths)
  (declare (xargs :measure (len lengths)))
  (if (endp lengths)
      (cons nil lib)
    (proof-with-checked-results
        ((integral (b1-bit-length-paired-bit-length-descent-integer lib (car lengths)))
         (rest (b1-bit-length-paired-bit-length-descent-integers
                (cdr integral) (cdr lengths))))
      (cons (cons (car integral) (car rest)) (cdr rest)))))

(defund b1-bit-length-paired-bit-length-descent-combine
    (parent-a child-a step-a parent-b child-b step-b
     lib goal stop-test child parent integers ordinal-comparison)
  (let ((proof (library-library-proof lib)))
    (if (not (or step-a step-b))
        (proof-with-checked-results
            ((stop (b1-logic-bookproof-normalize-proof
                    lib stop-test nil (list *b1-logic-zp* *proof-not*)
                    (list (b1-logic-equal-to parent-a) (b1-logic-equal-to parent-b))
                    nil))
             (continue (proof-proof-assume proof stop-test nil))
             (impossible (proof-proof-cut proof stop continue)))
          (proof-proof-subsume proof impossible (cons goal (proof-step-clause impossible))))
      (proof-with-checked-results
          ((parent-expanded (proof-proof-reflexive proof parent))
           (parent-expanded (proof-proof-rewrite proof parent-expanded parent-a '(1 2 1)))
           (parent-expanded (proof-proof-rewrite proof parent-expanded parent-b '(1 2 2)))
           (child-expanded (proof-proof-reflexive proof child))
           (child-expanded (proof-proof-rewrite proof child-expanded child-a '(1 2 1)))
           (child-expanded (proof-proof-rewrite proof child-expanded child-b '(1 2 2)))
           (child-first (proof-step-first child-expanded))
           (child-value (proof-term-at child-first 2))
           (parent-first (proof-step-first parent-expanded))
           (parent-value (proof-term-at parent-first 2))
           (positive (proof-proof-prove
                      proof (library-positive (if (and step-a step-b)
                                                  *b1-bitwise-two*
                                                *proof-one*))
                      nil nil))
           (strict (library-library-less-from-difference
                    lib child-value parent-value positive integers))
           (strict (library-library-transport-argument lib strict parent-expanded 2))
           (strict (library-library-transport-argument lib strict child-expanded 1)))
        (proof-proof-transport proof strict ordinal-comparison)))))

(defund b1-bit-length-paired-bit-length-descent-first-case
    (n left-case lib right goal stop-test child parent integers ordinal-comparison replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "b1-bit-length-paired-bit-length-descent-first-case")
    (proof-with-checked-results
        ((result (b1-bit-length-length-halving-cases lib right replies)))
      (let ((right-case (car result))
            (current-lib (cdr result)))
        (if (eq (car right-case) :b1-bit-length-case)
            (proof-with-checked-results
                ((step (b1-bit-length-paired-bit-length-descent-combine
                        (cadr left-case) (caddr left-case) (cadddr left-case)
                        (cadr right-case) (caddr right-case) (cadddr right-case)
                        current-lib goal stop-test child parent integers ordinal-comparison)))
              (b1-bit-length-paired-bit-length-descent-first-case
               (1- n) left-case lib right goal stop-test child parent integers
               ordinal-comparison (append replies (list (cons step current-lib)))))
          result)))))

(defun b1-bit-length-paired-bit-length-descent-cases
    (n lib left right goal stop-test child parent integers ordinal-comparison replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "b1-bit-length-paired-bit-length-descent-cases")
    (proof-with-checked-results
        ((result (b1-bit-length-length-halving-cases lib left replies)))
      (let ((left-case (car result)))
        (if (eq (car left-case) :b1-bit-length-case)
            (proof-with-checked-results
                ((reply (b1-bit-length-paired-bit-length-descent-first-case
                         1000000 left-case (cdr result) right goal stop-test child
                         parent integers ordinal-comparison nil)))
              (b1-bit-length-paired-bit-length-descent-cases
               (1- n) lib left right goal stop-test child parent integers ordinal-comparison
               (append replies (list reply))))
          result)))))

(defun b1-bit-length-length-arguments (lengths)
  (if (endp lengths)
      nil
    (proof-with-checked-results
        ((argument (proof-term-at (car lengths) 1))
         (rest (b1-bit-length-length-arguments (cdr lengths))))
      (cons argument rest))))

(defun b1-bit-length-paired-bit-length-descent (lib goal stop-test)
  (proof-with-checked-results ((parts (proof-list-of-length goal 3)))
    (let ((child (cadr parts))
          (parent (caddr parts)))
      (proof-with-checked-results
          ((terms (if (integerp parent)
                      '(:failure "failure" "")
                    (b1-bit-length-length-arguments (seq-slice (cdr parent) 0 3))))
           (terms (proof-list-of-length terms 2))
           (integers (if (integerp child)
                         '(:failure "failure" "")
                       (b1-bit-length-paired-bit-length-descent-integers
                        lib (append (cdr child) (cdr parent)))))
           (child-integer (library-library-type-of (cdr integers) child (car integers)))
           (parent-integer (library-library-type-of (cdr integers) parent (car integers)))
           (ordinal-comparison (library-library-cite
                                (cdr integers) "FINITE-ORDER" (list child parent)
                                (list child-integer parent-integer))))
        (b1-bit-length-paired-bit-length-descent-cases
         1000000 (cdr integers) (car terms) (cadr terms) goal stop-test child parent
         (car integers) ordinal-comparison nil)))))

(defun b1-bit-length-integer-non-nil (lib integral)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (b1-logic-step-first integral))
         (value (proof-term-at literal 1))
         (empty (proof-eq value *proof-false*))
         (assumed (proof-proof-assume proof empty t))
         (reduced (proof-proof-rewrite proof integral assumed '(1 1)))
         (constant (b1-logic-bookproof-constant lib (library-integer *proof-false*)))
         (reduced (proof-proof-rewrite proof reduced constant '(1)))
         (non-nil (proof-proof-nil-or-true proof value))
         (tidied (proof-proof-tidy proof reduced))
         (not-empty (proof-proof-front proof tidied (proof-neg empty))))
      (proof-proof-cut proof non-nil not-empty))))

(defun b1-bit-length-mismatch-is-integer-leaf (value tests lib connective child-call hypothesis)
  (declare (ignore tests))
  (let* ((proof (library-library-proof lib))
         (claim (list connective (library-integer value) value))
         (unfold (list connective)))
    (cond ((equal value *proof-false*)
           (b1-logic-bookproof-normalize-proof lib claim nil unfold nil nil))
          ((equal value *proof-zero*)
           (proof-with-checked-results
               ((integer-zero (library-library-type-of lib *proof-zero* nil)))
             (b1-logic-bookproof-normalize-proof lib claim (list integer-zero) unfold nil nil)))
          (t
           (proof-with-checked-results
               ((child-present (proof-proof-assume proof child-call t))
                (child-type (b1-logic-bookproof-forces
                             lib (library-integer child-call) hypothesis
                             (list child-present) unfold nil))
                (integral (library-library-type-of lib value (list child-type)))
                (non-nil (b1-bit-length-integer-non-nil lib integral)))
             (b1-logic-bookproof-normalize-proof lib claim (list integral non-nil)
                                                 unfold nil nil))))))

(defun b1-bit-length-mismatch-is-integer-by-value
    (n lib value template tests connective child-call hypothesis)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((zp n) '(:failure "Fuel" "b1-bit-length-mismatch-is-integer-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (yes (b1-bit-length-mismatch-is-integer-by-value
                 (1- n) lib (cadr branches) template
                 (append tests (list (list (car branches) t)))
                 connective child-call hypothesis))
           (no (b1-bit-length-mismatch-is-integer-by-value
                (1- n) lib (caddr branches) template
                (append tests (list (list (car branches) nil)))
                connective child-call hypothesis))
           (if-true (proof-proof-if-true proof value))
           (true-equality (proof-proof-symmetric proof if-true))
           (yes (proof-proof-rewrite-result proof yes true-equality template *proof-result*))
           (if-false (proof-proof-if-false proof value))
           (false-equality (proof-proof-symmetric proof if-false))
           (no (proof-proof-rewrite-result proof no false-equality template *proof-result*)))
        (proof-proof-cases proof (car branches) yes no)))
     ((and (proof-compound value) (not (consp value)))
      '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((equality (proof-proof-beta proof value))
           (literal (proof-step-first equality))
           (value (proof-term-at literal 2))
           (opened (b1-bit-length-mismatch-is-integer-by-value
                    (1- n) lib value template tests connective child-call hypothesis))
           (reversed (proof-proof-symmetric proof equality)))
        (proof-proof-rewrite-result proof opened reversed template *proof-result*)))
     (t (proof-with-checked-results
            ((step (b1-bit-length-mismatch-is-integer-leaf
                    value tests lib connective child-call hypothesis))
             (literal (proof-step-first step))
             (target (proof-subst template (list (cons *proof-result* value)))))
          (if (equal literal target) step '(:failure "failure" "")))))))

(defun b1-bit-length-mismatch-is-integer (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (call (caddr parts))
       (args (if (integerp call)
                 '(:failure "failure" "")
               (proof-list-of-length (cdr call) 2))))
    (let* ((a (car args))
           (b (cadr args))
           (length-a (list *b1-bit-length-length* a))
           (length-b (list *b1-bit-length-length* b))
           (measure (library-plus length-a length-b))
           (high-a (list *b1-bit-length-logcdr* a))
           (high-b (list *b1-bit-length-logcdr* b))
           (pairs (list (list a high-a) (list b high-b)))
           (bindings (table-put (list (cons a high-a)) b high-b))
           (stop (proof-ite (list *b1-logic-zp* length-a)
                            (list *b1-logic-zp* length-b) *proof-false*))
           (connective (car parts)))
      (proof-with-checked-results
          ((smaller (proof-subst measure bindings))
           (descent (b1-bit-length-paired-bit-length-descent
                     lib (list *proof-ordinal-less* smaller measure) stop)))
        (let* ((lib (cdr descent))
               (proof (library-library-proof lib)))
          (proof-with-checked-results
              ((child-formula (proof-subst formula bindings))
               (descends (proof-step-first (car descent)))
               (start (proof-proof-assume
                       proof (proof-ite descends child-formula *proof-true*) t))
               (hypothesis (proof-proof-prove-if proof start (car descent)))
               (child-call (proof-term-at child-formula 2))
               (template (list connective (library-integer *proof-result*) *proof-result*))
               (equation (proof-proof-unfold proof call))
               (equation-first (proof-step-first equation))
               (value (proof-term-at equation-first 2))
               (step (b1-bit-length-mismatch-is-integer-by-value
                      1000000 lib value template nil connective child-call hypothesis))
               (reversed (proof-proof-symmetric proof equation))
               (step (proof-proof-rewrite-result proof step reversed template *proof-result*))
               (ordinal (b1-bit-length-bit-length-sum-ordinal lib measure))
               (induction (proof-proof-induct (library-library-proof (cdr ordinal))
                                              (car ordinal) step formula measure (list pairs))))
            (cons induction (cdr ordinal))))))))
