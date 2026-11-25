(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-bit-types-expt* (proof-cl "EXPT"))
(defconst *b1-bit-types-lognot* (proof-cl "LOGNOT"))
(defconst *b1-bit-types-fix* (proof-sym "FIX" "ACL2"))
(defconst *b1-bit-types-bfix* (proof-sym "BFIX$INLINE" "ACL2"))
(defconst *b1-bit-types-logand* (proof-sym "BINARY-LOGAND" "ACL2"))
(defconst *b1-bit-types-logior* (proof-sym "BINARY-LOGIOR" "ACL2"))
(defconst *b1-bit-types-imod* (proof-sym "IMOD$INLINE" "ACL2"))
(defconst *b1-bit-types-expt2* (proof-sym "EXPT2$INLINE" "ACL2"))
(defconst *b1-bit-types-logcar* (proof-sym "LOGCAR$INLINE" "ACL2"))
(defconst *b1-bit-types-logcons* (proof-sym "LOGCONS$INLINE" "ACL2"))
(defconst *b1-bit-types-logrev1* (proof-sym "LOGREV1" "ACL2"))
(defconst *b1-bit-types-builtin-nfix* (proof-sym "NFIX" "ACL2"))

(defconst *b1-bit-types-typed-operations*
  (list (cons (proof-sym "IFLOOR$INLINE" "ACL2") (proof-sym "IFLOOR-TYPE" "ACL2"))
        (cons *b1-bit-types-imod* (proof-sym "IMOD-TYPE" "ACL2"))
        (cons *b1-bit-types-expt2* (proof-sym "EXPT2-TYPE" "ACL2"))
        (cons *b1-bit-types-logcar* (proof-sym "LOGCAR-TYPE" "ACL2"))
        (cons (proof-sym "LOGCDR$INLINE" "ACL2") (proof-sym "LOGCDR-TYPE" "ACL2"))
        (cons *b1-bit-types-logcons* (proof-sym "LOGCONS-TYPE" "ACL2"))
        (cons (proof-sym "LOGMASK$INLINE" "ACL2") (proof-sym "LOGMASK-TYPE" "ACL2"))
        (cons (proof-sym "LOGHEAD$INLINE" "ACL2") (proof-sym "LOGHEAD-TYPE" "ACL2"))
        (cons (proof-sym "LOGTAIL$INLINE" "ACL2") (proof-sym "LOGTAIL-TYPE" "ACL2"))
        (cons (proof-sym "LOGAPP" "ACL2") (proof-sym "LOGAPP-TYPE" "ACL2"))
        (cons (proof-sym "LOGRPL" "ACL2") (proof-sym "LOGRPL-TYPE" "ACL2"))
        (cons (proof-sym "LOGEXT" "ACL2") (proof-sym "LOGEXT-TYPE" "ACL2"))))

(defund b1-bit-types-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defund b1-bit-types-normalize (lib value evidence unfold)
  (b1-logic-bookproof-normalize lib value evidence unfold nil nil nil nil))

(defund b1-bit-types-unfold (lib value)
  (proof-proof-unfold (library-library-proof lib) value))

(defund b1-bit-types-beta (lib value)
  (proof-proof-beta (library-library-proof lib) value))

(defun b1-bit-types-typed-bit-is-natural-present (test lib)
  (proof-with-checked-results
      ((equation (proof-proof-assume (library-library-proof lib) test t))
       (value (proof-term-at test 2))
       (natural (library-library-natural lib value)))
    (library-library-transport-argument lib natural equation 1)))

(defun b1-bit-types-typed-bit-is-natural (lib bit)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first bit))
         (value (proof-term-at literal 1)))
      (let ((zero (proof-eq value *proof-zero*))
            (one (proof-eq value *proof-one*)))
        (proof-with-checked-results
            ((not-zero (proof-proof-assume proof zero nil))
             (not-one (proof-proof-assume proof one nil))
             (zero-false (b1-logic-bookproof-false-value lib not-zero))
             (zero-rule (b1-logic-equal-to zero-false))
             (one-false (b1-logic-bookproof-false-value lib not-one))
             (one-rule (b1-logic-equal-to one-false))
             (computed (b1-logic-bookproof-normalize
                        lib literal (list not-zero not-one)
                        (list *b1-fixer-laws-bitp* *b1-logic-eql* *b1-logic-eq*)
                        (list zero-rule one-rule) nil nil nil))
             (rewritten (proof-proof-rewrite proof bit computed '(1)))
             (not-nil (b1-logic-proof-not-nil proof))
             (impossible (b1-logic-bookproof-contradiction
                          lib rewritten not-nil (list *library-natp* value)))
             (at-zero (b1-bit-types-typed-bit-is-natural-present zero lib))
             (at-one (b1-bit-types-typed-bit-is-natural-present one lib))
             (nonzero (proof-proof-cases proof one at-one impossible)))
          (proof-proof-cases proof zero at-zero nonzero))))))

(defun b1-bit-types-prior-type (lib value)
  (proof-with-checked-results ((head (proof-term-at value 0)))
    (let* ((proof (library-library-proof lib))
           (name (table-get *b1-bit-types-typed-operations* head nil)))
      (if (not (assoc-equal name (proof-proof-facts proof)))
          nil
        (proof-with-checked-results
            ((theorem (proof-proof-fact proof name nil))
             (literal (proof-step-first theorem))
             (normalized (b1-logic-bookproof-normalize lib literal nil nil nil nil nil nil))
             (opened (proof-proof-rewrite proof theorem normalized '(1)))
             (pattern (b1-bit-types-step-at opened 1))
             (matched (b1-logic-match pattern value nil)))
          (if (car matched)
              (proof-proof-instantiate proof opened (table-items (cdr matched)))
            '(:failure "failure" "")))))))

(defun b1-bit-types-floor-integer (lib floor x-type y-type)
  (proof-with-checked-results
      ((x (proof-term-at floor 1))
       (y (proof-term-at floor 2))
       (rational (b1-arithmetic-known-type
                  lib *library-rationalp*
                  (b1-arithmetic-product x (b1-arithmetic-reciprocal y))
                  (list x-type y-type)))
       (interval (b1-floor-interval lib floor rational)))
    (cons (caar interval) (cdr interval))))

(defun b1-bit-types-mod-two-equation-branch (fact lib bits explained mod half integral int-half)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((selected (proof-proof-select proof bits fact))
         (reconstructed (proof-proof-rewrite proof explained selected '(1 2 2)))
         (definition (proof-proof-unfold proof mod))
         (opened (proof-proof-rewrite proof definition reconstructed '(1 2 1)))
         (oriented (library-library-axiom lib "COMMUTATIVITY-OF-*" (list half *b1-bits-two*)))
         (opened (proof-proof-rewrite proof opened oriented '(1 2 2 1)))
         (left (b1-bit-types-step-at opened 2))
         (right (b1-bit-types-step-at selected 2))
         (cancel (library-library-linear-equal lib left right (list integral int-half)))
         (reversed (proof-proof-symmetric proof selected)))
      (proof-proof-chain proof opened (list cancel reversed)))))

(defund b1-bit-types-mod-two-equation (lib integral)
  (proof-with-checked-results
      ((value (b1-bit-types-step-at integral 1))
       (explained (b1-bits-decomposition lib integral)))
    (let* ((lib (cdr explained))
           (mod (list *b1-modular-mod* value *b1-bits-two*))
           (half (list *b1-quotient-floor* value *b1-bits-two*)))
      (proof-with-checked-results
          ((int-two (library-library-type-of lib *b1-bits-two* nil))
           (int-half (b1-bit-types-floor-integer lib half integral int-two)))
        (let* ((lib (cdr int-half))
               (proof (library-library-proof lib))
               (bits (b1-bits-low-bit value))
               (test (list *b1-bits-evenp* value)))
          (proof-with-checked-results
              ((even (proof-proof-assume proof test t))
               (yes (b1-bit-types-mod-two-equation-branch
                     even lib bits (car explained) mod half integral (car int-half)))
               (odd (proof-proof-assume proof test nil))
               (no (b1-bit-types-mod-two-equation-branch
                    odd lib bits (car explained) mod half integral (car int-half)))
               (result (proof-proof-cases proof test yes no)))
            (cons result lib)))))))

(defun b1-bit-types-power-unit-type (lib step unit)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (library-library-transport-argument lib step unit (1- (len literal)))))

(defun b1-bit-types-positive-power-of-two-consequence (premise lib value typed formula bindings zero)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reflexive (proof-proof-reflexive proof value))
         (at-zero (proof-proof-assume proof zero t))
         (unit (proof-proof-rewrite proof reflexive at-zero '(1 2 2)))
         (expt-zero (b1-powers-expt-zero lib *b1-bits-two*))
         (unit (proof-proof-chain proof unit (list expt-zero)))
         (int-one (library-library-type-of lib *proof-one* nil))
         (pos-one (proof-proof-prove proof (library-positive *proof-one*) nil nil))
         (int-unit (b1-bit-types-power-unit-type lib int-one unit))
         (pos-unit (b1-bit-types-power-unit-type lib pos-one unit))
         (yes (b1-logic-bookproof-normalize-proof lib typed (list int-unit pos-unit) nil nil nil))
         (nonzero (proof-proof-assume proof zero nil))
         (predecessor (b1-powers-natural-predecessor lib premise nonzero))
         (descent (proof-step-first (cadr predecessor)))
         (child (proof-subst formula bindings))
         (case-step (proof-proof-assume proof (proof-ite descent child *proof-true*) t))
         (hypothesis (proof-proof-prove-if proof case-step (cadr predecessor)))
         (child-proof (proof-proof-modus-ponens proof hypothesis (car predecessor)))
         (child-types (proof-proof-conjunct proof child-proof))
         (integer-index (library-library-cite lib "NATURAL-INTEGER" (list *library-x*) (list premise)))
         (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE" (list *library-x*) (list premise)))
         (comparison (b1-arithmetic-integer-compare lib *library-x* *proof-zero* (list integer-index)))
         (bounded (proof-proof-discharge proof comparison nonnegative))
         (bigger (proof-proof-discharge proof bounded nonzero))
         (view (b1-logic-bookproof-normalize
                lib value (list integer-index bigger nonzero)
                (list *b1-bit-types-expt* *b1-quotient-zip* *b1-quotient-numeric-eq*
                      *b1-logic-eql* *b1-bit-types-fix* *proof-not*)
                nil nil nil nil))
         (product (b1-bit-types-step-at view 2))
         (multiplied (library-library-type-of lib product (list (car child-types))))
         (pos-two (proof-proof-prove proof (library-positive *b1-bits-two*) nil nil))
         (product-positive (b1-arithmetic-positive-product
                            lib pos-two (cadr child-types) (list (car child-types))))
         (integer (library-library-transport-argument lib multiplied view 1))
         (positive (library-library-transport-argument lib product-positive view 2))
         (no (b1-logic-bookproof-normalize-proof lib typed (list integer positive) nil nil nil)))
      (proof-proof-cases proof zero yes no))))

(defun b1-bit-types-positive-power-of-two-library (lib name)
  (let ((proof (library-library-proof lib)))
    (if (assoc-equal name (proof-proof-facts proof))
        lib
      (let* ((atom (list *library-natp* *library-x*))
             (value (list *b1-bit-types-expt* *b1-bits-two* *library-x*))
             (typed (proof-ite (library-integer value) (library-positive value) *proof-false*))
             (formula (list *library-implies* atom typed))
             (next-index (library-plus *library-x* *proof-neg-one*))
             (bindings (list (cons *library-x* next-index)))
             (zero (proof-eq *library-x* *proof-zero*)))
        (proof-with-checked-results
            ((ordinal (library-library-builtin lib 1 *library-x*))
             (premise (b1-logic-bookproof-prove-implication-premise lib formula))
             (consequence (b1-bit-types-positive-power-of-two-consequence
                           premise lib value typed formula bindings zero))
             (induction-case (b1-logic-bookproof-prove-implication-with-premise
                              lib formula premise consequence))
             (result (proof-proof-induct proof ordinal induction-case formula
                                        (list *library-count* *library-x*)
                                        (list (table-items bindings)))))
          (library-library-lemma lib "POSITIVE-POWER-OF-TWO" formula result nil))))))

(defun b1-bit-types-positive-power-of-two (lib exponent natural)
  (let ((name (proof-sym "SELF-POSITIVE-POWER-OF-TWO" "ACL2")))
    (proof-with-checked-results ((lib (b1-bit-types-positive-power-of-two-library lib name)))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((law (proof-proof-fact proof name (list (list *library-x* exponent))))
             (consequence (proof-proof-modus-ponens proof law natural))
             (steps (proof-proof-conjunct proof consequence)))
          (cons steps lib))))))

(defund b1-bit-types-exponent-types (n lib term)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "b1-bit-types-exponent-types"))
   ((proof-is-call term *b1-bit-types-expt2*)
    (proof-with-checked-results
        ((opened (b1-bit-types-normalize lib term nil (list *b1-bit-types-expt2*)))
         (raw (b1-bit-types-step-at opened 2))
         (types (b1-bit-types-exponent-types (1- n) lib raw))
         (integer (library-library-transport-argument (cdr types) (caar types) opened 1))
         (positive (library-library-transport-argument (cdr types) (cadar types) opened 2)))
      (cons (list integer positive) (cdr types))))
   (t (proof-with-checked-results ((parts (proof-list-of-length term 3)))
        (if (not (equal (cadr parts) *b1-bits-two*))
            '(:failure "failure" "")
          (let ((exponent (caddr parts)))
            (proof-with-checked-results ((natural (b1-integer-nfix-natural lib exponent)))
              (b1-bit-types-positive-power-of-two lib exponent natural))))))))

(defun b1-bit-types-result-with-library (result lib)
  (if (failure-p result) result (cons result lib)))

(defund b1-bit-types-evidence-type (claim evidence)
  (if (endp evidence)
      nil
    (proof-with-checked-results ((literal (proof-step-first (car evidence))))
      (if (equal literal claim)
          (car evidence)
        (b1-bit-types-evidence-type claim (cdr evidence))))))

(defund b1-bit-types-prior-proof (lib predicate value claim)
  (proof-with-checked-results ((previous (b1-bit-types-prior-type lib value)))
    (and previous
         (proof-with-checked-results ((literal (proof-step-first previous)))
           (if (equal literal claim)
               previous
             (proof-with-checked-results
                 ((head (proof-term-at literal 0))
                  (previous (if (equal head *b1-fixer-laws-bitp*)
                                (b1-bit-types-typed-bit-is-natural lib previous)
                              previous)))
               (if (and (equal head *b1-fixer-laws-bitp*)
                        (equal predicate *library-natp*))
                   previous
                 (proof-with-checked-results ((head (b1-bit-types-step-at previous 0)))
                   (and (equal head *library-natp*)
                        (equal predicate *proof-integerp*)
                        (library-library-cite lib "NATURAL-INTEGER" (list value) (list previous)))))))))))

(defun b1-bit-types-integer-fix-leaf (value lib)
  (if (equal value *proof-zero*)
      (library-library-type-of lib *proof-zero* nil)
    (proof-proof-assume (library-library-proof lib) (library-integer value) t)))

(defun b1-bit-types-bit-leaf (value lib)
  (b1-logic-bookproof-normalize-proof
   lib (list *b1-fixer-laws-bitp* value) nil
   (list *b1-fixer-laws-bitp* *b1-logic-eql* *b1-logic-eq*) nil nil))

(defun b1-bit-types-bit-predicate (lib predicate value bit)
  (if (equal predicate *b1-fixer-laws-bitp*)
      bit
    (proof-with-checked-results ((natural (b1-bit-types-typed-bit-is-natural lib bit)))
      (if (equal predicate *library-natp*)
          natural
        (library-library-cite lib "NATURAL-INTEGER" (list value) (list natural))))))

(defun b1-bit-types-by-value-join (lib value template yes no)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((if-true (proof-proof-if-true proof value))
         (true-equality (proof-proof-symmetric proof if-true))
         (yes (proof-proof-rewrite-result proof yes true-equality template *proof-result*))
         (if-false (proof-proof-if-false proof value))
         (false-equality (proof-proof-symmetric proof if-false))
         (no (proof-proof-rewrite-result proof no false-equality template *proof-result*)))
      (proof-proof-cases proof (cadr value) yes no))))

(defun b1-bit-types-exponent-predicate (types predicate value)
  (let ((integral (caar types))
        (lower (cadar types))
        (lib (cdr types)))
    (if (equal predicate *proof-integerp*)
        (cons integral lib)
      (proof-with-checked-results
          ((nonnegative (library-library-cite
                         lib "POSITIVE-NONNEGATIVE" (list value) (list integral lower)))
           (natural (library-library-cite
                     lib "NATURAL-FROM-BOUNDS" (list value) (list integral nonnegative))))
        (cons natural lib)))))

(defun b1-bit-types-shifted-exponent-natural (n lib value)
  (proof-with-checked-results
      ((power (proof-term-at value 2))
       (types (b1-bit-types-exponent-types n lib power))
       (shifted (b1-abstract-lists-shifted-positive-index
                 (cdr types) value (caar types) (cadar types))))
    (b1-bit-types-result-with-library
     (library-library-cite (cdr shifted) "NATURAL-FROM-BOUNDS" (list value) (car shifted))
     (cdr shifted))))

(defund b1-bit-types-modulus-view (lib view divisor fixed integral)
  (if (equal fixed divisor)
      view
    (proof-with-checked-results
        ((reduction (b1-logic-bookproof-normalize
                     lib divisor (list integral) (list *b1-quotient-ifix*) nil nil nil nil)))
      (proof-proof-rewrite (library-library-proof lib) view reduction '(1 2 2)))))

(defun b1-bit-types-logrev-definition (lib)
  (let ((entry (assoc-equal *b1-bit-types-logrev1*
                            (proof-proof-definitions (library-library-proof lib)))))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun b1-bit-types-arguments (term)
  (if (integerp term)
      '(:failure "failure" "")
    (cdr term)))

(defun b1-bit-types-floor-evidence (lib floor evidence)
  (case (len evidence)
    (2 (b1-bit-types-floor-integer lib floor (car evidence) (cadr evidence)))
    (0 '(:failure "failure" ""))
    (1 '(:failure "failure" ""))
    (otherwise '(:failure "failure" ""))))

(defund b1-bit-types-and-integer-hypothesis (lib claim bindings)
  (proof-with-checked-results ((lemma (b1-bitwise-floor-half-descent lib)))
    (let* ((lib (cdr lemma))
           (proof (library-library-proof lib))
           (unit (list *b1-logic-eql* *library-x* *proof-neg-one*)))
      (proof-with-checked-results
          ((descent (proof-proof-fact proof (car lemma) nil))
           (no-unit (proof-proof-assume proof unit nil))
           (opened (b1-bit-types-normalize lib unit nil (list *b1-logic-eql* *b1-logic-eq*)))
           (no-unit (proof-proof-rewrite proof no-unit opened '(1 1)))
           (no-zip (proof-proof-assume proof (list *b1-quotient-zip* *library-x*) nil))
           (descent (proof-proof-discharge proof descent no-zip))
           (descent (proof-proof-discharge proof descent no-unit))
           (antecedent (proof-step-first descent))
           (child (proof-subst claim bindings))
           (inductive (proof-proof-assume proof (proof-ite antecedent child *proof-true*) t))
           (hypothesis (proof-proof-prove-if proof inductive descent)))
        (cons hypothesis lib)))))

(defund b1-bit-types-bit-modulus-view (lib value)
  (proof-with-checked-results
      ((view (b1-bit-types-normalize lib value nil (list *b1-bit-types-imod*)))
       (mod (b1-bit-types-step-at view 2))
       (divisor (proof-term-at mod 2))
       (base (b1-bit-types-normalize lib divisor nil (list *b1-quotient-ifix*)))
       (base-value (b1-bit-types-step-at base 2)))
    (if (not (equal base-value *b1-bits-two*))
        '(:failure "failure" "")
      (proof-with-checked-results
          ((view (proof-proof-rewrite (library-library-proof lib) view base '(1 2 2)))
           (mod (b1-bit-types-step-at view 2))
           (dividend (proof-term-at mod 1)))
        (cons dividend view)))))

(defund b1-bit-types-reverse-is-natural-closed-case (lib carry closed premise)
  (proof-with-checked-results
      ((int-carry (library-library-cite lib "NATURAL-INTEGER" (list carry) (list premise)))
       (end (b1-bit-types-step-at closed 2))
       (fixed (b1-bit-types-normalize lib end (list int-carry) (list *b1-quotient-ifix*)))
       (fixed (proof-proof-chain (library-library-proof lib) closed (list fixed)))
       (yes (library-library-transport-argument lib premise fixed 1)))
    (list int-carry yes)))

(defund b1-bit-types-reverse-is-natural-branches (lib source test)
  (let ((proof (library-library-proof lib))
        (unfold (list *b1-bit-types-logrev1*)))
    (proof-with-checked-results
        ((end (proof-proof-assume proof test t))
         (continue (proof-proof-assume proof test nil))
         (closed (b1-bit-types-normalize lib source (list end) unfold))
         (advanced (b1-bit-types-normalize lib source (list continue) unfold)))
      (list closed advanced))))

(defund b1-bit-types-reverse-is-natural-induction-premises (lib formula index previous bindings)
  (proof-with-checked-results
      ((hypothesis (b1-abstract-lists-decreased-formula lib formula index previous bindings))
       (ordinal (library-library-cite lib "NFIX-ORDINAL" (list index) nil))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula)))
    (list hypothesis ordinal premise)))

; Each conditional visits the true branch before the false branch. A later
; branch starts with the Library returned by the preceding branch.
(mutual-recursion

 (defun b1-bit-types-by-value (n lib value template recipe context)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "b1-bit-types-by-value"))
    ((proof-is-call value *proof-if*)
     (proof-with-checked-results
         ((branches (proof-list-of-length (cdr value) 3))
          (yes (b1-bit-types-by-value (1- n) lib (cadr branches) template recipe context))
          (no (b1-bit-types-by-value (1- n) (cdr yes) (caddr branches) template recipe context))
          (step (b1-bit-types-by-value-join (cdr no) value template (car yes) (car no))))
       (cons step (cdr no))))
    ((and (proof-compound value) (not (consp value)))
     '(:failure "failure" ""))
    ((and (proof-compound value) (proof-compound (car value)))
     (proof-with-checked-results
         ((equality (b1-bit-types-beta lib value))
          (opened (b1-bit-types-step-at equality 2))
          (selected (b1-bit-types-by-value (1- n) lib opened template recipe context))
          (reversed (proof-proof-symmetric (library-library-proof (cdr selected)) equality))
          (step (proof-proof-rewrite-result (library-library-proof (cdr selected))
                                            (car selected) reversed template *proof-result*)))
       (cons step (cdr selected))))
    (t
     (proof-with-checked-results
         ((result
           (case recipe
             (:integer-fix
              (b1-bit-types-result-with-library (b1-bit-types-integer-fix-leaf value lib) lib))
             (:bit
              (b1-bit-types-result-with-library (b1-bit-types-bit-leaf value lib) lib))
             (:and-integer
              (b1-bit-types-and-integer-leaf (1- n) value nil lib (car context) (cadr context)))
             (otherwise
              (b1-bit-types-numeric-type (1- n) lib (car template) value context))))
          (literal (proof-step-first (car result)))
          (target (proof-subst template (list (cons *proof-result* value)))))
       (if (equal literal target)
           result
         '(:failure "failure" ""))))))

 (defun b1-bit-types-integer-fix-visit (n lib value)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-bit-types-integer-fix-visit")
     (proof-with-checked-results
         ((view (b1-bit-types-unfold lib value))
          (body (b1-bit-types-step-at view 2))
          (selected (b1-bit-types-by-value (1- n) lib body
                                          (list *proof-integerp* *proof-result*) :integer-fix nil)))
       (library-library-transport-argument lib (car selected) view 1))))

 (defun b1-bit-types-and-integer-leaf (n value tests lib claim bindings)
   (declare (ignore tests)
            (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "b1-bit-types-and-integer-leaf"))
    ((or (equal value *library-x*) (equal value *library-y*))
     (proof-with-checked-results
         ((negative (proof-proof-assume (library-library-proof lib) (list *b1-quotient-zip* value) nil))
          (step (b1-logic-bookproof-forces
                 lib (library-integer value) negative nil
                 (list *b1-quotient-zip* *b1-quotient-numeric-eq* *proof-not*) nil)))
       (cons step lib)))
    ((equal value *proof-zero*)
     (b1-bit-types-result-with-library (library-library-type-of lib *proof-zero* nil) lib))
    (t
     (proof-with-checked-results ((hypothesis (b1-bit-types-and-integer-hypothesis lib claim bindings)))
       (b1-bit-types-numeric-type (1- n) (cdr hypothesis) *proof-integerp* value (list (car hypothesis)))))))

 (defun b1-bit-types-and-integer (n lib expression)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-bit-types-and-integer")
     (let* ((name (proof-sym "SELF-LOGAND-INTEGER" "ACL2"))
            (proof (library-library-proof lib)))
       (proof-with-checked-results
           ((lib
             (if (assoc-equal name (proof-proof-facts proof))
                 lib
               (let* ((call (list *b1-bit-types-logand* *library-x* *library-y*))
                      (claim (library-integer call))
                      (half-a (list *b1-quotient-floor* *library-x* *b1-bits-two*))
                      (half-b (list *b1-quotient-floor* *library-y* *b1-bits-two*))
                      (measure (list *library-count* *library-x*))
                      (bindings (list (cons *library-x* half-a) (cons *library-y* half-b)))
                      (template (list *proof-integerp* *proof-result*)))
                 (proof-with-checked-results
                     ((view (b1-bit-types-unfold lib call))
                      (body (b1-bit-types-step-at view 2))
                      (selected (b1-bit-types-by-value (1- n) lib body template
                                                       :and-integer (list claim bindings))))
                   (let* ((lib (cdr selected))
                          (proof (library-library-proof lib)))
                     (proof-with-checked-results
                         ((reversed (proof-proof-symmetric proof view))
                          (result (proof-proof-rewrite-result proof (car selected) reversed
                                                              template *proof-result*))
                          (ordinal (library-library-builtin lib 1 *library-x*))
                          (step (proof-proof-induct proof ordinal result claim measure
                                                     (list (table-items bindings)))))
                       (library-library-lemma lib "LOGAND-INTEGER" claim step nil)))))))
            (args (b1-bit-types-arguments expression))
            (step (proof-proof-fact (library-library-proof lib) name
                                   (seq-zip (list *library-x* *library-y*) args))))
         (cons step lib)))))

 (defun b1-bit-types-numeric-parts (n lib parts evidence)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "b1-bit-types-numeric-parts"))
    ((endp parts) (cons nil lib))
    (t (proof-with-checked-results
           ((first (b1-bit-types-numeric-type (1- n) lib *proof-integerp* (car parts) evidence))
            (rest (b1-bit-types-numeric-parts (1- n) (cdr first) (cdr parts) evidence)))
         (cons (cons (car first) (car rest)) (cdr rest))))))

 (defun b1-bit-types-numeric-mod-bit (n lib value evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-bit-types-numeric-mod-bit")
     (proof-with-checked-results
         ((view (b1-bit-types-bit-modulus-view lib value))
          (integral (b1-bit-types-numeric-type (1- n) lib *proof-integerp* (car view) evidence))
          (equation (b1-bit-types-mod-two-equation (cdr integral) (car integral)))
          (low-bit (b1-bit-types-step-at (car equation) 2))
          (bits (b1-bit-types-by-value (1- n) (cdr equation) low-bit
                                       (list *b1-fixer-laws-bitp* *proof-result*) :bit nil))
          (equality (proof-proof-chain (library-library-proof (cdr bits)) (cdr view) (list (car equation)))))
       (b1-bit-types-result-with-library
        (library-library-transport-argument (cdr bits) (car bits) equality 1) (cdr bits)))))

 (defun b1-bit-types-numeric-mod-natural (n lib value evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-bit-types-numeric-mod-natural")
     (proof-with-checked-results
         ((view (b1-bit-types-normalize lib value nil (list *b1-bit-types-imod*)))
          (mod (b1-bit-types-step-at view 2))
          (parts (proof-list-of-length mod 3)))
       (let ((dividend (cadr parts))
             (divisor (caddr parts)))
         (proof-with-checked-results
             ((fixed (if (proof-is-call divisor *b1-quotient-ifix*)
                         (proof-term-at divisor 1)
                       divisor))
              (types (b1-bit-types-exponent-types n lib fixed))
              (view (b1-bit-types-modulus-view (cdr types) view divisor fixed (caar types)))
              (mod (b1-bit-types-step-at view 2))
              (int-x (b1-bit-types-numeric-type (1- n) (cdr types) *proof-integerp* dividend evidence))
              (lemma (b1-modular-remainder-lemma (cdr int-x))))
           (let* ((lib (cdr lemma))
                  (proof (library-library-proof lib)))
             (proof-with-checked-results
                 ((theorem (proof-proof-fact proof (car lemma)
                                             (list (list *library-x* dividend) (list *library-y* fixed))))
                  (antecedent (b1-bit-types-step-at theorem 1))
                  (premise (b1-logic-bookproof-normalize-proof
                            lib antecedent (list (car int-x) (caar types) (cadar types)) nil nil nil))
                  (equation (proof-proof-modus-ponens proof theorem premise))
                  (conjuncts (b1-logic-bookproof-split-conjuncts lib equation))
                  (bounds (proof-list-of-length conjuncts 3))
                  (natural (library-library-cite lib "NATURAL-FROM-BOUNDS" (list mod)
                                                (list (car bounds) (cadr bounds))))
                  (result (library-library-transport-argument lib natural view 1)))
               (cons result lib))))))))

 (defun b1-bit-types-reverse-is-natural-consequence (n premise lib carry closed added hypothesis advanced test)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-bit-types-reverse-is-natural-consequence")
     (proof-with-checked-results
         ((base (b1-bit-types-reverse-is-natural-closed-case lib carry closed premise))
          (low (proof-term-at added 1))
          (bit (b1-bit-types-numeric-type (1- n) lib *b1-fixer-laws-bitp* low nil)))
       (let* ((lib (cdr bit))
              (proof (library-library-proof lib))
              (bit (car bit))
              (int-carry (car base))
              (yes (cadr base)))
         (proof-with-checked-results
             ((bit-literal (proof-step-first bit))
              (bit-value (proof-term-at bit-literal 1))
              (bfix (b1-logic-bookproof-from-fact
                     lib (proof-sym "BFIX-BITP" "ACL2")
                     (list *library-implies* bit-literal
                           (proof-eq (list *b1-bit-types-bfix* bit-value) bit-value))))
              (bfix (proof-proof-modus-ponens proof bfix bit))
              (rule (b1-logic-equal-to bfix))
              (expanded (b1-logic-bookproof-normalize
                         lib added (list int-carry) (list *b1-bit-types-logcons* *b1-quotient-ifix*)
                         (list rule) nil nil nil))
              (number (b1-arithmetic-known-type lib *library-numberp* carry (list int-carry)))
              (double (b1-bitwise-twice lib carry number))
              (reversed (proof-proof-symmetric proof double))
              (expanded (proof-proof-rewrite-first proof expanded reversed))
              (natural (library-library-cite lib "NATURAL-SUM" (list carry carry) (list premise premise)))
              (bit-natural (b1-bit-types-typed-bit-is-natural lib bit))
              (sum (b1-bit-types-step-at expanded 2))
              (args (b1-bit-types-arguments sum))
              (args (proof-list-of-length args 2))
              (value (library-library-cite lib "NATURAL-SUM" args
                                          (list (if (equal (car args) bit-value) bit-natural natural)
                                                (if (equal (cadr args) bit-value) bit-natural natural))))
              (value (library-library-transport-argument lib value expanded 1))
              (child (proof-proof-modus-ponens proof hypothesis value))
              (no (library-library-transport-argument lib child advanced 1))
              (step (proof-proof-cases proof test yes no)))
           (cons step lib))))))

 (defun b1-bit-types-reverse-is-natural-library (n lib name)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-bit-types-reverse-is-natural-library")
     (let ((proof (library-library-proof lib)))
       (if (assoc-equal name (proof-proof-facts proof))
           lib
         (proof-with-checked-results
             ((definition (b1-bit-types-logrev-definition lib))
              (definition (proof-list-of-length definition 2))
              (formals (proof-list-of-length (car definition) 3)))
           (let* ((index (car formals))
                  (items (cadr formals))
                  (carry (caddr formals))
                  (source (cons *b1-bit-types-logrev1* formals))
                  (formula (list *library-implies* (list *library-natp* carry) (list *library-natp* source)))
                  (test (list *b1-logic-zp* index)))
             (proof-with-checked-results
                 ((branches (b1-bit-types-reverse-is-natural-branches lib source test))
                  (advanced-call (b1-bit-types-step-at (cadr branches) 2))
                  (parts (proof-list-of-length advanced-call 4)))
               (let* ((previous (cadr parts))
                      (high (caddr parts))
                      (added (cadddr parts))
                      (bindings (table-put (table-put (list (cons index previous)) items high) carry added)))
                 (proof-with-checked-results
                     ((premises (b1-bit-types-reverse-is-natural-induction-premises
                                 lib formula index previous bindings))
                      (consequence (b1-bit-types-reverse-is-natural-consequence
                                    (1- n) (caddr premises) lib carry (car branches) added
                                    (car premises) (cadr branches) test)))
                   (let* ((lib (cdr consequence))
                          (proof (library-library-proof lib)))
                     (proof-with-checked-results
                         ((induction-case (b1-logic-bookproof-prove-implication-with-premise
                                           lib formula (caddr premises) (car consequence)))
                          (result (proof-proof-induct proof (cadr premises) induction-case formula
                                                     (list *library-nfix* index) (list (table-items bindings)))))
                       (library-library-lemma lib "LOGREV1-NATURAL" formula result nil))))))))))))

 (defun b1-bit-types-reverse-is-natural (n lib call initial)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-bit-types-reverse-is-natural")
     (let ((name (proof-sym "SELF-LOGREV1-NATURAL" "ACL2")))
       (proof-with-checked-results
           ((lib (b1-bit-types-reverse-is-natural-library (1- n) lib name))
            (definition (b1-bit-types-logrev-definition lib))
            (formals (proof-term-at definition 0))
            (actuals (b1-bit-types-arguments call)))
         (let ((proof (library-library-proof lib)))
           (proof-with-checked-results
               ((law (proof-proof-fact proof name (seq-zip formals actuals)))
                (result (proof-proof-modus-ponens proof law initial)))
             (cons result lib)))))))

 (defun b1-bit-types-numeric-fallback (n lib predicate value evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-bit-types-numeric-fallback")
     (proof-with-checked-results ((head (proof-term-at value 0)))
       (cond
        ((proof-is-call value *b1-quotient-ifix*)
         (b1-bit-types-result-with-library (b1-bit-types-integer-fix-visit (1- n) lib value) lib))
        ((proof-is-call value *b1-quotient-floor*)
         (proof-with-checked-results
             ((parts (b1-bit-types-numeric-parts (1- n) lib (cdr value) evidence)))
           (b1-bit-types-floor-evidence (cdr parts) value (car parts))))
        ((proof-is-call value *b1-bit-types-logand*)
         (b1-bit-types-and-integer (1- n) lib value))
        ((member-equal head (list *b1-modular-mod* *b1-bit-types-logior* *b1-bit-types-lognot*))
         (proof-with-checked-results
             ((view (b1-bit-types-normalize lib value nil (list head)))
              (body (b1-bit-types-step-at view 2))
              (result (b1-bit-types-numeric-type (1- n) lib predicate body evidence)))
           (b1-bit-types-result-with-library
            (library-library-transport-argument (cdr result) (car result) view 1) (cdr result))))
        ((member-equal head (list *proof-plus* *proof-times* *proof-minus*))
         (proof-with-checked-results
             ((parts (b1-bit-types-numeric-parts (1- n) lib (cdr value) evidence)))
           (b1-bit-types-result-with-library
            (library-library-type-of (cdr parts) value (car parts)) (cdr parts))))
        (t (b1-bit-types-result-with-library (library-library-type-of lib value evidence) lib))))))

 (defun b1-bit-types-numeric-type (n lib predicate value evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-bit-types-numeric-type")
     (let ((claim (list predicate value))
           (template (list predicate *proof-result*)))
       (proof-with-checked-results ((present (b1-bit-types-evidence-type claim evidence)))
         (cond
          (present (cons present lib))
          ((proof-is-call value *proof-if*)
           (b1-bit-types-by-value (1- n) lib value template :numeric-type evidence))
          (t
           (proof-with-checked-results ((previous (b1-bit-types-prior-proof lib predicate value claim)))
             (cond
              (previous (cons previous lib))
              ((proof-is-call value *b1-bit-types-bfix*)
               (proof-with-checked-results
                   ((view (b1-bit-types-unfold lib value))
                    (body (b1-bit-types-step-at view 2))
                    (bits (b1-bit-types-by-value (1- n) lib body
                                                 (list *b1-fixer-laws-bitp* *proof-result*) :bit nil))
                    (bit (library-library-transport-argument lib (car bits) view 1)))
                 (b1-bit-types-result-with-library
                  (b1-bit-types-bit-predicate lib predicate value bit) lib)))
              ((and (equal predicate *b1-fixer-laws-bitp*) (proof-is-call value *b1-bit-types-imod*))
               (b1-bit-types-numeric-mod-bit (1- n) lib value evidence))
              ((proof-is-call value *b1-bit-types-builtin-nfix*)
               (proof-with-checked-results ((natural (b1-integer-nfix-natural lib value)))
                 (b1-bit-types-result-with-library
                  (if (equal predicate *library-natp*)
                      natural
                    (library-library-cite lib "NATURAL-INTEGER" (list value) (list natural)))
                  lib)))
              ((or (proof-is-call value *b1-bit-types-expt*) (proof-is-call value *b1-bit-types-expt2*))
               (proof-with-checked-results ((types (b1-bit-types-exponent-types n lib value)))
                 (b1-bit-types-exponent-predicate types predicate value)))
              ((equal predicate *library-natp*)
               (cond
                ((proof-is-call value *b1-bit-types-imod*)
                 (b1-bit-types-numeric-mod-natural (1- n) lib value evidence))
                ((proof-is-call value *proof-plus*)
                 (proof-with-checked-results ((left (proof-term-at value 1)))
                   (if (equal left *proof-neg-one*)
                       (b1-bit-types-shifted-exponent-natural n lib value)
                     (b1-bit-types-result-with-library (library-library-natural lib value) lib))))
                ((proof-is-call value *b1-bit-types-logrev1*)
                 (proof-with-checked-results
                     ((carry (proof-term-at value 3))
                      (initial (b1-bit-types-numeric-type (1- n) lib *library-natp* carry evidence)))
                   (b1-bit-types-reverse-is-natural (1- n) (cdr initial) value (car initial))))
                (t (b1-bit-types-result-with-library (library-library-natural lib value) lib))))
              (t (b1-bit-types-numeric-fallback (1- n) lib predicate value evidence)))))))))))

(defun b1-bit-types-integer-fix (lib value)
  (b1-bit-types-integer-fix-visit 1000000 lib value))

(defun b1-bit-types-bit-operation-type (lib formula)
  (proof-with-checked-results
      ((flattened (b1-logic-bookproof-normalize lib formula nil nil nil nil nil nil))
       (literal (b1-bit-types-step-at flattened 2))
       (parts (proof-list-of-length literal 2)))
    (let ((predicate (car parts))
          (call (cadr parts)))
      (proof-with-checked-results
          ((head (proof-term-at call 0))
           (opened (b1-logic-bookproof-normalize lib call nil (list head) nil nil nil t))
           (body (b1-bit-types-step-at opened 2))
           (raw (b1-bit-types-numeric-type 1000000 lib predicate body nil))
           (step (library-library-transport-argument (cdr raw) (car raw) opened 1))
           (result (proof-proof-transport (library-library-proof (cdr raw)) step flattened)))
        (cons result (cdr raw))))))
