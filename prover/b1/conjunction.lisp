(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun b1-conjunction-halved (term)
  (list *b1-quotient-floor* term *b1-bits-two*))

(defun b1-conjunction-conjunction (a b)
  (list *b1-bitwise-logand* a b))

(defun b1-conjunction-bit-conjunction (a b yes no)
  (proof-ite (list *b1-bits-evenp* a) yes
             (proof-ite (list *b1-bits-evenp* b) yes no)))

(defund b1-conjunction-case-assume (lib test holds)
  (proof-proof-assume (library-library-proof lib) test holds))

(defun b1-conjunction-reduction-at (lib term equality)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reflexive (proof-proof-reflexive proof term))
         (literal (b1-logic-step-first equality))
         (slot (proof-term-at literal 1)))
      (proof-proof-rewrite-result proof reflexive equality (proof-eq *proof-false* term) slot))))

(defund b1-conjunction-signed-constant-add (lib label suffix step)
  (proof-with-checked-results ((claim (proof-step-first step)))
    (library-library-lemma lib (concatenate 'string label suffix) claim step nil)))

(defun b1-conjunction-signed-constant-install (lib labels suffix steps)
  (declare (xargs :measure (len labels)))
  (if (or (endp labels) (endp steps))
      lib
    (proof-with-checked-results
        ((lib (b1-conjunction-signed-constant-add lib (car labels) suffix (car steps))))
      (b1-conjunction-signed-constant-install lib (cdr labels) suffix (cdr steps)))))

(defun b1-conjunction-signed-constant (lib value)
  (let* ((at-zero (equal value *proof-zero*))
         (suffix (if at-zero "ZERO" "MINUS-ONE"))
         (floor (proof-sym (concatenate 'string "SELF-HALF-" suffix) "ACL2"))
         (even (proof-sym (concatenate 'string "SELF-EVENP-" suffix) "ACL2"))
         (facts (proof-proof-facts (library-library-proof lib))))
    (proof-with-checked-results
        ((lib (if (assoc-equal floor facts)
                  lib
                (proof-with-checked-results
                    ((pair (b1-bits-constant-bit-pair
                            lib value (if at-zero *proof-zero* *proof-one*))))
                  (b1-conjunction-signed-constant-install
                   (cdr pair) '("HALF-" "EVENP-") suffix (car pair)))))
         (floor-step (proof-proof-fact (library-library-proof lib) floor nil))
         (even-step (proof-proof-fact (library-library-proof lib) even nil)))
      (cons (list floor-step even-step) lib))))

(defun b1-conjunction-zip-from-integer (lib integral zero)
  (proof-with-checked-results
      ((literal (b1-logic-step-first integral))
       (term (proof-term-at literal 1))
       (zero-first (b1-logic-step-first zero))
       (head (proof-term-at zero-first 0)))
    (let ((zip (list *b1-quotient-zip* term))
          (unfold (list *b1-quotient-zip* *b1-quotient-numeric-eq*)))
      (if (equal head *proof-not*)
          (b1-logic-bookproof-normalize-proof
           lib (proof-neg zip) (list integral zero) (append unfold (list *proof-not*)) nil nil)
        (b1-logic-bookproof-normalize-proof lib zip (list integral zero) unfold nil nil)))))

(defun b1-conjunction-logand-unit-at-test (lib term unfold test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equality (proof-proof-assume proof test t))
         (chosen (b1-logic-bookproof-normalize
                  lib term nil unfold (list (b1-logic-equal-to equality)) nil nil nil))
         (reversed (proof-proof-symmetric proof equality)))
      (proof-proof-chain proof chosen (list reversed)))))

(defun b1-conjunction-logand-unit (lib unit other integral first)
  (let ((proof (library-library-proof lib))
        (term (if first
                  (b1-conjunction-conjunction unit other)
                (b1-conjunction-conjunction other unit))))
    (if (equal unit *proof-zero*)
        (proof-with-checked-results
            ((zipped (b1-logic-bookproof-normalize
                      lib (list *b1-quotient-zip* *proof-zero*) nil
                      (list *b1-quotient-zip* *b1-quotient-numeric-eq*) nil nil nil nil)))
          (b1-logic-bookproof-case-proof
           lib (proof-eq term *proof-zero*) nil (list *b1-bitwise-logand*)
           (list (b1-logic-equal-to zipped)) 16))
      (let ((zero (proof-eq other *proof-zero*))
            (minus-one (proof-eq other *proof-neg-one*))
            (unfold (list *b1-bitwise-logand* *b1-quotient-zip*
                          *b1-quotient-numeric-eq* *b1-logic-eql*)))
        (proof-with-checked-results
            ((at-zero (b1-conjunction-logand-unit-at-test lib term unfold zero))
             (at-minus (b1-conjunction-logand-unit-at-test lib term unfold minus-one))
             (no-zero (proof-proof-assume proof zero nil))
             (no-zip (b1-conjunction-zip-from-integer lib integral no-zero))
             (no-minus (proof-proof-assume proof minus-one nil))
             (e-minus (proof-proof-unfold proof (list *b1-logic-eql* other *proof-neg-one*)))
             (e-minus (proof-proof-symmetric proof e-minus))
             (no-minus (proof-proof-rewrite proof no-minus e-minus '(1 1)))
             (no (b1-logic-bookproof-normalize
                  lib term (list no-zip no-minus) unfold nil nil nil nil))
             (no-first (proof-step-first no))
             (no-value (proof-term-at no-first 2)))
          (if (not (equal no-value other))
              '(:failure "failure" "")
            (proof-with-checked-results
                ((nonzero (proof-proof-cases proof minus-one at-minus no)))
              (proof-proof-cases proof zero at-zero nonzero))))))))

(defund b1-conjunction-joined-conjunction-at-unit (test lib claim int-x int-y)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equality (proof-proof-assume proof test t))
         (args (proof-list-of-length (cdr test) 2))
         (variable (car args))
         (value (cadr args))
         (first-arg (equal variable *library-x*))
         (other-int (if first-arg int-y int-x))
         (other-first (proof-step-first other-int))
         (other (proof-term-at other-first 1))
         (reduction (b1-conjunction-reduction-at lib claim equality))
         (specialized-first (proof-step-first reduction))
         (specialized (proof-term-at specialized-first 2))
         (lhs (b1-conjunction-logand-unit lib value other other-int first-arg))
         (consts (b1-conjunction-signed-constant lib value))
         (rhs (proof-term-at specialized 2))
         (interval (b1-bits-half-interval (cdr consts) other-int)))
      (let* ((lib (cdr interval))
             (proof (library-library-proof lib))
             (floor-const (car (car consts)))
             (even-const (cadr (car consts)))
             (high-int (caar (car interval))))
        (proof-with-checked-results
            ((high (b1-conjunction-logand-unit
                    lib value (b1-conjunction-halved other) high-int first-arg))
             (opened (b1-conjunction-reduction-at lib rhs floor-const))
             (opened (proof-proof-rewrite proof opened high '(1 2 1 2)))
             (opened-first (proof-step-first opened))
             (opened-value (proof-term-at opened-first 2))
             (even-first (proof-step-first even-const))
             (even-slot (proof-term-at even-first 1))
             (opened (proof-proof-rewrite-result
                      proof opened even-const (proof-eq *proof-false* opened-value) even-slot))
             (layout (if (equal value *proof-neg-one*)
                         (b1-bits-decomposition lib other-int)
                       (proof-with-checked-results
                           ((zero (proof-proof-reflexive proof *proof-zero*)))
                         (cons zero lib)))))
          (let* ((lib (cdr layout))
                 (proof (library-library-proof lib))
                 (layout (car layout)))
            (proof-with-checked-results
                ((opened-first (proof-step-first opened))
                 (opened-value (proof-term-at opened-first 2))
                 (layout-first (proof-step-first layout))
                 (layout-value (proof-term-at layout-first 2))
                 (finish (b1-logic-bookproof-case-proof
                          lib (proof-eq opened-value layout-value) nil nil nil 16))
                 (finished (proof-proof-chain proof opened (list finish)))
                 (reversed (proof-proof-symmetric proof finished))
                 (step (proof-proof-chain proof lhs (list layout reversed)))
                 (result (proof-proof-transport proof step reduction)))
              (cons result lib))))))))

(defun b1-conjunction-joined-conjunction-no-eql (lib variable negative)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof (list *b1-logic-eql* variable *proof-neg-one*)))
         (reversed (proof-proof-symmetric proof opened)))
      (proof-proof-rewrite proof negative reversed '(1 1)))))

(defun b1-conjunction-joined-conjunction-cases
    (tests evidence lib claim term int-x int-y)
  (declare (xargs :measure (len tests)))
  (if (endp tests)
      (proof-with-checked-results
          ((zip-x (b1-conjunction-zip-from-integer lib int-x (car evidence)))
           (zip-y (b1-conjunction-zip-from-integer lib int-y (cadr evidence)))
           (eql-x (b1-conjunction-joined-conjunction-no-eql lib *library-x* (caddr evidence)))
           (eql-y (b1-conjunction-joined-conjunction-no-eql lib *library-y* (cadddr evidence)))
           (step (b1-logic-bookproof-normalize
                  lib term (list zip-x zip-y eql-x eql-y) (list *b1-bitwise-logand*)
                  nil nil nil nil)))
        (cons step lib))
    (let ((test (car tests)))
      (proof-with-checked-results
          ((yes (b1-conjunction-joined-conjunction-at-unit test lib claim int-x int-y))
           (lib (cdr yes))
           (negative (b1-conjunction-case-assume lib test nil))
           (no (b1-conjunction-joined-conjunction-cases
                (cdr tests) (append evidence (list negative)) lib claim term int-x int-y))
           (lib (cdr no))
           (step (proof-proof-cases (library-library-proof lib) test (car yes) (car no))))
        (cons step lib)))))

(defun b1-conjunction-joined-conjunction-install (lib)
  (let* ((x *library-x*)
         (y *library-y*)
         (term (b1-conjunction-conjunction x y))
         (high (b1-conjunction-conjunction (b1-conjunction-halved x) (b1-conjunction-halved y)))
         (claim (proof-eq term (b1-bits-join-bits
                                high (b1-conjunction-bit-conjunction x y *proof-zero* *proof-one*))))
         (tests (list (proof-eq x *proof-zero*) (proof-eq y *proof-zero*)
                      (proof-eq x *proof-neg-one*) (proof-eq y *proof-neg-one*))))
    (proof-with-checked-results
        ((ints (library-library-ints lib (list x y)))
         (int-x (car ints))
         (int-y (cadr ints))
         (cases (b1-conjunction-joined-conjunction-cases tests nil lib claim term int-x int-y))
         (x-type (proof-step-first int-x))
         (y-type (proof-step-first int-y)))
      (library-library-lemma (cdr cases) "LOGAND-BIT-DECOMPOSITION" claim (car cases)
                             (list (proof-neg x-type) (proof-neg y-type))))))

(defun b1-conjunction-joined-conjunction (lib first second)
  (let ((name (proof-sym "SELF-LOGAND-BIT-DECOMPOSITION" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (b1-conjunction-joined-conjunction-install lib)))
         (first-literal (b1-logic-step-first first))
         (x (proof-term-at first-literal 1))
         (second-literal (b1-logic-step-first second))
         (y (proof-term-at second-literal 1))
         (step (proof-proof-use (library-library-proof lib) name
                                (list (list *library-x* x) (list *library-y* y))
                                (list first second))))
      (cons step lib))))

(defun b1-conjunction-halving-pairs (variables)
  (declare (xargs :measure (len variables)))
  (if (endp variables)
      nil
    (cons (list (car variables) (b1-conjunction-halved (car variables)))
          (b1-conjunction-halving-pairs (cdr variables)))))

(defun b1-conjunction-pair-bindings (pairs bindings)
  (declare (xargs :measure (len pairs)))
  (if (endp pairs)
      bindings
    (b1-conjunction-pair-bindings
     (cdr pairs) (table-put bindings (caar pairs) (cadar pairs)))))

(defun b1-conjunction-induction-half (lib formula variables descent)
  (let ((proof (library-library-proof lib))
        (bindings (b1-conjunction-pair-bindings (b1-conjunction-halving-pairs variables) nil)))
    (proof-with-checked-results
        ((smaller (proof-subst formula bindings))
         (descends (b1-logic-step-first descent))
         (assumed (proof-proof-assume proof (proof-ite descends smaller *proof-true*) t)))
      (proof-proof-prove-if proof assumed descent))))

(defun b1-conjunction-projection-lemma-high-for-unit (test lib high b int-b)
  (proof-with-checked-results
      ((value (proof-term-at test 2))
       (consts (b1-conjunction-signed-constant lib value)))
    (let* ((lib (cdr consts))
           (proof (library-library-proof lib))
           (floor (caar consts)))
      (proof-with-checked-results
          ((equality (proof-proof-assume proof test t))
           (reduction (b1-conjunction-reduction-at lib high equality))
           (reduction (proof-proof-rewrite proof reduction floor '(1 2 1)))
           (unit (b1-conjunction-logand-unit lib value b int-b t))
           (reduced (proof-proof-chain proof reduction (list unit)))
           (unit-first (proof-step-first unit))
           (unit-value (proof-term-at unit-first 2))
           (result (library-library-type-of lib unit-value (list int-b)))
           (step (library-library-transport-argument lib result reduced 1)))
        (cons step lib)))))

(defun b1-conjunction-projection-lemma-result (evidence bit lib joined integral claim even)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((joined-first (proof-step-first joined))
         (joined-value (proof-term-at joined-first 2))
         (parts (b1-logic-bookproof-normalize lib joined-value evidence nil nil nil nil nil))
         (exact (proof-proof-chain proof joined (list parts)))
         (exact-first (proof-step-first exact))
         (exact-value (proof-term-at exact-first 2))
         (int-result (library-library-type-of lib exact-value (list integral)))
         (bits (b1-bits-bit-pair lib integral bit)))
      (let* ((lib (cdr bits))
             (proof (library-library-proof lib)))
        (proof-with-checked-results
            ((int-result (library-library-transport-argument lib int-result exact 1))
             (reversed (proof-proof-symmetric proof exact))
             (floor (proof-proof-rewrite proof (car (car bits)) reversed '(1 1 1)))
             (reversed (proof-proof-symmetric proof exact))
             (is-even (proof-proof-rewrite proof (cadr (car bits)) reversed '(1 1 1)))
             (expected (b1-logic-bookproof-normalize lib (caddr even) evidence nil nil nil nil nil))
             (reversed (proof-proof-symmetric proof expected))
             (is-even (proof-proof-chain proof is-even (list reversed)))
             (step (b1-logic-bookproof-normalize-proof
                    lib claim (list int-result floor is-even) nil nil nil)))
          (cons step lib))))))

(defun b1-conjunction-projection-lemma-with-high (integral lib joined claim even even-x even-y)
  (proof-with-checked-results
      ((x-even (proof-proof-assume (library-library-proof lib) even-x t))
       (yes (b1-conjunction-projection-lemma-result
             (list x-even) *proof-zero* lib joined integral claim even))
       (lib (cdr yes))
       (x-odd (proof-proof-assume (library-library-proof lib) even-x nil))
       (y-even (proof-proof-assume (library-library-proof lib) even-y t))
       (no-left (b1-conjunction-projection-lemma-result
                 (list x-odd y-even) *proof-zero* lib joined integral claim even))
       (lib (cdr no-left))
       (y-odd (proof-proof-assume (library-library-proof lib) even-y nil))
       (no-right (b1-conjunction-projection-lemma-result
                  (list x-odd y-odd) *proof-one* lib joined integral claim even))
       (lib (cdr no-right))
       (no (proof-proof-cases (library-library-proof lib)
                              even-y (car no-left) (car no-right)))
       (step (proof-proof-cases (library-library-proof lib) even-x (car yes) no)))
    (cons step lib)))

(defun b1-conjunction-projection-lemma-consequence (premise lib x y b high even claim formula)
  (proof-with-checked-results
      ((parts (b1-logic-bookproof-split-conjuncts lib premise))
       (ints (proof-list-of-length parts 2))
       (int-x (car ints))
       (int-y (cadr ints))
       (interval-a (b1-bits-half-interval lib int-x))
       (int-a (caar (car interval-a)))
       (interval-b (b1-bits-half-interval (cdr interval-a) int-y))
       (int-b (caar (car interval-b)))
       (joined-result (b1-conjunction-joined-conjunction (cdr interval-b) int-x int-y)))
    (let* ((lib (cdr joined-result))
           (proof (library-library-proof lib))
           (joined (car joined-result))
           (zero (proof-eq x *proof-zero*))
           (minus-one (proof-eq x *proof-neg-one*))
           (even-x (list *b1-bits-evenp* x))
           (even-y (list *b1-bits-evenp* y)))
      (proof-with-checked-results
          ((no-zero (proof-proof-assume proof zero nil))
           (no-zip (b1-conjunction-zip-from-integer lib int-x no-zero))
           (no-minus (proof-proof-assume proof minus-one nil))
           (descent-name (b1-bitwise-floor-half-descent lib))
           (lib (cdr descent-name))
           (proof (library-library-proof lib))
           (descent (proof-proof-use proof (car descent-name) (list (list *library-x* x))
                                     (list no-zip no-minus)))
           (hyp (b1-conjunction-induction-half lib formula (list x y) descent))
           (hyp-first (proof-step-first hyp))
           (hyp-guard (proof-term-at hyp-first 1))
           (child-guard (b1-logic-bookproof-normalize-proof
                         lib hyp-guard (list int-a int-b) nil nil nil))
           (child-projections (proof-proof-modus-ponens proof hyp child-guard))
           (child-parts (b1-logic-bookproof-split-conjuncts lib child-projections))
           (high-int (proof-term-at child-parts 0))
           (zero-high (b1-conjunction-projection-lemma-high-for-unit zero lib high b int-b))
           (at-zero (b1-conjunction-projection-lemma-with-high
                     (car zero-high) (cdr zero-high) joined claim even even-x even-y))
           (unit-high (b1-conjunction-projection-lemma-high-for-unit
                       minus-one (cdr at-zero) high b int-b))
           (at-unit (b1-conjunction-projection-lemma-with-high
                     (car unit-high) (cdr unit-high) joined claim even even-x even-y))
           (other (b1-conjunction-projection-lemma-with-high
                   high-int (cdr at-unit) joined claim even even-x even-y))
           (lib (cdr other))
           (proof (library-library-proof lib))
           (nonzero (proof-proof-cases proof minus-one (car at-unit) (car other)))
           (step (proof-proof-cases proof zero (car at-zero) nonzero)))
        (cons step lib)))))

(defun b1-conjunction-projection-lemma-install (lib)
  (let* ((x *library-x*)
         (y *library-y*)
         (a (b1-conjunction-halved x))
         (b (b1-conjunction-halved y))
         (term (b1-conjunction-conjunction x y))
         (high (b1-conjunction-conjunction a b))
         (guard (proof-ite (library-integer x) (library-integer y) *proof-false*))
         (even (proof-eq (list *b1-bits-evenp* term)
                         (b1-conjunction-bit-conjunction x y *proof-true* *proof-false*)))
         (claim (proof-ite (library-integer term)
                           (proof-ite (proof-eq (b1-conjunction-halved term) high)
                                      even *proof-false*)
                           *proof-false*))
         (formula (list *library-implies* guard claim)))
    (proof-with-checked-results
        ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
         (consequence (b1-conjunction-projection-lemma-consequence
                       premise lib x y b high even claim formula))
         (lib (cdr consequence))
         (case-step (b1-logic-bookproof-prove-implication-with-premise
                     lib formula premise (car consequence)))
         (ordinal (library-library-builtin lib 1 x))
         (step (proof-proof-induct (library-library-proof lib) ordinal case-step
                                   formula (list *library-count* x)
                                   (list (list (list x a) (list y b))))))
      (library-library-lemma lib "LOGAND-PROJECTIONS" formula step nil))))

(defun b1-conjunction-projection-lemma (lib)
  (let ((name (proof-sym "SELF-LOGAND-PROJECTIONS" "ACL2")))
    (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
        (cons name lib)
      (proof-with-checked-results ((lib (b1-conjunction-projection-lemma-install lib)))
        (cons name lib)))))

(defun b1-conjunction-use-projection (lib first second)
  (proof-with-checked-results
      ((projection (b1-conjunction-projection-lemma lib))
       (lib (cdr projection))
       (proof (library-library-proof lib))
       (first-literal (b1-logic-step-first first))
       (x (proof-term-at first-literal 1))
       (second-literal (b1-logic-step-first second))
       (y (proof-term-at second-literal 1))
       (fact (proof-proof-fact proof (car projection)
                               (list (list *library-x* x) (list *library-y* y))))
       (fact-first (proof-step-first fact))
       (guard-term (proof-term-at fact-first 1))
       (guard (b1-logic-bookproof-normalize-proof lib guard-term (list first second) nil nil nil))
       (conjunction (proof-proof-modus-ponens proof fact guard))
       (parts (b1-logic-bookproof-split-conjuncts lib conjunction)))
    (cons parts lib)))

(defun b1-conjunction-zip-noninteger (lib noninteger)
  (proof-with-checked-results
      ((literal (b1-logic-step-first noninteger))
       (test (proof-term-at literal 1))
       (term (proof-term-at test 1)))
    (b1-logic-bookproof-normalize-proof
     lib (list *b1-quotient-zip* term) (list noninteger)
     (list *b1-quotient-zip* *b1-quotient-numeric-eq*) nil nil)))

(defun b1-conjunction-zero-on-zip (lib term zipped)
  (b1-logic-bookproof-case-proof lib (proof-eq term *proof-zero*) (list zipped)
                                (list *b1-bitwise-logand*) nil 16))

(defun b1-conjunction-term-args (term size)
  (if (integerp term)
      '(:failure "failure" "")
    (proof-list-of-length (cdr term) size)))

(defun b1-conjunction-full-conjunction-exceptional (variable noninteger lib term formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((zip (b1-conjunction-zip-noninteger lib noninteger))
         (result (b1-conjunction-zero-on-zip lib term zip))
         (one (proof-eq variable *proof-neg-one*))
         (integer-constant (library-library-type-of lib *proof-neg-one* nil))
         (assumed (proof-proof-assume proof one t))
         (integer-var (library-library-transport-argument lib integer-constant assumed 1))
         (conflict (proof-proof-cut proof integer-var noninteger))
         (excluded (proof-proof-front proof conflict (proof-neg one)))
         (false (b1-logic-bookproof-false-value lib excluded))
         (step (b1-logic-bookproof-case-proof
                lib formula nil nil (list (b1-logic-equal-to result) (b1-logic-equal-to false)) 16)))
      (cons step lib))))

(defund b1-conjunction-full-conjunction-base (test lib formula x y int-x int-y)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((args (b1-conjunction-term-args test 2))
         (variable (car args))
         (value (cadr args))
         (first-arg (equal variable x))
         (other (if first-arg y x))
         (integral (if first-arg int-y int-x))
         (assumed (proof-proof-assume proof test t))
         (reduction (b1-conjunction-reduction-at lib formula assumed))
         (result (b1-conjunction-logand-unit lib value other integral first-arg))
         (literal (proof-step-first reduction))
         (claim (proof-term-at literal 2))
         (step (b1-logic-bookproof-case-proof
                lib claim nil nil (list (b1-logic-equal-to result)) 16)))
      (proof-proof-transport proof step reduction))))

(defun b1-conjunction-full-conjunction-step (negatives lib formula term x y int-x int-y)
  (proof-with-checked-results
      ((no-zip (b1-conjunction-zip-from-integer lib int-x (car negatives)))
       (descent-name (b1-bitwise-floor-half-descent lib))
       (lib (cdr descent-name))
       (proof (library-library-proof lib))
       (descent (proof-proof-use proof (car descent-name) (list (list *library-x* x))
                                 (list no-zip (caddr negatives))))
       (smaller (b1-conjunction-induction-half lib formula (list x y) descent))
       (projection (b1-conjunction-use-projection lib int-x int-y))
       (lib (cdr projection))
       (proof (library-library-proof lib))
       (projections (proof-list-of-length (car projection) 3))
       (floor (cadr projections))
       (even (caddr projections))
       (minus-one (proof-eq term *proof-neg-one*))
       (value (proof-proof-assume proof minus-one t))
       (consts (b1-conjunction-signed-constant lib *proof-neg-one*))
       (lib (cdr consts))
       (proof (library-library-proof lib))
       (high (proof-proof-rewrite proof floor value '(1 1 1)))
       (high (proof-proof-rewrite proof high (car (car consts)) '(1 1)))
       (high (proof-proof-symmetric proof high))
       (halves (proof-proof-rewrite proof high smaller '(1)))
       (conjuncts (proof-proof-conjunct proof halves))
       (first (car conjuncts))
       (low (proof-proof-rewrite proof even value '(1 1 1)))
       (low (proof-proof-rewrite proof low (cadr (car consts)) '(1 1)))
       (low (proof-proof-symmetric proof low))
       (even-x (list *b1-bits-evenp* x))
       (low-first (proof-step-first low))
       (low-test (proof-term-at low-first 1))
       (assumed-even (proof-proof-assume proof even-x t))
       (selected (proof-proof-select proof low-test assumed-even))
       (contradiction (proof-proof-rewrite proof low selected '(1 1)))
       (simplified (proof-proof-simplify-first proof contradiction nil nil))
       (tidied (proof-proof-tidy proof simplified))
       (odd (proof-proof-front proof tidied (proof-neg even-x)))
       (pieces (b1-bits-decomposition lib int-x))
       (lib (cdr pieces))
       (proof (library-library-proof lib))
       (pieces (proof-proof-rewrite proof (car pieces) first '(1 2 1 2)))
       (pieces-first (proof-step-first pieces))
       (pieces-value (proof-term-at pieces-first 2))
       (low-piece (proof-term-at pieces-value 2))
       (selected (proof-proof-select proof low-piece odd))
       (pieces (proof-proof-rewrite proof pieces selected '(1 2 2)))
       (pieces-first (proof-step-first pieces))
       (pieces-value (proof-term-at pieces-first 2))
       (normalized (b1-logic-bookproof-normalize lib pieces-value nil nil nil nil nil nil))
       (pieces (proof-proof-chain proof pieces (list normalized)))
       (conflict (proof-proof-cut proof pieces (caddr negatives)))
       (not-ones (proof-proof-front proof conflict (proof-neg minus-one)))
       (one-false (b1-logic-bookproof-false-value lib not-ones))
       (negative-false (b1-logic-bookproof-false-value lib (caddr negatives)))
       (step (b1-logic-bookproof-normalize-proof
              lib formula nil nil
              (list (b1-logic-equal-to one-false) (b1-logic-equal-to negative-false)) nil)))
    (cons step lib)))

(defun b1-conjunction-full-conjunction-cases (tests evidence lib formula term x y int-x int-y)
  (declare (xargs :measure (len tests)))
  (if (endp tests)
      (b1-conjunction-full-conjunction-step evidence lib formula term x y int-x int-y)
    (let ((test (car tests)))
      (proof-with-checked-results
          ((yes (b1-conjunction-full-conjunction-base test lib formula x y int-x int-y))
           (negative (b1-conjunction-case-assume lib test nil))
           (no (b1-conjunction-full-conjunction-cases
                (cdr tests) (append evidence (list negative)) lib formula term x y int-x int-y))
           (lib (cdr no))
           (step (proof-proof-cases (library-library-proof lib) test yes (car no))))
        (cons step lib)))))

(defun b1-conjunction-full-conjunction-ordinary (int-x int-y lib formula term x y)
  (let ((tests (list (proof-eq x *proof-zero*) (proof-eq y *proof-zero*)
                     (proof-eq x *proof-neg-one*) (proof-eq y *proof-neg-one*))))
    (b1-conjunction-full-conjunction-cases tests nil lib formula term x y int-x int-y)))

(defund b1-conjunction-associated-conjunction-reduction (term lib variable zipped)
  (if (proof-is-call term *b1-bitwise-logand*)
      (cond
       ((member-equal variable (cdr term))
        (b1-conjunction-zero-on-zip lib term zipped))
       ((member-equal *proof-zero* (cdr term))
        (let ((first (equal (cadr term) *proof-zero*)))
          (proof-with-checked-results ((other (proof-term-at term (if first 2 1))))
            (b1-conjunction-logand-unit lib *proof-zero* other nil first)))))
    nil))

(defund b1-conjunction-associated-conjunction-unit (term lib value integers)
  (if (and (proof-is-call term *b1-bitwise-logand*) (member-equal value (cdr term)))
      (let ((first (equal (cadr term) value)))
        (proof-with-checked-results ((other (proof-term-at term (if first 2 1))))
          (let ((integral (table-get integers other nil)))
            (if (or integral (equal value *proof-zero*))
                (b1-conjunction-logand-unit lib value other integral first)
              nil))))
    nil))

(defund b1-conjunction-associated-conjunction-normalize-attempt (lib goal rule replies)
  (b1-logic-bookproof-normalize-proof-with-library
   lib goal nil nil (list (list :callback rule)) nil replies))

(defun b1-conjunction-associated-conjunction-normalize (n lib goal rule replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "b1-conjunction-associated-conjunction-normalize")
    (proof-with-checked-results
        ((result (b1-conjunction-associated-conjunction-normalize-attempt lib goal rule replies)))
      (if (b1-logic-call-p result)
          (let ((current-lib (b1-logic-call-library result))
                (term (b1-logic-call-term result))
                (rule (b1-logic-call-id result)))
            (proof-with-checked-results
                ((step (if (eq (car rule) :unit)
                           (b1-conjunction-associated-conjunction-unit
                            term current-lib (cadr rule) (caddr rule))
                         (b1-conjunction-associated-conjunction-reduction
                          term current-lib (cadr rule) (caddr rule)))))
              (b1-conjunction-associated-conjunction-normalize
               (1- n) lib goal rule (append replies (list (cons step current-lib))))))
        result))))

(defun b1-conjunction-associated-conjunction-exceptional (variable noninteger lib formula)
  (proof-with-checked-results ((zipped (b1-conjunction-zip-noninteger lib noninteger)))
    (b1-conjunction-associated-conjunction-normalize
     1000000 lib formula (list :reduction variable zipped) nil)))

(defun b1-conjunction-associated-conjunction-integers (proofs integers)
  (declare (xargs :measure (len proofs)))
  (if (endp proofs)
      integers
    (proof-with-checked-results
        ((literal (proof-step-first (car proofs)))
         (term (proof-term-at literal 1)))
      (b1-conjunction-associated-conjunction-integers
       (cdr proofs) (table-put integers term (car proofs))))))

(defun b1-conjunction-associated-conjunction-base (test lib formula int-y int-z projected-yz)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof test t))
         (reduction (b1-conjunction-reduction-at lib formula assumed))
         (value (proof-term-at test 2))
         (yz-integral (proof-term-at projected-yz 0))
         (integers (b1-conjunction-associated-conjunction-integers
                    (list int-y int-z yz-integral) nil))
         (literal (proof-step-first reduction))
         (claim (proof-term-at literal 2))
         (reduced (b1-conjunction-associated-conjunction-normalize
                   1000000 lib claim (list :unit value integers) nil)))
      (proof-with-checked-results
          ((step (proof-proof-transport (library-library-proof (cdr reduced))
                                        (car reduced) reduction)))
        (cons step (cdr reduced))))))

(defun b1-conjunction-associated-conjunction-rewrite-projection (proof step equality)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (value (proof-term-at literal 2))
       (equation (proof-step-first equality))
       (slot (proof-term-at equation 1)))
    (proof-proof-rewrite-result proof step equality (proof-eq *proof-false* value) slot)))

(defun b1-conjunction-associated-conjunction-ordinary (int-x int-y int-z lib formula variables)
  (proof-with-checked-results
      ((projected-xy (b1-conjunction-use-projection lib int-x int-y))
       (projected-yz (b1-conjunction-use-projection (cdr projected-xy) int-y int-z)))
    (let* ((lib (cdr projected-yz))
           (projected-xy (car projected-xy))
           (projected-yz (car projected-yz))
           (x (car variables))
           (zero (proof-eq x *proof-zero*))
           (minus-one (proof-eq x *proof-neg-one*)))
      (proof-with-checked-results
          ((xy-int (proof-term-at projected-xy 0))
           (lhs (b1-conjunction-joined-conjunction lib xy-int int-z))
           (yz-int (proof-term-at projected-yz 0))
           (rhs (b1-conjunction-joined-conjunction (cdr lhs) int-x yz-int))
           (lib (cdr rhs))
           (proof (library-library-proof lib))
           (xy-floor (proof-term-at projected-xy 1))
           (lhs (proof-proof-rewrite proof (car lhs) xy-floor '(1 2 1 2 1)))
           (yz-floor (proof-term-at projected-yz 1))
           (rhs (proof-proof-rewrite proof (car rhs) yz-floor '(1 2 1 2 2)))
           (xy-even (proof-term-at projected-xy 2))
           (lhs (b1-conjunction-associated-conjunction-rewrite-projection proof lhs xy-even))
           (yz-even (proof-term-at projected-yz 2))
           (rhs (b1-conjunction-associated-conjunction-rewrite-projection proof rhs yz-even))
           (no-zero (proof-proof-assume proof zero nil))
           (no-zip (b1-conjunction-zip-from-integer lib int-x no-zero))
           (descent-name (b1-bitwise-floor-half-descent lib))
           (lib (cdr descent-name))
           (proof (library-library-proof lib))
           (no-minus (proof-proof-assume proof minus-one nil))
           (descent (proof-proof-use proof (car descent-name) (list (list *library-x* x))
                                     (list no-zip no-minus)))
           (smaller (b1-conjunction-induction-half lib formula variables descent))
           (lhs (proof-proof-rewrite proof lhs smaller '(1 2 1 2)))
           (lhs-first (proof-step-first lhs))
           (lhs-value (proof-term-at lhs-first 2))
           (rhs-first (proof-step-first rhs))
           (rhs-value (proof-term-at rhs-first 2))
           (same (b1-logic-bookproof-case-proof lib (proof-eq lhs-value rhs-value) nil nil nil 16))
           (reversed (proof-proof-symmetric proof rhs))
           (successor (proof-proof-chain proof lhs (list same reversed)))
           (at-zero (b1-conjunction-associated-conjunction-base
                     zero lib formula int-y int-z projected-yz))
           (at-minus (b1-conjunction-associated-conjunction-base
                      minus-one (cdr at-zero) formula int-y int-z projected-yz))
           (lib (cdr at-minus))
           (proof (library-library-proof lib))
           (nonzero (proof-proof-cases proof minus-one (car at-minus) successor))
           (step (proof-proof-cases proof zero (car at-zero) nonzero)))
        (cons step lib)))))

(defun b1-conjunction-with-integers-visit (remaining proofs lib ordinary exceptional)
  (declare (xargs :measure (len remaining)))
  (if (endp remaining)
      (if (eq (car ordinary) :full)
          (b1-conjunction-full-conjunction-ordinary
           (car proofs) (cadr proofs) lib
           (cadr ordinary) (caddr ordinary) (cadddr ordinary) (car (cddddr ordinary)))
        (b1-conjunction-associated-conjunction-ordinary
         (car proofs) (cadr proofs) (caddr proofs) lib (cadr ordinary) (caddr ordinary)))
    (let* ((term (car remaining))
           (test (library-integer term)))
      (proof-with-checked-results
          ((integral (b1-conjunction-case-assume lib test t))
           (yes (b1-conjunction-with-integers-visit
                 (cdr remaining) (append proofs (list integral)) lib ordinary exceptional))
           (lib (cdr yes))
           (noninteger (b1-conjunction-case-assume lib test nil))
           (no (if (eq (car exceptional) :full)
                   (b1-conjunction-full-conjunction-exceptional
                    term noninteger lib (cadr exceptional) (caddr exceptional))
                 (b1-conjunction-associated-conjunction-exceptional
                  term noninteger lib (cadr exceptional))))
           (lib (cdr no))
           (step (proof-proof-cases (library-library-proof lib) test (car yes) (car no))))
        (cons step lib)))))

(defun b1-conjunction-with-integers (lib variables ordinary exceptional)
  (b1-conjunction-with-integers-visit variables nil lib ordinary exceptional))

(defun b1-conjunction-full-conjunction (lib formula)
  (proof-with-checked-results
      ((condition (proof-term-at formula 1))
       (term (proof-term-at condition 1))
       (args (b1-conjunction-term-args term 2))
       (x (car args))
       (y (cadr args))
       (both (proof-term-at formula 2))
       (case-step (b1-conjunction-with-integers lib (list x y) (list :full formula term x y)
                                               (list :full term formula)))
       (lib (cdr case-step))
       (ordinal (library-library-builtin lib 1 x))
       (step (proof-proof-induct (library-library-proof lib) ordinal (car case-step)
                                 formula (list *library-count* x)
                                 (list (b1-conjunction-halving-pairs (list x y))))))
    (cons step lib)))

(defun b1-conjunction-associated-conjunction (lib formula)
  (proof-with-checked-results
      ((lhs (proof-term-at formula 1))
       (outer-args (b1-conjunction-term-args lhs 2))
       (inner-args (b1-conjunction-term-args (car outer-args) 2))
       (x (car inner-args))
       (variables (list x (cadr inner-args) (cadr outer-args)))
       (case-step (b1-conjunction-with-integers lib variables (list :associated formula variables)
                                               (list :associated formula)))
       (lib (cdr case-step))
       (ordinal (library-library-builtin lib 1 x))
       (step (proof-proof-induct (library-library-proof lib) ordinal (car case-step)
                                 formula (list *library-count* x)
                                 (list (b1-conjunction-halving-pairs variables)))))
    (cons step lib)))
