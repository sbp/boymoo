(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-mismatch-mismatch* (proof-sym "LOGBITP-MISMATCH" "ACL2"))
(defconst *b1-mismatch-max* (proof-cl "MAX"))
(defconst *b1-mismatch-logbitp* (proof-cl "LOGBITP"))
(defconst *b1-mismatch-oddp* (proof-cl "ODDP"))

; A paired binding takes its value and its Library from one call.
(defmacro b1-mismatch-let (bindings result)
  (if (endp bindings)
      result
    (let* ((binding (car bindings))
           (target (car binding)))
      (if (consp target)
          (let ((name (car target))
                (lib (cadr target)))
            `(proof-with-checked-results ((,name ,(cadr binding)))
               (let ((,name (car ,name))
                     (,lib (cdr ,name)))
                 (declare (ignorable ,name ,lib))
                 (b1-mismatch-let ,(cdr bindings) ,result))))
        `(proof-with-checked-results (,binding)
           (b1-mismatch-let ,(cdr bindings) ,result))))))

(defmacro b1-mismatch-pair (lib form)
  `(proof-with-checked-results ((b1-mismatch-value ,form))
     (cons b1-mismatch-value ,lib)))

(defmacro b1-mismatch-normalize (lib term &key evidence unfold rules)
  `(b1-logic-bookproof-normalize ,lib ,term ,evidence ,unfold ,rules
                               nil nil nil))

(defmacro b1-mismatch-normalize-proof (lib term &key evidence unfold rules)
  `(b1-logic-bookproof-normalize-proof ,lib ,term ,evidence ,unfold ,rules nil))

(defmacro b1-mismatch-case-proof (lib term &key evidence unfold rules)
  `(b1-logic-bookproof-case-proof ,lib ,term ,evidence ,unfold ,rules 16))

(defun b1-mismatch-term-at-path (term path)
  (declare (xargs :measure (acl2-count path)))
  (if (endp path)
      term
    (proof-with-checked-results ((part (proof-term-at term (car path))))
      (b1-mismatch-term-at-path part (cdr path)))))

(defun b1-mismatch-step-at-path (step path)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (b1-mismatch-term-at-path literal path)))

(defmacro b1-mismatch-at (term &rest path)
  `(b1-mismatch-term-at-path ,term ',path))

(defmacro b1-mismatch-step-at (step &rest path)
  `(b1-mismatch-step-at-path ,step ',path))

(defun b1-mismatch-term-arguments (term)
  (if (integerp term)
      '(:failure "failure" "")
    (cdr term)))

(defun b1-mismatch-two-arguments (term)
  (proof-with-checked-results ((args (b1-mismatch-term-arguments term)))
    (proof-list-of-length args 2)))

(defun b1-mismatch-mismatch-induction-init (lib call formula)
  (b1-mismatch-let
    ((args (b1-mismatch-two-arguments call))
     (a (car args))
     (b (cadr args))
     (length-a (list *b1-bit-length-length* a))
     (length-b (list *b1-bit-length-length* b))
     (measure (library-plus length-a length-b))
     (substitution
      (table-put (list (cons a (list *b1-bit-length-logcdr* a)))
                   b (list *b1-bit-length-logcdr* b)))
     (child (proof-subst call substitution))
     (low-match (proof-eq (list *b1-bit-types-logcar* a)
                         (list *b1-bit-types-logcar* b)))
     (stopped (proof-ite (list *b1-logic-zp* length-a)
                        (list *b1-logic-zp* length-b)
                        *proof-false*))
     (view (library-inherited proof-proof-unfold lib call)))
    (list :b1-mismatch-mismatch-induction lib call formula measure
          substitution child low-match stopped view)))

(defun b1-mismatch-mismatch-induction-lib (induction)
  (cadr induction))

(defun b1-mismatch-mismatch-induction-call (induction)
  (caddr induction))

(defun b1-mismatch-mismatch-induction-formula (induction)
  (cadddr induction))

(defun b1-mismatch-mismatch-induction-measure (induction)
  (nth 4 induction))

(defun b1-mismatch-mismatch-induction-substitution (induction)
  (nth 5 induction))

(defun b1-mismatch-mismatch-induction-child (induction)
  (nth 6 induction))

(defun b1-mismatch-mismatch-induction-low-match (induction)
  (nth 7 induction))

(defun b1-mismatch-mismatch-induction-stopped (induction)
  (nth 8 induction))

(defun b1-mismatch-mismatch-induction-view (induction)
  (nth 9 induction))

(defun b1-mismatch-mismatch-induction-with-lib (induction lib)
  (cons (car induction) (cons lib (cddr induction))))

(defun b1-mismatch-mismatch-induction-first (induction)
  (b1-mismatch-let
    ((lib (b1-mismatch-mismatch-induction-lib induction))
     (view (b1-mismatch-mismatch-induction-view induction))
     (opened (b1-mismatch-step-at view 2))
     (different (library-inherited proof-proof-assume lib
                                  (b1-mismatch-mismatch-induction-low-match induction)
                                  nil))
     (selected (library-inherited proof-proof-select lib opened different)))
    (library-inherited proof-proof-chain lib view (list selected))))

(defun b1-mismatch-mismatch-induction-matching (induction equal-step)
  (b1-mismatch-let
    ((lib (b1-mismatch-mismatch-induction-lib induction))
     (low-match (b1-mismatch-mismatch-induction-low-match induction))
     (not-different (b1-mismatch-normalize lib (proof-neg low-match)
                                          :evidence (list equal-step)
                                          :unfold (list *proof-not*)))
     (rule (b1-logic-equal-to not-different))
     (literal (b1-mismatch-normalize-proof lib (proof-neg (proof-neg low-match))
                                           :unfold (list *proof-not*)
                                           :rules (list rule)))
     (view (b1-mismatch-mismatch-induction-view induction))
     (opened (b1-mismatch-step-at view 2))
     (selected (library-inherited proof-proof-select lib opened literal)))
    (library-inherited proof-proof-chain lib view (list selected))))

(defun b1-mismatch-mismatch-induction-later (induction opened)
  (b1-mismatch-let
    ((lib (b1-mismatch-mismatch-induction-lib induction))
     (branch (b1-mismatch-step-at opened 2))
     (selected (library-inherited proof-proof-if-false lib branch))
     (continued (library-inherited proof-proof-chain lib opened (list selected)))
     (body (b1-mismatch-step-at continued 2))
     (normalized (b1-mismatch-normalize lib body)))
    (library-inherited proof-proof-chain lib continued (list normalized))))

(defun b1-mismatch-mismatch-induction-hypothesis (induction)
  (b1-mismatch-let
    ((lib (b1-mismatch-mismatch-induction-lib induction))
     (measure (b1-mismatch-mismatch-induction-measure induction))
     (substitution (b1-mismatch-mismatch-induction-substitution induction))
     (smaller-measure (proof-subst measure substitution))
     (smaller (list *proof-ordinal-less* smaller-measure measure))
     ((descent lib)
      (b1-bit-length-paired-bit-length-descent
       lib smaller (b1-mismatch-mismatch-induction-stopped induction)))
     (child (proof-subst (b1-mismatch-mismatch-induction-formula induction)
                        substitution))
     (assumption (library-inherited proof-proof-assume lib
                                     (proof-ite smaller child *proof-true*) t)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-prove-if lib assumption descent))))

(defun b1-mismatch-mismatch-induction-finish (induction step)
  (b1-mismatch-let
    ((lib (b1-mismatch-mismatch-induction-lib induction))
     (measure (b1-mismatch-mismatch-induction-measure induction))
     ((ordinal lib) (b1-bit-length-bit-length-sum-ordinal lib measure))
     (bindings (table-items (b1-mismatch-mismatch-induction-substitution induction))))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-induct lib ordinal step
                         (b1-mismatch-mismatch-induction-formula induction)
                         measure (list bindings)))))

(defun b1-mismatch-normalized-bit-functions (lib term)
  (let ((ifix *b1-quotient-ifix*)
        (logcar *b1-bit-types-logcar*)
        (logcdr *b1-bit-length-logcdr*))
    (b1-mismatch-let
      ((fixed-two (b1-mismatch-normalize lib (list ifix *b1-bits-two*)
                                          :unfold (list ifix)))
       (low-rule (b1-logic-equal-to fixed-two))
       (low (b1-mismatch-normalize lib (list logcar term)
                                    :unfold (list logcar *b1-bit-types-imod*)
                                    :rules (list low-rule)))
       (high-rule (b1-logic-equal-to fixed-two))
       (high (b1-mismatch-normalize lib (list logcdr term)
                                     :unfold (list logcdr *b1-bit-length-ifloor*)
                                     :rules (list high-rule))))
      (list low high))))

(defun b1-mismatch-bit-join (lib term low high)
  (b1-mismatch-let
    ((integral (b1-bit-types-integer-fix lib (list *b1-quotient-ifix* term)))
     ((formula lib) (b1-bits-decomposition lib integral))
     ((mod-two lib) (b1-bit-types-mod-two-equation lib integral))
     (low-part (library-inherited proof-proof-chain lib low (list mod-two)))
     (reverse-high (library-inherited proof-proof-symmetric lib high))
     (replaced (library-inherited proof-proof-rewrite lib formula reverse-high
                                   '(1 2 1 2)))
     (reverse-low (library-inherited proof-proof-symmetric lib low-part)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-rewrite lib replaced reverse-low '(1 2 2)))))

(defun b1-mismatch-equality-from-bit-parts-counterpart (p q lib positive-same)
  (b1-mismatch-let
    ((partial (library-inherited proof-proof-rewrite lib p positive-same '(1 2 1)))
     (reverse-q (library-inherited proof-proof-symmetric lib q)))
    (library-inherited proof-proof-chain lib partial (list reverse-q))))

(defun b1-mismatch-add-equality-from-bit-parts (lib)
  (b1-mismatch-let
    ((left (b1-mismatch-normalized-bit-functions lib *library-x*))
     (right (b1-mismatch-normalized-bit-functions lib *library-y*))
     (same (proof-eq (list *b1-quotient-ifix* *library-x*)
                     (list *b1-quotient-ifix* *library-y*)))
     (low-x (b1-mismatch-step-at (car left) 1))
     (low-y (b1-mismatch-step-at (car right) 1))
     (low (proof-eq low-x low-y))
     (high-x (b1-mismatch-step-at (cadr left) 1))
     (high-y (b1-mismatch-step-at (cadr right) 1))
     (high (proof-eq high-x high-y))
     (claim (proof-eq same (proof-ite low high *proof-false*)))
     (positive-same (library-inherited proof-proof-assume lib same t))
     (negative-same (library-inherited proof-proof-assume lib same nil))
     (low-counterpart
      (b1-mismatch-equality-from-bit-parts-counterpart
       (car left) (car right) lib positive-same))
     (high-counterpart
      (b1-mismatch-equality-from-bit-parts-counterpart
       (cadr left) (cadr right) lib positive-same))
     (good (b1-mismatch-case-proof lib claim
                                    :evidence (list positive-same low-counterpart
                                                    high-counterpart)))
     (low-match (library-inherited proof-proof-assume lib low t))
     (high-match (library-inherited proof-proof-assume lib high t))
     ((join-x lib) (b1-mismatch-bit-join lib *library-x* (car left) (cadr left)))
     ((join-y lib) (b1-mismatch-bit-join lib *library-y* (car right) (cadr right)))
     (joined (library-inherited proof-proof-rewrite lib join-x high-match '(1 2 1 2)))
     (joined (library-inherited proof-proof-rewrite lib joined low-match '(1 2 2)))
     (reverse-y (library-inherited proof-proof-symmetric lib join-y))
     (equal-step (library-inherited proof-proof-chain lib joined (list reverse-y)))
     (impossible (b1-logic-bookproof-contradiction lib equal-step negative-same claim))
     (low-differs (library-inherited proof-proof-assume lib low nil))
     (wrong-low (b1-mismatch-case-proof lib claim
                                         :evidence (list negative-same low-differs)))
     (high-differs (library-inherited proof-proof-assume lib high nil))
     (wrong-high (b1-mismatch-case-proof
                  lib claim :evidence (list negative-same low-match high-differs)))
     (bad-high (library-inherited proof-proof-cases lib high impossible wrong-high))
     (bad (library-inherited proof-proof-cases lib low bad-high wrong-low))
     (step (library-inherited proof-proof-cases lib same good bad)))
    (library-library-lemma lib "FIXED-INTEGER-EQUALITY-BY-BITS" claim step nil)))

(defun b1-mismatch-equality-from-bit-parts (lib a b)
  (let ((name (proof-sym "SELF-FIXED-INTEGER-EQUALITY-BY-BITS" "ACL2")))
    (b1-mismatch-let
      ((lib (if (assoc-equal name (library-inherited proof-proof-facts lib))
                lib
              (b1-mismatch-add-equality-from-bit-parts lib))))
      (b1-mismatch-pair lib
        (library-inherited proof-proof-fact lib name
                           (list (list *library-x* a) (list *library-y* b)))))))

(defun b1-mismatch-zero-length-values (lib term stopped)
  (b1-mismatch-let
    ((fixed (list *b1-quotient-ifix* term))
     (zero-eq (proof-eq fixed *proof-zero*))
     (unit-eq (proof-eq fixed *proof-neg-one*))
     (claim (proof-ite zero-eq zero-eq unit-eq))
     (opened (b1-bit-length-open-length lib term))
     (zero (car opened))
     (unit (cadr opened))
     (step (nth 4 opened))
     (zero-case (library-inherited proof-proof-assume lib zero t))
     (zero-fixed (b1-bit-length-fixed-integer-when-zero lib term zero-case))
     (selected (library-inherited proof-proof-select lib claim zero-fixed))
     (at-zero (library-inherited proof-proof-transport lib zero-fixed selected))
     (unit-case (library-inherited proof-proof-assume lib unit t))
     (unit-opened (library-inherited proof-proof-unfold lib unit))
     (unit-value (library-inherited proof-proof-rewrite lib unit-case unit-opened '(1)))
     (unit-rule (b1-logic-equal-to unit-value))
     (unit-fixed (b1-mismatch-normalize lib fixed
                                        :unfold (list *b1-quotient-ifix*)
                                        :rules (list unit-rule)))
     (at-unit (b1-revappend-right-disjunct lib claim unit-fixed))
     (shorter (b1-mismatch-step-at step 2 2))
     (shorter-arg (proof-term-at shorter 1))
     ((natural lib) (b1-bit-length-natural-bit-length lib shorter-arg))
     (integral (library-library-cite lib "NATURAL-INTEGER" (list shorter) (list natural)))
     (lower (library-library-cite lib "NATURAL-NONNEGATIVE" (list shorter) (list natural)))
     (positive-len
      (library-library-cite lib "POSITIVE-ONE-PLUS" (list shorter) (list integral lower)))
     (sum (b1-mismatch-step-at step 2))
     (typed-sum (library-library-type-of lib sum (list integral)))
     (typed-len (library-library-transport-argument lib typed-sum step 1))
     (positive-len (library-library-transport-argument lib positive-len step 2))
     (stopped-literal (proof-step-first stopped))
     (rejected (b1-mismatch-normalize lib stopped-literal
                                      :evidence (list typed-len positive-len)
                                      :unfold (list *b1-logic-zp* *proof-not*)))
     (stopped-false (library-inherited proof-proof-rewrite lib stopped rejected '(1)))
     (non-nil (library-inherited b1-logic-proof-not-nil lib))
     (impossible (b1-logic-bookproof-contradiction lib stopped-false non-nil claim))
     (unit-split (library-inherited proof-proof-cases lib unit at-unit impossible)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-cases lib zero at-zero unit-split))))

(defun b1-mismatch-low-bit-of-fixed-point (lib term fixed)
  (b1-mismatch-let
    ((bits (b1-mismatch-normalized-bit-functions lib term))
     (low (library-inherited proof-proof-rewrite lib (car bits) fixed '(1 2 1)))
     (value (b1-mismatch-step-at fixed 2))
     (integral (library-library-type-of lib value nil))
     ((equation lib) (b1-bit-types-mod-two-equation lib integral))
     (body (b1-mismatch-step-at equation 2))
     (branch (b1-mismatch-normalize lib body :unfold (list *b1-bits-evenp*))))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-chain lib low (list equation branch)))))

(defun b1-mismatch-fixed-points-agree-compare (first second lib a b low goal)
  (b1-mismatch-let
    ((first-value (b1-mismatch-step-at first 2))
     (second-value (b1-mismatch-step-at second 2)))
    (if (equal first-value second-value)
        (b1-mismatch-let
          ((reverse-second (library-inherited proof-proof-symmetric lib second)))
          (b1-mismatch-pair lib
            (library-inherited proof-proof-chain lib first (list reverse-second))))
      (b1-mismatch-let
        (((left lib) (b1-mismatch-low-bit-of-fixed-point lib a first))
         ((right lib) (b1-mismatch-low-bit-of-fixed-point lib b second))
         (conflict (library-inherited proof-proof-rewrite lib low left '(1 1)))
         (conflict (library-inherited proof-proof-rewrite lib conflict right '(1 2)))
         (literal (proof-step-first conflict))
         (constant (b1-logic-bookproof-constant lib literal))
         (conflict (library-inherited proof-proof-rewrite lib conflict constant '(1)))
         (non-nil (library-inherited b1-logic-proof-not-nil lib)))
        (b1-mismatch-pair lib
          (b1-logic-bookproof-contradiction lib conflict non-nil goal))))))

(defun b1-mismatch-fixed-points-agree-cases (first lib a b low goal b-zero b-values)
  (b1-mismatch-let
    ((at-zero (library-inherited proof-proof-assume lib b-zero t))
     ((yes lib) (b1-mismatch-fixed-points-agree-compare first at-zero lib a b low goal))
     (nonzero (library-inherited proof-proof-assume lib b-zero nil))
     (at-unit (library-inherited proof-proof-prove-if lib b-values nonzero))
     ((no lib) (b1-mismatch-fixed-points-agree-compare first at-unit lib a b low goal)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-cases lib b-zero yes no))))

(defun b1-mismatch-fixed-points-agree (lib a b finished low)
  (b1-mismatch-let
    ((stops (library-inherited proof-proof-conjunct lib finished))
     ((a-values lib) (b1-mismatch-zero-length-values lib a (car stops)))
     ((b-values lib) (b1-mismatch-zero-length-values lib b (cadr stops)))
     (a-zero (b1-mismatch-step-at a-values 1))
     (b-zero (b1-mismatch-step-at b-values 1))
     (goal (proof-eq (list *b1-quotient-ifix* a) (list *b1-quotient-ifix* b)))
     (at-zero (library-inherited proof-proof-assume lib a-zero t))
     ((yes lib)
      (b1-mismatch-fixed-points-agree-cases at-zero lib a b low goal b-zero b-values))
     (nonzero (library-inherited proof-proof-assume lib a-zero nil))
     (at-unit (library-inherited proof-proof-prove-if lib a-values nonzero))
     ((no lib)
      (b1-mismatch-fixed-points-agree-cases at-unit lib a b low goal b-zero b-values)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-cases lib a-zero yes no))))

(defun b1-mismatch-natural-mismatch-consequence (premise lib induction claim low)
  (b1-mismatch-let
    ((zero-type (library-library-natural lib *proof-zero*))
     (initial (b1-mismatch-mismatch-induction-first induction))
     (immediate (library-library-transport-argument lib zero-type initial 1))
     (equal-step (library-inherited proof-proof-assume lib low t))
     (view (b1-mismatch-mismatch-induction-matching induction equal-step))
     (opened (b1-mismatch-step-at view 2))
     (true-branch (library-inherited proof-proof-if-true lib opened))
     (finished (library-inherited proof-proof-chain lib view (list true-branch)))
     (premise-finished (library-inherited proof-proof-rewrite lib premise finished '(1)))
     (non-nil (library-inherited b1-logic-proof-not-nil lib))
     (empty-case (b1-logic-bookproof-contradiction lib premise-finished non-nil claim))
     (advanced (b1-mismatch-mismatch-induction-later induction view))
     (child-term (b1-mismatch-mismatch-induction-child induction))
     (child (library-inherited proof-proof-assume lib child-term t))
     (advanced-body (b1-mismatch-step-at advanced 2))
     (false-branch (library-inherited proof-proof-if-false lib advanced-body))
     (exhausted (library-inherited proof-proof-chain lib advanced (list false-branch)))
     (premise-exhausted (library-inherited proof-proof-rewrite lib premise exhausted '(1)))
     (non-nil (library-inherited b1-logic-proof-not-nil lib))
     (absent (b1-logic-bookproof-contradiction lib premise-exhausted non-nil claim))
     ((law lib) (b1-mismatch-mismatch-induction-hypothesis induction))
     (tail (library-inherited proof-proof-modus-ponens lib law child))
     (one-type (library-library-natural lib *proof-one*))
     (successor (library-library-cite lib "NATURAL-SUM"
                                      (list *proof-one* child-term)
                                      (list one-type tail)))
     (selected (library-inherited proof-proof-select lib advanced-body child))
     (keep (library-inherited proof-proof-chain lib advanced (list selected)))
     (present (library-library-transport-argument lib successor keep 1))
     (child-case (library-inherited proof-proof-cases lib child-term present absent))
     (stop-case (library-inherited proof-proof-cases lib
                                   (b1-mismatch-mismatch-induction-stopped induction)
                                   empty-case child-case)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-cases lib low stop-case immediate))))

(defun b1-mismatch-add-natural-mismatch (lib)
  (b1-mismatch-let
    ((found (list *b1-mismatch-mismatch* *library-x* *library-y*))
     (claim (list *library-natp* found))
     (formula (list *library-implies* found claim))
     (induction (b1-mismatch-mismatch-induction-init lib found formula))
     (low (b1-mismatch-mismatch-induction-low-match induction))
     (premise (b1-logic-bookproof-prove-implication-premise lib formula))
     ((consequence lib)
      (b1-mismatch-natural-mismatch-consequence premise lib induction claim low))
     (implication
      (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))
     ((step lib)
      (b1-mismatch-mismatch-induction-finish
       (b1-mismatch-mismatch-induction-with-lib induction lib) implication)))
    (library-library-lemma lib "FOUND-MISMATCH-IS-NATURAL" formula step nil)))

(defun b1-mismatch-natural-mismatch (lib call known)
  (let ((name (proof-sym "SELF-FOUND-MISMATCH-IS-NATURAL" "ACL2")))
    (b1-mismatch-let
      ((lib (if (assoc-equal name (library-inherited proof-proof-facts lib))
                lib
              (b1-mismatch-add-natural-mismatch lib)))
       (a (proof-term-at call 1))
       (b (proof-term-at call 2))
       (law (library-inherited proof-proof-fact lib name
                               (list (list *library-x* a) (list *library-y* b)))))
      (b1-mismatch-pair lib
        (library-inherited proof-proof-modus-ponens lib law known)))))

(defun b1-mismatch-equality-rules (steps)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      nil
    (list* (b1-logic-equal-to (car steps))
           (b1-mismatch-equality-rules (cdr steps)))))

(defun b1-mismatch-mismatch-exists-establish (reduction evidence extra lib formula)
  (b1-mismatch-case-proof lib formula
                          :evidence evidence
                          :unfold (list *b1-revappend-iff* *proof-not*)
                          :rules (b1-mismatch-equality-rules (cons reduction extra))))

(defun b1-mismatch-mismatch-exists-rewrite-hypothesis (lib hypothesis high-values)
  (declare (xargs :measure (acl2-count high-values)))
  (if (endp high-values)
      (cons hypothesis lib)
    (b1-mismatch-let
      ((value (car high-values))
       ((type-step lib)
        (b1-bit-types-numeric-type 1000000 lib *proof-integerp* value nil))
       (fixed (b1-mismatch-normalize lib (list *b1-quotient-ifix* value)
                                       :evidence (list type-step)
                                       :unfold (list *b1-quotient-ifix*)))
       (hypothesis (library-inherited proof-proof-rewrite-first lib hypothesis fixed)))
      (b1-mismatch-mismatch-exists-rewrite-hypothesis lib hypothesis (cdr high-values)))))

(defun b1-mismatch-mismatch-exists-later
    (present lib recurrence formula high hypothesis opened low-equal pair)
  (b1-mismatch-let
    ((child-term (b1-mismatch-mismatch-induction-child recurrence))
     (child (library-inherited proof-proof-assume lib child-term present))
     (opposite (library-inherited proof-proof-assume lib high present))
     (calculation (if present
                      (b1-logic-bookproof-equality-true lib opposite)
                    (b1-logic-bookproof-false-value lib opposite)))
     (hypothesis-literal (proof-step-first hypothesis))
     (rejected (b1-mismatch-normalize lib hypothesis-literal
                                      :evidence (list child)
                                      :unfold (list *b1-revappend-iff* *proof-not*)
                                      :rules (b1-mismatch-equality-rules (list calculation))))
     (rejected-step (library-inherited proof-proof-rewrite lib hypothesis rejected '(1)))
     (non-nil (library-inherited b1-logic-proof-not-nil lib))
     (contradiction (library-inherited proof-proof-cut lib rejected-step non-nil))
     (determined (library-inherited proof-proof-front lib contradiction
                                    (if present (proof-neg high) high)))
     (view (b1-mismatch-mismatch-induction-later
            (b1-mismatch-mismatch-induction-with-lib recurrence lib) opened))
     (next (b1-mismatch-step-at view 2))
     (selected (library-inherited proof-proof-select lib next child))
     (mapped (library-inherited proof-proof-chain lib view (list selected)))
     ((optional lib)
      (if present
          (b1-mismatch-let
            (((natural lib) (b1-mismatch-natural-mismatch lib child-term child))
             (child-type
              (library-library-cite lib "NATURAL-INTEGER" (list child-term) (list natural)))
             (value (b1-mismatch-step-at mapped 2))
             (integer-value (library-library-type-of lib value (list child-type)))
             (non-nil-value (b1-bit-length-integer-non-nil lib integer-value)))
            (cons (list non-nil-value) lib))
        (cons nil lib)))
     (value (if present
                (b1-logic-bookproof-false-value lib determined)
              (b1-logic-bookproof-equality-true lib determined))))
    (b1-mismatch-pair lib
      (b1-mismatch-mismatch-exists-establish mapped (cons low-equal optional)
                                             (list pair value) lib formula))))

(defun b1-mismatch-mismatch-exists (lib formula)
  (b1-mismatch-let
    ((parts (proof-list-of-length formula 3))
     (call (cadr parts))
     (args (b1-mismatch-two-arguments call))
     (a (car args))
     (b (cadr args))
     (recurrence (b1-mismatch-mismatch-induction-init lib call formula))
     ((pair lib) (b1-mismatch-equality-from-bit-parts lib a b))
     (recurrence (b1-mismatch-mismatch-induction-with-lib recurrence lib))
     (low (b1-mismatch-mismatch-induction-low-match recurrence))
     (stopped (b1-mismatch-mismatch-induction-stopped recurrence))
     (child (b1-mismatch-mismatch-induction-child recurrence))
     (high (b1-mismatch-step-at pair 2 2))
     (initial (b1-mismatch-mismatch-induction-first recurrence))
     (different (library-inherited proof-proof-assume lib low nil))
     (immediate
      (b1-mismatch-mismatch-exists-establish initial (list different) (list pair)
                                             lib formula))
     (low-equal (library-inherited proof-proof-assume lib low t))
     (opened (b1-mismatch-mismatch-induction-matching recurrence low-equal))
     (finished (library-inherited proof-proof-assume lib stopped t))
     ((fixed-equal lib) (b1-mismatch-fixed-points-agree lib a b finished low-equal))
     (opened-body (b1-mismatch-step-at opened 2))
     (selected (library-inherited proof-proof-select lib opened-body finished))
     (empty-case (library-inherited proof-proof-chain lib opened (list selected)))
     (truth (b1-logic-bookproof-equality-true lib fixed-equal))
     (base (b1-mismatch-mismatch-exists-establish empty-case nil (list truth) lib formula))
     ((hypothesis lib)
      (b1-mismatch-mismatch-induction-hypothesis
       (b1-mismatch-mismatch-induction-with-lib recurrence lib)))
     (high-values (b1-mismatch-term-arguments high))
     ((hypothesis lib)
      (b1-mismatch-mismatch-exists-rewrite-hypothesis lib hypothesis high-values))
     ((later-yes lib)
      (b1-mismatch-mismatch-exists-later t lib recurrence formula high
                                         hypothesis opened low-equal pair))
     ((later-no lib)
      (b1-mismatch-mismatch-exists-later nil lib recurrence formula high
                                         hypothesis opened low-equal pair))
     (later (library-inherited proof-proof-cases lib child later-yes later-no))
     (stop-case (library-inherited proof-proof-cases lib stopped base later))
     (split (library-inherited proof-proof-cases lib low stop-case immediate)))
    (b1-mismatch-mismatch-induction-finish
     (b1-mismatch-mismatch-induction-with-lib recurrence lib) split)))

(defun b1-mismatch-fixed-sign-case (step lib fixed claim)
  (b1-mismatch-let
    ((opened (b1-mismatch-normalize lib fixed
                                    :evidence (list step)
                                    :unfold (list *b1-quotient-ifix*))))
    (b1-mismatch-case-proof lib claim
                            :evidence (list step)
                            :rules (b1-mismatch-equality-rules (list opened)))))

(defun b1-mismatch-fixed-sign (lib term)
  (b1-mismatch-let
    ((int-test (library-integer term))
     (fixed (list *b1-quotient-ifix* term))
     (a (library-inherited proof-proof-assume lib int-test t))
     (b (library-inherited proof-proof-assume lib int-test nil))
     (claim (proof-eq (library-lt fixed *proof-zero*)
                      (proof-ite int-test (library-lt term *proof-zero*) *proof-false*)))
     (yes (b1-mismatch-fixed-sign-case a lib fixed claim))
     (no (b1-mismatch-fixed-sign-case b lib fixed claim)))
    (library-inherited proof-proof-cases lib int-test yes no)))

(defun b1-mismatch-nonnegative-high-bits (lib term sign)
  (b1-mismatch-let
    ((fixed (list *b1-quotient-ifix* term))
     (integral (b1-bit-types-integer-fix lib fixed))
     (sign-law (b1-mismatch-fixed-sign lib term))
     (reverse-sign (library-inherited proof-proof-symmetric lib sign-law))
     (lower (library-inherited proof-proof-rewrite lib sign reverse-sign '(1 1)))
     (test (proof-eq fixed *proof-zero*))
     (bits (b1-mismatch-normalized-bit-functions lib term))
     (high (cadr bits))
     (zero-step (library-inherited proof-proof-assume lib test t))
     (in-zero (library-inherited proof-proof-rewrite lib high zero-step '(1 2 1)))
     ((constant-bits lib) (b1-bits-constant-bit-pair lib *proof-zero* *proof-zero*))
     (in-zero (library-inherited proof-proof-chain lib in-zero (list (car constant-bits))))
     (zero-natural (library-library-natural lib *proof-zero*))
     (yes (library-library-transport-argument lib zero-natural in-zero 1))
     (order (b1-arithmetic-integer-compare lib fixed *proof-zero* (list integral)))
     (above (library-inherited proof-proof-discharge lib order lower))
     ((half-bounds lib) (b1-quotient-floor-half-bound lib fixed integral above))
     (natural (cadr half-bounds))
     (high-rhs (b1-mismatch-step-at high 2))
     (ratio (b1-floor-floor-of-ratio lib high-rhs))
     (inverse (b1-logic-bookproof-constant lib (b1-arithmetic-reciprocal *b1-bits-two*)))
     (ratio (library-inherited proof-proof-rewrite-first lib ratio inverse))
     (high-ratio (library-inherited proof-proof-chain lib high (list ratio)))
     (no (library-library-transport-argument lib natural high-ratio 1))
     (nat (library-inherited proof-proof-cases lib test yes no))
     (child (b1-mismatch-step-at nat 1))
     (integer-child (library-library-cite lib "NATURAL-INTEGER" (list child) (list nat)))
     (child-lower (library-library-cite lib "NATURAL-NONNEGATIVE" (list child) (list nat)))
     (raw (proof-neg (proof-ite (library-integer child)
                                (library-lt child *proof-zero*) *proof-false*))))
    (b1-mismatch-pair lib
      (b1-mismatch-normalize-proof lib raw
                                  :evidence (list integer-child child-lower)
                                  :unfold (list *proof-not*)))))

(defun b1-mismatch-max-with-zero (lib term-natural active-left parts)
  (b1-mismatch-let
    ((term (b1-mismatch-step-at term-natural 1))
     (expression (if active-left
                     (list *b1-mismatch-max* term *proof-zero*)
                   (list *b1-mismatch-max* *proof-zero* term)))
     (lower (library-library-cite lib "NATURAL-NONNEGATIVE" (list term)
                                  (list term-natural))))
    (if (not active-left)
        (b1-mismatch-pair lib
          (b1-mismatch-normalize lib expression :evidence (list lower)
                                                :unfold (list *b1-mismatch-max*)))
      (b1-mismatch-let
        ((positive-test (library-lt *proof-zero* term))
         (positive-step (library-inherited proof-proof-assume lib positive-test t))
         (yes (b1-mismatch-normalize lib expression :evidence (list positive-step)
                                                   :unfold (list *b1-mismatch-max*)))
         (negative (library-inherited proof-proof-assume lib positive-test nil))
         (choice (b1-mismatch-normalize lib expression :evidence (list negative)
                                                      :unfold (list *b1-mismatch-max*)))
         (integral (library-library-cite lib "NATURAL-INTEGER" (list term)
                                         (list term-natural)))
         (order (b1-arithmetic-integer-compare lib term *proof-zero* (cons integral parts)))
         (order (library-inherited proof-proof-discharge lib order lower))
         (cut (library-inherited proof-proof-cut lib order negative))
         (zero (library-inherited proof-proof-front lib cut (proof-eq term *proof-zero*)))
         (reverse-zero (library-inherited proof-proof-symmetric lib zero))
         (no (library-inherited proof-proof-chain lib choice (list reverse-zero))))
        (b1-mismatch-pair lib
          (library-inherited proof-proof-cases lib positive-test yes no))))))

(defun b1-mismatch-maximum-decreases-combine
    (parent-a child-a step-a parent-b child-b step-b lib stopped original claim)
  (let ((equations (list parent-a parent-b child-a child-b)))
    (cond
     ((not (or step-a step-b))
      (b1-mismatch-let
        ((stop (b1-mismatch-normalize-proof lib stopped
                                            :unfold (list *b1-logic-zp* *proof-not*)
                                            :rules (b1-mismatch-equality-rules equations)))
         (continuing (library-inherited proof-proof-assume lib stopped nil)))
        (b1-mismatch-pair lib
          (b1-logic-bookproof-contradiction lib stop continuing claim))))
     ((and step-a step-b)
      (b1-mismatch-let
        ((after-a (b1-mismatch-step-at child-a 2))
         (after-b (b1-mismatch-step-at child-b 2))
         (term-a (proof-term-at after-a 1))
         ((natural-a lib) (b1-bit-length-natural-bit-length lib term-a))
         (term-b (proof-term-at after-b 1))
         ((natural-b lib) (b1-bit-length-natural-bit-length lib term-b))
         (length-a (b1-mismatch-step-at natural-a 1))
         (type-a (library-library-cite lib "NATURAL-INTEGER" (list length-a) (list natural-a)))
         (length-b (b1-mismatch-step-at natural-b 1))
         (type-b (library-library-cite lib "NATURAL-INTEGER" (list length-b) (list natural-b)))
         (before-b (b1-mismatch-step-at parent-b 2))
         (before-a (b1-mismatch-step-at parent-a 2))
         (before (library-lt before-b before-a))
         (after (library-lt after-b after-a))
         (sums (b1-arithmetic-number-sums-init lib))
         (lib (b1-arithmetic-number-sums-library sums))
         (comparison (b1-arithmetic-number-sums-comparison-equation
                      sums before after (list type-a type-b))))
        (b1-mismatch-pair lib
          (b1-mismatch-case-proof lib claim
                                  :unfold (list *b1-mismatch-max*)
                                  :rules (b1-mismatch-equality-rules
                                          (append equations (list comparison)))))))
     (t
      (b1-mismatch-let
        ((active (b1-mismatch-step-at (if step-a child-a child-b) 2))
         (term (proof-term-at active 1))
         ((nat lib) (b1-bit-length-natural-bit-length lib term))
         (integral (library-library-cite lib "NATURAL-INTEGER" (list active) (list nat)))
         (one (library-library-natural lib *proof-one*))
         (nat-parent (library-library-cite lib "NATURAL-SUM" (list *proof-one* active)
                                          (list one nat)))
         ((maximum-parent lib) (b1-mismatch-max-with-zero lib nat-parent step-a (list integral)))
         ((maximum-child lib) (b1-mismatch-max-with-zero lib nat step-a nil))
         (left (b1-mismatch-normalize lib original
                                      :rules (b1-mismatch-equality-rules
                                              (list parent-a parent-b maximum-parent))))
         (target (proof-term-at claim 2))
         (right (b1-mismatch-normalize lib target
                                       :rules (b1-mismatch-equality-rules
                                               (list child-a child-b maximum-child))))
         (reverse-right (library-inherited proof-proof-symmetric lib right)))
        (b1-mismatch-pair lib
          (library-inherited proof-proof-chain lib left (list reverse-right))))))))

; Each request receives the original library and the accumulated replies.
(defun b1-mismatch-continue-length-cases (lib term replies reply)
  (if (failure-p reply)
      reply
    (b1-bit-length-length-halving-cases lib term replies)))

(defun b1-mismatch-maximum-decreases-first-case
    (n left lib b stopped original claim replies result)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "b1-mismatch-maximum-decreases-first-case"))
        ((failure-p result) result)
        ((not (eq (caar result) :b1-bit-length-case)) result)
        (t
         (let* ((right (car result))
                (reply (b1-mismatch-maximum-decreases-combine
                        (cadr left) (caddr left) (cadddr left)
                        (cadr right) (caddr right) (cadddr right)
                        (cdr result) stopped original claim))
                (replies (append replies (list reply))))
           (b1-mismatch-maximum-decreases-first-case
            (1- n) left lib b stopped original claim replies
            (b1-mismatch-continue-length-cases lib b replies reply))))))

(defun b1-mismatch-maximum-decreases-cases (n lib a b stopped original claim replies result)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "b1-mismatch-maximum-decreases-cases"))
        ((failure-p result) result)
        ((not (eq (caar result) :b1-bit-length-case)) result)
        (t
         (let* ((current-lib (cdr result))
                (reply (b1-mismatch-maximum-decreases-first-case
                        1000000 (car result) current-lib b stopped original claim nil
                        (b1-bit-length-length-halving-cases current-lib b nil)))
                (replies (append replies (list reply))))
           (b1-mismatch-maximum-decreases-cases
            (1- n) lib a b stopped original claim replies
            (b1-mismatch-continue-length-cases lib a replies reply))))))

(defun b1-mismatch-maximum-decreases (lib recurrence)
  (b1-mismatch-let
    ((args (b1-mismatch-two-arguments (b1-mismatch-mismatch-induction-call recurrence)))
     (a (car args))
     (b (cadr args))
     (original (list *b1-mismatch-max*
                     (list *b1-bit-length-length* a)
                     (list *b1-bit-length-length* b)))
     (high (list *b1-mismatch-max*
                 (list *b1-bit-length-length* (list *b1-bit-length-logcdr* a))
                 (list *b1-bit-length-length* (list *b1-bit-length-logcdr* b))))
     (claim (proof-eq original (library-plus *proof-one* high))))
    (b1-mismatch-maximum-decreases-cases
     1000000 lib a b (b1-mismatch-mismatch-induction-stopped recurrence) original claim nil
     (b1-bit-length-length-halving-cases lib a nil))))

(defun b1-mismatch-maximum-length-type-leaf (length-term lib)
  (b1-mismatch-let
    ((term (proof-term-at length-term 1)))
    (b1-bit-length-natural-bit-length lib term)))

(defun b1-mismatch-maximum-length-type-leaves (lib leaves replies)
  (declare (xargs :measure (acl2-count leaves)))
  (if (endp leaves)
      (cons replies lib)
    (b1-mismatch-let
      ((request (car leaves))
       ((step lib) (b1-mismatch-maximum-length-type-leaf (car request) lib)))
      (b1-mismatch-maximum-length-type-leaves
       lib (cdr leaves) (table-put replies request step)))))

(defun b1-mismatch-maximum-length-type (lib term)
  (b1-mismatch-let
    ((opened (library-inherited proof-proof-unfold lib term))
     (value (b1-mismatch-step-at opened 2))
     (leaves (library-inherited proof-proof-by-value-leaves lib value nil))
     ((replies lib) (b1-mismatch-maximum-length-type-leaves lib leaves nil))
     (fact (library-inherited proof-proof-by-value lib
                             value (list *library-natp* *proof-result*) replies nil)))
    (b1-mismatch-pair lib
      (library-library-transport-argument lib fact opened 1))))

(defun b1-mismatch-positive-maximum-length (lib term known)
  (b1-mismatch-let
    ((args (b1-mismatch-two-arguments term))
     (a (car args))
     (b (cadr args))
     (test (library-lt b a))
     (yes (library-inherited proof-proof-assume lib test t))
     (no (library-inherited proof-proof-assume lib test nil))
     (term-a (proof-term-at a 1))
     ((natural-a lib) (b1-bit-length-natural-bit-length lib term-a))
     (type-a (library-library-cite lib "NATURAL-INTEGER" (list a) (list natural-a)))
     (term-b (proof-term-at b 1))
     ((natural-b lib) (b1-bit-length-natural-bit-length lib term-b))
     (type-b (library-library-cite lib "NATURAL-INTEGER" (list b) (list natural-b)))
     (type-zero (library-library-type-of lib *proof-zero* nil))
     (known-value (b1-mismatch-step-at known 2))
     (known-a (equal known-value a))
     (left (if known-a
               known
             (library-library-cite lib "LESS-TRANSITIVE" (list *proof-zero* b a)
                                    (list type-zero type-b type-a known yes))))
     (right (if known-a
                (library-library-cite lib "LESS-THEN-WEAK" (list *proof-zero* a b)
                                      (list type-zero type-a type-b known no))
              known))
     (at-yes (b1-mismatch-normalize lib term :evidence (list yes) :unfold (list *b1-mismatch-max*)))
     (a-step (library-library-transport-argument lib left at-yes 2))
     (at-no (b1-mismatch-normalize lib term :evidence (list no) :unfold (list *b1-mismatch-max*)))
     (b-step (library-library-transport-argument lib right at-no 2)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-cases lib test a-step b-step))))

(defund b1-mismatch-immediate-nonnegative-bound-stuck (term stopped nonnegative lib)
  (b1-mismatch-let
    (((values lib) (b1-mismatch-zero-length-values lib term stopped))
     (zero (b1-mismatch-step-at values 1))
     (nonzero (library-inherited proof-proof-assume lib zero nil))
     (negative (library-inherited proof-proof-prove-if lib values nonzero))
     (sign (b1-mismatch-fixed-sign lib term))
     (reverse-sign (library-inherited proof-proof-symmetric lib sign))
     (fixed (library-inherited proof-proof-rewrite lib nonnegative reverse-sign '(1 1)))
     (fixed (library-inherited proof-proof-rewrite lib fixed negative '(1 1 1)))
     (fixed-literal (proof-step-first fixed))
     (opened (b1-mismatch-normalize lib fixed-literal :unfold (list *proof-not*)))
     (rewritten (library-inherited proof-proof-rewrite lib fixed opened '(1)))
     (absurd (library-inherited proof-proof-tidy lib rewritten))
     (assumption (library-inherited proof-proof-assume lib zero t))
     (no (library-inherited proof-proof-subsume lib absurd (cons zero (proof-step-clause absurd)))))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-cases lib zero assumption no))))

(defun b1-mismatch-immediate-nonnegative-bound-zero-values (lib terms stopped signs)
  (declare (xargs :measure (acl2-count terms)))
  (if (or (endp terms) (endp stopped) (endp signs))
      (cons nil lib)
    (b1-mismatch-let
      (((first lib)
        (b1-mismatch-immediate-nonnegative-bound-stuck
         (car terms) (car stopped) (car signs) lib))
       ((rest lib)
        (b1-mismatch-immediate-nonnegative-bound-zero-values
         lib (cdr terms) (cdr stopped) (cdr signs))))
      (cons (cons first rest) lib))))

(defun b1-mismatch-immediate-nonnegative-bound-longer (axis lib lengths tests maximum)
  (b1-mismatch-let
    ((size (proof-term-at lengths axis))
     (term (proof-term-at size 1))
     ((natural lib) (b1-bit-length-natural-bit-length lib term))
     (typed (library-library-cite lib "NATURAL-INTEGER" (list size) (list natural)))
     (test (proof-term-at tests axis))
     (negative (library-inherited proof-proof-assume lib test nil))
     (positive-size (b1-integer-no-zp lib size negative typed)))
    (b1-mismatch-positive-maximum-length lib maximum positive-size)))

(defun b1-mismatch-immediate-nonnegative-bound (lib recurrence maximum signs different)
  (b1-mismatch-let
    ((args (b1-mismatch-two-arguments (b1-mismatch-mismatch-induction-call recurrence)))
     (lengths (b1-mismatch-two-arguments maximum))
     (test-a (list *b1-logic-zp* (car lengths)))
     (test-b (list *b1-logic-zp* (cadr lengths)))
     (tests (list test-a test-b))
     (stopped-a (library-inherited proof-proof-assume lib test-a t))
     (stopped-b (library-inherited proof-proof-assume lib test-b t))
     ((zeros lib)
      (b1-mismatch-immediate-nonnegative-bound-zero-values
       lib args (list stopped-a stopped-b) signs))
     (zeros (proof-list-of-length zeros 2))
     (reverse-b (library-inherited proof-proof-symmetric lib (cadr zeros)))
     (equal-step (library-inherited proof-proof-chain lib (car zeros) (list reverse-b)))
     ((pair lib) (b1-mismatch-equality-from-bit-parts lib (car args) (cadr args)))
     (both (library-inherited proof-proof-rewrite lib equal-step pair '(1)))
     (conjuncts (library-inherited proof-proof-conjunct lib both))
     (impossible (b1-logic-bookproof-contradiction
                  lib (car conjuncts) different (library-positive maximum)))
     ((longer-b lib) (b1-mismatch-immediate-nonnegative-bound-longer 1 lib lengths tests maximum))
     (b-case (library-inherited proof-proof-cases lib test-b impossible longer-b))
     ((longer-a lib) (b1-mismatch-immediate-nonnegative-bound-longer 0 lib lengths tests maximum)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-cases lib test-a b-case longer-a))))

(defun b1-mismatch-mismatch-bound-extra-step (lib terms signs)
  (if (or (endp terms) (endp signs))
      (cons nil lib)
    (b1-mismatch-nonnegative-high-bits lib (car terms) (car signs))))

(defun b1-mismatch-mismatch-bound-extra-visit (terms signs result)
  (declare (xargs :measure (acl2-count terms)))
  (cond ((failure-p result) result)
        ((or (endp terms) (endp signs)) result)
        (t
         (b1-mismatch-let
           ((rest (b1-mismatch-mismatch-bound-extra-visit
                   (cdr terms) (cdr signs)
                   (b1-mismatch-mismatch-bound-extra-step (cdr result) (cdr terms) (cdr signs)))))
           (cons (cons (car result) (car rest)) (cdr rest))))))

(defun b1-mismatch-mismatch-bound-extra (lib terms signs)
  (b1-mismatch-mismatch-bound-extra-visit
   terms signs (b1-mismatch-mismatch-bound-extra-step lib terms signs)))

(defun b1-mismatch-mismatch-bound-consequence
    (premise lib strict recurrence call maximum low-match claim)
  (b1-mismatch-let
    ((fields (if strict
                 (b1-logic-bookproof-split-conjuncts lib premise)
               (list premise)))
     (last-field (1- (len fields)))
     (signs (take last-field fields))
     (found (proof-term-at fields last-field))
     ((first lib)
      (if strict
          (b1-mismatch-let
            ((different (library-inherited proof-proof-assume lib low-match nil))
             ((immediate lib)
              (b1-mismatch-immediate-nonnegative-bound lib recurrence maximum signs different))
             (initial (b1-mismatch-mismatch-induction-first
                       (b1-mismatch-mismatch-induction-with-lib recurrence lib))))
            (b1-mismatch-pair lib
              (library-library-transport-argument lib immediate initial 1)))
        (b1-mismatch-let
          (((maximum-type lib) (b1-mismatch-maximum-length-type lib maximum))
           (lower (library-library-cite lib "NATURAL-NONNEGATIVE" (list maximum)
                                       (list maximum-type)))
           (initial (b1-mismatch-mismatch-induction-first
                     (b1-mismatch-mismatch-induction-with-lib recurrence lib)))
           (reverse-initial (library-inherited proof-proof-symmetric lib initial)))
          (b1-mismatch-pair lib
            (library-inherited proof-proof-rewrite lib lower reverse-initial '(1 1 2))))))
     (recurrence (b1-mismatch-mismatch-induction-with-lib recurrence lib))
     (equal-step (library-inherited proof-proof-assume lib low-match t))
     (opened (b1-mismatch-mismatch-induction-matching recurrence equal-step))
     (opened-body (b1-mismatch-step-at opened 2))
     (if-true (library-inherited proof-proof-if-true lib opened-body))
     (ending (library-inherited proof-proof-chain lib opened (list if-true)))
     (found-ending (library-inherited proof-proof-rewrite lib found ending '(1)))
     (non-nil (library-inherited b1-logic-proof-not-nil lib))
     (base (b1-logic-bookproof-contradiction lib found-ending non-nil claim))
     (advanced (b1-mismatch-mismatch-induction-later recurrence opened))
     (advanced-body (b1-mismatch-step-at advanced 2))
     (if-false (library-inherited proof-proof-if-false lib advanced-body))
     (absent (library-inherited proof-proof-chain lib advanced (list if-false)))
     (found-absent (library-inherited proof-proof-rewrite lib found absent '(1)))
     (non-nil (library-inherited b1-logic-proof-not-nil lib))
     (none (b1-logic-bookproof-contradiction lib found-absent non-nil claim))
     (child (b1-mismatch-mismatch-induction-child recurrence))
     (have-child (library-inherited proof-proof-assume lib child t))
     ((hypothesis lib) (b1-mismatch-mismatch-induction-hypothesis recurrence))
     (call-args (b1-mismatch-term-arguments call))
     ((extra lib) (b1-mismatch-mismatch-bound-extra lib call-args signs))
     (hypothesis-test (b1-mismatch-step-at hypothesis 1))
     (guard (b1-mismatch-normalize-proof lib hypothesis-test :evidence (cons have-child extra)))
     (child-bound (library-inherited proof-proof-modus-ponens lib hypothesis guard))
     (child-comparison (if strict
                           (proof-step-first child-bound)
                         (b1-mismatch-step-at child-bound 1)))
     (child-max (proof-term-at child-comparison (if strict 2 1)))
     ((natural-index lib) (b1-mismatch-natural-mismatch lib child have-child))
     ((natural-max lib) (b1-mismatch-maximum-length-type lib child-max))
     (index-literal (b1-mismatch-step-at natural-index 1))
     (index-integer (library-library-cite lib "NATURAL-INTEGER" (list index-literal)
                                         (list natural-index)))
     (max-literal (b1-mismatch-step-at natural-max 1))
     (max-integer (library-library-cite lib "NATURAL-INTEGER" (list max-literal)
                                       (list natural-max)))
     (compared (b1-mismatch-two-arguments child-comparison))
     (increased (library-lt (library-plus *proof-one* (car compared))
                            (library-plus *proof-one* (cadr compared))))
     (sums (b1-arithmetic-number-sums-init lib))
     (lib (b1-arithmetic-number-sums-library sums))
     (alignment (b1-arithmetic-number-sums-comparison-equation
                 sums child-comparison increased (list index-integer max-integer)))
     ((max-falls lib) (b1-mismatch-maximum-decreases lib recurrence))
     (selected (library-inherited proof-proof-select lib advanced-body have-child))
     (stepped (library-inherited proof-proof-chain lib advanced (list selected)))
     (shifted (library-inherited proof-proof-rewrite lib child-bound alignment
                                (if strict '(1) '(1 1))))
     (reverse-falls (library-inherited proof-proof-symmetric lib max-falls))
     (shifted (library-inherited proof-proof-rewrite lib shifted reverse-falls
                                (if strict '(1 2) '(1 1 1))))
     (reverse-step (library-inherited proof-proof-symmetric lib stepped))
     (step (library-inherited proof-proof-rewrite lib shifted reverse-step
                             (if strict '(1 1) '(1 1 2))))
     (continue (library-inherited proof-proof-cases lib child step none))
     (stop-case (library-inherited proof-proof-cases lib
                                   (b1-mismatch-mismatch-induction-stopped recurrence)
                                   base continue)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-cases lib low-match stop-case first))))

(defun b1-mismatch-mismatch-bound (lib formula)
  (b1-mismatch-let
    ((parts (proof-list-of-length formula 3))
     (condition (cadr parts))
     (claim (caddr parts))
     (head (proof-term-at claim 0))
     (strict (not (equal head *proof-not*)))
     (call (if strict (b1-mismatch-at condition 2 2) condition))
     (recurrence (b1-mismatch-mismatch-induction-init lib call formula))
     (maximum (if strict (proof-term-at claim 2) (b1-mismatch-at claim 1 1)))
     (low-match (b1-mismatch-mismatch-induction-low-match recurrence))
     (premise (b1-logic-bookproof-prove-implication-premise lib formula))
     ((consequence lib)
      (b1-mismatch-mismatch-bound-consequence
       premise lib strict recurrence call maximum low-match claim))
     (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))
    (b1-mismatch-mismatch-induction-finish
     (b1-mismatch-mismatch-induction-with-lib recurrence lib) step)))

(defun b1-mismatch-floor-of-doubled-divisor-cancel (term types lib inv divisor inverse)
  (b1-mismatch-let
    ((numeric (b1-arithmetic-known-type lib *library-numberp* term types)))
    (b1-powers-multiply-inverse lib inv divisor term inverse numeric)))

(defun b1-mismatch-add-floor-of-doubled-divisor (lib)
  (b1-mismatch-let
    ((x *library-x*)
     (d *library-y*)
     (int-x (library-inherited proof-proof-assume lib (library-integer x) t))
     (int-d (library-inherited proof-proof-assume lib (library-integer d) t))
     (pos-d (library-inherited proof-proof-assume lib (library-positive d) t))
     (int-two (library-library-type-of lib *b1-bits-two* nil))
     (pos-two (library-inherited proof-proof-prove lib
                                 (library-positive *b1-bits-two*) nil nil))
     (two (b1-modular-modulus-init lib int-two pos-two))
     (ring (b1-modular-modulus-init lib int-d pos-d))
     (doubled (b1-arithmetic-product *b1-bits-two* d))
     (int-doubled (library-library-type-of lib doubled (list int-d)))
     (pos-doubled
      (b1-arithmetic-positive-product lib (b1-modular-modulus-positive two) pos-d (list int-d)))
     (total (b1-modular-modulus-init lib int-doubled pos-doubled))
     (half (b1-modular-modulus-floor two x))
     (half-ratio (b1-modular-modulus-ratio two x))
     (half-number (b1-modular-modulus-rational two x int-x))
     ((half-interval lib) (b1-floor-interval lib half half-number))
     (int-half (car half-interval))
     (lower-half (cadr half-interval))
     (upper-half (caddr half-interval))
     (q (b1-modular-modulus-floor ring half))
     (half-over-d (b1-modular-modulus-rational
                   (b1-modular-modulus-with-lib ring lib) half int-half))
     ((q-interval lib) (b1-floor-interval lib q half-over-d))
     (int-q (car q-interval))
     (lower-q (cadr q-interval))
     (upper-q (caddr q-interval))
     (successor (library-plus *proof-one* q))
     ((scaled-upper lib)
      (b1-arithmetic-multiply-strict lib pos-d upper-q (list int-d int-q half-over-d)))
     (scaled-half (b1-modular-modulus-scale-ratio
                   (b1-modular-modulus-with-lib ring lib) half int-half))
     (scaled-upper (library-inherited proof-proof-rewrite lib scaled-upper scaled-half '(1 1)))
     (bound (b1-arithmetic-product d successor))
     (int-bound (library-library-type-of lib bound (list int-d int-q)))
     ((weak-top lib) (b1-floor-advance-bound lib scaled-upper int-half int-bound))
     (sums (b1-arithmetic-number-sums-init lib))
     (lib (b1-arithmetic-number-sums-library sums))
     (upper (b1-floor-strict-then-weak lib sums upper-half weak-top
                                       (list int-half int-bound half-number)))
     (low-boundary (b1-arithmetic-product d q))
     (contrary-lower (library-inherited proof-proof-assume lib
                                       (library-lt half low-boundary) t))
     (inv (b1-arithmetic-reciprocal d))
     ((positive-inverse lib)
      (b1-modular-modulus-inverse-positive (b1-modular-modulus-with-lib ring lib)))
     (inverse-equation (b1-modular-modulus-inverse (b1-modular-modulus-with-lib ring lib) t))
     ((reduced lib)
      (b1-arithmetic-multiply-strict lib positive-inverse contrary-lower (list int-half int-d int-q)))
     (commute-inv (library-library-axiom lib "COMMUTATIVITY-OF-*" (list inv half)))
     (reduced (library-inherited proof-proof-rewrite lib reduced commute-inv '(1 1)))
     (cancel-q (b1-mismatch-floor-of-doubled-divisor-cancel
                q (list int-q) lib inv d inverse-equation))
     (reduced (library-inherited proof-proof-rewrite lib reduced cancel-q '(1 2)))
     (lower-cut (library-inherited proof-proof-cut lib reduced lower-q))
     (contrary (proof-step-first contrary-lower))
     (lower (library-inherited proof-proof-front lib lower-cut (proof-neg contrary)))
     (ratio (b1-modular-modulus-ratio total x))
     (ratio-number
      (b1-modular-modulus-rational (b1-modular-modulus-with-lib total lib) x int-x))
     (scaled (b1-arithmetic-product d ratio))
     (scale-total
      (b1-modular-modulus-scale-ratio (b1-modular-modulus-with-lib total lib) x int-x))
     (associate (library-library-axiom lib "ASSOCIATIVITY-OF-*" (list *b1-bits-two* d ratio)))
     (scale-total (library-inherited proof-proof-rewrite lib scale-total associate '(1 1)))
     (small-inverse (b1-arithmetic-reciprocal *b1-bits-two*))
     (total-left (b1-mismatch-step-at scale-total 1))
     (scale-reflexive (library-inherited proof-proof-reflexive lib
                                        (b1-arithmetic-product small-inverse total-left)))
     (scale-total (library-inherited proof-proof-rewrite lib scale-reflexive scale-total '(1 2 2)))
     (scaled-number (b1-arithmetic-known-type lib *library-numberp* scaled (list ratio-number int-d)))
     (two-inverse (b1-modular-modulus-inverse (b1-modular-modulus-with-lib two lib) t))
     (remove-two (b1-powers-multiply-inverse lib small-inverse *b1-bits-two*
                                             scaled two-inverse scaled-number))
     (reverse-two (library-inherited proof-proof-symmetric lib remove-two))
     (commute-x (library-library-axiom lib "COMMUTATIVITY-OF-*" (list small-inverse x)))
     (equation (library-inherited proof-proof-chain lib reverse-two (list scale-total commute-x)))
     (test (library-lt ratio q))
     (assumed-test (library-inherited proof-proof-assume lib test t))
     ((scaled-test lib)
      (b1-arithmetic-multiply-strict lib pos-d assumed-test (list int-d ratio-number int-q)))
     (scaled-test (library-inherited proof-proof-rewrite lib scaled-test equation '(1 1)))
     (sums (b1-arithmetic-number-sums-init lib))
     (lib (b1-arithmetic-number-sums-library sums))
     (boundary-type (library-library-type-of lib low-boundary (list int-d int-q)))
     (conflict (b1-floor-strict-then-weak lib sums scaled-test lower
                                          (list int-half boundary-type half-number)))
     (conflict-cut (library-inherited proof-proof-cut lib conflict lower-half))
     (final-lower (library-inherited proof-proof-front lib conflict-cut (proof-neg test)))
     ((final-upper lib)
      (b1-arithmetic-multiply-strict lib positive-inverse upper (list int-d half-number int-bound)))
     (reverse-equation (library-inherited proof-proof-symmetric lib equation))
     (final-upper (library-inherited proof-proof-rewrite lib final-upper reverse-equation '(1 1 2)))
     (cancel-ratio (b1-mismatch-floor-of-doubled-divisor-cancel
                    ratio (list ratio-number) lib inv d inverse-equation))
     (final-upper (library-inherited proof-proof-rewrite lib final-upper cancel-ratio '(1 1)))
     (cancel-successor (b1-mismatch-floor-of-doubled-divisor-cancel
                        successor (list int-q) lib inv d inverse-equation))
     (final-upper (library-inherited proof-proof-rewrite lib final-upper cancel-successor '(1 2)))
     (total-floor (b1-modular-modulus-floor total x))
     ((actual lib) (b1-floor-interval lib total-floor ratio-number))
     ((step lib)
      (b1-floor-equal-intervals lib actual (list int-q final-lower final-upper) ratio-number))
     (claim (proof-step-first step))
     (nx (proof-step-first int-x))
     (nd (proof-step-first int-d))
     (pd (proof-step-first pos-d)))
    (library-library-lemma lib "FLOOR-OF-DOUBLED-DIVISOR" claim step
                            (list (proof-neg nx) (proof-neg nd) (proof-neg pd)))))

(defun b1-mismatch-floor-of-doubled-divisor (lib integral divisor-type divisor-positive)
  (let ((name (proof-sym "SELF-FLOOR-OF-DOUBLED-DIVISOR" "ACL2")))
    (b1-mismatch-let
      ((lib (if (assoc-equal name (library-inherited proof-proof-facts lib))
                lib
              (b1-mismatch-add-floor-of-doubled-divisor lib)))
       (numerator (b1-mismatch-step-at integral 1))
       (divisor (b1-mismatch-step-at divisor-type 1)))
      (b1-mismatch-pair lib
        (library-inherited proof-proof-use lib name
                           (list (list *library-x* numerator) (list *library-y* divisor))
                           (list integral divisor-type divisor-positive))))))

(defun b1-mismatch-bit-at-successor (lib index-natural term)
  (b1-mismatch-let
    ((index (b1-mismatch-step-at index-natural 1))
     (next-index (library-plus *proof-one* index))
     (one-natural (library-library-natural lib *proof-one*))
     (next-natural (library-library-cite lib "NATURAL-SUM" (list *proof-one* index)
                                        (list one-natural index-natural)))
     (index-type (library-library-cite lib "NATURAL-INTEGER" (list index) (list index-natural)))
     (a (library-inherited proof-proof-unfold lib (list *b1-mismatch-logbitp* next-index term)))
     (next-nfix (b1-integer-nfix-identity lib next-natural))
     (a (library-inherited proof-proof-rewrite lib a next-nfix '(1 2 1 2 2)))
     (lib (b1-powers-build-recurrences lib))
     (two-number (b1-arithmetic-known-type lib *library-numberp* *b1-bits-two* nil))
     (two-nonzero (library-inherited proof-proof-prove lib
                                     (proof-neg (proof-eq *b1-bits-two* *proof-zero*))
                                     nil (list *proof-not*)))
     (power-step (library-library-cite lib "EXPT-STEP-UP" (list *b1-bits-two* index)
                                       (list index-type two-number two-nonzero)))
     (commutation (library-library-axiom lib "COMMUTATIVITY-OF-+" (list index *proof-one*)))
     (power-step (library-inherited proof-proof-rewrite lib power-step commutation '(1 1 2)))
     (a (library-inherited proof-proof-rewrite lib a power-step '(1 2 1 2)))
     (fixed (b1-bit-types-integer-fix lib (list *b1-quotient-ifix* term)))
     ((power-types lib) (b1-bit-types-positive-power-of-two lib index index-natural))
     ((quotient lib)
      (b1-mismatch-floor-of-doubled-divisor lib fixed (car power-types) (cadr power-types)))
     (a (library-inherited proof-proof-rewrite lib a quotient '(1 2 1)))
     (bits (b1-mismatch-normalized-bit-functions lib term))
     (high (cadr bits))
     (reverse-high (library-inherited proof-proof-symmetric lib high))
     (a (library-inherited proof-proof-rewrite lib a reverse-high '(1 2 1 1)))
     (high-term (b1-mismatch-step-at high 1))
     (b (library-inherited proof-proof-unfold lib (list *b1-mismatch-logbitp* index high-term)))
     (index-nfix (b1-integer-nfix-identity lib index-natural))
     (b (library-inherited proof-proof-rewrite lib b index-nfix '(1 2 1 2 2)))
     ((high-type lib)
      (b1-bit-types-numeric-type 1000000 lib *proof-integerp* high-term nil))
     (fixed-high (b1-mismatch-normalize lib (list *b1-quotient-ifix* high-term)
                                         :evidence (list high-type)
                                         :unfold (list *b1-quotient-ifix*)))
     (b (library-inherited proof-proof-rewrite lib b fixed-high '(1 2 1 1)))
     (reverse-b (library-inherited proof-proof-symmetric lib b)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-chain lib a (list reverse-b)))))

(defun b1-mismatch-bit-at-zero (lib term)
  (b1-mismatch-let
    ((fixed (list *b1-quotient-ifix* term))
     (int-fixed (b1-bit-types-integer-fix lib fixed))
     (odd (library-inherited proof-proof-unfold lib (list *b1-mismatch-logbitp* *proof-zero* term)))
     (zero-natural (library-library-natural lib *proof-zero*))
     (zero-nfix (b1-integer-nfix-identity lib zero-natural))
     (odd (library-inherited proof-proof-rewrite lib odd zero-nfix '(1 2 1 2 2)))
     (expt-zero (b1-powers-expt-zero lib *b1-bits-two*))
     (odd (library-inherited proof-proof-rewrite lib odd expt-zero '(1 2 1 2)))
     (floor (b1-mismatch-step-at odd 2 1))
     (int-one (library-library-type-of lib *proof-one* nil))
     (pos-one (library-inherited proof-proof-prove lib (library-positive *proof-one*) nil nil))
     (one (b1-modular-modulus-init lib int-one pos-one))
     (rational (b1-modular-modulus-rational one fixed int-fixed))
     ((actual lib) (b1-floor-interval lib floor rational))
     (ratio (b1-mismatch-normalize lib (b1-modular-modulus-ratio one fixed)))
     (times-one (b1-arithmetic-multiply-one lib fixed (list int-fixed) nil))
     (ratio (library-inherited proof-proof-chain lib ratio (list times-one)))
     (sums (b1-arithmetic-number-sums-init lib))
     (lib (b1-arithmetic-number-sums-library sums))
     (zero-zero (library-lt *proof-zero* *proof-zero*))
     (zero-one (library-lt *proof-zero* *proof-one*))
     (lower (b1-arithmetic-number-sums-comparison-equation
             sums (library-lt fixed fixed) zero-zero (list int-fixed)))
     (upper (b1-arithmetic-number-sums-comparison-equation
             sums (library-lt fixed (library-plus *proof-one* fixed)) zero-one (list int-fixed)))
     (no-less (library-inherited proof-proof-prove lib (proof-neg zero-zero) nil (list *proof-not*)))
     (reverse-lower (library-inherited proof-proof-symmetric lib lower))
     (low (library-inherited proof-proof-rewrite lib no-less reverse-lower '(1 1)))
     (less (library-inherited proof-proof-prove lib zero-one nil nil))
     (high (library-inherited proof-proof-transport lib less upper))
     (reverse-ratio (library-inherited proof-proof-symmetric lib ratio))
     (low (library-inherited proof-proof-rewrite lib low reverse-ratio '(1 1 1)))
     (reverse-ratio (library-inherited proof-proof-symmetric lib ratio))
     (high (library-inherited proof-proof-rewrite lib high reverse-ratio '(1 1)))
     ((quotient lib) (b1-floor-equal-intervals lib actual (list int-fixed low high) rational))
     (odd (library-inherited proof-proof-rewrite lib odd quotient '(1 2 1)))
     (odd-body (b1-mismatch-step-at odd 2))
     (opened (library-inherited proof-proof-unfold lib odd-body))
     (odd (library-inherited proof-proof-chain lib odd (list opened)))
     (bits (b1-mismatch-normalized-bit-functions lib term))
     ((mod-two lib) (b1-bit-types-mod-two-equation lib int-fixed))
     (low-bit (library-inherited proof-proof-chain lib (car bits) (list mod-two))))
    (cons (list odd low-bit) lib)))

(defun b1-mismatch-mismatch-correct-test-parity (lib tested axis equation parity)
  (b1-mismatch-let
    ((body (b1-mismatch-step-at equation 2))
     (value (b1-mismatch-normalize lib body :evidence (list parity) :unfold (list *proof-not*)))
     (answer (library-inherited proof-proof-chain lib equation (list value))))
    (library-inherited proof-proof-rewrite lib tested answer (list 1 2 1 axis))))

(defun b1-mismatch-mismatch-correct-with-parity
    (x y lib current x-bit y-bit claim zero-goal x-odd y-odd)
  (b1-mismatch-let
    ((low (b1-mismatch-normalize lib current :evidence (list x y)
                                 :rules (b1-mismatch-equality-rules (list x-bit y-bit))))
     (value (b1-mismatch-step-at low 2)))
    (if (not (equal value *proof-false*))
        (b1-mismatch-let
          ((different (library-inherited proof-proof-assume lib current nil))
           (parity (library-inherited proof-proof-rewrite lib different low '(1 1)))
           (literal (proof-step-first parity))
           (normal (b1-mismatch-normalize lib literal :unfold (list *proof-not*)))
           (parity (library-inherited proof-proof-rewrite lib parity normal '(1)))
           (non-nil (library-inherited b1-logic-proof-not-nil lib)))
          (b1-logic-bookproof-contradiction lib parity non-nil claim))
      (b1-mismatch-let
        ((tested (b1-mismatch-mismatch-correct-test-parity lib zero-goal 1 x-odd x))
         (tested (b1-mismatch-mismatch-correct-test-parity lib tested 2 y-odd y))
         (target (b1-mismatch-step-at tested 2))
         (reduced (b1-mismatch-normalize lib target :unfold (list *proof-not*)))
         (truth (library-inherited proof-proof-prove lib *proof-true* nil nil))
         (chain (library-inherited proof-proof-chain lib tested (list reduced))))
        (library-inherited proof-proof-transport lib truth chain)))))

(defun b1-mismatch-mismatch-correct-test-y
    (x lib even-y current x-bit y-bit claim zero-goal x-odd y-odd)
  (b1-mismatch-let
    ((holds (library-inherited proof-proof-assume lib even-y t))
     (yes (b1-mismatch-mismatch-correct-with-parity
           x holds lib current x-bit y-bit claim zero-goal x-odd y-odd))
     (fails (library-inherited proof-proof-assume lib even-y nil))
     (no (b1-mismatch-mismatch-correct-with-parity
          x fails lib current x-bit y-bit claim zero-goal x-odd y-odd)))
    (library-inherited proof-proof-cases lib even-y yes no)))

(defun b1-mismatch-mismatch-correct-successor (lib axis term bound child-natural)
  (b1-mismatch-let
    (((position lib) (b1-mismatch-bit-at-successor lib child-natural term))
     (reverse-position (library-inherited proof-proof-symmetric lib position)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-rewrite lib bound reverse-position (list 1 1 axis)))))

(defun b1-mismatch-mismatch-correct-successors (axis terms result child-natural)
  (declare (xargs :measure (acl2-count terms)))
  (cond ((failure-p result) result)
        ((endp terms) result)
        (t
         (b1-mismatch-mismatch-correct-successors
          (1+ axis) (cdr terms)
          (b1-mismatch-mismatch-correct-successor
           (cdr result) axis (car terms) (car result) child-natural)
          child-natural))))

(defun b1-mismatch-mismatch-correct-lift-axis (lib claim lifted axis)
  (b1-mismatch-let
    ((reverse-lifted (library-inherited proof-proof-symmetric lib lifted)))
    (library-inherited proof-proof-rewrite lib claim reverse-lifted (list 1 1 axis 1))))

(defun b1-mismatch-mismatch-correct-lift (lib claim lifted axes)
  (declare (xargs :measure (acl2-count axes)))
  (if (or (failure-p claim) (endp axes))
      claim
    (b1-mismatch-mismatch-correct-lift
     lib (b1-mismatch-mismatch-correct-lift-axis lib claim lifted (car axes))
     lifted (cdr axes))))

(defun b1-mismatch-mismatch-correct-consequence (premise lib claim a b recurrence current)
  (b1-mismatch-let
    ((zero (b1-mismatch-mismatch-induction-first recurrence))
     (reflexive (library-inherited proof-proof-reflexive lib claim))
     (zero-goal (library-inherited proof-proof-rewrite lib reflexive zero '(1 2 1 1 1)))
     (zero-goal (library-inherited proof-proof-rewrite lib zero-goal zero '(1 2 1 2 1)))
     ((x-pair lib) (b1-mismatch-bit-at-zero lib a))
     ((y-pair lib) (b1-mismatch-bit-at-zero lib b))
     (x-odd (car x-pair))
     (x-bit (cadr x-pair))
     (y-odd (car y-pair))
     (y-bit (cadr y-pair))
     (even-x (b1-mismatch-step-at x-odd 2 1))
     (even-y (b1-mismatch-step-at y-odd 2 1))
     (x-yes (library-inherited proof-proof-assume lib even-x t))
     (yes (b1-mismatch-mismatch-correct-test-y
           x-yes lib even-y current x-bit y-bit claim zero-goal x-odd y-odd))
     (x-no (library-inherited proof-proof-assume lib even-x nil))
     (no (b1-mismatch-mismatch-correct-test-y
          x-no lib even-y current x-bit y-bit claim zero-goal x-odd y-odd))
     (first (library-inherited proof-proof-cases lib even-x yes no))
     (recurrence (b1-mismatch-mismatch-induction-with-lib recurrence lib))
     (low-equal (library-inherited proof-proof-assume lib current t))
     (opened (b1-mismatch-mismatch-induction-matching recurrence low-equal))
     (opened-body (b1-mismatch-step-at opened 2))
     (if-true (library-inherited proof-proof-if-true lib opened-body))
     (finished (library-inherited proof-proof-chain lib opened (list if-true)))
     (finished-premise (library-inherited proof-proof-rewrite lib premise finished '(1)))
     (non-nil (library-inherited b1-logic-proof-not-nil lib))
     (base (b1-logic-bookproof-contradiction lib finished-premise non-nil claim))
     (later (b1-mismatch-mismatch-induction-later recurrence opened))
     (later-body (b1-mismatch-step-at later 2))
     (if-false (library-inherited proof-proof-if-false lib later-body))
     (absent (library-inherited proof-proof-chain lib later (list if-false)))
     (absent-premise (library-inherited proof-proof-rewrite lib premise absent '(1)))
     (non-nil (library-inherited b1-logic-proof-not-nil lib))
     (none (b1-logic-bookproof-contradiction lib absent-premise non-nil claim))
     (child (b1-mismatch-mismatch-induction-child recurrence))
     (have-child (library-inherited proof-proof-assume lib child t))
     ((child-natural lib) (b1-mismatch-natural-mismatch lib child have-child))
     ((hypothesis lib)
      (b1-mismatch-mismatch-induction-hypothesis
       (b1-mismatch-mismatch-induction-with-lib recurrence lib)))
     (claim-child (library-inherited proof-proof-modus-ponens lib hypothesis have-child))
     ((claim-child lib)
      (b1-mismatch-mismatch-correct-successors 1 (list a b) (cons claim-child lib) child-natural))
     (selected (library-inherited proof-proof-select lib later-body have-child))
     (lifted (library-inherited proof-proof-chain lib later (list selected)))
     (claim-child (b1-mismatch-mismatch-correct-lift lib claim-child lifted '(1 2)))
     (remaining (library-inherited proof-proof-cases lib child claim-child none))
     (stopped (b1-mismatch-mismatch-induction-stopped recurrence))
     (stop-case (library-inherited proof-proof-cases lib stopped base remaining)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-cases lib current stop-case first))))

(defun b1-mismatch-mismatch-correct (lib formula)
  (b1-mismatch-let
    ((parts (proof-list-of-length formula 3))
     (call (cadr parts))
     (claim (caddr parts))
     (args (b1-mismatch-two-arguments call))
     (recurrence (b1-mismatch-mismatch-induction-init lib call formula))
     (current (b1-mismatch-mismatch-induction-low-match recurrence))
     (premise (b1-logic-bookproof-prove-implication-premise lib formula))
     ((consequence lib)
      (b1-mismatch-mismatch-correct-consequence
       premise lib claim (car args) (cadr args) recurrence current))
     (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))
    (b1-mismatch-mismatch-induction-finish
     (b1-mismatch-mismatch-induction-with-lib recurrence lib) step)))

(defun b1-mismatch-fixed-values (terms)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      nil
    (b1-mismatch-let
      ((value (proof-term-at (car terms) 1))
       (rest (b1-mismatch-fixed-values (cdr terms))))
      (cons value rest))))

(defun b1-mismatch-fixed-arguments (term)
  (b1-mismatch-let
    ((args (b1-mismatch-term-arguments term))
     (values (b1-mismatch-fixed-values (take (min 3 (len args)) args))))
    (proof-list-of-length values 2)))

(defun b1-mismatch-equal-fixed-by-bits-consequence
    (premise lib goal call smaller bits-equal same-bit agreement)
  (b1-mismatch-let
    ((different (library-inherited proof-proof-assume lib goal nil))
     (exists (b1-logic-bookproof-from-fact
              lib (proof-sym "LOGBITP-MISMATCH-UNDER-IFF" "BITOPS")
              (list *b1-revappend-iff* call (proof-neg goal))))
     (found (b1-logic-bookproof-forces lib call exists (list different)
                                      (list *b1-revappend-iff*) nil))
     ((proper-index lib) (b1-mismatch-natural-mismatch lib call found))
     (within (b1-logic-bookproof-from-fact
              lib (proof-sym "LOGBITP-MISMATCH-UPPER-BOUND" "BITOPS")
              (list *library-implies* call smaller)))
     (bound (library-inherited proof-proof-modus-ponens lib within found))
     (same-bit-test (proof-term-at same-bit 1))
     (known (b1-mismatch-normalize-proof lib same-bit-test
                                        :evidence (list premise proper-index bound)))
     (agreement (b1-logic-bookproof-from-fact lib agreement same-bit))
     (equal-step (library-inherited proof-proof-modus-ponens lib agreement known))
     (mismatch (b1-logic-bookproof-from-fact
                lib (proof-sym "LOGBITP-MISMATCH-CORRECT" "ACL2")
                (list *library-implies* call (proof-neg bits-equal))))
     (unequal (library-inherited proof-proof-modus-ponens lib mismatch found))
     (cut (library-inherited proof-proof-cut lib equal-step unequal)))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-front lib cut goal))))

(defun b1-mismatch-equal-fixed-by-bits-with-index (lib formula index)
  (b1-mismatch-let
    ((parts (proof-list-of-length formula 3))
     (test (cadr parts))
     (goal (caddr parts))
     (args (b1-mismatch-fixed-arguments goal))
     (a (car args))
     (b (cadr args))
     (call (list *b1-mismatch-mismatch* a b))
     (maximum (list *b1-mismatch-max* (list *b1-bit-length-length* a)
                                     (list *b1-bit-length-length* b)))
     (smaller (proof-neg (library-lt maximum call)))
     (bits-equal (proof-eq (list *b1-mismatch-logbitp* call a)
                           (list *b1-mismatch-logbitp* call b)))
     (same-bit (list *library-implies*
                     (proof-ite test (proof-ite (list *library-natp* call) smaller *proof-false*)
                                *proof-false*)
                     bits-equal))
     (agreement (b1-logic-matching-claim (b1-search-fact-index-claims index) same-bit)))
    (if (not agreement)
        '(:failure "Unproved" "")
      (b1-mismatch-let
        ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
         ((consequence lib)
          (b1-mismatch-equal-fixed-by-bits-consequence premise lib goal call smaller
                                                     bits-equal same-bit agreement)))
        (b1-mismatch-pair lib
          (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))))))

(defun b1-mismatch-equal-fixed-by-bits (lib formula)
  (b1-mismatch-equal-fixed-by-bits-with-index lib formula nil))

(defun b1-mismatch-mismatch-wrapped-index-consequence
    (premise lib a b assumption call goal index)
  (b1-mismatch-let
    ((exists (b1-logic-bookproof-from-fact
              lib (proof-sym "LOGBITP-MISMATCH-UNDER-IFF" "BITOPS")
              (list *b1-revappend-iff* call assumption)))
     (found (b1-logic-bookproof-forces lib call exists (list premise)
                                      (list *b1-revappend-iff*) nil))
     ((index-type lib) (b1-mismatch-natural-mismatch lib call found))
     (head (proof-term-at index 0))
     (opened (b1-mismatch-normalize lib index :unfold (list head)))
     (identity (b1-integer-nfix-identity lib index-type))
     (exposed (library-inherited proof-proof-chain lib opened (list identity)))
     (raw (proof-eq (list *b1-mismatch-logbitp* call a)
                     (list *b1-mismatch-logbitp* call b)))
     (correctness (b1-logic-bookproof-from-fact
                   lib (proof-sym "LOGBITP-MISMATCH-CORRECT" "ACL2")
                   (list *library-implies* call (proof-neg raw))))
     (failure (library-inherited proof-proof-modus-ponens lib correctness found))
     (failure (b1-mismatch-mismatch-correct-lift lib failure exposed '(1 2))))
    (b1-mismatch-pair lib
      (library-inherited proof-proof-transport lib failure goal))))

(defun b1-mismatch-mismatch-wrapped-index (lib formula)
  (b1-mismatch-let
    ((parts (proof-list-of-length formula 3))
     (assumption (cadr parts))
     (conclusion (caddr parts))
     (assumption-parts (proof-list-of-length assumption 2))
     (args (b1-mismatch-fixed-arguments (cadr assumption-parts)))
     (a (car args))
     (b (cadr args))
     (call (list *b1-mismatch-mismatch* a b))
     (goal (b1-mismatch-normalize lib conclusion))
     (index (b1-mismatch-step-at goal 2 1 1 1))
     (premise (b1-logic-bookproof-prove-implication-premise lib formula))
     ((consequence lib)
      (b1-mismatch-mismatch-wrapped-index-consequence
       premise lib a b assumption call goal index)))
    (b1-mismatch-pair lib
      (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))))
