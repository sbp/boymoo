(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-fixer-laws-bitp* (proof-sym "BITP" "ACL2"))
(defconst *b1-fixer-laws-posp* (proof-sym "POSP" "ACL2"))
(defconst *b1-fixer-laws-booleanp* (proof-sym "BOOLEANP" "ACL2"))
(defconst *b1-fixer-laws-char-code* (proof-cl "CHAR-CODE"))
(defconst *b1-fixer-laws-code-char* (proof-cl "CODE-CHAR"))
(defconst *b1-fixer-laws-list* (proof-quote (proof-cl "LIST")))

(defun b1-fixer-laws-step-term (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b1-fixer-laws-unpack-slice (term start stop size)
  (if (integerp term)
      '(:failure "failure" "")
    (proof-list-of-length (seq-slice term start stop) size)))

(defun b1-fixer-laws-bit-fix-identity-consequence
    (premise lib bit no test kept value functions)
  (let* ((proof (library-library-proof lib))
         (zero (proof-eq bit *proof-zero*)))
    (proof-with-checked-results
        ((missing (proof-proof-assume proof zero nil))
         (non-one (b1-logic-bookproof-false-value lib no))
         (non-zero (b1-logic-bookproof-false-value lib missing))
         (term (proof-step-first premise))
         (reduced (b1-logic-bookproof-normalize
                   lib term (list no missing)
                   (list *b1-fixer-laws-bitp* *b1-logic-eql* *b1-logic-eq*)
                   (list (b1-logic-equal-to non-one) (b1-logic-equal-to non-zero))
                   nil nil nil))
         (impossible (proof-proof-rewrite proof premise reduced '(1)))
         (not-nil (b1-logic-proof-not-nil proof))
         (cut (proof-proof-cut proof impossible not-nil))
         (at-zero (proof-proof-front proof cut zero))
         (zero-case (b1-logic-bookproof-normalize
                      lib value (list no) functions nil nil nil nil))
         (reverse-zero (proof-proof-symmetric proof at-zero))
         (otherwise (proof-proof-chain proof zero-case (list reverse-zero))))
      (proof-proof-cases proof test kept otherwise))))

(defun b1-fixer-laws-bit-fix-identity (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (claim (proof-list-of-length (caddr parts) 3)))
      (let* ((value (cadr claim))
             (bit (caddr claim))
             (test (proof-eq bit *proof-one*)))
        (proof-with-checked-results
            ((yes (proof-proof-assume proof test t))
             (no (proof-proof-assume proof test nil))
             (fixer (proof-term-at value 0)))
          (let ((functions (list fixer *b1-logic-eql* *b1-logic-eq*)))
            (proof-with-checked-results
                ((chosen (b1-logic-bookproof-normalize
                           lib value (list yes) functions nil nil nil nil))
                 (reverse-yes (proof-proof-symmetric proof yes))
                 (kept (proof-proof-chain proof chosen (list reverse-yes)))
                 (premise (b1-logic-bookproof-prove-implication-premise lib formula))
                 (consequence (b1-fixer-laws-bit-fix-identity-consequence
                               premise lib bit no test kept value functions)))
              (b1-logic-bookproof-prove-implication-with-premise
               lib formula premise consequence))))))))

(defun b1-fixer-laws-maybe-recognizer (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
      (let ((call (cadr parts))
            (claim (caddr parts)))
        (if (proof-is-call formula *library-implies*)
            (proof-with-checked-results
                ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
                 (opened (proof-proof-unfold proof call))
                 (consequence (proof-proof-rewrite proof premise opened '(1))))
              (b1-logic-bookproof-prove-implication-with-premise
               lib formula premise consequence))
          (proof-with-checked-results
              ((item (proof-term-at call 1))
               (have (proof-proof-assume proof item t))
               (missing (proof-proof-assume proof item nil))
               (null-value (b1-logic-bookproof-false-value lib missing))
               (recognizer (proof-term-at call 0)))
            (let ((functions (list recognizer *b1-fixer-laws-posp* *proof-not*)))
              (proof-with-checked-results
                  ((before (b1-logic-bookproof-normalize
                             lib call (list have) functions nil nil nil t))
                   (test (b1-fixer-laws-step-term before 2))
                   (present (proof-proof-assume proof test t))
                   (absent (proof-proof-assume proof test nil))
                   (selected-present (proof-proof-select proof claim present))
                   (reverse-present (proof-proof-symmetric proof selected-present))
                   (good (proof-proof-chain proof before (list reverse-present)))
                   (absent-value (b1-logic-bookproof-false-value lib absent))
                   (left (proof-proof-chain proof before (list absent-value)))
                   (selected-absent (proof-proof-select proof claim absent))
                   (negative-branch (proof-term-at claim 3))
                   (reduced (b1-logic-bookproof-normalize
                              lib negative-branch (list have) (list *proof-not*)
                              nil nil nil nil))
                   (right (proof-proof-chain proof selected-absent (list reduced)))
                   (reverse-right (proof-proof-symmetric proof right))
                   (bad (proof-proof-chain proof left (list reverse-right)))
                   (yes (proof-proof-cases proof test good bad))
                   (no (b1-logic-bookproof-case-proof
                        lib formula (list missing) functions
                        (list (b1-logic-equal-to null-value)) 16)))
                (proof-proof-cases proof item yes no)))))))))

(defun b1-fixer-laws-equality-equivalence-view (call lib)
  (proof-with-checked-results ((head (proof-term-at call 0)))
    (b1-logic-bookproof-normalize
     lib call nil (list head *b1-logic-eql* *b1-logic-eq*) nil nil nil nil)))

(defun b1-fixer-laws-equality-equivalence-to-equal (step lib)
  (proof-with-checked-results
      ((term (proof-step-first step))
       (view (b1-fixer-laws-equality-equivalence-view term lib)))
    (proof-proof-rewrite (library-library-proof lib) step view '(1))))

(defun b1-fixer-laws-equality-equivalence-compose (premise lib transitive)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((conjuncts (proof-proof-conjunct proof premise))
         (left (b1-fixer-laws-equality-equivalence-to-equal (car conjuncts) lib))
         (right (b1-fixer-laws-equality-equivalence-to-equal (cadr conjuncts) lib))
         (chain (proof-proof-chain proof left (list right)))
         (claim (proof-term-at transitive 2))
         (view (b1-fixer-laws-equality-equivalence-view claim lib)))
      (proof-proof-transport proof chain view))))

(defun b1-fixer-laws-equality-equivalence (lib formula)
  (let ((proof (library-library-proof lib))
        (functions (list *b1-fixer-laws-booleanp* *b1-logic-eq*)))
    (proof-with-checked-results
        ((outer (b1-fixer-laws-unpack-slice formula 1 3 2))
         (clauses (b1-fixer-laws-unpack-slice (cadr outer) 1 3 2))
         (remaining (b1-fixer-laws-unpack-slice (cadr clauses) 1 3 2))
         (boolean-call (proof-term-at (car outer) 1))
         (tested (b1-fixer-laws-equality-equivalence-view boolean-call lib))
         (condition (b1-fixer-laws-step-term tested 2))
         (present (proof-proof-assume proof condition t))
         (true-value (b1-logic-bookproof-equality-true lib present))
         (absent (proof-proof-assume proof condition nil))
         (false-value (b1-logic-bookproof-false-value lib absent))
         (yes (b1-logic-bookproof-normalize-proof
               lib (car outer) nil functions
               (list (b1-logic-equal-to tested) (b1-logic-equal-to true-value)) nil))
         (no (b1-logic-bookproof-normalize-proof
              lib (car outer) nil functions
              (list (b1-logic-equal-to tested) (b1-logic-equal-to false-value)) nil))
         (typed (proof-proof-cases proof condition yes no))
         (reflexive-view (b1-fixer-laws-equality-equivalence-view (car clauses) lib))
         (diagonal (b1-logic-bookproof-normalize-proof
                    lib (car clauses) nil nil (list (b1-logic-equal-to reflexive-view)) nil))
         (symmetric (car remaining))
         (premise (b1-logic-bookproof-prove-implication-premise lib symmetric))
         (equal-premise (b1-fixer-laws-equality-equivalence-to-equal premise lib))
         (reversed (proof-proof-symmetric proof equal-premise))
         (symmetric-claim (proof-term-at symmetric 2))
         (symmetric-view (b1-fixer-laws-equality-equivalence-view symmetric-claim lib))
         (symmetric-step (proof-proof-transport proof reversed symmetric-view))
         (symm (b1-logic-bookproof-prove-implication-with-premise
                lib symmetric premise symmetric-step))
         (transitive (cadr remaining))
         (premise (b1-logic-bookproof-prove-implication-premise lib transitive))
         (composed (b1-fixer-laws-equality-equivalence-compose premise lib transitive))
         (trans (b1-logic-bookproof-prove-implication-with-premise
                 lib transitive premise composed)))
      (b1-logic-bookproof-normalize-proof
       lib formula (list typed diagonal symm trans) nil nil nil))))

(defun b1-fixer-laws-fixed-character-code-branch (evidence lib changed fixed fix)
  (proof-with-checked-results
      ((normalized (b1-logic-bookproof-normalize
                    lib fixed (list evidence) (list fix) nil nil nil nil)))
    (b1-revappend-lift-argument lib changed normalized 1)))

(defun b1-fixer-laws-fixed-character-code (lib fixed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((parts (proof-list-of-length fixed 2)))
      (let* ((fix (car parts))
             (value (cadr parts))
             (test (list *b1-printing-characterp* value))
             (changed (list *b1-fixer-laws-char-code* fixed)))
        (proof-with-checked-results
            ((yes (proof-proof-assume proof test t))
             (no (proof-proof-assume proof test nil))
             (yes-branch (b1-fixer-laws-fixed-character-code-branch
                          yes lib changed fixed fix))
             (present (proof-proof-symmetric proof yes-branch))
             (absent (b1-fixer-laws-fixed-character-code-branch no lib changed fixed fix))
             (code-zero (proof-proof-compute
                         proof (list *b1-fixer-laws-code-char* *proof-zero*) '("char" 0)))
             (absent (proof-proof-rewrite proof absent code-zero '(1 2 1)))
             (term (b1-fixer-laws-step-term absent 2))
             (computed (proof-proof-compute proof term 0))
             (absent (proof-proof-chain proof absent (list computed)))
             (opened (library-library-axiom lib "COMPLETION-OF-CHAR-CODE" (list value)))
             (body (b1-fixer-laws-step-term opened 2))
             (selected (proof-proof-select proof body no))
             (empty (proof-proof-chain proof opened (list selected)))
             (reversed (proof-proof-symmetric proof absent))
             (otherwise (proof-proof-chain proof empty (list reversed))))
          (proof-proof-cases proof test present otherwise))))))

(defun b1-fixer-laws-fixed-string-characters-branch (evidence lib changed fixed fix)
  (proof-with-checked-results
      ((normalized (b1-logic-bookproof-normalize
                    lib fixed (list evidence) (list fix) nil nil nil nil)))
    (b1-revappend-lift-argument lib changed normalized 1)))

(defun b1-fixer-laws-fixed-string-characters (lib fixed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((parts (proof-list-of-length fixed 2)))
      (let* ((fix (car parts))
             (value (cadr parts))
             (test (list *b1-logic-stringp* value))
             (changed (list *b1-printing-coerce* fixed *b1-fixer-laws-list*)))
        (proof-with-checked-results
            ((yes (proof-proof-assume proof test t))
             (no (proof-proof-assume proof test nil))
             (opened (library-library-axiom
                      lib "COMPLETION-OF-COERCE" (list value *b1-fixer-laws-list*)))
             (body (b1-fixer-laws-step-term opened 2))
             (reduced (b1-logic-bookproof-normalize
                       lib body (list no) nil nil nil nil nil))
             (empty (proof-proof-chain proof opened (list reduced)))
             (yes-branch (b1-fixer-laws-fixed-string-characters-branch
                          yes lib changed fixed fix))
             (unchanged (proof-proof-symmetric proof yes-branch))
             (absent (b1-fixer-laws-fixed-string-characters-branch no lib changed fixed fix))
             (term (b1-fixer-laws-step-term absent 2))
             (computed (proof-proof-compute proof term *proof-nil*))
             (absent (proof-proof-chain proof absent (list computed)))
             (reversed (proof-proof-symmetric proof absent))
             (otherwise (proof-proof-chain proof empty (list reversed))))
          (proof-proof-cases proof test unchanged otherwise))))))

(defun b1-fixer-laws-character-fixer-p (fixed)
  (proof-with-checked-results
      ((head (proof-term-at fixed 0))
       (name (proof-term-at head 2)))
    (cond ((stringp name) (<= 0 (text-find name "CHAR-FIX")))
          ((integerp name) '(:failure "failure" ""))
          (t (if (member-equal "CHAR-FIX" name) t nil)))))

(defun b1-fixer-laws-fixed-congruence-consequence (premise lib opened claim)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equation (proof-proof-rewrite proof premise opened '(1)))
         (claim-sides (b1-fixer-laws-unpack-slice claim 1 :none 2))
         (literal (proof-step-first equation)))
      (if (equal literal claim)
          equation
        (proof-with-checked-results
            ((fixed (b1-fixer-laws-unpack-slice literal 1 :none 2))
             (characterp (b1-fixer-laws-character-fixer-p (car fixed)))
             (lhs (if characterp
                      (b1-fixer-laws-fixed-character-code lib (car fixed))
                    (b1-fixer-laws-fixed-string-characters lib (car fixed))))
             (rhs (if characterp
                      (b1-fixer-laws-fixed-character-code lib (cadr fixed))
                    (b1-fixer-laws-fixed-string-characters lib (cadr fixed))))
             (translated (proof-proof-rewrite proof lhs equation '(1 2 1)))
             (reverse-rhs (proof-proof-symmetric proof rhs))
             (translated (proof-proof-chain proof translated (list reverse-rhs)))
             (translated-claim (proof-step-first translated)))
          (if (equal translated-claim claim)
              translated
            (let ((left (car claim-sides))
                  (right (cadr claim-sides)))
              (proof-with-checked-results
                  ((left-head (proof-term-at left 0))
                   (lhs (b1-logic-bookproof-normalize
                         lib left nil (list left-head) (list (b1-logic-equal-to translated))
                         nil nil nil))
                   (right-head (proof-term-at right 0))
                   (rhs (b1-logic-bookproof-normalize
                         lib right nil (list right-head) nil nil nil nil))
                   (reverse-rhs (proof-proof-symmetric proof rhs)))
                (proof-proof-chain proof lhs (list reverse-rhs))))))))))

(defun b1-fixer-laws-fixed-congruence (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (guard-head (proof-term-at (cadr parts) 0))
       (opened (b1-logic-bookproof-normalize
                lib (cadr parts) nil (list guard-head *b1-logic-eql* *b1-logic-eq*)
                nil nil nil nil))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-fixer-laws-fixed-congruence-consequence
                     premise lib opened (caddr parts))))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))
