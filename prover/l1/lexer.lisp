(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *lexer-plain* (proof-sym "LEX-PLAIN" "BOYMOO"))
(defconst *lexer-quoted* (proof-sym "LEX-QUOTED" "BOYMOO"))
(defconst *lexer-part* (proof-sym "LEX-PART" "BOYMOO"))
(defconst *lexer-symbol-rest* (proof-sym "LEX-SYMBOL-REST" "BOYMOO"))
(defconst *lexer-sharp* (proof-sym "LEX-SHARP" "BOYMOO"))
(defconst *lexer-atom* (proof-sym "LEX-ATOM" "BOYMOO"))

; The first depth selects the output suffix. The second selects the input suffix.
(defconst *lexer-fields*
  (list (list *lexer-plain* 1 0)
        (list *lexer-quoted* 2 0)
        (list *lexer-part* 2 0)
        (list *lexer-symbol-rest* 1 2)
        (list *lexer-sharp* 1 0)
        (list *lexer-atom* 1 0)))

(defun lexer-tail (term n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      term
    (lexer-tail (list *library-cdr* term) (1- n))))

(defun lexer-length (term)
  (list *library-len* term))

(defun lexer-lexer-proofs-init (lib)
  (list :lexer-proofs lib nil))

(defun lexer-lexer-proofs-lib (lexer)
  (cadr lexer))

(defun lexer-lexer-proofs-induction (lexer)
  (caddr lexer))

(defun lexer-lexer-proofs-with-induction (lexer induction)
  (list :lexer-proofs (lexer-lexer-proofs-lib lexer) induction))

(defun lexer-lexer-proofs-with-lib (lexer lib)
  (list :lexer-proofs lib (lexer-lexer-proofs-induction lexer)))

(defun lexer-lexer-proofs-cite (lexer call suffix)
  (let ((proof (library-library-proof (lexer-lexer-proofs-lib lexer))))
    (if (endp call)
        '(:failure "unproved" "")
      (let* ((name (car call))
             (definition (assoc-equal name (proof-proof-definitions proof))))
        (if (not definition)
            '(:failure "failure" "")
          (proof-with-checked-results ((name-text (proof-term-at name 2)))
            (proof-proof-fact
             proof (proof-sym (concatenate 'string "SELF-" name-text suffix) "ACL2")
             (seq-zip (cadr definition) (cdr call)))))))))

(defun lexer-lexer-proofs-selector-rewrite (proof term inside)
  (proof-with-checked-results ((reflexive (proof-proof-reflexive proof term)))
    (proof-proof-rewrite proof reflexive inside '(1 2 1))))

(defun lexer-lexer-proofs-selectors-visit (n lib term)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "lexer-lexer-proofs-selectors-visit")
    (proof-with-checked-results ((head (proof-term-at term 0)))
      (if (not (member-equal head (list *library-car* *library-cdr*)))
          nil
        (proof-with-checked-results
            ((parts (proof-list-of-length term 2))
             (original (cadr parts))
             (inside (lexer-lexer-proofs-selectors-visit (1- n) lib original))
             (arg (if inside (proof-rewritten-term inside) original)))
          (let ((proof (library-library-proof lib)))
            (if (not (proof-is-call arg *proof-cons*))
                (and inside (lexer-lexer-proofs-selector-rewrite proof term inside))
              (proof-with-checked-results
                  ((selected (library-library-axiom
                              lib (if (equal head *library-car*) "CAR-CONS" "CDR-CONS")
                              (cdr arg)))
                   (selection (if inside
                                  (proof-with-checked-results
                                      ((rewritten (lexer-lexer-proofs-selector-rewrite
                                                   proof term inside)))
                                    (proof-proof-chain proof rewritten (list selected)))
                                selected))
                   (value (proof-rewritten-term selection))
                   (rest (lexer-lexer-proofs-selectors-visit (1- n) lib value)))
                (proof-proof-chain proof selection (list rest))))))))))

(defun lexer-lexer-proofs-selectors (lexer term)
  (lexer-lexer-proofs-selectors-visit 1000000 (lexer-lexer-proofs-lib lexer) term))

(defun lexer-lexer-proofs-replace-endpoint (lexer step equality lower)
  (let ((proof (library-library-proof (lexer-lexer-proofs-lib lexer))))
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (head (proof-term-at literal 0))
         (place (cond ((equal head *proof-less*) (list 1 (if lower 1 2) 1))
                      ((not (equal head *proof-not*)) '(:failure "failure" ""))
                      (t (proof-with-checked-results
                             ((comparison (proof-term-at literal 1))
                              (head (proof-term-at comparison 0)))
                           (if (equal head *proof-less*)
                               (list 1 1 (if lower 2 1) 1)
                             '(:failure "failure" ""))))))
         (rewritten (proof-proof-rewrite proof step equality place)))
      (proof-proof-tidy proof rewritten))))

(defun lexer-lexer-proofs-plain-test (lexer call hypotheses)
  (let ((proof (library-library-proof (lexer-lexer-proofs-lib lexer))))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof call))
         (body (proof-rewritten-term opened))
         (test (proof-term-at body 1))
         (evidence (descent-hypotheses-find hypotheses test)))
      (if (car evidence)
          evidence
        (proof-with-checked-results
            ((parts (proof-list-of-length (seq-slice test 1 3) 2))
             (cons-test (descent-hypotheses-find (cdr evidence) (car parts)))
             (plain (descent-hypotheses-find (cdr cons-test) (cadr parts))))
          (let ((hypotheses (cdr plain)))
            (if (and (car cons-test) (car plain))
                (proof-with-checked-results
                    ((step (proof-proof-prove proof test
                                              (list (car cons-test) (car plain)) nil)))
                  (cons step hypotheses))
              (proof-with-checked-results ((accumulated (proof-term-at call 2)))
                (if (not (equal accumulated *proof-false*))
                    (cons nil hypotheses)
                  (proof-with-checked-results
                      ((run (descent-hypotheses-find
                             hypotheses (list *proof-consp* (list *library-car* call)))))
                    (if (not (car run))
                        run
                      ; A plain scan with an empty accumulator must consume
                      ; a character to return a nonempty run.
                      (proof-with-checked-results
                          ((not-started (proof-proof-if-false proof body))
                           (empty (proof-proof-chain proof opened (list not-started)))
                           (run-proof (proof-proof-rewrite proof (car run) empty '(1 1 1)))
                           (literal (proof-step-first run-proof))
                           (argument (proof-term-at literal 1))
                           (projection (lexer-lexer-proofs-selectors lexer argument))
                           (projected (proof-proof-rewrite proof run-proof projection '(1 1)))
                           (literal (proof-step-first projected))
                           (computed (proof-proof-compute proof literal *proof-nil*))
                           (rewritten (proof-proof-rewrite proof projected computed '(1)))
                           (tidied (proof-proof-tidy proof rewritten))
                           (step (proof-proof-front proof tidied test)))
                        (cons step (cdr run))))))))))))))

(defun lexer-lexer-proofs-changed-bindings (formals actuals)
  (if (or (endp formals) (endp actuals))
      nil
    (if (equal (car formals) (car actuals))
        (lexer-lexer-proofs-changed-bindings (cdr formals) (cdr actuals))
      (cons (list (car formals) (car actuals))
            (lexer-lexer-proofs-changed-bindings (cdr formals) (cdr actuals))))))

(defun lexer-lexer-proofs-substitution (bindings subst)
  (if (endp bindings)
      subst
    (lexer-lexer-proofs-substitution
     (cdr bindings) (table-put subst (caar bindings) (cadar bindings)))))

(defun lexer-lexer-proofs-induction-step (lexer call hypotheses)
  (let* ((lib (lexer-lexer-proofs-lib lexer))
         (proof (library-library-proof lib))
         (induction (lexer-lexer-proofs-induction lexer))
         (formals (cadr induction))
         (formula (caddr induction))
         (measure (cadddr induction))
         (substitutions (nth 4 induction))
         (bindings (lexer-lexer-proofs-changed-bindings formals (cdr call)))
         (sub (lexer-lexer-proofs-substitution bindings nil))
         (lexer (if (member-equal bindings substitutions)
                    lexer
                  (lexer-lexer-proofs-with-induction
                   lexer (list (car induction) formals formula measure
                               (append substitutions (list bindings)))))))
    (proof-with-checked-results
        ((smaller-measure (proof-subst measure sub))
         (goal (list *proof-ordinal-less* smaller-measure measure))
         (direct (descent-direct-builtin lib (list goal) hypotheses))
         (smaller (if (car direct)
                      direct
                    (descent-selector-decrease lib goal (cdr direct))))
         (child-formula (proof-subst formula sub))
         (ih (proof-ite goal child-formula *proof-true*))
         (assumed (proof-proof-assume proof ih t))
         (step (proof-proof-prove-if proof assumed (car smaller))))
      (list step lexer (cdr smaller)))))

(defun lexer-lexer-proofs-lexed-suffix (lexer call hypotheses)
  (let ((proof (library-library-proof (lexer-lexer-proofs-lib lexer)))
        (induction (lexer-lexer-proofs-induction lexer)))
    (proof-with-checked-results
        ((head (proof-term-at call 0))
         (formula-proof
          (cond ((and induction (equal head (car induction)))
                 (lexer-lexer-proofs-induction-step lexer call hypotheses))
                ((equal head *lexer-plain*)
                 (proof-with-checked-results
                     ((started (lexer-lexer-proofs-plain-test lexer call hypotheses))
                      (step (if (car started)
                                (proof-with-checked-results
                                    ((strict (lexer-lexer-proofs-cite lexer call "-STRICT")))
                                  (proof-proof-discharge proof strict (car started)))
                              (lexer-lexer-proofs-cite lexer call "-UPPER"))))
                   (list step lexer (cdr started))))
                (t (proof-with-checked-results
                       ((strict (lexer-lexer-proofs-cite lexer call "-STRICT")))
                     (list strict lexer hypotheses))))))
      (if (equal head *lexer-plain*)
          formula-proof
        (proof-with-checked-results
            ((evidence (descent-hypotheses-require (caddr formula-proof) call))
             (step (proof-proof-modus-ponens proof (car formula-proof) (car evidence))))
          (list step (cadr formula-proof) (cdr evidence)))))))

(defun lexer-lexer-proofs-suffix-selection (selected depth)
  (declare (xargs :measure (acl2-count selected)))
  (if (and (proof-is-call selected *library-cdr*) (consp (cdr selected)))
      (lexer-lexer-proofs-suffix-selection (cadr selected) (1+ depth))
    (if (proof-is-call selected *library-cdr*)
        '(:failure "failure" "")
      (cons selected depth))))

(defun lexer-lexer-proofs-suffix-edge (lexer rest hypotheses)
  (let ((lib (lexer-lexer-proofs-lib lexer)))
    (proof-with-checked-results
        ((selection (lexer-lexer-proofs-suffix-selection rest 0))
         (selected (car selection))
         (depth (cdr selection))
         (fields (and (not (zp depth))
                      (proof-with-checked-results ((head (proof-term-at selected 0)))
                        (cdr (assoc-equal head *lexer-fields*))))))
      (cond
       ((and fields (equal (car fields) depth))
        (proof-with-checked-results
            ((input (proof-term-at selected 1))
             (parent (lexer-tail input (cadr fields)))
             (comparison (lexer-lexer-proofs-lexed-suffix lexer selected hypotheses))
             (lexer (cadr comparison))
             (equation (lexer-lexer-proofs-selectors lexer parent)))
          (if (not equation)
              (list (car comparison) parent lexer (caddr comparison))
            (proof-with-checked-results
                ((parent (proof-rewritten-term equation))
                 (step (lexer-lexer-proofs-replace-endpoint lexer (car comparison) equation nil)))
              (list step parent lexer (caddr comparison))))))
       ((proof-is-call rest *library-cdr*)
        (proof-with-checked-results
            ((parent (proof-term-at rest 1))
             (cons-proof (descent-hypotheses-require hypotheses (list *proof-consp* parent)))
             (step (library-library-cite lib "LEN-CDR-LESS" (list parent)
                                         (list (car cons-proof)))))
          (list step parent lexer (cdr cons-proof))))
       (t (proof-with-checked-results ((written (proof-write rest)))
            '(:failure "unproved" "")))))))

(defund lexer-lexer-proofs-link-edge (lexer current hypotheses step)
  (proof-with-checked-results
      ((edge (lexer-lexer-proofs-suffix-edge lexer current hypotheses))
       (bound (if step
                  (library-library-compare-chain (lexer-lexer-proofs-lib lexer) step (car edge))
                (car edge))))
    (cons bound (cdr edge))))

(defun lexer-lexer-proofs-relation-walk (n lexer current source hypotheses step seen)
  (declare (xargs :measure (nfix n)))
  (let ((lib (lexer-lexer-proofs-lib lexer)))
    (cond
     ((equal current source)
      (proof-with-checked-results
          ((bound (if step
                      step
                    (proof-with-checked-results
                        ((length-term (lexer-length source))
                         (integer-step (library-library-type-of lib length-term nil)))
                      (library-library-cite lib "WEAK-REFLEXIVE" (list length-term)
                                            (list integer-step))))))
        (list bound lexer hypotheses)))
     ((zp n) '(:failure "fuel" "lexer-lexer-proofs-relation-walk"))
     ((member-equal current seen)
      (proof-with-checked-results ((written (proof-write source)))
        '(:failure "unproved" "")))
     (t (proof-with-checked-results
            ((edge (lexer-lexer-proofs-link-edge lexer current hypotheses step)))
          (lexer-lexer-proofs-relation-walk (1- n) (caddr edge) (cadr edge) source
                                          (cadddr edge) (car edge) (cons current seen)))))))

(defun lexer-lexer-proofs-relation (lexer rest source hypotheses)
  (lexer-lexer-proofs-relation-walk 1000000 lexer rest source hypotheses nil nil))

(defun lexer-lexer-proofs-implication (lexer antecedent result)
  (let ((proof (library-library-proof (lexer-lexer-proofs-lib lexer))))
    (proof-with-checked-results
        ((literal (proof-step-first result))
         (formula (list *library-implies* antecedent literal))
         (unfolded (proof-proof-unfold proof formula))
         (unfolded-value (proof-rewritten-term unfolded))
         (true-branch (proof-proof-if-true proof unfolded-value))
         (yes (proof-proof-chain proof unfolded (list true-branch)))
         (yes-value (proof-rewritten-term yes))
         (chosen (proof-proof-select proof yes-value result))
         (yes (proof-proof-chain proof yes (list chosen)))
         (false-branch (proof-proof-if-false proof unfolded-value))
         (no (proof-proof-chain proof unfolded (list false-branch)))
         (yes-proof (proof-proof-true-from-eq proof yes))
         (no-proof (proof-proof-true-from-eq proof no)))
      (proof-proof-cases proof antecedent yes-proof no-proof))))

(defun lexer-lexer-proofs-result-branch (lexer function source value tests template)
  (let* ((lib (lexer-lexer-proofs-lib lexer))
         (proof (library-library-proof lib)))
    (if (equal value *proof-false*)
        (proof-with-checked-results
            ((goal (proof-subst template (list (cons *proof-result* value))))
             (step (proof-proof-prove proof goal nil (list *library-implies*))))
          (cons step lexer))
      (let ((weak (equal function *lexer-plain*))
            (fields (assoc-equal function *lexer-fields*)))
        (proof-with-checked-results
            ((nonempty (if weak nil (proof-proof-assume proof value t)))
             (hypotheses (descent-hypotheses-init
                          lib tests (if weak nil (list nonempty))))
             (rest (if fields
                       (lexer-tail value (cadr fields))
                     '(:failure "failure" "")))
             (equation (lexer-lexer-proofs-selectors lexer rest))
             (actual (if equation (proof-rewritten-term equation) rest))
             (bound (lexer-lexer-proofs-relation lexer actual source hypotheses))
             (lexer (cadr bound))
             (step (if weak
                       (proof-with-checked-results
                           ((literal (proof-step-first (car bound)))
                            (head (proof-term-at literal 0)))
                         (if (equal head *proof-less*)
                             (library-library-as-weak lib (car bound))
                           (car bound)))
                     (car bound)))
             (step (if equation
                       (proof-with-checked-results
                           ((reverse-equation (proof-proof-symmetric proof equation)))
                         (lexer-lexer-proofs-replace-endpoint lexer step reverse-equation t))
                     step))
             (result (if weak step (lexer-lexer-proofs-implication lexer value step))))
          (cons result lexer))))))

(defun lexer-lexer-proofs-prove-result-leaf (value tests lexer function source template)
  (lexer-lexer-proofs-result-branch lexer function source value tests template))

(defun lexer-lexer-proofs-prove-result-by-value (n lexer function source value template tests)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof (lexer-lexer-proofs-lib lexer))))
    (cond
     ((zp n) '(:failure "fuel" "lexer-lexer-proofs-prove-result-by-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
          ((branches (proof-list-of-length (cdr value) 3))
           (test (car branches))
           (yes (lexer-lexer-proofs-prove-result-by-value
                 (1- n) lexer function source (cadr branches) template
                 (append tests (list (list test t)))))
           (no (lexer-lexer-proofs-prove-result-by-value
                (1- n) (cdr yes) function source (caddr branches) template
                (append tests (list (list test nil)))))
           (true-branch (proof-proof-if-true proof value))
           (true-branch (proof-proof-symmetric proof true-branch))
           (yes-proof (proof-proof-rewrite-result proof (car yes) true-branch
                                                  template *proof-result*))
           (false-branch (proof-proof-if-false proof value))
           (false-branch (proof-proof-symmetric proof false-branch))
           (no-proof (proof-proof-rewrite-result proof (car no) false-branch
                                                 template *proof-result*))
           (step (proof-proof-cases proof test yes-proof no-proof)))
        (cons step (cdr no))))
     ((and (proof-compound value) (not (consp value))) '(:failure "failure" ""))
     ((and (proof-compound value) (proof-compound (car value)))
      (proof-with-checked-results
          ((expansion (proof-simplify-expansion proof value))
           (result (lexer-lexer-proofs-prove-result-by-value
                    (1- n) lexer function source (cadr expansion) template tests))
           (reversed (proof-proof-symmetric proof (car expansion)))
           (step (proof-proof-rewrite-result proof (car result) reversed template *proof-result*)))
        (cons step (cdr result))))
     (t (proof-with-checked-results
            ((result (lexer-lexer-proofs-prove-result-leaf value tests lexer function source template))
             (literal (proof-step-first (car result)))
             (target (proof-subst template (list (cons *proof-result* value)))))
          (if (equal literal target) result '(:failure "failure" "")))))))

(defun lexer-lexer-proofs-prove-result (lexer function induct)
  (let* ((lib (lexer-lexer-proofs-lib lexer))
         (proof (library-library-proof lib))
         (definition (assoc-equal function (proof-proof-definitions proof)))
         (fields (assoc-equal function *lexer-fields*)))
    (cond
     ((not definition) '(:failure "failure" ""))
     ((not fields) '(:failure "failure" ""))
     (t
      (let* ((formals (cadr definition))
             (call (cons function formals))
             (weak (equal function *lexer-plain*))
             (left (lexer-tail *proof-result* (cadr fields))))
        (proof-with-checked-results
            ((input (proof-term-at formals 0))
             (right (lexer-tail input (caddr fields)))
             (template (if weak
                           (library-le (lexer-length left) (lexer-length right))
                         (list *library-implies* *proof-result*
                               (library-lt (lexer-length left) (lexer-length right)))))
             (formula (proof-subst template (list (cons *proof-result* call))))
             (measure (list *library-count* input))
             (lexer (if induct
                        (lexer-lexer-proofs-with-induction
                         lexer (list function formals formula measure nil))
                      lexer))
             (unfolded (proof-proof-unfold proof call))
             (body (proof-rewritten-term unfolded))
             (result (lexer-lexer-proofs-prove-result-by-value
                      1000000 lexer function right body template nil))
             (lexer (cdr result))
             (reverse-equation (proof-proof-symmetric proof unfolded))
             (step (proof-proof-rewrite-result proof (car result) reverse-equation
                                               template *proof-result*))
             (step (if induct
                       (proof-with-checked-results ((ordinal (library-library-builtin lib 1 input)))
                         (proof-proof-induct proof ordinal step formula measure
                                             (nth 4 (lexer-lexer-proofs-induction lexer))))
                     step))
             (function-name (proof-term-at function 2))
             (name (string-append function-name (if weak "-UPPER" "-STRICT")))
             (extended (library-library-lemma lib name formula step nil)))
          (lexer-lexer-proofs-with-lib
           (if induct (lexer-lexer-proofs-with-induction lexer nil) lexer)
           extended)))))))

(defun lexer-lexer-proofs-prove-plain-strict (lexer)
  (let* ((lib (lexer-lexer-proofs-lib lexer))
         (proof (library-library-proof lib))
         (definition (assoc-equal *lexer-plain* (proof-proof-definitions proof))))
    (if (not definition)
        '(:failure "failure" "")
      (let* ((formals (cadr definition))
             (call (cons *lexer-plain* formals)))
        (proof-with-checked-results
            ((equation (proof-proof-unfold proof call))
             (body (proof-rewritten-term equation))
             (branches (proof-list-of-length (cdr body) 3))
             (test (car branches))
             (hypotheses (descent-hypotheses-init lib (list (list test t)) nil))
             (input (proof-term-at formals 0))
             (bound (lexer-lexer-proofs-relation lexer (lexer-tail (cadr branches) 1)
                                                input hypotheses))
             (true-branch (proof-proof-if-true proof body))
             (unfolded (proof-proof-chain proof equation (list true-branch)))
             (reversed (proof-proof-symmetric proof unfolded))
             (step (proof-proof-rewrite proof (car bound) reversed '(1 1 1 1)))
             (goal (library-lt (lexer-length (lexer-tail call 1)) (lexer-length input)))
             (extended (library-library-lemma lib "LEX-PLAIN-STRICT" goal step
                                              (list (proof-neg test)))))
          (lexer-lexer-proofs-with-lib (cadr bound) extended))))))

(defun lexer-lexer-proofs-build (lexer)
  (proof-with-checked-results
      ((lexer (lexer-lexer-proofs-prove-result lexer *lexer-plain* t))
       (lexer (lexer-lexer-proofs-prove-plain-strict lexer))
       (lexer (lexer-lexer-proofs-prove-result lexer *lexer-quoted* t))
       (lexer (lexer-lexer-proofs-prove-result lexer *lexer-part* nil))
       (lexer (lexer-lexer-proofs-prove-result lexer *lexer-symbol-rest* nil))
       (lexer (lexer-lexer-proofs-prove-result lexer *lexer-sharp* nil)))
    (lexer-lexer-proofs-prove-result lexer *lexer-atom* nil)))

(defun lexer-lexer-proofs-decrease (lexer goal hypotheses)
  (let* ((lib (lexer-lexer-proofs-lib lexer))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length goal 3))
         (child (cadr parts))
         (parent (caddr parts))
         (suffix (proof-term-at child 1))
         (source (proof-term-at parent 1))
         (bound (lexer-lexer-proofs-relation lexer suffix source hypotheses))
         (ordinal (library-library-ordinal-comparison lib child parent))
         (step (proof-proof-transport proof (car bound) ordinal)))
      (list step (cadr bound) (caddr bound)))))
