(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t3-book-evaluators-eval* (proof-sym "EVAL-FOR-MV-NTH" "ACL2"))
(defconst *t3-book-evaluators-flag-eval* (proof-sym "FLAG-IS-CP-EV" "FLAG"))
(defconst *t3-book-evaluators-mode* (proof-sym "T3-LIST-MODE" "ACL2"))
(defconst *t3-book-evaluators-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *t3-book-evaluators-pairlis* (proof-sym "PAIRLIS$" "ACL2"))
(defconst *t3-book-evaluators-kwote* (proof-sym "KWOTE" "ACL2"))
(defconst *t3-book-evaluators-kwote-list* (proof-sym "KWOTE-LST" "ACL2"))
(defconst *t3-book-evaluators-mv-nth* (proof-sym "MV-NTH" "ACL2"))
(defconst *t3-book-evaluators-symbolp* (proof-cl "SYMBOLP"))

(defun t3-book-evaluators-evaluator-names-prefix (names)
  (cadr names))

(defun t3-book-evaluators-evaluator-names-core (names)
  (caddr names))

(defun t3-book-evaluators-evaluator-names-value (names)
  (cadddr names))

(defun t3-book-evaluators-evaluator-names-values (names)
  (car (cddddr names)))

(defun t3-book-evaluators-evaluator-names-rule (names label)
  (concatenate 'string (t3-book-evaluators-evaluator-names-prefix names) label))

(defun t3-book-evaluators-evaluator-names-from-prefix (prefix)
  (list :t3-evaluator-names prefix
        (proof-sym (concatenate 'string "SELF-" prefix "CORE") "ACL2")
        (proof-sym (concatenate 'string "SELF-" prefix "VALUE") "ACL2")
        (proof-sym (concatenate 'string "SELF-" prefix "VALUES") "ACL2")))

(defun t3-book-evaluators-evaluator-names-init (name)
  (cond ((equal name *t3-book-evaluators-eval*)
         (t3-book-evaluators-evaluator-names-from-prefix "T3-EVAL-"))
        ((equal name *t3-book-evaluators-flag-eval*)
         (t3-book-evaluators-evaluator-names-from-prefix "T3-FLAG-EVAL-"))
        (t (proof-with-checked-results ((source (proof-write name)))
             (t3-book-evaluators-evaluator-names-from-prefix
              (concatenate 'string "T3-EVAL-" (text-upper (siphash-hexdigest source)) "-"))))))

(defun t3-book-evaluators-second (value)
  (list *library-car* (list *library-cdr* value)))

(defun t3-book-evaluators-third (value)
  (t3-book-evaluators-second (list *library-cdr* value)))

(defun t3-book-evaluators-quote-excluded (lib value signed)
  (let ((proof (library-library-proof lib))
        (test (proof-eq value (proof-quote *proof-quote*))))
    (proof-with-checked-results
     ((identity (proof-proof-assume proof test t))
      (literal (proof-step-first signed))
      (bad (if (proof-is-call literal *proof-consp*)
               (proof-with-checked-results
                ((changed (proof-proof-rewrite proof signed identity '(1 1))))
                (t3-logic-libraryproofs-simplify-first lib changed nil nil))
             (proof-with-checked-results
              ((quote-symbol (t3-book-values-book-proofs-prove
                              (t3-book-values-make-book-proofs lib nil nil)
                              (list *t3-book-evaluators-symbolp* (proof-quote *proof-quote*)) nil nil))
               (typed (library-library-transport-argument lib quote-symbol identity 1)))
              (proof-proof-cut proof typed signed)))))
     (proof-proof-front proof bad (proof-neg test)))))

(defun t3-book-evaluators-argument-selectors-loop (arity values)
  (declare (xargs :measure (nfix arity)))
  (if (zp arity)
      nil
    (cons (list *library-car* values)
          (t3-book-evaluators-argument-selectors-loop
           (1- arity) (list *library-cdr* values)))))

(defun t3-book-evaluators-argument-selectors (values arity)
  (cond ((integerp arity) (t3-book-evaluators-argument-selectors-loop arity values))
        ((eq arity t) (t3-book-evaluators-argument-selectors-loop 1 values))
        ((null arity) nil)
        (t '(:failure "failure" ""))))

(defun t3-book-evaluators-primitive-branches (primitives head actuals)
  (if (endp primitives)
      *proof-false*
    (proof-with-checked-results
     ((otherwise (t3-book-evaluators-primitive-branches (cdr primitives) head actuals))
      (primitive (proof-list-of-length (car primitives) 2))
      (arguments (t3-book-evaluators-argument-selectors actuals (cadr primitive))))
     (proof-ite (proof-eq head (proof-quote (car primitive)))
                (cons (car primitive) arguments)
                otherwise))))

(defun t3-book-evaluators-core-definition (core primitives)
  (let* ((head (list *library-car* *library-x*))
         (tail (list *library-cdr* *library-x*))
         (actuals (list core *proof-true* tail *library-y*)))
    (proof-with-checked-results
     ((branches (t3-book-evaluators-primitive-branches primitives head actuals)))
     (let* ((apply (proof-ite (list *t3-book-evaluators-symbolp* head) branches *proof-false*))
            (closure (list core *proof-false* (t3-book-evaluators-third head)
                           (list *t3-book-evaluators-pairlis*
                                 (t3-book-evaluators-second head) actuals)))
            (application (proof-ite (list *proof-consp* head) closure apply))
            (atom (proof-ite (list *t3-book-evaluators-symbolp* *library-x*)
                             (proof-ite *library-x*
                                        (list *library-cdr*
                                              (list *t3-book-evaluators-assoc* *library-x* *library-y*))
                                        *proof-false*)
                             *proof-false*))
            (term (proof-ite (list *proof-consp* *library-x*)
                             (proof-ite (proof-eq head (proof-quote *proof-quote*))
                                        (t3-book-evaluators-second *library-x*) application)
                             atom))
            (term-list (proof-ite (list *proof-consp* *library-x*)
                                  (list *proof-cons* (list core *proof-false* head *library-y*) actuals)
                                  *proof-false*)))
       (list core (list *t3-book-evaluators-mode* *library-x* *library-y*)
             (proof-ite *t3-book-evaluators-mode* term-list term))))))

(defun t3-book-evaluators-measure-step (lib clause call)
  (if (not call)
      (library-library-builtin lib 1 *library-x*)
    (proof-with-checked-results
     ((comparison (proof-list-of-length (car (last clause)) 3))
      (evidence (t3-logic-evidence-init lib (termination-call-tests call) nil nil))
      (answer (t3-size-count-descent lib (cadr comparison) (caddr comparison) evidence)))
     (car answer))))

(defun t3-book-evaluators-measure-proofs (lib obligations seen)
  (if (endp obligations)
      nil
    (let* ((case (car obligations))
           (clause (car case)))
      (if (member-equal clause seen)
          (t3-book-evaluators-measure-proofs lib (cdr obligations) seen)
        (proof-with-checked-results
         ((step (t3-book-evaluators-measure-step lib clause (cadr case)))
          (step (proof-proof-subsume (library-library-proof lib) step clause))
          (rest (t3-book-evaluators-measure-proofs lib (cdr obligations) (cons clause seen))))
         (cons step rest))))))

(defun t3-book-evaluators-add-core (lib definition measure)
  (let* ((core (car definition))
         (group (list definition)))
    (proof-with-checked-results
     ((calls (termination-recursive-calls *termination-all* group))
      (obligations (termination-obligation-cases group (list (cons core measure)) calls))
      (steps (t3-book-evaluators-measure-proofs lib obligations nil))
      (entry (proof-proof-entry "measure" core (list core measure) steps))
      (proof (proof-proof-add-definition (library-library-proof lib) core
                                         (cadr definition) (caddr definition)))
      (line (proof-line "define" (list *termination-all* definition))))
     (library-library-with-entries
      (library-library-with-proof lib proof)
      (append (library-library-entries lib)
              (list (list "define" core (caddr entry)
                          (concatenate 'string line (cadddr entry)))))))))

(defun t3-book-evaluators-core-calls (terms core)
  (cond ((endp terms) nil)
        ((proof-is-call (car terms) core)
         (cons (car terms) (t3-book-evaluators-core-calls (cdr terms) core)))
        (t (t3-book-evaluators-core-calls (cdr terms) core))))

(defun t3-book-evaluators-replace-core-call (lib equation call names)
  (let* ((proof (library-library-proof lib))
         (alias (if (equal (cadr call) *proof-false*)
                    (t3-book-evaluators-evaluator-names-value names)
                  (t3-book-evaluators-evaluator-names-values names))))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof (cons alias (cddr call))))
      (symmetric (proof-proof-symmetric proof opened)))
     (t3-book-spines-replace-value lib equation (list symmetric)))))

(defun t3-book-evaluators-replace-core-calls (lib equation calls names)
  (declare (xargs :measure (acl2-count calls)))
  (if (or (endp calls) (failure-p equation))
      equation
    (t3-book-evaluators-replace-core-calls
     lib (t3-book-evaluators-replace-core-call lib equation (car calls) names) (cdr calls) names)))

(defund t3-book-evaluators-normalize (lib term evidence definitions)
  (t3-book-values-book-proofs-normalize
   (t3-book-values-make-book-proofs lib nil nil) term evidence definitions))

(defun t3-book-evaluators-define-alias-equation (lib names alias label)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((equation (proof-proof-unfold proof (list alias *library-x* *library-y*)))
      (right (proof-rewritten-term equation))
      (opened (proof-proof-unfold proof right))
      (equation (proof-proof-chain proof equation (list opened)))
      (right (proof-rewritten-term equation))
      (normalized (t3-book-evaluators-normalize lib right nil nil))
      (equation (proof-proof-chain proof equation (list normalized)))
      (right (proof-rewritten-term equation))
      (terms (t3-book-theorems-terms right))
      (equation
       (t3-book-evaluators-replace-core-calls
        lib equation (proof-unique (t3-book-evaluators-core-calls
                                    terms (t3-book-evaluators-evaluator-names-core names)))
        names))
      (claim (proof-step-first equation)))
     (library-library-lemma lib (t3-book-evaluators-evaluator-names-rule names label)
                            claim equation nil))))

(defun t3-book-evaluators-define-evaluator (lib names primitives)
  (let ((core (t3-book-evaluators-evaluator-names-core names))
        (value (t3-book-evaluators-evaluator-names-value names))
        (values (t3-book-evaluators-evaluator-names-values names))
        (formals (list *library-x* *library-y*)))
    (proof-with-checked-results
     ((definition (t3-book-evaluators-core-definition core primitives))
      (lib (t3-book-evaluators-add-core lib definition (list *library-count* *library-x*)))
      (lib (library-library-definition lib value formals (cons core (cons *proof-false* formals))))
      (lib (library-library-definition lib values formals (cons core (cons *proof-true* formals))))
      (lib (t3-book-evaluators-define-alias-equation lib names value "VALUE-EQUATION")))
     (t3-book-evaluators-define-alias-equation lib names values "VALUES-EQUATION"))))

(defund t3-book-evaluators-rewrite-constructor-branch (proof value equation branch index)
  (t3-book-spines-constructor-form-rewrite proof value equation branch index))

(defun t3-book-evaluators-constructor-form (n lib value evidence)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t3-book-evaluators-constructor-form")
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
       ((equation (t3-book-evaluators-normalize lib value evidence nil))
        (current (if equation (proof-rewritten-term equation) value))
        (equation
         (if (proof-is-call current *proof-if*)
             (proof-with-checked-results
              ((yes (proof-term-at current 2))
               (branch (t3-book-evaluators-constructor-form (1- n) lib yes evidence))
               (equation (t3-book-evaluators-rewrite-constructor-branch proof value equation branch 2))
               (no (proof-term-at current 3))
               (branch (t3-book-evaluators-constructor-form (1- n) lib no evidence)))
              (t3-book-evaluators-rewrite-constructor-branch proof value equation branch 3))
           equation)))
       (and equation (proof-proof-tidy proof equation))))))

(defun t3-book-evaluators-expanded (lib names call evidence changes)
  (proof-with-checked-results
   ((head (proof-term-at call 0))
    (rule (t3-book-evaluators-evaluator-names-rule
           names (if (equal head (t3-book-evaluators-evaluator-names-value names))
                     "VALUE-EQUATION" "VALUES-EQUATION")))
    (equation (library-library-cite lib rule (cdr call) nil))
    (equation (t3-book-spines-replace-value lib equation changes))
    (right (proof-rewritten-term equation))
    (normalized (t3-book-evaluators-constructor-form 1000000 lib right evidence)))
   (proof-proof-chain (library-library-proof lib) equation (list normalized))))

(defun t3-book-evaluators-view (lib function equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first equation))
      (left (proof-term-at literal 1))
      (reflexive (proof-proof-reflexive proof (list function left)))
      (observed (proof-proof-rewrite proof reflexive equation '(1 2 1)))
      (right (proof-rewritten-term observed))
      (computed (t3-book-values-book-proofs-constant
                 (t3-book-values-make-book-proofs lib nil nil) right)))
     (proof-proof-chain proof observed (list computed)))))

(defun t3-book-evaluators-on-atom (lib selector value atom)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((selector-name (proof-term-at selector 2))
      (completion (library-library-axiom lib (concatenate 'string "COMPLETION-OF-" selector-name)
                                         (list value)))
      (right (proof-rewritten-term completion))
      (selected (proof-proof-select proof right atom)))
     (proof-proof-chain proof completion (list selected)))))

(defun t3-book-evaluators-add-selector (lib names test present absent values selector result label)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((yes (t3-book-evaluators-expanded lib names values (list present) nil))
      (yes (t3-book-evaluators-view lib selector yes))
      (no (t3-book-evaluators-expanded lib names values (list absent) nil))
      (no (t3-book-evaluators-view lib selector no))
      (change (t3-book-evaluators-on-atom lib selector *library-x* absent))
      (finished (t3-book-evaluators-expanded lib names
                                             (list result (list selector *library-x*) *library-y*)
                                             nil (list change)))
      (backwards (proof-proof-symmetric proof finished))
      (no (proof-proof-chain proof no (list backwards)))
      (step (proof-proof-cases proof test yes no))
      (claim (proof-step-first step)))
     (library-library-lemma lib (t3-book-evaluators-evaluator-names-rule names label)
                            claim step nil))))

(defun t3-book-evaluators-evaluator-selectors (lib names)
  (let* ((proof (library-library-proof lib))
         (test (list *proof-consp* *library-x*))
         (value (t3-book-evaluators-evaluator-names-value names))
         (values (t3-book-evaluators-evaluator-names-values names))
         (call (list values *library-x* *library-y*)))
    (proof-with-checked-results
     ((present (proof-proof-assume proof test t))
      (absent (proof-proof-assume proof test nil))
      (lib (t3-book-evaluators-add-selector lib names test present absent call *library-car*
                                            value "VALUES-FIRST")))
     (t3-book-evaluators-add-selector lib names test present absent call *library-cdr*
                                      values "VALUES-REST"))))

(defun t3-book-evaluators-list-case (lib value evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((equation (proof-proof-unfold proof (list *t3-book-lemmas-true-listp* value)))
      (right (proof-rewritten-term equation))
      (normalized (t3-book-evaluators-normalize lib right evidence (list (proof-cl "EQ")))))
     (proof-proof-chain proof equation (list normalized)))))

(defun t3-book-evaluators-tail-induction (lib formula present)
  (let* ((proof (library-library-proof lib))
         (tail (list *library-cdr* *library-x*))
         (pairs (list (list *library-x* tail))))
    (proof-with-checked-results
     ((bound (library-library-builtin lib 3 *library-x*))
      (smaller (proof-proof-discharge proof bound present))
      (literal (proof-step-first smaller))
      (instance (proof-subst formula (list (cons *library-x* tail))))
      (hypothesis (proof-proof-assume proof (proof-ite literal instance *proof-true*) t))
      (step (proof-proof-prove-if proof hypothesis smaller)))
     (list pairs step))))

(defun t3-book-evaluators-add-proper-values (lib names test present absent call)
  (let ((proof (library-library-proof lib))
        (proper (list *t3-book-lemmas-true-listp* call)))
    (proof-with-checked-results
     ((induction (t3-book-evaluators-tail-induction lib proper present))
      (step (t3-book-evaluators-expanded lib names call (list present) nil))
      (right (proof-rewritten-term step))
      (opened (t3-book-evaluators-list-case lib right nil))
      (yes (proof-proof-transport proof (cadr induction) opened))
      (yes (library-library-transport-argument lib yes step 1))
      (base (t3-book-evaluators-expanded lib names call (list absent) nil))
      (empty (t3-book-evaluators-list-case lib *proof-false* nil))
      (empty (proof-proof-true-from-eq proof empty))
      (no (library-library-transport-argument lib empty base 1))
      (ordinal (library-library-builtin lib 1 *library-x*))
      (cases (proof-proof-cases proof test yes no))
      (result (proof-proof-induct proof ordinal cases proper (list *library-count* *library-x*)
                                  (list (car induction)))))
     (library-library-lemma lib (t3-book-evaluators-evaluator-names-rule names "PROPER-VALUES")
                            proper result nil))))

(defun t3-book-evaluators-add-quoted-values (lib names test present absent)
  (let* ((proof (library-library-proof lib))
         (before (list *library-car* *library-x*))
         (cast-list (list *t3-book-evaluators-kwote-list* *library-x*))
         (quoted (list (t3-book-evaluators-evaluator-names-values names) cast-list *library-y*))
         (premise (list *t3-book-lemmas-true-listp* *library-x*))
         (formula (list *library-implies* premise (proof-eq quoted *library-x*))))
    (proof-with-checked-results
     ((accepted (proof-proof-assume proof premise t))
      (induction (t3-book-evaluators-tail-induction lib formula present))
      (list-case (t3-book-evaluators-list-case lib *library-x* (list present)))
      (tail-type (proof-proof-rewrite proof accepted list-case '(1)))
      (tail-type (proof-proof-tidy proof tail-type))
      (smaller (proof-proof-modus-ponens proof (cadr induction) tail-type))
      (cast (t3-book-spines-shallow lib cast-list (list present)))
      (answer (t3-book-evaluators-expanded lib names quoted nil (list cast)))
      (quoted-head (t3-book-spines-shallow lib (list *t3-book-evaluators-kwote* before) nil))
      (first (t3-book-evaluators-expanded lib names
                                        (list (t3-book-evaluators-evaluator-names-value names)
                                              (list *t3-book-evaluators-kwote* before) *library-y*)
                                        nil (list quoted-head)))
      (answer (t3-book-spines-replace-value lib answer (list first smaller)))
      (elim (library-library-axiom lib "CAR-CDR-ELIM" (list *library-x*)))
      (reassembled (proof-proof-modus-ponens proof elim present))
      (yes (proof-proof-chain proof answer (list reassembled)))
      (cast (t3-book-spines-shallow lib cast-list (list absent)))
      (base (t3-book-evaluators-expanded lib names quoted nil (list cast)))
      (list-case (t3-book-evaluators-list-case lib *library-x* (list absent)))
      (empty (proof-proof-rewrite proof accepted list-case '(1)))
      (empty (proof-proof-tidy proof empty))
      (empty (proof-proof-symmetric proof empty))
      (no (proof-proof-chain proof base (list empty)))
      (cases (proof-proof-cases proof test yes no))
      (step (t3-book-lemmas-implication lib formula cases))
      (ordinal (library-library-builtin lib 1 *library-x*))
      (result (proof-proof-induct proof ordinal step formula (list *library-count* *library-x*)
                                  (list (car induction)))))
     (library-library-lemma lib (t3-book-evaluators-evaluator-names-rule names "QUOTED-VALUES")
                            formula result nil))))

(defun t3-book-evaluators-quoted-values (lib names)
  (let* ((proof (library-library-proof lib))
         (test (list *proof-consp* *library-x*))
         (call (list (t3-book-evaluators-evaluator-names-values names) *library-x* *library-y*)))
    (proof-with-checked-results
     ((present (proof-proof-assume proof test t))
      (absent (proof-proof-assume proof test nil))
      (lib (t3-book-evaluators-add-proper-values lib names test present absent call)))
     (t3-book-evaluators-add-quoted-values lib names test present absent))))

(defun t3-book-evaluators-symbol-is-atom (lib typed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((literal (proof-step-first typed))
      (value (proof-term-at literal 1))
      (cons (list *proof-consp* value))
      (rule (proof-proof-fact proof "consp-not-symbolp" (list (list *library-x* value))))
      (positive (proof-proof-assume proof cons t))
      (denial (proof-proof-modus-ponens proof rule positive))
      (contradiction (proof-proof-cut proof typed denial)))
     (proof-proof-front proof contradiction (proof-neg cons)))))

(defun t3-book-evaluators-constraint-guards (lib evidence term rhs index)
  (let* ((head (list *library-car* term))
         (cell (list *proof-consp* term))
         (symbol (list *t3-book-evaluators-symbolp* term)))
    (cond
     ((equal index 1)
      (proof-with-checked-results
       ((typed (t3-logic-evidence-require evidence symbol))
        (atomic (t3-book-evaluators-symbol-is-atom lib (car typed))))
       (list (list (car typed) atomic) nil)))
     ((or (equal index 4) (equal index 6))
      (proof-with-checked-results
       ((atomic (t3-logic-evidence-require evidence (proof-neg cell))))
       (if (equal index 4)
           (list (list (car atomic)) nil)
         (proof-with-checked-results
          ((nonsymbol (t3-logic-evidence-require (cdr atomic) (proof-neg symbol))))
          (list (list (car atomic) (car nonsymbol)) nil)))))
     (t
      (proof-with-checked-results
       ((present (t3-logic-evidence-require evidence cell)))
       (let ((evidence (cdr present))
             (present (car present)))
         (cond
          ((equal index 0)
           (proof-with-checked-results
            ((excluded (t3-logic-evidence-require evidence
                                                 (proof-neg (proof-eq head (proof-quote *proof-quote*))))))
            (list (list present (car excluded)) nil)))
          ((or (equal index 2) (<= 8 index))
           (proof-with-checked-results
            ((fn (if (equal index 2) *proof-quote* (proof-term-at rhs 0)))
             (change (t3-logic-evidence-require evidence (proof-eq head (proof-quote fn)))))
            (list (list present) (list (car change)))))
          ((equal index 3)
           (proof-with-checked-results
            ((closure (t3-logic-evidence-require evidence (list *proof-consp* head)))
             (excluded (t3-book-evaluators-quote-excluded lib head (car closure))))
            (list (list present (car closure) excluded) nil)))
          ((equal index 7)
           (proof-with-checked-results
            ((not-symbol (t3-logic-evidence-require evidence
                                                   (proof-neg (list *t3-book-evaluators-symbolp* head))))
             (atomic (t3-logic-evidence-require (cdr not-symbol) (proof-neg (list *proof-consp* head))))
             (excluded (t3-book-evaluators-quote-excluded lib head (car not-symbol))))
            (list (list present (car atomic) (car not-symbol) excluded) nil)))
          (t (list (list present) nil)))))))))

(defun t3-book-evaluators-constraint-recovery (lib names rhs guards tail environment result)
  (let* ((proof (library-library-proof lib))
         (original (list (t3-book-evaluators-evaluator-names-values names) tail environment)))
    (proof-with-checked-results
     ((proper (library-library-cite lib (t3-book-evaluators-evaluator-names-rule names "PROPER-VALUES")
                                    (list tail environment) nil))
      (quoted (library-library-cite lib (t3-book-evaluators-evaluator-names-rule names "QUOTED-VALUES")
                                    (list original *proof-false*) nil))
      (recovered (proof-proof-modus-ponens proof quoted proper))
      (other (t3-book-evaluators-expanded lib names rhs guards nil))
      (other (t3-book-spines-replace-value lib other (list recovered)))
      (other (proof-proof-symmetric proof other)))
     (proof-proof-chain proof result (list other)))))

(defun t3-book-evaluators-constraint-argument (lib names tail environment result after-first)
  (proof-with-checked-results
     ((result
       (if after-first
           (proof-with-checked-results
            ((rest (library-library-cite lib (t3-book-evaluators-evaluator-names-rule names "VALUES-REST")
                                          (list tail environment) nil)))
            (t3-book-spines-replace-value lib result (list rest)))
         result))
      (tail (if after-first (list *library-cdr* tail) tail))
      (first (library-library-cite lib (t3-book-evaluators-evaluator-names-rule names "VALUES-FIRST")
                                   (list tail environment) nil)))
   (t3-book-spines-replace-value lib result (list first))))

(defun t3-book-evaluators-constraint-arguments (lib names args tail environment result after-first)
  (declare (xargs :measure (acl2-count args)))
  (if (or (endp args) (failure-p result))
      result
    (let ((step (t3-book-evaluators-constraint-argument lib names tail environment result after-first)))
      (t3-book-evaluators-constraint-arguments
       lib names (cdr args) (if after-first (list *library-cdr* tail) tail) environment step t))))

(defund t3-book-evaluators-equation-constraint (lib names formula index)
  (proof-with-checked-results
   ((premise (proof-term-at formula 1))
    (evidence (t3-logic-evidence-init lib (list (list premise t)) nil nil))
    (equation (proof-term-at formula 2))
    (parts (proof-list-of-length (cdr equation) 2))
    (actuals (proof-list-of-length (cdar parts) 2))
    (setup (t3-book-evaluators-constraint-guards lib evidence (car actuals) (cadr parts) index))
    (result (t3-book-evaluators-expanded lib names (car parts) (car setup) (cadr setup)))
    (result
     (let ((tail (list *library-cdr* (car actuals)))
           (environment (cadr actuals))
           (rhs (cadr parts)))
       (cond ((equal index 0)
              (t3-book-evaluators-constraint-recovery lib names rhs (car setup) tail environment result))
             ((<= 8 index)
              (t3-book-evaluators-constraint-arguments lib names (cdr rhs) tail environment result nil))
             (t result))))
    (claim (proof-step-first result)))
   (if (equal claim equation)
       (t3-book-lemmas-implication lib formula result)
     '(:failure "unsupported" ""))))

(defun t3-book-evaluators-shape-arities (declarations)
  (if (endp declarations)
      t
    (proof-with-checked-results ((declaration (proof-list-of-length (car declarations) 2)))
      (and (equal (cadr declaration) 2)
           (t3-book-evaluators-shape-arities (cdr declarations))))))

(defun t3-book-evaluators-shape-equations (formulas term values)
  (if (endp formulas)
      nil
    (proof-with-checked-results ((named (proof-list-of-length (car formulas) 2)))
      (let ((formula (cadr named)))
        (if (not (proof-is-call formula *library-implies*))
            :invalid
          (proof-with-checked-results ((equation (proof-term-at formula 2)))
            (if (not (proof-is-call equation *proof-equal*))
                :invalid
              (proof-with-checked-results
               ((parts (proof-list-of-length (cdr equation) 2))
                (lhs (t3-book-theorems-head (car parts))))
               (if (or (not (or (equal lhs term) (equal lhs values)))
                       (not (equal (len (car parts)) 3)))
                   :invalid
                 (proof-with-checked-results
                  ((rhs (t3-book-theorems-head (cadr parts)))
                   (rest (t3-book-evaluators-shape-equations (cdr formulas) term values)))
                  (if (eq rest :invalid) rest (cons (list lhs rhs) rest))))))))))))

(defun t3-book-evaluators-evaluator-shape (declarations formulas)
  (if (not (equal (len declarations) 2))
      nil
    (proof-with-checked-results ((binary (t3-book-evaluators-shape-arities declarations)))
      (if (or (not binary) (< (len formulas) 8))
          nil
        (let ((term (caar declarations))
              (values (caadr declarations)))
          (proof-with-checked-results ((equations (t3-book-evaluators-shape-equations formulas term values)))
            (and (not (eq equations :invalid))
                 (equal (take 8 equations)
                        (list (list term term) (list term *proof-if*) (list term *library-car*)
                              (list term term) (list values *proof-quote*) (list values *proof-cons*)
                              (list term *proof-quote*) (list term *proof-quote*))))))))))

(defun t3-book-evaluators-witness-goals (formulas functions)
  (if (endp formulas)
      nil
    (proof-with-checked-results
     ((named (proof-list-of-length (car formulas) 2))
      (goal (t3-tactics-replace-functions (cadr named) functions))
      (rest (t3-book-evaluators-witness-goals (cdr formulas) functions)))
     (cons goal rest))))

(defun t3-book-evaluators-witness-primitives (goals)
  (if (endp goals)
      nil
    (proof-with-checked-results
     ((equation (proof-term-at (car goals) 2))
      (rhs (proof-term-at equation 2))
      (head (proof-term-at rhs 0))
      (rest (t3-book-evaluators-witness-primitives (cdr goals))))
     (cons (list head (1- (len rhs))) rest))))

(defun t3-book-evaluators-witness-proofs (lib names goals index)
  (declare (xargs :measure (acl2-count goals)))
  (if (endp goals)
      nil
    (proof-with-checked-results
     ((step (t3-book-evaluators-equation-constraint lib names (car goals) index))
      (rest (t3-book-evaluators-witness-proofs lib names (cdr goals) (1+ index))))
     (cons step rest))))

(defun t3-book-evaluators-witness (lib declarations formulas)
  (proof-with-checked-results
   ((declarations (proof-list-of-length declarations 2))
    (first (proof-list-of-length (car declarations) 2))
    (second (proof-list-of-length (cadr declarations) 2))
    (names (t3-book-evaluators-evaluator-names-init (car first)))
    (value (t3-book-evaluators-evaluator-names-value names))
    (values (t3-book-evaluators-evaluator-names-values names))
    (functions (table-put (list (cons (car first) value)) (car second) values))
    (goals (t3-book-evaluators-witness-goals formulas functions))
    (primitives (t3-book-evaluators-witness-primitives (nthcdr 8 goals)))
    (lib (t3-book-evaluators-define-evaluator lib names primitives))
    (lib (t3-book-evaluators-evaluator-selectors lib names))
    (lib (t3-book-evaluators-quoted-values lib names))
    (proofs (t3-book-evaluators-witness-proofs lib names goals 0))
    (entry (proof-proof-entry "witness" (car first) (list (car first) value values) proofs)))
   (cons entry lib)))
