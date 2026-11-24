(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-warrant-badge* (proof-sym "BADGE-USERFN" "ACL2"))
(defconst *l1-warrant-tame-function* (proof-sym "TAMEP-FUNCTIONP" "ACL2"))
(defconst *l1-warrant-apply* (proof-sym "APPLY$" "ACL2"))
(defconst *l1-warrant-application-selector*
  (proof-sym "APPLY$-EQUIVALENCE-WITNESS" "ACL2"))
(defconst *l1-warrant-apply-user-function* (proof-sym "APPLY$-USERFN" "ACL2"))
(defconst *l1-warrant-left-function* (proof-sym "L1-LEFT-FUNCTION" "ACL2"))
(defconst *l1-warrant-right-function* (proof-sym "L1-RIGHT-FUNCTION" "ACL2"))
(defconst *l1-warrant-badge-failure* (proof-sym "L1-BADGE-FAILURE" "ACL2"))
(defconst *l1-warrant-warrant-selection* (proof-sym "L1-WARRANT-SELECTION" "ACL2"))
(defconst *l1-warrant-application-equation* (proof-sym "L1-APPLICATION-EQUATION" "ACL2"))
(defconst *l1-warrant-direct-selection* (proof-sym "L1-DIRECT-SELECTION" "ACL2"))
(defconst *l1-warrant-lambda* (proof-cl "LAMBDA"))
(defconst *l1-warrant-symbolp* (proof-cl "SYMBOLP"))
(defconst *l1-warrant-trivial-function*
  (list *l1-warrant-lambda* *proof-nil* *proof-false*))
(defconst *l1-warrant-definitions*
  (list *library-implies* *proof-not* *termination-return-last*
        (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "EQ")
        (proof-cl "EQL") (proof-cl "NULL")
        (proof-sym "LAMBDA-OBJECT-SHAPEP" "ACL2")
        (proof-sym "LAMBDA-OBJECT-FORMALS" "ACL2")
        (proof-sym "LAMBDA-OBJECT-BODY" "ACL2")
        (proof-sym "SYMBOL-LISTP" "ACL2")
        *l1-warrant-tame-function* (proof-sym "TAMEP" "ACL2")))

(defun l1-warrant-warrant-proof-init ()
  (proof-proof-with-kind (proof-proof-init) :l1-warrant))

(defun l1-warrant-term-at-place (term place)
  (declare (xargs :measure (acl2-count place)))
  (if (endp place)
      term
    (proof-with-checked-results ((child (proof-term-at term (car place))))
      (l1-warrant-term-at-place child (cdr place)))))

(defun l1-warrant-step-at-place (step place)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (l1-warrant-term-at-place literal place)))

(defun l1-warrant-warrant-proof-constant (proof term)
  (l1-application-proof-constant proof term))

(defun l1-warrant-warrant-proof-simplify (proof term evidence definitions)
  (l1-application-proof-simplify proof term evidence definitions))

(defun l1-warrant-warrant-proof-trivial-function-tame (proof)
  (l1-warrant-warrant-proof-simplify
   proof (list *l1-warrant-tame-function* (proof-quote *l1-warrant-trivial-function*))
   nil *l1-warrant-definitions*))

(defun l1-warrant-simplify (proof term evidence definitions)
  (l1-application-proof-simplify proof term evidence definitions))

(defun l1-warrant-simplify-first (proof step evidence definitions)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (equality (l1-warrant-simplify proof literal evidence definitions)))
    (if equality
        (proof-with-checked-results ((rewritten (proof-proof-rewrite proof step equality '(1))))
          (proof-proof-tidy proof rewritten))
      step)))

(defun l1-warrant-prove (proof term evidence definitions)
  (l1-application-proof-prove proof term evidence definitions))

(defun l1-warrant-comparison-argument (comparison)
  (if (eq (car comparison) :choicerule)
      (l1-witness-choice-rule-argument comparison)
    (l1-witness-comparison-argument comparison)))

(defun l1-warrant-comparison-counterexample (comparison)
  (if (eq (car comparison) :choicerule)
      (l1-witness-choice-rule-counterexample comparison)
    (l1-witness-comparison-counterexample comparison)))

(defun l1-warrant-badge-test (test)
  (and (proof-is-call test *proof-if*)
       (proof-with-checked-results ((otherwise-term (proof-term-at test 3)))
         (and (equal otherwise-term *proof-false*)
              (proof-with-checked-results ((badge (proof-term-at test 1)))
                (and (proof-is-call badge *proof-equal*)
                     (proof-with-checked-results ((lookup (proof-term-at badge 1)))
                       (and (proof-is-call lookup *l1-warrant-badge*) badge))))))))

(defun l1-warrant-warrant-tests (comparison)
  (let ((counterexample (l1-warrant-comparison-counterexample comparison)))
    (and (proof-is-call counterexample *proof-not*)
         (proof-with-checked-results ((contract (proof-term-at counterexample 1)))
           (let ((guarded (proof-is-call contract *library-implies*)))
             (proof-with-checked-results
                 ((test (if guarded (proof-term-at contract 2) contract))
                  (badge (l1-warrant-badge-test test)))
               (and badge
                    (proof-with-checked-results
                        ((free (l1-finite-choice-variable-free-in
                                (l1-warrant-comparison-argument comparison) badge)))
                      (and (not free)
                           (proof-with-checked-results
                               ((guard (if guarded (proof-term-at contract 1) :none)))
                             (list test guard)))))))))))

(defun l1-warrant-warrant-parts (data)
  (proof-with-checked-results ((comparison (l1-witness-comparison-read data)))
    (and comparison
         (proof-with-checked-results ((tests (l1-warrant-warrant-tests comparison)))
           (and tests (cons comparison tests))))))

(defun l1-warrant-choice-witness (proof data)
  (proof-with-checked-results ((parts (l1-warrant-warrant-parts data)))
    (and parts
      (let* ((comparison (car parts))
             (argument (l1-warrant-comparison-argument comparison))
             (parameters (l1-witness-comparison-parameters comparison))
             (formals (cons argument parameters))
             (counterexample (l1-warrant-comparison-counterexample comparison))
             (test (proof-sym "L1-WARRANT-COUNTEREXAMPLE" "ACL2"))
             (choose (proof-sym "L1-WARRANT-CHOICE" "ACL2"))
             (test-call (cons test formals))
             (selected (cons choose parameters))
             (choice (list choose (list argument) (or parameters *proof-nil*)
                           test-call *proof-nil*)))
        (proof-with-checked-results
            ((definition (proof-line "define" (list *proof-nil* (list test formals counterexample))))
             (proof (proof-proof-add-definition proof test formals counterexample))
             (registration (l1-witness-available-choice proof "choose" choice))
             (proof (cdr registration))
             (axiom (proof-proof-fact proof choose nil))
             (open-test (proof-proof-unfold proof test-call))
             (axiom (proof-proof-rewrite proof axiom open-test '(1 1)))
             (open-choice (proof-proof-unfold proof (list* test selected parameters)))
             (axiom (proof-proof-rewrite proof axiom open-choice '(1 2)))
             (witness (l1-witness-witness-entry proof comparison selected axiom "")))
          (and witness
               (proof-with-checked-results ((source (proof-line "choose" choice)))
                 (list (car witness) (concatenate 'string definition source (cadr witness))))))))))

(defun l1-warrant-fixed-failure-argument (badge-matches guarded)
  (if (not guarded)
      *proof-false*
    (proof-with-checked-results ((arity (l1-warrant-term-at-place badge-matches '(2 1 1))))
      (if (or (integerp arity) (eq arity t))
          (proof-quote (make-list-ac (if (eq arity t) 1 (nfix arity))
                                    *l1-warrant-trivial-function* nil))
        '(:failure "failure" "")))))

(defun l1-warrant-fixed-failure (proof comparison test guard)
  (let ((guarded (not (eq guard :none))))
    (proof-with-checked-results
        ((badge-matches (proof-term-at test 1))
         (argument (l1-warrant-fixed-failure-argument badge-matches guarded)))
      (let ((substitution (list (cons (l1-warrant-comparison-argument comparison) argument)))
            (conditional (proof-ite *library-x* *library-y* *proof-false*)))
        (proof-with-checked-results
            ((failure (proof-subst (l1-warrant-comparison-counterexample comparison) substitution))
             (mismatch (proof-proof-assume proof *library-x* nil))
             (fixed-guard (if guarded (l1-warrant-term-at-place failure '(1 1)) :none))
             (guard-holds (and guarded (proof-proof-assume proof *library-z* t)))
             (application (proof-term-at test 2))
             (fixed-application (proof-subst application substitution)))
          (let ((template (if guarded
                              (list *library-implies* *library-z* conditional)
                            conditional))
                (bindings (append (list (list *library-x* badge-matches))
                                  (and guarded (list (list *library-z* fixed-guard)))
                                  (list (list *library-y* fixed-application))))
                (premises (if guarded (list mismatch guard-holds) (list mismatch))))
            (proof-with-checked-results
                ((generic (l1-warrant-prove proof (proof-neg template) premises
                                            (list *library-implies* *proof-not*)))
                 (instance (proof-proof-instantiate proof generic bindings))
                 (step (if guarded
                           (proof-with-checked-results
                               ((evidence (l1-warrant-prove proof fixed-guard nil
                                                           *l1-warrant-definitions*)))
                             (proof-proof-discharge proof instance evidence))
                         instance))
                 (subsumed (proof-proof-subsume proof step (list failure badge-matches))))
              (list argument subsumed))))))))

(defun l1-warrant-implication (proof antecedent consequent)
  (let ((formula (list *library-implies* *library-y* *library-z*))
        (definitions (list *library-implies*)))
    (proof-with-checked-results
        ((antecedent-true (proof-proof-assume proof *library-y* t))
         (consequent-true (proof-proof-assume proof *library-z* t))
         (yes (l1-warrant-prove proof formula (list antecedent-true consequent-true) definitions))
         (antecedent-false (proof-proof-assume proof *library-y* nil))
         (no (l1-warrant-prove proof formula (list antecedent-false) definitions))
         (generic (proof-proof-cases proof *library-y* yes no))
         (literal (proof-step-first consequent))
         (step (proof-proof-instantiate proof generic (list (list *library-y* antecedent)
                                                           (list *library-z* literal)))))
      (proof-proof-discharge proof step consequent))))

(defun l1-warrant-application-selection-actual
    (proof necessary opened-test applied argument actual left right index)
  (let ((mapping (list (cons argument actual)))
        (equality (proof-eq (list *l1-warrant-apply* left actual)
                            (list *l1-warrant-apply* right actual)))
        (place (list 1 index 1)))
    (proof-with-checked-results
        ((expected (proof-subst applied mapping))
         (agreement (proof-eq equality expected))
         (assumption (proof-proof-assume proof agreement t))
         (necessary (proof-proof-rewrite proof necessary assumption place))
         (instance (proof-proof-instantiate proof opened-test (table-items mapping)))
         (restore (proof-proof-symmetric proof instance))
         (necessary (proof-proof-rewrite proof necessary restore place)))
      (list necessary agreement))))

(defun l1-warrant-application-selection
    (proof comparison test guard selector bad-argument bad-failure left right)
  (let* ((argument (l1-warrant-comparison-argument comparison))
         (picked (list *l1-warrant-application-selector* left right))
         (premise (l1-warrant-comparison-counterexample comparison))
         (guarded (not (eq guard :none))))
    (proof-with-checked-results
        ((badge (proof-term-at test 1))
         (selected (proof-ite badge picked bad-argument))
         (contract (proof-term-at premise 1))
         (parameters (l1-recursive-pairs-to-map
                      (seq-zip (l1-witness-choice-rule-parameters selector) (list left right)) nil))
         (parameters (table-put parameters (l1-witness-choice-rule-argument selector) argument))
         (necessary (l1-witness-choice-rule-counterexample-proof selector proof parameters))
         (necessary (l1-warrant-simplify-first proof necessary nil (list *termination-return-last*)))
         (badge-holds (proof-proof-assume proof badge t))
         (application (proof-term-at test 2))
         (applied (if guarded (list *library-implies* guard application) application))
         (opened-test (proof-proof-select proof test badge-holds))
         (opened-test (if guarded
                          (proof-with-checked-results ((identity (proof-proof-reflexive proof contract)))
                            (proof-proof-rewrite proof identity opened-test '(1 2 2)))
                        opened-test))
         (first (l1-warrant-application-selection-actual proof necessary opened-test applied
                                                        argument argument left right 1))
         (second (l1-warrant-application-selection-actual proof (car first) opened-test applied
                                                         argument picked left right 2))
         (choose-application (proof-proof-select proof selected badge-holds))
         (choose-application (proof-proof-symmetric proof choose-application))
         (yes (proof-proof-rewrite-first proof (car second) choose-application))
         (badge-fails (proof-proof-assume proof badge nil))
         (choose-fixed (proof-proof-select proof selected badge-fails))
         (choose-fixed (proof-proof-symmetric proof choose-fixed))
         (fixed (proof-proof-rewrite-result proof bad-failure choose-fixed premise argument))
         (no (l1-warrant-implication proof premise fixed))
         (step (proof-proof-cases proof badge yes no))
         (literal (proof-step-first step))
         (step (proof-proof-subsume proof step (list literal (proof-neg (cadr first))
                                                     (proof-neg (cadr second))))))
      (list selected step))))

(defun l1-warrant-counts-total (counts)
  (if (endp counts)
      0
    (+ (car counts) (l1-warrant-counts-total (cdr counts)))))

(defun l1-warrant-lemma (name step)
  (proof-with-checked-results
      ((entry (proof-proof-entry "lemma" name (cons name (proof-step-clause step)) (list step))))
    (list (l1-warrant-counts-total (caddr entry)) (cadddr entry))))

(defun l1-warrant-entries-count (entries)
  (if (endp entries)
      0
    (+ (cadar entries) (l1-warrant-entries-count (cdr entries)))))

(defun l1-warrant-entries-sources (entries)
  (if (endp entries)
      nil
    (cons (caddar entries) (l1-warrant-entries-sources (cdr entries)))))

(defun l1-warrant-append-source (left right)
  ;; The accumulated proof text can occupy a large part of the heap.
  (prog2$ (if (> (+ (length left) (length right)) 2000000)
              #+sbcl (gc$ :full t)
              #-sbcl (gc$)
            nil)
          (string-append left right)))

(defun l1-warrant-source-length (sources)
  (if (endp sources)
      0
    (+ (length (car sources)) (l1-warrant-source-length (cdr sources)))))

(defun l1-warrant-split-sources (sources remaining left)
  (declare (xargs :measure (acl2-count sources)))
  (if (or (<= remaining 0) (endp (cdr sources)))
      (cons (reverse left) sources)
    (l1-warrant-split-sources (cdr sources) (- remaining (length (car sources)))
                              (cons (car sources) left))))

(defun l1-warrant-split-source-in-half (sources)
  (let ((half (max 1 (floor (l1-warrant-source-length sources) 2))))
    (l1-warrant-split-sources sources half nil)))

(defun l1-warrant-join-sources (n sources)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "Fuel" "l1-warrant-join-sources"))
        ((endp sources) "")
        ((endp (cdr sources)) (car sources))
        (t (let* ((split (l1-warrant-split-source-in-half sources))
                  (left (car split))
                  (right (cdr split)))
             (proof-with-checked-results
                 ((left (l1-warrant-join-sources (1- n) left))
                  (right (l1-warrant-join-sources (1- n) right)))
               (l1-warrant-append-source left right))))))

(defun l1-warrant-source-halves (sources)
  (cond ((endp sources) (list "" ""))
        ((endp (cdr sources)) (list (car sources) ""))
        (t (let ((split (l1-warrant-split-source-in-half sources)))
             (proof-with-checked-results
                 ((left (l1-warrant-join-sources 1000000 (car split)))
                  (right (l1-warrant-join-sources 1000000 (cdr split))))
               (list left right))))))

;; Finish the two halves before allocating the complete certificate string.
(defun l1-warrant-result-halves (result)
  (if (or (failure-p result) (not (car result)))
      result
    (let ((value (car result)))
      (proof-with-checked-results ((halves (l1-warrant-source-halves (cadr value))))
        (cons (list (car value) halves (caddr value)) (cdr result))))))

(defun l1-warrant-materialize-result (result)
  (if (or (failure-p result) (not (car result)))
      result
    (let* ((value (car result))
           (halves (cadr value))
           (source (if (equal (cadr halves) "")
                       (car halves)
                     (l1-warrant-append-source (car halves) (cadr halves)))))
      (cons (list (car value) source (caddr value)) (cdr result)))))

(defun l1-warrant-put-fact (proof name step)
  (proof-proof-with-facts
   proof (table-put (proof-proof-facts proof) name (proof-step-clause step))))

(defun l1-warrant-remove-fact (proof name)
  (proof-with-checked-results ((facts (table-delete (proof-proof-facts proof) name)))
    (proof-proof-with-facts proof facts)))

(defun l1-warrant-direct-selection-complete (proof comparison step selected left right count sources)
  (let* ((certificates (l1-primitive-certificates-init proof))
         (proof (l1-warrant-put-fact proof *l1-warrant-direct-selection* step))
         (certificates (l1-primitive-certificates-with-proof certificates proof)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof *l1-warrant-direct-selection* nil))
         (discharged (l1-primitive-discharge-primitives certificates fact nil))
         (chosen (proof-subst selected (list (cons *l1-warrant-left-function* left)
                                             (cons *l1-warrant-right-function* right))))
         (certificates (cdr discharged))
         (witness (l1-witness-witness-entry (l1-primitive-certificates-proof certificates)
                                            comparison chosen (car discharged) "")))
      (if (not witness)
          '(:failure "failure" "")
        (let* ((entries (l1-primitive-certificates-entries certificates))
               (count (+ count (car witness) (l1-warrant-entries-count entries)))
               (sources (append sources (l1-warrant-entries-sources entries)
                                (list (cadr witness)))))
          (proof-with-checked-results
              ((closed (l1-primitive-certificates-close certificates))
               (proof (l1-warrant-remove-fact (l1-primitive-certificates-proof closed)
                                               *l1-warrant-direct-selection*)))
            (cons (list count sources "") proof)))))))

(defun l1-warrant-direct-selection-with-equation (proof comparison selection selected complete left right
                                                       argument equation)
  (proof-with-checked-results
      ((entry (l1-warrant-lemma *l1-warrant-application-equation* equation)))
    (let ((proof (l1-warrant-put-fact proof *l1-warrant-application-equation* equation))
          (picked (list *l1-warrant-application-selector* left right)))
      (proof-with-checked-results
          ((step (proof-proof-instantiate proof selection (list (list *l1-warrant-left-function* left)
                                                                (list *l1-warrant-right-function* right))))
           (known (proof-proof-fact proof *l1-warrant-application-equation* (list (list argument argument))))
           (step (proof-proof-discharge proof step known))
           (known (proof-proof-fact proof *l1-warrant-application-equation* (list (list argument picked))))
           (step (proof-proof-discharge proof step known))
           (direct (l1-warrant-lemma *l1-warrant-direct-selection* step))
           (count (+ (car entry) (car direct)))
           (sources (list (cadr entry) (cadr direct)))
           (result (if complete
                       (l1-warrant-direct-selection-complete proof comparison step selected
                                                             left right count sources)
                     (cons (list count sources
                                 "requires primitive dispatch and badge lookup certificates") proof)))
           (proof (l1-warrant-remove-fact (cdr result) *l1-warrant-application-equation*)))
        (cons (car result) proof)))))

(defun l1-warrant-direct-selection-application (proof comparison applied selection selected complete function)
  (let* ((argument (l1-warrant-comparison-argument comparison))
         (application (l1-application-quoted-application proof function argument nil nil nil)))
    (cond
     ((failure-p application)
      (if (equal (cadr application) "UnsupportedApplication")
          (cons nil proof)
        application))
     (t
      (let ((left (car application))
            (right (cadr application))
            (abstract (caddr application))
            (logical (cadddr application)))
        (proof-with-checked-results
            ((abstract-result (l1-warrant-step-at-place abstract '(2)))
             (logical-result (l1-warrant-step-at-place logical '(2))))
          (if (not (equal (proof-eq abstract-result logical-result) applied))
              (cons nil proof)
            (proof-with-checked-results
                ((abstract-term (l1-warrant-step-at-place abstract '(1)))
                 (logical-term (l1-warrant-step-at-place logical '(1)))
                 (equation (proof-proof-reflexive proof (proof-eq abstract-term logical-term)))
                 (equation (proof-proof-rewrite proof equation abstract '(1 2 1)))
                 (equation (proof-proof-rewrite proof equation logical '(1 2 2)))
                 (equation (proof-proof-tidy proof equation)))
              (l1-warrant-direct-selection-with-equation proof comparison selection selected complete
                                                         left right argument equation)))))))))

(defun l1-warrant-direct-selection-fragments (proof comparison applied selection selected complete)
  (if (not (proof-is-call applied *proof-equal*))
      (cons nil proof)
    (proof-with-checked-results ((user-call (proof-term-at applied 1)))
      (if (not (proof-is-call user-call *l1-warrant-apply-user-function*))
          (cons nil proof)
        (proof-with-checked-results ((designator (proof-term-at user-call 1)))
          (if (not (proof-is-call designator *proof-quote*))
              (cons nil proof)
            (proof-with-checked-results ((function (proof-term-at designator 1)))
              (l1-warrant-direct-selection-application proof comparison applied selection
                                                       selected complete function))))))))

(defun l1-warrant-direct-selection-with-proof (proof comparison applied selection selected complete)
  (l1-warrant-materialize-result
   (l1-warrant-result-halves
    (l1-warrant-direct-selection-fragments proof comparison applied selection selected complete))))

(defun l1-warrant-direct-selection (proof comparison applied selection selected complete)
  (proof-with-checked-results
      ((result (l1-warrant-direct-selection-with-proof proof comparison applied selection selected complete)))
    (car result)))

(defun l1-warrant-find-application-selector (choices)
  (cond ((endp choices) nil)
        ((equal (l1-witness-choice-rule-name (car choices)) *l1-warrant-application-selector*)
         (car choices))
        (t (l1-warrant-find-application-selector (cdr choices)))))

(defun l1-warrant-guarded-entries (proof comparison test)
  (proof-with-checked-results
      ((badge (proof-term-at test 1))
       (quoted (l1-guarded-quoted-arguments proof badge))
       (valid (l1-guarded-badge-validity proof badge))
       (arity (l1-guarded-argument-arity-with-proof
               proof test (l1-warrant-comparison-argument comparison)
               (l1-warrant-comparison-counterexample comparison)))
       (proof (cdr arity))
       (arity (car arity))
       (designator (l1-warrant-term-at-place test '(1 1 1)))
       (lambdas (if (equal designator (proof-quote (proof-sym "UNTIL$-AC" "ACL2")))
                    (l1-guarded-constant-lambdas proof (l1-warrant-comparison-argument comparison))
                  (list 0 ""))))
    (cons (list (+ (car quoted) (car valid) (car arity) (car lambdas))
                (concatenate 'string (cadr quoted) (cadr valid) (cadr arity) (cadr lambdas)))
          proof)))

(defun l1-warrant-warrant-cases-unguarded
    (proof comparison test selector bad-argument selected selection count source reason complete)
  (let ((proof (l1-warrant-put-fact proof *l1-warrant-warrant-selection* selection)))
    (proof-with-checked-results
        ((applied (proof-term-at test 2))
         (warrant-selection (proof-proof-fact proof *l1-warrant-warrant-selection* nil))
         (direct (l1-warrant-direct-selection-fragments proof comparison applied
                                                         warrant-selection selected complete))
         (proof (cdr direct))
         (direct (car direct))
         (answer (cond
                  (direct (list (+ count (car direct))
                                (cons source (cadr direct)) (caddr direct)))
                  (complete
                   (proof-with-checked-results
                       ((bad-failure (proof-proof-fact proof *l1-warrant-badge-failure* nil))
                        (witness (l1-recursive-witness-parts proof comparison test selector
                                                           bad-argument bad-failure))
                        (entries (car witness))
                        (count (+ count (cadr witness) (l1-warrant-entries-count entries)))
                        (fragments (cons source (append (l1-warrant-entries-sources entries)
                                                        (list (caddr witness))))))
                     (list count fragments "")))
                  (t (list count (list source) reason))))
         (proof (l1-warrant-remove-fact proof *l1-warrant-warrant-selection*)))
      (cons answer proof))))

(defun l1-warrant-warrant-cases-fragments (proof parts choices complete)
  (proof-with-checked-results
      ((parts (proof-list-of-length parts 3)))
    (let ((comparison (car parts))
          (test (cadr parts))
          (guard (caddr parts)))
      (proof-with-checked-results
          ((fixed (l1-warrant-fixed-failure proof comparison test guard))
           (lemma (l1-warrant-lemma *l1-warrant-badge-failure* (cadr fixed))))
        (let ((selector (l1-warrant-find-application-selector choices)))
          (if (not selector)
              (cons (list (car lemma) (list (cadr lemma)) "requires an application selector") proof)
            (let* ((guarded (not (eq guard :none)))
                   (reason (if guarded
                               "requires choice over guarded application failures"
                             "requires the matched-badge application equations")))
              (proof-with-checked-results
                  ((prelude (if guarded
                                (l1-warrant-guarded-entries proof comparison test)
                              (cons (list 0 "") proof)))
                   (proof (l1-warrant-put-fact (cdr prelude) *l1-warrant-badge-failure* (cadr fixed)))
                   (prelude (car prelude))
                   (bad-failure (proof-proof-fact proof *l1-warrant-badge-failure* nil))
                   (selected (l1-warrant-application-selection proof comparison test guard selector
                                                              (car fixed) bad-failure
                                                              *l1-warrant-left-function*
                                                              *l1-warrant-right-function*))
                   (bridge (l1-warrant-lemma *l1-warrant-warrant-selection* (cadr selected)))
                   (count (+ (car lemma) (car prelude) (car bridge)))
                   (source (concatenate 'string (cadr lemma) (cadr prelude) (cadr bridge)))
                   (result (if guarded
                               (cons (list count (list source) reason) proof)
                             (l1-warrant-warrant-cases-unguarded proof comparison test selector (car fixed)
                                                                 (car selected) (cadr selected)
                                                                 count source reason complete)))
                   (proof (l1-warrant-remove-fact (cdr result) *l1-warrant-badge-failure*)))
                (cons (car result) proof)))))))))

(defun l1-warrant-warrant-cases-with-proof (proof parts choices complete)
  (l1-warrant-materialize-result
   (l1-warrant-result-halves
    (l1-warrant-warrant-cases-fragments proof parts choices complete))))

(defun l1-warrant-warrant-cases (proof parts choices complete)
  (proof-with-checked-results ((result (l1-warrant-warrant-cases-with-proof proof parts choices complete)))
    (car result)))

(defun l1-warrant-warrant-logic (certificates)
  (let ((conditional (proof-ite *library-x* *library-y* *library-z*)))
    (proof-with-checked-results
        ((proof (l1-primitive-certificates-proof certificates))
         (excluded (proof-proof-excluded-middle proof *library-x*))
         (middle (l1-primitive-certificates-add certificates
                                                (proof-sym "SELF-EXCLUDED-MIDDLE" "ACL2") excluded))
         (proof (l1-primitive-certificates-proof (cdr middle)))
         (if-true (proof-proof-if-true proof conditional))
         (yes (l1-primitive-certificates-add (cdr middle) (proof-sym "SELF-IF-TRUE" "ACL2") if-true))
         (proof (l1-primitive-certificates-proof (cdr yes)))
         (if-false (proof-proof-if-false proof conditional))
         (no (l1-primitive-certificates-add (cdr yes) (proof-sym "SELF-IF-FALSE" "ACL2") if-false)))
      (cdr no))))

(defun l1-warrant-warrant-lemmas-fragments (proof data choices complete)
  (proof-with-checked-results ((parts (l1-warrant-warrant-parts data)))
    (if (not parts)
        (cons nil proof)
      (proof-with-checked-results
          ((certificates (l1-warrant-warrant-logic (l1-primitive-certificates-init proof)))
           (cases (l1-warrant-warrant-cases-fragments (l1-primitive-certificates-proof certificates)
                                                     parts choices complete)))
        (let* ((result (car cases))
               (entries (l1-primitive-certificates-entries certificates))
               (answer (list (+ (car result) (l1-warrant-entries-count entries))
                             (append (l1-warrant-entries-sources entries) (cadr result))
                             (caddr result)))
               (certificates (l1-primitive-certificates-with-proof certificates (cdr cases))))
          (proof-with-checked-results ((closed (l1-primitive-certificates-close certificates)))
            (cons answer (l1-primitive-certificates-proof closed))))))))

(defun l1-warrant-warrant-lemmas-with-proof (proof data choices complete)
  (l1-warrant-materialize-result
   (l1-warrant-result-halves
    (l1-warrant-warrant-lemmas-fragments proof data choices complete))))

(defun l1-warrant-warrant-lemmas (proof data choices complete)
  (proof-with-checked-results
      ((result (l1-warrant-warrant-lemmas-with-proof proof data choices complete)))
    (car result)))
