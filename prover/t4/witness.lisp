(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-witness-choice* (proof-sym "T4-SUPPLIED-CHOICE" "ACL2"))
(defconst *t4-witness-selector* (proof-sym "T4-COUNTEREXAMPLE" "ACL2"))
(defconst *t4-witness-predicate* (proof-sym "T4-CHOSEN-PREDICATE" "ACL2"))
(defconst *t4-witness-choice-definitions*
  (list *termination-return-last* *proof-not* *library-implies*
        (proof-cl "EQ") (proof-cl "EQL") (proof-cl "ATOM") (proof-cl "ENDP")))
(defconst *t4-witness-car* (proof-cl "CAR"))
(defconst *t4-witness-cdr* (proof-cl "CDR"))

(defun t4-witness-comparison-witness (comparison)
  (cadr comparison))

(defun t4-witness-comparison-parameters (comparison)
  (caddr comparison))

(defun t4-witness-comparison-argument (comparison)
  (cadddr comparison))

(defun t4-witness-comparison-counterexample (comparison)
  (nth 4 comparison))

(defun t4-witness-comparison-definition-name (comparison)
  (nth 5 comparison))

(defun t4-witness-comparison-necessity-name (comparison)
  (nth 6 comparison))

(defun t4-witness-comparison-application (comparison)
  (nth 7 comparison))

(defun t4-witness-choice-rule-name (rule)
  (cadr rule))

(defun t4-witness-choice-rule-parameters (rule)
  (caddr rule))

(defun t4-witness-choice-rule-argument (rule)
  (cadddr rule))

(defun t4-witness-choice-rule-counterexample (rule)
  (nth 4 rule))

(defun t4-witness-choice-rule-necessity-name (rule)
  (nth 5 rule))

(defun t4-witness-choice-rule-definition-name (rule)
  (nth 6 rule))

(defun t4-witness-step-term (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun t4-witness-need-at-least (items minimum)
  (let ((size (len items)))
    (cond ((integerp items) '(:failure "failure" ""))
          ((< size minimum) '(:failure "SearchMiss" ""))
          (t items))))

(defun t4-witness-comparison-read-application
    (witness definition-name necessity-name call application necessity)
  (proof-with-checked-results ((head (proof-term-at application 0)))
    (if (not (proof-compound head))
        nil
      (proof-with-checked-results ((application (t4-witness-need-at-least application 2)))
        (if (not (equal (cadr application) (cons witness (cdr call))))
            nil
          (proof-with-checked-results ((conclusion (proof-term-at necessity 2)))
            (if (not (equal conclusion (proof-neg call)))
                nil
              (let ((failure (cadr necessity)))
                (if (not (proof-is-call failure *proof-not*))
                    nil
                  (proof-with-checked-results ((formals (proof-term-at head 1)))
                    (cond ((or (null formals) (equal formals 0) (equal formals "")) nil)
                          (t (proof-with-checked-results
                                 ((argument (proof-term-at formals 0)))
                               (list :comparison witness (cdr call) argument failure
                                     definition-name necessity-name application))))))))))))))

(defun t4-witness-comparison-read (data)
  (proof-with-checked-results ((parts (proof-list-of-length data 2)))
    (let ((functions (car parts))
          (formulas (cadr parts)))
      (cond
       ((integerp functions) '(:failure "failure" ""))
       ((or (not (equal (len functions) 2))
            (not (proof-compound formulas))
            (not (equal (len formulas) 2)))
        nil)
       (t
        (proof-with-checked-results
            ((witness-spec (proof-list-of-length (car functions) 2))
             (predicate-spec (proof-list-of-length (cadr functions) 2))
             (definition-spec (proof-list-of-length (car formulas) 2))
             (necessity-spec (proof-list-of-length (cadr formulas) 2)))
          (let ((definition (cadr definition-spec))
                (necessity (cadr necessity-spec)))
            (if (or (not (equal (cadr witness-spec) (cadr predicate-spec)))
                    (not (proof-is-call definition *proof-equal*))
                    (not (proof-is-call necessity *library-implies*)))
                nil
              (proof-with-checked-results ((equation (proof-list-of-length definition 3)))
                (let ((call (cadr equation))
                      (application (caddr equation)))
                  (and (proof-is-call call (car predicate-spec))
                       (proof-compound application)
                       (t4-witness-comparison-read-application
                        (car witness-spec) (car definition-spec) (car necessity-spec)
                        call application necessity))))))))))))

(defun t4-witness-choice-rule-counterexample-proof (rule proof bindings)
  (let ((pairs (table-items bindings))
        (definition (t4-witness-choice-rule-definition-name rule)))
    (proof-with-checked-results
        ((step (proof-proof-fact proof (t4-witness-choice-rule-necessity-name rule) pairs)))
      (if (not definition)
          step
        (proof-with-checked-results
            ((value (proof-proof-fact proof definition pairs))
             (application (t4-witness-step-term value 2))
             (beta (proof-proof-beta proof application))
             (value (proof-proof-chain proof value (list beta)))
             (step (proof-proof-rewrite proof step value '(1 2 1))))
          (proof-proof-tidy proof step))))))

(defun t4-witness-available-choice (proof kind data)
  (cond
   ((equal kind "constrain")
    (proof-with-checked-results ((comparison (t4-witness-comparison-read data)))
      (cons (and comparison
                 (list :choicerule
                       (t4-witness-comparison-witness comparison)
                       (t4-witness-comparison-parameters comparison)
                       (t4-witness-comparison-argument comparison)
                       (t4-witness-comparison-counterexample comparison)
                       (t4-witness-comparison-necessity-name comparison)
                       (t4-witness-comparison-definition-name comparison)))
            proof)))
   ((equal kind "choose")
    (proof-with-checked-results ((parts (proof-list-of-length data 5)))
      (let ((name (car parts))
            (bound (cadr parts))
            (free (caddr parts))
            (predicate (cadddr parts))
            (strengthened (nth 4 parts)))
        (cond
         ((integerp bound) '(:failure "failure" ""))
         ((and (equal (len bound) 1) (equal strengthened *proof-nil*))
          (let ((parameters (if (equal free *proof-nil*) nil free)))
            (if (integerp parameters)
                '(:failure "failure" "")
              (let ((call (cons name parameters))
                    (argument (car bound)))
                (proof-with-checked-results
                    ((selected (proof-subst predicate (list (cons argument call)))))
                  (let ((facts (table-put (proof-proof-facts proof) name
                                            (list (list *library-implies* predicate selected)))))
                    (cons (list :choicerule name parameters argument predicate name nil)
                          (proof-proof-with-facts proof facts))))))))
         (t (cons nil proof))))))
   (t (cons nil proof))))

(mutual-recursion
 (defun t4-witness-variable-free-in (variable term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) (equal variable term))
         ((endp term) '(:failure "failure" ""))
         ((equal (car term) *proof-quote*) nil)
         (t (t4-witness-variable-free-in-arguments variable (cdr term)))))

 (defun t4-witness-variable-free-in-arguments (variable arguments)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (or (t4-witness-variable-free-in variable (car arguments))
         (t4-witness-variable-free-in-arguments variable (cdr arguments))))))

(mutual-recursion
 (defun t4-witness-match-counterexample (pattern term rule comparison bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (cond
    ((equal pattern (t4-witness-choice-rule-argument rule))
     (cons (equal term (t4-witness-comparison-argument comparison)) bindings))
    ((member-equal pattern (t4-witness-choice-rule-parameters rule))
     (proof-with-checked-results
         ((captured (t4-witness-variable-free-in
                     (t4-witness-comparison-argument comparison) term)))
       (if captured
           (cons nil bindings)
         (let ((entry (assoc-equal pattern bindings)))
           (if entry
               (cons (equal (cdr entry) term) bindings)
             (cons t (table-put bindings pattern term)))))))
    ((not (proof-compound pattern)) (cons (equal pattern term) bindings))
    ((endp pattern) '(:failure "failure" ""))
    ((equal (car pattern) *proof-quote*) (cons (equal pattern term) bindings))
    ((and (proof-compound term)
          (equal (len pattern) (len term))
          (equal (car pattern) (car term)))
     (t4-witness-match-counterexample-arguments
      (cdr pattern) (cdr term) rule comparison bindings))
    (t (cons nil bindings))))

 (defun t4-witness-match-counterexample-arguments (patterns terms rule comparison bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (endp patterns)
       (cons t bindings)
     (proof-with-checked-results
         ((matched (t4-witness-match-counterexample
                    (car patterns) (car terms) rule comparison bindings)))
       (if (car matched)
           (t4-witness-match-counterexample-arguments
            (cdr patterns) (cdr terms) rule comparison (cdr matched))
         matched)))))

(defun t4-witness-normal-form (proof term)
  (proof-with-checked-results
      ((equality (proof-proof-simplify proof term nil (list *termination-return-last*))))
    (if equality (t4-witness-step-term equality 2) term)))

(defun t4-witness-remove-definition (proof name)
  (proof-with-checked-results
      ((definitions (table-delete (proof-proof-definitions proof) name))
       (facts (table-delete (proof-proof-facts proof) name)))
    (proof-proof-with-kind
     (proof-make-proof facts definitions (proof-proof-primitives proof))
     (proof-proof-kind proof))))

(defun t4-witness-reduce-necessity (proof necessary index)
  (proof-with-checked-results
      ((term (t4-witness-step-term necessary index))
       (reduced (proof-proof-simplify proof term nil (list *termination-return-last*))))
    (if reduced (proof-proof-rewrite proof necessary reduced (list 1 index)) necessary)))

(defun t4-witness-align-necessity (proof necessary comparison)
  (proof-with-checked-results
      ((opening (proof-proof-simplify proof (t4-witness-comparison-counterexample comparison)
                                      nil (list *termination-return-last*))))
    (if opening
        (proof-with-checked-results ((reversed (proof-proof-symmetric proof opening)))
          (proof-proof-rewrite proof necessary reversed '(1 1)))
      necessary)))

(defun t4-witness-witness-entry (proof comparison chosen-argument necessary)
  (proof-with-checked-results
      ((application (t4-witness-need-at-least
                     (t4-witness-comparison-application comparison) 2)))
    (let* ((parameters (t4-witness-comparison-parameters comparison))
           (selector-call (cons *t4-witness-selector* parameters))
           (predicate-call (cons *t4-witness-predicate* parameters))
           (body (list* (car application) selector-call (cddr application)))
           (formals (or parameters *proof-nil*))
           (witness (t4-witness-comparison-witness comparison)))
      (proof-with-checked-results
          ((define-selector (proof-line "define" (list *proof-nil*
                                                      (list *t4-witness-selector* formals
                                                            chosen-argument))))
           (define-predicate (proof-line "define" (list *proof-nil*
                                                       (list *t4-witness-predicate* formals
                                                             body))))
           (proof (proof-proof-add-definition
                   proof *t4-witness-selector* parameters chosen-argument))
           (proof (proof-proof-add-definition proof *t4-witness-predicate* parameters body))
           (value (proof-proof-unfold proof predicate-call))
           (beta (proof-proof-beta proof body))
           (expanded (proof-proof-chain proof value (list beta)))
           (selector-definition (proof-proof-unfold proof selector-call))
           (expanded (proof-proof-rewrite-first proof expanded selector-definition))
           (selected (t4-witness-step-term expanded 2))
           (reduced (proof-proof-simplify proof selected nil (list *termination-return-last*)))
           (expanded (proof-proof-chain proof expanded (list reduced)))
           (necessary (t4-witness-reduce-necessity proof necessary 1))
           (necessary (t4-witness-reduce-necessity proof necessary 2))
           (necessary (t4-witness-align-necessity proof necessary comparison))
           (reversed (proof-proof-symmetric proof expanded))
           (needed (proof-proof-rewrite proof necessary reversed '(1 2 1)))
           (needed (proof-proof-tidy proof needed))
           (entry (proof-proof-entry "witness" witness
                                     (list witness *t4-witness-selector* *t4-witness-predicate*)
                                     (list value needed)))
           (proof (t4-witness-remove-definition proof *t4-witness-selector*))
           (proof (t4-witness-remove-definition proof *t4-witness-predicate*)))
        (let ((counts (caddr entry)))
          (cons (list (+ (car counts) (cadr counts))
                      (concatenate 'string define-selector define-predicate (cadddr entry)))
                proof))))))

(defun t4-witness-obvious-choice-independent (proof comparison failure opening)
  (let ((implication (list *library-implies* failure failure))
        (definitions (list *library-implies*)))
    (proof-with-checked-results
        ((holds (proof-proof-assume proof failure t))
         (yes (proof-proof-prove proof implication (list holds) definitions))
         (denied (proof-proof-assume proof failure nil))
         (no (proof-proof-prove proof implication (list denied) definitions))
         (necessary (proof-proof-cases proof failure yes no)))
      (if (not opening)
          (list *proof-false* necessary)
        (proof-with-checked-results
            ((selected (proof-proof-instantiate
                        proof opening
                        (list (list (t4-witness-comparison-argument comparison)
                                    *proof-false*))))
             (reversed (proof-proof-symmetric proof selected))
             (alignment (proof-proof-chain proof opening (list reversed)))
             (necessary (proof-proof-rewrite proof necessary alignment '(1 2)))
             (necessary (proof-proof-tidy proof necessary)))
          (list *proof-false* necessary))))))

(defun t4-witness-proof-miss-p (value)
  (and (failure-p value) (equal (cadr value) "value")))

(defun t4-witness-obvious-choice-arguments (arguments proof variable failure always-holds)
  (if (endp arguments)
      nil
    (let ((argument (car arguments))
          (definitions (list *library-implies*)))
      (proof-with-checked-results
          ((selected-failure (proof-subst failure (list (cons variable argument)))))
        (let ((implication (list *library-implies* failure selected-failure)))
          (if always-holds
              (proof-with-checked-results
                  ((consequence (proof-proof-prove proof implication
                                                  (list always-holds) definitions)))
                (list argument consequence))
            (let ((fixed-failure (proof-proof-prove proof selected-failure nil
                                                    *t4-witness-choice-definitions*)))
              (if (t4-witness-proof-miss-p fixed-failure)
                  (t4-witness-obvious-choice-arguments
                   (cdr arguments) proof variable failure always-holds)
                (proof-with-checked-results
                    ((fixed-failure fixed-failure)
                     (holds (proof-proof-assume proof failure t))
                     (yes (proof-proof-prove proof implication
                                            (list holds fixed-failure) definitions))
                     (denied (proof-proof-assume proof failure nil))
                     (no (proof-proof-prove proof implication (list denied) definitions))
                     (consequence (proof-proof-cases proof failure yes no)))
                  (list argument consequence))))))))))

(defun t4-witness-obvious-choice (proof comparison)
  (let ((failure (t4-witness-comparison-counterexample comparison))
        (variable (t4-witness-comparison-argument comparison)))
    (proof-with-checked-results
        ((opening (proof-proof-simplify proof failure nil *t4-witness-choice-definitions*))
         (value (if opening (t4-witness-step-term opening 2) failure))
         (dependent (t4-witness-variable-free-in variable value)))
      (if (not dependent)
          (t4-witness-obvious-choice-independent proof comparison failure opening)
        (let ((always-holds (proof-proof-prove proof (proof-neg failure) nil
                                               *t4-witness-choice-definitions*))
              (arguments (list *proof-false* *proof-true* *proof-zero*)))
          (if (t4-witness-proof-miss-p always-holds)
              (t4-witness-obvious-choice-arguments arguments proof variable failure nil)
            (proof-with-checked-results ((always-holds always-holds))
              (t4-witness-obvious-choice-arguments
               arguments proof variable failure always-holds))))))))

(defun t4-witness-choice-actuals (parameters bindings)
  (if (endp parameters)
      nil
    (cons (table-get bindings (car parameters) *proof-false*)
          (t4-witness-choice-actuals (cdr parameters) bindings))))

(defun t4-witness-choice-bindings (parameters actuals bindings)
  (if (endp parameters)
      bindings
    (t4-witness-choice-bindings
     (cdr parameters) (cdr actuals)
     (table-put bindings (car parameters) (car actuals)))))

(defun t4-witness-selector-choices (choices proof comparison target)
  (if (endp choices)
      (t4-witness-obvious-choice proof comparison)
    (let ((choice (car choices)))
      (proof-with-checked-results
          ((pattern (t4-witness-normal-form proof (t4-witness-choice-rule-counterexample choice)))
           (matched (t4-witness-match-counterexample pattern target choice comparison nil)))
        (if (not (car matched))
            (t4-witness-selector-choices (cdr choices) proof comparison target)
          (let* ((parameters (t4-witness-choice-rule-parameters choice))
                 (actuals (t4-witness-choice-actuals parameters (cdr matched)))
                 (bindings (t4-witness-choice-bindings parameters actuals nil))
                 (bindings (table-put bindings (t4-witness-choice-rule-argument choice)
                                        (t4-witness-comparison-argument comparison))))
            (proof-with-checked-results
                ((necessary (t4-witness-choice-rule-counterexample-proof choice proof bindings)))
              (list (cons (t4-witness-choice-rule-name choice) actuals) necessary))))))))

(defun t4-witness-selector (proof comparison choices)
  (proof-with-checked-results
      ((target (t4-witness-normal-form proof (t4-witness-comparison-counterexample comparison))))
    (t4-witness-selector-choices choices proof comparison target)))

(defun t4-witness-argument-shape-collect (n step proof argument values pairs)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t4-witness-argument-shape-collect")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (cond
       ((proof-is-call literal *proof-if*)
        (proof-with-checked-results ((otherwise (proof-term-at literal 3)))
          (if (not (equal otherwise *proof-false*))
              (list values pairs)
            (proof-with-checked-results
                ((parts (proof-proof-conjunct proof step))
                 (collected (t4-witness-argument-shape-collect
                             (1- n) (car parts) proof argument values pairs)))
              (t4-witness-argument-shape-collect
               (1- n) (cadr parts) proof argument (car collected) (cadr collected))))))
       ((proof-is-call literal *proof-consp*)
        (proof-with-checked-results ((term (proof-term-at literal 1)))
          (list values (table-put pairs term step))))
       ((proof-is-call literal *proof-equal*)
        (proof-with-checked-results
            ((sides (proof-list-of-length (cdr literal) 2))
             (right-free (t4-witness-variable-free-in argument (cadr sides))))
          (let ((values (if right-free values (table-put values (car sides) step))))
            (proof-with-checked-results ((left-free (t4-witness-variable-free-in argument
                                                                               (car sides))))
              (if left-free
                  (list values pairs)
                (proof-with-checked-results ((reversed (proof-proof-symmetric proof step)))
                  (list (table-put values (cadr sides) reversed) pairs)))))))
       (t (list values pairs))))))

(defun t4-witness-argument-shape-recover (n term proof values pairs)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t4-witness-argument-shape-recover")
    (let ((value (assoc-equal term values))
          (pair (assoc-equal term pairs)))
      (cond
       (value (cdr value))
       ((not pair) nil)
       (t
        (proof-with-checked-results
            ((head (t4-witness-argument-shape-recover
                    (1- n) (list *t4-witness-car* term) proof values pairs))
             (tail (t4-witness-argument-shape-recover
                    (1- n) (list *t4-witness-cdr* term) proof values pairs)))
          (if (or (not head) (not tail))
              nil
            (proof-with-checked-results
                ((constructor (proof-proof-fact proof (proof-sym "CAR-CDR-ELIM" "ACL2")
                                                (list (list *library-x* term))))
                 (constructor (proof-proof-modus-ponens proof constructor (cdr pair)))
                 (made (proof-proof-symmetric proof constructor))
                 (made (proof-proof-rewrite proof made head '(1 2 1)))
                 (made (proof-proof-rewrite proof made tail '(1 2 2))))
              (proof-proof-tidy proof made)))))))))

(defun t4-witness-argument-shape (proof argument guard)
  (proof-with-checked-results
      ((collected (t4-witness-argument-shape-collect 1000000 guard proof argument nil nil)))
    (t4-witness-argument-shape-recover 1000000 argument proof (car collected) (cadr collected))))

(defun t4-witness-forced-argument-guard (proof variable failure test)
  (proof-with-checked-results
      ((guard (proof-term-at test 1))
       (failure-holds (proof-proof-assume proof failure t))
       (guard-denied (proof-proof-assume proof guard nil))
       (opening (if (proof-is-call test *library-implies*)
                    (proof-proof-unfold proof test)
                  (proof-proof-reflexive proof test)))
       (body (t4-witness-step-term opening 2))
       (selected (proof-proof-select proof body guard-denied))
       (empty (proof-proof-chain proof opening (list selected)))
       (holds-vacuously (proof-proof-true-from-eq proof empty))
       (given (proof-proof-cut proof holds-vacuously failure-holds))
       (given (proof-proof-front proof given guard))
       (fixed (t4-witness-argument-shape proof variable given)))
    (if (not fixed)
        nil
      (proof-with-checked-results
          ((specialized (proof-proof-rewrite-first proof failure-holds fixed))
           (conclusion (proof-step-first specialized))
           (equation (proof-proof-unfold proof (list *library-implies* failure conclusion)))
           (body (t4-witness-step-term equation 2))
           (body-yes (proof-proof-select proof body failure-holds))
           (body-consequence (proof-term-at body 2))
           (body-consequence (proof-proof-select proof body-consequence specialized))
           (yes (proof-proof-chain proof equation (list body-yes body-consequence)))
           (body-no (proof-proof-if-false proof body))
           (no (proof-proof-chain proof equation (list body-no)))
           (value (t4-witness-step-term fixed 2))
           (yes (proof-proof-true-from-eq proof yes))
           (no (proof-proof-true-from-eq proof no))
           (necessity (proof-proof-cases proof failure yes no)))
        (list value necessity)))))

(defun t4-witness-forced-argument (proof comparison)
  (let ((failure (t4-witness-comparison-counterexample comparison))
        (variable (t4-witness-comparison-argument comparison)))
    (and (proof-is-call failure *proof-not*)
      (proof-with-checked-results ((test (proof-term-at failure 1)))
        (cond
         ((proof-is-call test *library-implies*)
          (t4-witness-forced-argument-guard proof variable failure test))
         ((proof-is-call test *proof-if*)
          (proof-with-checked-results ((no (proof-term-at test 3)))
            (and (equal no *proof-true*)
              (t4-witness-forced-argument-guard proof variable failure test))))
         (t nil))))))

(mutual-recursion
 (defun t4-witness-branch-selectors-tests (term variable)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) nil)
    ((endp term) '(:failure "failure" ""))
    ((member-equal (car term) (list *proof-if* *library-implies*))
     (proof-with-checked-results
         ((test (proof-term-at term 1))
          (dependent (t4-witness-variable-free-in variable test))
          (rest (t4-witness-branch-selectors-tests-arguments (cdr term) variable)))
       (if dependent rest (cons test rest))))
    (t (t4-witness-branch-selectors-tests-arguments (cdr term) variable))))

 (defun t4-witness-branch-selectors-tests-arguments (arguments variable)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (proof-with-checked-results
         ((tests (t4-witness-branch-selectors-tests (car arguments) variable))
          (rest (t4-witness-branch-selectors-tests-arguments (cdr arguments) variable)))
       (append tests rest)))))

(defun t4-witness-branch-reduction-opening (term premise proof)
  (proof-with-checked-results
      ((opened (and (or (proof-is-call term *library-implies*)
                        (proof-is-call term *proof-not*))
                    (proof-proof-unfold proof term)))
       (body (if opened (t4-witness-step-term opened 2) term)))
    (if (or (not (proof-compound body)) (proof-is-call body *proof-quote*))
        (list :done opened)
      (proof-with-checked-results
          ((selected
            (and (proof-is-call body *proof-if*)
                 (proof-with-checked-results
                     ((literal (proof-step-first premise))
                      (test (proof-term-at body 1)))
                   (and (or (equal literal test) (equal literal (proof-neg test)))
                        (proof-proof-select proof body premise))))))
        (if selected
            (proof-with-checked-results
                ((equation (if opened (proof-proof-chain proof opened (list selected)) selected)))
              (list :done equation))
          (list :arguments (cdr body) opened))))))

(defun t4-witness-branch-reduction-finish (equation premise proof)
  (proof-with-checked-results ((equation equation))
    (and equation
         (proof-with-checked-results
             ((value (t4-witness-step-term equation 2))
              (reduced (proof-proof-simplify proof value (list premise)
                                             *t4-witness-choice-definitions*)))
           (proof-proof-chain proof equation (list reduced))))))

(defun t4-witness-branch-rewrite-argument (reduced equation index term proof)
  (proof-with-checked-results ((reduced reduced))
    (if reduced
        (proof-with-checked-results ((base (or equation (proof-proof-reflexive proof term))))
          (proof-proof-rewrite proof base reduced (list 1 2 index)))
      equation)))

(mutual-recursion
 (defun t4-witness-branch-selectors-reduce-branch (n term premise proof)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "t4-witness-branch-selectors-reduce-branch")
     (t4-witness-branch-reduce-body
      (1- n) (t4-witness-branch-reduction-opening term premise proof) term premise proof)))

 (defun t4-witness-branch-reduce-body (n opening term premise proof)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t4-witness-branch-reduce-body"))
    ((failure-p opening) opening)
    ((eq (car opening) :done) (cadr opening))
    (t (t4-witness-branch-reduction-finish
        (t4-witness-branch-reduce-arguments
         (1- n) (cadr opening) 1 (caddr opening) term premise proof)
        premise proof))))

 (defun t4-witness-branch-reduce-arguments (n arguments index equation term premise proof)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t4-witness-branch-reduce-arguments"))
    ((failure-p equation) equation)
    ((endp arguments) equation)
    (t
     (t4-witness-branch-reduce-arguments
      (1- n) (cdr arguments) (1+ index)
      (t4-witness-branch-rewrite-argument
       (t4-witness-branch-selectors-reduce-branch (1- n) (car arguments) premise proof)
       equation index term proof)
      term premise proof)))))

(defun t4-witness-branch-arm (proof comparison choices test positive)
  (let ((failure (t4-witness-comparison-counterexample comparison))
        (variable (t4-witness-comparison-argument comparison)))
    (proof-with-checked-results
        ((premise (proof-proof-assume proof test positive))
         (reduction (t4-witness-branch-selectors-reduce-branch 1000000 failure premise proof)))
      (and reduction
        (proof-with-checked-results
            ((reduced-failure (t4-witness-step-term reduction 2))
             (problem (update-nth 4 reduced-failure comparison))
             (solved (t4-witness-selector proof problem choices)))
          (and solved
            (let ((argument (car solved))
                  (consequence (cadr solved)))
              (proof-with-checked-results
                  ((specialized (proof-proof-instantiate
                                 proof reduction (list (list variable argument))))
                   (literal (proof-step-first consequence))
                   (specialized-failure (t4-witness-step-term specialized 2)))
                (and (equal (cdr literal) (list reduced-failure specialized-failure))
                  (proof-with-checked-results
                      ((reversed (proof-proof-symmetric proof reduction))
                       (consequence (proof-proof-rewrite proof consequence reversed '(1 1)))
                       (reversed (proof-proof-symmetric proof specialized))
                       (consequence (proof-proof-rewrite proof consequence reversed '(1 2))))
                    (list argument consequence premise)))))))))))

(defun t4-witness-branch-align (proof argument arm template variable)
  (proof-with-checked-results
      ((selected (proof-proof-select proof argument (caddr arm)))
       (reversed (proof-proof-symmetric proof selected)))
    (proof-proof-rewrite-result proof (cadr arm) reversed template variable)))

(defun t4-witness-branch-join (proof comparison test positive negative)
  (let ((argument (proof-ite test (car positive) (car negative)))
        (template (list *library-implies* *proof-true*
                        (t4-witness-comparison-counterexample comparison)))
        (variable (t4-witness-comparison-argument comparison)))
    (proof-with-checked-results
        ((yes (t4-witness-branch-align proof argument positive template variable))
         (no (t4-witness-branch-align proof argument negative template variable))
         (necessary (proof-proof-cases proof test yes no)))
      (list argument necessary))))

(defun t4-witness-branch-try-tests (tests proof comparison choices)
  (if (endp tests)
      nil
    (let ((test (car tests)))
      (proof-with-checked-results
          ((positive (t4-witness-branch-arm proof comparison choices test t))
           (negative (and positive (t4-witness-branch-arm proof comparison choices test nil))))
        (if negative
            (t4-witness-branch-join proof comparison test positive negative)
          (t4-witness-branch-try-tests (cdr tests) proof comparison choices))))))

(defun t4-witness-branch-selectors (proof comparison choices)
  (proof-with-checked-results
      ((tests (t4-witness-branch-selectors-tests
               (t4-witness-comparison-counterexample comparison)
               (t4-witness-comparison-argument comparison))))
    (t4-witness-branch-try-tests (seq-slice (proof-unique tests) 0 4)
                                proof comparison choices)))

(defun t4-witness-prove-witness (proof data choices)
  (proof-with-checked-results ((comparison (t4-witness-comparison-read data)))
    (if (not comparison)
        (cons nil proof)
      (proof-with-checked-results
          ((direct (or (t4-witness-selector proof comparison choices)
                       (t4-witness-forced-argument proof comparison)
                       (t4-witness-branch-selectors proof comparison choices))))
        (if direct
            (t4-witness-witness-entry proof comparison (car direct) (cadr direct))
          (cons nil proof))))))

(defun t4-witness-counterexample-choice (proof constraint)
  (proof-with-checked-results ((problem (t4-witness-comparison-read constraint)))
    (if (not problem)
        '(:failure "failure" "")
      (let ((data (list *t4-witness-choice*
                        (list (t4-witness-comparison-argument problem))
                        (or (t4-witness-comparison-parameters problem) *proof-nil*)
                        (t4-witness-comparison-counterexample problem)
                        *proof-nil*)))
        (proof-with-checked-results
            ((registration (t4-witness-available-choice proof "choose" data))
             (proved (t4-witness-prove-witness (cdr registration) constraint
                                              (list (car registration)))))
          (if (not (car proved))
              '(:failure "failure" "")
            (proof-with-checked-results
                ((proof (cdr proved))
                 (facts (table-delete (proof-proof-facts proof) *t4-witness-choice*))
                 (choice (proof-line "choose" data)))
              (cons (list choice (cadar proved)) (proof-proof-with-facts proof facts)))))))))

(mutual-recursion
 (defun t4-witness-dependencies-collect (n term called)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t4-witness-dependencies-collect"))
    ((not (proof-compound term)) called)
    ((endp term) '(:failure "failure" ""))
    ((equal (car term) *proof-quote*) called)
    ((equal (car term) *termination-return-last*)
     (t4-witness-dependencies-collect (1- n) (car (last term)) called))
    (t
     (let ((head (car term)))
       (proof-with-checked-results
           ((called
             (if (proof-compound head)
                 (proof-with-checked-results ((body (proof-term-at head 2)))
                   (t4-witness-dependencies-collect (1- n) body called))
               (add-to-set-equal head called))))
         (t4-witness-dependencies-arguments (1- n) (cdr term) called))))))

 (defun t4-witness-dependencies-arguments (n arguments called)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "t4-witness-dependencies-arguments"))
    ((endp arguments) called)
    (t
     (proof-with-checked-results
         ((called (t4-witness-dependencies-collect (1- n) (car arguments) called)))
       (t4-witness-dependencies-arguments (1- n) (cdr arguments) called))))))

; The comparison order for a set is the order of its members' S-expression text.
(mutual-recursion
 (defun t4-witness-dependency-text (value)
   (declare (xargs :measure (1+ (* 2 (acl2-count value)))))
   (cond
    ((null value) "()")
    ((eq value t) "t")
    ((integerp value) (decimal-text value))
    ((rationalp value) (concatenate 'string (decimal-text (numerator value)) "/"
                                    (decimal-text (denominator value))))
    ((stringp value)
     (concatenate 'string "\"" (text-replace (text-replace value "\\" "\\\\") "\"" "\\\"") "\""))
    ((consp value)
     (concatenate 'string "("
                  (text-join " " (t4-witness-dependency-text-items value)) ")"))
    (t "nil")))

 (defun t4-witness-dependency-text-items (items)
   (declare (xargs :measure (* 2 (acl2-count items))))
   (if (endp items)
       nil
     (cons (t4-witness-dependency-text (car items))
           (t4-witness-dependency-text-items (cdr items))))))

(defun t4-witness-dependency-sort-keys (called)
  (if (endp called)
      nil
    (cons (list (t4-witness-dependency-text (car called)) (car called))
          (t4-witness-dependency-sort-keys (cdr called)))))

(defun t4-witness-dependency-sort-values (entries)
  (if (endp entries)
      nil
    (cons (cadar entries) (t4-witness-dependency-sort-values (cdr entries)))))

(defun t4-witness-dependencies (term)
  (proof-with-checked-results ((called (t4-witness-dependencies-collect 1000000 term nil)))
    (t4-witness-dependency-sort-values (seq-sorted (t4-witness-dependency-sort-keys called)))))

(defun t4-witness-affected-definitions-p (definitions affected)
  (if (endp definitions)
      nil
    (proof-with-checked-results
        ((definition (proof-list-of-length (car definitions) 3))
         (calls (t4-witness-dependencies (caddr definition))))
      (or (intersectp-equal calls affected)
          (t4-witness-affected-definitions-p (cdr definitions) affected)))))

(defun t4-witness-affected-definition-names (definitions affected)
  (if (endp definitions)
      affected
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (t4-witness-affected-definition-names (cdr definitions)
                                           (add-to-set-equal (car definition) affected)))))

(defun t4-witness-affected-formulas (formulas index affected)
  (if (endp formulas)
      nil
    (proof-with-checked-results
        ((formula (proof-list-of-length (car formulas) 2))
         (calls (t4-witness-dependencies (cadr formula)))
         (rest (t4-witness-affected-formulas (cdr formulas) index affected)))
      (if (intersectp-equal calls affected)
          (cons (list index (car formula)) rest)
        rest))))

(defun t4-witness-affected-statement (kind data index affected)
  (cond
   ((equal kind "define")
    (if (integerp data)
        '(:failure "failure" "")
      (proof-with-checked-results
          ((dependent (t4-witness-affected-definitions-p (cdr data) affected))
           (affected (if dependent
                         (t4-witness-affected-definition-names (cdr data) affected)
                       affected)))
        (cons nil affected))))
   ((equal kind "constrain")
    (proof-with-checked-results
        ((formulas (proof-term-at data 1))
         (hits (and (proof-compound formulas)
                    (t4-witness-affected-formulas formulas index affected))))
      (cons hits affected)))
   ((member-equal kind '("theorem" "axiom"))
    (proof-with-checked-results
        ((hits (t4-witness-affected-formulas (list data) index affected)))
      (cons hits affected)))
   ((equal kind "choose")
    (proof-with-checked-results
        ((name (proof-term-at data 0))
         (predicate (proof-term-at data 3))
         (calls (t4-witness-dependencies predicate))
         (affected (if (intersectp-equal calls affected)
                       (add-to-set-equal name affected)
                     affected))
         (hits (t4-witness-affected-formulas (list (list name predicate)) index affected)))
      (cons hits affected)))
   (t (cons nil affected))))

(defun t4-witness-affected-constraints-prefix (statements before index affected)
  (if (endp statements)
      nil
    (proof-with-checked-results ((statement (proof-list-of-length (car statements) 3)))
      (and (< index before)
        (proof-with-checked-results
            ((result (t4-witness-affected-statement (cadr statement) (caddr statement)
                                                   index affected))
             (rest (t4-witness-affected-constraints-prefix (cdr statements) before
                                                          (1+ index) (cdr result))))
          (append (car result) rest))))))

(defun t4-witness-affected-constraints (statements before functions)
  (t4-witness-affected-constraints-prefix statements before 1 (proof-unique functions)))
