(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-witness-choice* (proof-sym "L1-SUPPLIED-CHOICE" "ACL2"))
(defconst *l1-witness-selector* (proof-sym "L1-COUNTEREXAMPLE" "ACL2"))
(defconst *l1-witness-predicate* (proof-sym "L1-CHOSEN-PREDICATE" "ACL2"))
(defconst *l1-witness-normal-definitions* (list *termination-return-last*))
(defconst *l1-witness-choice-definitions*
  (list *termination-return-last* *proof-not* *library-implies*
        (proof-cl "EQ") (proof-cl "EQL") (proof-cl "ATOM") (proof-cl "ENDP")))

(defun l1-witness-make-comparison
    (witness parameters argument counterexample definition-name necessity-name application)
  (list :comparison witness parameters argument counterexample
        definition-name necessity-name application))

(defun l1-witness-comparison-witness (comparison)
  (nth 1 comparison))

(defun l1-witness-comparison-parameters (comparison)
  (nth 2 comparison))

(defun l1-witness-comparison-argument (comparison)
  (nth 3 comparison))

(defun l1-witness-comparison-counterexample (comparison)
  (nth 4 comparison))

(defun l1-witness-comparison-definition-name (comparison)
  (nth 5 comparison))

(defun l1-witness-comparison-necessity-name (comparison)
  (nth 6 comparison))

(defun l1-witness-comparison-application (comparison)
  (nth 7 comparison))

(defun l1-witness-make-choice-rule
    (name parameters argument counterexample necessity-name definition-name)
  (list :choicerule name parameters argument counterexample necessity-name definition-name))

(defun l1-witness-choice-rule-name (rule)
  (nth 1 rule))

(defun l1-witness-choice-rule-parameters (rule)
  (nth 2 rule))

(defun l1-witness-choice-rule-argument (rule)
  (nth 3 rule))

(defun l1-witness-choice-rule-counterexample (rule)
  (nth 4 rule))

(defun l1-witness-choice-rule-necessity-name (rule)
  (nth 5 rule))

(defun l1-witness-choice-rule-definition-name (rule)
  (nth 6 rule))

(defun l1-witness-step-term (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun l1-witness-need-at-least (items minimum)
  (if (or (integerp items) (< (len items) minimum))
      '(:failure "failure" "")
    items))

(defun l1-witness-comparison-atomic-parameters-p (parameters)
  (if (endp parameters)
      t
    (and (not (proof-compound (car parameters)))
         (l1-witness-comparison-atomic-parameters-p (cdr parameters)))))

(defun l1-witness-comparison-read-formals
    (witness parameters arity definition-name necessity-name application head failure)
  (proof-with-checked-results ((formals (proof-term-at head 1)))
    (let ((actuals (cddr application)))
      (and (proof-compound formals)
           (subsetp-equal actuals parameters)
           (subsetp-equal parameters actuals)
           (equal (len actuals) arity)
           (equal (len formals) (1+ arity))
           (not (member-equal (car formals) parameters))
           (l1-witness-comparison-atomic-parameters-p parameters)
           (equal (len (proof-unique parameters)) arity)
           (l1-witness-make-comparison
            witness parameters (car formals) failure definition-name necessity-name
            application)))))

(defun l1-witness-comparison-read-application
    (witness arity call application definition-name necessity-name necessity)
  (proof-with-checked-results ((head (proof-term-at application 0)))
    (and (proof-compound head)
         (proof-with-checked-results
             ((application (l1-witness-need-at-least application 2)))
           (let ((parameters (cdr call)))
             (and (equal (cadr application) (cons witness parameters))
                  (proof-with-checked-results ((conclusion (proof-term-at necessity 2)))
                    (let ((failure (cadr necessity)))
                      (and (equal conclusion (proof-neg call))
                           (proof-is-call failure *proof-not*)
                           (l1-witness-comparison-read-formals
                            witness parameters arity definition-name necessity-name
                            application head failure))))))))))

(defun l1-witness-comparison-read (data)
  (proof-with-checked-results ((parts (proof-list-of-length data 2)))
    (let ((functions (car parts))
          (formulas (cadr parts)))
      (cond
       ((integerp functions)
        '(:failure "failure" ""))
       ((or (not (equal (len functions) 2))
            (not (proof-compound formulas))
            (not (equal (len formulas) 2)))
        nil)
       (t (proof-with-checked-results
              ((witness-spec (proof-list-of-length (car functions) 2))
               (predicate-spec (proof-list-of-length (cadr functions) 2))
               (definition-spec (proof-list-of-length (car formulas) 2))
               (necessity-spec (proof-list-of-length (cadr formulas) 2)))
            (let ((arity (cadr witness-spec))
                  (definition (cadr definition-spec))
                  (necessity (cadr necessity-spec)))
              (and (equal arity (cadr predicate-spec))
                   (proof-is-call definition *proof-equal*)
                   (proof-is-call necessity *library-implies*)
                   (proof-with-checked-results
                       ((equation (proof-list-of-length definition 3)))
                     (let ((call (cadr equation))
                           (application (caddr equation)))
                       (and (proof-is-call call (car predicate-spec))
                            (equal (len call) (1+ arity))
                            (proof-compound application)
                            (l1-witness-comparison-read-application
                             (car witness-spec) arity call application
                             (car definition-spec) (car necessity-spec) necessity))))))))))))

(defun l1-witness-choice-rule-counterexample-proof (rule proof bindings)
  (let ((pairs (table-items bindings))
        (definition (l1-witness-choice-rule-definition-name rule)))
    (proof-with-checked-results
        ((step (proof-proof-fact proof (l1-witness-choice-rule-necessity-name rule) pairs)))
      (if (not definition)
          step
        (proof-with-checked-results
            ((value (proof-proof-fact proof definition pairs))
             (application (l1-witness-step-term value 2))
             (beta (proof-proof-beta proof application))
             (value (proof-proof-chain proof value (list beta)))
             (step (proof-proof-rewrite proof step value '(1 2 1))))
          (proof-proof-tidy proof step))))))

(defun l1-witness-available-choice (proof kind data)
  (cond
   ((equal kind "constrain")
    (proof-with-checked-results ((comparison (l1-witness-comparison-read data)))
      (cons (and comparison
                 (l1-witness-make-choice-rule
                  (l1-witness-comparison-witness comparison)
                  (l1-witness-comparison-parameters comparison)
                  (l1-witness-comparison-argument comparison)
                  (l1-witness-comparison-counterexample comparison)
                  (l1-witness-comparison-necessity-name comparison)
                  (l1-witness-comparison-definition-name comparison)))
            proof)))
   ((equal kind "choose")
    (proof-with-checked-results ((parts (proof-list-of-length data 5)))
      (let ((name (car parts))
            (bound (cadr parts))
            (free (caddr parts))
            (predicate (cadddr parts))
            (strengthened (nth 4 parts)))
        (cond
         ((integerp bound)
          '(:failure "failure" ""))
         ((and (equal (len bound) 1) (equal strengthened *proof-nil*))
          (let ((parameters (if (equal free *proof-nil*) nil free))
                (argument (car bound)))
            (if (integerp parameters)
                '(:failure "failure" "")
              (proof-with-checked-results
                  ((selected (proof-subst predicate
                                          (list (cons argument (cons name parameters))))))
                (let ((facts (table-put (proof-proof-facts proof) name
                                          (list (list *library-implies* predicate selected)))))
                  (cons (l1-witness-make-choice-rule name parameters argument predicate
                                                     name nil)
                        (proof-proof-with-facts proof facts)))))))
         (t (cons nil proof))))))
   (t (cons nil proof))))

(defun l1-witness-admit-definitions (proof definitions)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      proof
    (proof-with-checked-results
        ((definition (proof-list-of-length (car definitions) 3))
         (proof (proof-proof-add-definition proof (car definition)
                                            (cadr definition) (caddr definition))))
      (l1-witness-admit-definitions proof (cdr definitions)))))

(defun l1-witness-admit-formulas (proof formulas)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      proof
    (proof-with-checked-results ((formula (proof-list-of-length (car formulas) 2)))
      (let ((facts (table-put (proof-proof-facts proof) (car formula) (cdr formula))))
        (l1-witness-admit-formulas (proof-proof-with-facts proof facts) (cdr formulas))))))

(defun l1-witness-admit (proof kind data)
  (proof-with-checked-results
      ((proof
        (cond ((equal kind "define")
               (if (integerp data)
                   '(:failure "failure" "")
                 (l1-witness-admit-definitions proof (cdr data))))
              ((member-equal kind '("theorem" "axiom"))
               (l1-witness-admit-formulas proof (list data)))
              ((equal kind "constrain")
               (proof-with-checked-results ((formulas (proof-term-at data 1)))
                 (if (proof-compound formulas)
                     (l1-witness-admit-formulas proof formulas)
                   proof)))
              (t proof))))
    (l1-witness-available-choice proof kind data)))

(defun l1-witness-admitted-fact-names (kind data choice)
  (cond ((equal kind "define") (strip-cars (cdr data)))
        ((member-equal kind '("theorem" "axiom")) (list (car data)))
        ((equal kind "constrain")
         (and (proof-compound (cadr data)) (strip-cars (cadr data))))
        ((and (equal kind "choose") choice)
         (list (l1-witness-choice-rule-name choice)))
        (t nil)))

(mutual-recursion
 (defun l1-witness-match-counterexample (pattern term rule comparison bindings)
   (declare (xargs :measure (acl2-count pattern)))
   (cond
    ((equal pattern (l1-witness-choice-rule-argument rule))
     (cons (equal term (l1-witness-comparison-argument comparison)) bindings))
    ((member-equal pattern (l1-witness-choice-rule-parameters rule))
     (proof-with-checked-results
         ((captured (l1-finite-choice-variable-free-in
                     (l1-witness-comparison-argument comparison) term)))
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
     (l1-witness-match-counterexample-arguments
      (cdr pattern) (cdr term) rule comparison bindings))
    (t (cons nil bindings))))

 (defun l1-witness-match-counterexample-arguments (patterns terms rule comparison bindings)
   (declare (xargs :measure (acl2-count patterns)))
   (if (endp patterns)
       (cons t bindings)
     (proof-with-checked-results
         ((matched (l1-witness-match-counterexample
                    (car patterns) (car terms) rule comparison bindings)))
       (if (car matched)
           (l1-witness-match-counterexample-arguments
            (cdr patterns) (cdr terms) rule comparison (cdr matched))
         matched)))))

(defun l1-witness-normal-form (proof term)
  (proof-with-checked-results
      ((equality (l1-application-proof-simplify proof term nil *l1-witness-normal-definitions*)))
    (if equality (l1-witness-step-term equality 2) term)))

(defun l1-witness-reduce-necessity (proof necessary index)
  (proof-with-checked-results
      ((term (l1-witness-step-term necessary index))
       (reduced (l1-application-proof-simplify proof term nil *l1-witness-normal-definitions*)))
    (if reduced (proof-proof-rewrite proof necessary reduced (list 1 index)) necessary)))

(defun l1-witness-predicate-necessity (proof comparison expanded necessary)
  (proof-with-checked-results
      ((selected (l1-witness-step-term expanded 2))
       (expansion (l1-application-proof-simplify proof selected nil *l1-witness-normal-definitions*))
       (expanded (proof-proof-chain proof expanded (list expansion)))
       (necessary (l1-witness-reduce-necessity proof necessary 1))
       (necessary (l1-witness-reduce-necessity proof necessary 2))
       (opening (l1-application-proof-simplify proof
                                             (l1-witness-comparison-counterexample comparison)
                                             nil *l1-witness-normal-definitions*))
       (necessary (if opening
                      (proof-with-checked-results ((reverse (proof-proof-symmetric proof opening)))
                        (proof-proof-rewrite proof necessary reverse '(1 1)))
                    necessary))
       (reverse (proof-proof-symmetric proof expanded))
       (needed (proof-proof-rewrite proof necessary reverse '(1 2 1))))
    (proof-proof-tidy proof needed)))

(defun l1-witness-witness-proof-after (proof selector predicate)
  (let ((definitions (proof-proof-definitions proof)))
    (if (or (assoc-equal selector definitions) (assoc-equal predicate definitions))
        (let ((remaining (remove-assoc-equal predicate (remove-assoc-equal selector definitions))))
          (proof-proof-with-kind
           (proof-make-proof (proof-proof-facts proof) remaining (proof-proof-primitives proof))
           (proof-proof-kind proof)))
      proof)))

(defun l1-witness-witness-entry-with-proof (proof comparison chosen-argument necessary tag)
  (let* ((parameters (l1-witness-comparison-parameters comparison))
         (selector (if (equal tag "") *l1-witness-selector*
                     (proof-sym (concatenate 'string "L1-COUNTEREXAMPLE-" tag) "ACL2")))
         (predicate (if (equal tag "") *l1-witness-predicate*
                      (proof-sym (concatenate 'string "L1-CHOSEN-PREDICATE-" tag) "ACL2")))
         (facts (proof-proof-facts proof))
         (before proof))
    (if (or (assoc-equal selector facts) (assoc-equal predicate facts))
        (cons nil proof)
      (proof-with-checked-results
          ((application (l1-witness-need-at-least
                         (l1-witness-comparison-application comparison) 2)))
        (let* ((selector-call (cons selector parameters))
               (predicate-call (cons predicate parameters))
               (body (list* (car application) selector-call (cddr application)))
               (formals (or parameters *proof-nil*))
               (witness (l1-witness-comparison-witness comparison)))
          (proof-with-checked-results
              ((define-selector (proof-line "define" (list *proof-nil*
                                                          (list selector formals chosen-argument))))
               (define-predicate (proof-line "define" (list *proof-nil*
                                                           (list predicate formals body))))
               (proof (proof-proof-add-definition proof selector parameters chosen-argument))
               (proof (proof-proof-add-definition proof predicate parameters body))
               (value (proof-proof-unfold proof predicate-call))
               (beta (proof-proof-beta proof body))
               (expanded (proof-proof-chain proof value (list beta)))
               (selector-definition (proof-proof-unfold proof selector-call))
               (expanded (proof-proof-rewrite-first proof expanded selector-definition))
               (needed (l1-witness-predicate-necessity proof comparison expanded necessary))
               (entry (proof-proof-entry "witness" witness (list witness selector predicate)
                                         (list value needed))))
            (cons (list (+ (car (caddr entry)) (cadr (caddr entry)))
                        (concatenate 'string define-selector define-predicate (cadddr entry)))
                  (l1-witness-witness-proof-after before selector predicate))))))))

(defun l1-witness-witness-entry (proof comparison chosen-argument necessary tag)
  (proof-with-checked-results
      ((entry (l1-witness-witness-entry-with-proof proof comparison chosen-argument necessary tag)))
    (car entry)))

(defun l1-witness-obvious-choice-arguments (arguments proof variable failure always-holds)
  (declare (xargs :measure (acl2-count arguments)))
  (if (endp arguments)
      nil
    (let ((argument (car arguments))
          (definitions (list *library-implies*)))
      (proof-with-checked-results
          ((selected-failure (proof-subst failure (list (cons variable argument)))))
        (let ((implication (list *library-implies* failure selected-failure)))
          (if always-holds
              (proof-with-checked-results
                  ((consequence (l1-application-proof-prove proof implication
                                                            (list always-holds) definitions)))
                (list argument consequence))
            (let ((fixed-failure
                   (l1-application-proof-prove proof selected-failure nil *l1-witness-choice-definitions*)))
              (if (l1-application-unproved-p fixed-failure)
                  (l1-witness-obvious-choice-arguments
                   (cdr arguments) proof variable failure always-holds)
                (proof-with-checked-results
                    ((fixed-failure fixed-failure)
                     (holds (proof-proof-assume proof failure t))
                     (yes (l1-application-proof-prove proof implication (list holds fixed-failure)
                                                      definitions))
                     (denied (proof-proof-assume proof failure nil))
                     (no (l1-application-proof-prove proof implication (list denied) definitions))
                     (consequence (proof-proof-cases proof failure yes no)))
                  (list argument consequence))))))))))

(defun l1-witness-obvious-choice (proof comparison)
  (let* ((failure (l1-witness-comparison-counterexample comparison))
         (variable (l1-witness-comparison-argument comparison))
         (always-holds (l1-application-proof-prove proof (proof-neg failure) nil
                                                   *l1-witness-choice-definitions*)))
    (proof-with-checked-results
        ((always-holds (if (l1-application-unproved-p always-holds) nil always-holds)))
      (l1-witness-obvious-choice-arguments (list *proof-false* *proof-true* *proof-zero*)
                                           proof variable failure always-holds))))

(defun l1-witness-choice-actuals (parameters bindings)
  (if (endp parameters)
      nil
    (cons (table-get bindings (car parameters) *proof-false*)
          (l1-witness-choice-actuals (cdr parameters) bindings))))

(defun l1-witness-choice-bindings (parameters actuals bindings)
  (declare (xargs :measure (acl2-count parameters)))
  (if (endp parameters)
      bindings
    (l1-witness-choice-bindings (cdr parameters) (cdr actuals)
                                (table-put bindings (car parameters) (car actuals)))))

(defun l1-witness-matched-choice (proof choice comparison target matched-bindings)
  (let* ((parameters (l1-witness-choice-rule-parameters choice))
         (actuals (l1-witness-choice-actuals parameters matched-bindings))
         (bindings (l1-witness-choice-bindings parameters actuals nil))
         (argument (l1-witness-comparison-argument comparison))
         (bindings (table-put bindings (l1-witness-choice-rule-argument choice) argument)))
    (proof-with-checked-results
        ((necessary (l1-witness-choice-rule-counterexample-proof choice proof bindings))
         (selected (cons (l1-witness-choice-rule-name choice) actuals))
         (expected (proof-subst target (list (cons argument selected))))
         (conclusion (l1-witness-step-term necessary 2))
         (normal (l1-witness-normal-form proof conclusion)))
      (and (equal normal expected) (list selected necessary)))))

(defun l1-witness-select-choice (proof choices comparison target)
  (declare (xargs :measure (acl2-count choices)))
  (if (endp choices)
      nil
    (let ((choice (car choices)))
      (proof-with-checked-results
          ((pattern (l1-witness-normal-form proof (l1-witness-choice-rule-counterexample choice)))
           (matched (l1-witness-match-counterexample pattern target choice comparison nil))
           (selected (and (car matched)
                          (l1-witness-matched-choice proof choice comparison target (cdr matched)))))
        (or selected (l1-witness-select-choice proof (cdr choices) comparison target))))))

(defun l1-witness-prove-witness-with-proof (proof data choices tag)
  (proof-with-checked-results ((comparison (l1-witness-comparison-read data)))
    (if (not comparison)
        (cons nil proof)
      (proof-with-checked-results
          ((target (l1-witness-normal-form proof (l1-witness-comparison-counterexample comparison)))
           (application (l1-witness-need-at-least (l1-witness-comparison-application comparison) 2))
           (argument (l1-witness-comparison-argument comparison))
           (beta (proof-proof-beta proof (list* (car application) argument (cddr application))))
           (body (l1-witness-step-term beta 2))
           (normal (l1-witness-normal-form proof (proof-neg body))))
        (if (not (equal target normal))
            (cons nil proof)
          (proof-with-checked-results
              ((supplied (l1-witness-select-choice proof choices comparison target))
               (direct (or supplied (l1-witness-obvious-choice proof comparison)))
               (direct (or direct (l1-finite-choice-finite-choice proof argument target))))
            (if direct
                (l1-witness-witness-entry-with-proof proof comparison (car direct)
                                                     (cadr direct) tag)
              (cons nil proof))))))))

(defun l1-witness-prove-witness (proof data choices tag)
  (proof-with-checked-results ((result (l1-witness-prove-witness-with-proof proof data choices tag)))
    (car result)))

(defun l1-witness-remove-facts (proof names)
  (declare (xargs :measure (acl2-count names)))
  (if (endp names)
      proof
    (proof-with-checked-results ((facts (table-delete (proof-proof-facts proof) (car names))))
      (l1-witness-remove-facts (proof-proof-with-facts proof facts) (cdr names)))))

(defund l1-witness-choice-theorem-source (proof formula obligation)
  (let ((name (car formula)))
    (proof-with-checked-results
        ((step (proof-proof-subsume proof obligation (list (cadr formula))))
         (entry (proof-proof-entry "theorem" name (list name) (list step))))
      (cadddr entry))))

(mutual-recursion
 (defun l1-witness-dependencies-collect (term called)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) called)
         ((endp term) '(:failure "failure" ""))
         ((equal (car term) *proof-quote*) called)
         ((equal (car term) *termination-return-last*)
          (l1-witness-dependencies-last (cdr term) called))
         (t
          (let ((head (car term)))
            (proof-with-checked-results
                ((called (cond ((not (proof-compound head)) (add-to-set-equal head called))
                               ((consp (cddr head))
                                (l1-witness-dependencies-collect (caddr head) called))
                               (t '(:failure "failure" "")))))
              (l1-witness-dependencies-arguments (cdr term) called))))))

 (defun l1-witness-dependencies-arguments (arguments called)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       called
     (proof-with-checked-results
         ((called (l1-witness-dependencies-collect (car arguments) called)))
       (l1-witness-dependencies-arguments (cdr arguments) called))))

 (defun l1-witness-dependencies-last (arguments called)
   (declare (xargs :measure (acl2-count arguments)))
   (cond ((endp arguments) called)
         ((endp (cdr arguments)) (l1-witness-dependencies-collect (car arguments) called))
         (t (l1-witness-dependencies-last (cdr arguments) called)))))

; Sets are written in the order of the serialized text of their members.
(mutual-recursion
 (defun l1-witness-dependency-text (value)
   (declare (xargs :measure (1+ (* 2 (acl2-count value)))))
   (cond ((null value) "()")
         ((eq value t) "t")
         ((integerp value) (decimal-text value))
         ((rationalp value)
          (concatenate 'string (decimal-text (numerator value)) "/" (decimal-text (denominator value))))
         ((stringp value)
          (concatenate 'string "\"" (text-replace (text-replace value "\\" "\\\\") "\"" "\\\"") "\""))
         ((consp value)
          (concatenate 'string "(" (text-join " " (l1-witness-dependency-text-items value)) ")"))
         (t "nil")))

 (defun l1-witness-dependency-text-items (items)
   (declare (xargs :measure (* 2 (acl2-count items))))
   (if (endp items)
       nil
     (cons (l1-witness-dependency-text (car items))
           (l1-witness-dependency-text-items (cdr items))))))

(defun l1-witness-dependency-sort-keys (called)
  (if (endp called)
      nil
    (cons (cons (l1-witness-dependency-text (car called)) (car called))
          (l1-witness-dependency-sort-keys (cdr called)))))

(defun l1-witness-dependencies (term)
  (proof-with-checked-results ((called (l1-witness-dependencies-collect term nil)))
    (strip-cdrs (seq-sorted (l1-witness-dependency-sort-keys called)))))

(defun l1-witness-affected-definitions-p (definitions affected)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      nil
    (proof-with-checked-results
        ((definition (proof-list-of-length (car definitions) 3))
         (calls (l1-witness-dependencies-collect (caddr definition) nil)))
      (or (intersectp-equal calls affected)
          (l1-witness-affected-definitions-p (cdr definitions) affected)))))

(defun l1-witness-affected-definition-names (definitions affected)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      affected
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (l1-witness-affected-definition-names (cdr definitions)
                                           (add-to-set-equal (car definition) affected)))))

(defun l1-witness-affected-formulas (formulas index affected hits)
  (declare (xargs :measure (acl2-count formulas)))
  (if (endp formulas)
      hits
    (proof-with-checked-results
        ((formula (proof-list-of-length (car formulas) 2))
         (calls (l1-witness-dependencies-collect (cadr formula) nil)))
      (l1-witness-affected-formulas (cdr formulas) index affected
                                    (if (intersectp-equal calls affected)
                                        (cons (list index (car formula)) hits)
                                      hits)))))

(defund l1-witness-affected-statement (kind data index affected hits)
  (cond
   ((equal kind "define")
    (if (integerp data)
        '(:failure "failure" "")
      (proof-with-checked-results
          ((dependent (l1-witness-affected-definitions-p (cdr data) affected))
           (affected (if dependent
                         (l1-witness-affected-definition-names (cdr data) affected)
                       affected)))
        (cons hits affected))))
   ((equal kind "constrain")
    (proof-with-checked-results
        ((formulas (proof-term-at data 1))
         (hits (if (proof-compound formulas)
                   (l1-witness-affected-formulas formulas index affected hits)
                 hits)))
      (cons hits affected)))
   ((member-equal kind '("theorem" "axiom"))
    (proof-with-checked-results
        ((hits (l1-witness-affected-formulas (list data) index affected hits)))
      (cons hits affected)))
   ((equal kind "choose")
    (proof-with-checked-results
        ((name (proof-term-at data 0))
         (predicate (proof-term-at data 3))
         (calls (l1-witness-dependencies-collect predicate nil))
         (affected (if (intersectp-equal calls affected)
                       (add-to-set-equal name affected)
                     affected))
         (hits (l1-witness-affected-formulas (list (list name predicate)) index affected hits)))
      (cons hits affected)))
   (t (cons hits affected))))

