(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-treeorder-complex* (proof-sym "COMPLEX-RATIONALP" "ACL2"))
(defconst *t4-treeorder-alphorder* (proof-sym "ALPHORDER" "ACL2"))
(defconst *t4-treeorder-symbol-less* (proof-sym "SYMBOL<" "ACL2"))
(defconst *t4-treeorder-characterp* (proof-cl "CHARACTERP"))
(defconst *t4-treeorder-stringp* (proof-cl "STRINGP"))
(defconst *t4-treeorder-symbolp* (proof-cl "SYMBOLP"))
(defconst *t4-treeorder-eq* (proof-cl "EQ"))
(defconst *t4-treeorder-types*
  (list *proof-integerp* *library-rationalp* *t4-treeorder-complex*
        *t4-treeorder-characterp* *t4-treeorder-stringp* *t4-treeorder-symbolp*))
(defconst *t4-treeorder-atom* (proof-cl "ATOM"))
(defconst *t4-treeorder-string-less* (proof-cl "STRING<"))
(defconst *t4-treeorder-string-le* (proof-cl "STRING<="))
(defconst *t4-treeorder-realpart* (proof-cl "REALPART"))
(defconst *t4-treeorder-num-eq* (proof-cl "="))
(defconst *t4-treeorder-lexorder* (proof-sym "LEXORDER" "ACL2"))

(defun t4-treeorder-request-p (result)
  (and (consp result) (eq (car result) :t4-treeorder-request)))

(defun t4-treeorder-request-method (request) (cadr request))
(defun t4-treeorder-request-args (request) (caddr request))
(defun t4-treeorder-request-lib (request) (cadddr request))

(defmacro t4-treeorder-with-results (bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (or (failure-p ,name) (t4-treeorder-request-p ,name))
             ,name
           (t4-treeorder-with-results ,(cdr bindings) ,result))))))

; The context pairs the Library with the unconsumed method replies.
(defun t4-treeorder-method (context method args)
  (let ((replies (cdr context)))
    (if (endp replies)
        (list :t4-treeorder-request method args (car context))
      (proof-with-checked-results ((reply (car replies)))
        (cons (car reply) (cons (cdr reply) (cdr replies)))))))

(defun t4-treeorder-proof (context)
  (library-library-proof (car context)))

(defund t4-treeorder-step-term (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun t4-treeorder-reflexive (context term)
  (proof-with-checked-results ((step (proof-proof-reflexive (t4-treeorder-proof context) term)))
    (cons step context)))

(defund t4-treeorder-assume (context term holds)
  (proof-proof-assume (t4-treeorder-proof context) term holds))

(defund t4-treeorder-constant (context term)
  (proof-with-checked-results
      ((result (t4-ordinals-ordinals-constant (car context) term))
       (context (cons (cdr result) (cdr context))))
    (if (and (not (car result))
             (member-equal (car term)
                           (list *proof-cons* *t4-treeorder-characterp*
                                 (proof-cl "SYMBOL-NAME") (proof-sym "SYMBOL-PACKAGE-NAME" "ACL2")
                                 *proof-plus* *proof-times* *proof-minus* *proof-less*))
             (proof-all-quoted-p (cdr term)))
        (t4-treeorder-method context :constant (list term))
      (cons (car result) context))))

(defund t4-treeorder-chain (context first rest)
  (proof-with-checked-results ((step (proof-proof-chain (t4-treeorder-proof context) first rest)))
    (cons step context)))

(mutual-recursion
 (defund t4-treeorder-simplify-visit (n context term known definitions)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "t4-treeorder-simplify-visit")
     (t4-treeorder-with-results
         ((base (t4-treeorder-simplify-base (1- n) context term known definitions))
          (context (cdr base))
          (equality (car base))
          (reduced (if equality (t4-treeorder-step-term equality 2) term))
          (selected (t4-ordinals-nonnil-selection (car context) reduced)))
       (if (not selected)
           base
         (t4-treeorder-with-results
             ((next (t4-treeorder-simplify-visit (1- n) context (cadr selected) known definitions))
              (opened (t4-treeorder-chain (cdr next) (car selected) (list (car next)))))
           (if equality
               (t4-treeorder-chain (cdr opened) equality (list (car opened)))
             opened))))))
 (defund t4-treeorder-simplify-base (n context term known definitions)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "t4-treeorder-simplify-base"))
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*))
     (cons nil context))
    ((endp term) '(:failure "failure" ""))
    ((or (proof-compound (car term)) (member-equal (car term) definitions))
     (t4-treeorder-with-results
         ((expansion (proof-simplify-expansion (t4-treeorder-proof context) term))
          (next (t4-treeorder-simplify-visit (1- n) context (cadr expansion) known definitions)))
       (t4-treeorder-chain (cdr next) (car expansion) (list (car next)))))
    ((proof-is-call term *proof-if*)
     (t4-treeorder-with-results
         ((test (proof-term-at term 1))
          (first (t4-treeorder-simplify-visit (1- n) context test known definitions))
          (context (cdr first))
          (path (proof-simplify-if-path (t4-treeorder-proof context) term (car first) known)))
       (if (eq (car path) :simplify)
           (t4-treeorder-with-results
               ((next (t4-treeorder-simplify-visit (1- n) context (caddr path) known definitions)))
             (t4-treeorder-chain (cdr next) (cadr path) (list (car next))))
         (cons path context))))
    (t (t4-treeorder-simplify-arguments (1- n) context term (cdr term) 1 nil known definitions))))
 (defund t4-treeorder-simplify-arguments (n context term args index equality known definitions)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "t4-treeorder-simplify-arguments"))
    ((endp args)
     (t4-treeorder-with-results
         ((current (if equality (t4-treeorder-step-term equality 2) term))
          (constant (t4-treeorder-constant context current)))
       (cond ((not (car constant)) (cons equality (cdr constant)))
             (equality (t4-treeorder-chain (cdr constant) equality (list (car constant))))
             (t constant))))
    (t
     (t4-treeorder-with-results
         ((argument (t4-treeorder-simplify-visit (1- n) context (car args) known definitions))
          (context (cdr argument))
          (next (proof-simplify-argument-result (t4-treeorder-proof context)
                                                term index equality (car argument))))
       (t4-treeorder-simplify-arguments (1- n) context term (cdr args) (1+ index)
                                        next known definitions))))))

(defun t4-treeorder-simplify (context term known definitions)
  (t4-treeorder-simplify-visit 1000000 context term known definitions))

(defun t4-treeorder-simplify-or-reflexive (context term known definitions)
  (t4-treeorder-with-results ((result (t4-treeorder-simplify context term known definitions)))
    (if (car result) result (t4-treeorder-reflexive (cdr result) term))))

(defund t4-treeorder-prove-visit (n context term known definitions)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-treeorder-prove-visit")
    (t4-treeorder-with-results ((premise (t4-ordinals-prove-premise (car context) term known)))
      (if premise
          (cons premise context)
        (t4-treeorder-with-results
            ((simplified (t4-treeorder-simplify context term known definitions))
             (context (cdr simplified))
             (equality (car simplified))
             (value (and equality (t4-treeorder-step-term equality 2))))
          (cond
           ((or (not equality) (equal value term)) (proof-prove-unproved-term term))
           ((equal value *proof-true*)
            (proof-with-checked-results
                ((step (proof-proof-true-from-eq (t4-treeorder-proof context) equality)))
              (cons step context)))
           (t
            (t4-treeorder-with-results
                ((result (t4-treeorder-prove-visit (1- n) context value known definitions))
                 (context (cdr result))
                 (step (proof-proof-transport (t4-treeorder-proof context) (car result) equality)))
              (cons step context)))))))))

(defun t4-treeorder-prove (context term known definitions)
  (t4-treeorder-prove-visit 1000000 context term known definitions))

(defun t4-treeorder-type-cases-type-fact (name premise lib value)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof name (list (list *library-x* value)))))
      (proof-proof-modus-ponens proof fact premise))))

(defun t4-treeorder-type-cases-number-denials (suffixes number lib value)
  (if (endp suffixes)
      nil
    (proof-with-checked-results
        ((step (t4-treeorder-type-cases-type-fact
                (concatenate 'string "acl2-numberp-not-" (car suffixes)) number lib value))
         (rest (t4-treeorder-type-cases-number-denials (cdr suffixes) number lib value)))
      (cons step rest))))

(defund t4-treeorder-type-cases-case-data (test given lib value)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((rat (cond ((equal test *proof-integerp*)
                     (proof-with-checked-results
                         ((axiom (library-library-axiom lib "INTEGER-IMPLIES-RATIONAL" (list value))))
                       (proof-proof-modus-ponens proof axiom given)))
                    ((equal test *library-rationalp*) given)
                    (t nil))))
      (cond
       (rat
        (let ((complex-test (list *t4-treeorder-complex* value)))
          (proof-with-checked-results
              ((assumed (proof-proof-assume proof complex-test t))
               (no-rat (t4-treeorder-type-cases-type-fact
                        "complex-rationalp-not-rationalp" assumed lib value))
               (contradiction (proof-proof-cut proof rat no-rat))
               (no-complex (proof-proof-front proof contradiction (proof-neg complex-test)))
               (number (t4-treeorder-type-cases-type-fact "rationalp-acl2-numberp" rat lib value))
               (denials (t4-treeorder-type-cases-number-denials
                         '("characterp" "stringp" "symbolp") number lib value)))
            (if (equal test *proof-integerp*)
                (list* rat no-complex denials)
              (cons no-complex denials)))))
       ((equal test *t4-treeorder-complex*)
        (proof-with-checked-results
            ((number (t4-treeorder-type-cases-type-fact
                      "complex-rationalp-acl2-numberp" given lib value)))
          (t4-treeorder-type-cases-number-denials '("characterp" "stringp" "symbolp") number lib value)))
       ((equal test *t4-treeorder-characterp*)
        (proof-with-checked-results
            ((no-string (t4-treeorder-type-cases-type-fact "characterp-not-stringp" given lib value))
             (no-symbol (t4-treeorder-type-cases-type-fact "characterp-not-symbolp" given lib value)))
          (list no-string no-symbol)))
       ((equal test *t4-treeorder-stringp*)
        (proof-with-checked-results
            ((no-symbol (t4-treeorder-type-cases-type-fact "stringp-not-symbolp" given lib value)))
          (list no-symbol)))
       (t nil)))))

(defun t4-treeorder-choose (lib equation assumption)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (t4-treeorder-step-term equation 2))
         (selected (proof-proof-select proof value assumption)))
      (proof-proof-chain proof equation (list selected)))))

(defun t4-treeorder-compared-literals-normalize (term context same evidence x)
  (let ((proof (t4-treeorder-proof context)))
    (t4-treeorder-with-results
        ((identity (proof-proof-reflexive proof term))
         (moved (proof-proof-rewrite-result proof identity same (proof-eq *proof-true* term) x))
         (value (t4-treeorder-step-term moved 2))
         (simplified (t4-treeorder-simplify
                      context value evidence (list *t4-treeorder-eq* *proof-not*)))
         (context (cdr simplified))
         (step (proof-proof-chain (t4-treeorder-proof context) moved (list (car simplified)))))
      (cons step context))))

(defun t4-treeorder-compared-literals-branches
    (context left right known test yes-value no-value x y)
  (let ((proof (t4-treeorder-proof context)))
    (t4-treeorder-with-results
        ((same (proof-proof-assume proof test t))
         (irreflexive (t4-treeorder-method
                       context :fact-proof
                       (list (proof-neg (list *t4-treeorder-symbol-less* y y)) known)))
         (context (cdr irreflexive)))
      (if (not (car irreflexive))
          '(:failure "SearchMiss" "")
        (let ((evidence (append known (list (car irreflexive)))))
          (t4-treeorder-with-results
              ((if-true (proof-proof-if-true (t4-treeorder-proof context) left))
               (normalized-yes
                (t4-treeorder-compared-literals-normalize yes-value context same evidence x))
               (normalized-right
                (t4-treeorder-compared-literals-normalize right (cdr normalized-yes) same evidence x))
               (context (cdr normalized-right))
               (proof (t4-treeorder-proof context))
               (right-reversed (proof-proof-symmetric proof (car normalized-right)))
               (yes (proof-proof-chain proof if-true (list (car normalized-yes) right-reversed)))
               (no-eq (t4-treeorder-simplify-or-reflexive
                       context no-value known (list *t4-treeorder-eq* *proof-not*)))
               (no-result (t4-treeorder-step-term (car no-eq) 2))
               (context (cdr no-eq)))
            (if (not (equal no-result right))
                '(:failure "InferenceMismatch" "")
              (let ((proof (t4-treeorder-proof context)))
                (proof-with-checked-results
                    ((if-false (proof-proof-if-false proof left))
                     (no (proof-proof-chain proof if-false (list (car no-eq))))
                     (step (proof-proof-cases proof test yes no)))
                  (cons step context))))))))))

(defun t4-treeorder-compared-literals (context left right known)
  (cond ((equal left right) (t4-treeorder-reflexive context left))
        ((not (proof-is-call left *proof-if*)) '(:failure "SearchMiss" ""))
        (t
         (proof-with-checked-results ((test (proof-term-at left 1)))
           (if (not (proof-is-call test *proof-equal*))
               '(:failure "SearchMiss" "")
             (proof-with-checked-results ((arms (proof-list-of-length (cdr left) 3)))
               (let ((yes (cadr arms))
                     (vars (cdr test)))
                 (if (not (or (equal yes test) (equal yes (cons *t4-treeorder-eq* vars))))
                     '(:failure "SearchMiss" "")
                   (proof-with-checked-results ((vars (proof-list-of-length vars 2)))
                     (t4-treeorder-compared-literals-branches
                      context left right known test yes (caddr arms) (car vars) (cadr vars)))))))))))

(defun t4-treeorder-atomic-order-atoms-compare (y-types context x-types fast-view ordinary-view)
  (let ((premises (append x-types y-types))
        (definitions (list *t4-treeorder-eq* *proof-not*)))
    (t4-treeorder-with-results
        ((a (t4-treeorder-step-term fast-view 2))
         (b (t4-treeorder-step-term ordinary-view 2))
         (left (t4-treeorder-simplify-or-reflexive context a premises definitions))
         (right (t4-treeorder-simplify-or-reflexive (cdr left) b premises definitions))
         (left-value (t4-treeorder-step-term (car left) 2))
         (right-value (t4-treeorder-step-term (car right) 2))
         (proof-step (t4-treeorder-compared-literals (cdr right) left-value right-value premises))
         (context (cdr proof-step))
         (proof (t4-treeorder-proof context))
         (reverse (proof-proof-symmetric proof (car right)))
         (step (proof-proof-chain proof (car left) (list (car proof-step) reverse))))
      (cons step context))))

(defun t4-treeorder-boolean-comparison-premise (known context value simplified)
  (if (endp known)
      (cons simplified context)
    (proof-with-checked-results ((literal (proof-step-first (car known))))
      (cond
       ((equal literal value)
        (let ((proof (t4-treeorder-proof context)))
          (proof-with-checked-results
              ((typed (proof-proof-fact proof "booleanp-<"
                                       (seq-zip (list *library-x* *library-y*) (cdr value))))
               (truth (t4-ordinals-ordinals-true-boolean (car context) typed (car known)))
               (context (cons (cdr truth) (cdr context)))
               (step (proof-proof-chain (t4-treeorder-proof context) simplified (list (car truth)))))
            (cons step context))))
       ((equal literal (proof-neg value))
        (let ((proof (t4-treeorder-proof context)))
          (proof-with-checked-results
              ((nil-or-true (proof-proof-nil-or-true proof value))
               (front (proof-proof-front proof nil-or-true value))
               (cut (proof-proof-cut proof front (car known)))
               (step (proof-proof-chain proof simplified (list cut))))
            (cons step context))))
       (t (t4-treeorder-boolean-comparison-premise (cdr known) context value simplified))))))

(defund t4-treeorder-boolean-comparison-normalize (term context known)
  (t4-treeorder-with-results
      ((simplified (t4-treeorder-simplify-or-reflexive
                    context term known (list *proof-not* *t4-treeorder-eq* *t4-treeorder-num-eq*)))
       (value (t4-treeorder-step-term (car simplified) 2)))
    (if (proof-is-call value *proof-less*)
        (t4-treeorder-boolean-comparison-premise known (cdr simplified) value (car simplified))
      simplified)))

(defund t4-treeorder-boolean-comparison-decision (term)
  (if (proof-is-call term *proof-if*)
      (if (consp (cdr term))
          (proof-with-checked-results ((nested (t4-treeorder-boolean-comparison-decision (cadr term))))
            (or nested (cadr term)))
        (proof-term-at term 1))
    (if (proof-is-call term *proof-less*) term nil)))

(defund t4-treeorder-boolean-comparison-known-p (known test)
  (if (endp known)
      nil
    (proof-with-checked-results ((literal (proof-step-first (car known))))
      (or (equal literal test) (equal literal (proof-neg test))
          (t4-treeorder-boolean-comparison-known-p (cdr known) test)))))

(defun t4-treeorder-boolean-comparison-visit (n context left right known depth)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "t4-treeorder-boolean-comparison-visit"))
   ((equal left right) (t4-treeorder-reflexive context left))
   (t
    (t4-treeorder-with-results
        ((a (t4-treeorder-boolean-comparison-normalize left context known))
         (b (t4-treeorder-boolean-comparison-normalize right (cdr a) known))
         (context (cdr b))
         (proof (t4-treeorder-proof context))
         (left-value (t4-treeorder-step-term (car a) 2))
         (right-value (t4-treeorder-step-term (car b) 2)))
      (if (equal left-value right-value)
          (proof-with-checked-results
              ((reverse (proof-proof-symmetric proof (car b)))
               (step (proof-proof-chain proof (car a) (list reverse))))
            (cons step context))
        (proof-with-checked-results
            ((left-test (t4-treeorder-boolean-comparison-decision left-value))
             (test (or left-test (t4-treeorder-boolean-comparison-decision right-value)))
             (seen (and (not (equal depth 4)) test
                        (t4-treeorder-boolean-comparison-known-p known test))))
          (if (or (equal depth 4) (not test) seen)
              '(:failure "SearchMiss" "")
            (t4-treeorder-with-results
                ((yes-premise (t4-treeorder-assume context test t))
                 (yes (t4-treeorder-boolean-comparison-visit
                       (1- n) context left-value right-value (append known (list yes-premise)) (1+ depth)))
                 (no-premise (t4-treeorder-assume (cdr yes) test nil))
                 (no (t4-treeorder-boolean-comparison-visit
                      (1- n) (cdr yes) left-value right-value (append known (list no-premise)) (1+ depth)))
                 (context (cdr no))
                 (proof (t4-treeorder-proof context))
                 (cases (proof-proof-cases proof test (car yes) (car no)))
                 (reverse (proof-proof-symmetric proof (car b)))
                 (step (proof-proof-chain proof (car a) (list cases reverse))))
              (cons step context)))))))))

(defun t4-treeorder-boolean-comparison (context left right known depth)
  (t4-treeorder-boolean-comparison-visit 1000000 context left right known depth))

(defun t4-treeorder-reverse-equality (lib step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((literal (proof-step-first step)))
      (if (proof-is-call literal *proof-equal*)
          (proof-proof-symmetric proof step)
        (proof-with-checked-results
            ((equation (proof-term-at literal 1))
             (args (if (integerp equation)
                       (proof-term-at equation 1)
                     (proof-list-of-length (cdr equation) 2)))
             (reverse (proof-eq (cadr args) (car args)))
             (assumed (proof-proof-assume proof reverse t))
             (symmetric (proof-proof-symmetric proof assumed))
             (contradiction (proof-proof-cut proof symmetric step)))
          (proof-proof-front proof contradiction (proof-neg reverse)))))))

(defun t4-treeorder-complement-order-yes (context forward strict denied ryes fyes)
  (let* ((lib (car context))
         (proof (t4-treeorder-proof context)))
    (t4-treeorder-with-results
        ((anti (library-library-axiom lib "LEXORDER-ANTI-SYMMETRIC" (list *library-x* *library-y*)))
         (both (t4-division-combine lib (list fyes ryes)))
         (same (proof-proof-modus-ponens proof anti both))
         (truth (t4-treeorder-method context :boolean-true (list same)))
         (context (cdr truth))
         (proof (t4-treeorder-proof context))
         (if-true (proof-proof-if-true proof strict))
         (rewritten (proof-proof-rewrite proof if-true (car truth) '(1 2 1)))
         (value (t4-treeorder-step-term rewritten 2))
         (simplified (t4-treeorder-simplify context value nil (list *proof-not*)))
         (context (cdr simplified))
         (proof (t4-treeorder-proof context))
         (equal-branch (proof-proof-chain proof rewritten (list (car simplified))))
         (if-false (proof-proof-if-false proof strict))
         (no-forward (proof-proof-cases proof forward equal-branch if-false))
         (simplified (t4-treeorder-simplify context denied (list ryes) (list *proof-not*)))
         (context (cdr simplified))
         (proof (t4-treeorder-proof context))
         (reversed (proof-proof-symmetric proof (car simplified)))
         (step (proof-proof-chain proof no-forward (list reversed))))
      (cons step context))))

(defun t4-treeorder-complement-order-no (context forward strict same denied rno)
  (let* ((lib (car context))
         (proof (t4-treeorder-proof context)))
    (t4-treeorder-with-results
        ((total (library-library-axiom lib "LEXORDER-TOTAL" (list *library-x* *library-y*)))
         (not-forward (proof-proof-assume proof forward nil))
         (if-not-forward (proof-proof-prove-if proof total not-forward))
         (forced (proof-proof-cut proof if-not-forward rno))
         (has-forward (proof-proof-front proof forced forward))
         (reflexive (library-library-axiom lib "LEXORDER-REFLEXIVE" (list *library-y*)))
         (equal-assumption (proof-proof-assume proof same t))
         (reverse (proof-proof-symmetric proof equal-assumption))
         (equal-case (proof-proof-rewrite proof reflexive reverse '(1 2)))
         (cut (proof-proof-cut proof equal-case rno))
         (distinct (proof-proof-front proof cut (proof-neg same)))
         (strict-identity (proof-proof-reflexive proof strict))
         (no-reverse (t4-treeorder-choose lib strict-identity has-forward))
         (simplified (t4-treeorder-simplify context (proof-neg same) (list distinct)
                                            (list *proof-not*)))
         (context (cdr simplified))
         (no-reverse (proof-proof-chain (t4-treeorder-proof context) no-reverse (list (car simplified))))
         (simplified (t4-treeorder-simplify context denied (list rno) (list *proof-not*)))
         (context (cdr simplified))
         (proof (t4-treeorder-proof context))
         (reversed (proof-proof-symmetric proof (car simplified)))
         (step (proof-proof-chain proof no-reverse (list reversed))))
      (cons step context))))

(defun t4-treeorder-complement-order-lemma (context label)
  (let* ((proof (t4-treeorder-proof context))
         (forward (list *t4-treeorder-lexorder* *library-x* *library-y*))
         (reverse (list *t4-treeorder-lexorder* *library-y* *library-x*))
         (same (proof-eq *library-x* *library-y*))
         (strict (proof-ite forward (proof-neg same) *proof-false*))
         (denied (proof-neg reverse)))
    (t4-treeorder-with-results
        ((ryes (proof-proof-assume proof reverse t))
         (rno (proof-proof-assume proof reverse nil))
         (fyes (proof-proof-assume proof forward t))
         (yes (t4-treeorder-complement-order-yes context forward strict denied ryes fyes))
         (no (t4-treeorder-complement-order-no (cdr yes) forward strict same denied rno))
         (context (cdr no))
         (step (proof-proof-cases (t4-treeorder-proof context) reverse (car yes) (car no)))
         (lib (library-library-lemma (car context) label (proof-eq strict denied) step nil)))
      (cons lib (cdr context)))))

(defun t4-treeorder-complement-order (context x y)
  (let ((label "STRICT-LEXORDER-REVERSE"))
    (t4-treeorder-with-results
        ((context (if (assoc-equal (proof-sym "SELF-STRICT-LEXORDER-REVERSE" "ACL2")
                                    (proof-proof-facts (t4-treeorder-proof context)))
                      context
                    (t4-treeorder-complement-order-lemma context label)))
         (step (library-library-cite (car context) label (list x y) nil)))
      (cons step context))))

(defun t4-treeorder-atomic-lexorder (context x y ax ay)
  (let ((definitions (list *t4-treeorder-atom* *proof-not*)))
    (t4-treeorder-with-results
        ((xatom (t4-treeorder-prove context (list *t4-treeorder-atom* x) (list ax) definitions))
         (yatom (t4-treeorder-prove (cdr xatom) (list *t4-treeorder-atom* y) (list ay) definitions))
         (context (cdr yatom))
         (lib (car context))
         (opened (proof-proof-unfold (t4-treeorder-proof context) (list *t4-treeorder-lexorder* x y)))
         (chosen (t4-treeorder-choose lib opened (car xatom)))
         (step (t4-treeorder-choose lib chosen (car yatom))))
      (cons step context))))

(defun t4-treeorder-numeric-view (lib x y x-rat y-rat)
  (proof-with-checked-results
      ((alpha (proof-proof-unfold (library-library-proof lib) (list *t4-treeorder-alphorder* x y)))
       (chosen (t4-treeorder-choose lib alpha x-rat)))
    (t4-treeorder-choose lib chosen y-rat)))

(defun t4-treeorder-rational-cases-noncons (rational lib)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((term (t4-treeorder-step-term rational 1))
         (numeric (t4-treeorder-type-cases-type-fact "rationalp-acl2-numberp" rational lib term))
         (shape (list *proof-consp* term))
         (assumed (proof-proof-assume proof shape t))
         (denial (t4-treeorder-type-cases-type-fact "consp-not-acl2-numberp" assumed lib term))
         (cut (proof-proof-cut proof numeric denial)))
      (proof-proof-front proof cut (proof-neg shape)))))

(defun t4-treeorder-rational-cases-negate-alpha (strict definition context)
  (t4-treeorder-with-results
      ((literal (proof-step-first strict))
       (denial (t4-treeorder-prove context (proof-neg (proof-neg literal)) (list strict) (list *proof-not*)))
       (context (cdr denial))
       (proof (t4-treeorder-proof context))
       (reverse (proof-proof-symmetric proof definition))
       (step (proof-proof-rewrite proof (car denial) reverse '(1 1))))
    (cons step context)))

(defun t4-treeorder-rational-cases-no-equality (strict lib y y-rat ay same)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((axiom (library-library-axiom lib "ALPHORDER-REFLEXIVE" (list y)))
         (reflexive (proof-proof-modus-ponens proof axiom ay))
         (numeric (t4-treeorder-numeric-view lib y y y-rat y-rat))
         (less-self (proof-proof-rewrite proof reflexive numeric '(1)))
         (assumed (proof-proof-assume proof same t))
         (changed (proof-proof-rewrite-first proof strict assumed))
         (cut (proof-proof-cut proof changed less-self)))
      (proof-proof-front proof cut (proof-neg same)))))

(defun t4-treeorder-leaf-reply (known context leaf)
  (let ((reply (assoc-equal known leaf)))
    (if reply
        (proof-with-checked-results ((result (cdr reply)))
          (cons (car result) (cons (cdr result) (cdr context))))
      '(:failure "SearchMiss" ""))))

(defun t4-treeorder-strict-atoms-atomic-left-atomic-right-compare (known context left right facts)
  (proof-with-checked-results
      ((last (if (endp known) '(:failure "failure" "") (car (last known))))
       (asymmetric (t4-treeorder-reverse-equality (car context) last)))
    (t4-treeorder-boolean-comparison context left right (append facts known (list asymmetric)) 0)))

(defun t4-treeorder-rational-cases-leaf (leaf known context)
  (if (eq (car leaf) :strict-atoms)
      (t4-treeorder-strict-atoms-atomic-left-atomic-right-compare
       known context (cadr leaf) (caddr leaf) (cadddr leaf))
    (t4-treeorder-leaf-reply known context leaf)))

(defun t4-treeorder-rational-cases (context x y x-rat y-rat leaf)
  (let* ((lib (car context))
         (proof (t4-treeorder-proof context))
         (forward (list *proof-less* x y))
         (reverse (list *proof-less* y x))
         (same (proof-eq x y)))
    (t4-treeorder-with-results
        ((ax (t4-treeorder-rational-cases-noncons x-rat lib))
         (ay (t4-treeorder-rational-cases-noncons y-rat lib))
         (alpha-xy (t4-treeorder-numeric-view lib x y x-rat y-rat))
         (alpha-yx (t4-treeorder-numeric-view lib y x y-rat x-rat))
         (px (proof-proof-assume proof forward t))
         (qx (proof-proof-assume proof forward nil))
         (py (proof-proof-assume proof reverse t))
         (qy (proof-proof-assume proof reverse nil))
         (total-axiom (library-library-axiom lib "ALPHORDER-TOTAL" (list x y)))
         (atoms (t4-division-combine lib (list ax ay)))
         (total (proof-proof-modus-ponens proof total-axiom atoms))
         (no-alpha-xy (t4-treeorder-rational-cases-negate-alpha py alpha-xy context))
         (context (cdr no-alpha-xy))
         (obstruction (proof-proof-prove-if (t4-treeorder-proof context) total (car no-alpha-xy)))
         (no-alpha-yx (t4-treeorder-rational-cases-negate-alpha px alpha-yx context))
         (context (cdr no-alpha-yx))
         (lib (car context))
         (proof (t4-treeorder-proof context))
         (cut (proof-proof-cut proof obstruction (car no-alpha-yx)))
         (opposite (proof-proof-front proof cut (proof-neg reverse)))
         (anti (library-library-axiom lib "ALPHORDER-ANTI-SYMMETRIC" (list x y)))
         (xy (proof-proof-transport proof qy alpha-xy))
         (yx (proof-proof-transport proof qx alpha-yx))
         (sides (t4-division-combine lib (list ax ay xy yx)))
         (same-proof (proof-proof-modus-ponens proof anti sides))
         (no-equality (t4-treeorder-rational-cases-no-equality px lib y y-rat ay same))
         (yes (t4-treeorder-rational-cases-leaf leaf (list px opposite no-equality) context))
         (context (cdr yes))
         (no-equality (t4-treeorder-rational-cases-no-equality py (car context) y y-rat ay same))
         (reverse-yes (t4-treeorder-rational-cases-leaf leaf (list qx py no-equality) context))
         (reverse-no (t4-treeorder-rational-cases-leaf leaf (list qx qy same-proof) (cdr reverse-yes)))
         (context (cdr reverse-no))
         (proof (t4-treeorder-proof context))
         (no (proof-proof-cases proof reverse (car reverse-yes) (car reverse-no)))
         (step (proof-proof-cases proof forward (car yes) no)))
      (cons step context))))

(defun t4-treeorder-strict-atoms-atomic-left-atomic-right-paired (kind types x y)
  (proof-with-checked-results ((first (t4-structural-evidence-find types (list kind x))))
    (if (car first)
        (proof-with-checked-results ((second (t4-structural-evidence-find (cdr first) (list kind y))))
          (cons (if (car second) t nil) (cdr second)))
      first)))

(defun t4-treeorder-strict-atoms-untyped-p (kinds types x y)
  (if (endp kinds)
      (cons t types)
    (proof-with-checked-results ((first (t4-structural-evidence-find types (list (car kinds) x))))
      (if (car first)
          (cons nil (cdr first))
        (proof-with-checked-results
            ((second (t4-structural-evidence-find (cdr first) (list (car kinds) y))))
          (if (car second)
              (cons nil (cdr second))
            (t4-treeorder-strict-atoms-untyped-p (cdr kinds) (cdr second) x y)))))))

(defun t4-treeorder-strict-atoms-complex (context left right x y facts)
  (let ((lib (car context)))
    (proof-with-checked-results
        ((x-axiom (library-library-axiom lib "COMPLEX-IMPLIES1" (list x)))
         (x-pieces (t4-division-pieces lib x-axiom))
         (x-pieces (proof-list-of-length x-pieces 2))
         (y-axiom (library-library-axiom lib "COMPLEX-IMPLIES1" (list y)))
         (y-pieces (t4-division-pieces lib y-axiom))
         (y-pieces (proof-list-of-length y-pieces 2)))
      (t4-treeorder-rational-cases
       context (list *t4-treeorder-realpart* x) (list *t4-treeorder-realpart* y)
       (car x-pieces) (car y-pieces) (list :strict-atoms left right facts)))))

(defun t4-treeorder-strict-atoms-symbol (context left right types facts same y)
  (t4-treeorder-with-results
      ((equal-symbols (proof-proof-assume (t4-treeorder-proof context) same t))
       (reflexive (t4-treeorder-method
                   context :fact-proof-evidence
                   (list (proof-neg (list *t4-treeorder-symbol-less* y y)) types)))
       (context (cdr reflexive)))
    (if (not (car reflexive))
        '(:failure "SearchMiss" "")
      (let ((proof (t4-treeorder-proof context)))
        (t4-treeorder-with-results
            ((reversed (proof-proof-symmetric proof equal-symbols))
             (neither (proof-proof-rewrite proof (car reflexive) reversed '(1 1 1)))
             (yes (t4-treeorder-boolean-comparison
                   context left right (append facts (list equal-symbols neither)) 0))
             (not-same (proof-proof-assume (t4-treeorder-proof (cdr yes)) same nil))
             (no (t4-treeorder-boolean-comparison
                  (cdr yes) left right (append facts (list not-same)) 0))
             (context (cdr no))
             (step (proof-proof-cases (t4-treeorder-proof context) same (car yes) (car no))))
          (cons step context))))))

(defun t4-treeorder-strict-atoms-string-yes (context left-active active equal-strings reflexive same)
  (t4-treeorder-with-results
      ((proof (t4-treeorder-proof context))
       (reverse (proof-proof-symmetric proof equal-strings))
       (false-lt (if reflexive
                     (proof-proof-rewrite proof reflexive reverse '(1 1 1))
                   '(:failure "failure" "")))
       (denied (t4-treeorder-simplify context (proof-neg same) (list equal-strings) (list *proof-not*)))
       (context (cdr denied))
       (proof (t4-treeorder-proof context))
       (identity (proof-proof-reflexive proof active))
       (lost (proof-proof-rewrite proof identity (car denied) '(1 2 2)))
       (both-nil (t4-treeorder-step-term lost 2))
       (test (proof-term-at both-nil 1))
       (if-true (proof-proof-if-true proof both-nil))
       (if-false (proof-proof-if-false proof both-nil))
       (cases (proof-proof-cases proof test if-true if-false))
       (lost (proof-proof-chain proof lost (list cases)))
       (l-nil (t4-treeorder-simplify context left-active (list false-lt) (list *proof-not*)))
       (context (cdr l-nil))
       (proof (t4-treeorder-proof context))
       (lost-reversed (proof-proof-symmetric proof lost))
       (step (proof-proof-chain proof (car l-nil) (list lost-reversed))))
    (cons step context)))

(defun t4-treeorder-strict-atoms-string (context left-active active facts types same y)
  (t4-treeorder-with-results
      ((equal-strings (proof-proof-assume (t4-treeorder-proof context) same t))
       (reflexive (t4-treeorder-method
                   context :fact-proof-evidence
                   (list (proof-neg (list *t4-treeorder-string-less* y y)) types)))
       (yes (t4-treeorder-strict-atoms-string-yes
             (cdr reflexive) left-active active equal-strings (car reflexive) same))
       (context (cdr yes))
       (no-fact (proof-proof-assume (t4-treeorder-proof context) same nil))
       (premises (append facts (list no-fact)))
       (compared (t4-treeorder-simplify-or-reflexive
                  context active premises (list *t4-treeorder-string-le* *proof-not* *t4-treeorder-eq*)))
       (compared-value (t4-treeorder-step-term (car compared) 2))
       (comparing (t4-treeorder-boolean-comparison (cdr compared) left-active compared-value premises 0))
       (context (cdr comparing))
       (proof (t4-treeorder-proof context))
       (reverse (proof-proof-symmetric proof (car compared)))
       (no (proof-proof-chain proof (car comparing) (list reverse)))
       (step (proof-proof-cases proof same (car yes) no)))
    (cons step context)))

(defun t4-treeorder-strict-atoms-direct (context left at-x direct facts types x y)
  (t4-treeorder-with-results
      ((strict (t4-treeorder-step-term direct 1))
       (l-open (t4-treeorder-simplify-or-reflexive
                context left facts (list *proof-not* *t4-treeorder-eq* *t4-treeorder-num-eq*)))
       (strict-open (t4-treeorder-simplify-or-reflexive
                     (cdr l-open) strict facts (list *t4-treeorder-alphorder*)))
       (context (cdr strict-open))
       (active (t4-treeorder-step-term (car strict-open) 2))
       (paired (t4-treeorder-strict-atoms-atomic-left-atomic-right-paired
                *t4-treeorder-stringp* (t4-structural-evidence-with-proof types (car context)) x y))
       (left-active (t4-treeorder-step-term (car l-open) 2))
       (equal-proof (if (car paired)
                        (t4-treeorder-strict-atoms-string
                         context left-active active facts (cdr paired) (proof-eq x y) y)
                      (t4-treeorder-boolean-comparison context left-active active facts 0)))
       (context (cdr equal-proof))
       (proof (t4-treeorder-proof context))
       (reverse (proof-proof-symmetric proof (car strict-open)))
       (via-direct (proof-proof-chain proof (car l-open) (list (car equal-proof) reverse direct)))
       (step (proof-proof-chain proof at-x (list via-direct))))
    (cons step context)))

(defun t4-treeorder-strict-atoms-chain (result at-x reversed-view)
  (t4-treeorder-with-results
      ((result result)
       (context (cdr result))
       (proof (t4-treeorder-proof context))
       (reverse (proof-proof-symmetric proof reversed-view))
       (step (proof-proof-chain proof at-x (list (car result) reverse))))
    (cons step context)))

(defun t4-treeorder-strict-atoms-atomic-left-atomic-right
    (right-type context left-type at-x reversed-view direct x y)
  (let ((facts (append left-type right-type)))
    (t4-treeorder-with-results
        ((types (t4-structural-evidence-init (car context) nil facts))
         (left (t4-treeorder-step-term at-x 2))
         (right (t4-treeorder-step-term reversed-view 2))
         (complex (t4-treeorder-strict-atoms-atomic-left-atomic-right-paired
                   *t4-treeorder-complex* types x y)))
      (if (car complex)
          (t4-treeorder-strict-atoms-chain
           (t4-treeorder-strict-atoms-complex context left right x y facts) at-x reversed-view)
        (t4-treeorder-with-results
            ((symbols (t4-treeorder-strict-atoms-atomic-left-atomic-right-paired
                       *t4-treeorder-symbolp* (cdr complex) x y)))
          (if (car symbols)
              (t4-treeorder-strict-atoms-chain
               (t4-treeorder-strict-atoms-symbol context left right (cdr symbols) facts (proof-eq x y) y)
               at-x reversed-view)
            (t4-treeorder-with-results
                ((strings (t4-treeorder-strict-atoms-atomic-left-atomic-right-paired
                           *t4-treeorder-stringp* (cdr symbols) x y))
                 (direct-branch (if (car strings)
                                    strings
                                  (t4-treeorder-strict-atoms-untyped-p
                                   *t4-treeorder-types* (cdr strings) x y))))
              (if (car direct-branch)
                  (t4-treeorder-strict-atoms-direct context left at-x direct facts (cdr direct-branch) x y)
                (t4-treeorder-strict-atoms-chain
                 (t4-treeorder-boolean-comparison context left right facts 0) at-x reversed-view)))))))))

(mutual-recursion
 (defun t4-treeorder-type-cases-visit (n kinds denied context value leaf)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "t4-treeorder-type-cases-visit"))
    ((endp kinds) (t4-treeorder-type-cases-leaf (1- n) leaf denied context))
    (t
     (let ((test (list (car kinds) value)))
       (t4-treeorder-with-results
           ((given (t4-treeorder-assume context test t))
            (extra (t4-treeorder-type-cases-case-data (car kinds) given (car context) value))
            (yes (t4-treeorder-type-cases-leaf (1- n) leaf (append denied (cons given extra)) context))
            (context (cdr yes))
            (denial (t4-treeorder-assume context test nil))
            (no (t4-treeorder-type-cases-visit (1- n) (cdr kinds) (append denied (list denial))
                                             context value leaf))
            (context (cdr no))
            (step (proof-proof-cases (t4-treeorder-proof context) test (car yes) (car no))))
         (cons step context))))))
 (defun t4-treeorder-type-cases-leaf (n leaf known context)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "t4-treeorder-type-cases-leaf")
     (case (car leaf)
       (:atomic-order-atoms
        (t4-treeorder-atomic-order-atoms (1- n) known context (cadr leaf) (caddr leaf) (cadddr leaf)))
       (:atomic-order-compare
        (t4-treeorder-atomic-order-atoms-compare known context (cadr leaf) (caddr leaf) (cadddr leaf)))
       (:strict-atoms-left
        (t4-treeorder-strict-atoms-atomic-left
         (1- n) known context (cadr leaf) (caddr leaf) (cadddr leaf)
         (car (cddddr leaf)) (cadr (cddddr leaf))))
       (:strict-atoms-right
        (t4-treeorder-strict-atoms-atomic-left-atomic-right
         known context (cadr leaf) (caddr leaf) (cadddr leaf)
         (car (cddddr leaf)) (cadr (cddddr leaf)) (caddr (cddddr leaf))))
       (otherwise (t4-treeorder-leaf-reply known context leaf)))))
 (defun t4-treeorder-atomic-order-atoms (n x-types context fast opened y)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "t4-treeorder-atomic-order-atoms")
     (let ((definitions (list *t4-treeorder-eq* *proof-not*)))
       (t4-treeorder-with-results
           ((fast-view (t4-treeorder-simplify-or-reflexive context fast x-types definitions))
            (ordinary (t4-treeorder-step-term opened 2))
            (simplified (t4-treeorder-simplify (cdr fast-view) ordinary x-types definitions))
            (context (cdr simplified))
            (ordinary-view (proof-proof-chain (t4-treeorder-proof context) opened (list (car simplified))))
            (cases (t4-treeorder-type-cases-visit
                    (1- n) *t4-treeorder-types* nil context y
                    (list :atomic-order-compare x-types (car fast-view) ordinary-view)))
            (context (cdr cases))
            (proof (t4-treeorder-proof context))
            (reverse (proof-proof-symmetric proof ordinary-view))
            (step (proof-proof-chain proof (car fast-view) (list (car cases) reverse))))
         (cons step context)))))
 (defun t4-treeorder-strict-atoms-atomic-left
     (n left-type context fast reversed-view direct x y)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "t4-treeorder-strict-atoms-atomic-left")
     (t4-treeorder-with-results
         ((at-x (t4-treeorder-simplify-or-reflexive
                 context fast left-type (list *proof-not* *t4-treeorder-eq* *t4-treeorder-num-eq*))))
       (t4-treeorder-type-cases-visit
        (1- n) *t4-treeorder-types* nil (cdr at-x) y
        (list :strict-atoms-right left-type (car at-x) reversed-view direct x y))))))

(defun t4-treeorder-type-cases (context value leaf)
  (t4-treeorder-type-cases-visit 1000000 *t4-treeorder-types* nil context value leaf))

(defun t4-treeorder-atomic-order (context fast ordinary x y)
  (proof-with-checked-results ((opened (proof-proof-unfold (t4-treeorder-proof context) ordinary)))
    (t4-treeorder-type-cases context x (list :atomic-order-atoms fast opened y))))

(defun t4-treeorder-strict-atoms (context fast x y x-atom y-atom)
  (let ((proof (t4-treeorder-proof context))
        (ordinary (proof-neg (list *t4-treeorder-alphorder* y x))))
    (t4-treeorder-with-results
        ((x-test (proof-step-first x-atom))
         (opened-x (proof-proof-unfold proof x-test))
         (noncons-x (proof-proof-rewrite proof x-atom opened-x '(1)))
         (y-test (proof-step-first y-atom))
         (opened-y (proof-proof-unfold proof y-test))
         (noncons-y (proof-proof-rewrite proof y-atom opened-y '(1)))
         (direct (t4-treeorder-complement-order context x y))
         (context (cdr direct))
         (xy (t4-treeorder-atomic-lexorder context x y noncons-x noncons-y))
         (context (cdr xy))
         (direct-step (proof-proof-rewrite (t4-treeorder-proof context) (car direct) (car xy) '(1 1 1)))
         (yx (t4-treeorder-atomic-lexorder context y x noncons-y noncons-x))
         (context (cdr yx))
         (direct-step (proof-proof-rewrite (t4-treeorder-proof context) direct-step (car yx) '(1 2 1)))
         (reversed-view (t4-treeorder-simplify-or-reflexive
                         context ordinary nil
                         (list *t4-treeorder-alphorder* *proof-not* *t4-treeorder-eq* *t4-treeorder-num-eq*))))
      (t4-treeorder-type-cases
       (cdr reversed-view) x (list :strict-atoms-left fast (car reversed-view) direct-step x y)))))

(defun t4-treeorder-selector-bindings (selector x y)
  (list (list x (list selector x)) (list y (list selector y))))

(defun t4-treeorder-substitutions (x y)
  (list (t4-treeorder-selector-bindings *library-car* x y)
        (t4-treeorder-selector-bindings *library-cdr* x y)))

(defun t4-treeorder-compound-argument-p (args)
  (and (consp args)
       (or (proof-compound (car args)) (t4-treeorder-compound-argument-p (cdr args)))))

(defund t4-treeorder-substitute (term bindings)
  (proof-subst term (list (cons (caar bindings) (cadar bindings))
                          (cons (caadr bindings) (cadadr bindings)))))

(defun t4-treeorder-tree-order-equivalence-smaller
    (selectors substitutions context first second tests formula x)
  (if (endp selectors)
      '(:failure "SearchMiss" "")
    (proof-with-checked-results
        ((smaller (t4-treeorder-substitute formula (car substitutions))))
      (if (not (equal (proof-eq first second) smaller))
          (t4-treeorder-tree-order-equivalence-smaller
           (cdr selectors) (cdr substitutions) context first second tests formula x)
        (let* ((lib (car context))
               (proof (t4-treeorder-proof context)))
          (proof-with-checked-results
              ((decrease (library-library-builtin lib (if (equal (car selectors) *library-car*) 2 3) x))
               (evidence (t4-structural-evidence-init lib tests nil))
               (cons-step (t4-structural-evidence-require evidence (list *proof-consp* x)))
               (literal (proof-step-first decrease))
               (assumption (proof-proof-assume proof (proof-ite literal smaller *proof-true*) t))
               (strict (proof-proof-discharge proof decrease (car cons-step)))
               (step (proof-proof-prove-if proof assumption strict)))
            (cons step context)))))))

(defund t4-treeorder-same-if-test-p (first second)
  (and (proof-is-call first *proof-if*)
       (proof-is-call second *proof-if*)
       (proof-with-checked-results ((a (proof-term-at first 1))
                                    (b (proof-term-at second 1)))
         (equal a b))))

(defun t4-treeorder-tree-order-equivalence-case (proof first second step holds)
  (proof-with-checked-results
      ((a (if holds (proof-proof-if-true proof first) (proof-proof-if-false proof first)))
       (b (if holds (proof-proof-if-true proof second) (proof-proof-if-false proof second)))
       (reverse (proof-proof-symmetric proof b)))
    (proof-proof-chain proof a (list step reverse))))

(defun t4-treeorder-tree-order-equivalence-visit
    (n first second tests context formula x y substitutions)
  (declare (xargs :measure (nfix n)))
  (cond
   ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "t4-treeorder-tree-order-equivalence-visit"))
   ((equal first second) (t4-treeorder-reflexive context first))
   ((and (proof-is-call second *t4-treeorder-alphorder*) (equal (cdr second) (list x y)))
    (t4-treeorder-atomic-order context first second x y))
   (t
    (t4-treeorder-with-results
        ((same (t4-treeorder-same-if-test-p first second)))
      (if (not same)
          (t4-treeorder-tree-order-equivalence-smaller
           (list *library-car* *library-cdr*) substitutions context first second tests formula x)
        (let ((test (cadr first)))
          (t4-treeorder-with-results
              ((first-yes (proof-term-at first 2))
               (second-yes (proof-term-at second 2))
               (yes (t4-treeorder-tree-order-equivalence-visit
                     (1- n) first-yes second-yes (append tests (list (list test t)))
                     context formula x y substitutions))
               (first-no (proof-term-at first 3))
               (second-no (proof-term-at second 3))
               (no (t4-treeorder-tree-order-equivalence-visit
                    (1- n) first-no second-no (append tests (list (list test nil)))
                    (cdr yes) formula x y substitutions))
               (context (cdr no))
               (proof (t4-treeorder-proof context))
               (yes-case (t4-treeorder-tree-order-equivalence-case proof first second (car yes) t))
               (no-case (t4-treeorder-tree-order-equivalence-case proof first second (car no) nil))
               (step (proof-proof-cases proof test yes-case no-case)))
            (cons step context))))))))

(defun t4-treeorder-tree-order-equivalence-prove (context formula left right x y)
  (t4-treeorder-with-results
      ((setup (t4-treeorder-method context :use-arithmetic nil))
       (context (cdr setup))
       (proof (t4-treeorder-proof context))
       (a (proof-proof-unfold proof left))
       (b (proof-proof-unfold proof right))
       (substitutions (t4-treeorder-substitutions x y))
       (first (t4-treeorder-step-term a 2))
       (second (t4-treeorder-step-term b 2))
       (visited (t4-treeorder-tree-order-equivalence-visit
                 1000000 first second nil context formula x y substitutions))
       (context (cdr visited))
       (lib (car context))
       (proof (t4-treeorder-proof context))
       (reversed (proof-proof-symmetric proof b))
       (case-proof (proof-proof-chain proof a (list (car visited) reversed)))
       (ordinal (library-library-builtin lib 1 x))
       (step (proof-proof-induct proof ordinal case-proof formula
                                 (t4-structural-count x) substitutions)))
    (cons step lib)))

(defun t4-treeorder-tree-order-equivalence (lib formula recursive replies)
  (if (not (proof-is-call formula *proof-equal*))
      (cons nil lib)
    (proof-with-checked-results ((right (proof-term-at formula 2)))
      (if (not (proof-is-call right *t4-treeorder-lexorder*))
          (cons nil lib)
        (proof-with-checked-results ((sides (proof-list-of-length (cdr formula) 2)))
          (let ((left (car sides)))
            (if (not (proof-compound left))
                (cons nil lib)
              (proof-with-checked-results ((name (proof-term-at left 0)))
                (if (or (equal name (car right))
                        (not (member-equal name recursive))
                        (not (equal (cdr left) (cdr right)))
                        (t4-treeorder-compound-argument-p (cdr right)))
                    (cons nil lib)
                  (proof-with-checked-results
                      ((x (proof-term-at right 1))
                       (y (proof-term-at right 2)))
                    (if (equal x y)
                        (cons nil lib)
                      (proof-with-checked-results ((args (proof-list-of-length (cdr right) 2)))
                        (t4-treeorder-tree-order-equivalence-prove
                         (cons lib replies) formula left right (car args) (cadr args))))))))))))))

(defun t4-treeorder-strict-tree-order-lifted-negative (opening lib rev)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((identity (proof-proof-reflexive proof (proof-neg rev))))
      (proof-proof-rewrite proof identity opening '(1 2 1)))))

(defun t4-treeorder-strict-tree-order-branch-selector
    (lib test sign selector bindings a b rev reverse-claim first x)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left-test (proof-proof-assume proof test sign))
         (right-test (t4-treeorder-reverse-equality lib left-test))
         (first-view (t4-treeorder-choose lib a left-test))
         (chosen (t4-treeorder-choose lib b right-test))
         (second-view (t4-treeorder-strict-tree-order-lifted-negative chosen lib rev))
         (smaller (library-library-builtin lib (if (equal selector *library-cdr*) 3 2) x))
         (comparison (proof-step-first smaller))
         (claim (t4-treeorder-substitute reverse-claim bindings))
         (hypothesis (proof-ite comparison claim *proof-true*))
         (evidence (t4-structural-evidence-init lib (list (list first nil)) nil))
         (cons-step (t4-structural-evidence-require evidence (list *proof-consp* x)))
         (assumption (proof-proof-assume proof hypothesis t))
         (discharged (proof-proof-discharge proof smaller (car cons-step)))
         (smaller-proof (proof-proof-prove-if proof assumption discharged))
         (reverse (proof-proof-symmetric proof second-view)))
      (proof-proof-chain proof first-view (list smaller-proof reverse)))))

(defun t4-treeorder-strict-tree-order-branch
    (x-shape y-shape context f g first second rev reverse-claim substitutions x y)
  (let* ((lib (car context))
         (proof (t4-treeorder-proof context)))
    (t4-treeorder-with-results
        ((has-x (proof-proof-assume proof first x-shape))
         (has-y (proof-proof-assume proof second y-shape))
         (chosen-x (t4-treeorder-choose lib f has-x))
         (a (t4-treeorder-choose lib chosen-x has-y))
         (chosen-y (t4-treeorder-choose lib g has-y))
         (b (t4-treeorder-choose lib chosen-y has-x)))
      (cond
       ((not (equal x-shape y-shape))
        (t4-treeorder-with-results
            ((opened (t4-treeorder-strict-tree-order-lifted-negative b lib rev))
             (value (t4-treeorder-step-term opened 2))
             (simplified (t4-treeorder-simplify context value nil (list *proof-not*)))
             (context (cdr simplified))
             (proof (t4-treeorder-proof context))
             (equality (proof-proof-chain proof opened (list (car simplified))))
             (reverse (proof-proof-symmetric proof equality))
             (step (proof-proof-chain proof a (list reverse))))
          (cons step context)))
       (x-shape
        (t4-treeorder-with-results
            ((value (t4-treeorder-step-term a 2))
             (atoms (t4-treeorder-strict-atoms context value x y has-x has-y))
             (context (cdr atoms))
             (proof (t4-treeorder-proof context))
             (lifted (t4-treeorder-strict-tree-order-lifted-negative b (car context) rev))
             (reverse (proof-proof-symmetric proof lifted))
             (step (proof-proof-chain proof a (list (car atoms) reverse))))
          (cons step context)))
       (t
        (proof-with-checked-results
            ((value (t4-treeorder-step-term a 2))
             (test (proof-term-at value 1))
             (yes (t4-treeorder-strict-tree-order-branch-selector
                   lib test t *library-cdr* (cadr substitutions) a b rev reverse-claim first x))
             (no (t4-treeorder-strict-tree-order-branch-selector
                  lib test nil *library-car* (car substitutions) a b rev reverse-claim first x))
             (step (proof-proof-cases proof test yes no)))
          (cons step context)))))))

(defun t4-treeorder-strict-tree-order-branches (context f g x y rev reverse-claim substitutions)
  (let ((first (list *t4-treeorder-atom* x))
        (second (list *t4-treeorder-atom* y)))
    (t4-treeorder-with-results
        ((yes-yes (t4-treeorder-strict-tree-order-branch
                   t t context f g first second rev reverse-claim substitutions x y))
         (yes-no (t4-treeorder-strict-tree-order-branch
                  t nil (cdr yes-yes) f g first second rev reverse-claim substitutions x y))
         (context (cdr yes-no))
         (yes (proof-proof-cases (t4-treeorder-proof context) second (car yes-yes) (car yes-no)))
         (no-yes (t4-treeorder-strict-tree-order-branch
                  nil t context f g first second rev reverse-claim substitutions x y))
         (no-no (t4-treeorder-strict-tree-order-branch
                 nil nil (cdr no-yes) f g first second rev reverse-claim substitutions x y))
         (context (cdr no-no))
         (proof (t4-treeorder-proof context))
         (no (proof-proof-cases proof second (car no-yes) (car no-no)))
         (ordinal (library-library-builtin (car context) 1 x))
         (cases (proof-proof-cases proof first yes no))
         (step (proof-proof-induct proof ordinal cases reverse-claim
                                   (t4-structural-count x) substitutions)))
      (cons step context))))

(defun t4-treeorder-strict-tree-order-prove (context left specification x y)
  (t4-treeorder-with-results
      ((setup (t4-treeorder-method context :use-arithmetic nil))
       (context (cdr setup))
       (proof (t4-treeorder-proof context))
       (f (proof-proof-unfold proof left))
       (rev (list *t4-treeorder-lexorder* y x))
       (g (proof-proof-unfold proof rev))
       (reverse-claim (proof-eq left (proof-neg rev)))
       (substitutions (t4-treeorder-substitutions x y))
       (cases (t4-treeorder-strict-tree-order-branches context f g x y rev reverse-claim substitutions))
       (complement (t4-treeorder-complement-order (cdr cases) x y))
       (context (cdr complement))
       (proof (t4-treeorder-proof context))
       (direct (proof-proof-symmetric proof (car complement)))
       (reversed (proof-proof-symmetric proof specification))
       (step (proof-proof-chain proof (car cases) (list direct reversed))))
    (cons step (car context))))

(defun t4-treeorder-strict-tree-order (lib formula recursive replies)
  (if (not (proof-is-call formula *proof-equal*))
      (cons nil lib)
    (proof-with-checked-results ((sides (proof-list-of-length (cdr formula) 2)))
      (let ((left (car sides))
            (right (cadr sides)))
        (if (or (not (proof-compound left))
                (not (equal (len left) 3))
                (not (member-equal (car left) recursive))
                (not (proof-compound right))
                (not (equal (cdr left) (cdr right)))
                (t4-treeorder-compound-argument-p (cdr left)))
            (cons nil lib)
          (proof-with-checked-results ((specification (t4-order-strict-equation lib right)))
            (if (not specification)
                (cons nil lib)
              (proof-with-checked-results
                  ((body (t4-treeorder-step-term specification 2))
                   (test (proof-term-at body 1))
                   (head (proof-term-at test 0)))
                (let ((x (cadr left))
                      (y (caddr left)))
                  (if (or (not (equal head *t4-treeorder-lexorder*)) (equal x y))
                      (cons nil lib)
                    (t4-treeorder-strict-tree-order-prove (cons lib replies) left specification x y)))))))))))
