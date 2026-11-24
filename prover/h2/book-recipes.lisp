(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h2-book-recipes-append* (proof-sym "BINARY-APPEND" "ACL2"))
(defconst *h2-book-recipes-listp* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *h2-book-recipes-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *h2-book-recipes-remove* (proof-sym "REMOVE1-EQUAL" "ACL2"))
(defconst *h2-book-recipes-list-fix* (proof-sym "TRUE-LIST-FIX" "ACL2"))
(defconst *h2-book-recipes-duplicity* (proof-sym "DUPLICITY" "ACL2"))
(defconst *h2-book-recipes-alistp* (proof-sym "ALISTP" "ACL2"))
(defconst *h2-book-recipes-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *h2-book-recipes-nat-list* (proof-sym "NAT-LISTP" "ACL2"))
(defconst *h2-book-recipes-header* (proof-sym "HEADER" "ACL2"))
(defconst *h2-book-recipes-compress* (proof-sym "COMPRESS1" "ACL2"))
(defconst *h2-book-recipes-header-key* (proof-quote (proof-sym "HEADER" "KEYWORD")))

(defconst *h2-book-recipes-append-equations*
  (let ((a *h2-book-recipes-append*)
        (f *h2-book-recipes-list-fix*)
        (l *library-len*)
        (x *library-x*)
        (y *library-y*)
        (z *library-z*))
    (list (list (proof-eq (list a (list a x y) z) (list a x (list a y z)))
                (list a) nil)
          (list (proof-eq (list f (list a x y)) (list a x (list f y)))
                (list a f) nil)
          (list (proof-eq (list l (list a x y))
                          (library-plus (list l x) (list l y)))
                (list a l) '("SELF-ADD-ZERO-LEFT" "ASSOCIATIVITY-OF-+")))))

(defun h2-book-recipes-request-p (result)
  (and (consp result) (eq (car result) :h2-book-recipes-request)))

(defun h2-book-recipes-request-operation (request)
  (cadr request))

(defun h2-book-recipes-request-proof (request)
  (caddr request))

(defun h2-book-recipes-request-args (request)
  (cadddr request))

; An execution carries the current BookProof and the unconsumed replies.
(defun h2-book-recipes-operation (execution operation args)
  (let ((proof (car execution))
        (replies (cdr execution)))
    (if (endp replies)
        (list :h2-book-recipes-request operation proof args)
      (let ((reply (car replies)))
        (if (failure-p reply)
            (cons reply (cons proof (cdr replies)))
          (cons (car reply) (cons (cdr reply) (cdr replies))))))))

(defmacro h2-book-recipes-with-result (name form body)
  `(let ((reply ,form))
     (if (or (h2-book-recipes-request-p reply) (failure-p (car reply)))
         reply
       (let ((execution (cdr reply))
             ,@(if name `((,name (car reply))) nil))
         ,body))))

(defmacro h2-book-recipes-checked (bindings body)
  (if (endp bindings)
      body
    (let ((name (caar bindings)))
      `(let (,(car bindings))
         (if (failure-p ,name)
             (cons ,name execution)
           (h2-book-recipes-checked ,(cdr bindings) ,body))))))

(defun h2-book-recipes-output (result keep-unproved)
  (if (h2-book-recipes-request-p result)
      result
    (let ((value (car result)))
      (if (and (failure-p value)
               (not (and keep-unproved (equal (cadr value) "Unproved"))))
          value
        (cons value (cadr result))))))

(defmacro h2-book-recipes-expose (name run arguments)
  `(defun ,name (proof ,@arguments)
     (h2-book-recipes-output (,run (list proof) ,@arguments) nil)))

(defmacro h2-book-recipes-derive (formula &key definitions facts repeat seeds cases)
  `(h2-book-recipes-operation
    execution :derive
    (list ,formula ,(or definitions "") ,facts nil 1 ,(or repeat "") ,seeds ,cases 80)))

(defmacro h2-book-recipes-auxiliary (name formula definitions)
  `(h2-book-recipes-operation
    execution :auxiliary
    (list ,name ,formula ,definitions nil nil 1 "" nil nil 80)))

(defun h2-book-recipes-restore-fixed-calls (result saved)
  (if (h2-book-recipes-request-p result)
      result
    (let ((execution (cdr result)))
      (h2-book-recipes-with-result nil
        (h2-book-recipes-operation execution :restore-fixed-calls (list saved))
        (cons (car result) execution)))))

(defun h2-book-recipes-arguments (term arity)
  (if (integerp term)
      '(:failure "failure" "")
    (proof-list-of-length (cdr term) arity)))

(defun h2-book-recipes-last-term (term)
  (proof-term-at term (if (consp term) (1- (len term)) 0)))

(defun h2-book-recipes-match-append (execution formula equations)
  (if (endp equations)
      (cons nil execution)
    (let* ((equation (car equations))
           (pattern (car equation))
           (definitions (cadr equation))
           (facts (caddr equation)))
      (h2-book-recipes-checked ((matched (h2-search-match pattern formula nil)))
        (let ((variable (cdr (assoc-equal *library-x* (cdr matched)))))
          (if (and (car matched) (not (proof-compound variable)))
              (h2-book-recipes-with-result nil
                (h2-book-recipes-operation execution :configure-book
                                           (list definitions nil facts nil))
                (h2-book-recipes-operation execution :induct-with-folded-calls
                                           (list formula variable definitions)))
            (h2-book-recipes-match-append execution formula (cdr equations))))))))

(defun h2-book-recipes-run-append-equation (execution formula)
  (h2-book-recipes-match-append execution formula *h2-book-recipes-append-equations*))

(h2-book-recipes-expose h2-book-recipes-append-equation
  h2-book-recipes-run-append-equation (formula))

(defun h2-book-recipes-append-recognizer-match (execution formula variable left right)
  (if (or (proof-compound variable)
          (not (proof-compound left))
          (not (equal (len left) 2))
          (not (proof-is-call (cadr left) *h2-book-recipes-append*)))
      (cons nil execution)
    (h2-book-recipes-checked ((parts (h2-book-recipes-arguments (cadr left) 2)))
      (let ((recognizer (car left))
            (first (car parts))
            (tail (cadr parts)))
        (if (or (not (equal first variable))
                (not (equal right (proof-ite (list recognizer first)
                                            (list recognizer tail) *proof-false*))))
            (cons nil execution)
          (h2-book-recipes-with-result library
            (h2-book-recipes-operation execution :library nil)
            (if (not (assoc-equal recognizer
                                  (proof-proof-definitions (library-library-proof library))))
                (cons nil execution)
              (let ((definitions (list *h2-book-recipes-append* *h2-book-recipes-listp* recognizer)))
                (h2-book-recipes-with-result list-rules
                  (h2-book-recipes-operation execution :list-rules nil)
                  (h2-book-recipes-with-result nil
                    (h2-book-recipes-operation execution :configure
                                              (list definitions (cons "built-in-clause-3" list-rules)
                                                    nil 80))
                    (h2-book-recipes-operation execution :induct-with-folded-calls
                                               (list formula variable definitions))))))))))))

(defun h2-book-recipes-run-append-recognizer (execution formula)
  (if (not (proof-is-call formula *library-implies*))
      (cons nil execution)
    (h2-book-recipes-checked ((premise (proof-term-at formula 1)))
      (if (not (proof-is-call premise *h2-book-recipes-listp*))
          (cons nil execution)
        (h2-book-recipes-checked ((claim (proof-term-at formula 2)))
          (if (not (proof-is-call claim *proof-equal*))
              (cons nil execution)
            (h2-book-recipes-checked ((variable (proof-term-at premise 1))
                                     (parts (h2-book-recipes-arguments claim 2)))
              (h2-book-recipes-append-recognizer-match execution formula variable
                                                       (car parts) (cadr parts)))))))))

(h2-book-recipes-expose h2-book-recipes-append-recognizer
  h2-book-recipes-run-append-recognizer (formula))

(defun h2-book-recipes-inverse-step (proof name proof-string package namespace)
  (proof-with-checked-results
      ((fact (proof-proof-fact
              proof (proof-sym "SYMBOL-NAME-INTERN-IN-PACKAGE-OF-SYMBOL" "ACL2")
              (list (list (proof-sym "S" "ACL2") name)
                    (list (proof-sym "ANY-SYMBOL" "ACL2") package))))
       (literal (proof-step-first fact))
       (premise (proof-term-at literal 1))
       (evidence (proof-proof-prove proof premise (list proof-string namespace) nil)))
    (proof-proof-modus-ponens proof fact evidence)))

(defun h2-book-recipes-run-inverse (execution name proof-string package namespace)
  (h2-book-recipes-with-result library (h2-book-recipes-operation execution :library nil)
    (cons (h2-book-recipes-inverse-step (library-library-proof library)
                                      name proof-string package namespace)
          execution)))

(defun h2-book-recipes-injective-intern-inverse (name proof-string proof package namespace)
  (h2-book-recipes-output
   (h2-book-recipes-run-inverse (list proof) name proof-string package namespace) nil))

(defun h2-book-recipes-run-injective-intern (execution formula)
  (h2-book-recipes-checked
      ((formula-parts (h2-book-recipes-arguments formula 2))
       (claim-parts (h2-book-recipes-arguments (cadr formula-parts) 2))
       (comparison (car claim-parts))
       (names (cadr claim-parts))
       (compared (h2-book-recipes-arguments comparison 2))
       (strings (h2-book-recipes-arguments names 2))
       (left (car compared))
       (right (cadr compared))
       (package (proof-term-at left 2)))
    (h2-book-recipes-with-result library (h2-book-recipes-operation execution :library nil)
      (let ((proof (library-library-proof library)))
        (h2-book-recipes-checked
            ((evidence (proof-proof-assume proof (car formula-parts) t))
             (first (proof-proof-conjunct proof evidence))
             (second (proof-proof-conjunct proof (cadr first)))
             (namespace (cadr second))
             (a-identity (h2-book-recipes-inverse-step proof (car strings) (car first)
                                                      package namespace))
             (b-identity (h2-book-recipes-inverse-step proof (cadr strings) (car second)
                                                      package namespace))
             (same-interns (proof-proof-assume proof comparison t))
             (reverse-interns (proof-proof-symmetric proof same-interns))
             (rewritten (proof-proof-rewrite proof b-identity reverse-interns '(1 1 1)))
             (reverse-identity (proof-proof-symmetric proof a-identity))
             (forward (proof-proof-chain proof reverse-identity (list rewritten)))
             (reflexive (proof-proof-reflexive proof left))
             (same-names (proof-proof-assume proof names t))
             (backward (proof-proof-rewrite proof reflexive same-names '(1 2 1)))
             (backward-claim (proof-step-first backward)))
          (if (not (equal backward-claim (proof-eq left right)))
              (cons '(:failure "failure" "") execution)
            (h2-book-recipes-checked
                ((equal-tests (h2-ordering-equal-tests library comparison names forward backward)))
              (cons (h2-search-search-introduce library formula equal-tests) execution))))))))

(h2-book-recipes-expose h2-book-recipes-injective-intern
  h2-book-recipes-run-injective-intern (formula))

(defun h2-book-recipes-run-make-list-recognizer (execution formula)
  (h2-book-recipes-checked
      ((left (proof-term-at formula 1))
       (call (proof-term-at left 1))
       (actuals (h2-book-recipes-arguments call 3)))
    (let ((n (car actuals)) (val (cadr actuals)) (ac (caddr actuals)))
      (h2-book-recipes-with-result library (h2-book-recipes-operation execution :library nil)
        (let ((proof (library-library-proof library)))
          (h2-book-recipes-checked
              ((opening (proof-proof-unfold proof call))
               (opened (proof-step-first opening))
               (body (proof-term-at opened 2))
               (branches (h2-book-recipes-arguments body 3))
               (test (car branches))
               (child (caddr branches))
               (child-n (proof-term-at child 1))
               (child-ac (proof-term-at child 3))
               (updates (list (list n child-n) (list ac child-ac)))
               (descent (library-library-builtin library 9 n))
               (less (proof-step-first descent))
               (reduced (proof-subst formula (proof-bindings-table updates nil)))
               (hypothesis (proof-proof-assume proof (proof-ite less reduced *proof-true*) t))
               (ih (proof-proof-prove-if proof hypothesis descent)))
            (h2-book-recipes-with-result rules (h2-book-recipes-operation execution :list-rules nil)
              (h2-book-recipes-checked
                  ((cons-rule (proof-term-at rules 0))
                   (proper-cons (proof-proof-fact proof (proof-sym cons-rule "ACL2")
                                                 (list (list *library-x* val) (list *library-y* ac))))
                   (inductive (proof-proof-chain proof ih (list proper-cons)))
                   (when-true (proof-proof-if-true proof body))
                   (yes (proof-proof-chain proof opening (list when-true)))
                   (when-false (proof-proof-if-false proof body))
                   (no (proof-proof-chain proof opening (list when-false)))
                   (reflexive (proof-proof-reflexive proof (list *h2-book-recipes-listp* ac)))
                   (reverse-yes (proof-proof-symmetric proof yes))
                   (base (proof-proof-rewrite proof reflexive reverse-yes '(1 1 1)))
                   (reverse-no (proof-proof-symmetric proof no))
                   (step (proof-proof-rewrite proof inductive reverse-no '(1 1 1)))
                   (ordinal (library-library-builtin library 1 n))
                   (cases (proof-proof-cases proof test base step)))
                (cons (proof-proof-induct proof ordinal cases formula
                                          (list *library-count* n) (list updates))
                      execution)))))))))

(h2-book-recipes-expose h2-book-recipes-make-list-recognizer
  h2-book-recipes-run-make-list-recognizer (formula))

(defun h2-book-recipes-gentle-take-branches
  (execution library formula n updates opening body test branch empty fallback cell recursive)
  (let ((proof (library-library-proof library)))
    (h2-book-recipes-checked
        ((nil-is-list (proof-proof-prove proof (list *h2-book-recipes-listp* *proof-false*)
                                         nil (list *h2-book-recipes-listp* (proof-cl "EQ"))))
         (fact (proof-proof-fact proof (proof-sym "TRUE-LISTP-OF-MAKE-LIST-AC" "ACL2")
                                 (seq-zip (list (proof-sym "N" "ACL2") (proof-sym "VAL" "ACL2")
                                               (proof-sym "AC" "ACL2"))
                                         (cdr fallback))))
         (simple (proof-proof-transport proof nil-is-list fact))
         (branch-yes (proof-proof-if-true proof branch))
         (reverse-branch-yes (proof-proof-symmetric proof branch-yes))
         (placed (proof-proof-rewrite-result proof simple reverse-branch-yes
                                             (list *h2-book-recipes-listp* fallback) fallback))
         (branch-no (proof-proof-if-false proof branch))
         (reverse-branch-no (proof-proof-symmetric proof branch-no))
         (nested (proof-proof-rewrite-result proof recursive reverse-branch-no
                                             (list *h2-book-recipes-listp* cell) cell))
         (continuation (proof-proof-cases proof empty placed nested))
         (body-yes (proof-proof-if-true proof body))
         (yes (proof-proof-chain proof opening (list body-yes)))
         (body-no (proof-proof-if-false proof body))
         (no (proof-proof-chain proof opening (list body-no)))
         (base (library-library-transport-argument library nil-is-list yes 1))
         (recursive-case (library-library-transport-argument library continuation no 1))
         (cases (proof-proof-cases proof test base recursive-case))
         (ordinal (library-library-builtin library 1 n)))
      (cons (proof-proof-induct proof ordinal cases formula
                                (list *library-count* n) (list updates))
            execution))))

(defun h2-book-recipes-run-gentle-take (execution formula)
  (h2-book-recipes-checked ((call (proof-term-at formula 1))
                           (actuals (h2-book-recipes-arguments call 2)))
    (let ((n (car actuals)) (data (cadr actuals)))
      (h2-book-recipes-with-result library (h2-book-recipes-operation execution :library nil)
        (let ((proof (library-library-proof library)))
          (h2-book-recipes-checked
              ((opening (proof-proof-unfold proof call))
               (opened (proof-step-first opening))
               (body (proof-term-at opened 2))
               (branches (h2-book-recipes-arguments body 3))
               (test (car branches))
               (branch (caddr branches))
               (inner (h2-book-recipes-arguments branch 3))
               (empty (car inner))
               (fallback (cadr inner))
               (cell (caddr inner))
               (cell-parts (proof-list-of-length cell 3))
               (value (cadr cell-parts))
               (child (caddr cell-parts))
               (child-n (proof-term-at child 1))
               (child-data (proof-term-at child 2))
               (updates (list (list n child-n) (list data child-data)))
               (guard (proof-term-at test 1))
               (assumed (proof-proof-assume proof guard t))
               (guard-equation (proof-proof-unfold proof guard))
               (guard-open (proof-proof-rewrite proof assumed guard-equation '(1)))
               (conditions (proof-proof-conjunct proof guard-open))
               (guarded (library-library-builtin library 14 n))
               (typed (proof-proof-discharge proof guarded (car conditions)))
               (descent (proof-proof-discharge proof typed (cadr conditions)))
               (less (proof-step-first descent))
               (reduced (proof-subst formula (proof-bindings-table updates nil)))
               (hypothesis (proof-proof-assume proof (proof-ite less reduced *proof-true*) t))
               (recursive (proof-proof-prove-if proof hypothesis descent)))
            (h2-book-recipes-with-result rules (h2-book-recipes-operation execution :list-rules nil)
              (h2-book-recipes-checked
                  ((cons-rule (proof-term-at rules 0))
                   (cons-is-list (proof-proof-fact proof (proof-sym cons-rule "ACL2")
                                                   (list (list *library-x* value) (list *library-y* child))))
                   (step (proof-proof-transport proof recursive cons-is-list)))
                (h2-book-recipes-gentle-take-branches
                 execution library formula n updates opening body test branch empty fallback cell step)))))))))

(h2-book-recipes-expose h2-book-recipes-gentle-take
  h2-book-recipes-run-gentle-take (formula))

(defun h2-book-recipes-remove-one-configure (execution formula data definitions facts)
  (h2-book-recipes-with-result nil
    (h2-book-recipes-operation execution :configure
                               (list definitions (cons "built-in-clause-3" facts) nil 80))
    (h2-book-recipes-operation execution :induct-with-folded-calls
                               (list formula data definitions))))

(defun h2-book-recipes-run-remove-one (execution name formula)
  (let ((hint (proof-sym "CONS-WITH-HINT" "ACL2"))
        (remove *h2-book-recipes-remove*)
        (member *h2-book-recipes-member*))
    (h2-book-recipes-with-result facts (h2-book-recipes-operation execution :list-rules nil)
      (cond
       ((equal name "LEN-OF-REMOVE1-EQUAL")
        (h2-book-recipes-checked ((left (proof-term-at formula 1))
                                 (call (proof-term-at left 1))
                                 (data (h2-book-recipes-last-term call)))
          (let* ((len-cons (list *library-len* (list *proof-cons* *library-x* *library-y*)))
                 (len-tail (list *library-len* *library-y*))
                 (goal (proof-eq len-cons (library-plus *proof-one* len-tail))))
            (h2-book-recipes-with-result length-cons
              (h2-book-recipes-auxiliary "LEN-OF-CONS" goal "LEN")
              (h2-book-recipes-remove-one-configure
               execution formula data (list remove member *library-len* hint)
               (append facts (cons length-cons
                                   '("SELF-LEN-INTEGER" "ASSOCIATIVITY-OF-+" "SELF-ADD-ZERO-LEFT"
                                     "SELF-H2-ADD1-SUB1" "SELF-H2-SUB1-ADD1"))))))))
       ((equal name "MEMBER-EQUAL-OF-REMOVE1-EQUAL")
        (h2-book-recipes-checked ((claim (proof-term-at formula 2))
                                 (call (proof-term-at claim 2))
                                 (data (h2-book-recipes-last-term call)))
          (h2-book-recipes-with-result nonnil
            (h2-book-recipes-operation execution :search '(:nonnil-cons))
            (h2-book-recipes-remove-one-configure
             execution formula data (list remove member hint) (append facts (list nonnil))))))
       ((equal name "SUBSETP-EQUAL-OF-REMOVE1-EQUAL-LEFT")
        (h2-book-recipes-checked ((left (proof-term-at formula 1))
                                 (data (proof-term-at left 1)))
          (h2-book-recipes-remove-one-configure
           execution formula data (list remove (proof-sym "SUBSETP-EQUAL" "ACL2") hint) facts)))
       (t
        (h2-book-recipes-checked ((claim (proof-term-at formula 2))
                                 (left (proof-term-at claim 1))
                                 (call (proof-term-at left 1))
                                 (lookup (h2-book-recipes-last-term call))
                                 (data (h2-book-recipes-last-term lookup)))
          (h2-book-recipes-remove-one-configure
           execution formula data (list remove *h2-book-recipes-assoc* hint) facts)))))))

(h2-book-recipes-expose h2-book-recipes-remove-one
  h2-book-recipes-run-remove-one (name formula))

(defun h2-book-recipes-split-array-fields (n proof step)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h2-book-recipes-split-array-fields")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (if (not (proof-is-call literal *proof-if*))
          (list step)
        (proof-with-checked-results ((false-branch (proof-term-at literal 3)))
          (if (not (equal false-branch *proof-false*))
              (list step)
            (proof-with-checked-results
                ((pieces (proof-proof-conjunct proof step))
                 (rest (h2-book-recipes-split-array-fields (1- n) proof (cadr pieces))))
              (cons (car pieces) rest))))))))

(defun h2-book-recipes-array-fields-from-facts (proof condition names)
  (if (endp names)
      nil
    (proof-with-checked-results
        ((literal (proof-step-first condition))
         (bindings (seq-zip (list (proof-sym "NAME" "ACL2") (proof-sym "L" "ACL2"))
                           (cdr literal)))
         (theorem (proof-proof-fact proof (proof-sym (car names) "ACL2") bindings))
         (step (proof-proof-modus-ponens proof theorem condition))
         (fields (h2-book-recipes-split-array-fields 1000000 proof step))
         (rest (h2-book-recipes-array-fields-from-facts proof condition (cdr names))))
      (append fields rest))))

(defun h2-book-recipes-run-array-fields (execution condition)
  (h2-book-recipes-with-result library (h2-book-recipes-operation execution :library nil)
    (cons (h2-book-recipes-array-fields-from-facts
           (library-library-proof library) condition '("ARRAY1P-FORWARD" "ARRAY1P-LINEAR"))
          execution)))

(h2-book-recipes-expose h2-book-recipes-array-fields
  h2-book-recipes-run-array-fields (condition))

(defun h2-book-recipes-compressed-header-cases (execution proof goal old key)
  (h2-book-recipes-checked ((positive (proof-proof-assume proof old t)))
    (h2-book-recipes-with-result found
      (h2-book-recipes-derive goal :definitions "HEADER COMPRESS1 ASSOC-EQUAL"
                             :facts (list key) :seeds (list positive))
      (h2-book-recipes-checked ((negative (proof-proof-assume proof old nil)))
        (h2-book-recipes-with-result missing
          (h2-book-recipes-derive
           goal :definitions "HEADER COMPRESS1 ASSOC-EQUAL ARRAY-ORDER ASSOC-KEYWORD DIMENSIONS DEFAULT COMPRESS11 ZP"
           :facts (list key) :repeat "ASSOC-EQUAL" :seeds (list negative))
          (cons (list found missing) execution))))))

(defun h2-book-recipes-save-compressed-header (execution goal old key name)
  (h2-book-recipes-with-result library (h2-book-recipes-operation execution :library nil)
    (let ((proof (library-library-proof library)))
      (h2-book-recipes-with-result saved
        (h2-book-recipes-operation execution :keep-folded (list (list old)))
        (h2-book-recipes-with-result sides
          (h2-book-recipes-restore-fixed-calls
           (h2-book-recipes-compressed-header-cases execution proof goal old key) saved)
          (h2-book-recipes-checked ((step (proof-proof-cases proof old (car sides) (cadr sides))))
            (h2-book-recipes-with-result nil
              (h2-book-recipes-operation execution :lemma (list "H2-HEADER-OF-COMPRESS1" goal step nil))
              (cons name execution))))))))

(defun h2-book-recipes-run-compressed-header (execution)
  (let ((name "SELF-H2-HEADER-OF-COMPRESS1"))
    (h2-book-recipes-with-result library (h2-book-recipes-operation execution :library nil)
      (let ((proof (library-library-proof library)))
        (if (assoc-equal (proof-sym name "ACL2") (proof-proof-facts proof))
            (cons name execution)
          (let* ((old (list *h2-book-recipes-assoc* *h2-book-recipes-header-key* *library-z*))
                 (comp (list *h2-book-recipes-compress* *library-y* *library-z*))
                 (goal (proof-eq (list *h2-book-recipes-header* *library-x* comp)
                                 (list *h2-book-recipes-header* *library-x* *library-z*))))
            (h2-book-recipes-with-result key
              (h2-book-recipes-operation execution :search '(:assoc-returned-key))
              (h2-book-recipes-save-compressed-header execution goal old key name))))))))

(h2-book-recipes-expose h2-book-recipes-compressed-header
  h2-book-recipes-run-compressed-header ())

(defun h2-book-recipes-derive-folded (execution formula definitions terms)
  (h2-book-recipes-with-result saved
    (h2-book-recipes-operation execution :keep-folded (list terms))
    (h2-book-recipes-restore-fixed-calls
     (h2-book-recipes-derive formula :definitions definitions) saved)))

(defun h2-book-recipes-array-guarded (execution formula definitions header-p)
  (h2-book-recipes-checked ((parts (h2-book-recipes-arguments formula 2)))
    (let ((guard (car parts))
          (goal (cadr parts)))
      (h2-book-recipes-with-result library (h2-book-recipes-operation execution :library nil)
        (h2-book-recipes-checked
            ((premise (proof-proof-assume (library-library-proof library) guard t)))
          (h2-book-recipes-with-result fields
            (h2-book-recipes-run-array-fields execution premise)
            (h2-book-recipes-with-result step
              (h2-book-recipes-derive goal :definitions definitions
                                     :seeds (if header-p (cons premise fields) fields)
                                     :cases (and header-p (list goal)))
              (cons (h2-search-search-introduce library formula step) execution))))))))

(defun h2-book-recipes-find-array-field (fields goal)
  (if (endp fields)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first (car fields))))
      (if (equal literal goal)
          (car fields)
        (h2-book-recipes-find-array-field (cdr fields) goal)))))

(defun h2-book-recipes-consp-header-condition
  (library premise alist header-name data guard)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((name (proof-sym "NAME" "ACL2"))
         (l (proof-sym "L" "ACL2"))
         (classification (proof-proof-fact proof (proof-sym "CONSP-ASSOC-EQUAL" "ACL2")
                                           (list (list name *h2-book-recipes-header-key*) (list l data))))
         (classified (proof-proof-modus-ponens proof classification alist))
         (guard-name (proof-term-at guard 1))
         (existence (proof-proof-fact
                     proof (proof-sym "HEADER-WHEN-ARRAY1P" "ACL2")
                     (list (list (proof-sym "NAME2" "ACL2") guard-name)
                           (list name header-name) (list l data))))
         (exists (proof-proof-modus-ponens proof existence premise))
         (header (proof-step-first exists))
         (opening (proof-proof-unfold proof header))
         (opened (proof-step-first opening))
         (body (proof-term-at opened 2))
         (unwrapped (h2-search-search-remove-wrappers library body))
         (lookup (proof-proof-chain proof opening (list unwrapped)))
         (assoc-exists (proof-proof-rewrite proof exists lookup '(1)))
         (classified-first (proof-step-first classified))
         (consp-call (proof-term-at classified-first 1))
         (absence (proof-proof-assume proof consp-call nil))
         (empty (proof-proof-prove-if proof classified absence))
         (contradiction (proof-proof-rewrite proof assoc-exists empty '(1)))
         (conflict (proof-proof-tidy proof contradiction))
         (cons-proof (proof-proof-front proof conflict consp-call)))
      (library-library-transport-argument library cons-proof lookup 1))))

(defun h2-book-recipes-consp-header (execution formula)
  (h2-book-recipes-checked ((parts (h2-book-recipes-arguments formula 2)))
    (let ((guard (car parts))
          (goal (cadr parts)))
      (h2-book-recipes-with-result library (h2-book-recipes-operation execution :library nil)
        (h2-book-recipes-checked
            ((premise (proof-proof-assume (library-library-proof library) guard t))
             (header (proof-term-at goal 1))
             (arguments (h2-book-recipes-arguments header 2)))
          (let ((name (car arguments))
                (data (cadr arguments)))
            (h2-book-recipes-with-result fields
              (h2-book-recipes-run-array-fields execution premise)
              (h2-book-recipes-checked
                  ((alist (h2-book-recipes-find-array-field fields (list *h2-book-recipes-alistp* data)))
                   (step (h2-book-recipes-consp-header-condition library premise alist name data guard)))
                (cons (h2-search-search-introduce library formula step) execution)))))))))

(defun h2-book-recipes-assoc-header-compress (execution formula preservation)
  (h2-book-recipes-checked
      ((left (proof-term-at formula 1))
       (compressed (proof-term-at left 2))
       (arguments (h2-book-recipes-arguments compressed 2)))
    (let ((comp-name (car arguments)) (data (cadr arguments)))
      (h2-book-recipes-with-result library (h2-book-recipes-operation execution :library nil)
        (let ((proof (library-library-proof library)))
          (h2-book-recipes-checked
              ((lifted (proof-proof-fact proof preservation
                                         (list (list *library-x* comp-name) (list *library-y* comp-name)
                                               (list *library-z* data))))
               (literal (proof-step-first lifted))
               (left (proof-term-at literal 1))
               (header (proof-proof-unfold proof left))
               (opened (proof-step-first header))
               (body (proof-term-at opened 2))
               (unwrapped (h2-search-search-remove-wrappers library body))
               (lookup (proof-proof-chain proof header (list unwrapped)))
               (reverse-lookup (proof-proof-symmetric proof lookup)))
            (cons (proof-proof-chain proof reverse-lookup (list lifted)) execution)))))))

(defun h2-book-recipes-run-array-proof (execution label formula)
  (cond
   ((equal label "ALEN1-INTRO2")
    (let ((first (proof-sym "SELF-H2-NTH-ZERO" "ACL2")))
      (h2-book-recipes-with-result library (h2-book-recipes-operation execution :library nil)
        (if (assoc-equal first (proof-proof-facts (library-library-proof library)))
            (h2-book-recipes-derive formula :definitions "ALEN1" :facts (list first))
          (h2-book-recipes-with-result nil
            (h2-book-recipes-auxiliary "NTH-ZERO"
                                       (proof-eq (list (proof-cl "NTH") *proof-zero* *library-x*)
                                                 (list *library-car* *library-x*))
                                       "NTH ZP")
            (h2-book-recipes-derive formula :definitions "ALEN1" :facts (list first)))))))
   ((member-equal label '("NORMALIZE-ALEN1-NAME" "ALEN1-OF-ACONS-OF-HEADER"))
    (h2-book-recipes-derive formula :definitions "ALEN1 DIMENSIONS HEADER ASSOC-EQUAL ACONS SYNP"))
   ((member-equal label '("ALEN1-OF-CONS" "HEADER-OF-CONS"))
    (h2-book-recipes-checked ((left (proof-term-at formula 1))
                             (cell (proof-term-at left 2))
                             (tail (proof-term-at cell 2)))
      (let ((definitions (if (equal label "ALEN1-OF-CONS")
                             "ALEN1 DIMENSIONS HEADER ASSOC-EQUAL"
                           "HEADER ASSOC-EQUAL")))
        (h2-book-recipes-derive-folded
         execution formula definitions
         (list (list *h2-book-recipes-assoc* *h2-book-recipes-header-key* tail))))))
   ((member-equal label '("INTEGERP-OF-ALEN1-GEN" "POSP-OF-ALEN1" "RATIONALP-OF-ALEN1-WHEN-ARRAY1P"))
    (h2-book-recipes-array-guarded execution formula "ALEN1 DIMENSIONS HEADER POSP" nil))
   ((equal label "HEADER-WHEN-ARRAY1P")
    (h2-book-recipes-array-guarded execution formula "HEADER ASSOC-KEYWORD" t))
   ((equal label "CONSP-OF-HEADER-WHEN-ARRAY1P-FREE")
    (h2-book-recipes-consp-header execution formula))
   ((member-equal label '("EQUAL-OF-HEADER-AND-CAR-OF-HEADER" "CAR-OF-HEADER"))
    (h2-book-recipes-with-result key
      (h2-book-recipes-operation execution :search '(:assoc-returned-key))
      (h2-book-recipes-checked
          ((header (if (equal label "EQUAL-OF-HEADER-AND-CAR-OF-HEADER")
                       (proof-term-at formula 2)
                     (proof-with-checked-results ((left (proof-term-at formula 1)))
                       (proof-term-at left 1))))
           (data (h2-book-recipes-last-term header)))
        (h2-book-recipes-derive
         formula :definitions "HEADER" :facts (list key)
         :cases (list (list *h2-book-recipes-assoc* *h2-book-recipes-header-key* data))))))
   ((equal label "EQUAL-OF-ASSOC-EQUAL-SAME")
    (h2-book-recipes-with-result key
      (h2-book-recipes-operation execution :search '(:assoc-returned-key))
      (h2-book-recipes-checked ((right (proof-term-at formula 2))
                               (test (proof-term-at right 2)))
        (h2-book-recipes-derive formula :facts (list key "SELF-H2-EQUAL-NIL") :cases (list test)))))
   ((member-equal label '("HEADER-OF-COMPRESS1" "MAXIMUM-LENGTH-OF-COMPRESS1" "DIMENSIONS-OF-COMPRESS1"
                          "ALEN1-OF-COMPRESS1" "DEFAULT-OF-COMPRESS1" "ASSOC-EQUAL-OF-HEADER-OF-COMPRESS1"))
    (h2-book-recipes-with-result name (h2-book-recipes-run-compressed-header execution)
      (let ((preservation (proof-sym name "ACL2")))
        (if (equal label "ASSOC-EQUAL-OF-HEADER-OF-COMPRESS1")
            (h2-book-recipes-assoc-header-compress execution formula preservation)
          (let ((definitions (table-get
                              '(("MAXIMUM-LENGTH-OF-COMPRESS1" . "MAXIMUM-LENGTH")
                                ("DIMENSIONS-OF-COMPRESS1" . "DIMENSIONS")
                                ("ALEN1-OF-COMPRESS1" . "ALEN1 DIMENSIONS")
                                ("DEFAULT-OF-COMPRESS1" . "DEFAULT HEADER"))
                              label "")))
            (h2-book-recipes-derive formula :definitions definitions :facts (list preservation)))))))
   (t (cons nil execution))))

(h2-book-recipes-expose h2-book-recipes-array-proof
  h2-book-recipes-run-array-proof (label formula))

(defun h2-book-recipes-fallback-call (execution operation recipe label formula)
  (h2-book-recipes-with-result step
    (h2-book-recipes-operation execution operation (list recipe label formula))
    (if (and (eq recipe :numeric-theorem)
             (consp step) (eq (car step) :h2-book-recipes-folded-induction))
        (h2-book-recipes-operation execution :induct-with-folded-calls (cdr step))
      (cons step execution))))

(defun h2-book-recipes-focus-fallback (execution label formula recipes)
  (if (endp recipes)
      (h2-book-recipes-run-append-recognizer execution formula)
    (h2-book-recipes-with-result step
      (h2-book-recipes-fallback-call execution (caar recipes) (cdar recipes) label formula)
      (if step
          (cons step execution)
        (h2-book-recipes-focus-fallback execution label formula (cdr recipes))))))

(defun h2-book-recipes-pack-arguments (term)
  (if (equal (len term) 2) term '(:failure "failure" "")))

(defun h2-book-recipes-label (name)
  (proof-with-checked-results ((label (proof-term-at name 2)))
    (if (stringp label) label '(:failure "failure" ""))))

(defun h2-book-recipes-focus-by-label (execution label formula)
  (cond
   ((equal label "GENERIC-TAIL-RECURSIVE-DEFPUN-F")
    (h2-book-recipes-operation execution :recipes (list :tail-recursive-equation formula)))
   ((member-equal label '("CHARACTER-LISTP-OF-PACK-LIST" "CHARACTER-LISTP-OF-PACK-TREE"))
    (h2-book-recipes-checked ((call (proof-term-at formula 1))
                             (args (h2-book-recipes-pack-arguments call)))
      (h2-book-recipes-operation execution :search (cons :pack-characters args))))
   ((equal label "NORMALIZE-COMPRESS1-NAME")
    (h2-book-recipes-operation execution :search (list :normalize-compression formula)))
   ((member-equal label '("ALISTP-OF-COMPRESS1" "BOUNDED-INTEGER-ALISTP-OF-COMPRESS1"))
    (h2-book-recipes-operation execution :search (list :compression-list-theorem label formula)))
   ((equal label "ARRAY1P-OF-COMPRESS1")
    (h2-book-recipes-with-result name (h2-book-recipes-run-compressed-header execution)
      (h2-book-recipes-operation execution :search (list :compressed-array formula name))))
   ((member-equal label '("ASSOC-EQUAL-OF-COMPRESS1" "ASSOC-EQUAL-OF-COMPRESS1-WHEN-<"))
    (h2-book-recipes-operation execution :compression-lookup-theorem (list label formula)))
   ((equal label "AREF1-OF-COMPRESS1")
    (h2-book-recipes-operation execution :compressed-aref (list formula)))
   ((equal label "EQUAL-OF-INTERN-IN-PACKAGE-OF-SYMBOLS")
    (h2-book-recipes-run-injective-intern execution formula))
   ((equal label "TRUE-LISTP-OF-MAKE-LIST-AC")
    (h2-book-recipes-run-make-list-recognizer execution formula))
   ((equal label "TRUE-LISTP-OF-GENTLE-TAKE")
    (h2-book-recipes-run-gentle-take execution formula))
   ((equal label "NONNEG-INT-MOD-<-DIVISOR")
    (h2-book-recipes-operation execution :recipes (list :remainder-theorem formula)))
   ((equal label "NONNEG-INT-MOD-NONNEGATIVE-INTEGER-QUOTIENT")
    (h2-book-recipes-operation execution :recipes (list :quotient-remainder formula)))
   ((member-equal label '("NONNEG-INT-MOD-0" "NONNEG-INT-MOD-1"))
    (h2-book-recipes-operation execution :recipes (list :small-remainder formula)))
   ((member-equal label '("DIVISOR-NONNEGATIVE-INTEGER-QUOTIENT" "DIVIDES-WHEN-NONNEG-INT-MOD-0"))
    (h2-book-recipes-operation execution :recipes (list :division-of-exact-multiple label formula)))
   ((equal label "NONNEG-INT-MOD-WHEN-DIVIDES")
    (h2-book-recipes-operation execution :recipes (list :exact-multiple-has-zero-remainder formula)))
   ((equal label "NONNEG-INT-GCD->-0")
    (h2-book-recipes-operation execution :recipes (list :positive-gcd formula)))
   ((equal label "APPEND-UNDER-IFF")
    (h2-book-recipes-with-result truth
      (h2-book-recipes-operation execution :search '(:nonnil-cons))
      (h2-book-recipes-with-result nil
        (h2-book-recipes-operation execution :configure-book
                                   (list (list *h2-book-recipes-append*) nil (list truth) nil))
        (h2-book-recipes-operation execution :solve
                                   (list formula nil (list (list *proof-consp* *library-x*)))))))
   ((member-equal label '("DUPLICITY-WHEN-NOT-CONSP" "DUPLICITY-OF-CONS"))
    (h2-book-recipes-with-result nil
      (h2-book-recipes-operation execution :configure-book (list (list *h2-book-recipes-duplicity*) nil nil nil))
      (h2-book-recipes-operation execution :solve (list formula nil nil))))
   ((equal label "NAT-LISTP-WHEN-NOT-CONSP")
    (h2-book-recipes-derive formula :definitions "NAT-LISTP" :facts '("SELF-H2-EQUAL-NIL")))
   ((equal label "NAT-LISTP-OF-CONS")
    (h2-book-recipes-checked ((left (proof-term-at formula 1))
                             (cell (proof-term-at left 1))
                             (tail (proof-term-at cell 2)))
      (h2-book-recipes-derive-folded execution formula "NAT-LISTP"
                                    (list (list *h2-book-recipes-nat-list* tail)))))
   ((member-equal label '("LEN-OF-REMOVE1-EQUAL" "MEMBER-EQUAL-OF-REMOVE1-EQUAL"
                          "SUBSETP-EQUAL-OF-REMOVE1-EQUAL-LEFT" "ASSOC-EQUAL-OF-REMOVE1-EQUAL"))
    (h2-book-recipes-run-remove-one execution label formula))
   (t
    (h2-book-recipes-with-result step
      (h2-book-recipes-run-array-proof execution label formula)
      (if step
          (cons step execution)
        (h2-book-recipes-focus-fallback
         execution label formula
         '((:recipes . :measure-theorem)
           (:recipes . :subsequence-theorem)
           (:search . :set-theorem)
           (:recipes . :numeric-theorem)
           (:search . :product-theorem)
           (:search . :count-theorem))))))))

(defun h2-book-recipes-run-focused-proof (execution name formula)
  (h2-book-recipes-checked ((label (h2-book-recipes-label name)))
    (h2-book-recipes-with-result appended
      (h2-book-recipes-run-append-equation execution formula)
      (if appended
          (cons appended execution)
        (h2-book-recipes-with-result binomial
          (h2-book-recipes-operation execution :search (list :binomial-theorem label formula))
          (if binomial
              (cons binomial execution)
            (h2-book-recipes-focus-by-label execution label formula)))))))

(h2-book-recipes-expose h2-book-recipes-focused-proof
  h2-book-recipes-run-focused-proof (name formula))

(defun h2-book-recipes-focused-proof-with-replies (proof name formula replies)
  (h2-book-recipes-output (h2-book-recipes-run-focused-proof (cons proof replies) name formula) t))

(defun h2-book-recipes-call-with-replies (proof recipe args replies)
  (let* ((execution (cons proof replies))
         (result
          (case recipe
            (:focused-proof (h2-book-recipes-run-focused-proof execution (car args) (cadr args)))
            (:append-equation (h2-book-recipes-run-append-equation execution (car args)))
            (:append-recognizer (h2-book-recipes-run-append-recognizer execution (car args)))
            (:injective-intern (h2-book-recipes-run-injective-intern execution (car args)))
            (:injective-intern-inverse
             (h2-book-recipes-run-inverse execution (nth 0 args) (nth 1 args) (nth 2 args) (nth 3 args)))
            (:make-list-recognizer (h2-book-recipes-run-make-list-recognizer execution (car args)))
            (:gentle-take (h2-book-recipes-run-gentle-take execution (car args)))
            (:remove-one (h2-book-recipes-run-remove-one execution (car args) (cadr args)))
            (:array-fields (h2-book-recipes-run-array-fields execution (car args)))
            (:compressed-header (h2-book-recipes-run-compressed-header execution))
            (:array-proof (h2-book-recipes-run-array-proof execution (car args) (cadr args)))
            (otherwise (cons '(:failure "failure" "") execution)))))
    (h2-book-recipes-output result t)))

; These dispatch forms expand where the book prover answers a request.
(defmacro h2-book-recipes-search-call (search recipe args)
  `(let ((search ,search)
         (recipe ,recipe)
         (args ,args))
     (let ((result
            (case recipe
              (:nonnil-cons (h2-book-logic-nonnil-cons search))
              (:assoc-returned-key (h2-book-logic-assoc-returned-key search))
              (:binomial-theorem (h2-binomial-binomial-theorem search (car args) (cadr args)))
              (:pack-characters (h2-characters-pack-characters search (car args) (cadr args)))
              (:normalize-compression (h2-compression-normalize-compression search (car args)))
              (:compression-list-theorem (h2-compression-compression-list-theorem search (car args) (cadr args)))
              (:compressed-array (h2-compression-compressed-array search (car args) (cadr args)))
              (:set-theorem (h2-sets-set-theorem search (car args) (cadr args)))
              (:product-theorem (h2-products-product-theorem search (car args) (cadr args)))
              (:count-theorem (h2-list-counts-count-theorem search (car args) (cadr args)))
              (otherwise '(:failure "failure" "")))))
       (if (h2-search-request-p (car result)) (car result) result))))

(defmacro h2-book-recipes-recipes-call (recipes recipe args)
  `(let ((recipes ,recipes)
         (recipe ,recipe)
         (args ,args))
     (let ((result
            (case recipe
              (:tail-recursive-equation (h2-tail-recursion-tail-recursive-equation recipes (car args)))
              (:remainder-theorem (h2-modular-remainder-theorem recipes (car args)))
              (:quotient-remainder (h2-modular-quotient-remainder recipes (car args)))
              (:small-remainder (h2-modular-small-remainder recipes (car args)))
              (:division-of-exact-multiple (h2-modular-division-of-exact-multiple recipes (car args) (cadr args)))
              (:exact-multiple-has-zero-remainder (h2-modular-exact-multiple-has-zero-remainder recipes (car args)))
              (:positive-gcd (h2-modular-positive-gcd recipes (car args)))
              (:measure-theorem (h2-ordinals-measure-theorem recipes (car args) (cadr args)))
              (:subsequence-theorem (h2-subsequence-subsequence-theorem recipes (car args) (cadr args)))
              (:numeric-theorem (h2-numeric-recipes-numeric-theorem recipes (car args) (cadr args)))
              (otherwise '(:failure "failure" "")))))
       (cond ((h2-search-request-p (car result)) (car result))
             ((and (eq recipe :numeric-theorem) (h2-numeric-recipes-folded-request-p (car result)))
              (cons (cons :h2-book-recipes-folded-induction
                          (h2-numeric-recipes-folded-request-args (car result)))
                    (cdr result)))
             (t result)))))
