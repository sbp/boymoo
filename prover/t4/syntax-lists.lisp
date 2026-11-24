(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t4-syntax-lists-atom* (proof-cl "ATOM"))
(defconst *t4-syntax-lists-endp* (proof-cl "ENDP"))
(defconst *t4-syntax-lists-eq* (proof-cl "EQ"))
(defconst *t4-syntax-lists-symbolp* (proof-cl "SYMBOLP"))
(defconst *t4-syntax-lists-term* (proof-sym "PSEUDO-TERMP" "ACL2"))
(defconst *t4-syntax-lists-terms* (proof-sym "PSEUDO-TERM-LISTP" "ACL2"))
(defconst *t4-syntax-lists-clauses* (proof-sym "PSEUDO-TERM-LIST-LISTP" "ACL2"))
(defconst *t4-syntax-lists-force* (proof-sym "FORCE" "ACL2"))
(defconst *t4-syntax-lists-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *t4-syntax-lists-and-list* (proof-sym "AND-LIST" "ACL2"))
(defconst *t4-syntax-lists-or-list* (proof-sym "OR-LIST" "ACL2"))
(defconst *t4-syntax-lists-iff* (proof-sym "IFF" "ACL2"))
(defconst *t4-syntax-lists-iff-list* (proof-sym "IFF-LIST" "ACL2"))
(defconst *t4-syntax-lists-disjoin* (proof-sym "DISJOIN" "ACL2"))
(defconst *t4-syntax-lists-disjoin-list* (proof-sym "DISJOIN-LST" "ACL2"))
(defconst *t4-syntax-lists-conjoin* (proof-sym "CONJOIN" "ACL2"))
(defconst *t4-syntax-lists-conjoin-clauses* (proof-sym "CONJOIN-CLAUSES" "ACL2"))
(defconst *t4-syntax-lists-clauses-result* (proof-sym "CLAUSES-RESULT" "ACL2"))
(defconst *t4-syntax-lists-list-types*
  (list (cons *t4-syntax-lists-terms* *t4-syntax-lists-term*)
        (cons *t4-syntax-lists-clauses* *t4-syntax-lists-terms*)))
(defconst *t4-syntax-lists-flag* (proof-sym "T4-LIST-BRANCH" "ACL2"))

(defun t4-syntax-lists-step-at (step index)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun t4-syntax-lists-prove (n lib term evidence definitions)
  (let ((result (if (zp n)
                    '(:failure "Fuel" "t4-syntax-lists-prove")
                  (t4-ordinals-ordinals-prove lib term evidence definitions))))
    (if (failure-p result)
        (cons result lib)
      result)))

(defun t4-syntax-lists-choose (lib equation condition)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((body (t4-syntax-lists-step-at equation 2))
         (branch (proof-proof-select proof body condition)))
      (proof-proof-chain proof equation (list branch)))))

(defund t4-syntax-lists-open-body-step (proof equation)
  (proof-with-checked-results
      ((body (t4-syntax-lists-step-at equation 2))
       (head (and (proof-compound body) (proof-term-at body 0))))
    (if (and (proof-compound body) (proof-compound head))
        (proof-with-checked-results
            ((beta (proof-proof-beta proof body))
             (next (proof-proof-chain proof equation (list beta))))
          (list :open-body next))
      equation)))

(defun t4-syntax-lists-open-body-visit (n proof equation)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      '(:failure "Fuel" "t4-syntax-lists-open-body-visit")
    (let ((result (t4-syntax-lists-open-body-step proof equation)))
      (if (eq (car result) :open-body)
          (t4-syntax-lists-open-body-visit (1- n) proof (cadr result))
        result))))

(defun t4-syntax-lists-open-body (lib call)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((equation (proof-proof-unfold proof call)))
      (t4-syntax-lists-open-body-visit 1000000 proof equation))))

(defun t4-syntax-lists-spine-opening (lib call shape)
  (proof-with-checked-results
      ((equation (t4-syntax-lists-open-body lib call))
       (body (t4-syntax-lists-step-at equation 2))
       (test (proof-term-at body 1))
       (obj (proof-term-at test 1)))
    (if (not (member-equal test (list (list *t4-syntax-lists-atom* obj)
                                     (list *t4-syntax-lists-endp* obj)
                                     (list *proof-consp* obj))))
        '(:failure "InferenceMismatch" "")
      (proof-with-checked-results ((literal (proof-step-first shape)))
        (let* ((cons-test (list *proof-consp* obj))
               (positive (equal literal cons-test))
               (sign (if (equal (car test) *proof-consp*) positive (not positive))))
          (if (or positive (equal literal (proof-neg cons-test)))
              (list equation (if sign test (proof-neg test)))
            '(:failure "InferenceMismatch" "")))))))

(defun t4-syntax-lists-project-one (lib equation pair name)
  (proof-with-checked-results
      ((equality (library-library-axiom lib name (cdr pair)))
       (right (t4-syntax-lists-step-at equation 2))
       (left (t4-syntax-lists-step-at equality 1)))
    (proof-proof-rewrite-result (library-library-proof lib) equation equality
                                (proof-eq *proof-result* right) left)))

(defund t4-syntax-lists-project-pair (lib equation pair)
  (proof-with-checked-results
      ((after-car (t4-syntax-lists-project-one lib equation pair "CAR-CONS")))
    (t4-syntax-lists-project-one lib after-car pair "CDR-CONS")))

(defun t4-syntax-lists-projections (lib equation pair)
  (declare (xargs :measure (acl2-count pair)))
  (if (and (consp pair) (proof-is-call pair *proof-cons*))
      (proof-with-checked-results ((projected (t4-syntax-lists-project-pair lib equation pair)))
        (if (consp (cddr pair))
            (t4-syntax-lists-projections lib projected (caddr pair))
          (proof-term-at pair 2)))
    equation))

(defun t4-syntax-lists-consp-cons (lib pair)
  (proof-proof-fact (library-library-proof lib) "consp-cons"
                   (seq-zip (list *library-x* *library-y*) (cdr pair))))

(defund t4-syntax-lists-lift-one (lib step equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((backward (proof-proof-symmetric proof equation)))
      (proof-proof-rewrite-first proof step backward))))

(defun t4-syntax-lists-lift-proof (lib step equations)
  (declare (xargs :measure (acl2-count equations)))
  (if (endp equations)
      step
    (proof-with-checked-results
        ((rewritten (t4-syntax-lists-lift-one lib step (car equations))))
      (t4-syntax-lists-lift-proof lib rewritten (cdr equations)))))

(defun t4-syntax-lists-recur (lib formula obj selector number)
  (let* ((proof (library-library-proof lib))
         (actual (list selector obj))
         (binding (list (list obj actual))))
    (proof-with-checked-results
        ((smaller (library-library-builtin lib number obj))
         (comparison (proof-step-first smaller))
         (substituted (proof-subst formula (list (cons obj actual))))
         (assumption (proof-proof-assume proof (proof-ite comparison substituted *proof-true*) t))
         (step (proof-proof-prove-if proof assumption smaller)))
      (list step binding))))

(defun t4-syntax-lists-iff-forward (lib equivalence premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((call (proof-step-first equivalence)))
      (if (not (proof-is-call call *t4-syntax-lists-iff*))
          '(:failure "InferenceMismatch" "")
        (proof-with-checked-results
            ((antecedent (proof-term-at call 1))
             (literal (proof-step-first premise)))
          (if (not (equal antecedent literal))
              '(:failure "InferenceMismatch" "")
            (proof-with-checked-results
                ((opening (proof-proof-unfold proof call))
                 (unfolded (proof-proof-rewrite proof equivalence opening '(1)))
                 (selected (proof-proof-prove-if proof unfolded premise))
                 (parts (proof-proof-conjunct proof selected)))
              (car parts))))))))

(defun t4-syntax-lists-request-p (value)
  (and (consp value) (eq (car value) :call)))

(defun t4-syntax-lists-request (lib replies operation arguments)
  (if (endp replies)
      (list (list :call operation arguments) lib nil)
    (let ((reply (car replies)))
      (if (failure-p reply)
          (list reply lib (cdr replies))
        (list (car reply) (cdr reply) (cdr replies))))))

(defmacro t4-syntax-lists-with-replies (bindings result)
  (if (endp bindings)
      result
    (let* ((name (caar bindings))
           (form (cadar bindings))
           (kind (caddar bindings))
           (rest (cdr bindings))
           (body `(if (or (failure-p ,name) (t4-syntax-lists-request-p ,name))
                      (list ,name lib replies)
                    (t4-syntax-lists-with-replies ,rest ,result))))
      (if (eq kind :recipe)
          `(let* ((reply ,form)
                  (lib (cadr reply))
                  (replies (caddr reply))
                  (,name (car reply)))
             ,body)
        `(let ((,name ,form)) ,body)))))

(defun t4-syntax-lists-result (outcome)
  (cons (car outcome) (cadr outcome)))

(defun t4-syntax-lists-context-prove (lib term evidence definitions contextual replies)
  (if contextual
      (t4-syntax-lists-request lib replies :prove (list term evidence definitions))
    (let ((result (t4-syntax-lists-prove 1000000 lib term evidence definitions)))
      (list (car result) (cdr result) replies))))

(defun t4-syntax-lists-context-constant (lib term contextual replies)
  (if contextual
      (t4-syntax-lists-request lib replies :constant (list term))
    (let ((result (t4-ordinals-ordinals-constant lib term)))
      (if (failure-p result)
          (list result lib replies)
        (list (car result) (cdr result) replies)))))

(defun t4-syntax-lists-spine-run (lib call shape contextual replies)
  (t4-syntax-lists-with-replies
      ((opening (t4-syntax-lists-spine-opening lib call shape))
       (premise (t4-syntax-lists-context-prove
                 lib (cadr opening) (list shape)
                 (list *t4-syntax-lists-atom* *t4-syntax-lists-endp* *proof-not*)
                 contextual replies) :recipe))
    (list (t4-syntax-lists-choose lib (car opening) premise) lib replies)))

(defun t4-syntax-lists-spine (lib call shape)
  (t4-syntax-lists-result (t4-syntax-lists-spine-run lib call shape nil nil)))

(defun t4-syntax-lists-spine-with-replies (lib call shape replies)
  (t4-syntax-lists-result (t4-syntax-lists-spine-run lib call shape t replies)))

(defun t4-syntax-lists-constructed-view-run (lib call pair contextual replies)
  (t4-syntax-lists-with-replies
      ((pair-cons (t4-syntax-lists-consp-cons lib pair))
       (equation (t4-syntax-lists-spine-run lib call pair-cons contextual replies) :recipe))
    (list (t4-syntax-lists-projections lib equation pair) lib replies)))

(defun t4-syntax-lists-constructed-view (lib call pair)
  (t4-syntax-lists-result (t4-syntax-lists-constructed-view-run lib call pair nil nil)))

(defun t4-syntax-lists-constructed-view-with-replies (lib call pair replies)
  (t4-syntax-lists-result (t4-syntax-lists-constructed-view-run lib call pair t replies)))

(defun t4-syntax-lists-syntax-type-visit (n lib call premises contextual replies)
  (declare (xargs :measure (nfix n)))
  (if (not (o< (nfix (1- n)) (nfix n)))
      (list '(:failure "Fuel" "t4-syntax-lists-syntax-type-visit") lib replies)
    (let ((known (assoc-equal call premises)))
      (if known
          (list (cdr known) lib replies)
        (t4-syntax-lists-with-replies ((parts (proof-list-of-length call 2)))
          (let* ((operator (car parts))
                 (datum (cadr parts))
                 (element-type (cdr (assoc-equal operator *t4-syntax-lists-list-types*))))
            (cond
             ((and element-type (equal datum *proof-false*))
              (t4-syntax-lists-context-prove lib call nil
                                            (list operator *t4-syntax-lists-atom* *proof-not*)
                                            contextual replies))
             ((or (and (not element-type) (not (equal operator *t4-syntax-lists-term*)))
                  (not (proof-is-call datum *proof-cons*)))
              (list '(:failure "SearchMiss" "")
                    lib replies))
             (t
              (t4-syntax-lists-with-replies
                  ((equation (t4-syntax-lists-constructed-view-run lib call datum contextual replies)
                             :recipe))
                (if element-type
                    (t4-syntax-lists-with-replies
                        ((head (proof-term-at datum 1))
                         (typed-head (t4-syntax-lists-syntax-type-visit
                                      (1- n) lib (list element-type head) premises contextual replies)
                                     :recipe)
                         (tail (proof-term-at datum 2))
                         (typed-tail (t4-syntax-lists-syntax-type-visit
                                      (1- n) lib (list operator tail) premises contextual replies)
                                     :recipe)
                         (combined (t4-division-combine lib (list typed-head typed-tail))))
                      (list (proof-proof-transport (library-library-proof lib) combined equation)
                            lib replies))
                  (t4-syntax-lists-with-replies
                      ((fields (proof-list-of-length (cdr datum) 2)))
                    (let ((tag (car fields))
                          (args (cadr fields)))
                      (if (or (not (proof-is-call tag *proof-quote*))
                              (equal tag (proof-quote *proof-quote*)))
                          (list '(:failure "SearchMiss" "") lib replies)
                        (t4-syntax-lists-with-replies
                            ((body (t4-syntax-lists-step-at equation 2))
                             (test (proof-term-at body 1))
                             (unequal (t4-syntax-lists-context-prove
                                       lib (proof-neg test) nil (list *t4-syntax-lists-eq* *proof-not*)
                                       contextual replies) :recipe)
                             (equation (t4-syntax-lists-choose lib equation unequal))
                             (typed (t4-syntax-lists-syntax-type-visit
                                     (1- n) lib (list *t4-syntax-lists-terms* args) premises
                                     contextual replies) :recipe)
                             (typed-first (proof-step-first typed))
                             (positive (t4-syntax-lists-context-prove
                                        lib (proof-neg (proof-neg typed-first)) (list typed)
                                        (list *proof-not*) contextual replies) :recipe)
                             (equation (t4-syntax-lists-choose lib equation positive))
                             (symbol-equation (t4-syntax-lists-context-constant
                                               lib (list *t4-syntax-lists-symbolp* tag)
                                               contextual replies) :recipe)
                             (tagged (proof-proof-true-from-eq
                                      (library-library-proof lib) symbol-equation))
                             (equation (t4-syntax-lists-choose lib equation tagged))
                             (tagged-first (proof-step-first tagged))
                             (tag-equation (t4-syntax-lists-context-constant
                                            lib tagged-first contextual replies) :recipe)
                             (joined (proof-proof-chain (library-library-proof lib)
                                                        equation (list tag-equation))))
                          (list (proof-proof-true-from-eq (library-library-proof lib) joined)
                                lib replies)))))))))))))))

(defun t4-syntax-lists-syntax-type (lib call premises)
  (t4-syntax-lists-result (t4-syntax-lists-syntax-type-visit 1000000 lib call premises nil nil)))

(defun t4-syntax-lists-syntax-type-with-replies (lib call premises replies)
  (t4-syntax-lists-result (t4-syntax-lists-syntax-type-visit 1000000 lib call premises t replies)))

(defun t4-syntax-lists-evaluate-run (lib call premises replies)
  (t4-syntax-lists-with-replies
      ((equation (t4-syntax-lists-request lib replies :evaluator-equation (list call premises))
                 :recipe))
    (if (not equation)
        (list '(:failure "SearchMiss" "")
              lib replies)
      (t4-syntax-lists-with-replies ((pair (proof-term-at call 1)))
        (list (t4-syntax-lists-projections lib equation pair) lib replies)))))

(defun t4-syntax-lists-evaluate (lib call premises replies)
  (t4-syntax-lists-result (t4-syntax-lists-evaluate-run lib call premises replies)))

(defun t4-syntax-lists-iff-transitive-run (lib first second replies)
  (t4-syntax-lists-with-replies
      ((first-head (t4-syntax-lists-step-at first 0))
       (second-head (t4-syntax-lists-step-at second 0)))
    (if (not (and (equal first-head second-head) (equal second-head *t4-syntax-lists-iff*)))
        (list '(:failure "InferenceMismatch" "") lib replies)
      (t4-syntax-lists-with-replies
          ((middle (t4-syntax-lists-step-at first 2))
           (next-middle (t4-syntax-lists-step-at second 1)))
        (if (not (equal middle next-middle))
            (list '(:failure "InferenceMismatch" "") lib replies)
          (t4-syntax-lists-with-replies
              ((premise (t4-division-combine lib (list first second)))
               (left (t4-syntax-lists-step-at first 1))
               (right (t4-syntax-lists-step-at second 2))
               (hypothesis (proof-step-first premise))
               (thesis (list *t4-syntax-lists-iff* left right))
               (rule (t4-syntax-lists-request
                      lib replies :fact-proof (list (list *library-implies* hypothesis thesis) nil))
                     :recipe))
            (if (not rule)
                (list '(:failure "SearchMiss" "") lib replies)
              (list (proof-proof-modus-ponens (library-library-proof lib) rule premise)
                    lib replies))))))))

(defun t4-syntax-lists-iff-transitive (lib first second replies)
  (t4-syntax-lists-result (t4-syntax-lists-iff-transitive-run lib first second replies)))

(defun t4-syntax-lists-disjunction-run (lib evaluator list-evaluator clause environment replies)
  (let ((term (list *t4-syntax-lists-iff*
                    (list evaluator (list *t4-syntax-lists-disjoin* clause) environment)
                    (list *t4-syntax-lists-or-list* (list list-evaluator clause environment)))))
    (t4-syntax-lists-with-replies
        ((fact (t4-syntax-lists-request lib replies :fact-proof (list term nil)) :recipe))
      (list (or fact '(:failure "SearchMiss" ""))
            lib replies))))

(defun t4-syntax-lists-disjunction (lib evaluator list-evaluator clause environment replies)
  (t4-syntax-lists-result
   (t4-syntax-lists-disjunction-run lib evaluator list-evaluator clause environment replies)))

(defun t4-syntax-lists-induct (lib obj result formula bindings)
  (proof-with-checked-results ((ordinal (library-library-builtin lib 1 obj)))
    (proof-proof-induct (library-library-proof lib) ordinal result formula
                        (t4-structural-count obj) bindings)))

(defun t4-syntax-lists-record-premises (steps facts)
  (declare (xargs :measure (acl2-count steps)))
  (if (endp steps)
      facts
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (t4-syntax-lists-record-premises (cdr steps)
                                       (table-put facts literal (car steps))))))

(defun t4-syntax-lists-force-guards (lib guards forced)
  (declare (xargs :measure (acl2-count guards)))
  (if (endp guards)
      forced
    (proof-with-checked-results ((literal (proof-step-first (car guards))))
      (if (proof-is-call literal *t4-syntax-lists-force*)
          (let ((proof (library-library-proof lib)))
            (proof-with-checked-results
                ((key (proof-term-at literal 1))
                 (unfolded (proof-proof-unfold proof literal))
                 (premise (proof-proof-rewrite proof (car guards) unfolded '(1))))
              (t4-syntax-lists-force-guards lib (cdr guards) (table-put forced key premise))))
        (t4-syntax-lists-force-guards lib (cdr guards) forced)))))

(defun t4-syntax-lists-guard-premise (forced obj)
  (if (endp forced)
      nil
    (let ((term (caar forced)))
      (if (and (proof-compound term) (equal (cdr term) (list obj)))
          (cdar forced)
        (t4-syntax-lists-guard-premise (cdr forced) obj)))))

(defun t4-syntax-lists-induction-guards (lib guards premise rest-guard)
  (if (endp guards)
      nil
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((literal (proof-step-first (car guards)))
           (guard
            (if (equal literal (list *t4-syntax-lists-force* premise))
                (proof-with-checked-results
                    ((rest-literal (proof-step-first rest-guard))
                     (opening (proof-proof-unfold proof (list *t4-syntax-lists-force* rest-literal))))
                  (proof-proof-transport proof rest-guard opening))
              (car guards)))
           (rest (t4-syntax-lists-induction-guards lib (cdr guards) premise rest-guard)))
        (cons guard rest)))))

(defun t4-syntax-lists-list-typing-branches (lib operator exact head rest explicit replies)
  (if explicit
      (t4-syntax-lists-with-replies
          ((exact (t4-syntax-lists-choose lib exact head))
           (yes (proof-proof-chain (library-library-proof lib) exact (list rest)))
           (empty (proof-proof-unfold (library-library-proof lib) (list operator *proof-false*)))
           (right (t4-syntax-lists-step-at empty 2))
           (reduced (t4-syntax-lists-request
                     lib replies :simplify (list right nil (list *t4-syntax-lists-atom* *proof-not*)))
                    :recipe)
           (no (proof-proof-chain (library-library-proof lib) empty (list reduced))))
        (list (list yes no) lib replies))
    (t4-syntax-lists-with-replies
        ((combined (t4-division-combine lib (list head rest)))
         (yes (proof-proof-transport (library-library-proof lib) combined exact))
         (no (t4-syntax-lists-syntax-type-visit
              1000000 lib (list operator *proof-false*) nil t replies) :recipe))
      (list (list yes no) lib replies))))

(defun t4-syntax-lists-list-typing-finish (lib formula call operator obj explicit
                                             guard ih binding guards forced premise replies)
  (let ((shape (list *proof-consp* obj)))
    (t4-syntax-lists-with-replies
        ((cons-proof (proof-proof-assume (library-library-proof lib) shape t))
         (premise-term (proof-step-first premise))
         (unfolded (t4-syntax-lists-spine-run lib premise-term cons-proof t replies) :recipe)
         (rewritten (proof-proof-rewrite (library-library-proof lib) premise unfolded '(1)))
         (children (t4-division-pieces lib rewritten))
         (rest-guard (proof-find-evidence children (list (list (car premise-term)
                                                               (list *library-cdr* obj))))))
      (if (not rest-guard)
          (list nil lib replies)
        (t4-syntax-lists-with-replies
            ((ih-guard (t4-syntax-lists-induction-guards lib guards premise-term rest-guard))
             (combined (t4-division-combine lib ih-guard))
             (rest (proof-proof-modus-ponens (library-library-proof lib) ih combined))
             (view (t4-syntax-lists-spine-run lib call cons-proof t replies) :recipe)
             (pair (t4-syntax-lists-step-at view 2))
             (exact (t4-syntax-lists-constructed-view-run
                     lib (list operator pair) pair t replies) :recipe)
             (facts (t4-syntax-lists-record-premises (append children (table-values forced)) nil))
             (datum (proof-term-at pair 1))
             (head (t4-syntax-lists-syntax-type-visit
                    1000000 lib (list (cdr (assoc-equal operator *t4-syntax-lists-list-types*)) datum)
                    facts t replies) :recipe)
             (branches (t4-syntax-lists-list-typing-branches
                        lib operator exact head rest explicit replies) :recipe)
             (yes (t4-syntax-lists-lift-proof lib (car branches) (list view)))
             (atom-proof (proof-proof-assume (library-library-proof lib) shape nil))
             (atom-view (t4-syntax-lists-spine-run lib call atom-proof t replies) :recipe)
             (no (t4-syntax-lists-lift-proof lib (cadr branches) (list atom-view)))
             (cases (proof-proof-cases (library-library-proof lib) shape yes no))
             (result (t4-ordinals-ordinals-imply lib guard cases)))
          (list (t4-syntax-lists-induct lib obj result formula (list binding)) lib replies))))))

(defun t4-syntax-lists-list-typing-prove (lib formula guard call operator obj explicit replies)
  (t4-syntax-lists-with-replies
      ((arithmetic (t4-syntax-lists-request lib replies :use-arithmetic nil) :recipe)
       (recur (t4-syntax-lists-recur lib formula obj *library-cdr* 3))
       (assumed (proof-proof-assume (library-library-proof lib) guard t))
       (guards (t4-division-pieces lib assumed))
       (forced (t4-syntax-lists-force-guards lib guards nil))
       (premise (t4-syntax-lists-guard-premise forced obj)))
    (if premise
        (t4-syntax-lists-list-typing-finish lib formula call operator obj explicit
                                           guard (car recur) (cadr recur) guards forced premise replies)
      (list nil lib replies))))

(defun t4-syntax-lists-list-typing-definition-p (definition call obj)
  (if (not (proof-is-call definition *proof-if*))
      nil
    (proof-with-checked-results ((test (proof-term-at definition 1)))
      (if (not (member-equal test (list (list *t4-syntax-lists-atom* obj)
                                       (list *t4-syntax-lists-endp* obj))))
          nil
        (proof-with-checked-results ((base (proof-term-at definition 2)))
          (if (not (equal base *proof-false*))
              nil
            (proof-with-checked-results ((branch (proof-term-at definition 3)))
              (if (not (proof-is-call branch *proof-cons*))
                  nil
                (proof-with-checked-results ((tail (proof-term-at branch 2)))
                  (equal tail (list* (car call) (list *library-cdr* obj) (cddr call))))))))))))

(defun t4-syntax-lists-list-typing-run (lib formula recursive replies)
  (if (not (proof-is-call formula *library-implies*))
      (list nil lib replies)
    (t4-syntax-lists-with-replies
        ((parts (proof-list-of-length (cdr formula) 2))
         (guard (car parts))
         (target (cadr parts))
         (rhs (and (proof-is-call target *proof-equal*) (proof-term-at target 2)))
         (explicit (equal rhs *proof-true*))
         (recognized (if explicit (proof-term-at target 1) target))
         (operator (and (proof-compound recognized) (proof-term-at recognized 0))))
      (if (not (assoc-equal operator *t4-syntax-lists-list-types*))
          (list nil lib replies)
        (t4-syntax-lists-with-replies
            ((call (proof-term-at recognized 1))
             (name (and (proof-compound call) (proof-term-at call 0))))
          (if (not (and (proof-compound call) (member-equal name recursive)))
              (list nil lib replies)
            (t4-syntax-lists-with-replies
                ((recognized (proof-list-of-length recognized 2))
                 (call (cadr recognized))
                 (obj (proof-term-at call 1)))
              (if (proof-compound obj)
                  (list nil lib replies)
                (t4-syntax-lists-with-replies
                    ((opening (proof-proof-unfold (library-library-proof lib) call))
                     (definition (t4-syntax-lists-step-at opening 2))
                     (applicable (t4-syntax-lists-list-typing-definition-p definition call obj)))
                  (if applicable
                      (t4-syntax-lists-list-typing-prove lib formula guard call operator obj
                                                        explicit replies)
                    (list nil lib replies)))))))))))

(defun t4-syntax-lists-list-typing (lib formula recursive replies)
  (t4-syntax-lists-result (t4-syntax-lists-list-typing-run lib formula recursive replies)))

(defun t4-syntax-lists-binding-evaluation-prove (lib formula guard conclusion lookup
                                                     variable obj list-eval syntax env replies)
  (let ((shape (list *proof-consp* obj)))
    (t4-syntax-lists-with-replies
        ((arithmetic (t4-syntax-lists-request lib replies :use-arithmetic nil) :recipe)
         (cons-proof (proof-proof-assume (library-library-proof lib) shape t))
         (atom-proof (proof-proof-assume (library-library-proof lib) shape nil))
         (assumed (proof-proof-assume (library-library-proof lib) guard t))
         (parts (t4-division-pieces lib assumed))
         (parts (proof-list-of-length parts 2))
         (tests (car parts))
         (found (cadr parts))
         (nil-lookup (t4-syntax-lists-spine-run lib lookup atom-proof t replies) :recipe)
         (empty (proof-proof-rewrite-first (library-library-proof lib) found nil-lookup))
         (empty-literal (proof-step-first empty))
         (constant (t4-syntax-lists-request lib replies :constant (list empty-literal)) :recipe)
         (empty (if constant
                    (proof-proof-rewrite (library-library-proof lib) empty constant '(1))
                  '(:failure "failure" "")))
         (absent (proof-proof-subsume (library-library-proof lib) empty
                                      (list conclusion shape (proof-neg guard))))
         (source (t4-syntax-lists-spine-run lib syntax cons-proof t replies) :recipe)
         (pair (t4-syntax-lists-step-at source 2)))
      (if (not (proof-is-call pair *proof-cons*))
          (list '(:failure "InferenceMismatch" "") lib replies)
        (t4-syntax-lists-with-replies
            ((evaluated (t4-syntax-lists-evaluate-run lib (list list-eval pair env) nil replies)
                        :recipe)
             (evaluated-values (t4-syntax-lists-step-at evaluated 2))
             (folded (t4-syntax-lists-constructed-view-run
                      lib (list *t4-syntax-lists-and-list* evaluated-values) evaluated-values
                      t replies) :recipe)
             (tests (proof-proof-rewrite-first (library-library-proof lib) tests source))
             (tests (proof-proof-rewrite-first (library-library-proof lib) tests evaluated))
             (tests (proof-proof-rewrite-first (library-library-proof lib) tests folded))
             (parts (t4-division-pieces lib tests))
             (parts (proof-list-of-length parts 2))
             (first (car parts))
             (rest (cadr parts))
             (first-literal (proof-step-first first))
             (head (t4-syntax-lists-evaluate-run lib first-literal nil replies) :recipe)
             (equality (proof-proof-rewrite (library-library-proof lib) first head '(1)))
             (match (proof-eq variable (list *library-car* (list *library-car* obj))))
             (searched (t4-syntax-lists-spine-run lib lookup cons-proof t replies) :recipe))
          (let ((proof (library-library-proof lib)))
            (t4-syntax-lists-with-replies
                ((same-match (proof-proof-assume proof match t))
                 (at-head (t4-syntax-lists-choose lib searched same-match))
                 (reverse-equality (proof-proof-symmetric proof equality))
                 (reverse-head (proof-proof-symmetric proof at-head))
                 (same (proof-proof-rewrite proof reverse-equality reverse-head '(1 1 1 1)))
                 (same-match (proof-proof-assume proof match t))
                 (reverse-match (proof-proof-symmetric proof same-match))
                 (same (proof-proof-rewrite proof same reverse-match '(1 2 1)))
                 (same (proof-proof-tidy proof same))
                 (different (proof-proof-assume proof match nil))
                 (tail (t4-syntax-lists-choose lib searched different))
                 (recur (t4-syntax-lists-recur lib formula obj *library-cdr* 3))
                 (next-hit (proof-proof-rewrite-first proof found tail))
                 (combined (t4-division-combine lib (list rest next-hit)))
                 (next-result (proof-proof-modus-ponens proof (car recur) combined))
                 (later (t4-syntax-lists-lift-proof lib next-result (list tail)))
                 (matched (proof-proof-cases proof match same later))
                 (cases (proof-proof-cases proof shape matched absent))
                 (result (t4-ordinals-ordinals-imply lib guard cases)))
              (list (t4-syntax-lists-induct lib obj result formula (list (cadr recur)))
                    lib replies))))))))

(defun t4-syntax-lists-binding-evaluation-fold (lib formula guard conclusion fold hit functions replies)
  (t4-syntax-lists-with-replies ((lookup (proof-term-at hit 1)))
    (if (not (proof-is-call lookup *t4-syntax-lists-assoc*))
        (list nil lib replies)
      (t4-syntax-lists-with-replies ((eval-call (proof-term-at fold 1)))
        (if (not (and (proof-compound eval-call) (eql (len eval-call) 3)))
            (list nil lib replies)
          (t4-syntax-lists-with-replies
              ((lookup-args (proof-list-of-length (cdr lookup) 2))
               (variable (car lookup-args))
               (obj (cadr lookup-args))
               (list-eval (car eval-call))
               (syntax (cadr eval-call))
               (env (caddr eval-call))
               (left (proof-term-at conclusion 1))
               (evaluator (and (proof-compound left) (proof-term-at left 0))))
            (if (and (member-equal list-eval functions)
                     (member-equal evaluator functions)
                     (equal (cdr conclusion)
                            (list (list evaluator (list *library-cdr* lookup) env)
                                  (list evaluator variable env)))
                     (proof-compound syntax)
                     (equal (cdr syntax) (list obj))
                     (not (proof-compound obj)))
                (t4-syntax-lists-binding-evaluation-prove lib formula guard conclusion lookup
                                                         variable obj list-eval syntax env replies)
              (list nil lib replies))))))))

(defun t4-syntax-lists-binding-evaluation-run (lib formula functions replies)
  (if (not (proof-is-call formula *library-implies*))
      (list nil lib replies)
    (t4-syntax-lists-with-replies ((conclusion (proof-term-at formula 2)))
      (if (not (proof-is-call conclusion *proof-equal*))
          (list nil lib replies)
        (t4-syntax-lists-with-replies
            ((parts (proof-list-of-length (cdr formula) 2))
             (guard (car parts)))
          (if (not (proof-is-call guard *proof-if*))
              (list nil lib replies)
            (t4-syntax-lists-with-replies ((failure (proof-term-at guard 3)))
              (if (not (equal failure *proof-false*))
                  (list nil lib replies)
                (t4-syntax-lists-with-replies ((fold (proof-term-at guard 1)))
                  (if (not (proof-is-call fold *t4-syntax-lists-and-list*))
                      (list nil lib replies)
                    (t4-syntax-lists-with-replies ((hit (proof-term-at guard 2)))
                      (if (proof-is-call hit *proof-consp*)
                          (t4-syntax-lists-binding-evaluation-fold lib formula guard conclusion fold
                                                                  hit functions replies)
                        (list nil lib replies)))))))))))))

(defun t4-syntax-lists-binding-evaluation (lib formula functions replies)
  (t4-syntax-lists-result (t4-syntax-lists-binding-evaluation-run lib formula functions replies)))

(defun t4-syntax-lists-prove-substitution-hypothesis (selector as-term lib obj joint satisfied)
  (let* ((proof (library-library-proof lib))
         (mode (if as-term *proof-true* *proof-false*))
         (binding (list (list obj (list selector obj)) (list *t4-syntax-lists-flag* mode))))
    (proof-with-checked-results
        ((decrease (library-library-builtin lib (if (equal selector *library-car*) 2 3) obj))
         (tests (proof-step-first decrease))
         (specialized (proof-subst joint (table-put (list (cons obj (list selector obj)))
                                                     *t4-syntax-lists-flag* mode)))
         (assumed (proof-proof-assume proof (proof-ite tests specialized *proof-true*) t))
         (smaller (proof-proof-prove-if proof assumed decrease))
         (mode-proof (if as-term
                         (proof-proof-prove proof *proof-true* nil nil)
                       (proof-proof-not-nil proof)))
         (selected (proof-proof-prove-if proof smaller mode-proof))
         (result (proof-proof-modus-ponens proof selected satisfied)))
      (list result binding))))

(defun t4-syntax-lists-restore-evaluator-input (lib eval-before equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reflexive (proof-proof-reflexive proof eval-before))
         (backward (proof-proof-symmetric proof equation)))
      (proof-proof-rewrite proof reflexive backward '(1 1 1)))))

(defun t4-syntax-lists-prove-substitution-app (lib rebuilt tag-test eval-before list-evaluator
                                                  evaluator env cons-proof on-tail pair replies)
  (t4-syntax-lists-with-replies
      ((unmatched (proof-proof-assume (library-library-proof lib) tag-test nil))
       (tag-def (proof-proof-unfold (library-library-proof lib) tag-test))
       (before-tag (proof-proof-rewrite (library-library-proof lib) unmatched tag-def '(1 1)))
       (before-tag (proof-proof-tidy (library-library-proof lib) before-tag))
       (car-eq (library-library-axiom lib "CAR-CONS" (cdr pair)))
       (car-back (proof-proof-symmetric (library-library-proof lib) car-eq))
       (after-tag (proof-proof-rewrite (library-library-proof lib) before-tag car-back '(1 1 1)))
       (after-shape (t4-syntax-lists-consp-cons lib pair))
       (before (t4-syntax-lists-request
                lib replies :evaluator-reapply (list eval-before list-evaluator cons-proof before-tag))
               :recipe)
       (after (t4-syntax-lists-request
               lib replies :evaluator-reapply
               (list (list evaluator pair env) list-evaluator after-shape after-tag)) :recipe)
       (after (t4-syntax-lists-projections lib after pair))
       (equal-app (proof-proof-rewrite (library-library-proof lib) after on-tail '(1 2 1 2 1)))
       (before-back (proof-proof-symmetric (library-library-proof lib) before))
       (app (proof-proof-chain (library-library-proof lib) equal-app (list before-back))))
    (list (t4-syntax-lists-lift-proof lib app (list rebuilt)) lib replies)))

(defun t4-syntax-lists-prove-substitution-missing (lib term-view hit obj subst-list bindings
                                                      eval-before list-evaluator evaluator env
                                                      shape cons-proof atom-proof on-tail replies)
  (let ((stop (list *t4-syntax-lists-atom* obj))
        (tag-test (list *t4-syntax-lists-eq* (list *library-car* obj) (proof-quote *proof-quote*)))
        (definitions (list *t4-syntax-lists-atom* *proof-not*)))
    (t4-syntax-lists-with-replies
        ((assumed (proof-proof-assume (library-library-proof lib) hit nil))
         (missing (t4-syntax-lists-choose lib term-view assumed))
         (halt (t4-syntax-lists-request lib replies :prove (list stop (list atom-proof) definitions))
               :recipe)
         (unchanged-atom (t4-syntax-lists-choose lib missing halt))
         (atom-result (t4-syntax-lists-restore-evaluator-input lib eval-before unchanged-atom))
         (kept (t4-syntax-lists-request
                lib replies :prove (list (proof-neg stop) (list cons-proof) definitions)) :recipe)
         (app (t4-syntax-lists-choose lib missing kept))
         (quoted (proof-proof-assume (library-library-proof lib) tag-test t))
         (unchanged-quote (t4-syntax-lists-choose lib app quoted))
         (quote-result (t4-syntax-lists-restore-evaluator-input lib eval-before unchanged-quote))
         (different (proof-proof-assume (library-library-proof lib) tag-test nil))
         (rebuilt (t4-syntax-lists-choose lib app different))
         (pair (t4-syntax-lists-step-at rebuilt 2)))
      (if (not (equal pair (list *proof-cons* (list *library-car* obj)
                                 (list subst-list (list *library-cdr* obj) bindings))))
          (list '(:failure "InferenceMismatch" "") lib replies)
        (t4-syntax-lists-with-replies
            ((app-result (t4-syntax-lists-prove-substitution-app
                          lib rebuilt tag-test eval-before list-evaluator evaluator env
                          cons-proof on-tail pair replies) :recipe)
             (tag-cases (proof-proof-cases (library-library-proof lib) tag-test quote-result app-result)))
          (list (proof-proof-cases (library-library-proof lib) shape tag-cases atom-result)
                lib replies))))))

(defun t4-syntax-lists-prove-substitution-term (lib term obj bindings subst-list eval-before
                                                   list-evaluator evaluator env valid satisfied shape
                                                   cons-proof atom-proof on-tail replies)
  (let* ((lookup (list *t4-syntax-lists-assoc* obj bindings))
         (hit (list *proof-consp* lookup)))
    (t4-syntax-lists-with-replies
        ((term-view (t4-syntax-lists-open-body lib term))
         (hit-proof (proof-proof-assume (library-library-proof lib) hit t))
         (found (t4-syntax-lists-choose lib term-view hit-proof))
         (right (t4-syntax-lists-step-at found 2))
         (want (proof-eq (list evaluator right env) eval-before))
         (hit-proof (proof-proof-assume (library-library-proof lib) hit t))
         (validity (t4-division-combine lib (list satisfied hit-proof)))
         (pieces (t4-division-pieces lib validity))
         (observed (t4-syntax-lists-request lib replies :fact-proof (list want pieces)) :recipe))
      (if (not observed)
          (list '(:failure "SearchMiss" "")
                lib replies)
        (t4-syntax-lists-with-replies
            ((found-result (t4-syntax-lists-lift-proof lib observed (list found)))
             (missing (t4-syntax-lists-prove-substitution-missing
                       lib term-view hit obj subst-list bindings eval-before list-evaluator
                       evaluator env shape cons-proof atom-proof on-tail replies) :recipe)
             (cases (proof-proof-cases (library-library-proof lib) hit found-result missing)))
          (list (t4-ordinals-ordinals-imply lib valid cases) lib replies))))))

(defun t4-syntax-lists-prove-substitution-list (lib terms list-before list-evaluator env valid shape
                                                   cons-proof atom-proof on-head on-tail replies)
  (t4-syntax-lists-with-replies
      ((nil-pair (t4-syntax-lists-spine-run lib terms atom-proof t replies) :recipe)
       (nil-after (t4-syntax-lists-evaluate-run
                   lib (list list-evaluator *proof-false* env) nil replies) :recipe)
       (nil-before (t4-syntax-lists-evaluate-run lib list-before (list atom-proof) replies) :recipe)
       (nil-back (proof-proof-symmetric (library-library-proof lib) nil-before))
       (nil-joined (proof-proof-chain (library-library-proof lib) nil-after (list nil-back)))
       (nil-result (t4-syntax-lists-lift-proof lib nil-joined (list nil-pair)))
       (list-view (t4-syntax-lists-spine-run lib terms cons-proof t replies) :recipe)
       (right (t4-syntax-lists-step-at list-view 2))
       (list-after (t4-syntax-lists-evaluate-run lib (list list-evaluator right env) nil replies)
                   :recipe)
       (list-cons (t4-syntax-lists-evaluate-run lib list-before (list cons-proof) replies) :recipe)
       (list-after (proof-proof-rewrite (library-library-proof lib) list-after on-head '(1 2 1)))
       (list-after (proof-proof-rewrite (library-library-proof lib) list-after on-tail '(1 2 2)))
       (list-back (proof-proof-symmetric (library-library-proof lib) list-cons))
       (cons-joined (proof-proof-chain (library-library-proof lib) list-after (list list-back)))
       (cons-result (t4-syntax-lists-lift-proof lib cons-joined (list list-view)))
       (cases (proof-proof-cases (library-library-proof lib) shape cons-result nil-result)))
    (list (t4-ordinals-ordinals-imply lib valid cases) lib replies)))

(defun t4-syntax-lists-prove-substitution-run (lib name joint term terms eval-before list-before replies)
  (t4-syntax-lists-with-replies
      ((joint-parts (proof-list-of-length (cdr joint) 3))
       (valid (proof-term-at (cadr joint-parts) 1))
       (satisfied (proof-proof-assume (library-library-proof lib) valid t))
       (term-parts (proof-list-of-length term 3))
       (obj (cadr term-parts))
       (bindings (caddr term-parts))
       (subst-list (proof-term-at terms 0))
       (eval-parts (proof-list-of-length eval-before 3))
       (evaluator (car eval-parts))
       (env (caddr eval-parts))
       (list-evaluator (proof-term-at list-before 0))
       (shape (list *proof-consp* obj))
       (cons-proof (proof-proof-assume (library-library-proof lib) shape t))
       (atom-proof (proof-proof-assume (library-library-proof lib) shape nil))
       (head (t4-syntax-lists-prove-substitution-hypothesis *library-car* t lib obj joint satisfied))
       (tail (t4-syntax-lists-prove-substitution-hypothesis *library-cdr* nil lib obj joint satisfied))
       (term-result (t4-syntax-lists-prove-substitution-term
                     lib term obj bindings subst-list eval-before list-evaluator evaluator env
                     valid satisfied shape cons-proof atom-proof (car tail) replies) :recipe)
       (list-result (t4-syntax-lists-prove-substitution-list
                     lib terms list-before list-evaluator env valid shape cons-proof atom-proof
                     (car head) (car tail) replies) :recipe)
       (if-true (proof-proof-if-true (library-library-proof lib) joint))
       (yes (proof-proof-transport (library-library-proof lib) term-result if-true))
       (if-false (proof-proof-if-false (library-library-proof lib) joint))
       (no (proof-proof-transport (library-library-proof lib) list-result if-false))
       (cases (proof-proof-cases (library-library-proof lib) *t4-syntax-lists-flag* yes no))
       (step (t4-syntax-lists-induct lib obj cases joint (list (cadr head) (cadr tail))))
       (new-library (library-library-lemma lib name joint step nil)))
    (list nil new-library replies)))

(defun t4-syntax-lists-prove-substitution (lib name joint term terms eval-before list-before replies)
  (t4-syntax-lists-result
   (t4-syntax-lists-prove-substitution-run lib name joint term terms eval-before list-before replies)))

(defun t4-syntax-lists-substitution-term-mode (expanded)
  (if (not (proof-is-call expanded *proof-if*))
      nil
    (proof-with-checked-results ((branch (proof-term-at expanded 3)))
      (if (not (proof-is-call branch *proof-if*))
          nil
        (proof-with-checked-results ((dispatch (proof-term-at branch 3)))
          (if (not (proof-is-call dispatch *proof-if*))
              nil
            (proof-with-checked-results ((candidate (proof-term-at dispatch 3)))
              (if (not (proof-is-call candidate *proof-cons*))
                  nil
                (proof-with-checked-results ((tail (proof-term-at candidate 2)))
                  (and (proof-compound tail)
                       (proof-with-checked-results ((function (proof-term-at tail 0)))
                         (list function))))))))))))

(defun t4-syntax-lists-substitution-list-mode (expanded)
  (if (not (proof-is-call expanded *proof-if*))
      nil
    (proof-with-checked-results ((branch (proof-term-at expanded 3)))
      (if (not (proof-is-call branch *proof-cons*))
          nil
        (proof-with-checked-results ((candidate (proof-term-at branch 1)))
          (and (proof-compound candidate)
               (proof-with-checked-results ((function (proof-term-at candidate 0)))
                 (list function))))))))

(defun t4-syntax-lists-substitution-modes (reapplications function operator expanded)
  (if (endp reapplications)
      nil
    (let* ((key (caar reapplications))
           (eval-term (car key))
           (eval-list (cadr key)))
      (proof-with-checked-results
          ((term-mode (and (equal function eval-term)
                           (t4-syntax-lists-substitution-term-mode expanded))))
        (if term-mode
            (proof-with-checked-results ((subst-list (car term-mode)))
              (list eval-term eval-list operator subst-list))
          (proof-with-checked-results
              ((list-mode (and (equal function eval-list)
                               (t4-syntax-lists-substitution-list-mode expanded))))
            (if list-mode
                (proof-with-checked-results ((subst-term (car list-mode)))
                  (list eval-term eval-list subst-term operator))
              (t4-syntax-lists-substitution-modes (cdr reapplications)
                                                  function operator expanded))))))))

(defun t4-syntax-lists-substitution-satisfied-p (step eval-list environment bindings)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (if (not (proof-is-call literal *t4-syntax-lists-and-list*))
        nil
      (proof-with-checked-results ((call (proof-term-at literal 1)))
        (if (not (proof-is-call call eval-list))
            nil
          (proof-with-checked-results ((env (proof-term-at call 2)))
            (if (not (equal env environment))
                nil
              (proof-with-checked-results ((alist (proof-term-at call 1)))
                (and (proof-compound alist) (equal (cdr alist) (list bindings)))))))))))

(defun t4-syntax-lists-substitution-satisfied (evidence eval-list environment bindings)
  (if (endp evidence)
      nil
    (proof-with-checked-results
        ((matches (t4-syntax-lists-substitution-satisfied-p (car evidence) eval-list environment bindings)))
      (if matches
          (car evidence)
        (t4-syntax-lists-substitution-satisfied (cdr evidence) eval-list environment bindings)))))

(defun t4-syntax-lists-substitution-evaluation-finish (lib guard operator obj bindings env
                                                          modes satisfied replies)
  (let ((eval-term (nth 0 modes))
        (eval-list (nth 1 modes))
        (subst-term (nth 2 modes))
        (subst-list (nth 3 modes)))
    (t4-syntax-lists-with-replies
        ((arithmetic (t4-syntax-lists-request lib replies :use-arithmetic nil) :recipe)
         (name (proof-term-at subst-term 2))
         (key (concatenate 'string "EVAL-SUBSTITUTION-" name))
         (valid (proof-step-first satisfied))
         (term (list subst-term *library-x* bindings))
         (terms (list subst-list *library-x* bindings))
         (eval-before (list eval-term *library-x* env))
         (list-before (list eval-list *library-x* env))
         (at-term (list *library-implies* valid (proof-eq (list eval-term term env) eval-before)))
         (at-list (list *library-implies* valid (proof-eq (list eval-list terms env) list-before)))
         (joint (proof-ite *t4-syntax-lists-flag* at-term at-list))
         (lemma (proof-sym (concatenate 'string "SELF-" key) "ACL2"))
         (existing (assoc-equal lemma (proof-proof-facts (library-library-proof lib))))
         (established (if existing
                          (list nil lib replies)
                        (t4-syntax-lists-prove-substitution-run lib key joint term terms
                                                               eval-before list-before replies))
                      :recipe)
         (mode (if (equal operator subst-term) *proof-true* *proof-false*))
         (result (proof-proof-fact (library-library-proof lib) lemma
                                  (list (list *t4-syntax-lists-flag* mode) (list *library-x* obj))))
         (mode-evidence (if (equal mode *proof-true*)
                            (proof-proof-prove (library-library-proof lib) *proof-true* nil nil)
                          (proof-proof-not-nil (library-library-proof lib))))
         (conditional (proof-proof-prove-if (library-library-proof lib) result mode-evidence))
         (exact (proof-proof-modus-ponens (library-library-proof lib) conditional satisfied)))
      (list (t4-ordinals-ordinals-imply lib guard exact) lib replies))))

(defun t4-syntax-lists-substitution-evaluation-modes (lib guard left reapplications replies)
  (let* ((operator (caadr left))
         (obj (cadadr left))
         (bindings (caddr (cadr left)))
         (env (caddr left)))
    (if (or (proof-compound obj) (proof-compound bindings) (proof-compound env))
        (list nil lib replies)
      (t4-syntax-lists-with-replies
          ((opening (t4-syntax-lists-open-body lib (cadr left)))
           (expanded (t4-syntax-lists-step-at opening 2))
           (modes (t4-syntax-lists-substitution-modes reapplications (car left) operator expanded)))
        (let ((definitions (proof-proof-definitions (library-library-proof lib))))
          (if (not (and modes (assoc-equal (nth 2 modes) definitions)
                        (assoc-equal (nth 3 modes) definitions)))
              (list nil lib replies)
            (t4-syntax-lists-with-replies
                ((assumed (proof-proof-assume (library-library-proof lib) guard t))
                 (evidence (t4-division-pieces lib assumed))
                 (satisfied (t4-syntax-lists-substitution-satisfied evidence (cadr modes) env bindings)))
              (if satisfied
                  (t4-syntax-lists-substitution-evaluation-finish
                   lib guard operator obj bindings env modes satisfied replies)
                (list nil lib replies)))))))))

(defun t4-syntax-lists-substitution-evaluation-run (lib formula functions reapplications replies)
  (if (not (proof-is-call formula *library-implies*))
      (list nil lib replies)
    (t4-syntax-lists-with-replies ((conclusion (proof-term-at formula 2)))
      (if (not (proof-is-call conclusion *proof-equal*))
          (list nil lib replies)
        (t4-syntax-lists-with-replies
            ((parts (proof-list-of-length (cdr formula) 2))
             (endpoints (proof-list-of-length (cdr conclusion) 2)))
          (let ((guard (car parts))
                (left (car endpoints))
                (right (cadr endpoints)))
            (if (and (proof-compound left) (eql (len left) 3)
                     (member-equal (car left) functions)
                     (proof-compound (cadr left)) (eql (len (cadr left)) 3)
                     (proof-is-call right (car left))
                     (equal (cdr right) (list (cadadr left) (caddr left)))
                     (assoc-equal (caadr left) (proof-proof-definitions (library-library-proof lib))))
                (t4-syntax-lists-substitution-evaluation-modes lib guard left reapplications replies)
              (list nil lib replies))))))))

(defun t4-syntax-lists-substitution-evaluation (lib formula functions reapplications replies)
  (t4-syntax-lists-result
   (t4-syntax-lists-substitution-evaluation-run lib formula functions reapplications replies)))

(defun t4-syntax-lists-evaluated-clause-map-show (lib value call replies)
  (if (proof-is-call value *proof-cons*)
      (t4-syntax-lists-with-replies
          ((shown (t4-syntax-lists-constructed-view-run lib call value t replies) :recipe))
        (list shown lib replies))
    (t4-syntax-lists-with-replies
        ((denial (t4-syntax-lists-request
                  lib replies :prove
                  (list (proof-neg (list *proof-consp* *proof-false*)) nil (list *proof-not*)))
                 :recipe)
         (shown (t4-syntax-lists-spine-run lib call denial t replies) :recipe))
      (list shown lib replies))))

(defun t4-syntax-lists-evaluated-clause-map-transformed (spine-shape lib widened left replies)
  (t4-syntax-lists-with-replies
      ((clauses (t4-syntax-lists-spine-run lib widened spine-shape t replies) :recipe)
       (reflexive (proof-proof-reflexive (library-library-proof lib) (cadr left)))
       (result (proof-proof-rewrite (library-library-proof lib) reflexive clauses '(1 2 1)))
       (value (t4-syntax-lists-step-at clauses 2))
       (right (t4-syntax-lists-step-at result 2))
       (shown (t4-syntax-lists-evaluated-clause-map-show lib value right replies) :recipe)
       (reflexive (proof-proof-reflexive (library-library-proof lib) left))
       (combined (proof-proof-chain (library-library-proof lib) result (list shown)))
       (in-eval (proof-proof-rewrite (library-library-proof lib) reflexive combined '(1 2 1)))
       (in-eval-right (t4-syntax-lists-step-at in-eval 2))
       (evaluated (t4-syntax-lists-evaluate-run lib in-eval-right nil replies) :recipe))
    (list (proof-proof-chain (library-library-proof lib) in-eval (list evaluated)) lib replies)))

(defun t4-syntax-lists-evaluated-clause-map-compare-head (sign lib old-head after premise replies)
  (t4-syntax-lists-with-replies
      ((assumed (proof-proof-assume (library-library-proof lib) old-head sign))
       (selected (proof-proof-select (library-library-proof lib) after assumed))
       (right (t4-syntax-lists-step-at selected 2))
       (equivalent (t4-syntax-lists-request
                    lib replies :prove
                    (list (list *t4-syntax-lists-iff* right old-head)
                          (list assumed premise) (list *t4-syntax-lists-iff* *proof-not*)))
                   :recipe)
       (backward (proof-proof-symmetric (library-library-proof lib) selected)))
    (list (proof-proof-rewrite (library-library-proof lib) equivalent backward '(1 1)) lib replies)))

(defun t4-syntax-lists-evaluated-clause-map-base (lib widened left right atom-proof replies)
  (t4-syntax-lists-with-replies
      ((old-empty (t4-syntax-lists-evaluate-run lib right (list atom-proof) replies) :recipe)
       (new-empty (t4-syntax-lists-evaluated-clause-map-transformed
                   atom-proof lib widened left replies) :recipe)
       (nil-comparison (t4-syntax-lists-request
                        lib replies :prove
                        (list (list *t4-syntax-lists-iff-list* *proof-false* *proof-false*) nil
                              (list *t4-syntax-lists-iff-list* *proof-not*))) :recipe)
       (new-back (proof-proof-symmetric (library-library-proof lib) new-empty))
       (first (proof-proof-rewrite (library-library-proof lib) nil-comparison new-back '(1 1)))
       (old-back (proof-proof-symmetric (library-library-proof lib) old-empty)))
    (list (proof-proof-rewrite (library-library-proof lib) first old-back '(1 2)) lib replies)))

(defun t4-syntax-lists-evaluated-clause-map-conclude (lib known after old-head premise ih
                                                         old-pair new-pair old new replies)
  (t4-syntax-lists-with-replies
      ((positive (t4-syntax-lists-evaluated-clause-map-compare-head
                  t lib old-head after premise replies) :recipe)
       (negative (t4-syntax-lists-evaluated-clause-map-compare-head
                  nil lib old-head after premise replies) :recipe)
       (head-cases (proof-proof-cases (library-library-proof lib) old-head positive negative))
       (head-iff (t4-syntax-lists-iff-transitive-run lib known head-cases replies) :recipe)
       (tail-iff (proof-proof-modus-ponens (library-library-proof lib) ih premise))
       (compared (proof-proof-unfold (library-library-proof lib)
                                     (list *t4-syntax-lists-iff-list* new-pair old-pair)))
       (new-cons (t4-syntax-lists-consp-cons lib new-pair))
       (old-cons (t4-syntax-lists-consp-cons lib old-pair))
       (shapes (t4-division-combine lib (list new-cons old-cons)))
       (compared (t4-syntax-lists-choose lib compared shapes))
       (compared (t4-syntax-lists-projections lib compared new-pair))
       (compared (t4-syntax-lists-projections lib compared old-pair))
       (combination (t4-division-combine lib (list head-iff tail-iff)))
       (yes (proof-proof-transport (library-library-proof lib) combination compared))
       (new-back (proof-proof-symmetric (library-library-proof lib) new))
       (yes (proof-proof-rewrite (library-library-proof lib) yes new-back '(1 1)))
       (old-back (proof-proof-symmetric (library-library-proof lib) old)))
    (list (proof-proof-rewrite (library-library-proof lib) yes old-back '(1 2)) lib replies)))

(defun t4-syntax-lists-evaluated-clause-map-add (lib new-head old-head added list-evaluator env
                                                    guard premise ih old-pair new-pair old new replies)
  (t4-syntax-lists-with-replies
      ((eval-call (list list-evaluator added env))
       (evaluated-added (t4-syntax-lists-evaluate-run lib eval-call nil replies) :recipe)
       (fold (list *t4-syntax-lists-or-list* eval-call))
       (known (t4-syntax-lists-request
               lib replies :fact-proof (list (list *t4-syntax-lists-iff* new-head fold) nil))
              :recipe))
    (if (not known)
        (list '(:failure "SearchMiss" "")
              lib replies)
      (t4-syntax-lists-with-replies
          ((list-value (t4-syntax-lists-step-at evaluated-added 2))
           (or-value (t4-syntax-lists-constructed-view-run
                      lib (list *t4-syntax-lists-or-list* list-value) list-value t replies) :recipe)
           (known (proof-proof-rewrite (library-library-proof lib) known evaluated-added '(1 2 1)))
           (known (proof-proof-rewrite (library-library-proof lib) known or-value '(1 2)))
           (after (t4-syntax-lists-step-at known 2)))
        (if (equal after (proof-ite old-head *proof-true* (cadr guard)))
            (t4-syntax-lists-evaluated-clause-map-conclude
             lib known after old-head premise ih old-pair new-pair old new replies)
          (list '(:failure "InferenceMismatch" "") lib replies))))))

(defun t4-syntax-lists-evaluated-clause-map-step (lib widened left right obj clause guard
                                                     premise ih cons-proof replies)
  (t4-syntax-lists-with-replies
      ((old (t4-syntax-lists-evaluate-run lib right (list cons-proof) replies) :recipe)
       (new (t4-syntax-lists-evaluated-clause-map-transformed cons-proof lib widened left replies)
            :recipe)
       (old-pair (t4-syntax-lists-step-at old 2))
       (new-pair (t4-syntax-lists-step-at new 2)))
    (if (not (and (proof-is-call old-pair *proof-cons*) (proof-is-call new-pair *proof-cons*)))
        (list '(:failure "InferenceMismatch" "") lib replies)
      (t4-syntax-lists-with-replies
          ((old-head (proof-term-at old-pair 1))
           (new-head (proof-term-at new-pair 1))
           (disjoin (proof-term-at new-head 1))
           (added (proof-term-at disjoin 1)))
        (if (not (and (equal disjoin (list *t4-syntax-lists-disjoin* added))
                      (equal added (list *proof-cons* (list *library-car* obj) clause))))
            (list '(:failure "InferenceMismatch" "") lib replies)
          (t4-syntax-lists-evaluated-clause-map-add
           lib new-head old-head added (car left) (caddr left) guard premise ih
           old-pair new-pair old new replies))))))

(defun t4-syntax-lists-evaluated-clause-map-prove (lib formula guard obj clause widened left right replies)
  (let ((shape (list *proof-consp* obj)))
    (t4-syntax-lists-with-replies
        ((arithmetic (t4-syntax-lists-request lib replies :use-arithmetic nil) :recipe)
         (cons-proof (proof-proof-assume (library-library-proof lib) shape t))
         (atom-proof (proof-proof-assume (library-library-proof lib) shape nil))
         (recur (t4-syntax-lists-recur lib formula obj *library-cdr* 3))
         (premise (proof-proof-assume (library-library-proof lib) guard t))
         (no (t4-syntax-lists-evaluated-clause-map-base lib widened left right atom-proof replies)
             :recipe)
         (yes (t4-syntax-lists-evaluated-clause-map-step lib widened left right obj clause guard
                                                        premise (car recur) cons-proof replies)
              :recipe)
         (cases (proof-proof-cases (library-library-proof lib) shape yes no))
         (result (t4-ordinals-ordinals-imply lib guard cases)))
      (list (t4-syntax-lists-induct lib obj result formula (list (cadr recur))) lib replies))))

(defun t4-syntax-lists-evaluated-clause-map-check (lib formula guard left right clause-values widened-call
                                                     recursive replies)
  (let ((list-evaluator (car left))
        (env (caddr left))
        (obj (cadr right)))
    (if (not (and (proof-is-call clause-values list-evaluator) (eql (len clause-values) 3)
                  (equal (caddr clause-values) env)))
        (list nil lib replies)
      (t4-syntax-lists-with-replies ((widened (proof-term-at widened-call 1)))
        (let ((clause (cadr clause-values)))
          (if (or (proof-compound obj) (not (proof-compound widened))
                  (not (equal (cdr widened) (list obj clause)))
                  (not (member-equal (car widened) recursive)))
              (list nil lib replies)
            (t4-syntax-lists-with-replies
                ((opening (proof-proof-unfold (library-library-proof lib) widened))
                 (view (t4-syntax-lists-step-at opening 2)))
              (let ((tail (list (car widened) (list *library-cdr* obj) clause)))
                (if (equal view (proof-ite (list *t4-syntax-lists-atom* obj) *proof-false*
                                           (list *proof-cons* (list *proof-cons*
                                                                   (list *library-car* obj) clause)
                                                 tail)))
                    (t4-syntax-lists-evaluated-clause-map-prove
                     lib formula guard obj clause widened left right replies)
                  (list nil lib replies))))))))))

(defun t4-syntax-lists-evaluated-clause-map-run (lib formula recursive functions replies)
  (if (not (proof-is-call formula *library-implies*))
      (list nil lib replies)
    (t4-syntax-lists-with-replies ((comparison (proof-term-at formula 2)))
      (if (not (proof-is-call comparison *t4-syntax-lists-iff-list*))
          (list nil lib replies)
        (t4-syntax-lists-with-replies
            ((parts (proof-list-of-length (cdr formula) 2))
             (guard (car parts))
             (endpoints (proof-list-of-length (cdr comparison) 2))
             (left (car endpoints))
             (right (cadr endpoints)))
          (if (not (proof-is-call guard *proof-not*))
              (list nil lib replies)
            (t4-syntax-lists-with-replies ((fold (proof-term-at guard 1)))
              (if (not (and (proof-is-call fold *t4-syntax-lists-or-list*)
                            (proof-compound left) (eql (len left) 3)
                            (member-equal (car left) functions)
                            (proof-is-call right (car left)) (eql (len right) 3)
                            (equal (caddr right) (caddr left))
                            (proof-is-call (cadr left) *t4-syntax-lists-disjoin-list*)))
                  (list nil lib replies)
                (t4-syntax-lists-with-replies ((clause-values (proof-term-at fold 1)))
                  (t4-syntax-lists-evaluated-clause-map-check
                   lib formula guard left right clause-values (cadr left) recursive replies))))))))))

(defun t4-syntax-lists-evaluated-clause-map (lib formula recursive functions replies)
  (t4-syntax-lists-result
   (t4-syntax-lists-evaluated-clause-map-run lib formula recursive functions replies)))

(defun t4-syntax-lists-evaluated-clause-result-parts-fold (lib unpacked opened list-evaluator env replies)
  (t4-syntax-lists-with-replies
      ((literal (proof-step-first opened))
       (conjunction (proof-term-at literal 1))
       (syntax (proof-term-at conjunction 1))
       (folded (list *t4-syntax-lists-and-list* (list list-evaluator syntax env)))
       (law (t4-syntax-lists-request
             lib replies :fact-proof (list (list *t4-syntax-lists-iff* literal folded) nil))
            :recipe))
    (if (not law)
        (list '(:failure "SearchMiss" "") lib replies)
      (t4-syntax-lists-with-replies
          ((truth (t4-syntax-lists-iff-forward lib law opened))
           (clauses (t4-syntax-lists-step-at unpacked 2))
           (disjoined (t4-syntax-lists-constructed-view-run lib syntax clauses t replies) :recipe)
           (disjoined-right (t4-syntax-lists-step-at disjoined 2))
           (evaluated (t4-syntax-lists-evaluate-run lib (list list-evaluator disjoined-right env)
                                                   nil replies) :recipe)
           (parts (proof-proof-rewrite-first (library-library-proof lib) truth disjoined))
           (parts (proof-proof-rewrite-first (library-library-proof lib) parts evaluated))
           (part-term (proof-step-first parts))
           (values-right (t4-syntax-lists-step-at evaluated 2))
           (views (t4-syntax-lists-constructed-view-run lib part-term values-right t replies) :recipe)
           (rewritten (proof-proof-rewrite (library-library-proof lib) parts views '(1))))
        (list (t4-division-pieces lib rewritten) lib replies)))))

(defun t4-syntax-lists-evaluated-clause-result-open (lib result processor output tuple-value
                                                        wanted list-evaluator env replies)
  (t4-syntax-lists-with-replies
      ((unpacked (proof-proof-unfold (library-library-proof lib) result))
       (right (t4-syntax-lists-step-at unpacked 2))
       (unpacked (proof-proof-rewrite-result (library-library-proof lib) unpacked output
                                            (proof-eq *proof-result* right) processor))
       (unpacked (t4-syntax-lists-projections lib unpacked tuple-value))
       (right (t4-syntax-lists-step-at unpacked 2))
       (test (proof-term-at right 1))
       (status (t4-syntax-lists-request
                lib replies :prove
                (list (if (equal test *proof-false*) (proof-neg test) test) nil
                      (list *proof-not*)))
               :recipe)
       (unpacked (t4-syntax-lists-choose lib unpacked status))
       (opened (proof-proof-rewrite-first (library-library-proof lib) wanted unpacked))
       (argument (t4-syntax-lists-step-at opened 1))
       (definition (proof-proof-unfold (library-library-proof lib) argument))
       (opened (proof-proof-rewrite-first (library-library-proof lib) opened definition)))
    (t4-syntax-lists-evaluated-clause-result-parts-fold lib unpacked opened
                                                       list-evaluator env replies)))

(defun t4-syntax-lists-evaluated-clause-result-evaluated-parts
  (branch lib opening result processor wanted list-evaluator env replies)
  (t4-syntax-lists-with-replies
      ((output (t4-syntax-lists-choose lib opening branch))
       (right (t4-syntax-lists-step-at output 2))
       (output
        (if (proof-is-call right *termination-return-last*)
            (let ((proof (library-library-proof lib)))
              (proof-with-checked-results ((unfolded (proof-proof-unfold proof right)))
                (proof-proof-chain proof output (list unfolded))))
          output))
       (tuple-value (t4-syntax-lists-step-at output 2)))
    (if (proof-is-call tuple-value *proof-cons*)
        (t4-syntax-lists-evaluated-clause-result-open lib result processor output tuple-value
                                                    wanted list-evaluator env replies)
      (list '(:failure "InferenceMismatch" "") lib replies))))

(defun t4-syntax-lists-evaluated-clause-result-fail (lib fail conclusion guard opening result
                                                        processor wanted evaluator list-evaluator env
                                                        replies)
  (t4-syntax-lists-with-replies
      ((branch (proof-proof-assume (library-library-proof lib) fail t))
       (parts (t4-syntax-lists-evaluated-clause-result-evaluated-parts
               branch lib opening result processor wanted list-evaluator env replies) :recipe)
       (parts (proof-list-of-length parts 2))
       (fail-head (car parts))
       (empty (t4-syntax-lists-disjunction-run
               lib evaluator list-evaluator *proof-false* env replies) :recipe)
       (false-result (t4-syntax-lists-iff-forward lib empty fail-head))
       (evaluated (t4-syntax-lists-evaluate-run lib (list list-evaluator *proof-false* env)
                                               nil replies) :recipe)
       (false-result (proof-proof-rewrite-first (library-library-proof lib) false-result evaluated))
       (literal (proof-step-first false-result))
       (denial (t4-syntax-lists-request
                lib replies :prove
                (list (proof-neg (list *proof-consp* *proof-false*)) nil (list *proof-not*)))
               :recipe)
       (end (t4-syntax-lists-spine-run lib literal denial t replies) :recipe)
       (reduced (proof-proof-rewrite (library-library-proof lib) false-result end '(1))))
    (list (proof-proof-subsume (library-library-proof lib) reduced
                               (list conclusion (proof-neg fail) (proof-neg guard)))
          lib replies)))

(defun t4-syntax-lists-evaluated-clause-result-preserve (lib other-clauses binding-values denied
                                                            admissible fail demand list-evaluator
                                                            changed clause env changed-or
                                                            conclusion replies)
  (t4-syntax-lists-with-replies
      ((other (proof-step-first other-clauses))
       (lhs (proof-term-at other 1))
       (thinning (list *t4-syntax-lists-iff-list* lhs binding-values))
       (compatible (t4-syntax-lists-request lib replies :fact-proof (list thinning (list denied)))
                   :recipe))
    (if (not compatible)
        (list '(:failure "SearchMiss" "")
              lib replies)
      (t4-syntax-lists-with-replies
          ((fold-agreement (proof-eq other (list *t4-syntax-lists-and-list* binding-values)))
           (equivalence (t4-syntax-lists-request
                         lib replies :fact-proof (list fold-agreement (list compatible))) :recipe))
        (if (not equivalence)
            (list '(:failure "SearchMiss" "")
                  lib replies)
          (t4-syntax-lists-with-replies
              ((agreement (proof-proof-rewrite (library-library-proof lib) other-clauses
                                               equivalence '(1)))
               (not-admissible (proof-proof-assume (library-library-proof lib) admissible nil))
               (not-fail (proof-proof-assume (library-library-proof lib) fail nil))
               (accepted (proof-proof-cut (library-library-proof lib) not-admissible not-fail))
               (accepted (proof-proof-front (library-library-proof lib) accepted admissible))
               (rewritten (proof-eq (list list-evaluator changed env) (list list-evaluator clause env)))
               (preservation (t4-syntax-lists-request
                              lib replies :fact-proof
                              (list rewritten (append demand (list accepted agreement)))) :recipe))
            (if (not preservation)
                (list '(:failure "SearchMiss" "")
                      lib replies)
              (t4-syntax-lists-with-replies
                  ((original-or (proof-proof-rewrite (library-library-proof lib) changed-or
                                                     preservation '(1 1)))
                   (contradiction (proof-proof-cut (library-library-proof lib) original-or denied)))
                (list (proof-proof-front (library-library-proof lib) contradiction conclusion)
                      lib replies)))))))))

(defun t4-syntax-lists-evaluated-clause-result-success (lib fail opening result processor wanted
                                                           evaluator list-evaluator env clause
                                                           alist denied admissible demand conclusion
                                                           replies)
  (t4-syntax-lists-with-replies
      ((branch (proof-proof-assume (library-library-proof lib) fail nil))
       (parts (t4-syntax-lists-evaluated-clause-result-evaluated-parts
               branch lib opening result processor wanted list-evaluator env replies) :recipe)
       (parts (proof-list-of-length parts 2))
       (new-head (car parts))
       (other-clauses (cadr parts))
       (new-arg (t4-syntax-lists-step-at new-head 1))
       (changed (proof-term-at new-arg 1))
       (changed-disjunction (t4-syntax-lists-disjunction-run
                            lib evaluator list-evaluator changed env replies) :recipe)
       (changed-or (t4-syntax-lists-iff-forward lib changed-disjunction new-head))
       (other-arg (t4-syntax-lists-step-at other-clauses 1))
       (other-eval (proof-term-at other-arg 1))
       (widened (proof-term-at other-eval 1)))
    (if (and (proof-compound widened) (eql (len widened) 3) (equal (caddr widened) clause)
             (proof-compound (cadr widened)) (equal (cdr (cadr widened)) (list alist)))
        (let ((binding-values (list list-evaluator (cadr widened) env)))
          (t4-syntax-lists-evaluated-clause-result-preserve
           lib other-clauses binding-values denied admissible fail demand list-evaluator
           changed clause env changed-or conclusion replies))
      (list nil lib replies))))

(defun t4-syntax-lists-evaluated-clause-result-prove (lib guard conclusion opening fail admissible
                                                         result processor alist demand wanted
                                                         evaluator list-evaluator clause env replies)
  (t4-syntax-lists-with-replies
      ((arithmetic (t4-syntax-lists-request lib replies :use-arithmetic nil) :recipe)
       (original (t4-syntax-lists-disjunction-run lib evaluator list-evaluator clause env replies)
                 :recipe)
       (orig-left (t4-syntax-lists-step-at original 1))
       (orig-right (t4-syntax-lists-step-at original 2))
       (disjunction-denial (proof-eq (proof-neg orig-left) (proof-neg orig-right)))
       (deny-rule (t4-syntax-lists-request
                   lib replies :fact-proof (list disjunction-denial (list original))) :recipe))
    (if (not deny-rule)
        (list '(:failure "SearchMiss" "") lib replies)
      (t4-syntax-lists-with-replies
          ((negated (proof-proof-assume (library-library-proof lib) conclusion nil))
           (denied (proof-proof-rewrite (library-library-proof lib) negated deny-rule '(1)))
           (no (t4-syntax-lists-evaluated-clause-result-fail
                lib fail conclusion guard opening result processor wanted evaluator list-evaluator
                env replies) :recipe)
           (yes (t4-syntax-lists-evaluated-clause-result-success
                 lib fail opening result processor wanted evaluator list-evaluator env clause
                 alist denied admissible demand conclusion replies) :recipe))
        (if (not yes)
            (list nil lib replies)
          (t4-syntax-lists-with-replies
              ((cases (proof-proof-cases (library-library-proof lib) fail no yes)))
            (list (t4-ordinals-ordinals-imply lib guard cases) lib replies)))))))

(defun t4-syntax-lists-evaluated-clause-result-wanted-p (step evaluator env)
  (proof-with-checked-results ((term (proof-step-first step)))
    (and (proof-is-call term evaluator) (eql (len term) 3) (equal (caddr term) env)
         (proof-is-call (cadr term) *t4-syntax-lists-conjoin-clauses*))))

(defun t4-syntax-lists-evaluated-clause-result-wanted (demand evaluator env)
  (if (endp demand)
      nil
    (proof-with-checked-results
        ((found (t4-syntax-lists-evaluated-clause-result-wanted-p (car demand) evaluator env)))
      (if found
          (car demand)
        (t4-syntax-lists-evaluated-clause-result-wanted (cdr demand) evaluator env)))))

(defun t4-syntax-lists-evaluated-clause-result-reapplications (reapplications evaluator)
  (if (endp reapplications)
      nil
    (proof-with-checked-results
        ((key (proof-list-of-length (caar reapplications) 2))
         (rest (t4-syntax-lists-evaluated-clause-result-reapplications
                (cdr reapplications) evaluator)))
      (if (equal (car key) evaluator)
          (cons key rest)
        rest))))

(defun t4-syntax-lists-evaluated-clause-result-opening (lib guard conclusion result processor
                                                           demand wanted evaluator clause env
                                                           reapplications replies)
  (t4-syntax-lists-with-replies
      ((alist (proof-term-at processor 2))
       (opening (proof-proof-unfold (library-library-proof lib) processor))
       (body (t4-syntax-lists-step-at opening 2)))
    (if (not (proof-is-call body *proof-if*))
        (list nil lib replies)
      (t4-syntax-lists-with-replies ((fail (proof-term-at body 1)))
        (if (not (proof-is-call fail *proof-not*))
            (list nil lib replies)
          (t4-syntax-lists-with-replies
              ((admissible (proof-term-at fail 1))
               (available (t4-syntax-lists-evaluated-clause-result-reapplications
                           reapplications evaluator)))
            (if available
                (t4-syntax-lists-evaluated-clause-result-prove
                 lib guard conclusion opening fail admissible result processor alist demand wanted
                 evaluator (cadar available) clause env replies)
              (list nil lib replies))))))))

(defun t4-syntax-lists-evaluated-clause-result-find (lib guard conclusion evaluator clause env
                                                        reapplications replies)
  (t4-syntax-lists-with-replies
      ((assumed (proof-proof-assume (library-library-proof lib) guard t))
       (demand (t4-division-pieces lib assumed))
       (wanted (t4-syntax-lists-evaluated-clause-result-wanted demand evaluator env)))
    (if (not wanted)
        (list nil lib replies)
      (t4-syntax-lists-with-replies
          ((syntax (t4-syntax-lists-step-at wanted 1))
           (result (proof-term-at syntax 1)))
        (if (not (proof-is-call result *t4-syntax-lists-clauses-result*))
            (list nil lib replies)
          (t4-syntax-lists-with-replies ((processor (proof-term-at result 1)))
            (if (and (proof-compound processor) (eql (len processor) 4)
                     (equal (cadr processor) clause))
                (t4-syntax-lists-evaluated-clause-result-opening
                 lib guard conclusion result processor demand wanted evaluator clause env
                 reapplications replies)
              (list nil lib replies))))))))

(defun t4-syntax-lists-evaluated-clause-result-run (lib formula reapplications replies)
  (if (not (proof-is-call formula *library-implies*))
      (list nil lib replies)
    (t4-syntax-lists-with-replies
        ((parts (proof-list-of-length (cdr formula) 2))
         (guard (car parts))
         (conclusion (cadr parts)))
      (if (and (proof-compound conclusion) (eql (len conclusion) 3)
               (proof-is-call (cadr conclusion) *t4-syntax-lists-disjoin*))
          (t4-syntax-lists-with-replies ((disjoined (proof-list-of-length (cadr conclusion) 2)))
            (t4-syntax-lists-evaluated-clause-result-find
             lib guard conclusion (car conclusion) (cadr disjoined) (caddr conclusion)
             reapplications replies))
        (list nil lib replies)))))

(defun t4-syntax-lists-evaluated-clause-result (lib formula reapplications replies)
  (t4-syntax-lists-result
   (t4-syntax-lists-evaluated-clause-result-run lib formula reapplications replies)))
