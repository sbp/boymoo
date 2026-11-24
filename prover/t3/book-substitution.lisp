(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-substitution-term* (proof-sym "PSEUDO-TERMP" "ACL2"))
(defconst *t3-book-substitution-list* (proof-sym "PSEUDO-TERM-LISTP" "ACL2"))
(defconst *t3-book-substitution-sublis* (proof-sym "SUBLIS-VAR1" "ACL2"))
(defconst *t3-book-substitution-sublis-list* (proof-sym "SUBLIS-VAR1-LST" "ACL2"))
(defconst *t3-book-substitution-subcor* (proof-sym "SUBCOR-VAR" "ACL2"))
(defconst *t3-book-substitution-subcor-list* (proof-sym "SUBCOR-VAR-LST" "ACL2"))
(defconst *t3-book-substitution-subcor-var* (proof-sym "SUBCOR-VAR1" "ACL2"))
(defconst *t3-book-substitution-fast-sublis* (proof-sym "FSUBLIS-VAR" "ACL2"))
(defconst *t3-book-substitution-fast-sublis-list* (proof-sym "FSUBLIS-VAR-LST" "ACL2"))
(defconst *t3-book-substitution-cons-term* (proof-sym "CONS-TERM" "ACL2"))
(defconst *t3-book-substitution-cons-term1* (proof-sym "CONS-TERM1" "ACL2"))
(defconst *t3-book-substitution-fold-mv* (proof-sym "CONS-TERM1-MV2" "ACL2"))
(defconst *t3-book-substitution-kwote* (proof-sym "KWOTE" "ACL2"))
(defconst *t3-book-substitution-alist* (proof-sym "ALIST" "ACL2"))
(defconst *t3-book-substitution-vars* (proof-sym "VARS" "ACL2"))
(defconst *t3-book-substitution-terms* (proof-sym "TERMS" "ACL2"))
(defconst *t3-book-substitution-strip-cdrs* (proof-sym "STRIP-CDRS" "ACL2"))
(defconst *t3-book-substitution-lookup-term*
  (proof-sym "PSEUDO-TERMP-CDR-ASSOC-EQUAL" "ACL2"))
(defconst *t3-book-substitution-mv-nth* *t3-book-projections-mv-nth*)

(defun t3-book-substitution-quoted-base (lib formula)
  (t3-book-associations-prove-formula
   1000000 lib formula
   (list *t3-book-substitution-term* *t3-book-substitution-list*
         *t3-book-substitution-kwote* (proof-cl "ATOM") (proof-cl "NULL")
         (proof-cl "EQ") *proof-not*)
   nil))

(defun t3-book-substitution-conditional-term-type (lib)
  (let* ((proof (library-library-proof lib))
         (branch (proof-ite *library-x* *library-y* *library-z*))
         (y (list *t3-book-substitution-term* *library-y*))
         (z (list *t3-book-substitution-term* *library-z*)))
    (proof-with-checked-results
        ((y-case (proof-proof-assume proof y t))
         (z-case (proof-proof-assume proof z t))
         (true-branch (proof-proof-if-true proof branch))
         (yes (library-library-transport-argument lib y-case true-branch 1))
         (false-branch (proof-proof-if-false proof branch))
         (no (library-library-transport-argument lib z-case false-branch 1))
         (step (proof-proof-cases proof *library-x* yes no))
         (claim (proof-step-first step)))
      (library-library-lemma lib "T3-CONDITIONAL-TERM-TYPE" claim step
                             (list (proof-neg y) (proof-neg z))))))

(defund t3-book-substitution-open-trial (proof value)
  (proof-with-checked-results
      ((opened (proof-proof-beta proof value))
       (body (proof-rewritten-term opened)))
    (cons body opened)))

(mutual-recursion
 (defun t3-book-substitution-constant-folding-trial-type (n value lib)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "t3-book-substitution-constant-folding-trial-type")
     (let ((proof (library-library-proof lib)))
       (cond
        ((proof-is-call value *proof-if*)
         (proof-with-checked-results
             ((branches (t3-book-substitution-constant-folding-trial-arms
                         (1- n) (cddr value) lib)))
           (library-library-cite
            lib "T3-CONDITIONAL-TERM-TYPE" (cdr value) branches)))
        ((and (proof-compound value) (endp value))
         (proof-term-at value 0))
        ((and (proof-compound value) (proof-compound (car value)))
         (proof-with-checked-results
             ((opened (t3-book-substitution-open-trial proof value))
              (step (t3-book-substitution-constant-folding-trial-type
                     (1- n) (car opened) lib)))
           (library-library-transport-argument lib step (cdr opened) 1)))
        ((proof-is-call value *t3-book-substitution-kwote*)
         (library-library-cite lib "T3-TERM-OF-KWOTE" (cdr value) nil))
        (t (t3-book-substitution-quoted-base
            lib (list *t3-book-substitution-term* value)))))))

 (defun t3-book-substitution-constant-folding-trial-arms (n arms lib)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n)
          '(:failure "Fuel" "t3-book-substitution-constant-folding-trial-arms"))
         ((endp arms) nil)
         (t
          (proof-with-checked-results
              ((first (t3-book-substitution-constant-folding-trial-type
                       (1- n) (car arms) lib))
               (rest (t3-book-substitution-constant-folding-trial-arms
                      (1- n) (cdr arms) lib)))
            (cons first rest))))))

(defun t3-book-substitution-constant-folding-retained (value tests lib)
  (declare (ignore tests))
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((selected (t3-book-projections-project lib 1 value))
         (term (proof-rewritten-term selected))
         (known (proof-proof-assume proof (list *t3-book-substitution-term* term) t)))
      (library-library-transport-argument lib known selected 1))))

(defun t3-book-substitution-list-components (lib typed present)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((term (proof-step-first typed))
         (equation (t3-book-spines-shallow lib term (list present)))
         (rewritten (proof-proof-rewrite proof typed equation '(1)))
         (step (proof-proof-tidy proof rewritten)))
      (proof-proof-conjunct proof step))))

(defun t3-book-substitution-total-list-components-part
    (lib axiom predicate value test on-cons absent)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (library-library-axiom lib axiom (list value)))
         (body (proof-rewritten-term opened))
         (selected (proof-proof-select proof body absent))
         (missing (proof-proof-chain proof opened (list selected)))
         (nil-type (t3-book-substitution-quoted-base
                    lib (list predicate *proof-false*)))
         (empty (library-library-transport-argument lib nil-type missing 1)))
      (proof-proof-cases proof test on-cons empty))))

(defun t3-book-substitution-total-list-components (lib typed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((term (proof-step-first typed))
         (value (proof-term-at term 1))
         (test (list *proof-consp* value))
         (present (proof-proof-assume proof test t))
         (absent (proof-proof-assume proof test nil))
         (parts (t3-book-substitution-list-components lib typed present))
         (head (t3-book-substitution-total-list-components-part
                lib "COMPLETION-OF-CAR" *t3-book-substitution-term* value test
                (car parts) absent))
         (tail (t3-book-substitution-total-list-components-part
                lib "COMPLETION-OF-CDR" *t3-book-substitution-list* value test
                (cadr parts) absent)))
      (list head tail))))

(defun t3-book-substitution-parallel-lookup-leaf
    (value tests lib variable head tail ih)
  (if (equal value *library-x*)
      variable
    (proof-with-checked-results
        ((head-type (proof-step-first head))
         (head-term (proof-term-at head-type 1)))
      (if (equal value head-term)
          head
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results
              ((evidence (t3-logic-evidence-init lib tests nil nil))
               (cons-case (t3-logic-evidence-require
                           evidence (list *proof-consp* *library-z*)))
               (builtin (library-library-builtin lib 3 *library-z*))
               (decrease (proof-proof-discharge proof builtin (car cons-case)))
               (claim (proof-proof-prove-if proof ih decrease))
               (with-variable (proof-proof-prove-if proof claim variable)))
            (proof-proof-prove-if proof with-variable tail)))))))

(defun t3-book-substitution-original-arguments-nonquote
    (lib evidence head quote-test)
  (proof-with-checked-results
      ((found (t3-logic-evidence-find evidence (proof-neg quote-test))))
    (if (car found)
        found
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((reverse (t3-logic-evidence-require
                       (cdr found) (proof-neg (proof-eq (proof-quote *proof-quote*) head))))
             (affirmed (proof-proof-assume proof quote-test t))
             (symmetric (proof-proof-symmetric proof affirmed))
             (rejected (proof-proof-cut proof symmetric (car reverse)))
             (step (proof-proof-front proof rejected (proof-neg quote-test))))
          (cons step (cdr reverse)))))))

(defun t3-book-substitution-original-arguments (lib accepted evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((term (proof-step-first accepted))
         (parent (proof-term-at term 1))
         (head (list *library-car* parent))
         (quote-test (proof-eq head (proof-quote *proof-quote*)))
         (nonquote (t3-book-substitution-original-arguments-nonquote
                    lib evidence head quote-test))
         (present (t3-logic-evidence-require
                   (cdr nonquote) (list *proof-consp* parent)))
         (known (list (car present) (car nonquote)))
         (arguments (list *t3-book-substitution-list* (list *library-cdr* parent)))
         (absent (proof-proof-assume proof arguments nil))
         (refused (t3-book-spines-shallow lib term (append known (list absent))))
         (rewritten (proof-proof-rewrite proof accepted refused '(1)))
         (contradiction (proof-proof-tidy proof rewritten))
         (step (proof-proof-front proof contradiction arguments)))
      (cons (list known step) (cdr present)))))

(defun t3-book-substitution-rebuild
    (lib term typed correct-args same-length known)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((old-term (proof-step-first typed))
         (old (t3-book-spines-shallow lib old-term known))
         (rewritten (proof-proof-rewrite proof typed old '(1)))
         (step (proof-proof-tidy proof rewritten))
         (new (t3-book-spines-shallow lib (list *t3-book-substitution-term* term)
                                     (append known (list correct-args))))
         (aligned (t3-book-spines-replace-value lib new (list same-length))))
      (proof-proof-transport proof step aligned))))

(defun t3-book-substitution-term-traversal-lib (traversal)
  (nth 1 traversal))

(defun t3-book-substitution-term-traversal-multivalue (traversal)
  (nth 2 traversal))

(defun t3-book-substitution-term-traversal-calls (traversal)
  (nth 3 traversal))

(defun t3-book-substitution-term-traversal-environment (traversal)
  (nth 4 traversal))

(defun t3-book-substitution-term-traversal-env-proof (traversal)
  (nth 5 traversal))

(defun t3-book-substitution-term-traversal-measure (traversal)
  (nth 6 traversal))

(defun t3-book-substitution-term-traversal-substitutions (traversal)
  (nth 7 traversal))

(defun t3-book-substitution-term-traversal-targets (traversal)
  (nth 8 traversal))

(defun t3-book-substitution-term-traversal-templates (traversal)
  (nth 9 traversal))

(defun t3-book-substitution-term-traversal-claims (traversal)
  (nth 10 traversal))

(defun t3-book-substitution-term-traversal-formula (traversal)
  (nth 11 traversal))

(defun t3-book-substitution-term-traversal-kind (traversal)
  (nth 12 traversal))

(defun t3-book-substitution-term-traversal-view (traversal value)
  (if (t3-book-substitution-term-traversal-multivalue traversal)
      (list *t3-book-substitution-mv-nth* *proof-one* value)
    value))

(defun t3-book-substitution-term-traversal-list-goal (value)
  (proof-ite (list *t3-book-substitution-list* value)
             (proof-eq (list *library-len* value)
                       (list *library-len* *library-x*))
             *proof-false*))

(defun t3-book-substitution-term-traversal-make-claim (guard template call)
  (proof-with-checked-results
      ((result (proof-subst template (list (cons *proof-result* call)))))
    (proof-ite guard result *proof-true*)))

(defun t3-book-substitution-term-traversal-init (lib calls environment multivalue)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((env-proof (if (equal environment *proof-true*)
                        (proof-proof-prove proof *proof-true* nil nil)
                      (proof-proof-assume proof environment t)))
         (measure (list *library-count* *library-x*))
         (targets (list (list *t3-book-substitution-term* *library-x*)
                        (list *t3-book-substitution-list* *library-x*)))
         (traversal (list :t3-term-traversal lib multivalue calls environment
                          env-proof measure nil targets))
         (view (t3-book-substitution-term-traversal-view traversal *proof-result*))
         (templates (list (list *t3-book-substitution-term* view)
                          (t3-book-substitution-term-traversal-list-goal view))))
      (if (< (len calls) 2)
          (if (consp calls)
              '(:failure "failure" "")
            '(:failure "failure" ""))
        (proof-with-checked-results
            ((term-claim (t3-book-substitution-term-traversal-make-claim
                          (car targets) (car templates) (car calls)))
             (list-claim (t3-book-substitution-term-traversal-make-claim
                          (cadr targets) (cadr templates) (cadr calls)))
             (claims (list term-claim list-claim))
             (formula (proof-ite environment
                                 (proof-ite term-claim list-claim *proof-false*)
                                 *proof-true*)))
          (append traversal (list templates claims formula :base)))))))

(defun t3-book-substitution-term-traversal-smaller-at
    (traversal argument index accepted evidence)
  (let* ((lib (t3-book-substitution-term-traversal-lib traversal))
         (proof (library-library-proof lib))
         (measure (t3-book-substitution-term-traversal-measure traversal))
         (substitutions (t3-book-substitution-term-traversal-substitutions traversal))
         (entry (assoc-equal argument substitutions))
         (pairs (if entry (cdr entry) (list (list *library-x* argument))))
         (current (if entry traversal
                    (update-nth 7 (table-put substitutions argument pairs) traversal)))
         (lower (list *library-count* argument)))
    (proof-with-checked-results
        ((parent (proof-term-at argument 1))
         (descent
          (if (equal parent *library-x*)
              (proof-with-checked-results
                  ((present (t3-logic-evidence-require
                             evidence (list *proof-consp* *library-x*)))
                   (builtin (library-library-builtin
                             lib (if (equal (car argument) *library-car*) 2 3)
                             *library-x*))
                   (step (proof-proof-discharge proof builtin (car present))))
                (cons step (cdr present)))
            (t3-size-count-descent lib lower measure evidence)))
         (claim (proof-subst
                 (t3-book-substitution-term-traversal-formula traversal)
                 (proof-bindings-table pairs nil)))
         (guard (proof-ite (list *proof-ordinal-less* lower measure)
                           claim *proof-true*))
         (hypothesis (proof-proof-assume proof guard t))
         (child (proof-proof-prove-if proof hypothesis (car descent)))
         (both (proof-proof-prove-if
                proof child (t3-book-substitution-term-traversal-env-proof traversal)))
         (parts (proof-proof-conjunct proof both))
         (position (if (< index 0) (+ index (len parts)) index))
         (selected (if (< position 0)
                       '(:failure "MissingProofInput" "")
                     (proof-term-at parts position)))
         (step (proof-proof-prove-if proof selected accepted)))
      (list step current (cdr descent)))))

(defun t3-book-substitution-term-traversal-smaller
    (traversal field index accepted evidence)
  (t3-book-substitution-term-traversal-smaller-at
   traversal (list field *library-x*) index accepted evidence))

(defun t3-book-substitution-term-traversal-list-result
    (traversal value typed evidence)
  (let* ((lib (t3-book-substitution-term-traversal-lib traversal))
         (proof (library-library-proof lib))
         (cons-test (list *proof-consp* *library-x*)))
    (cond
     ((equal value *library-x*)
      (proof-with-checked-results
          ((length (proof-proof-reflexive proof (list *library-len* *library-x*)))
           (result (t3-scan-typed-pair lib typed length)))
        (list result traversal evidence)))
     ((equal value *proof-false*)
      (proof-with-checked-results
          ((atom (t3-logic-evidence-require evidence (proof-neg cons-test)))
           (original (t3-book-halves-length-cons lib *library-x* (car atom)))
           (empty (t3-book-halves-length-cons lib *proof-false* nil))
           (reversed (proof-proof-symmetric proof original))
           (length (proof-proof-chain proof empty (list reversed)))
           (typed-nil (t3-book-substitution-quoted-base
                       lib (list *t3-book-substitution-list* *proof-false*)))
           (result (t3-scan-typed-pair lib typed-nil length)))
        (list result traversal (cdr atom))))
     (t
      (proof-with-checked-results
          ((present (t3-logic-evidence-require evidence cons-test))
           (parts (t3-book-substitution-list-components lib typed (car present)))
           (head (t3-book-substitution-term-traversal-smaller
                  traversal *library-car* 0 (car parts) (cdr present)))
           (tail (t3-book-substitution-term-traversal-smaller
                  (cadr head) *library-cdr* 1 (cadr parts) (caddr head)))
           (tail-parts (proof-proof-conjunct proof (car tail)))
           (pair (t3-scan-typed-pair lib (car head) (car tail-parts)))
           (equation (t3-book-spines-shallow lib (list *t3-book-substitution-list* value) nil))
           (recognized (proof-proof-transport proof pair equation))
           (actual-size (t3-book-halves-length-cons lib value nil))
           (aligned (t3-book-spines-replace-value lib actual-size (list (cadr tail-parts))))
           (known-size (t3-book-halves-length-cons lib *library-x* (car present)))
           (reverse (proof-proof-symmetric proof known-size))
           (length (proof-proof-chain proof aligned (list reverse)))
           (result (t3-scan-typed-pair lib recognized length)))
        (list result (cadr tail) (caddr tail)))))))

(defun t3-book-substitution-substitution-init (lib operator)
  (let* ((parallel (equal operator *t3-book-substitution-subcor*))
         (multivalue (equal operator *t3-book-substitution-sublis*))
         (calls (if parallel
                    (list (list *t3-book-substitution-subcor*
                                *t3-book-substitution-vars* *t3-book-substitution-terms*
                                *library-x*)
                          (list *t3-book-substitution-subcor-list*
                                *t3-book-substitution-vars* *t3-book-substitution-terms*
                                *library-x*))
                  (list
                   (list (if multivalue *t3-book-substitution-sublis*
                           *t3-book-substitution-fast-sublis*)
                         *t3-book-substitution-alist* *library-x*)
                   (list (if multivalue *t3-book-substitution-sublis-list*
                           *t3-book-substitution-fast-sublis-list*)
                         *t3-book-substitution-alist* *library-x*))))
         (environment (list *t3-book-substitution-list*
                            (if parallel *t3-book-substitution-terms*
                              (list *t3-book-substitution-strip-cdrs*
                                    *t3-book-substitution-alist*)))))
    (proof-with-checked-results
        ((traversal (t3-book-substitution-term-traversal-init
                     lib calls environment multivalue)))
      (update-nth 12 (if parallel :parallel :alist) traversal))))

(defun t3-book-substitution-substitution-term-result-rebuilt
    (traversal value typed evidence)
  (let* ((lib (t3-book-substitution-term-traversal-lib traversal))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((arguments (t3-book-substitution-original-arguments lib typed evidence))
         (known (caar arguments))
         (original (cadar arguments))
         (tail (t3-book-substitution-term-traversal-smaller
                traversal *library-cdr* 1 original (cdr arguments)))
         (parts (proof-proof-conjunct proof (car tail)))
         (built (t3-book-substitution-rebuild
                 lib (cons *proof-cons* (cdr value)) typed (car parts) (cadr parts)
                 (append known (list original))))
         (result (if (proof-is-call value *proof-cons*)
                     built
                   (library-library-cite
                    lib "T3-CONS-TERM-TYPE" (cdr value) (list built)))))
      (list result (cadr tail) (caddr tail)))))

(defun t3-book-substitution-substitution-term-result
    (traversal value typed evidence)
  (let* ((lib (t3-book-substitution-term-traversal-lib traversal))
         (proof (library-library-proof lib))
         (env-proof (t3-book-substitution-term-traversal-env-proof traversal)))
    (if (equal value *library-x*)
        (list typed traversal evidence)
      (proof-with-checked-results
          ((producer (if (proof-is-call value *t3-book-substitution-mv-nth*)
                         (proof-term-at value 2)
                       nil)))
        (cond
         ((proof-is-call producer *t3-book-substitution-fold-mv*)
          (proof-with-checked-results
              ((result (library-library-cite
                        lib "T3-CONS-TERM1-MV2-TYPE" (cdr producer) (list typed))))
            (list result traversal evidence)))
         ((or (proof-is-call value *t3-book-substitution-cons-term*)
              (proof-is-call value *proof-cons*))
          (t3-book-substitution-substitution-term-result-rebuilt
           traversal value typed evidence))
         (t
          (proof-with-checked-results
              ((result
                (if (eq (t3-book-substitution-term-traversal-kind traversal) :alist)
                    (if (assoc-equal *t3-book-substitution-lookup-term*
                                     (proof-proof-facts proof))
                        (proof-with-checked-results
                            ((lookup (proof-proof-fact
                                      proof *t3-book-substitution-lookup-term* nil)))
                          (proof-proof-modus-ponens proof lookup env-proof))
                      (proof-with-checked-results
                          ((lookup (library-library-cite
                                    lib "T3-LOOKUP-TERM"
                                    (list *library-x* *t3-book-substitution-alist*) nil)))
                        (proof-proof-prove-if proof lookup env-proof)))
                  (proof-with-checked-results
                      ((lookup (library-library-cite
                                lib "T3-PARALLEL-TERM-LOOKUP"
                                (list *library-x* *t3-book-substitution-terms*
                                      *t3-book-substitution-vars*)
                                nil))
                       (claim (proof-proof-prove-if proof lookup typed)))
                    (proof-proof-prove-if proof claim env-proof)))))
            (list result traversal evidence))))))))

(defun t3-book-substitution-term-result-request-p (result)
  (eq (car result) :t3-book-substitution-term-result))

(defmacro t3-book-substitution-with-results (bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (or (failure-p ,name)
                 (t3-book-substitution-term-result-request-p ,name))
             ,name
           (t3-book-substitution-with-results ,(cdr bindings) ,result))))))

(defun t3-book-substitution-term-traversal-prove-leaf
    (value tests traversal typed index replies)
  (let* ((lib (t3-book-substitution-term-traversal-lib traversal))
         (proof (library-library-proof lib)))
    (t3-book-substitution-with-results
        ((evidence (t3-logic-evidence-init lib tests nil (list (proof-cl "EQL"))))
         (initial (if (t3-book-substitution-term-traversal-multivalue traversal)
                      (t3-book-projections-project lib 1 value)
                    (proof-proof-reflexive proof value)))
         (chosen (proof-rewritten-term initial))
         (normalized (t3-book-associations-normalize lib chosen nil nil))
         (selected (proof-proof-chain proof initial (list normalized)))
         (term (proof-rewritten-term selected))
         (leaf
          (cond ((not (equal index 0))
                 (t3-book-substitution-term-traversal-list-result
                  traversal term typed evidence))
                ((not (eq (t3-book-substitution-term-traversal-kind traversal) :base))
                 (t3-book-substitution-substitution-term-result
                  traversal term typed evidence))
                (t
                 (let ((reply (assoc-equal (list term typed evidence) replies)))
                   (if reply
                       (cdr reply)
                     (list :t3-book-substitution-term-result
                           traversal term typed evidence))))))
         (view (if (equal index 0)
                   (list *t3-book-substitution-term* *proof-result*)
                 (t3-book-substitution-term-traversal-list-goal *proof-result*)))
         (updated (library-library-proof
                   (t3-book-substitution-term-traversal-lib (cadr leaf))))
         (reverse (proof-proof-symmetric updated selected))
         (result (proof-proof-rewrite-result
                  updated (car leaf) reverse view *proof-result*)))
      (cons result (cadr leaf)))))

(defun t3-book-substitution-by-value-lib (lib traversal)
  (if traversal
      (t3-book-substitution-term-traversal-lib traversal)
    lib))

(defun t3-book-substitution-by-value-leaf (value tests lib leaf traversal)
  (case (car leaf)
    (:retained
     (proof-with-checked-results
         ((step (t3-book-substitution-constant-folding-retained value tests lib)))
       (cons step traversal)))
    (:parallel
     (proof-with-checked-results
         ((step (t3-book-substitution-parallel-lookup-leaf
                 value tests lib (cadr leaf) (caddr leaf) (cadddr leaf)
                 (nth 4 leaf))))
       (cons step traversal)))
    (otherwise
     (t3-book-substitution-term-traversal-prove-leaf
      value tests traversal (cadr leaf) (caddr leaf) (cadddr leaf)))))

(defund t3-book-substitution-by-value-branch (proof value)
  (if (proof-is-call value *proof-if*)
      (proof-with-checked-results ((parts (proof-list-of-length (cdr value) 3)))
        (cons :if parts))
    (proof-with-checked-results ((opened (t3-logic-by-value-unfold proof value)))
      (if opened
          (proof-with-checked-results ((body (proof-rewritten-term opened)))
            (list :opened body opened))
        '(:leaf)))))

(defun t3-book-substitution-by-value-visit
    (n lib value template leaf tests traversal)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t3-book-substitution-by-value-visit")
    (let* ((current (t3-book-substitution-by-value-lib lib traversal))
           (proof (library-library-proof current))
           (branch (t3-book-substitution-by-value-branch proof value)))
      (case (car branch)
       (:if
        (t3-book-substitution-with-results
            ((yes (t3-book-substitution-by-value-visit
                   (1- n) lib (caddr branch) template leaf
                   (append tests (list (list (cadr branch) t))) traversal))
             (no (t3-book-substitution-by-value-visit
                  (1- n) lib (cadddr branch) template leaf
                  (append tests (list (list (cadr branch) nil))) (cdr yes)))
             (updated (library-library-proof
                       (t3-book-substitution-by-value-lib lib (cdr no))))
             (result (proof-by-value-join updated value template (car yes) (car no))))
          (cons result (cdr no))))
       (:opened
        (t3-book-substitution-with-results
            ((step (t3-book-substitution-by-value-visit
                    (1- n) lib (cadr branch) template leaf tests traversal))
             (updated (library-library-proof
                       (t3-book-substitution-by-value-lib lib (cdr step))))
             (reverse (proof-proof-symmetric updated (caddr branch)))
             (result (proof-proof-rewrite-result
                      updated (car step) reverse template *proof-result*)))
          (cons result (cdr step))))
       (:leaf
        (t3-book-substitution-with-results
            ((result (t3-book-substitution-by-value-leaf value tests current leaf traversal))
             (step (t3-logic-by-value-check-leaf (car result) value template)))
          (cons step (cdr result))))
       (otherwise branch)))))

(defund t3-book-substitution-term-traversal-prove-claim
    (traversal call template target claim index replies)
  (let* ((lib (t3-book-substitution-term-traversal-lib traversal))
         (proof (library-library-proof lib)))
    (t3-book-substitution-with-results
        ((equation (proof-proof-unfold proof call))
         (typed (proof-proof-assume proof target t))
         (body (proof-rewritten-term equation))
         (branches (t3-book-substitution-by-value-visit
                    1000000 lib body template (list :traversal typed index replies)
                    nil traversal))
         (updated (t3-book-substitution-term-traversal-lib (cdr branches)))
         (updated-proof (library-library-proof updated))
         (reverse (proof-proof-symmetric updated-proof equation))
         (result (proof-proof-rewrite-result
                  updated-proof (car branches) reverse template *proof-result*))
         (step (t3-scan-conclusion updated claim result)))
      (cons step (cdr branches)))))

(defun t3-book-substitution-term-traversal-prove-claims
    (traversal calls templates targets claims index replies)
  (declare (xargs :measure (acl2-count calls)))
  (if (or (endp calls) (endp templates) (endp targets))
      (cons nil traversal)
    (t3-book-substitution-with-results
        ((claim (t3-book-substitution-term-traversal-prove-claim
                 traversal (car calls) (car templates) (car targets) (car claims)
                 index replies))
         (rest (t3-book-substitution-term-traversal-prove-claims
                (cdr claim) (cdr calls) (cdr templates) (cdr targets)
                (cdr claims) (1+ index) replies)))
      (cons (cons (car claim) (car rest)) (cdr rest)))))

(defun t3-book-substitution-term-traversal-prove (traversal label replies)
  (t3-book-substitution-with-results
      ((claims-and-traversal
        (t3-book-substitution-term-traversal-prove-claims
         traversal
         (t3-book-substitution-term-traversal-calls traversal)
         (t3-book-substitution-term-traversal-templates traversal)
         (t3-book-substitution-term-traversal-targets traversal)
         (t3-book-substitution-term-traversal-claims traversal)
         0 replies))
       (claims (proof-list-of-length (car claims-and-traversal) 2))
       (result (cdr claims-and-traversal))
       (lib (t3-book-substitution-term-traversal-lib result))
       (formula (t3-book-substitution-term-traversal-formula result))
       (proof (library-library-proof lib))
       (typed (t3-scan-typed-pair lib (car claims) (cadr claims)))
       (case-proof (t3-scan-conclusion lib formula typed))
       (ordinal (library-library-builtin lib 1 *library-x*))
       (step (proof-proof-induct
              proof ordinal case-proof formula
              (t3-book-substitution-term-traversal-measure result)
              (table-values
               (t3-book-substitution-term-traversal-substitutions result))))
       (extended (library-library-lemma lib label formula step nil)))
    (update-nth 1 extended result)))

(defun t3-book-substitution-constant-folding-multivalue (lib trial trial-term)
  (let* ((proof (library-library-proof lib))
         (call (list *t3-book-substitution-fold-mv* *library-x* *library-y* *library-z*))
         (template (list *t3-book-substitution-term*
                         (list *t3-book-substitution-mv-nth* *proof-one* *proof-result*)))
         (choices (proof-ite
                   *library-x*
                   (list *proof-cons* *proof-true*
                         (list *proof-cons* *library-x* *proof-false*))
                   (list *proof-cons* *proof-false*
                         (list *proof-cons* *library-y* *proof-false*))))
         (conditions (list (proof-neg (list *t3-book-substitution-term* *library-x*))
                           (proof-neg (list *t3-book-substitution-term* *library-y*)))))
    (proof-with-checked-results
        ((source (proof-proof-unfold proof call))
         (body (proof-rewritten-term source))
         (beta (proof-proof-beta proof body))
         (opened (proof-proof-chain proof source (list beta)))
         (body (proof-rewritten-term opened))
         (beta (proof-proof-beta proof body))
         (source (proof-proof-chain proof opened (list beta)))
         (original (proof-proof-assume
                    proof (list *t3-book-substitution-term* *library-z*) t))
         (result (t3-book-substitution-by-value-visit
                  1000000 lib choices template '(:retained) nil nil))
         (branches (car result))
         (claim (proof-step-first branches))
         (lib (library-library-lemma
               lib "T3-CHANGED-TERM-RESULT" claim branches conditions))
         (outputs (library-library-cite
                   lib "T3-CHANGED-TERM-RESULT" (list trial *library-z*)
                   (list trial-term original)))
         (proof (library-library-proof lib))
         (reverse (proof-proof-symmetric proof source))
         (step (proof-proof-rewrite-result proof outputs reverse template *proof-result*))
         (claim (proof-step-first step))
         (original-claim (proof-step-first original)))
      (library-library-lemma lib "T3-CONS-TERM1-MV2-TYPE" claim step
                             (list (proof-neg original-claim))))))

(defun t3-book-substitution-constant-folding (lib multivalue)
  (let* ((quoted (list *t3-book-substitution-term*
                       (list *t3-book-substitution-kwote* *library-x*)))
         (term1 (list *t3-book-substitution-cons-term1* *library-x* *library-y*))
         (built (list *t3-book-substitution-term*
                      (list *proof-cons* *library-x* *library-y*)))
         (cons-term (list *t3-book-substitution-term*
                          (list *t3-book-substitution-cons-term*
                                *library-x* *library-y*))))
    (proof-with-checked-results
        ((quoted-proof (t3-book-substitution-quoted-base lib quoted))
         (lib (library-library-lemma lib "T3-TERM-OF-KWOTE" quoted quoted-proof nil))
         (lib (t3-book-substitution-conditional-term-type lib))
         (proof (library-library-proof lib))
         (opened (proof-proof-unfold proof term1))
         (body (proof-rewritten-term opened))
         (beta (proof-proof-beta proof body))
         (opened (proof-proof-chain proof opened (list beta)))
         (branch (proof-rewritten-term opened))
         (trial (proof-term-at branch 1))
         (proof-of-trial
          (t3-book-substitution-constant-folding-trial-type 1000000 trial lib))
         (lib (library-library-lemma
               lib "T3-CONSTANT-FOLD-TERM" (list *t3-book-substitution-term* trial)
               proof-of-trial nil))
         (trial-term (library-library-cite
                      lib "T3-CONSTANT-FOLD-TERM" (list *library-x* *library-y*) nil))
         (proof (library-library-proof lib))
         (available (proof-proof-assume proof built t))
         (folded (library-library-cite
                  lib "T3-CONDITIONAL-TERM-TYPE" (cdr branch) (list trial-term available)))
         (folded (library-library-transport-argument lib folded opened 1))
         (source (proof-proof-unfold proof (cadr cons-term)))
         (branch (proof-rewritten-term source))
         (finished (library-library-cite
                    lib "T3-CONDITIONAL-TERM-TYPE" (cdr branch) (list folded available)))
         (finished (library-library-transport-argument lib finished source 1))
         (lib (library-library-lemma lib "T3-CONS-TERM-TYPE" cons-term finished
                                     (list (proof-neg built)))))
      (if multivalue
          (t3-book-substitution-constant-folding-multivalue lib trial trial-term)
        lib))))

(defun t3-book-substitution-parallel-lookup (lib)
  (let* ((proof (library-library-proof lib))
         (accepted (list *t3-book-substitution-term* *library-x*))
         (value-type (list *t3-book-substitution-list* *library-y*))
         (found (list *t3-book-substitution-subcor-var* *library-z* *library-y* *library-x*))
         (target (list *t3-book-substitution-term* found))
         (conditional (proof-ite value-type target *proof-true*))
         (formula (proof-ite accepted conditional *proof-true*))
         (measure (list *library-count* *library-z*))
         (pairs (list (list *library-z* (list *library-cdr* *library-z*))
                      (list *library-y* (list *library-cdr* *library-y*))))
         (bindings (proof-bindings-table pairs nil))
         (template (list *t3-book-substitution-term* *proof-result*)))
    (proof-with-checked-results
        ((variable (proof-proof-assume proof accepted t))
         (typed (proof-proof-assume proof value-type t))
         (parts (t3-book-substitution-total-list-components lib typed))
         (child (proof-subst measure bindings))
         (smaller (list *proof-ordinal-less* child measure))
         (substituted (proof-subst formula bindings))
         (ih (proof-proof-assume proof (proof-ite smaller substituted *proof-true*) t))
         (opened (proof-proof-unfold proof found))
         (body (proof-rewritten-term opened))
         (by-value (t3-book-substitution-by-value-visit
                    1000000 lib body template
                    (list :parallel variable (car parts) (cadr parts) ih) nil nil))
         (result (library-library-transport-argument lib (car by-value) opened 1))
         (inner (t3-scan-conclusion lib conditional result))
         (outer (t3-scan-conclusion lib formula inner))
         (ordinal (library-library-builtin lib 1 *library-z*))
         (step (proof-proof-induct proof ordinal outer formula measure (list pairs))))
      (library-library-lemma lib "T3-PARALLEL-TERM-LOOKUP" formula step nil))))

(defun t3-book-substitution-premise-map (parts facts)
  (if (endp parts)
      facts
    (proof-with-checked-results ((term (proof-step-first (car parts))))
      (t3-book-substitution-premise-map
       (cdr parts) (table-put facts term (car parts))))))

(defund t3-book-substitution-premise-fields (lib step facts)
  (proof-with-checked-results
      ((term (proof-step-first step))
       (false-branch (if (proof-is-call term *proof-if*) (proof-term-at term 3) nil)))
    (if (equal false-branch *proof-false*)
        (proof-with-checked-results
            ((parts (proof-proof-conjunct (library-library-proof lib) step))
             (fields (t3-book-associations-components lib (car parts)))
             (updated (t3-book-substitution-premise-map fields facts)))
          (list :rest (cadr parts) updated))
      (proof-with-checked-results ((fields (t3-book-associations-components lib step)))
        (t3-book-substitution-premise-map fields facts)))))

(defun t3-book-substitution-premises (n lib step facts)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "t3-book-substitution-premises")
    (let ((result (t3-book-substitution-premise-fields lib step facts)))
      (if (eq (car result) :rest)
          (t3-book-substitution-premises (1- n) lib (cadr result) (caddr result))
        result))))

(defun t3-book-substitution-lookup-premise (facts term)
  (let ((entry (assoc-equal term facts)))
    (if entry
        (cdr entry)
      '(:failure "MissingProofInput" ""))))

(defun t3-book-substitution-substitution-theorem (traversal name formula label fast)
  (let* ((lib (t3-book-substitution-term-traversal-lib traversal))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((consequent (proof-term-at formula 2))
         (beta (if fast (proof-proof-beta proof consequent) nil))
         (result (if beta (proof-rewritten-term beta) consequent))
         (with-length (proof-is-call result *proof-if*))
         (pair (if with-length (proof-term-at result 1) result))
         (target-and-view (proof-list-of-length pair 2))
         (target (car target-and-view))
         (view (cadr target-and-view))
         (source (if (t3-book-substitution-term-traversal-multivalue traversal)
                     (proof-term-at view 2)
                   view))
         (formal (proof-term-at source (max 0 (1- (len source)))))
         (index (if (equal target *t3-book-substitution-list*) 1 0))
         (guard (proof-term-at formula 1))
         (accepted (proof-proof-assume proof guard t))
         (facts (t3-book-substitution-premises 1000000 lib accepted nil))
         (invariant (library-library-cite lib label (list formal) nil))
         (environment
          (t3-book-substitution-lookup-premise
           facts (t3-book-substitution-term-traversal-environment traversal)))
         (both (proof-proof-prove-if proof invariant environment))
         (parts (proof-proof-conjunct proof both))
         (input-type (t3-book-substitution-lookup-premise facts (list target formal)))
         (proved (proof-proof-prove-if proof (nth index parts) input-type))
         (step (if (and (equal index 1) (not with-length))
                   (proof-with-checked-results
                       ((components (proof-proof-conjunct proof proved)))
                     (car components))
                 proved))
         (claim (proof-step-first step)))
      (if (not (equal claim result))
          '(:failure "Unsupported" "")
        (proof-with-checked-results
            ((transported (if beta (proof-proof-transport proof step beta) step))
             (concluded (t3-book-lemmas-implication lib formula transported))
             (entry (proof-proof-entry "theorem" name (list name) (list concluded))))
          (cons entry lib))))))

(defun t3-book-substitution-substitution (lib name formula operator)
  (let ((fast (equal operator *t3-book-substitution-fast-sublis*))
        (parallel (equal operator *t3-book-substitution-subcor*)))
    (proof-with-checked-results
        ((lib (if fast
                  lib
                (t3-book-substitution-constant-folding
                 lib (equal operator *t3-book-substitution-sublis*))))
         (lib
          (cond (parallel (t3-book-substitution-parallel-lookup lib))
                ((assoc-equal *t3-book-substitution-lookup-term*
                              (proof-proof-facts (library-library-proof lib)))
                 lib)
                (t (t3-book-associations-invariant
                    lib "T3-LOOKUP-TERM" *t3-book-associations-assoc*
                    (list *t3-book-substitution-list*
                          (list *t3-book-substitution-strip-cdrs* *library-y*))
                    (list *t3-book-substitution-term*
                          (list *library-cdr* *proof-result*))))))
         (operation (t3-book-substitution-substitution-init lib operator))
         (operator-name (proof-term-at operator 2))
         (label (concatenate 'string "T3-" operator-name "-INVARIANT"))
         (proved (t3-book-substitution-term-traversal-prove operation label nil)))
      (t3-book-substitution-substitution-theorem proved name formula label fast))))
