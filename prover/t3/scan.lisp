(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-scan-skip-alternative* (proof-sym "FIND-ALTERNATIVE-SKIP" "ACL2"))
(defconst *t3-scan-skip-bound* (proof-sym "SELF-T3-SKIP-INDEX" "ACL2"))
(defconst *t3-scan-whitespace* (proof-sym "SCAN-PAST-WHITESPACE" "ACL2"))
(defconst *t3-scan-whitespace-bound* (proof-sym "SELF-T3-WHITESPACE-INDEX" "ACL2"))
(defconst *t3-scan-search* (proof-sym "SEARCH-FN" "ACL2"))
(defconst *t3-scan-search-start* (proof-sym "SEARCH-FROM-START" "ACL2"))
(defconst *t3-scan-search-bound* (proof-sym "SELF-T3-SEARCH-INDEX" "ACL2"))

(defun t3-scan-index-claim (index result)
  (proof-ite (proof-eq result *proof-zero*) *proof-true*
             (proof-ite (library-integer result) (library-lt index result) *proof-false*)))

(defun t3-scan-conclusion (lib conditional step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((true-case (proof-proof-if-true proof conditional))
      (yes (proof-proof-transport proof step true-case))
      (truth (t3-logic-libraryproofs-prove lib *proof-true* nil nil))
      (false-case (proof-proof-if-false proof conditional))
      (no (proof-proof-transport proof truth false-case))
      (test (proof-term-at conditional 1)))
     (proof-proof-cases proof test yes no))))

(defun t3-scan-typed-pair (lib first second)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((test (proof-step-first first))
      (yes (proof-step-first second))
      (selected (proof-proof-select proof (proof-ite test yes *proof-false*) first)))
     (proof-proof-transport proof second selected))))

(defun t3-scan-weak-after-advance (lib old new result evidence advance result-type weak)
  (proof-with-checked-results
   ((old-type (t3-logic-evidence-integer evidence old))
    (new-type (t3-logic-evidence-integer (cdr old-type) new))
    (strict (library-library-cite lib "LESS-THEN-WEAK" (list old new result)
                                  (list (car old-type) (car new-type) result-type advance weak)))
    (bound (library-library-cite lib "LESS-TO-WEAK" (list old result)
                                 (list (car old-type) result-type strict))))
   (cons bound (cdr new-type))))

(defun t3-scan-binding-pairs (formals actuals)
  (if (or (endp formals) (endp actuals))
      nil
    (let ((remaining (t3-scan-binding-pairs (cdr formals) (cdr actuals))))
      (if (equal (car formals) (car actuals))
          remaining
        (cons (list (car formals) (car actuals)) remaining)))))

(defun t3-scan-binding (pairs binding)
  (if (endp pairs)
      binding
    (t3-scan-binding (cdr pairs) (table-put binding (caar pairs) (cadar pairs)))))

(defun t3-scan-record-substitution (pairs substitutions)
  (if (member-equal pairs substitutions) substitutions (append substitutions (list pairs))))

(defun t3-scan-use-induction-hypothesis (lib smaller formula binding)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((first (proof-step-first smaller))
      (instance (proof-subst formula binding))
      (hypothesis (proof-proof-assume proof (proof-ite first instance *proof-true*) t)))
     (proof-proof-prove-if proof hypothesis smaller))))

(defun t3-scan-induction-result (lib target formals formula measure substitutions evidence)
  (let* ((pairs (t3-scan-binding-pairs formals (cdr target)))
         (substitutions (t3-scan-record-substitution pairs substitutions))
         (binding (t3-scan-binding pairs nil)))
    (proof-with-checked-results
     ((instance (proof-subst measure binding))
      (smaller (t3-arithmetic-gap-descent lib instance measure evidence))
      (step (t3-scan-use-induction-hypothesis lib (car smaller) formula binding)))
     (list step substitutions (cdr smaller)))))

(defun t3-scan-search-claim (index bound target)
  (let* ((value (proof-ite (library-integer target) (library-le index target) *proof-false*))
         (types (proof-ite (library-integer index)
                           (proof-ite (library-integer bound) value *proof-false*) *proof-false*)))
    (proof-ite target types *proof-true*)))

(defun t3-scan-whitespace-claim (index bound value)
  (let ((assumptions (proof-ite (library-integer index)
                                (proof-ite (library-integer bound) (library-le index bound) *proof-false*)
                                *proof-false*))
        (result (proof-ite (library-integer value) (library-le index value) *proof-false*)))
    (proof-ite assumptions result *proof-true*)))

(defun t3-scan-formals (lib name)
  (let ((entry (assoc-equal name (proof-proof-definitions (library-library-proof lib)))))
    (if (not entry)
        '(:failure "failure" "")
      (proof-with-checked-results ((fields (proof-list-of-length (cdr entry) 2)))
        (car fields)))))

(defun t3-scan-step-right (step)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((first (proof-step-first step)))
      (proof-term-at first 2))))

(defun t3-scan-rewrite-result-back (proof step equation template)
  (proof-with-checked-results ((symmetric (proof-proof-symmetric proof equation)))
    (proof-proof-rewrite-result proof step symmetric template *proof-result*)))

(defun t3-scan-skip-advance (lib index result nonzero formals formula measure substitutions evidence)
  (let* ((proof (library-library-proof lib))
         (pairs (t3-scan-binding-pairs formals (cdr result)))
         (substitutions (t3-scan-record-substitution pairs substitutions))
         (binding (t3-scan-binding pairs nil)))
    (proof-with-checked-results
     ((new (proof-subst index binding))
      (instance (proof-subst measure binding))
      (smaller (t3-arithmetic-gap-descent lib instance measure evidence))
      (hypothesis (t3-scan-use-induction-hypothesis lib (car smaller) formula binding))
      (proved (proof-proof-prove-if proof hypothesis nonzero))
      (types (proof-proof-conjunct proof proved))
      (move (t3-arithmetic-integer-comparison lib index new (cdr smaller)))
      (old-type (t3-logic-evidence-integer (cdr move) index))
      (new-type (t3-logic-evidence-integer (cdr old-type) new))
      (advance (library-library-cite lib "LESS-TRANSITIVE" (list index new result)
                                     (list (car old-type) (car new-type) (car types)
                                           (car move) (cadr types)))))
     (list (car types) advance substitutions))))

(defun t3-scan-skip-leaf-nonzero (lib index result claim tests formals formula measure substitutions)
  (let* ((proof (library-library-proof lib))
         (is-zero (proof-eq result *proof-zero*)))
    (proof-with-checked-results
     ((nonzero (proof-proof-assume proof is-zero nil))
      (evidence (t3-logic-evidence-init lib tests nil nil))
      (bound (cond ((proof-is-call result *t3-scan-skip-alternative*)
                    (t3-scan-skip-advance lib index result nonzero formals formula measure substitutions evidence))
                   ((proof-is-call result *proof-plus*)
                    (proof-with-checked-results
                     ((intact (t3-logic-evidence-integer evidence result))
                      (advance (t3-arithmetic-integer-comparison lib index result (cdr intact))))
                     (list (car intact) (car advance) substitutions)))
                   (t '(:failure "Unsupported" ""))))
      (truth (t3-logic-libraryproofs-prove lib *proof-true* nil nil))
      (when-zero (proof-proof-if-true proof claim))
      (yes (proof-proof-transport proof truth when-zero))
      (selected (proof-proof-select proof (cadddr claim) (car bound)))
      (valid (proof-proof-transport proof (cadr bound) selected))
      (when-nonzero (proof-proof-if-false proof claim))
      (no (proof-proof-transport proof valid when-nonzero))
      (step (proof-proof-cases proof is-zero yes no)))
     (cons step (caddr bound)))))

(defun t3-scan-scan-index-bound-leaf (value tests lib index formals formula measure template substitutions)
  (proof-with-checked-results
   ((opened (t3-logic-libraryproofs-normalize lib value nil nil))
    (result (if opened (t3-scan-step-right opened) value)))
   (let ((claim (t3-scan-index-claim index result)))
     (proof-with-checked-results
      ((proved (if (equal result *proof-zero*)
                   (proof-with-checked-results ((step (t3-logic-libraryproofs-prove-formula lib claim nil nil)))
                     (cons step substitutions))
                 (t3-scan-skip-leaf-nonzero lib index result claim tests formals formula measure substitutions)))
       (step (if opened
                 (t3-scan-rewrite-result-back (library-library-proof lib) (car proved) opened template)
               (car proved))))
      (cons step (cdr proved))))))

(defun t3-scan-search-leaf-order (lib index result formals formula measure substitutions evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((ih (t3-scan-induction-result lib result formals formula measure substitutions evidence))
      (nonnil (proof-proof-assume proof result t))
      (proved (proof-proof-prove-if proof (car ih) nonnil))
      (child (proof-proof-conjunct proof proved))
      (child (proof-proof-conjunct proof (cadr child)))
      (typed-order (proof-proof-conjunct proof (cadr child)))
      (new (proof-term-at result 3))
      (advance (t3-arithmetic-integer-comparison lib index new (caddr ih)))
      (order (t3-scan-weak-after-advance lib index new result (cdr advance)
                                        (car advance) (car typed-order) (cadr typed-order))))
     (list (car typed-order) (car order) (cadr ih)))))

(defun t3-scan-search-index-bound-leaf (result tests lib index bound formals formula measure substitutions)
  (let ((claim (t3-scan-search-claim index bound result)))
    (if (equal result *proof-false*)
        (proof-with-checked-results ((step (t3-logic-libraryproofs-prove-formula lib claim nil nil)))
          (cons step substitutions))
      (proof-with-checked-results
       ((evidence (t3-logic-evidence-init lib tests nil nil))
        (old-type (t3-logic-evidence-integer evidence index))
        (bound-type (t3-logic-evidence-integer (cdr old-type) bound))
        (order (cond ((proof-is-call result *t3-scan-search-start*)
                      (t3-scan-search-leaf-order lib index result formals formula measure substitutions
                                                (cdr bound-type)))
                     ((not (equal result index)) '(:failure "failure" ""))
                     (t
                      (proof-with-checked-results
                       ((reflexive (library-library-cite lib "WEAK-REFLEXIVE" (list index) (list (car old-type)))))
                       (list (car old-type) reflexive substitutions)))))
        (value (t3-scan-typed-pair lib (car order) (cadr order)))
        (typed (t3-scan-typed-pair lib (car bound-type) value))
        (typed (t3-scan-typed-pair lib (car old-type) typed))
        (step (t3-scan-conclusion lib claim typed)))
       (cons step (caddr order))))))

(defun t3-scan-whitespace-recursive-leaf (lib index bound result claim formals formula measure substitutions
                                         evidence bound-type)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((new (proof-term-at result 2))
      (ih (t3-scan-induction-result lib result formals formula measure substitutions evidence))
      (bound-new (t3-arithmetic-successor-bound lib index new bound (caddr ih)))
      (new-type (t3-logic-evidence-integer (cdr bound-new) new))
      (within (t3-scan-typed-pair lib bound-type (car bound-new)))
      (inputs (t3-scan-typed-pair lib (car new-type) within))
      (proved (proof-proof-prove-if proof (car ih) inputs))
      (typed-order (proof-proof-conjunct proof proved))
      (advance (t3-arithmetic-integer-comparison lib index new (cdr new-type)))
      (order (t3-scan-weak-after-advance lib index new result (cdr advance)
                                        (car advance) (car typed-order) (cadr typed-order)))
      (typed (t3-scan-typed-pair lib (car typed-order) (car order)))
      (step (t3-scan-conclusion lib claim typed)))
     (cons step (cadr ih)))))

(defun t3-scan-whitespace-bound-leaf (lib bound result claim tests index-type bound-type within)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((test-pair (proof-term-at tests 0))
      (holds (proof-term-at test-pair 1)))
     (cond
      ((not (equal result bound)) '(:failure "failure" ""))
      (holds
       (proof-with-checked-results
        ((test (proof-term-at test-pair 0))
         (cannot (t3-logic-libraryproofs-prove-formula lib (proof-neg test) (list *proof-not*)
                                                      (list index-type bound-type)))
         (assumed (proof-proof-assume proof test t))
         (contradiction (proof-proof-cut proof assumed cannot))
         (step (proof-proof-subsume proof contradiction
                                    (cons (caddr claim) (proof-step-clause contradiction)))))
        (t3-scan-conclusion lib claim step)))
      (t (proof-with-checked-results ((step (t3-scan-typed-pair lib bound-type within)))
           (t3-scan-conclusion lib claim step)))))))

(defun t3-scan-whitespace-index-bound-leaf (value tests lib index bound formals formula measure template substitutions)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((opened (t3-logic-libraryproofs-normalize lib value nil nil))
      (result (if opened (t3-scan-step-right opened) value))
      (claim (t3-scan-whitespace-claim index bound result))
      (typed (proof-proof-assume proof (cadr claim) t))
      (types (proof-proof-conjunct proof typed))
      (bounds (proof-proof-conjunct proof (cadr types)))
      (evidence (t3-logic-evidence-init lib tests (list (car types) (car bounds) (cadr bounds)) nil))
      (proved
       (if (proof-is-call result *t3-scan-whitespace*)
           (t3-scan-whitespace-recursive-leaf lib index bound result claim formals formula measure substitutions
                                             evidence (car bounds))
         (proof-with-checked-results
          ((step (if (equal result index)
                     (proof-with-checked-results
                      ((reflexive (library-library-cite lib "WEAK-REFLEXIVE" (list index) (list (car types))))
                       (pair (t3-scan-typed-pair lib (car types) reflexive)))
                      (t3-scan-conclusion lib claim pair))
                   (t3-scan-whitespace-bound-leaf lib bound result claim tests (car types) (car bounds) (cadr bounds)))))
          (cons step substitutions))))
      (step (if opened (t3-scan-rewrite-result-back proof (car proved) opened template) (car proved))))
     (cons step (cdr proved)))))

; The substitutions found on the true branch precede those found on the false branch.
(defun t3-scan-prove-value (n lib value template tests kind index bound formals formula measure substitutions)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof lib)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "t3-scan-prove-value"))
     ((proof-is-call value *proof-if*)
      (proof-with-checked-results
       ((parts (proof-list-of-length (cdr value) 3))
        (test (car parts))
        (yes (t3-scan-prove-value (1- n) lib (cadr parts) template (append tests (list (list test t)))
                                 kind index bound formals formula measure substitutions))
        (no (t3-scan-prove-value (1- n) lib (caddr parts) template (append tests (list (list test nil)))
                                kind index bound formals formula measure (cdr yes)))
        (step (proof-by-value-join proof value template (car yes) (car no))))
       (cons step (cdr no))))
     (t
      (proof-with-checked-results ((opened (t3-logic-by-value-unfold proof value)))
        (if opened
            (proof-with-checked-results
             ((result (t3-scan-step-right opened))
              (child (t3-scan-prove-value (1- n) lib result template tests
                                         kind index bound formals formula measure substitutions))
              (step (t3-scan-rewrite-result-back proof (car child) opened template)))
             (cons step (cdr child)))
          (proof-with-checked-results
           ((leaf (case kind
                    (:skip (t3-scan-scan-index-bound-leaf value tests lib index formals formula measure
                                                         template substitutions))
                    (:search (t3-scan-search-index-bound-leaf value tests lib index bound formals formula measure
                                                             substitutions))
                    (otherwise (t3-scan-whitespace-index-bound-leaf value tests lib index bound formals formula measure
                                                                   template substitutions))))
            (step (t3-logic-by-value-check-leaf (car leaf) value template)))
           (cons step (cdr leaf)))))))))

(defun t3-scan-prove-index-bound (lib name kind index bound formals formula measure template source)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((value (t3-scan-step-right source))
      (leaves (t3-scan-prove-value 1000000 lib value template nil kind index bound formals formula measure nil))
      (step (t3-scan-rewrite-result-back proof (car leaves) source template))
      (ordinal (library-library-cite lib "GAP-ORDINAL" (cdr measure) nil))
      (result (proof-proof-induct proof ordinal step formula measure (cdr leaves))))
     (library-library-lemma lib name formula result nil))))

(defun t3-scan-scan-index-bound (lib)
  (proof-with-checked-results
   ((formals (t3-scan-formals lib *t3-scan-skip-alternative*))
    (formals (proof-list-of-length formals 4)))
   (let* ((index (cadr formals))
          (bound (caddr formals))
          (call (cons *t3-scan-skip-alternative* formals))
          (template (t3-scan-index-claim index *proof-result*))
          (formula (t3-scan-index-claim index call))
          (measure (list *library-gap* bound index)))
     (proof-with-checked-results ((source (proof-proof-unfold (library-library-proof lib) call)))
       (t3-scan-prove-index-bound lib "T3-SKIP-INDEX" :skip index bound formals formula measure template source)))))

(defun t3-scan-search-index-bound (lib)
  (proof-with-checked-results
   ((formals (t3-scan-formals lib *t3-scan-search-start*))
    (formals (proof-list-of-length formals 4)))
   (let* ((index (caddr formals))
          (bound (cadddr formals))
          (call (cons *t3-scan-search-start* formals))
          (template (t3-scan-search-claim index bound *proof-result*))
          (formula (t3-scan-search-claim index bound call))
          (measure (list *library-gap* bound index)))
     (proof-with-checked-results ((source (proof-proof-unfold (library-library-proof lib) call)))
       (t3-scan-prove-index-bound lib "T3-SEARCH-INDEX" :search index bound formals formula measure template source)))))

(defun t3-scan-whitespace-index-bound (lib)
  (proof-with-checked-results
   ((formals (t3-scan-formals lib *t3-scan-whitespace*))
    (formals (proof-list-of-length formals 3)))
   (let* ((index (cadr formals))
          (bound (caddr formals))
          (call (cons *t3-scan-whitespace* formals))
          (template (t3-scan-whitespace-claim index bound *proof-result*))
          (formula (t3-scan-whitespace-claim index bound call)))
     (proof-with-checked-results ((source (proof-proof-unfold (library-library-proof lib) call)))
       (let ((measure (list *library-gap* bound index)))
         (t3-scan-prove-index-bound lib "T3-WHITESPACE-INDEX" :whitespace index bound
                                    formals formula measure template source))))))

(defun t3-scan-with-updated-library (evidence old-lib new-lib)
  (if (equal (t3-logic-evidence-lib evidence) old-lib)
      (t3-logic-evidence-with-lib evidence new-lib)
    evidence))

(defun t3-scan-record-steps (evidence steps)
  (if (endp steps)
      evidence
    (proof-with-checked-results ((first (proof-step-first (car steps))))
      (t3-scan-record-steps
       (t3-logic-evidence-with-facts evidence
                                    (table-put (t3-logic-evidence-facts evidence) first (car steps)))
       (cdr steps)))))

(defun t3-scan-infer-skip-result (lib term evidence)
  (let ((proof (library-library-proof lib)))
    (if (not (assoc-equal *t3-scan-skip-alternative* (proof-proof-definitions proof)))
        (cons lib evidence)
      (proof-with-checked-results
       ((nonzero (t3-logic-evidence-find evidence (proof-neg (proof-eq term *proof-zero*)))))
       (if (not (car nonzero))
           (cons lib (cdr nonzero))
         (proof-with-checked-results
          ((updated-lib (if (assoc-equal *t3-scan-skip-bound* (proof-proof-facts proof))
                            lib
                          (t3-scan-scan-index-bound lib)))
           (evidence (t3-scan-with-updated-library (cdr nonzero) lib updated-lib))
           (proof (library-library-proof updated-lib))
           (formals (t3-scan-formals updated-lib *t3-scan-skip-alternative*))
           (fact (proof-proof-fact proof *t3-scan-skip-bound* (seq-zip formals (cdr term))))
           (proved (proof-proof-prove-if proof fact (car nonzero)))
           (steps (proof-proof-conjunct proof proved))
           (evidence (t3-scan-record-steps evidence steps)))
          (cons updated-lib evidence)))))))

(defun t3-scan-whitespace-within (lib index bound index-type bound-type evidence)
  (proof-with-checked-results ((within (t3-logic-evidence-find evidence (library-le index bound))))
    (cond ((car within) within)
          ((and (proof-is-call index *proof-plus*) (member-equal *proof-one* (cdr index)))
           (proof-with-checked-results
            ((base (proof-term-at index (if (equal (cadr index) *proof-one*) 2 1))))
            (t3-arithmetic-successor-bound lib base index bound (cdr within))))
          (t
           (proof-with-checked-results
            ((strict (t3-arithmetic-integer-comparison lib index bound (cdr within)))
             (step (library-library-cite lib "LESS-TO-WEAK" (list index bound)
                                        (list index-type bound-type (car strict)))))
            (cons step (cdr strict)))))))

(defun t3-scan-infer-whitespace-result (lib term evidence)
  (proof-with-checked-results
   ((updated-lib (if (assoc-equal *t3-scan-whitespace-bound* (proof-proof-facts (library-library-proof lib)))
                     lib
                   (t3-scan-whitespace-index-bound lib)))
    (evidence (t3-scan-with-updated-library evidence lib updated-lib))
    (term (proof-list-of-length term 4)))
   (let ((proof (library-library-proof updated-lib))
         (index (caddr term))
         (bound (cadddr term)))
     (proof-with-checked-results
      ((formals (t3-scan-formals updated-lib *t3-scan-whitespace*))
       (predicate (proof-proof-fact proof *t3-scan-whitespace-bound* (seq-zip formals (cdr term))))
       (index-type (t3-logic-evidence-integer evidence index))
       (bound-type (t3-logic-evidence-integer (cdr index-type) bound))
       (within (t3-scan-whitespace-within updated-lib index bound (car index-type) (car bound-type)
                                         (cdr bound-type)))
       (within-pair (t3-scan-typed-pair updated-lib (car bound-type) (car within)))
       (typed (t3-scan-typed-pair updated-lib (car index-type) within-pair))
       (proved (proof-proof-prove-if proof predicate typed))
       (steps (proof-proof-conjunct proof proved))
       (evidence (t3-scan-record-steps (cdr within) steps)))
      (cons updated-lib evidence)))))

(defun t3-scan-select-search-application (lib equation value nonnil definitions)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((observed (proof-proof-rewrite proof nonnil equation '(1)))
      (tests (proof-proof-conjunct proof observed))
      (selection (proof-proof-select proof value (car tests)))
      (equation (proof-proof-chain proof equation (list selection)))
      (value (t3-scan-step-right equation))
      (opened (t3-logic-libraryproofs-normalize lib value nil definitions)))
     (proof-proof-chain proof equation (list opened)))))

(defun t3-scan-search-application (lib term nonnil)
  (let ((definitions (list *t3-scan-search* (proof-cl "EQ") *proof-not* (proof-sym "MV-NTH" "ACL2")
                           *t3-logic-atom* *t3-logic-zp*)))
    (proof-with-checked-results
     ((equation (t3-logic-libraryproofs-normalize lib term nil definitions))
      (value (t3-scan-step-right equation))
      (equation
       (if (proof-is-call value *proof-if*)
           (proof-with-checked-results ((no (proof-term-at value 3)))
             (if (equal no *proof-false*)
                 (t3-scan-select-search-application lib equation value nonnil definitions)
               equation))
         equation))
      (value (t3-scan-step-right equation)))
     (if (proof-is-call value *t3-scan-search-start*)
         equation
       '(:failure "Unsupported" "")))))

(defun t3-scan-extend-search-order (lib term start evidence index result-type order)
  (proof-with-checked-results
   ((whitespace (t3-scan-infer-whitespace-result lib start evidence))
    (lib (car whitespace))
    (old (proof-term-at start 2))
    (before (t3-logic-evidence-require (cdr whitespace) (library-le old start)))
    (old-type (t3-logic-evidence-integer (cdr before) old))
    (order (library-library-cite lib "T3-WEAK-TRANSITIVE" (list old start term)
                                (list (car old-type) index result-type (car before) order)))
    (evidence (t3-scan-record-steps (cdr old-type) (list order))))
   (cons lib evidence)))

(defun t3-scan-infer-search-nonnil (lib term evidence nonnil)
  (proof-with-checked-results
   ((opened (t3-scan-search-application lib term nonnil))
    (exact (t3-scan-step-right opened))
    (updated-lib (if (assoc-equal *t3-scan-search-bound* (proof-proof-facts (library-library-proof lib)))
                     lib
                   (t3-scan-search-index-bound lib)))
    (evidence (t3-scan-with-updated-library evidence lib updated-lib))
    (proof (library-library-proof updated-lib))
    (formals (t3-scan-formals updated-lib *t3-scan-search-start*))
    (step (proof-proof-fact proof *t3-scan-search-bound* (seq-zip formals (cdr exact))))
    (nonempty (proof-proof-rewrite proof nonnil opened '(1)))
    (proved (proof-proof-prove-if proof step nonempty))
    (index-rest (proof-proof-conjunct proof proved))
    (bound-rest (proof-proof-conjunct proof (cadr index-rest)))
    (type-order (proof-proof-conjunct proof (cadr bound-rest)))
    (reverse (proof-proof-symmetric proof opened))
    (result-type (proof-proof-rewrite-first proof (car type-order) reverse))
    (reverse (proof-proof-symmetric proof opened))
    (order (proof-proof-rewrite-first proof (cadr type-order) reverse))
    (evidence (t3-scan-record-steps evidence (list (car index-rest) (car bound-rest) result-type order)))
    (start (proof-term-at exact 3)))
   (if (proof-is-call start *t3-scan-whitespace*)
       (t3-scan-extend-search-order updated-lib term start evidence (car index-rest) result-type order)
     (cons updated-lib evidence))))

(defun t3-scan-infer-search-result (lib term evidence)
  (proof-with-checked-results ((nonnil (t3-logic-evidence-find evidence term)))
    (if (car nonnil)
        (t3-scan-infer-search-nonnil lib term (cdr nonnil) (car nonnil))
      (proof-with-checked-results
       ((different (t3-logic-evidence-find (cdr nonnil) (proof-neg (proof-eq term *proof-false*)))))
       (if (not (car different))
           (cons lib (cdr different))
         (let ((proof (library-library-proof lib)))
           (proof-with-checked-results
            ((either (proof-proof-nil-or-true proof term))
             (cut (proof-proof-cut proof either (car different)))
             (nonnil (proof-proof-front proof cut term)))
            (t3-scan-infer-search-nonnil lib term (cdr different) nonnil))))))))

(mutual-recursion
 (defun t3-scan-infer-scan-result (lib term evidence)
   (declare (xargs :measure (1+ (* 2 (acl2-count term)))))
   (cond ((proof-is-call term *proof-plus*) (t3-scan-infer-scan-arguments lib (cdr term) evidence))
         ((proof-is-call term *t3-scan-skip-alternative*) (t3-scan-infer-skip-result lib term evidence))
         ((proof-is-call term *t3-scan-search*) (t3-scan-infer-search-result lib term evidence))
         ((proof-is-call term *t3-scan-whitespace*) (t3-scan-infer-whitespace-result lib term evidence))
         (t (cons lib evidence))))

 (defun t3-scan-infer-scan-arguments (lib arguments evidence)
   (declare (xargs :measure (* 2 (acl2-count arguments))))
   (if (endp arguments)
       (cons lib evidence)
     (proof-with-checked-results ((result (t3-scan-infer-scan-result lib (car arguments) evidence)))
       (t3-scan-infer-scan-arguments (car result) (cdr arguments) (cdr result))))))
