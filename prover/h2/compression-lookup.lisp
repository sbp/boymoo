(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h2-compression-lookup-key* (proof-sym "INDEX" "ACL2"))
(defconst *h2-compression-lookup-accumulator* (proof-sym "ACCUMULATOR" "ACL2"))
(defconst *h2-compression-lookup-null* (proof-cl "NULL"))
(defconst *h2-compression-lookup-header-key*
  (proof-quote (proof-sym "HEADER" "KEYWORD")))
(defconst *h2-compression-lookup-array1p* (proof-sym "ARRAY1P" "ACL2"))
(defconst *h2-compression-lookup-dimensions* (proof-sym "DIMENSIONS" "ACL2"))
(defconst *h2-compression-lookup-aref* (proof-sym "AREF1" "ACL2"))
(defconst *h2-compression-lookup-bounded*
  (proof-sym "BOUNDED-INTEGER-ALISTP" "ACL2"))

(defun h2-compression-lookup-request-p (result)
  (and (consp result) (eq (car result) :h2-compression-lookup-request)))

(defun h2-compression-lookup-request-operation (request)
  (cadr request))

(defun h2-compression-lookup-request-proof (request)
  (caddr request))

(defun h2-compression-lookup-request-args (request)
  (cadddr request))

; The context pairs the caller's BookProof with the remaining operation replies.
(defund h2-compression-lookup-operation (context operation args)
  (let ((replies (cdr context)))
    (if (endp replies)
        (list :h2-compression-lookup-request operation (car context) args)
      (let ((reply (car replies)))
        (if (failure-p reply)
            (cons reply (cons (car context) (cdr replies)))
          (cons (car reply) (cons (cdr reply) (cdr replies))))))))

(defmacro h2-compression-lookup-with-calls (bindings body)
  (if (endp bindings)
      body
    (let ((name (caar bindings))
          (call (cadar bindings)))
      `(let ((h2-compression-lookup-reply ,call))
         (if (h2-compression-lookup-request-p h2-compression-lookup-reply)
             h2-compression-lookup-reply
           (let ((,name (car h2-compression-lookup-reply))
                 (context (cdr h2-compression-lookup-reply)))
             (declare (ignorable context))
             (if (failure-p ,name)
                 h2-compression-lookup-reply
               (h2-compression-lookup-with-calls ,(cdr bindings) ,body))))))))

(defmacro h2-compression-lookup-check (bindings body)
  (if (endp bindings)
      body
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (failure-p ,name)
             (cons ,name context)
           (h2-compression-lookup-check ,(cdr bindings) ,body))))))

(defmacro h2-compression-lookup-with-folded (terms body)
  `(h2-compression-lookup-with-calls
       ((saved-calls (h2-compression-lookup-operation
                      context :keep-folded (list ,terms))))
     (let ((scoped-result ,body))
       (if (h2-compression-lookup-request-p scoped-result)
           scoped-result
         (h2-compression-lookup-with-calls
             ((restored (h2-compression-lookup-operation
                         (cdr scoped-result) :restore-fixed-calls (list saved-calls))))
           (cons (car scoped-result) context))))))

(defun h2-compression-lookup-derive (context formula definitions facts seeds cases)
  (h2-compression-lookup-operation
   context :derive (list formula definitions facts nil 1 "" seeds cases 80)))

(defun h2-compression-lookup-auxiliary
    (context name formula definitions facts cases)
  (h2-compression-lookup-operation
   context :auxiliary (list name formula definitions facts nil 1 "" nil cases 80)))

(defun h2-compression-lookup-base (proof)
  (library-library-proof (h2-search-search-library proof)))

(defun h2-compression-lookup-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h2-compression-lookup-arguments (term count)
  (if (integerp term)
      '(:failure "failure" "")
    (proof-list-of-length (cdr term) count)))

(defun h2-compression-lookup-assoc (key data)
  (list *h2-alist-recognizers-assoc* key data))

(defun h2-compression-lookup-lemma-present-p (proof name)
  (if (assoc-equal (proof-sym name "ACL2")
                   (proof-proof-facts (h2-compression-lookup-base proof)))
      t
    nil))

(defun h2-compression-lookup-omitted (entry default)
  (let ((missing (list *h2-compression-lookup-null* entry)))
    (proof-ite missing missing (proof-eq (list *library-cdr* entry) default))))

(defun h2-compression-lookup-specialize-view-run
    (context key entry rest index evidence)
  (let* ((tail-lookup (h2-compression-lookup-assoc key rest))
         (source (h2-compression-lookup-assoc key (list *proof-cons* entry rest)))
         (target (proof-eq source (proof-ite (proof-eq key index) entry tail-lookup))))
    (h2-compression-lookup-with-folded (list entry tail-lookup)
      (h2-compression-lookup-with-calls
          ((assoc-law (h2-compression-lookup-operation
                       context :search '(:compression-lookup-assoc-returned-key))))
        (h2-compression-lookup-derive context target "ASSOC-EQUAL"
                                      (list assoc-law) (list evidence) nil)))))

(defun h2-compression-lookup-revappend-view-run (context first second result)
  (h2-compression-lookup-with-folded (list result)
    (h2-compression-lookup-derive
     context (proof-eq (list *h2-alist-recognizers-revappend* first second) result)
     "REVAPPEND" nil nil nil)))

(defun h2-compression-lookup-skip-status (proof index limit index-type limit-type)
  (let* ((span (library-diff limit index))
         (test (list *h2-compression-zp* span))
         (integers (list index-type limit-type))
         (library (h2-search-search-library proof))
         (base (library-library-proof library)))
    (proof-with-checked-results
        ((opening (proof-proof-unfold base test))
         (typed (library-library-type-of library span integers))
         (check (h2-book-logic-select-body proof opening typed))
         (comparison (library-library-comparison library index limit integers))
         (reversed (proof-proof-symmetric base comparison)))
      (proof-proof-rewrite base check reversed '(1 2 1)))))

(defun h2-compression-lookup-find-part (parts term compare-head)
  (if (endp parts)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first (car parts))))
      (if (if compare-head (proof-is-call literal term) (equal literal term))
          (car parts)
        (h2-compression-lookup-find-part (cdr parts) term compare-head)))))

(defun h2-compression-lookup-array-bounds (proof condition dimension-name)
  (let ((base (h2-compression-lookup-base proof)))
    (proof-with-checked-results
        ((data (h2-compression-lookup-step-at condition 2))
         (literal (proof-step-first condition))
         (view (h2-book-logic-logical-equation proof literal))
         (opened (proof-proof-rewrite base condition view '(1)))
         (parts (h2-ranges-conjuncts proof opened))
         (bound (h2-compression-lookup-find-part
                 parts *h2-compression-lookup-bounded* t))
         (dim (list *h2-compression-lookup-dimensions* dimension-name data))
         (expanded (h2-book-logic-logical-equation proof dim))
         (header (list *h2-compression-header* dimension-name data))
         (header-view (h2-book-logic-logical-equation proof header))
         (expansion (proof-step-first expanded))
         (expanded (proof-proof-rewrite-result base expanded header-view expansion header))
         (dimension (h2-compression-lookup-step-at bound 2))
         (length-type (h2-compression-lookup-find-part
                       parts (library-integer dimension) nil))
         (reversed (proof-proof-symmetric base expanded))
         (typed (proof-proof-rewrite base length-type reversed '(1 1 1)))
         (bounded (proof-proof-rewrite base bound reversed '(1 2 1)))
         (alist (h2-compression-lookup-find-part
                 parts (list *h2-alist-recognizers-alist* data) nil))
         (typed-literal (proof-step-first typed))
         (bounded-length (h2-compression-lookup-step-at bounded 2)))
      (let ((length-term (list *library-car* dim)))
        (if (and (equal typed-literal (library-integer length-term))
                 (equal bounded-length length-term))
            (list alist typed bounded)
          '(:failure "failure" ""))))))

(defund h2-compression-lookup-heading-facts-step (context library replies)
  (h2-compression-lookup-check ((result (h2-alists-heading-facts library replies)))
    (h2-compression-lookup-with-calls
        ((installed (h2-compression-lookup-operation
                     context :with-library (list (cdr result)))))
      (if (h2-alists-request-p (car result))
          (h2-compression-lookup-with-calls
              ((step (h2-compression-lookup-operation
                      context :derive (h2-alists-request-arguments (car result))))
               (updated-library (h2-compression-lookup-operation context :library nil)))
            (cons (list :reply (cons step updated-library)) context))
        (cons (list :names (car result)) context)))))

(defun h2-compression-lookup-heading-facts-run (n context library replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons '(:failure "Fuel" "h2-compression-lookup-heading-facts-run") context)
    (h2-compression-lookup-with-calls
        ((next (h2-compression-lookup-heading-facts-step context library replies)))
      (if (eq (car next) :reply)
          (h2-compression-lookup-heading-facts-run
           (1- n) context library (append replies (list (cadr next))))
        (cons (cadr next) context)))))

(defun h2-compression-lookup-header-independent-lookup-run (context)
  (let* ((key *h2-compression-lookup-key*)
         (data *h2-compression-data*)
         (core (h2-compression-lookup-assoc *h2-compression-lookup-header-key* data))
         (header (list *h2-compression-header* *h2-compression-name* data))
         (source (h2-compression-lookup-assoc key (list *proof-cons* header *library-y*)))
         (target (h2-compression-lookup-assoc key *library-y*))
         (formula (list *library-implies* (library-integer key) (proof-eq source target))))
    (h2-compression-lookup-with-calls
        ((library (h2-compression-lookup-operation context :library nil))
         (heading (h2-compression-lookup-heading-facts-run 1000000 context library nil)))
      (h2-compression-lookup-with-folded (list core target)
        (h2-compression-lookup-with-calls
            ((assoc-law (h2-compression-lookup-operation
                         context :search '(:compression-lookup-assoc-returned-key))))
          (h2-compression-lookup-auxiliary
           context "ASSOC-AFTER-ARRAY-HEADER" formula "HEADER ASSOC-EQUAL"
           (list assoc-law (cadr heading)) (list core)))))))

(defun h2-compression-lookup-aref-integer-view-run (context)
  (let* ((key *h2-compression-lookup-key*)
         (name *h2-compression-name*)
         (data *h2-compression-data*)
         (entry (h2-compression-lookup-assoc key data))
         (value (proof-ite entry (list *library-cdr* entry)
                           (list *h2-compression-default* name data)))
         (formula (list *library-implies* (library-integer key)
                        (proof-eq (list *h2-compression-lookup-aref* name data key)
                                  value))))
    (h2-compression-lookup-with-calls
        ((library (h2-compression-lookup-operation context :library nil))
         (heading (h2-compression-lookup-heading-facts-run 1000000 context library nil)))
      (h2-compression-lookup-with-folded (list entry)
        (h2-compression-lookup-auxiliary
         context "AREF1-INTEGER-LOOKUP" formula "AREF1 EQ NULL"
         (list (cadr heading)) (list entry))))))

(defun h2-compression-lookup-bound-key
    (context library check car-cons assoc-law exists key data key-type limit outside actual)
  (let ((base (library-library-proof library)))
    (h2-compression-lookup-check
        ((view (proof-proof-fact base (proof-sym assoc-law "ACL2")
                                 (list (list *library-x* key) (list *library-y* data))))
         (key-value (h2-book-logic-select-body library view exists))
         (check (proof-proof-rewrite-first base check car-cons))
         (check (proof-proof-rewrite-first base check key-value)))
      (h2-compression-lookup-with-calls
          ((heading (h2-compression-lookup-heading-facts-run 1000000 context library nil))
           (library (h2-compression-lookup-operation context :library nil)))
        (h2-compression-lookup-check
            ((other-header (library-library-cite library "H2-INTEGER-NOT-HEADER"
                                                (list key) (list key-type)))
             (test (h2-compression-lookup-step-at check 1)))
          (h2-compression-lookup-with-calls
              ((negative (h2-compression-lookup-derive
                          context (proof-neg test) "EQ" nil (list other-header) nil))
               (library (h2-compression-lookup-operation context :library nil)))
            (let ((base (library-library-proof library)))
              (h2-compression-lookup-check
                  ((guarded-ranges (proof-proof-prove-if base check negative))
                   (ranges (proof-proof-prove-if base guarded-ranges key-type))
                   (parts (proof-proof-conjunct base ranges))
                   (upper (cadr parts))
                   (upper-literal (proof-step-first upper)))
                (if (equal upper-literal (library-lt key limit))
                    (h2-compression-lookup-check
                        ((cut (proof-proof-cut base upper outside))
                         (missing (proof-proof-front base cut (proof-neg actual)))
                         (value (h2-search-search-nil-value library missing)))
                      (cons value context))
                  (cons '(:failure "failure" "") context))))))))))

(defun h2-compression-lookup-lookup-above-bound-run
    (context key-type bounded outside)
  (h2-compression-lookup-check
      ((bounded-term (proof-step-first bounded))
       (fields (h2-compression-lookup-arguments bounded-term 2))
       (key (h2-compression-lookup-step-at key-type 1)))
    (let* ((data (car fields))
           (limit (cadr fields))
           (actual (h2-compression-lookup-assoc key data))
           (recognizer (list *h2-compression-lookup-bounded*
                             *h2-alist-recognizers-bound*)))
      (h2-compression-lookup-with-calls
          ((parts (h2-compression-lookup-operation
                   context :search (list :compression-lookup-list-parts recognizer)))
           (law (h2-compression-lookup-operation
                 context :search (list :compression-lookup-lookup-singleton recognizer parts)))
           (library (h2-compression-lookup-operation context :library nil)))
        (let ((base (library-library-proof library)))
          (h2-compression-lookup-check
              ((signature
                (proof-proof-fact
                 base (proof-sym law "ACL2")
                 (list (list *library-x* data)
                       (list *h2-alist-recognizers-key* key)
                       (list *h2-alist-recognizers-bound* limit))))
               (exists (proof-proof-assume base actual t))
               (premise (h2-compression-lookup-step-at signature 1))
               (support (proof-proof-prove base premise (list bounded exists) nil))
               (one (proof-proof-modus-ponens base signature support))
               (singleton (h2-compression-lookup-step-at one 1))
               (literal (proof-step-first one))
               (opening (h2-book-logic-logical-equation library literal))
               (opened (proof-proof-rewrite base one opening '(1))))
            (h2-compression-lookup-with-calls
                ((cons-proof (h2-compression-lookup-derive
                              context (proof-neg (list (proof-cl "ATOM") singleton))
                              "" nil nil nil))
                 (library (h2-compression-lookup-operation context :library nil)))
              (let ((base (library-library-proof library)))
                (h2-compression-lookup-check
                    ((shape (proof-proof-prove-if base opened cons-proof))
                     (shape-parts (proof-proof-conjunct base shape))
                     (field-parts (proof-proof-conjunct base (cadr shape-parts))))
                  (h2-compression-lookup-with-calls
                      ((car-cons (h2-compression-lookup-derive
                                  context (proof-eq (list *library-car* singleton) actual)
                                  "" nil nil nil))
                       (assoc-law (h2-compression-lookup-operation
                                   context :search '(:compression-lookup-assoc-returned-key)))
                       (library (h2-compression-lookup-operation context :library nil)))
                    (h2-compression-lookup-bound-key
                     context library (car field-parts) car-cons assoc-law exists
                     key data key-type limit outside actual)))))))))))

(defun h2-compression-lookup-empty-loop
    (context library seek empty left-place backwards)
  (let ((base (library-library-proof library)))
    (h2-compression-lookup-check
        ((reflexive (proof-proof-reflexive base seek))
         (empty-lookup (proof-proof-rewrite base reflexive empty left-place)))
      (h2-compression-lookup-with-calls
          ((equation
            (if backwards
                (h2-compression-lookup-revappend-view-run
                 context *proof-false* *h2-compression-lookup-accumulator*
                 *h2-compression-lookup-accumulator*)
              (h2-compression-lookup-derive
               context
               (proof-eq
                (h2-compression-lookup-assoc *h2-compression-lookup-key* *proof-false*)
                *proof-false*)
               "ASSOC-EQUAL" nil nil nil)))
           (library (h2-compression-lookup-operation context :library nil)))
        (let ((base (library-library-proof library)))
          (h2-compression-lookup-check
              ((value (if backwards
                          (proof-proof-rewrite base empty-lookup equation '(1 2 2))
                        (proof-proof-chain base empty-lookup (list equation)))))
            (cons value context)))))))

(defun h2-compression-lookup-loop-base
    (library target lower upper earlier reached too-large empty-lookup
             claim key-type index-type limit-type stopped)
  (let ((base (library-library-proof library)))
    (proof-with-checked-results
        ((selected (proof-proof-select base target earlier))
         (reversed (proof-proof-symmetric base selected))
         (left-outside (proof-proof-chain base empty-lookup (list reversed)))
         (selected (proof-proof-select base target reached))
         (subtarget (proof-term-at target 3))
         (selected-subtarget (proof-proof-select base subtarget too-large))
         (beyond (proof-proof-chain base selected (list selected-subtarget)))
         (reversed (proof-proof-symmetric base beyond))
         (right-outside (proof-proof-chain base empty-lookup (list reversed)))
         (below-upper (proof-proof-assume base upper t))
         (impossible (library-library-cite
                      library "WEAK-THEN-LESS"
                      (list *h2-compression-index* *h2-compression-lookup-key*
                            *h2-compression-limit*)
                      (list index-type key-type limit-type reached below-upper)))
         (conflict (proof-proof-cut base impossible stopped))
         (conflict (proof-proof-subsume base conflict
                                        (cons claim (proof-step-clause conflict))))
         (right (proof-proof-cases base upper conflict right-outside)))
      (proof-proof-cases base lower left-outside right))))

(defun h2-compression-lookup-loop-order
    (library step step-type rising still-scanning earlier reached
             key-type index-type lower)
  (let* ((base (library-library-proof library))
         (key *h2-compression-lookup-key*)
         (index *h2-compression-index*)
         (test (proof-eq key index))
         (before-step (library-lt key step)))
    (proof-with-checked-results
        ((same (proof-proof-assume base test t))
         (different (proof-proof-assume base test nil))
         (reversed (proof-proof-symmetric base same))
         (at-entry (proof-proof-rewrite base rising reversed '(1 1)))
         (weak-refl (library-library-cite library "WEAK-REFLEXIVE"
                                          (list index) (list index-type)))
         (reversed (proof-proof-symmetric base same))
         (not-before (proof-proof-rewrite base weak-refl reversed '(1 1 1)))
         (reversed (proof-proof-symmetric base same))
         (below-end (proof-proof-rewrite base still-scanning reversed '(1 1)))
         (before-child (library-library-cite
                        library "LESS-TRANSITIVE" (list key index step)
                        (list key-type index-type step-type earlier rising)))
         (past-entry (library-library-cite
                      library "H2-INTEGER-TRICHOTOMY" (list key index)
                      (list key-type index-type reached different)))
         (step-bound (library-library-axiom library "COMMUTATIVITY-OF-+"
                                            (list index *proof-one*)))
         (bound (proof-proof-assume base before-step t))
         (bound (proof-proof-rewrite base bound step-bound '(1 2)))
         (inside-step (library-library-cite
                       library "H2-INTEGER-SUCCESSOR-BOUND"
                       (list key index) (list key-type index-type bound)))
         (cut (proof-proof-cut base past-entry inside-step))
         (past-child (proof-proof-front base cut (proof-neg before-step))))
      (list (list test same different)
            (list at-entry not-before below-end)
            (list before-child past-child earlier reached lower)))))

(defun h2-compression-lookup-loop-track
    (context backwards decision tracked saved child output next-accumulator order)
  (let* ((key *h2-compression-lookup-key*)
         (index *h2-compression-index*)
         (accumulator *h2-compression-lookup-accumulator*)
         (same (cadar order))
         (different (caddar order)))
    (h2-compression-lookup-with-calls
        ((entry-exists (h2-compression-lookup-derive
                        context saved "" nil (list decision) (list saved))))
      (if backwards
          (h2-compression-lookup-with-calls
              ((view (h2-compression-lookup-revappend-view-run
                      context output accumulator
                      (list *h2-alist-recognizers-revappend* child next-accumulator)))
               (library (h2-compression-lookup-operation context :library nil)))
            (h2-compression-lookup-check
                ((tracked (proof-proof-rewrite
                           (library-library-proof library) tracked view '(1 2 2))))
              (h2-compression-lookup-with-calls
                  ((fallback (h2-compression-lookup-specialize-view-run
                              context key saved accumulator index entry-exists)))
                (cons (list tracked tracked fallback) context))))
        (h2-compression-lookup-with-calls
            ((view (h2-compression-lookup-specialize-view-run
                    context key saved child index entry-exists))
             (library (h2-compression-lookup-operation context :library nil)))
          (let ((base (library-library-proof library)))
            (h2-compression-lookup-check
                ((selected (h2-book-logic-select-body library view same))
                 (attained (proof-proof-chain base tracked (list selected)))
                 (selected (h2-book-logic-select-body library view different))
                 (missed (proof-proof-chain base tracked (list selected))))
              (cons (list attained missed nil) context))))))))

(defun h2-compression-lookup-loop-hit
    (context library select-induction induction tracking order entry target decision)
  (let* ((base (library-library-proof library))
         (attained (car tracking))
         (fallback-update (caddr tracking))
         (same (cadar order))
         (hit-bounds (cadr order))
         (at-entry (car hit-bounds))
         (not-before (cadr hit-bounds))
         (below-end (caddr hit-bounds)))
    (h2-compression-lookup-check
        ((attained
          (if select-induction
              (proof-with-checked-results
                  ((selected (h2-book-logic-select-body library induction at-entry)))
                (proof-proof-chain base attained (list selected)))
            attained))
         (attained
          (if fallback-update
              (proof-with-checked-results
                  ((selected (h2-book-logic-select-body library fallback-update same)))
                (proof-proof-chain base attained (list selected)))
            attained))
         (selected (proof-proof-select base target not-before))
         (subtarget (proof-term-at target 3))
         (selected-subtarget (proof-proof-select base subtarget below-end))
         (same-target (proof-proof-chain base selected (list selected-subtarget)))
         (same-entry (proof-proof-reflexive base entry))
         (same-entry (proof-proof-rewrite base same-entry same '(1 2 1)))
         (same-right (h2-compression-lookup-step-at same-target 2))
         (same-target (proof-proof-rewrite-result
                       base same-target same-entry (proof-eq *proof-false* same-right) entry))
         (same-right (h2-compression-lookup-step-at same-target 2))
         (attained-right (h2-compression-lookup-step-at attained 2)))
      (h2-compression-lookup-with-calls
          ((same-result (h2-compression-lookup-derive
                         context (proof-eq same-right attained-right)
                         "" nil (list decision) nil))
           (library (h2-compression-lookup-operation context :library nil)))
        (let ((base (library-library-proof library)))
          (h2-compression-lookup-check
              ((same-result (proof-proof-chain base same-target (list same-result)))
               (reversed (proof-proof-symmetric base same-result))
               (hit (proof-proof-chain base attained (list reversed))))
            (cons hit context)))))))

(defun h2-compression-lookup-loop-miss
    (library hit induction tracking order target)
  (let* ((base (library-library-proof library))
         (test (caar order))
         (different (caddar order))
         (missed (cadr tracking))
         (fallback-update (caddr tracking))
         (miss-bounds (caddr order))
         (before-child (car miss-bounds))
         (past-child (cadr miss-bounds))
         (earlier (caddr miss-bounds))
         (reached (cadddr miss-bounds))
         (lower (car (cddddr miss-bounds))))
    (proof-with-checked-results
        ((missed (proof-proof-chain base missed (list induction)))
         (missed
          (if fallback-update
              (proof-with-checked-results
                  ((unchanged (h2-book-logic-select-body library fallback-update different))
                   (literal (proof-step-first missed))
                   (slot (h2-compression-lookup-step-at unchanged 1)))
                (proof-proof-rewrite-result base missed unchanged literal slot))
            missed))
         (selected (h2-book-logic-select-body library missed before-child))
         (target-view (proof-proof-select base target earlier))
         (reversed (proof-proof-symmetric base target-view))
         (before (proof-proof-chain base selected (list reversed)))
         (selected (h2-book-logic-select-body library missed past-child))
         (target-view (proof-proof-select base target reached))
         (reversed (proof-proof-symmetric base target-view))
         (after (proof-proof-chain base selected (list reversed)))
         (outside (proof-proof-cases base lower before after)))
      (proof-proof-cases base test hit outside))))

(defun h2-compression-lookup-loop-iteration
    (context backwards skipped active seek left-place entry target formula
             step decrease evidence order drop child output saved)
  (h2-compression-lookup-with-calls
      ((library (h2-compression-lookup-operation context :library nil)))
    (let ((base (library-library-proof library))
          (accumulator *h2-compression-lookup-accumulator*))
      (h2-compression-lookup-check ((decision (proof-proof-assume base drop skipped)))
        (let* ((next-accumulator (if skipped accumulator (list *proof-cons* saved accumulator)))
               (index-binding (list *h2-compression-index* step))
               (advance (if (and backwards (not skipped))
                            (list index-binding (list accumulator next-accumulator))
                          (list index-binding))))
          (h2-compression-lookup-check
              ((decrease-literal (proof-step-first decrease))
               (smaller-formula (proof-subst formula (proof-bindings-table advance nil)))
               (smaller (proof-proof-assume base
                                            (proof-ite decrease-literal smaller-formula *proof-true*)
                                            t))
               (implication (proof-proof-prove-if base smaller decrease))
               (guard (h2-compression-lookup-step-at implication 1))
               (premise (proof-proof-prove base guard evidence nil))
               (induction (proof-proof-modus-ponens base implication premise))
               (selected (h2-book-logic-select-body library active decision))
               (reflexive (proof-proof-reflexive base seek))
               (tracked (proof-proof-rewrite base reflexive selected left-place)))
            (h2-compression-lookup-with-calls
                ((tracking
                  (if skipped
                      (cons (list tracked tracked nil) context)
                    (h2-compression-lookup-loop-track
                     context backwards decision tracked saved child output next-accumulator order)))
                 (library (h2-compression-lookup-operation context :library nil))
                 (hit (h2-compression-lookup-loop-hit
                       context library (or backwards skipped) induction
                       tracking order entry target decision))
                 (library (h2-compression-lookup-operation context :library nil)))
              (h2-compression-lookup-check
                  ((outcome (h2-compression-lookup-loop-miss
                             library hit induction tracking order target)))
                (cons (list outcome advance) context)))))))))

(defun h2-compression-lookup-loop-finish
    (context backwards active seek left-place entry target formula
             step decrease evidence order drop child output saved stopping base-case span stem name)
  (h2-compression-lookup-with-calls
      ((skipped (h2-compression-lookup-loop-iteration
                 context backwards t active seek left-place entry target formula
                 step decrease evidence order drop child output saved))
       (retained (h2-compression-lookup-loop-iteration
                  context backwards nil active seek left-place entry target formula
                  step decrease evidence order drop child output saved))
       (library (h2-compression-lookup-operation context :library nil)))
    (let* ((base (library-library-proof library))
           (skipped-update (cadr skipped))
           (retained-update (cadr retained))
           (updates (if (equal skipped-update retained-update)
                        (list skipped-update)
                      (list skipped-update retained-update))))
      (h2-compression-lookup-check
          ((continuing (proof-proof-cases base drop (car skipped) (car retained)))
           (cases (proof-proof-cases base stopping base-case continuing))
           (ordinal (library-library-builtin library 1 span))
           (case-proof (h2-search-search-introduce library formula cases))
           (proved (proof-proof-induct base ordinal case-proof formula
                                       (list *library-count* span) updates)))
        (h2-compression-lookup-with-calls
            ((added (h2-compression-lookup-operation
                     context :lemma (list (concatenate 'string "H2-" stem) formula proved nil))))
          (cons name context))))))

(defun h2-compression-lookup-loop-running
    (context library backwards active seek left-place entry target formula
             lower upper claim key-type index-type limit-type empty-lookup
             stopped still-scanning running stopping span stem name)
  (let* ((base (library-library-proof library))
         (index *h2-compression-index*)
         (limit *h2-compression-limit*)
         (step (library-plus index *proof-one*)))
    (h2-compression-lookup-check
        ((earlier (proof-proof-assume base lower t))
         (reached (proof-proof-assume base lower nil))
         (too-large (proof-proof-assume base upper nil))
         (base-case (h2-compression-lookup-loop-base
                     library target lower upper earlier reached too-large empty-lookup
                     claim key-type index-type limit-type stopped))
         (body (h2-compression-lookup-step-at active 2))
         (parts (h2-compression-lookup-arguments body 3))
         (drop (car parts))
         (child (cadr parts))
         (output (caddr parts))
         (saved (proof-term-at output 1))
         (step-type (library-library-type-of library step (list index-type)))
         (rising (library-library-cite library "SUCCESSOR-LARGER"
                                       (list index) (list index-type)))
         (commutative (library-library-axiom library "COMMUTATIVITY-OF-+"
                                             (list *proof-one* index)))
         (rising (proof-proof-rewrite base rising commutative '(1 2))))
      (h2-compression-lookup-with-calls
          ((decrease (h2-compression-lookup-operation
                      context :search (list :compression-lookup-range-decrease index limit running)))
           (library (h2-compression-lookup-operation context :library nil)))
        (h2-compression-lookup-check
            ((order (h2-compression-lookup-loop-order
                     library step step-type rising still-scanning earlier reached
                     key-type index-type lower)))
          (h2-compression-lookup-loop-finish
           context backwards active seek left-place entry target formula step decrease
           (list key-type step-type limit-type) order drop child output saved
           stopping base-case span stem name))))))

(defun h2-compression-lookup-loop-stopping (context library backwards stem name)
  (let* ((base (library-library-proof library))
         (key *h2-compression-lookup-key*)
         (index *h2-compression-index*)
         (limit *h2-compression-limit*)
         (data *h2-compression-data*)
         (default *h2-compression-default*)
         (accumulator *h2-compression-lookup-accumulator*)
         (loop-term (list *h2-compression-compress-loop* *h2-compression-name*
                          data index limit default))
         (seek (h2-compression-lookup-assoc
                key (if backwards
                        (list *h2-alist-recognizers-revappend* loop-term accumulator)
                      loop-term)))
         (fallback (if backwards (h2-compression-lookup-assoc key accumulator) *proof-false*))
         (entry (h2-compression-lookup-assoc key data))
         (lower (library-lt key index))
         (upper (library-lt key limit))
         (target (proof-ite lower fallback
                            (proof-ite upper
                                       (proof-ite (h2-compression-lookup-omitted entry default)
                                                  fallback entry)
                                       fallback)))
         (claim (proof-eq seek target))
         (guard (proof-ite (library-integer key)
                           (proof-ite (library-integer index) (library-integer limit)
                                      *proof-false*)
                           *proof-false*))
         (formula (list *library-implies* guard claim))
         (span (library-diff limit index))
         (stopping (list *h2-compression-zp* span))
         (left-place (if backwards '(1 2 2 1) '(1 2 2))))
    (h2-compression-lookup-check
        ((assumed (proof-proof-assume base guard t))
         (types (proof-proof-conjunct base assumed))
         (key-type (car types))
         (range-types (proof-proof-conjunct base (cadr types)))
         (index-type (car range-types))
         (limit-type (cadr range-types))
         (stationary (proof-proof-assume base stopping t))
         (running (proof-proof-assume base stopping nil))
         (stop-view (h2-compression-lookup-skip-status
                     library index limit index-type limit-type))
         (empty (h2-compression-logical-branch library loop-term stationary))
         (active (h2-compression-logical-branch library loop-term running))
         (stopped (proof-proof-rewrite base stationary stop-view '(1)))
         (running-view (proof-proof-rewrite base running stop-view '(1 1))))
      (h2-compression-lookup-with-calls
          ((still-scanning (h2-compression-lookup-derive
                            context (library-lt index limit) "" nil (list running-view) nil))
           (library (h2-compression-lookup-operation context :library nil))
           (empty-lookup (h2-compression-lookup-empty-loop
                          context library seek empty left-place backwards))
           (library (h2-compression-lookup-operation context :library nil)))
        (h2-compression-lookup-loop-running
         context library backwards active seek left-place entry target formula
         lower upper claim key-type index-type limit-type empty-lookup
         stopped still-scanning running stopping span stem name)))))

(defun h2-compression-lookup-lookup-on-loop-run (context backwards)
  (let* ((stem (concatenate 'string "COMPRESS-LOOKUP-"
                            (if backwards "REVAPPEND" "FORWARD")))
         (name (concatenate 'string "SELF-H2-" stem)))
    (h2-compression-lookup-with-calls
        ((library (h2-compression-lookup-operation context :library nil)))
      (if (h2-compression-lookup-lemma-present-p library name)
          (cons name context)
        (h2-compression-lookup-loop-stopping context library backwards stem name)))))

(defund h2-compression-lookup-leaf-test (library choice header header-view)
  (let ((base (library-library-proof library)))
    (proof-with-checked-results
        ((choice (proof-list-of-length choice 2))
         (test (car choice))
         (holds (cadr choice))
         (comparison (h2-book-logic-logical-equation library test))
         (right (h2-compression-lookup-step-at comparison 2))
         (comparison (proof-proof-rewrite-result
                      base comparison header-view (proof-eq *proof-false* right) header))
         (assumption (proof-proof-assume base test holds)))
      (proof-proof-rewrite base assumption comparison (if holds '(1) '(1 1))))))

(defun h2-compression-lookup-leaf-tests (library choices header header-view)
  (if (endp choices)
      nil
    (proof-with-checked-results
        ((test-proof (h2-compression-lookup-leaf-test library (car choices) header header-view))
         (rest (h2-compression-lookup-leaf-tests library (cdr choices) header header-view)))
      (cons test-proof rest))))

(defun h2-compression-lookup-leaf-reverse
    (context equation loop tail loop-bindings alist substitutions)
  (h2-compression-lookup-with-calls
      ((laws (h2-compression-lookup-operation
              context :search (list :compression-lookup-compression-laws
                                    (list *h2-alist-recognizers-alist*))))
       (library (h2-compression-lookup-operation context :library nil)))
    (let ((base (library-library-proof library)))
      (h2-compression-lookup-check
          ((loop-law (proof-term-at laws (if (consp laws) (1- (len laws)) 0)))
           (proper (proof-proof-fact base (proof-sym loop-law "ACL2") loop-bindings))
           (list-shape (proof-proof-modus-ponens base proper alist)))
        (h2-compression-lookup-with-calls
            ((not-string (h2-compression-lookup-derive
                          context (proof-neg (list *h2-alist-recognizers-string* loop))
                          "ALISTP" '("consp-not-stringp") (list list-shape) nil))
             (library (h2-compression-lookup-operation context :library nil)))
          (let ((base (library-library-proof library)))
            (h2-compression-lookup-check
                ((opening (proof-proof-unfold base tail))
                 (reversed-view (h2-book-logic-select-body library opening not-string))
                 (equation (proof-proof-rewrite base equation reversed-view '(1 2 2))))
              (cons (list equation (append substitutions
                                           (list (list *h2-compression-lookup-accumulator*
                                                       *proof-false*))))
                    context))))))))

(defun h2-compression-lookup-remove-empty (context equation key)
  (let ((expected (h2-compression-lookup-assoc key *proof-false*)))
    (h2-compression-lookup-with-calls
        ((empty (h2-compression-lookup-derive
                 context (proof-eq expected *proof-false*) "ASSOC-EQUAL" nil nil nil))
         (library (h2-compression-lookup-operation context :library nil)))
      (h2-compression-lookup-check
          ((right (h2-compression-lookup-step-at equation 2))
           (left (h2-compression-lookup-step-at empty 1))
           (value (proof-proof-rewrite-result (library-library-proof library)
                                              equation empty (proof-eq *proof-false* right)
                                              left)))
        (cons value context)))))

(defun h2-compression-lookup-leaf-interval
    (context backwards equation substitutions key key-type typed lower within)
  (h2-compression-lookup-with-calls
      ((loop-law (h2-compression-lookup-lookup-on-loop-run context backwards))
       (library (h2-compression-lookup-operation context :library nil)))
    (let ((base (library-library-proof library)))
      (h2-compression-lookup-check
          ((interval-law (proof-proof-fact base (proof-sym loop-law "ACL2") substitutions))
           (premise (h2-compression-lookup-step-at interval-law 1))
           (zero-type (library-library-type-of library *proof-zero* nil))
           (guard (proof-proof-prove base premise (list key-type zero-type typed) nil))
           (interval (proof-proof-modus-ponens base interval-law guard))
           (interval (h2-book-logic-select-body library interval lower))
           (interval (h2-book-logic-select-body library interval within))
           (equation (proof-proof-chain base equation (list interval))))
        (if backwards
            (h2-compression-lookup-remove-empty context equation key)
          (cons equation context))))))

(defun h2-compression-lookup-leaf-compressed
    (context library value key name data header-law key-type typed alist lower within)
  (let ((base (library-library-proof library)))
    (h2-compression-lookup-check
        ((tail (proof-term-at value 2))
         (backwards (proof-is-call tail *h2-alist-recognizers-reverse*))
         (loop-term (if backwards (proof-term-at tail 1) tail))
         (law (proof-proof-fact base (proof-sym header-law "ACL2")
                                (list (list *h2-compression-lookup-key* key)
                                      (list *h2-compression-name* name)
                                      (list *h2-compression-data* data)
                                      (list *library-y* tail))))
         (equation (proof-proof-modus-ponens base law key-type))
         (loop-bindings (seq-zip (list *h2-compression-name* *h2-compression-data*
                                     *h2-compression-index* *h2-compression-limit*
                                     *h2-compression-default*)
                                (cdr loop-term)))
         (substitutions (append loop-bindings (list (list *h2-compression-lookup-key* key)))))
      (h2-compression-lookup-with-calls
          ((prepared (if backwards
                         (h2-compression-lookup-leaf-reverse
                          context equation loop-term tail loop-bindings alist substitutions)
                       (cons (list equation substitutions) context))))
        (h2-compression-lookup-leaf-interval
         context backwards (car prepared) (cadr prepared) key key-type typed lower within)))))

(defun h2-compression-lookup-within-array-lookup-leaf-run
    (value choices context key name data old-lookup header header-view
           header-law key-type typed alist lower within target)
  (h2-compression-lookup-with-calls
      ((library (h2-compression-lookup-operation context :library nil)))
    (h2-compression-lookup-check
        ((tests (h2-compression-lookup-leaf-tests library choices header header-view))
         (equation (proof-proof-reflexive (library-library-proof library) old-lookup)))
      (h2-compression-lookup-with-calls
          ((equation (if (equal value data)
                         (cons equation context)
                       (h2-compression-lookup-leaf-compressed
                        context library value key name data header-law
                        key-type typed alist lower within))))
        (h2-compression-lookup-check ((right (h2-compression-lookup-step-at equation 2)))
          (h2-compression-lookup-with-calls
              ((aligned
                (h2-compression-lookup-with-folded (list old-lookup)
                  (h2-compression-lookup-derive
                   context (proof-eq right target) "NULL" nil tests (list old-lookup))))
               (library (h2-compression-lookup-operation context :library nil)))
            (h2-compression-lookup-check
                ((value (proof-proof-chain (library-library-proof library) equation
                                            (list aligned))))
              (cons value context))))))))

(defun h2-compression-lookup-by-value
    (n context value template choices key name data old-lookup header header-view
       header-law key-type typed alist lower within)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons '(:failure "Fuel" "h2-compression-lookup-by-value") context)
    (cond
     ((proof-is-call value *proof-if*)
      (h2-compression-lookup-check ((branches (h2-compression-lookup-arguments value 3)))
        (let ((test (car branches)))
          (h2-compression-lookup-with-calls
              ((yes (h2-compression-lookup-by-value
                     (1- n) context (cadr branches) template
                     (append choices (list (list test t)))
                     key name data old-lookup header header-view header-law
                     key-type typed alist lower within))
               (no (h2-compression-lookup-by-value
                    (1- n) context (caddr branches) template
                    (append choices (list (list test nil)))
                    key name data old-lookup header header-view header-law
                    key-type typed alist lower within))
               (library (h2-compression-lookup-operation context :library nil)))
            (h2-compression-lookup-check
                ((step (proof-by-value-join (library-library-proof library)
                                            value template yes no)))
              (cons step context))))))
     ((and (proof-compound value) (endp value))
      (cons (proof-index-failure) context))
     ((and (proof-compound value) (proof-compound (car value)))
      (h2-compression-lookup-with-calls
          ((library (h2-compression-lookup-operation context :library nil)))
        (h2-compression-lookup-check
            ((equality (proof-proof-beta (library-library-proof library) value))
             (opened (h2-compression-lookup-step-at equality 2)))
          (h2-compression-lookup-with-calls
              ((step (h2-compression-lookup-by-value
                      (1- n) context opened template choices
                      key name data old-lookup header header-view header-law
                      key-type typed alist lower within))
               (library (h2-compression-lookup-operation context :library nil)))
            (let ((base (library-library-proof library)))
              (h2-compression-lookup-check
                  ((reversed (proof-proof-symmetric base equality))
                   (step (proof-proof-rewrite-result base step reversed template *proof-result*)))
                (cons step context)))))))
     (t
      (h2-compression-lookup-with-calls
          ((step (h2-compression-lookup-within-array-lookup-leaf-run
                  value choices context key name data old-lookup header header-view
                  header-law key-type typed alist lower within (caddr template))))
        (h2-compression-lookup-check
            ((first (proof-step-first step))
             (target (proof-subst template (list (cons *proof-result* value)))))
          (if (equal first target)
              (cons step context)
            (cons '(:failure "failure" "") context))))))))

(defun h2-compression-lookup-within-array-lookup-run
    (context goal natural typed alist within)
  (h2-compression-lookup-check
      ((equality (h2-compression-lookup-arguments goal 2))
       (lookup (car equality))
       (target (cadr equality))
       (lookup-parts (h2-compression-lookup-arguments lookup 2))
       (key (car lookup-parts))
       (compression (cadr lookup-parts))
       (array-parts (h2-compression-lookup-arguments compression 2))
       (name (car array-parts))
       (data (cadr array-parts))
       (old-lookup (h2-compression-lookup-assoc key data)))
    (h2-compression-lookup-with-calls
        ((library (h2-compression-lookup-operation context :library nil)))
      (h2-compression-lookup-check
          ((key-type (library-library-cite library "NATURAL-INTEGER" (list key) (list natural)))
           (lower (library-library-cite library "NATURAL-NONNEGATIVE" (list key) (list natural))))
        (h2-compression-lookup-with-calls
            ((header-law (h2-compression-lookup-header-independent-lookup-run context))
             (library (h2-compression-lookup-operation context :library nil)))
          (h2-compression-lookup-check
              ((opening (h2-book-logic-logical-equation library compression))
               (header (list *h2-compression-header* name data))
               (header-view (h2-book-logic-logical-equation library header))
               (template (proof-eq (h2-compression-lookup-assoc key *proof-result*) target))
               (body (h2-compression-lookup-step-at opening 2)))
            (h2-compression-lookup-with-calls
                ((found (h2-compression-lookup-by-value
                         1000000 context body template nil
                         key name data old-lookup header header-view header-law
                         key-type typed alist lower within))
                 (library (h2-compression-lookup-operation context :library nil)))
              (let ((base (library-library-proof library)))
                (h2-compression-lookup-check
                    ((reversed (proof-proof-symmetric base opening))
                     (step (proof-proof-rewrite base found reversed '(1 1 2))))
                  (cons step context))))))))))

(defun h2-compression-lookup-other-bound
    (library rest name data)
  (let ((base (library-library-proof library)))
    (proof-with-checked-results
        ((original-name (h2-compression-lookup-step-at rest 1))
         (preservation (proof-proof-fact
                        base (proof-sym "ARRAY1P-OF-COMPRESS1" "ACL2")
                        (list (list (proof-sym "ARRAY-NAME" "ACL2") original-name)
                              (list (proof-sym "ARRAY-NAME2" "ACL2") name)
                              (list *h2-compression-data* data))))
         (compressed (proof-proof-modus-ponens base preservation rest))
         (bounds (h2-compression-lookup-array-bounds library compressed name))
         (size (proof-proof-fact
                base (proof-sym "DIMENSIONS-OF-COMPRESS1" "ACL2")
                (list (list (proof-sym "ARRAY-NAME" "ACL2") name)
                      (list (proof-sym "ARRAY-NAME2" "ACL2") name)
                      (list (proof-cl "ARRAY") data)))))
      (proof-proof-rewrite base (caddr bounds) size '(1 2 1)))))

(defun h2-compression-lookup-unbounded-theorem
    (context library formula goal natural rest key name data)
  (let ((base (library-library-proof library)))
    (h2-compression-lookup-check
        ((bounds (h2-compression-lookup-array-bounds library rest name))
         (typed (cadr bounds))
         (limit (h2-compression-lookup-step-at typed 1))
         (test (library-lt key limit))
         (within (proof-proof-assume base test t))
         (outside (proof-proof-assume base test nil)))
      (h2-compression-lookup-with-calls
          ((good (h2-compression-lookup-within-array-lookup-run
                  context goal natural typed (car bounds) within))
           (library (h2-compression-lookup-operation context :library nil)))
        (h2-compression-lookup-check
            ((key-type (library-library-cite library "NATURAL-INTEGER"
                                             (list key) (list natural))))
          (h2-compression-lookup-with-calls
              ((source-absent (h2-compression-lookup-lookup-above-bound-run
                               context key-type (caddr bounds) outside))
               (library (h2-compression-lookup-operation context :library nil)))
            (h2-compression-lookup-check
                ((bound (h2-compression-lookup-other-bound library rest name data)))
              (h2-compression-lookup-with-calls
                  ((output-absent (h2-compression-lookup-lookup-above-bound-run
                                   context key-type bound outside))
                   (empty (h2-compression-lookup-derive
                           context goal "" nil (list source-absent output-absent) nil))
                   (library (h2-compression-lookup-operation context :library nil)))
                (h2-compression-lookup-check
                    ((result (proof-proof-cases (library-library-proof library)
                                                 test good empty))
                     (step (h2-search-search-introduce library formula result)))
                  (cons step context))))))))))

(defun h2-compression-lookup-bounded-theorem
    (context library formula goal natural rest)
  (let ((base (library-library-proof library)))
    (h2-compression-lookup-check
        ((conjuncts (proof-proof-conjunct base rest))
         (within (car conjuncts))
         (fields (proof-proof-conjunct base (cadr conjuncts))))
      (h2-compression-lookup-with-calls
          ((result (h2-compression-lookup-within-array-lookup-run
                    context goal natural (cadr fields) (car fields) within))
           (library (h2-compression-lookup-operation context :library nil)))
        (h2-compression-lookup-check
            ((step (h2-search-search-introduce library formula result)))
          (cons step context))))))

(defun h2-compression-lookup-compression-lookup-theorem-run (context theorem formula)
  (h2-compression-lookup-check ((parts (h2-compression-lookup-arguments formula 2)))
    (let ((guard (car parts))
          (goal (cadr parts)))
      (h2-compression-lookup-with-calls
          ((library (h2-compression-lookup-operation context :library nil)))
        (let ((base (library-library-proof library)))
          (h2-compression-lookup-check
              ((assumed (proof-proof-assume base guard t))
               (conditions (proof-proof-conjunct base assumed))
               (natural (car conditions))
               (rest (cadr conditions)))
            (h2-compression-lookup-with-calls
                ((budget (h2-compression-lookup-operation context :set-fuel '(90000))))
              (h2-compression-lookup-check
                  ((lookup (proof-term-at goal 1))
                   (lookup-parts (h2-compression-lookup-arguments lookup 2))
                   (key (car lookup-parts))
                   (compression (cadr lookup-parts))
                   (array-parts (h2-compression-lookup-arguments compression 2)))
                (if (text-ends-with theorem "WHEN-<")
                    (h2-compression-lookup-bounded-theorem
                     context library formula goal natural rest)
                  (h2-compression-lookup-unbounded-theorem
                   context library formula goal natural rest key
                   (car array-parts) (cadr array-parts)))))))))))

(defun h2-compression-lookup-rewrite-right (base step equation)
  (proof-with-checked-results
      ((right (h2-compression-lookup-step-at step 2))
       (slot (h2-compression-lookup-step-at equation 1)))
    (proof-proof-rewrite-result base step equation (proof-eq *proof-false* right) slot)))

(defun h2-compression-lookup-aref-outside
    (context library formula unchanged right-view conditional array name key-type default)
  (let ((base (library-library-proof library)))
    (h2-compression-lookup-check
        ((test (proof-term-at conditional 1))
         (inside (proof-proof-assume base test t))
         (outside (proof-proof-assume base test nil))
         (selected (proof-proof-select base conditional inside))
         (reversed (proof-proof-symmetric base selected))
         (good (proof-proof-chain base unchanged (list reversed)))
         (bounds (h2-compression-lookup-array-bounds library array name))
         (length-term (proof-term-at test 2))
         (length-view (h2-book-logic-logical-equation library length-term))
         (out-of-bounds (proof-proof-rewrite base outside length-view '(1 1 2))))
      (h2-compression-lookup-with-calls
          ((absent (h2-compression-lookup-lookup-above-bound-run
                    context key-type (caddr bounds) out-of-bounds))
           (library (h2-compression-lookup-operation context :library nil)))
        (let ((base (library-library-proof library)))
          (h2-compression-lookup-check
              ((value (proof-proof-rewrite base right-view absent '(1 2 1)))
               (right (h2-compression-lookup-step-at value 2))
               (yes (proof-term-at right 2))
               (if-nil (proof-proof-fact base "if-nil"
                                        (list (list *library-y* yes)
                                              (list *library-z* default))))
               (value (proof-proof-chain base value (list if-nil)))
               (selected (proof-proof-select base conditional outside))
               (reversed (proof-proof-symmetric base selected))
               (empty (proof-proof-chain base unchanged (list value reversed)))
               (cases (proof-proof-cases base test good empty))
               (step (h2-search-search-introduce library formula cases)))
            (cons step context)))))))

(defun h2-compression-lookup-aref-view (base law name table key key-type)
  (proof-with-checked-results
      ((fact (proof-proof-fact base law
                               (list (list *h2-compression-name* name)
                                     (list *h2-compression-data* table)
                                     (list *h2-compression-lookup-key* key)))))
    (proof-proof-modus-ponens base fact key-type)))

(defun h2-compression-lookup-aref-same
    (context formula lookup defaults array name compression key data key-type conditional default)
  (h2-compression-lookup-with-calls
      ((law-name (h2-compression-lookup-aref-integer-view-run context))
       (library (h2-compression-lookup-operation context :library nil)))
    (let ((base (library-library-proof library))
          (law (proof-sym law-name "ACL2")))
      (h2-compression-lookup-check
          ((left-view (h2-compression-lookup-aref-view base law name compression key key-type))
           (right-view (h2-compression-lookup-aref-view base law name data key key-type))
           (left-view (h2-compression-lookup-rewrite-right base left-view defaults))
           (left-view (h2-compression-lookup-rewrite-right base left-view lookup))
           (left (h2-compression-lookup-step-at left-view 2))
           (right (h2-compression-lookup-step-at right-view 2)))
        (let ((entry (h2-compression-lookup-assoc key data)))
          (h2-compression-lookup-with-calls
              ((same (h2-compression-lookup-with-folded (list entry)
                       (h2-compression-lookup-derive
                        context (proof-eq left right) "" nil nil (list entry))))
               (library (h2-compression-lookup-operation context :library nil)))
            (let ((base (library-library-proof library)))
              (h2-compression-lookup-check
                  ((reversed (proof-proof-symmetric base right-view))
                   (unchanged (proof-proof-chain base left-view (list same reversed))))
                (h2-compression-lookup-aref-outside
                 context library formula unchanged right-view conditional
                 array name key-type default)))))))))

(defun h2-compression-lookup-aref-defaults
    (context library formula lookup array name compression comp-name
             key data key-type conditional default)
  (h2-compression-lookup-with-calls
      ((hint (h2-compression-lookup-derive
              context (proof-eq (list *h2-compression-default* comp-name data) default)
              "DEFAULT HEADER" nil nil nil)))
    (let ((base (library-library-proof library)))
      (h2-compression-lookup-check
          ((lookup (h2-compression-lookup-rewrite-right base lookup hint))
           (header-rule (proof-proof-fact
                         base (proof-sym "HEADER-OF-COMPRESS1" "ACL2")
                         (list (list (proof-sym "ARRAY-NAME" "ACL2") name)
                               (list (proof-sym "ARRAY-NAME2" "ACL2") comp-name)
                               (list (proof-cl "ARRAY") data))))
           (def-view (h2-book-logic-logical-equation
                      library (list *h2-compression-default* name compression)))
           (def-view (h2-compression-lookup-rewrite-right base def-view header-rule))
           (default-view (h2-book-logic-logical-equation library default))
           (reversed (proof-proof-symmetric base default-view))
           (defaults (proof-proof-chain base def-view (list reversed))))
        (h2-compression-lookup-aref-same
         context formula lookup defaults array name compression key data key-type
         conditional default)))))

(defun h2-compression-lookup-aref-source
    (context library formula natural array name compression comp-name
             key data key-type conditional default)
  (let ((base (library-library-proof library)))
    (h2-compression-lookup-check
        ((original (proof-step-first array))
         (opening (h2-book-logic-logical-equation library original))
         (original-array (proof-proof-rewrite base array opening '(1)))
         (parts (proof-proof-conjunct base original-array))
         (contents (cadr parts))
         (fake (proof-quote (proof-sym "FAKE-NAME" "KEYWORD")))
         (fake-view (h2-book-logic-logical-equation
                     library (list *h2-compression-lookup-array1p* fake data)))
         (fake-predicate (h2-compression-lookup-step-at fake-view 2))
         (name-type (proof-term-at fake-predicate 1)))
      (h2-compression-lookup-with-calls
          ((fake-type (h2-compression-lookup-derive context name-type "" nil nil nil))
           (library (h2-compression-lookup-operation context :library nil)))
        (let ((base (library-library-proof library)))
          (h2-compression-lookup-check
              ((fake-proof (proof-proof-prove base fake-predicate (list fake-type contents) nil))
               (fake-array (proof-proof-transport base fake-proof fake-view))
               (lookup-rule
                (proof-proof-fact base (proof-sym "ASSOC-EQUAL-OF-COMPRESS1" "ACL2")
                                  (list (list *h2-compression-lookup-key* key)
                                        (list *h2-compression-name* comp-name)
                                        (list *h2-compression-data* data))))
               (premise (h2-compression-lookup-step-at lookup-rule 1))
               (guard (proof-proof-prove base premise (list natural fake-array) nil))
               (lookup (proof-proof-modus-ponens base lookup-rule guard)))
            (h2-compression-lookup-aref-defaults
             context library formula lookup array name compression comp-name
             key data key-type conditional default)))))))

(defun h2-compression-lookup-compressed-aref-run (context formula)
  (h2-compression-lookup-check ((parts (h2-compression-lookup-arguments formula 2)))
    (h2-compression-lookup-with-calls
        ((library (h2-compression-lookup-operation context :library nil)))
      (let ((base (library-library-proof library)))
        (h2-compression-lookup-check
            ((guard (proof-proof-assume base (car parts) t))
             (conditions (proof-proof-conjunct base guard))
             (natural (car conditions))
             (array (cadr conditions))
             (goal (h2-compression-lookup-arguments (cadr parts) 2))
             (call (h2-compression-lookup-arguments (car goal) 3))
             (name (car call))
             (compression (cadr call))
             (key (caddr call))
             (array-parts (h2-compression-lookup-arguments compression 2))
             (conditional (cadr goal))
             (default (proof-term-at conditional 3))
             (key-type (library-library-cite library "NATURAL-INTEGER"
                                              (list key) (list natural))))
          (h2-compression-lookup-with-calls
              ((budget (h2-compression-lookup-operation context :set-fuel '(90000))))
            (h2-compression-lookup-aref-source
             context library formula natural array name compression (car array-parts)
             key (cadr array-parts) key-type conditional default)))))))

(defun h2-compression-lookup-output (result keep-unproved)
  (if (h2-compression-lookup-request-p result)
      result
    (let ((value (car result)))
      (if (and (failure-p value)
               (not (and keep-unproved (equal (cadr value) "Unproved"))))
          value
        (cons value (cadr result))))))

(defmacro h2-compression-lookup-expose (name run args)
  `(defun ,name (proof ,@args)
     (h2-compression-lookup-output (,run (list proof) ,@args) nil)))

(h2-compression-lookup-expose h2-compression-lookup-specialize-view
  h2-compression-lookup-specialize-view-run (key entry rest index evidence))

(h2-compression-lookup-expose h2-compression-lookup-revappend-view
  h2-compression-lookup-revappend-view-run (first second result))

(h2-compression-lookup-expose h2-compression-lookup-lookup-on-loop
  h2-compression-lookup-lookup-on-loop-run (backwards))

(h2-compression-lookup-expose h2-compression-lookup-lookup-above-bound
  h2-compression-lookup-lookup-above-bound-run (key-type bounded outside))

(h2-compression-lookup-expose h2-compression-lookup-header-independent-lookup
  h2-compression-lookup-header-independent-lookup-run ())

(h2-compression-lookup-expose h2-compression-lookup-within-array-lookup
  h2-compression-lookup-within-array-lookup-run (goal natural typed alist within))

(defun h2-compression-lookup-within-array-lookup-leaf
    (value choices proof key name data old-lookup header header-view
           header-law key-type typed alist lower within target)
  (h2-compression-lookup-output
   (h2-compression-lookup-within-array-lookup-leaf-run
    value choices (list proof) key name data old-lookup header header-view
    header-law key-type typed alist lower within target)
   nil))

(h2-compression-lookup-expose h2-compression-lookup-compression-lookup-theorem
  h2-compression-lookup-compression-lookup-theorem-run (theorem formula))

(h2-compression-lookup-expose h2-compression-lookup-aref-integer-view
  h2-compression-lookup-aref-integer-view-run ())

(h2-compression-lookup-expose h2-compression-lookup-compressed-aref
  h2-compression-lookup-compressed-aref-run (formula))

(defund h2-compression-lookup-call-with-replies (proof operation args replies)
  (let ((context (cons proof replies)))
    (h2-compression-lookup-output
     (case operation
       (:specialize-view
        (h2-compression-lookup-specialize-view-run
         context (car args) (cadr args) (caddr args) (cadddr args) (nth 4 args)))
       (:revappend-view
        (h2-compression-lookup-revappend-view-run context (car args) (cadr args) (caddr args)))
       (:lookup-on-loop (h2-compression-lookup-lookup-on-loop-run context (car args)))
       (:lookup-above-bound
        (h2-compression-lookup-lookup-above-bound-run context (car args) (cadr args) (caddr args)))
       (:header-independent-lookup (h2-compression-lookup-header-independent-lookup-run context))
       (:within-array-lookup
        (h2-compression-lookup-within-array-lookup-run
         context (car args) (cadr args) (caddr args) (cadddr args) (nth 4 args)))
       (:within-array-lookup-leaf
        (h2-compression-lookup-within-array-lookup-leaf-run
         (car args) (cadr args) context (caddr args) (cadddr args)
         (nth 4 args) (nth 5 args) (nth 6 args) (nth 7 args) (nth 8 args)
         (nth 9 args) (nth 10 args) (nth 11 args) (nth 12 args) (nth 13 args)
         (nth 14 args)))
       (:compression-lookup-theorem
        (h2-compression-lookup-compression-lookup-theorem-run context (car args) (cadr args)))
       (:aref-integer-view (h2-compression-lookup-aref-integer-view-run context))
       (:compressed-aref (h2-compression-lookup-compressed-aref-run context (car args)))
       (otherwise (cons '(:failure "failure" "") context)))
     t)))

(defun h2-compression-lookup-search-call (search recipe args)
  (case recipe
    (:compression-lookup-assoc-returned-key
     (h2-book-logic-assoc-returned-key search))
    (:compression-lookup-range-decrease
     (h2-compression-range-decrease search (car args) (cadr args) (caddr args)))
    (:compression-lookup-list-parts
     (h2-compression-recognizer-call 1000000 search :list-parts (car args) nil nil))
    (:compression-lookup-lookup-singleton
     (h2-compression-recognizer-call
      1000000 search :lookup-singleton (car args) (cadr args) nil))
    (:compression-lookup-compression-laws
     (h2-compression-compression-laws search (car args)))
    (otherwise '(:failure "failure" ""))))
