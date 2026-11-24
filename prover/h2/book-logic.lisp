(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h2-book-logic-proof (search)
  (if (eq (car search) :proof)
      search
    (library-library-proof (h2-search-search-library search))))

(defun h2-book-logic-first-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h2-book-logic-stop-p (value)
  (or (failure-p value) (h2-search-request-p value) (eq (car value) :call)))

(defun h2-book-logic-search-call (search method args)
  (let ((result (h2-search-search-call-with-outcome search method args)))
    (if (h2-search-request-p result) (cons result search) result)))

(defun h2-book-logic-saved-result (search)
  (let* ((replies (h2-search-search-replies search))
         (event (car (h2-search-reply-pending replies))))
    (and (h2-search-transcript-p replies)
         (eq (car event) :h2-book-logic-completed)
         (cons (cadr event)
               (h2-search-search-with-replies (caddr event)
                                              (h2-search-reply-rest replies))))))

(defun h2-book-logic-enter-result (search replies)
  (if (h2-search-transcript-p replies)
      (h2-search-search-with-replies
       search (h2-search-transcript-record :h2-book-logic-enter replies))
    search))

; Replace the consumed events of a completed call with its result.
(defun h2-book-logic-save-result (result before)
  (if (or (not (h2-search-transcript-p before))
          (h2-search-request-p (car result))
          (eq (caar result) :call))
      result
    (let* ((search (cdr result))
           (remaining (h2-search-reply-pending (h2-search-search-replies search)))
           (event (list :h2-book-logic-completed (car result)
                        (h2-search-search-with-replies search nil))))
      (cons (car result)
            (h2-search-search-with-replies
             search (h2-search-reply-transcript remaining (cons event (cddr before))))))))

(defmacro h2-book-logic-with-saved-result (search body)
  `(let ((h2-book-logic-saved (h2-book-logic-saved-result ,search)))
     (if h2-book-logic-saved
         h2-book-logic-saved
       (let* ((h2-book-logic-before (h2-search-search-replies ,search))
              (,search (h2-book-logic-enter-result ,search h2-book-logic-before)))
         (h2-book-logic-save-result ,body h2-book-logic-before)))))

(defmacro h2-book-logic-with-saved-search (search body)
  `(let ((h2-book-logic-result
          (h2-book-logic-with-saved-result ,search
            (let ((h2-book-logic-next ,body))
              (if (failure-p h2-book-logic-next)
                  (cons h2-book-logic-next ,search)
                (cons nil h2-book-logic-next))))))
     (or (car h2-book-logic-result) (cdr h2-book-logic-result))))

(defmacro h2-book-logic-with-results (search bindings result)
  (if (endp bindings)
      result
    (let* ((binding (car bindings))
           (names (car binding)))
      `(let ((h2-book-logic-current-result ,(cadr binding)))
         (if (h2-book-logic-stop-p h2-book-logic-current-result)
             (cons h2-book-logic-current-result ,search)
           ,(if (consp names)
                `(if (h2-book-logic-stop-p (car h2-book-logic-current-result))
                     h2-book-logic-current-result
                   (let ((,(car names) (car h2-book-logic-current-result))
                         (,(cadr names) (cdr h2-book-logic-current-result)))
                     (h2-book-logic-with-results ,search ,(cdr bindings) ,result)))
              `(let ((,names h2-book-logic-current-result))
                 (h2-book-logic-with-results ,search ,(cdr bindings) ,result))))))))

(defun h2-book-logic-has-fact (search name)
  (if (assoc-equal (proof-sym name "ACL2")
                   (proof-proof-facts (h2-book-logic-proof search)))
      t
    nil))

(defun h2-book-logic-add-lemma (search name claim step conditions)
  (let ((result
         (h2-book-logic-with-saved-result search
           (let ((library (library-library-lemma (h2-search-search-library search)
                                                 name claim step conditions)))
             (if (failure-p library)
                 (cons library search)
               (cons nil (h2-search-search-with-library search library)))))))
    (or (car result) (cdr result))))

(defun h2-book-logic-definition-names (definitions names)
  (if (endp definitions)
      names
    (let ((symbol (caar definitions)))
      (proof-with-checked-results ((name (proof-term-at symbol 2)))
        (h2-book-logic-definition-names
         (cdr definitions) (table-put names name symbol))))))

(defun h2-book-logic-resolve-names (wanted names)
  (if (endp wanted)
      nil
    (let ((entry (assoc-equal (car wanted) names)))
      (if (not entry)
          '(:failure "TacticInapplicable" "")
        (proof-with-checked-results
            ((rest (h2-book-logic-resolve-names (cdr wanted) names)))
          (cons (cdr entry) rest))))))

(defun h2-book-logic-set-rules-with-names
    (search names definitions facts repeat split-limit)
  (h2-book-logic-with-saved-search search
    (proof-with-checked-results
        ((opened (h2-book-logic-resolve-names (text-split definitions :none) names))
         (repeated (h2-book-logic-resolve-names (text-split repeat :none) names)))
      (h2-search-search-configure
       search opened (list* "built-in-clause-3" "SELF-H2-COUNT-CDDR-LESS" facts)
       repeated split-limit))))

;; The names of the definitions for h2-book-logic-resolve-names, which reads
;; them with assoc-equal. Each name goes to the front of the list, so the
;; symbol found for a name is that of its latest definition, as it is in the
;; table of h2-book-logic-definition-names, and no name walks the list.
(defun h2-book-logic-definition-names-latest-first (definitions names)
  (if (endp definitions)
      names
    (let ((symbol (caar definitions)))
      (proof-with-checked-results ((name (proof-term-at symbol 2)))
        (h2-book-logic-definition-names-latest-first
         (cdr definitions) (cons (cons name symbol) names))))))

(defun h2-book-logic-set-rules (search definitions facts repeat split-limit)
  (h2-book-logic-with-saved-search search
    (proof-with-checked-results
        ((names (h2-book-logic-definition-names-latest-first
                 (proof-proof-definitions (h2-book-logic-proof search)) nil)))
      (h2-book-logic-set-rules-with-names search names definitions facts repeat split-limit))))

(defun h2-book-logic-derive
    (search formula definitions facts variable depth repeat seeds cases split-limit)
  (h2-book-logic-with-results search
      ((search (h2-book-logic-set-rules search definitions facts repeat split-limit)))
    (if (and variable (not (equal variable "")))
        (h2-book-logic-search-call search :list-induction
                                   (list formula (proof-sym variable "ACL2") nil depth))
      (h2-book-logic-search-call search :solve (list formula seeds cases)))))

(defun h2-book-logic-auxiliary
    (search name formula definitions facts variable depth repeat seeds cases split-limit)
  (h2-book-logic-with-saved-result search
    (let ((label (concatenate 'string "SELF-H2-" name)))
      (if (h2-book-logic-has-fact search label)
          (cons label search)
        (h2-book-logic-with-results search
            (((step search) (h2-book-logic-derive search formula definitions facts variable
                                                 depth repeat seeds cases split-limit))
             (search (h2-book-logic-add-lemma search (concatenate 'string "H2-" name)
                                             formula step nil)))
          (cons label search))))))

(defun h2-book-logic-select-body (search opening evidence)
  (let ((proof (h2-book-logic-proof search)))
    (proof-with-checked-results
        ((body (h2-book-logic-first-at opening 2))
         (selected (proof-proof-select proof body evidence)))
      (proof-proof-chain proof opening (list selected)))))

(defun h2-book-logic-logical-equation (search term)
  (let ((proof (h2-book-logic-proof search)))
    (proof-with-checked-results
        ((opening (proof-proof-unfold proof term))
         (body (h2-book-logic-first-at opening 2))
         (direct (h2-search-search-remove-wrappers search body)))
      (proof-proof-chain proof opening (list direct)))))

(defun h2-book-logic-zip-bindings (variables values bindings)
  (if (or (endp variables) (endp values))
      bindings
    (h2-book-logic-zip-bindings
     (cdr variables) (cdr values)
     (table-put bindings (car variables) (car values)))))

(defun h2-book-logic-choice-projections (bound index call bindings)
  (if (endp bound)
      bindings
    (h2-book-logic-choice-projections
     (cdr bound) (1+ index) call
     (table-put bindings (car bound)
                  (list (proof-sym "MV-NTH" "ACL2") (proof-quote index) call)))))

(defun h2-book-logic-choice-axiom-witnesses (call bound)
  (if (and (consp bound) (endp (cdr bound)))
      (list (cons (car bound) call))
    (h2-book-logic-choice-projections bound 0 call nil)))

(defun h2-book-logic-choice-axiom (data)
  (proof-with-checked-results ((data (proof-list-of-length data 5)))
    (let* ((name (car data))
           (bound (cadr data))
           (free (if (equal (caddr data) *proof-nil*) nil (caddr data)))
           (body (cadddr data))
           (other (fifth data))
           (call (cons name free))
           (chosen (h2-book-logic-choice-axiom-witnesses call bound)))
      (proof-with-checked-results ((body-chosen (proof-subst body chosen)))
        (let* ((implication (list *library-implies* body body-chosen))
               (basic (if (equal (len bound) 1)
                          implication
                        (proof-ite (list (proof-sym "TRUE-LISTP" "ACL2") call)
                                   implication *proof-false*))))
          (if (equal other *proof-nil*)
              basic
            (let* ((other-call (cons name other))
                   (other-chosen (h2-book-logic-choice-axiom-witnesses other-call bound)))
              (proof-with-checked-results
                  ((other-body (proof-subst body (h2-book-logic-zip-bindings free other nil)))
                   (other-via-chosen (proof-subst other-body chosen))
                   (other-via-other (proof-subst other-body other-chosen))
                   (body-via-other (proof-subst body other-chosen)))
                (let* ((equal-values (proof-eq call other-call))
                       (first-only (proof-ite body-chosen (proof-neg other-via-chosen)
                                              *proof-false*))
                       (second-only (proof-ite other-via-other (proof-neg body-via-other)
                                               *proof-false*)))
                  (proof-ite basic
                             (proof-ite equal-values equal-values
                                        (proof-ite first-only first-only second-only))
                             *proof-false*))))))))))

(defun h2-book-logic-cons-implies-truth (search)
  (let* ((proof (h2-book-logic-proof search))
         (consp-x (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((cons-step (proof-proof-assume proof consp-x t)))
      (let* ((derived (h2-book-logic-derive
                       search (proof-neg (list *proof-consp* *proof-false*))
                       "" nil nil 1 "" nil nil 80))
             (empty (car derived))
             (search (cdr derived))
             (library (h2-search-search-library search)))
        (if (or (failure-p empty) (h2-search-request-p empty))
            empty
          (proof-with-checked-results
              ((unequal (h2-alists-distinguish library
                                               (proof-eq *library-x* *proof-false*)
                                               cons-step empty))
               (either (proof-proof-nil-or-true proof *library-x*))
               (step (proof-proof-cut proof either unequal))
               (condition (proof-step-first cons-step)))
            (h2-book-logic-add-lemma search "H2-CONSP-NONNIL" *library-x* step
                                     (list (proof-neg condition)))))))))

(defun h2-book-logic-nonnil-cons (search)
  (let ((name "SELF-H2-CONS-NONNIL"))
    (if (h2-book-logic-has-fact search name)
        (cons name search)
      (let* ((library (h2-search-search-library search))
             (proof (library-library-proof library))
             (cell (list *proof-cons* *library-x* *library-y*))
             (result
              (proof-with-checked-results
                  ((shape (proof-proof-fact proof "consp-cons" nil))
                   (step (library-library-cite library "H2-CONSP-NONNIL" (list cell) (list shape))))
                (h2-book-logic-add-lemma search "H2-CONS-NONNIL" cell step nil))))
        (if (failure-p result)
            (cons result search)
          (cons name result))))))

(defun h2-book-logic-assoc-returned-key (search)
  (let* ((assoc-term (list (proof-sym "ASSOC-EQUAL" "ACL2") *library-x* *library-y*))
         (goal (proof-eq (list *library-car* assoc-term)
                         (proof-ite assoc-term *library-x* *proof-false*)))
         (nonnil (h2-book-logic-nonnil-cons search)))
    (if (failure-p (car nonnil))
        nonnil
      (h2-book-logic-auxiliary (cdr nonnil) "ASSOC-RETURNED-KEY" goal "ASSOC-EQUAL"
                               (list (car nonnil)) "Y" 1 "" nil nil 80))))

(defun h2-book-logic-nil-test (search)
  (let* ((proof (h2-book-logic-proof search))
         (test (proof-eq *library-x* *proof-false*)))
    (proof-with-checked-results
        ((present (proof-proof-assume proof *library-x* t))
         (absent (proof-proof-assume proof *library-x* nil))
         (opening (proof-proof-unfold proof (proof-neg *library-x*)))
         (test-evidence (proof-proof-assume proof test t))
         (contradiction (proof-proof-rewrite proof present test-evidence '(1)))
         (contradiction (proof-proof-tidy proof contradiction))
         (unequal (proof-proof-front proof contradiction (proof-neg test)))
         (different (proof-proof-fact proof "equal-different"
                                      (list (list *library-x* *library-x*)
                                            (list *library-y* *proof-false*))))
         (different (proof-proof-front proof different (proof-eq test *proof-false*)))
         (negative (proof-proof-discharge proof different unequal))
         (not-present (h2-book-logic-select-body search opening present))
         (not-present (proof-proof-symmetric proof not-present))
         (yes (proof-proof-chain proof negative (list not-present)))
         (same (proof-proof-reflexive proof test))
         (nil-value (h2-search-search-nil-value search absent))
         (same (proof-proof-rewrite proof same nil-value '(1 2 1)))
         (right (h2-book-logic-first-at same 2))
         (constant (proof-proof-constant proof right))
         (positive (proof-proof-chain proof same (list constant)))
         (not-absent (h2-book-logic-select-body search opening absent))
         (not-absent (proof-proof-symmetric proof not-absent))
         (no (proof-proof-chain proof positive (list not-absent)))
         (step (proof-proof-cases proof *library-x* yes no)))
      (h2-book-logic-add-lemma search "H2-EQUAL-NIL"
                               (proof-eq test (proof-neg *library-x*)) step nil))))

(defun h2-book-logic-true-boolean (search)
  (let* ((proof (h2-book-logic-proof search))
         (typed (list (proof-sym "BOOLEANP" "ACL2") *library-x*))
         (claim (proof-eq *library-x* *proof-true*)))
    (proof-with-checked-results
        ((typed-step (proof-proof-assume proof typed t))
         (typed-opening (proof-proof-unfold proof typed))
         (opened (proof-proof-rewrite proof typed-step typed-opening '(1)))
         (true-eq (proof-proof-unfold proof (list (proof-cl "EQ") *library-x* *proof-true*)))
         (opened (proof-proof-rewrite proof opened true-eq '(1 1)))
         (false-eq (proof-proof-unfold proof (list (proof-cl "EQ") *library-x* *proof-false*)))
         (opened (proof-proof-rewrite proof opened false-eq '(1 3)))
         (not-true (proof-proof-assume proof claim nil))
         (empty (proof-proof-prove-if proof opened not-true))
         (present (proof-proof-assume proof *library-x* t))
         (conflict (proof-proof-rewrite proof present empty '(1)))
         (conflict (proof-proof-tidy proof conflict))
         (step (proof-proof-front proof conflict claim)))
      (h2-book-logic-add-lemma search "H2-TRUE-BOOLEAN" claim step
                               (list (proof-neg *library-x*) (proof-neg typed))))))
