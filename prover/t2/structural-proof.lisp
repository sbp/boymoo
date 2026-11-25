(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t2-structural-proof-aliases*
  (list *termination-return-last* (proof-cl "ATOM") (proof-cl "ENDP")
        (proof-cl "EQ") (proof-cl "EQL") (proof-cl "LISTP") *proof-not*
        (proof-cl "NULL")))

(defun t2-structural-proof-reduction-make (lib expand facts equalities budget)
  (list :t2-structural-proof-reduction lib expand facts equalities budget))

(defun t2-structural-proof-reduction-lib (reduction)
  (cadr reduction))

(defun t2-structural-proof-reduction-expand (reduction)
  (caddr reduction))

(defun t2-structural-proof-reduction-facts (reduction)
  (cadddr reduction))

(defun t2-structural-proof-reduction-equalities (reduction)
  (nth 4 reduction))

(defun t2-structural-proof-reduction-budget (reduction)
  (nth 5 reduction))

(defun t2-structural-proof-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun t2-structural-proof-learn-premises (facts premises)
  (declare (xargs :measure (acl2-count premises)))
  (if (endp premises)
      facts
    (proof-with-checked-results
        ((next (t2-tactics-ruler-facts-learn facts (car premises))))
      (t2-structural-proof-learn-premises next (cdr premises)))))

(defun t2-structural-proof-equation-map (equations equalities)
  (declare (xargs :measure (acl2-count equations)))
  (if (endp equations)
      equalities
    (let ((step (car equations)))
      (proof-with-checked-results
          ((left (t2-structural-proof-step-at step 1))
           (right (t2-structural-proof-step-at step 2)))
        (t2-structural-proof-equation-map
         (cdr equations)
         (if (equal left right) equalities (table-put equalities left step)))))))

(defun t2-structural-proof-reduction-init (lib expand tests premises equations)
  (proof-with-checked-results
      ((facts (t2-tactics-ruler-facts-init lib tests nil))
       (derived (t2-tactics-ruler-facts-premises facts))
       (facts (t2-structural-proof-learn-premises (cdr derived) premises))
       (equalities (t2-structural-proof-equation-map equations nil)))
    (t2-structural-proof-reduction-make lib expand facts equalities 24000)))

(defun t2-structural-proof-expansion-argument (term index)
  (let ((index (if (< index 0) (+ (len term) index) index)))
    (if (< index 0)
        '(:failure "missing-term-part" "")
      (proof-term-at term index))))

(defun t2-structural-proof-expansion-rule (rule term operator)
  (case (car rule)
    (:term (equal (cadr rule) term))
    (:head (equal (cadr rule) operator))
    (:arg (and (equal (cadr rule) operator)
               (proof-with-checked-results
                   ((argument (t2-structural-proof-expansion-argument term (caddr rule))))
                 (equal argument (cadddr rule)))))
    (:constructed
     (and (equal (cadr rule) operator)
          (proof-with-checked-results
              ((argument (t2-structural-proof-expansion-argument term (caddr rule))))
            (or (equal argument *proof-false*) (proof-is-call argument *proof-cons*)))))
    (:reply (equal (cadr rule) term))
    (:any t)
    (otherwise nil)))

(defun t2-structural-proof-expansion-test (rules term operator)
  (if (endp rules)
      nil
    (let ((rule (car rules)))
      (proof-with-checked-results
          ((matched (t2-structural-proof-expansion-rule rule term operator)))
        (if matched
            (if (eq (car rule) :reply) (caddr rule) t)
          (t2-structural-proof-expansion-test (cdr rules) term operator))))))

(defun t2-structural-proof-reduction-can-open (reduction term opened)
  (declare (ignore opened))
  (let ((operator (t2-book-logic-head term)))
    (if (member-equal operator *t2-structural-proof-aliases*)
        t
      (t2-structural-proof-expansion-test
       (t2-structural-proof-reduction-expand reduction) term operator))))

(defun t2-structural-proof-unopened-equality (term opened equalities)
  (if (member-equal term opened)
      nil
    (table-get equalities term nil)))

(defun t2-structural-proof-update-context-library (context original lib)
  (if (and (not (equal original lib))
           (equal original (t2-tactics-ruler-facts-proof context)))
      (t2-tactics-ruler-facts-with-proof context lib)
    context))

(defun t2-structural-proof-replacement-constructor (lib operator argument context)
  (cond
   ((not (proof-is-call argument *proof-cons*)) :base)
   ((equal operator *proof-consp*)
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((constructor (proof-proof-fact proof "consp-cons"
                                          (seq-zip (list *library-x* *library-y*) (cdr argument))))
           (boolean (proof-proof-fact proof "booleanp-consp" (list (list *library-x* argument))))
           (positive (t2-book-logic-true-boolean lib boolean constructor))
           (context (t2-structural-proof-update-context-library context lib (cdr positive))))
        (list :with-state (car positive) (cdr positive) context))))
   (t (library-library-axiom lib (if (equal operator *t2-book-logic-car*) "CAR-CONS" "CDR-CONS")
                            (cdr argument)))))

(defun t2-structural-proof-cons-index-p (tail index)
  (declare (xargs :measure (nfix index)))
  (and (proof-is-call tail *proof-cons*)
       (or (zp index)
           (proof-with-checked-results ((rest (proof-term-at tail 2)))
             (t2-structural-proof-cons-index-p rest (1- index))))))

(defun t2-structural-proof-replacement-mv-nth (lib term)
  (proof-with-checked-results ((index-term (proof-term-at term 1)))
    (if (not (proof-is-call index-term *proof-quote*))
        :base
      (proof-with-checked-results ((index (proof-term-at index-term 1)))
        (if (not (integerp index))
            :base
          (proof-with-checked-results
              ((result (proof-term-at term 2))
               (fits (and (<= 0 index) (<= index 3)
                          (t2-structural-proof-cons-index-p result index))))
            (if fits
                (t2-input-fields-cons-projection lib *t2-input-fields-mv-nth* index result)
              :base)))))))

(defun t2-structural-proof-replacement-equal (lib term context)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((right (proof-term-at term 2))
         (left (proof-term-at term 1))
         (reverse (proof-eq right left))
         (known (t2-tactics-ruler-facts-find context reverse)))
      (if (car known)
          (proof-with-checked-results
              ((symmetric (proof-proof-symmetric proof (car known)))
               (step (t2-field-true-equality lib symmetric)))
            (list :with-state step lib (cdr known)))
        (proof-with-checked-results
            ((different (t2-tactics-ruler-facts-find (cdr known) (proof-neg reverse)))
             (step (if (car different)
                       (proof-with-checked-results
                           ((forward (t2-products-flip-neq lib (car different))))
                         (t2-field-false-value lib forward))
                     :base)))
          (list :with-state step lib (cdr different)))))))

(defun t2-structural-proof-replacement-reply (lib term context opened equalities)
  (let ((operator (t2-book-logic-head term))
        (equation (t2-structural-proof-unopened-equality term opened equalities)))
    (cond
     (equation equation)
     ((member-equal operator (list *t2-book-logic-car* *t2-book-logic-cdr* *proof-consp*))
      (proof-with-checked-results ((argument (proof-term-at term 1)))
        (t2-structural-proof-replacement-constructor lib operator argument context)))
     ((equal operator *t2-input-fields-mv-nth*)
      (t2-structural-proof-replacement-mv-nth lib term))
     ((equal operator *proof-equal*)
      (t2-structural-proof-replacement-equal lib term context))
     (t :base))))

(defun t2-structural-proof-reduction-reply (reduction request)
  (let ((method (t2-book-logic-search-request-method request))
        (term (t2-book-logic-search-request-term request))
        (opened (t2-book-logic-search-request-opened request))
        (equalities (t2-structural-proof-reduction-equalities reduction)))
    (case method
      (:normalize
       (let ((equation (t2-structural-proof-unopened-equality term opened equalities)))
         (if equation
             (proof-with-checked-results ((target (t2-structural-proof-step-at equation 2)))
               (list :chain equation target (append opened (list term))))
           :base)))
      (:replacement
       (t2-structural-proof-replacement-reply (t2-book-logic-search-request-lib request)
        term (t2-book-logic-search-request-context request) opened equalities))
      (:can-open (t2-structural-proof-reduction-can-open reduction term opened))
      (otherwise :base))))

(defund t2-structural-proof-reduction-attempt (reduction search method term context depth opened replies)
  (let* ((configured (t2-book-logic-search-with-hooks search '(:normalize :replacement :can-open) replies))
         (result (if (eq method :normalize)
                     (t2-book-logic-search-normalize configured term context depth opened)
                   (t2-book-logic-search-replacement configured term context depth opened)))
         (value (car result)))
    (cond
     ((failure-p result) result)
     ((failure-p value) value)
     ((t2-book-logic-search-request-p value)
      (proof-with-checked-results ((reply (t2-structural-proof-reduction-reply reduction value)))
        (list :reply reply)))
     (t
      (let* ((ending-search (cadr result))
             (updated-context (cddr result))
             (lib (t2-book-logic-search-lib ending-search))
             (initial-lib (t2-structural-proof-reduction-lib reduction))
             (initial-facts (t2-structural-proof-reduction-facts reduction))
             (facts (if (equal initial-facts context)
                        updated-context
                      (t2-structural-proof-update-context-library initial-facts initial-lib lib))))
        (cons (list value updated-context)
              (t2-structural-proof-reduction-make
               lib (t2-structural-proof-reduction-expand reduction)
               facts (t2-structural-proof-reduction-equalities reduction)
               (t2-book-logic-search-budget ending-search))))))))

(defun t2-structural-proof-reduction-run (n reduction search method term context depth opened replies)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t2-structural-proof-reduction-run")
    (let ((result (t2-structural-proof-reduction-attempt
                   reduction search method term context depth opened replies)))
      (if (eq (car result) :reply)
          (t2-structural-proof-reduction-run
           (1- n) reduction search method term context depth opened (append replies (cdr result)))
        result))))

(defun t2-structural-proof-reduction-dispatch (reduction method term context depth opened)
  (let ((search (t2-book-logic-search-init (t2-structural-proof-reduction-lib reduction)
                                         nil nil (t2-structural-proof-reduction-budget reduction) nil)))
    (t2-structural-proof-reduction-run 1000000 reduction search method term context depth opened nil)))

(defun t2-structural-proof-reduction-normalize (reduction term context depth opened)
  (t2-structural-proof-reduction-dispatch reduction :normalize term context depth opened))

(defun t2-structural-proof-reduction-form (reduction term)
  (proof-with-checked-results
      ((result (t2-structural-proof-reduction-normalize
                reduction term (t2-structural-proof-reduction-facts reduction) -1 nil))
       (updated (cdr result))
       (step (or (caar result)
                 (t2-arithmetic-arithmetic-reflexive
                  (t2-structural-proof-reduction-lib updated) term))))
    (cons step updated)))

(defun t2-structural-proof-reduce (lib expand tests premises equations term)
  (proof-with-checked-results
      ((reduction (t2-structural-proof-reduction-init lib expand tests premises equations))
       (result (t2-structural-proof-reduction-form reduction term)))
    (cons (car result) (t2-structural-proof-reduction-lib (cdr result)))))

(defund t2-structural-proof-congruence-start (lib first second)
  (if (equal first second)
      (t2-arithmetic-arithmetic-reflexive lib first)
    (let ((operator (t2-book-logic-head first)))
      (if (or (not operator) (equal operator *proof-quote*)
              (not (equal operator (t2-book-logic-head second)))
              (not (equal (len first) (len second))))
          nil
        (proof-with-checked-results
            ((ordered (and (member-equal operator (list *proof-plus* *proof-times*))
                           (t2-book-logic-ac-equal lib first second))))
          (or ordered
              (proof-with-checked-results ((result (t2-arithmetic-arithmetic-reflexive lib first)))
                (list :arguments result))))))))

(defund t2-structural-proof-congruence-rewrite (lib result equation position)
  (cond ((not equation) nil)
        ((failure-p equation) equation)
        (t (proof-proof-rewrite (library-library-proof lib) result equation (list 1 2 position)))))

(mutual-recursion
 (defun t2-structural-proof-congruence (lib first second)
   (declare (xargs :measure (acl2-count first)))
   (let ((result (t2-structural-proof-congruence-start lib first second)))
     (if (and (consp first) (eq (car result) :arguments))
         (t2-structural-proof-congruence-arguments lib (cdr first) (cdr second) 1 (cadr result))
       result)))
 (defun t2-structural-proof-congruence-arguments (lib left right position result)
   (declare (xargs :measure (acl2-count left)))
   (cond
    ((or (endp left) (endp right)) result)
    ((equal (car left) (car right))
     (t2-structural-proof-congruence-arguments lib (cdr left) (cdr right) (1+ position) result))
    (t
     (let* ((equation (t2-structural-proof-congruence lib (car left) (car right)))
            (next (t2-structural-proof-congruence-rewrite lib result equation position)))
       (if (or (not next) (failure-p next))
           next
         (t2-structural-proof-congruence-arguments lib (cdr left) (cdr right) (1+ position) next)))))))

(defun t2-structural-proof-unproved (target)
  (proof-with-checked-results ((text (proof-write target)))
    '(:failure "unproved" "")))

(defun t2-structural-proof-align-target (lib target)
  (let ((arity (len (cdr target))))
    (case arity
      (2 (t2-structural-proof-congruence lib (cadr target) (caddr target)))
      (0 '(:failure "failure" ""))
      (1 '(:failure "failure" ""))
      (otherwise
       '(:failure "failure" "")))))

(defund t2-structural-proof-solve-case (lib goal expand tests premises equations)
  (proof-with-checked-results
      ((reduction (t2-structural-proof-reduction-init lib expand tests premises equations))
       (normal (t2-structural-proof-reduction-form reduction goal))
       (normalized (car normal))
       (reduction (cdr normal))
       (lib (t2-structural-proof-reduction-lib reduction))
       (proof (library-library-proof lib))
       (target (t2-structural-proof-step-at normalized 2)))
    (if (equal target *proof-true*)
        (proof-with-checked-results ((step (proof-proof-true-from-eq proof normalized)))
          (cons step lib))
      (proof-with-checked-results
          ((known (t2-tactics-ruler-facts-find (t2-structural-proof-reduction-facts reduction) target))
           (aligned (cond ((car known) (car known))
                          ((proof-is-call target *proof-equal*)
                           (t2-structural-proof-align-target lib target)))))
        (if aligned
            (proof-with-checked-results ((step (proof-proof-transport proof aligned normalized)))
              (cons step lib))
          (proof-with-checked-results ((test (t2-book-logic-search-first-test nil target)))
            (if (or (not test) (equal test 0) (equal test ""))
                (t2-structural-proof-unproved target)
              (list :split test target lib))))))))

(defun t2-structural-proof-solve (lib goal expand tests premises equations depth)
  (declare (xargs :measure (nfix depth)))
  (let ((result (t2-structural-proof-solve-case lib goal expand tests premises equations)))
    (if (not (eq (car result) :split))
        result
      (if (zp depth)
          (t2-structural-proof-unproved (caddr result))
        (let ((test (cadr result))
              (lib (cadddr result)))
          (proof-with-checked-results
              ((left (t2-structural-proof-solve
                      lib goal expand (append tests (list (list test t))) premises equations (1- depth)))
               (right (t2-structural-proof-solve
                       (cdr left) goal expand (append tests (list (list test nil)))
                       premises equations (1- depth)))
               (lib (cdr right))
               (step (proof-proof-cases (library-library-proof lib) test (car left) (car right))))
            (cons step lib)))))))

(defun t2-structural-proof-substitution-map (pairs bindings)
  (declare (xargs :measure (acl2-count pairs)))
  (if (endp pairs)
      bindings
    (let* ((pair (car pairs))
           (size (len pair)))
      (cond
       ((not (or (consp pair) (null pair)))
        '(:failure "failure" ""))
       ((not (equal size 2))
        '(:failure "recipe-mismatch" ""))
       (t (t2-structural-proof-substitution-map
           (cdr pairs) (table-put bindings (car pair) (cadr pair))))))))

(defun t2-structural-proof-induction-instance (lib formula descent substitutions)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((bindings (t2-structural-proof-substitution-map substitutions nil))
         (instance (proof-subst formula bindings))
         (comparison (proof-step-first descent))
         (premise (proof-proof-assume proof (proof-ite comparison instance *proof-true*) t)))
      (proof-proof-prove-if proof premise descent))))

(defun t2-structural-proof-smaller (lib formula root child tests extras bindings)
  (let ((substitutions (cons (list root child) bindings))
        (order (list *proof-ordinal-less* (list *library-count* child) (list *library-count* root))))
    (proof-with-checked-results
        ((facts (t2-tactics-ruler-facts-init lib tests extras))
         (descent (t2-guarded-selectors-context-selector-decrease lib order facts))
         (instance (t2-structural-proof-induction-instance lib formula (car descent) substitutions)))
      (list instance substitutions))))

(defun t2-structural-proof-components (lib premise tests count known)
  (proof-with-checked-results
      ((term (proof-step-first premise))
       (opened (t2-structural-proof-reduce lib (list (list :term term)) tests known nil term))
       (lib (cdr opened))
       (rewritten (proof-proof-rewrite (library-library-proof lib) premise (car opened) '(1)))
       (components (t2-power-conjuncts lib rewritten count)))
    (cons components lib)))

(defun t2-structural-proof-induct (lib formula root cases substitutions)
  (proof-with-checked-results ((ordinal (library-library-builtin lib 1 root)))
    (proof-proof-induct (library-library-proof lib) ordinal cases formula
                        (list *library-count* root) substitutions)))
