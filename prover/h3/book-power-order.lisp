(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

; A paired result carries the proof state through success or failure.
(defmacro h3-book-power-order-with-state (object bindings body)
  (if (endp bindings)
      body
    (let* ((binding (car bindings))
           (name (car binding))
           (form (cadr binding))
           (mode (caddr binding))
           (then `(h3-book-power-order-with-state ,object ,(cdr bindings) ,body)))
      (cond
       ((eq mode :pair)
        `(let ((h3-book-power-order-pair ,form))
           (if (failure-p h3-book-power-order-pair)
               (cons h3-book-power-order-pair ,object)
             (let ((,name (car h3-book-power-order-pair))
                   (,object (cdr h3-book-power-order-pair)))
               (if (failure-p ,name)
                   h3-book-power-order-pair
                 ,then)))))
       ((eq mode :state)
        `(let ((h3-book-power-order-state ,form))
           (if (failure-p h3-book-power-order-state)
               (cons h3-book-power-order-state ,object)
             (let ((,object h3-book-power-order-state))
               ,then))))
       (t
        `(let ((,name ,form))
           (if (failure-p ,name)
               (cons ,name ,object)
             ,then)))))))

(defun h3-book-power-order-bound-library (bound-result)
  (if (failure-p bound-result)
      bound-result
    (cons (car bound-result) (h3-book-order-bounds-lib (cdr bound-result)))))

(defun h3-book-power-order-truth (value)
  (cond ((rationalp value) (not (zerop value)))
        ((stringp value) (not (equal value "")))
        (t (not (or (null value) (eq value :none))))))

(defun h3-book-power-order-step-argument (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h3-book-power-order-arguments (term)
  (if (integerp term)
      '(:failure "failure" "")
    (cdr term)))

(defun h3-book-power-order-unit-bound (term growing strict)
  (let* ((growing (h3-book-power-order-truth growing))
         (low (if growing *proof-one* term))
         (high (if growing term *proof-one*)))
    (if (h3-book-power-order-truth strict)
        (library-lt low high)
      (library-le low high))))

(defun h3-book-power-order-scale-order (lib endpoints scalar signs types)
  (case (len endpoints)
    (0 '(:failure "failure" ""))
    (1 '(:failure "failure" ""))
    (2 (h3-book-quotient-scale-order-with-library lib (car endpoints) (cadr endpoints)
                                                 scalar signs types))
    (otherwise '(:failure "failure" ""))))

(defun h3-book-power-order-times-positive-with-library (lib bound scalar positive types)
  (h3-book-power-order-with-state lib
    ((numeric (h3-book-signs-number lib scalar))
     (signs (h3-book-signs-sign-evidence-with-library lib numeric 1 positive) :pair)
     (literal (proof-step-first bound))
     (weak (proof-is-call literal *proof-not*))
     (comparison (if weak (proof-term-at literal 1) literal))
     (endpoints (h3-book-power-order-arguments comparison))
     (equality (h3-book-power-order-scale-order lib endpoints scalar signs types) :pair)
     (step (proof-proof-rewrite (library-library-proof lib) bound equality
                                (if weak '(1 1) '(1)))))
    (cons step lib)))

(defun h3-book-power-order-endpoint-types (endpoints rational-one factor)
  (if (endp endpoints)
      nil
    (cons (if (equal (car endpoints) *proof-one*) rational-one factor)
          (h3-book-power-order-endpoint-types (cdr endpoints) rational-one factor))))

(defun h3-book-power-order-rewrite-scaled (proof scaled terms prefix position
                                                unit-product scalar-identity combined)
  (declare (xargs :measure (acl2-count terms)))
  (cond
   ((failure-p scaled) scaled)
   ((endp terms) (proof-proof-tidy proof scaled))
   (t
    (let* ((replacement (if (equal (car terms) unit-product) scalar-identity combined))
           (next (proof-proof-rewrite proof scaled replacement (append prefix (list position)))))
      (h3-book-power-order-rewrite-scaled proof next (cdr terms) prefix (1+ position)
                                          unit-product scalar-identity combined)))))

(defun h3-book-power-order-scaled-unit-bound-with-library
  (lib bound scalar positive factor combined)
  (h3-book-power-order-with-state lib
    ((one (library-library-axiom lib "INTEGER-1" nil))
     (rational-one (h3-book-numerator-as-rational lib one))
     (literal (proof-step-first bound))
     (weak (proof-is-call literal *proof-not*))
     (comparison (if weak (proof-term-at literal 1) literal))
     (endpoints (h3-book-power-order-arguments comparison))
     (types (h3-book-power-order-endpoint-types endpoints rational-one factor))
     (scaled (h3-book-power-order-times-positive-with-library lib bound scalar positive types) :pair)
     (s (h3-book-power-order-step-argument scalar 1))
     (identity (library-library-axiom lib "UNICITY-OF-1" (list s)))
     (numeric (h3-book-signs-number lib scalar))
     (fixed (h3-book-arithmetic-fix-value lib s numeric))
     (proof (library-library-proof lib))
     (scalar-identity (proof-proof-chain proof identity (list fixed)))
     (scaled-literal (proof-step-first scaled))
     (expression (if weak (proof-term-at scaled-literal 1) scaled-literal))
     (terms (h3-book-power-order-arguments expression))
     (step (h3-book-power-order-rewrite-scaled
            proof scaled terms (if weak '(1 1) '(1)) 1
            (list *proof-times* *proof-one* s) scalar-identity combined)))
    (cons step lib)))

(defun h3-book-power-order-advance-bound-with-library
  (lib base positive base-bound exponent exponent-positive previous previous-bound growing)
  (h3-book-power-order-with-state lib
    ((b (h3-book-power-order-step-argument base 1))
     (n (h3-book-power-order-step-argument exponent 1))
     (index (h3-book-power-order-step-argument previous 1))
     (base-data (h3-book-powers-positive-base lib base positive) :pair)
     (recurrence (h3-book-powers-predecessor-equation lib (car base-data) (cadr base-data)
                                                       exponent exponent-positive) :pair)
     (child (h3-book-powers-power b index))
     (child-type (h3-book-powers-rational-power lib base index))
     (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list child b)))
     (proof (library-library-proof lib))
     (reversed (proof-proof-symmetric proof recurrence))
     (product (proof-proof-chain proof commuted (list reversed)))
     (multiplied (h3-book-power-order-scaled-unit-bound-with-library
                  lib previous-bound base positive child-type product) :pair)
     (power-type (h3-book-powers-rational-power lib base n))
     (ordered (if (h3-book-power-order-truth growing)
                  (list base-bound multiplied) (list multiplied base-bound)))
     (context (h3-book-order-bounds-init lib (list base child-type power-type))))
    (h3-book-power-order-bound-library
     (h3-book-order-bounds-compose-with-bounds context (car ordered) (cadr ordered)))))

(defun h3-book-power-order-unit-lemma-name (growing)
  (if (h3-book-power-order-truth growing)
      "H3-BOOK-POWER-ABOVE-ONE"
    "H3-BOOK-POWER-BELOW-ONE"))

(defun h3-book-power-order-fact (facts term)
  (let ((entry (assoc-equal term facts)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun h3-book-power-order-prove-unit-bound-empty (zero lib term index growing target)
  (proof-with-checked-results
    ((at-zero (h3-book-powers-power-equation lib term *proof-one* (list index zero)))
     (proof (library-library-proof lib))
     (reflexive (proof-proof-reflexive proof target))
     (identity (proof-proof-rewrite proof reflexive at-zero
                                    (if (h3-book-power-order-truth growing)
                                        '(1 2 1 1) '(1 2 1 2))))
     (search (h3-rewrite-search-init lib nil nil nil 150 nil))
     (one-order (car (h3-rewrite-search-prove
                      search (library-le *proof-one* *proof-one*) nil))))
    (proof-proof-transport proof one-order identity)))

(defun h3-book-power-order-prove-unit-bound-advance
  (index-positive child previous lib base positive relative index growing)
  (h3-book-power-order-advance-bound-with-library
   lib base positive relative index index-positive child previous growing))

(defun h3-book-power-order-prove-unit-bound-with-library (lib growing)
  (h3-book-power-order-with-state lib
    ((registered (h3-book-sums-lemmas-with-library lib) :pair)
     (base-term (list *library-rationalp* *library-y*))
     (positive-term (library-lt *proof-zero* *library-y*))
     (relative-term (h3-book-power-order-unit-bound *library-y* growing nil))
     (index-term (list *proof-integerp* *library-x*))
     (nonnegative-term (library-le *proof-zero* *library-x*))
     (guard (h3-book-floor-conjunction
             (list base-term positive-term relative-term index-term nonnegative-term)))
     (term (h3-book-powers-power *library-y* *library-x*))
     (target (h3-book-power-order-unit-bound term growing nil))
     (formula (list *library-implies* guard target))
     (search (h3-rewrite-search-init lib nil nil nil 150 nil))
     (assumed (proof-proof-assume (library-library-proof lib) guard t))
     (facts (h3-rewrite-search-context search (list assumed)))
     (base (h3-book-power-order-fact facts base-term))
     (positive (h3-book-power-order-fact facts positive-term))
     (relative (h3-book-power-order-fact facts relative-term))
     (index (h3-book-power-order-fact facts index-term))
     (nonnegative (h3-book-power-order-fact facts nonnegative-term))
     (zero-data (h3-book-powers-natural-exponent-induction-zero lib index))
     (test (car zero-data))
     (empty (h3-book-power-order-prove-unit-bound-empty
             (cadr zero-data) lib term index growing target))
     (step-data (h3-book-powers-natural-exponent-induction-step
                 lib (list base positive relative) formula index nonnegative test) :pair)
     (nonempty (h3-book-power-order-prove-unit-bound-advance
                (car step-data) (cadr step-data) (caddr step-data)
                lib base positive relative index growing) :pair)
     (done (h3-book-powers-natural-exponent-induction
            lib formula index test (cadddr step-data) empty nonempty) :pair)
     (lib (library-library-lemma lib (h3-book-power-order-unit-lemma-name growing)
                                 formula done nil) :state))
    (cons nil lib)))

(defun h3-book-power-order-unit-bound-natural-with-library
  (lib base positive relative index nonnegative growing)
  (let* ((name (h3-book-power-order-unit-lemma-name growing))
         (key (proof-sym (concatenate 'string "SELF-" name) "ACL2"))
         (extension (if (assoc-equal key (proof-proof-facts (library-library-proof lib)))
                        (cons nil lib)
                      (h3-book-power-order-prove-unit-bound-with-library lib growing))))
    (if (failure-p (car extension))
        extension
      (let ((lib (cdr extension)))
        (h3-book-power-order-with-state lib
          ((i (h3-book-power-order-step-argument index 1))
           (b (h3-book-power-order-step-argument base 1))
           (numeric (library-library-cite lib name (list i b) nil))
           (guard (h3-book-floor-conjunct-proof lib (list base positive relative index nonnegative)))
           (step (proof-proof-modus-ponens (library-library-proof lib) numeric guard)))
          (cons step lib))))))

(defun h3-book-power-order-unit-bound-positive-with-library
  (lib base positive relative index index-positive growing)
  (h3-book-power-order-with-state lib
    ((registered (h3-book-sums-lemmas-with-library lib) :pair)
     (nonnegative (h3-book-powers-nonnegative-integer lib index index-positive))
     (child-data (h3-book-powers-decrease-index lib index nonnegative index-positive) :pair)
     (child (car child-data))
     (child-bound (cadr child-data))
     (context (h3-book-order-bounds-init lib (list base relative)))
     (b (h3-book-power-order-step-argument base 1))
     (weak (h3-book-power-order-bound-library
            (h3-book-order-bounds-bound-with-bounds
             context (h3-book-power-order-unit-bound b growing nil))) :pair)
     (previous (h3-book-power-order-unit-bound-natural-with-library
                lib base positive weak child child-bound growing) :pair))
    (h3-book-power-order-advance-bound-with-library
     lib base positive relative index index-positive child previous growing)))

(defun h3-book-power-order-power-difference-bound
  (lib base positive relative delta-integer delta exponent-bound literal strict evidence growing)
  (h3-book-power-order-with-state lib
    ((sums (h3-book-sums-book-sums-init lib))
     (comparison (if strict literal (proof-term-at literal 1)))
     (goal (if strict (library-lt *proof-zero* delta) (library-lt delta *proof-zero*)))
     (same (h3-book-sums-cancel-comparison lib sums comparison goal evidence))
     (distance (proof-proof-rewrite (library-library-proof lib) exponent-bound same
                                   (if strict '(1) '(1 1)))))
    (if strict
        (h3-book-power-order-unit-bound-positive-with-library
         lib base positive relative delta-integer distance growing)
      (h3-book-power-order-unit-bound-natural-with-library
       lib base positive relative delta-integer distance growing))))

(defun h3-book-power-order-compare-powers-with-library
  (lib base positive relative first second exponent-bound growing)
  (h3-book-power-order-with-state lib
    ((registered (h3-book-sums-lemmas-with-library lib) :pair)
     (i (h3-book-power-order-step-argument first 1))
     (j (h3-book-power-order-step-argument second 1))
     (b (h3-book-power-order-step-argument base 1))
     (delta (library-diff j i))
     (delta-integer (descent-library-type-of lib delta (list first second)) :pair)
     (literal (proof-step-first exponent-bound))
     (strict (proof-is-call literal *proof-less*))
     (evidence (list first second delta-integer))
     (bound (h3-book-power-order-power-difference-bound
             lib base positive relative delta-integer delta exponent-bound literal strict evidence growing) :pair)
     (base-data (h3-book-powers-positive-base lib base positive) :pair)
     (eq-power (h3-book-powers-power-add-integer lib (car base-data) (cadr base-data)
                                                 first delta-integer) :pair)
     (left (h3-book-power-order-step-argument eq-power 1))
     (sum (proof-term-at left 2))
     (aligned (h3-book-translation-sum-equality lib sum j evidence) :pair)
     (proof (library-library-proof lib))
     (eq-power (proof-proof-rewrite proof eq-power aligned '(1 1 2)))
     (start (h3-book-powers-power b i))
     (difference (h3-book-powers-power b delta))
     (commuted (library-library-axiom lib "COMMUTATIVITY-OF-*" (list difference start)))
     (reversed (proof-proof-symmetric proof eq-power))
     (product (proof-proof-chain proof commuted (list reversed)))
     (start-type (h3-book-powers-rational-power lib base i))
     (start-positive (h3-book-powers-positive-power lib base positive first) :pair)
     (factor (h3-book-powers-rational-power lib base delta)))
    (h3-book-power-order-scaled-unit-bound-with-library
     lib bound start-type start-positive factor product)))

(defun h3-book-power-order-pair-base (first second)
  (cond
   ((proof-is-call first *h3-book-powers-expt*)
    (cond ((equal second *proof-one*) (proof-term-at first 1))
          ((proof-is-call second *h3-book-powers-expt*)
           (proof-with-checked-results
             ((left-base (proof-term-at first 1))
              (right-base (proof-term-at second 1)))
             (if (equal left-base right-base) left-base :none)))
          (t :none)))
   ((and (equal first *proof-one*) (proof-is-call second *h3-book-powers-expt*))
    (proof-term-at second 1))
   (t :none)))

(defun h3-book-power-order-as-powers-rewrite (lib result terms prefix position base)
  (declare (xargs :measure (acl2-count terms)))
  (cond
   ((failure-p result) result)
   ((endp terms) result)
   (t
    (let ((next
           (if (equal (car terms) *proof-one*)
               (proof-with-checked-results
                 ((at-zero (h3-book-powers-power-equation
                            lib (h3-book-powers-power base *proof-zero*) *proof-one* nil))
                  (proof (library-library-proof lib))
                  (reversed (proof-proof-symmetric proof at-zero)))
                 (proof-proof-rewrite proof result reversed (append prefix (list position))))
             result)))
      (h3-book-power-order-as-powers-rewrite lib next (cdr terms) prefix (1+ position) base)))))

(defun h3-book-power-order-as-powers (lib formula base)
  (proof-with-checked-results
    ((weak (proof-is-call formula *proof-not*))
     (comparison (if weak (proof-term-at formula 1) formula))
     (result (proof-proof-reflexive (library-library-proof lib) formula))
     (terms (h3-book-power-order-arguments comparison)))
    (h3-book-power-order-as-powers-rewrite lib result terms (if weak '(1 2 1) '(1 2)) 1 base)))

(defun h3-book-power-order-library-to-context (result context)
  (if (failure-p result)
      (cons result context)
    (cons (car result) (h3-book-order-bounds-with-library context (cdr result)))))

(defun h3-book-power-order-unit-premises (context base growing strict term)
  (h3-book-power-order-with-state context
    ((exponent (proof-term-at term 2))
     (typed (h3-book-power-order-library-to-context
             (h3-book-exponent-type-and-bound (h3-book-order-bounds-lib context) exponent context)
             context) :pair)
     (b (h3-book-power-order-step-argument base 1))
     (relative (h3-book-order-bounds-bound-with-bounds
                context (h3-book-power-order-unit-bound b growing strict)) :pair)
     (bound (h3-book-order-bounds-bound-with-bounds
             context (if strict (library-lt *proof-zero* exponent)
                       (library-le *proof-zero* exponent))) :pair))
    (cons (list (car typed) relative bound) context)))

(defun h3-book-power-order-compare-with-one-with-context
  (formula context base positive low high strict)
  (if (and (not (equal low *proof-one*)) (not (equal high *proof-one*)))
      (cons nil context)
    (let* ((growing (equal low *proof-one*))
           (term (if growing high low))
           (premises (h3-book-power-order-unit-premises context base growing strict term))
           (context (cdr premises))
           (data (car premises)))
      (cond
       ((h3-rewrite-unproved-p data) (cons nil context))
       ((failure-p data) premises)
       (t
        (h3-book-power-order-with-state context
          ((lib (h3-book-order-bounds-lib context))
           (result (h3-book-power-order-library-to-context
                    (if strict
                        (h3-book-power-order-unit-bound-positive-with-library
                         lib base positive (cadr data) (car data) (caddr data) growing)
                      (h3-book-power-order-unit-bound-natural-with-library
                       lib base positive (cadr data) (car data) (caddr data) growing))
                    context) :pair)
           (literal (proof-step-first result)))
          (cons (if (equal literal formula) result '(:failure "failure" "")) context)))))))

(defun h3-book-power-order-direction-bounds (context b growing strict first second)
  (h3-book-power-order-with-state context
    ((relative (h3-book-order-bounds-bound-with-bounds
                context (h3-book-power-order-unit-bound b growing strict)) :pair)
     (i (h3-book-power-order-step-argument first 1))
     (j (h3-book-power-order-step-argument second 1))
     (exponent-bound (h3-book-order-bounds-bound-with-bounds
                      context (if strict (library-lt i j) (library-le i j))) :pair))
    (cons (list relative exponent-bound) context)))

(defun h3-book-power-order-try-directions (directions context b base positive strict normalized)
  (declare (xargs :measure (acl2-count directions)))
  (if (endp directions)
      (cons '(:failure "unproved" "") context)
    (let* ((direction (car directions))
           (growing (car direction))
           (first (cadr direction))
           (second (caddr direction))
           (attempt (h3-book-power-order-direction-bounds context b growing strict first second))
           (context (cdr attempt))
           (bounds (car attempt)))
      (cond
       ((h3-rewrite-unproved-p bounds)
        (h3-book-power-order-try-directions (cdr directions) context b base positive strict normalized))
       ((failure-p bounds) attempt)
       (t
        (h3-book-power-order-with-state context
          ((result (h3-book-power-order-library-to-context
                    (h3-book-power-order-compare-powers-with-library
                     (h3-book-order-bounds-lib context) base positive (car bounds)
                     first second (cadr bounds) growing)
                    context) :pair)
           (step (proof-proof-transport
                  (library-library-proof (h3-book-order-bounds-lib context)) result normalized)))
          (cons step context)))))))

(defun h3-book-power-order-comparison-start (formula context)
  (h3-book-power-order-with-state context
    ((limits (h3-book-order-bound-parts formula)))
    (if (null limits)
        (cons '(:failure "unproved" "") context)
      (h3-book-power-order-with-state context
        ((low (car limits))
         (high (cadr limits))
         (strict (caddr limits))
         (b (h3-book-power-order-pair-base low high)))
        (if (eq b :none)
            (h3-book-order-bounds-bound-with-bounds context formula)
          (h3-book-power-order-with-state context
            ((base (h3-book-order-bounds-rational context b))
             (positive (h3-book-order-bounds-bound-with-bounds
                        context (library-lt *proof-zero* b)) :pair)
             (direct (h3-book-power-order-compare-with-one-with-context
                      formula context base positive low high strict) :pair))
            (if direct
                (cons direct context)
              (h3-book-power-order-with-state context
                ((normalized (h3-book-power-order-as-powers
                              (h3-book-order-bounds-lib context) formula b))
                 (comparison (h3-book-power-order-step-argument normalized 2))
                 (parts (h3-book-order-bound-parts comparison)))
                (if (null parts)
                    (cons '(:failure "failure" "") context)
                  (cons (list :indices (list (car parts) (cadr parts))
                              normalized b base positive strict)
                        context))))))))))

(defun h3-book-power-order-comparison-index (term context)
  (h3-book-power-order-with-state context
    ((index (proof-term-at term 2)))
    (let* ((typed (h3-book-power-order-library-to-context
                   (h3-book-exponent-type-and-bound
                    (h3-book-order-bounds-lib context) index context)
                   context))
           (value (car typed))
           (context (cdr typed)))
      (cond ((h3-rewrite-unproved-p value) (cons (list :noninteger index) context))
            ((failure-p value) typed)
            (t (cons (car value) context))))))

(defun h3-book-power-order-assume-integer (context test)
  (let ((lib (h3-book-order-bounds-lib context))
        (evidence (table-values (h3-book-order-bounds-evidence context))))
    (proof-with-checked-results
      ((typed (proof-proof-assume (library-library-proof lib) test t)))
      (h3-book-order-bounds-init lib (append evidence (list typed))))))

(defun h3-book-power-order-reduce-noninteger (lib formula strict term test position)
  (proof-with-checked-results
    ((comparison (if strict formula (proof-term-at formula 1)))
     (endpoint (if strict position (- 3 position)))
     (path (append (if strict '(1 2) '(1 2 1)) (list endpoint)))
     (proof (library-library-proof lib))
     (untyped (proof-proof-assume proof test nil))
     (opened (h3-book-powers-power-equation lib term *proof-one* (list untyped)))
     (original (proof-term-at comparison endpoint)))
    (if (equal original term)
        (proof-with-checked-results
          ((reflexive (proof-proof-reflexive proof formula))
           (reduced (proof-proof-rewrite proof reflexive opened path))
           (goal (h3-book-power-order-step-argument reduced 2)))
          (list reduced goal))
      '(:failure "failure" ""))))

(defun h3-book-power-order-join-exponent-cases (test yes no reduced)
  (let ((context (cdr no)))
    (h3-book-power-order-with-state context
      ((step (car no))
       (proof (library-library-proof (h3-book-order-bounds-lib context)))
       (transported (proof-proof-transport proof step reduced))
       (result (proof-proof-cases proof test yes transported)))
      (cons result context))))

; A request holds a phase, its Bounds, the pending cases and its arguments.
(defun h3-book-power-order-comparison-result (result pending)
  (list (if pending :resume :finished) (cdr result) pending (car result)))

(defun h3-book-power-order-comparison-indices (context pending arguments)
  (let ((formula (car arguments))
        (normalized (cadr arguments))
        (b (caddr arguments))
        (base (cadddr arguments))
        (positive (nth 4 arguments))
        (strict (nth 5 arguments))
        (terms (nth 6 arguments))
        (position (nth 7 arguments))
        (indices (nth 8 arguments)))
    (if (endp terms)
        (let ((high (car indices))
              (low (cadr indices)))
          (h3-book-power-order-comparison-result
           (h3-book-power-order-try-directions
            (list (list t low high) (list nil high low)) context b base positive strict normalized)
           pending))
      (let* ((term (car terms))
             (typed (h3-book-power-order-comparison-index term context))
             (context (cdr typed))
             (value (car typed)))
        (cond
         ((eq (car value) :noninteger)
          (let* ((test (list *proof-integerp* (cadr value)))
                 (added (h3-book-power-order-assume-integer context test)))
            (if (failure-p added)
                (h3-book-power-order-comparison-result (cons added context) pending)
              (list :compare added
                    (cons (list :integer context formula strict term test position) pending)
                    formula))))
         ((failure-p value)
          (h3-book-power-order-comparison-result typed pending))
         (t (list :indices context pending
                  (list formula normalized b base positive strict
                        (cdr terms) (1+ position) (cons value indices)))))))))

(defun h3-book-power-order-resume-comparison (context pending result)
  (let ((case-data (car pending))
        (pending (cdr pending)))
    (if (eq (car case-data) :integer)
        (let* ((lib (h3-book-order-bounds-lib context))
               (context (h3-book-order-bounds-with-library (cadr case-data) lib)))
          (if (failure-p result)
              (h3-book-power-order-comparison-result (cons result context) pending)
            (let* ((test (nth 5 case-data))
                   (reduced (h3-book-power-order-reduce-noninteger
                             lib (caddr case-data) (cadddr case-data)
                             (nth 4 case-data) test (nth 6 case-data))))
              (if (failure-p reduced)
                  (h3-book-power-order-comparison-result (cons reduced context) pending)
                (list :compare context
                      (cons (list :noninteger test result (car reduced)) pending)
                      (cadr reduced))))))
      (h3-book-power-order-comparison-result
       (h3-book-power-order-join-exponent-cases
        (cadr case-data) (caddr case-data) (cons result context) (cadddr case-data))
       pending))))

(defun h3-book-power-order-comparison-next (request)
  (let ((context (cadr request))
        (pending (caddr request))
        (arguments (cadddr request)))
    (case (car request)
      (:compare
       (let* ((started (h3-book-power-order-comparison-start arguments context))
              (value (car started)))
         (if (eq (car value) :indices)
             (list :indices (cdr started) pending
                   (list arguments (caddr value) (cadddr value)
                         (nth 4 value) (nth 5 value) (nth 6 value) (cadr value) 1 nil))
           (h3-book-power-order-comparison-result started pending))))
      (:indices (h3-book-power-order-comparison-indices context pending arguments))
      (:resume (h3-book-power-order-resume-comparison context pending arguments))
      (otherwise request))))

(defun h3-book-power-order-run-comparison (n request)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n)
         (cons '(:failure "fuel" "h3-book-power-order-run-comparison") (cadr request)))
        ((eq (car request) :finished) (cons (cadddr request) (cadr request)))
        (t (h3-book-power-order-run-comparison
            (1- n) (h3-book-power-order-comparison-next request)))))

(defun h3-book-power-order-exponent-comparison-with-context (n formula context)
  (h3-book-power-order-run-comparison n (list :compare context nil formula)))

(defun h3-book-power-order-pair-base-arguments (endpoints)
  (let ((count (len endpoints)))
    (case count
      (0 '(:failure "failure" ""))
      (1 '(:failure "failure" ""))
      (2 (h3-book-power-order-pair-base (car endpoints) (cadr endpoints)))
      (otherwise
       '(:failure "failure" "")))))

(defun h3-book-power-order-equivalent-power-order-solve (extra desired lib context)
  (h3-book-power-order-with-state lib
    ((added (h3-book-order-bounds-init
             lib (append (table-values (h3-book-order-bounds-evidence context)) (list extra)))))
    (h3-book-power-order-bound-library
     (h3-book-power-order-exponent-comparison-with-context 1000000 desired added))))

(defun h3-book-power-order-equivalent-power-order-forward (given lib rhs lhs context)
  (h3-book-power-order-with-state lib
    ((against (proof-proof-assume (library-library-proof lib) rhs nil))
     (opposed (h3-book-power-order-equivalent-power-order-solve
               against (proof-neg lhs) lib context) :pair)
     (proof (library-library-proof lib))
     (contradiction (proof-proof-cut proof given opposed))
     (step (proof-proof-front proof contradiction rhs)))
    (cons step lib)))

(defun h3-book-power-order-equivalent-power-order-with-library (lib goal context)
  (h3-book-power-order-with-state lib
    ((arguments (h3-book-power-order-arguments goal))
     (sides (proof-list-of-length arguments 2))
     (first (car sides))
     (second (cadr sides))
     (weak (and (proof-is-call first *proof-not*) (proof-is-call second *proof-not*)))
     (lhs (if weak (proof-term-at first 1) first))
     (rhs (if weak (proof-term-at second 1) second))
     (base (if (and (proof-is-call lhs *proof-less*) (proof-is-call rhs *proof-less*))
               (h3-book-power-order-pair-base-arguments (cdr lhs))
             :none)))
    (if (eq base :none)
        (cons nil lib)
      (h3-book-power-order-with-state lib
        ((start (h3-book-floor-equivalent-booleans-start lib lhs) :pair)
         (forward (h3-book-power-order-equivalent-power-order-forward
                   (car start) lib rhs lhs context) :pair)
         (positive (h3-book-floor-equivalent-booleans-positive lib (cadr start) forward) :pair)
         (no (proof-proof-assume (library-library-proof lib) lhs nil))
         (given (proof-proof-assume (library-library-proof lib) rhs t))
         (backward (h3-book-power-order-equivalent-power-order-solve given lhs lib context) :pair)
         (result (h3-book-floor-equivalent-booleans-finish lib lhs rhs positive no backward)))
        (if (not weak)
            (cons result lib)
          (h3-book-power-order-with-state lib
            ((proof (library-library-proof lib))
             (reflexive (proof-proof-reflexive proof first))
             (step (proof-proof-rewrite proof reflexive result '(1 2 1))))
            (cons step lib)))))))

(defun h3-book-power-order-has-power-comparison (formula)
  (proof-with-checked-results
    ((parts (h3-book-order-bound-parts formula)))
    (if (null parts)
        nil
      (proof-with-checked-results
        ((base (h3-book-power-order-pair-base (car parts) (cadr parts))))
        (not (eq base :none))))))

(defun h3-book-power-order-integral-power-test-with-library (lib goal context)
  (h3-book-power-order-with-state lib
    ((arguments (h3-book-power-order-arguments goal))
     (sides (proof-list-of-length arguments 2))
     (test (car sides))
     (condition (cadr sides))
     (term (proof-term-at test 1))
     (power-arguments (h3-book-power-order-arguments term))
     (operands (proof-list-of-length power-arguments 2))
     (b (car operands))
     (i (cadr operands))
     (base-data (h3-book-exponent-type-and-bound lib b context) :pair)
     (index-data (h3-book-exponent-type-and-bound lib i context) :pair)
     (base (car base-data))
     (index (car index-data))
     (rational (h3-book-numerator-as-rational lib base))
     (positive (h3-book-power-order-bound-library
                (h3-book-order-bounds-bound-with-bounds
                 (h3-book-order-bounds-with-library context lib) (library-lt *proof-zero* b))) :pair)
     (test-negative (library-lt i *proof-zero*))
     (proof (library-library-proof lib))
     (unfold (proof-proof-unfold proof condition))
     (above (proof-proof-assume proof test-negative nil))
     (whole (h3-book-powers-integral-power-natural lib base index above) :pair)
     (proof (library-library-proof lib))
     (body (h3-book-power-order-step-argument unfold 2))
     (selected-branch (proof-proof-select proof body above))
     (selected (proof-proof-chain proof unfold (list selected-branch)))
     (predicate (h3-book-signs-predicate-value-with-library lib whole) :pair)
     (proof (library-library-proof lib))
     (reversed (proof-proof-symmetric proof selected))
     (good (proof-proof-chain proof predicate (list reversed)))
     (below (proof-proof-assume proof test-negative t))
     (bounded (h3-book-order-bounds-init
               lib (append (table-values (h3-book-order-bounds-evidence context)) (list below))))
     (smaller (h3-book-power-order-bound-library
               (h3-book-power-order-exponent-comparison-with-context
                1000000 (library-lt term *proof-one*) bounded)) :pair)
     (power-positive (h3-book-powers-positive-power lib rational positive index) :pair)
     (proof (library-library-proof lib))
     (incompatible (proof-proof-fact proof "integer-discrete" (list (list *library-x* term))))
     (assumed (proof-proof-assume proof test t))
     (both (h3-book-floor-conjunct-proof lib (list assumed power-positive)))
     (impossible (proof-proof-modus-ponens proof incompatible both))
     (contradiction (proof-proof-cut proof smaller impossible))
     (fractional (proof-proof-front proof contradiction (proof-neg test)))
     (selected-branch (proof-proof-select proof body below))
     (lowered (proof-proof-chain proof unfold (list selected-branch)))
     (nil-value (h3-rewrite-nil-value lib fractional))
     (reversed (proof-proof-symmetric proof lowered))
     (bad (proof-proof-chain proof nil-value (list reversed)))
     (step (proof-proof-cases proof test-negative bad good)))
    (cons step lib)))

(defun h3-book-power-order-window-premises (context term b)
  (h3-book-power-order-with-state context
    ((base (h3-book-order-bounds-rational context b))
     (positive (h3-book-order-bounds-bound-with-bounds
                context (library-lt *proof-zero* b)) :pair)
     (unit (h3-book-order-bounds-bound-with-bounds context (library-le *proof-one* b)) :pair)
     (lower (h3-book-order-bounds-bound-with-bounds context (library-le *proof-one* term)) :pair)
     (upper (h3-book-order-bounds-bound-with-bounds context (library-lt term b)) :pair))
    (cons (list base positive unit lower upper) context)))

(defun h3-book-power-order-unit-power-in-window-with-library (lib goal context)
  (h3-book-power-order-with-state lib
    ((term (proof-term-at goal 1))
     (arguments (h3-book-power-order-arguments term))
     (operands (proof-list-of-length arguments 2))
     (b (car operands))
     (i (cadr operands))
     (premises (h3-book-power-order-bound-library
                (h3-book-power-order-window-premises
                 (h3-book-order-bounds-with-library context lib) term b)) :pair)
     (base (car premises))
     (positive (cadr premises))
     (unit (caddr premises))
     (lower (cadddr premises))
     (upper (car (cddddr premises)))
     (integer (list *proof-integerp* i))
     (proof (library-library-proof lib))
     (typed (proof-proof-assume proof integer t))
     (index-negative (library-lt i *proof-zero*))
     (at-zero (proof-eq i *proof-zero*))
     (below (proof-proof-assume proof index-negative t))
     (bounded (h3-book-order-bounds-init
               lib (append (table-values (h3-book-order-bounds-evidence context)) (list typed below))))
     (smaller (h3-book-power-order-bound-library
               (h3-book-power-order-exponent-comparison-with-context
                1000000 (library-lt term *proof-one*) bounded)) :pair)
     (proof (library-library-proof lib))
     (too-low (proof-proof-cut proof smaller lower))
     (negative (proof-proof-subsume proof too-low (cons goal (proof-step-clause too-low))))
     (nonnegative (proof-proof-assume proof index-negative nil))
     (is-zero (proof-proof-assume proof at-zero t))
     (zero (h3-book-powers-power-equation lib term *proof-one* (list typed is-zero)))
     (not-zero (proof-proof-assume proof at-zero nil))
     (pos (h3-book-powers-positive-index lib typed nonnegative not-zero) :pair)
     (zero-integer (library-library-axiom lib "INTEGER-0" nil))
     (previous (h3-book-floor-integer-gap-with-library lib zero-integer typed pos) :pair)
     (proof (library-library-proof lib))
     (one (proof-proof-compute proof (library-plus *proof-one* *proof-zero*) 1))
     (previous (proof-proof-rewrite proof previous one '(1 1 2)))
     (one-int (library-library-axiom lib "INTEGER-1" nil))
     (order (h3-book-power-order-compare-powers-with-library
             lib base positive unit one-int typed previous t) :pair)
     (base-data (h3-book-powers-positive-base lib base positive) :pair)
     (numeric (car base-data))
     (nonzero (cadr base-data))
     (value (h3-book-powers-unit-index-power lib numeric nonzero))
     (fixed (h3-book-arithmetic-fix-value lib b numeric))
     (proof (library-library-proof lib))
     (first (proof-proof-chain proof value (list fixed)))
     (out-of-range (proof-proof-rewrite proof order first '(1 1 2)))
     (too-high (proof-proof-cut proof upper out-of-range))
     (remaining (proof-proof-subsume proof too-high (cons goal (proof-step-clause too-high))))
     (zero-or-positive (proof-proof-cases proof at-zero zero remaining))
     (for-integers (proof-proof-cases proof index-negative negative zero-or-positive))
     (not-integer (proof-proof-assume proof integer nil))
     (outside (h3-book-powers-power-equation lib term *proof-one* (list not-integer)))
     (step (proof-proof-cases proof integer for-integers outside)))
    (cons step lib)))

(defun h3-book-power-order-integral-shape (goal lhs)
  (and (proof-is-call lhs *proof-integerp*)
       (proof-with-checked-results ((power (proof-term-at lhs 1)))
         (and (proof-is-call power *h3-book-powers-expt*)
              (proof-with-checked-results
                ((rhs (proof-term-at goal 2))
                 (exponent (proof-term-at power 2)))
                (equal rhs (library-le *proof-zero* exponent)))))))

(defun h3-book-power-order-power-order-theorem-with-library (lib formula)
  (h3-book-power-order-with-state lib
    ((parts (if (proof-is-call formula *library-implies*)
                (proof-list-of-length (cdr formula) 2)
              (list nil formula)))
     (guard (car parts))
     (goal (cadr parts))
     (direct (h3-book-power-order-has-power-comparison goal))
     (equation (proof-is-call goal *proof-equal*))
     (lhs (and equation (proof-term-at goal 1)))
     (equivalent (and equation (h3-book-power-order-has-power-comparison lhs)))
     (integral (and equation (h3-book-power-order-integral-shape goal lhs)))
     (guarded (h3-book-power-order-truth guard))
     (window (and guarded equation (proof-is-call lhs *h3-book-powers-expt*)
                  (proof-with-checked-results ((rhs (proof-term-at goal 2)))
                    (equal rhs *proof-one*)))))
    (if (not (or direct equivalent integral window))
        (cons nil lib)
      (h3-book-power-order-with-state lib
        ((given (and guarded (proof-proof-assume (library-library-proof lib) guard t)))
         (context (h3-book-order-bounds-init lib (and given (list given))))
         (step
          (cond (direct
                 (h3-book-power-order-bound-library
                  (h3-book-power-order-exponent-comparison-with-context 1000000 goal context)))
                (equivalent (h3-book-power-order-equivalent-power-order-with-library lib goal context))
                (integral (h3-book-power-order-integral-power-test-with-library lib goal context))
                (t (h3-book-power-order-unit-power-in-window-with-library lib goal context))) :pair)
         (result (if (and guarded step) (h3-rewrite-implication lib guard step) step)))
        (cons result lib)))))

