(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-book-power-identities-fix* (proof-sym "FIX" "ACL2"))
(defconst *h3-book-power-identities-zip* (proof-sym "ZIP" "ACL2"))

; A paired binding carries the updated Library into the next form.
; A Library update is itself the new Library, without a separate value.
(defmacro h3-book-power-identities-with-results (lib bindings result)
  (if (endp bindings)
      result
    (let* ((binding (car bindings))
           (name (car binding))
           (form (cadr binding))
           (remaining (cdr bindings)))
      (case (caddr binding)
        (:pair
         `(let ((h3-power-identities-pair ,form))
            (if (failure-p h3-power-identities-pair)
                (cons h3-power-identities-pair ,lib)
              (let ((,name (car h3-power-identities-pair))
                    (,lib (cdr h3-power-identities-pair)))
                (if (failure-p ,name)
                    (cons ,name ,lib)
                  (h3-book-power-identities-with-results ,lib ,remaining ,result))))))
        (:update
         `(let ((h3-power-identities-updated ,form))
            (if (failure-p h3-power-identities-updated)
                (cons h3-power-identities-updated ,lib)
              (let ((,lib h3-power-identities-updated))
                (h3-book-power-identities-with-results ,lib ,remaining ,result)))))
        (otherwise
         `(let ((,name ,form))
            (if (failure-p ,name)
                (cons ,name ,lib)
              (h3-book-power-identities-with-results ,lib ,remaining ,result))))))))

(defun h3-book-power-identities-first-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h3-book-power-identities-arguments (term size)
  (if (integerp term)
      '(:failure "failure" "")
    (proof-list-of-length (cdr term) size)))

(defun h3-book-power-identities-prove (lib term)
  (let* ((search (h3-rewrite-search-init lib nil nil nil 150 nil))
         (result (h3-rewrite-search-prove search term nil)))
    (car result)))

(defun h3-book-power-identities-each-base-branch
    (numeric status nonzero lib base)
  (if nonzero
      (list :h3-power-base-request :particular numeric status lib)
    (h3-book-power-identities-with-results lib
        ((fixed (h3-book-arithmetic-fix-value lib base numeric))
         (literal (proof-step-first status))
         (fixed (if (proof-is-call literal *proof-equal*)
                    (proof-proof-chain (library-library-proof lib) fixed (list status))
                  fixed)))
      (list :h3-power-base-request :default fixed status lib))))

(defun h3-book-power-identities-each-base (lib base particular default)
  (let* ((number (list *library-numberp* base))
         (zero (proof-eq base *proof-zero*)))
    (h3-book-power-identities-with-results lib
        ((numeric (proof-proof-assume (library-library-proof lib) number t)))
      (if (endp default)
          (h3-book-power-identities-with-results lib
              ((status (proof-proof-assume (library-library-proof lib) zero t)))
            (h3-book-power-identities-each-base-branch numeric status nil lib base))
        (h3-book-power-identities-with-results lib ((equal-zero (car default) :pair))
          (if (not particular)
              (h3-book-power-identities-with-results lib
                  ((status (proof-proof-assume (library-library-proof lib) zero nil)))
                (h3-book-power-identities-each-base-branch numeric status t lib base))
            (h3-book-power-identities-with-results lib
                ((different particular :pair)
                 (nonnumeric (proof-proof-assume (library-library-proof lib) number nil))
                 (numeric-case (proof-proof-cases (library-library-proof lib)
                                                  zero equal-zero different)))
              (if (endp (cdr default))
                  (h3-book-power-identities-each-base-branch nonnumeric nonnumeric nil lib base)
                (h3-book-power-identities-with-results lib ((other (cadr default) :pair))
                  (cons (proof-proof-cases (library-library-proof lib) number numeric-case other)
                        lib))))))))))

(defmacro h3-book-power-identities-with-base-forms
    (live-lib lib base particular-names particular-form default-names default-form)
  `(let* ((h3-power-base-original-library ,lib)
          (h3-power-base-term ,base)
          (h3-power-base-request
           (h3-book-power-identities-each-base h3-power-base-original-library
                                               h3-power-base-term nil nil)))
     (if (not (eq (car h3-power-base-request) :h3-power-base-request))
         h3-power-base-request
       (let* ((h3-power-base-zero
               (let ((,live-lib (nth 4 h3-power-base-request))
                     (,(car default-names) (nth 2 h3-power-base-request))
                     (,(cadr default-names) (nth 3 h3-power-base-request)))
                 ,default-form))
              (h3-power-base-request
               (h3-book-power-identities-each-base h3-power-base-original-library
                                                   h3-power-base-term nil
                                                   (list h3-power-base-zero))))
         (if (not (eq (car h3-power-base-request) :h3-power-base-request))
             h3-power-base-request
           (let* ((h3-power-base-particular
                   (let ((,live-lib (nth 4 h3-power-base-request))
                         (,(car particular-names) (nth 2 h3-power-base-request))
                         (,(cadr particular-names) (nth 3 h3-power-base-request)))
                     ,particular-form))
                  (h3-power-base-request
                   (h3-book-power-identities-each-base h3-power-base-original-library
                                                       h3-power-base-term
                                                       h3-power-base-particular
                                                       (list h3-power-base-zero))))
             (if (not (eq (car h3-power-base-request) :h3-power-base-request))
                 h3-power-base-request
               (let ((h3-power-base-other
                      (let ((,live-lib (nth 4 h3-power-base-request))
                            (,(car default-names) (nth 2 h3-power-base-request))
                            (,(cadr default-names) (nth 3 h3-power-base-request)))
                        ,default-form)))
                 (h3-book-power-identities-each-base h3-power-base-original-library
                                                     h3-power-base-term
                                                     h3-power-base-particular
                                                     (list h3-power-base-zero
                                                           h3-power-base-other))))))))))

(defmacro h3-book-power-identities-with-each-base (lib base particular default)
  `(h3-book-power-identities-with-base-forms
     h3-power-base-live-library ,lib ,base
     (h3-power-base-first h3-power-base-second)
     (,(car particular) h3-power-base-live-library h3-power-base-first
                        h3-power-base-second ,@(cdr particular))
     (h3-power-base-first h3-power-base-second)
     (,(car default) h3-power-base-live-library h3-power-base-first
                     h3-power-base-second ,@(cdr default))))

(defun h3-book-power-identities-base-zero-power-branch
    (p lib test target term literal holds fixed-zero)
  (proof-with-checked-results
      ((evidence (proof-proof-assume p test holds))
       (computed (h3-book-powers-power-equation lib term literal
                                                 (list evidence fixed-zero)))
       (selected (proof-proof-select p target evidence))
       (back (proof-proof-symmetric p selected)))
    (proof-proof-chain p computed (list back))))

(defun h3-book-power-identities-base-zero-power (lib term fixed-zero)
  (proof-with-checked-results ((index (proof-term-at term 2)))
    (let* ((p (library-library-proof lib))
           (test (list *h3-book-power-identities-zip* index))
           (target (proof-ite test *proof-one* *proof-zero*)))
      (proof-with-checked-results
          ((yes (h3-book-power-identities-base-zero-power-branch
                 p lib test target term *proof-one* t fixed-zero))
           (no (h3-book-power-identities-base-zero-power-branch
                p lib test target term *proof-zero* nil fixed-zero)))
        (proof-proof-cases p test yes no)))))

(defun h3-book-power-identities-power-index-zero (lib base)
  (h3-book-powers-power-equation lib (h3-book-powers-power base *proof-zero*)
                                *proof-one* nil))

(defun h3-book-power-identities-power-index-one-numeric (typed nonzero lib)
  (h3-book-powers-unit-index-power lib typed nonzero))

(defun h3-book-power-identities-power-index-one-default (fixed status lib base)
  (declare (ignore status))
  (let ((p (library-library-proof lib)))
    (proof-with-checked-results
        ((computed (h3-book-powers-power-equation lib (h3-book-powers-power base *proof-one*)
                                                  *proof-zero* (list fixed)))
         (back (proof-proof-symmetric p fixed)))
      (proof-proof-chain p computed (list back)))))

(defun h3-book-power-identities-power-index-one (lib base)
  (car (h3-book-power-identities-with-base-forms
        lib lib base
        (typed nonzero)
        (cons (h3-book-power-identities-power-index-one-numeric typed nonzero lib) lib)
        (fixed status)
        (cons (h3-book-power-identities-power-index-one-default fixed status lib base) lib))))

(defun h3-book-power-identities-base-one-natural (lib index bound)
  (let ((search (h3-rewrite-search-init lib nil nil nil 150 nil)))
    (h3-book-power-identities-with-results lib
        ((whole (library-library-axiom lib "INTEGER-1" nil))
         (base (h3-book-numerator-as-rational lib whole))
         (positive-proof (h3-rewrite-search-prove search (library-lt *proof-zero* *proof-one*) nil))
         (positive (car positive-proof))
         (upper-proof (h3-rewrite-search-prove (cdr positive-proof)
                                              (h3-book-power-order-unit-bound *proof-one* nil nil)
                                              nil))
         (upper-relative (car upper-proof))
         (upper (h3-book-power-order-unit-bound-natural-with-library
                 lib base positive upper-relative index bound nil) :pair)
         (lower-proof (h3-rewrite-search-prove (h3-rewrite-search-with-lib (cdr upper-proof) lib)
                                              (h3-book-power-order-unit-bound *proof-one* t nil)
                                              nil))
         (lower-relative (car lower-proof))
         (lower (h3-book-power-order-unit-bound-natural-with-library
                 lib base positive lower-relative index bound t) :pair)
         (exponent (h3-book-power-identities-first-at index 1))
         (lib (h3-numeric-order-numeric-order lib) :update)
         (power-type (h3-book-powers-rational-power lib base exponent))
         (power-number (h3-book-signs-number lib power-type))
         (base-number (h3-book-signs-number lib base)))
      (cons (h3-numeric-order-cite lib "WEAK-ANTISYMMETRIC"
                                  (list (h3-book-powers-power *proof-one* exponent) *proof-one*)
                                  (list power-number base-number upper lower))
            lib))))

(defun h3-book-power-identities-power-base-one (lib index)
  (let* ((term (h3-book-powers-power *proof-one* index))
         (type-test (list *proof-integerp* index))
         (test (library-lt index *proof-zero*)))
    (h3-book-power-identities-with-results lib
        ((typed (proof-proof-assume (library-library-proof lib) type-test t))
         (lower (proof-proof-assume (library-library-proof lib) test nil))
         (nonnegative (h3-book-power-identities-base-one-natural lib typed lower) :pair)
         (below (proof-proof-assume (library-library-proof lib) test t))
         (sum-lemmas (h3-book-sums-lemmas-with-library lib) :pair)
         (opposite (library-library-type-of lib (library-minus index) (list typed)))
         (rational (h3-book-numerator-as-rational lib typed))
         (numeric (h3-book-signs-number lib rational))
         (reflection (h3-book-signs-negative-reflection-with-library lib numeric) :pair)
         (positive (proof-proof-rewrite (library-library-proof lib) below reflection '(1)))
         (opposite-bound (h3-book-powers-nonnegative-integer lib opposite positive))
         (op (h3-book-power-identities-base-one-natural lib opposite opposite-bound) :pair)
         (one (library-library-axiom lib "INTEGER-1" nil))
         (unit (h3-book-numerator-as-rational lib one))
         (one-positive (h3-book-power-identities-prove lib (library-lt *proof-zero* *proof-one*)))
         (base (h3-book-powers-positive-base lib unit one-positive) :pair)
         (inverted (h3-book-powers-inverse-power-equation lib (car base) (cadr base)
                                                          typed below) :pair))
      (let ((p (library-library-proof lib)))
        (h3-book-power-identities-with-results lib
            ((negative (proof-proof-rewrite p inverted op '(1 2 1)))
             (division (proof-proof-compute p (list *h3-book-arithmetic-divide* *proof-one*) 1))
             (negative (proof-proof-chain p negative (list division)))
             (not-integer (proof-proof-assume p type-test nil))
             (absent (h3-book-powers-power-equation lib term *proof-one* (list not-integer)))
             (integer-case (proof-proof-cases p test negative nonnegative)))
          (cons (proof-proof-cases p type-test integer-case absent) lib))))))

(defun h3-book-power-identities-equal-when-both-zero-factors
    (p start right zeros position)
  (declare (xargs :measure (acl2-count zeros)))
  (if (or (endp zeros) (failure-p right))
      right
    (h3-book-power-identities-equal-when-both-zero-factors
     p start
     (proof-with-checked-results
         ((back (proof-proof-symmetric p (car zeros)))
          (exact (proof-proof-rewrite p start back '(1 1 2))))
       (proof-proof-rewrite p right exact (list 1 2 position)))
     (cdr zeros) (1+ position))))

(defun h3-book-power-identities-equal-when-both-zero
    (lib base first second summed zeros)
  (declare (ignore summed))
  (let ((p (library-library-proof lib)))
    (proof-with-checked-results
        ((start (h3-book-power-identities-power-index-zero lib base))
         (sum-zero (proof-term-at zeros 0))
         (back (proof-proof-symmetric p sum-zero))
         (left (proof-proof-rewrite p start back '(1 1 2)))
         (right (proof-proof-reflexive p (list *proof-times* (h3-book-powers-power base first)
                                                           (h3-book-powers-power base second))))
         (right (h3-book-power-identities-equal-when-both-zero-factors p start right (cdr zeros) 1))
         (computed (proof-proof-compute p (list *proof-times* *proof-one* *proof-one*) 1))
         (right (proof-proof-chain p right (list computed)))
         (back (proof-proof-symmetric p right)))
      (proof-proof-chain p left (list back)))))

(defun h3-book-power-identities-addition-with-zero-sum-removed
    (lib base first second first-position summed nonzero-sum fixed)
  (h3-book-power-identities-with-results lib
      ((i (h3-book-power-identities-first-at first 1))
       (j (h3-book-power-identities-first-at second 1))
       (total (h3-book-power-identities-first-at summed 1)))
    (let* ((p (library-library-proof lib))
           (result (h3-book-powers-power base total))
           (left (h3-book-powers-power base i))
           (right (h3-book-powers-power base j))
           (product (list *proof-times* left right))
           (test (proof-eq i *proof-zero*)))
      (h3-book-power-identities-with-results lib
          ((zero-first (proof-proof-assume p test t))
           (sum-start (proof-proof-reflexive p total))
           (base-eq (proof-proof-rewrite p sum-start zero-first (list 1 2 first-position)))
           (alignment-left (h3-book-power-identities-first-at base-eq 2))
           (alignment (h3-book-translation-sum-equality-with-library
                       lib alignment-left j (list second)) :pair))
        (let ((p (library-library-proof lib)))
          (h3-book-power-identities-with-results lib
              ((base-eq (proof-proof-chain p base-eq (list alignment)))
               (left-eq (h3-book-powers-power-equation lib left *proof-one* (list first zero-first)))
               (product-start (proof-proof-reflexive p product))
               (yes-rhs (proof-proof-rewrite p product-start left-eq '(1 2 1)))
               (unity (library-library-axiom lib "UNICITY-OF-1" (list right)))
               (right-type (h3-book-powers-numeric-power lib right))
               (identity (h3-book-arithmetic-fix-value lib right right-type))
               (yes-rhs (proof-proof-chain p yes-rhs (list unity identity)))
               (result-start (proof-proof-reflexive p result))
               (yes-lhs (proof-proof-rewrite p result-start base-eq '(1 2 2)))
               (yes-back (proof-proof-symmetric p yes-rhs))
               (yes (proof-proof-chain p yes-lhs (list yes-back)))
               (no-left (h3-book-powers-power-equation lib result *proof-zero*
                                                       (list summed nonzero-sum fixed)))
               (nonzero-first (proof-proof-assume p test nil))
               (factor (h3-book-powers-power-equation lib left *proof-zero*
                                                      (list first nonzero-first fixed)))
               (product-start (proof-proof-reflexive p product))
               (no-rhs (proof-proof-rewrite p product-start factor '(1 2 1)))
               (zero-product (h3-book-arithmetic-zero-left lib right))
               (no-rhs (proof-proof-chain p no-rhs (list zero-product)))
               (no-back (proof-proof-symmetric p no-rhs))
               (no (proof-proof-chain p no-left (list no-back))))
            (cons (proof-proof-cases p test yes no) lib)))))))

(defun h3-book-power-identities-signed-zero-index
    (lib index other integers zero-sum summed context nonnegative)
  (h3-book-power-identities-with-results lib
      ((i (h3-book-power-identities-first-at index 1))
       (j (h3-book-power-identities-first-at other 1))
       (start (proof-proof-reflexive (library-library-proof lib)
                                    (library-plus summed (library-minus j))))
       (cancellation (proof-proof-rewrite (library-library-proof lib) start zero-sum '(1 2 1)))
       (combined (h3-book-power-identities-first-at cancellation 1))
       (isolate (h3-book-translation-sum-equality-with-library lib combined i integers) :pair)
       (reduced (h3-book-power-identities-first-at cancellation 2))
       (opposite (h3-book-translation-sum-equality-with-library lib reduced (library-minus j) integers) :pair)
       (back (proof-proof-symmetric (library-library-proof lib) isolate))
       (equality (proof-proof-chain (library-library-proof lib) back (list cancellation opposite))))
    (let* ((context (h3-book-order-bounds-with-library context lib))
           (near-goal (if nonnegative (library-le *proof-zero* i) (library-le i *proof-zero*)))
           (companion-goal (if nonnegative (library-le *proof-zero* j) (library-le j *proof-zero*)))
           (far (if nonnegative (library-le i *proof-zero*) (library-le *proof-zero* i))))
      (h3-book-power-identities-with-results lib
          ((near-result (h3-book-order-bounds-bound-with-bounds context near-goal))
           (context (cdr near-result))
           (lib (h3-book-order-bounds-lib context) :update)
           (near (car near-result))
           (companion-result (h3-book-order-bounds-bound-with-bounds context companion-goal))
           (context (cdr companion-result))
           (lib (h3-book-order-bounds-lib context) :update)
           (companion (car companion-result)))
        (let ((p (library-library-proof lib)))
          (h3-book-power-identities-with-results lib
              ((start (proof-proof-reflexive p far))
               (rewritten (proof-proof-rewrite p start equality (list 1 2 1 (if nonnegative 2 1))))
               (sums (h3-book-sums-book-sums-init lib))
               (far-side (h3-book-power-identities-first-at rewritten 2))
               (shifted (proof-term-at far-side 1))
               (companion-side (h3-book-power-identities-first-at companion 1))
               (aligned (h3-book-sums-cancel-comparison lib sums shifted companion-side integers))
               (remaining (library-library-transport-argument lib companion aligned 1))
               (remaining (proof-proof-transport p remaining rewritten))
               (rational (h3-book-numerator-as-rational lib index))
               (number (h3-book-signs-number lib rational))
               (zero (library-library-axiom lib "INTEGER-0" nil))
               (rational-zero (h3-book-numerator-as-rational lib zero))
               (number-zero (h3-book-signs-number lib rational-zero))
               (step (h3-numeric-order-cite lib "WEAK-ANTISYMMETRIC" (list i *proof-zero*)
                                           (if nonnegative
                                               (list number number-zero remaining near)
                                             (list number number-zero near remaining)))))
            (cons (list step context) lib)))))))

(defun h3-book-power-identities-signed-zero-indices
    (lib integers zero-sum context nonnegative)
  (h3-book-power-identities-with-results lib
      ((lib (h3-numeric-order-numeric-order lib) :update)
       (summed (h3-book-power-identities-first-at zero-sum 1))
       (pair (proof-list-of-length integers 2))
       (first (h3-book-power-identities-signed-zero-index
               lib (car pair) (cadr pair) integers zero-sum summed context nonnegative) :pair)
       (second (h3-book-power-identities-signed-zero-index
                lib (cadr pair) (car pair) integers zero-sum summed (cadr first) nonnegative) :pair))
    (cons (list (car first) (car second)) lib)))

(defun h3-book-power-identities-argument-present-p (value)
  (and value (not (equal value 0)) (not (equal value ""))))

(defun h3-book-power-identities-totalized-power-addition-zero-case
    (lib test conditional term product summed first second context nonnegative base a b total)
  (let ((p (library-library-proof lib)))
    (h3-book-power-identities-with-results lib ((zero-sum (proof-proof-assume p test t)))
      (if conditional
          (h3-book-power-identities-with-results lib
              ((eq-one (h3-book-powers-power-equation lib term *proof-one* (list summed zero-sum)))
               (selected (proof-proof-select p product zero-sum))
               (back (proof-proof-symmetric p selected)))
            (cons (proof-proof-chain p eq-one (list back)) lib))
        (h3-book-power-identities-with-results lib
            ((zeros (h3-book-power-identities-signed-zero-indices
                     lib (list first second) zero-sum context nonnegative) :pair))
          (cons (h3-book-power-identities-equal-when-both-zero lib base a b total (cons zero-sum zeros))
                lib))))))

(defun h3-book-power-identities-totalized-power-addition-align (proof lib total first second)
  (h3-book-power-identities-with-results lib
      ((left (h3-book-power-identities-first-at proof 1))
       (exponent (proof-term-at left 2))
       (equivalent (h3-book-translation-sum-equality-with-library
                    lib exponent total (list first second)) :pair))
    (cons (proof-proof-rewrite (library-library-proof lib) proof equivalent '(1 1 2)) lib)))

(defun h3-book-power-identities-totalized-power-addition-numeric-selection
    (lib selected fixed-test remaining base base-number nonzero)
  (if (not (h3-book-power-identities-argument-present-p fixed-test))
      selected
    (let ((p (library-library-proof lib)))
      (proof-with-checked-results
          ((fixed (h3-book-arithmetic-fix-value lib base base-number))
           (back (proof-proof-symmetric p fixed))
           (reduced (proof-proof-rewrite p nonzero back '(1 1 1)))
           (inner (proof-proof-select p remaining reduced)))
        (proof-proof-chain p selected (list inner))))))

(defun h3-book-power-identities-totalized-power-addition-numeric
    (base-number nonzero lib conditional test product fixed-test remaining base total
                 first second term summed context nonnegative a b)
  (h3-book-power-identities-with-results lib
      ((proof (h3-book-powers-power-add-integer lib base-number nonzero first second) :pair)
       (proof (h3-book-power-identities-totalized-power-addition-align
               proof lib total first second) :pair))
    (if (not conditional)
        (cons proof lib)
      (let ((p (library-library-proof lib)))
        (h3-book-power-identities-with-results lib
            ((negative (proof-proof-assume p test nil))
             (selected (proof-proof-select p product negative))
             (selected (h3-book-power-identities-totalized-power-addition-numeric-selection
                        lib selected fixed-test remaining base base-number nonzero))
             (back (proof-proof-symmetric p selected))
             (other (proof-proof-chain p proof (list back)))
             (zero (h3-book-power-identities-totalized-power-addition-zero-case
                    lib test conditional term product summed first second context nonnegative
                    base a b total) :pair))
          (cons (proof-proof-cases (library-library-proof lib) test zero other) lib))))))

(defun h3-book-power-identities-totalized-power-addition-default
    (fixed status lib test fixed-test term summed product remaining total a base first second
           conditional context nonnegative b)
  (declare (ignore status))
  (h3-book-power-identities-with-results lib
      ((negative (proof-proof-assume (library-library-proof lib) test nil)))
    (if (h3-book-power-identities-argument-present-p fixed-test)
        (let ((p (library-library-proof lib)))
          (h3-book-power-identities-with-results lib
              ((proof (h3-book-powers-power-equation lib term *proof-zero* (list summed negative fixed)))
               (selected (proof-proof-select p product negative))
               (inner (proof-proof-select p remaining fixed))
               (selected (proof-proof-chain p selected (list inner)))
               (zero (h3-book-power-identities-totalized-power-addition-zero-case
                      lib test conditional term product summed first second context nonnegative
                      base a b total) :pair))
            (let ((p (library-library-proof lib)))
              (h3-book-power-identities-with-results lib
                  ((back (proof-proof-symmetric p selected))
                   (other (proof-proof-chain p proof (list back))))
                (cons (proof-proof-cases p test zero other) lib)))))
      (h3-book-power-identities-with-results lib
          ((first-addend (proof-term-at total 1))
           (proof (h3-book-power-identities-addition-with-zero-sum-removed
                   lib base first second (if (equal first-addend a) 1 2) summed negative fixed) :pair)
           (proof (if conditional
                      (let ((p (library-library-proof lib)))
                        (proof-with-checked-results
                            ((selected (proof-proof-select p product negative))
                             (back (proof-proof-symmetric p selected)))
                          (proof-proof-chain p proof (list back))))
                    proof))
           (zero (h3-book-power-identities-totalized-power-addition-zero-case
                  lib test conditional term product summed first second context nonnegative
                  base a b total) :pair))
        (cons (proof-proof-cases (library-library-proof lib) test zero proof) lib)))))

(defun h3-book-power-identities-totalized-power-addition-indices (pair)
  (cond
    ((integerp pair) (proof-term-at pair 1))
    ((endp (cdr pair)) '(:failure "failure" ""))
    (t
     (proof-with-checked-results ((first (proof-term-at (cadr pair) 2)))
       (if (endp (cddr pair))
           '(:failure "failure" "")
         (proof-with-checked-results ((second (proof-term-at (caddr pair) 2)))
           (if (endp (cdddr pair))
               (list first second)
             (proof-with-checked-results ((third (proof-term-at (cadddr pair) 2)))
               '(:failure "failure" "")))))))))

(defun h3-book-power-identities-totalized-power-addition (lib goal context nonnegative)
  (h3-book-power-identities-with-results lib
      ((sides (h3-book-power-identities-arguments goal 2))
       (power-args (h3-book-power-identities-arguments (car sides) 2)))
    (let* ((term (car sides))
           (product (cadr sides))
           (base (car power-args))
           (total (cadr power-args))
           (conditional (proof-is-call product *proof-if*)))
      (h3-book-power-identities-with-results lib
          ((parts (if conditional
                      (h3-book-power-identities-arguments product 3)
                    (list (proof-eq total *proof-zero*) nil product)))
           (fixed-test (and (proof-is-call (caddr parts) *proof-if*)
                            (proof-term-at (caddr parts) 1)))
           (pair (if (h3-book-power-identities-argument-present-p fixed-test)
                     (proof-term-at (caddr parts) 3)
                   (caddr parts)))
           (indices (h3-book-power-identities-totalized-power-addition-indices pair))
           (first-type (h3-book-exponent-type-and-bound
                        lib (car indices) (h3-book-order-bounds-with-library context lib)) :pair)
           (second-type (h3-book-exponent-type-and-bound
                         lib (cadr indices) (h3-book-order-bounds-with-library context lib)) :pair)
           (sum-lemmas (h3-book-sums-lemmas-with-library lib) :pair)
           (summed (library-library-type-of lib total (list (car first-type) (car second-type)))))
        (let ((first (car first-type))
              (second (car second-type))
              (test (car parts))
              (remaining (caddr parts))
              (a (car indices))
              (b (cadr indices)))
          (h3-book-power-identities-with-base-forms
           lib lib base
           (typed nonzero)
           (h3-book-power-identities-totalized-power-addition-numeric
            typed nonzero lib conditional test product fixed-test remaining base total first second
            term summed context nonnegative a b)
           (fixed status)
           (h3-book-power-identities-totalized-power-addition-default
            fixed status lib test fixed-test term summed product remaining total a base first second
            conditional context nonnegative b)))))))

(defun h3-book-power-identities-totalized-power-product-factors
    (lib known terms typings zeros position)
  (declare (xargs :measure (acl2-count terms)))
  (if (or (endp terms) (endp typings) (endp zeros) (failure-p known))
      known
    (h3-book-power-identities-totalized-power-product-factors
     lib
     (proof-with-checked-results
         ((power-one (h3-book-powers-power-equation lib (car terms) *proof-one*
                                                    (list (car typings) (car zeros)))))
       (proof-proof-rewrite (library-library-proof lib) known power-one (list 1 2 position)))
     (cdr terms) (cdr typings) (cdr zeros) (1+ position))))

(defun h3-book-power-identities-totalized-power-product-numeric
    (base-type nonzero lib first second base removed other both-zero known)
  (h3-book-power-identities-with-results lib
      ((combined (h3-book-powers-power-add-integer lib base-type nonzero first second) :pair))
    (let ((p (library-library-proof lib)))
      (h3-book-power-identities-with-results lib
          ((fixed (h3-book-arithmetic-fix-value lib base base-type))
           (back (proof-proof-symmetric p fixed))
           (ordinary (proof-proof-rewrite p nonzero back '(1 1 1)))
           (inner (proof-proof-select p other ordinary))
           (selected (proof-proof-chain p removed (list inner)))
           (back-combined (proof-proof-symmetric p combined))
           (back-selected (proof-proof-symmetric p selected))
           (nonempty (proof-proof-chain p back-combined (list back-selected))))
        (cons (proof-proof-cases p both-zero known nonempty) lib)))))

(defun h3-book-power-identities-totalized-power-product-default-vanishes
    (term typed nonzero position lib fixed product right left selected)
  (let ((p (library-library-proof lib)))
    (proof-with-checked-results
        ((zero (h3-book-powers-power-equation lib term *proof-zero* (list typed fixed nonzero)))
         (start (proof-proof-reflexive p product))
         (proof (proof-proof-rewrite p start zero (list 1 2 position)))
         (rule (if (equal position 1)
                   (h3-book-arithmetic-zero-left lib right)
                 (h3-event-counts-multiply-zero lib left)))
         (back (proof-proof-symmetric p selected)))
      (proof-proof-chain p proof (list rule back)))))

(defun h3-book-power-identities-totalized-power-product-default
    (fixed status lib removed other i-zero j-zero absent right second left first
           product both-zero known)
  (declare (ignore status))
  (let ((p (library-library-proof lib)))
    (h3-book-power-identities-with-results lib
        ((inner (proof-proof-select p other fixed))
         (selected (proof-proof-chain p removed (list inner)))
         (first-empty (proof-proof-assume p i-zero t))
         (second-empty (proof-proof-assume p j-zero t))
         (both (h3-book-floor-conjunct-proof lib (list first-empty second-empty)))
         (cut (proof-proof-cut p both absent))
         (second-nonzero (proof-proof-front p cut (proof-neg j-zero)))
         (yes (h3-book-power-identities-totalized-power-product-default-vanishes
               right second second-nonzero 2 lib fixed product right left selected))
         (first-nonzero (proof-proof-assume p i-zero nil))
         (no (h3-book-power-identities-totalized-power-product-default-vanishes
              left first first-nonzero 1 lib fixed product right left selected))
         (nonempty (proof-proof-cases p i-zero yes no)))
      (cons (proof-proof-cases p both-zero known nonempty) lib))))

(defun h3-book-power-identities-totalized-power-product (lib goal context)
  (h3-book-power-identities-with-results lib
      ((sides (h3-book-power-identities-arguments goal 2))
       (factors (h3-book-power-identities-arguments (car sides) 2))
       (base-index (h3-book-power-identities-arguments (car factors) 2))
       (j (proof-term-at (cadr factors) 2))
       (first-type (h3-book-exponent-type-and-bound
                    lib (cadr base-index) (h3-book-order-bounds-with-library context lib)) :pair)
       (second-type (h3-book-exponent-type-and-bound
                     lib j (h3-book-order-bounds-with-library context lib)) :pair)
       (parts (h3-book-power-identities-arguments (cadr sides) 3))
       (zero-tests (if (integerp (car parts))
                       (proof-term-at (car parts) 1)
                     (proof-list-of-length (seq-slice (car parts) 1 3) 2))))
    (let* ((p (library-library-proof lib))
           (product (car sides))
           (result (cadr sides))
           (left (car factors))
           (right (cadr factors))
           (base (car base-index))
           (first (car first-type))
           (second (car second-type))
           (both-zero (car parts))
           (other (caddr parts))
           (i-zero (car zero-tests))
           (j-zero (cadr zero-tests)))
      (h3-book-power-identities-with-results lib
          ((empty (proof-proof-assume p both-zero t))
           (zeros (proof-proof-conjunct p empty))
           (known (proof-proof-reflexive p product))
           (known (h3-book-power-identities-totalized-power-product-factors
                   lib known factors (list first second) zeros 1))
           (computed (proof-proof-compute p (list *proof-times* *proof-one* *proof-one*) 1))
           (selected (proof-proof-select p result empty))
           (back (proof-proof-symmetric p selected))
           (known (proof-proof-chain p known (list computed back)))
           (absent (proof-proof-assume p both-zero nil))
           (removed (proof-proof-select p result absent)))
        (h3-book-power-identities-with-base-forms
         lib lib base
         (base-type nonzero)
         (h3-book-power-identities-totalized-power-product-numeric
          base-type nonzero lib first second base removed other both-zero known)
         (fixed status)
         (h3-book-power-identities-totalized-power-product-default
          fixed status lib removed other i-zero j-zero absent right second left first
          product both-zero known))))))

(defun h3-book-power-identities-special-power (lib goal)
  (if (not (proof-is-call goal *proof-equal*))
      (cons nil lib)
    (h3-book-power-identities-with-results lib ((term (proof-term-at goal 1)))
      (if (not (proof-is-call term *h3-book-powers-expt*))
          (cons nil lib)
        (h3-book-power-identities-with-results lib
            ((arguments (h3-book-power-identities-arguments term 2)))
          (let ((base (car arguments))
                (index (cadr arguments)))
            (if (not (or (equal index *proof-zero*) (equal index *proof-one*)
                         (equal base *proof-zero*) (equal base *proof-one*)))
                (cons nil lib)
              (h3-book-power-identities-with-results lib ((value (proof-term-at goal 2)))
                (cond
                  ((and (equal index *proof-zero*) (equal value *proof-one*))
                   (cons (h3-book-power-identities-power-index-zero lib base) lib))
                  ((and (equal index *proof-one*)
                        (equal value (list *h3-book-power-identities-fix* base)))
                   (cons (h3-book-power-identities-power-index-one lib base) lib))
                  ((and (equal base *proof-zero*)
                        (equal value (proof-ite (list *h3-book-power-identities-zip* index)
                                                *proof-one* *proof-zero*)))
                   (h3-book-power-identities-with-results lib
                       ((numeric (h3-book-power-identities-prove lib (list *library-numberp* *proof-zero*)))
                        (fixed (h3-book-arithmetic-fix-value lib *proof-zero* numeric)))
                     (cons (h3-book-power-identities-base-zero-power lib term fixed) lib)))
                  ((and (equal base *proof-one*) (equal value *proof-one*))
                   (h3-book-power-identities-power-base-one lib index))
                  (t (cons nil lib)))))))))))

(defun h3-book-power-identities-equal-power-zero-numeric (typed nonzero lib b i right)
  (let ((p (library-library-proof lib)))
    (proof-with-checked-results
        ((positive (h3-book-powers-nonzero-power lib typed nonzero i))
         (result (h3-rewrite-nil-value lib positive))
         (fixed (h3-book-arithmetic-fix-value lib b typed))
         (back (proof-proof-symmetric p fixed))
         (nonzero-fixed (proof-proof-rewrite p nonzero back '(1 1 1)))
         (selected (proof-proof-select p right nonzero-fixed))
         (back (proof-proof-symmetric p selected)))
      (proof-proof-chain p result (list back)))))

(defun h3-book-power-identities-equal-power-zero-default-branch
    (typed exponent value index-test lib term fixed left i right search)
  (let* ((p (library-library-proof lib))
         (evidence (if index-test (list typed fixed index-test) (list typed fixed))))
    (proof-with-checked-results
        ((equation (h3-book-powers-power-equation lib term value evidence))
         (start (proof-proof-reflexive p left))
         (reduced (proof-proof-rewrite p start equation '(1 2 1)))
         (distinct (if (equal value *proof-zero*)
                       (cons nil search)
                     (h3-rewrite-search-prove search (proof-neg (proof-eq *proof-one* *proof-zero*)) nil)))
         (different (car distinct))
         (truth (if (equal value *proof-zero*)
                    (proof-with-checked-results ((same (proof-proof-reflexive p *proof-zero*)))
                      (h3-book-arithmetic-truth-value lib same))
                  (h3-rewrite-nil-value lib different)))
         (result (proof-proof-chain p reduced (list truth)))
         (opened (proof-proof-unfold p (list (proof-sym "IFIX" "ACL2") i)))
         (body (h3-book-power-identities-first-at opened 2))
         (selected (proof-proof-select p body typed))
         (identity (proof-proof-chain p opened (list selected)))
         (actual (h3-book-power-identities-first-at identity 2)))
      (if (not (equal actual exponent))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((selected (proof-proof-select p right fixed))
             (condition (proof-proof-rewrite p selected identity '(1 2 1 1)))
             (condition-value (h3-book-power-identities-first-at condition 2))
             (result-value (h3-book-power-identities-first-at result 2))
             (outcome-result (h3-rewrite-search-prove
                              (cdr distinct) (proof-eq condition-value result-value) evidence))
             (outcome (car outcome-result))
             (chain (proof-proof-chain p condition (list outcome)))
             (back (proof-proof-symmetric p chain))
             (result (proof-proof-chain p result (list back))))
          (cons result (cdr outcome-result)))))))

(defun h3-book-power-identities-equal-power-zero-default (fixed status lib i term left right)
  (declare (ignore status))
  (let ((p (library-library-proof lib))
        (test (list *proof-integerp* i))
        (at-zero (proof-eq i *proof-zero*))
        (search (h3-rewrite-search-init lib (list *proof-not*) nil nil 150 nil)))
    (proof-with-checked-results
        ((integer (proof-proof-assume p test t))
         (zero (proof-proof-assume p at-zero t))
         (zero-result (h3-book-power-identities-equal-power-zero-default-branch
                       integer i *proof-one* zero lib term fixed left i right search))
         (not-zero (proof-proof-assume p at-zero nil))
         (nonzero-result (h3-book-power-identities-equal-power-zero-default-branch
                          integer i *proof-zero* not-zero lib term fixed left i right (cdr zero-result)))
         (yes (proof-proof-cases p at-zero (car zero-result) (car nonzero-result)))
         (not-integer (proof-proof-assume p test nil))
         (no-result (h3-book-power-identities-equal-power-zero-default-branch
                     not-integer *proof-zero* *proof-one* nil lib term fixed left i right
                     (cdr nonzero-result))))
      (proof-proof-cases p test yes (car no-result)))))

(defun h3-book-power-identities-equal-power-zero (lib statement)
  (proof-with-checked-results
      ((sides (h3-book-power-identities-arguments statement 2))
       (term (proof-term-at (car sides) 1))
       (arguments (h3-book-power-identities-arguments term 2)))
    (let ((left (car sides))
          (right (cadr sides))
          (b (car arguments))
          (i (cadr arguments)))
      (car (h3-book-power-identities-with-base-forms
            lib lib b
            (typed nonzero)
            (cons (h3-book-power-identities-equal-power-zero-numeric typed nonzero lib b i right) lib)
            (fixed status)
            (cons (h3-book-power-identities-equal-power-zero-default fixed status lib i term left right)
                  lib))))))

(defun h3-book-power-identities-power-is-nonzero (lib goal context)
  (h3-book-power-identities-with-results lib
      ((equality (proof-term-at goal 1))
       (sides (h3-book-power-identities-arguments equality 2)))
    (let ((call (cond ((equal (cadr sides) *proof-zero*) (car sides))
                      ((equal (car sides) *proof-zero*) (cadr sides))
                      (t nil))))
      (if (not (proof-is-call call *h3-book-powers-expt*))
          (cons nil lib)
        (h3-book-power-identities-with-results lib
            ((base (proof-term-at call 1))
             (typed-result (h3-book-exponent-nonzero-base-with-context lib base context))
             (context (cdr typed-result))
             (lib (h3-book-order-bounds-lib context) :update)
             (typed (car typed-result))
             (index (proof-term-at call 2))
             (fact (h3-book-powers-nonzero-power lib (car typed) (cadr typed) index))
             (literal (proof-step-first fact)))
          (let ((search (h3-book-order-bounds-search context)))
            (cons (h3-rewrite-search-known search goal (list (cons literal fact))) lib)))))))

(defun h3-book-power-identities-reciprocal-power-at-literal (lib equation value)
  (let ((p (library-library-proof lib)))
    (proof-with-checked-results
        ((actual (h3-book-power-identities-first-at equation 1))
         (start (proof-proof-reflexive p (list *h3-book-arithmetic-divide* actual)))
         (reciprocal (proof-proof-rewrite p start equation '(1 2 1)))
         (number (proof-term-at value 1))
         (computed (proof-proof-compute p (list *h3-book-arithmetic-divide* value) number)))
      (proof-proof-chain p reciprocal (list computed)))))

(defun h3-book-power-identities-opposite-power-default
    (fixed status lib source opposite i negated integer numeric)
  (declare (ignore status))
  (let ((p (library-library-proof lib))
        (test (proof-eq i *proof-zero*))
        (opposite-zero (proof-eq (library-minus i) *proof-zero*)))
    (proof-with-checked-results
        ((zero (proof-proof-assume p test t))
         (start (proof-proof-reflexive p (library-minus i)))
         (emptied (proof-proof-rewrite p start zero '(1 2 1)))
         (compute-zero (proof-proof-compute p (library-minus *proof-zero*) 0))
         (emptied (proof-proof-chain p emptied (list compute-zero)))
         (first (h3-book-powers-power-equation lib opposite *proof-one* (list negated emptied fixed)))
         (second (h3-book-powers-power-equation lib source *proof-one* (list integer zero fixed)))
         (reciprocal (h3-book-power-identities-reciprocal-power-at-literal lib second *proof-one*))
         (back (proof-proof-symmetric p reciprocal))
         (yes (proof-proof-chain p first (list back)))
         (nonzero (proof-proof-assume p test nil))
         (start (proof-proof-reflexive p (library-minus (library-minus i))))
         (zero (proof-proof-assume p opposite-zero t))
         (impossible (proof-proof-rewrite p start zero '(1 2 1)))
         (compute-zero (proof-proof-compute p (library-minus *proof-zero*) 0))
         (impossible (proof-proof-chain p impossible (list compute-zero)))
         (citation (library-library-cite lib *h3-book-sums-double* (list i) nil))
         (identity (h3-book-arithmetic-fix-value lib i numeric))
         (double (proof-proof-chain p citation (list identity)))
         (impossible (proof-proof-rewrite p impossible double '(1 1)))
         (cut (proof-proof-cut p impossible nonzero))
         (opposite-nonzero (proof-proof-front p cut (proof-neg opposite-zero)))
         (first (h3-book-powers-power-equation lib opposite *proof-zero* (list negated opposite-nonzero fixed)))
         (second (h3-book-powers-power-equation lib source *proof-zero* (list integer nonzero fixed)))
         (reciprocal (h3-book-power-identities-reciprocal-power-at-literal lib second *proof-zero*))
         (back (proof-proof-symmetric p reciprocal))
         (no (proof-proof-chain p first (list back))))
      (proof-proof-cases p test yes no))))

(defun h3-book-power-identities-opposite-power-noninteger
    (lib type-test base i source opposite multiplied)
  (let ((p (library-library-proof lib))
        (number-test (list *library-numberp* i))
        (negated-test (list *proof-integerp* (library-minus i))))
    (h3-book-power-identities-with-results lib
        ((missing (proof-proof-assume p type-test nil))
         (typed (proof-proof-assume p number-test t))
         (opposite-integer (proof-proof-assume p negated-test t))
         (doubled (library-library-type-of lib (library-minus (library-minus i)) (list opposite-integer)))
         (citation (library-library-cite lib *h3-book-sums-double* (list i) nil))
         (identity (h3-book-arithmetic-fix-value lib i typed))
         (double (proof-proof-chain p citation (list identity)))
         (impossible (proof-proof-rewrite p doubled double '(1 1)))
         (cut (proof-proof-cut p impossible missing))
         (opposite-not-integer (proof-proof-front p cut (proof-neg negated-test)))
         (start (proof-proof-reflexive p multiplied))
         (times-negative (h3-book-signs-times-negative-one-with-library lib typed) :pair))
      (let ((p (library-library-proof lib)))
        (h3-book-power-identities-with-results lib
            ((transformed (proof-proof-rewrite p start times-negative '(1 2 2)))
             (equation (h3-book-powers-power-equation lib opposite *proof-one* (list opposite-not-integer)))
             (typed-case (proof-proof-chain p transformed (list equation)))
             (notnumber (proof-proof-assume p number-test nil))
             (rule (library-library-axiom lib "DEFAULT-*-2" (list *proof-neg-one* i)))
             (zero (proof-proof-modus-ponens p rule notnumber))
             (start (proof-proof-reflexive p multiplied))
             (absent (proof-proof-rewrite p start zero '(1 2 2)))
             (unit (h3-book-power-identities-power-index-zero lib base))
             (no-number (proof-proof-chain p absent (list unit)))
             (noninteger (proof-proof-cases p number-test typed-case no-number))
             (normal (h3-book-powers-power-equation lib source *proof-one* (list missing)))
             (reciprocal (h3-book-power-identities-reciprocal-power-at-literal lib normal *proof-one*))
             (back (proof-proof-symmetric p reciprocal)))
          (cons (proof-proof-chain p noninteger (list back)) lib))))))

(defun h3-book-power-identities-opposite-power (lib base i)
  (h3-book-power-identities-with-results lib ((sum-lemmas (h3-book-sums-lemmas-with-library lib) :pair))
    (let* ((p (library-library-proof lib))
           (source (h3-book-powers-power base i))
           (opposite (h3-book-powers-power base (library-minus i)))
           (multiplied (h3-book-powers-power base (list *proof-times* *proof-neg-one* i)))
           (type-test (list *proof-integerp* i)))
      (h3-book-power-identities-with-results lib
          ((integer (proof-proof-assume p type-test t))
           (rational (h3-book-numerator-as-rational lib integer))
           (numeric (h3-book-signs-number lib rational))
           (negated (library-library-type-of lib (library-minus i) (list integer)))
           (start (proof-proof-reflexive p multiplied))
           (times-negative (h3-book-signs-times-negative-one-with-library lib numeric) :pair)
           (move (proof-proof-rewrite (library-library-proof lib) start times-negative '(1 2 2)))
           (change (h3-book-power-identities-with-base-forms
                    lib lib base
                    (typed nz)
                    (h3-book-powers-power-opposite lib typed nz integer)
                    (fixed status)
                    (cons (h3-book-power-identities-opposite-power-default
                           fixed status lib source opposite i negated integer numeric)
                          lib)) :pair)
           (for-integers (proof-proof-chain (library-library-proof lib) move (list change)))
           (other (h3-book-power-identities-opposite-power-noninteger
                   lib type-test base i source opposite multiplied) :pair))
        (cons (proof-proof-cases (library-library-proof lib) type-test for-integers other) lib)))))

(defun h3-book-power-identities-power-inverse-exponent-theorem-reverse (lib left right base i)
  (let ((earlier (proof-sym "EXPT-MINUS-HELPER" "ACL2")))
    (h3-book-power-identities-with-results lib
        ((known (if (assoc-equal earlier (proof-proof-facts (library-library-proof lib)))
                    (cons (proof-proof-fact (library-library-proof lib) earlier
                                            (list (list (proof-sym "R" "ACL2") base)
                                                  (list (proof-sym "I" "ACL2") i)))
                          lib)
                  (h3-book-power-identities-opposite-power lib base i)) :pair))
      (let ((p (library-library-proof lib)))
        (h3-book-power-identities-with-results lib
            ((start (proof-proof-reflexive p right))
             (result (proof-proof-rewrite p start known '(1 2 1)))
             (opposite (h3-book-arithmetic-reciprocal-involution lib left))
             (numeric (h3-book-powers-numeric-power lib left))
             (fixed (h3-book-arithmetic-fix-value lib left numeric))
             (result (proof-proof-chain p result (list opposite fixed))))
          (cons (proof-proof-symmetric p result) lib))))))

(defun h3-book-power-identities-power-inverse-exponent-theorem (lib goal)
  (h3-book-power-identities-with-results lib ((sides (h3-book-power-identities-arguments goal 2)))
    (let ((left (car sides))
          (right (cadr sides)))
      (if (not (and (proof-is-call left *h3-book-powers-expt*)
                    (proof-is-call right *h3-book-arithmetic-divide*)))
          (cons nil lib)
        (h3-book-power-identities-with-results lib ((reciprocal (proof-term-at right 1)))
          (if (not (proof-is-call reciprocal *h3-book-powers-expt*))
              (cons nil lib)
            (h3-book-power-identities-with-results lib
                ((args (h3-book-power-identities-arguments reciprocal 2)))
              (if (equal left (h3-book-powers-power (car args) (list *proof-times* *proof-neg-one* (cadr args))))
                  (h3-book-power-identities-opposite-power lib (car args) (cadr args))
                (h3-book-power-identities-with-results lib
                    ((args (h3-book-power-identities-arguments left 2)))
                  (if (equal reciprocal (h3-book-powers-power (car args) (list *proof-times* *proof-neg-one* (cadr args))))
                      (h3-book-power-identities-power-inverse-exponent-theorem-reverse
                       lib left right (car args) (cadr args))
                    (cons nil lib)))))))))))

(defun h3-book-power-identities-exponent-sum-bounds (result terms nonnegative)
  (declare (xargs :measure (acl2-count terms)))
  (if (or (endp terms) (failure-p (car result)))
      result
    (let* ((term (car terms))
           (goal (if nonnegative (library-le *proof-zero* term) (library-le term *proof-zero*))))
      (h3-book-power-identities-exponent-sum-bounds
       (h3-book-order-bounds-bound-with-bounds (cdr result) goal) (cdr terms) nonnegative))))

(defun h3-book-power-identities-exponent-sum-sign-result (goal result nonnegative)
  (let* ((value (car result))
         (context (cdr result))
         (lib (h3-book-order-bounds-lib context)))
    (cond ((h3-rewrite-unproved-p value) (cons nil lib))
          ((failure-p value) (cons value lib))
          (t (h3-book-power-identities-totalized-power-addition lib goal context nonnegative)))))

(defun h3-book-power-identities-exponent-sum-signs (goal context terms)
  (let ((positive (h3-book-power-identities-exponent-sum-bounds (cons t context) terms t)))
    (if (h3-rewrite-unproved-p (car positive))
        (h3-book-power-identities-exponent-sum-sign-result
         goal (h3-book-power-identities-exponent-sum-bounds (cons t (cdr positive)) terms nil) nil)
      (h3-book-power-identities-exponent-sum-sign-result goal positive t))))

(defun h3-book-power-identities-exponent-sum (lib goal context)
  (h3-book-power-identities-with-results lib
      ((sides (h3-book-power-identities-arguments goal 2))
       (total (proof-term-at (car sides) 2)))
    (if (not (proof-is-call total *proof-plus*))
        (cons nil lib)
      (h3-book-power-identities-with-results lib
          ((args (h3-book-power-identities-arguments (car sides) 2))
           (indices (h3-book-power-identities-arguments total 2)))
        (let* ((base (car args))
               (i (car indices))
               (j (cadr indices))
               (right (cadr sides))
               (product (list *proof-times* (h3-book-powers-power base i) (h3-book-powers-power base j)))
               (zero (proof-eq total *proof-zero*))
               (fixed (proof-eq (list *h3-book-power-identities-fix* base) *proof-zero*))
               (context (h3-book-order-bounds-with-library context lib)))
          (cond ((or (equal right (proof-ite zero *proof-one* product))
                     (equal right (proof-ite zero *proof-one* (proof-ite fixed *proof-zero* product))))
                 (h3-book-power-identities-totalized-power-addition lib goal context nil))
                ((equal right product)
                 (h3-book-power-identities-exponent-sum-signs goal context indices))
                (t (cons nil lib))))))))

(defun h3-book-power-identities-all-powers-p (terms)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      t
    (and (proof-is-call (car terms) *h3-book-powers-expt*)
         (h3-book-power-identities-all-powers-p (cdr terms)))))

(defun h3-book-power-identities-is-totalized-power-product (goal)
  (proof-with-checked-results ((sides (h3-book-power-identities-arguments goal 2)))
    (let ((left (car sides))
          (right (cadr sides)))
      (if (not (and (proof-is-call left *proof-times*)
                    (h3-book-power-identities-all-powers-p (cdr left))))
          nil
        (proof-with-checked-results
            ((first (proof-term-at left 1))
             (args (h3-book-power-identities-arguments first 2))
             (second (proof-term-at left 2))
             (second-base (proof-term-at second 1)))
          (let ((base (car args))
                (i (cadr args)))
            (if (not (equal second-base base))
                nil
              (proof-with-checked-results ((j (proof-term-at second 2)))
                (equal right
                       (proof-ite (proof-ite (proof-eq i *proof-zero*) (proof-eq j *proof-zero*) *proof-false*)
                                  *proof-one*
                                  (proof-ite (proof-eq (list *h3-book-power-identities-fix* base) *proof-zero*)
                                             *proof-zero*
                                             (h3-book-powers-power base (library-plus i j)))))))))))))

(defun h3-book-power-identities-power-default-exponent (lib goal context)
  (proof-with-checked-results
      ((sides (h3-book-power-identities-arguments goal 2))
       (args (h3-book-power-identities-arguments (car sides) 2)))
    (let* ((call (car sides))
           (value (cadr sides))
           (base (car args))
           (index (cadr args))
           (test (list *proof-integerp* index))
           (context (h3-book-order-bounds-with-library context lib))
           (evidence (h3-book-order-bounds-evidence context))
           (missing (table-get evidence (proof-neg test) nil)))
      (cond ((and (equal value *proof-one*) missing)
             (h3-book-powers-power-equation lib call *proof-one* (list missing)))
            ((and (equal base *proof-zero*) (equal value *proof-zero*))
             (let ((whole (table-get evidence test nil)))
               (proof-with-checked-results
                   ((nonzero (h3-rewrite-search-known (h3-book-order-bounds-search context)
                                                      (proof-neg (proof-eq index *proof-zero*)) evidence)))
                 (if (and whole nonzero)
                     (proof-with-checked-results
                         ((numeric (h3-book-power-identities-prove lib (list *library-numberp* *proof-zero*)))
                          (fixed (h3-book-arithmetic-fix-value lib *proof-zero* numeric)))
                       (h3-book-powers-power-equation lib call *proof-zero* (list whole nonzero fixed)))
                   nil))))
            (t nil)))))

(defun h3-book-power-identities-theorem-conjunct (lib goal)
  (h3-book-power-identities-with-results lib
      ((first (h3-book-power-identities-special-power lib (cadr goal)) :pair)
       (second (h3-book-power-identities-special-power lib (caddr goal)) :pair))
    (cons (if (and first second) (h3-book-floor-conjunct-proof lib (list first second)) nil) lib)))

(defun h3-book-power-identities-theorem-context (lib guard)
  (proof-with-checked-results ((evidence (proof-proof-assume (library-library-proof lib) guard t)))
    (h3-book-order-bounds-init lib (list evidence))))

(defun h3-book-power-identities-theorem-nonzero (lib guard goal)
  (h3-book-power-identities-with-results lib ((equality (proof-term-at goal 1)))
    (if (not (proof-is-call equality *proof-equal*))
        (cons nil lib)
      (h3-book-power-identities-with-results lib
          ((context (h3-book-power-identities-theorem-context lib guard))
           (proof (h3-book-power-identities-power-is-nonzero lib goal context) :pair))
        (cons (if proof (h3-rewrite-implication lib guard proof) nil) lib)))))

(defun h3-book-power-identities-theorem-equal-zero (lib goal left right)
  (if (not (proof-is-call left *proof-equal*))
      nil
    (proof-with-checked-results ((term (proof-term-at left 1)))
      (if (not (proof-is-call term *h3-book-powers-expt*))
          nil
        (proof-with-checked-results ((value (proof-term-at left 2)))
          (if (not (equal value *proof-zero*))
              nil
            (proof-with-checked-results ((args (h3-book-power-identities-arguments term 2)))
              (let ((base (car args))
                    (index (cadr args)))
                (if (equal right
                           (proof-ite (proof-eq (list *h3-book-power-identities-fix* base) *proof-zero*)
                                      (proof-neg (proof-eq (list (proof-sym "IFIX" "ACL2") index) *proof-zero*))
                                      *proof-false*))
                    (h3-book-power-identities-equal-power-zero lib goal)
                  nil)))))))))

(defun h3-book-power-identities-theorem-guarded (lib guard goal left)
  (if (proof-is-call left *h3-book-powers-expt*)
      (h3-book-power-identities-with-results lib
          ((context (h3-book-power-identities-theorem-context lib guard))
           (proof (h3-book-power-identities-exponent-sum lib goal context) :pair))
        (cons (or proof (h3-book-power-identities-power-default-exponent lib goal context)) lib))
    (h3-book-power-identities-with-results lib ((product (h3-book-power-identities-is-totalized-power-product goal)))
      (if (not product)
          (cons nil lib)
        (h3-book-power-identities-with-results lib ((context (h3-book-power-identities-theorem-context lib guard)))
          (h3-book-power-identities-totalized-power-product lib goal context))))))

(defun h3-book-power-identities-theorem-equation (lib guard goal)
  (h3-book-power-identities-with-results lib
      ((sides (h3-book-power-identities-arguments goal 2))
       (proof (h3-book-power-identities-special-power lib goal) :pair)
       (proof (if proof (cons proof lib)
                (h3-book-power-identities-power-inverse-exponent-theorem lib goal)) :pair)
       (proof (or proof (h3-book-power-identities-theorem-equal-zero lib goal (car sides) (cadr sides)))))
    (h3-book-power-identities-with-results lib
        ((proof (if (and (not proof) (h3-book-power-identities-argument-present-p guard))
                    (h3-book-power-identities-theorem-guarded lib guard goal (car sides))
                  (cons proof lib)) :pair))
      (cons (if (and (h3-book-power-identities-argument-present-p guard) proof)
                (h3-rewrite-implication lib guard proof)
              proof)
            lib))))

(defun h3-book-power-identities-power-identities-theorem (lib formula)
  (h3-book-power-identities-with-results lib
      ((parts (if (proof-is-call formula *library-implies*)
                  (h3-book-power-identities-arguments formula 2)
                (list nil formula))))
    (let ((guard (car parts))
          (goal (cadr parts)))
      (cond
        ((and (not (h3-book-power-identities-argument-present-p guard)) (proof-is-call goal *proof-if*))
         (h3-book-power-identities-with-results lib ((alternative (proof-term-at goal 3)))
           (if (equal alternative *proof-false*)
               (h3-book-power-identities-theorem-conjunct lib goal)
             (cons nil lib))))
        ((and (h3-book-power-identities-argument-present-p guard) (proof-is-call goal *proof-not*))
         (h3-book-power-identities-theorem-nonzero lib guard goal))
        ((proof-is-call goal *proof-equal*)
         (h3-book-power-identities-theorem-equation lib guard goal))
        (t (cons nil lib))))))
