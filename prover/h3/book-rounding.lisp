(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-book-rounding-fl* (proof-sym "FL" "ACL2"))
(defconst *h3-book-rounding-two* (proof-quote 2))
(defconst *h3-book-rounding-half* (proof-quote '("ratio" 1 2)))
(defconst *h3-book-rounding-halving* "H3-BOOK-FLOOR-HALVING")

; A two-name binding takes the value and object from a successful pair.
(defmacro h3-book-rounding-with-results (bindings result)
  (if (endp bindings)
      result
    (let* ((binding (car bindings))
           (names (car binding))
           (later (cdr bindings)))
      (if (consp names)
          `(proof-with-checked-results ((h3-book-rounding-pair ,(cadr binding)))
             (let ((,(car names) (car h3-book-rounding-pair))
                   (,(cadr names) (cdr h3-book-rounding-pair)))
               (h3-book-rounding-with-results ,later ,result)))
        `(proof-with-checked-results (,binding)
           (h3-book-rounding-with-results ,later ,result))))))

(defun h3-book-rounding-library-result (result lib)
  (if (failure-p result) (cons result lib) result))

(defun h3-book-rounding-checked-pair (result)
  (if (failure-p (car result)) (car result) result))

; On failure, return the Library reached at that call.
(defmacro h3-book-rounding-with-library (lib bindings result)
  (if (endp bindings)
      `(h3-book-rounding-library-result ,result ,lib)
    (let* ((binding (car bindings))
           (names (car binding))
           (next `(h3-book-rounding-with-library ,lib ,(cdr bindings) ,result)))
      (cond
       ((consp names)
        (let ((value (car names))
              (object (cadr names)))
          `(let ((h3-book-rounding-pair ,(cadr binding)))
             (if (failure-p h3-book-rounding-pair)
                 (cons h3-book-rounding-pair ,lib)
               (let* ((,value (car h3-book-rounding-pair))
                      (,object (cdr h3-book-rounding-pair))
                      ,@(and (not (eq object lib))
                             `((,lib (h3-book-order-bounds-lib ,object)))))
                 (if (failure-p ,value) (cons ,value ,lib) ,next))))))
       ((eq names lib)
        `(let ((h3-book-rounding-next-library ,(cadr binding)))
           (if (failure-p h3-book-rounding-next-library)
               (cons h3-book-rounding-next-library ,lib)
             (let ((,lib h3-book-rounding-next-library)) ,next))))
       (t
        `(let (,binding)
           (if (failure-p ,names) (cons ,names ,lib) ,next)))))))

(defun h3-book-rounding-step-first (step)
  (if (not step)
      '(:failure "failure" "")
    (proof-step-first step)))

(defun h3-book-rounding-step-at (step index)
  (proof-with-checked-results ((literal (h3-book-rounding-step-first step)))
    (proof-term-at literal index)))

(defun h3-book-rounding-tail-of-size (term size)
  (h3-book-quotient-tail-of-size term size))

(defun h3-book-rounding-argument-present-p (value)
  (and value (not (equal value 0)) (not (equal value ""))))

(defun h3-book-rounding-fl-interval-with-library (lib rational)
  (h3-book-rounding-with-library lib
      ((value (h3-book-rounding-step-at rational 1))
       (floor (list *h3-book-floor-floor* value *proof-one*))
       (proof (library-library-proof lib))
       (opened (proof-proof-unfold proof (list *h3-book-rounding-fl* value)))
       (numeric (h3-book-signs-number lib rational))
       (ratio (h3-book-floor-ratio-by-one lib value numeric))
       (ratio-type (library-library-transport-argument lib rational ratio 1))
       ((interval lib) (h3-book-floor-floor-bounds-with-library lib floor ratio-type))
       (interval (h3-book-floor-change-interval-value lib interval ratio))
       (proof (library-library-proof lib))
       (result (proof-proof-symmetric proof opened))
       (whole (proof-proof-rewrite proof (car interval) result '(1 1)))
       (lower (proof-proof-rewrite proof (cadr interval) result '(1 1 2)))
       (upper (proof-proof-rewrite proof (caddr interval) result '(1 2 2))))
    (cons (list whole lower upper) lib)))

(defun h3-book-rounding-rewrite-ratio-operands
    (proof operands ratio cancellation positive position equation)
  (if (endp operands)
      equation
    (proof-with-checked-results
        ((equation (if (equal (car operands) ratio)
                       (proof-proof-rewrite proof equation cancellation
                                            (list 1 2 (if positive position (- 3 position))))
                     equation)))
      (h3-book-rounding-rewrite-ratio-operands
       proof (cdr operands) ratio cancellation positive (1+ position) equation))))

(defun h3-book-rounding-scale-comparison (lib comparison d-type signs)
  (if (integerp comparison)
      '(:failure "failure" "")
    (let ((operands (cdr comparison)))
      (case (len operands)
        (0 '(:failure "failure" ""))
        (1 '(:failure "failure" ""))
        (2 (h3-book-quotient-scale-order-with-library lib (car operands) (cadr operands) d-type signs nil))
        (3 '(:failure "failure" ""))
        (otherwise
         '(:failure "failure" ""))))))

(defun h3-book-rounding-multiply-ratio-bound-with-library (lib given n-type d-type signs)
  (h3-book-rounding-with-library lib
      ((n (h3-book-rounding-step-at n-type 1))
       (d (h3-book-rounding-step-at d-type 1))
       (ratio (h3-book-floor-floor-ratio n d))
       (literal (h3-book-rounding-step-first given))
       (weak (proof-is-call literal *proof-not*))
       (comparison (if weak (proof-term-at literal 1) literal))
       ((equation lib) (h3-book-rounding-scale-comparison lib comparison d-type signs))
       (numeric (h3-book-signs-number lib d-type))
       (law (h3-book-arithmetic-inverse lib d numeric (h3-book-signs-signs-zero signs)))
       (n-numeric (h3-book-signs-number lib n-type))
       (cancellation (h3-book-quotient-clear-reciprocal lib ratio d law n-numeric))
       (proof (library-library-proof lib))
       (equation (h3-book-rounding-rewrite-ratio-operands
                  proof (cdr comparison) ratio cancellation
                  (< 0 (h3-book-signs-signs-sign signs)) 1 equation))
       (rewritten (proof-proof-rewrite proof given equation (if weak '(1 1) '(1))))
       (step (proof-proof-tidy proof rewritten)))
    (cons step lib)))

(defun h3-book-rounding-floor-of-nonnumeric-or-complex
    (lib call not-rational d-type d-nonzero)
  (proof-with-checked-results
      ((parts (h3-book-rounding-tail-of-size call 2))
       (n (car parts))
       (d (cadr parts))
       (test (list *library-numberp* n))
       (proof (library-library-proof lib))
       (numeric (proof-proof-assume proof test t))
       (missing (proof-proof-assume proof test nil))
       (ratio (h3-book-floor-floor-ratio n d))
       (rat-test (list *library-rationalp* ratio))
       (hypothetical (proof-proof-assume proof rat-test t))
       (d-numeric (h3-book-signs-number lib d-type))
       (law (h3-book-arithmetic-inverse lib d d-numeric d-nonzero))
       (cancelled (h3-book-quotient-clear-reciprocal lib ratio d law numeric))
       (product (h3-book-signs-rational-product lib hypothetical d-type))
       (contradicted (proof-proof-rewrite proof product cancelled '(1 1)))
       (fault (proof-proof-cut proof contradicted not-rational))
       (no-rat (proof-proof-front proof fault (proof-neg rat-test)))
       (yes (h3-book-floor-floor-default lib call no-rat))
       (no (h3-book-floor-floor-zero-by-argument lib call missing)))
    (proof-proof-cases proof test yes no)))

(defun h3-book-rounding-divide-floor (lib term divisor)
  (proof-with-checked-results
      ((reciprocal (list *h3-book-arithmetic-divide* divisor))
       (target (list *h3-book-floor-floor* term divisor))
       (proof (library-library-proof lib))
       (actual (proof-proof-unfold
                proof (list *h3-book-rounding-fl* (list *proof-times* reciprocal term))))
       (ratio (library-library-axiom lib "COMMUTATIVITY-OF-*" (list reciprocal term)))
       (actual (proof-proof-rewrite proof actual ratio '(1 2 1)))
       (through (h3-book-floor-floor-through-ratio lib target))
       (back (proof-proof-symmetric proof through)))
    (proof-proof-chain proof actual (list back))))

(defun h3-book-rounding-half-floor (lib term)
  (proof-with-checked-results
      ((call (list *h3-book-rounding-fl* (list *proof-times* *h3-book-rounding-half* term)))
       (proof (library-library-proof lib))
       (computed (proof-proof-compute
                  proof (list *h3-book-arithmetic-divide* *h3-book-rounding-two*)
                  (cadr *h3-book-rounding-half*)))
       (reciprocal (proof-proof-symmetric proof computed))
       (identity (proof-proof-reflexive proof call))
       (replaced (proof-proof-rewrite proof identity reciprocal '(1 2 1 1)))
       (divided (h3-book-rounding-divide-floor lib term *h3-book-rounding-two*)))
    (proof-proof-chain proof replaced (list divided))))

(defun h3-book-rounding-floor-divisor-shift-with-library (lib term d-int d-positive)
  (h3-book-rounding-with-library lib
      ((divisor (h3-book-rounding-step-at d-int 1))
       (d-type (h3-book-numerator-as-rational lib d-int))
       (d-numeric (h3-book-signs-number lib d-type))
       ((signs lib) (h3-book-signs-sign-evidence-with-library lib d-numeric 1 d-positive))
       (inner (list *h3-book-rounding-fl* term))
       (target (list *h3-book-floor-floor* term divisor))
       (candidate (list *h3-book-floor-floor* inner divisor))
       (test (list *library-rationalp* term))
       (rational (proof-proof-assume (library-library-proof lib) test t))
       ((inner-interval lib) (h3-book-rounding-fl-interval-with-library lib rational))
       (i-int (car inner-interval))
       (i-rat (h3-book-numerator-as-rational lib i-int))
       (quotient (h3-book-floor-floor-ratio inner divisor))
       (bounds (h3-book-order-bounds-init lib (list i-rat d-type)))
       (q-rat (h3-book-order-bounds-rational bounds quotient))
       ((q-interval lib) (h3-book-floor-floor-bounds-with-library lib candidate q-rat))
       (q-int (car q-interval))
       ((scaled-lo lib)
        (h3-book-rounding-multiply-ratio-bound-with-library lib (cadr q-interval) i-rat d-type signs))
       ((scaled-hi lib)
        (h3-book-rounding-multiply-ratio-bound-with-library lib (caddr q-interval) i-rat d-type signs))
       (upper-term (h3-book-rounding-step-at scaled-hi 2))
       (upper-int (library-library-type-of lib upper-term (list q-int d-int)))
       ((gap lib) (h3-book-floor-integer-gap-with-library lib i-int upper-int scaled-hi))
       (bounds (h3-book-order-bounds-init
                lib (list i-int q-int rational d-type d-positive
                          (cadr inner-interval) (caddr inner-interval) scaled-lo gap)))
       ((lower bounds)
        (h3-book-order-bounds-bound-with-bounds bounds (library-le (list *proof-times* candidate divisor) term)))
       ((upper bounds) (h3-book-order-bounds-bound-with-bounds bounds (library-lt term upper-term)))
       (bounds (h3-book-order-bounds-init lib (list q-int rational d-type d-positive lower upper)))
       (target-ratio (h3-book-floor-floor-ratio term divisor))
       ((candidate-lo bounds)
        (h3-book-order-quotient-bound-with-bounds lib (library-le candidate target-ratio) bounds 0))
       ((candidate-hi bounds)
        (h3-book-order-quotient-bound-with-bounds
         lib (library-lt target-ratio (library-plus *proof-one* candidate)) bounds 0))
       (ratio-type (h3-book-order-bounds-rational bounds target-ratio))
       ((target-interval lib) (h3-book-floor-floor-bounds-with-library lib target ratio-type))
       ((exact lib) (h3-book-floor-same-floor-interval-with-library
                     lib ratio-type (list q-int candidate-lo candidate-hi) target-interval))
       (proof (library-library-proof lib))
       (missing (proof-proof-assume proof test nil))
       (one (car (h3-rewrite-search-prove
                  (h3-rewrite-search-init lib nil nil nil 150 nil)
                  (list *library-rationalp* *proof-one*) nil)))
       (unique (car (h3-rewrite-search-prove
                     (h3-rewrite-search-init lib nil nil nil 150 nil)
                     (proof-neg (proof-eq *proof-one* *proof-zero*)) nil)))
       (before (h3-book-rounding-floor-of-nonnumeric-or-complex
                lib (list *h3-book-floor-floor* term *proof-one*) missing one unique))
       (opened (proof-proof-unfold proof inner))
       (before (proof-proof-chain proof opened (list before)))
       (identity (proof-proof-reflexive proof candidate))
       (candidate-zero (proof-proof-rewrite proof identity before '(1 2 1)))
       (zero-call (h3-book-rounding-step-at candidate-zero 2))
       (zero (h3-book-floor-floor-zero-by-argument lib zero-call nil))
       (candidate-zero (proof-proof-chain proof candidate-zero (list zero)))
       (target-zero (h3-book-rounding-floor-of-nonnumeric-or-complex
                     lib target missing d-type (h3-book-signs-signs-zero signs)))
       (reversed (proof-proof-symmetric proof target-zero))
       (absent (proof-proof-chain proof candidate-zero (list reversed)))
       (step (proof-proof-cases proof test exact absent)))
    (cons step lib)))

(defun h3-book-rounding-floor-divisor-shift (lib term d-int d-positive)
  (h3-book-rounding-checked-pair
   (h3-book-rounding-floor-divisor-shift-with-library lib term d-int d-positive)))

(defun h3-book-rounding-floor-halving-with-library (lib)
  (h3-book-rounding-with-library lib
      ((search (h3-rewrite-search-init lib nil nil nil 150 nil))
       (int-result (h3-rewrite-search-prove
                    search (list *proof-integerp* *h3-book-rounding-two*) nil))
       (integer (car int-result))
       (positive (car (h3-rewrite-search-prove
                       (cdr int-result) (library-lt *proof-zero* *h3-book-rounding-two*) nil)))
       ((shift lib) (h3-book-rounding-floor-divisor-shift-with-library lib *library-x* integer positive))
       (inner (h3-book-rounding-half-floor lib (list *h3-book-rounding-fl* *library-x*)))
       (outer (h3-book-rounding-half-floor lib *library-x*))
       (proof (library-library-proof lib))
       (back (proof-proof-symmetric proof outer))
       (step (proof-proof-chain proof inner (list shift back))))
    (cons step lib)))

(defun h3-book-rounding-fl-at-integer (lib integer)
  (proof-with-checked-results
      ((value (h3-book-rounding-step-at integer 1))
       (proof (library-library-proof lib))
       (expansion (proof-proof-unfold proof (list *h3-book-rounding-fl* value)))
       (rational (h3-book-numerator-as-rational lib integer))
       (numeric (h3-book-signs-number lib rational))
       (identity (h3-book-floor-ratio-by-one lib value numeric))
       (ratio-type (library-library-transport-argument lib integer identity 1))
       (call (h3-book-rounding-step-at expansion 2))
       (exact (h3-book-floor-exact-floor lib call ratio-type)))
    (proof-proof-chain proof expansion (list exact identity))))

(defun h3-book-rounding-clear-scaled-integer (lib value context scaled scale factor fact)
  (proof-with-checked-results
      ((denominator (proof-quote (/ factor)))
       (product (list *proof-times* denominator scaled))
       (grouped-factor (list *proof-times* denominator scale))
       (grouped (list *proof-times* grouped-factor value))
       (equality (h3-book-arithmetic-associative-equal lib product grouped))
       (proof (library-library-proof lib))
       (computed (proof-proof-compute proof grouped-factor 1))
       (equality (proof-proof-rewrite proof equality computed '(1 2 1)))
       (unit (library-library-axiom lib "UNICITY-OF-1" (list value)))
       (numeric (h3-book-order-bounds-numeric context value))
       (fixed (h3-book-arithmetic-fix-value lib value numeric))
       (equality (proof-proof-chain proof equality (list unit fixed)))
       (d-type (car (h3-rewrite-search-prove
                     (h3-rewrite-search-init lib nil nil nil 150 nil)
                     (list *proof-integerp* denominator) nil)))
       (rule (proof-proof-fact proof "integerp-binary-*"
                               (list (list *library-x* denominator) (list *library-y* scaled))))
       (both (h3-book-floor-conjunct-proof lib (list d-type fact)))
       (whole (proof-proof-modus-ponens proof rule both))
       (rewritten (proof-proof-rewrite proof whole equality '(1 1))))
    (proof-proof-tidy proof rewritten)))

(defun h3-book-rounding-integer-divisor-premise (term value)
  (if (not (proof-is-call term *proof-integerp*))
      nil
    (proof-with-checked-results ((scaled (proof-term-at term 1)))
      (if (and (proof-is-call scaled *proof-times*)
               (member-equal value (cdr scaled)))
          (proof-with-checked-results
              ((scale (proof-term-at scaled (if (equal (cadr scaled) value) 2 1))))
            (if (not (proof-is-call scale *proof-quote*))
                nil
              (proof-with-checked-results
                  ((datum (proof-term-at scale 1))
                   (factor (h3-rewrite-rational-value datum)))
                (and factor
                     (not (equal factor 0))
                     (or (equal (numerator factor) 1) (equal (numerator factor) -1))
                     (list scaled scale factor)))))
        nil))))

(defun h3-book-rounding-clear-integer-divisor-in-evidence (lib value context evidence)
  (if (endp evidence)
      nil
    (proof-with-checked-results
        ((premise (h3-book-rounding-integer-divisor-premise (caar evidence) value)))
      (if premise
          (h3-book-rounding-clear-scaled-integer
           lib value context (car premise) (cadr premise) (caddr premise) (cdar evidence))
        (h3-book-rounding-clear-integer-divisor-in-evidence lib value context (cdr evidence))))))

(defun h3-book-rounding-clear-integer-divisor (lib value context)
  (h3-book-rounding-clear-integer-divisor-in-evidence
   lib value (h3-book-order-bounds-with-library context lib)
   (h3-book-order-bounds-evidence context)))

(defun h3-book-rounding-integer-floor-from-guard (lib value guard)
  (if (not (h3-book-rounding-argument-present-p guard))
      (cons nil lib)
    (proof-with-checked-results
        ((given (proof-proof-assume (library-library-proof lib) guard t))
         (context (h3-book-order-bounds-init lib (list given)))
         (step (h3-book-rounding-clear-integer-divisor lib value context)))
      (cons step lib))))

(defun h3-book-rounding-integer-floor-result-with-library (lib value guard)
  (h3-book-rounding-with-library lib nil
    (cond
     ((proof-is-call value *h3-book-floor-floor*)
      (h3-book-floor-floor-is-integer-with-library lib value))
     ((proof-is-call value *h3-book-rounding-fl*)
      (h3-book-rounding-with-library lib
          ((clause (proof-proof-unfold (library-library-proof lib) value))
           (opened (h3-book-rounding-step-at clause 2)))
        (if (proof-is-call opened *h3-book-floor-floor*)
            (h3-book-rounding-with-library lib
                (((integer lib) (h3-book-floor-floor-is-integer-with-library lib opened))
                 (step (library-library-transport-argument lib integer clause 1)))
              (cons step lib))
          (h3-book-rounding-integer-floor-from-guard lib value guard))))
     (t (h3-book-rounding-integer-floor-from-guard lib value guard)))))

(defun h3-book-rounding-integer-floor-result (lib value guard)
  (h3-book-rounding-checked-pair
   (h3-book-rounding-integer-floor-result-with-library lib value guard)))

(defun h3-book-rounding-guarded-step-with-library (lib guard step)
  (cons (if (and (h3-book-rounding-argument-present-p guard) step)
            (h3-rewrite-implication lib guard step)
          step)
        lib))

(defun h3-book-rounding-halving-lemma (lib)
  (let ((name (proof-sym (string-append "SELF-" *h3-book-rounding-halving*) "ACL2"))
        (proof (library-library-proof lib)))
    (cond
     ((assoc-equal name (proof-proof-facts proof)) (cons nil lib))
     ((not (assoc-equal *h3-book-rounding-fl* (proof-proof-definitions proof)))
      (cons *h3-rewrite-unproved* lib))
     (t (h3-book-rounding-with-library lib
            (((step lib) (h3-book-rounding-floor-halving-with-library lib))
             (claim (proof-step-first step))
             (lib (library-library-lemma lib *h3-book-rounding-halving* claim step nil)))
          (cons nil lib))))))

(defun h3-book-rounding-halving-goal (lib guard goal)
  (if (not (proof-is-call goal *proof-equal*))
      (cons nil lib)
    (proof-with-checked-results ((right-floor (proof-term-at goal 2)))
      (if (not (proof-is-call right-floor *h3-book-rounding-fl*))
          (cons nil lib)
        (proof-with-checked-results ((right (proof-term-at right-floor 1)))
          (if (not (proof-is-call right *proof-times*))
              (cons nil lib)
            (proof-with-checked-results ((coefficient (proof-term-at right 1)))
              (if (not (equal coefficient *h3-book-rounding-half*))
                  (cons nil lib)
                (proof-with-checked-results
                    ((value (proof-term-at right 2))
                     (left (proof-term-at goal 1)))
                  (if (not (equal left
                                  (list *h3-book-rounding-fl*
                                        (list *proof-times* *h3-book-rounding-half*
                                              (list *h3-book-rounding-fl* value)))))
                      (cons nil lib)
                    (h3-book-rounding-with-library lib
                        (((registered lib) (h3-book-rounding-halving-lemma lib))
                         (step (library-library-cite lib *h3-book-rounding-halving* (list value) nil)))
                      (h3-book-rounding-guarded-step-with-library lib guard step))))))))))))

(defun h3-book-rounding-integer-equality (lib guard goal)
  (if (not (and (h3-book-rounding-argument-present-p guard) (proof-is-call goal *proof-equal*)))
      nil
    (proof-with-checked-results ((left (proof-term-at goal 1)))
      (if (not (proof-is-call left *h3-book-rounding-fl*))
          nil
        (proof-with-checked-results
            ((input (proof-term-at left 1))
             (value (proof-term-at goal 2)))
          (if (not (equal input value))
              nil
            (proof-with-checked-results
                ((given (proof-proof-assume (library-library-proof lib) guard t))
                 (context (h3-book-order-bounds-init lib (list given))))
              (let ((integer (table-get (h3-book-order-bounds-evidence context)
                                          (list *proof-integerp* value) nil)))
                (and integer (h3-book-rounding-fl-at-integer lib integer))))))))))

(defun h3-book-rounding-rounding-theorem-with-library (lib formula)
  (h3-book-rounding-with-library lib
      ((implies (proof-is-call formula *library-implies*))
       (parts (and implies (proof-list-of-length (cdr formula) 2)))
       (guard (car parts))
       (goal (if implies (cadr parts) formula)))
    (if (proof-is-call goal *proof-integerp*)
        (h3-book-rounding-with-library lib
            ((value (proof-term-at goal 1))
             ((step lib) (h3-book-rounding-integer-floor-result-with-library lib value guard)))
          (h3-book-rounding-guarded-step-with-library lib guard step))
      (h3-book-rounding-with-library lib ((step (h3-book-rounding-integer-equality lib guard goal)))
        (if step
            (h3-book-rounding-guarded-step-with-library lib guard step)
          (h3-book-rounding-halving-goal lib guard goal))))))

