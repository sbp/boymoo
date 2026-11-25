(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

; Keep the Library at a failed attempt so that a search can continue with
; the lemmas already added by that attempt.
(defmacro h3-book-translation-with-library (library bindings result)
  (if (endp bindings)
      result
    (let ((name (caar bindings))
          (form (cadar bindings))
          (kind (caddar bindings))
          (rest (cdr bindings)))
      (case kind
        (:library
         `(let ((translation-pair ,form))
            (if (failure-p translation-pair)
                (cons translation-pair ,library)
              (let ((,name (car translation-pair))
                    (,library (cdr translation-pair)))
                (if (failure-p ,name)
                    (cons ,name ,library)
                  (h3-book-translation-with-library ,library ,rest ,result))))))
        (otherwise
         `(let ((,name ,form))
            (if (failure-p ,name)
                (cons ,name ,library)
              (h3-book-translation-with-library ,library ,rest ,result))))))))

(defun h3-book-translation-result (result)
  (if (failure-p (car result)) (car result) result))

(defun h3-book-translation-retryable-p (result)
  (and (failure-p result)
       (member-equal (cadr result) '("unproved" "different-normal-forms" "wrong-sum-arity" "value"))
       t))

(defund h3-book-translation-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h3-book-translation-sum-equality-form (library sums term evidence)
  (proof-with-checked-results
      ((normal (h3-book-arithmetic-normal-form library term))
       (ordered (or normal (library-inherited proof-proof-reflexive library term)))
       (value (h3-book-translation-step-at ordered 2))
       (form (h3-book-sums-book-sums-sum-form sums value evidence)))
    (library-inherited proof-proof-chain library ordered (list form))))

(defun h3-book-translation-sum-equality-with-library (library first second evidence)
  (h3-book-translation-with-library library
      ((registered (h3-book-sums-lemmas-with-library library) :library)
       (sums (h3-book-sums-book-sums-init library))
       (left (h3-book-translation-sum-equality-form library sums first evidence))
       (right (h3-book-translation-sum-equality-form library sums second evidence))
       (left-value (h3-book-translation-step-at left 2))
       (right-value (h3-book-translation-step-at right 2)))
    (cons (if (equal left-value right-value)
              (proof-with-checked-results
                  ((reversed (library-inherited proof-proof-symmetric library right)))
                (library-inherited proof-proof-chain library left (list reversed)))
            '(:failure "unproved" ""))
          library)))

(defun h3-book-translation-sum-equality (library first second evidence)
  (h3-book-translation-result
   (h3-book-translation-sum-equality-with-library library first second evidence)))

(defund h3-book-translation-sum-ratio (library first second divisor)
  (let ((total (library-plus first second))
        (reciprocal (list *h3-book-arithmetic-divide* divisor)))
    (proof-with-checked-results
        ((commuted (library-library-axiom library "COMMUTATIVITY-OF-*" (list total reciprocal)))
         (distributed (library-library-axiom library "DISTRIBUTIVITY" (list reciprocal first second)))
         (equation (library-inherited proof-proof-chain library commuted (list distributed)))
         (first-order (library-library-axiom library "COMMUTATIVITY-OF-*" (list reciprocal first)))
         (equation (library-inherited proof-proof-rewrite library equation first-order '(1 2 1)))
         (second-order (library-library-axiom library "COMMUTATIVITY-OF-*" (list reciprocal second)))
         (equation (library-inherited proof-proof-rewrite library equation second-order '(1 2 2))))
      (library-inherited proof-proof-tidy library equation))))

(defun h3-book-translation-translate-floor (library original shifted ratio-type change integer)
  (h3-book-translation-with-library library
      ((interval (h3-book-floor-floor-bounds-with-library library original ratio-type) :library)
       (ratio (h3-book-translation-step-at ratio-type 1))
       (shift (h3-book-translation-step-at integer 1))
       (changed (h3-book-translation-step-at change 2)))
    (if (not (equal changed (library-plus ratio shift)))
        (cons '(:failure "failure" "") library)
      (let ((q-int (car interval))
            (lo (cadr interval))
            (hi (caddr interval)))
        (h3-book-translation-with-library library
            ((q (h3-book-translation-step-at q-int 1))
             (candidate (library-plus q shift))
             (candidate-int (library-library-type-of library candidate (list q-int integer)))
             (sums (h3-book-sums-book-sums-init library))
             (lo-test (h3-book-translation-step-at lo 1))
             (lower (h3-book-sums-cancel-comparison
                     library sums (library-lt changed candidate) lo-test
                     (list ratio-type q-int integer)))
             (hi-test (proof-step-first hi))
             (upper (h3-book-sums-cancel-comparison
                     library sums (library-lt changed (library-plus *proof-one* candidate))
                     hi-test (list ratio-type q-int integer)))
             (lower (library-library-transport-argument library lo lower 1))
             (symmetric-change (library-inherited proof-proof-symmetric library change))
             (lower (library-inherited proof-proof-rewrite library lower symmetric-change '(1 1 1)))
             (upper (library-inherited proof-proof-transport library hi upper))
             (upper (library-library-transport-argument library upper change 1))
             (shift-type (h3-book-numerator-as-rational library integer))
             (sum-type (h3-numeric-rational-sum library ratio-type shift-type))
             (shifted-type (library-library-transport-argument library sum-type change 1))
             (shifted-interval
              (h3-book-floor-floor-bounds-with-library library shifted shifted-type) :library)
             (equation (h3-book-floor-same-floor-interval-with-library
                        library shifted-type shifted-interval (list candidate-int lower upper))
                       :library))
          (cons equation library))))))

(defun h3-book-translation-rational-ratio-noncomplex (library dividend divisor ratio evidence)
  (let* ((complex-test (list *h3-book-signs-complexp* dividend))
         (side (table-get evidence (proof-neg complex-test) nil))
         (test (list *library-rationalp* dividend)))
    (if (not side)
        '(:failure "unproved" "")
      (proof-with-checked-results
          ((divisor-type (proof-step-first divisor))
           (inverse-term (proof-term-at ratio 2))
           (reciprocal (h3-book-quotient-rational-type
                        library inverse-term (list (cons divisor-type divisor))))
           (positive (library-inherited proof-proof-assume library test t))
           (yes (h3-book-signs-rational-product library positive reciprocal))
           (negative (library-inherited proof-proof-assume library test nil))
           (absent (h3-book-floor-nonnumeric-given-noncomplex library side negative))
           (rule (library-library-axiom library "DEFAULT-*-1" (list dividend inverse-term)))
           (zero (library-inherited proof-proof-modus-ponens library rule absent))
           (integer-zero (library-library-axiom library "INTEGER-0" nil))
           (rational-zero (h3-book-numerator-as-rational library integer-zero))
           (no (library-library-transport-argument library rational-zero zero 1)))
        (library-inherited proof-proof-cases library test yes no)))))

(defund h3-book-translation-rational-ratio-start (library dividend divisor context)
  (proof-with-checked-results
      ((divisor-term (h3-book-translation-step-at divisor 1))
       (divisor-type (proof-step-first divisor)))
    (let* ((ratio (h3-book-floor-floor-ratio dividend divisor-term))
           (evidence (h3-book-order-bounds-evidence context))
           (direct (h3-book-quotient-rational-type
                    library ratio (table-put evidence divisor-type divisor))))
      (cond
       ((not (h3-rewrite-unproved-p direct)) direct)
       ((not (proof-is-call dividend *proof-plus*))
        (h3-book-translation-rational-ratio-noncomplex library dividend divisor ratio evidence))
       ((not (equal (len (cdr dividend)) 2))
        '(:failure "wrong-sum-arity" ""))
       (t
        (proof-with-checked-results
            ((expansion (h3-book-translation-sum-ratio library (cadr dividend) (caddr dividend)
                                                      divisor-term)))
          (list :expand expansion ratio evidence)))))))

(defun h3-book-translation-rational-ratio-finish (library dividend divisor opening parts)
  (let ((sum (proof-with-checked-results ((parts parts))
               (h3-numeric-rational-sum library (car parts) (cadr parts)))))
    (if (h3-rewrite-unproved-p sum)
        (h3-book-translation-rational-ratio-noncomplex
         library dividend divisor (caddr opening) (cadddr opening))
      (proof-with-checked-results ((sum sum))
        (library-library-transport-argument library sum (cadr opening) 1)))))

(mutual-recursion
 (defun h3-book-translation-rational-ratio (library dividend divisor context)
   (declare (xargs :measure (acl2-count dividend)))
   (let ((opening (h3-book-translation-rational-ratio-start library dividend divisor context)))
     (if (and (consp dividend) (eq (car opening) :expand))
         (h3-book-translation-rational-ratio-finish
          library dividend divisor opening
          (h3-book-translation-rational-ratio-summands library (cdr dividend) divisor context))
       opening)))

 (defun h3-book-translation-rational-ratio-summands (library summands divisor context)
   (declare (xargs :measure (acl2-count summands)))
   (if (endp summands)
       nil
     (proof-with-checked-results
         ((first (h3-book-translation-rational-ratio library (car summands) divisor context))
          (rest (h3-book-translation-rational-ratio-summands library (cdr summands) divisor context)))
       (cons first rest)))))

(defund h3-book-translation-integer-factor (library term context)
  (if (proof-is-call term *h3-book-floor-floor*)
      (h3-book-floor-floor-is-integer-with-library library term)
    (let ((result (library-library-type-of
                   library term (table-values (h3-book-order-bounds-evidence context)))))
      (cons (if (h3-book-translation-retryable-p result)
                '(:failure "unproved" "")
              result)
            library))))

(mutual-recursion
 (defun h3-book-translation-integer-translation (n library delta divisor law context)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       (cons '(:failure "fuel" "h3-book-translation-integer-translation") library)
     (let* ((ratio (h3-book-floor-floor-ratio delta divisor))
            (given (table-get (h3-book-order-bounds-evidence context)
                               (library-integer ratio) nil)))
       (cond
        (given (cons given library))
        ((proof-is-call delta *proof-minus*)
         (h3-book-translation-with-library library
             ((term (proof-term-at delta 1))
              (original (h3-book-translation-integer-translation
                         (1- n) library term divisor law context)
                        :library)
              (equation (h3-book-signs-minus-product-with-library
                         library term (list *h3-book-arithmetic-divide* divisor) t)
                        :library)
              (changed (h3-book-translation-step-at equation 2))
              (result (library-library-type-of library changed (list original))))
           (cons (library-library-transport-argument library result equation 1) library)))
        ((proof-is-call delta *proof-plus*)
         (h3-book-translation-with-library library
             ((terms (proof-list-of-length (cdr delta) 2))
              (left (car terms))
              (right (cadr terms))
              (equation (h3-book-translation-sum-ratio library left right divisor))
              (changed (h3-book-translation-step-at equation 2))
              (first (h3-book-translation-integer-translation
                      (1- n) library left divisor law context)
                     :library)
              (second (h3-book-translation-integer-translation
                       (1- n) library right divisor law context)
                      :library)
              (result (library-library-type-of library changed (list first second))))
           (cons (library-library-transport-argument library result equation 1) library)))
        ((proof-is-call delta *proof-times*)
         (h3-book-translation-with-library library
             ((terms (proof-list-of-length (cdr delta) 2)))
           (h3-book-translation-integer-translation-product
            (1- n) library (list terms (reverse terms)) ratio divisor law context)))
        (t (cons '(:failure "unproved" "") library))))))

 (defun h3-book-translation-integer-translation-product (n library pairs ratio divisor law context)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) (cons '(:failure "fuel" "h3-book-translation-integer-translation-product") library))
    ((endp pairs) (cons '(:failure "unproved" "") library))
    (t
     (let* ((factor (caar pairs))
            (unit (cadar pairs))
            (whole-result (h3-book-translation-integer-factor library factor context))
            (library (cdr whole-result))
            (whole (car whole-result)))
       (cond
        ((h3-rewrite-unproved-p whole)
         (h3-book-translation-integer-translation-product
          (1- n) library (cdr pairs) ratio divisor law context))
        ((failure-p whole) whole-result)
        ((equal unit divisor)
         (h3-book-translation-with-library library
             ((equation (h3-book-quotient-cancel-inverse-pair library ratio divisor factor law))
              (rational (h3-book-numerator-as-rational library whole))
              (numeric (h3-book-signs-number library rational))
              (fixed (h3-book-arithmetic-fix-value library factor numeric))
              (equation (library-inherited proof-proof-chain library equation (list fixed))))
           (cons (library-library-transport-argument library whole equation 1) library)))
        (t
         (let* ((unit-result (h3-book-translation-integer-translation
                              (1- n) library unit divisor law context))
                (library (cdr unit-result))
                (unit-ratio (car unit-result)))
           (cond
            ((h3-rewrite-unproved-p unit-ratio)
             (h3-book-translation-integer-translation-product
              (1- n) library (cdr pairs) ratio divisor law context))
            ((failure-p unit-ratio) unit-result)
            (t
             (h3-book-translation-with-library library
                 ((unit-term (h3-book-translation-step-at unit-ratio 1))
                  (expression (list *proof-times* factor unit-term))
                  (equation (h3-book-arithmetic-associative-equal library ratio expression))
                  (product (library-library-type-of library expression (list whole unit-ratio))))
               (cons (library-library-transport-argument library product equation 1) library))))))))))))

(defun h3-book-translation-floor-zero-for-nonrational-divisor (library call not-rational context)
  (proof-with-checked-results ((dividend (proof-term-at call 1)))
    (let ((rational (h3-book-order-bounds-rational
                     (h3-book-order-bounds-with-library context library) dividend)))
      (if (not (h3-rewrite-unproved-p rational))
          (proof-with-checked-results ((rational rational))
            (h3-book-mod-floor-zero-with-mixed-types library call rational not-rational))
        (let* ((test (list *library-rationalp* dividend))
               (complex-test (list *h3-book-signs-complexp* dividend))
               (side (table-get (h3-book-order-bounds-evidence context)
                                  (proof-neg complex-test) nil)))
          (if (not side)
              '(:failure "unproved" "")
            (proof-with-checked-results
                ((positive (library-inherited proof-proof-assume library test t))
                 (yes (h3-book-mod-floor-zero-with-mixed-types library call positive not-rational))
                 (negative (library-inherited proof-proof-assume library test nil))
                 (absent (h3-book-floor-nonnumeric-given-noncomplex library side negative))
                 (no (h3-book-floor-floor-zero-by-argument library call absent)))
              (library-inherited proof-proof-cases library test yes no))))))))

(defun h3-book-translation-mod-translate-floor-zero (call library base context no-rat)
  (proof-with-checked-results ((dividend (proof-term-at call 1)))
    (if (not (equal dividend base))
        '(:failure "unproved" "")
      (proof-with-checked-results
          ((divisor (proof-term-at call 2))
           (rational (h3-book-order-bounds-rational
                      (h3-book-order-bounds-with-library context library) divisor)))
        (h3-book-mod-floor-zero-with-mixed-types library call rational no-rat)))))

(defun h3-book-translation-translate-mod-by-type-floor-zero (call library divisor not-rational context)
  (proof-with-checked-results ((denominator (proof-term-at call 2)))
    (if (equal denominator divisor)
        (h3-book-translation-floor-zero-for-nonrational-divisor library call not-rational context)
      '(:failure "unproved" ""))))

(defun h3-book-translation-call-floor-zero (library call recipe)
  (case (car recipe)
    (:complex-dividend
     (h3-book-translation-mod-translate-floor-zero
      call library (cadr recipe) (caddr recipe) (cadddr recipe)))
    (:nonrational-divisor
     (h3-book-translation-translate-mod-by-type-floor-zero
      call library (cadr recipe) (caddr recipe) (cadddr recipe)))))

(defun h3-book-translation-zero-product (library factors factor evidence)
  (case (len factors)
    (0 '(:failure "failure" ""))
    (1 '(:failure "failure" ""))
    (2 (h3-book-arithmetic-zero-product library (car factors) (cadr factors) factor evidence))
    (otherwise
     '(:failure "failure" ""))))

(mutual-recursion
 (defun h3-book-translation-zero-multiple (library term divisor evidence floor-zero)
   (declare (xargs :measure (acl2-count term)))
   (proof-with-checked-results ((given (and evidence (proof-step-first evidence))))
     (cond
      ((and evidence (equal given (proof-eq term *proof-zero*))) evidence)
      ((atom term) '(:failure "unproved" ""))
      ((and floor-zero (proof-is-call term *h3-book-floor-floor*))
       (h3-book-translation-call-floor-zero library term floor-zero))
      ((proof-is-call term *proof-plus*)
       (proof-with-checked-results
           ((initial (library-inherited proof-proof-reflexive library term))
            (step (h3-book-translation-zero-multiple-sum
                   library (cdr term) 1 initial divisor evidence floor-zero))
            (zero (library-inherited proof-proof-compute
                                     library (library-plus *proof-zero* *proof-zero*) 0)))
         (library-inherited proof-proof-chain library step (list zero))))
      ((proof-is-call term *proof-minus*)
       (if (endp (cdr term))
           '(:failure "failure" "")
         (proof-with-checked-results
             ((part (h3-book-translation-zero-multiple library (cadr term) divisor evidence floor-zero))
              (initial (library-inherited proof-proof-reflexive library term))
              (reduced (library-inherited proof-proof-rewrite library initial part '(1 2 1)))
              (zero (library-inherited proof-proof-compute library (library-minus *proof-zero*) 0)))
           (library-inherited proof-proof-chain library reduced (list zero)))))
      ((not (proof-is-call term *proof-times*)) '(:failure "unproved" ""))
      ((and (member-equal divisor (cdr term)) evidence)
       (h3-book-translation-zero-product library (cdr term) divisor evidence))
      (t (h3-book-translation-zero-multiple-product
          library (cdr term) (cdr term) divisor evidence floor-zero)))))

 (defun h3-book-translation-zero-multiple-sum (library parts index step divisor evidence floor-zero)
   (declare (xargs :measure (acl2-count parts)))
   (if (endp parts)
       step
     (proof-with-checked-results
         ((child (h3-book-translation-zero-multiple library (car parts) divisor evidence floor-zero))
          (step (library-inherited proof-proof-rewrite library step child (list 1 2 index))))
       (h3-book-translation-zero-multiple-sum library (cdr parts) (1+ index)
                                              step divisor evidence floor-zero))))

 (defun h3-book-translation-zero-multiple-product (library parts factors divisor evidence floor-zero)
   (declare (xargs :measure (acl2-count parts)))
   (if (endp parts)
       '(:failure "unproved" "")
     (let ((equation (h3-book-translation-zero-multiple library (car parts)
                                                         divisor evidence floor-zero)))
       (if (h3-rewrite-unproved-p equation)
           (h3-book-translation-zero-multiple-product library (cdr parts) factors
                                                      divisor evidence floor-zero)
         (proof-with-checked-results ((equation equation))
           (h3-book-translation-zero-product library factors (car parts) equation)))))))

(defun h3-book-translation-unchanged-remainder (library base delta divisor vanished)
  (let* ((total (library-plus base delta))
         (original (list *h3-book-mod-mod* base divisor))
         (changed (list *h3-book-mod-mod* total divisor))
         (test (list *library-numberp* base)))
    (proof-with-checked-results
        ((initial (library-inherited proof-proof-reflexive library total))
         (fixed (library-inherited proof-proof-rewrite library initial vanished '(1 2 2)))
         (commuted (library-library-axiom library "COMMUTATIVITY-OF-+" (list base *proof-zero*)))
         (identity (library-library-axiom library "UNICITY-OF-0" (list base)))
         (fixed (library-inherited proof-proof-chain library fixed (list commuted identity)))
         (present (library-inherited proof-proof-assume library test t))
         (exact (h3-book-arithmetic-fix-value library base present))
         (exact (library-inherited proof-proof-chain library fixed (list exact)))
         (initial (library-inherited proof-proof-reflexive library changed))
         (yes (library-inherited proof-proof-rewrite library initial exact '(1 2 1)))
         (missing (library-inherited proof-proof-assume library test nil))
         (empty (h3-book-arithmetic-fix-value library base missing))
         (empty (library-inherited proof-proof-chain library fixed (list empty)))
         (initial (library-inherited proof-proof-reflexive library changed))
         (no (library-inherited proof-proof-rewrite library initial empty '(1 2 1)))
         (remainder (h3-book-translation-step-at no 2))
         (zero (h3-book-mod-mod-zero-dividend library remainder nil))
         (original-zero (h3-book-mod-mod-zero-dividend library original missing))
         (reversed (library-inherited proof-proof-symmetric library original-zero))
         (no (library-inherited proof-proof-chain library no (list zero reversed))))
      (library-inherited proof-proof-cases library test yes no))))

(defun h3-book-translation-mod-translate-rational
    (library base delta divisor integer law old-type context)
  (let* ((sum (library-plus base delta))
         (old-floor (list *h3-book-floor-floor* base divisor))
         (new-floor (list *h3-book-floor-floor* sum divisor))
         (original (list *h3-book-mod-mod* base divisor))
         (changed (list *h3-book-mod-mod* sum divisor)))
    (h3-book-translation-with-library library
        ((ratio-change (h3-book-translation-sum-ratio library base delta divisor))
         (floor-change (h3-book-translation-translate-floor
                        library old-floor new-floor old-type ratio-change integer)
                       :library)
         (opening (library-inherited proof-proof-unfold library changed))
         (opened (library-inherited proof-proof-rewrite library opening floor-change '(1 2 2 1 1)))
         (shift (h3-book-translation-step-at integer 1))
         (candidate (library-plus old-floor shift))
         (product (library-library-axiom library "COMMUTATIVITY-OF-*" (list candidate divisor)))
         (distribution (h3-book-arithmetic-multiply-out library divisor candidate))
         (product (library-inherited proof-proof-chain library product (list distribution)))
         (commuted (library-library-axiom library "COMMUTATIVITY-OF-*" (list divisor old-floor)))
         (product (library-inherited proof-proof-rewrite library product commuted '(1 2 1)))
         (commuted (library-library-axiom library "COMMUTATIVITY-OF-*" (list divisor shift)))
         (product (library-inherited proof-proof-rewrite library product commuted '(1 2 2)))
         (clear (h3-book-quotient-clear-reciprocal library shift divisor law nil))
         (product (library-inherited proof-proof-rewrite library product clear '(1 2 2)))
         (opened (library-inherited proof-proof-rewrite library opened product '(1 2 2 1)))
         (before (library-inherited proof-proof-unfold library original))
         (after-value (h3-book-translation-step-at opened 2))
         (before-value (h3-book-translation-step-at before 2))
         (identity (h3-book-translation-sum-equality-with-library
                    library after-value before-value
                    (table-values (h3-book-order-bounds-evidence context)))
                   :library)
         (symmetric-before (library-inherited proof-proof-symmetric library before)))
      (cons (library-inherited proof-proof-chain library opened (list identity symmetric-before))
            library))))

(defund h3-book-translation-mod-translate-start (library base delta divisor notzero context)
  (h3-book-translation-with-library library
      ((y (h3-book-translation-step-at divisor 1))
       (registered (h3-book-sums-lemmas-with-library library) :library)
       (numeric (h3-book-signs-number library divisor))
       (law (h3-book-arithmetic-inverse library y numeric notzero))
       (integer (h3-book-translation-integer-translation 1000000 library delta y law context)
                :library))
    (let ((old-type (h3-book-translation-rational-ratio library base divisor context)))
      (if (not (h3-rewrite-unproved-p old-type))
          (h3-book-translation-with-library library ((old-type old-type))
            (h3-book-translation-mod-translate-rational
             library base delta y integer law old-type context))
        (let ((test (list *h3-book-signs-complexp* base)))
          (h3-book-translation-with-library library
              ((side (library-inherited proof-proof-assume library test nil))
               (evidence (table-values (h3-book-order-bounds-evidence context)))
               (noncomplex (h3-book-order-bounds-init library (append evidence (list side)))))
            (cons (list :split y test noncomplex) library)))))))

(defun h3-book-translation-mod-translate-complex (library base delta y test yes context)
  (h3-book-translation-with-library library
      ((no-type (library-inherited proof-proof-fact library "complex-rationalp-not-rationalp"
                                  (list (list *library-x* base))))
       (complex (library-inherited proof-proof-assume library test t))
       (no-rat (library-inherited proof-proof-modus-ponens library no-type complex))
       (vanished (h3-book-translation-zero-multiple
                  library delta y nil (list :complex-dividend base context no-rat)))
       (no (h3-book-translation-unchanged-remainder library base delta y vanished)))
    (cons (library-inherited proof-proof-cases library test no yes) library)))

(defun h3-book-translation-mod-translate-with-library
    (n library base delta divisor notzero context)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (cons '(:failure "fuel" "h3-book-translation-mod-translate-with-library") library)
    (let* ((started (h3-book-translation-mod-translate-start library base delta divisor notzero context))
           (part (car started))
           (library (cdr started)))
      (if (eq (car part) :split)
          (h3-book-translation-with-library library
              ((yes (h3-book-translation-mod-translate-with-library
                     (1- n) library base delta divisor notzero (cadddr part))
                    :library))
            (h3-book-translation-mod-translate-complex
             library base delta (cadr part) (caddr part) yes context))
        started))))

(defun h3-book-translation-translate-mod-by-type-rational-case
    (typed library base delta divisor context)
  (let ((test (proof-eq divisor *proof-zero*)))
    (h3-book-translation-with-library library
        ((known (h3-rewrite-search-known (h3-book-order-bounds-search context)
                                        (proof-neg test)
                                        (h3-book-order-bounds-evidence context))))
      (if known
          (h3-book-translation-mod-translate-with-library 1000000 library base delta typed known context)
        (h3-book-translation-with-library library
            ((zero (library-inherited proof-proof-assume library test t))
             (vanished (h3-book-translation-zero-multiple library delta divisor zero nil))
             (yes (h3-book-translation-unchanged-remainder library base delta divisor vanished))
             (notzero (library-inherited proof-proof-assume library test nil))
             (no (h3-book-translation-mod-translate-with-library
                  1000000 library base delta typed notzero context)
                 :library))
          (cons (library-inherited proof-proof-cases library test yes no) library))))))

(defun h3-book-translation-translate-mod-by-type (library base delta divisor context)
  (let* ((context (h3-book-order-bounds-with-library context library))
         (typed (h3-book-order-bounds-rational context divisor)))
    (h3-book-translation-with-library library
        ((typed (if (h3-rewrite-unproved-p typed) nil typed)))
      (if typed
          (h3-book-translation-translate-mod-by-type-rational-case typed library base delta divisor context)
        (let* ((test (list *library-rationalp* divisor))
               (complex-test (list *h3-book-signs-complexp* divisor))
               (side (table-get (h3-book-order-bounds-evidence context)
                                  (proof-neg complex-test) nil)))
          (h3-book-translation-with-library library
              ((not-rational (library-inherited proof-proof-assume library test nil))
               (vanished (if side
                             (proof-with-checked-results
                                 ((no-type (h3-book-floor-nonnumeric-given-noncomplex
                                            library side not-rational)))
                               (h3-book-translation-zero-multiple library delta divisor no-type nil))
                           (h3-book-translation-zero-multiple
                            library delta divisor nil
                            (list :nonrational-divisor divisor not-rational context))))
               (no (h3-book-translation-unchanged-remainder library base delta divisor vanished))
               (assumed (library-inherited proof-proof-assume library test t))
               (yes (h3-book-translation-translate-mod-by-type-rational-case
                     assumed library base delta divisor context)
                    :library))
            (cons (library-inherited proof-proof-cases library test yes no) library)))))))

(defun h3-book-translation-expose-signed-summands (library term index child)
  (if (not child)
      (cons nil library)
    (h3-book-translation-with-library library
        ((value (h3-book-translation-step-at child 2)))
      (if (not (proof-is-call value *proof-plus*))
          (cons nil library)
        (h3-book-translation-with-library library
            ((initial (library-inherited proof-proof-reflexive library term))
             (opened (library-inherited proof-proof-rewrite library initial child (list 1 2 index)))
             (registered (if (equal index 1)
                             (h3-book-sums-lemmas-with-library library)
                           (cons nil library))
                         :library)
             (distribution (if (equal index 1)
                               (library-library-cite library *h3-book-sums-negate* (cdr value) nil)
                             (library-library-axiom library "DISTRIBUTIVITY"
                                                    (cons *proof-neg-one* (cdr value))))))
          (cons (library-inherited proof-proof-chain library opened (list distribution)) library))))))

(mutual-recursion
 (defun h3-book-translation-expose-mod-summands (library term)
   (declare (xargs :measure (acl2-count term)))
   (let ((minus (proof-is-call term *proof-minus*))
         (times (proof-is-call term *proof-times*)))
     (cond
      ((atom term) (cons nil library))
      ((proof-is-call term *h3-book-mod-mod*)
       (cons (library-inherited proof-proof-unfold library term) library))
      ((and (or minus times) (endp (cdr term)))
       (cons '(:failure "failure" "") library))
      (minus
       (h3-book-translation-with-library library
           ((child (h3-book-translation-expose-mod-summands library (cadr term)) :library))
         (h3-book-translation-expose-signed-summands library term 1 child)))
      ((and times (equal (cadr term) *proof-neg-one*))
       (if (endp (cddr term))
           (cons '(:failure "failure" "") library)
         (h3-book-translation-with-library library
             ((child (h3-book-translation-expose-mod-summands library (caddr term)) :library))
           (h3-book-translation-expose-signed-summands library term 2 child))))
      ((proof-is-call term *proof-plus*)
       (h3-book-translation-expose-plus-summands library term (cdr term) 1 nil))
      (t (cons nil library)))))

 (defun h3-book-translation-expose-plus-summands (library term arguments index result)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       (cons result library)
     (h3-book-translation-with-library library
         ((child (h3-book-translation-expose-mod-summands library (car arguments)) :library)
          (result (if child
                      (proof-with-checked-results
                          ((start (or result (library-inherited proof-proof-reflexive library term))))
                        (library-inherited proof-proof-rewrite library start child (list 1 2 index)))
                    result)))
       (h3-book-translation-expose-plus-summands library term (cdr arguments) (1+ index) result)))))

(mutual-recursion
 (defun h3-book-translation-summands (term)
   (declare (xargs :measure (acl2-count term)))
   (if (and (consp term) (proof-is-call term *proof-plus*))
       (h3-book-translation-summands-list (cdr term))
     (list term)))

 (defun h3-book-translation-summands-list (terms)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       nil
     (append (h3-book-translation-summands (car terms))
             (h3-book-translation-summands-list (cdr terms))))))

(defun h3-book-translation-remove-summands (base-parts parts)
  (cond
   ((endp base-parts) parts)
   ((member-equal (car base-parts) parts)
    (h3-book-translation-remove-summands
     (cdr base-parts) (remove1-equal (car base-parts) parts)))
   (t nil)))

(defun h3-book-translation-displacement-sum (delta terms)
  (if (endp terms)
      delta
    (h3-book-translation-displacement-sum (library-plus delta (car terms)) (cdr terms))))

(defun h3-book-translation-displacements (expanded base)
  (let* ((parts (h3-book-translation-summands expanded))
         (remaining (h3-book-translation-remove-summands
                     (h3-book-translation-summands base) parts)))
    (if (consp (cdr remaining))
        (append parts
                (list (h3-book-translation-displacement-sum (car remaining) (cdr remaining))))
      parts)))

(defun h3-book-translation-modulus-translation-deltas
    (library deltas opening expanded base divisor context guard reversed left)
  (declare (xargs :measure (acl2-count deltas)))
  (if (endp deltas)
      (cons nil library)
    (let* ((delta (car deltas))
           (aligned (h3-book-arithmetic-associative-equal
                     library expanded (library-plus base delta))))
      (cond
       ((h3-book-translation-retryable-p aligned)
        (h3-book-translation-modulus-translation-deltas
         library (cdr deltas) opening expanded base divisor context guard reversed left))
       ((failure-p aligned) (cons aligned library))
       (t
        (let* ((translation (h3-book-translation-translate-mod-by-type library base delta divisor context))
               (library (cdr translation))
               (equation (car translation)))
          (cond
           ((h3-book-translation-retryable-p equation)
            (h3-book-translation-modulus-translation-deltas
             library (cdr deltas) opening expanded base divisor context guard reversed left))
           ((failure-p equation) translation)
           (t
            (h3-book-translation-with-library library
                ((changed-arg (library-inherited proof-proof-chain library opening (list aligned)))
                 (initial (library-inherited proof-proof-reflexive library left))
                 (original (library-inherited proof-proof-rewrite library initial changed-arg '(1 2 1)))
                 (step (library-inherited proof-proof-chain library original (list equation)))
                 (step (if reversed (library-inherited proof-proof-symmetric library step) step)))
              (cons (h3-rewrite-implication library guard step) library))))))))))

(defun h3-book-translation-modulus-translation-openings
    (library openings base divisor context guard reversed left)
  (declare (xargs :measure (acl2-count openings)))
  (cond
   ((endp openings) (cons nil library))
   ((not (car openings))
    (h3-book-translation-modulus-translation-openings
     library (cdr openings) base divisor context guard reversed left))
   (t
    (h3-book-translation-with-library library
        ((expanded (h3-book-translation-step-at (car openings) 2))
         (deltas (h3-book-translation-displacements expanded base))
         (step (h3-book-translation-modulus-translation-deltas
                library deltas (car openings) expanded base divisor context guard reversed left)
               :library))
      (if step
          (cons step library)
        (h3-book-translation-modulus-translation-openings
         library (cdr openings) base divisor context guard reversed left))))))

(defun h3-book-translation-modulus-translation-directions (library directions context guard)
  (declare (xargs :measure (acl2-count directions)))
  (if (endp directions)
      (cons nil library)
    (let* ((direction (car directions))
           (reversed (car direction))
           (left (cadr direction))
           (right (caddr direction)))
      (h3-book-translation-with-library library
          ((parts (proof-list-of-length (cdr left) 2))
           (changed (car parts))
           (divisor (cadr parts))
           (base (proof-term-at right 1))
           (reflexive (library-inherited proof-proof-reflexive library changed))
           (exposed (h3-book-translation-expose-mod-summands library changed) :library)
           (step (h3-book-translation-modulus-translation-openings
                  library (list reflexive exposed) base divisor context guard reversed left)
                 :library))
        (if step
            (cons step library)
          (h3-book-translation-modulus-translation-directions
           library (cdr directions) context guard))))))

(defun h3-book-translation-all-mod-p (terms)
  (or (endp terms)
      (and (proof-is-call (car terms) *h3-book-mod-mod*)
           (h3-book-translation-all-mod-p (cdr terms)))))

(defun h3-book-translation-modulus-translation-with-library (library formula)
  (if (not (proof-is-call formula *library-implies*))
      (cons nil library)
    (h3-book-translation-with-library library
        ((parts (proof-list-of-length (cdr formula) 2))
         (guard (car parts))
         (goal (cadr parts)))
      (if (not (and (proof-is-call goal *proof-equal*)
                    (h3-book-translation-all-mod-p (cdr goal))))
          (cons nil library)
        (h3-book-translation-with-library library
            ((left (proof-term-at goal 1))
             (left-divisor (proof-term-at left 2))
             (right (proof-term-at goal 2))
             (right-divisor (proof-term-at right 2)))
          (if (not (equal left-divisor right-divisor))
              (cons nil library)
            (h3-book-translation-with-library library
                ((assumed (library-inherited proof-proof-assume library guard t))
                 (context (h3-book-order-bounds-init library (list assumed)))
                 (arguments (proof-list-of-length goal 3)))
              (h3-book-translation-modulus-translation-directions
               library (list (list nil (cadr arguments) (caddr arguments))
                             (list t (caddr arguments) (cadr arguments)))
               context guard))))))))

(defun h3-book-translation-product-remainder-default (status library product divisor call target)
  (proof-with-checked-results
      ((dividend-zero (h3-book-translation-zero-product library (cdr product) divisor status))
       (initial (library-inherited proof-proof-reflexive library call))
       (empty (library-inherited proof-proof-rewrite library initial dividend-zero '(1 2 1)))
       (zero-call (h3-book-translation-step-at empty 2))
       (zero (h3-book-mod-mod-zero-dividend library zero-call nil))
       (empty (library-inherited proof-proof-chain library empty (list zero)))
       (target-zero (h3-book-translation-zero-product library (cdr target) divisor status))
       (symmetric (library-inherited proof-proof-symmetric library target-zero)))
    (library-inherited proof-proof-chain library empty (list symmetric))))

(defun h3-book-translation-product-remainder-with-library (library call factor)
  (h3-book-translation-with-library library
      ((parts (proof-list-of-length call 3))
       (product (cadr parts))
       (divisor (caddr parts))
       (singly (list *h3-book-mod-mod* factor *proof-one*))
       (target (list *proof-times* divisor singly))
       (numeric-test (list *library-numberp* divisor))
       (zero-test (proof-eq divisor *proof-zero*))
       (typed (library-inherited proof-proof-assume library numeric-test t))
       (nonzero (library-inherited proof-proof-assume library zero-test nil))
       (law (h3-book-arithmetic-inverse library divisor typed nonzero))
       (left (list *h3-book-floor-floor* product divisor))
       (right (list *h3-book-floor-floor* factor *proof-one*))
       (ratio (h3-book-floor-floor-ratio product divisor))
       (reduced (h3-book-quotient-cancel-inverse-pair library ratio divisor factor law))
       (by-one (h3-book-floor-floor-ratio factor *proof-one*))
       (identity (library-inherited proof-proof-reflexive library by-one))
       (reciprocal (library-inherited proof-proof-compute
                                      library (list *h3-book-arithmetic-divide* *proof-one*) 1))
       (unity (library-inherited proof-proof-rewrite library identity reciprocal '(1 2 2)))
       (one-right (h3-book-arithmetic-one-right library factor))
       (unity (library-inherited proof-proof-chain library unity (list one-right)))
       (symmetric (library-inherited proof-proof-symmetric library unity))
       (equal-ratios (library-inherited proof-proof-chain library reduced (list symmetric)))
       (left-floor (h3-book-floor-floor-through-ratio library left))
       (quotients (library-inherited proof-proof-rewrite library left-floor equal-ratios '(1 2 1)))
       (right-floor (h3-book-floor-floor-through-ratio library right))
       (symmetric (library-inherited proof-proof-symmetric library right-floor))
       (quotients (library-inherited proof-proof-chain library quotients (list symmetric)))
       (unfolded (library-inherited proof-proof-unfold library call))
       (opened (library-inherited proof-proof-rewrite library unfolded quotients '(1 2 2 1 1)))
       (identity (library-inherited proof-proof-reflexive library target))
       (single-mod (library-inherited proof-proof-unfold library singly))
       (expanded (library-inherited proof-proof-rewrite library identity single-mod '(1 2 2)))
       (right-side (h3-book-translation-step-at expanded 2))
       (summation (proof-term-at right-side 2))
       (distribution (library-library-axiom library "DISTRIBUTIVITY" (cons divisor (cdr summation))))
       (expanded (library-inherited proof-proof-chain library expanded (list distribution)))
       (right-side (h3-book-translation-step-at expanded 2))
       (second (proof-term-at right-side 2))
       (negation (proof-term-at second 2))
       (negated (proof-term-at negation 1))
       (minus-product (h3-book-signs-minus-product-with-library library divisor negated nil) :library)
       (expanded (library-inherited proof-proof-rewrite library expanded minus-product '(1 2 2)))
       (one-right (h3-book-arithmetic-one-right library right))
       (integer (h3-book-floor-floor-is-integer-with-library library right) :library)
       (rational (h3-book-numerator-as-rational library integer))
       (numeric (h3-book-signs-number library rational))
       (fixed (h3-book-arithmetic-fix-value library right numeric))
       (fixed-floor (library-inherited proof-proof-chain library one-right (list fixed)))
       (expanded (library-inherited proof-proof-rewrite library expanded fixed-floor '(1 2 2 1 2)))
       (opened-value (h3-book-translation-step-at opened 2))
       (expanded-value (h3-book-translation-step-at expanded 2))
       (aligned (h3-book-arithmetic-associative-equal library opened-value expanded-value))
       (symmetric (library-inherited proof-proof-symmetric library expanded))
       (exact (library-inherited proof-proof-chain library opened (list aligned symmetric)))
       (zero (library-inherited proof-proof-assume library zero-test t))
       (default (h3-book-translation-product-remainder-default zero library product divisor call target))
       (yes (library-inherited proof-proof-cases library zero-test default exact))
       (nonnumeric (library-inherited proof-proof-assume library numeric-test nil))
       (no (h3-book-translation-product-remainder-default nonnumeric library product divisor call target)))
    (cons (library-inherited proof-proof-cases library numeric-test yes no) library)))

(defun h3-book-translation-modulus-scaling-zero (library guard call factor scaled divisor)
  (h3-book-translation-with-library library
      ((assumption (library-inherited proof-proof-assume library guard t))
       (context (h3-book-order-bounds-init library (list assumption)))
       (registered (h3-book-sums-lemmas-with-library library) :library)
       (integer (h3-book-translation-integer-factor library factor context) :library)
       (rational (h3-book-numerator-as-rational library integer))
       (numeric (h3-book-signs-number library rational))
       (ratio (h3-book-floor-ratio-by-one library factor numeric))
       (ratio-integer (library-library-transport-argument library integer ratio 1))
       (one-nonzero (car (h3-rewrite-search-prove
                          (h3-rewrite-search-init library nil nil nil 150 nil)
                          (proof-neg (proof-eq *proof-one* *proof-zero*)) nil)))
       (one-numeric (h3-book-arithmetic-typed-number library *proof-one*))
       (exact (h3-book-mod-mod-exact-if-integer-ratio
               library (caddr scaled) numeric one-numeric one-nonzero ratio-integer))
       (remainder (h3-book-translation-product-remainder-with-library library call factor) :library)
       (result (library-inherited proof-proof-rewrite library remainder exact '(1 2 2)))
       (zero (library-inherited proof-proof-reflexive library *proof-zero*))
       (product (h3-book-arithmetic-zero-product library divisor *proof-zero* *proof-zero* zero)))
    (cons (library-inherited proof-proof-chain library result (list product)) library)))

(defun h3-book-translation-modulus-scaling-goal (library guard goal)
  (if (not (proof-is-call goal *proof-equal*))
      (cons nil library)
    (h3-book-translation-with-library library ((call (proof-term-at goal 1)))
      (if (not (proof-is-call call *h3-book-mod-mod*))
          (cons nil library)
        (h3-book-translation-with-library library ((product (proof-term-at call 1)))
          (if (not (proof-is-call product *proof-times*))
              (cons nil library)
            (h3-book-translation-with-library library
                ((arguments (proof-list-of-length (cdr goal) 2))
                 (target (cadr arguments))
                 (parts (proof-list-of-length call 3))
                 (divisor (caddr parts)))
              (if (not (member-equal divisor (cdr product)))
                  (cons nil library)
                (h3-book-translation-with-library library
                    ((first (proof-term-at product 1))
                     (factor (if (equal first divisor) (proof-term-at product 2) first))
                     (scaled (list *proof-times* divisor
                                   (list *h3-book-mod-mod* factor *proof-one*))))
                  (if (not (or (equal target scaled)
                               (and guard (equal target *proof-zero*))))
                      (cons nil library)
                    (h3-book-translation-with-library library
                        ((result (if (equal target scaled)
                                     (h3-book-translation-product-remainder-with-library library call factor)
                                   (h3-book-translation-modulus-scaling-zero
                                    library guard call factor scaled divisor))
                                 :library))
                      (cons (if guard (h3-rewrite-implication library guard result) result)
                            library))))))))))))

(defun h3-book-translation-modulus-scaling-with-library (library formula)
  (if (proof-is-call formula *library-implies*)
      (h3-book-translation-with-library library ((parts (proof-list-of-length (cdr formula) 2)))
        (let* ((guard (car parts))
               (guard (if (or (equal guard 0) (equal guard "")) nil guard)))
          (h3-book-translation-modulus-scaling-goal library guard (cadr parts))))
    (h3-book-translation-modulus-scaling-goal library nil formula)))

