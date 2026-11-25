(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun t2-books-make-obligation (raw name kind data)
  (list raw name kind data))

(defun t2-books-obligation-name (target)
  (cadr target))

(defun t2-books-obligation-kind (target)
  (caddr target))

(defun t2-books-obligation-data (target)
  (cadddr target))

(defun t2-books-first-name (kind data)
  (cond
   ((equal kind "define")
    (proof-with-checked-results ((definition (proof-term-at data 1)))
      (proof-term-at definition 0)))
   ((equal kind "constrain")
    (proof-with-checked-results ((declarations (proof-term-at data 0))
                                 (declaration (proof-term-at declarations 0)))
      (proof-term-at declaration 0)))
   ((equal kind "theorem") (proof-term-at data 0))
   (t nil)))

(defun t2-books-independent-theory (lib)
  lib)

(defun t2-books-parse-aid (kind data measures hints)
  (cond
   ((equal kind "measure")
    (proof-with-checked-results ((name (proof-term-at data 0)))
      (list (table-put measures name (seq-slice data 1 3)) hints)))
   ((equal kind "hints")
    (proof-with-checked-results ((name (proof-term-at data 0))
                                 (hint (proof-term-at data 1)))
      (list measures (table-put hints name hint))))
   (t (list measures hints))))

(defun t2-books-line-break-p (code text-p)
  (or (eql code 10)
      (eql code 13)
      (and text-p (or (eql code 11)
                      (eql code 12)
                      (and (<= 28 code) (<= code 30))
                      (eql code 133)))))

(defun t2-books-split-lines-chars (chars reversed keepends text-p)
  (cond
   ((endp chars)
    (and (consp reversed) (list (coerce (reverse reversed) 'string))))
   ((t2-books-line-break-p (char-code (car chars)) text-p)
    (let* ((crlf (and (eql (char-code (car chars)) 13)
                      (consp (cdr chars))
                      (eql (char-code (cadr chars)) 10)))
           (rest (if crlf (cddr chars) (cdr chars)))
           (line (cond ((not keepends) reversed)
                       (crlf (list* (cadr chars) (car chars) reversed))
                       (t (cons (car chars) reversed)))))
      (cons (coerce (reverse line) 'string)
            (t2-books-split-lines-chars rest nil keepends text-p))))
   (t (t2-books-split-lines-chars
       (cdr chars) (cons (car chars) reversed) keepends text-p))))

(defun t2-books-split-lines (source keepends text-p)
  (t2-books-split-lines-chars (coerce source 'list) nil keepends text-p))

(mutual-recursion
 (defun t2-books-sexp-text (value)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count value)))))
   (cond
    ((stringp value)
     (let* ((slash (coerce (list (code-char 92)) 'string))
            (quote-mark (coerce (list (code-char 34)) 'string))
            (escaped (text-replace
                      (text-replace value slash (string-append slash slash))
                      quote-mark (string-append slash quote-mark))))
       (string-append quote-mark (string-append escaped quote-mark))))
    ((integerp value) (decimal-text value))
    ((rationalp value)
     (text-join "/" (list (decimal-text (numerator value)) (decimal-text (denominator value)))))
    ((equal value t) "t")
    (t (string-append "(" (string-append (text-join " " (t2-books-sexp-fields value)) ")")))))
 (defun t2-books-sexp-fields (values)
   (declare (xargs :measure (* 2 (acl2-count values))))
   (if (endp values)
       nil
     (cons (t2-books-sexp-text (car values))
           (t2-books-sexp-fields (cdr values))))))

(defun t2-books-failure-kind-p (value kinds)
  (and (failure-p value) (member-equal (cadr value) kinds) t))

(defun t2-books-statement-prover-init (generator)
  (list :t2-books-statement-prover generator))

(defun t2-books-statement-prover-generator (prover)
  (cadr prover))

(defun t2-books-statement-prover-with-generator (prover generator)
  (cons (car prover) (cons generator (cddr prover))))

(defconst *t2-books-book-lemmas*
  '(:field :order :power :power-products :ratios
    :input-fields :input-state :input-channels :exponent-parity
    :exponent-equalities :dyadic :rounding :rational-scaling :half-parity
    :quotient-rounding :round-ties :numeric-types :field-cancellation
    :power-transport :floor-bracket :floor-thresholds :completed-operations))

(defun t2-books-build-lemma-family (lib family)
  (case family
    (:field (t2-field-build lib))
    (:order (t2-order-build lib))
    (:power (t2-power-build lib))
    (:power-products (t2-power-products-build lib))
    (:ratios (t2-ratios-build lib))
    (:input-fields (t2-input-fields-build lib))
    (:input-state (t2-input-state-build lib))
    (:input-channels (t2-input-channels-build lib))
    (:exponent-parity (t2-exponent-parity-build lib))
    (:exponent-equalities (t2-exponent-equalities-build lib))
    (:dyadic (t2-dyadic-build lib))
    (:rounding (t2-rounding-build lib))
    (:rational-scaling (t2-rational-scaling-build lib))
    (:half-parity (t2-half-parity-build lib))
    (:quotient-rounding (t2-quotient-rounding-build lib))
    (:round-ties (t2-round-ties-build lib))
    (:numeric-types (t2-numeric-types-build lib))
    (:field-cancellation (t2-field-cancellation-build lib))
    (:power-transport (t2-power-transport-build lib))
    (:floor-bracket (t2-floor-bracket-build lib))
    (:floor-thresholds (t2-floor-thresholds-build lib))
    (:completed-operations (t2-completed-operations-build lib))
    (otherwise '(:failure "failure" ""))))

(defconst *t2-books-definition-failures*
  '("unsupported" "missing-binding" "recipe-mismatch" "key" "value" "assertion" "stop"))

(defconst *t2-books-termination-unproved*
  '(:failure "unproved" ""))

(defun t2-books-selector-measures (selectors)
  (if (endp selectors)
      nil
    (cons (cons (caar selectors) (list *library-count* (cdar selectors)))
          (t2-books-selector-measures (cdr selectors)))))

(defun t2-books-statement-prover-definition-floor (prover definitions calls)
  (let* ((generator (t2-books-statement-prover-generator prover))
         (measures (t2-tactics-generator-measures-for generator definitions))
         (result (if (failure-p measures)
                     measures
                   (t2-floor-split-definition
                    (t2-tactics-generator-lib generator) definitions calls measures))))
    (cond
     ((t2-books-failure-kind-p result '("unsupported" "missing-binding" "recipe-mismatch" "key" "value" "assertion"))
      (cons *t2-books-termination-unproved* prover))
     ((failure-p result) (cons result prover))
     (t
      (cons (or (car result) *t2-books-termination-unproved*)
            (t2-books-statement-prover-with-generator
             prover (t2-tactics-generator-with-lib generator (cdr result))))))))

(defun t2-books-statement-prover-definition-dyadic (prover definitions calls)
  (let* ((generator (t2-books-statement-prover-generator prover))
         (entry (t2-dyadic-definition
                 (t2-tactics-generator-lib generator) definitions calls)))
    (cond ((or (null entry)
               (t2-books-failure-kind-p entry '("missing-binding" "recipe-mismatch" "key" "value" "assertion")))
           (t2-books-statement-prover-definition-floor prover definitions calls))
          (t (cons entry prover)))))

(defun t2-books-statement-prover-definition-selectors (prover data)
  (let ((selection
         (proof-with-checked-results ((rulers (proof-term-at data 0))
                                      (calls (termination-recursive-calls rulers (cdr data)))
                                      (selectors (termination-selector-plan (cdr data) calls)))
           (list rulers calls selectors))))
    (if (failure-p selection)
        (cons selection prover)
      (let ((rulers (car selection))
            (calls (cadr selection))
            (selectors (caddr selection)))
        (if (endp selectors)
            (t2-books-statement-prover-definition-dyadic prover (cdr data) calls)
          (let* ((attempt (t2-tactics-generator-prove-definition-attempt
                           (t2-books-statement-prover-generator prover)
                           rulers (cdr data) (t2-books-selector-measures selectors)))
                 (entry (car attempt))
                 (prover (t2-books-statement-prover-with-generator prover (cdr attempt))))
            (if (t2-books-failure-kind-p entry *t2-books-definition-failures*)
                (t2-books-statement-prover-definition-dyadic prover (cdr data) calls)
              (cons entry prover))))))))

(defun t2-books-statement-prover-definition-with-state (prover data)
  (let* ((attempt (t2-tactics-generator-prove-attempt
                   (t2-books-statement-prover-generator prover) "define" data))
         (entry (car attempt))
         (prover (t2-books-statement-prover-with-generator prover (cdr attempt))))
    (if (t2-books-failure-kind-p entry *t2-books-definition-failures*)
        (t2-books-statement-prover-definition-selectors prover data)
      (cons entry prover))))

(defun t2-books-proof-with-lib (result lib)
  (if (failure-p result) (cons result lib) result))

(defun t2-books-structural-theorem (lib formula)
  (let* ((tree (t2-books-proof-with-lib (t2-symbol-trees-prove lib formula) lib))
         (step (car tree))
         (lib (cdr tree)))
    (cond
     ((t2-books-failure-kind-p step '("unproved")) (cons nil lib))
     (step tree)
     (t
      (let* ((list-proof (t2-books-proof-with-lib (t2-structural-lists-prove lib formula) lib))
             (step (car list-proof))
             (lib (cdr list-proof)))
        (cond
         ((t2-books-failure-kind-p step '("unproved")) (cons nil lib))
         (step list-proof)
         (t
          (let ((rebalance (t2-tree-rebalance-prove-attempt lib formula)))
            (if (t2-books-failure-kind-p (car rebalance) '("unproved"))
                (cons nil (cdr rebalance))
              rebalance)))))))))

(defun t2-books-search-proof (lib index formula opened uses)
  (let ((search (t2-book-logic-search-init lib index opened 3600 uses)))
    (if (failure-p search)
        (cons search lib)
      (let ((result (t2-book-logic-search-proof search formula nil 5)))
        (if (failure-p result)
            (cons result lib)
          (cons (car result) (t2-book-logic-search-lib (cdr result))))))))

(defun t2-books-search-theorem (lib formula hint index)
  (let ((index (or index (t2-book-logic-rules-init lib))))
    (if (failure-p index)
        (cons index lib)
      (let* ((opened (t2-hints-expanded-functions hint))
             (result (t2-books-search-proof lib index formula opened nil))
             (lib (cdr result)))
        (if (not (t2-books-failure-kind-p (car result) '("unproved")))
            result
          (let ((enabled (t2-hints-enabled-functions hint)))
            (if (failure-p enabled)
                (cons enabled lib)
              (let ((uses (t2-hints-instances lib hint)))
                (cond ((failure-p uses) (cons uses lib))
                      ((and (subsetp-equal enabled opened) (endp uses)) result)
                      (t (t2-books-search-proof
                          lib index formula (union-equal opened enabled) uses)))))))))))

(defun t2-books-theorem-proof-with-rules (lib formula name hints index prepared)
  (let* ((conditional (t2-conditional-prove lib formula))
         (factored (if conditional
                       (cons conditional lib)
                     (t2-books-proof-with-lib (t2-factorization-prove lib formula) lib)))
         (structural (if (car factored)
                         factored
                       (t2-books-structural-theorem (cdr factored) formula))))
    (if (car structural)
        structural
      (let ((lib (cdr structural)))
        (t2-books-search-theorem
         lib formula (table-get hints name nil)
         (if prepared (t2-book-logic-rules-from-prepared prepared lib) index))))))

(defun t2-books-statement-prover-theorem-with-rules (prover target hints index prepared)
  (let ((formula (proof-term-at (t2-books-obligation-data target) 1)))
    (if (failure-p formula)
        (cons formula prover)
      (let* ((generator (t2-books-statement-prover-generator prover))
             (lib (t2-tactics-generator-lib generator))
             (name (t2-books-obligation-name target))
             (result (t2-books-theorem-proof-with-rules lib formula name hints index prepared))
             (lib (cdr result))
             (proof (library-library-proof lib))
             (prover (t2-books-statement-prover-with-generator
                      prover (t2-tactics-generator-with-lib generator lib)))
             (entry
              (proof-with-checked-results
                  ((step (car result))
                   (final (proof-proof-subsume proof step (list formula))))
                (proof-proof-entry "theorem" name (list name) (list final)))))
        (cons (if (failure-p entry) entry (list lib entry)) prover)))))

(defun t2-books-statement-prover-theorem (prover target hints index)
  (t2-books-statement-prover-theorem-with-rules prover target hints index nil))

(defun t2-books-statement-prover-witness-with-rules (prover data prepared)
  (let* ((generator (t2-books-statement-prover-generator prover))
         (lib (t2-tactics-generator-lib generator))
         (copy (t2-tactics-generator-with-lib generator (t2-books-independent-theory lib)))
         (result (t2-evaluator-witness copy data)))
    (cond
     ((t2-books-failure-kind-p
       result '("unproved" "recipe-mismatch" "missing-binding" "missing-term-part"
                "value" "key" "assertion" "index" "recursion"))
      (let ((equation (t2-equational-witness-with-prepared-rules
                       (t2-books-independent-theory lib) data prepared)))
        (if (failure-p equation)
            (cons equation prover)
          (cons (list (cdr equation) (car equation)) prover))))
     ((failure-p result) (cons result prover))
     (t (cons (list (t2-tactics-generator-lib (cdr result)) (car result)) prover)))))

(defun t2-books-statement-prover-witness (prover data)
  (t2-books-statement-prover-witness-with-rules prover data nil))

(defun t2-books-statement-prover-generate-with-prepared-rules (prover target hints prepared)
  (if (equal (t2-books-obligation-kind target) "theorem")
      (t2-books-statement-prover-theorem-with-rules prover target hints nil prepared)
    (t2-books-statement-prover-witness-with-rules prover (t2-books-obligation-data target) prepared)))

(defun t2-books-statement-prover-generate-with-state (prover target hints index)
  (let ((kind (t2-books-obligation-kind target))
        (data (t2-books-obligation-data target)))
    (cond
     ((equal kind "theorem") (t2-books-statement-prover-theorem prover target hints index))
     ((equal kind "define")
      (let ((result (t2-books-statement-prover-definition-with-state prover data)))
        (if (failure-p (car result))
            result
          (cons (list (t2-tactics-generator-lib (t2-books-statement-prover-generator (cdr result)))
                      (car result))
                (cdr result)))))
     (t (t2-books-statement-prover-witness prover data)))))

(defun t2-books-statement-prover-generate (prover target hints index)
  (let ((result (t2-books-statement-prover-generate-with-state prover target hints index)))
    (if (failure-p (car result)) (car result) result)))

; Progress holds the prover, rule index, seen lines, reversed targets, and candidates.
