(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun t2-books-make-obligation (raw name kind data)
  (list raw name kind data))

(defun t2-books-obligation-raw (target)
  (car target))

(defun t2-books-obligation-name (target)
  (cadr target))

(defun t2-books-obligation-kind (target)
  (caddr target))

(defun t2-books-obligation-data (target)
  (cadddr target))

(defun t2-books-make-candidate (entries prerequisites)
  (list entries prerequisites))

(defun t2-books-candidate-entries (candidate)
  (car candidate))

(defun t2-books-candidate-prerequisites (candidate)
  (cadr candidate))

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

(defun t2-books-parse-aid-events (events source-events-p measures hints)
  (if (endp events)
      (list measures hints)
    (proof-with-checked-results
        ((fields (proof-list-of-length (car events) (if source-events-p 3 2)))
         (event (if source-events-p (cdr fields) fields))
         (aids (t2-books-parse-aid (car event) (cadr event) measures hints)))
      (t2-books-parse-aid-events (cdr events) source-events-p (car aids) (cadr aids)))))

(defun t2-books-parse-aids (events)
  (t2-books-parse-aid-events events nil nil nil))

(defun t2-books-book-aids (events)
  (t2-books-parse-aid-events events t nil nil))

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

(defun t2-books-read-event (line)
  (proof-with-checked-results ((parsed (reader-reader-line (reader-reader-init line))))
    (car parsed)))

(defun t2-books-referenced-facts-add-definition-names (definitions local)
  (if (endp definitions)
      local
    (proof-with-checked-results ((name (proof-term-at (car definitions) 0)))
      (t2-books-referenced-facts-add-definition-names
       (cdr definitions) (add-to-set-equal name local)))))

(defun t2-books-referenced-facts-local (kind source local)
  (if (not (equal kind "define"))
      local
    (proof-with-checked-results
        ((first (proof-term-at (t2-books-split-lines source nil nil) 0))
         (event (t2-books-read-event first)))
      (t2-books-referenced-facts-add-definition-names (cdr (cadr event)) local))))

(defun t2-books-referenced-facts-scan (lines names)
  (if (endp lines)
      names
    (let ((line (car lines)))
      (if (and (> (length line) 7)
               (text-starts-with line "(fact ")
               (text-ends-with line ")"))
          (proof-with-checked-results ((event (t2-books-read-event line))
                                       (name (proof-term-at (cadr event) 0)))
            (t2-books-referenced-facts-scan
             (cdr lines) (add-to-set-equal name names)))
        (t2-books-referenced-facts-scan (cdr lines) names)))))

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

(defun t2-books-reference-keys (names local)
  (cond
   ((endp names) nil)
   ((member-equal (car names) local)
    (t2-books-reference-keys (cdr names) local))
   (t
    (cons (list (t2-books-sexp-text (car names)) (car names))
          (t2-books-reference-keys (cdr names) local)))))

(defun t2-books-reference-values (keys)
  (if (endp keys)
      nil
    (cons (cadar keys) (t2-books-reference-values (cdr keys)))))

(defun t2-books-referenced-facts-collect (entries names local)
  (if (endp entries)
      (t2-books-reference-values (seq-sorted (t2-books-reference-keys names local)))
    (proof-with-checked-results
        ((entry (proof-list-of-length (car entries) 4))
         (local (t2-books-referenced-facts-local
                 (car entry) (cadddr entry) (add-to-set-equal (cadr entry) local)))
         (names (t2-books-referenced-facts-scan
                 (text-split (cadddr entry) (coerce (list (code-char 10)) 'string)) names)))
      (t2-books-referenced-facts-collect (cdr entries) names local))))

(defun t2-books-referenced-facts (entries)
  (t2-books-referenced-facts-collect entries nil nil))

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
  '("Unsupported" "MissingBinding" "RecipeMismatch" "key" "value" "assertion" "stop"))

(defconst *t2-books-termination-unproved*
  '(:failure "Unproved" ""))

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
     ((t2-books-failure-kind-p result '("Unsupported" "MissingBinding" "RecipeMismatch" "key" "value" "assertion"))
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
               (t2-books-failure-kind-p entry '("MissingBinding" "RecipeMismatch" "key" "value" "assertion")))
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

(defun t2-books-statement-prover-definition (prover data)
  (let ((result (t2-books-statement-prover-definition-with-state prover data)))
    (if (failure-p (car result)) (car result) result)))

(defun t2-books-proof-with-lib (result lib)
  (if (failure-p result) (cons result lib) result))

(defun t2-books-structural-theorem (lib formula)
  (let* ((tree (t2-books-proof-with-lib (t2-symbol-trees-prove lib formula) lib))
         (step (car tree))
         (lib (cdr tree)))
    (cond
     ((t2-books-failure-kind-p step '("Unproved")) (cons nil lib))
     (step tree)
     (t
      (let* ((list-proof (t2-books-proof-with-lib (t2-structural-lists-prove lib formula) lib))
             (step (car list-proof))
             (lib (cdr list-proof)))
        (cond
         ((t2-books-failure-kind-p step '("Unproved")) (cons nil lib))
         (step list-proof)
         (t
          (let ((rebalance (t2-tree-rebalance-prove-attempt lib formula)))
            (if (t2-books-failure-kind-p (car rebalance) '("Unproved"))
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
        (if (not (t2-books-failure-kind-p (car result) '("Unproved")))
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

(defun t2-books-theorem-proof (lib formula name hints index)
  (t2-books-theorem-proof-with-rules lib formula name hints index nil))

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
       result '("Unproved" "RecipeMismatch" "MissingBinding" "MissingTermPart"
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

(defun t2-books-make-book-prover (generator library measures theory lines proofs skips)
  (list :t2-books-book-prover generator library measures theory lines proofs skips))

(defun t2-books-book-prover-library-measures (prover)
  (nth 3 prover))

(defun t2-books-book-prover-theory (prover)
  (nth 4 prover))

(defun t2-books-book-prover-library-lines (prover)
  (nth 5 prover))

(defun t2-books-book-prover-proofs (prover)
  (nth 6 prover))

(defun t2-books-book-prover-skips (prover)
  (nth 7 prover))

(defun t2-books-book-prover-note-skip (prover raw reason)
  (update-nth 7 (table-put (t2-books-book-prover-skips prover) raw reason) prover))

(defun t2-books-library-measures (events measures)
  (if (endp events)
      measures
    (proof-with-checked-results
        ((event (proof-list-of-length (car events) 3))
         (name (proof-term-at (caddr event) 0)))
      (t2-books-library-measures
       (cdr events) (table-put measures name (seq-slice (caddr event) 1 3))))))

(defun t2-books-admit-event (generator event)
  (t2-tactics-generator-admit-given generator (cadr event) (caddr event)))

(defun t2-books-admit-events (generator events)
  (declare (xargs :measure (acl2-count events)))
  (if (or (failure-p generator) (endp events))
      generator
    (t2-books-admit-events
     (proof-with-checked-results ((event (proof-list-of-length (car events) 3)))
       (t2-books-admit-event generator event))
     (cdr events))))

(defun t2-books-build-lemma-families (lib families)
  (declare (xargs :measure (acl2-count families)))
  (if (or (failure-p lib) (endp families))
      lib
    (t2-books-build-lemma-families (t2-books-build-lemma-family lib (car families))
                                  (cdr families))))

(defun t2-books-book-prover-init (library-source library-events measure-events)
  (proof-with-checked-results
      ((measures (t2-books-library-measures measure-events nil))
       (generator (t2-tactics-generator-init measures))
       (generator (t2-books-admit-events generator library-events))
       (theory (t2-books-build-lemma-families
                (t2-tactics-generator-lib generator) *t2-books-book-lemmas*)))
    (t2-books-make-book-prover
     (t2-tactics-generator-with-lib generator theory) library-source measures theory
     (proof-unique (t2-books-split-lines library-source t nil)) nil nil)))

(defun t2-books-candidate-matches-p (prerequisites facts)
  (or (endp prerequisites)
      (and (equal (table-get facts (caar prerequisites) :none) (cdar prerequisites))
           (t2-books-candidate-matches-p (cdr prerequisites) facts))))

(defun t2-books-candidate-prerequisite-facts (names facts)
  (if (endp names)
      nil
    (let ((fact (assoc-equal (car names) facts)))
      (if (not fact)
          '(:failure "MissingBinding" "")
        (proof-with-checked-results
            ((rest (t2-books-candidate-prerequisite-facts (cdr names) facts)))
          (cons fact rest))))))

(defun t2-books-candidate-from-entry (lib entry)
  (proof-with-checked-results
      ((entries (t2-tactics-proof-entries (library-library-entries lib) entry))
       (names (t2-books-referenced-facts entries))
       (facts (t2-books-candidate-prerequisite-facts
               names (proof-proof-facts (library-library-proof lib)))))
    (t2-books-make-candidate entries facts)))

(defun t2-books-book-prover-candidate-with-state (prover target hints index)
  (let* ((generator (t2-books-statement-prover-generator prover))
         (lib (t2-tactics-generator-lib generator))
         (facts (proof-proof-facts (library-library-proof lib)))
         (raw (t2-books-obligation-raw target))
         (cached (table-get (t2-books-book-prover-proofs prover) raw nil))
         (skip (assoc-equal raw (t2-books-book-prover-skips prover))))
    (cond
     ((and cached (t2-books-candidate-matches-p (t2-books-candidate-prerequisites cached) facts))
      (cons cached prover))
     (skip (cons '(:failure "Unproved" "") prover))
     (t (let* ((generated (t2-books-statement-prover-generate-with-state prover target hints index))
               (result (car generated))
               (candidate (if (failure-p result)
                              result
                            (t2-books-candidate-from-entry (car result) (cadr result)))))
          (cons candidate (cdr generated)))))))

(defun t2-books-book-prover-candidate (prover target hints index)
  (let ((result (t2-books-book-prover-candidate-with-state prover target hints index)))
    (if (failure-p (car result)) (car result) result)))

(defun t2-books-book-skip-sources (lines skips)
  (declare (xargs :measure (acl2-count lines)))
  (if (or (failure-p skips) (endp lines))
      skips
    (t2-books-book-skip-sources
     (cdr lines)
     (proof-with-checked-results
         ((event (t2-books-read-event (seq-slice (car lines) 0 -1)))
          (name (proof-term-at (cadr event) 0)))
       (table-put skips name (car lines))))))

(defun t2-books-book-admit-event (prover index event)
  (proof-with-checked-results
      ((generator (t2-books-admit-event (t2-books-statement-prover-generator prover) event))
       (index (if (member-equal (cadr event) '("theorem" "constrain" "axiom"))
                  (t2-book-logic-rules-update index (t2-tactics-generator-lib generator))
                index)))
    (cons index (t2-books-statement-prover-with-generator prover generator))))

(defun t2-books-book-try-candidate (prover target hints index candidates)
  (let* ((attempt (t2-books-book-prover-candidate-with-state prover target hints index))
         (result (car attempt))
         (prover (cdr attempt))
         (raw (t2-books-obligation-raw target)))
    (cond
     ((t2-books-failure-kind-p result '("Unproved"))
      (cons candidates (t2-books-book-prover-note-skip prover raw (caddr result))))
     ((t2-books-failure-kind-p result '("RecipeMismatch" "MissingBinding" "assertion" "value" "key" "recursion"))
      (cons candidates (t2-books-book-prover-note-skip prover raw "proof tactic needs another case")))
     ((failure-p result) result)
     (t (cons (table-put candidates (t2-books-obligation-name target) result) prover)))))

; Progress holds the prover, rule index, seen lines, reversed targets, and candidates.
(defun t2-books-book-event (event progress hints skips)
  (proof-with-checked-results ((event (proof-list-of-length event 3)))
    (let ((raw (car event))
          (prover (car progress))
          (index (cadr progress))
          (seen (caddr progress))
          (targets (cadddr progress))
          (candidates (nth 4 progress)))
      (if (or (member-equal raw seen)
              (member-equal raw (t2-books-book-prover-library-lines prover)))
          progress
        (proof-with-checked-results
            ((name (t2-books-first-name (cadr event) (caddr event)))
             (skip (assoc-equal name skips))
             (target (and skip (t2-books-make-obligation raw name (cadr event) (caddr event))))
             (choices (if skip
                          (t2-books-book-try-candidate prover target hints index candidates)
                        (cons candidates prover)))
             (admitted (t2-books-book-admit-event (cdr choices) index event)))
          (list (cdr admitted) (car admitted) (cons raw seen)
                (if skip (cons target targets) targets) (car choices)))))))

(defun t2-books-book-events (events progress hints skips)
  (declare (xargs :measure (acl2-count events)))
  (cond
   ((failure-p progress) progress)
   ((endp events)
    (cons (list (reverse (cadddr progress)) (nth 4 progress)) (car progress)))
   (t (t2-books-book-events (cdr events) (t2-books-book-event (car events) progress hints skips)
                           hints skips))))

(defun t2-books-book-prover-book (prover name expected skip-lines aid-events statement-events statement-source)
  (declare (ignore name))
  (proof-with-checked-results ((skips (t2-books-book-skip-sources skip-lines nil)))
    (if (not (equal (len skips) expected))
        '(:failure "failure" "")
      (proof-with-checked-results ((aids (t2-books-book-aids aid-events)))
        (let* ((measures (table-update (t2-books-book-prover-library-measures prover) (car aids)))
               (hints (cadr aids))
               (lib (t2-books-independent-theory (t2-books-book-prover-theory prover)))
               (generator (t2-books-statement-prover-generator prover))
               (generator (t2-tactics-generator-with-lib
                           (t2-tactics-generator-with-measures generator measures) lib))
               (prover (t2-books-statement-prover-with-generator prover generator)))
          (proof-with-checked-results
              ((index (t2-book-logic-rules-init lib))
               (result (t2-books-book-events statement-events (list prover index nil nil nil)
                                             hints skips)))
            (let ((targets (caar result))
                  (candidates (cadar result)))
              (if (not (equal (len targets) expected))
                  '(:failure "failure" "")
                (cons (list statement-source targets candidates skips) (cdr result))))))))))

(defun t2-books-proof-step-count (counts total)
  (if (endp counts)
      total
    (t2-books-proof-step-count (cdr counts) (+ total (car counts)))))

(defun t2-books-proof-file-sources (entries installed sources steps)
  (declare (xargs :measure (acl2-count entries)))
  (if (endp entries)
      (list (text-join "" (reverse sources)) steps installed)
    (proof-with-checked-results ((entry (proof-list-of-length (car entries) 4)))
      (let* ((label (cadr entry))
             (source (cadddr entry))
             (helper-p (member-equal (car entry) '("lemma" "define")))
             (prior (and helper-p (assoc-equal label installed))))
        (cond
         ((not prior)
          (t2-books-proof-file-sources
           (cdr entries)
           (if helper-p (table-put installed label source) installed)
           (cons source sources) (t2-books-proof-step-count (caddr entry) steps)))
         ((equal source (cdr prior))
          (t2-books-proof-file-sources (cdr entries) installed sources steps))
         (t
          (proof-with-checked-results ((name (proof-write label)))
            '(:failure "failure" ""))))))))

(defun t2-books-proof-file-skip (prover target skips)
  (let* ((name (t2-books-obligation-name target))
         (skip (assoc-equal name skips))
         (raw (t2-books-obligation-raw target))
         (reason (assoc-equal raw (t2-books-book-prover-skips prover))))
    (cond ((not skip)
           '(:failure "failure" ""))
          ((not reason)
           '(:failure "failure" ""))
          (t (list target 0 (cdr skip) (cdr reason))))))

(defun t2-books-proof-file-chunk (prover target candidates skips progress)
  (let ((candidate (table-get candidates (t2-books-obligation-name target) nil))
        (installed (car progress))
        (chunks (cdr progress)))
    (if (not candidate)
        (proof-with-checked-results ((chunk (t2-books-proof-file-skip prover target skips)))
          (cons installed (cons chunk chunks)))
      (proof-with-checked-results
          ((proof (t2-books-proof-file-sources
                   (t2-books-candidate-entries candidate) installed nil 0)))
        (cons (caddr proof) (cons (list target (cadr proof) (car proof) "") chunks))))))

(defun t2-books-proof-file-chunks (prover targets candidates skips progress)
  (declare (xargs :measure (acl2-count targets)))
  (cond
   ((failure-p progress) progress)
   ((endp targets) (reverse (cdr progress)))
   (t (t2-books-proof-file-chunks
       prover (cdr targets) candidates skips
       (t2-books-proof-file-chunk prover (car targets) candidates skips progress)))))

(defun t2-books-book-prover-proof-file (prover targets candidates skips)
  (t2-books-proof-file-chunks prover targets candidates skips (cons nil nil)))

(defun t2-books-newline-count (chars count)
  (if (endp chars)
      count
    (t2-books-newline-count
     (cdr chars) (if (eql (char-code (car chars)) 10) (1+ count) count))))

(defun t2-books-owner-of-line (chunks number)
  (if (endp chunks)
      nil
    (proof-with-checked-results ((chunk (proof-list-of-length (car chunks) 4)))
      (let ((remaining (- number (t2-books-newline-count (coerce (caddr chunk) 'list) 0))))
        (if (<= remaining 0)
            (car chunk)
          (t2-books-owner-of-line (cdr chunks) remaining))))))
