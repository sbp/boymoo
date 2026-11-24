(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun b1-division-term-at (term place)
  (declare (xargs :measure (acl2-count place)))
  (if (endp place)
      term
    (proof-with-checked-results ((part (proof-term-at term (car place))))
      (b1-division-term-at part (cdr place)))))

(defun b1-division-step-at (step place)
  (proof-with-checked-results ((literal (b1-logic-step-first step)))
    (b1-division-term-at literal place)))

(defun b1-division-bool-less (lib formula)
  (proof-proof-fact (library-library-proof lib) "booleanp-<"
                    (seq-zip (list *library-x* *library-y*) (cdr formula))))

(defun b1-division-positive-scale-cancel (lib order terms pos a inverse-law evidence)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      order
    (proof-with-checked-results
        ((numeric (b1-arithmetic-known-type lib *library-numberp* (car terms) evidence))
         (cancellation (b1-powers-multiply-inverse lib (b1-arithmetic-reciprocal a) a
                                                   (car terms) inverse-law numeric))
         (order (library-inherited proof-proof-rewrite lib order cancellation (list 1 pos))))
      (b1-division-positive-scale-cancel lib order (cdr terms) (1+ pos) a inverse-law evidence))))

(defun b1-division-positive-scale (lib comparison strict rational evidence)
  (proof-with-checked-results
      ((a (b1-division-step-at strict '(2)))
       (terms (proof-list-of-length (cdr comparison) 2)))
    (let* ((scaled (library-lt (b1-arithmetic-product a (car terms))
                               (b1-arithmetic-product a (cadr terms))))
           (rational-evidence (cons rational evidence)))
      (proof-with-checked-results
          ((original (library-inherited proof-proof-assume lib comparison t))
           (forward (b1-arithmetic-multiply-strict lib strict original rational-evidence))
           (lib (cdr forward))
           (inverse (b1-arithmetic-positive-reciprocal lib strict rational))
           (lib (cdr inverse))
           (scaled-proof (library-inherited proof-proof-assume lib scaled t))
           (inverse-order (b1-arithmetic-multiply-strict lib (car inverse)
                                                         scaled-proof rational-evidence))
           (lib (cdr inverse-order))
           (numeric (b1-arithmetic-known-type lib *library-numberp* a (list rational)))
           (nonzero (b1-arithmetic-positive-nonzero lib strict))
           (inverse-law (b1-arithmetic-inverse-product lib a numeric nonzero))
           (commute (library-library-axiom lib "COMMUTATIVITY-OF-*"
                                           (list (b1-arithmetic-reciprocal a) a)))
           (inverse-law (library-inherited proof-proof-chain lib commute (list inverse-law)))
           (inverse-order (b1-division-positive-scale-cancel lib (car inverse-order) terms
                                                             1 a inverse-law evidence))
           (no (library-inherited proof-proof-assume lib comparison nil))
           (cut (library-inherited proof-proof-cut lib inverse-order no))
           (reverse-step (library-inherited proof-proof-front lib cut (proof-neg scaled)))
           (assumed (library-inherited proof-proof-assume lib comparison t))
           (boolean (b1-division-bool-less lib comparison))
           (pos-left (b1-logic-bookproof-boolean-value lib assumed boolean))
           (boolean (b1-division-bool-less lib scaled))
           (pos-right (b1-logic-bookproof-boolean-value lib (car forward) boolean))
           (pos-right (library-inherited proof-proof-symmetric lib pos-right))
           (yes (library-inherited proof-proof-chain lib pos-left (list pos-right)))
           (no (b1-logic-bookproof-false-value lib no))
           (reverse-step (b1-logic-bookproof-false-value lib reverse-step))
           (reverse-step (library-inherited proof-proof-symmetric lib reverse-step))
           (no (library-inherited proof-proof-chain lib no (list reverse-step)))
           (result (library-inherited proof-proof-cases lib comparison yes no)))
        (cons result lib)))))

(defun b1-division-extract-factor (lib term factor)
  (declare (xargs :measure (acl2-count term)))
  (if (not (proof-is-call term *proof-times*))
      nil
    (if (not (equal (len term) 3))
        (proof-list-of-length term 3)
      (let* ((a (cadr term))
             (b (caddr term))
             (proof (library-library-proof lib)))
        (cond ((equal a factor) (proof-proof-reflexive proof term))
              ((equal b factor) (library-library-axiom lib "COMMUTATIVITY-OF-*" (list a b)))
              (t
               (proof-with-checked-results ((left (b1-division-extract-factor lib a factor)))
                 (if left
                     (proof-with-checked-results
                         ((base (proof-proof-reflexive proof term))
                          (result (proof-proof-rewrite proof base left '(1 2 1)))
                          (rest (b1-division-step-at left '(2 2)))
                          (associate (library-library-axiom lib "ASSOCIATIVITY-OF-*"
                                                             (list factor rest b))))
                       (proof-proof-chain proof result (list associate)))
                   (proof-with-checked-results ((right (b1-division-extract-factor lib b factor)))
                     (and right
                          (proof-with-checked-results
                              ((rest (b1-division-step-at right '(2 2)))
                               (base (proof-proof-reflexive proof term))
                               (result (proof-proof-rewrite proof base right '(1 2 2)))
                               (associate (library-library-axiom lib "ASSOCIATIVITY-OF-*"
                                                                  (list a factor rest)))
                               (associate (proof-proof-symmetric proof associate))
                               (result (proof-proof-chain proof result (list associate)))
                               (commute (library-library-axiom lib "COMMUTATIVITY-OF-*"
                                                                (list a factor)))
                               (result (proof-proof-rewrite proof result commute '(1 2 1)))
                               (associate (library-library-axiom lib "ASSOCIATIVITY-OF-*"
                                                                  (list factor a rest))))
                            (proof-proof-chain proof result (list associate)))))))))))))

(defun b1-division-cancel-reciprocal (lib factor argument inverse evidence)
  (let ((inv (b1-arithmetic-reciprocal factor))
        (proof (library-library-proof lib)))
    (if (equal argument inv)
        inverse
      (proof-with-checked-results ((grouping (b1-division-extract-factor lib argument inv)))
        (and grouping
             (proof-with-checked-results
                 ((base (proof-proof-reflexive proof (b1-arithmetic-product factor argument)))
                  (start (proof-proof-rewrite proof base grouping '(1 2 2)))
                  (rest (b1-division-step-at grouping '(2 2)))
                  (number (b1-arithmetic-known-type lib *library-numberp* rest evidence))
                  (cancelled (b1-powers-multiply-inverse lib factor inv rest inverse number)))
               (proof-proof-chain proof start (list cancelled))))))))

(defun b1-division-scaled-compare-negate (lib result factor terms pos)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      (cons result lib)
    (proof-with-checked-results
        ((step (b1-arithmetic-negative-left-factor lib factor (car terms)))
         (lib (cdr step))
         (result (library-inherited proof-proof-rewrite lib result (car step) (list 1 2 pos))))
      (b1-division-scaled-compare-negate lib result factor (cdr terms) (1+ pos)))))

(defun b1-division-scaled-compare-negative (lib before factor strict rational evidence)
  (proof-with-checked-results
      ((abs-rational (b1-arithmetic-known-type lib *library-rationalp*
                                              (library-minus factor) (list rational)))
       (result (b1-division-positive-scale lib before strict abs-rational evidence))
       (terms (proof-list-of-length (cdr before) 2))
       (result (b1-division-scaled-compare-negate (cdr result) (car result) factor terms 1))
       (sums (b1-arithmetic-number-sums-init (cdr result)))
       (lib (b1-arithmetic-number-sums-library sums))
       (comparison (b1-division-step-at (car result) '(2)))
       (align (b1-arithmetic-number-sums-comparison-equation
               sums comparison (library-lt (b1-arithmetic-product factor (cadr terms))
                                           (b1-arithmetic-product factor (car terms))) evidence))
       (result (library-inherited proof-proof-chain lib (car result) (list align))))
    (let ((nonzero-test (proof-eq factor *proof-zero*)))
      (proof-with-checked-results
          ((assumed (library-inherited proof-proof-assume lib nonzero-test t))
           (contradiction (library-inherited proof-proof-rewrite lib strict assumed '(1 2 1)))
           (contradiction (b1-arithmetic-simplify-first lib contradiction))
           (nonzero (library-inherited proof-proof-front lib contradiction (proof-neg nonzero-test))))
        (cons (list result nonzero) lib)))))

(defun b1-division-scaled-compare-positive (lib before strict rational evidence)
  (proof-with-checked-results
      ((result (b1-division-positive-scale lib before strict rational evidence))
       (lib (cdr result))
       (nonzero (b1-arithmetic-positive-nonzero lib strict)))
    (cons (list (car result) nonzero) lib)))

(defun b1-division-scaled-compare-cancel (lib result factor inverse evidence terms pos)
  (declare (xargs :measure (acl2-count terms)))
  (if (endp terms)
      result
    (proof-with-checked-results
        ((arg (proof-term-at (car terms) 2))
         (step (b1-division-cancel-reciprocal lib factor arg inverse evidence))
         (result (if step
                     (library-inherited proof-proof-rewrite lib result step (list 1 2 pos))
                   result)))
      (b1-division-scaled-compare-cancel lib result factor inverse evidence (cdr terms) (1+ pos)))))

(defun b1-division-scaled-compare (lib before factor strict rational evidence reversed-order)
  (proof-with-checked-results
      ((num-factor (b1-arithmetic-known-type lib *library-numberp* factor (list rational)))
       (case-result (if reversed-order
                        (b1-division-scaled-compare-negative lib before factor strict rational evidence)
                      (b1-division-scaled-compare-positive lib before strict rational evidence)))
       (lib (cdr case-result))
       (result (caar case-result))
       (inverse (b1-arithmetic-inverse-product lib factor num-factor (cadar case-result)))
       (comparison (b1-division-step-at result '(2)))
       (result (b1-division-scaled-compare-cancel lib result factor inverse evidence
                                                  (cdr comparison) 1)))
    (cons result lib)))

(defun b1-division-zero-product-rule (lib term)
  (and (proof-is-call term *proof-times*)
       (proof-with-checked-results ((parts (proof-list-of-length term 3)))
         (let ((a (cadr parts))
               (b (caddr parts)))
           (cond ((equal b *proof-zero*) (b1-arithmetic-multiply-zero lib a))
                 ((equal a *proof-zero*)
                  (proof-with-checked-results
                      ((commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list a b)))
                       (zero (b1-arithmetic-multiply-zero lib b)))
                    (library-inherited proof-proof-chain lib commute (list zero)))))))))

(defun b1-division-normalize-zero-products-run (lib term rules provep replies)
  (if provep
      (b1-logic-bookproof-normalize-proof-with-library lib term nil nil rules nil replies)
    (b1-logic-bookproof-normalize-with-library lib term nil nil rules nil nil nil replies)))

(defun b1-division-normalize-zero-products-replay (n lib term rules provep replies result)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "b1-division-normalize-zero-products-replay")
    (cond ((failure-p result) result)
          ((b1-logic-call-p result)
           (let* ((current (b1-logic-call-library result))
                  (step (b1-division-zero-product-rule current (b1-logic-call-term result)))
                  (reply (if (failure-p step) step (cons step current)))
                  (replies (append replies (list reply))))
             (b1-division-normalize-zero-products-replay
              (1- n) lib term rules provep replies
              (b1-division-normalize-zero-products-run lib term rules provep replies))))
          (t (car result)))))

(defun b1-division-normalize-zero-products (lib term rules provep)
  (let ((rules (append rules '((:callback :zero-product)))))
    (b1-division-normalize-zero-products-replay
     1000000 lib term rules provep nil
     (b1-division-normalize-zero-products-run lib term rules provep nil))))

(defun b1-division-product-with-inverse-unit (lib x second unit)
  (if (equal second (b1-arithmetic-reciprocal x))
      unit
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((final (proof-term-at second 2))
           (associate (library-library-axiom lib "ASSOCIATIVITY-OF-*"
                                             (list x (b1-arithmetic-reciprocal x) final)))
           (distributive (proof-proof-symmetric proof associate))
           (unit (proof-proof-rewrite proof distributive unit '(1 2 1)))
           (identity (library-library-axiom lib "UNICITY-OF-1" (list final))))
        (proof-proof-chain proof unit (list identity))))))

(defun b1-division-product-with-inverse (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (product-parts (proof-list-of-length (cadr parts) 3))
         (test (proof-term-at (caddr parts) 1)))
      (let ((lhs (cadr parts))
            (choices (caddr parts))
            (x (cadr product-parts))
            (second (caddr product-parts)))
        (proof-with-checked-results
            ((not-zero (proof-proof-assume proof test nil))
             (nonzero-fix (b1-reciprocal-reverse-inequality lib not-zero))
             (types (b1-powers-nonzero-fixed-base lib x nonzero-fix))
             (unit (b1-arithmetic-inverse-product lib x (car types) (cadr types)))
             (unit (b1-division-product-with-inverse-unit lib x second unit))
             (unselected (proof-proof-if-false proof choices))
             (unselected (proof-proof-symmetric proof unselected))
             (no (proof-proof-chain proof unit (list unselected)))
             (zero (proof-proof-assume proof test t)))
          (let* ((type-test (list *library-numberp* x))
                 (fixed (list *b1-powers-fix* x)))
            (proof-with-checked-results
                ((xt (proof-proof-assume proof type-test t))
                 (zero (proof-proof-symmetric proof zero))
                 (exact (b1-logic-bookproof-normalize lib fixed (list xt) (list *b1-powers-fix*)
                                                     nil nil nil nil))
                 (zero-x (proof-proof-rewrite proof zero exact '(1 1)))
                 (numeric-zero (b1-division-normalize-zero-products
                                 lib lhs (list (b1-logic-equal-to zero-x)) nil))
                 (not-numeric (proof-proof-assume proof type-test nil))
                 (other (b1-arithmetic-nonnumeric-product lib lhs not-numeric nil))
                 (numeric-cases (proof-proof-cases proof type-test numeric-zero other))
                 (selected (proof-proof-if-true proof choices))
                 (selected (proof-proof-symmetric proof selected))
                 (yes (proof-proof-chain proof numeric-cases (list selected))))
              (proof-proof-cases proof test yes no))))))))

(defun b1-division-align-comparison-args (lib equivalence actuals expecteds pos)
  (declare (xargs :measure (acl2-count actuals)))
  (if (or (endp actuals) (endp expecteds))
      equivalence
    (proof-with-checked-results
        ((result
          (if (equal (car actuals) (car expecteds))
              equivalence
            (proof-with-checked-results
                ((commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (cdar actuals)))
                 (term (b1-division-step-at commute '(2))))
              (if (equal term (car expecteds))
                  (library-inherited proof-proof-rewrite lib equivalence commute (list 1 2 pos))
                '(:failure "failure" ""))))))
      (b1-division-align-comparison-args lib result (cdr actuals) (cdr expecteds) (1+ pos)))))

(defun b1-division-align-comparison (lib equivalence right)
  (proof-with-checked-results ((comparison (b1-division-step-at equivalence '(2))))
    (b1-division-align-comparison-args lib equivalence (cdr comparison) (cdr right) 1)))

(defun b1-division-divide-positive-consequence (guard lib formula)
  (proof-with-checked-results
      ((parts (b1-logic-bookproof-split-conjuncts lib guard)))
    (if (< (len parts) 2)
        '(:failure "failure" "")
      (proof-with-checked-results
          ((goal (proof-term-at formula 2))
           (tests (proof-list-of-length (cdr goal) 2))
           (factor (b1-division-step-at (car parts) '(2)))
           (equivalence (b1-division-scaled-compare lib (car tests) factor (car parts) (cadr parts)
                                                   (cddr parts) nil))
           (lib (cdr equivalence))
           (step (b1-division-align-comparison lib (car equivalence) (cadr tests))))
        (cons step lib)))))

(defun b1-division-divide-positive (lib formula)
  (proof-with-checked-results
      ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-division-divide-positive-consequence premise lib formula))
       (lib (cdr consequence))
       (step (b1-logic-bookproof-prove-implication-with-premise
              lib formula premise (car consequence))))
    (cons step lib)))

(defun b1-division-divide-by-sign-find-rational (evidence x)
  (declare (xargs :measure (acl2-count evidence)))
  (if (endp evidence)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (b1-logic-step-first (car evidence))))
      (if (equal literal (list *library-rationalp* x))
          (car evidence)
        (b1-division-divide-by-sign-find-rational (cdr evidence) x)))))

(defun b1-division-divide-by-sign-consequence-compare
    (displayed sign reverse-order lib x left inverted rat evidence)
  (let ((before (if inverted displayed left))
        (after (if inverted left displayed)))
    (proof-with-checked-results
        ((equality (b1-division-scaled-compare lib before x sign rat evidence reverse-order))
         (lib (cdr equality))
         (equality (b1-division-align-comparison lib (car equality) after))
         (equality (if inverted (library-inherited proof-proof-symmetric lib equality) equality)))
      (cons equality lib))))

(defun b1-division-divide-by-sign-consequence
    (guard lib x left choices choice-parts further-parts inverted)
  (let ((pos-test (car choice-parts))
        (on-positive (cadr choice-parts))
        (further (caddr choice-parts))
        (zero-test (car further-parts))
        (on-zero (cadr further-parts))
        (on-negative (caddr further-parts)))
    (proof-with-checked-results
        ((evidence (b1-logic-bookproof-split-conjuncts lib guard))
         (rat (b1-division-divide-by-sign-find-rational evidence x))
         (numeric (b1-arithmetic-known-type lib *library-numberp* x (list rat)))
         (positive-x (library-inherited proof-proof-assume lib pos-test t))
         (no-positive (library-inherited proof-proof-assume lib pos-test nil))
         (not-zero (library-inherited proof-proof-assume lib zero-test nil))
         (not-zero (b1-reciprocal-reverse-inequality lib not-zero))
         (trichotomy (library-library-axiom lib "TRICHOTOMY" (list x)))
         (branches (library-inherited proof-proof-conjunct lib trichotomy))
         (order (library-inherited proof-proof-modus-ponens lib (car branches) numeric))
         (order (library-inherited proof-proof-prove-if lib order no-positive))
         (positive-minus-x (library-inherited proof-proof-prove-if lib order not-zero))
         (selected (library-inherited proof-proof-if-true lib choices))
         (yes (b1-division-divide-by-sign-consequence-compare
               on-positive positive-x nil lib x left inverted rat evidence))
         (lib (cdr yes))
         (selected (library-inherited proof-proof-symmetric lib selected))
         (yes (library-inherited proof-proof-chain lib (car yes) (list selected)))
         (zero-eq (library-inherited proof-proof-assume lib zero-test t))
         (zero-eq (library-inherited proof-proof-symmetric lib zero-eq))
         (base (b1-division-normalize-zero-products
                lib (proof-eq left on-zero) (list (b1-logic-equal-to zero-eq)) t))
         (zero-choice (library-inherited proof-proof-if-true lib further))
         (zero-choice (library-inherited proof-proof-symmetric lib zero-choice))
         (base (library-inherited proof-proof-chain lib base (list zero-choice)))
         (negative (b1-division-divide-by-sign-consequence-compare
                    on-negative positive-minus-x t lib x left inverted rat evidence))
         (lib (cdr negative))
         (negative-choice (library-inherited proof-proof-if-false lib further))
         (negative-choice (library-inherited proof-proof-symmetric lib negative-choice))
         (negative (library-inherited proof-proof-chain lib (car negative) (list negative-choice)))
         (zero-cases (library-inherited proof-proof-cases lib zero-test base negative))
         (unselected (library-inherited proof-proof-if-false lib choices))
         (unselected (library-inherited proof-proof-symmetric lib unselected))
         (no (library-inherited proof-proof-chain lib zero-cases (list unselected)))
         (step (library-inherited proof-proof-cases lib pos-test yes no)))
      (cons step lib))))

(defun b1-division-divide-by-sign (lib formula inverted)
  (proof-with-checked-results
      ((goal (proof-term-at formula 2))
       (goal-parts (proof-list-of-length (cdr goal) 2))
       (choice-parts (proof-list-of-length (cdadr goal-parts) 3))
       (further-parts (proof-list-of-length (cdr (caddr choice-parts)) 3))
       (x (proof-term-at (car choice-parts) 2))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-division-divide-by-sign-consequence
                     premise lib x (car goal-parts) (cadr goal-parts) choice-parts further-parts inverted))
       (lib (cdr consequence))
       (step (b1-logic-bookproof-prove-implication-with-premise lib formula premise
                                                             (car consequence))))
    (cons step lib)))

(defun b1-division-equal-tests (lib original forward backward)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (b1-logic-step-first original))
         (left-false (proof-proof-assume proof test nil))
         (cut (proof-proof-cut proof backward left-false))
         (right-test (b1-logic-step-first forward))
         (right-false (proof-proof-front proof cut (proof-neg right-test)))
         (left-true (b1-logic-bookproof-equality-true lib original))
         (right-true (b1-logic-bookproof-equality-true lib forward))
         (right-true (proof-proof-symmetric proof right-true))
         (yes (proof-proof-chain proof left-true (list right-true)))
         (left-false (b1-logic-bookproof-false-value lib left-false))
         (right-false (b1-logic-bookproof-false-value lib right-false))
         (right-false (proof-proof-symmetric proof right-false))
         (no (proof-proof-chain proof left-false (list right-false))))
      (proof-proof-cases proof test yes no))))

(defun b1-division-scaled-equality-cancel (lib restored reciprocal-a a inverse-back parts index)
  (declare (xargs :measure (acl2-count parts)))
  (if (endp parts)
      restored
    (proof-with-checked-results
        ((cancellation (b1-powers-multiply-inverse lib reciprocal-a a (caar parts)
                                                   inverse-back (cadar parts)))
         (restored (library-inherited proof-proof-rewrite lib restored cancellation (list 1 index))))
      (b1-division-scaled-equality-cancel lib restored reciprocal-a a inverse-back
                                         (cdr parts) (1+ index)))))

(defun b1-division-scaled-equality (lib comparison factor-type nonzero left-type right-type)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((a (b1-division-step-at factor-type '(1)))
         (terms (proof-list-of-length (cdr comparison) 2)))
      (let* ((left (car terms))
             (right (cadr terms))
             (scaled-left (b1-arithmetic-product a left))
             (scaled-right (b1-arithmetic-product a right))
             (scaled (proof-eq scaled-left scaled-right)))
        (proof-with-checked-results
            ((original (proof-proof-assume proof comparison t))
             (forward (proof-proof-reflexive proof scaled-left))
             (forward (proof-proof-rewrite proof forward original '(1 2 2)))
             (inverse (b1-arithmetic-inverse-product lib a factor-type nonzero)))
          (let ((reciprocal-a (b1-arithmetic-reciprocal a)))
            (proof-with-checked-results
                ((commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list reciprocal-a a)))
                 (inverse-back (proof-proof-chain proof commute (list inverse)))
                 (restored (proof-proof-reflexive proof (b1-arithmetic-product reciprocal-a scaled-left)))
                 (scaled-step (proof-proof-assume proof scaled t))
                 (restored (proof-proof-rewrite proof restored scaled-step '(1 2 2)))
                 (restored (b1-division-scaled-equality-cancel lib restored reciprocal-a a inverse-back
                                                             (list (list left left-type)
                                                                   (list right right-type)) 1)))
              (b1-division-equal-tests lib original forward restored))))))))

(defun b1-division-zero-reciprocal (lib term fixed-zero)
  (let ((proof (library-library-proof lib))
        (test (list *library-numberp* term)))
    (proof-with-checked-results
        ((numeric (proof-proof-assume proof test t))
         (complete (library-library-axiom lib "COMPLETION-OF-UNARY-/" (list term)))
         (exact (b1-logic-bookproof-normalize lib (list *b1-powers-fix* term) (list numeric)
                                             (list *b1-powers-fix*) nil nil nil nil))
         (is-zero (proof-proof-rewrite proof fixed-zero exact '(1 1)))
         (target (b1-division-step-at complete '(2)))
         (yes (b1-logic-bookproof-normalize lib target (list numeric is-zero) (list *proof-not*)
                                           nil nil nil nil))
         (not-numeric (proof-proof-assume proof test nil))
         (no (b1-logic-bookproof-normalize lib target (list not-numeric) (list *proof-not*)
                                          nil nil nil nil))
         (cases (proof-proof-cases proof test yes no)))
      (proof-proof-chain proof complete (list cases)))))

(defun b1-division-mixed-numeric-equality (lib comparison nonnumeric numeric)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof comparison t))
         (numeric-term (b1-division-step-at numeric '(1)))
         (left (proof-term-at comparison 1))
         (assumed (if (equal numeric-term left) (proof-proof-symmetric proof assumed) assumed))
         (other (library-library-transport-argument lib numeric assumed 1))
         (contradiction (proof-proof-cut proof other nonnumeric))
         (refuted (proof-proof-front proof contradiction (proof-neg comparison))))
      (b1-logic-bookproof-false-value lib refuted))))

(defun b1-division-multiply-division-equality (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (before-parts (proof-list-of-length (cadr parts) 3))
         (divided-parts (proof-list-of-length (caddr before-parts) 3))
         (x (proof-term-at (cadr divided-parts) 1))
         (choice-parts (proof-list-of-length (cdr (caddr parts)) 3))
         (zero-test (proof-term-at (cadr choice-parts) 1)))
      (let ((before (cadr parts))
            (choices (caddr parts))
            (divided (caddr before-parts))
            (inv (cadr divided-parts))
            (y (caddr divided-parts))
            (number-z (car choice-parts))
            (zero-choices (cadr choice-parts)))
        (proof-with-checked-results
            ((numeric (proof-proof-assume proof number-z t))
             (not-zero (proof-proof-assume proof zero-test nil))
             (factor (b1-powers-nonzero-fixed-base lib x not-zero))
             (divided-type (b1-arithmetic-known-type lib *library-numberp* divided nil))
             (scaled (b1-division-scaled-equality lib before (car factor) (cadr factor) numeric divided-type))
             (inverse (b1-arithmetic-inverse-product lib x (car factor) (cadr factor)))
             (associate (library-library-axiom lib "ASSOCIATIVITY-OF-*" (list x inv y)))
             (expanded (proof-proof-symmetric proof associate))
             (expanded (proof-proof-rewrite proof expanded inverse '(1 2 1)))
             (identity (library-library-axiom lib "UNICITY-OF-1" (list y)))
             (expanded (proof-proof-chain proof expanded (list identity)))
             (scaled (proof-proof-rewrite proof scaled expanded '(1 2 2)))
             (unselected (proof-proof-if-false proof zero-choices))
             (unselected (proof-proof-symmetric proof unselected))
             (nonzero-case (proof-proof-chain proof scaled (list unselected)))
             (assumed (proof-proof-assume proof zero-test t))
             (inverse-zero (b1-division-zero-reciprocal lib x assumed))
             (empty (b1-division-normalize-zero-products
                     lib before (list (b1-logic-equal-to inverse-zero)) nil))
             (selected (proof-proof-if-true proof zero-choices))
             (selected (proof-proof-symmetric proof selected))
             (zero-case (proof-proof-chain proof empty (list selected)))
             (with-number (proof-proof-cases proof zero-test zero-case nonzero-case))
             (selected (proof-proof-if-true proof choices))
             (selected (proof-proof-symmetric proof selected))
             (with-number (proof-proof-chain proof with-number (list selected)))
             (not-number (proof-proof-assume proof number-z nil))
             (outside (b1-division-mixed-numeric-equality lib before not-number divided-type))
             (unselected (proof-proof-if-false proof choices))
             (unselected (proof-proof-symmetric proof unselected))
             (outside (proof-proof-chain proof outside (list unselected))))
          (proof-proof-cases proof number-z with-number outside))))))

(defun b1-division-reciprocal-equality-consequence
    (premise lib before choices choice-parts x y inv)
  (declare (ignore premise))
  (let ((proof (library-library-proof lib))
        (zero-test (car choice-parts))
        (on-zero (cadr choice-parts))
        (on-nonzero (caddr choice-parts))
        (numeric-x-test (list *library-numberp* x)))
    (proof-with-checked-results
        ((zero (proof-proof-assume proof zero-test t))
         (zero-is-fix (proof-proof-symmetric proof zero))
         (inverse-zero (b1-division-zero-reciprocal lib y zero-is-fix))
         (opened (b1-logic-bookproof-normalize lib before nil nil (list (b1-logic-equal-to inverse-zero))
                                               nil nil nil))
         (target (b1-division-step-at opened '(2)))
         (exact (proof-proof-assume proof target t))
         (reverse-exact (proof-proof-symmetric proof exact))
         (zero (proof-proof-assume proof on-zero t))
         (zero (proof-proof-symmetric proof zero))
         (swap (b1-division-equal-tests lib exact reverse-exact zero))
         (selected (proof-proof-if-true proof choices))
         (selected (proof-proof-symmetric proof selected))
         (zero-case (proof-proof-chain proof opened (list swap selected)))
         (not-zero (proof-proof-assume proof zero-test nil))
         (not-zero (b1-reciprocal-reverse-inequality lib not-zero))
         (factor (b1-powers-nonzero-fixed-base lib y not-zero))
         (inverse-type (b1-arithmetic-known-type lib *library-numberp* inv nil))
         (numeric-x (proof-proof-assume proof numeric-x-test t))
         (scaled (b1-division-scaled-equality lib before (car factor) (cadr factor) numeric-x inverse-type))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list y x)))
         (scaled (proof-proof-rewrite proof scaled commute '(1 2 1)))
         (inverse (b1-arithmetic-inverse-product lib y (car factor) (cadr factor)))
         (scaled (proof-proof-rewrite proof scaled inverse '(1 2 2)))
         (not-numeric-x (proof-proof-assume proof numeric-x-test nil))
         (left-false (b1-division-mixed-numeric-equality lib before not-numeric-x inverse-type))
         (product (proof-term-at on-nonzero 1))
         (product-zero (b1-arithmetic-nonnumeric-product lib product not-numeric-x nil))
         (right-false (b1-logic-bookproof-normalize lib on-nonzero nil nil
                                                   (list (b1-logic-equal-to product-zero)) nil nil nil))
         (right-false (proof-proof-symmetric proof right-false))
         (nonnumber (proof-proof-chain proof left-false (list right-false)))
         (nonzero-case (proof-proof-cases proof numeric-x-test scaled nonnumber))
         (unselected (proof-proof-if-false proof choices))
         (unselected (proof-proof-symmetric proof unselected))
         (nonzero-case (proof-proof-chain proof nonzero-case (list unselected))))
      (proof-proof-cases proof zero-test zero-case nonzero-case))))

(defun b1-division-reciprocal-equality (lib formula)
  (proof-with-checked-results
      ((goal (proof-term-at formula 2))
       (goal-parts (proof-list-of-length goal 3))
       (before-parts (proof-list-of-length (cadr goal-parts) 3))
       (y (proof-term-at (caddr before-parts) 1))
       (choice-parts (proof-list-of-length (cdr (caddr goal-parts)) 3))
       (premise (b1-logic-bookproof-prove-implication-premise lib formula))
       (consequence (b1-division-reciprocal-equality-consequence
                     premise lib (cadr goal-parts) (caddr goal-parts) choice-parts
                     (cadr before-parts) y (caddr before-parts))))
    (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence)))
