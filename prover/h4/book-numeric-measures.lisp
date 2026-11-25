(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-numeric-measures-countdown-integer*
  (proof-sym "H4-COUNTDOWN-INTEGER" "ACL2"))
(defconst *h4-book-numeric-measures-countdown-positive*
  (proof-sym "H4-COUNTDOWN-POSITIVE" "ACL2"))
(defconst *h4-book-numeric-measures-positive-fix* (proof-sym "PFIX" "ACL2"))
(defconst *h4-book-numeric-measures-natural-fix* (proof-sym "NFIX" "ACL2"))

(defun h4-book-numeric-measures-first-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h4-book-numeric-measures-step-map (steps evidence)
  (if (endp steps)
      evidence
    (proof-with-checked-results ((literal (proof-step-first (car steps))))
      (h4-book-numeric-measures-step-map
       (cdr steps) (table-put evidence literal (car steps))))))

(defun h4-book-numeric-measures-signed-countdowns (p call)
  (proof-with-checked-results
   ((steps (h4-book-measures-rule-tests p (termination-call-tests call))))
   (h4-book-numeric-measures-step-map steps nil)))

(defun h4-book-numeric-measures-positive-integer (p term evidence)
  (let* ((key (proof-neg (list *h4-book-arithmetic-zp* term)))
         (entry (assoc-equal key evidence))
         (proof (library-library-proof p))
         (bindings (list (list *library-x* term))))
    (if (not entry)
        '(:failure "missing-proof-input" "")
      (proof-with-checked-results
       ((integral (proof-proof-use proof *h4-book-numeric-measures-countdown-integer*
                                  bindings (list (cdr entry))))
        (positive (proof-proof-use proof *h4-book-numeric-measures-countdown-positive*
                                  bindings (list (cdr entry)))))
       (list integral positive)))))

(defun h4-book-numeric-measures-floor-parts (term)
  (proof-with-checked-results
   ((parts
     (cond
      ((proof-is-call term *h4-book-division-floor*)
       (proof-list-of-length (cdr term) 2))
      ((and (proof-compound term) (equal (len term) 2)
            (not (proof-compound (car term)))
            (proof-is-call (cadr term) *proof-times*))
       (proof-with-checked-results ((product (proof-list-of-length (cadr term) 3)))
         (let ((reciprocal (caddr product)))
           (and (proof-is-call reciprocal *h4-book-division-reciprocal*)
                (proof-with-checked-results ((base (proof-term-at reciprocal 1)))
                  (list (cadr product) base))))))
      (t nil))))
   (let ((base (cadr parts)))
     (and (proof-is-call base *proof-quote*)
       (proof-with-checked-results ((number (proof-term-at base 1)))
         (and (integerp number) (< 1 number) parts))))))

(defun h4-book-numeric-measures-same-arity-p (calls arity)
  (if (endp calls)
      t
    (and (equal (len (termination-call-actuals (car calls))) arity)
         (h4-book-numeric-measures-same-arity-p (cdr calls) arity))))

(defun h4-book-numeric-measures-floor-column-p (calls index)
  (if (endp calls)
      t
    (proof-with-checked-results
     ((actual (proof-term-at (termination-call-actuals (car calls)) index))
      (parts (h4-book-numeric-measures-floor-parts actual)))
     (and parts (h4-book-numeric-measures-floor-column-p (cdr calls) index)))))

(defun h4-book-numeric-measures-some-floor-column-p (positions calls index)
  (and (consp positions)
       (proof-with-checked-results
        ((column (h4-book-numeric-measures-floor-column-p calls index)))
        (or column (h4-book-numeric-measures-some-floor-column-p
                    (cdr positions) calls (1+ index))))))

(defun h4-book-numeric-measures-uses-floor-measure (calls)
  (and (consp calls)
       (let ((actuals (termination-call-actuals (car calls))))
         (and (h4-book-numeric-measures-same-arity-p calls (len actuals))
              (h4-book-numeric-measures-some-floor-column-p actuals calls 0)))))

(defun h4-book-numeric-measures-subtraction-calls-p (calls first second)
  (if (endp calls)
      t
    (let ((actuals (termination-call-actuals (car calls))))
      (and (or (equal actuals first) (equal actuals second))
           (h4-book-numeric-measures-subtraction-calls-p (cdr calls) first second)))))

(defun h4-book-numeric-measures-subtraction-step (p call a b total first)
  (proof-with-checked-results
   ((evidence (h4-book-numeric-measures-signed-countdowns p call))
    (x-steps (h4-book-numeric-measures-positive-integer p a evidence))
    (y-steps (h4-book-numeric-measures-positive-integer p b evidence)))
   (let* ((integers (list (car x-steps) (car y-steps)))
          (actuals (termination-call-actuals call))
          (past (library-plus (car actuals) (cadr actuals)))
          (decrease-by (if (equal actuals first) (cadr y-steps) (cadr x-steps))))
     (proof-with-checked-results
      ((positive-total (library-library-cite p "POSITIVE-SUM" (list a b)
                                           (list (cadr x-steps) (cadr y-steps))))
       (smaller (library-library-less-from-difference p past total decrease-by integers))
       (past-type (library-library-type-of p past integers))
       (total-type (library-library-type-of p total integers)))
      (library-library-cite p "NFIX-DECREASE" (list past total)
                            (list past-type total-type positive-total smaller))))))

(defun h4-book-numeric-measures-rational (p term evidence)
  (proof-with-checked-results
   ((axiom (library-library-axiom p "INTEGER-IMPLIES-RATIONAL" (list term)))
    (type-step (library-library-type-of p term evidence)))
   (h4-tactics-tactics-modus-ponens p axiom type-step)))

(defun h4-book-numeric-measures-floor-view-positions (proof equality product unit positions)
  (if (endp positions)
      equality
    (proof-with-checked-results
     ((equality (if (equal (caar positions) product)
                    (proof-proof-rewrite proof equality unit (list* 1 2 (cadar positions)))
                  equality)))
     (h4-book-numeric-measures-floor-view-positions
      proof equality product unit (cdr positions)))))

(defun h4-book-numeric-measures-floor-view (p actual value base integers)
  (let ((floor (list *h4-book-division-floor* value base))
        (proof (library-library-proof p)))
    (if (equal actual floor)
        (proof-proof-reflexive proof floor)
      (proof-with-checked-results
       ((ratio (proof-term-at actual 1))
        (alias (proof-proof-unfold proof actual))
        (alias-rhs (h4-book-numeric-measures-first-at alias 2)))
       (if (not (equal alias-rhs (list *h4-book-division-floor* ratio *proof-one*)))
           '(:failure "inapplicable-step" "")
         (proof-with-checked-results
          ((law (proof-proof-fact proof "rationalp-unary-/" (list (list *library-x* base))))
           (base-type (h4-book-numeric-measures-rational p base nil))
           (reciprocal (h4-tactics-tactics-modus-ponens p law base-type))
           (ratio-factor (proof-term-at ratio 2))
           (law (proof-proof-fact proof "rationalp-binary-*"
                                  (list (list *library-x* value) (list *library-y* ratio-factor))))
           (value-type (h4-book-numeric-measures-rational p value integers))
           (premise (h4-book-division-conjunction p (list value-type reciprocal)))
           (ratio-rational (h4-tactics-tactics-modus-ponens p law premise))
           (law (proof-proof-fact proof "rationalp-acl2-numberp" (list (list *library-x* ratio))))
           (number (h4-tactics-tactics-modus-ponens p law ratio-rational))
           (fixed (h4-tactics-tactics-normalize
                   p (list *h4-book-division-fix* ratio) (list number)
                   (list *h4-book-division-fix*) nil nil))
           (commutativity (library-library-axiom p "COMMUTATIVITY-OF-*" (list ratio *proof-one*)))
           (unicity (library-library-axiom p "UNICITY-OF-1" (list ratio)))
           (unit (proof-proof-chain proof commutativity (list unicity fixed)))
           (inverse (list *h4-book-division-reciprocal* *proof-one*))
           (product (list *proof-times* ratio inverse))
           (inverse-one (proof-proof-compute proof inverse 1))
           (product-reflexive (proof-proof-reflexive proof product))
           (product-unit (proof-proof-rewrite proof product-reflexive inverse-one '(1 2 2)))
           (unit (proof-proof-chain proof product-unit (list unit)))
           (opened (proof-proof-unfold proof alias-rhs))
           (body (h4-book-numeric-measures-first-at opened 2))
           (opened (h4-tactics-tactics-rewrite-context p body :none opened))
           (body (h4-book-numeric-measures-first-at opened 2))
           (positions (h4-book-equivalence-positions body nil))
           (opened (h4-book-numeric-measures-floor-view-positions
                    proof opened product unit positions))
           (original (proof-proof-unfold proof floor))
           (body (h4-book-numeric-measures-first-at original 2))
           (logical (h4-tactics-tactics-rewrite-context p body :none original))
           (reverse (proof-proof-symmetric proof logical)))
          (proof-proof-chain proof alias (list opened reverse))))))))

(defun h4-book-numeric-measures-division-step (p call index)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((actual (proof-term-at (termination-call-actuals call) index))
      (parts (h4-book-numeric-measures-floor-parts actual))
      (parts (proof-list-of-length parts 2))
      (value (car parts))
      (base (cadr parts))
      (evidence (h4-book-numeric-measures-signed-countdowns p call))
      (steps (h4-book-numeric-measures-positive-integer p value evidence))
      (integral (car steps))
      (positive (cadr steps))
      (lemma (proof-proof-fact proof *h4-book-division-floor-bounds*
                              (list (list *library-x* value) (list *library-y* base))))
      (base-type (library-library-type-of p base nil))
      (base-bound (h4-tactics-tactics-establish p (library-lt *proof-one* base) nil nil nil nil))
      (premise (h4-book-division-conjunction p (list integral positive base-type base-bound)))
      (bounds (h4-tactics-tactics-modus-ponens p lemma premise))
      (conjuncts (h4-tactics-tactics-conjunct p bounds))
      (natural (car conjuncts))
      (smaller (cadr conjuncts))
      (floor (list *h4-book-division-floor* value base))
      (floor-integer (library-library-cite p "NATURAL-INTEGER" (list floor) (list natural)))
      (step (library-library-cite p "NFIX-DECREASE" (list floor value)
                                  (list floor-integer integral positive smaller)))
      (view (h4-book-numeric-measures-floor-view p actual value base (list integral)))
      (reverse (proof-proof-symmetric proof view)))
     (proof-proof-rewrite proof step reverse '(1 1 1)))))

(defun h4-book-numeric-measures-call-proofs (p definitions measures calls recipe arguments proofs)
  (if (endp calls)
      (table-values proofs)
    (proof-with-checked-results
     ((cases (termination-obligation-cases definitions measures (list (car calls))))
      (clause (caadr cases))
      (step (if (eq recipe :subtraction)
                (h4-book-numeric-measures-subtraction-step
                 p (car calls) (car arguments) (cadr arguments) (caddr arguments) (cadddr arguments))
              (h4-book-numeric-measures-division-step p (car calls) (car arguments))))
      (step (proof-proof-subsume (library-library-proof p) step clause)))
     (h4-book-numeric-measures-call-proofs
      p definitions measures (cdr calls) recipe arguments (table-put proofs clause step)))))

(defun h4-book-numeric-measures-measure-result (p definitions calls function-name value recipe arguments)
  (let* ((measure (list *library-nfix* value))
         (measures (list (cons function-name measure))))
    (proof-with-checked-results
     ((cases (termination-obligation-cases definitions measures nil))
      (clause (caar cases))
      (ordinal (library-library-cite p "NFIX-ORDINAL" (list value) nil))
      (ordinal (proof-proof-subsume (library-library-proof p) ordinal clause))
      (proofs (h4-book-numeric-measures-call-proofs
               p definitions measures calls recipe arguments (list (cons clause ordinal)))))
     (list (list measure) proofs))))

(defun h4-book-numeric-measures-subtraction-measure (p definitions calls)
  (and (equal (len definitions) 1)
    (proof-with-checked-results ((formals (proof-term-at (car definitions) 1)))
      (and (equal (len formals) 2)
        (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
          (let* ((a (car formals))
                 (b (cadr formals))
                 (first (list (library-diff a b) b))
                 (second (list a (library-diff b a))))
            (and (h4-book-numeric-measures-subtraction-calls-p calls first second)
              (let ((total (library-plus a b)))
                (h4-book-numeric-measures-measure-result
                 p definitions calls (car definition) total :subtraction (list a b total first))))))))))

(defun h4-book-numeric-measures-division-updates (calls index)
  (if (endp calls)
      nil
    (proof-with-checked-results
     ((actual (proof-term-at (termination-call-actuals (car calls)) index))
      (parts (h4-book-numeric-measures-floor-parts actual))
      (rest (h4-book-numeric-measures-division-updates (cdr calls) index)))
     (cons parts rest))))

(defun h4-book-numeric-measures-division-formal-p (updates formal)
  (if (endp updates)
      t
    (and (consp (car updates)) (equal (caar updates) formal)
         (h4-book-numeric-measures-division-formal-p (cdr updates) formal))))

(defun h4-book-numeric-measures-division-target (formals calls index)
  (and (consp formals)
    (proof-with-checked-results
     ((updates (h4-book-numeric-measures-division-updates calls index)))
     (if (h4-book-numeric-measures-division-formal-p updates (car formals))
         (list index (car formals))
       (h4-book-numeric-measures-division-target (cdr formals) calls (1+ index))))))

(defun h4-book-numeric-measures-result-with-library (result p allow-fallback)
  (cond ((not (failure-p result)) (cons result p))
        ((and allow-fallback
              (member-equal (cadr result)
                            '("inapplicable-step" "inapplicable-term" "missing-proof-input"
                              "assertion" "value" "key" "unproved")))
         (cons nil p))
        (t result)))

(defun h4-book-numeric-measures-division-attempt (p definitions calls support allow-fallback)
  (let ((target
         (and (and (equal (len definitions) 1) support)
           (proof-with-checked-results ((floor (h4-book-numeric-measures-uses-floor-measure calls)))
             (and floor
               (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
                 (h4-book-numeric-measures-division-target (cadr definition) calls 0)))))))
    (if (or (null target) (failure-p target))
        (h4-book-numeric-measures-result-with-library target p allow-fallback)
      (let* ((proof (library-library-proof p))
             (facts (table-update (proof-proof-facts proof) support))
             (p (library-library-with-proof p (proof-proof-with-facts proof facts)))
             (result (h4-book-numeric-measures-measure-result
                      p definitions calls (caar definitions) (cadr target) :division (list (car target)))))
        (h4-book-numeric-measures-result-with-library result p allow-fallback)))))

(defun h4-book-numeric-measures-fixed-value-type-components (hypothesis p opened test)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((body (h4-book-numeric-measures-first-at opened 2))
      (choice (proof-proof-select proof body hypothesis))
      (selected (proof-proof-chain proof opened (list choice)))
      (literal (proof-step-first hypothesis))
      (parts (if (equal literal test)
                 (h4-tactics-tactics-conjunct p hypothesis)
               (proof-with-checked-results
                ((fallback (h4-book-numeric-measures-first-at selected 2))
                 (integral (library-library-type-of p fallback nil))
                 (positive (h4-tactics-tactics-establish p (library-positive fallback) nil nil nil nil)))
                (list integral positive))))
      (first (library-library-transport-argument p (car parts) selected 1))
      (second (library-library-transport-argument p (cadr parts) selected 2)))
     (list first second))))

(defun h4-book-numeric-measures-fixed-natural-type (p value opened test body)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((assumption (proof-proof-assume proof test t))
      (natural (proof-proof-unfold proof (list *library-natp* value)))
      (given (proof-proof-transport proof assumption natural))
      (fallback-term (proof-term-at body 3))
      (fallback (library-library-natural p fallback-term))
      (yes (proof-proof-if-true proof body))
      (yes (proof-proof-chain proof opened (list yes)))
      (yes (library-library-transport-argument p given yes 1))
      (no (proof-proof-if-false proof body))
      (no (proof-proof-chain proof opened (list no)))
      (no (library-library-transport-argument p fallback no 1)))
     (proof-proof-cases proof test yes no))))

(defun h4-book-numeric-measures-fixed-value-type (p call)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
     ((parts (proof-list-of-length call 2))
      (opened (proof-proof-unfold proof call))
      (body (h4-book-numeric-measures-first-at opened 2))
      (test (proof-term-at body 1)))
     (if (equal (car parts) *h4-book-numeric-measures-natural-fix*)
         (h4-book-numeric-measures-fixed-natural-type p (cadr parts) opened test body)
       (proof-with-checked-results
        ((yes (proof-proof-assume proof test t))
         (yes (h4-book-numeric-measures-fixed-value-type-components yes p opened test))
         (no (proof-proof-assume proof test nil))
         (no (h4-book-numeric-measures-fixed-value-type-components no p opened test))
         (integral (proof-proof-cases proof test (car yes) (car no)))
         (positive (proof-proof-cases proof test (cadr yes) (cadr no))))
        (list integral positive))))))

(defun h4-book-numeric-measures-increasing-index-bounds (formals actuals index)
  (and (and (consp formals) (consp actuals))
    (let ((rest (h4-book-numeric-measures-increasing-index-bounds (cdr formals) (cdr actuals) (1+ index))))
      (if (equal (car actuals) (list *h4-book-numeric-measures-positive-fix* (car formals)))
          (cons (list index (car actuals)) rest)
        rest))))

(defun h4-book-numeric-measures-increasing-index-advances (formals actuals index)
  (and (and (consp formals) (consp actuals))
    (let ((old (list *h4-book-numeric-measures-natural-fix* (car formals)))
          (rest (h4-book-numeric-measures-increasing-index-advances (cdr formals) (cdr actuals) (1+ index))))
      (if (equal (car actuals) (library-plus old *proof-one*))
          (cons (list index old (car actuals)) rest)
        rest))))

(defun h4-book-numeric-measures-increasing-index-proof (p definitions calls function-name bound old new inside)
  (let ((proof (library-library-proof p))
        (measure (list *library-gap* bound old)))
    (proof-with-checked-results
     ((bound-types (h4-book-numeric-measures-fixed-value-type p bound))
      (bound-integer (car bound-types))
      (bound-positive (cadr bound-types))
      (old-natural (h4-book-numeric-measures-fixed-value-type p old))
      (old-integer (library-library-cite p "NATURAL-INTEGER" (list old) (list old-natural)))
      (one-natural (library-library-natural p *proof-one*))
      (new-natural (library-library-cite p "NATURAL-SUM" (list old *proof-one*)
                                         (list old-natural one-natural)))
      (new-integer (library-library-cite p "NATURAL-INTEGER" (list new) (list new-natural)))
      (growth (library-library-cite p "SUCCESSOR-LARGER" (list old) (list old-integer)))
      (commute (library-library-axiom p "COMMUTATIVITY-OF-+" (list *proof-one* old)))
      (growth (proof-proof-rewrite proof growth commute '(1 2)))
      (smaller (library-library-cite p "GAP-DECREASE" (list bound old new)
                                    (list bound-integer old-integer new-integer inside growth)))
      (bound-equation (proof-proof-unfold proof (list *h4-book-numeric-measures-positive-fix* bound)))
      (body (h4-book-numeric-measures-first-at bound-equation 2))
      (fixed-bound (h4-tactics-tactics-normalize p body (list bound-integer bound-positive) nil nil nil))
      (fixed-bound (proof-proof-chain proof bound-equation (list fixed-bound)))
      (new-nonnegative (library-library-cite p "NATURAL-NONNEGATIVE" (list new) (list new-natural)))
      (index-equation (proof-proof-unfold proof (list *h4-book-numeric-measures-natural-fix* new)))
      (body (h4-book-numeric-measures-first-at index-equation 2))
      (fixed-index (h4-tactics-tactics-normalize p body (list new-integer new-nonnegative)
                                              (list *proof-not*) nil nil))
      (fixed-index (proof-proof-chain proof index-equation (list fixed-index)))
      (reverse-bound (proof-proof-symmetric proof fixed-bound))
      (smaller (proof-proof-rewrite proof smaller reverse-bound '(1 1 1)))
      (reverse-index (proof-proof-symmetric proof fixed-index))
      (smaller (proof-proof-rewrite proof smaller reverse-index '(1 1 2)))
      (ordinal (library-library-cite p "GAP-ORDINAL" (list bound old) nil))
      (cases (termination-obligation-cases definitions (list (cons function-name measure)) calls))
      (step (proof-proof-subsume proof smaller (caadr cases))))
     (list (list measure) (list ordinal step)))))

(defun h4-book-numeric-measures-increasing-index-measure (p definitions calls)
  (and (and (equal (len definitions) 1) (equal (len calls) 1)
             (assoc-equal *h4-book-numeric-measures-positive-fix*
                          (proof-proof-definitions (library-library-proof p))))
    (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
      (let* ((formals (cadr definition))
             (actuals (termination-call-actuals (car calls)))
             (bounds (h4-book-numeric-measures-increasing-index-bounds formals actuals 0))
             (advances (h4-book-numeric-measures-increasing-index-advances formals actuals 0)))
        (and (and (equal (len bounds) 1) (equal (len advances) 1))
          (if (equal (caar bounds) (caar advances))
              '(:failure "failure" "")
            (let ((bound (cadar bounds))
                  (old (cadar advances))
                  (new (caddar advances)))
              (proof-with-checked-results
               ((evidence (h4-book-numeric-measures-signed-countdowns p (car calls))))
               (let ((inside (table-get evidence (library-lt old bound) nil)))
                 (and inside (h4-book-numeric-measures-increasing-index-proof
                              p definitions calls (car definition) bound old new inside)))))))))))

(defun h4-book-numeric-measures-numeric-termination (p definitions calls support)
  (let ((result (or (h4-book-numeric-measures-subtraction-measure p definitions calls)
                    (h4-book-numeric-measures-increasing-index-measure p definitions calls))))
    (if result
        (h4-book-numeric-measures-result-with-library result p t)
      (h4-book-numeric-measures-division-attempt p definitions calls support t))))
