(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-signed-bitwise-bitp* (proof-sym "BITP" "ACL2"))
(defconst *b2-signed-bitwise-logand* *b2-logand-logand*)

(defun b2-signed-bitwise-step-at (step index)
  (if (not step)
      '(:failure "failure" "")
    (proof-with-checked-results ((literal (proof-step-first step)))
      (proof-term-at literal index))))

(defun b2-signed-bitwise-known-step (known term)
  (let ((entry (assoc-equal term known)))
    (if entry
        (cdr entry)
      '(:failure "tactic-rejected" ""))))

(defun b2-signed-bitwise-assumptions (lib tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((test (proof-list-of-length (car tests) 2))
         (step (proof-proof-assume (library-library-proof lib)
                                   (car test) (cadr test)))
         (rest (b2-signed-bitwise-assumptions lib (cdr tests))))
      (cons step rest))))

; The two requests of a choice use the Library at their respective branches.
(defmacro b2-signed-bitwise-with-choice (library test formals body)
  (let ((branch `(let ((,(car formals) (caddr (car choice-request)))
                       (,(cadr formals) (cadddr (car choice-request)))
                       (,(caddr formals) (nth 4 (car choice-request))))
                   ,body)))
    `(let ((choice-lib ,library) (choice-test ,test))
       (proof-with-checked-results
           ((choice-request (b2-tactics-choose choice-lib choice-test nil nil))
            (first-answer ,branch)
            (choice-request (b2-tactics-choose choice-lib choice-test nil
                                               (list first-answer))))
         (if (eq (caar choice-request) :call)
             (proof-with-checked-results ((second-answer ,branch))
               (b2-tactics-choose choice-lib choice-test nil
                                  (list first-answer second-answer)))
           choice-request)))))

(defun b2-signed-bitwise-bit-from-bounds-case (is-zero facts lib value goal typed lower upper)
  (let* ((proof (library-library-proof lib))
         (test (car (last facts))))
    (if is-zero
        (b2-tactics-tactics-solve lib goal (list test) (list goal) nil 0 nil)
      (let ((sign (library-positive value)))
        (proof-with-checked-results
            ((nonpositive (proof-proof-assume proof sign nil))
             (zero (b2-powers-zero-from-signs lib value typed lower nonpositive))
             (nonzero-cut (proof-proof-cut proof zero test))
             (positive-bit (proof-proof-front proof nonzero-cut sign))
             (before-one (proof-proof-fact proof "integer-discrete"
                                           (list (list *library-x* value))))
             (one-condition (b2-signed-bitwise-step-at before-one 1))
             (one-evidence (b2-tactics-tactics-solve
                            lib one-condition (list typed positive-bit) nil nil 0 nil))
             (at-least-one (proof-proof-modus-ponens proof before-one one-evidence)))
          (let ((delta (library-diff value *proof-one*))
                (above-one (library-lt *proof-one* value)))
            (proof-with-checked-results
                ((above (proof-proof-assume proof above-one t))
                 (compare-one (library-library-comparison lib *proof-one* value (list typed)))
                 (pos-delta (proof-proof-rewrite proof above compare-one '(1)))
                 (pos-delta (proof-proof-tidy proof pos-delta))
                 (law (proof-proof-fact proof "integer-discrete" (list (list *library-x* delta))))
                 (law-condition (b2-signed-bitwise-step-at law 1))
                 (typed-delta (library-library-type-of lib delta (list typed)))
                 (law-evidence (b2-tactics-tactics-solve
                                lib law-condition (list typed-delta pos-delta) nil nil 0 nil))
                 (impossible (proof-proof-modus-ponens proof law law-evidence))
                 (compare-two (library-library-comparison lib value *b2-logand-two* (list typed)))
                 (difference (proof-proof-rewrite proof upper compare-two '(1)))
                 (difference (proof-proof-tidy proof difference))
                 (below-one (b2-tactics-tactics-less-from-difference
                             lib delta *proof-one* difference (list typed)))
                 (at-most-one (proof-proof-cut proof below-one impossible))
                 (at-most-one (proof-proof-front proof at-most-one (proof-neg above-one)))
                 (nonone (proof-proof-assume proof (proof-eq value *proof-one*) nil))
                 (rational-value (library-library-rational lib value (list typed)))
                 (rational-one (library-library-rational lib *proof-one* nil))
                 (less-one (b2-rational-order-strict-from-weak
                            lib at-most-one nonone rational-value rational-one))
                 (equal-cut (proof-proof-cut proof less-one at-least-one))
                 (exact (proof-proof-front proof equal-cut (proof-eq value *proof-one*))))
              (b2-tactics-tactics-solve lib goal (list exact) (list goal) nil 0 nil))))))))

(defun b2-signed-bitwise-bit-from-bounds (lib typed lower upper)
  (proof-with-checked-results ((value (b2-signed-bitwise-step-at typed 1)))
    (let ((goal (list *b2-signed-bitwise-bitp* value)))
      (proof-with-checked-results
          ((answer (b2-signed-bitwise-with-choice
                    lib (proof-eq value *proof-zero*) (branch-lib is-zero facts)
                    (proof-with-checked-results
                        ((step (b2-signed-bitwise-bit-from-bounds-case
                                is-zero facts branch-lib value goal typed lower upper)))
                      (cons step branch-lib)))))
        (car answer)))))

(defun b2-signed-bitwise-excluded-half (lib half value equation excluded)
  (let ((test (proof-eq half value))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left (b2-signed-bitwise-step-at equation 1))
         (equality (proof-proof-assume proof test t))
         (known (b2-tactics-tactics-normalize lib left (list equality) nil nil 1500 nil))
         (exact (proof-proof-rewrite proof equation known '(1 1)))
         (exact (proof-proof-tidy proof exact))
         (exact (proof-proof-symmetric proof exact))
         (excluded-test (proof-proof-cut proof exact excluded)))
      (proof-proof-front proof excluded-test (proof-neg test)))))

(defun b2-signed-bitwise-half-decrease-earlier
    (lib q sign negative is-zero types addition known neq0 neq1)
  (cond
   (negative
    (if is-zero
        sign
      (proof-with-checked-results
          ((weak (b2-butlast-integer-after-successor lib sign types))
           (bound (b2-bounds-prove-integer-bound
                   lib (library-le q *proof-neg-one*) (append types (list weak))))
           (excluded (b2-signed-bitwise-known-step known neq1))
           (unequal (b2-signed-bitwise-excluded-half lib q *proof-neg-one* addition excluded))
           (rational-q (library-library-rational lib q types))
           (rational-negative-one (library-library-rational lib *proof-neg-one* nil)))
        (b2-rational-order-strict-from-weak lib bound unequal rational-q rational-negative-one))))
   (is-zero
    (proof-with-checked-results
        ((excluded (b2-signed-bitwise-known-step known neq0))
         (unequal (b2-signed-bitwise-excluded-half lib q *proof-zero* addition excluded))
         (rational-zero (library-library-rational lib *proof-zero* nil))
         (rational-q (library-library-rational lib q types)))
      (b2-rational-order-strict-from-weak lib sign unequal rational-zero rational-q)))
   (t sign)))

(defun b2-signed-bitwise-half-decrease-order (lib q addition expanded types earlier sign negative)
  (let ((proof (library-library-proof lib)))
    (if negative
        (proof-with-checked-results
            ((below (b2-bounds-prove-integer-bound
                     lib (library-lt expanded q) (append types (list earlier))))
             (ordered (proof-proof-rewrite proof below addition '(1 1)))
             (ordered (proof-proof-tidy proof ordered))
             (x-sign (b2-bounds-prove-integer-bound
                      lib (library-lt *library-x* *proof-zero*) (append types (list ordered sign))))
             (reversed (b2-rational-order-reverse-negations lib q *library-x*))
             (order (proof-proof-transport proof ordered reversed)))
          (list order x-sign))
      (proof-with-checked-results
          ((above (b2-bounds-prove-integer-bound
                   lib (library-lt q expanded) (append types (list earlier))))
           (order (proof-proof-rewrite proof above addition '(1 2)))
           (order (proof-proof-tidy proof order))
           (x-sign (b2-bounds-prove-integer-bound
                    lib (library-le *proof-zero* *library-x*) (append types (list order sign)))))
        (list order x-sign)))))

(defun b2-signed-bitwise-half-decrease-establish-by-bit-compare
    (negative signs lib q addition expanded types is-zero known neq0 neq1 ordinal)
  (let* ((sign (car (last signs)))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((earlier (b2-signed-bitwise-half-decrease-earlier
                   lib q sign negative is-zero types addition known neq0 neq1))
         (ordered (b2-signed-bitwise-half-decrease-order
                   lib q addition expanded types earlier sign negative))
         (q-count (b2-powers-integer-count lib q (cadr types) sign))
         (x-count (b2-powers-integer-count lib *library-x* (car types) (cadr ordered)))
         (ordered-count (library-library-transport-argument lib (car ordered) q-count 1))
         (ordered-count (library-library-transport-argument lib ordered-count x-count 2)))
      (proof-proof-transport proof ordered-count ordinal))))

(defun b2-signed-bitwise-half-decrease-establish-by-bit
    (is-zero facts lib q r types known neq0 neq1 as-bit sum-equation ordinal)
  (let ((proof (library-library-proof lib))
        (bit (list *b2-signed-bitwise-bitp* r)))
    (proof-with-checked-results
        ((exact (if is-zero
                    (car (last facts))
                  (proof-with-checked-results
                      ((equation (b2-tactics-tactics-normalize lib bit facts (list bit) nil 1500 nil))
                       (exact (proof-proof-rewrite proof as-bit equation '(1))))
                    (proof-proof-tidy proof exact))))
         (addition (proof-proof-rewrite proof sum-equation exact '(1 1 1)))
         (addition (proof-proof-tidy proof addition))
         (expanded (b2-signed-bitwise-step-at addition 1)))
      (b2-signed-bitwise-with-choice
       lib (library-lt q *proof-zero*) (branch-lib negative signs)
       (proof-with-checked-results
           ((step (b2-signed-bitwise-half-decrease-establish-by-bit-compare
                   negative signs branch-lib q addition expanded types is-zero known neq0 neq1 ordinal)))
         (cons step branch-lib))))))

(defun b2-signed-bitwise-half-decrease-establish
    (premise lib q r x-kind neq0 neq1 q-type ordinal)
  (proof-with-checked-results
      ((known (b2-tactics-tactics-evidence lib (list premise)))
       (x-type (b2-signed-bitwise-known-step known x-kind))
       (two-type (library-library-type-of lib *b2-logand-two* nil))
       (two-positive (b2-tactics-tactics-solve
                      lib (library-positive *b2-logand-two*) nil nil nil 0 nil))
       (remainder (b2-floor-intervals-integer-remainder
                   lib *library-x* *b2-logand-two* x-type two-type two-positive q-type)))
    (let ((lib (cdr remainder))
          (types (list x-type q-type))
          (formula (list *library-implies* (list *library-numberp* *library-x*)
                         (proof-eq (library-plus r (b2-products-product *b2-logand-two* q))
                                   *library-x*))))
      (proof-with-checked-results
          ((as-bit (b2-signed-bitwise-bit-from-bounds
                    lib (caar remainder) (cadar remainder) (caddar remainder)))
           (elimination (b2-floor-intervals-floor-theorem lib *b2-floor-intervals-mod-elim* formula)))
        (let* ((lib (cdr elimination))
               (proof (library-library-proof lib)))
          (proof-with-checked-results
              ((number (library-library-number lib *library-x* types))
               (eliminated (proof-proof-modus-ponens proof (car elimination) number))
               (doubled (b2-scaling-doubled lib q q-type))
               (sum-equation (proof-proof-rewrite proof eliminated doubled '(1 1 2)))
               (sum-equation (proof-proof-tidy proof sum-equation)))
            (b2-signed-bitwise-with-choice
             lib (proof-eq r *proof-zero*) (branch-lib is-zero facts)
             (b2-signed-bitwise-half-decrease-establish-by-bit
              is-zero facts branch-lib q r types known neq0 neq1 as-bit sum-equation ordinal))))))))

(defun b2-signed-bitwise-floor-request-p (result)
  (and (consp result)
       (consp (car result))
       (eq (caar result) :call)
       (eq (cadar result) :b2-signed-bitwise-floor-type)))

(defun b2-signed-bitwise-half-decrease-fact (lib name term typed nonzero nonminusone)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step (proof-proof-fact proof name (list (list *library-x* term))))
         (condition (b2-signed-bitwise-step-at step 1))
         (premise (b2-tactics-tactics-solve
                   lib condition (list typed nonzero nonminusone) nil nil 0 nil))
         (result (proof-proof-modus-ponens proof step premise)))
      (cons result lib))))

(defun b2-signed-bitwise-half-decrease (lib term typed nonzero nonminusone floor-type)
  (let ((name (proof-sym "B2-SIGNED-HALF-COUNT" "ACL2")))
    (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
        (b2-signed-bitwise-half-decrease-fact lib name term typed nonzero nonminusone)
      (let* ((q (list *b2-floor-intervals-floor* *library-x* *b2-logand-two*))
             (r (list *b2-floor-intervals-mod* *library-x* *b2-logand-two*))
             (smaller (list *library-count* q))
             (larger (list *library-count* *library-x*))
             (target (list *proof-ordinal-less* smaller larger))
             (x-kind (library-integer *library-x*))
             (neq0 (proof-neg (proof-eq *library-x* *proof-zero*)))
             (neq1 (proof-neg (proof-eq *library-x* *proof-neg-one*))))
        (proof-with-checked-results ((condition (b2-powers-and-terms (list x-kind neq0 neq1))))
          (if (not floor-type)
              (cons (list :call :b2-signed-bitwise-floor-type lib *library-x* *b2-logand-two*) lib)
            (proof-with-checked-results ((floor-answer floor-type))
              (let ((lib (cdr floor-answer))
                    (q-type (car floor-answer)))
                (proof-with-checked-results
                    ((ordinal (library-library-ordinal-comparison lib smaller larger))
                     (request (b2-tactics-tactics-implication lib condition target nil))
                     (body (b2-signed-bitwise-half-decrease-establish
                            (nth 3 (car request)) (cdr request) q r x-kind neq0 neq1 q-type ordinal))
                     (lemma (b2-tactics-tactics-implication lib condition target body))
                     (added (b2-tactics-tactics-add-lemma (cdr lemma) "SIGNED-HALF-COUNT" (car lemma) :none)))
                  (b2-signed-bitwise-half-decrease-fact
                   (cdr added) name term typed nonzero nonminusone))))))))))

(defun b2-signed-bitwise-by-value-join (lib value template yes no)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((true-equality (proof-proof-if-true proof value))
         (true-equality (proof-proof-symmetric proof true-equality))
         (yes (proof-proof-rewrite-result proof yes true-equality template *proof-result*))
         (false-equality (proof-proof-if-false proof value))
         (false-equality (proof-proof-symmetric proof false-equality))
         (no (proof-proof-rewrite-result proof no false-equality template *proof-result*)))
      (proof-proof-cases proof (cadr value) yes no))))

(defun b2-signed-bitwise-by-value-check (value template step)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (target (proof-subst template (list (cons *proof-result* value)))))
    (if (equal literal target)
        step
      '(:failure "tactic-rejected" ""))))

(defun b2-signed-bitwise-integer-logand-leaf-decrease (lib known floor-type)
  (let ((nonzip-term (proof-neg (list *b2-powers-zip* *library-x*))))
    (proof-with-checked-results
        ((nonzip (b2-signed-bitwise-known-step known nonzip-term))
         (typed (b2-tactics-tactics-from-impossible
                 lib (library-integer *library-x*) nonzip nil (list *b2-powers-zip*) nil 1500 nil))
         (nonzero (b2-tactics-tactics-from-impossible
                   lib (proof-neg (proof-eq *library-x* *proof-zero*))
                   nonzip nil (list *b2-powers-zip*) nil 1500 nil))
         (nonminusone (b2-signed-bitwise-known-step
                       known (proof-neg (proof-eq *library-x* *proof-neg-one*)))))
      (b2-signed-bitwise-half-decrease lib *library-x* typed nonzero nonminusone floor-type))))

; A leaf can add lemmas. Visit its branches in order and carry the Library forward.
(mutual-recursion
 (defun b2-signed-bitwise-by-value (n lib value template tests goal measure binding floor-type digit)
   (declare (xargs :measure (nfix n)))
   (cond
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "Fuel" "b2-signed-bitwise-by-value"))
    ((proof-is-call value *proof-if*)
     (proof-with-checked-results
         ((branches (proof-list-of-length (cdr value) 3))
          (yes (b2-signed-bitwise-by-value
                (1- n) lib (cadr branches) template (append tests (list (list (car branches) t)))
                goal measure binding floor-type digit)))
       (if (b2-signed-bitwise-floor-request-p yes)
           yes
         (proof-with-checked-results
             ((no (b2-signed-bitwise-by-value
                   (1- n) (cdr yes) (caddr branches) template
                   (append tests (list (list (car branches) nil))) goal measure binding floor-type digit)))
           (if (b2-signed-bitwise-floor-request-p no)
               no
             (proof-with-checked-results
                 ((step (b2-signed-bitwise-by-value-join (cdr no) value template (car yes) (car no))))
               (cons step (cdr no))))))))
    ((and (proof-compound value) (endp value)) '(:failure "tactic-rejected" ""))
    ((and (proof-compound value) (proof-compound (car value)))
     (proof-with-checked-results
         ((equality (proof-proof-beta (library-library-proof lib) value))
          (opened (b2-signed-bitwise-step-at equality 2))
          (result (b2-signed-bitwise-by-value
                   (1- n) lib opened template tests goal measure binding floor-type digit)))
       (if (b2-signed-bitwise-floor-request-p result)
           result
         (let ((proof (library-library-proof (cdr result))))
           (proof-with-checked-results
               ((reverse (proof-proof-symmetric proof equality))
                (step (proof-proof-rewrite-result proof (car result) reverse template *proof-result*)))
             (cons step (cdr result)))))))
    (t
     (proof-with-checked-results
         ((result (if digit
                      (proof-with-checked-results ((step (library-library-type-of lib value nil)))
                        (cons step lib))
                    (b2-signed-bitwise-integer-logand-leaf
                     (1- n) value tests lib template goal measure binding floor-type))))
       (if (b2-signed-bitwise-floor-request-p result)
           result
         (proof-with-checked-results
             ((step (b2-signed-bitwise-by-value-check value template (car result))))
           (cons step (cdr result))))))))

 (defun b2-signed-bitwise-integer-logand-leaf
     (n value signed lib template goal measure binding floor-type)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "Fuel" "b2-signed-bitwise-integer-logand-leaf")
     (proof-with-checked-results
         ((facts (b2-signed-bitwise-assumptions lib signed))
          (known (b2-tactics-tactics-evidence lib facts)))
       (cond
        ((equal value *proof-zero*)
         (proof-with-checked-results ((step (library-library-type-of lib *proof-zero* nil)))
           (cons step lib)))
        ((member-equal value (list *library-x* *library-y*))
         (proof-with-checked-results
             ((nonzip (b2-signed-bitwise-known-step known (proof-neg (list *b2-powers-zip* value))))
              (step (b2-tactics-tactics-from-impossible
                     lib (library-integer value) nonzip nil (list *b2-powers-zip*) nil 1500 nil)))
           (cons step lib)))
        (t
         (proof-with-checked-results
             ((decrease (b2-signed-bitwise-integer-logand-leaf-decrease lib known floor-type)))
           (if (b2-signed-bitwise-floor-request-p decrease)
               decrease
             (let ((lib (cdr decrease)))
               (proof-with-checked-results
                   ((induction (b2-tactics-tactics-induction-hypothesis
                                lib goal measure binding (car decrease)))
                    (bit (proof-term-at value 2))
                    (digit (b2-signed-bitwise-by-value
                            (1- n) lib bit template nil goal measure binding floor-type t))
                    (step (library-library-type-of (cdr digit) value (list induction (car digit)))))
                 (cons step (cdr digit))))))))))))

(defun b2-signed-bitwise-integer-logand-build (lib floor-type)
  (let* ((call (list *b2-signed-bitwise-logand* *library-x* *library-y*))
         (goal (library-integer call))
         (measure (list *library-count* *library-x*))
         (binding (list (list *library-x* (list *b2-floor-intervals-floor* *library-x* *b2-logand-two*))
                        (list *library-y* (list *b2-floor-intervals-floor* *library-y* *b2-logand-two*))))
         (template (library-integer *proof-result*)))
    (proof-with-checked-results
        ((opened (b2-tactics-tactics-normalize lib call nil (list call) nil 1500 t))
         (value (b2-signed-bitwise-step-at opened 2))
         (body (b2-signed-bitwise-by-value
                1000000 lib value template nil goal measure binding floor-type nil)))
      (if (b2-signed-bitwise-floor-request-p body)
          body
        (let* ((lib (cdr body))
               (proof (library-library-proof lib)))
          (proof-with-checked-results
              ((reverse (proof-proof-symmetric proof opened))
               (step (proof-proof-rewrite-result proof (car body) reverse template *proof-result*))
               (ordinal (library-library-builtin lib 1 *library-x*))
               (induction (proof-proof-induct proof ordinal step goal measure (list binding))))
            (b2-tactics-tactics-add-lemma lib "SIGNED-LOGAND-INTEGER" induction :none)))))))

(defun b2-signed-bitwise-integer-logand (lib a b floor-type)
  (let ((name (proof-sym "B2-SIGNED-LOGAND-INTEGER" "ACL2")))
    (proof-with-checked-results
        ((built (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                    (cons name lib)
                  (b2-signed-bitwise-integer-logand-build lib floor-type))))
      (if (b2-signed-bitwise-floor-request-p built)
          built
        (let ((lib (cdr built)))
          (proof-with-checked-results
              ((step (proof-proof-fact (library-library-proof lib) name
                                       (list (list *library-x* a) (list *library-y* b)))))
            (cons step lib)))))))
