(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-lexical-fast* (proof-sym "FAST-LEXORDER" "ACL2"))
(defconst *b1-lexical-alphorder* (proof-sym "ALPHORDER" "ACL2"))
(defconst *b1-lexical-fast-strict* (proof-sym "FAST-<<" "ACL2"))
(defconst *b1-lexical-complex* (proof-sym "COMPLEX-RATIONALP" "ACL2"))
(defconst *b1-lexical-characterp* (proof-cl "CHARACTERP"))
(defconst *b1-lexical-types*
  (list *proof-integerp* *library-rationalp* *b1-lexical-complex*
        *b1-lexical-characterp* *b1-logic-stringp* *b1-logic-symbolp*))

(defun b1-lexical-first-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b1-lexical-comparison-arguments (formula)
  (proof-with-checked-results ((comparison (proof-term-at formula 1)))
    (if (integerp comparison)
        '(:failure "failure" "")
      (proof-list-of-length (cdr comparison) 2))))

(defun b1-lexical-type-fact (lib name term premise)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof name (list (list *library-x* term)))))
      (proof-proof-modus-ponens proof fact premise))))

(defun b1-lexical-type-consequences-facts (names prefix lib term premise)
  (if (endp names)
      nil
    (proof-with-checked-results
        ((step (b1-lexical-type-fact lib (concatenate 'string prefix (car names)) term premise))
         (rest (b1-lexical-type-consequences-facts (cdr names) prefix lib term premise)))
      (cons step rest))))

(defun b1-lexical-type-consequences (lib term head positive)
  (let ((proof (library-library-proof lib)))
    (cond
     ((member-equal head (list *proof-integerp* *library-rationalp* *b1-lexical-complex*))
      (proof-with-checked-results
          ((first (if (equal head *proof-integerp*)
                      (b1-arithmetic-known-type lib *library-rationalp* term (list positive))
                    nil)))
        (if (equal head *b1-lexical-complex*)
            (proof-with-checked-results
                ((numeric (b1-lexical-type-fact lib "complex-rationalp-acl2-numberp" term positive)))
              (b1-lexical-type-consequences-facts
               '("characterp" "stringp" "symbolp") "acl2-numberp-not-" lib term numeric))
          (let ((complex-test (list *b1-lexical-complex* term)))
            (proof-with-checked-results
                ((rational (b1-arithmetic-known-type lib *library-rationalp* term (list positive)))
                 (assumed (proof-proof-assume proof complex-test t))
                 (excluded (b1-lexical-type-fact lib "complex-rationalp-not-rationalp" term assumed))
                 (cut (proof-proof-cut proof rational excluded))
                 (noncomplex (proof-proof-front proof cut (proof-neg complex-test)))
                 (numeric (b1-arithmetic-known-type lib *library-numberp* term (list rational)))
                 (rest (b1-lexical-type-consequences-facts
                        '("characterp" "stringp" "symbolp") "acl2-numberp-not-" lib term numeric)))
              (if first (cons first (cons noncomplex rest)) (cons noncomplex rest)))))))
     ((equal head *b1-lexical-characterp*)
      (b1-lexical-type-consequences-facts '("stringp" "symbolp") "characterp-not-" lib term positive))
     ((equal head *b1-logic-stringp*)
      (proof-with-checked-results
          ((step (b1-lexical-type-fact lib "stringp-not-symbolp" term positive)))
        (list step)))
     (t nil))))

(defun b1-lexical-strict-dual-lemma (lib)
  (let* ((proof (library-library-proof lib))
         (forward (list *b1-total-order-strict* *library-x* *library-y*))
         (backward (list *b1-total-order-order* *library-y* *library-x*)))
    (proof-with-checked-results
        ((have-backward (proof-proof-assume proof backward t))
         (have-forward (proof-proof-assume proof forward t))
         (components (b1-total-order-strict-components lib have-forward))
         (parts (proof-list-of-length components 2))
         (same (b1-total-order-antisymmetric lib (car parts) have-backward))
         (impossible (proof-proof-cut proof same (cadr parts)))
         (front (proof-proof-front proof impossible (proof-neg forward)))
         (no-strict (b1-logic-bookproof-false-value lib front))
         (no-dual (b1-logic-bookproof-normalize lib (proof-neg backward) (list have-backward)
                                               (list *proof-not*) nil nil nil nil))
         (reversed (proof-proof-symmetric proof no-dual))
         (yes (proof-proof-chain proof no-strict (list reversed)))
         (no-backward (proof-proof-assume proof backward nil))
         (total (b1-total-order-order-fact lib "TOTAL" (list *library-y* *library-x*)))
         (ordered (proof-proof-prove-if proof total no-backward)))
      (let ((same (proof-eq *library-x* *library-y*)))
        (proof-with-checked-results
            ((reflexive (b1-total-order-order-fact lib "REFLEXIVE" (list *library-x*)))
             (assumed (proof-proof-assume proof same t))
             (contrary (proof-proof-rewrite proof reflexive assumed '(1 1)))
             (cut (proof-proof-cut proof contrary no-backward))
             (unequal (proof-proof-front proof cut (proof-neg same)))
             (opened (b1-total-order-strict-definition lib forward))
             (opened-term (b1-lexical-first-at opened 2))
             (normalized (b1-logic-bookproof-normalize lib opened-term (list ordered unequal)
                                                       (list *proof-not*) nil nil nil nil))
             (strict-value (proof-proof-chain proof opened (list normalized)))
             (dual-value (b1-logic-bookproof-normalize lib (proof-neg backward) (list no-backward)
                                                      (list *proof-not*) nil nil nil nil))
             (reversed (proof-proof-symmetric proof dual-value))
             (no (proof-proof-chain proof strict-value (list reversed)))
             (step (proof-proof-cases proof backward yes no))
             (claim (proof-step-first step)))
          (library-library-lemma lib "STRICT-LEXORDER-DUAL" claim step nil))))))

(defun b1-lexical-strict-dual (lib x y)
  (let ((name (proof-sym "SELF-STRICT-LEXORDER-DUAL" "ACL2")))
    (proof-with-checked-results
        ((lib (if (assoc-equal name (proof-proof-facts (library-library-proof lib)))
                  lib
                (b1-lexical-strict-dual-lemma lib)))
         (step (proof-proof-fact (library-library-proof lib) name
                                 (list (list *library-x* x) (list *library-y* y)))))
      (cons step lib))))

(defun b1-lexical-comparison-value (lib step)
  (proof-with-checked-results
      ((literal (proof-step-first step))
       (parts (proof-list-of-length literal 3))
       (boolean (proof-proof-fact (library-library-proof lib) "booleanp-<"
                                   (list (list *library-x* (cadr parts))
                                         (list *library-y* (caddr parts))))))
    (b1-logic-bookproof-boolean-value lib step boolean)))

(defun b1-lexical-strict-atoms-not-constant (term lib)
  (if (proof-is-call term *proof-not*)
      (proof-with-checked-results ((argument (proof-term-at term 1)))
        (if (proof-is-call argument *proof-quote*)
            (b1-logic-bookproof-normalize lib term nil (list *proof-not*) nil nil nil nil)
          nil))
    nil))

(defun b1-lexical-strict-atoms-simplify-known-negation (term lib facts)
  (if (proof-is-call term *proof-not*)
      (proof-with-checked-results ((argument (proof-term-at term 1)))
        (let ((support (or (cdr (assoc-equal argument facts))
                           (cdr (assoc-equal (proof-neg argument) facts)))))
          (if support
              (b1-logic-bookproof-normalize lib term (list support) (list *proof-not*) nil nil nil nil)
            nil)))
    nil))

(defun b1-lexical-case-proof-visit (n result lib goal evidence unfold rules replies)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "b1-lexical-case-proof-visit"))
   ((failure-p result) result)
   ((b1-logic-call-p result)
    (let* ((current (b1-logic-call-library result))
           (term (b1-logic-call-term result))
           (id (b1-logic-call-id result))
           (step (if (eq id :not-constant)
                     (b1-lexical-strict-atoms-not-constant term current)
                   (b1-lexical-strict-atoms-simplify-known-negation term current (cadr id))))
           (reply (if (failure-p step) step (cons step current)))
           (replies (append replies (list reply))))
      (b1-lexical-case-proof-visit
       (1- n) (b1-logic-bookproof-case-proof-with-library lib goal evidence unfold rules 16 replies)
       lib goal evidence unfold rules replies)))
   ((b1-logic-branch-p result)
    '(:failure "failure" ""))
   (t (car result))))

(defun b1-lexical-case-proof (lib goal evidence unfold rules)
  (b1-lexical-case-proof-visit
   1000000 (b1-logic-bookproof-case-proof-with-library lib goal evidence unfold rules 16 nil)
   lib goal evidence unfold rules nil))

(defun b1-lexical-step-map (known facts)
  (if (endp known)
      facts
    (proof-with-checked-results ((literal (proof-step-first (car known))))
      (b1-lexical-step-map (cdr known) (table-put facts literal (car known))))))

(defun b1-lexical-strict-atoms-simplify (known rules lib formula unfold)
  (proof-with-checked-results ((facts (b1-lexical-step-map known nil)))
    (b1-lexical-case-proof lib formula known unfold
                           (list* '(:callback :not-constant)
                                  (list :callback (list :known-negation facts)) rules))))

(defun b1-lexical-strict-atoms-split-test (test known rules lib formula unfold)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((affirmed (proof-proof-assume proof test t))
         (yes (b1-lexical-comparison-value lib affirmed))
         (denied (proof-proof-assume proof test nil))
         (no (b1-logic-bookproof-false-value lib denied))
         (yes (b1-lexical-strict-atoms-simplify
               known (append rules (list (b1-logic-equal-to yes))) lib formula unfold))
         (no (b1-lexical-strict-atoms-simplify
              known (append rules (list (b1-logic-equal-to no))) lib formula unfold)))
      (proof-proof-cases proof test yes no))))

(defun b1-lexical-strict-atoms-compare-symbol-order (step lib before distinct formula unfold)
  (proof-with-checked-results
      ((value (b1-logic-bookproof-normalize lib (proof-neg before) (list step)
                                            (list *proof-not*) nil nil nil nil)))
    (b1-lexical-strict-atoms-simplify (append distinct (list step))
                                      (list (b1-logic-equal-to value)) lib formula unfold)))

(defun b1-lexical-value-rules (values)
  (if (endp values)
      nil
    (cons (b1-logic-equal-to (car values))
          (b1-lexical-value-rules (cdr values)))))

(defun b1-lexical-strict-atoms-compare-compare-real
    (tie real-props values known lib formula unfold x y im)
  (let ((premises (append known real-props))
        (rules (b1-lexical-value-rules values)))
    (if tie
        (b1-lexical-strict-atoms-split-test
         (library-lt (list im x) (list im y)) premises rules lib formula unfold)
      (b1-lexical-strict-atoms-simplify premises rules lib formula unfold))))

(defun b1-lexical-compare-cases-strict-branch
    (strict reverse lib sums same no-reflexive types known formula unfold x y im)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof same t))
         (reversed (proof-proof-symmetric proof assumed))
         (collapsed (proof-proof-rewrite proof strict reversed (list 1 (if reverse 1 2))))
         (cut (proof-proof-cut proof collapsed no-reflexive))
         (neq (proof-proof-front proof cut (proof-neg same)))
         (opposite (b1-arithmetic-number-sums-weaken sums strict types))
         (reversed (b1-reciprocal-reverse-inequality lib neq))
         (value (b1-lexical-comparison-value lib strict)))
      (b1-lexical-strict-atoms-compare-compare-real
       nil (list strict opposite neq reversed) (list value) known lib formula unfold x y im))))

(defun b1-lexical-compare-cases (lib a b types known formula unfold x y im)
  (proof-with-checked-results ((sums (b1-arithmetic-number-sums-init lib)))
    (let* ((lib (b1-arithmetic-number-sums-library sums))
           (proof (library-library-proof lib))
           (before (library-lt a b))
           (after (library-lt b a))
           (same (proof-eq a b)))
      (proof-with-checked-results
          ((earlier (proof-proof-assume proof before t))
           (following (proof-proof-assume proof before nil))
           (order (b1-arithmetic-comparison-cases lib a b types sums))
           (ordered (proof-proof-front proof order before))
           (cut (proof-proof-cut proof ordered following))
           (last (proof-proof-front proof cut same))
           (different (proof-proof-assume proof same nil))
           (cut (proof-proof-cut proof last different))
           (later (proof-proof-front proof cut after))
           (reflexive (b1-arithmetic-number-sums-comparison-equation
                       sums (library-lt a a) (library-lt *proof-zero* *proof-zero*) types))
           (zero (library-library-axiom lib "ZERO" nil))
           (reversed (proof-proof-symmetric proof reflexive))
           (no-reflexive (proof-proof-rewrite proof zero reversed '(1 1)))
           (equal (proof-proof-assume proof same t))
           (no-after (proof-proof-rewrite proof no-reflexive equal '(1 1 1)))
           (reversed (proof-proof-symmetric proof equal))
           (middle (b1-lexical-strict-atoms-compare-compare-real
                    t (list following no-after equal reversed) nil known lib formula unfold x y im))
           (yes (b1-lexical-compare-cases-strict-branch
                 earlier nil lib sums same no-reflexive types known formula unfold x y im))
           (no (b1-lexical-compare-cases-strict-branch
                later t lib sums same no-reflexive types known formula unfold x y im))
           (tie (proof-proof-cases proof same middle no))
           (step (proof-proof-cases proof before yes tie)))
        (cons step lib)))))

(defun b1-lexical-strict-atoms-compare-ordinary (lib x y known x-type equal-test)
  (let* ((direct (proof-eq (list *b1-lexical-fast-strict* x y) (list *b1-total-order-strict* x y)))
         (ordinary (list *b1-lexical-fast-strict* *b1-total-order-strict* *b1-total-order-order*
                         *b1-lexical-alphorder* *proof-not* *b1-logic-eq* (proof-cl "STRING<=")))
         (rules '((:callback :not-constant)))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((strict (if (equal x-type *b1-logic-stringp*)
                     (proof-with-checked-results
                         ((same (proof-proof-assume proof equal-test t))
                          (law (b1-logic-bookproof-from-fact
                                lib (proof-sym "STRING<-IRREFLEXIVE" "ACL2")
                                (proof-neg (list (proof-cl "STRING<") x x))))
                          (law (proof-proof-rewrite proof law same '(1 1 2)))
                          (yes (b1-lexical-case-proof lib direct
                                                     (append known (list same law)) ordinary rules))
                          (unequal (proof-proof-assume proof equal-test nil))
                          (no (b1-lexical-case-proof lib direct
                                                    (append known (list unequal)) ordinary rules)))
                       (proof-proof-cases proof equal-test yes no))
                   (b1-lexical-case-proof lib direct known ordinary rules)))
         (dual (b1-lexical-strict-dual lib x y)))
      (let* ((lib (cdr dual))
             (proof (library-library-proof lib)))
        (proof-with-checked-results
            ((result (proof-proof-chain proof strict (list (car dual))))
             (weak (proof-proof-fact proof (proof-sym "FAST-LEXORDER-IS-LEXORDER" "ACL2")
                                     (list (list *library-x* y) (list *library-y* x))))
             (reversed (proof-proof-symmetric proof weak))
             (step (proof-proof-rewrite proof result reversed '(1 2 1))))
          (cons step lib))))))

(defun b1-lexical-strict-atoms-compare (x-type y-type known lib formula x y unfold equal-test)
  (let ((rational (list *proof-integerp* *library-rationalp*))
        (proof (library-library-proof lib)))
    (cond
     ((and (member-equal x-type rational) (member-equal y-type rational))
      (proof-with-checked-results
          ((step (b1-lexical-strict-atoms-split-test (library-lt x y) known nil lib formula unfold)))
        (cons step lib)))
     ((and (equal x-type *b1-lexical-characterp*) (equal y-type *b1-lexical-characterp*))
      (let ((code (proof-cl "CHAR-CODE")))
        (proof-with-checked-results
            ((step (b1-lexical-strict-atoms-split-test
                    (library-lt (list code x) (list code y)) known nil lib formula unfold)))
          (cons step lib))))
     ((and (equal x-type *b1-logic-symbolp*) (equal y-type *b1-logic-symbolp*))
      (proof-with-checked-results
          ((same (proof-proof-assume proof equal-test t))
           (unequal (proof-proof-assume proof equal-test nil))
           (reversed (proof-proof-symmetric proof same))
           (yes (b1-lexical-strict-atoms-simplify (append known (list same reversed)) nil lib formula unfold)))
        (let ((before (list (proof-sym "SYMBOL<" "ACL2") x y)))
          (proof-with-checked-results
              ((reversed (b1-reciprocal-reverse-inequality lib unequal)))
            (let ((distinct (append known (list unequal reversed))))
              (proof-with-checked-results
                  ((before-yes (proof-proof-assume proof before t))
                   (before-yes (b1-lexical-strict-atoms-compare-symbol-order
                                before-yes lib before distinct formula unfold))
                   (before-no (proof-proof-assume proof before nil))
                   (before-no (b1-lexical-strict-atoms-compare-symbol-order
                               before-no lib before distinct formula unfold))
                   (no (proof-proof-cases proof before before-yes before-no))
                   (step (proof-proof-cases proof equal-test yes no)))
                (cons step lib)))))))
     ((and (equal x-type *b1-lexical-complex*) (equal y-type *b1-lexical-complex*))
      (let ((re (proof-cl "REALPART"))
            (im (proof-cl "IMAGPART")))
        (proof-with-checked-results
            ((numeric-x (library-library-axiom lib "COMPLEX-IMPLIES1" (list x)))
             (real-x (b1-logic-bookproof-split-conjuncts-first lib numeric-x))
             (numeric-y (library-library-axiom lib "COMPLEX-IMPLIES1" (list y)))
             (real-y (b1-logic-bookproof-split-conjuncts-first lib numeric-y)))
          (b1-lexical-compare-cases lib (list re x) (list re y) (list real-x real-y)
                                     known formula unfold x y im))))
     ((and (equal x-type y-type) (or (equal x-type *b1-logic-stringp*) (null x-type)))
      (b1-lexical-strict-atoms-compare-ordinary lib x y known x-type equal-test))
     (t (proof-with-checked-results
            ((step (b1-lexical-strict-atoms-simplify known nil lib formula unfold)))
          (cons step lib))))))

(defun b1-lexical-find-proof (known literal)
  (if (endp known)
      '(:failure "failure" "")
    (proof-with-checked-results ((first (proof-step-first (car known))))
      (if (equal first literal)
          (car known)
        (b1-lexical-find-proof (cdr known) literal)))))

(defun b1-lexical-fast-lexorder-both-atoms-comparison (x-type y-type known lib x y formula unfold)
  (if (or (not (equal x-type *b1-logic-symbolp*)) (not (equal y-type *b1-logic-symbolp*)))
      (b1-logic-bookproof-case-proof lib formula known unfold nil 16)
    (let* ((proof (library-library-proof lib))
           (test (proof-eq x y))
           (symbol-test (list *b1-logic-symbolp* y))
           (sym-less (proof-sym "SYMBOL<" "ACL2")))
      (proof-with-checked-results
          ((same (proof-proof-assume proof test t))
           (symbol (b1-lexical-find-proof known symbol-test))
           (irreflexive (b1-logic-bookproof-from-fact
                         lib (proof-sym "SYMBOL<-IRREFLEXIVE" "ACL2")
                         (list *library-implies* symbol-test (proof-neg (list sym-less y y)))))
           (not-less (proof-proof-modus-ponens proof irreflexive symbol))
           (reversed (proof-proof-symmetric proof same))
           (not-less (proof-proof-rewrite proof not-less reversed '(1 1 2)))
           (yes (b1-logic-bookproof-case-proof lib formula (append known (list same not-less)) unfold nil 16))
           (different (proof-proof-assume proof test nil))
           (no (b1-logic-bookproof-case-proof lib formula (append known (list different)) unfold nil 16)))
        (proof-proof-cases proof test yes no)))))

(defun b1-lexical-atom-cases-evidence (lib term index failures)
  (proof-with-checked-results ((head (proof-term-at *b1-lexical-types* index)))
    (let ((test (list head term)))
      (proof-with-checked-results
          ((yes (proof-proof-assume (library-library-proof lib) test t))
           (types (b1-lexical-type-consequences lib term head yes)))
        (list test head (append failures (cons yes types)))))))

(defun b1-lexical-atom-cases-add-failure (lib test failures)
  (proof-with-checked-results ((assumed (proof-proof-assume (library-library-proof lib) test nil)))
    (append failures (list assumed))))

; A consequence specifies the comparison and the evidence from the enclosing atom case.
(mutual-recursion
 (defun b1-lexical-atom-cases-choose (n index failures lib term consequence)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "b1-lexical-atom-cases-choose"))
         ((failure-p failures) failures)
         ((equal index (len *b1-lexical-types*))
          (b1-lexical-atom-case-consequence (1- n) consequence lib nil failures))
         (t (b1-lexical-atom-cases-accept
             (1- n) index failures lib term consequence
             (b1-lexical-atom-cases-evidence lib term index failures)))))
 (defun b1-lexical-atom-cases-accept (n index failures lib term consequence evidence)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "b1-lexical-atom-cases-accept"))
         ((failure-p evidence) evidence)
         (t (b1-lexical-atom-cases-reject
             (1- n) index failures term consequence (car evidence)
             (b1-lexical-atom-case-consequence (1- n) consequence lib
                                               (cadr evidence) (caddr evidence))))))
 (defun b1-lexical-atom-cases-reject (n index failures term consequence test accepted)
   (declare (xargs :measure (nfix n)))
   (cond ((zp n) '(:failure "fuel" "b1-lexical-atom-cases-reject"))
         ((failure-p accepted) accepted)
         (t (proof-with-checked-results
                ((rejected (b1-lexical-atom-cases-choose
                            (1- n) (+ index 1)
                            (b1-lexical-atom-cases-add-failure (cdr accepted) test failures)
                            (cdr accepted) term consequence))
                 (step (proof-proof-cases (library-library-proof (cdr rejected)) test
                                          (car accepted) (car rejected))))
              (cons step (cdr rejected))))))
 (defun b1-lexical-atom-case-consequence (n consequence lib type evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-lexical-atom-case-consequence")
     (let ((mode (cadr consequence))
           (formula (caddr consequence))
           (x (cadddr consequence))
           (y (nth 4 consequence))
           (atoms (nth 5 consequence))
           (unfold (nth 6 consequence)))
       (if (eq (car consequence) :first)
           (b1-lexical-atom-pair-cases-first (1- n) type evidence lib y atoms mode formula x unfold)
         (let ((x-type (nth 7 consequence))
               (known (append atoms (nth 8 consequence) evidence)))
           (if (eq mode :strict)
               (b1-lexical-strict-atoms-compare x-type type known lib formula x y unfold (proof-eq x y))
             (proof-with-checked-results
                 ((step (b1-lexical-fast-lexorder-both-atoms-comparison
                         x-type type known lib x y formula unfold)))
               (cons step lib))))))))
 (defun b1-lexical-atom-pair-cases-first (n x-type x-types lib y atoms mode formula x unfold)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "b1-lexical-atom-pair-cases-first")
     (b1-lexical-atom-cases-choose (1- n) 0 nil lib y
                                  (list :second mode formula x y atoms unfold x-type x-types)))))

(defun b1-lexical-atom-cases (lib term consequence)
  (b1-lexical-atom-cases-choose 1000000 0 nil lib term consequence))

(defun b1-lexical-atom-pair-cases (lib x y atoms mode formula unfold)
  (b1-lexical-atom-cases lib x (list :first mode formula x y atoms unfold)))

(defun b1-lexical-fast-lexorder-both-atoms (atoms lib x y formula unfold)
  (b1-lexical-atom-pair-cases lib x y atoms :weak formula unfold))

(defun b1-lexical-strict-atoms (lib formula x y atoms)
  (b1-lexical-atom-pair-cases
   lib x y atoms :strict formula
   (list *b1-lexical-fast-strict* *b1-lexical-fast* *proof-not* *b1-logic-eq* (proof-cl "="))))

(defun b1-lexical-lexicographic-induction-recur
    (selector same lib x-cons y-cons x y x-atom induction claim definitions)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((other (if (equal selector *library-cdr*)
                    (proof-proof-symmetric proof same)
                  (b1-reciprocal-reverse-inequality lib same))))
      (let ((bindings (table-put (list (cons x (list selector x))) y (list selector y))))
        (proof-with-checked-results
            ((smaller (b1-induction-tree-induction-hypothesis induction bindings (list (list x-atom nil))))
             (equation (b1-logic-bookproof-normalize lib claim (list x-cons y-cons same other)
                                                    definitions nil nil nil nil))
             (step (proof-proof-transport proof (car smaller) equation)))
          (cons step (cdr smaller)))))))

(defun b1-lexical-lexicographic-induction (lib claim definitions atoms)
  (proof-with-checked-results ((arguments (b1-lexical-comparison-arguments claim)))
    (let* ((proof (library-library-proof lib))
           (x (car arguments))
           (y (cadr arguments))
           (x-atom (list *b1-logic-atom* x))
           (y-atom (list *b1-logic-atom* y)))
      (proof-with-checked-results
          ((x-cons (proof-proof-assume proof x-atom nil))
           (y-cons (proof-proof-assume proof y-atom nil))
           (x-is-atom (proof-proof-assume proof x-atom t))
           (y-is-atom (proof-proof-assume proof y-atom t)))
        (let* ((induction (b1-induction-tree-induction-init lib claim x))
               (heads-match (proof-eq (list *library-car* x) (list *library-car* y))))
          (proof-with-checked-results
              ((same (proof-proof-assume proof heads-match t))
               (same (b1-lexical-lexicographic-induction-recur
                      *library-cdr* same lib x-cons y-cons x y x-atom induction claim definitions))
               (different (proof-proof-assume proof heads-match nil))
               (different (b1-lexical-lexicographic-induction-recur
                           *library-car* different lib x-cons y-cons x y x-atom (cdr same) claim definitions))
               (both-cons (proof-proof-cases proof heads-match (car same) (car different)))
               (left-only (b1-logic-bookproof-case-proof lib claim (list x-is-atom y-cons)
                                                        (append definitions (list *proof-not*)) nil 16))
               (right-only (b1-logic-bookproof-case-proof lib claim (list x-cons y-is-atom)
                                                         (append definitions (list *proof-not*)) nil 16))
               (both-atoms (if (eq (car atoms) :strict)
                               (b1-lexical-strict-atoms lib claim (cadr atoms) (caddr atoms)
                                                       (list x-is-atom y-is-atom))
                             (b1-lexical-fast-lexorder-both-atoms
                              (list x-is-atom y-is-atom) lib (cadr atoms) (caddr atoms)
                              claim (cadddr atoms)))))
            (let* ((lib (cdr both-atoms))
                   (proof (library-library-proof lib))
                   (induction (b1-induction-tree-induction-with-lib (cdr different) lib)))
              (proof-with-checked-results
                  ((left (proof-proof-cases proof y-atom (car both-atoms) left-only))
                   (right (proof-proof-cases proof y-atom right-only both-cons))
                   (step (proof-proof-cases proof x-atom left right))
                   (step (b1-induction-tree-induction-finish induction step)))
                (cons step lib)))))))))

(defun b1-lexical-fast-lexorder (lib formula)
  (proof-with-checked-results ((arguments (b1-lexical-comparison-arguments formula)))
    (let ((unfold (list *b1-lexical-fast* *b1-total-order-order* *b1-lexical-alphorder* *proof-not* *b1-logic-eq*)))
      (proof-with-checked-results
          ((result (b1-lexical-lexicographic-induction
                    lib formula (list *b1-lexical-fast* *b1-total-order-order*)
                    (list :weak (car arguments) (cadr arguments) unfold))))
        (car result)))))

(defun b1-lexical-fast-strict-order (lib formula)
  (proof-with-checked-results
      ((arguments (b1-lexical-comparison-arguments formula))
       (claim (proof-term-at formula 1)))
    (let* ((x (car arguments))
           (y (cadr arguments))
           (dual (proof-eq claim (proof-neg (list *b1-lexical-fast* y x)))))
      (proof-with-checked-results
          ((result (b1-lexical-lexicographic-induction
                    lib dual (list *b1-lexical-fast-strict* *b1-lexical-fast*) (list :strict x y))))
        (let* ((lib (cdr result))
               (proof (library-library-proof lib)))
          (proof-with-checked-results
              ((weak (proof-proof-fact proof (proof-sym "FAST-LEXORDER-IS-LEXORDER" "ACL2")
                                       (list (list *library-x* y) (list *library-y* x))))
               (step (proof-proof-rewrite proof (car result) weak '(1 2 1)))
               (dual (b1-lexical-strict-dual lib x y)))
            (let* ((lib (cdr dual))
                   (proof (library-library-proof lib)))
              (proof-with-checked-results
                  ((reversed (proof-proof-symmetric proof (car dual)))
                   (step (proof-proof-chain proof step (list reversed))))
                (cons step lib)))))))))
