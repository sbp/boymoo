(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b1-revappend-rev* (proof-cl "REVAPPEND"))
(defconst *b1-revappend-last* (proof-cl "LAST"))
(defconst *b1-revappend-butlast* (proof-cl "BUTLAST"))
(defconst *b1-revappend-append* (proof-sym "BINARY-APPEND" "ACL2"))
(defconst *b1-revappend-fix* (proof-sym "TRUE-LIST-FIX" "ACL2"))
(defconst *b1-revappend-iff* (proof-sym "IFF" "ACL2"))
(defconst *b1-revappend-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *b1-revappend-intersection* (proof-sym "INTERSECTION-EQUAL" "ACL2"))
(defconst *b1-revappend-take* (proof-sym "TAKE" "ACL2"))
(defconst *b1-revappend-nfix* (proof-sym "NFIX" "ACL2"))
(defconst *b1-revappend-acc* (proof-sym "ACC" "ACL2"))
(defconst *b1-revappend-item* (proof-sym "A" "ACL2"))

(defun b1-revappend-first-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b1-revappend-first-at-at (step index argument)
  (proof-with-checked-results ((term (b1-revappend-first-at step index)))
    (proof-term-at term argument)))

(defun b1-revappend-equation-sides (formula)
  (if (integerp formula)
      '(:failure "failure" "")
    (proof-list-of-length (cdr formula) 2)))

(defun b1-revappend-chain-symmetric (lib first rest last)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((reversed (proof-proof-symmetric proof last)))
      (proof-proof-chain proof first (append rest (list reversed))))))

(defun b1-revappend-open-list (lib term evidence)
  (proof-with-checked-results ((head (proof-term-at term 0)))
    (b1-logic-bookproof-normalize
     lib term evidence (list head *b1-logic-atom* *b1-logic-endp* *proof-not*)
     nil nil nil nil)))

(defun b1-revappend-extend-accumulator (x accumulator)
  (list *proof-cons* (list *library-car* x) accumulator))

(defun b1-revappend-list-induction-prepare (lib formula x accumulator)
  (let* ((test (list *proof-consp* x))
         (bindings (list (cons x (list *library-cdr* x))))
         (bindings (if accumulator
                       (table-put bindings accumulator
                                    (b1-revappend-extend-accumulator x accumulator))
                     bindings))
         (induction (b1-induction-tree-induction-init lib formula x)))
    (proof-with-checked-results
        ((hypothesis (b1-induction-tree-induction-hypothesis
                      induction bindings (list (list test t))))
         (cons-step (proof-proof-assume (library-library-proof lib) test t)))
      (list (cdr hypothesis) test cons-step (car hypothesis)))))

(defun b1-revappend-list-induction (lib preparation base step)
  (proof-with-checked-results
      ((preparation preparation)
       (step step)
       (base base)
       (cases (proof-proof-cases (library-library-proof lib)
                                 (cadr preparation) step base)))
    (b1-induction-tree-induction-finish (car preparation) cases)))

(defmacro b1-revappend-with-list-induction (parameters step base)
  (let ((lib (nth 0 parameters))
        (formula (nth 1 parameters))
        (x (nth 2 parameters))
        (accumulator (nth 3 parameters))
        (atom (nth 4 parameters))
        (cons-step (nth 5 parameters))
        (hypothesis (nth 6 parameters)))
    `(proof-with-checked-results
         ((b1-revappend-preparation (b1-revappend-list-induction-prepare
                                     ,lib ,formula ,x ,accumulator))
          (b1-revappend-cons-case
           (let ((,cons-step (caddr b1-revappend-preparation))
                 (,hypothesis (cadddr b1-revappend-preparation)))
             ,step))
          (,atom (proof-proof-assume (library-library-proof ,lib)
                                     (cadr b1-revappend-preparation) nil))
          (b1-revappend-atom-case ,base))
       (b1-revappend-list-induction
        ,lib b1-revappend-preparation b1-revappend-atom-case b1-revappend-cons-case))))

(defun b1-revappend-lift-argument (lib expression argument index)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((reflexive (proof-proof-reflexive proof expression)))
      (proof-proof-rewrite proof reflexive argument (list 1 2 index)))))

(defun b1-revappend-open-argument (lib expression term evidence index)
  (proof-with-checked-results ((argument (b1-revappend-open-list lib term evidence)))
    (b1-revappend-lift-argument lib expression argument index)))

(defun b1-revappend-accumulator-commutation-base (atom lib before after operation-on-result)
  (proof-with-checked-results
      ((left (b1-revappend-open-list lib before (list atom)))
       (right (b1-revappend-open-argument lib after operation-on-result (list atom) 1)))
    (b1-revappend-chain-symmetric lib left nil right)))

(defun b1-revappend-accumulator-commutation-step
    (cons-step induction lib before x operation accumulator parameters after operation-on-result)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((moved (b1-revappend-open-list lib before (list cons-step)))
         (operation-step
          (b1-revappend-open-list
           lib (cons operation (cons (b1-revappend-extend-accumulator x accumulator)
                                     parameters)) nil))
         (reversed (proof-proof-symmetric proof operation-step))
         (moved (proof-proof-rewrite proof moved reversed '(1 2 2)))
         (extended (b1-revappend-open-argument
                    lib after operation-on-result (list cons-step) 1)))
      (b1-revappend-chain-symmetric lib moved (list induction) extended))))

(defun b1-revappend-accumulator-commutation-initial (initial)
  (cond ((integerp initial)
         '(:failure "failure" ""))
        ((consp (cdr initial)) initial)
        (t '(:failure "failure" ""))))

(defun b1-revappend-accumulator-commutation (lib formula)
  (proof-with-checked-results
      ((sides (b1-revappend-equation-sides formula)))
    (let* ((reversed (not (proof-is-call (car sides) *b1-revappend-rev*)))
           (before (if reversed (cadr sides) (car sides)))
           (after (if reversed (car sides) (cadr sides))))
      (proof-with-checked-results
          ((before (proof-list-of-length before 3))
           (initial (b1-revappend-accumulator-commutation-initial (caddr before)))
           (operation-on-result (proof-term-at after 1)))
        (let ((operation (car initial))
              (accumulator (cadr initial))
              (parameters (cddr initial))
              (x (cadr before))
              (goal (proof-eq before after)))
          (proof-with-checked-results
              ((step
                (b1-revappend-with-list-induction
                 (lib goal x accumulator atom cons-step induction)
                 (b1-revappend-accumulator-commutation-step
                  cons-step induction lib before x operation accumulator parameters
                  after operation-on-result)
                 (b1-revappend-accumulator-commutation-base
                  atom lib before after operation-on-result))))
            (if reversed
                (proof-proof-symmetric (library-library-proof lib) step)
              step)))))))

(defun b1-revappend-revappend-with-nil-accumulator-equation (claim lib)
  (proof-with-checked-results
      ((sides (b1-revappend-equation-sides claim)))
    (let* ((reverse (not (proof-is-call (car sides) *b1-revappend-rev*)))
           (rev (if reverse (cadr sides) (car sides)))
           (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((rev (proof-list-of-length rev 3))
           (law (proof-proof-fact
                 proof (proof-sym "REVAPPEND-OF-APPEND-ARG2" "ACL2")
                 (list (list *library-x* (cadr rev))
                       (list *library-y* (caddr rev))
                       (list *b1-revappend-acc* *proof-false*))))
           (identity (b1-revappend-open-list
                      lib (list *b1-revappend-append* *proof-false* (caddr rev)) nil))
           (law (proof-proof-rewrite proof law identity '(1 1 2))))
        (if reverse (proof-proof-symmetric proof law) law)))))

(defun b1-revappend-revappend-with-nil-accumulator (lib formula)
  (if (proof-is-call formula *library-implies*)
      (proof-with-checked-results
          ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
           (claim (proof-term-at formula 2))
           (consequence (b1-revappend-revappend-with-nil-accumulator-equation claim lib)))
        (b1-logic-bookproof-prove-implication-with-premise lib formula premise consequence))
    (b1-revappend-revappend-with-nil-accumulator-equation formula lib)))

(defun b1-revappend-car-of-revappend-base (atom lib lhs call rhs)
  (proof-with-checked-results
      ((opened (b1-revappend-open-argument lib lhs call (list atom) 1))
       (selected (proof-proof-if-false (library-library-proof lib) rhs)))
    (b1-revappend-chain-symmetric lib opened nil selected)))

(defun b1-revappend-car-of-revappend-step-branch (tail lib reduced rhs cons-step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((current (b1-revappend-first-at reduced 2))
         (normalized (b1-logic-bookproof-normalize
                      lib current (list tail) nil nil nil nil nil))
         (value (proof-proof-chain proof reduced (list normalized)))
         (last (b1-logic-bookproof-normalize
                lib rhs (list cons-step tail)
                (list *b1-revappend-last* *b1-logic-atom* *proof-not*)
                nil nil nil nil)))
      (b1-revappend-chain-symmetric lib value nil last))))

(defun b1-revappend-car-of-revappend-step (cons-step induction lib lhs call rhs tail-test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-argument lib lhs call (list cons-step) 1))
         (reduced (proof-proof-chain proof opened (list induction)))
         (tail-cons (proof-proof-assume proof tail-test t))
         (yes (b1-revappend-car-of-revappend-step-branch tail-cons lib reduced rhs cons-step))
         (tail-atom (proof-proof-assume proof tail-test nil))
         (no (b1-revappend-car-of-revappend-step-branch tail-atom lib reduced rhs cons-step)))
      (proof-proof-cases proof tail-test yes no))))

(defun b1-revappend-car-of-revappend (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 3))
       (lhs (proof-list-of-length (cadr formula) 2))
       (call (proof-list-of-length (cadr lhs) 3)))
    (let* ((rhs (caddr formula))
           (x (cadr call))
           (tail-test (list *proof-consp* (list *library-cdr* x))))
      (b1-revappend-with-list-induction
       (lib formula x (caddr call) atom cons-step induction)
       (b1-revappend-car-of-revappend-step cons-step induction lib lhs call rhs tail-test)
       (b1-revappend-car-of-revappend-base atom lib lhs call rhs)))))

(defun b1-revappend-consp-value (lib consp-step)
  (proof-with-checked-results
      ((term (b1-revappend-first-at consp-step 1))
       (boolean (proof-proof-fact (library-library-proof lib) "booleanp-consp"
                                  (list (list *library-x* term)))))
    (b1-logic-bookproof-boolean-value lib consp-step boolean)))

(defun b1-revappend-consp-of-revappend-base (atom lib lhs call rhs)
  (proof-with-checked-results
      ((opened (b1-revappend-open-argument lib lhs call (list atom) 1))
       (selected (proof-proof-if-false (library-library-proof lib) rhs)))
    (b1-revappend-chain-symmetric lib opened nil selected)))

(defun b1-revappend-consp-of-revappend-step
    (cons-step induction lib lhs call rhs x acc child-has-head)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-argument lib lhs call (list cons-step) 1))
         (opened (proof-proof-chain proof opened (list induction)))
         (pair (proof-proof-fact proof "consp-cons"
                                 (list (list *library-x* (list *library-car* x))
                                       (list *library-y* acc))))
         (test (proof-proof-assume proof child-has-head t))
         (current (b1-revappend-first-at opened 2))
         (select-yes (proof-proof-select proof current test))
         (child-value (b1-revappend-consp-value lib test))
         (yes (proof-proof-chain proof opened (list select-yes child-value)))
         (no-test (proof-proof-assume proof child-has-head nil))
         (select-no (proof-proof-select proof current no-test))
         (pair-value (b1-revappend-consp-value lib pair))
         (no (proof-proof-chain proof opened (list select-no pair-value)))
         (selected (proof-proof-select proof rhs cons-step))
         (whole-value (b1-revappend-consp-value lib cons-step))
         (expected (proof-proof-chain proof selected (list whole-value)))
         (cases (proof-proof-cases proof child-has-head yes no)))
      (b1-revappend-chain-symmetric lib cases nil expected))))

(defun b1-revappend-consp-of-revappend (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 3))
       (lhs (proof-list-of-length (cadr formula) 2))
       (call (proof-list-of-length (cadr lhs) 3)))
    (let* ((rhs (caddr formula))
           (x (cadr call))
           (acc (caddr call))
           (child-has-head (list *proof-consp* (list *library-cdr* x))))
      (b1-revappend-with-list-induction
       (lib formula x acc atom cons-step induction)
       (b1-revappend-consp-of-revappend-step
        cons-step induction lib lhs call rhs x acc child-has-head)
       (b1-revappend-consp-of-revappend-base atom lib lhs call rhs)))))

(defun b1-revappend-cons-is-nonempty (lib consp-step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((value (b1-revappend-first-at consp-step 1)))
      (let ((empty (proof-eq value *proof-false*)))
        (proof-with-checked-results
            ((assumed (proof-proof-assume proof empty t))
             (impossible (proof-proof-rewrite proof consp-step assumed '(1 1)))
             (simplified (proof-proof-simplify-first proof impossible nil nil))
             (not-empty (proof-proof-front proof simplified (proof-neg empty)))
             (either (proof-proof-nil-or-true proof value)))
          (proof-proof-cut proof either not-empty))))))

(defun b1-revappend-revappend-nonempty (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((formula (proof-list-of-length formula 3))
         (call (proof-list-of-length (cadr formula) 3)))
      (let ((test (list *proof-consp* (cadr call))))
        (proof-with-checked-results
            ((cons-step (proof-proof-assume proof test t))
             (rule (proof-proof-fact
                    proof (proof-sym "CONSP-OF-REVAPPEND" "ACL2")
                    (list (list *library-x* (cadr call)) (list *library-y* (caddr call)))))
             (current (b1-revappend-first-at rule 2))
             (selected (proof-proof-select proof current cons-step))
             (cons-value (b1-revappend-consp-value lib cons-step))
             (value (proof-proof-chain proof rule (list selected cons-value)))
             (true-value (proof-proof-true-from-eq proof value))
             (have-value (b1-revappend-cons-is-nonempty lib true-value))
             (yes (b1-logic-bookproof-normalize-proof
                   lib formula (list cons-step have-value) (list *b1-revappend-iff*) nil nil))
             (atom (proof-proof-assume proof test nil))
             (opened (b1-revappend-open-list lib call (list atom)))
             (no (b1-logic-bookproof-case-proof
                  lib formula (list atom) (list *b1-revappend-iff*)
                  (list (b1-logic-equal-to opened)) 16)))
          (proof-proof-cases proof test yes no))))))

(defun b1-revappend-length-of-revappend-finish (value cons-step lib rhs x)
  (proof-with-checked-results
      ((desired (b1-revappend-open-argument
                 lib rhs (list *library-len* x) (list cons-step) 1))
       (value-right (b1-revappend-first-at value 2))
       (desired-right (b1-revappend-first-at desired 2))
       (arithmetic (library-library-linear-equal lib value-right desired-right nil)))
    (b1-revappend-chain-symmetric lib value (list arithmetic) desired)))

(defun b1-revappend-length-of-revappend-base (atom lib lhs call rhs x)
  (proof-with-checked-results
      ((value (b1-revappend-open-argument lib lhs call (list atom) 1)))
    (b1-revappend-length-of-revappend-finish value atom lib rhs x)))

(defun b1-revappend-length-of-revappend-step (cons-step induction lib lhs call rhs x acc)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (b1-revappend-open-argument lib lhs call (list cons-step) 1))
         (value (proof-proof-chain proof value (list induction)))
         (actual (b1-revappend-open-list
                  lib (list *library-len* (b1-revappend-extend-accumulator x acc)) nil))
         (value (proof-proof-rewrite proof value actual '(1 2 2))))
      (b1-revappend-length-of-revappend-finish value cons-step lib rhs x))))

(defun b1-revappend-length-of-revappend (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 3))
       (lhs (proof-list-of-length (cadr formula) 2))
       (call (proof-list-of-length (cadr lhs) 3)))
    (let ((rhs (caddr formula))
          (x (cadr call))
          (acc (caddr call)))
      (b1-revappend-with-list-induction
       (lib formula x acc atom cons-step induction)
       (b1-revappend-length-of-revappend-step cons-step induction lib lhs call rhs x acc)
       (b1-revappend-length-of-revappend-base atom lib lhs call rhs x)))))

(defun b1-revappend-revappend-of-list-fix-expose (cons-step lib lhs x)
  (proof-with-checked-results
      ((fixed (b1-revappend-open-argument
               lib lhs (list *b1-revappend-fix* x) (list cons-step) 1))
       (current (b1-revappend-first-at fixed 2))
       (opened (b1-revappend-open-list lib current nil)))
    (proof-proof-chain (library-library-proof lib) fixed (list opened))))

(defun b1-revappend-revappend-of-list-fix-base (atom lib lhs rhs x)
  (proof-with-checked-results
      ((left (b1-revappend-revappend-of-list-fix-expose atom lib lhs x))
       (right (b1-revappend-open-list lib rhs (list atom))))
    (b1-revappend-chain-symmetric lib left nil right)))

(defun b1-revappend-revappend-of-list-fix-step (cons-step induction lib lhs rhs x)
  (proof-with-checked-results
      ((left (b1-revappend-revappend-of-list-fix-expose cons-step lib lhs x))
       (right (b1-revappend-open-list lib rhs (list cons-step))))
    (b1-revappend-chain-symmetric lib left (list induction) right)))

(defun b1-revappend-revappend-of-list-fix (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 3))
       (lhs (proof-list-of-length (cadr formula) 3))
       (fixed (proof-list-of-length (cadr lhs) 2)))
    (let ((rhs (caddr formula))
          (x (cadr fixed))
          (acc (caddr lhs)))
      (b1-revappend-with-list-induction
       (lib formula x acc atom cons-step induction)
       (b1-revappend-revappend-of-list-fix-step cons-step induction lib lhs rhs x)
       (b1-revappend-revappend-of-list-fix-base atom lib lhs rhs x)))))

(defun b1-revappend-reversed-twice-base (atom lib lhs inner rhs)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-argument lib lhs inner (list atom) 1))
         (current (b1-revappend-first-at opened 2))
         (reduced (b1-revappend-open-list lib current nil))
         (opened (proof-proof-chain proof opened (list reduced)))
         (right (b1-revappend-open-list lib rhs (list atom))))
      (b1-revappend-chain-symmetric lib opened nil right))))

(defun b1-revappend-reversed-twice-step (cons-step induction lib lhs inner rhs x)
  (let* ((proof (library-library-proof lib))
         (tail (list *library-cdr* x))
         (singleton (list *proof-cons* (list *library-car* x) *proof-false*))
         (reverse-tail (list *b1-revappend-rev* tail *proof-false*)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-argument lib lhs inner (list cons-step) 1))
         (law (b1-revappend-revappend-with-nil-accumulator
               lib (proof-eq (list *b1-revappend-rev* tail singleton)
                             (list *b1-revappend-append* reverse-tail singleton))))
         (opened (proof-proof-rewrite proof opened law '(1 2 1)))
         (concat (proof-proof-fact
                  proof (proof-sym "REVAPPEND-OF-APPEND-ARG1" "ACL2")
                  (list (list *library-x* reverse-tail)
                        (list *library-y* singleton)
                        (list *library-z* *proof-false*))))
         (opened (proof-proof-chain proof opened (list concat)))
         (singleton-reverse
          (b1-revappend-open-list lib (list *b1-revappend-rev* singleton *proof-false*) nil))
         (current (b1-revappend-first-at singleton-reverse 2))
         (reduced (b1-revappend-open-list lib current nil))
         (singleton-reverse (proof-proof-chain proof singleton-reverse (list reduced)))
         (opened (proof-proof-rewrite proof opened singleton-reverse '(1 2 1)))
         (current (b1-revappend-first-at opened 2))
         (reduced (b1-revappend-open-list lib current nil))
         (opened (proof-proof-chain proof opened (list reduced)))
         (nested (b1-revappend-first-at-at opened 2 2))
         (reduced (b1-revappend-open-list lib nested nil))
         (opened (proof-proof-rewrite proof opened reduced '(1 2 2)))
         (opened (proof-proof-rewrite proof opened induction '(1 2 2)))
         (right (b1-revappend-open-list lib rhs (list cons-step))))
      (b1-revappend-chain-symmetric lib opened nil right))))

(defun b1-revappend-reversed-twice (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 3))
       (lhs (proof-list-of-length (cadr formula) 3))
       (inner (proof-list-of-length (cadr lhs) 3)))
    (let ((rhs (caddr formula))
          (x (cadr inner)))
      (b1-revappend-with-list-induction
       (lib formula x nil atom cons-step induction)
       (b1-revappend-reversed-twice-step cons-step induction lib lhs inner rhs x)
       (b1-revappend-reversed-twice-base atom lib lhs inner rhs)))))

(defun b1-revappend-count-of-revappend-base (atom lib call acc count-x total)
  (proof-with-checked-results
      ((first (b1-revappend-open-list lib call (list atom)))
       (natural (library-library-natural lib count-x))
       (lower (library-library-cite lib "NATURAL-NONNEGATIVE"
                                   (list count-x) (list natural)))
       (sums (b1-arithmetic-number-sums-init lib))
       (negative (b1-revappend-first-at lower 1))
       (comparison (b1-arithmetic-number-sums-comparison-equation
                    sums (library-lt total (list *library-count* acc)) negative nil)))
    (let* ((lib (b1-arithmetic-number-sums-library sums))
           (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((reversed (proof-proof-symmetric proof comparison))
           (bound (proof-proof-rewrite proof lower reversed '(1 1)))
           (reversed (proof-proof-symmetric proof first))
           (step (proof-proof-rewrite proof bound reversed '(1 1 2 1))))
        (cons step lib)))))

(defun b1-revappend-count-of-revappend-step (cons-step induction lib call x acc count-x total)
  (let ((proof (library-library-proof lib))
        (new-accumulator (b1-revappend-extend-accumulator x acc)))
    (proof-with-checked-results
        ((actual (b1-revappend-open-list lib (list *library-count* new-accumulator) nil))
         (lower (proof-proof-rewrite proof induction actual '(1 1 1 2)))
         (expand (b1-revappend-open-argument lib total count-x (list cons-step) 1))
         (lower-left (b1-revappend-first-at-at lower 1 1))
         (expanded (b1-revappend-first-at expand 2))
         (normal (library-library-linear-equal lib lower-left expanded nil))
         (aligned (b1-revappend-chain-symmetric lib normal nil expand))
         (lower (proof-proof-rewrite proof lower aligned '(1 1 1)))
         (opened (b1-revappend-open-list lib call (list cons-step)))
         (reversed (proof-proof-symmetric proof opened)))
      (proof-proof-rewrite proof lower reversed '(1 1 2 1)))))

(defun b1-revappend-count-of-revappend (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 2))
       (comparison (proof-list-of-length (cadr formula) 3))
       (counted (proof-list-of-length (caddr comparison) 2))
       (call (proof-list-of-length (cadr counted) 3)))
    (let* ((total (cadr comparison))
           (x (cadr call))
           (acc (caddr call))
           (count-x (list *library-count* x)))
      (proof-with-checked-results
          ((preparation (b1-revappend-list-induction-prepare lib formula x acc))
           (step (b1-revappend-count-of-revappend-step
                  (caddr preparation) (cadddr preparation) lib call x acc count-x total))
           (atom (proof-proof-assume (library-library-proof lib) (cadr preparation) nil))
           (base (b1-revappend-count-of-revappend-base atom lib call acc count-x total))
           (finished (b1-revappend-list-induction (cdr base) preparation (car base) step)))
        (cons finished (cdr base))))))

(defun b1-revappend-positive-length (lib cons-step)
  (proof-with-checked-results ((x (b1-revappend-first-at cons-step 1)))
    (let ((smaller (list *library-len* (list *library-cdr* x))))
      (proof-with-checked-results
          ((natural (library-library-natural lib smaller))
           (lower (library-library-cite lib "NATURAL-NONNEGATIVE"
                                       (list smaller) (list natural)))
           (integer-step (library-library-type-of lib smaller nil))
           (successor (library-library-cite lib "POSITIVE-ONE-PLUS"
                                           (list smaller) (list integer-step lower)))
           (opened (b1-revappend-open-list lib (list *library-len* x) (list cons-step))))
        (library-library-transport-argument lib successor opened 2)))))

(defun b1-revappend-reverse-not-unchanged (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((formula (proof-list-of-length formula 3))
         (same (proof-list-of-length (cadr formula) 3))
         (call (proof-list-of-length (caddr same) 3)))
      (let* ((opposite (caddr formula))
             (acc (cadr same))
             (x (cadr call))
             (test (list *proof-consp* x))
             (length-acc (list *library-len* acc)))
        (proof-with-checked-results
            ((cons-step (proof-proof-assume proof test t))
             (atom (proof-proof-assume proof test nil))
             (length-x (b1-revappend-positive-length lib cons-step))
             (positive (b1-revappend-first-at length-x 2))
             (sum-larger (library-library-less-from-difference
                          lib length-acc (library-plus positive length-acc) length-x nil))
             (distribution (proof-proof-fact
                            proof (proof-sym "LEN-OF-REVAPPEND" "ACL2")
                            (list (list *library-x* x) (list *library-y* acc))))
             (assumed (proof-proof-assume proof same t))
             (reversed (proof-proof-symmetric proof assumed))
             (lengths-equal (proof-proof-rewrite proof distribution reversed '(1 1 1)))
             (reversed (proof-proof-symmetric proof lengths-equal))
             (impossible (proof-proof-rewrite proof sum-larger reversed '(1 2)))
             (integer-step (library-library-type-of lib length-acc nil))
             (reflexive (library-library-cite lib "WEAK-REFLEXIVE"
                                             (list length-acc) (list integer-step)))
             (cut (proof-proof-cut proof impossible reflexive))
             (unequal (proof-proof-front proof cut (proof-neg same)))
             (false-value (b1-logic-bookproof-false-value lib unequal))
             (normalized (b1-logic-bookproof-normalize
                          lib opposite (list cons-step) (list *proof-not*) nil nil nil nil))
             (yes (b1-revappend-chain-symmetric lib false-value nil normalized))
             (opened (b1-revappend-open-list lib call (list atom)))
             (no (b1-logic-bookproof-normalize-proof
                  lib formula (list atom) (list *proof-not*)
                  (list (b1-logic-equal-to opened)) nil)))
          (proof-proof-cases proof test yes no))))))

(defun b1-revappend-cons-value (lib term)
  (if (proof-is-call term *proof-cons*)
      (proof-proof-fact (library-library-proof lib) "consp-cons"
                        (seq-zip (list *library-x* *library-y*) (cdr term)))
    '(:failure "failure" "")))

(defun b1-revappend-right-disjunct (lib term step)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (proof-term-at term 1))
         (assumed (proof-proof-assume proof test t))
         (selected (proof-proof-if-true proof term))
         (yes (proof-proof-transport proof assumed selected))
         (selected (proof-proof-if-false proof term))
         (no (proof-proof-transport proof step selected)))
      (proof-proof-cases proof test yes no))))

(defun b1-revappend-nonempty-fold-of-reversal-base (atom lib lhs call slot scan formula)
  (proof-with-checked-results
      ((left (b1-revappend-open-argument lib lhs call (list atom) slot))
       (empty (b1-revappend-open-list lib scan (list atom))))
    (b1-logic-bookproof-case-proof
     lib formula nil (list *b1-revappend-iff*)
     (list (b1-logic-equal-to left) (b1-logic-equal-to empty)) 16)))

(defun b1-revappend-nonempty-fold-of-reversal-step
    (cons-step induction lib lhs call slot head-test scan scan-pair x formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left (b1-revappend-open-argument lib lhs call (list cons-step) slot))
         (hit (proof-proof-assume proof head-test t))
         (result-x (b1-revappend-open-list lib scan (list cons-step hit)))
         (result-pair (b1-revappend-open-list lib scan-pair (list hit)))
         (current-x (b1-revappend-first-at result-x 2))
         (nonempty-x (if (equal current-x x)
                         cons-step
                       (b1-revappend-cons-value lib current-x)))
         (nonempty-x (b1-revappend-cons-is-nonempty lib nonempty-x))
         (witnessed-x (proof-proof-transport proof nonempty-x result-x))
         (current-pair (b1-revappend-first-at result-pair 2))
         (nonempty-pair (b1-revappend-cons-value lib current-pair))
         (nonempty-pair (b1-revappend-cons-is-nonempty lib nonempty-pair))
         (witnessed-pair (proof-proof-transport proof nonempty-pair result-pair))
         (induction-right (b1-revappend-first-at induction 2))
         (witness (b1-revappend-right-disjunct lib induction-right witnessed-pair))
         (induction-left (b1-revappend-first-at induction 1))
         (child-truth (b1-logic-bookproof-forces
                       lib induction-left induction (list witness) (list *b1-revappend-iff*) nil))
         (transported (proof-proof-transport proof child-truth left))
         (yes (b1-logic-bookproof-normalize-proof
               lib formula (list transported witnessed-x) (list *b1-revappend-iff*) nil nil))
         (miss (proof-proof-assume proof head-test nil))
         (scan-tail (b1-revappend-open-list lib scan (list cons-step miss)))
         (older-acc (b1-revappend-open-list lib scan-pair (list miss)))
         (inherited (proof-proof-rewrite proof induction older-acc '(1 2 3)))
         (reflexive (proof-proof-reflexive proof formula))
         (shape (proof-proof-rewrite proof reflexive left '(1 2 1)))
         (shape (proof-proof-rewrite proof shape scan-tail '(1 2 2 1)))
         (shape (proof-proof-rewrite proof shape scan-tail '(1 2 2 2)))
         (no (proof-proof-transport proof inherited shape)))
      (proof-proof-cases proof head-test yes no))))

(defun b1-revappend-nonempty-fold-of-reversal (lib formula slot head-test)
  (proof-with-checked-results ((formula (proof-list-of-length formula 3)))
    (let* ((lhs (cadr formula))
           (offset (if (and (integerp slot) (< slot 0)) (+ (len lhs) slot) slot)))
      (proof-with-checked-results
          ((call (if (and (integerp offset) (<= 0 offset))
                     (proof-term-at lhs offset)
                   '(:failure "failure" "")))
           (call (proof-list-of-length call 3)))
        (let* ((x (cadr call))
               (acc (caddr call))
               (shape (append (seq-slice lhs :none slot)
                              (cons *proof-result* (seq-slice lhs (1+ slot) :none)))))
          (proof-with-checked-results
              ((scan (proof-subst shape (list (cons *proof-result* x))))
               (scan-pair (proof-subst shape
                                       (list (cons *proof-result*
                                                   (b1-revappend-extend-accumulator x acc))))))
            (b1-revappend-with-list-induction
             (lib formula x acc atom cons-step induction)
             (b1-revappend-nonempty-fold-of-reversal-step
              cons-step induction lib lhs call slot head-test scan scan-pair x formula)
             (b1-revappend-nonempty-fold-of-reversal-base atom lib lhs call slot scan formula))))))))

(defun b1-revappend-member-of-revappend (lib formula)
  (let* ((name (proof-sym "SELF-MEMBER-REVAPPEND-IFF" "ACL2"))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((updated
          (if (assoc-equal name (proof-proof-facts proof))
              lib
            (let* ((left (list *b1-revappend-member* *b1-revappend-item* *library-x*))
                   (right (list *b1-revappend-member* *b1-revappend-item* *library-y*))
                   (reverse (list *b1-revappend-rev* *library-x* *library-y*))
                   (claim (list *b1-revappend-iff*
                                (list *b1-revappend-member* *b1-revappend-item* reverse)
                                (proof-ite left left right)))
                   (head-test (proof-eq *b1-revappend-item* (list *library-car* *library-x*))))
              (proof-with-checked-results
                  ((step (b1-revappend-nonempty-fold-of-reversal lib claim 2 head-test)))
                (library-library-lemma lib "MEMBER-REVAPPEND-IFF" claim step nil)))))
         (step (b1-logic-bookproof-from-fact updated name formula)))
      (cons step updated))))

(defun b1-revappend-intersects-reversed-first (lib formula)
  (proof-with-checked-results
      ((lhs (proof-term-at formula 1))
       (lhs (proof-list-of-length lhs 3))
       (reverse (proof-list-of-length (cadr lhs) 3)))
    (b1-revappend-nonempty-fold-of-reversal
     lib formula 1 (list *b1-revappend-member* (list *library-car* (cadr reverse)) (caddr lhs)))))

(defun b1-revappend-intersects-reversed-second-member-rule (term lib mem-reversed equivalence)
  (if (proof-is-call term *proof-if*)
      (proof-with-checked-results ((test (proof-term-at term 1)))
        (if (equal test mem-reversed)
            (b1-logic-bookproof-select-equivalent-test lib term equivalence)
          (cons nil lib)))
    (cons nil lib)))

(defun b1-revappend-intersects-reversed-second-normalization-pass (lib lhs evidence replies)
  (b1-logic-bookproof-normalize-with-library
   lib lhs evidence
   (list *b1-revappend-intersection* *b1-logic-endp* *b1-logic-atom* *proof-not*)
   '((:callback :member-rule)) nil nil nil replies))

(defun b1-revappend-intersects-reversed-second-normalize
    (n lib lhs evidence mem-reversed equivalence replies result)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "b1-revappend-intersects-reversed-second-normalize"))
   ((b1-logic-call-p result)
    (let* ((reply (b1-revappend-intersects-reversed-second-member-rule
                   (b1-logic-call-term result) (b1-logic-call-library result)
                   mem-reversed equivalence))
           (replies (append replies (list reply))))
      (b1-revappend-intersects-reversed-second-normalize
       (1- n) lib lhs evidence mem-reversed equivalence replies
       (b1-revappend-intersects-reversed-second-normalization-pass lib lhs evidence replies))))
   (t result)))

(defun b1-revappend-intersects-reversed-second-base (atom lib formula)
  (b1-logic-bookproof-case-proof
   lib formula (list atom)
   (list *b1-revappend-intersection* *b1-logic-endp* *b1-logic-atom*
         *proof-not* *b1-revappend-iff*)
   nil 16))

(defun b1-revappend-intersects-reversed-second-step-left
    (evidence lib lhs cons-step mem-reversed equivalence)
  (let ((evidence (cons cons-step evidence)))
    (b1-revappend-intersects-reversed-second-normalize
     1000000 lib lhs evidence mem-reversed equivalence nil
     (b1-revappend-intersects-reversed-second-normalization-pass lib lhs evidence nil))))

(defun b1-revappend-intersects-reversed-second-step-truth (equation lib)
  (proof-with-checked-results
      ((right (b1-revappend-first-at equation 2))
       (cons-step (b1-revappend-cons-value lib right))
       (nonempty (b1-revappend-cons-is-nonempty lib cons-step)))
    (proof-proof-transport (library-library-proof lib) nonempty equation)))

(defun b1-revappend-intersects-reversed-second-step
    (cons-step induction lib lhs rhs formula mem-first mem-second mem-reversed equivalence)
  (let ((proof (library-library-proof lib))
        (unfold (list *b1-revappend-iff*)))
    (proof-with-checked-results
        ((in-first (proof-proof-assume proof mem-first t))
         (not-first (proof-proof-assume proof mem-first nil))
         (in-second (proof-proof-assume proof mem-second t))
         (not-second (proof-proof-assume proof mem-second nil))
         (first-term (proof-term-at rhs 2))
         (first (b1-revappend-open-list lib first-term (list cons-step in-first)))
         (have-first (b1-revappend-intersects-reversed-second-step-truth first lib))
         (left (b1-revappend-intersects-reversed-second-step-left
                (list in-first) lib lhs cons-step mem-reversed equivalence))
         (lib (cdr left))
         (truth (b1-revappend-intersects-reversed-second-step-truth (car left) lib))
         (yes (b1-logic-bookproof-normalize-proof
               lib formula (list truth have-first) unfold nil nil))
         (second-term (proof-term-at rhs 3))
         (second (b1-revappend-open-list lib second-term (list cons-step in-second)))
         (have-second (b1-revappend-intersects-reversed-second-step-truth second lib))
         (either (b1-revappend-right-disjunct lib rhs have-second))
         (left (b1-revappend-intersects-reversed-second-step-left
                (list not-first in-second) lib lhs cons-step mem-reversed equivalence))
         (lib (cdr left))
         (truth (b1-revappend-intersects-reversed-second-step-truth (car left) lib))
         (only-second (b1-logic-bookproof-normalize-proof
                       lib formula (list truth either) unfold nil nil))
         (reflexive (proof-proof-reflexive (library-library-proof lib) formula))
         (left (b1-revappend-intersects-reversed-second-step-left
                (list not-first not-second) lib lhs cons-step mem-reversed equivalence))
         (lib (cdr left)))
      (let ((proof (library-library-proof lib)))
        (proof-with-checked-results
            ((view (proof-proof-rewrite proof reflexive (car left) '(1 2 1)))
             (no-first (b1-revappend-open-list lib first-term (list cons-step not-first)))
             (no-second (b1-revappend-open-list lib second-term (list cons-step not-second)))
             (view (proof-proof-rewrite proof view no-first '(1 2 2 1)))
             (view (proof-proof-rewrite proof view no-first '(1 2 2 2)))
             (view (proof-proof-rewrite proof view no-second '(1 2 2 3)))
             (neither (proof-proof-transport proof induction view))
             (no-first (proof-proof-cases proof mem-second only-second neither))
             (step (proof-proof-cases proof mem-first yes no-first)))
          (cons step lib))))))

(defun b1-revappend-intersects-reversed-second (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 3))
       (lhs (proof-list-of-length (cadr formula) 3))
       (reversed-list (proof-list-of-length (caddr lhs) 3)))
    (let* ((source (cadr lhs))
           (head (list *library-car* source))
           (mem-first (list *b1-revappend-member* head (cadr reversed-list)))
           (mem-second (list *b1-revappend-member* head (caddr reversed-list)))
           (mem-reversed (list *b1-revappend-member* head reversed-list)))
      (proof-with-checked-results
          ((equivalence (b1-revappend-member-of-revappend
                         lib (list *b1-revappend-iff* mem-reversed
                                   (proof-ite mem-first mem-first mem-second))))
           (lib (cdr equivalence))
           (preparation (b1-revappend-list-induction-prepare lib formula source nil))
           (step (b1-revappend-intersects-reversed-second-step
                  (caddr preparation) (cadddr preparation) lib lhs (caddr formula)
                  formula mem-first mem-second mem-reversed (car equivalence)))
           (lib (cdr step))
           (atom (proof-proof-assume (library-library-proof lib) (cadr preparation) nil))
           (base (b1-revappend-intersects-reversed-second-base atom lib formula))
           (finished (b1-revappend-list-induction lib preparation base (car step))))
        (cons finished lib)))))

(defun b1-revappend-unequal-lengths (lib left right strict)
  (let* ((proof (library-library-proof lib))
         (same (proof-eq left right))
         (size (list *library-len* right)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof same t))
         (collapsed (proof-proof-rewrite proof strict assumed '(1 1 1)))
         (integer-step (library-library-type-of lib size nil))
         (reflexive (library-library-cite lib "WEAK-REFLEXIVE"
                                         (list size) (list integer-step)))
         (impossible (proof-proof-cut proof collapsed reflexive)))
      (proof-proof-front proof impossible (proof-neg same)))))

(defun b1-revappend-cons-equality (lib left right)
  (proof-with-checked-results
      ((left-head (proof-term-at left 1))
       (right-head (proof-term-at right 1))
       (left-tail (proof-term-at left 2))
       (right-tail (proof-term-at right 2)))
    (let ((shape (proof-ite (proof-eq left-head right-head)
                           (proof-eq left-tail right-tail) *proof-false*)))
      (b1-logic-bookproof-from-fact lib (proof-sym "CONS-EQUAL" "ACL2")
                                   (proof-eq (proof-eq left right) shape)))))

(defun b1-revappend-revappend-pair-equality-consequence-mixed
    (short short-rev is-atom long long-acc long-rev is-cons reverse lib equal-acc-lengths claim)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((short-size (b1-revappend-open-argument
                      lib (list *library-len* short-rev) short-rev (list is-atom) 1))
         (aligned (if reverse (proof-proof-symmetric proof equal-acc-lengths) equal-acc-lengths))
         (short-size (proof-proof-chain proof short-size (list aligned)))
         (big (proof-proof-fact
               proof (proof-sym "LEN-OF-REVAPPEND" "ACL2")
               (list (list *library-x* long) (list *library-y* long-acc))))
         (positive-long (b1-revappend-positive-length lib is-cons))
         (big-right (b1-revappend-first-at big 2))
         (strict (library-library-less-from-difference
                  lib (list *library-len* long-acc) big-right positive-long nil))
         (strict (library-library-transport-argument lib strict short-size 1))
         (strict (library-library-transport-argument lib strict big 2))
         (distinct (b1-revappend-unequal-lengths lib short-rev long-rev strict))
         (distinct (if reverse (b1-reciprocal-reverse-inequality lib distinct) distinct))
         (fixed-atom (b1-revappend-open-list lib (list *b1-revappend-fix* short) (list is-atom)))
         (fixed-cons (b1-revappend-open-list lib (list *b1-revappend-fix* long) (list is-cons)))
         (fixed-right (b1-revappend-first-at fixed-cons 2)))
      (let ((nil-test (proof-eq fixed-right *proof-false*)))
        (proof-with-checked-results
            ((cons-step (b1-revappend-cons-value lib fixed-right))
             (assumed (proof-proof-assume proof nil-test t))
             (impossible (proof-proof-rewrite proof cons-step assumed '(1 1)))
             (impossible (proof-proof-simplify-first proof impossible nil nil))
             (unequal (proof-proof-front proof impossible (proof-neg nil-test)))
             (reversed (proof-proof-symmetric proof fixed-cons))
             (unequal (proof-proof-rewrite proof unequal reversed '(1 1 1)))
             (reversed (proof-proof-symmetric proof fixed-atom))
             (unequal (proof-proof-rewrite proof unequal reversed '(1 1 2)))
             (unequal (if reverse unequal (b1-reciprocal-reverse-inequality lib unequal)))
             (distinct-false (b1-logic-bookproof-false-value lib distinct))
             (unequal-false (b1-logic-bookproof-false-value lib unequal)))
          (b1-logic-bookproof-case-proof
           lib claim nil nil
           (list (b1-logic-equal-to distinct-false) (b1-logic-equal-to unequal-false)) 16))))))

(defun b1-revappend-revappend-pair-equality-consequence
    (equal-acc-lengths lib claim outputs-equal choices rev-a rev-b
                       x y a b x-test y-test both induction fixing)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((cons-x (proof-proof-assume proof x-test t))
         (cons-y (proof-proof-assume proof y-test t))
         (atom-x (proof-proof-assume proof x-test nil))
         (atom-y (proof-proof-assume proof y-test nil))
         (empty-a (b1-revappend-open-list lib rev-a (list atom-x)))
         (empty-b (b1-revappend-open-list lib rev-b (list atom-y)))
         (fixed-atom-x (b1-revappend-open-list lib (car fixing) (list atom-x)))
         (fixed-atom-y (b1-revappend-open-list lib (cadr fixing) (list atom-y)))
         (base (b1-logic-bookproof-case-proof
                lib claim nil nil
                (list (b1-logic-equal-to empty-a) (b1-logic-equal-to empty-b)
                      (b1-logic-equal-to fixed-atom-x) (b1-logic-equal-to fixed-atom-y)) 16))
         (short-x (b1-revappend-revappend-pair-equality-consequence-mixed
                   x rev-a atom-x y b rev-b cons-y nil lib equal-acc-lengths claim))
         (short-y (b1-revappend-revappend-pair-equality-consequence-mixed
                   y rev-b atom-y x a rev-a cons-x t lib equal-acc-lengths claim))
         (smaller (b1-induction-tree-induction-hypothesis
                   induction both (list (list x-test t))))
         (new-a (table-get both a nil))
         (next-a (b1-revappend-open-list lib (list *library-len* new-a) nil))
         (new-b (table-get both b nil))
         (next-b (b1-revappend-open-list lib (list *library-len* new-b) nil))
         (next-guard (proof-proof-rewrite proof next-a equal-acc-lengths '(1 2 2)))
         (next-guard (b1-revappend-chain-symmetric lib next-guard nil next-b))
         (inherited (proof-proof-modus-ponens proof (car smaller) next-guard))
         (cons-equation (b1-revappend-cons-equality lib new-a new-b))
         (inherited (proof-proof-rewrite proof inherited cons-equation '(1 2 1)))
         (lhs (proof-proof-reflexive proof outputs-equal))
         (opened (b1-revappend-open-list lib rev-a (list cons-x)))
         (lhs (proof-proof-rewrite proof lhs opened '(1 2 1)))
         (opened (b1-revappend-open-list lib rev-b (list cons-y)))
         (lhs (proof-proof-rewrite proof lhs opened '(1 2 2)))
         (fixed-x (b1-revappend-open-list lib (car fixing) (list cons-x)))
         (fixed-y (b1-revappend-open-list lib (cadr fixing) (list cons-y)))
         (rhs (proof-proof-reflexive proof choices))
         (rhs (proof-proof-rewrite proof rhs fixed-x '(1 2 2 1)))
         (rhs (proof-proof-rewrite proof rhs fixed-y '(1 2 2 2)))
         (fixed-right-x (b1-revappend-first-at fixed-x 2))
         (fixed-right-y (b1-revappend-first-at fixed-y 2))
         (fixed-equal (b1-revappend-cons-equality lib fixed-right-x fixed-right-y))
         (rhs (proof-proof-rewrite proof rhs fixed-equal '(1 2 2)))
         (inherited-right (b1-revappend-first-at inherited 2))
         (rhs-right (b1-revappend-first-at rhs 2))
         (regroup (b1-logic-bookproof-case-proof lib (proof-eq inherited-right rhs-right)
                                                nil nil nil 16))
         (step (b1-revappend-chain-symmetric lib lhs (list inherited regroup) rhs))
         (y-yes (proof-proof-cases proof y-test step short-y))
         (y-no (proof-proof-cases proof y-test short-x base))
         (step (proof-proof-cases proof x-test y-yes y-no)))
      (cons step (cdr smaller)))))

(defun b1-revappend-revappend-pair-equality (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 3))
       (claim (proof-list-of-length (caddr formula) 3))
       (outputs-equal (proof-list-of-length (cadr claim) 3))
       (rev-a (proof-list-of-length (cadr outputs-equal) 3))
       (rev-b (proof-list-of-length (caddr outputs-equal) 3)))
    (let* ((x (cadr rev-a))
           (a (caddr rev-a))
           (y (cadr rev-b))
           (b (caddr rev-b))
           (x-test (list *proof-consp* x))
           (y-test (list *proof-consp* y))
           (both (list (cons x (list *library-cdr* x))))
           (both (table-put both y (list *library-cdr* y)))
           (both (table-put both a (b1-revappend-extend-accumulator x a)))
           (both (table-put both b (b1-revappend-extend-accumulator y b)))
           (induction (b1-induction-tree-induction-init lib formula x))
           (fixing (list (list *b1-revappend-fix* x) (list *b1-revappend-fix* y))))
      (proof-with-checked-results
          ((premise (b1-logic-bookproof-prove-implication-premise lib formula))
           (consequence (b1-revappend-revappend-pair-equality-consequence
                         premise lib claim outputs-equal (caddr claim) rev-a rev-b
                         x y a b x-test y-test both induction fixing))
           (step (b1-logic-bookproof-prove-implication-with-premise
                  lib formula premise (car consequence))))
        (b1-induction-tree-induction-finish (cdr consequence) step)))))

(defun b1-revappend-butlast-once-selected (items bound lib nfix-one)
  (b1-logic-bookproof-normalize
   lib (list *b1-revappend-butlast* items *proof-one*) (list bound)
   (list *b1-revappend-butlast* *proof-not*)
   (list (b1-logic-equal-to nfix-one)) nil nil nil))

(defun b1-revappend-butlast-once-short (lib x tail-length tail-case expanded nfix-one)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (b1-revappend-open-list lib tail-length (list tail-case)))
         (size (proof-proof-rewrite proof expanded opened '(1 2 2)))
         (one (b1-logic-bookproof-constant lib (library-plus *proof-one* *proof-zero*)))
         (size (proof-proof-chain proof size (list one)))
         (too-short (b1-logic-bookproof-normalize-proof
                     lib (proof-neg (library-lt *proof-one* *proof-one*))
                     nil (list *proof-not*) nil nil))
         (reversed (proof-proof-symmetric proof size))
         (too-short (proof-proof-rewrite proof too-short reversed '(1 1 2))))
      (b1-revappend-butlast-once-selected x too-short lib nfix-one))))

(defun b1-revappend-butlast-once-long (lib x tail tail-length tail-case expanded nfix-one)
  (let* ((proof (library-library-proof lib))
         (tail-limit (library-lt *proof-one* tail-length)))
    (proof-with-checked-results
        ((positive-tail (b1-revappend-positive-length lib tail-case))
         (expanded-right (b1-revappend-first-at expanded 2))
         (enough (library-library-less-from-difference
                  lib *proof-one* expanded-right positive-tail nil))
         (enough (library-library-transport-argument lib enough expanded 2))
         (value (b1-revappend-butlast-once-selected x enough lib nfix-one))
         (difference-term (b1-revappend-first-at-at value 2 1))
         (difference (b1-revappend-lift-argument lib difference-term expanded 1))
         (difference-right (b1-revappend-first-at difference 2))
         (aligned (library-library-linear-equal lib difference-right tail-length nil))
         (difference (proof-proof-chain proof difference (list aligned)))
         (value (proof-proof-rewrite proof value difference '(1 2 1)))
         (child-integer (library-library-type-of lib tail-length nil))
         (zero-test (b1-logic-bookproof-normalize
                     lib (list *b1-logic-zp* tail-length) (list positive-tail child-integer)
                     (list *b1-logic-zp* *proof-not*) nil nil nil nil))
         (current (b1-revappend-first-at value 2))
         (opened (b1-logic-bookproof-normalize
                  lib current nil (list *b1-revappend-take*)
                  (list (b1-logic-equal-to zero-test)) nil nil nil))
         (value (proof-proof-chain proof value (list opened)))
         (remaining (b1-revappend-first-at-at value 2 2))
         (room (proof-proof-assume proof tail-limit t))
         (have-room (b1-revappend-butlast-once-selected tail room lib nfix-one))
         (room-size (b1-revappend-first-at-at have-room 2 1))
         (remaining-size (proof-term-at remaining 1))
         (align (library-library-linear-equal lib room-size remaining-size nil))
         (have-room (proof-proof-rewrite proof have-room align '(1 2 1)))
         (no-room (proof-proof-assume proof tail-limit nil))
         (too-short (b1-revappend-butlast-once-selected tail no-room lib nfix-one))
         (not-below-one (b1-arithmetic-integer-discrete lib positive-tail child-integer))
         (one-integer (library-library-type-of lib *proof-one* nil))
         (order (b1-arithmetic-integer-compare
                 lib *proof-one* tail-length (list child-integer one-integer)))
         (order (proof-proof-front proof order tail-limit))
         (other (proof-proof-cut proof order no-room))
         (other (proof-proof-front proof other (library-lt tail-length *proof-one*)))
         (other (proof-proof-cut proof other not-below-one))
         (exact (proof-proof-front proof other (proof-eq *proof-one* tail-length)))
         (reversed (proof-proof-symmetric proof exact))
         (exhausted (b1-logic-bookproof-normalize
                     lib remaining nil (list *b1-revappend-take* *b1-logic-zp* *proof-not*)
                     (list (b1-logic-equal-to reversed)) nil nil nil))
         (joined (b1-revappend-chain-symmetric lib too-short nil exhausted))
         (relation (proof-proof-cases proof tail-limit have-room joined))
         (reversed (proof-proof-symmetric proof relation)))
      (proof-proof-rewrite proof value reversed '(1 2 2)))))

(defun b1-revappend-butlast-once (lib x cons-step tail-case)
  (let* ((tail (list *library-cdr* x))
         (length (list *library-len* x))
         (tail-length (list *library-len* tail)))
    (proof-with-checked-results
        ((nfix-one (b1-logic-bookproof-normalize
                    lib (list *b1-revappend-nfix* *proof-one*) nil
                    (list *b1-revappend-nfix* *library-natp* *proof-not*) nil nil nil nil))
         (expanded (b1-revappend-open-list lib length (list cons-step)))
         (first (proof-step-first tail-case)))
      (if (equal first (proof-neg (list *proof-consp* tail)))
          (b1-revappend-butlast-once-short lib x tail-length tail-case expanded nfix-one)
        (b1-revappend-butlast-once-long lib x tail tail-length tail-case expanded nfix-one)))))

(defun b1-revappend-cdr-of-revappend-base (atom lib lhs call rhs)
  (proof-with-checked-results
      ((left (b1-revappend-open-argument lib lhs call (list atom) 1))
       (selected (proof-proof-if-false (library-library-proof lib) rhs)))
    (b1-revappend-chain-symmetric lib left nil selected)))

(defun b1-revappend-cdr-of-revappend-step-right (tail-case lib rhs cons-step x)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((displayed (proof-proof-select proof rhs cons-step))
         (butlast (b1-revappend-butlast-once lib x cons-step tail-case))
         (divided (proof-proof-rewrite proof displayed butlast '(1 2 1)))
         (current (b1-revappend-first-at divided 2))
         (opened (b1-revappend-open-list lib current nil)))
      (proof-proof-chain proof divided (list opened)))))

(defun b1-revappend-cdr-of-revappend-step (cons-step induction lib lhs call rhs x tail-test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left (b1-revappend-open-argument lib lhs call (list cons-step) 1))
         (tail-cons (proof-proof-assume proof tail-test t))
         (tail-atom (proof-proof-assume proof tail-test nil))
         (formula-child (proof-proof-chain proof left (list induction)))
         (child (b1-revappend-first-at formula-child 2))
         (selected (proof-proof-select proof child tail-cons))
         (right (b1-revappend-cdr-of-revappend-step-right tail-cons lib rhs cons-step x))
         (yes (b1-revappend-chain-symmetric lib formula-child (list selected) right))
         (current (b1-revappend-first-at left 2))
         (no-value (b1-logic-bookproof-normalize
                    lib current (list tail-atom)
                    (list *b1-revappend-rev* *b1-logic-endp* *b1-logic-atom* *proof-not*)
                    nil nil nil nil))
         (right (b1-revappend-cdr-of-revappend-step-right tail-atom lib rhs cons-step x))
         (no (b1-revappend-chain-symmetric lib left (list no-value) right)))
      (proof-proof-cases proof tail-test yes no))))

(defun b1-revappend-cdr-of-revappend (lib formula)
  (proof-with-checked-results
      ((formula (proof-list-of-length formula 3))
       (lhs (proof-list-of-length (cadr formula) 2))
       (call (proof-list-of-length (cadr lhs) 3)))
    (let* ((rhs (caddr formula))
           (x (cadr call))
           (tail-test (list *proof-consp* (list *library-cdr* x))))
      (b1-revappend-with-list-induction
       (lib formula x (caddr call) atom cons-step induction)
       (b1-revappend-cdr-of-revappend-step cons-step induction lib lhs call rhs x tail-test)
       (b1-revappend-cdr-of-revappend-base atom lib lhs call rhs)))))
