(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t3-book-merges-merge* (proof-sym "MERGE-TERM-ORDER" "ACL2"))
(defconst *t3-book-merges-sort* (proof-sym "MERGE-SORT-TERM-ORDER" "ACL2"))
(defconst *t3-book-merges-order* (proof-sym "TERM-ORDER" "ACL2"))
(defconst *t3-book-merges-e* (proof-sym "E" "ACL2"))
(defconst *t3-book-merges-merge-count* (proof-sym "HOW-MANY-MERGE-TERM-ORDER" "ACL2"))
(defconst *t3-book-merges-split-count* (proof-sym "HOW-MANY-EVENS-AND-ODDS" "ACL2"))
(defconst *t3-book-merges-occurrences* *t3-book-counterexamples-count*)
(defconst *t3-book-merges-true-listp* *t3-book-lemmas-true-listp*)
(defconst *t3-book-merges-evens* *t3-size-evens*)

(defun t3-book-merges-occurrences (sequence)
  (list *t3-book-merges-occurrences* *t3-book-merges-e* sequence))

(defun t3-book-merges-proper (sequence)
  (list *t3-book-merges-true-listp* sequence))

(defun t3-book-merges-hypothesis (lib formula smaller measure pairs decreases)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((result (proof-subst formula (proof-bindings-table pairs nil)))
         (predicate (proof-ite (list *proof-ordinal-less* smaller measure)
                               result *proof-true*))
         (assumed (proof-proof-assume proof predicate t)))
      (proof-proof-prove-if proof assumed decreases))))

(defun t3-book-merges-proper-args (x y)
  (proof-ite (t3-book-merges-proper x) (t3-book-merges-proper y) *proof-false*))

(defun t3-book-merges-merge-init (lib formula)
  (list :t3-merge lib formula
        (list *proof-consp* *library-x*)
        (list *proof-consp* *library-y*)
        (list *t3-book-merges-order* (list *library-car* *library-x*)
              (list *library-car* *library-y*))
        (list *t3-book-merges-merge* *library-x* *library-y*)
        (library-plus (list *library-len* *library-x*)
                      (list *library-len* *library-y*))
        (list (list (list *library-x* (list *library-cdr* *library-x*)))
              (list (list *library-y* (list *library-cdr* *library-y*))))))

(defun t3-book-merges-merge-lib (merge)
  (nth 1 merge))

(defun t3-book-merges-merge-formula (merge)
  (nth 2 merge))

(defun t3-book-merges-merge-x (merge)
  (nth 3 merge))

(defun t3-book-merges-merge-y (merge)
  (nth 4 merge))

(defun t3-book-merges-merge-decision (merge)
  (nth 5 merge))

(defun t3-book-merges-merge-call (merge)
  (nth 6 merge))

(defun t3-book-merges-merge-measure (merge)
  (nth 7 merge))

(defun t3-book-merges-merge-substitutions (merge)
  (nth 8 merge))

(defun t3-book-merges-merge-remaining (merge branch evidence)
  (let* ((lib (t3-book-merges-merge-lib merge))
         (proof (library-library-proof lib))
         (measure (t3-book-merges-merge-measure merge))
         (substitutions (t3-book-merges-merge-substitutions merge))
         (position (if (< branch 0) (+ branch (len substitutions)) branch)))
    (proof-with-checked-results
        ((pairs (if (< position 0)
                    '(:failure "missing-proof-input" "")
                  (proof-term-at substitutions position)))
         (variable (caar pairs))
         (other (if (equal variable *library-x*) *library-y* *library-x*))
         (facts (t3-logic-evidence-init lib nil evidence nil))
         (size (t3-size-length-tail lib variable facts))
         (smaller (proof-subst measure (proof-bindings-table pairs nil)))
         (numeric (t3-size-shift lib (car size) (list *library-len* other)
                                 (equal branch 1) nil))
         (comparison (library-library-ordinal-comparison lib smaller measure))
         (decrease (proof-proof-transport proof numeric comparison)))
      (t3-book-merges-hypothesis lib (t3-book-merges-merge-formula merge)
                                 smaller measure pairs decrease))))

(defun t3-book-merges-through (lib template equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first equation))
         (left (proof-term-at literal 1))
         (term (proof-subst template (list (cons *proof-result* left))))
         (value (proof-proof-reflexive proof term)))
      (t3-book-spines-replace-value lib value (list equation)))))

(defun t3-book-merges-merge-count-base (branch evidence lib merge counts total)
  (let ((proof (library-library-proof lib))
        (missing (if (equal branch 0) *library-x* *library-y*))
        (retained (if (equal branch 0) *library-y* *library-x*))
        (template (t3-book-merges-occurrences *proof-result*)))
    (proof-with-checked-results
        ((opened (t3-book-spines-shallow lib (t3-book-merges-merge-call merge) evidence))
         (left (t3-book-merges-through lib template opened))
         (zero (t3-book-spines-shallow lib (t3-book-merges-occurrences missing) evidence))
         (same (proof-proof-reflexive proof total))
         (right (t3-book-spines-replace-value lib same (list zero)))
         (right-value (proof-rewritten-term right))
         (count (t3-book-merges-occurrences retained))
         (integer (t3-book-counterexamples-multiplicities-integer-at counts count))
         (identity (library-library-linear-equal lib right-value count (list integer)))
         (right (proof-proof-chain proof right (list identity)))
         (reverse (proof-proof-symmetric proof right)))
      (proof-proof-chain proof left (list reverse)))))

(defun t3-book-merges-merge-count-recursive-leaf
    (matches lib counts total evidence assumed variable other comparison exposed)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((test (proof-proof-assume proof comparison matches))
         (guard (append evidence (list test)))
         (exposed-value (proof-rewritten-term exposed))
         (opened (t3-book-spines-shallow lib exposed-value guard))
         (result (proof-proof-chain proof exposed (list opened)))
         (result (t3-book-spines-replace-value lib result (list assumed)))
         (updated (t3-book-spines-shallow lib (t3-book-merges-occurrences variable) guard))
         (same (proof-proof-reflexive proof total))
         (right (t3-book-spines-replace-value lib same (list updated)))
         (tail-count (t3-book-merges-occurrences (list *library-cdr* variable)))
         (tail-integer (t3-book-counterexamples-multiplicities-integer-at counts tail-count))
         (other-integer (t3-book-counterexamples-multiplicities-integer-at
                         counts (t3-book-merges-occurrences other)))
         (left-value (proof-rewritten-term result))
         (right-value (proof-rewritten-term right))
         (identity (library-library-linear-equal
                    lib left-value right-value (list tail-integer other-integer)))
         (reverse (proof-proof-symmetric proof right)))
      (proof-proof-chain proof result (list identity reverse)))))

(defun t3-book-merges-merge-count-recursive
    (branch evidence assumed lib merge counts total)
  (let* ((proof (library-library-proof lib))
         (variable (if (equal branch 0) *library-x* *library-y*))
         (other (if (equal branch 0) *library-y* *library-x*))
         (comparison (proof-eq *t3-book-merges-e* (list *library-car* variable))))
    (proof-with-checked-results
        ((opened (t3-book-spines-shallow lib (t3-book-merges-merge-call merge) evidence))
         (exposed (t3-book-merges-through
                   lib (t3-book-merges-occurrences *proof-result*) opened))
         (yes (t3-book-merges-merge-count-recursive-leaf
               t lib counts total evidence assumed variable other comparison exposed))
         (no (t3-book-merges-merge-count-recursive-leaf
              nil lib counts total evidence assumed variable other comparison exposed)))
      (proof-proof-cases proof comparison yes no))))

(defun t3-book-merges-sort-proper-merge-base (branch evidence lib merge left right)
  (proof-with-checked-results
      ((equation (t3-book-spines-shallow lib (t3-book-merges-merge-call merge) evidence)))
    (library-library-transport-argument lib (if (equal branch 0) right left)
                                        equation 1)))

(defun t3-book-merges-sort-proper-merge-step-typed (lib step evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((claim (proof-step-first step))
         (equation (t3-book-spines-shallow lib claim evidence))
         (rewritten (proof-proof-rewrite proof step equation '(1))))
      (proof-proof-tidy proof rewritten))))

(defun t3-book-merges-sort-proper-merge-step
    (branch evidence assumed lib merge left right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (if (equal branch 0)
                    (t3-book-merges-sort-proper-merge-step-typed lib left evidence)
                  left))
         (second (if (equal branch 0)
                     right
                   (t3-book-merges-sort-proper-merge-step-typed lib right evidence)))
         (known (t3-book-permutations-conjunction lib first second))
         (accepted (proof-proof-modus-ponens proof assumed known))
         (equation (t3-book-spines-shallow lib (t3-book-merges-merge-call merge) evidence))
         (opened (t3-book-merges-through lib (t3-book-merges-proper *proof-result*) equation))
         (value (proof-rewritten-term opened))
         (shallow (t3-book-spines-shallow lib value evidence))
         (result (proof-proof-chain proof opened (list shallow))))
      (proof-proof-transport proof accepted result))))

(defun t3-book-merges-call-request-p (result)
  (eq (car result) :t3-book-merges-call))

(defmacro t3-book-merges-with-results (bindings result)
  (if (endp bindings)
      result
    (let ((binding (car bindings))
          (name (caar bindings)))
      `(let (,binding)
         (if (or (failure-p ,name) (t3-book-merges-call-request-p ,name))
             ,name
           (t3-book-merges-with-results ,(cdr bindings) ,result))))))

(defun t3-book-merges-reply (lib kind args replies)
  (let ((entry (assoc-equal args replies)))
    (if entry
        (cdr entry)
      (list :t3-book-merges-call kind args lib))))

(defun t3-book-merges-merge-callback (merge kind args replies)
  (let ((lib (t3-book-merges-merge-lib merge))
        (branch (car args))
        (evidence (cadr args)))
    (case (car replies)
      (:count
       (if (eq kind :base)
           (t3-book-merges-merge-count-base
            branch evidence lib merge (cadr replies) (caddr replies))
         (t3-book-merges-merge-count-recursive
          branch evidence (caddr args) lib merge (cadr replies) (caddr replies))))
      (:proper
       (if (eq kind :base)
           (t3-book-merges-sort-proper-merge-base
            branch evidence lib merge (cadr replies) (caddr replies))
         (t3-book-merges-sort-proper-merge-step
          branch evidence (caddr args) lib merge (cadr replies) (caddr replies))))
      (otherwise (t3-book-merges-reply lib kind args replies)))))

(defun t3-book-merges-merge-prove (merge base recursive implication-goal)
  (let* ((lib (t3-book-merges-merge-lib merge))
         (proof (library-library-proof lib))
         (formula (t3-book-merges-merge-formula merge))
         (x-test (t3-book-merges-merge-x merge))
         (y-test (t3-book-merges-merge-y merge))
         (decision (t3-book-merges-merge-decision merge))
         (measure (t3-book-merges-merge-measure merge)))
    (t3-book-merges-with-results
        ((x (proof-proof-assume proof x-test t))
         (y (proof-proof-assume proof y-test t))
         (no-x (proof-proof-assume proof x-test nil))
         (no-y (proof-proof-assume proof y-test nil))
         (evidence (list x y))
         (left (proof-proof-assume proof decision t))
         (right (proof-proof-assume proof decision nil))
         (ih (t3-book-merges-merge-remaining merge 0 evidence))
         (first (t3-book-merges-merge-callback merge :recursive
                                              (list 0 (list x y left) ih) recursive))
         (ih (t3-book-merges-merge-remaining merge 1 evidence))
         (second (t3-book-merges-merge-callback merge :recursive
                                               (list 1 (list x y right) ih) recursive))
         (step (proof-proof-cases proof decision first second))
         (base-y (t3-book-merges-merge-callback merge :base (list 1 (list x no-y)) base))
         (step (proof-proof-cases proof y-test step base-y))
         (base-x (t3-book-merges-merge-callback merge :base (list 0 (list no-x)) base))
         (case-proof (proof-proof-cases proof x-test step base-x))
         (case-proof (if implication-goal
                         (t3-book-lemmas-implication lib formula case-proof)
                       case-proof))
         (natural (t3-logic-libraryproofs-natural lib measure))
         (ordinal (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural))))
      (proof-proof-induct proof ordinal case-proof formula measure
                          (t3-book-merges-merge-substitutions merge)))))

(defun t3-book-merges-merge-count (lib name formula)
  (let ((merge (t3-book-merges-merge-init lib formula))
        (total (library-plus (t3-book-merges-occurrences *library-x*)
                             (t3-book-merges-occurrences *library-y*))))
    (proof-with-checked-results
        ((counts (t3-book-counterexamples-multiplicities-init lib))
         (callbacks (list :count counts total))
         (step (t3-book-merges-merge-prove merge callbacks callbacks nil))
         (entry (proof-proof-entry "theorem" name (list name) (list step))))
      (cons entry lib))))

(defun t3-book-merges-split-count-step
    (matches lib has-list head evens left right a b integers induction)
  (let* ((proof (library-library-proof lib))
         (template (t3-book-merges-occurrences *proof-result*)))
    (proof-with-checked-results
        ((match (proof-proof-assume proof head matches))
         (evidence (list has-list match))
         (equation (t3-book-spines-shallow lib evens evidence))
         (opened (t3-book-merges-through lib template equation))
         (term (proof-rewritten-term opened))
         (equation (t3-book-spines-shallow lib term evidence))
         (opened (proof-proof-chain proof opened (list equation)))
         (same (proof-proof-reflexive proof left))
         (result (t3-book-spines-replace-value lib same (list opened)))
         (aligned (if matches
                      (library-plus *proof-one* (library-plus b a))
                    (library-plus b a)))
         (term (proof-rewritten-term result))
         (reorder (library-library-linear-equal lib term aligned integers))
         (result (proof-proof-chain proof result (list reorder)))
         (result (t3-book-spines-replace-value lib result (list induction)))
         (right (t3-book-spines-shallow lib right evidence))
         (reverse (proof-proof-symmetric proof right)))
      (proof-proof-chain proof result (list reverse)))))

(defun t3-book-merges-split-count (lib name formula)
  (let* ((proof (library-library-proof lib))
         (cons-test (list *proof-consp* *library-x*))
         (tail (list *library-cdr* *library-x*))
         (twice (list *library-cdr* tail))
         (evens (list *t3-book-merges-evens* *library-x*))
         (rest (list *t3-book-merges-evens* tail))
         (pairs (list (list *library-x* tail)))
         (smaller (list *library-count* tail))
         (measure (list *library-count* *library-x*)))
    (proof-with-checked-results
        ((counts (t3-book-counterexamples-multiplicities-init lib))
         (statement (proof-term-at formula 2))
         (parts (if (integerp statement)
                    (proof-term-at statement 1)
                  (proof-list-of-length (cdr statement) 2)))
         (left (car parts))
         (right (cadr parts))
         (decrease (library-library-builtin lib 3 *library-x*))
         (induction (t3-book-merges-hypothesis lib statement smaller measure pairs decrease))
         (atom (proof-proof-assume proof cons-test nil))
         (completed (library-library-axiom lib "COMPLETION-OF-CDR" (list *library-x*)))
         (body (proof-rewritten-term completed))
         (selected (proof-proof-select proof body atom))
         (cdr-step (proof-proof-chain proof completed (list selected)))
         (empty-evens (t3-book-spines-shallow
                       lib (list *t3-book-merges-evens* *proof-false*) nil))
         (empty-count (t3-book-spines-shallow
                       lib (t3-book-merges-occurrences *proof-false*) nil))
         (same (proof-proof-reflexive proof left))
         (opened (t3-book-spines-shallow lib evens (list atom)))
         (base (t3-book-spines-replace-value
                lib same (list opened cdr-step empty-evens empty-count)))
         (term (proof-rewritten-term base))
         (constant (t3-logic-libraryproofs-constant lib term))
         (right-atom (t3-book-spines-shallow lib right (list atom)))
         (reversed (proof-proof-symmetric proof right-atom))
         (base (proof-proof-chain proof base (list constant reversed)))
         (has-list (proof-proof-assume proof cons-test t))
         (head (proof-eq *t3-book-merges-e* (list *library-car* *library-x*)))
         (a (t3-book-merges-occurrences (list *t3-book-merges-evens* twice)))
         (b (t3-book-merges-occurrences rest))
         (a-integer (t3-book-counterexamples-multiplicities-integer-at counts a))
         (b-integer (t3-book-counterexamples-multiplicities-integer-at counts b))
         (integers (list a-integer b-integer))
         (yes (t3-book-merges-split-count-step
               t lib has-list head evens left right a b integers induction))
         (no (t3-book-merges-split-count-step
              nil lib has-list head evens left right a b integers induction))
         (step (proof-proof-cases proof head yes no))
         (cases (proof-proof-cases proof cons-test step base))
         (ordinal (library-library-builtin lib 1 *library-x*))
         (theorem (proof-proof-induct proof ordinal cases statement measure (list pairs)))
         (result (t3-book-lemmas-implication lib formula theorem))
         (entry (proof-proof-entry "theorem" name (list name) (list result))))
      (cons entry lib))))

(defun t3-book-merges-sort-induction-premise (lib formula measure pairs evidence)
  (proof-with-checked-results
      ((smaller (proof-subst measure (proof-bindings-table pairs nil)))
       (bound (t3-size-alternating-length lib smaller measure evidence))
       (lib (cadr bound))
       (proof (library-library-proof lib))
       (comparison (library-library-ordinal-comparison lib smaller measure))
       (decrease (proof-proof-transport proof (car bound) comparison))
       (hypothesis (t3-book-merges-hypothesis lib formula smaller measure pairs decrease)))
    (list hypothesis lib (caddr bound))))

(defun t3-book-merges-sort-count-base (equation lib)
  (t3-book-merges-through lib (t3-book-merges-occurrences *proof-result*) equation))

(defun t3-book-merges-sort-count-recursive (equation parent evens odds lib)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (proof-rewritten-term equation))
         (parts (proof-list-of-length value 3))
         (merged (proof-proof-fact
                  proof *t3-book-merges-merge-count*
                  (list (list *library-x* (cadr parts)) (list *library-y* (caddr parts)))))
         (through (t3-book-merges-through
                   lib (t3-book-merges-occurrences *proof-result*) equation))
         (result (proof-proof-chain proof through (list merged)))
         (odd-definition (proof-proof-unfold proof (list *t3-size-odds* *library-x*)))
         (result (t3-book-spines-replace-value lib result (list evens odds odd-definition)))
         (split (proof-proof-fact proof *t3-book-merges-split-count* nil))
         (count (proof-proof-modus-ponens proof split parent)))
      (proof-proof-chain proof result (list count)))))

(defun t3-book-merges-sort-proper-base (equation lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((antecedent (proof-term-at formula 1))
         (guard (proof-proof-assume proof antecedent t)))
      (library-library-transport-argument lib guard equation 1))))

(defun t3-book-merges-sort-proper-recursive
    (equation parent evens odds lib evens-proper odds-proper)
  (declare (ignore parent))
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((first (proof-proof-modus-ponens proof evens evens-proper))
         (second (proof-proof-modus-ponens proof odds odds-proper))
         (first-type (proof-step-first first))
         (first-argument (proof-term-at first-type 1))
         (second-type (proof-step-first second))
         (second-argument (proof-term-at second-type 1))
         (known (proof-proof-fact
                 proof (proof-sym "SELF-T3-MERGE-PROPER" "ACL2")
                 (list (list *library-x* first-argument) (list *library-y* second-argument))))
         (conjunction (t3-book-permutations-conjunction lib first second))
         (result (proof-proof-modus-ponens proof known conjunction)))
      (library-library-transport-argument lib result equation 1))))

(defun t3-book-merges-sort-callback (lib formula kind args replies)
  (case (car replies)
    (:count
     (if (eq kind :base)
         (t3-book-merges-sort-count-base (car args) lib)
       (t3-book-merges-sort-count-recursive
        (car args) (cadr args) (caddr args) (cadddr args) lib)))
    (:proper
     (if (eq kind :base)
         (t3-book-merges-sort-proper-base (car args) lib formula)
       (t3-book-merges-sort-proper-recursive
        (car args) (cadr args) (caddr args) (cadddr args)
        lib (cadr replies) (caddr replies))))
    (otherwise (t3-book-merges-reply lib kind args replies))))

(defun t3-book-merges-sort-induction (lib formula base recursive implication-goal)
  (let* ((proof (library-library-proof lib))
         (tail-cons (list *proof-consp* (list *library-cdr* *library-x*)))
         (parent-cons (list *proof-consp* *library-x*))
         (measure (list *library-len* *library-x*))
         (evens (list (list *library-x* (list *t3-book-merges-evens* *library-x*))))
         (odds (list (list *library-x* (list *t3-size-odds* *library-x*))))
         (sort-call (list *t3-book-merges-sort* *library-x*)))
    (t3-book-merges-with-results
        ((present (proof-proof-assume proof tail-cons t))
         (complete (library-library-axiom lib "COMPLETION-OF-CDR" (list *library-x*)))
         (body (proof-rewritten-term complete))
         (false-branch (proof-proof-if-false proof body))
         (parent (proof-proof-chain proof complete (list false-branch)))
         (rewritten (proof-proof-rewrite proof present parent '(1 1)))
         (contradicted (t3-logic-libraryproofs-simplify-first lib rewritten nil nil))
         (original (proof-proof-front proof contradicted parent-cons))
         (evidence (t3-logic-evidence-init lib nil (list present original) nil))
         (even-premise (t3-book-merges-sort-induction-premise lib formula measure evens evidence))
         (odd-premise (t3-book-merges-sort-induction-premise
                       (cadr even-premise) formula measure odds (caddr even-premise)))
         (lib (cadr odd-premise))
         (proof (library-library-proof lib))
         (equation (t3-book-spines-shallow lib sort-call (list present)))
         (given (t3-logic-evidence-require (caddr odd-premise) parent-cons))
         (step (t3-book-merges-sort-callback
                lib formula :recursive
                (list equation (car given) (car even-premise) (car odd-premise)) recursive))
         (absent (proof-proof-assume proof tail-cons nil))
         (unchanged (t3-book-spines-shallow lib sort-call (list absent)))
         (base-step (t3-book-merges-sort-callback lib formula :base (list unchanged) base))
         (case-proof (proof-proof-cases proof tail-cons step base-step))
         (case-proof (if implication-goal
                         (t3-book-lemmas-implication lib formula case-proof)
                       case-proof))
         (natural (t3-logic-libraryproofs-natural lib measure))
         (ordinal (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural)))
         (result (proof-proof-induct proof ordinal case-proof formula measure (list evens odds))))
      (cons result lib))))

(defun t3-book-merges-sort-count (lib name formula)
  (proof-with-checked-results
      ((result (t3-book-merges-sort-induction lib formula '(:count) '(:count) nil))
       (entry (proof-proof-entry "theorem" name (list name) (list (car result)))))
    (cons entry (cdr result))))

(defun t3-book-merges-proper-evens (lib)
  (let* ((proof (library-library-proof lib))
         (call (list *t3-book-merges-evens* *library-x*))
         (formula (t3-book-merges-proper call))
         (cons-test (list *proof-consp* *library-x*))
         (child (list *library-cdr* (list *library-cdr* *library-x*)))
         (pairs (list (list *library-x* child)))
         (smaller (list *library-count* child))
         (measure (list *library-count* *library-x*))
         (template (t3-book-merges-proper *proof-result*)))
    (proof-with-checked-results
        ((present (proof-proof-assume proof cons-test t))
         (absent (proof-proof-assume proof cons-test nil))
         (evidence (t3-logic-evidence-init lib nil (list present) nil))
         (decreases (t3-size-count-descent lib smaller measure evidence))
         (assumed (t3-book-merges-hypothesis lib formula smaller measure pairs (car decreases)))
         (equation (t3-book-spines-shallow lib call (list present)))
         (opened (t3-book-merges-through lib template equation))
         (value (proof-rewritten-term opened))
         (equation (t3-book-spines-shallow lib value (list present)))
         (result (proof-proof-chain proof opened (list equation)))
         (step (proof-proof-transport proof assumed result))
         (equation (t3-book-spines-shallow lib call (list absent)))
         (empty (t3-book-merges-through lib template equation))
         (nil-proper (t3-book-spines-shallow lib (t3-book-merges-proper *proof-false*) nil))
         (nil-proper (proof-proof-true-from-eq proof nil-proper))
         (base (proof-proof-transport proof nil-proper empty))
         (ordinal (library-library-builtin lib 1 *library-x*))
         (cases (proof-proof-cases proof cons-test step base)))
      (proof-proof-induct proof ordinal cases formula measure (list pairs)))))

(defun t3-book-merges-sort-proper (lib name formula)
  (let* ((proof (library-library-proof lib))
         (guard (t3-book-merges-proper-args *library-x* *library-y*))
         (goal (t3-book-merges-proper (list *t3-book-merges-merge*
                                           *library-x* *library-y*)))
         (merge-formula (list *library-implies* guard goal))
         (merge (t3-book-merges-merge-init lib merge-formula)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof guard t))
         (parts (proof-proof-conjunct proof assumed))
         (callbacks (list :proper (car parts) (cadr parts)))
         (merge-proof (t3-book-merges-merge-prove merge callbacks callbacks t))
         (lib (library-library-lemma lib "T3-MERGE-PROPER" merge-formula merge-proof nil))
         (proof (library-library-proof lib))
         (evens-proper (t3-book-merges-proper-evens lib))
         (shifted (proof-proof-instantiate
                   proof evens-proper (list (list *library-x* (list *library-cdr* *library-x*)))))
         (odds (proof-proof-unfold proof (list *t3-size-odds* *library-x*)))
         (odds-proper (library-library-transport-argument lib shifted odds 1))
         (callbacks (list :proper evens-proper odds-proper))
         (result (t3-book-merges-sort-induction lib formula callbacks callbacks t))
         (entry (proof-proof-entry "theorem" name (list name) (list (car result)))))
      (cons entry (cdr result)))))
