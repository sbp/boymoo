(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *t3-size-make-ord* (proof-sym "MAKE-ORD" "ACL2"))
(defconst *t3-size-o-finp* (proof-sym "O-FINP" "ACL2"))
(defconst *t3-size-o-first-expt* (proof-sym "O-FIRST-EXPT" "ACL2"))
(defconst *t3-size-o-first-coeff* (proof-sym "O-FIRST-COEFF" "ACL2"))
(defconst *t3-size-o-rst* (proof-sym "O-RST" "ACL2"))
(defconst *t3-size-posp* (proof-sym "POSP" "ACL2"))
(defconst *t3-size-evens* (proof-sym "EVENS" "ACL2"))
(defconst *t3-size-odds* (proof-sym "ODDS" "ACL2"))
(defconst *t3-size-ordinal-operations*
  (list *t3-size-make-ord* *t3-size-o-finp* *t3-size-o-first-expt*
        *t3-size-o-first-coeff* *t3-size-o-rst* *t3-logic-atom*
        *library-natp* *t3-size-posp* (proof-cl "=") (proof-cl "EQL")
        (proof-cl "EQ") *proof-not*))
(defconst *t3-size-w* (proof-sym "W" "ACL2"))

(defun t3-size-endpoints (proof)
  (proof-with-checked-results ((literal (proof-step-first proof)))
    (if (proof-is-call literal *proof-less*)
        (cdr literal)
      (proof-with-checked-results ((negated (proof-term-at literal 1)))
        (cond ((integerp negated)
               '(:failure "failure" ""))
              ((stringp negated)
               (coerce (reverse (cdr (coerce negated 'list))) 'string))
              (t (reverse (cdr negated))))))))

(defun t3-size-chain (lib lower upper integers)
  (proof-with-checked-results
   ((lower-ends (t3-size-endpoints lower))
    (lower-ends (proof-list-of-length lower-ends 2))
    (upper-ends (t3-size-endpoints upper))
    (upper-ends (proof-list-of-length upper-ends 2)))
   (let ((a (car lower-ends))
         (b (cadr lower-ends))
         (middle (car upper-ends))
         (c (cadr upper-ends)))
     (if (not (equal b middle))
         '(:failure "proof-mismatch" "")
       (let* ((lower-strict (proof-is-call (proof-step-first lower) *proof-less*))
              (upper-strict (proof-is-call (proof-step-first upper) *proof-less*))
              (name (cond (lower-strict (if upper-strict "LESS-TRANSITIVE" "LESS-THEN-WEAK"))
                          (upper-strict "WEAK-THEN-LESS")
                          (t "T3-WEAK-TRANSITIVE"))))
         (proof-with-checked-results
          ((a-type (t3-logic-libraryproofs-type-of lib a integers))
           (b-type (t3-logic-libraryproofs-type-of lib b integers))
           (c-type (t3-logic-libraryproofs-type-of lib c integers)))
          (library-library-cite lib name (list a b c)
                                (list a-type b-type c-type lower upper))))))))

(defun t3-size-shift (lib proof offset prefix integers)
  (let ((rules (library-library-proof lib)))
    (proof-with-checked-results
     ((endpoints (t3-size-endpoints proof))
      (endpoints (proof-list-of-length endpoints 2))
      (literal (proof-step-first proof)))
     (let* ((a (car endpoints))
            (b (cadr endpoints))
            (strict (proof-is-call literal *proof-less*))
            (name (if strict "LESS-SHIFT" "T3-WEAK-SHIFT"))
            (where (if strict '(1) '(1 1))))
       (proof-with-checked-results
        ((a-type (t3-logic-libraryproofs-type-of lib a integers))
         (b-type (t3-logic-libraryproofs-type-of lib b integers))
         (offset-type (t3-logic-libraryproofs-type-of lib offset integers))
         (result (library-library-cite lib name (list a b offset)
                                       (list a-type b-type offset-type proof)))
         (result
          (if prefix
              (proof-with-checked-results
               ((first (library-library-axiom lib "COMMUTATIVITY-OF-+"
                                              (list (if strict a b) offset)))
                (changed (proof-proof-rewrite rules result first (append where '(1))))
                (second (library-library-axiom lib "COMMUTATIVITY-OF-+"
                                               (list (if strict b a) offset))))
               (proof-proof-rewrite rules changed second (append where '(2))))
            result)))
        (proof-proof-tidy rules result))))))

(defun t3-size-sum-at-least (lib included other-nonnegative integers prefix)
  (let ((proof (library-library-proof lib))
        (identity (if prefix "ADD-ZERO-RIGHT" "ADD-ZERO-LEFT")))
    (proof-with-checked-results
     ((expanded (t3-size-shift lib other-nonnegative included prefix integers))
      (included-type (t3-logic-libraryproofs-type-of lib included integers))
      (same (library-library-cite lib identity (list included) (list included-type)))
      (result (proof-proof-rewrite proof expanded same '(1 1 2))))
     (proof-proof-tidy proof result))))

(defun t3-size-selector-path (child parent)
  (declare (xargs :measure (acl2-count child)))
  (cond
   ((and (proof-compound child) (endp child))
    '(:failure "missing-proof-input" ""))
   ((equal child parent) nil)
   ((and (consp child) (proof-compound child)
         (member-equal (car child) (list *library-car* *library-cdr*)))
    (if (endp (cdr child))
        '(:failure "missing-proof-input" "")
      (proof-with-checked-results ((rest (t3-size-selector-path (cadr child) parent)))
        (if (eq rest :none) :none (cons child rest)))))
   (t :none)))

(defun t3-size-ordinal-comparison (lib a b)
  (proof-with-checked-results
   ((a-type (t3-logic-libraryproofs-type-of lib a nil))
    (b-type (t3-logic-libraryproofs-type-of lib b nil)))
   (library-library-cite lib "FINITE-ORDER" (list a b) (list a-type b-type))))

(defun t3-size-builtin-test (test evidence)
  (proof-with-checked-results
   ((positive (if (proof-is-call test *proof-not*)
                  (proof-with-checked-results ((term (proof-term-at test 1)))
                    (t3-logic-evidence-find evidence term))
                (cons nil evidence))))
   (if (car positive)
       positive
     (t3-logic-evidence-find (cdr positive) (proof-neg test)))))

(defun t3-size-builtin-discharge (test proof clause result)
  (if (member-equal test clause)
      result
    (proof-with-checked-results ((known (t3-size-builtin-test test (cdr result))))
      (if (not (car known))
          known
        (proof-with-checked-results ((step (proof-proof-discharge proof (car result) (car known))))
          (cons step (cdr known)))))))

(defun t3-size-builtin-tests (tests proof clause result)
  (declare (xargs :measure (acl2-count tests)))
  (if (or (endp tests) (failure-p result) (not (car result)))
      result
    (t3-size-builtin-tests (cdr tests) proof clause
                           (t3-size-builtin-discharge (car tests) proof clause result))))

(defun t3-size-builtin-candidates (candidates proof clause result)
  (declare (xargs :measure (acl2-count candidates)))
  (if (or (endp candidates) (failure-p result) (car result))
      result
    (let ((candidate (car candidates)))
      (t3-size-builtin-candidates
       (cdr candidates) proof clause
       (t3-size-builtin-tests (cdr (proof-step-clause candidate)) proof clause
                              (cons candidate (cdr result)))))))

(defun t3-size-direct-builtin (lib clause evidence)
  (if (endp clause)
      '(:failure "missing-proof-input" "")
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
       ((matches (descent-builtin-matches (seq-range 1 24 1) proof clause (car (last clause)) nil)))
       (if (or (car matches) (not evidence))
           (cons (car matches) evidence)
         (t3-size-builtin-candidates (cdr matches) proof clause (cons nil evidence)))))))

(defun t3-size-count-edge (term lib result)
  (let* ((arg (cadr term))
         (lower (list *library-count* term))
         (upper (list *library-count* arg))
         (proof (library-library-proof lib)))
    (proof-with-checked-results
     ((direct (t3-size-direct-builtin lib (list (list *proof-ordinal-less* lower upper))
                                     (cdr result)))
      (bound
       (if (car direct)
           (proof-with-checked-results ((order (t3-size-ordinal-comparison lib lower upper)))
             (proof-proof-rewrite proof (car direct) order '(1)))
         (library-library-cite lib (if (equal (car term) *library-car*)
                                       "COUNT-CAR-WEAK" "COUNT-CDR-WEAK")
                               (list arg) nil)))
      (step (if (car result) (t3-size-chain lib (car result) bound nil) bound)))
     (cons step (cdr direct)))))

(defun t3-size-count-edges (edges lib result)
  (declare (xargs :measure (acl2-count edges)))
  (if (or (endp edges) (failure-p result))
      result
    (t3-size-count-edges (cdr edges) lib (t3-size-count-edge (car edges) lib result))))

(defun t3-size-count-bound (lib child parent evidence)
  (proof-with-checked-results ((edges (t3-size-selector-path child parent)))
    (cond
     ((eq edges :none) '(:failure "unsupported" ""))
     ((endp edges)
      (let ((size (list *library-count* child)))
        (proof-with-checked-results
         ((typed (t3-logic-libraryproofs-type-of lib size nil))
          (step (library-library-cite lib "WEAK-REFLEXIVE" (list size) (list typed))))
         (cons step evidence))))
     (t (t3-size-count-edges edges lib (cons nil evidence))))))

(defun t3-size-count-descent-along-path (lib argument smaller larger evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((parent (proof-term-at larger 1)))
      (if (equal argument *proof-false*)
          (let* ((tail (list *library-cdr* parent))
                 (middle (list *library-count* tail)))
            (proof-with-checked-results
             ((strict (t3-size-count-bound lib tail parent evidence))
              (literal (proof-step-first (car strict))))
             (if (not (proof-is-call literal *proof-less*))
                 '(:failure "unsupported" "")
               (proof-with-checked-results
                ((natural (t3-logic-libraryproofs-natural lib middle))
                 (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE"
                                                    (list middle) (list natural)))
                 (positive-size (t3-size-chain lib nonnegative (car strict) nil))
                 (simplified (t3-logic-libraryproofs-simplify lib smaller nil (list *library-count*)))
                 (result (library-library-transport-argument lib positive-size simplified 1))
                 (order (t3-size-ordinal-comparison lib smaller larger))
                 (step (proof-proof-transport proof result order)))
                (cons step (cdr strict))))))
        (proof-with-checked-results
         ((result (t3-size-count-bound lib argument parent evidence))
          (literal (proof-step-first (car result))))
         (if (not (proof-is-call literal *proof-less*))
             '(:failure "unsupported" "")
           (proof-with-checked-results
            ((order (t3-size-ordinal-comparison lib smaller larger))
             (step (proof-proof-transport proof (car result) order)))
            (cons step (cdr result)))))))))

(defund t3-size-count-descent-plan (lib smaller)
  (proof-with-checked-results
   ((argument (proof-term-at smaller 1))
    (head (if (proof-compound argument) (proof-term-at argument 0) :atom)))
   (cond
    ((or (proof-compound head) (equal head *proof-if*) (member-equal head *t3-logic-wrappers*))
     (list :by-value argument))
    ((proof-is-call argument (proof-sym "HARD-ERROR" "ACL2"))
     (proof-with-checked-results ((opened (proof-proof-unfold (library-library-proof lib) argument)))
       (list :hard-error opened)))
    (t (list :selector argument)))))

(defund t3-size-count-descent-value-plan (proof value)
  (proof-with-checked-results
   ((head (if (proof-compound value) (proof-term-at value 0) :atom)))
   (cond
    ((or (member-equal head *t3-logic-wrappers*) (proof-compound head))
     (proof-with-checked-results
      ((opened (if (proof-compound head)
                   (proof-proof-beta proof value)
                 (proof-proof-unfold proof value))))
      (list :open opened)))
    ((proof-is-call value *proof-if*)
     (proof-with-checked-results ((parts (proof-list-of-length (cdr value) 3)))
       (cons :conditional parts)))
    (t '(:leaf)))))

(defun t3-size-count-descent-join (proof value template test yes no)
  (proof-with-checked-results
   ((take-yes (proof-proof-if-true proof value))
    (take-yes (proof-proof-symmetric proof take-yes))
    (yes (proof-proof-rewrite-result proof yes take-yes template *proof-result*))
    (take-no (proof-proof-if-false proof value))
    (take-no (proof-proof-symmetric proof take-no))
    (no (proof-proof-rewrite-result proof no take-no template *proof-result*)))
   (proof-proof-cases proof test yes no)))

(mutual-recursion
 (defun t3-size-count-descent-run (n lib smaller larger evidence)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "t3-size-count-descent-run"))
    ((failure-p evidence) evidence)
    (t
     (let* ((plan (t3-size-count-descent-plan lib smaller))
            (proof (library-library-proof lib))
            (goal (list *proof-ordinal-less* (list *library-count* *proof-result*) larger)))
       (case (car plan)
         (:by-value
          (proof-with-checked-results
           ((step (t3-size-count-descent-by-value (1- n) (cadr plan) goal nil lib larger evidence)))
           (cons step evidence)))
         (:hard-error
          (let* ((opened (cadr plan))
                 (zero (list *library-count* (caddr (proof-step-first opened)))))
            (proof-with-checked-results
             ((result (t3-size-count-descent-run (1- n) lib zero larger evidence))
              (reverse (proof-proof-symmetric proof opened))
              (step (proof-proof-rewrite-result proof (car result) reverse goal *proof-result*)))
             (cons step (cdr result)))))
         (:selector
          (t3-size-count-descent-along-path lib (cadr plan) smaller larger evidence))
         (otherwise plan))))))

 (defun t3-size-count-descent-by-value (n value template tests lib larger evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "t3-size-count-descent-by-value")
     (let* ((proof (library-library-proof lib))
            (plan (t3-size-count-descent-value-plan proof value)))
       (case (car plan)
         (:open
          (let ((opened (cadr plan)))
            (proof-with-checked-results
             ((step (t3-size-count-descent-by-value
                     (1- n) (caddr (proof-step-first opened)) template tests lib larger evidence))
              (reverse (proof-proof-symmetric proof opened)))
             (proof-proof-rewrite-result proof step reverse template *proof-result*))))
         (:conditional
          (let ((test (cadr plan)))
            (proof-with-checked-results
             ((yes (t3-size-count-descent-by-value
                    (1- n) (caddr plan) template (append tests (list (list test t)))
                    lib larger evidence))
              (no (t3-size-count-descent-by-value
                   (1- n) (cadddr plan) template (append tests (list (list test nil)))
                   lib larger evidence)))
             (t3-size-count-descent-join proof value template test yes no))))
         (:leaf
          (proof-with-checked-results
           ((step (t3-size-count-descent-branch (1- n) value tests lib larger evidence))
            (literal (proof-step-first step))
            (expected (proof-subst template (list (cons *proof-result* value)))))
           (if (equal literal expected) step '(:failure "proof-mismatch" ""))))
         (otherwise plan)))))

 (defun t3-size-count-descent-branch (n value tests lib larger evidence)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "t3-size-count-descent-branch")
     (proof-with-checked-results
      ((result
        (t3-size-count-descent-run
         (1- n) lib (list *library-count* value) larger
         (t3-logic-evidence-init
          lib (append (t3-logic-evidence-tests evidence) tests)
          (table-values (t3-logic-evidence-facts evidence))
          (t3-logic-evidence-definitions evidence)))))
      (car result)))))

(defun t3-size-count-descent (lib smaller larger evidence)
  (t3-size-count-descent-run 1000000 lib smaller larger evidence))

(defun t3-size-phase-count (measure)
  (proof-with-checked-results
   ((doubled (if (proof-is-call measure *proof-plus*)
                 (proof-with-checked-results ((first (proof-term-at measure 1)))
                   (if (equal first *proof-one*) (proof-term-at measure 2) measure))
               measure)))
   (if (proof-is-call doubled *proof-times*)
       (proof-with-checked-results ((first (proof-term-at doubled 1)))
         (if (equal first *t3-arithmetic-two*)
             (proof-with-checked-results ((second (proof-term-at doubled 2)))
               (if (proof-is-call second *library-count*) second nil))
           nil))
     nil)))

(defun t3-size-doubled-rank (base phase)
  (let ((product (list *proof-times* *t3-arithmetic-two* base)))
    (if phase (library-plus *proof-one* product) product)))

(defun t3-size-phase-lemma (lower upper)
  (concatenate 'string "T3-DOUBLE-PHASE-" (if lower "1" "0") (if upper "1" "0")))

(defun t3-size-ordinal-doubled (lib measure)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((matched (t3-size-phase-count measure))
      (doubled (if (proof-is-call measure *proof-plus*) (proof-term-at measure 2) measure))
      (doubled-eq
       (if matched
           (proof-with-checked-results ((typed (t3-logic-libraryproofs-type-of lib matched nil)))
             (library-library-cite lib "T3-DOUBLE" (list matched) (list typed)))
         '(:failure "failure" "")))
      (doubled-eq (if (equal measure doubled)
                      doubled-eq
                    (proof-with-checked-results ((same (proof-proof-reflexive proof measure)))
                      (proof-proof-rewrite proof same doubled-eq '(1 2 2)))))
      (natural (t3-logic-libraryproofs-natural lib (caddr (proof-step-first doubled-eq))))
      (natural (library-library-transport-argument lib natural doubled-eq 1)))
     (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural)))))

(defun t3-size-doubled-descent-compare (lib smaller larger evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((order (t3-arithmetic-integer-comparison lib smaller larger evidence))
      (ordinal (t3-size-ordinal-comparison lib smaller larger))
      (step (proof-proof-transport proof (car order) ordinal)))
     (list step lib (cdr order)))))

(defun t3-size-doubled-descent-from-bound (lib smaller larger evidence size)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((literal (proof-step-first size)))
      (if (proof-is-call literal *proof-less*)
          (proof-with-checked-results
           ((after (t3-size-phase-count smaller))
            (before (t3-size-phase-count larger))
            (name (t3-size-phase-lemma (proof-is-call smaller *proof-plus*)
                                      (proof-is-call larger *proof-plus*)))
            (after-type (t3-logic-libraryproofs-type-of lib after nil))
            (before-type (t3-logic-libraryproofs-type-of lib before nil))
            (order (library-library-cite lib name (list after before)
                                         (list after-type before-type size)))
            (ordinal (t3-size-ordinal-comparison lib smaller larger))
            (step (proof-proof-transport proof order ordinal)))
           (list step lib evidence))
        (t3-size-doubled-descent-compare
         lib smaller larger
         (t3-logic-evidence-with-facts
          evidence (table-put (t3-logic-evidence-facts evidence) literal size)))))))

(defun t3-size-doubled-descent (lib smaller larger evidence transformed)
  (proof-with-checked-results
   ((before (t3-size-phase-count larger))
    (after (t3-size-phase-count smaller)))
   (cond
    ((not (and before after)) '(:failure "unsupported" ""))
    ((equal before after) (t3-size-doubled-descent-compare lib smaller larger evidence))
    (t
     (proof-with-checked-results
      ((child (proof-term-at after 1))
       (parent (proof-term-at before 1)))
      (let ((bound (t3-size-count-bound lib child parent evidence)))
        (cond
         ((not (failure-p bound))
          (t3-size-doubled-descent-from-bound lib smaller larger (cdr bound) (car bound)))
         ((and transformed (equal (cadr bound) "unsupported"))
          (list :t3-size-transformed child parent evidence))
         (t bound))))))))

(defun t3-size-len-cons (lib car-term cdr-term)
  (let* ((term (list *library-len* (list *proof-cons* car-term cdr-term)))
         (rules (library-library-proof lib)))
    (proof-with-checked-results
     ((equation (proof-proof-unfold rules term))
      (cons-proof (proof-proof-fact rules "consp-cons"
                                    (list (list *library-x* car-term)
                                          (list *library-y* cdr-term))))
      (selection (proof-proof-select rules (caddr (proof-step-first equation)) cons-proof))
      (opened (proof-proof-chain rules equation (list selection)))
      (normal (t3-logic-libraryproofs-normalize lib (caddr (proof-step-first opened)) nil nil)))
     (proof-proof-chain rules opened (list normal)))))

(defun t3-size-length-tail (lib term evidence)
  (proof-with-checked-results
   ((needed (t3-logic-evidence-require evidence (list *t3-logic-consp* term)))
    (step (library-library-cite lib "LEN-CDR-LESS" (list term) (list (car needed)))))
   (cons step (cdr needed))))

(defun t3-size-length-weak (lib)
  (let* ((proof (library-library-proof lib))
         (parent (list *library-len* *library-x*))
         (child (list *library-len* (list *library-cdr* *library-x*)))
         (cons-test (list *t3-logic-consp* *library-x*)))
    (proof-with-checked-results
     ((evidence (t3-logic-evidence-init lib (list (list cons-test t)) nil nil))
      (strict (t3-size-length-tail lib *library-x* evidence))
      (smaller (library-library-as-weak lib (car strict)))
      (atom-proof (proof-proof-assume proof cons-test nil))
      (parent-zero (t3-logic-libraryproofs-simplify lib parent (list atom-proof) (list *library-len*)))
      (cdr-equation (library-library-axiom lib "COMPLETION-OF-CDR" (list *library-x*)))
      (selected (proof-proof-select proof (caddr (proof-step-first cdr-equation)) atom-proof))
      (cdr-zero (proof-proof-chain proof cdr-equation (list selected)))
      (same-child (proof-proof-reflexive proof child))
      (child-zero (proof-proof-rewrite proof same-child cdr-zero '(1 2 1)))
      (zero-length (t3-logic-libraryproofs-simplify lib (caddr (proof-step-first child-zero))
                                                   nil (list *library-len*)))
      (child-zero (proof-proof-chain proof child-zero (list zero-length)))
      (typed (t3-logic-libraryproofs-type-of lib *proof-zero* nil))
      (reflexive (library-library-cite lib "WEAK-REFLEXIVE" (list *proof-zero*) (list typed)))
      (parent-zero (proof-proof-symmetric proof parent-zero))
      (zero-case (proof-proof-rewrite proof reflexive parent-zero '(1 1 1)))
      (child-zero (proof-proof-symmetric proof child-zero))
      (zero-case (proof-proof-rewrite proof zero-case child-zero '(1 1 2)))
      (step (proof-proof-cases proof cons-test smaller zero-case)))
     (library-library-lemma lib "T3-LEN-CDR-WEAK" (library-le child parent) step nil))))

(defun t3-size-evens-step (lib bound term evidence)
  (let* ((proof (library-library-proof lib))
         (evens-term (list *t3-size-evens* term))
         (after (list *t3-size-evens* (list *library-cdr* (list *library-cdr* term)))))
    (proof-with-checked-results
     ((step (t3-size-shift lib bound *proof-one* t nil))
      (evens (proof-proof-unfold proof evens-term))
      (not-end (t3-logic-evidence-require evidence (proof-neg (list *t3-logic-endp* term))))
      (selected (proof-proof-select proof (caddr (proof-step-first evens)) (car not-end)))
      (evens (proof-proof-chain proof evens (list selected)))
      (same (proof-proof-reflexive proof (list *library-len* evens-term)))
      (len-evens (proof-proof-rewrite proof same evens '(1 2 1)))
      (cons-length (t3-size-len-cons lib (list *library-car* term) after))
      (len-evens (proof-proof-chain proof len-evens (list cons-length)))
      (length (proof-proof-unfold proof (list *library-len* term)))
      (is-cons (t3-logic-evidence-require (cdr not-end) (list *t3-logic-consp* term)))
      (selected (proof-proof-select proof (caddr (proof-step-first length)) (car is-cons)))
      (length (proof-proof-chain proof length (list selected)))
      (strict (proof-is-call (proof-step-first step) *proof-less*))
      (len-evens (proof-proof-symmetric proof len-evens))
      (step (proof-proof-rewrite proof step len-evens (if strict '(1 1) '(1 1 2))))
      (length (proof-proof-symmetric proof length))
      (step (proof-proof-rewrite proof step length (if strict '(1 2) '(1 1 1))))
      (step (proof-proof-tidy proof step)))
     (cons step (cdr is-cons)))))

(defun t3-size-evens-bounds (lib)
  (proof-with-checked-results ((lib (t3-size-length-weak lib)))
    (let* ((proof (library-library-proof lib))
           (x *library-x*)
           (evens (list *t3-size-evens* x))
           (once (list *library-cdr* x))
           (twice (list *library-cdr* once))
           (rest (list *t3-size-evens* twice))
           (measure (list *library-count* x))
           (formula (library-le (list *library-len* evens) (list *library-len* x)))
           (tail-formula (library-le (list *library-len* rest) (list *library-len* twice)))
           (end (list *t3-logic-endp* x))
           (cons-test (list *t3-logic-consp* x)))
      (proof-with-checked-results
       ((entering (t3-logic-evidence-init lib (list (list end nil)) nil nil))
        (smaller (t3-size-count-descent lib (list *library-count* twice) measure entering))
        (hypothesis (proof-ite (proof-step-first (car smaller)) tail-formula *proof-true*))
        (premise (proof-proof-assume proof hypothesis t))
        (ih (proof-proof-prove-if proof premise (car smaller)))
        (weak (library-library-cite lib "T3-LEN-CDR-WEAK" (list once) nil))
        (bound (t3-size-chain lib ih weak nil))
        (positive (t3-size-evens-step lib bound x (cdr smaller)))
        (leaving (t3-logic-evidence-init lib (list (list end t)) nil nil))
        (ended (t3-logic-evidence-require leaving end))
        (left-zero (t3-logic-libraryproofs-simplify lib (list *library-len* evens)
                                                   (list (car ended))
                                                   (list *t3-size-evens* *library-len*)))
        (not-cons (t3-logic-evidence-require (cdr ended) (proof-neg cons-test)))
        (right-zero (t3-logic-libraryproofs-simplify lib (list *library-len* x)
                                                    (list (car not-cons)) (list *library-len*)))
        (typed (t3-logic-libraryproofs-type-of lib *proof-zero* nil))
        (base (library-library-cite lib "WEAK-REFLEXIVE" (list *proof-zero*) (list typed)))
        (left-zero (proof-proof-symmetric proof left-zero))
        (base (proof-proof-rewrite proof base left-zero '(1 1 2)))
        (right-zero (proof-proof-symmetric proof right-zero))
        (base (proof-proof-rewrite proof base right-zero '(1 1 1)))
        (ordinal (library-library-builtin lib 1 x))
        (cases (proof-proof-cases proof end base (car positive)))
        (step (proof-proof-induct proof ordinal cases formula measure
                                  (list (list (list x twice))))))
       (library-library-lemma lib "T3-EVENS-LENGTH" formula step nil)))))

(defun t3-size-evidence-after-library (evidence lib extended)
  (if (equal (t3-logic-evidence-lib evidence) lib)
      (t3-logic-evidence-with-lib evidence extended)
    evidence))

(defun t3-size-alternating-length (lib smaller larger evidence)
  (proof-with-checked-results
   ((extended
     (if (assoc-equal (proof-sym "SELF-T3-EVENS-LENGTH" "ACL2")
                      (proof-proof-facts (library-library-proof lib)))
         lib
       (t3-size-evens-bounds lib)))
    (part (proof-term-at smaller 1))
    (term (proof-term-at larger 1)))
   (let* ((evidence (t3-size-evidence-after-library evidence lib extended))
          (lib extended)
          (proof (library-library-proof lib))
          (tail (list *library-cdr* term))
          (tail2 (list *library-cdr* tail)))
     (cond
      ((equal part (list *t3-size-odds* term))
       (proof-with-checked-results
        ((first (library-library-cite lib "T3-EVENS-LENGTH" (list tail) nil))
         (second (t3-size-length-tail lib term evidence))
         (bound (t3-size-chain lib first (car second) nil))
         (opened (proof-proof-unfold proof part))
         (reverse (proof-proof-symmetric proof opened))
         (step (proof-proof-rewrite proof bound reverse '(1 1 1)))
         (step (proof-proof-tidy proof step)))
        (list step lib (cdr second))))
      ((not (equal part (list *t3-size-evens* term)))
       '(:failure "unsupported" ""))
      (t
       (let ((not-end (proof-neg (list *t3-logic-endp* term))))
         (proof-with-checked-results
          ((first (library-library-cite lib "T3-EVENS-LENGTH" (list tail2) nil))
           (second (t3-size-length-tail lib tail evidence))
           (bound (t3-size-chain lib first (car second) nil))
           (found (t3-logic-evidence-find (cdr second) not-end))
           (evidence
            (if (car found)
                (cdr found)
              (proof-with-checked-results
               ((is-cons (t3-logic-evidence-require (cdr found) (list *t3-logic-consp* term)))
                (fact (t3-logic-libraryproofs-prove-formula
                       lib not-end (list *t3-logic-endp* *t3-logic-atom* *proof-not*)
                       (list (car is-cons))))
                (literal (proof-step-first fact)))
               (t3-logic-evidence-with-facts
                (cdr is-cons) (table-put (t3-logic-evidence-facts (cdr is-cons))
                                           literal fact)))))
           (step (t3-size-evens-step lib bound term evidence)))
          (list (car step) lib (cdr step)))))))))

(defun t3-size-constructors (lib measure)
  (proof-with-checked-results ((parts (proof-list-of-length measure 4)))
    (let ((proof (library-library-proof lib))
          (exponent (cadr parts))
          (coefficient (caddr parts))
          (rest (cadddr parts)))
      (proof-with-checked-results
       ((inner (proof-proof-fact proof "consp-cons"
                                 (list (list *library-x* exponent)
                                       (list *library-y* coefficient))))
        (outer (proof-proof-fact proof "consp-cons"
                                 (list (list *library-x* (list *proof-cons* exponent coefficient))
                                       (list *library-y* rest)))))
       (list inner outer)))))

(defun t3-size-ordinal-with-phase (coefficient phase)
  (list *t3-size-make-ord* *proof-one* coefficient phase))

(defun t3-size-open-ordinal-order (lib left right evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((opened (proof-proof-unfold proof (list *proof-ordinal-less* left right)))
      (left-facts (t3-size-constructors lib left))
      (right-facts (t3-size-constructors lib right))
      (normal (t3-logic-libraryproofs-normalize
               lib (caddr (proof-step-first opened)) (append left-facts right-facts evidence)
               *t3-size-ordinal-operations*)))
     (proof-proof-chain proof opened (list normal)))))

(defun t3-size-ordinal-ranking-unit (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (constructed (t3-size-ordinal-with-phase x y))
         (goal (list *proof-ordinalp* constructed)))
    (proof-with-checked-results
     ((ix (proof-proof-assume proof (library-integer x) t))
      (px (proof-proof-assume proof (library-positive x) t))
      (ny (proof-proof-assume proof (list *library-natp* y) t))
      (iy (library-library-cite lib "NATURAL-INTEGER" (list y) (list ny)))
      (finite (library-library-cite lib "INTEGER-FINITE" (list y) (list iy)))
      (no-cons (t3-logic-libraryproofs-simplify-first lib finite nil
                                                     (list *t3-size-o-finp* *t3-logic-atom*)))
      (one (t3-logic-libraryproofs-natural lib *proof-one*))
      (ordinal-one (library-library-cite lib "NATURAL-ORDINAL" (list *proof-one*) (list one)))
      (ordinal-y (library-library-cite lib "NATURAL-ORDINAL" (list y) (list ny)))
      (expansion (proof-proof-unfold proof goal))
      (constructors (t3-size-constructors lib constructed))
      (body (t3-logic-libraryproofs-prove-formula
             lib (caddr (proof-step-first expansion))
             (append *t3-size-ordinal-operations* (list *proof-ordinal-less*))
             (append constructors (list ix px no-cons ordinal-one ordinal-y))))
      (step (proof-proof-transport proof body expansion)))
     (library-library-lemma lib "T3-UNIT-ORDINAL" goal step
                           (library-guards (list (proof-step-first ix)
                                                 (proof-step-first px)
                                                 (proof-step-first ny)))))))

(defun t3-size-ordinal-ranking-coefficient (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (left (t3-size-ordinal-with-phase x *library-z*))
         (right (t3-size-ordinal-with-phase y *t3-size-w*))
         (same (proof-eq x y)))
    (proof-with-checked-results
     ((bound (proof-proof-assume proof (library-lt x y) t))
      (equality (proof-proof-assume proof same t))
      (impossible (proof-proof-rewrite proof bound equality '(1 1)))
      (iy (proof-proof-assume proof (library-integer y) t))
      (reflexive (library-library-cite lib "WEAK-REFLEXIVE" (list y) (list iy)))
      (cut (proof-proof-cut proof impossible reflexive))
      (apart (proof-proof-front proof cut (proof-neg same)))
      (opened (t3-size-open-ordinal-order lib left right (list apart)))
      (step (proof-proof-transport proof bound opened)))
     (library-library-lemma lib "T3-ORDINAL-COEFFICIENT-LESS"
                           (list *proof-ordinal-less* left right) step
                           (library-guards (list (proof-step-first iy) (proof-step-first bound)))))))

(defun t3-size-ordinal-ranking-lemmas (lib)
  (if (assoc-equal (proof-sym "SELF-T3-UNIT-ORDINAL" "ACL2")
                   (proof-proof-facts (library-library-proof lib)))
      lib
    (proof-with-checked-results
     ((lib (t3-size-ordinal-ranking-unit lib))
      (lib (t3-size-ordinal-ranking-coefficient lib))
      (left (t3-size-ordinal-with-phase *library-x* *library-y*))
      (right (t3-size-ordinal-with-phase *library-x* *library-z*))
      (phase (t3-size-open-ordinal-order lib left right nil)))
     (library-library-lemma
      lib "T3-ORDINAL-PHASE-ORDER"
      (proof-eq (list *proof-ordinal-less* left right)
                (list *proof-ordinal-less* *library-y* *library-z*))
      phase nil))))

(defun t3-size-ordinal-phase (lib measure)
  (proof-with-checked-results ((parts (proof-list-of-length measure 4)))
    (let ((exponent (cadr parts))
          (coefficient (caddr parts))
          (rest (cadddr parts)))
      (if (or (not (equal exponent *proof-one*))
              (not (proof-is-call coefficient *proof-plus*)))
          '(:failure "unsupported" "")
        (proof-with-checked-results ((args (proof-list-of-length coefficient 3)))
          (if (not (equal (cadr args) *proof-one*))
              '(:failure "unsupported" "")
            (let ((total (caddr args)))
              (proof-with-checked-results
               ((nat (t3-logic-libraryproofs-natural lib total))
                (total-type (t3-logic-libraryproofs-type-of lib total nil))
                (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE"
                                                    (list total) (list nat)))
                (positive (library-library-cite lib "POSITIVE-ONE-PLUS" (list total)
                                                 (list total-type nonnegative)))
                (lib (t3-size-ordinal-ranking-lemmas lib))
                (coefficient-type (t3-logic-libraryproofs-type-of lib coefficient nil))
                (rest-natural (t3-logic-libraryproofs-natural lib rest))
                (step (library-library-cite lib "T3-UNIT-ORDINAL" (list coefficient rest)
                                             (list coefficient-type positive rest-natural))))
               (cons step lib)))))))))

(defun t3-size-coefficient-descent (lib smaller larger order)
  (proof-with-checked-results
   ((lib (t3-size-ordinal-ranking-lemmas lib))
    (small-coefficient (proof-term-at smaller 2))
    (large-coefficient (proof-term-at larger 2))
    (small-phase (proof-term-at smaller 3))
    (large-phase (proof-term-at larger 3))
    (typed (t3-logic-libraryproofs-type-of lib large-coefficient nil))
    (step (proof-proof-use
           (library-library-proof lib) (proof-sym "SELF-T3-ORDINAL-COEFFICIENT-LESS" "ACL2")
           (list (list *library-x* small-coefficient) (list *library-y* large-coefficient)
                 (list *library-z* small-phase) (list *t3-size-w* large-phase))
           (list typed order))))
   (cons step lib)))

(defun t3-size-phase-descent (lib smaller larger order)
  (proof-with-checked-results
   ((small-coefficient (proof-term-at smaller 2))
    (large-coefficient (proof-term-at larger 2)))
   (if (not (equal small-coefficient large-coefficient))
       '(:failure "failure" "")
     (proof-with-checked-results
      ((lib (t3-size-ordinal-ranking-lemmas lib))
       (left (proof-term-at smaller 3))
       (right (proof-term-at larger 3))
       (comparison (t3-size-ordinal-comparison lib left right))
       (ordered (proof-proof-transport (library-library-proof lib) order comparison))
       (equality (library-library-cite lib "T3-ORDINAL-PHASE-ORDER"
                                        (list small-coefficient left right) nil))
       (step (proof-proof-transport (library-library-proof lib) ordered equality)))
      (cons step lib)))))

(defun t3-size-sum-count-match (after before)
  (if (and (proof-is-call after *library-count*) (proof-is-call before *library-count*))
      (proof-with-checked-results
       ((child (proof-term-at after 1))
        (parent (proof-term-at before 1))
        (path (t3-size-selector-path child parent)))
       (not (eq path :none)))
    nil))

(defun t3-size-sum-count-matches (left right before-left before-right)
  (proof-with-checked-results ((first (t3-size-sum-count-match left before-left)))
    (and first (t3-size-sum-count-match right before-right))))

(defun t3-size-sum-count-ordered (lib left right before-left before-right after evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((a (t3-size-count-bound lib (cadr left) (cadr before-left) evidence))
      (b (t3-size-count-bound lib (cadr right) (cadr before-right) (cdr a)))
      (lower (t3-size-shift lib (car a) right nil nil))
      (upper (t3-size-shift lib (car b) before-left t nil))
      (result (t3-size-chain lib lower upper nil))
      (result
       (if (equal (list left right) (cdr after))
           result
         (let ((place (if (proof-is-call (proof-step-first result) *proof-less*)
                          '(1 1) '(1 1 2))))
           (proof-with-checked-results
            ((commuted (library-library-axiom lib "COMMUTATIVITY-OF-+" (list left right))))
            (proof-proof-rewrite proof result commuted place)))))
      (result (proof-proof-tidy proof result)))
     (cons result (cdr b)))))

(defun t3-size-sum-count (lib after before evidence)
  (if (not (and (proof-is-call after *proof-plus*) (proof-is-call before *proof-plus*)))
      '(:failure "unsupported" "")
    (proof-with-checked-results
     ((parts (proof-list-of-length (cdr after) 2))
      (before-left (proof-term-at before 1))
      (before-right (proof-term-at before 2))
      (left (car parts))
      (right (cadr parts))
      (matched (t3-size-sum-count-matches left right before-left before-right)))
     (if matched
         (t3-size-sum-count-ordered lib left right before-left before-right after evidence)
       (proof-with-checked-results
        ((matched (t3-size-sum-count-matches right left before-left before-right)))
        (if matched
            (t3-size-sum-count-ordered lib right left before-left before-right after evidence)
          '(:failure "unsupported" "")))))))

(defun t3-size-ordinal-descent (lib smaller larger evidence)
  (proof-with-checked-results
   ((sc (proof-term-at smaller 2))
    (bc (proof-term-at larger 2)))
   (if (equal sc bc)
       (proof-with-checked-results
        ((left (proof-term-at smaller 3))
         (right (proof-term-at larger 3))
         (order (t3-logic-libraryproofs-prove lib (library-lt left right) nil nil))
         (result (t3-size-phase-descent lib smaller larger order)))
        (list (car result) (cdr result)
              (t3-size-evidence-after-library evidence lib (cdr result))))
     (proof-with-checked-results ((small-one (proof-term-at sc 1))
                                  (large-one (proof-term-at bc 1)))
       (if (not (and (equal small-one large-one) (equal large-one *proof-one*)))
           '(:failure "failure" "")
         (proof-with-checked-results
          ((after (proof-term-at sc 2))
           (before (proof-term-at bc 2))
           (sum (t3-size-sum-count lib after before evidence))
           (bound (t3-size-shift lib (car sum) *proof-one* t nil)))
          (if (not (proof-is-call (proof-step-first bound) *proof-less*))
              '(:failure "unsupported" "")
            (proof-with-checked-results ((result (t3-size-coefficient-descent lib smaller larger bound)))
              (list (car result) (cdr result)
                    (t3-size-evidence-after-library (cdr sum) lib (cdr result)))))))))))

(defun t3-size-build-consp (lib)
  (let* ((proof (library-library-proof lib))
         (cell (list *proof-cons* *library-x* *library-y*))
         (constructed (list *t3-logic-consp* cell))
         (is-true (proof-eq constructed *proof-true*)))
    (proof-with-checked-results
     ((boolean (proof-proof-fact proof "booleanp-consp" (list (list *library-x* cell))))
      (positive (proof-proof-fact proof "consp-cons" nil))
      (boolean (t3-logic-libraryproofs-simplify-first
                lib boolean nil (list (proof-sym "BOOLEANP" "ACL2") (proof-cl "EQ"))))
      (not-true (proof-proof-assume proof is-true nil))
      (equal-nil (proof-proof-prove-if proof boolean not-true))
      (equal-nil (t3-logic-libraryproofs-simplify-first lib equal-nil nil (list (proof-cl "EQ"))))
      (contradicted (proof-proof-rewrite proof positive equal-nil '(1)))
      (contradicted (proof-proof-tidy proof contradicted))
      (step (proof-proof-front proof contradicted is-true)))
     (library-library-lemma lib "T3-CONSP-CONS-TRUE" is-true step nil))))

(defun t3-size-build-natural-leaves (leaves lib)
  (declare (xargs :measure (acl2-count leaves)))
  (if (endp leaves)
      nil
    (let* ((request (car leaves))
           (step (t3-logic-libraryproofs-natural lib (car request))))
      (cons (cons request step) (t3-size-build-natural-leaves (cdr leaves) lib)))))

(defun t3-size-build-length (lib)
  (let* ((proof (library-library-proof lib))
         (length (list *t3-logic-length* *library-x*))
         (goal (list *library-natp* length))
         (template (list *library-natp* *proof-result*)))
    (proof-with-checked-results
     ((equation (proof-proof-unfold proof length))
      (value (caddr (proof-step-first equation)))
      (leaves (t3-logic-libraryproofs-by-value-leaves lib value nil))
      (leaf (t3-size-build-natural-leaves leaves lib))
      (result (t3-logic-libraryproofs-by-value lib value template leaf nil))
      (step (library-library-transport-argument lib result equation 1)))
     (library-library-lemma lib "T3-LENGTH-NATURAL" goal step nil))))

(defun t3-size-build-weak (lib)
  (let* ((proof (library-library-proof lib))
         (x *library-x*)
         (y *library-y*)
         (z *library-z*)
         (a (library-diff y x))
         (b (library-diff z y)))
    (proof-with-checked-results
     ((integers (library-library-ints lib (list x y z)))
      (xy (proof-proof-assume proof (library-lt y x) nil))
      (yz (proof-proof-assume proof (library-lt z y) nil))
      (left-axiom (library-library-axiom lib "<-ON-OTHERS" (list y x)))
      (left (proof-proof-rewrite proof xy left-axiom '(1 1)))
      (right-axiom (library-library-axiom lib "<-ON-OTHERS" (list z y)))
      (right (proof-proof-rewrite proof yz right-axiom '(1 1)))
      (a-type (t3-logic-libraryproofs-type-of lib a integers))
      (b-type (t3-logic-libraryproofs-type-of lib b integers))
      (sum-bound (library-library-cite lib "NONNEGATIVE-SUM" (list a b)
                                       (list a-type b-type left right)))
      (typed (library-guards (list (proof-step-first (car integers))
                                   (proof-step-first (cadr integers))
                                   (proof-step-first (caddr integers)))))
      (step (library-library-weak-from-difference lib x z sum-bound integers))
      (lib (library-library-lemma lib "T3-WEAK-TRANSITIVE" (library-le x z) step
                                  (append typed (list (library-lt y x) (library-lt z y)))))
      (sum-x (library-plus x z))
      (sum-y (library-plus y z))
      (step (library-library-weak-from-difference lib sum-x sum-y left integers)))
     (library-library-lemma lib "T3-WEAK-SHIFT" (library-le sum-x sum-y) step
                           (append typed (list (library-lt y x)))))))

(defun t3-size-build-phase (phase result conditions)
  (let* ((lib (car result))
         (evidence (cdr result))
         (a (car phase))
         (b (cadr phase))
         (left (t3-size-doubled-rank *library-x* a))
         (right (t3-size-doubled-rank *library-y* b)))
    (proof-with-checked-results
     ((step (t3-arithmetic-integer-comparison lib left right evidence))
      (extended (library-library-lemma lib (t3-size-phase-lemma a b)
                                       (library-lt left right) (car step) conditions)))
     (cons extended (t3-size-evidence-after-library (cdr step) lib extended)))))

(defun t3-size-build-phases (phases result conditions)
  (declare (xargs :measure (acl2-count phases)))
  (cond ((failure-p result) result)
        ((endp phases) (car result))
        (t (t3-size-build-phases (cdr phases) (t3-size-build-phase (car phases) result conditions)
                                 conditions))))

(defun t3-size-build (lib)
  (proof-with-checked-results
   ((lib (t3-size-build-consp lib))
    (lib (t3-size-build-length lib))
    (lib (t3-size-build-weak lib))
    (types (library-library-ints lib (list *library-x* *library-y*)))
    (less (proof-proof-assume (library-library-proof lib) (library-lt *library-x* *library-y*) t))
    (evidence (t3-logic-evidence-init lib nil (append types (list less)) nil))
    (conditions (library-guards (list (proof-step-first (car types))
                                        (proof-step-first (cadr types))
                                        (proof-step-first less)))))
   (t3-size-build-phases '((nil nil) (nil t) (t nil) (t t)) (cons lib evidence) conditions)))
