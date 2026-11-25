(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *b2-measures-nfix* (proof-sym "NFIX" "ACL2"))
(defconst *b2-measures-zp* (proof-sym "ZP" "ACL2"))
(defconst *b2-measures-set-empty* (proof-sym "EMPTYP$INLINE" "SET"))
(defconst *b2-measures-set-fix* (proof-sym "SFIX$INLINE" "SET"))
(defconst *b2-measures-set-tail* (proof-sym "TAIL$INLINE" "SET"))
(defconst *b2-measures-setp* (proof-sym "SETP" "SET"))

(defun b2-measures-rejected-step-p (value)
  (and (failure-p value)
       (member-equal (cadr value) '("value" "inapplicable" "unproved"))))

(defun b2-measures-rulers-make (lib steps)
  (list :b2-measures-rulers lib steps))

(defun b2-measures-rulers-lib (rulers)
  (cadr rulers))

(defun b2-measures-rulers-steps (rulers)
  (caddr rulers))

(defun b2-measures-rulers-init (lib evidence)
  (proof-with-checked-results ((steps (b2-tactics-tactics-evidence lib evidence)))
    (b2-measures-rulers-make lib steps)))

(defun b2-measures-rulers-with-lib (rulers lib)
  (b2-measures-rulers-make lib (b2-measures-rulers-steps rulers)))

(defun b2-measures-rulers-store (rulers term step)
  (cons step
        (b2-measures-rulers-make
         (b2-measures-rulers-lib rulers)
         (table-put (b2-measures-rulers-steps rulers) term step))))

(defun b2-measures-state-result (result)
  (if (failure-p (car result)) (car result) result))

(defun b2-measures-rulers-state (result rulers)
  (if (failure-p result) (cons result rulers) result))

(defun b2-measures-rulers-impossible (rulers term premise evidence unfold)
  (proof-with-checked-results
      ((step (b2-tactics-tactics-from-impossible
              (b2-measures-rulers-lib rulers) term premise evidence unfold nil 1500 nil)))
    (b2-measures-rulers-store rulers term step)))

(defun b2-measures-rulers-integer (rulers argument)
  (let* ((term (library-integer argument))
         (steps (b2-measures-rulers-steps rulers))
         (known (table-get steps term nil))
         (positive-test (table-get steps (proof-neg (list *b2-measures-zp* argument)) nil))
         (nonzip (table-get steps (proof-neg (list *b2-powers-zip* argument)) nil)))
    (cond (known (cons known rulers))
          (positive-test (b2-measures-rulers-impossible
                          rulers term positive-test nil (list *b2-measures-zp*)))
          (nonzip (b2-measures-rulers-impossible rulers term nonzip nil (list *b2-powers-zip*)))
          (t (cons nil rulers)))))

(defun b2-measures-rulers-find-cons (heads rulers term argument)
  (if (endp heads)
      (cons nil rulers)
    (let* ((lib (b2-measures-rulers-lib rulers))
           (proof (library-library-proof lib))
           (steps (b2-measures-rulers-steps rulers))
           (selection (list (car heads) argument))
           (known (table-get steps selection nil))
           (not-nil (table-get steps (proof-neg (proof-eq selection *proof-false*)) nil))
           (cons-step (table-get steps (list *proof-consp* selection) nil)))
      (proof-with-checked-results
          ((premise
            (cond (known known)
                  (cons-step
                   (b2-tactics-tactics-from-impossible lib selection cons-step nil nil nil 1500 nil))
                  (not-nil
                   (proof-with-checked-results ((term-or-nil (proof-proof-nil-or-true proof selection)))
                     (proof-proof-cut proof term-or-nil not-nil)))
                  (t nil))))
        (if premise
            (proof-with-checked-results
                ((atom-step (proof-proof-assume proof term nil))
                 (equality (b2-tactics-tactics-normalize lib selection (list atom-step) nil nil 1500 nil))
                 (rewritten (proof-proof-rewrite proof premise equality '(1)))
                 (result (proof-proof-tidy proof rewritten))
                 (step (proof-proof-front proof result term)))
              (b2-measures-rulers-store rulers term step))
          (b2-measures-rulers-find-cons (cdr heads) rulers term argument))))))

(defun b2-measures-rulers-find-state (rulers term)
  (let* ((steps (b2-measures-rulers-steps rulers))
         (known (table-get steps term nil)))
    (cond
     (known (cons known rulers))
     ((proof-is-call term *proof-integerp*)
      (b2-measures-rulers-state
       (proof-with-checked-results ((argument (proof-term-at term 1)))
         (if (equal term (library-integer argument))
             (b2-measures-rulers-integer rulers argument)
           (let ((nonzip (table-get steps (proof-neg (list *b2-powers-zip* argument)) nil)))
             (if nonzip
                 (b2-measures-rulers-impossible rulers term nonzip nil (list *b2-powers-zip*))
               (cons nil rulers)))))
       rulers))
     ((proof-is-call term *proof-less*)
      (let ((argument (proof-term-at term 2)))
        (let ((positive-test (table-get steps (proof-neg (list *b2-measures-zp* argument)) nil)))
          (cond
           ((failure-p argument) (cons argument rulers))
           ((and (equal term (library-positive argument)) positive-test)
            (let ((integer-answer (b2-measures-rulers-integer rulers argument)))
              (if (failure-p integer-answer) (cons integer-answer rulers)
                (b2-measures-rulers-state
                 (b2-measures-rulers-impossible (cdr integer-answer) term positive-test
                                                 (list (car integer-answer)) (list *b2-measures-zp*))
                 (cdr integer-answer)))))
           (t (cons nil rulers))))))
     ((proof-is-call term *proof-consp*)
      (b2-measures-rulers-state
       (proof-with-checked-results ((argument (proof-term-at term 1)))
         (b2-measures-rulers-find-cons (list *library-car* *library-cdr*) rulers term argument))
       rulers))
     (t (cons nil rulers)))))

(defun b2-measures-rulers-find (rulers term)
  (b2-measures-state-result (b2-measures-rulers-find-state rulers term)))

(defun b2-measures-rulers-require (rulers term)
  (proof-with-checked-results ((result (b2-measures-rulers-find rulers term)))
    (if (car result)
        result
      (b2-tactics-unproved))))

(defun b2-measures-builtin-evidence (rulers test)
  (let ((direct (if (proof-is-call test *proof-not*)
                    (let ((term (proof-term-at test 1)))
                      (if (failure-p term) (cons term rulers)
                        (b2-measures-rulers-find-state rulers term)))
                  (cons nil rulers))))
    (if (car direct) direct
      (b2-measures-rulers-find-state (cdr direct) (proof-neg test)))))

(defun b2-measures-discharge-tests (tests proof clause step rulers)
  (cond ((endp tests) (cons step rulers))
        ((member-equal (car tests) clause)
         (b2-measures-discharge-tests (cdr tests) proof clause step rulers))
        (t
         (let ((answer (b2-measures-builtin-evidence rulers (car tests))))
           (if (or (failure-p (car answer)) (not (car answer)))
               answer
             (let ((step (proof-proof-discharge proof step (car answer))))
               (if (failure-p step) (cons step (cdr answer))
                 (b2-measures-discharge-tests (cdr tests) proof clause step (cdr answer)))))))))

(defun b2-measures-discharge-matches (matches proof clause rulers)
  (if (endp matches)
      (cons nil rulers)
    (let* ((step (car matches))
           (result (b2-measures-discharge-tests (cdr (proof-step-clause step)) proof clause step rulers)))
      (if (car result) result
        (b2-measures-discharge-matches (cdr matches) proof clause (cdr result))))))

(defun b2-measures-rulers-direct-builtin (lib clause rulers)
  (if (endp clause)
      '(:failure "tactic-rejected" "")
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((matches (descent-builtin-matches (seq-range 1 24 1) proof clause (car (last clause)) nil)))
        (if (or (car matches) (not rulers))
            (cons (car matches) rulers)
          (b2-measures-state-result
           (b2-measures-discharge-matches (cdr matches) proof clause rulers)))))))

(defun b2-measures-selector-chain-bound (lib edge step rulers)
  (let* ((head (car edge))
         (base (cadr edge))
         (answer (b2-measures-rulers-find-state rulers (list *proof-consp* base)))
         (next (proof-with-checked-results
                   ((evidence (car answer))
                    (bound (descent-selector-edge lib head base evidence)))
                 (if step (library-library-compare-chain lib bound step) bound))))
    (cons next (cdr answer))))

(defun b2-measures-selector-chain-steps (edges lib outcome)
  (cond
   ((failure-p (car outcome)) outcome)
   ((endp edges)
    (let* ((step (car outcome))
           (result
            (proof-with-checked-results
                ((first (proof-step-first step))
                 (head (proof-term-at first 0)))
              (if (equal head *proof-less*) step
                '(:failure "tactic-rejected" "")))))
      (cons result (cdr outcome))))
   (t (b2-measures-selector-chain-steps
       (cdr edges) lib (b2-measures-selector-chain-bound lib (car edges) (car outcome) (cdr outcome))))))

(defun b2-measures-selector-chain (lib child parent rulers)
  (let ((edges (descent-selector-chain-edges child parent nil)))
    (cond ((failure-p edges) (cons edges rulers))
          (edges (b2-measures-selector-chain-steps edges lib (cons nil rulers)))
          (t (let ((reason (proof-with-checked-results ((text (proof-write parent)))
                             '(:failure "inapplicable" ""))))
               (cons reason rulers))))))

(defun b2-measures-selector-step (lib actual parent rulers)
  (let ((proof (library-library-proof lib))
        (terms
         (proof-with-checked-results
             ((head (proof-term-at actual 0))
              (selector (member-equal head (list *library-car* *library-cdr*)))
              (argument (if selector (proof-term-at actual 1) nil))
              (base (proof-term-at parent 1)))
           (list head selector argument base))))
    (cond
     ((failure-p terms) (cons terms rulers))
     ((and (cadr terms) (equal (caddr terms) (cadddr terms)))
      (let ((result
             (proof-with-checked-results
                 ((builtin (library-library-builtin lib (if (equal (car terms) *library-car*) 2 3)
                                                    (cadddr terms)))
                  (answer (b2-measures-rulers-require rulers (list *proof-consp* (cadddr terms)))))
               (cons (proof-proof-discharge proof builtin (car answer)) (cdr answer)))))
        (if (failure-p result) (cons result rulers) result)))
     (t
      (let* ((base (cadddr terms))
             (answer (b2-measures-selector-chain lib actual base rulers))
             (step (proof-with-checked-results
                       ((decrease (car answer))
                        (order (library-library-ordinal-comparison lib (list *library-count* actual) parent)))
                     (proof-proof-transport proof decrease order))))
        (cons step (cdr answer)))))))

(defun b2-measures-selector-decrease-state (lib goal rulers)
  (let* ((proof (library-library-proof lib))
         (terms
          (proof-with-checked-results
              ((parts (proof-list-of-length goal 3))
               (child-head (proof-term-at (cadr parts) 0))
               (parent-head (proof-term-at (caddr parts) 0)))
            (if (and (equal child-head *library-count*) (equal parent-head *library-count*))
                (proof-with-checked-results
                    ((raw (proof-term-at (cadr parts) 1))
                     (opened (proof-proof-simplify proof raw nil (list *termination-return-last*)))
                     (actual (if opened
                                 (proof-with-checked-results ((equation (proof-step-first opened)))
                                   (proof-term-at equation 2))
                               raw)))
                  (list actual (caddr parts) opened))
              '(:failure "tactic-rejected" "")))))
    (if (failure-p terms) (cons terms rulers)
      (let* ((answer (b2-measures-selector-step lib (car terms) (cadr terms) rulers))
             (opened (caddr terms)))
        (if (or (not opened) (failure-p (car answer))) answer
          (let ((step
                 (proof-with-checked-results
                     ((symmetric (proof-proof-symmetric proof opened))
                      (rewrite (proof-proof-rewrite proof (car answer) symmetric '(1 1 1))))
                   (proof-proof-tidy proof rewrite))))
            (cons step (cdr answer))))))))

(defun b2-measures-rulers-selector-decrease (lib goal rulers)
  (b2-measures-state-result (b2-measures-selector-decrease-state lib goal rulers)))

(defun b2-measures-set-tail-branch (lib value nonempty test atom-step nil-test sign)
  (let ((proof (library-library-proof lib))
        (empty (list *b2-measures-set-empty* value)))
    (proof-with-checked-results
        ((assumption (proof-proof-assume proof nil-test sign))
         (evidence (list atom-step assumption))
         (equality (b2-tactics-tactics-normalize lib empty evidence
                                                (list empty (list *b2-measures-setp* value))
                                                nil 1500 nil))
         (first (if equality (proof-step-first equality)
                  '(:failure "failure" "")))
         (normal (proof-term-at first 2))
         (true-step (b2-tactics-tactics-solve lib normal evidence nil nil 0 nil))
         (transport (proof-proof-transport proof true-step equality))
         (conflict (proof-proof-cut proof transport nonempty))
         (subsume (proof-proof-subsume proof conflict (cons test (proof-step-clause conflict)))))
      (proof-proof-tidy proof subsume))))

(defun b2-measures-set-tail-decrease (lib value nonempty)
  (let ((proof (library-library-proof lib))
        (test (list *proof-consp* value))
        (nil-test (proof-eq value *proof-false*)))
    (proof-with-checked-results
        ((atom-step (proof-proof-assume proof test nil))
         (yes (b2-measures-set-tail-branch lib value nonempty test atom-step nil-test t))
         (no (b2-measures-set-tail-branch lib value nonempty test atom-step nil-test nil))
         (cons-step (proof-proof-cases proof nil-test yes no))
         (tail (b2-tactics-tactics-normalize lib (list *b2-measures-set-tail* value)
                                             (list nonempty)
                                             (list *b2-measures-set-tail* *b2-measures-set-fix*)
                                             nil 1500 nil))
         (structural (library-library-builtin lib 3 value))
         (step (proof-proof-discharge proof structural cons-step))
         (symmetric (proof-proof-symmetric proof tail))
         (rewrite (proof-proof-rewrite proof step symmetric '(1 1 1))))
      (proof-proof-tidy proof rewrite))))

(defun b2-measures-count-increment-exchange (lib step offset term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((exchange (library-library-axiom lib "COMMUTATIVITY-OF-+" (list offset term)))
         (rewrite (proof-proof-rewrite proof step exchange '(1 1 1))))
      (proof-proof-tidy proof rewrite))))

(defmacro b2-measures-with-ruler-queries (rulers queries result)
  (if (endp queries)
      result
    (let ((binding (car queries)))
      `(let ((b2-measures-query (b2-measures-rulers-find-state ,rulers ,(cadr binding))))
         (let ((,rulers (cdr b2-measures-query))
               (,(car binding) (car b2-measures-query)))
           (if (failure-p ,(car binding))
               b2-measures-query
             (b2-measures-with-ruler-queries ,rulers ,(cdr queries) ,result)))))))

(defun b2-measures-count-decrement (lib a b rulers)
  (let ((proof (library-library-proof lib)))
    (b2-measures-with-ruler-queries rulers
        ((typed (library-integer b))
         (positive-b (library-positive b)))
      (cons (if (and typed positive-b)
                (proof-with-checked-results
                    ((builtin (library-library-builtin lib 14 b))
                     (typed-step (proof-proof-discharge proof builtin typed))
                     (step (proof-proof-discharge proof typed-step positive-b))
                     (first (proof-term-at a 1)))
                  (if (equal first b)
                      (b2-measures-count-increment-exchange lib step *proof-neg-one* b)
                    step))
              nil)
            rulers))))

(defun b2-measures-count-negative (lib b typed negative nonzip nonpositive)
  (if (and typed (not negative) nonzip nonpositive)
      (let ((proof (library-library-proof lib))
            (sign (library-lt b *proof-zero*)))
        (proof-with-checked-results
            ((not-negative (proof-proof-assume proof sign nil))
             (zero (b2-powers-zero-from-signs lib b typed not-negative nonpositive))
             (nonzero (b2-tactics-tactics-from-impossible
                       lib (proof-neg (proof-eq b *proof-zero*)) nonzip nil
                       (list *b2-powers-zip*) nil 1500 nil))
             (cut (proof-proof-cut proof zero nonzero)))
          (proof-proof-front proof cut sign)))
    negative))

(defun b2-measures-count-increment (lib a b rulers)
  (b2-measures-with-ruler-queries rulers
      ((typed (library-integer b))
       (negative (library-lt b *proof-zero*))
       (nonzip (proof-neg (list *b2-powers-zip* b)))
       (nonpositive (proof-neg (library-positive b))))
    (let ((sign (b2-measures-count-negative lib b typed negative nonzip nonpositive)))
      (cond ((failure-p sign) (cons sign rulers))
            ((and typed sign)
             (let ((answer (b2-powers-below-zero-count lib b typed sign)))
               (if (failure-p answer) (cons answer rulers)
                 (let ((lib (cdr answer)))
                   (cons (if (equal (cadr a) b)
                             (b2-measures-count-increment-exchange lib (car answer) *proof-one* b)
                           (car answer))
                         (b2-measures-rulers-with-lib rulers lib))))))
            (t (cons nil rulers))))))

(defun b2-measures-count-nil (lib smaller parent argument rulers)
  (let* ((proof (library-library-proof lib))
         (cons-answer (b2-measures-rulers-require rulers (list *proof-consp* argument))))
    (if (failure-p cons-answer) (cons cons-answer rulers)
      (let ((step
             (proof-with-checked-results
                 ((fact (proof-proof-fact proof (proof-sym "ACL2-COUNT-CAR-CDR-LINEAR" "ACL2")
                                          (list (list *library-x* argument))))
                  (equation (proof-proof-modus-ponens proof fact (car cons-answer)))
                  (first (proof-step-first equation))
                  (right (proof-term-at first 2))
                  (total (proof-term-at right 2))
                  (natural (library-library-natural lib total))
                  (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE" (list total) (list natural)))
                  (typed (library-library-type-of lib total nil))
                  (positive (library-library-cite lib "POSITIVE-ONE-PLUS" (list total) (list typed nonnegative)))
                  (as-count (library-library-transport-argument lib positive equation 2))
                  (zero (b2-tactics-tactics-normalize lib smaller nil (list *library-count*) nil 1500 nil))
                  (positive-count (library-library-transport-argument lib as-count zero 1))
                  (order (library-library-ordinal-comparison lib smaller parent)))
               (proof-proof-transport proof positive-count order))))
        (cons step (cdr cons-answer))))))

(defun b2-measures-count-offset (lib a b rulers)
  (cond ((member-equal a (list (library-plus *proof-neg-one* b) (library-plus b *proof-neg-one*)))
         (b2-measures-count-decrement lib a b rulers))
        ((member-equal a (list (library-plus *proof-one* b) (library-plus b *proof-one*)))
         (b2-measures-count-increment lib a b rulers))
        (t (cons nil rulers))))

(defun b2-measures-count-tail (lib a b rulers)
  (if (equal a (list *b2-measures-set-tail* b))
      (b2-measures-with-ruler-queries rulers
          ((nonempty (proof-neg (list *b2-measures-set-empty* b))))
        (cons (if nonempty (b2-measures-set-tail-decrease lib b nonempty) nil) rulers))
    (cons nil rulers)))

(defun b2-measures-strict-count-state (lib smaller parent rulers)
  (let* ((args (proof-with-checked-results
                    ((a (proof-term-at smaller 1))
                     (b (proof-term-at parent 1)))
                  (list a b))))
    (if (failure-p args) (cons args rulers)
      (let* ((a (car args))
             (b (cadr args))
             (tail (b2-measures-count-tail lib a b rulers)))
        (if (car tail) tail
          (let ((offset (b2-measures-count-offset lib a b (cdr tail))))
            (cond ((car offset) offset)
                  ((equal smaller (list *library-count* *proof-false*))
                   (b2-measures-count-nil lib smaller parent b (cdr offset)))
                  (t (b2-measures-selector-decrease-state
                      lib (list *proof-ordinal-less* smaller parent) (cdr offset))))))))))

(defun b2-measures-nfix-natural (lib term)
  (proof-with-checked-results
      ((argument (proof-term-at term 1))
       (self-nfix (list *library-nfix* argument))
       (equation (b2-tactics-tactics-solve lib (proof-eq term self-nfix) nil
                                          (list term self-nfix *library-natp*) nil 0 nil))
       (natural (library-library-cite lib "NFIX-NATURAL" (cdr term) nil)))
    (library-library-transport-argument lib natural equation 1)))

(defun b2-measures-natural-by-search (lib term)
  (proof-with-checked-results ((search (b2-search-search-init lib 12 nil)))
    (car (b2-search-search-prove search (list *library-natp* term) nil 2 0))))

(mutual-recursion
 (defun b2-measures-measure-natural (lib term)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((proof-is-call term *b2-measures-nfix*) (b2-measures-nfix-natural lib term))
    ((and (consp term) (proof-is-call term *proof-plus*))
     (proof-with-checked-results ((evidence (b2-measures-natural-list lib (cdr term))))
       (library-library-cite lib "NATURAL-SUM" (cdr term) evidence)))
    (t (let ((natural (library-library-natural lib term)))
         (if (b2-measures-rejected-step-p natural)
             (b2-measures-natural-by-search lib term)
           natural)))))
 (defun b2-measures-natural-list (lib terms)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms) nil
     (proof-with-checked-results
         ((step (b2-measures-measure-natural lib (car terms)))
          (rest (b2-measures-natural-list lib (cdr terms))))
       (cons step rest)))))

(defun b2-measures-ordinal (lib term)
  (let ((step (descent-measure-ordinal lib term)))
    (if (b2-measures-rejected-step-p step)
        (proof-with-checked-results ((natural (b2-measures-measure-natural lib term)))
          (library-library-cite lib "NATURAL-ORDINAL" (list term) (list natural)))
      step)))

(defun b2-measures-integer-measure (lib term evidence)
  (let ((step (library-library-type-of lib term evidence)))
    (if (b2-measures-rejected-step-p step)
        (proof-with-checked-results ((natural (b2-measures-measure-natural lib term)))
          (library-library-cite lib "NATURAL-INTEGER" (list term) (list natural)))
      step)))

(defun b2-measures-integer-list (lib terms evidence)
  (if (endp terms) nil
    (proof-with-checked-results
        ((step (b2-measures-integer-measure lib (car terms) evidence))
         (rest (b2-measures-integer-list lib (cdr terms) evidence)))
      (cons step rest))))

(defun b2-measures-finite-order (lib smaller parent evidence)
  (let ((terms (list smaller parent)))
    (proof-with-checked-results ((types (b2-measures-integer-list lib terms evidence)))
      (library-library-cite lib "FINITE-ORDER" terms types))))

(defun b2-measures-unfold-measure (lib term)
  (if (not (proof-compound term)) nil
    (let* ((proof (library-library-proof lib))
           (definitions (proof-proof-definitions proof)))
      (proof-with-checked-results ((head (proof-term-at term 0)))
        (if (and (assoc-equal head definitions)
                 (not (member-equal head (list *proof-plus* *library-count* *library-len* *b2-measures-nfix*))))
            (proof-with-checked-results
                ((equation (proof-proof-unfold proof term))
                 (first (proof-step-first equation))
                 (right (proof-term-at first 2)))
              (if (proof-is-call right *proof-plus*) equation nil))
          nil)))))

(defun b2-measures-step-term (step position)
  (proof-with-checked-results ((first (proof-step-first step)))
    (proof-term-at first position)))

(defun b2-measures-sum-arguments (smaller parent position)
  (proof-with-checked-results
      ((before (proof-term-at parent position))
       (after (proof-term-at smaller position)))
    (list after before)))

(defun b2-measures-sum-exchange (lib step after before other)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left (library-library-axiom lib "COMMUTATIVITY-OF-+" (list after other)))
         (exchanged (proof-proof-rewrite proof step left '(1 1)))
         (right (library-library-axiom lib "COMMUTATIVITY-OF-+" (list before other))))
      (proof-proof-rewrite proof exchanged right '(1 2)))))

(defun b2-measures-sum-shift (lib step after before previous evidence position)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((order (b2-measures-finite-order lib after before evidence))
         (comparison (proof-proof-rewrite proof step order '(1)))
         (other (proof-term-at previous (- 3 position)))
         (nodes (list after before other))
         (types (b2-measures-integer-list lib nodes evidence))
         (shift (library-library-cite lib "LESS-SHIFT" nodes (append types (list comparison))))
         (shifted (if (equal position 2) (b2-measures-sum-exchange lib shift after before other) shift))
         (tidied (proof-proof-tidy proof shifted))
         (next (b2-measures-step-term shifted 1)))
      (cons tidied next))))

(defun b2-measures-sum-bound (lib smaller parent evidence shifts)
  (cond
   ((endp shifts) (b2-tactics-unproved))
   ((endp (cdr shifts)) (car shifts))
   (t
    (proof-with-checked-results
        ((middle (b2-measures-step-term (car shifts) 2))
         (nodes (list smaller middle parent))
         (types (b2-measures-integer-list lib nodes evidence)))
      (library-library-cite lib "LESS-TRANSITIVE" nodes (append types shifts))))))

(defun b2-measures-finish-sum (lib smaller parent evidence shifts)
  (proof-with-checked-results
      ((bound (b2-measures-sum-bound lib smaller parent evidence shifts))
       (order (b2-measures-finite-order lib smaller parent evidence)))
    (proof-proof-transport (library-library-proof lib) bound order)))

(defun b2-measures-is-length-decrease (smaller parent)
  (and (proof-is-call smaller *library-len*)
       (proof-is-call parent *library-len*)
       (proof-with-checked-results
           ((child (proof-term-at smaller 1))
            (base (proof-term-at parent 1)))
         (equal child (list *library-cdr* base)))))

(defun b2-measures-length-decrease (lib smaller parent rulers)
  (proof-with-checked-results
      ((cons-step (b2-measures-rulers-require rulers (list *proof-consp* (cadr parent))))
       (size (library-library-cite lib "LEN-CDR-LESS" (cdr parent) (list (car cons-step))))
       (order (library-library-ordinal-comparison lib smaller parent)))
    (proof-proof-transport (library-library-proof lib) size order)))

(defun b2-measures-unfold-goal (lib goal)
  (proof-with-checked-results
      ((left (b2-measures-unfold-measure lib (cadr goal)))
       (right (b2-measures-unfold-measure lib (caddr goal))))
    (if (or left right)
        (proof-with-checked-results
            ((smaller (if left (b2-measures-step-term left 2) (cadr goal)))
             (parent (if right (b2-measures-step-term right 2) (caddr goal))))
          (list (list (car goal) smaller parent) left right))
      nil)))

(defun b2-measures-restore-goal (lib step left right)
  (proof-with-checked-results
      ((step (if left (library-library-transport-argument lib step left 1) step)))
    (if right (library-library-transport-argument lib step right 2) step)))

(defun b2-measures-compare-by-fact (lib goal evidence rulers)
  (let ((smaller (cadr goal))
        (parent (caddr goal))
        (known (b2-measures-rulers-steps rulers)))
    (proof-with-checked-results
        ((search (b2-search-search-init lib 12 nil))
         (stored (b2-search-search-fact search goal known 2 0))
         (step (car stored))
         (first (and step (proof-step-first step))))
      (if (and step (equal first goal)) step
        (proof-with-checked-results
            ((result (b2-search-search-fact (cdr stored) (library-lt smaller parent) known 2 0))
             (fact (car result)))
          (if fact
              (proof-with-checked-results ((order (b2-measures-finite-order lib smaller parent evidence)))
                (proof-proof-transport (library-library-proof lib) fact order))
            (b2-tactics-unproved)))))))

(defun b2-measures-count-normalization (lib smaller evidence)
  (proof-with-checked-results ((argument (proof-term-at smaller 1)))
    (b2-tactics-tactics-normalize lib argument evidence
                                  (list (proof-sym "HARD-ERROR" "ACL2")
                                        (proof-sym "THE-CHECK" "ACL2"))
                                  nil 1500 nil)))

(defun b2-measures-restore-count (lib step opened)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((symmetric (proof-proof-symmetric proof opened))
         (rewritten (proof-proof-rewrite proof step symmetric '(1 1 1))))
      (proof-proof-tidy proof rewritten))))

(defun b2-measures-count-final (lib goal evidence rulers)
  (let* ((strict (b2-measures-strict-count-state lib (cadr goal) (caddr goal) rulers))
         (rulers (cdr strict))
         (lib (b2-measures-rulers-lib rulers)))
    (cons (if (b2-measures-rejected-step-p (car strict))
              (b2-measures-compare-by-fact lib goal evidence rulers)
            (car strict))
          lib)))

(defun b2-measures-compare-branch (lib goal evidence test held-step pending)
  (let* ((holds (not held-step))
         (signed (proof-proof-assume (library-library-proof lib) test holds)))
    (if (failure-p signed)
        (list pending lib signed)
      (let ((branch (list :compare goal (append evidence (list signed))))
            (after (if holds (list :negative-branch goal evidence test)
                     (list :join-branches test held-step))))
        (list (list* branch after pending) lib nil)))))

(defun b2-measures-compare-count (lib goal evidence rulers pending)
  (let* ((smaller (cadr goal))
         (parent (caddr goal))
         (opened (b2-measures-count-normalization lib smaller evidence)))
    (cond
     ((failure-p opened) (list pending lib opened))
     (opened
      (let ((right (b2-measures-step-term opened 2)))
        (if (failure-p right)
            (list pending lib right)
          (let ((rewritten (list (car goal) (list *library-count* right) parent)))
            (list (list* (list :compare rewritten evidence) (list :restore-count opened) pending)
                  lib nil)))))
     (t
      (let ((test (b2-tactics-first-test (cadr smaller))))
        (cond
         ((failure-p test) (list pending lib test))
         (test (b2-measures-compare-branch lib goal evidence test nil pending))
         (t
          (let ((answer (b2-measures-count-final lib goal evidence rulers)))
            (list pending (cdr answer) (car answer))))))))))

(defun b2-measures-compare-after-length (lib goal evidence rulers pending)
  (let ((smaller (cadr goal))
        (parent (caddr goal)))
    (if (and (proof-is-call smaller *proof-plus*) (proof-is-call parent *proof-plus*))
        (list (cons (list :sum (list smaller parent evidence) '(1 2) parent nil) pending)
              lib nil)
      (let ((expanded (b2-measures-unfold-goal lib goal)))
        (cond
         ((failure-p expanded) (list pending lib expanded))
         (expanded
          (list (list* (list :compare (car expanded) evidence)
                       (list :restore-goal (cadr expanded) (caddr expanded)) pending)
                lib nil))
         ((and (proof-is-call smaller *library-count*) (proof-is-call parent *library-count*))
          (b2-measures-compare-count lib goal evidence rulers pending))
         (t (list pending lib (b2-measures-compare-by-fact lib goal evidence rulers))))))))

(defun b2-measures-compare-start (lib goal evidence pending)
  (let ((direct
         (proof-with-checked-results
             ((parts (proof-list-of-length goal 3))
              (rulers (b2-measures-rulers-init lib evidence)))
           (b2-measures-rulers-direct-builtin lib (list parts) rulers))))
    (cond
     ((failure-p direct) (list pending lib direct))
     ((car direct) (list pending lib (car direct)))
     (t
      (let* ((smaller (cadr goal))
             (parent (caddr goal))
             (rulers (cdr direct))
             (length-case (b2-measures-is-length-decrease smaller parent)))
        (cond
         ((failure-p length-case) (list pending lib length-case))
         (length-case (list pending lib (b2-measures-length-decrease lib smaller parent rulers)))
         (t (b2-measures-compare-after-length lib goal evidence rulers pending))))))))

(defun b2-measures-sum-advance (task previous shifts pending)
  (cons (list :sum (cadr task) (cdr (caddr task)) previous shifts) pending))

(defun b2-measures-compare-sum-task (lib task pending)
  (let* ((terms (cadr task))
         (smaller (car terms))
         (parent (cadr terms))
         (evidence (caddr terms))
         (positions (caddr task))
         (previous (cadddr task))
         (shifts (car (cddddr task))))
    (if (endp positions)
        (list pending lib (b2-measures-finish-sum lib smaller parent evidence shifts))
      (let* ((args (b2-measures-sum-arguments smaller parent (car positions)))
             (after (car args))
             (before (cadr args)))
        (cond
         ((failure-p args) (list pending lib args))
         ((equal before after) (list (b2-measures-sum-advance task previous shifts pending) lib nil))
         (t
          (list (list* (list :compare (list *proof-ordinal-less* after before) evidence)
                       (list :sum-shift task after before) pending)
                lib nil)))))))

(defun b2-measures-compare-sum-shift (lib task step pending)
  (let* ((sum-task (cadr task))
         (after (caddr task))
         (before (cadddr task))
         (evidence (caddr (cadr sum-task)))
         (position (car (caddr sum-task)))
         (previous (cadddr sum-task))
         (shifts (car (cddddr sum-task)))
         (shift (b2-measures-sum-shift lib step after before previous evidence position)))
    (if (failure-p shift)
        (list pending lib shift)
      (list (b2-measures-sum-advance sum-task (cdr shift) (cons (car shift) shifts) pending) lib nil))))

(defun b2-measures-advance-comparison (lib task pending step)
  (case (car task)
    (:compare (b2-measures-compare-start lib (cadr task) (caddr task) pending))
    (:sum (b2-measures-compare-sum-task lib task pending))
    (:sum-shift (b2-measures-compare-sum-shift lib task step pending))
    (:restore-goal (list pending lib (b2-measures-restore-goal lib step (cadr task) (caddr task))))
    (:restore-count (list pending lib (b2-measures-restore-count lib step (cadr task))))
    (:negative-branch (b2-measures-compare-branch lib (cadr task) (caddr task) (cadddr task) step pending))
    (:join-branches (list pending lib (proof-proof-cases (library-library-proof lib)
                                                        (cadr task) (caddr task) step)))
    (otherwise (list pending lib step))))

; A comparison comes before the pending proof operations that use its result.
(defun b2-measures-run-comparison (n lib pending step)
  (declare (xargs :measure (nfix n)))
  (cond
   ((or (failure-p step) (endp pending)) (cons step lib))
   ((zp n) (cons '(:failure "fuel" "b2-measures-run-comparison") lib))
   (t
    (let ((next (b2-measures-advance-comparison lib (car pending) (cdr pending) step)))
      (b2-measures-run-comparison (1- n) (cadr next) (car next) (caddr next))))))

(defun b2-measures-compare-state (n lib goal evidence)
  (b2-measures-run-comparison n lib (list (list :compare goal evidence)) nil))

(defun b2-measures-definition-names (definitions)
  (if (endp definitions) nil
    (proof-with-checked-results
        ((name (proof-term-at (car definitions) 0))
         (rest (b2-measures-definition-names (cdr definitions))))
      (cons name rest))))

(defun b2-measures-aid-plan (names aids plan)
  (if (endp names) plan
    (let ((entry (assoc-equal (car names) aids)))
      (if entry
          (b2-measures-aid-plan (cdr names) aids (table-put plan (car entry) (cdr entry)))
        nil))))

(defun b2-measures-count-plan (selected)
  (if (endp selected) nil
    (cons (cons (caar selected) (list *library-count* (cdar selected)))
          (b2-measures-count-plan (cdr selected)))))

(defun b2-measures-offset-calls (calls position possible)
  (if (endp calls) t
    (proof-with-checked-results
        ((actual (proof-term-at (termination-call-actuals (car calls)) position))
         (term (termination-logical-body actual)))
      (and (member-equal term possible)
           (b2-measures-offset-calls (cdr calls) position possible)))))

(defun b2-measures-next-offset (name formals position calls)
  (if (endp formals) nil
    (let* ((formal (car formals))
           (possible (list (library-plus *proof-one* formal)
                           (library-plus *proof-neg-one* formal)
                           (library-plus formal *proof-one*)
                           (library-plus formal *proof-neg-one*))))
      (proof-with-checked-results ((valid (b2-measures-offset-calls calls position possible)))
        (if valid
            (cons (list (cons name (list *library-count* formal)))
                  (list :offset (cdr formals) (1+ position)))
          (b2-measures-next-offset name (cdr formals) (1+ position) calls))))))

(defun b2-measures-plan-offsets (definitions calls)
  (if (equal (len definitions) 1)
      (proof-with-checked-results ((definition (proof-list-of-length (car definitions) 3)))
        (b2-measures-next-offset (car definition) (cadr definition) 0 calls))
    nil))

(defun b2-measures-plan-selector (definitions calls)
  (proof-with-checked-results ((selected (termination-selector-plan definitions calls)))
    (if selected
        (cons (b2-measures-count-plan selected) (list :offsets))
      (b2-measures-plan-offsets definitions calls))))

(defun b2-measures-plan-first (definitions calls aids names)
  (proof-with-checked-results ((name (proof-term-at names 0)))
    (cond
     ((equal name *b2-pathnames-cancel*)
      (proof-with-checked-results ((plan (b2-pathnames-path-plan definitions)))
        (cons plan nil)))
     ((equal name *b2-scaling-power*)
      (proof-with-checked-results
          ((formals (proof-term-at (car definitions) 1))
           (argument (proof-term-at formals 0))
           (measure (b2-scaling-power-measure argument)))
        (list (list (cons *b2-scaling-power* measure)))))
     (t
      (let ((plan (b2-measures-aid-plan names aids nil)))
        (if plan (cons plan (list :selector))
          (b2-measures-plan-selector definitions calls)))))))

(defun b2-measures-plan-next (definitions calls aids names position)
  (case (car position)
    (:first (b2-measures-plan-first definitions calls aids names))
    (:selector (b2-measures-plan-selector definitions calls))
    (:offsets (b2-measures-plan-offsets definitions calls))
    (:offset (b2-measures-next-offset (car names) (cadr position) (caddr position) calls))
    (otherwise nil)))

(defun b2-measures-call-evidence (proof tests)
  (if (endp tests) nil
    (proof-with-checked-results
        ((signed (proof-list-of-length (car tests) 2))
         (step (proof-proof-assume proof (car signed) (cadr signed)))
         (rest (b2-measures-call-evidence proof (cdr tests))))
      (cons step rest))))

(defun b2-measures-ordinality-case (lib name clause)
  (proof-with-checked-results ((term (proof-term-at (car clause) 1)))
    (cond
     ((equal name *b2-scaling-power*)
      (cons (library-library-cite lib "NFIX-ORDINAL" (cdr term) nil) lib))
     ((equal name *b2-pathnames-cancel*) (b2-pathnames-path-ordinal lib term))
     (t (cons (b2-measures-ordinal lib term) lib)))))

(defun b2-measures-prove-decrease (lib name goal call evidence)
  (cond
   ((equal name *b2-pathnames-cancel*)
    (proof-with-checked-results
        ((path (b2-pathnames-pathcomparison-init lib goal evidence)))
      (cons (b2-pathnames-pathcomparison-prove path call) lib)))
   ((equal name (proof-sym "ILOG" "RADIX")) (b2-quotients-ilog-decrease lib goal evidence))
   ((equal name *b2-scaling-power*) (b2-scaling-power-decrease lib goal evidence))
   (t (b2-measures-compare-state 1000000 lib goal evidence))))

(defun b2-measures-decrease-case (lib name clause call)
  (proof-with-checked-results ((direct (descent-direct-builtin lib clause nil)))
    (if (car direct) (cons (car direct) lib)
      (proof-with-checked-results
          ((evidence (b2-measures-call-evidence (library-library-proof lib) (termination-call-tests call))))
        (b2-measures-prove-decrease lib name (car (last clause)) call evidence)))))

(defun b2-measures-subsumed-case (lib name clause call)
  (let ((answer (if call (b2-measures-decrease-case lib name clause call)
                  (b2-measures-ordinality-case lib name clause))))
    (if (failure-p answer) (cons answer lib)
      (let ((lib (cdr answer)))
        (cons (proof-with-checked-results ((step (car answer)))
                (proof-proof-subsume (library-library-proof lib) step clause))
              lib)))))

(defun b2-measures-collect-case (lib name cases seen proofs)
  (if (failure-p cases) (cons cases lib)
    (let ((clause (caar cases))
          (call (cadar cases)))
      (if (member-equal clause seen) (cons (cons seen proofs) lib)
        (let ((result (b2-measures-subsumed-case lib name clause call)))
          (if (failure-p (car result)) result
            (cons (cons (cons clause seen) (cons (car result) proofs)) (cdr result))))))))

(defun b2-measures-prove-ordinalities (definitions measures name proved)
  (if (or (failure-p (car proved)) (endp definitions)) proved
    (b2-measures-prove-ordinalities
     (cdr definitions) measures name
     (b2-measures-collect-case (cdr proved) name
                               (termination-ordinality-cases (list (car definitions)) measures)
                               (caar proved) (cdar proved)))))

(defun b2-measures-prove-decreases (calls measures formals name proved)
  (cond
   ((failure-p (car proved)) proved)
   ((endp calls) (cons (reverse (cdar proved)) (cdr proved)))
   (t
    (b2-measures-prove-decreases
     (cdr calls) measures formals name
     (b2-measures-collect-case (cdr proved) name
                               (termination-call-cases (list (car calls)) measures formals)
                               (caar proved) (cdar proved))))))

(defun b2-measures-entry-fields (names measure)
  (if (endp names) nil
    (let ((field (assoc-equal (car names) measure)))
      (if (not field) '(:failure "tactic-rejected" "")
        (proof-with-checked-results ((rest (b2-measures-entry-fields (cdr names) measure)))
          (cons (cdr field) rest))))))

(defun b2-measures-assemble-entry (lib name names measure decreases)
  (let ((fields (b2-measures-entry-fields names measure)))
    (if (failure-p fields) (cons fields lib)
      (cons (proof-proof-entry "measure" name (cons name fields) decreases) lib))))

(defun b2-measures-prove-candidate (lib definitions calls name names measure)
  (let ((formals (termination-formals definitions nil nil)))
    (if (failure-p formals) (cons formals lib)
      (let ((ordinals (b2-measures-prove-ordinalities definitions measure name (cons (cons nil nil) lib))))
        (if (failure-p (car ordinals)) ordinals
          (let ((decreases (b2-measures-prove-decreases calls measure formals name ordinals)))
            (if (failure-p (car decreases)) decreases
              (b2-measures-assemble-entry (cdr decreases) name names measure (car decreases)))))))))

(defun b2-measures-plan-attempt (lib definitions calls aids name names position)
  (let ((candidate (b2-measures-plan-next definitions calls aids names position)))
    (cond
     ((failure-p candidate) (list nil candidate))
     ((not candidate) (list nil (b2-tactics-unproved)))
     (t
      (let ((answer (b2-measures-prove-candidate lib definitions calls name names (car candidate))))
        (if (b2-measures-rejected-step-p (car answer))
            (list t (cdr answer) (cdr candidate))
          (list nil (b2-measures-state-result answer))))))))

(defun b2-measures-try-plans (n definitions calls aids name names attempt)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "b2-measures-try-plans"))
   ((not (car attempt)) (cadr attempt))
   (t
    (b2-measures-try-plans
     (1- n) definitions calls aids name names
     (b2-measures-plan-attempt (cadr attempt) definitions calls aids name names
                               (caddr attempt))))))

(defun b2-measures-prove-measure (lib definitions calls aids)
  (proof-with-checked-results
      ((definition (proof-term-at definitions 0))
       (name (proof-term-at definition 0))
       (names (b2-measures-definition-names definitions)))
    (b2-measures-try-plans
     1000000 definitions calls aids name names
     (b2-measures-plan-attempt lib definitions calls aids name names (list :first)))))
