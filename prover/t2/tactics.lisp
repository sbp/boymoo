(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t2-tactics-atom* (proof-cl "ATOM"))
(defconst *t2-tactics-endp* (proof-cl "ENDP"))
(defconst *t2-tactics-null* (proof-cl "NULL"))
(defconst *t2-tactics-eq* (proof-cl "EQ"))
(defconst *t2-tactics-eql* (proof-cl "EQL"))
(defconst *t2-tactics-equal-num* (proof-cl "="))
(defconst *t2-tactics-zp* (proof-sym "ZP" "ACL2"))
(defconst *t2-tactics-zip* (proof-sym "ZIP" "ACL2"))
(defconst *t2-tactics-posp* (proof-sym "POSP" "ACL2"))
(defconst *t2-tactics-definition-heads*
  (list *termination-return-last* *t2-tactics-atom* *t2-tactics-endp*
        *t2-tactics-null* *t2-tactics-eq* *t2-tactics-eql* *t2-tactics-equal-num*
        *t2-tactics-zp* *t2-tactics-zip* *t2-tactics-posp* *library-natp*))

(defconst *t2-tactics-entry-names*
  (list (coerce "ACL2::SELF-" 'list)
        (coerce "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_$<>+=*/!?-" 'list)))

(defun t2-tactics-entry-prefix-p (prefix characters)
  (if (endp prefix)
      t
    (and (consp characters)
         (eql (car prefix) (car characters))
         (t2-tactics-entry-prefix-p (cdr prefix) (cdr characters)))))

(defun t2-tactics-entry-name-tail (characters)
  (if (and (consp characters)
           (member-equal (car characters) (cadr *t2-tactics-entry-names*)))
      (cons (car characters) (t2-tactics-entry-name-tail (cdr characters)))
    nil))

(defun t2-tactics-entry-names-scan (characters skip names)
  (if (endp characters)
      names
    (if (posp skip)
        (t2-tactics-entry-names-scan (cdr characters) (1- skip) names)
      (let* ((prefix (car *t2-tactics-entry-names*))
             (tail (and (t2-tactics-entry-prefix-p prefix characters)
                        (t2-tactics-entry-name-tail (nthcdr (len prefix) characters)))))
        (if (endp tail)
            (t2-tactics-entry-names-scan (cdr characters) 0 names)
          (let ((name (coerce (append prefix tail) 'string)))
            (t2-tactics-entry-names-scan
             (cdr characters) (1- (+ (len prefix) (len tail)))
             (if (member-equal name names) names (cons name names)))))))))

(defun t2-tactics-entry-names (source names)
  (if (stringp source)
      (t2-tactics-entry-names-scan (coerce source 'list) 0 names)
    '(:failure "failure" "")))

(defun t2-tactics-proof-entries-visit (lemmas needed entries)
  (if (endp lemmas)
      entries
    (let ((lemma (car lemmas)))
      (proof-with-checked-results
       ((name (proof-term-at lemma 1))
        (text (proof-write name)))
       (if (member-equal text needed)
           (proof-with-checked-results
            ((source (proof-term-at lemma 3))
             (needed (t2-tactics-entry-names source needed)))
            (t2-tactics-proof-entries-visit (cdr lemmas) needed (cons lemma entries)))
         (t2-tactics-proof-entries-visit (cdr lemmas) needed entries))))))

(defun t2-tactics-proof-entries (lemmas entry)
  (proof-with-checked-results
   ((source (proof-term-at entry 3))
    (needed (t2-tactics-entry-names source nil)))
   (t2-tactics-proof-entries-visit (reverse lemmas) needed (list entry))))

(defun t2-tactics-ruler-facts-hypotheses (facts)
  (cadr facts))

(defun t2-tactics-ruler-facts-derived (facts)
  (caddr facts))

(defun t2-tactics-ruler-facts-proof (facts)
  (descent-hypotheses-proof (t2-tactics-ruler-facts-hypotheses facts)))

(defun t2-tactics-ruler-facts-tests (facts)
  (descent-hypotheses-tests (t2-tactics-ruler-facts-hypotheses facts)))

(defun t2-tactics-ruler-facts-extra (facts)
  (descent-hypotheses-extra (t2-tactics-ruler-facts-hypotheses facts)))

(defun t2-tactics-ruler-facts-with-proof (facts proof)
  (list :t2-ruler-facts
        (descent-hypotheses-with-proof (t2-tactics-ruler-facts-hypotheses facts) proof)
        (t2-tactics-ruler-facts-derived facts)))

(defun t2-tactics-generator-make (measures lib shared)
  (list :t2-tactics-generator measures lib shared))

(defun t2-tactics-generator-measures (generator)
  (cadr generator))

(defun t2-tactics-generator-lib (generator)
  (caddr generator))

(defun t2-tactics-generator-shared (generator)
  (cadddr generator))

(defun t2-tactics-generator-with-lib (generator lib)
  (t2-tactics-generator-make (t2-tactics-generator-measures generator) lib
                             (t2-tactics-generator-shared generator)))

(defun t2-tactics-generator-with-measures (generator measures)
  (t2-tactics-generator-make measures (t2-tactics-generator-lib generator)
                             (t2-tactics-generator-shared generator)))

(defconst *t2-tactics-unsupported-recipe*
  '(:failure "unsupported" ""))

(defun t2-tactics-generator-admit-definitions (proof definitions)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      proof
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3))
      (proof (proof-proof-add-definition proof (car definition) (cadr definition) (caddr definition))))
     (t2-tactics-generator-admit-definitions proof (cdr definitions)))))

(defun t2-tactics-generator-admit-constraints (facts constraints)
  (declare (xargs :measure (acl2-count constraints)))
  (if (endp constraints)
      facts
    (proof-with-checked-results
     ((constraint (proof-list-of-length (car constraints) 2)))
     (t2-tactics-generator-admit-constraints
      (table-put facts (car constraint) (list (cadr constraint)))
      (cdr constraints)))))

(defun t2-tactics-generator-admit-proof (proof kind data)
  (cond
   ((equal kind "define")
    (t2-tactics-generator-admit-definitions proof (cdr data)))
   ((member-equal kind '("theorem" "axiom"))
    (proof-with-checked-results
     ((formula (proof-term-at data 1))
      (name (proof-term-at data 0)))
     (proof-proof-with-facts proof (table-put (proof-proof-facts proof) name (list formula)))))
   ((equal kind "constrain")
    (proof-with-checked-results ((constraints (proof-term-at data 1)))
      (if (equal constraints *proof-nil*)
          proof
        (proof-with-checked-results
         ((facts (t2-tactics-generator-admit-constraints (proof-proof-facts proof) constraints)))
         (proof-proof-with-facts proof facts)))))
   (t proof)))

(defun t2-tactics-generator-admit-given (generator kind data)
  (let ((lib (t2-tactics-generator-lib generator)))
    (proof-with-checked-results
     ((proof (t2-tactics-generator-admit-proof (library-library-proof lib) kind data)))
     (t2-tactics-generator-with-lib generator (library-library-with-proof lib proof)))))

(defun t2-tactics-required-key (dictionary key)
  (let ((entry (assoc-equal key dictionary)))
    (if entry
        (cdr entry)
      '(:failure "missing-binding" ""))))

(defun t2-tactics-generator-measures-for-definitions (definitions stored measures)
  (if (endp definitions)
      measures
    (proof-with-checked-results
     ((definition (proof-list-of-length (car definitions) 3))
      (pair (t2-tactics-required-key stored (car definition)))
      (pair (proof-list-of-length pair 2)))
     (if (not (equal (cadr pair) *proof-ordinal-less*))
         *t2-tactics-unsupported-recipe*
       (t2-tactics-generator-measures-for-definitions
        (cdr definitions) stored (table-put measures (car definition) (car pair)))))))

(defun t2-tactics-generator-measures-for (generator definitions)
  (t2-tactics-generator-measures-for-definitions
   definitions (t2-tactics-generator-measures generator) nil))

(defun t2-tactics-ruler-facts-init (proof tests extra)
  (t2-guarded-selectors-context-init proof tests extra t))

(defun t2-tactics-ruler-facts-context (facts)
  (if (eq (car facts) :t2-ruler-facts)
      facts
    (t2-guarded-selectors-context-from-hypotheses
     (t2-tactics-ruler-facts-hypotheses facts) (t2-tactics-ruler-facts-derived facts))))

(defun t2-tactics-bare-proof-p (facts)
  (let ((proof (t2-tactics-ruler-facts-proof facts)))
    (equal proof (descent-proof proof))))

(defconst *t2-tactics-bare-axiom-error*
  '(:failure "failure" ""))

(defun t2-tactics-bare-selector-axiom-p (term quoted)
  (and (proof-is-call quoted *proof-quote*)
       (not (equal quoted *proof-false*))
       (equal (len term) 2)
       (or (proof-is-call term *library-car*) (proof-is-call term *library-cdr*))))

(defun t2-tactics-bare-learn-equality (proof step test holds)
  (if holds
      (proof-with-checked-results ((parts (proof-list-of-length test 3)))
        (let* ((left (cadr parts))
               (right (caddr parts))
               (selector (cond ((t2-tactics-bare-selector-axiom-p left right) left)
                               ((t2-tactics-bare-selector-axiom-p right left) right)
                               (t nil))))
          (if selector
              (proof-with-checked-results
               ((atom-step (proof-proof-assume proof (list *proof-consp* (cadr selector)) nil)))
               *t2-tactics-bare-axiom-error*)
            (t2-guarded-selectors-nonempty-source (library-make-library proof nil) step))))
    (proof-with-checked-results ((right (proof-term-at test 2)))
      (if (equal right *proof-false*)
          (proof-with-checked-results
           ((left (proof-term-at test 1))
            (nil-test (proof-proof-nil-or-true proof left))
            (cut (proof-proof-cut proof nil-test step)))
           (proof-proof-front proof cut left))
        nil))))

(defun t2-tactics-bare-learn-branch (proof step branch equality literal)
  (proof-with-checked-results
   ((when-held (proof-proof-transport proof branch equality))
    (cut (proof-proof-cut proof when-held step)))
   (proof-proof-front proof cut literal)))

(defun t2-tactics-bare-learn-if (proof step test holds)
  (proof-with-checked-results ((parts (proof-list-of-length (cdr test) 3)))
    (let ((condition (car parts))
          (yes (cadr parts))
          (no (caddr parts)))
      (cond
       ((and holds (equal no *proof-false*)) (proof-proof-conjunct proof step))
       ((and (not holds) (or (equal yes condition) (equal yes *proof-true*)))
        (proof-with-checked-results
         ((selected (proof-proof-if-true proof test))
          (branch (if (equal yes *proof-true*)
                      (proof-proof-prove proof *proof-true* nil nil)
                    (proof-proof-assume proof condition t)))
          (evidence (t2-tactics-bare-learn-branch proof step branch selected (proof-neg condition))))
         (list :selected evidence test)))
       ((and (not holds) (equal no *proof-true*))
        (proof-with-checked-results
         ((branch (proof-proof-prove proof *proof-true* nil nil))
          (selected (proof-proof-if-false proof test))
          (evidence (t2-tactics-bare-learn-branch proof step branch selected condition)))
         (list :selected evidence test)))
       (t nil)))))

(defun t2-tactics-bare-learn-literal (proof step test holds)
  (cond
   ((proof-is-call test *proof-not*)
    (proof-with-checked-results
     ((inner (proof-term-at test 1))
      (assumption (proof-proof-assume proof inner nil))
      (cut (proof-proof-cut proof assumption step)))
     (proof-proof-front proof cut inner)))
   ((and (proof-compound test) (member-equal (car test) *t2-tactics-definition-heads*))
    (proof-with-checked-results
     ((equation (proof-proof-unfold proof test))
      (rewritten (proof-proof-rewrite proof step equation (if holds '(1) '(1 1)))))
     (proof-proof-tidy proof rewritten)))
   ((proof-is-call test *proof-equal*) (t2-tactics-bare-learn-equality proof step test holds))
   ((and holds (proof-is-call test *proof-consp*))
    (proof-with-checked-results
     ((argument (proof-term-at test 1))
      (nil-test (proof-proof-nil-or-true proof argument))
      (contradiction (proof-proof-rewrite proof step nil-test '(1 1)))
      (simplified (proof-proof-simplify-first proof contradiction nil nil)))
     (proof-proof-front proof simplified argument)))
   ((and holds (or (proof-is-call test *library-car*) (proof-is-call test *library-cdr*)))
    (proof-with-checked-results ((base (proof-term-at test 1))) *t2-tactics-bare-axiom-error*))
   (t nil)))

(defund t2-tactics-bare-learn-next (facts step literal)
  (let ((proof (t2-tactics-ruler-facts-proof facts))
        (holds (not (proof-is-call literal *proof-not*))))
    (proof-with-checked-results ((test (if holds literal (proof-term-at literal 1))))
      (if (proof-is-call test *proof-if*)
          (t2-tactics-bare-learn-if proof step test holds)
        (proof-with-checked-results ((next (t2-tactics-bare-learn-literal proof step test holds)))
          (and next (list next)))))))

(defund t2-tactics-bare-learn-selected (facts step evidence test)
  (let ((proof (t2-tactics-ruler-facts-proof facts)))
    (proof-with-checked-results
     ((selection (proof-proof-select proof test evidence))
      (rewritten (proof-proof-rewrite proof step selection '(1 1))))
     (proof-proof-tidy proof rewritten))))

(mutual-recursion
 (defun t2-tactics-bare-learn (n facts step)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "t2-tactics-bare-learn")
     (proof-with-checked-results ((literal (proof-step-first step)))
       (if (assoc-equal literal (t2-tactics-ruler-facts-extra facts))
           facts
         (proof-with-checked-results
          ((facts (t2-guarded-selectors-context-learn-extra facts step))
           (steps (t2-tactics-bare-learn-next facts step literal)))
          (if (eq (car steps) :selected)
              (proof-with-checked-results
               ((facts (t2-tactics-bare-learn (1- n) facts (cadr steps)))
                (selected (t2-tactics-bare-learn-selected facts step (cadr steps) (caddr steps))))
               (t2-tactics-bare-learn (1- n) facts selected))
            (t2-tactics-bare-learn-steps (1- n) facts steps)))))))
 (defun t2-tactics-bare-learn-steps (n facts steps)
   (declare (xargs :measure (nfix n)))
   (cond
    ((endp steps) facts)
    ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "t2-tactics-bare-learn-steps"))
    (t (proof-with-checked-results ((facts (t2-tactics-bare-learn (1- n) facts (car steps))))
         (t2-tactics-bare-learn-steps (1- n) facts (cdr steps)))))))

(defun t2-tactics-bare-learn-tests (tests facts proof)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      facts
    (proof-with-checked-results
     ((test (proof-list-of-length (car tests) 2))
      (step (proof-proof-assume proof (car test) (cadr test)))
      (facts (t2-tactics-bare-learn 1000000 facts step)))
     (t2-tactics-bare-learn-tests (cdr tests) facts proof))))

(defun t2-tactics-bare-premises (facts)
  (proof-with-checked-results
   ((facts (if (t2-tactics-ruler-facts-derived facts)
               facts
             (t2-tactics-bare-learn-tests
              (t2-tactics-ruler-facts-tests facts)
              (t2-guarded-selectors-context-from-hypotheses (t2-tactics-ruler-facts-hypotheses facts) t)
              (t2-tactics-ruler-facts-proof facts)))))
   (cons (table-values (t2-tactics-ruler-facts-extra facts)) facts)))

(defun t2-tactics-bare-find (facts term)
  (proof-with-checked-results
   ((found (descent-hypotheses-find (t2-tactics-ruler-facts-hypotheses facts) term)))
   (let ((facts (t2-guarded-selectors-context-from-hypotheses (cdr found) (t2-tactics-ruler-facts-derived facts))))
     (if (car found)
         (cons (car found) facts)
       (proof-with-checked-results ((premises (t2-tactics-bare-premises facts)))
         (cons (table-get (t2-tactics-ruler-facts-extra (cdr premises)) term nil) (cdr premises)))))))

(defun t2-tactics-ruler-facts-learn (facts step)
  (let ((facts (t2-tactics-ruler-facts-context facts)))
    (if (t2-tactics-bare-proof-p facts)
        (t2-tactics-bare-learn 1000000 facts step)
      (t2-guarded-selectors-context-learn-step facts step))))

(defun t2-tactics-ruler-facts-premises (facts)
  (let ((facts (t2-tactics-ruler-facts-context facts)))
    (if (t2-tactics-bare-proof-p facts)
        (t2-tactics-bare-premises facts)
      (t2-guarded-selectors-context-premises facts))))

(defun t2-tactics-ruler-facts-find (facts term)
  (let ((facts (t2-tactics-ruler-facts-context facts)))
    (if (t2-tactics-bare-proof-p facts)
        (t2-tactics-bare-find facts term)
      (t2-guarded-selectors-context-find facts term))))

(defun t2-tactics-ruler-facts-require (facts term)
  (proof-with-checked-results ((result (t2-tactics-ruler-facts-find facts term)))
    (if (car result) result (descent-missing-hypothesis term))))

(defun t2-tactics-countdown-fixed-absolute-count (lib measure facts)
  (t2-countdown-fixed-absolute-count lib measure (t2-tactics-ruler-facts-context facts)))

(defun t2-tactics-countdown-signed-premise (lib value facts negative)
  (t2-countdown-signed-premise lib value (t2-tactics-ruler-facts-context facts) negative))

(defun t2-tactics-countdown-negative-countdown (lib goal facts)
  (t2-countdown-negative-countdown lib goal (t2-tactics-ruler-facts-context facts)))

(defund t2-tactics-builtin-evidence (facts test)
  (proof-with-checked-results
   ((negative (if (proof-is-call test *proof-not*)
                  (proof-with-checked-results ((inner (proof-term-at test 1)))
                    (t2-tactics-ruler-facts-find facts inner))
                (cons nil facts))))
   (if (car negative)
       negative
     (t2-tactics-ruler-facts-find (cdr negative) (proof-neg test)))))

(defund t2-tactics-discharge-builtin-tests (tests proof clause step facts)
  (declare (xargs :measure (acl2-count tests)))
  (cond
   ((endp tests) (cons step facts))
   ((member-equal (car tests) clause)
    (t2-tactics-discharge-builtin-tests (cdr tests) proof clause step facts))
   (t
    (proof-with-checked-results ((evidence (t2-tactics-builtin-evidence facts (car tests))))
      (if (car evidence)
          (proof-with-checked-results ((step (proof-proof-discharge proof step (car evidence))))
            (t2-tactics-discharge-builtin-tests (cdr tests) proof clause step (cdr evidence)))
        (cons nil (cdr evidence)))))))

(defun t2-tactics-discharge-builtin-matches (matches proof clause facts)
  (declare (xargs :measure (acl2-count matches)))
  (if (endp matches)
      (cons nil facts)
    (let ((step (car matches)))
      (proof-with-checked-results
       ((result (t2-tactics-discharge-builtin-tests (cdr (proof-step-clause step)) proof clause step facts)))
       (if (car result)
           result
         (t2-tactics-discharge-builtin-matches (cdr matches) proof clause (cdr result)))))))

(defun t2-tactics-direct-builtin (lib clause goal facts)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((matches (descent-builtin-matches (seq-range 1 24 1) proof clause goal nil)))
      (if (car matches)
          (cons (car matches) facts)
        (t2-tactics-discharge-builtin-matches (cdr matches) proof clause facts)))))

(defun t2-tactics-fixed-absolute-p (measure)
  (and (proof-is-call measure *t2-countdown-cl-abs*)
       (proof-with-checked-results ((value (proof-term-at measure 1)))
         (proof-is-call value *t2-arithmetic-ifix*))))

(defun t2-tactics-measure-ordinal (lib measure)
  (proof-with-checked-results
   ((builtin (descent-direct-builtin lib (list (list *proof-ordinalp* measure)) nil)))
   (if (car builtin)
       (car builtin)
     (proof-with-checked-results ((head (proof-term-at measure 0)))
       (if (equal head *library-gap*)
           (library-library-cite lib "GAP-ORDINAL" (cdr measure) nil)
         (proof-with-checked-results ((natural (t2-arithmetic-arithmetic-natural lib measure)))
           (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural))))))))

(defun t2-tactics-generator-ordinal-recipe (lib measure)
  (proof-with-checked-results ((weighted (t2-phase-weighted-measure measure)))
    (if weighted
        (t2-phase-weighted-ordinal lib measure)
      (proof-with-checked-results ((absolute (t2-tactics-fixed-absolute-p measure)))
        (cond (absolute (t2-countdown-fixed-absolute-ordinal lib measure))
              ((proof-is-call measure *t2-arithmetic-nfix*)
               (proof-with-checked-results
                ((lib (t2-arithmetic-arithmetic-build-countdowns lib))
                 (natural (t2-arithmetic-arithmetic-natural lib measure))
                 (step (library-library-cite lib "NATURAL-ORDINAL" (list measure) (list natural))))
                (cons step lib)))
              (t (proof-with-checked-results ((step (t2-tactics-measure-ordinal lib measure)))
                   (cons step lib))))))))

(defun t2-tactics-generator-ordinal (generator measure)
  (proof-with-checked-results
   ((result (t2-tactics-generator-ordinal-recipe (t2-tactics-generator-lib generator) measure)))
   (cons (car result) (t2-tactics-generator-with-lib generator (cdr result)))))

(defun t2-tactics-floor-arity-error (actual positive)
  (let ((size (len actual)))
    (cond
     ((equal size 3) nil)
     ((< size 3)
      (if positive
          '(:failure "failure" "")
        '(:failure "failure" "")))
     (t '(:failure "failure" "")))))

(defun t2-tactics-floor-decrease (lib actual value facts)
  (proof-with-checked-results
   ((direct (t2-tactics-ruler-facts-find facts (library-positive value)))
    (positive
     (if (car direct)
         (list (car direct) lib (cdr direct))
       (proof-with-checked-results
        ((nonnegative (t2-tactics-ruler-facts-find (cdr direct) (library-nonnegative value))))
        (if (car nonnegative)
            (t2-tactics-countdown-signed-premise lib value (cdr nonnegative) nil)
          (list nil lib (cdr nonnegative))))))
    (arity-error (t2-tactics-floor-arity-error actual (car positive)))
    (result
     (if (car positive)
         (t2-floor-positive-floor-decrease (cadr positive) value (caddr actual)
                                           (caddr positive) (car positive))
       (t2-half-signed-floor-decrease (cadr positive) value (caddr actual) (caddr positive)))))
   (cons (caar result) (cdr result))))

(defun t2-tactics-quotient-decrease (lib actual facts)
  (proof-with-checked-results
   ((args (proof-list-of-length (cdr actual) 2))
    (lib (t2-quotient-build-quotient-descent lib))
    (bounds (t2-floor-divisor-bounds lib (cadr args) (t2-tactics-ruler-facts-with-proof facts lib)))
    (lib (cdr bounds))
    (facts (cadar bounds))
    (integral (t2-tactics-ruler-facts-require facts (library-integer (car args))))
    (positive (t2-tactics-countdown-signed-premise lib (car args) (cdr integral) nil))
    (evidence (caar bounds))
    (step (library-library-cite (cadr positive) "COUNT-QUOTIENT-DECREASE" args
                                (list (car integral) (car evidence) (car positive) (cadr evidence)))))
   (cons step (cadr positive))))

(defun t2-tactics-count-decrease (lib goal child parent facts)
  (proof-with-checked-results
   ((actual (proof-term-at child 1))
    (floor-p (proof-is-call actual *t2-floor-floor*))
    (quotient-p (proof-is-call actual *t2-quotient-quotient*))
    (dividend (and (or floor-p quotient-p) (proof-term-at actual 1)))
    (value (proof-term-at parent 1)))
   (cond
    ((and floor-p (equal dividend value))
     (t2-tactics-floor-decrease lib actual value facts))
    ((and quotient-p (equal dividend value))
     (t2-tactics-quotient-decrease lib actual facts))
    ((member-equal actual (list (library-plus value *proof-one*)
                               (library-plus *proof-one* value) (list *t2-countdown-lognot* value)))
     (proof-with-checked-results ((result (t2-tactics-countdown-negative-countdown lib goal facts)))
       (cons (car result) (cadr result))))
    (t
     (proof-with-checked-results
      ((first (and (proof-is-call actual *proof-plus*) (proof-term-at actual 1)))
       (second (and (proof-is-call actual *proof-plus*) (equal first value) (proof-term-at actual 2))))
      (cond
       ((proof-is-call second *proof-minus*)
        (proof-with-checked-results
         ((part (proof-term-at second 1))
          (result (t2-subtraction-subtraction-decrease lib value part facts)))
         (cons (caar result) (cdr result))))
       ((or (proof-is-call actual *t2-arithmetic-numerator*)
            (proof-is-call actual *t2-arithmetic-denominator*))
        (proof-with-checked-results
         ((result (t2-arithmetic-rational-count-decrease lib goal facts)))
         (cons (car result) (cadr result))))
       ((proof-is-call actual *t2-lists-hons-remove*)
        (proof-with-checked-results
         ((result (t2-lists-removal-decrease lib goal facts :ruler-facts)))
         (cons (car result) (cadr result))))
       ((or (proof-is-call actual *library-car*) (proof-is-call actual *library-cdr*))
        (proof-with-checked-results
         ((result (t2-guarded-selectors-context-selector-decrease lib goal facts)))
         (cons (car result) lib)))
       (t
        (proof-with-checked-results ((result (t2-guarded-selectors-guarded-decrease lib goal facts)))
          (if (car result)
              (cons (car result) lib)
            (proof-with-checked-results
             ((head (proof-term-at actual 0))
              (text (proof-write head)))
             *t2-tactics-unsupported-recipe*))))))))))

(defun t2-tactics-unweighted-decrease (lib goal child parent facts)
  (cond
   ((proof-is-call parent *t2-arithmetic-nfix*)
    (proof-with-checked-results
     ((result (t2-arithmetic-clipped-decrease lib goal facts)))
     (cons (car result) (cadr result))))
   ((proof-is-call parent *library-count*)
    (t2-tactics-count-decrease lib goal child parent facts))
   ((proof-is-call parent *proof-plus*)
    (proof-with-checked-results ((result (t2-lists-sum-decrease lib goal facts)))
      (cons (car result) lib)))
   ((proof-is-call parent *library-len*)
    (proof-with-checked-results ((result (t2-lists-split-decrease lib goal facts :ruler-facts)))
      (cons (car result) (cadr result))))
   (t *t2-tactics-unsupported-recipe*)))

(defun t2-tactics-fixed-absolute-reduction (lib clause child parent facts)
  (proof-with-checked-results
   ((small (t2-tactics-countdown-fixed-absolute-count lib child facts))
    (large (t2-tactics-countdown-fixed-absolute-count (cadr small) parent (caddr small)))
    (small-first (proof-step-first (car small)))
    (small-count (proof-term-at small-first 2))
    (large-first (proof-step-first (car large)))
    (large-count (proof-term-at large-first 2)))
   (let ((simpler (append (butlast clause 1) (list (list *proof-ordinal-less* small-count large-count)))))
     (list :fixed-absolute (car small) (car large) simpler (cadr large)))))

(defund t2-tactics-generator-decrease-recipe (lib clause tests)
  (proof-with-checked-results
   ((goal (proof-term-at clause (nfix (1- (len clause)))))
    (facts (t2-tactics-ruler-facts-init lib tests nil))
    (direct (t2-tactics-direct-builtin lib clause goal facts)))
   (if (car direct)
       (cons (car direct) lib)
     (proof-with-checked-results
      ((goal (proof-list-of-length goal 3))
       (child (cadr goal))
       (parent (caddr goal))
       (facts (cdr direct))
       (weighted (t2-phase-weighted-measure child))
       (weighted (and weighted (t2-phase-weighted-measure parent))))
      (if weighted
          (proof-with-checked-results
           ((result (t2-phase-weighted-decrease lib goal facts)))
           (cons (caar result) (cdr result)))
        (proof-with-checked-results
         ((absolute (t2-tactics-fixed-absolute-p child))
          (absolute (and absolute (t2-tactics-fixed-absolute-p parent))))
         (if absolute
             (t2-tactics-fixed-absolute-reduction lib clause child parent facts)
           (t2-tactics-unweighted-decrease lib goal child parent facts))))))))

(defun t2-tactics-generator-decrease-visit (n lib clause tests)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "fuel" "t2-tactics-generator-decrease-visit")
    (let ((result (t2-tactics-generator-decrease-recipe lib clause tests)))
      (if (eq (car result) :fixed-absolute)
          (proof-with-checked-results
           ((proof (t2-tactics-generator-decrease-visit (1- n) (car (cddddr result)) (cadddr result) tests))
            (lib (cdr proof))
            (step (library-library-transport-argument lib (car proof) (cadr result) 1))
            (step (library-library-transport-argument lib step (caddr result) 2)))
           (cons step lib))
        result))))

(defun t2-tactics-generator-decrease (generator clause tests)
  (proof-with-checked-results
   ((result (t2-tactics-generator-decrease-visit
             1000000 (t2-tactics-generator-lib generator) clause tests)))
   (cons (car result) (t2-tactics-generator-with-lib generator (cdr result)))))

(defun t2-tactics-generator-init (measures)
  (proof-with-checked-results
   ((lib (t2-arithmetic-arithmetic-build (library-library-init (proof-proof-init)))))
   (t2-tactics-generator-make measures lib 0)))

(defun t2-tactics-prior-proof (prior clause)
  (if (endp prior)
      nil
    (let* ((candidate (car prior))
           (literals (proof-step-clause (cadr candidate))))
      (if (subsetp-equal (remove-equal *proof-false* literals) clause)
          candidate
        (t2-tactics-prior-proof (cdr prior) clause)))))

(defun t2-tactics-prove-case-step (generator clause call)
  (if call
      (t2-tactics-generator-decrease generator clause (termination-call-tests call))
    (proof-with-checked-results
     ((literal (proof-term-at clause 0))
      (measure (proof-term-at literal 1)))
     (t2-tactics-generator-ordinal generator measure))))

;; A serial number records the identity of each generated Step.
;; Clauses that reuse a Step also reuse its number.
(defun t2-tactics-prove-case (generator clause call progress)
  (let ((seen (car progress))
        (available (cadr progress))
        (recorded (caddr progress)))
    (if (member-equal clause seen)
        (cons progress generator)
      (let* ((goal (car (last clause)))
             (prior (table-get available goal nil))
             (candidate (t2-tactics-prior-proof prior clause)))
        (if candidate
            (cons (list (cons clause seen) available (cons (cons clause candidate) recorded))
                  generator)
          (let ((result (t2-tactics-prove-case-step generator clause call)))
            (if (failure-p result)
                (cons result generator)
              (let* ((candidate (list (len recorded) (car result)))
                     (available (table-put available goal (append prior (list candidate)))))
                (cons (list (cons clause seen) available (cons (cons clause candidate) recorded))
                      (cdr result))))))))))

(defun t2-tactics-prove-ordinalities (definitions measures progress)
  (if (or (endp definitions) (failure-p (car progress)))
      progress
    (let* ((generator (cdr progress))
           (measure (t2-tactics-required-key measures (caar definitions))))
      (if (failure-p measure)
          (cons measure generator)
        (t2-tactics-prove-ordinalities
         (cdr definitions) measures
         (t2-tactics-prove-case generator (list (list *proof-ordinalp* measure)) nil
                                (car progress)))))))

(defun t2-tactics-prove-calls (calls measures formals progress)
  (if (or (endp calls) (failure-p (car progress)))
      progress
    (let* ((generator (cdr progress))
           (cases (termination-call-cases (list (car calls)) measures formals)))
      (if (failure-p cases)
          (cons cases generator)
        (t2-tactics-prove-calls
         (cdr calls) measures formals
         (t2-tactics-prove-case generator (caar cases) (car calls) (car progress)))))))

(defun t2-tactics-count-proof-uses (cases counts)
  (if (endp cases)
      counts
    (let* ((number (cadar cases))
           (step (caddar cases))
           (uses (table-get counts number nil)))
      (t2-tactics-count-proof-uses (cdr cases)
                                  (table-put counts number
                                               (list step (1+ (if uses (cadr uses) 0))))))))

(defun t2-tactics-name-shared-proof (generator step)
  (let* ((shared (1+ (t2-tactics-generator-shared generator)))
         (lib (t2-tactics-generator-lib generator))
         (generator (t2-tactics-generator-make (t2-tactics-generator-measures generator) lib shared))
         (name (concatenate 'string "CALL-DECREASE-" (decimal-text shared)))
         (result (proof-with-checked-results ((literal (proof-step-first step)))
                   (library-library-lemma lib name literal step (cdr (proof-step-clause step))))))
    (if (failure-p result)
        (cons result generator)
      (cons (library-library-cite result name nil nil)
            (t2-tactics-generator-with-lib generator result)))))

(defun t2-tactics-name-shared-proofs (counts shared generator)
  (if (endp counts)
      (cons shared generator)
    (let* ((entry (car counts))
           (number (car entry))
           (step (cadr entry))
           (uses (caddr entry))
           (lines (and (< 1 uses) (proof-serialize step))))
      (cond
       ((failure-p lines) (cons lines generator))
       ((< 4 (len lines))
        (let ((result (t2-tactics-name-shared-proof generator step)))
          (if (failure-p (car result))
              result
            (t2-tactics-name-shared-proofs
             (cdr counts) (table-put shared number (car result)) (cdr result)))))
       (t (t2-tactics-name-shared-proofs (cdr counts) shared generator))))))

(defun t2-tactics-subsume-cases (proof cases shared)
  (if (endp cases)
      nil
    (let* ((entry (car cases))
           (clause (car entry))
           (step (table-get shared (cadr entry) (caddr entry))))
      (proof-with-checked-results
       ((step (proof-proof-subsume proof step clause))
        (rest (t2-tactics-subsume-cases proof (cdr cases) shared)))
       (cons step rest)))))

(defun t2-tactics-definition-entry (name measures progress)
  (let* ((cases (reverse (caddar progress)))
         (shared (t2-tactics-name-shared-proofs
                  (t2-tactics-count-proof-uses cases nil) nil (cdr progress))))
    (if (failure-p (car shared))
        shared
      (let* ((generator (cdr shared))
             (proof (library-library-proof (t2-tactics-generator-lib generator)))
             (entry (proof-with-checked-results
                     ((proofs (t2-tactics-subsume-cases proof cases (car shared))))
                     (proof-proof-entry "measure" name (cons name (table-values measures)) proofs))))
        (cons entry generator)))))

(defun t2-tactics-generator-prove-definition-attempt (generator rulers definitions measures)
  (let ((initial (proof-with-checked-results
                  ((definition (proof-term-at definitions 0))
                   (name (proof-term-at definition 0))
                   (formals (termination-formals definitions nil nil)))
                  (list name formals))))
    (if (failure-p initial)
        (cons initial generator)
      (let* ((progress (t2-tactics-prove-ordinalities
                        definitions measures (cons (list nil nil nil) generator)))
             (progress
              (if (failure-p (car progress))
                  progress
                (let ((calls (termination-recursive-calls rulers definitions)))
                  (if (failure-p calls)
                      (cons calls (cdr progress))
                    (t2-tactics-prove-calls calls measures (cadr initial) progress))))))
        (if (failure-p (car progress))
            progress
          (t2-tactics-definition-entry (car initial) measures progress))))))

(defun t2-tactics-generator-prove-definition (generator rulers definitions measures)
  (let ((result (t2-tactics-generator-prove-definition-attempt generator rulers definitions measures)))
    (if (failure-p (car result)) (car result) result)))

(defun t2-tactics-common-lisp-name-p (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((parts (proof-list-of-length (car definitions) 3))
      (package (proof-term-at (car parts) 1)))
     (or (equal package "COMMON-LISP") (t2-tactics-common-lisp-name-p (cdr definitions))))))

(defun t2-tactics-generator-prove-attempt (generator kind data)
  (if (not (equal kind "define"))
      (cons *t2-tactics-unsupported-recipe* generator)
    (let* ((definitions (cdr data))
           (plan (proof-with-checked-results
                  ((common-lisp (t2-tactics-common-lisp-name-p definitions)))
                  (if common-lisp
                      *t2-tactics-unsupported-recipe*
                    (proof-with-checked-results
                     ((rulers (proof-term-at data 0))
                      (measures (t2-tactics-generator-measures-for generator definitions)))
                     (cons rulers measures))))))
      (if (failure-p plan)
          (cons plan generator)
        (t2-tactics-generator-prove-definition-attempt generator (car plan) definitions (cdr plan))))))

