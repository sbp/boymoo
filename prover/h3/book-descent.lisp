(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-book-descent-zp* (proof-sym "ZP" "ACL2"))
(defconst *h3-book-descent-selectors* (list *library-car* *library-cdr*))
(defconst *h3-book-descent-transparent*
  (list (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "EQ")
        (proof-cl "EQL") *proof-not* (proof-cl "NULL") (proof-cl "=")
        *h3-book-descent-zp* *library-natp* (proof-sym "POSP" "ACL2")
        (proof-sym "FORCE" "ACL2") (proof-sym "CASE-SPLIT" "ACL2")
        (proof-sym "SYNP" "ACL2")))
(defconst *h3-book-descent-support*
  '("consp-cons" "CAR-CONS" "CDR-CONS" "DEFAULT-CAR" "DEFAULT-CDR"))
(defconst *h3-book-descent-set-empty* (proof-sym "EMPTYP$INLINE" "SET"))
(defconst *h3-book-descent-set-fix* (proof-sym "SFIX$INLINE" "SET"))
(defconst *h3-book-descent-set-type* (proof-sym "SETP" "SET"))
(defconst *h3-book-descent-set-selectors*
  (list (cons (proof-sym "HEAD$INLINE" "SET")
              (proof-sym "HEAD-COUNT-BUILT-IN" "SET"))
        (cons (proof-sym "TAIL$INLINE" "SET")
              (proof-sym "TAIL-COUNT-BUILT-IN" "SET"))))

(defun h3-book-descent-selector-path-end (actual)
  (if (and (consp (h3-rewrite-arguments actual))
           (consp (cdr actual))
           (member-equal (car actual) *h3-book-descent-selectors*))
      (h3-book-descent-selector-path-end (cadr actual))
    actual))

(defun h3-book-descent-match-descent (actual formal)
  (proof-with-checked-results ((actual (termination-logical-body actual)))
    (cond ((proof-is-call actual *proof-plus*)
           (or (equal (cdr actual) (list *proof-neg-one* formal))
               (equal (cdr actual) (list formal *proof-neg-one*))))
          ((endp (h3-rewrite-arguments actual)) nil)
          ((assoc-equal (car actual) *h3-book-descent-set-selectors*)
           (equal (cadr actual) formal))
          ((member-equal (car actual) *h3-book-descent-selectors*)
           (equal (h3-book-descent-selector-path-end actual) formal))
          (t nil))))

(mutual-recursion
 (defun h3-book-descent-candidates-available (term lib)
   (declare (xargs :measure (acl2-count term)))
   (if (or (atom term) (endp (h3-rewrite-arguments term)))
       t
     (let ((proof (library-library-proof lib)))
       (and (or (assoc-equal (car term) (proof-proof-definitions proof))
                (member-equal (car term) (proof-proof-primitives proof)))
            (h3-book-descent-candidates-available-args (cdr term) lib)))))
 (defun h3-book-descent-candidates-available-args (args lib)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       t
     (and (h3-book-descent-candidates-available (car args) lib)
          (h3-book-descent-candidates-available-args (cdr args) lib)))))

(defun h3-book-descent-definition-names (definitions)
  (if (endp definitions)
      nil
    (proof-with-checked-results
     ((name (proof-term-at (car definitions) 0))
      (rest (h3-book-descent-definition-names (cdr definitions))))
     (cons name rest))))

(defun h3-book-descent-aid-measures (aids lib measures)
  (if (endp aids)
      measures
    (proof-with-checked-results ((record (proof-list-of-length (car aids) 2)))
      (if (equal (car record) "measure")
          (let ((fields (cadr record)))
            (proof-with-checked-results
             ((order (proof-term-at fields 2))
              (measure (if (equal order *proof-ordinal-less*)
                           (proof-term-at fields 1)
                         nil)))
             (if (and (equal order *proof-ordinal-less*)
                      (h3-book-descent-candidates-available measure lib))
                 (proof-with-checked-results ((name (proof-term-at fields 0)))
                   (h3-book-descent-aid-measures
                    (cdr aids) lib (table-put measures name measure)))
               (h3-book-descent-aid-measures (cdr aids) lib measures))))
        (h3-book-descent-aid-measures (cdr aids) lib measures)))))

(defun h3-book-descent-hinted-measures (names measures ordered)
  (if (endp names)
      (list ordered)
    (let ((entry (assoc-equal (car names) measures)))
      (and entry
           (h3-book-descent-hinted-measures
            (cdr names) measures (table-put ordered (car names) (cdr entry)))))))

(defun h3-book-descent-choice-digits (names formals digits)
  (if (endp names)
      digits
    (let ((radix (len (cdr (assoc-equal (car names) formals)))))
      (if (zp radix)
          :none
        (h3-book-descent-choice-digits
         (cdr names) formals (cons (cons 0 radix) digits))))))

(defun h3-book-descent-next-digits (digits)
  (if (endp digits)
      :none
    (let ((next (1+ (caar digits)))
          (radix (cdar digits)))
      (if (< next radix)
          (cons (cons next radix) (cdr digits))
        (let ((rest (h3-book-descent-next-digits (cdr digits))))
          (if (eq rest :none)
              :none
            (cons (cons 0 radix) rest)))))))

(defun h3-book-descent-choice-positions (names digits positions)
  (if (endp names)
      positions
    (h3-book-descent-choice-positions
     (cdr names) (cdr digits) (table-put positions (car names) (caar digits)))))

(defun h3-book-descent-choice-matches (calls positions formals)
  (if (endp calls)
      t
    (let* ((call (car calls))
           (callee (termination-call-callee call))
           (caller (termination-call-caller call))
           (position (assoc-equal callee positions)))
      (if (not position)
          '(:failure "failure" "")
        (proof-with-checked-results
         ((actual (proof-term-at (termination-call-actuals call) (cdr position))))
         (let ((caller-position (assoc-equal caller positions)))
           (if (not caller-position)
               '(:failure "failure" "")
             (proof-with-checked-results
              ((formal (proof-term-at (cdr (assoc-equal caller formals))
                                      (cdr caller-position)))
               (matches (h3-book-descent-match-descent actual formal)))
              (and matches
                   (h3-book-descent-choice-matches (cdr calls) positions formals))))))))))

(defun h3-book-descent-choice-measures (positions formals)
  (if (endp positions)
      nil
    (let* ((name (caar positions))
           (formal (nth (cdar positions) (cdr (assoc-equal name formals)))))
      (cons (cons name (list *library-count* formal))
            (h3-book-descent-choice-measures (cdr positions) formals)))))

(defund h3-book-descent-choice (digits names formals calls)
  (let ((positions (h3-book-descent-choice-positions names (reverse digits) nil)))
    (proof-with-checked-results
     ((matches (h3-book-descent-choice-matches calls positions formals)))
     (and matches (list (h3-book-descent-choice-measures positions formals))))))

(defun h3-book-descent-assumptions (proof tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
     ((pair (proof-list-of-length (car tests) 2))
      (step (proof-proof-assume proof (car pair) (cadr pair)))
      (rest (h3-book-descent-assumptions proof (cdr tests))))
     (cons step rest))))

(defun h3-book-descent-signed-hypotheses (lib call)
  (h3-book-descent-assumptions (library-library-proof lib)
                               (termination-call-tests call)))

(defun h3-book-descent-support-names (names)
  (if (endp names)
      nil
    (cons (if (equal (car names) "consp-cons")
              (car names)
            (proof-sym (car names) "ACL2"))
          (h3-book-descent-support-names (cdr names)))))

(defun h3-book-descent-prove-under-rulers (lib conclusion evidence)
  (proof-with-checked-results
   ((rules (h3-rewrite-rules-init
            lib (h3-book-descent-support-names *h3-book-descent-support*) nil)))
   (car (h3-rewrite-search-prove
         (h3-rewrite-search-init lib *h3-book-descent-transparent* nil rules 20 nil)
         conclusion evidence))))

(defun h3-book-descent-set-selector-start (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((parts (proof-list-of-length (cdr formula) 2))
      (goal (proof-list-of-length (cadr parts) 3))
      (variable (proof-term-at (caddr goal) 1))
      (projection (proof-term-at (cadr goal) 1))
      (head (proof-term-at projection 0))
      (assume (proof-proof-assume proof (car parts) t)))
     (let* ((selector (if (equal head (proof-sym "HEAD$INLINE" "SET"))
                          *library-car*
                        *library-cdr*))
            (empty (list *h3-book-descent-set-empty* variable))
            (setp (list *h3-book-descent-set-type* variable))
            (evidence (list assume))
            (search (h3-rewrite-search-init
                     lib (append *h3-book-descent-transparent*
                                 (list head *h3-book-descent-set-fix*))
                     (list empty) nil 20 nil)))
       (proof-with-checked-results
        ((context (h3-rewrite-search-context search evidence))
         (equality (car (h3-rewrite-search-reduce search projection context nil nil)))
         (target (and equality (proof-rewritten-term equality))))
        (if (not (and equality (equal target (list selector variable))))
            *h3-rewrite-unproved*
          (proof-with-checked-results
           ((is-set (car (h3-rewrite-search-prove
                          (h3-rewrite-search-init
                           lib *h3-book-descent-transparent* (list empty) nil 20 nil)
                          setp evidence)))
            (cons-proof (car (h3-rewrite-search-prove
                              (h3-rewrite-search-init
                               lib *h3-book-descent-transparent* (list setp empty)
                               nil 20 nil)
                              (list *proof-consp* variable) (list assume is-set))))
            (ordinal (library-library-builtin lib (if (equal selector *library-car*) 2 3)
                                               variable))
            (ordinal (proof-proof-discharge proof ordinal cons-proof)))
           (list (car goal) variable (caddr goal) selector equality ordinal (car parts)))))))))

(defun h3-book-descent-set-selector-theorem-with-library (lib formula)
  (let ((start (h3-book-descent-set-selector-start lib formula)))
    (if (failure-p start)
        (cons start lib)
      (let* ((head (car start))
             (variable (cadr start))
             (larger (caddr start))
             (selector (cadddr start))
             (equality (nth 4 start))
             (ordinal (nth 5 start))
             (guard (nth 6 start))
             (arithmetic (if (equal head *proof-less*) (h3-merges-arithmetic lib) lib)))
        (if (failure-p arithmetic)
            (cons arithmetic lib)
          (let* ((lib arithmetic)
                 (proof (library-library-proof lib)))
            (cons
             (proof-with-checked-results
              ((ordinal (if (equal head *proof-less*)
                            (proof-with-checked-results
                             ((comparison (library-library-ordinal-comparison
                                           lib (list *library-count* (list selector variable))
                                           larger)))
                             (proof-proof-rewrite proof ordinal comparison '(1)))
                          ordinal))
               (symmetric (proof-proof-symmetric proof equality))
               (goal-proof (proof-proof-rewrite proof ordinal symmetric '(1 1 1))))
              (h3-rewrite-implication lib guard goal-proof))
             lib)))))))

(defun h3-book-descent-set-fix-type (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
     ((fixing (proof-term-at formula 1))
      (variable (proof-term-at fixing 1))
      (empty (list *h3-book-descent-set-empty* variable))
      (nonempty (proof-proof-assume proof empty nil))
      (type-given (car (h3-rewrite-search-prove
                        (h3-rewrite-search-init lib *h3-book-descent-transparent*
                                                (list empty) nil 150 nil)
                        (list *h3-book-descent-set-type* variable) (list nonempty))))
      (nil-goal (list *h3-book-descent-set-type* *proof-false*))
      (nil-type (car (h3-rewrite-search-prove
                      (h3-rewrite-search-init lib *h3-book-descent-transparent*
                                              (list nil-goal) nil 150 nil)
                      nil-goal nil)))
      (simplifier (h3-rewrite-search-init lib nil (list fixing) nil 150 nil))
      (empty-step (proof-proof-assume proof empty t))
      (yes-context (h3-rewrite-search-context simplifier (list empty-step)))
      (yes (h3-rewrite-search-reduce simplifier fixing yes-context nil nil))
      (yes-equality (car yes))
      (simplifier (cadr yes))
      (no-context (h3-rewrite-search-context simplifier (list nonempty)))
      (no (car (h3-rewrite-search-reduce simplifier fixing no-context nil nil)))
      (yes-proof (library-library-transport-argument lib nil-type yes-equality 1))
      (no-proof (library-library-transport-argument lib type-given no 1)))
     (proof-proof-cases proof empty yes-proof no-proof))))

(defun h3-book-descent-length-edge-with-library (lib smaller larger evidence)
  (if (not (and (proof-is-call smaller *library-len*)
                (proof-is-call larger *library-len*)))
      (cons nil lib)
    (let ((terms (proof-with-checked-results
                  ((child (proof-term-at smaller 1))
                   (parent (proof-term-at larger 1)))
                  (list child parent))))
      (cond
       ((failure-p terms) (cons terms lib))
       ((not (equal (car terms) (list *library-cdr* (cadr terms)))) (cons nil lib))
       (t
        (let ((arithmetic (h3-merges-arithmetic lib)))
          (if (failure-p arithmetic)
              (cons arithmetic lib)
            (let ((parent (cadr terms)))
              (cons
               (proof-with-checked-results
                ((consp-step (h3-book-descent-prove-under-rulers
                              arithmetic (list *proof-consp* parent) evidence)))
                (library-library-cite arithmetic "LEN-CDR-LESS"
                                      (list parent) (list consp-step)))
               arithmetic)))))))))

(defun h3-book-descent-use-set-selector (lib name parent guard)
  (cons
   (proof-with-checked-results
    ((fact (proof-proof-fact (library-library-proof lib) name
                             (list (list *library-x* parent)))))
    (h3-rewrite-apply-implication lib fact guard))
   lib))

(defun h3-book-descent-set-selector-decrease-with-library (lib actual parent evidence)
  (let ((selector (and (consp (h3-rewrite-arguments actual))
                       (assoc-equal (car actual) *h3-book-descent-set-selectors*))))
    (if (not (and selector (equal (cadr actual) parent)))
        (cons nil lib)
      (let* ((name (cdr selector))
             (facts (proof-proof-facts (library-library-proof lib)))
             (guard (h3-book-descent-prove-under-rulers
                     lib (proof-neg (list *h3-book-descent-set-empty* parent)) evidence)))
        (cond
         ((failure-p guard) (cons guard lib))
         ((assoc-equal name facts)
          (h3-book-descent-use-set-selector lib name parent guard))
         (t
          (let* ((label (concatenate 'string "H3-BOOK-SET-" (caddr name)))
                 (name (proof-sym (concatenate 'string "SELF-" label) "ACL2")))
            (if (assoc-equal name facts)
                (h3-book-descent-use-set-selector lib name parent guard)
              (let* ((conclusion (list *proof-ordinal-less*
                                       (list *library-count* (list (car actual) *library-x*))
                                       (list *library-count* *library-x*)))
                     (formula (list *library-implies*
                                    (proof-neg (list *h3-book-descent-set-empty* *library-x*))
                                    conclusion))
                     (theorem (h3-book-descent-set-selector-theorem-with-library lib formula))
                     (lib (cdr theorem))
                     (updated (if (failure-p (car theorem))
                                  (car theorem)
                                (library-library-lemma lib label formula (car theorem) nil))))
                (if (failure-p updated)
                    (cons updated lib)
                  (h3-book-descent-use-set-selector updated name parent guard)))))))))))

(defun h3-book-descent-empty-count-with-library (lib parent evidence)
  (let ((arithmetic (h3-merges-arithmetic lib)))
    (if (failure-p arithmetic)
        (cons arithmetic lib)
      (let* ((lib arithmetic)
             (proof (library-library-proof lib))
             (whole (list *library-count* parent))
             (tail (list *library-count* (list *library-cdr* parent))))
        (cons
         (proof-with-checked-results
          ((consp-step (h3-book-descent-prove-under-rulers
                        lib (list *proof-consp* parent) evidence))
           (builtin (library-library-builtin lib 3 parent))
           (decreases (proof-proof-discharge proof builtin consp-step))
           (comparison (library-library-ordinal-comparison lib tail whole))
           (strict (proof-proof-rewrite proof decreases comparison '(1)))
           (natural (library-library-natural lib tail))
           (nonnegative (library-library-cite lib "NATURAL-NONNEGATIVE"
                                              (list tail) (list natural)))
           (first (proof-step-first nonnegative)))
          (if (not (equal first (library-le *proof-zero* tail)))
              '(:failure "proof-mismatch" "")
            (proof-with-checked-results
             ((bound (library-library-compare-chain lib nonnegative strict))
              (empty (list *library-count* *proof-false*))
              (reduced (car (h3-rewrite-search-reduce
                             (h3-rewrite-search-init lib nil (list empty) nil 150 nil)
                             empty nil nil nil)))
              (bound (library-library-transport-argument lib bound reduced 1))
              (comparison (library-library-ordinal-comparison lib empty whole)))
             (proof-proof-transport proof bound comparison))))
         lib)))))

(defun h3-book-descent-count-selector (lib actual parent evidence call)
  (let ((consp-step (h3-book-descent-prove-under-rulers
                     lib (list *proof-consp* parent) evidence)))
    (if (failure-p consp-step)
        (cons consp-step lib)
      (let* ((child (proof-term-at actual 1))
             (arithmetic (cond ((failure-p child) child)
                               ((equal child parent) lib)
                               (t (h3-merges-arithmetic lib)))))
        (if (failure-p arithmetic)
            (cons arithmetic lib)
          (let ((lib arithmetic)
                (goal (list *proof-ordinal-less* (list *library-count* actual)
                            (list *library-count* parent))))
            (cons
             (proof-with-checked-results
              ((hypotheses (descent-hypotheses-init
                            lib (termination-call-tests call)
                            (append evidence (list consp-step))))
               (decrease (descent-selector-decrease lib goal hypotheses)))
              (car decrease))
             lib)))))))

(defun h3-book-descent-count-decrease-with-library (lib actual parent evidence call)
  (if (equal actual *proof-false*)
      (h3-book-descent-empty-count-with-library lib parent evidence)
    (let* ((set-decrease (h3-book-descent-set-selector-decrease-with-library
                          lib actual parent evidence))
           (lib (cdr set-decrease)))
      (if (car set-decrease)
          set-decrease
        (let ((matches (h3-book-descent-match-descent actual parent)))
          (cond
           ((failure-p matches) (cons matches lib))
           ((not matches) (cons *h3-rewrite-unproved* lib))
           ((proof-is-call actual *proof-plus*)
            (cons
             (proof-with-checked-results
              ((passing (h3-book-descent-prove-under-rulers
                         lib (proof-neg (list *h3-book-descent-zp* parent)) evidence))
               (first (proof-term-at actual 1))
               (builtin (library-library-builtin
                         lib (if (equal first *proof-neg-one*) 9 8) parent)))
              (proof-proof-discharge (library-library-proof lib) builtin passing))
             lib))
           (t (h3-book-descent-count-selector lib actual parent evidence call))))))))

(defun h3-book-descent-measure-edge-with-library (lib smaller larger evidence call)
  (cond
   ((and (proof-is-call smaller *library-len*) (proof-is-call larger *library-len*))
    (h3-book-descent-length-edge-with-library lib smaller larger evidence))
   ((not (and (proof-is-call smaller *library-count*) (proof-is-call larger *library-count*)))
    (cons nil lib))
   (t
    (let ((terms (proof-with-checked-results
                  ((child (proof-term-at smaller 1))
                   (parent (proof-term-at larger 1))
                   (matches (h3-book-descent-match-descent child parent)))
                  (and matches (list child parent)))))
      (cond
       ((failure-p terms) (cons terms lib))
       ((not terms) (cons nil lib))
       (t
        (let ((arithmetic (h3-merges-arithmetic lib)))
          (if (failure-p arithmetic)
              (cons arithmetic lib)
            (let* ((decrease (h3-book-descent-count-decrease-with-library
                              arithmetic (car terms) (cadr terms) evidence call))
                   (lib (cdr decrease))
                   (proof (library-library-proof lib)))
              (cons
               (proof-with-checked-results
                ((step (car decrease))
                 (ordinal (library-library-ordinal-comparison lib smaller larger))
                 (step (proof-proof-rewrite proof step ordinal '(1))))
                (proof-proof-tidy proof step))
               lib))))))))))

(defund h3-book-descent-additive-edge (new old index previous accumulated lib evidence call)
  (let* ((edge (h3-book-descent-measure-edge-with-library lib new old evidence call))
         (step (car edge))
         (lib (cdr edge)))
    (if (or (not step) (failure-p step))
        edge
      (let* ((index-offset (- 1 index))
             (index-offset (if (< index-offset 0) (+ (len previous) index-offset) index-offset))
             (shifted (if (and (<= 0 index-offset) (< index-offset (len previous)))
                          (descent-shift-with-library lib step (nth index-offset previous)
                                                      (equal index 1))
                        '(:failure "failure" ""))))
        (if (failure-p shifted)
            (cons shifted lib)
          (let ((lib (cdr shifted)))
            (cons (if accumulated
                      (library-library-compare-chain lib (car shifted) accumulated)
                    (car shifted))
                  lib)))))))

(defun h3-book-descent-additive-edges (new old index previous accumulated lib evidence call)
  (declare (xargs :measure (acl2-count new)))
  (if (or (endp new) (endp old))
      (cons accumulated lib)
    (let* ((same (equal (car new) (car old)))
           (edge (if same
                     (cons accumulated lib)
                   (h3-book-descent-additive-edge
                    (car new) (car old) index previous accumulated lib evidence call))))
      (if (and (not same) (or (not (car edge)) (failure-p (car edge))))
          edge
        (h3-book-descent-additive-edges
         (cdr new) (cdr old) (1+ index)
         (if same previous (update-nth index (car new) previous))
         (car edge) (cdr edge) evidence call)))))

(defun h3-book-descent-additive-descent-with-library (lib goal evidence call)
  (let ((parts (proof-list-of-length goal 3)))
    (cond
     ((failure-p parts) (cons parts lib))
     ((not (and (proof-is-call (cadr parts) *proof-plus*)
                (proof-is-call (caddr parts) *proof-plus*)))
      (cons nil lib))
     (t
      (let* ((before (cadr parts))
             (after (caddr parts))
             (edge (h3-book-descent-additive-edges
                    (cdr before) (cdr after) 0 (cdr after) nil lib evidence call))
             (step (car edge))
             (lib (cdr edge)))
        (if (or (not step) (failure-p step))
            edge
          (cons
           (proof-with-checked-results
            ((ordinal (library-library-ordinal-comparison lib before after)))
            (proof-proof-transport (library-library-proof lib) step ordinal))
           lib)))))))

(defun h3-book-descent-prove-normalized-descent-leaf
    (value tests lib parent evidence call)
  (let ((assumptions (h3-book-descent-assumptions (library-library-proof lib) tests)))
    (if (failure-p assumptions)
        (cons assumptions lib)
      (h3-book-descent-count-decrease-with-library
       lib value parent (append evidence assumptions) call))))

(defun h3-book-descent-by-value (n lib value template tests parent evidence call)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) (cons '(:failure "fuel" "h3-book-descent-by-value") lib))
   ((proof-is-call value *proof-if*)
    (let ((branches (proof-list-of-length (cdr value) 3)))
      (if (failure-p branches)
          (cons branches lib)
        (let* ((test (car branches))
               (yes (h3-book-descent-by-value
                     (1- n) lib (cadr branches) template
                     (append tests (list (list test t))) parent evidence call)))
          (if (failure-p (car yes))
              yes
            (let ((no (h3-book-descent-by-value
                       (1- n) (cdr yes) (caddr branches) template
                       (append tests (list (list test nil))) parent evidence call)))
              (if (failure-p (car no))
                  no
                (cons (proof-by-value-join
                       (library-library-proof (cdr no)) value template (car yes) (car no))
                      (cdr no)))))))))
   ((and (proof-compound value) (endp value))
    (cons '(:failure "failure" "") lib))
   ((and (proof-compound value) (proof-compound (car value)))
    (let* ((proof (library-library-proof lib))
           (equality (proof-proof-beta proof value))
           (opened (if (failure-p equality) equality (proof-rewritten-term equality))))
      (if (failure-p opened)
          (cons opened lib)
        (let* ((step (h3-book-descent-by-value
                      (1- n) lib opened template tests parent evidence call))
               (lib (cdr step))
               (proof (library-library-proof lib)))
          (cons
           (proof-with-checked-results
            ((step (car step))
             (symmetric (proof-proof-symmetric proof equality)))
            (proof-proof-rewrite-result proof step symmetric template *proof-result*))
           lib)))))
   (t
    (let ((step (h3-book-descent-prove-normalized-descent-leaf
                 value tests lib parent evidence call)))
      (cons
       (proof-with-checked-results
        ((literal (if (failure-p (car step)) (car step) (proof-step-first (car step))))
         (target (proof-subst template (list (cons *proof-result* value)))))
        (if (equal literal target) (car step) '(:failure "proof-mismatch" "")))
       (cdr step))))))

(defun h3-book-descent-normalize-count (lib smaller larger evidence call)
  (let ((terms
         (proof-with-checked-results
          ((parent (proof-term-at larger 1))
           (child (proof-term-at smaller 1))
           (search (h3-rewrite-search-init lib (list (proof-sym "HARD-ERROR" "ACL2"))
                                           nil nil 150 t))
           (context (h3-rewrite-search-context search evidence))
           (equality (car (h3-rewrite-search-reduce search child context nil nil)))
           (actual (if equality (proof-rewritten-term equality) child)))
          (list parent actual equality))))
    (if (failure-p terms)
        (cons terms lib)
      (let* ((parent (car terms))
             (actual (cadr terms))
             (equality (caddr terms))
             (template (list *proof-ordinal-less* (list *library-count* *proof-result*) larger))
             (step (if (proof-is-call actual *proof-if*)
                       (h3-book-descent-by-value
                        1000000 lib actual template nil parent evidence call)
                     (h3-book-descent-prove-normalized-descent-leaf
                      actual nil lib parent evidence call))))
        (if (or (not equality) (failure-p (car step)))
            step
          (let ((proof (library-library-proof (cdr step))))
            (cons
             (proof-with-checked-results ((symmetric (proof-proof-symmetric proof equality)))
               (proof-proof-rewrite-result proof (car step) symmetric template *proof-result*))
             (cdr step))))))))

(defun h3-book-descent-ordinality (lib clause goal)
  (let ((direct (descent-direct-builtin lib clause nil)))
    (cond
     ((failure-p direct) (cons direct lib))
     ((car direct) (cons (car direct) lib))
     (t
      (let ((arithmetic (h3-merges-arithmetic lib)))
        (if (failure-p arithmetic)
            (cons arithmetic lib)
          (let ((step
                 (proof-with-checked-results ((measure (proof-term-at goal 1)))
                   (descent-measure-ordinal-with-library arithmetic measure))))
            (if (failure-p step) (cons step arithmetic) step))))))))

(defun h3-book-descent-length-or-additive (lib goal smaller larger evidence call)
  (let* ((edge (h3-book-descent-length-edge-with-library lib smaller larger evidence))
         (lib (cdr edge)))
    (cond
     ((failure-p (car edge)) edge)
     ((car edge)
      (cons
       (proof-with-checked-results
        ((comparison (library-library-ordinal-comparison lib smaller larger)))
        (proof-proof-transport (library-library-proof lib) (car edge) comparison))
       lib))
     (t
      (let ((additive (h3-book-descent-additive-descent-with-library lib goal evidence call)))
        (if (car additive)
            additive
          (cons *h3-rewrite-unproved* (cdr additive))))))))

(defun h3-book-descent-prove-normalized-descent-with-library (lib clause call)
  (if (endp clause)
      (cons '(:failure "failure" "") lib)
    (let ((goal (car (last clause))))
      (if (not call)
          (h3-book-descent-ordinality lib clause goal)
        (let ((prepared
               (proof-with-checked-results
                ((evidence (h3-book-descent-signed-hypotheses lib call))
                 (hypotheses (descent-hypotheses-init lib (termination-call-tests call) evidence))
                 (direct (descent-direct-builtin lib clause hypotheses)))
                (list (car direct) evidence))))
          (cond
           ((failure-p prepared) (cons prepared lib))
           ((car prepared) (cons (car prepared) lib))
           (t
            (let ((parts (proof-list-of-length goal 3))
                  (evidence (cadr prepared)))
              (cond
               ((failure-p parts) (cons parts lib))
               ((and (proof-is-call (caddr parts) *library-count*)
                     (proof-is-call (cadr parts) *library-count*))
                (h3-book-descent-normalize-count lib (cadr parts) (caddr parts) evidence call))
               (t
                (h3-book-descent-length-or-additive
                 lib goal (cadr parts) (caddr parts) evidence call)))))))))))

(defun h3-book-descent-measure-head-p (head)
  (or (equal head *library-count*) (equal head *library-len*) (equal head *proof-plus*)))

(defun h3-book-descent-normalizations (terms index proof)
  (if (endp terms)
      (cons nil nil)
    (let* ((term (car terms))
           (head (car term)))
      (proof-with-checked-results
       ((equality (if (and (consp (h3-rewrite-arguments term))
                           (not (h3-book-descent-measure-head-p head))
                           (assoc-equal head (proof-proof-definitions proof)))
                      (proof-proof-unfold proof term)
                    nil))
        (target (if equality (proof-rewritten-term equality) nil))
        (rest (h3-book-descent-normalizations (cdr terms) (1+ index) proof)))
       (if (and equality (proof-compound target) (h3-book-descent-measure-head-p (car target)))
           (cons (cons target (car rest)) (cons (list index equality) (cdr rest)))
         (cons (cons term (car rest)) (cdr rest)))))))

(defund h3-book-descent-restore-normalization (proof step normalization)
  (proof-with-checked-results
   ((symmetric (proof-proof-symmetric proof (cadr normalization))))
   (proof-proof-rewrite proof step symmetric (list 1 (car normalization)))))

(defun h3-book-descent-restore-normalizations (proof step normalizations)
  (declare (xargs :measure (acl2-count normalizations)))
  (if (endp normalizations)
      step
    (proof-with-checked-results
     ((step (h3-book-descent-restore-normalization proof step (car normalizations))))
     (h3-book-descent-restore-normalizations proof step (cdr normalizations)))))

(defun h3-book-descent-prove-descent-with-library (lib clause call)
  (if (endp clause)
      (cons '(:failure "failure" "") lib)
    (let* ((goal (car (last clause)))
           (normalizations
            (if (integerp goal)
                '(:failure "failure" "")
              (h3-book-descent-normalizations (cdr goal) 1 (library-library-proof lib)))))
      (if (failure-p normalizations)
          (cons normalizations lib)
        (let* ((new-goal (and (consp goal) (cons (car goal) (car normalizations))))
               (clause (append (butlast clause 1) (list new-goal)))
               (result (h3-book-descent-prove-normalized-descent-with-library lib clause call)))
          (if (failure-p (car result))
              result
            (cons (h3-book-descent-restore-normalizations
                   (library-library-proof (cdr result)) (car result) (cdr normalizations))
                  (cdr result))))))))

(defun h3-book-descent-retryable-p (value)
  (and (failure-p value)
       (member-equal (cadr value) '("unproved" "proof-mismatch" "value" "key" "assertion"))))

(defun h3-book-descent-proof-exceeds-clause (literals clause)
  (if (endp literals)
      nil
    (or (and (not (equal (car literals) *proof-false*))
             (not (member-equal (car literals) clause)))
        (h3-book-descent-proof-exceeds-clause (cdr literals) clause))))

(defund h3-book-descent-try-clause (lib record seen proofs)
  (let ((clause (car record))
        (call (cadr record)))
    (if (member-equal clause seen)
        (cons (list seen proofs) lib)
      (let* ((result (h3-book-descent-prove-descent-with-library lib clause call))
             (step (car result))
             (lib (cdr result)))
        (cond
         ((h3-book-descent-retryable-p step) (cons nil lib))
         ((failure-p step) result)
         ((h3-book-descent-proof-exceeds-clause (proof-step-clause step) clause)
          (cons nil lib))
         (t
          (cons
           (proof-with-checked-results
            ((subsumed (proof-proof-subsume (library-library-proof lib) step clause)))
            (list (cons clause seen) (cons subsumed proofs)))
           lib)))))))

(defund h3-book-descent-try-call (lib call measures formals seen proofs)
  (let ((record (termination-call-cases (list call) measures formals)))
    (if (failure-p record)
        (cons record lib)
      (h3-book-descent-try-clause lib (car record) seen proofs))))

(defun h3-book-descent-try-call-cases (lib calls measures formals seen proofs)
  (declare (xargs :measure (acl2-count calls)))
  (if (endp calls)
      (cons (list seen proofs) lib)
    (let ((result (h3-book-descent-try-call lib (car calls) measures formals seen proofs)))
      (if (or (not (car result)) (failure-p (car result)))
          result
        (h3-book-descent-try-call-cases
         (cdr result) (cdr calls) measures formals (caar result) (cadar result))))))

(defund h3-book-descent-try-ordinality (lib definition measures seen proofs)
  (let ((record (termination-ordinality-cases (list definition) measures)))
    (if (failure-p record)
        (cons record lib)
      (h3-book-descent-try-clause lib (car record) seen proofs))))

(defun h3-book-descent-try-ordinality-cases (lib definitions calls measures formals seen proofs)
  (declare (xargs :measure (acl2-count definitions)))
  (if (endp definitions)
      (h3-book-descent-try-call-cases lib calls measures formals seen proofs)
    (let ((result (h3-book-descent-try-ordinality lib (car definitions) measures seen proofs)))
      (if (or (not (car result)) (failure-p (car result)))
          result
        (h3-book-descent-try-ordinality-cases
         (cdr result) (cdr definitions) calls measures formals (caar result) (cadar result))))))

(defun h3-book-descent-ordered-measure-terms (names measures)
  (if (endp names)
      nil
    (cons (cdr (assoc-equal (car names) measures))
          (h3-book-descent-ordered-measure-terms (cdr names) measures))))

(defund h3-book-descent-try-measures (lib definitions calls names measures proof-entry)
  (let ((formals (termination-formals definitions nil nil)))
    (if (failure-p formals)
        (cons formals lib)
      (let ((result (h3-book-descent-try-ordinality-cases
                     lib definitions calls measures formals nil nil)))
        (if (or (not (car result)) (failure-p (car result)))
            result
          (let ((first (car names)))
            (cons
             (cond
              ((endp names) '(:failure "failure" ""))
              ((eq proof-entry :proof-entry)
               (proof-proof-entry "measure" first
                                  (cons first (h3-book-descent-ordered-measure-terms names measures))
                                  (reverse (cadar result))))
              (t '(:failure "failure" "")))
             (cdr result))))))))

(defun h3-book-descent-termination-choices
    (remaining digits lib definitions calls names formals proof-entry)
  (declare (xargs :measure (nfix remaining)))
  (if (or (zp remaining) (eq digits :none))
      (cons *h3-rewrite-unproved* lib)
    (let ((choice (h3-book-descent-choice digits names formals calls)))
      (if (failure-p choice)
          (cons choice lib)
        (let ((result (if choice
                          (h3-book-descent-try-measures
                           lib definitions calls names (car choice) proof-entry)
                        (cons nil lib))))
          (if (car result)
              result
            (h3-book-descent-termination-choices
             (1- remaining) (h3-book-descent-next-digits digits) (cdr result)
             definitions calls names formals proof-entry)))))))

(defun h3-book-descent-termination-proof-with-library (lib fields aids proof-entry)
  (if (endp fields)
      (cons '(:failure "failure" "") lib)
    (let* ((definitions (cdr fields))
           (calls (termination-recursive-calls (car fields) definitions)))
      (cond
       ((failure-p calls) (cons calls lib))
       ((endp calls) (cons *h3-rewrite-unproved* lib))
       (t
        (let ((plan
               (proof-with-checked-results
                ((names (h3-book-descent-definition-names definitions))
                 (formals (termination-formals definitions t nil))
                 (measures (h3-book-descent-aid-measures aids lib nil)))
                (list names formals (h3-book-descent-hinted-measures names measures nil)))))
          (if (failure-p plan)
              (cons plan lib)
            (let* ((names (car plan))
                   (formals (cadr plan))
                   (hinted (caddr plan))
                   (result (if hinted
                               (h3-book-descent-try-measures
                                lib definitions calls names (car hinted) proof-entry)
                             (cons nil lib))))
              (if (car result)
                  result
                (h3-book-descent-termination-choices
                 250 (h3-book-descent-choice-digits names formals nil) (cdr result)
                 definitions calls names formals proof-entry))))))))))

