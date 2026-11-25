(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-accumulator-count-cells* (proof-sym "ACL2-COUNT-CAR-CDR-LINEAR" "ACL2"))

(defun h4-book-accumulator-atomic-arguments (args)
  (if (endp args)
      t
    (and (not (proof-compound (car args))) (h4-book-accumulator-atomic-arguments (cdr args)))))

(defun h4-book-accumulator-reverse-accumulator-shape (formula)
  (if (not (proof-is-call formula *proof-equal*))
      nil
    (proof-with-checked-results ((tail (proof-term-at formula 2)))
      (if (not (proof-is-call tail *h4-book-flatten-revappend*))
          nil
        (proof-with-checked-results
            ((parts (proof-list-of-length (cdr formula) 2))
             (arguments (proof-list-of-length tail 3)))
          (let ((executable (car parts))
                (accumulator (cadr arguments))
                (logical (caddr arguments)))
            (if (not (and (proof-compound executable) (proof-compound logical) (<= 2 (len logical))))
                nil
              (proof-with-checked-results ((head (proof-term-at executable 0)))
                (if (or (proof-compound head) (proof-compound (car logical)))
                    nil
                  (let ((args (append (cdr logical) (list accumulator))))
                    (and (equal (cdr executable) args)
                         (not (equal head (car logical)))
                         (no-duplicatesp-equal args)
                         (h4-book-accumulator-atomic-arguments args)
                         (list executable logical accumulator))))))))))))

(defun h4-book-accumulator-opened-call (p term tests)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((initial (proof-proof-unfold proof term))
         (body (proof-rewritten-term initial))
         (normalized (h4-tactics-tactics-normalize p body tests *h4-book-flatten-logic* nil nil)))
      (proof-proof-chain proof initial (list normalized)))))

(defun h4-book-accumulator-count-cells (p cells shape)
  (proof-with-checked-results
      ((view (proof-proof-fact (library-library-proof p) *h4-book-accumulator-count-cells*
                               (list (list *library-x* cells)))))
    (h4-tactics-tactics-modus-ponens p view shape)))

(defun h4-book-accumulator-mapped-count (p term equation)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((pair (proof-rewritten-term equation)))
      (if (not (proof-is-call pair *proof-cons*))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((shape (proof-proof-fact proof "consp-cons"
                                      (seq-zip (list *library-x* *library-y*) (cdr pair))))
             (count (h4-book-accumulator-count-cells p pair shape))
             (head (library-library-axiom p "CAR-CONS" (cdr pair)))
             (count (proof-proof-rewrite proof count head '(1 2 2 1 1)))
             (tail (library-library-axiom p "CDR-CONS" (cdr pair)))
             (count (proof-proof-rewrite proof count tail '(1 2 2 2 1)))
             (opened (h4-book-flatten-rewrite-argument p (list *library-count* term) 1 equation)))
          (proof-proof-chain proof opened (list count)))))))

(defun h4-book-accumulator-count-pair-bound-merge (p left right total strict)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((left-count (proof-rewritten-term left))
         (right-count (proof-rewritten-term right))
         (merged (if strict
                     (library-library-less-from-difference p left-count right-count total nil)
                   (library-library-weak-from-difference p left-count right-count total nil)))
         (reversed-left (proof-proof-symmetric proof left))
         (merged (proof-proof-rewrite proof merged reversed-left (if strict '(1 1) '(1 1 2))))
         (reversed-right (proof-proof-symmetric proof right)))
      (proof-proof-rewrite proof merged reversed-right (if strict '(1 2) '(1 1 1))))))

(defun h4-book-accumulator-count-pair-bound-strict (p a b da db left-head weak-tail)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((comparison (library-library-comparison p a b nil))
         (head (proof-proof-rewrite proof left-head comparison '(1)))
         (db-type (library-library-type-of p db nil))
         (da-type (library-library-type-of p da nil)))
      (library-library-cite p "POSITIVE-PLUS-NONNEGATIVE" (list db da)
                            (list db-type da-type head weak-tail)))))

(defun h4-book-accumulator-count-pair-bound-weak (p a b da db left-head weak-tail)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((comparison (library-library-axiom p "<-ON-OTHERS" (list b a)))
         (weak-head (proof-proof-rewrite proof left-head comparison '(1 1)))
         (da-type (library-library-type-of p da nil))
         (db-type (library-library-type-of p db nil)))
      (library-library-cite p "NONNEGATIVE-SUM" (list da db)
                            (list da-type db-type weak-head weak-tail)))))

(defun h4-book-accumulator-count-pair-bound (p left right left-head left-tail strict)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((head (proof-step-first left-head))
         (head (if strict head (proof-term-at head 1)))
         (head (proof-list-of-length head 3))
         (tail (proof-step-first left-tail))
         (tail (proof-term-at tail 1))
         (tail (proof-list-of-length tail 3)))
      (let* ((a (if strict (cadr head) (caddr head)))
             (b (if strict (caddr head) (cadr head)))
             (d (cadr tail))
             (c (caddr tail))
             (da (library-diff b a))
             (db (library-diff d c)))
        (proof-with-checked-results
            ((comparison (library-library-axiom p "<-ON-OTHERS" (list d c)))
             (weak-tail (proof-proof-rewrite proof left-tail comparison '(1 1)))
             (total (if strict
                        (h4-book-accumulator-count-pair-bound-strict p a b da db left-head weak-tail)
                      (h4-book-accumulator-count-pair-bound-weak p a b da db left-head weak-tail))))
          (h4-book-accumulator-count-pair-bound-merge p left right total strict))))))

(defun h4-book-accumulator-map-selector-count-base (shape p mapped subject-size)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (h4-book-accumulator-opened-call p mapped (list shape)))
         (output (proof-rewritten-term opened)))
      (if (not (equal output *proof-false*))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((nil-count (h4-tactics-tactics-normalize
                         p (list *library-count* *proof-false*) nil
                         (cons *library-count* *h4-book-flatten-logic*) nil nil))
             (count (proof-rewritten-term nil-count)))
          (if (not (equal count *proof-zero*))
              '(:failure "failure" "")
            (proof-with-checked-results
                ((left (h4-book-flatten-rewrite-argument p (list *library-count* mapped) 1 opened))
                 (left (proof-proof-chain proof left (list nil-count)))
                 (natural (library-library-natural p subject-size))
                 (nonnegative (library-library-cite p "NATURAL-NONNEGATIVE" (list subject-size)
                                                    (list natural)))
                 (reversed (proof-proof-symmetric proof left)))
              (proof-proof-rewrite proof nonnegative reversed '(1 1 2)))))))))

(defun h4-book-accumulator-map-selector-count-pair (shape induction p mapped bound)
  (proof-with-checked-results
      ((opened (h4-book-accumulator-opened-call p mapped (list shape)))
       (head (library-library-cite p bound (list (list *library-car* *library-x*)) nil))
       (mapped-count (h4-book-accumulator-mapped-count p mapped opened))
       (subject-count (h4-book-accumulator-count-cells p *library-x* shape)))
    (h4-book-accumulator-count-pair-bound p mapped-count subject-count head induction nil)))

(defun h4-book-accumulator-map-selector-count (p mapper selector)
  (let* ((proof (library-library-proof p))
         (subject *library-x*)
         (mapped (list mapper subject))
         (subject-size (list *library-count* subject))
         (goal (proof-neg (library-lt subject-size (list *library-count* mapped))))
         (bound (if (equal selector *library-car*) "COUNT-CAR-WEAK" "COUNT-CDR-WEAK"))
         (test (list *proof-consp* subject)))
    (proof-with-checked-results
        ((shape (proof-proof-assume proof test t))
         (induction (h4-book-flatten-cdr-induction-recurse shape p goal subject nil))
         (pair (h4-book-accumulator-map-selector-count-pair shape induction p mapped bound))
         (shape (proof-proof-assume proof test nil))
         (base (h4-book-accumulator-map-selector-count-base shape p mapped subject-size)))
      (h4-book-flatten-cdr-induction p goal subject base pair nil))))

(defun h4-book-accumulator-mapped-descent-head-shape (tests p subject head parent nonpair)
  (declare (xargs :measure (acl2-count tests)))
  (if (endp tests)
      '(:failure "unproved" "")
    (let* ((proof (library-library-proof p))
           (step (car tests)))
      (proof-with-checked-results
          ((first (proof-step-first step))
           (predicate (and (proof-is-call first *proof-not*) (proof-term-at first 1))))
        (if (not (and (proof-compound predicate) (equal (cdr predicate) (list subject))
                      (assoc-equal (car predicate) (proof-proof-definitions proof))))
            (h4-book-accumulator-mapped-descent-head-shape (cdr tests) p subject head parent nonpair)
          (proof-with-checked-results
              ((reduction (h4-book-accumulator-opened-call p predicate (list parent nonpair)))
               (right (proof-rewritten-term reduction)))
            (if (not (equal right *proof-true*))
                (h4-book-accumulator-mapped-descent-head-shape (cdr tests) p subject head parent nonpair)
              (proof-with-checked-results
                  ((positive (h4-tactics-tactics-non-nil p reduction))
                   (conflict (proof-proof-cut proof positive step)))
                (proof-proof-front proof conflict (list *proof-consp* head))))))))))

(defun h4-book-accumulator-mapped-descent-selector (output mapper subject head)
  (let ((tail (list mapper (list *library-cdr* subject))))
    (cond ((equal output (list *proof-cons* (list *library-car* head) tail))
           (cons *library-car* 2))
          ((equal output (list *proof-cons* (list *library-cdr* head) tail))
           (cons *library-cdr* 3))
          (t '(:failure "unproved" "")))))

(defun h4-book-accumulator-ordinal-comparison (p step)
  (proof-with-checked-results
      ((first (proof-step-first step))
       (args (proof-list-of-length (cdr first) 2)))
    (library-library-ordinal-comparison p (car args) (cadr args))))

(defun h4-book-accumulator-mapped-descent (p subject child tests parent)
  (let ((proof (library-library-proof p))
        (head (list *library-car* subject)))
    (if (not (and (proof-compound child) (equal (cdr child) (list subject))
                  (assoc-equal (car child) (proof-proof-definitions proof))))
        '(:failure "unproved" "")
      (proof-with-checked-results
          ((opened (h4-book-accumulator-opened-call p child (list parent)))
           (output (proof-rewritten-term opened))
           (selection (h4-book-accumulator-mapped-descent-selector output (car child) subject head))
           (nonpair (proof-proof-assume proof (list *proof-consp* head) nil))
           (head-shape (h4-book-accumulator-mapped-descent-head-shape tests p subject head parent nonpair))
           (builtin (library-library-builtin p (cdr selection) head))
           (head-order (proof-proof-discharge proof builtin head-shape))
           (comparison (h4-book-accumulator-ordinal-comparison p head-order))
           (head-order (proof-proof-rewrite proof head-order comparison '(1)))
           (count (h4-book-accumulator-map-selector-count p (car child) (car selection)))
           (tail-weak (proof-proof-instantiate proof count (list (list *library-x* (list *library-cdr* subject)))))
           (mapped-count (h4-book-accumulator-mapped-count p child opened))
           (subject-count (h4-book-accumulator-count-cells p subject parent))
           (strict (h4-book-accumulator-count-pair-bound p mapped-count subject-count head-order tail-weak t))
           (comparison (h4-book-accumulator-ordinal-comparison p strict)))
        (proof-proof-transport proof strict comparison)))))

(defun h4-book-accumulator-bindings (formals actuals)
  (cond ((or (endp formals) (endp actuals)) nil)
        ((equal (car formals) (car actuals))
         (h4-book-accumulator-bindings (cdr formals) (cdr actuals)))
        (t (cons (list (car formals) (car actuals))
                 (h4-book-accumulator-bindings (cdr formals) (cdr actuals))))))

(defun h4-book-accumulator-accumulator-induction-descend (p subject child tests parent)
  (if (equal child (list *library-cdr* subject))
      (proof-with-checked-results ((builtin (library-library-builtin p 3 subject)))
        (proof-proof-discharge (library-library-proof p) builtin parent))
    (h4-book-accumulator-mapped-descent p subject child tests parent)))

(defun h4-book-accumulator-accumulator-induction-advance
    (p formula executable subject tests changes implementation lifted actual)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((parent (proof-find-evidence tests (list (list *proof-consp* subject)))))
      (if (not parent)
          '(:failure "unproved" "")
        (let* ((bindings (h4-book-accumulator-bindings (cdr executable) (cdr actual)))
               (mapping (proof-bindings-table bindings nil))
               (child (table-get mapping subject nil)))
          (proof-with-checked-results
              ((less (h4-book-accumulator-accumulator-induction-descend p subject child tests parent)))
            (if (and (consp changes) (not (equal (car changes) bindings)))
                '(:failure "unproved" "")
              (proof-with-checked-results
                  ((smaller (proof-subst formula mapping))
                   (decrease (proof-step-first less))
                   (assumption (proof-proof-assume proof (proof-ite decrease smaller *proof-true*) t))
                   (induction (proof-proof-prove-if proof assumption less))
                   (value (proof-proof-chain proof implementation (list induction)))
                   (call (proof-rewritten-term value))
                   (restored (h4-book-flatten-unfold-on-list p call (car (last actual)) nil))
                   (reversed (proof-proof-symmetric proof lifted))
                   (step (proof-proof-chain proof value (list restored reversed))))
                (cons step (or changes (list bindings)))))))))))

(defun h4-book-accumulator-accumulator-induction-update-p (actual described executable logical accumulator)
  (if (not (and (proof-is-call actual (car executable)) (proof-is-call described *proof-cons*)))
      nil
    (proof-with-checked-results ((tail (proof-term-at described 2)))
      (if (not (equal tail (cons (car logical) (seq-slice actual 1 -1))))
          nil
        (proof-with-checked-results ((head (proof-term-at described 1)))
          (equal (car (last actual)) (list *proof-cons* head accumulator)))))))

(defun h4-book-accumulator-accumulator-induction-finish
    (p formula executable logical accumulator subject tests changes implementation specification actual described)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((target (proof-term-at formula 2))
         (lifted (h4-book-flatten-rewrite-argument p target 2 specification))
         (right (proof-rewritten-term lifted)))
      (if (equal actual right)
          (proof-with-checked-results
              ((reversed (proof-proof-symmetric proof lifted))
               (step (proof-proof-chain proof implementation (list reversed))))
            (cons step changes))
        (proof-with-checked-results
            ((update (h4-book-accumulator-accumulator-induction-update-p
                      actual described executable logical accumulator)))
          (if (not update)
              '(:failure "unproved" "")
            (h4-book-accumulator-accumulator-induction-advance
             p formula executable subject tests changes implementation lifted actual)))))))

(defun h4-book-accumulator-accumulator-induction-test (remaining)
  (proof-with-checked-results ((test (proof-term-at remaining 1)))
    (if (or (proof-is-call test *proof-not*)
            (and (proof-is-call test *proof-if*)
                 (equal (cddr test) (list *proof-false* *proof-true*))))
        (proof-term-at test 1)
      test)))

(mutual-recursion
 (defun h4-book-accumulator-accumulator-induction-compare
     (n tests p formula executable logical accumulator subject changes)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "h4-book-accumulator-accumulator-induction-compare")
     (let ((proof (library-library-proof p)))
       (proof-with-checked-results
           ((implementation (h4-book-accumulator-opened-call p executable tests))
            (specification (h4-book-accumulator-opened-call p logical tests))
            (actual (proof-rewritten-term implementation))
            (described (proof-rewritten-term specification)))
         (let ((remaining (if (proof-is-call actual *proof-if*) actual described)))
           (cond ((not (proof-is-call remaining *proof-if*))
                  (h4-book-accumulator-accumulator-induction-finish
                   p formula executable logical accumulator subject tests changes
                   implementation specification actual described))
                 ((equal (len tests) 4) '(:failure "unproved" ""))
                 (t
                  (proof-with-checked-results
                      ((test (h4-book-accumulator-accumulator-induction-test remaining))
                       (positive (proof-proof-assume proof test t))
                       (yes (h4-book-accumulator-accumulator-induction-compare-branch
                             (1- n) positive tests p formula executable logical accumulator subject changes))
                       (negative (proof-proof-assume proof test nil))
                       (no (h4-book-accumulator-accumulator-induction-compare-branch
                            (1- n) negative tests p formula executable logical accumulator subject (cdr yes)))
                       (step (h4-tactics-tactics-case-of p formula test (car yes) (car no))))
                    (cons step (cdr no))))))))))
 (defun h4-book-accumulator-accumulator-induction-compare-branch
     (n sign tests p formula executable logical accumulator subject changes)
   (declare (xargs :measure (nfix n)))
   (if (not (o< (nfix (1- n)) (nfix n)))
       '(:failure "fuel" "h4-book-accumulator-accumulator-induction-compare-branch")
     (h4-book-accumulator-accumulator-induction-compare
      (1- n) (append tests (list sign)) p formula executable logical accumulator subject changes))))

(defun h4-book-accumulator-accumulator-induction (p formula match subject)
  (let ((measure (list *library-count* subject)))
    (proof-with-checked-results
        ((parts (proof-list-of-length match 3))
         (result (h4-book-accumulator-accumulator-induction-compare
                  1000000 nil p formula (car parts) (cadr parts) (caddr parts) subject nil)))
      (if (endp (cdr result))
          (car result)
        (proof-with-checked-results ((ordinal (library-library-builtin p 1 subject)))
          (proof-proof-induct (library-library-proof p) ordinal (car result) formula measure (cdr result)))))))

(defun h4-book-accumulator-reverse-accumulator-proof-try (subjects p formula match)
  (if (endp subjects)
      nil
    (let ((result (h4-book-accumulator-accumulator-induction p formula match (car subjects))))
      (if (and (failure-p result) (equal (cadr result) "unproved"))
          (h4-book-accumulator-reverse-accumulator-proof-try (cdr subjects) p formula match)
        result))))

(defun h4-book-accumulator-reverse-accumulator-proof (p formula)
  (proof-with-checked-results ((match (h4-book-accumulator-reverse-accumulator-shape formula)))
    (if (not match)
        nil
      (let ((executable (car match))
            (logical (cadr match))
            (definitions (proof-proof-definitions (library-library-proof p))))
        (and (assoc-equal (car executable) definitions) (assoc-equal (car logical) definitions)
             (h4-book-accumulator-reverse-accumulator-proof-try (cdr logical) p formula match))))))
