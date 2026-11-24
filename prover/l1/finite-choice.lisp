(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(mutual-recursion
 (defun l1-finite-choice-variable-free-in (variable term)
   (declare (xargs :measure (acl2-count term)))
   (cond ((not (proof-compound term)) (equal variable term))
         ((endp term) (proof-term-at term 0))
         ((equal (car term) *proof-quote*) nil)
         (t (l1-finite-choice-variable-free-in-arguments variable (cdr term)))))

 (defun l1-finite-choice-variable-free-in-arguments (variable arguments)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (proof-with-checked-results
         ((found (l1-finite-choice-variable-free-in variable (car arguments))))
       (or found
           (l1-finite-choice-variable-free-in-arguments variable
                                                        (cdr arguments)))))))

(defund l1-finite-choice-independent-value-p (variable side other)
  (and (equal side variable)
       (proof-with-checked-results
           ((dependent (l1-finite-choice-variable-free-in variable other)))
         (not dependent))))

(mutual-recursion
 (defun l1-finite-choice-equality-tests (term argument)
   (declare (xargs :measure (acl2-count term)))
   (cond ((equal term argument)
          '(:failure "NonEqualityArgument" ""))
         ((or (endp term) (not (proof-compound term))
              (proof-is-call term *proof-quote*))
          nil)
         ((proof-is-call term *proof-equal*)
          (proof-with-checked-results
              ((parts (proof-list-of-length term 3))
               (left (l1-finite-choice-independent-value-p
                      argument (cadr parts) (caddr parts))))
            (if left
                (list (list term (caddr parts)))
              (proof-with-checked-results
                  ((right (l1-finite-choice-independent-value-p
                           argument (caddr parts) (cadr parts))))
                (if right
                    (list (list term (cadr parts)))
                  (l1-finite-choice-equality-tests-arguments (cdr term) argument))))))
         (t (l1-finite-choice-equality-tests-arguments (cdr term) argument))))

 (defun l1-finite-choice-equality-tests-arguments (arguments argument)
   (declare (xargs :measure (acl2-count arguments)))
   (if (endp arguments)
       nil
     (proof-with-checked-results
         ((first (l1-finite-choice-equality-tests (car arguments) argument))
          (rest (l1-finite-choice-equality-tests-arguments (cdr arguments) argument)))
       (append first rest)))))

(defund l1-finite-choice-differing-value (proof value)
  (let* ((test (proof-eq value *proof-false*))
         (bit (proof-ite test *proof-true* *proof-false*)))
    (proof-with-checked-results
        ((computed (proof-proof-compute
                    proof (proof-eq *proof-false* *proof-true*) *proof-nil*))
         (distinct (proof-proof-symmetric proof computed))
         (not-nil (proof-proof-not-nil proof))
         (yes (proof-proof-rewrite proof not-nil distinct '(1 1)))
         (test-holds (proof-proof-assume proof test t))
         (test-reversed (proof-proof-symmetric proof test-holds))
         (yes (proof-proof-rewrite proof yes test-reversed '(1 1 1)))
         (true-branch (proof-proof-if-true proof bit))
         (true-reversed (proof-proof-symmetric proof true-branch))
         (yes (proof-proof-rewrite proof yes true-reversed '(1 1 2)))
         (test-fails (proof-proof-assume proof test nil))
         (false-branch (proof-proof-if-false proof bit))
         (false-reversed (proof-proof-symmetric proof false-branch))
         (no (proof-proof-rewrite proof test-fails false-reversed '(1 1 2)))
         (yes (proof-proof-tidy proof yes))
         (no (proof-proof-tidy proof no))
         (cases (proof-proof-cases proof test yes no)))
      (list bit cases))))

(defun l1-finite-choice-all-quoted-p (keys)
  (or (endp keys)
      (and (proof-is-call (car keys) *proof-quote*)
           (l1-finite-choice-all-quoted-p (cdr keys)))))

(defun l1-finite-choice-fresh-literal (remaining value keys)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      '(:failure "failure" "")
    (let ((quoted (proof-quote value)))
      (if (member-equal quoted keys)
          (l1-finite-choice-fresh-literal (1- remaining) (1+ value) keys)
        quoted))))

(defund l1-finite-choice-fresh-literal-test (proof test bindings)
  (proof-with-checked-results ((actual (proof-subst test bindings)))
    (proof-proof-compute proof actual *proof-nil*)))

(defun l1-finite-choice-fresh-literal-tests (proof tests bindings false-tests)
  (if (endp tests)
      false-tests
    (proof-with-checked-results
        ((pair (proof-list-of-length (car tests) 2))
         (computed (l1-finite-choice-fresh-literal-test proof (car pair) bindings)))
      (l1-finite-choice-fresh-literal-tests
       proof (cdr tests) bindings (table-put false-tests (car pair) computed)))))

; The Boolean at each position differs from that projection of the key at the position.
(defun l1-finite-choice-fresh-differences (proof keys index)
  (if (endp keys)
      (list nil nil)
    (proof-with-checked-results
        ((projected (l1-application-component (car keys) index))
         (different (l1-finite-choice-differing-value proof projected))
         (rest (l1-finite-choice-fresh-differences proof (cdr keys) (1+ index))))
      (list (cons (car different) (car rest))
            (cons (cadr different) (cadr rest))))))

(defun l1-finite-choice-fresh-positions (keys index positions)
  (if (endp keys)
      positions
    (l1-finite-choice-fresh-positions
     (cdr keys) (1+ index) (table-put positions (car keys) index))))

(defund l1-finite-choice-fresh-symbolic-test
    (proof test key default bindings positions different)
  (proof-with-checked-results
      ((actual (proof-subst test bindings))
       (matched (proof-proof-assume proof actual t))
       (left (proof-term-at actual 1))
       (matched (if (equal left key) matched
                  (proof-proof-symmetric proof matched))))
    (let ((position (assoc-equal key positions)))
      (if (not position)
          '(:failure "failure" "")
        (let ((index (cdr position)))
          (proof-with-checked-results
              ((projection (l1-application-component key index))
               (projected (proof-proof-reflexive proof projection))
               (same (proof-proof-rewrite
                      proof projected matched
                      (list* 1 2 (make-list-ac (1+ index) 1 nil))))
               (selected (l1-application-select-component proof default index))
               (same (proof-proof-chain proof same (list selected)))
               (unequal (proof-proof-cut proof same (nth index different)))
               (equation (proof-proof-nil-or-true proof actual)))
            (proof-proof-discharge proof equation unequal)))))))

(defun l1-finite-choice-fresh-symbolic-tests
    (proof tests default bindings positions different false-tests)
  (if (endp tests)
      false-tests
    (proof-with-checked-results
        ((pair (proof-list-of-length (car tests) 2))
         (equation (l1-finite-choice-fresh-symbolic-test
                    proof (car pair) (cadr pair) default bindings positions different)))
      (l1-finite-choice-fresh-symbolic-tests
       proof (cdr tests) default bindings positions different
       (table-put false-tests (car pair) equation)))))

(defun l1-finite-choice-fresh-argument (proof argument tests keys)
  (if (l1-finite-choice-all-quoted-p keys)
      (proof-with-checked-results
          ((default (l1-finite-choice-fresh-literal (1+ (len keys)) 0 keys))
           (false-tests (l1-finite-choice-fresh-literal-tests
                         proof tests (list (cons argument default)) nil)))
        (list default false-tests))
    (proof-with-checked-results
        ((differences (l1-finite-choice-fresh-differences proof keys 0))
         (default (l1-primitive-cons-list (car differences) *proof-false*))
         (false-tests (l1-finite-choice-fresh-symbolic-tests
                       proof tests default (list (cons argument default))
                       (l1-finite-choice-fresh-positions keys 0 nil)
                       (cadr differences) nil)))
      (list default false-tests))))

(defund l1-finite-choice-default-equation-test (proof pair original other template)
  (let ((test (car pair))
        (equation (cdr pair)))
    (proof-with-checked-results
        ((unknown (proof-proof-nil-or-true proof test))
         (original (proof-proof-rewrite-result proof original unknown template test))
         (other (proof-proof-rewrite-result proof other equation template test)))
      (list original other))))

(defun l1-finite-choice-default-equation-tests
    (proof false-tests original other template)
  (if (endp false-tests)
      (proof-with-checked-results ((reversed (proof-proof-symmetric proof other)))
        (proof-proof-chain proof original (list reversed)))
    (proof-with-checked-results
        ((result (l1-finite-choice-default-equation-test
                  proof (car false-tests) original other template)))
      (l1-finite-choice-default-equation-tests
       proof (cdr false-tests) (car result) (cadr result) template))))

(defun l1-finite-choice-default-equation (proof failure argument default false-tests)
  (proof-with-checked-results
      ((instance (proof-subst failure (list (cons argument default))))
       (original (proof-proof-reflexive proof failure))
       (other (proof-proof-reflexive proof instance)))
    (l1-finite-choice-default-equation-tests
     proof false-tests original other (proof-eq *proof-nil* failure))))

(defun l1-finite-choice-test-keys (tests)
  (if (endp tests)
      nil
    (cons (cadar tests) (l1-finite-choice-test-keys (cdr tests)))))

(defun l1-finite-choice-failures (failure argument points)
  (if (endp points)
      nil
    (proof-with-checked-results
        ((instance (proof-subst failure (list (cons argument (car points)))))
         (rest (l1-finite-choice-failures failure argument (cdr points))))
      (cons instance rest))))

(defun l1-finite-choice-selections (point-failures selections)
  (if (endp point-failures)
      selections
    (let ((point (caar point-failures))
          (failure (cadar point-failures)))
      (l1-finite-choice-selections
       (cdr point-failures) (cons (proof-ite failure point (car selections)) selections)))))

(defund l1-finite-choice-branch (proof selected fails failure argument)
  (proof-with-checked-results
      ((true-branch (proof-proof-if-true proof selected))
       (chosen (proof-proof-symmetric proof true-branch))
       (assumed (proof-proof-assume proof fails t))
       (accepted (proof-proof-rewrite-result proof assumed chosen failure argument))
       (false-branch (proof-proof-if-false proof selected))
       (rejected (proof-proof-symmetric proof false-branch)))
    (list accepted rejected)))

(defun l1-finite-choice-branches (proof selections failures failure argument)
  (if (endp (cdr selections))
      (proof-with-checked-results ((accepted (proof-proof-assume proof (car failures) t)))
        (list (list accepted) nil))
    (proof-with-checked-results
        ((branch (l1-finite-choice-branch proof (car selections) (car failures) failure argument))
         (rest (l1-finite-choice-branches proof (cdr selections) (cdr failures)
                                         failure argument)))
      (list (cons (car branch) (car rest)) (cons (cadr branch) (cadr rest))))))

(defun l1-finite-choice-representative-at (items index)
  (let* ((size (len items))
         (offset (if (< index 0) (+ size index) index)))
    (if (or (< offset 0) (<= size offset))
        '(:failure "failure" "")
      (nth offset items))))

(defund l1-finite-choice-earlier-failure
    (index step proof accepted rejected failures failure argument)
  (proof-with-checked-results
      ((rejection (l1-finite-choice-representative-at rejected index))
       (later (proof-proof-rewrite-result proof step rejection failure argument))
       (failed (l1-finite-choice-representative-at failures index))
       (acceptance (l1-finite-choice-representative-at accepted index)))
    (proof-proof-cases proof failed acceptance later)))

(defun l1-finite-choice-earlier-failures
    (remaining step proof accepted rejected failures failure argument)
  (declare (xargs :measure (nfix remaining)))
  (if (zp remaining)
      step
    (let ((index (1- remaining)))
      (proof-with-checked-results
          ((step (l1-finite-choice-earlier-failure index step proof accepted rejected failures
                                                  failure argument)))
        (l1-finite-choice-earlier-failures index step proof accepted rejected failures
                                           failure argument)))))

(defun l1-finite-choice-finite-choice-selected-failure
    (index equation proof accepted rejected failures failure argument)
  (proof-with-checked-results
      ((initial (l1-finite-choice-representative-at accepted index))
       (step (l1-finite-choice-earlier-failures index initial proof accepted rejected
                                                failures failure argument))
       (needed (l1-finite-choice-representative-at failures index))
       (literal (proof-step-first step))
       (step (proof-proof-subsume proof step (list literal (proof-neg needed))))
       (reversed (proof-proof-symmetric proof equation))
       (rewritten (proof-proof-rewrite proof step reversed '(2 1))))
    (proof-proof-tidy proof rewritten)))

(defund l1-finite-choice-test-consequence
    (proof pair keys accepted rejected failures failure argument consequence)
  (let ((test (car pair))
        (key (cadr pair)))
    (proof-with-checked-results
        ((matched (proof-proof-assume proof test t))
         (left (proof-term-at test 1))
         (matched (if (equal left argument) matched
                    (proof-proof-symmetric proof matched)))
         (original (proof-proof-reflexive proof failure))
         (equation (proof-proof-rewrite-result
                    proof original matched (proof-eq *proof-nil* failure) argument))
         (index (seq-index keys key))
         (selected (l1-finite-choice-finite-choice-selected-failure
                    index equation proof accepted rejected failures failure argument)))
      (proof-proof-cases proof test selected consequence))))

(defun l1-finite-choice-test-consequences
    (proof tests keys accepted rejected failures failure argument consequence)
  (if (endp tests)
      consequence
    (proof-with-checked-results
        ((consequence (l1-finite-choice-test-consequence
                       proof (car tests) keys accepted rejected failures failure argument consequence)))
      (l1-finite-choice-test-consequences
       proof (cdr tests) keys accepted rejected failures failure argument consequence))))

(defun l1-finite-choice-necessity (proof failure consequence)
  (proof-with-checked-results
      ((result (proof-step-first consequence))
       (opened (proof-proof-unfold proof (list *library-implies* failure result)))
       (first (proof-step-first opened))
       (body (proof-term-at first 2))
       (assumed (proof-proof-assume proof failure t))
       (yes-branch (proof-proof-select proof body assumed))
       (yes-body (proof-term-at body 2))
       (yes-result (proof-proof-select proof yes-body consequence))
       (yes (proof-proof-chain proof opened (list yes-branch yes-result)))
       (yes (proof-proof-true-from-eq proof yes))
       (denied (proof-proof-assume proof failure nil))
       (no-branch (proof-proof-select proof body denied))
       (no (proof-proof-chain proof opened (list no-branch)))
       (no (proof-proof-true-from-eq proof no)))
    (proof-proof-cases proof failure yes no)))

(defun l1-finite-choice-finite-choice (proof argument failure)
  (let ((tests (l1-finite-choice-equality-tests failure argument)))
    (cond ((failure-p tests)
           (if (or (equal (cadr tests) "NonEqualityArgument")
                   (equal (cadr tests) "value"))
               nil
             tests))
          (t
           (let* ((tests (proof-unique tests))
                  (keys (proof-unique (l1-finite-choice-test-keys tests))))
             (proof-with-checked-results
                 ((fresh (l1-finite-choice-fresh-argument proof argument tests keys))
                  (default (car fresh))
                  (failures (l1-finite-choice-failures
                             failure argument (append keys (list default))))
                  (selections (l1-finite-choice-selections
                               (reverse (seq-zip keys failures)) (list default)))
                  (branches (l1-finite-choice-branches proof selections failures failure argument))
                  (accepted (car branches))
                  (rejected (cadr branches))
                  (equation (l1-finite-choice-default-equation
                             proof failure argument default (cadr fresh)))
                  (consequence (l1-finite-choice-finite-choice-selected-failure
                                (len keys) equation proof accepted rejected failures
                                failure argument))
                  (consequence (l1-finite-choice-test-consequences
                                proof (reverse tests) keys accepted rejected failures
                                failure argument consequence))
                  (necessity (l1-finite-choice-necessity proof failure consequence)))
               (list (car selections) necessity)))))))
