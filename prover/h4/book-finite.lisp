(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h4-book-finite-constructor-test (p)
  (let* ((proof (library-library-proof p))
         (pair (list *proof-cons* *library-x* *library-y*))
         (proposition (list *proof-consp* pair))
         (positive (proof-eq proposition *proof-true*)))
    (proof-with-checked-results
        ((witness (proof-proof-fact proof "consp-cons" nil))
         (boolean (proof-proof-fact proof "booleanp-consp" (list (list *library-x* pair))))
         (denied (proof-proof-assume proof positive nil))
         (formula (proof-step-first boolean))
         (reduced (h4-tactics-tactics-normalize
                   p formula (list denied) (list (proof-sym "BOOLEANP" "ACL2") (proof-cl "EQ")) nil nil))
         (as-nil (proof-proof-rewrite proof boolean reduced '(1)))
         (impossible (proof-proof-rewrite proof witness as-nil '(1)))
         (tidied (proof-proof-tidy proof impossible)))
      (proof-proof-front proof tidied positive))))

(defun h4-book-finite-reduction-provider (p)
  (proof-with-checked-results ((consp-cons (h4-book-finite-constructor-test p)))
    (h4-tactics-constructor-provider consp-cons)))

(defun h4-book-finite-reduction-provider-provide (term p consp-cons)
  (h4-tactics-constructor-reduction term p consp-cons))

(defun h4-book-finite-proposition-from-interval-point
    (p term bound delta integral lower excluded)
  (let ((proof (library-library-proof p))
        (integers (list integral)))
    (proof-with-checked-results
        ((delta-type (library-library-type-of p delta integers))
         (difference (library-library-axiom p "<-ON-OTHERS" (list term bound)))
         (nonnegative (proof-proof-rewrite proof lower difference '(1 1)))
         (natural (library-library-cite p "NATURAL-FROM-BOUNDS" (list delta) (list delta-type nonnegative)))
         (increase (library-lt bound term))
         (no-increase (proof-proof-assume proof increase nil))
         (compare (library-library-comparison p bound term integers))
         (stopped (proof-proof-rewrite proof no-increase compare '(1 1)))
         (as-zero (proof-proof-use proof *h4-book-arithmetic-natural-nonpositive-zero*
                                  (list (list *library-x* delta)) (list natural stopped)))
         (original (proof-proof-reflexive proof (library-plus bound delta)))
         (restored (proof-proof-rewrite proof original as-zero '(1 2 2)))
         (restored-first (proof-step-first restored))
         (original-sum (proof-term-at restored-first 1))
         (left (library-library-linear-equal p original-sum term integers))
         (left (proof-proof-symmetric proof left))
         (new-sum (proof-term-at restored-first 2))
         (right (library-library-linear-equal p new-sum bound integers))
         (equal-to-bound (proof-proof-chain proof left (list restored right)))
         (not-equal (proof-term-at excluded 0))
         (contradiction (proof-proof-cut proof equal-to-bound not-equal))
         (strictly-above (proof-proof-front proof contradiction increase)))
      (list strictly-above compare delta-type))))

(defun h4-book-finite-proposition-from-interval-next (p term number delta integral result)
  (let ((proof (library-library-proof p))
        (strictly-above (car result))
        (compare (cadr result))
        (delta-type (caddr result))
        (integers (list integral)))
    (proof-with-checked-results
        ((delta-positive (proof-proof-rewrite proof strictly-above compare '(1)))
         (discrete (proof-proof-fact proof "integer-discrete" (list (list *library-x* delta))))
         (premise (h4-book-division-conjunction p (list delta-type delta-positive)))
         (at-least-one (h4-tactics-tactics-modus-ponens p discrete premise))
         (next-comparison (library-library-comparison p term (proof-quote (1+ number)) integers))
         (delta-comparison (library-library-comparison p delta *proof-one* integers))
         (next-result (proof-rewritten-term next-comparison))
         (next-difference (proof-term-at next-result 2))
         (delta-result (proof-rewritten-term delta-comparison))
         (delta-difference (proof-term-at delta-result 2))
         (equal-differences (library-library-linear-equal p next-difference delta-difference integers))
         (adjusted (proof-proof-rewrite proof next-comparison equal-differences '(1 2 2)))
         (reversed (proof-proof-symmetric proof delta-comparison))
         (comparison (proof-proof-chain proof adjusted (list reversed)))
         (reverse-comparison (proof-proof-symmetric proof comparison)))
      (proof-proof-rewrite proof at-least-one reverse-comparison '(1 1)))))

(defun h4-book-finite-proposition-from-interval-visit (n p term number end integral lower upper excluded)
  (declare (xargs :measure (nfix n)))
  (cond ((not (o< (nfix (1- n)) (nfix n)))
         '(:failure "fuel" "h4-book-finite-proposition-from-interval-visit"))
        ((< end number) '(:failure "inapplicable-step" ""))
        (t
         (let* ((bound (proof-quote number))
                (delta (library-diff term bound)))
           (proof-with-checked-results
               ((point (h4-book-finite-proposition-from-interval-point p term bound delta integral lower excluded)))
             (if (equal number end)
                 (proof-proof-cut (library-library-proof p) (car point) upper)
               (proof-with-checked-results
                   ((next (h4-book-finite-proposition-from-interval-next p term number delta integral point)))
                 (h4-book-finite-proposition-from-interval-visit
                  (1- n) p term (1+ number) end integral next upper (cdr excluded)))))))))

(defun h4-book-finite-proposition-from-interval (p term start end integral lower upper excluded)
  (h4-book-finite-proposition-from-interval-visit 1000000 p term start end integral lower upper excluded))

(defun h4-book-finite-consecutive-p (domain expected)
  (if (endp domain)
      t
    (and (equal (if (eq (car domain) t) 1 (car domain)) expected)
         (h4-book-finite-consecutive-p (cdr domain) (1+ expected)))))

(defun h4-book-finite-interval-arguments (values arguments tests low high)
  (declare (xargs :measure (acl2-count values)))
  (if (not (proof-is-call values *proof-cons*))
      (and (equal values *proof-false*) (list arguments tests))
    (proof-with-checked-results ((parts (proof-list-of-length (cdr values) 2)))
      (let ((variable (car parts)))
        (if (or (proof-compound variable) (member-equal variable arguments))
            nil
          (h4-book-finite-interval-arguments
           (caddr values) (append arguments (list variable))
           (append tests (list (library-integer variable)
                               (proof-neg (library-lt variable low))
                               (proof-neg (library-lt high variable))))
           low high))))))

(defun h4-book-finite-interval-tests (tests right)
  (if (endp tests)
      t
    (if (not (proof-is-call right *proof-if*))
        nil
      (proof-with-checked-results ((test (proof-term-at right 1)))
        (if (not (equal test (car tests)))
            nil
          (proof-with-checked-results ((no (proof-term-at right 3)))
            (and (equal no *proof-false*)
                 (h4-book-finite-interval-tests (cdr tests) (caddr right)))))))))

(defun h4-book-finite-finite-interval-shape (formula)
  (if (not (proof-is-call formula *proof-equal*))
      nil
    (proof-with-checked-results ((sides (proof-list-of-length (cdr formula) 2)))
      (let ((left (car sides))
            (right (cadr sides)))
        (if (not (proof-compound left))
            nil
          (proof-with-checked-results ((head (proof-term-at left 0)))
            (if (or (proof-compound head) (not (equal (len left) 3))
                    (not (proof-is-call (caddr left) *proof-quote*)))
                nil
              (proof-with-checked-results ((domain (proof-term-at (caddr left) 1)))
                (let* ((size (len domain))
                       (first (car domain))
                       (start (if (eq first t) 1 first)))
                  (if (not (and (proof-compound domain) (<= 1 size) (<= size 3) (integerp start)
                                (h4-book-finite-consecutive-p domain start)))
                      nil
                    (proof-with-checked-results
                        ((plan (h4-book-finite-interval-arguments
                                (cadr left) nil nil (proof-quote first) (proof-quote (car (last domain))))))
                      (if (not (and plan (equal (len (car plan)) size)))
                          nil
                        (proof-with-checked-results ((holds (h4-book-finite-interval-tests (cadr plan) right)))
                          (and holds (list (car plan) domain)))))))))))))))

(defun h4-book-finite-prove-interval-cases-evaluate (evidence substitutions p formula provide)
  (proof-with-checked-results
      ((equality (h4-tactics-tactics-normalize
                  p formula evidence (table-keys (proof-proof-definitions (library-library-proof p)))
                  substitutions provide))
       (value (proof-rewritten-term equality)))
    (if (equal value *proof-true*)
        (h4-tactics-tactics-non-nil p equality)
      '(:failure "inapplicable-term" ""))))

(defun h4-book-finite-prove-interval-cases-inspect
    (n tests hypotheses first-test p formula variable excluded substitutions provide no-points)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof p)))
    (cond
     ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "h4-book-finite-prove-interval-cases-inspect"))
     ((endp tests)
        (proof-with-checked-results
            ((contradiction (proof-proof-instantiate proof no-points (list (list *library-x* variable)))))
          (proof-proof-subsume proof contradiction (cons formula (proof-step-clause contradiction)))))
     (t
      (let ((test (car tests)))
        (proof-with-checked-results
            ((positive (proof-proof-assume proof test t))
             (yes-hypotheses (append hypotheses (list positive)))
             (yes (if first-test
                      (h4-book-finite-prove-interval-cases-inspect
                       (1- n) (cdr tests) yes-hypotheses nil p formula variable excluded substitutions provide no-points)
                    (h4-book-finite-prove-interval-cases-evaluate
                     (append excluded yes-hypotheses) substitutions p formula provide)))
             (negative (proof-proof-assume proof test nil))
             (no-hypotheses (append hypotheses (list negative)))
             (no (if first-test
                     (h4-book-finite-prove-interval-cases-evaluate
                      (append excluded no-hypotheses) substitutions p formula provide)
                   (h4-book-finite-prove-interval-cases-inspect
                    (1- n) (cdr tests) no-hypotheses nil p formula variable excluded substitutions provide no-points))))
          (h4-tactics-tactics-case-of p formula test yes no)))))))

(defun h4-book-finite-prove-interval-cases-outside
    (excluded p formula variable domain substitutions provide no-points)
  (let ((tests (list (library-integer variable)
                     (library-lt variable (proof-quote (car domain)))
                     (library-lt (proof-quote (car (last domain))) variable))))
    (h4-book-finite-prove-interval-cases-inspect
     1000000 tests nil t p formula variable excluded substitutions provide no-points)))

(mutual-recursion
 (defun h4-book-finite-prove-interval-cases-compare
     (n arguments substitutions p formula domain provide no-points)
   (declare (xargs :measure (nfix n)))
   (cond ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "h4-book-finite-prove-interval-cases-compare"))
         ((endp arguments) (h4-book-finite-prove-interval-cases-evaluate nil substitutions p formula provide))
         (t (h4-book-finite-prove-interval-cases-test-value
             (1- n) domain nil p formula (car arguments) (cdr arguments) domain substitutions provide no-points))))
 (defun h4-book-finite-prove-interval-cases-test-value
     (n points excluded p formula variable rest domain substitutions provide no-points)
   (declare (xargs :measure (nfix n)))
   (cond ((not (o< (nfix (1- n)) (nfix n))) '(:failure "fuel" "h4-book-finite-prove-interval-cases-test-value"))
         ((endp points)
          (h4-book-finite-prove-interval-cases-outside
           excluded p formula variable domain substitutions provide no-points))
         (t
          (let ((test (proof-eq variable (proof-quote (car points))))
                (proof (library-library-proof p)))
            (proof-with-checked-results
                ((same (proof-proof-assume proof test t))
                 (yes (h4-book-finite-prove-interval-cases-compare
                       (1- n) rest (append substitutions (list same)) p formula domain provide no-points))
                 (different (proof-proof-assume proof test nil))
                 (no (h4-book-finite-prove-interval-cases-test-value
                      (1- n) (cdr points) (append excluded (list different)) p formula variable
                      rest domain substitutions provide no-points)))
              (h4-tactics-tactics-case-of p formula test yes no)))))))

(defun h4-book-finite-exclude-points (domain proof)
  (if (endp domain)
      nil
    (proof-with-checked-results
        ((first (proof-proof-assume proof (proof-eq *library-x* (proof-quote (car domain))) nil))
         (rest (h4-book-finite-exclude-points (cdr domain) proof)))
      (cons first rest))))

(defun h4-book-finite-prove-interval-cases (p formula arguments domain)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((provide (h4-book-finite-reduction-provider p))
         (start (proof-term-at domain 0))
         (end (car (last domain)))
         (integral (proof-proof-assume proof (library-integer *library-x*) t))
         (lower (proof-proof-assume proof (library-lt *library-x* (proof-quote start)) nil))
         (upper (proof-proof-assume proof (library-lt (proof-quote end) *library-x*) nil))
         (excluded (h4-book-finite-exclude-points domain proof))
         (no-points (h4-book-finite-proposition-from-interval p *library-x* start end integral lower upper excluded)))
      (h4-book-finite-prove-interval-cases-compare 1000000 arguments nil p formula domain provide no-points))))

(defun h4-book-finite-finite-comparison-proof (p formula)
  (proof-with-checked-results ((plan (h4-book-finite-finite-interval-shape formula)))
    (if (not plan)
        nil
      (let ((result (h4-book-finite-prove-interval-cases p formula (car plan) (cadr plan))))
        (if (and (failure-p result)
                 (member-equal (cadr result)
                               '("inapplicable-step" "inapplicable-term"
                                 "assertion" "value" "recursion" "unproved")))
            nil
          result)))))
