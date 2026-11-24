(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-pair-products-pair* (proof-sym "PROD-CONS$INLINE" "STD"))
(defconst *b2-pair-products-pairp* (proof-sym "PROD-CONSP" "STD"))
(defconst *b2-pair-products-tag* (proof-sym "TAG$INLINE" "ACL2"))
(defconst *b2-pair-products-selectors*
  (list (cons *library-car* (proof-sym "CAR-OF-PROD-CONS" "STD"))
        (cons *library-cdr* (proof-sym "CDR-OF-PROD-CONS" "STD"))))
(defconst *b2-pair-products-rebuild* (proof-sym "PROD-CONS-OF-CAR/CDR" "STD"))
(defconst *b2-pair-products-equality* (proof-sym "EQUAL-OF-PROD-CONS" "STD"))
(defconst *b2-pair-products-size* (proof-sym "ACL2-COUNT-OF-PROD-CONS" "STD"))
(defconst *b2-pair-products-tag-cons* (proof-sym "TAG-FORWARD-TO-CONSP" "STD"))
(defconst *b2-pair-products-when-either* (proof-sym "PROD-CONS-WHEN-EITHER" "STD"))

(defconst *b2-pair-products-pair-theorems*
  (list *b2-pair-products-size*
        (cdr (assoc-equal *library-car* *b2-pair-products-selectors*))
        (cdr (assoc-equal *library-cdr* *b2-pair-products-selectors*))
        *b2-pair-products-equality*
        (proof-sym "PROD-CONS-NOT-CONSP-FORWARD" "STD")
        *b2-pair-products-rebuild*
        *b2-pair-products-when-either*
        *b2-pair-products-tag-cons*))

(defun b2-pair-products-cons-request-p (result)
  (eq (car result) :b2-pair-products-cons-cases))

(defmacro b2-pair-products-prove-choice (lib test facts sign branch body)
  `(proof-with-checked-results
       ((b2-pair-products-request (b2-tactics-choose ,lib ,test ,facts nil))
        (,sign (cadddr (car b2-pair-products-request)))
        (,branch (car (cddddr (car b2-pair-products-request))))
        (b2-pair-products-answer ,body))
     (if (b2-pair-products-cons-request-p b2-pair-products-answer)
         b2-pair-products-answer
       (proof-with-checked-results
           ((b2-pair-products-replies (list (cons b2-pair-products-answer ,lib)))
            (b2-pair-products-result
             (b2-tactics-choose ,lib ,test ,facts b2-pair-products-replies)))
         (if (eq (caar b2-pair-products-result) :call)
             (proof-with-checked-results
                 ((,sign (cadddr (car b2-pair-products-result)))
                  (,branch (car (cddddr (car b2-pair-products-result))))
                  (b2-pair-products-answer ,body))
               (if (b2-pair-products-cons-request-p b2-pair-products-answer)
                   b2-pair-products-answer
                 (proof-with-checked-results
                     ((b2-pair-products-result
                       (b2-tactics-choose
                        ,lib ,test ,facts
                        (append b2-pair-products-replies
                                (list (cons b2-pair-products-answer ,lib))))))
                   (car b2-pair-products-result))))
           (car b2-pair-products-result))))))

(defun b2-pair-products-pair-size-bound (lib constructed left right cons-step other number tag)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((builtin (library-library-builtin lib number constructed))
         (descent (proof-proof-discharge proof builtin cons-step))
         (projection (library-library-axiom lib tag (list left right)))
         (reduced (proof-proof-rewrite proof descent projection '(1 1 1)))
         (ordinal (library-library-ordinal-comparison
                   lib (list *library-count* other) (list *library-count* constructed)))
         (strict (proof-proof-rewrite proof reduced ordinal '(1)))
         (strict (proof-proof-tidy proof strict)))
      (library-library-as-weak lib strict))))

(defun b2-pair-products-pair-size-conclude (constructed facts lib formula pair)
  (if (equal constructed *proof-false*)
      (b2-tactics-tactics-solve lib formula facts
                               (list pair (list *library-count* *proof-false*)) nil 0 nil)
    (proof-with-checked-results ((parts (proof-list-of-length constructed 3)))
      (let ((proof (library-library-proof lib)) (left (cadr parts)) (right (caddr parts)))
        (proof-with-checked-results
            ((cons-step (proof-proof-fact proof "consp-cons"
                                         (list (list *library-x* left) (list *library-y* right))))
             (car-bound (b2-pair-products-pair-size-bound
                         lib constructed left right cons-step left 2 "CAR-CONS"))
             (cdr-bound (b2-pair-products-pair-size-bound
                         lib constructed left right cons-step right 3 "CDR-CONS")))
          (b2-tactics-tactics-solve lib formula (append facts (list car-bound cdr-bound))
                                  (list pair) nil 0 nil))))))

(defun b2-pair-products-pair-theorem-prove (constructed facts lib formula pair)
  (proof-with-checked-results
      ((facts (if (equal constructed *proof-false*)
                  facts
                (proof-with-checked-results
                    ((left (proof-term-at constructed 1))
                     (right (proof-term-at constructed 2))
                     (cons-step (proof-proof-fact (library-library-proof lib) "consp-cons"
                                                  (list (list *library-x* left) (list *library-y* right))))
                     (present (b2-tactics-tactics-from-impossible
                               lib constructed cons-step nil nil nil 1500 nil)))
                  (append facts (list present))))))
    (b2-tactics-tactics-solve lib formula facts (list pair) nil 0 nil)))

(defun b2-pair-products-cons-case-proof (lib prove constructed facts)
  (case (car prove)
    (:size (b2-pair-products-pair-size-conclude constructed facts lib (cadr prove) (caddr prove)))
    (:theorem (b2-pair-products-pair-theorem-prove constructed facts lib (cadr prove) (caddr prove)))
    (otherwise (let ((reply (assoc-equal (list constructed facts) (cadr prove))))
                 (if reply
                     (cdr reply)
                   (list :b2-pair-products-cons-cases constructed facts))))))

(defun b2-pair-products-cons-cases-on-first (some facts lib a b prove)
  (if some
      (b2-pair-products-cons-case-proof lib prove (list *proof-cons* a b) facts)
    (b2-pair-products-prove-choice lib b facts other branch
      (b2-pair-products-cons-case-proof lib prove
                                      (if other (list *proof-cons* *proof-false* b) *proof-false*)
                                      branch))))

(defun b2-pair-products-cons-cases-with-proof (lib a b prove)
  (b2-pair-products-prove-choice lib a nil some facts
    (b2-pair-products-cons-cases-on-first some facts lib a b prove)))

(defun b2-pair-products-cons-cases (lib a b replies)
  (b2-pair-products-cons-cases-with-proof lib a b (list :replies replies)))

(defun b2-pair-products-pair-size (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 4))
       (guard (proof-list-of-length (cadr parts) 2))
       (comparison (proof-list-of-length (cadr guard) 3))
       (count-call (proof-list-of-length (cadr comparison) 2))
       (pair (cadr count-call))
       (args (proof-list-of-length pair 3)))
    (b2-pair-products-cons-cases-with-proof lib (cadr args) (caddr args)
                                           (list :size formula pair))))

(defun b2-pair-products-pair-reconstruction-prove-branch
    (cons-p facts lib occupied typed x goal pair)
  (if cons-p
      (proof-with-checked-results
          ((present (b2-tactics-tactics-from-impossible
                     lib occupied typed facts (list *b2-pair-products-pairp*) nil 1500 nil))
           (last-fact (if (consp facts)
                          (car (last facts))
                        '(:failure "tactic-rejected" "")))
           (rebuilt (b2-tactics-rebuild lib x last-fact)))
        (b2-tactics-tactics-solve lib goal (append facts (list present)) (list pair)
                                (list rebuilt) 0 nil))
    (proof-with-checked-results
        ((empty (b2-tactics-tactics-from-impossible
                 lib (proof-neg x) typed facts (list *b2-pair-products-pairp*) nil 1500 nil)))
      (b2-tactics-tactics-solve lib goal (append facts (list empty)) (list pair) nil 0 nil))))

(defun b2-pair-products-pair-reconstruction-prove (typed lib occupied x goal pair)
  (let ((test (list *proof-consp* x)))
    (b2-pair-products-prove-choice lib test nil cons-p facts
      (b2-pair-products-pair-reconstruction-prove-branch cons-p facts lib occupied typed x goal pair))))

(defun b2-pair-products-pair-reconstruction (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (goal (caddr parts))
       (goal-args (proof-list-of-length goal 3))
       (pair (cadr goal-args))
       (opened (proof-proof-unfold (library-library-proof lib) pair))
       (literal (proof-step-first opened))
       (body (proof-term-at literal 2))
       (occupied (proof-term-at body 1))
       (request (b2-tactics-tactics-implication lib (cadr parts) goal nil))
       (step (b2-pair-products-pair-reconstruction-prove
              (cadddr (car request)) lib occupied (caddr goal-args) goal pair))
       (closed (b2-tactics-tactics-implication lib (cadr parts) goal (cons step lib))))
    (car closed)))

(defun b2-pair-products-pair-equality-premise-proof-compare-conclusion
    (yes-second evidence lib yes-first rebuilt x test inspected goal)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((result
          (if (and yes-first yes-second)
              (proof-with-checked-results
                  ((first (proof-term-at evidence 0))
                   (made (proof-proof-rewrite proof rebuilt first '(1 1 1)))
                   (second (proof-term-at evidence 1))
                   (made (proof-proof-rewrite proof made second '(1 1 2))))
                (proof-proof-symmetric proof made))
            (let* ((slot (if yes-first 1 0))
                   (observed (list (if yes-first *library-cdr* *library-car*) x)))
              (proof-with-checked-results
                  ((reflexive (proof-proof-reflexive proof observed))
                   (assumed (proof-proof-assume proof test t))
                   (first (proof-proof-rewrite proof reflexive assumed '(1 2 1)))
                   (projection (proof-term-at inspected slot))
                   (chain (proof-proof-chain proof first (list projection)))
                   (comparison (proof-term-at evidence slot))
                   (contradicted (proof-proof-cut proof chain comparison)))
                (proof-proof-front proof contradicted (proof-neg test)))))))
      (b2-tactics-tactics-solve lib goal (append evidence (list result)) nil nil 0 nil))))

(defun b2-pair-products-pair-equality-premise-proof-compare
    (yes-first facts lib second rebuilt x test inspected goal)
  (b2-pair-products-prove-choice lib second facts yes-second evidence
    (b2-pair-products-pair-equality-premise-proof-compare-conclusion
     yes-second evidence lib yes-first rebuilt x test inspected goal)))

(defun b2-pair-products-pair-equality-premise-proof (typed lib x first second test inspected goal)
  (let ((value (list *b2-pair-products-pair* (list *library-car* x) (list *library-cdr* x))))
    (proof-with-checked-results
        ((rebuilt (b2-tactics-tactics-use-fact
                   lib *b2-pair-products-rebuild* (proof-eq value x) (list typed) nil nil 0 nil)))
      (b2-pair-products-prove-choice lib first nil yes-first facts
        (b2-pair-products-pair-equality-premise-proof-compare
         yes-first facts lib second rebuilt x test inspected goal)))))

(defun b2-pair-products-pair-equality (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (premise (cadr parts))
       (goal (caddr parts))
       (goal-args (proof-list-of-length goal 3))
       (test (cadr goal-args))
       (conditions (proof-list-of-length (caddr goal-args) 4))
       (test-args (proof-list-of-length test 3))
       (x (cadr test-args))
       (pair (caddr test-args))
       (pair-args (proof-list-of-length pair 3))
       (car-proof (b2-tactics-tactics-use-fact
                   lib (cdr (assoc-equal *library-car* *b2-pair-products-selectors*))
                   (proof-eq (list *library-car* pair) (cadr pair-args)) nil nil nil 0 nil))
       (cdr-proof (b2-tactics-tactics-use-fact
                   lib (cdr (assoc-equal *library-cdr* *b2-pair-products-selectors*))
                   (proof-eq (list *library-cdr* pair) (caddr pair-args)) nil nil nil 0 nil))
       (request (b2-tactics-tactics-implication lib premise goal nil))
       (step (b2-pair-products-pair-equality-premise-proof
              (cadddr (car request)) lib x (cadr conditions) (caddr conditions)
              test (list car-proof cdr-proof) goal))
       (closed (b2-tactics-tactics-implication lib premise goal (cons step lib))))
    (car closed)))

(defun b2-pair-products-tag-theorem (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (tagged (cadr parts))
       (cons-call (caddr parts))
       (request (b2-tactics-tactics-implication lib tagged cons-call nil))
       (step (b2-tactics-tactics-from-impossible
              lib cons-call (cadddr (car request)) nil (list *b2-pair-products-tag*) nil 1500 nil))
       (closed (b2-tactics-tactics-implication lib tagged cons-call (cons step lib))))
    (car closed)))

(defun b2-pair-products-theorem-pair (formula name)
  (cond ((member-equal name (table-values *b2-pair-products-selectors*))
         (proof-with-checked-results ((left (proof-term-at formula 1)))
           (proof-term-at left 1)))
        ((equal name *b2-pair-products-when-either*)
         (proof-with-checked-results ((right (proof-term-at formula 2)))
           (proof-term-at right 1)))
        (t (proof-with-checked-results ((first (proof-term-at formula 1))
                                        (test (proof-term-at first 1)))
             (proof-term-at test 1)))))

(defun b2-pair-products-pair-theorem (lib name formula)
  (cond ((equal name *b2-pair-products-rebuild*) (b2-pair-products-pair-reconstruction lib formula))
        ((equal name *b2-pair-products-equality*) (b2-pair-products-pair-equality lib formula))
        ((equal name *b2-pair-products-size*) (b2-pair-products-pair-size lib formula))
        ((equal name *b2-pair-products-tag-cons*) (b2-pair-products-tag-theorem lib formula))
        (t (proof-with-checked-results ((pair (b2-pair-products-theorem-pair formula name)))
             (cond ((integerp pair) '(:failure "tactic-rejected" ""))
                   ((endp (cdr pair))
                    '(:failure "tactic-rejected" ""))
                   ((endp (cddr pair))
                    '(:failure "tactic-rejected" ""))
                   ((consp (cdddr pair))
                    '(:failure "tactic-rejected" ""))
                   (t (b2-pair-products-cons-cases-with-proof lib (cadr pair) (caddr pair)
                                                              (list :theorem formula pair))))))))
