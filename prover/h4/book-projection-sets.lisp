(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun h4-book-projection-sets-step-argument (step index)
  (proof-with-checked-results
    ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h4-book-projection-sets-projected-member (p equation)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((result (h4-book-projection-sets-step-argument equation 2))
       (arguments (if (integerp result)
                      '(:failure "failure" "")
                    (cdr result)))
       (shape (proof-proof-fact
               proof "consp-cons" (seq-zip (list *library-x* *library-y*) arguments)))
       (member-step (h4-book-sets-head-member p result shape))
       (head (library-library-axiom p "CAR-CONS" arguments))
       (member-step (proof-proof-rewrite proof member-step head (list 1 1))))
      (library-library-transport-argument p member-step equation 2))))

(defun h4-book-projection-sets-projected-membership-atom
  (shape p belongs sequence goal formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((literal (proof-step-first belongs))
       (opened (h4-book-flatten-unfold-on-list p literal sequence shape))
       (impossible (proof-proof-rewrite proof belongs opened (list 1)))
       (weakened (proof-proof-subsume
                  proof impossible (cons goal (cdr (proof-step-clause impossible))))))
      (h4-tactics-tactics-imply p formula weakened))))

(defun h4-book-projection-sets-projected-membership-pair-here
  (same p shape-element goal shape provide)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((exists (proof-proof-rewrite proof shape-element same (list 1 1)))
       (equation (h4-book-projections-open-selected
                  p (caddr goal) (list shape exists) provide nil))
       (member-step (h4-book-projection-sets-projected-member p equation))
       (symmetric (proof-proof-symmetric proof same)))
      (proof-proof-rewrite proof member-step symmetric (list 1 1 1)))))

(defun h4-book-projection-sets-projected-membership-pair-there-branch
  (head-shape p goal shape provide item projection tail)
  (proof-with-checked-results
    ((equation (h4-book-projections-open-selected
                p (caddr goal) (list shape head-shape) provide nil))
     (literal (proof-step-first head-shape))
     (in-list
      (if (proof-is-call literal *proof-consp*)
          (proof-with-checked-results
            ((result (h4-book-projection-sets-step-argument equation 2))
             (head (proof-term-at result 1)))
            (h4-book-sets-member-extension p head (list projection tail) item))
        item)))
    (library-library-transport-argument p in-list equation 2)))

(defun h4-book-projection-sets-projected-membership-pair-there
  (different p belongs shape provide child shape-element sequence goal projection)
  (let ((proof (library-library-proof p))
        (tail (list *library-cdr* sequence))
        (test (list *proof-consp* (list *library-car* sequence))))
    (proof-with-checked-results
      ((literal (proof-step-first belongs))
       (opened (h4-book-projections-open-selected
                p literal (list shape different) provide nil))
       (tail-member (proof-proof-rewrite proof belongs opened (list 1)))
       (premise (h4-book-division-conjunction p (list shape-element tail-member)))
       (item (h4-tactics-tactics-modus-ponens p child premise))
       (positive (proof-proof-assume proof test t))
       (yes (h4-book-projection-sets-projected-membership-pair-there-branch
             positive p goal shape provide item projection tail))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-projection-sets-projected-membership-pair-there-branch
            negative p goal shape provide item projection tail)))
      (h4-tactics-tactics-case-of p goal test yes no))))

(defun h4-book-projection-sets-projected-membership-pair
  (shape child p element sequence shape-element goal provide belongs projection formula)
  (let ((test (proof-eq element (list *library-car* sequence)))
        (proof (library-library-proof p)))
    (proof-with-checked-results
      ((positive (proof-proof-assume proof test t))
       (yes (h4-book-projection-sets-projected-membership-pair-here
             positive p shape-element goal shape provide))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-projection-sets-projected-membership-pair-there
            negative p belongs shape provide child shape-element sequence goal projection))
       (cases (h4-tactics-tactics-case-of p goal test yes no)))
      (h4-tactics-tactics-imply p formula cases))))

(defun h4-book-projection-sets-projected-membership (p projection)
  (let* ((element *library-x*)
         (sequence *library-y*)
         (selector (if (equal projection *h4-book-projections-keys*)
                       *library-car*
                     *library-cdr*))
         (guard (proof-ite (list *proof-consp* element)
                           (list *h4-book-sets-member* element sequence) *proof-false*))
         (goal (list *h4-book-sets-member*
                     (list selector element) (list projection sequence)))
         (formula (list *library-implies* guard goal))
         (test (list *proof-consp* sequence))
         (proof (library-library-proof p)))
    (proof-with-checked-results
      ((given (proof-proof-assume proof guard t))
       (conjuncts (h4-tactics-tactics-conjunct p given))
       (provide (h4-book-finite-reduction-provider p))
       (positive (proof-proof-assume proof test t))
       (child (h4-book-flatten-cdr-induction-recurse positive p formula sequence nil))
       (yes (h4-book-projection-sets-projected-membership-pair
             positive child p element sequence (car conjuncts) goal provide
             (cadr conjuncts) projection formula))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-projection-sets-projected-membership-atom
            negative p (cadr conjuncts) sequence goal formula)))
      (h4-book-flatten-cdr-induction p formula sequence no yes nil))))

(defun h4-book-projection-sets-projected-subset-empty (shape p goal provide formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((project (h4-book-projections-open-selected p (cadr goal) (list shape) provide nil))
       (lifted (h4-book-flatten-rewrite-argument p goal 1 project))
       (rhs (h4-book-projection-sets-step-argument lifted 2))
       (base (h4-book-flatten-unfold-on-list p rhs *proof-false* nil))
       (truth (proof-proof-prove proof *proof-true* nil nil))
       (joined (proof-proof-chain proof lifted (list base)))
       (transported (proof-proof-transport proof truth joined)))
      (h4-tactics-tactics-imply p formula transported))))

(defun h4-book-projection-sets-projected-subset-pair-branch
  (head p goal shape provide include-tail member-step entry present)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((mapped (h4-book-projections-open-selected
                p (cadr goal) (list shape head) provide nil))
       (literal (proof-step-first head)))
      (if (not (proof-is-call literal *proof-consp*))
          (library-library-transport-argument p include-tail mapped 1)
        (proof-with-checked-results
          ((rule (proof-proof-instantiate proof member-step (list (list *library-x* entry))))
           (premise (h4-book-division-conjunction p (list head present)))
           (witness (h4-tactics-tactics-modus-ponens p rule premise))
           (sequence (h4-book-projection-sets-step-argument mapped 2))
           (equation (h4-book-flatten-unfold-on-list
                      p (list *h4-book-sets-subset* sequence (caddr goal)) sequence nil))
           (cdr-cons (library-library-axiom p "CDR-CONS" (cdr sequence)))
           (equation (proof-proof-rewrite proof equation cdr-cons (list 1 2 2 1)))
           (combined (h4-book-division-conjunction p (list witness include-tail)))
           (included (proof-proof-transport proof combined equation)))
          (library-library-transport-argument p included mapped 1))))))

(defun h4-book-projection-sets-projected-subset-pair
  (shape child p given goal provide member-step formula)
  (let* ((proof (library-library-proof p))
         (entry (list *library-car* *library-x*))
         (test (list *proof-consp* entry)))
    (proof-with-checked-results
      ((parts (h4-book-sets-subset-parts p given shape))
       (include-tail (h4-tactics-tactics-modus-ponens p child (cadr parts)))
       (positive (proof-proof-assume proof test t))
       (yes (h4-book-projection-sets-projected-subset-pair-branch
             positive p goal shape provide include-tail member-step entry (car parts)))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-projection-sets-projected-subset-pair-branch
            negative p goal shape provide include-tail member-step entry (car parts)))
       (cases (h4-tactics-tactics-case-of p goal test yes no)))
      (h4-tactics-tactics-imply p formula cases))))

(defun h4-book-projection-sets-projected-subset (p projection)
  (let* ((premise (list *h4-book-sets-subset* *library-x* *library-y*))
         (goal (list *h4-book-sets-subset*
                     (list projection *library-x*) (list projection *library-y*)))
         (formula (list *library-implies* premise goal))
         (test (list *proof-consp* *library-x*))
         (proof (library-library-proof p)))
    (proof-with-checked-results
      ((given (proof-proof-assume proof premise t))
       (member-step (h4-book-projection-sets-projected-membership p projection))
       (provide (h4-book-finite-reduction-provider p))
       (positive (proof-proof-assume proof test t))
       (child (h4-book-flatten-cdr-induction-recurse positive p formula *library-x* nil))
       (yes (h4-book-projection-sets-projected-subset-pair
             positive child p given goal provide member-step formula))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-projection-sets-projected-subset-empty negative p goal provide formula)))
      (h4-book-flatten-cdr-induction p formula *library-x* no yes nil))))

(defun h4-book-projection-sets-mapped-set-equiv (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((guard (proof-term-at formula 1))
       (given (proof-proof-assume proof guard t))
       (parts (h4-book-sets-set-parts p given))
       (goal (proof-term-at formula 2))
       (sides (proof-list-of-length goal 3))
       (left (proof-list-of-length (cadr sides) 2))
       (right (proof-list-of-length (caddr sides) 2))
       (rule (h4-book-projection-sets-projected-subset p (car left))))
      (let ((a (cadr left))
            (b (cadr right)))
        (proof-with-checked-results
          ((forward (proof-proof-instantiate proof rule
                                             (list (list *library-x* a) (list *library-y* b))))
           (forward (h4-tactics-tactics-modus-ponens p forward (car parts)))
           (backward (proof-proof-instantiate proof rule
                                              (list (list *library-x* b) (list *library-y* a))))
           (backward (h4-tactics-tactics-modus-ponens p backward (cadr parts)))
           (joined (h4-book-sets-set-pair p forward backward)))
          (h4-tactics-tactics-imply p formula joined))))))

(defun h4-book-projection-sets-pairlis-values-unequal-shapes
  (p longer shorter cons-shape atom-shape same provide goal formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((positive (h4-book-arity-length-positive p longer cons-shape))
       (positive (proof-proof-rewrite proof positive same (list 1 2)))
       (zero-length (h4-book-projections-open-selected
                     p (list *library-len* shorter) (list atom-shape) provide nil))
       (impossible (proof-proof-rewrite proof positive zero-length (list 1 2)))
       (zero (library-library-axiom p "ZERO" nil))
       (conflict (proof-proof-cut proof impossible zero))
       (weakened (proof-proof-subsume proof conflict
                                       (cons goal (proof-step-clause conflict)))))
      (h4-tactics-tactics-imply p formula weakened))))

(defun h4-book-projection-sets-pairlis-values-tail
  (p length-step result keys values first-shape second-shape child)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((literal (proof-step-first length-step))
       (sides (proof-list-of-length (cdr literal) 2))
       (a-type (library-library-type-of p (car sides) nil))
       (b-type (library-library-type-of p (cadr sides) nil))
       (cancelled (proof-proof-use
                   proof *h4-book-updates-equal-predecessors*
                   (list (list *library-x* (car sides)) (list *library-y* (cadr sides)))
                   (list a-type b-type)))
       (residual (proof-proof-transport proof length-step cancelled))
       (key-tail (h4-book-arity-predecessor-length p keys first-shape))
       (residual (proof-proof-rewrite proof residual key-tail (list 1 1)))
       (value-tail (h4-book-arity-predecessor-length p values second-shape))
       (residual (proof-proof-rewrite proof residual value-tail (list 1 2)))
       (induction (h4-tactics-tactics-modus-ponens p child residual)))
      (proof-proof-rewrite proof result induction (list 1 2 2)))))

(defun h4-book-projection-sets-pairlis-values-visit-branch
  (second-shape first-shape child p keys values length-step goal provide formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((first-literal (proof-step-first first-shape))
       (second-literal (proof-step-first second-shape)))
      (let ((has-keys (proof-is-call first-literal *proof-consp*))
            (has-values (proof-is-call second-literal *proof-consp*)))
        (if (not (equal has-keys has-values))
            (proof-with-checked-results
              ((same (if has-keys length-step (proof-proof-symmetric proof length-step))))
              (h4-book-projection-sets-pairlis-values-unequal-shapes
               p (if has-keys keys values) (if has-keys values keys)
               (if has-keys first-shape second-shape) (if has-keys second-shape first-shape)
               same provide goal formula))
          (proof-with-checked-results
            ((initial (h4-book-projections-open-selected
                       p (list *h4-book-arity-pairlis* keys values) (list first-shape) provide nil))
             (left (proof-term-at goal 1))
             (lifted (h4-book-flatten-rewrite-argument p left 1 initial))
             (rhs (h4-book-projection-sets-step-argument lifted 2))
             (selected (h4-book-projections-open-selected p rhs nil provide nil))
             (result (proof-proof-chain proof lifted (list selected)))
             (result (if has-keys
                         (h4-book-projection-sets-pairlis-values-tail
                          p length-step result keys values first-shape second-shape child)
                       result))
             (right (proof-term-at goal 2))
             (unfolded (h4-book-flatten-unfold-on-list p right values second-shape))
             (symmetric (proof-proof-symmetric proof unfolded))
             (joined (proof-proof-chain proof result (list symmetric))))
            (h4-tactics-tactics-imply p formula joined)))))))

(defun h4-book-projection-sets-pairlis-values-visit
  (first-shape child p keys values length-step goal provide formula)
  (let ((test (list *proof-consp* values))
        (proof (library-library-proof p)))
    (proof-with-checked-results
      ((positive (proof-proof-assume proof test t))
       (yes (h4-book-projection-sets-pairlis-values-visit-branch
             positive first-shape child p keys values length-step goal provide formula))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-projection-sets-pairlis-values-visit-branch
            negative first-shape child p keys values length-step goal provide formula)))
      (h4-tactics-tactics-case-of p formula test yes no))))

(defun h4-book-projection-sets-pairlis-values (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((guard (proof-term-at formula 1))
       (length-step (proof-proof-assume proof guard t))
       (literal (proof-step-first length-step))
       (sides (proof-list-of-length literal 3))
       (keys-length (proof-list-of-length (cadr sides) 2))
       (values-length (proof-list-of-length (caddr sides) 2))
       (goal (proof-term-at formula 2))
       (provide (h4-book-finite-reduction-provider p)))
      (let* ((keys (cadr keys-length))
             (values (cadr values-length))
             (changes (list (list values (list *library-cdr* values))))
             (test (list *proof-consp* keys)))
        (proof-with-checked-results
          ((positive (proof-proof-assume proof test t))
           (child (h4-book-flatten-cdr-induction-recurse positive p formula keys changes))
           (yes (h4-book-projection-sets-pairlis-values-visit
                 positive child p keys values length-step goal provide formula))
           (negative (proof-proof-assume proof test nil))
           (no (h4-book-projection-sets-pairlis-values-visit
                negative nil p keys values length-step goal provide formula)))
          (h4-book-flatten-cdr-induction p formula keys no yes changes))))))

(defun h4-book-projection-sets-all-lengths (terms)
  (or (endp terms)
      (and (proof-is-call (car terms) *library-len*)
           (h4-book-projection-sets-all-lengths (cdr terms)))))

(defun h4-book-projection-sets-length-arguments (terms)
  (if (endp terms)
      nil
    (proof-with-checked-results
      ((argument (proof-term-at (car terms) 1))
       (rest (h4-book-projection-sets-length-arguments (cdr terms))))
      (cons argument rest))))

(defun h4-book-projection-sets-mapped-projection (p formula goal a b projections)
  (if (endp projections)
      nil
    (let ((projection (car projections)))
      (if (equal (cdr goal) (list (list projection a) (list projection b)))
          (h4-book-projection-sets-mapped-set-equiv p formula)
        (h4-book-projection-sets-mapped-projection p formula goal a b (cdr projections))))))

(defun h4-book-projection-sets-projection-set-proof (p formula)
  (and (proof-is-call formula *library-implies*)
       (proof-with-checked-results
         ((parts (proof-list-of-length formula 3)))
         (let ((guard (cadr parts))
               (goal (caddr parts)))
           (cond
            ((and (proof-is-call guard *proof-equal*)
                  (h4-book-projection-sets-all-lengths (cdr guard)))
             (proof-with-checked-results
               ((arguments (h4-book-projection-sets-length-arguments (cdr guard)))
                (arguments (proof-list-of-length arguments 2)))
               (let ((keys (car arguments))
                     (values (cadr arguments)))
                 (and (equal goal
                             (proof-eq (list *h4-book-projections-values*
                                             (list *h4-book-arity-pairlis* keys values))
                                       (list *h4-book-flatten-list-fix* values)))
                      (h4-book-projection-sets-pairlis-values p formula)))))
            ((and (proof-is-call guard *h4-book-sets-set-equiv*)
                  (proof-is-call goal *h4-book-sets-set-equiv*))
             (proof-with-checked-results
               ((sides (proof-list-of-length guard 3)))
               (h4-book-projection-sets-mapped-projection
                p formula goal (cadr sides) (caddr sides) *h4-book-projections-projections*))))))))
