(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-sets-member* (proof-sym "MEMBER-EQUAL" "ACL2"))
(defconst *h4-book-sets-subset* (proof-sym "SUBSETP-EQUAL" "ACL2"))
(defconst *h4-book-sets-set-equiv* (proof-sym "SET-EQUIV" "ACL2"))
(defconst *h4-book-sets-boolean* (proof-sym "BOOLEANP" "ACL2"))
(defconst *h4-book-sets-item* (proof-sym "A" "ACL2"))

(defun h4-book-sets-nonempty-value (p shape)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first shape))
         (value (proof-term-at literal 1))
         (negative (proof-proof-assume pr value nil))
         (nil-value (h4-tactics-tactics-nil-value p negative))
         (as-nil (proof-proof-rewrite pr shape nil-value '(1 1)))
         (computed (proof-proof-compute pr (list *proof-consp* *proof-false*) *proof-nil*))
         (contradiction (proof-proof-rewrite pr as-nil computed '(1)))
         (tidied (proof-proof-tidy pr contradiction)))
      (proof-proof-front pr tidied value))))

(defun h4-book-sets-subset-parts (p step shape)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (sequence (proof-term-at literal 1))
         (expanded (h4-book-flatten-unfold-on-list p literal sequence shape))
         (rewritten (proof-proof-rewrite pr step expanded '(1))))
      (h4-tactics-tactics-conjunct p rewritten))))

(defun h4-book-sets-head-member (p sequence shape)
  (let ((pr (library-library-proof p))
        (term (list *h4-book-sets-member* (list *library-car* sequence) sequence)))
    (proof-with-checked-results
        ((expanded (h4-book-flatten-unfold-on-list p term sequence shape))
         (right (proof-rewritten-term expanded))
         (normal (h4-tactics-tactics-normalize p right nil nil nil nil))
         (selected (proof-proof-chain pr expanded (list normal)))
         (nonempty (h4-book-sets-nonempty-value p shape)))
      (proof-proof-transport pr nonempty selected))))

(defun h4-book-sets-member-extension-later (different p opened head tail membership)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((right (proof-rewritten-term opened))
         (branch (proof-proof-select pr right different))
         (selected (proof-proof-chain pr opened (list branch)))
         (cdr-cons (library-library-axiom p "CDR-CONS" (list head tail)))
         (rewritten (proof-proof-rewrite pr selected cdr-cons '(1 2 2))))
      (proof-proof-transport pr membership rewritten))))

(defun h4-book-sets-member-extension (p head tail membership)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first membership))
         (parts (proof-list-of-length literal 3)))
      (let* ((item (cadr parts))
             (cell (list *proof-cons* head tail))
             (source (list *h4-book-sets-member* item cell))
             (test (proof-eq item head)))
        (proof-with-checked-results
            ((opened (h4-book-flatten-unfold-on-list p source cell nil))
             (shape (proof-proof-fact pr "consp-cons"
                                      (list (list *library-x* head) (list *library-y* tail))))
             (yes (proof-proof-assume pr test t))
             (nonempty (h4-book-sets-nonempty-value p shape))
             (right (proof-rewritten-term opened))
             (branch (proof-proof-select pr right yes))
             (selected (proof-proof-chain pr opened (list branch)))
             (present (proof-proof-transport pr nonempty selected))
             (different (proof-proof-assume pr test nil))
             (later (h4-book-sets-member-extension-later
                     different p opened head tail membership)))
          (h4-tactics-tactics-case-of p source test present later))))))

(defun h4-book-sets-empty-subset (shape p goal claim)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((truth (proof-proof-prove pr *proof-true* nil nil))
         (equality (h4-book-flatten-unfold-on-list p goal *library-x* shape))
         (empty (proof-proof-transport pr truth equality)))
      (h4-tactics-tactics-imply p claim empty))))

(defun h4-book-sets-subset-extension-stop (shape p goal claim)
  (h4-book-sets-empty-subset shape p goal claim))

(defun h4-book-sets-subset-extension-extend (shape induction p given goal claim)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((parts (h4-book-sets-subset-parts p given shape))
         (head (h4-book-sets-member-extension p *library-z* *library-y* (car parts)))
         (child (h4-tactics-tactics-modus-ponens p induction (cadr parts)))
         (conjoined (h4-book-division-conjunction p (list head child)))
         (equality (h4-book-flatten-unfold-on-list p goal *library-x* shape))
         (result (proof-proof-transport pr conjoined equality)))
      (h4-tactics-tactics-imply p claim result))))

(defun h4-book-sets-subset-extension (p)
  (let* ((pr (library-library-proof p))
         (source (list *h4-book-sets-subset* *library-x* *library-y*))
         (goal (list *h4-book-sets-subset* *library-x*
                     (list *proof-cons* *library-z* *library-y*)))
         (claim (list *library-implies* source goal))
         (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((given (proof-proof-assume pr source t))
         (pair (proof-proof-assume pr test t))
         (induction (h4-book-flatten-cdr-induction-recurse pair p claim *library-x* nil))
         (extended (h4-book-sets-subset-extension-extend pair induction p given goal claim))
         (atom-case (proof-proof-assume pr test nil))
         (empty (h4-book-sets-subset-extension-stop atom-case p goal claim)))
      (h4-book-flatten-cdr-induction p claim *library-x* empty extended nil))))

(defun h4-book-sets-transfer-membership-stop (shape p membership member-term goal claim)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((equality (h4-book-flatten-unfold-on-list p member-term *library-x* shape))
         (impossible (proof-proof-rewrite pr membership equality '(1)))
         (conclusion (proof-proof-subsume
                       pr impossible (cons goal (cdr (proof-step-clause impossible))))))
      (h4-tactics-tactics-imply p claim conclusion))))

(defun h4-book-sets-transfer-membership-transfer-here (same p first)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results ((reversed (proof-proof-symmetric pr same)))
      (proof-proof-rewrite pr first reversed '(1 1)))))

(defun h4-book-sets-transfer-membership-transfer-later (different p lookup induction rest)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((member-tail (proof-proof-prove-if pr lookup different))
         (conjoined (h4-book-division-conjunction p (list member-tail rest))))
      (h4-tactics-tactics-modus-ponens p induction conjoined))))

(defun h4-book-sets-transfer-membership-transfer
    (shape induction p included membership member-term goal claim)
  (let ((pr (library-library-proof p))
        (test (proof-eq *h4-book-sets-item* (list *library-car* *library-x*))))
    (proof-with-checked-results
        ((parts (h4-book-sets-subset-parts p included shape))
         (equality (h4-book-flatten-unfold-on-list p member-term *library-x* shape))
         (lookup (proof-proof-rewrite pr membership equality '(1)))
         (same (proof-proof-assume pr test t))
         (here (h4-book-sets-transfer-membership-transfer-here same p (car parts)))
         (different (proof-proof-assume pr test nil))
         (later (h4-book-sets-transfer-membership-transfer-later
                 different p lookup induction (cadr parts)))
         (cases (h4-tactics-tactics-case-of p goal test here later)))
      (h4-tactics-tactics-imply p claim cases))))

(defun h4-book-sets-transfer-membership (p)
  (let* ((pr (library-library-proof p))
         (member-term (list *h4-book-sets-member* *h4-book-sets-item* *library-x*))
         (subset (list *h4-book-sets-subset* *library-x* *library-y*))
         (premise (proof-ite member-term subset *proof-false*))
         (goal (list *h4-book-sets-member* *h4-book-sets-item* *library-y*))
         (claim (list *library-implies* premise goal))
         (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((given (proof-proof-assume pr premise t))
         (parts (h4-tactics-tactics-conjunct p given))
         (pair (proof-proof-assume pr test t))
         (induction (h4-book-flatten-cdr-induction-recurse pair p claim *library-x* nil))
         (transferred (h4-book-sets-transfer-membership-transfer
                       pair induction p (cadr parts) (car parts) member-term goal claim))
         (atom-case (proof-proof-assume pr test nil))
         (empty (h4-book-sets-transfer-membership-stop
                 atom-case p (car parts) member-term goal claim)))
      (h4-book-flatten-cdr-induction p claim *library-x* empty transferred nil))))

(defun h4-book-sets-subset-transitivity-stop (shape p goal claim)
  (h4-book-sets-empty-subset shape p goal claim))

(defun h4-book-sets-subset-transitivity-compose
    (shape induction p included upper member-transfer goal claim)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((parts (h4-book-sets-subset-parts p included shape))
         (instance (proof-proof-instantiate
                    pr member-transfer
                    (list (list *h4-book-sets-item* (list *library-car* *library-x*))
                          (list *library-x* *library-y*) (list *library-y* *library-z*))))
         (first-premise (h4-book-division-conjunction p (list (car parts) upper)))
         (first-member (h4-tactics-tactics-modus-ponens p instance first-premise))
         (second-premise (h4-book-division-conjunction p (list (cadr parts) upper)))
         (child-subset (h4-tactics-tactics-modus-ponens p induction second-premise))
         (conjoined (h4-book-division-conjunction p (list first-member child-subset)))
         (equality (h4-book-flatten-unfold-on-list p goal *library-x* shape))
         (result (proof-proof-transport pr conjoined equality)))
      (h4-tactics-tactics-imply p claim result))))

(defun h4-book-sets-subset-transitivity (p)
  (let* ((pr (library-library-proof p))
         (first (list *h4-book-sets-subset* *library-x* *library-y*))
         (rest (list *h4-book-sets-subset* *library-y* *library-z*))
         (goal (list *h4-book-sets-subset* *library-x* *library-z*))
         (premise (proof-ite first rest *proof-false*))
         (claim (list *library-implies* premise goal))
         (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((given (proof-proof-assume pr premise t))
         (parts (h4-tactics-tactics-conjunct p given))
         (member-transfer (h4-book-sets-transfer-membership p))
         (pair (proof-proof-assume pr test t))
         (induction (h4-book-flatten-cdr-induction-recurse pair p claim *library-x* nil))
         (composed (h4-book-sets-subset-transitivity-compose
                    pair induction p (car parts) (cadr parts) member-transfer goal claim))
         (atom-case (proof-proof-assume pr test nil))
         (empty (h4-book-sets-subset-transitivity-stop atom-case p goal claim)))
      (h4-book-flatten-cdr-induction p claim *library-x* empty composed nil))))

(defun h4-book-sets-select-equal (p selector equality)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first equality))
         (sides (proof-list-of-length (cdr literal) 2)))
      (let ((left (car sides))
            (right (cadr sides))
            (prefix (if (equal selector *library-car*) "CAR-CONS" "CDR-CONS")))
        (proof-with-checked-results
            ((lifted (h4-book-flatten-rewrite-argument p (list selector left) 1 equality))
             (left-axiom (library-library-axiom p prefix (cdr left)))
             (reversed (proof-proof-symmetric pr left-axiom))
             (right-axiom (library-library-axiom p prefix (cdr right))))
          (proof-proof-chain pr reversed (list lifted right-axiom)))))))

(defun h4-book-sets-subset-of-equal-fixes-stop (shape p goal claim)
  (h4-book-sets-empty-subset shape p goal claim))

(defun h4-book-sets-subset-of-equal-fixes-proceed-fix-on-right (other-shape p fixed-y eq-on-left)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((opened (h4-book-flatten-unfold-on-list p fixed-y *library-y* other-shape)))
      (proof-proof-rewrite pr eq-on-left opened '(1 2)))))

(defun h4-book-sets-subset-of-equal-fixes-proceed-pair
    (other-shape p fixed-y eq-on-left induction extension goal shape)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((fixed-equal (h4-book-sets-subset-of-equal-fixes-proceed-fix-on-right
                      other-shape p fixed-y eq-on-left))
         (equal-head (h4-book-sets-select-equal p *library-car* fixed-equal))
         (equal-tail (h4-book-sets-select-equal p *library-cdr* fixed-equal))
         (at-head (h4-book-sets-head-member p *library-y* other-shape))
         (reversed (proof-proof-symmetric pr equal-head))
         (member-step (proof-proof-rewrite pr at-head reversed '(1 1)))
         (child (h4-tactics-tactics-modus-ponens p induction equal-tail))
         (extension-instance
          (proof-proof-instantiate
           pr extension
           (list (list *library-x* (list *library-cdr* *library-x*))
                 (list *library-y* (list *library-cdr* *library-y*))
                 (list *library-z* (list *library-car* *library-y*)))))
         (extended (h4-tactics-tactics-modus-ponens p extension-instance child))
         (elimination (library-library-axiom p "CAR-CDR-ELIM" (list *library-y*)))
         (restored (h4-tactics-tactics-modus-ponens p elimination other-shape))
         (included (proof-proof-rewrite pr extended restored '(1 2)))
         (conjoined (h4-book-division-conjunction p (list member-step included)))
         (opened (h4-book-flatten-unfold-on-list p goal *library-x* shape)))
      (proof-proof-transport pr conjoined opened))))

(defun h4-book-sets-subset-of-equal-fixes-proceed-atom (other-shape p fixed-y eq-on-left goal)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((fixed-equal (h4-book-sets-subset-of-equal-fixes-proceed-fix-on-right
                      other-shape p fixed-y eq-on-left))
         (literal (proof-step-first fixed-equal))
         (sides (proof-list-of-length (cdr literal) 2))
         (shape-left (proof-proof-fact pr "consp-cons"
                                           (seq-zip (list *library-x* *library-y*) (cdar sides))))
         (equality (h4-book-sets-subset-of-equal-fixes-proceed-fix-on-right
                   other-shape p fixed-y eq-on-left))
         (impossible (proof-proof-rewrite pr shape-left equality '(1 1)))
         (computed (proof-proof-compute pr (list *proof-consp* *proof-false*) *proof-nil*))
         (contradiction (proof-proof-rewrite pr impossible computed '(1))))
      (proof-proof-subsume pr contradiction (cons goal (cdr (proof-step-clause contradiction)))))))

(defun h4-book-sets-subset-of-equal-fixes-proceed
    (shape induction p fixed-x fixed-y given extension goal claim)
  (let ((pr (library-library-proof p))
        (test (list *proof-consp* *library-y*)))
    (proof-with-checked-results
        ((x-fixed (h4-book-flatten-unfold-on-list p fixed-x *library-x* shape))
         (eq-on-left (proof-proof-rewrite pr given x-fixed '(1 1)))
         (pair (proof-proof-assume pr test t))
         (paired (h4-book-sets-subset-of-equal-fixes-proceed-pair
                  pair p fixed-y eq-on-left induction extension goal shape))
         (atom-case (proof-proof-assume pr test nil))
         (atomic (h4-book-sets-subset-of-equal-fixes-proceed-atom
                  atom-case p fixed-y eq-on-left goal))
         (cases (h4-tactics-tactics-case-of p goal test paired atomic)))
      (h4-tactics-tactics-imply p claim cases))))

(defun h4-book-sets-subset-of-equal-fixes (p)
  (let* ((pr (library-library-proof p))
         (fixed-x (list *h4-book-flatten-list-fix* *library-x*))
         (fixed-y (list *h4-book-flatten-list-fix* *library-y*))
         (premise (proof-eq fixed-x fixed-y))
         (goal (list *h4-book-sets-subset* *library-x* *library-y*))
         (claim (list *library-implies* premise goal))
         (test (list *proof-consp* *library-x*))
         (changes (list (list *library-y* (list *library-cdr* *library-y*)))))
    (proof-with-checked-results
        ((extension (h4-book-sets-subset-extension p))
         (given (proof-proof-assume pr premise t))
         (pair (proof-proof-assume pr test t))
         (induction (h4-book-flatten-cdr-induction-recurse pair p claim *library-x* changes))
         (each (h4-book-sets-subset-of-equal-fixes-proceed
                pair induction p fixed-x fixed-y given extension goal claim))
         (atom-case (proof-proof-assume pr test nil))
         (empty (h4-book-sets-subset-of-equal-fixes-stop atom-case p goal claim)))
      (h4-book-flatten-cdr-induction p claim *library-x* empty each changes))))

(defun h4-book-sets-boolean-result-result (value tests p induction)
  (declare (ignore tests))
  (let ((target (list *h4-book-sets-boolean* value)))
    (cond ((or (equal value *proof-true*) (equal value *proof-false*))
           (h4-tactics-tactics-establish p target nil
                                            (list *h4-book-sets-boolean* (proof-cl "EQ")) nil nil))
          ((null induction) '(:failure "InapplicableStep" ""))
          (t (proof-with-checked-results ((literal (proof-step-first induction)))
               (if (equal target literal) induction '(:failure "InapplicableStep" "")))))))

(defun h4-book-sets-boolean-result-by-value (n p value tests induction)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h4-book-sets-boolean-result-by-value")
    (let ((pr (library-library-proof p))
          (template (list *h4-book-sets-boolean* *proof-result*)))
      (cond
       ((proof-is-call value *proof-if*)
        (proof-with-checked-results
            ((branches (proof-list-of-length (cdr value) 3))
             (yes (h4-book-sets-boolean-result-by-value
                   (1- n) p (cadr branches) (append tests (list (list (car branches) t))) induction))
             (no (h4-book-sets-boolean-result-by-value
                  (1- n) p (caddr branches) (append tests (list (list (car branches) nil))) induction)))
          (proof-by-value-join pr value template yes no)))
       ((null value) '(:failure "failure" ""))
       ((and (proof-compound value) (proof-compound (car value)))
        (proof-with-checked-results
            ((equality (proof-proof-beta pr value))
             (body (proof-rewritten-term equality))
             (opened (h4-book-sets-boolean-result-by-value (1- n) p body tests induction))
             (reversed (proof-proof-symmetric pr equality)))
          (proof-proof-rewrite-result pr opened reversed template *proof-result*)))
       (t (proof-with-checked-results
              ((step (h4-book-sets-boolean-result-result value tests p induction)))
            (proof-proof-by-value pr value template (list (cons (list value tests) step)) tests)))))))

(defun h4-book-sets-boolean-result (p equation induction)
  (proof-with-checked-results
      ((right (proof-rewritten-term equation))
       (result (h4-book-sets-boolean-result-by-value 1000000 p right nil induction)))
    (library-library-transport-argument p result equation 1)))

(defun h4-book-sets-boolean-subset-case (shape induction p call)
  (proof-with-checked-results
      ((equation (h4-book-flatten-unfold-on-list p call *library-x* shape)))
    (h4-book-sets-boolean-result p equation induction)))

(defun h4-book-sets-boolean-subset (p)
  (let* ((pr (library-library-proof p))
         (call (list *h4-book-sets-subset* *library-x* *library-y*))
         (goal (list *h4-book-sets-boolean* call))
         (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((pair (proof-proof-assume pr test t))
         (induction (h4-book-flatten-cdr-induction-recurse pair p goal *library-x* nil))
         (positive (h4-book-sets-boolean-subset-case pair induction p call))
         (atom-case (proof-proof-assume pr test nil))
         (negative (h4-book-sets-boolean-subset-case atom-case nil p call)))
      (h4-book-flatten-cdr-induction p goal *library-x* negative positive nil))))

(defun h4-book-sets-set-pair (p left right)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((left-literal (proof-step-first left))
         (x (proof-term-at left-literal 1))
         (right-literal (proof-step-first right))
         (y (proof-term-at right-literal 1))
         (conjoined (h4-book-division-conjunction p (list left right)))
         (opened (proof-proof-unfold pr (list *h4-book-sets-set-equiv* x y))))
      (proof-proof-transport pr conjoined opened))))

(defun h4-book-sets-set-parts (p step)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first step))
         (opened (proof-proof-unfold pr literal))
         (rewritten (proof-proof-rewrite pr step opened '(1))))
      (h4-tactics-tactics-conjunct p rewritten))))

(defun h4-book-sets-set-equivalence (p)
  (let* ((pr (library-library-proof p))
         (x *library-x*) (y *library-y*) (z *library-z*)
         (comparison (list *h4-book-sets-set-equiv* x y))
         (reverse-comparison (list *h4-book-sets-set-equiv* y x)))
    (proof-with-checked-results
        ((bool (h4-book-sets-boolean-subset p))
         (subset-bool (proof-proof-instantiate pr bool (list (list x y) (list y x))))
         (opened (proof-proof-unfold pr comparison))
         (typed (h4-book-sets-boolean-result p opened subset-bool))
         (identical-fixed (proof-proof-reflexive pr (list *h4-book-flatten-list-fix* x)))
         (of-fixes (h4-book-sets-subset-of-equal-fixes p))
         (reflexive (proof-proof-instantiate pr of-fixes (list (list y x))))
         (same (h4-tactics-tactics-modus-ponens p reflexive identical-fixed))
         (equivalence (h4-book-sets-set-pair p same same))
         (given-comparison (proof-proof-assume pr comparison t))
         (parts (h4-book-sets-set-parts p given-comparison))
         (reverse-step (h4-book-sets-set-pair p (cadr parts) (car parts)))
         (symmetric (h4-tactics-tactics-imply
                     p (list *library-implies* comparison reverse-comparison) reverse-step)))
      (let* ((last (list *h4-book-sets-set-equiv* y z))
             (premise (proof-ite comparison last *proof-false*)))
        (proof-with-checked-results
            ((given (proof-proof-assume pr premise t))
             (both (h4-tactics-tactics-conjunct p given))
             (left-parts (h4-book-sets-set-parts p (car both)))
             (right-parts (h4-book-sets-set-parts p (cadr both)))
             (rule (h4-book-sets-subset-transitivity p))
             (forward-premise (h4-book-division-conjunction
                               p (list (car left-parts) (car right-parts))))
             (xz (h4-tactics-tactics-modus-ponens p rule forward-premise))
             (reverse-rule (proof-proof-instantiate pr rule (list (list x z) (list z x))))
             (reverse-premise (h4-book-division-conjunction
                               p (list (cadr right-parts) (cadr left-parts))))
             (zx (h4-tactics-tactics-modus-ponens p reverse-rule reverse-premise))
             (result (h4-book-sets-set-pair p xz zx))
             (transitive (h4-tactics-tactics-imply
                          p (list *library-implies* premise (list *h4-book-sets-set-equiv* x z))
                          result)))
          (h4-book-division-conjunction p (list typed equivalence symmetric transitive)))))))

(defun h4-book-sets-set-refinement (p formula)
  (let ((pr (library-library-proof p)))
    (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2)))
      (let ((premise (car parts)))
        (proof-with-checked-results
            ((arguments (proof-list-of-length (cdr premise) 2))
             (given (proof-proof-assume pr premise t))
             (opened (proof-proof-unfold pr premise))
             (right (proof-rewritten-term opened))
             (normal (h4-tactics-tactics-normalize p right nil nil nil nil))
             (chain (proof-proof-chain pr opened (list normal)))
             (equal-fixes (proof-proof-rewrite pr given chain '(1)))
             (rule (h4-book-sets-subset-of-equal-fixes p))
             (forward-rule (proof-proof-instantiate
                            pr rule (list (list *library-x* (car arguments))
                                          (list *library-y* (cadr arguments)))))
             (first (h4-tactics-tactics-modus-ponens p forward-rule equal-fixes))
             (reverse-rule (proof-proof-instantiate
                            pr rule (list (list *library-x* (cadr arguments))
                                          (list *library-y* (car arguments)))))
             (reversed (proof-proof-symmetric pr equal-fixes))
             (second (h4-tactics-tactics-modus-ponens p reverse-rule reversed))
             (result (h4-book-sets-set-pair p first second)))
          (h4-tactics-tactics-imply p formula result))))))

(defun h4-book-sets-set-shape (formula)
  (cond ((proof-is-call formula *library-implies*)
         (proof-with-checked-results ((premise (proof-term-at formula 1)))
           (if (proof-is-call premise *h4-book-flatten-list-equiv*)
               (proof-with-checked-results ((goal (proof-term-at formula 2)))
                 (equal goal (cons *h4-book-sets-set-equiv* (cdr premise))))
             nil)))
        ((proof-is-call formula *proof-if*)
         (proof-with-checked-results ((test (proof-term-at formula 1)))
           (if (proof-is-call test *h4-book-sets-boolean*)
               (proof-with-checked-results ((comparison (proof-term-at test 1)))
                 (if (equal comparison (list *h4-book-sets-set-equiv* *library-x* *library-y*))
                     (proof-with-checked-results ((otherwise-term (proof-term-at formula 3)))
                       (equal otherwise-term *proof-false*))
                   nil))
             nil)))
        (t nil)))

(defun h4-book-sets-set-proof (p formula)
  (if (assoc-equal *h4-book-sets-set-equiv* (proof-proof-definitions (library-library-proof p)))
      (proof-with-checked-results ((matches (h4-book-sets-set-shape formula)))
        (if matches
            (let* ((step (if (proof-is-call formula *library-implies*)
                             (h4-book-sets-set-refinement p formula)
                           (h4-book-sets-set-equivalence p)))
                   (first (if (failure-p step) step (proof-step-first step))))
              (cond ((not (failure-p first)) (and (equal first formula) step))
                    ((member-equal (cadr first) '("InapplicableStep" "assertion")) nil)
                    (t first)))
          nil))
    nil))
