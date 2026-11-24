(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-projections-keys* (proof-sym "ALIST-KEYS" "ACL2"))
(defconst *h4-book-projections-values* (proof-sym "ALIST-VALS" "ACL2"))
(defconst *h4-book-projections-rev* (proof-sym "REV" "ACL2"))
(defconst *h4-book-projections-projections*
  (list *h4-book-projections-keys* *h4-book-projections-values*))

(defun h4-book-projections-step-argument (step index)
  (proof-with-checked-results
    ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h4-book-projections-open-selected (p call evidence provide rewrites)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((initial (proof-proof-unfold proof call))
       (body (h4-book-projections-step-argument initial 2))
       (reduced (h4-tactics-tactics-normalize
                 p body evidence *h4-book-flatten-logic* rewrites provide)))
      (if (h4-tactics-request-p reduced)
          reduced
        (proof-proof-chain proof initial (list reduced))))))

(defun h4-book-projections-difference (left right index)
  (if (endp left)
      nil
    (let* ((same (equal (car left) (car right)))
           (rest (h4-book-projections-difference
                  (cdr left) (cdr right) (1+ index))))
      (if same
          rest
        (cons index rest)))))

(defun h4-book-projections-list-equiv-shape (formula)
  (and (proof-is-call formula *library-implies*)
    (proof-with-checked-results
      ((premise (proof-term-at formula 1)))
      (and (proof-is-call premise *h4-book-flatten-list-equiv*)
        (proof-with-checked-results
          ((goal (proof-term-at formula 2)))
          (and (proof-is-call goal *proof-equal*)
            (proof-with-checked-results
              ((arguments (proof-list-of-length (cdr premise) 2))
               (sides (proof-list-of-length (cdr goal) 2)))
              (let ((a (car arguments))
                    (b (cadr arguments))
                    (left (car sides))
                    (right (cadr sides)))
                (and (and (not (equal a b))
                           (not (proof-compound a))
                           (not (proof-compound b))
                           (proof-compound left)
                           (proof-compound right)
                           (equal (len left) (len right)))
                  (proof-with-checked-results
                    ((head (proof-term-at left 0)))
                    (and (and (not (proof-compound head))
                               (equal head (car right)))
                      (let* ((difference (h4-book-projections-difference
                                          (cdr left) (cdr right) 1))
                             (index (car difference)))
                        (and (and (consp difference)
                                   (endp (cdr difference))
                                   (equal (nth index left) a)
                                   (equal (nth index right) b))
                          (list left right index))))))))))))))

(defun h4-book-projections-spine-test (test)
  (if (or (proof-is-call test *proof-not*) (proof-is-call test *proof-if*))
      (if (consp (cdr test))
          (h4-book-projections-spine-test (cadr test))
        '(:failure "failure" ""))
    test))

; A residual conditional requests a split on its test.
(defun h4-book-projections-list-fix-compare-result
  (evidence p start call case-rewrites hypothesis provide)
  (let ((proof (library-library-proof p))
        (rewrites (if hypothesis
                      (append case-rewrites (list hypothesis))
                    case-rewrites)))
    (proof-with-checked-results
      ((started (h4-book-projections-step-argument start 2))
       (opened (h4-book-projections-open-selected p started evidence provide rewrites))
       (first (proof-proof-chain proof start (list opened)))
       (second (h4-book-projections-open-selected p call evidence provide case-rewrites))
       (left (h4-book-projections-step-argument first 2))
       (right (h4-book-projections-step-argument second 2)))
      (if (equal left right)
          (proof-with-checked-results
            ((reverse-step (proof-proof-symmetric proof second)))
            (proof-proof-chain proof first (list reverse-step)))
        (let ((residual (if (proof-is-call left *proof-if*) left right)))
          (if (or (< 4 (len evidence)) (not (proof-is-call residual *proof-if*)))
              '(:failure "Unproved" "")
            (proof-with-checked-results
              ((outer-test (proof-term-at residual 1))
               (test (h4-book-projections-spine-test outer-test)))
              (list :cases test))))))))

(mutual-recursion
 (defun h4-book-projections-agrees-with-list-fix-compare-under
   (n evidence p start call case-rewrites hypothesis provide goal)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "h4-book-projections-agrees-with-list-fix-compare-under")
     (h4-book-projections-list-fix-compare-cases
      (1- n) (h4-book-projections-list-fix-compare-result
              evidence p start call case-rewrites hypothesis provide)
      evidence p start call case-rewrites hypothesis provide goal)))
 (defun h4-book-projections-list-fix-compare-cases
   (n result evidence p start call case-rewrites hypothesis provide goal)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "Fuel" "h4-book-projections-list-fix-compare-cases"))
    ((not (eq (car result) :cases)) result)
    (t (let ((proof (library-library-proof p))
             (test (cadr result)))
         (proof-with-checked-results
           ((yes (h4-book-projections-agrees-with-list-fix-compare-under-branch
                  (1- n) (proof-proof-assume proof test t)
                  evidence p start call case-rewrites hypothesis provide goal))
            (no (h4-book-projections-agrees-with-list-fix-compare-under-branch
                 (1- n) (proof-proof-assume proof test nil)
                 evidence p start call case-rewrites hypothesis provide goal)))
           (h4-tactics-tactics-case-of p goal test yes no))))))
 (defun h4-book-projections-agrees-with-list-fix-compare-under-branch
   (n sign evidence p start call case-rewrites hypothesis provide goal)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "Fuel" "h4-book-projections-agrees-with-list-fix-compare-under-branch")
     (if (failure-p sign)
         sign
       (h4-book-projections-agrees-with-list-fix-compare-under
        (1- n) (append evidence (list sign)) p start call case-rewrites
        hypothesis provide goal)))))

(defun h4-book-projections-agrees-with-list-fix-compare
  (shape hypothesis p left index fixed variable call provide goal)
  (proof-with-checked-results
    ((selected (h4-book-flatten-unfold-on-list p fixed variable shape))
     (start (h4-book-flatten-rewrite-argument p left index selected))
     (literal (proof-step-first shape)))
    (let ((pair (proof-is-call literal *proof-consp*)))
      (proof-with-checked-results
        ((nil-value (and (not pair) (h4-tactics-tactics-nil-value p shape))))
        (h4-book-projections-agrees-with-list-fix-compare-under
         1000000 (and pair (list shape)) p start call
         (and (not pair) (list nil-value)) hypothesis provide goal)))))

(defun h4-book-projections-agrees-with-list-fix (p call index)
  (let ((position (if (and (integerp index) (< index 0))
                      (+ (len call) index)
                    index)))
    (proof-with-checked-results
      ((variable (if (< position 0)
                     '(:failure "failure" "")
                   (proof-term-at call position))))
      (let* ((fixed (list *h4-book-flatten-list-fix* variable))
             (left (append (seq-slice call :none index)
                           (cons fixed (seq-slice call (1+ index) :none))))
             (goal (proof-eq left call))
             (test (list *proof-consp* variable))
             (proof (library-library-proof p)))
        (proof-with-checked-results
          ((provide (h4-book-finite-reduction-provider p))
           (positive (proof-proof-assume proof test t))
           (hypothesis (h4-book-flatten-cdr-induction-recurse
                        positive p goal variable nil))
           (yes (h4-book-projections-agrees-with-list-fix-compare
                 positive hypothesis p left index fixed variable call provide goal))
           (negative (proof-proof-assume proof test nil))
           (no (h4-book-projections-agrees-with-list-fix-compare
                negative nil p left index fixed variable call provide goal)))
          (h4-book-flatten-cdr-induction p goal variable no yes nil))))))

(defun h4-book-projections-list-equiv-proof (p formula match)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((parts (proof-list-of-length match 3))
       (guard (proof-term-at formula 1))
       (premise (proof-proof-assume proof guard t))
       (literal (proof-step-first premise))
       (opening (h4-book-order-order-view p literal nil nil))
       (same (proof-proof-rewrite proof premise opening (list 1)))
       (first (h4-book-projections-agrees-with-list-fix p (car parts) (caddr parts)))
       (left-arg (proof-term-at (car parts) (caddr parts)))
       (right-arg (proof-term-at (cadr parts) (caddr parts)))
       (replaced (proof-subst (car parts) (list (cons left-arg right-arg))))
       (last (if (equal replaced (cadr parts))
                 (proof-proof-instantiate proof first (list (list left-arg right-arg)))
               (h4-book-projections-agrees-with-list-fix p (cadr parts) (caddr parts))))
       (fixed (h4-book-projections-step-argument first 1))
       (elevated (h4-book-flatten-rewrite-argument p fixed (caddr parts) same))
       (symmetric (proof-proof-symmetric proof first))
       (joined (proof-proof-chain proof symmetric (list elevated last))))
      (h4-tactics-tactics-imply p formula joined))))

(defun h4-book-projections-projection-revappend-empty (shape p left right first provide)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((opened (h4-book-flatten-unfold-on-list p (cadr left) first shape))
       (exposed (h4-book-flatten-rewrite-argument p left 1 opened))
       (selected (h4-book-projections-open-selected
                  p (cadr right) (list shape) provide nil))
       (rest (h4-book-flatten-rewrite-argument p right 1 selected))
       (rhs (h4-book-projections-step-argument rest 2))
       (base (h4-book-flatten-unfold-on-list p rhs *proof-false* nil))
       (rest (proof-proof-chain proof rest (list base)))
       (symmetric (proof-proof-symmetric proof rest)))
      (proof-proof-chain proof exposed (list symmetric)))))

(defun h4-book-projections-projection-revappend-pair-branch
  (entry p right shape provide projection saved exposed)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((selected (h4-book-projections-open-selected
                  p (cadr right) (list shape entry) provide nil))
       (start (h4-book-flatten-rewrite-argument p right 1 selected))
       (literal (proof-step-first entry))
       (start
        (if (proof-is-call literal *proof-consp*)
            (proof-with-checked-results
              ((rhs (h4-book-projections-step-argument start 2))
               (sequence (proof-term-at rhs 1))
               (opened (h4-book-flatten-unfold-on-list p rhs sequence nil)))
              (proof-proof-chain proof start (list opened)))
          start))
       (stored (h4-book-projections-open-selected
                p (list projection saved) (list entry) provide nil))
       (projected (proof-proof-rewrite proof exposed stored (list 1 2 2)))
       (symmetric (proof-proof-symmetric proof start)))
      (proof-proof-chain proof projected (list symmetric)))))

(defun h4-book-projections-projection-revappend-pair
  (shape induction p left right first provide projection saved goal)
  (let ((proof (library-library-proof p))
        (test (list *proof-consp* (list *library-car* first))))
    (proof-with-checked-results
      ((opened (h4-book-flatten-unfold-on-list p (cadr left) first shape))
       (exposed (h4-book-flatten-rewrite-argument p left 1 opened))
       (exposed (proof-proof-chain proof exposed (list induction)))
       (positive (proof-proof-assume proof test t))
       (yes (h4-book-projections-projection-revappend-pair-branch
             positive p right shape provide projection saved exposed))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-projections-projection-revappend-pair-branch
            negative p right shape provide projection saved exposed)))
      (h4-tactics-tactics-case-of p goal test yes no))))

(defun h4-book-projections-projection-revappend (p projection first tail)
  (let* ((left (list projection (list *h4-book-flatten-revappend* first tail)))
         (right (list *h4-book-flatten-revappend*
                      (list projection first) (list projection tail)))
         (goal (proof-eq left right))
         (saved (list *proof-cons* (list *library-car* first) tail))
         (changes (list (list tail saved)))
         (test (list *proof-consp* first))
         (proof (library-library-proof p)))
    (proof-with-checked-results
      ((provide (h4-book-finite-reduction-provider p))
       (positive (proof-proof-assume proof test t))
       (hypothesis (h4-book-flatten-cdr-induction-recurse
                    positive p goal first changes))
       (yes (h4-book-projections-projection-revappend-pair
             positive hypothesis p left right first provide projection saved goal))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-projections-projection-revappend-empty
            negative p left right first provide)))
      (h4-book-flatten-cdr-induction p goal first no yes changes))))

(defun h4-book-projections-revappend-logical-view-compare
  (shape branch p first last assoc-step)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((lhs (h4-book-flatten-unfold-on-list p first *library-x* shape))
       (fixed (h4-book-projections-open-selected p (cadr last) (list shape) nil nil))
       (rhs (h4-book-flatten-rewrite-argument p last 1 fixed))
       (lhs (if branch (proof-proof-chain proof lhs (list branch)) lhs))
       (right (h4-book-projections-step-argument rhs 2))
       (rhs
        (if branch
            (proof-with-checked-results
              ((nested (proof-term-at right 1))
               (combined (proof-proof-instantiate
                          proof assoc-step
                          (seq-zip (list *library-x* *library-y* *library-z*)
                                  (append (cdr nested) (list *library-y*)))))
               (rhs (proof-proof-chain proof rhs (list combined)))
               (reassociated (h4-book-projections-step-argument combined 2))
               (inner (proof-term-at reassociated 2))
               (sequence (proof-term-at nested 2))
               (singleton (h4-book-flatten-unfold-on-list p inner sequence nil))
               (expanded (h4-book-projections-step-argument singleton 2))
               (rest (proof-term-at expanded 2))
               (zero (h4-book-flatten-unfold-on-list p rest *proof-false* nil))
               (rhs (proof-proof-rewrite proof rhs singleton (list 1 2 2))))
              (proof-proof-rewrite proof rhs zero (list 1 2 2 2)))
          (proof-with-checked-results
            ((base (h4-book-flatten-unfold-on-list p right *proof-false* nil)))
            (proof-proof-chain proof rhs (list base)))))
       (symmetric (proof-proof-symmetric proof rhs)))
      (proof-proof-chain proof lhs (list symmetric)))))

(defun h4-book-projections-revappend-logical-view (p)
  (let* ((first (list *h4-book-flatten-revappend* *library-x* *library-y*))
         (last (list *h4-book-flatten-append*
                     (list *h4-book-projections-rev* *library-x*) *library-y*))
         (goal (proof-eq first last))
         (saved (list *proof-cons* (list *library-car* *library-x*) *library-y*))
         (changes (list (list *library-y* saved)))
         (test (list *proof-consp* *library-x*))
         (proof (library-library-proof p)))
    (proof-with-checked-results
      ((assoc-step (h4-book-flatten-append-associativity p))
       (positive (proof-proof-assume proof test t))
       (hypothesis (h4-book-flatten-cdr-induction-recurse
                    positive p goal *library-x* changes))
       (yes (h4-book-projections-revappend-logical-view-compare
             positive hypothesis p first last assoc-step))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-projections-revappend-logical-view-compare
            negative nil p first last assoc-step))
       (view (h4-book-flatten-cdr-induction p goal *library-x* no yes changes)))
      (list view assoc-step))))

(defun h4-book-projections-reverse-as-revappend-compare (shape p base assoc-step)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((exposed (h4-book-projections-open-selected
                 p (list *h4-book-projections-rev* *library-x*) (list shape) nil nil))
       (rhs (h4-book-projections-step-argument base 2))
       (tested (h4-book-flatten-rewrite-argument p rhs 1 exposed))
       (literal (proof-step-first shape))
       (right (h4-book-projections-step-argument tested 2))
       (tested
        (if (proof-is-call literal *proof-consp*)
            (proof-with-checked-results
              ((nested (proof-term-at right 1))
               (instance (proof-proof-instantiate
                          proof assoc-step
                          (seq-zip (list *library-x* *library-y* *library-z*)
                                  (append (cdr nested) (list *proof-false*)))))
               (tested (proof-proof-chain proof tested (list instance)))
               (reassociated (h4-book-projections-step-argument instance 2))
               (inner (proof-term-at reassociated 2))
               (sequence (proof-term-at nested 2))
               (singleton (h4-book-flatten-unfold-on-list p inner sequence nil))
               (expanded (h4-book-projections-step-argument singleton 2))
               (rest (proof-term-at expanded 2))
               (tail (h4-book-flatten-unfold-on-list p rest *proof-false* nil))
               (tested (proof-proof-rewrite proof tested singleton (list 1 2 2))))
              (proof-proof-rewrite proof tested tail (list 1 2 2 2)))
          (proof-with-checked-results
            ((empty (h4-book-flatten-unfold-on-list p right *proof-false* nil)))
            (proof-proof-chain proof tested (list empty)))))
       (symmetric (proof-proof-symmetric proof exposed)))
      (proof-proof-chain proof base (list tested symmetric)))))

(defun h4-book-projections-reverse-as-revappend (p)
  (let* ((proof (library-library-proof p))
         (goal (proof-eq (list *h4-book-flatten-revappend* *library-x* *proof-false*)
                         (list *h4-book-projections-rev* *library-x*)))
         (test (list *proof-consp* *library-x*)))
    (proof-with-checked-results
      ((views (h4-book-projections-revappend-logical-view p))
       (base (proof-proof-instantiate
              proof (car views) (list (list *library-y* *proof-false*))))
       (positive (proof-proof-assume proof test t))
       (yes (h4-book-projections-reverse-as-revappend-compare
             positive p base (cadr views)))
       (negative (proof-proof-assume proof test nil))
       (no (h4-book-projections-reverse-as-revappend-compare
            negative p base (cadr views))))
      (h4-tactics-tactics-case-of p goal test yes no))))

(defun h4-book-projections-projection-reverse (p projection source)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
      ((combined (h4-book-projections-projection-revappend p projection *library-x* *library-y*))
       (law (proof-proof-instantiate proof combined
                                    (list (list *library-x* source)
                                          (list *library-y* *proof-false*))))
       (reverse-step (h4-book-projections-reverse-as-revappend p))
       (instance (proof-proof-instantiate proof reverse-step (list (list *library-x* source))))
       (symmetric (proof-proof-symmetric proof instance))
       (lifted (h4-book-flatten-rewrite-argument
                p (list projection (list *h4-book-projections-rev* source)) 1 symmetric))
       (result (proof-proof-chain proof lifted (list law)))
       (empty (h4-book-flatten-unfold-on-list
               p (list projection *proof-false*) *proof-false* nil))
       (result (proof-proof-rewrite proof result empty (list 1 2 2)))
       (last (proof-proof-instantiate proof reverse-step
                                     (list (list *library-x* (list projection source))))))
      (proof-proof-chain proof result (list last)))))

(defun h4-book-projections-projection-equality-proof (p formula)
  (and (proof-is-call formula *proof-equal*)
    (proof-with-checked-results
      ((sides (proof-list-of-length (cdr formula) 2)))
      (let ((left (car sides))
            (right (cadr sides)))
        (and (proof-compound left)
          (proof-with-checked-results
            ((projection (proof-term-at left 0)))
            (and (and (member-equal projection *h4-book-projections-projections*)
                       (equal (len left) 2))
              (let ((source (cadr left)))
                (cond
                 ((proof-is-call source *h4-book-flatten-revappend*)
                  (proof-with-checked-results
                    ((arguments (proof-list-of-length (cdr source) 2)))
                    (let ((a (car arguments))
                          (b (cadr arguments)))
                      (and (and (not (proof-compound a))
                                 (not (proof-compound b))
                                 (not (equal a b))
                                 (equal right (list *h4-book-flatten-revappend*
                                                    (list projection a)
                                                    (list projection b))))
                        (h4-book-projections-projection-revappend p projection a b)))))
                 ((proof-is-call source *h4-book-projections-rev*)
                  (proof-with-checked-results
                    ((a (proof-term-at source 1)))
                    (and (and (not (proof-compound a))
                               (equal right (list *h4-book-projections-rev* (list projection a))))
                      (h4-book-projections-projection-reverse p projection a)))))))))))))

(defun h4-book-projections-projection-proof (p formula)
  (proof-with-checked-results
    ((match (h4-book-projections-list-equiv-shape formula)))
    (if (and match (assoc-equal (caar match) (proof-proof-definitions (library-library-proof p))))
        (let ((result (h4-book-projections-list-equiv-proof p formula match)))
          (if (and (failure-p result)
                   (member-equal (cadr result)
                                 '("Unproved" "InapplicableStep" "InapplicableTerm" "MissingProofInput"
                                   "assertion" "key" "value" "recursion")))
              (h4-book-projections-projection-equality-proof p formula)
            result))
      (h4-book-projections-projection-equality-proof p formula))))
