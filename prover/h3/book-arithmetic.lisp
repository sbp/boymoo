(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h3-book-arithmetic-fix* (proof-sym "FIX" "ACL2"))
(defconst *h3-book-arithmetic-divide* (proof-sym "UNARY-/" "ACL2"))
(defconst *h3-book-arithmetic-associative*
  (list (cons *proof-plus* "+") (cons *proof-times* "*")))

(defun h3-book-arithmetic-step-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h3-book-arithmetic-tail (term)
  (if (integerp term)
      '(:failure "failure" "")
    (cdr term)))

(defun h3-book-arithmetic-binary-arguments (term)
  (proof-with-checked-results ((args (h3-book-arithmetic-tail term)))
    (proof-list-of-length args 2)))

(defun h3-book-arithmetic-value-at-path (value path)
  (declare (xargs :measure (acl2-count path)))
  (if (endp path)
      value
    (proof-with-checked-results
        ((child (proof-term-at value (car path))))
      (h3-book-arithmetic-value-at-path child (cdr path)))))

(defun h3-book-arithmetic-normal-form-node (path step)
  (proof-with-checked-results ((value (h3-book-arithmetic-step-at step 2)))
    (h3-book-arithmetic-value-at-path value path)))

(defun h3-book-arithmetic-normal-form-reassociate (n lib step path head add)
  (if (zp n)
      '(:failure "Fuel" "h3-book-arithmetic-normal-form-reassociate")
    (proof-with-checked-results
        ((node (h3-book-arithmetic-normal-form-node path step)))
      (if (not (proof-is-call node head))
          step
        (proof-with-checked-results ((parts (proof-list-of-length node 3)))
          (let ((left (cadr parts)) (right (caddr parts)))
            (if (proof-is-call left head)
                (proof-with-checked-results
                    ((rearrange (library-library-axiom
                                 lib add (append (cdr left) (list right))))
                     (next (proof-proof-rewrite
                            (library-library-proof lib) step rearrange
                            (append '(1 2) path))))
                  (h3-book-arithmetic-normal-form-reassociate
                   (1- n) lib next path head add))
              (h3-book-arithmetic-normal-form-reassociate
               (1- n) lib step (append path '(2)) head add))))))))

(defun h3-book-arithmetic-normal-form-swap (lib step place add swap left right rest suffix)
  (let ((proof (library-library-proof lib)))
    (if suffix
        (proof-with-checked-results
            ((tail (proof-term-at rest 2))
             (associate (library-library-axiom lib add (list left right tail)))
             (reverse-associate (proof-proof-symmetric proof associate))
             (step (proof-proof-rewrite proof step reverse-associate place))
             (commute (library-library-axiom lib swap (list left right)))
             (step (proof-proof-rewrite proof step commute (append place '(1))))
             (associate (library-library-axiom lib add (list right left tail))))
          (proof-proof-rewrite proof step associate place))
      (proof-with-checked-results
          ((commute (library-library-axiom lib swap (list left right))))
        (proof-proof-rewrite proof step commute place)))))

(defun h3-book-arithmetic-normal-form-pass (n lib step path head add swap changed)
  (if (zp n)
      '(:failure "Fuel" "h3-book-arithmetic-normal-form-pass")
    (proof-with-checked-results
        ((node (h3-book-arithmetic-normal-form-node path step)))
      (if (not (proof-is-call node head))
          (cons step changed)
        (proof-with-checked-results ((parts (proof-list-of-length node 3)))
          (let* ((left (cadr parts))
                 (rest (caddr parts))
                 (suffix (proof-is-call rest head)))
            (proof-with-checked-results
                ((right (if suffix (proof-term-at rest 1) rest))
                 (left-text (proof-write left))
                 (right-text (proof-write right)))
              (if (string< right-text left-text)
                  (proof-with-checked-results
                      ((next (h3-book-arithmetic-normal-form-swap
                              lib step (append '(1 2) path) add swap
                              left right rest suffix)))
                    (h3-book-arithmetic-normal-form-pass
                     (1- n) lib next (append path '(2)) head add swap t))
                (h3-book-arithmetic-normal-form-pass
                 (1- n) lib step (append path '(2)) head add swap changed)))))))))

(defun h3-book-arithmetic-normal-form-sort (n lib step head add swap)
  (if (zp n)
      '(:failure "Fuel" "h3-book-arithmetic-normal-form-sort")
    (proof-with-checked-results
        ((pass (h3-book-arithmetic-normal-form-pass
                1000000 lib step nil head add swap nil)))
      (if (cdr pass)
          (h3-book-arithmetic-normal-form-sort (1- n) lib (car pass) head add swap)
        (car pass)))))

(defun h3-book-arithmetic-normal-form-finish (lib term equation)
  (let ((proof (library-library-proof lib))
        (operator (assoc-equal (car term) *h3-book-arithmetic-associative*)))
    (if (not operator)
        (and equation (proof-proof-tidy proof equation))
      (let ((head (car term))
            (add (concatenate 'string "ASSOCIATIVITY-OF-" (cdr operator)))
            (swap (concatenate 'string "COMMUTATIVITY-OF-" (cdr operator))))
        (proof-with-checked-results
            ((step (or equation (proof-proof-reflexive proof term)))
             (step (h3-book-arithmetic-normal-form-reassociate
                    1000000 lib step nil head add))
             (step (h3-book-arithmetic-normal-form-sort 1000000 lib step head add swap))
             (value (h3-book-arithmetic-step-at step 2)))
          (and (not (equal value term)) (proof-proof-tidy proof step)))))))

(mutual-recursion
 (defun h3-book-arithmetic-normal-form (lib term)
   (declare (xargs :measure (acl2-count term)))
   (and (consp term)
        (h3-rewrite-arguments term)
        (proof-with-checked-results
            ((equation (h3-book-arithmetic-normal-form-children lib term (cdr term) 1 nil)))
          (h3-book-arithmetic-normal-form-finish lib term equation))))
 (defun h3-book-arithmetic-normal-form-children (lib term args index equation)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       equation
     (let ((proof (library-library-proof lib)))
       (proof-with-checked-results
           ((child (h3-book-arithmetic-normal-form lib (car args)))
            (next (if child
                      (proof-with-checked-results
                          ((step (or equation (proof-proof-reflexive proof term))))
                        (proof-proof-rewrite proof step child (list 1 2 index)))
                    equation)))
         (h3-book-arithmetic-normal-form-children
          lib term (cdr args) (1+ index) next))))))

(defun h3-book-arithmetic-associative-equal (lib a b)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left (or (h3-book-arithmetic-normal-form lib a)
                   (proof-proof-reflexive proof a)))
         (right (or (h3-book-arithmetic-normal-form lib b)
                    (proof-proof-reflexive proof b)))
         (left-value (h3-book-arithmetic-step-at left 2))
         (right-value (h3-book-arithmetic-step-at right 2)))
      (if (not (equal left-value right-value))
          '(:failure "Unproved" "")
        (proof-with-checked-results ((reverse-right (proof-proof-symmetric proof right)))
          (proof-proof-chain proof left (list reverse-right)))))))

(defun h3-book-arithmetic-search-prove (search term hypotheses)
  (car (h3-rewrite-search-prove search term hypotheses)))

(defun h3-book-arithmetic-typed-number (lib expr)
  (proof-with-checked-results ((head (proof-term-at expr 0)))
    (if (member-equal head (list *proof-plus* *proof-times* *proof-minus*
                                 *h3-book-arithmetic-divide*))
        (let ((proof (library-library-proof lib)))
          (proof-with-checked-results
              ((args (if (equal (len expr) 3)
                         (cdr expr)
                       (proof-with-checked-results ((arg (proof-term-at expr 1)))
                         (list arg *proof-zero*))))
               (closure (library-library-axiom lib "CLOSURE" args))
               (parts (proof-proof-conjunct proof closure)))
            (if (equal head *proof-plus*)
                (car parts)
              (proof-with-checked-results
                  ((parts (proof-proof-conjunct proof (cadr parts))))
                (if (equal head *proof-times*)
                    (car parts)
                  (proof-with-checked-results
                      ((parts (proof-proof-conjunct proof (cadr parts))))
                    (if (equal head *proof-minus*) (car parts) (cadr parts))))))))
      (h3-book-arithmetic-search-prove
       (h3-rewrite-search-init lib nil nil nil 150 nil)
       (list *library-numberp* expr) nil))))

(defun h3-book-arithmetic-fix-value (lib value evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof (list *h3-book-arithmetic-fix* value)))
         (body (h3-book-arithmetic-step-at opened 2))
         (selected (proof-proof-select proof body evidence)))
      (proof-proof-chain proof opened (list selected)))))

(defun h3-book-arithmetic-inverse (lib value numeric nonzero)
  (proof-with-checked-results
      ((fact (library-library-axiom lib "INVERSE-OF-*" (list value))))
    (h3-symbolic-order-guarded lib fact (list numeric nonzero))))

(defun h3-book-arithmetic-one-right (lib value)
  (proof-with-checked-results
      ((commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list value *proof-one*)))
       (unit (library-library-axiom lib "UNICITY-OF-1" (list value))))
    (proof-proof-chain (library-library-proof lib) commute (list unit))))

(defun h3-book-arithmetic-zero-left (lib value)
  (proof-with-checked-results
      ((commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list *proof-zero* value)))
       (zero (h3-event-counts-multiply-zero lib value)))
    (proof-proof-chain (library-library-proof lib) commute (list zero))))

(defun h3-book-arithmetic-multiply-fix (lib value other)
  (let* ((proof (library-library-proof lib))
         (test (list *library-numberp* value))
         (expr (list *proof-times* (list *h3-book-arithmetic-fix* value) other))
         (original (list *proof-times* value other)))
    (proof-with-checked-results
        ((reflexive (proof-proof-reflexive proof expr))
         (yes-test (proof-proof-assume proof test t))
         (fixed (h3-book-arithmetic-fix-value lib value yes-test))
         (yes (proof-proof-rewrite proof reflexive fixed '(1 2 1)))
         (no-test (proof-proof-assume proof test nil))
         (reflexive (proof-proof-reflexive proof expr))
         (fixed (h3-book-arithmetic-fix-value lib value no-test))
         (no (proof-proof-rewrite proof reflexive fixed '(1 2 1)))
         (default (library-library-axiom lib "DEFAULT-*-1" (list value other)))
         (default (proof-proof-modus-ponens proof default no-test))
         (zero (h3-book-arithmetic-zero-left lib other))
         (reverse-default (proof-proof-symmetric proof default))
         (no (proof-proof-chain proof no (list zero reverse-default)))
         (yes-first (proof-step-first yes))
         (no-first (proof-step-first no)))
      (if (and (equal yes-first no-first) (equal no-first (proof-eq expr original)))
          (proof-proof-cases proof test yes no)
        '(:failure "failure" "")))))

(defun h3-book-arithmetic-cancel-product-factor (lib step place arg value reciprocal factor-inverse)
  (let ((proof (library-library-proof lib))
        (pair (list *proof-times* (list *proof-times* arg value) reciprocal)))
    (proof-with-checked-results
        ((reduced (library-library-axiom lib "ASSOCIATIVITY-OF-*" (list arg value reciprocal)))
         (left (h3-book-arithmetic-step-at reduced 1)))
      (if (not (equal left pair))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((reduced (proof-proof-rewrite proof reduced factor-inverse '(1 2 2)))
             (unit (h3-book-arithmetic-one-right lib arg))
             (reduced (proof-proof-chain proof reduced (list unit))))
          (proof-proof-rewrite proof step reduced (list 1 place)))))))

(defun h3-book-arithmetic-cancel-product (lib a b value factor-inverse equality)
  (let ((proof (library-library-proof lib))
        (reciprocal (list *h3-book-arithmetic-divide* value)))
    (proof-with-checked-results
        ((left (h3-book-arithmetic-step-at equality 1))
         (start (proof-proof-reflexive proof (list *proof-times* left reciprocal)))
         (start (proof-proof-rewrite proof start equality '(1 2 1)))
         (start (h3-book-arithmetic-cancel-product-factor
                 lib start 1 a value reciprocal factor-inverse))
         (start (h3-book-arithmetic-cancel-product-factor
                 lib start 2 b value reciprocal factor-inverse)))
      (proof-proof-tidy proof start))))

(defun h3-book-arithmetic-zero-test (lib term proof)
  (proof-with-checked-results ((literal (proof-step-first proof)))
    (if (equal literal (list *library-numberp* term))
        '(:failure "Unproved" "")
      (proof-with-checked-results
          ((rules (h3-rewrite-rules-init lib (list (proof-sym "DEFAULT-UNARY-/" "ACL2")) nil)))
        (h3-book-arithmetic-search-prove
         (h3-rewrite-search-init lib (list *proof-not*) nil rules 150 nil)
         (proof-eq (list *h3-book-arithmetic-divide* term) *proof-zero*)
         (list proof))))))

(defmacro h3-book-arithmetic-scalar-cases-forms (lib value equal-form different-form nonnumeric-form)
  `(let* ((h3-scalar-proof (library-library-proof ,lib))
          (h3-scalar-value ,value)
          (h3-scalar-number (list *library-numberp* h3-scalar-value))
          (h3-scalar-zero (proof-eq h3-scalar-value *proof-zero*)))
     (proof-with-checked-results
         ((h3-scalar-known (proof-proof-assume h3-scalar-proof h3-scalar-number t))
          (h3-scalar-equal (proof-proof-assume h3-scalar-proof h3-scalar-zero t))
          (h3-scalar-equal-result ,equal-form)
          (h3-scalar-different (proof-proof-assume h3-scalar-proof h3-scalar-zero nil))
          (h3-scalar-different-result ,different-form)
          (h3-scalar-nonnumeric (proof-proof-assume h3-scalar-proof h3-scalar-number nil))
          (h3-scalar-numeric-result (proof-proof-cases h3-scalar-proof h3-scalar-zero
                                                      h3-scalar-equal-result
                                                      h3-scalar-different-result))
          (h3-scalar-nonnumeric-result ,nonnumeric-form))
       (proof-proof-cases h3-scalar-proof h3-scalar-number h3-scalar-numeric-result
                          h3-scalar-nonnumeric-result))))

(defmacro h3-book-arithmetic-with-scalar-cases (lib value use)
  `(h3-book-arithmetic-scalar-cases-forms
    ,lib ,value
    (,(car use) h3-scalar-known h3-scalar-equal nil ,@(cdr use))
    (,(car use) h3-scalar-known h3-scalar-different t ,@(cdr use))
    (,(car use) h3-scalar-nonnumeric h3-scalar-nonnumeric nil ,@(cdr use))))

(defun h3-book-arithmetic-scalar-cases (lib value use)
  (h3-book-arithmetic-scalar-cases-forms lib value (car use) (cadr use) (caddr use)))

(defun h3-book-arithmetic-truth-value (lib evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first evidence))
         (parts (proof-list-of-length literal 3))
         (identical (proof-proof-fact proof "equal-same" (list (list *library-x* (caddr parts)))))
         (reversed (proof-proof-symmetric proof evidence))
         (rewritten (proof-proof-rewrite proof identical reversed '(1 1 1))))
      (proof-proof-tidy proof rewritten))))

(defun h3-book-arithmetic-equivalent-equalities-positive (lib first forward)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((value (h3-book-arithmetic-truth-value lib forward))
         (reversed (proof-proof-symmetric proof value)))
      (proof-proof-chain proof first (list reversed)))))

(defun h3-book-arithmetic-equivalent-equalities-finish (lib p q yes not-p backward)
  (let ((proof (library-library-proof lib)) (neg-q (proof-neg q)))
    (proof-with-checked-results
        ((contradiction (proof-proof-cut proof backward not-p))
         (not-q (proof-proof-subsume proof contradiction
                                    (cons neg-q (proof-without-literal
                                                 (proof-step-clause contradiction) neg-q))))
         (p-nil (h3-rewrite-nil-value lib not-p))
         (q-nil (h3-rewrite-nil-value lib not-q))
         (reverse-q-nil (proof-proof-symmetric proof q-nil))
         (no (proof-proof-chain proof p-nil (list reverse-q-nil))))
      (proof-proof-cases proof p yes no))))

(defmacro h3-book-arithmetic-equivalent-equalities-forms (lib p q forward backward)
  `(let* ((h3-equivalence-lib ,lib)
          (h3-equivalence-p ,p)
          (h3-equivalence-q ,q)
          (h3-equivalence-proof (library-library-proof h3-equivalence-lib)))
     (proof-with-checked-results
         ((h3-equivalence-assume-p (proof-proof-assume h3-equivalence-proof h3-equivalence-p t))
          (h3-equivalence-p-true (h3-book-arithmetic-truth-value
                                  h3-equivalence-lib h3-equivalence-assume-p))
          (h3-equivalence-forward ,forward)
          (h3-equivalence-yes (h3-book-arithmetic-equivalent-equalities-positive
                               h3-equivalence-lib h3-equivalence-p-true h3-equivalence-forward))
          (h3-equivalence-not-p (proof-proof-assume h3-equivalence-proof h3-equivalence-p nil))
          (h3-equivalence-assume-q (proof-proof-assume h3-equivalence-proof h3-equivalence-q t))
          (h3-equivalence-backward ,backward))
       (h3-book-arithmetic-equivalent-equalities-finish
        h3-equivalence-lib h3-equivalence-p h3-equivalence-q h3-equivalence-yes
        h3-equivalence-not-p h3-equivalence-backward))))

(defmacro h3-book-arithmetic-with-equivalent-equalities (lib p q forward backward)
  `(h3-book-arithmetic-equivalent-equalities-forms
    ,lib ,p ,q
    (,(car forward) h3-equivalence-assume-p ,@(cdr forward))
    (,(car backward) h3-equivalence-assume-q ,@(cdr backward))))

(defun h3-book-arithmetic-equivalent-equalities (lib p q forward backward)
  (h3-book-arithmetic-equivalent-equalities-forms lib p q forward backward))

(defun h3-book-arithmetic-inverse-nonzero (lib term law)
  (let* ((proof (library-library-proof lib))
         (reciprocal (list *h3-book-arithmetic-divide* term))
         (test (proof-eq reciprocal *proof-zero*)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof test t))
         (bad (proof-proof-rewrite proof law assumed '(1 1 2)))
         (zero (h3-event-counts-multiply-zero lib term))
         (bad (proof-proof-rewrite proof bad zero '(1 1)))
         (literal (proof-step-first bad))
         (computed (proof-proof-compute proof literal *proof-nil*))
         (bad (proof-proof-rewrite proof bad computed '(1)))
         (bad (proof-proof-tidy proof bad)))
      (proof-proof-front proof bad (proof-neg test)))))

(defun h3-book-arithmetic-no-zero-product (lib a b an bn nz-a nz-b)
  (let* ((proof (library-library-proof lib))
         (product (list *proof-times* a b))
         (test (proof-eq product *proof-zero*)))
    (proof-with-checked-results
        ((commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list b a)))
         (assumed (proof-proof-assume proof test t))
         (zero (h3-book-arithmetic-zero-left lib a))
         (reverse-zero (proof-proof-symmetric proof zero))
         (bad (proof-proof-chain proof commute (list assumed reverse-zero)))
         (factor-inverse (h3-book-arithmetic-inverse lib a an nz-a))
         (canceled (h3-book-arithmetic-cancel-product
                    lib b *proof-zero* a factor-inverse bad))
         (fixed (h3-book-arithmetic-fix-value lib b bn))
         (canceled (proof-proof-rewrite proof canceled fixed '(1 1)))
         (zero-type (h3-book-arithmetic-typed-number lib *proof-zero*))
         (fixed (h3-book-arithmetic-fix-value lib *proof-zero* zero-type))
         (canceled (proof-proof-rewrite proof canceled fixed '(1 2)))
         (result (proof-proof-cut proof canceled nz-b)))
      (proof-proof-front proof result (proof-neg test)))))

(defun h3-book-arithmetic-zero-product (lib a b factor evidence)
  (let ((proof (library-library-proof lib)) (left (equal factor a)))
    (proof-with-checked-results ((literal (proof-step-first evidence)))
      (if (proof-is-call literal *proof-not*)
          (proof-with-checked-results
              ((default (library-library-axiom
                         lib (if left "DEFAULT-*-1" "DEFAULT-*-2") (list a b))))
            (proof-proof-modus-ponens proof default evidence))
        (let ((target (if left b a)))
          (proof-with-checked-results
              ((start (proof-proof-reflexive proof (list *proof-times* a b)))
               (start (proof-proof-rewrite proof start evidence (list 1 2 (if left 1 2))))
               (zero (if left
                         (h3-book-arithmetic-zero-left lib target)
                       (h3-event-counts-multiply-zero lib target))))
            (proof-proof-chain proof start (list zero))))))))

(defun h3-book-arithmetic-search-reduce (search term context)
  (car (h3-rewrite-search-reduce search term context nil nil)))

(defun h3-book-arithmetic-reverse-reduction (proof reduction)
  (if reduction
      (proof-proof-symmetric proof reduction)
    '(:failure "failure" "")))

(defun h3-book-arithmetic-reciprocal-involution-branch (numeric status nonzero lib term r rr)
  (let ((proof (library-library-proof lib)))
    (if (not nonzero)
        (proof-with-checked-results
            ((zero (h3-book-arithmetic-zero-test lib term status))
             (search (h3-rewrite-search-init lib (list *h3-book-arithmetic-fix*) nil nil 150 nil))
             (context (h3-rewrite-search-context
                       (h3-rewrite-search-init lib nil nil nil 150 nil) (list numeric status)))
             (rhs (h3-book-arithmetic-search-reduce search
                                                   (list *h3-book-arithmetic-fix* term) context))
             (start (proof-proof-reflexive proof rr))
             (result (proof-proof-rewrite proof start zero '(1 2 1)))
             (computed (proof-proof-compute proof (list *h3-book-arithmetic-divide* *proof-zero*) 0))
             (reverse-rhs (h3-book-arithmetic-reverse-reduction proof rhs)))
          (proof-proof-chain proof result (list computed reverse-rhs)))
      (proof-with-checked-results
          ((law (h3-book-arithmetic-inverse lib term numeric status))
           (r-type (h3-book-arithmetic-typed-number lib r))
           (r-nonzero (h3-book-arithmetic-inverse-nonzero lib term law))
           (law-r (h3-book-arithmetic-inverse lib r r-type r-nonzero))
           (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list rr r)))
           (other (proof-proof-chain proof commute (list law-r)))
           (reverse-other (proof-proof-symmetric proof other))
           (equality (proof-proof-chain proof law (list reverse-other)))
           (step (h3-book-arithmetic-cancel-product lib term rr r law-r equality))
           (rr-type (h3-book-arithmetic-typed-number lib rr))
           (fixed (h3-book-arithmetic-fix-value lib rr rr-type))
           (step (proof-proof-rewrite proof step fixed '(1 2)))
           (reversed (proof-proof-symmetric proof step)))
        (proof-proof-tidy proof reversed)))))

(defun h3-book-arithmetic-reciprocal-involution (lib term)
  (let* ((r (list *h3-book-arithmetic-divide* term))
         (rr (list *h3-book-arithmetic-divide* r))
         (target (proof-eq rr (list *h3-book-arithmetic-fix* term))))
    (proof-with-checked-results
        ((step (h3-book-arithmetic-with-scalar-cases
                lib term (h3-book-arithmetic-reciprocal-involution-branch lib term r rr)))
         (literal (proof-step-first step)))
      (if (equal literal target) step '(:failure "failure" "")))))

(defun h3-book-arithmetic-cancel-reciprocal-product-branch
    (numeric status nonzero lib scalar reciprocal start argument reciprocal-guard right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((product (if nonzero
                      (h3-book-arithmetic-inverse lib scalar numeric status)
                    (h3-book-arithmetic-zero-product lib scalar reciprocal scalar status)))
         (result (proof-proof-rewrite proof start product '(1 2 2)))
         (reduction (if nonzero
                        (h3-book-arithmetic-one-right lib argument)
                      (h3-event-counts-multiply-zero lib argument)))
         (result (proof-proof-chain proof result (list reduction)))
         (search (h3-rewrite-search-init lib (list *proof-not*) (list reciprocal-guard) nil 150 nil))
         (context (h3-rewrite-search-context search (list numeric status)))
         (reduced (h3-book-arithmetic-search-reduce search right context))
         (reverse-reduced (h3-book-arithmetic-reverse-reduction proof reduced)))
      (proof-proof-chain proof result (list reverse-reduced)))))

(defun h3-book-arithmetic-cancel-reciprocal-product (lib formula)
  (proof-with-checked-results
      ((parts (h3-book-arithmetic-binary-arguments formula))
       (test (proof-term-at (cadr parts) 1))
       (test-literal (proof-term-at test 1))
       (reciprocal-guard (proof-term-at test-literal 1))
       (scalar (proof-term-at reciprocal-guard 1))
       (then-branch (proof-term-at (cadr parts) 2))
       (argument (proof-term-at then-branch 1)))
    (let* ((reciprocal (list *h3-book-arithmetic-divide* scalar))
           (ordered (list *proof-times* argument (list *proof-times* scalar reciprocal))))
      (proof-with-checked-results
          ((start (h3-book-arithmetic-associative-equal lib (car parts) ordered)))
        (h3-book-arithmetic-with-scalar-cases
         lib scalar (h3-book-arithmetic-cancel-reciprocal-product-branch
                     lib scalar reciprocal start argument reciprocal-guard (cadr parts)))))))

(defun h3-book-arithmetic-reciprocal-zero-test-branch (numeric status nonzero lib term left right)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((fixed (h3-book-arithmetic-fix-value lib term numeric)))
      (if nonzero
          (proof-with-checked-results
              ((law (h3-book-arithmetic-inverse lib term numeric status))
               (nz (h3-book-arithmetic-inverse-nonzero lib term law))
               (reverse-fixed (proof-proof-symmetric proof fixed))
               (fixed-nz (proof-proof-rewrite proof status reverse-fixed '(1 1 1)))
               (left-nil (h3-rewrite-nil-value lib nz))
               (right-nil (h3-rewrite-nil-value lib fixed-nz))
               (reverse-right (proof-proof-symmetric proof right-nil)))
            (proof-proof-chain proof left-nil (list reverse-right)))
        (proof-with-checked-results
            ((result (h3-book-arithmetic-zero-test lib term status))
             (literal (proof-step-first status))
             (fixed (if (proof-is-call literal *proof-equal*)
                        (proof-proof-chain proof fixed (list status))
                      fixed))
             (result-first (proof-step-first result))
             (fixed-first (if (equal result-first left)
                              (proof-step-first fixed)
                            '(:failure "failure" ""))))
          (if (not (equal fixed-first right))
              '(:failure "failure" "")
            (proof-with-checked-results
                ((left-true (h3-book-arithmetic-truth-value lib result))
                 (right-true (h3-book-arithmetic-truth-value lib fixed))
                 (reverse-right (proof-proof-symmetric proof right-true)))
              (proof-proof-chain proof left-true (list reverse-right)))))))))

(defun h3-book-arithmetic-reciprocal-zero-test (lib formula)
  (proof-with-checked-results
      ((parts (h3-book-arithmetic-binary-arguments formula))
       (reciprocal (proof-term-at (car parts) 1))
       (term (proof-term-at reciprocal 1)))
    (h3-book-arithmetic-with-scalar-cases
     lib term (h3-book-arithmetic-reciprocal-zero-test-branch lib term (car parts) (cadr parts)))))

(defun h3-book-arithmetic-reciprocal-product-nonzero (lib formula an bn az bz)
  (proof-with-checked-results
      ((parts (h3-book-arithmetic-binary-arguments formula))
       (product (proof-term-at (car parts) 1))
       (factors (h3-book-arithmetic-binary-arguments product))
       (reciprocals (h3-book-arithmetic-binary-arguments (cadr parts))))
    (let ((proof (library-library-proof lib))
          (left (car parts)) (right (cadr parts))
          (a (car factors)) (b (cadr factors))
          (r (car reciprocals)) (s (cadr reciprocals)))
      (proof-with-checked-results
          ((product-type (h3-book-arithmetic-typed-number lib product))
           (product-nonzero (h3-book-arithmetic-no-zero-product lib a b an bn az bz))
           (law (h3-book-arithmetic-inverse lib product product-type product-nonzero))
           (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list left product)))
           (first-one (proof-proof-chain proof commute (list law)))
           (paired (list *proof-times* (list *proof-times* a r) (list *proof-times* b s)))
           (other-one (h3-book-arithmetic-associative-equal
                       lib (list *proof-times* right product) paired))
           (inverse-a (h3-book-arithmetic-inverse lib a an az))
           (other-one (proof-proof-rewrite proof other-one inverse-a '(1 2 1)))
           (inverse-b (h3-book-arithmetic-inverse lib b bn bz))
           (other-one (proof-proof-rewrite proof other-one inverse-b '(1 2 2)))
           (computed (proof-proof-compute proof (list *proof-times* *proof-one* *proof-one*) 1))
           (other-one (proof-proof-chain proof other-one (list computed)))
           (reverse-other (proof-proof-symmetric proof other-one))
           (equality (proof-proof-chain proof first-one (list reverse-other)))
           (result (h3-book-arithmetic-cancel-product lib left right product law equality))
           (left-type (h3-book-arithmetic-typed-number lib left))
           (left-fixed (h3-book-arithmetic-fix-value lib left left-type))
           (result (proof-proof-rewrite proof result left-fixed '(1 1)))
           (right-type (h3-book-arithmetic-typed-number lib right))
           (right-fixed (h3-book-arithmetic-fix-value lib right right-type))
           (result (proof-proof-rewrite proof result right-fixed '(1 2))))
        (proof-proof-tidy proof result)))))

(defun h3-book-arithmetic-reciprocal-product-second (bn bz valid lib formula left right a b r s an az active)
  (if (not (and active valid))
      (let ((proof (library-library-proof lib))
            (factor (if active b a)) (status (if active bz az)))
        (proof-with-checked-results
            ((product-zero (h3-book-arithmetic-zero-product lib a b factor status))
             (recip-zero (h3-book-arithmetic-zero-test lib factor status))
             (left-reduced (proof-proof-reflexive proof left))
             (left-reduced (proof-proof-rewrite proof left-reduced product-zero '(1 2 1)))
             (computed (proof-proof-compute proof (list *h3-book-arithmetic-divide* *proof-zero*) 0))
             (left-reduced (proof-proof-chain proof left-reduced (list computed)))
             (is-left (equal factor a))
             (right-reduced (proof-proof-reflexive proof right))
             (right-reduced (proof-proof-rewrite proof right-reduced recip-zero
                                                (list 1 2 (if is-left 1 2))))
             (zero (if is-left
                       (h3-book-arithmetic-zero-left lib s)
                     (h3-event-counts-multiply-zero lib r)))
             (right-reduced (proof-proof-chain proof right-reduced (list zero)))
             (reversed (proof-proof-symmetric proof right-reduced)))
          (proof-proof-chain proof left-reduced (list reversed))))
    (h3-book-arithmetic-reciprocal-product-nonzero lib formula an bn az bz)))

(defun h3-book-arithmetic-reciprocal-product-first (an az active lib formula left right a b r s)
  (h3-book-arithmetic-with-scalar-cases
   lib b (h3-book-arithmetic-reciprocal-product-second lib formula left right a b r s an az active)))

(defun h3-book-arithmetic-reciprocal-product (lib formula)
  (proof-with-checked-results
      ((parts (h3-book-arithmetic-binary-arguments formula))
       (product (proof-term-at (car parts) 1))
       (factors (h3-book-arithmetic-binary-arguments product))
       (reciprocals (h3-book-arithmetic-binary-arguments (cadr parts))))
    (h3-book-arithmetic-with-scalar-cases
     lib (car factors)
     (h3-book-arithmetic-reciprocal-product-first
      lib formula (car parts) (cadr parts) (car factors) (cadr factors)
      (car reciprocals) (cadr reciprocals)))))

(defun h3-book-arithmetic-product-equal-zero-second (bn bz valid lib formula a b an az active)
  (proof-with-checked-results
      ((zero (if (and active valid)
                 (h3-book-arithmetic-no-zero-product lib a b an bn az bz)
               (let ((factor (if active b a)) (evidence (if active bz az)))
                 (h3-book-arithmetic-zero-product lib a b factor evidence)))))
    (h3-book-arithmetic-search-prove
     (h3-rewrite-search-init lib (list *proof-not* *h3-book-arithmetic-fix*) nil nil 10 nil)
     formula (list an az bn bz zero))))

(defun h3-book-arithmetic-product-equal-zero-first (an az active lib formula a b)
  (h3-book-arithmetic-with-scalar-cases
   lib b (h3-book-arithmetic-product-equal-zero-second lib formula a b an az active)))

(defun h3-book-arithmetic-product-equal-zero (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (predicate (cadr parts))
       (left (proof-term-at predicate 1))
       (product (if (equal left *proof-zero*) (proof-term-at predicate 2) left))
       (factors (h3-book-arithmetic-binary-arguments product)))
    (h3-book-arithmetic-with-scalar-cases
     lib (car factors) (h3-book-arithmetic-product-equal-zero-first
                        lib formula (car factors) (cadr factors)))))

(defun h3-book-arithmetic-uniqueness-of-inverse-avoid-unit (vanished lib left nonunit)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((assumed (proof-proof-assume proof left t))
         (impossible (proof-proof-rewrite proof assumed vanished '(1 1)))
         (cut (proof-proof-cut proof impossible nonunit))
         (denied (proof-proof-front proof cut (proof-neg left))))
      (h3-rewrite-nil-value lib denied))))

(defun h3-book-arithmetic-uniqueness-of-inverse-forward (equality lib a b reciprocal law b-type reciprocal-type)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list b a)))
         (entered (proof-proof-chain proof commute (list equality)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list reciprocal a)))
         (other (proof-proof-chain proof commute (list law)))
         (reverse-other (proof-proof-symmetric proof other))
         (comparison (proof-proof-chain proof entered (list reverse-other)))
         (result (h3-book-arithmetic-cancel-product lib b reciprocal a law comparison))
         (fixed-b (h3-book-arithmetic-fix-value lib b b-type))
         (result (proof-proof-rewrite proof result fixed-b '(1 1)))
         (fixed-reciprocal (h3-book-arithmetic-fix-value lib reciprocal reciprocal-type)))
      (proof-proof-rewrite proof result fixed-reciprocal '(1 2)))))

(defun h3-book-arithmetic-uniqueness-of-inverse-backward (equality lib product law)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reflexive (proof-proof-reflexive proof product))
         (reduced (proof-proof-rewrite proof reflexive equality '(1 2 2))))
      (proof-proof-chain proof reduced (list law)))))

(defun h3-book-arithmetic-uniqueness-of-inverse-case
    (a-type status nonzero lib left conditional product a b reciprocal right nonunit)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results ((fixed (h3-book-arithmetic-fix-value lib a a-type)))
      (if (not nonzero)
          (proof-with-checked-results
              ((literal (proof-step-first status))
               (empty (if (proof-is-call literal *proof-equal*)
                          (proof-proof-chain proof fixed (list status))
                        fixed))
               (guard (h3-rewrite-introduce-double-negation lib empty))
               (zero (h3-book-arithmetic-zero-product lib a b a status))
               (result (h3-book-arithmetic-uniqueness-of-inverse-avoid-unit zero lib left nonunit))
               (selected (proof-proof-select proof conditional guard))
               (reversed (proof-proof-symmetric proof selected)))
            (proof-proof-chain proof result (list reversed)))
        (proof-with-checked-results
            ((reverse-fixed (proof-proof-symmetric proof fixed))
             (guard (proof-proof-rewrite proof status reverse-fixed '(1 1 1)))
             (law (h3-book-arithmetic-inverse lib a a-type status))
             (reciprocal-type (h3-book-arithmetic-typed-number lib reciprocal))
             (test (list *library-numberp* b))
             (b-type (proof-proof-assume proof test t))
             (yes (h3-book-arithmetic-with-equivalent-equalities
                   lib left right
                   (h3-book-arithmetic-uniqueness-of-inverse-forward
                    lib a b reciprocal law b-type reciprocal-type)
                   (h3-book-arithmetic-uniqueness-of-inverse-backward lib product law)))
             (absent (proof-proof-assume proof test nil))
             (zero (h3-book-arithmetic-zero-product lib a b b absent))
             (left-nil (h3-book-arithmetic-uniqueness-of-inverse-avoid-unit zero lib left nonunit))
             (right-assumed (proof-proof-assume proof right t))
             (reversed (proof-proof-symmetric proof right-assumed))
             (hypothetical (proof-proof-rewrite proof reciprocal-type reversed '(1 1)))
             (cut (proof-proof-cut proof hypothetical absent))
             (no-inverse (proof-proof-front proof cut (proof-neg right)))
             (right-nil (h3-rewrite-nil-value lib no-inverse))
             (reverse-right (proof-proof-symmetric proof right-nil))
             (no (proof-proof-chain proof left-nil (list reverse-right)))
             (cases (proof-proof-cases proof test yes no))
             (selected (proof-proof-select proof conditional guard))
             (reversed (proof-proof-symmetric proof selected)))
          (proof-proof-chain proof cases (list reversed)))))))

(defun h3-book-arithmetic-uniqueness-of-inverse (lib formula)
  (proof-with-checked-results
      ((parts (h3-book-arithmetic-binary-arguments formula))
       (product (proof-term-at (car parts) 1))
       (factors (h3-book-arithmetic-binary-arguments product))
       (right (proof-term-at (cadr parts) 2))
       (nonunit (h3-book-arithmetic-search-prove
                 (h3-rewrite-search-init lib nil nil nil 150 nil)
                 (proof-neg (proof-eq *proof-zero* *proof-one*)) nil)))
    (let ((a (car factors)) (b (cadr factors))
          (left (car parts)) (conditional (cadr parts)))
      (h3-book-arithmetic-with-scalar-cases
       lib a (h3-book-arithmetic-uniqueness-of-inverse-case
              lib left conditional product a b (list *h3-book-arithmetic-divide* a) right nonunit)))))

(defun h3-book-arithmetic-right-cancellation-forward (step lib a b z law)
  (h3-book-arithmetic-cancel-product lib a b z law step))

(defun h3-book-arithmetic-right-cancellation-backward (step lib a b z)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((start (proof-proof-reflexive
                 proof (list *proof-times* (list *h3-book-arithmetic-fix* a) z)))
         (start (proof-proof-rewrite proof start step '(1 2 1)))
         (fixed (h3-book-arithmetic-multiply-fix lib a z))
         (start (proof-proof-rewrite proof start fixed '(1 1)))
         (fixed (h3-book-arithmetic-multiply-fix lib b z))
         (start (proof-proof-rewrite proof start fixed '(1 2))))
      (proof-proof-tidy proof start))))

(defun h3-book-arithmetic-right-cancellation-branch (numeric status nonzero lib formula p q a b z)
  (if (not nonzero)
      (proof-with-checked-results
          ((zero-a (h3-book-arithmetic-zero-product lib a z z status))
           (zero-b (h3-book-arithmetic-zero-product lib b z z status)))
        (h3-book-arithmetic-search-prove
         (h3-rewrite-search-init lib (list *h3-book-arithmetic-fix* *proof-not*) nil nil 150 nil)
         formula (list numeric status zero-a zero-b)))
    (proof-with-checked-results
        ((law (h3-book-arithmetic-inverse lib z numeric status))
         (comparison (h3-book-arithmetic-with-equivalent-equalities
                      lib p q (h3-book-arithmetic-right-cancellation-forward lib a b z law)
                      (h3-book-arithmetic-right-cancellation-backward lib a b z))))
      (h3-book-arithmetic-search-prove
       (h3-rewrite-search-init lib (list *h3-book-arithmetic-fix* *proof-not*) nil nil 150 nil)
       formula (list numeric status comparison)))))

(defun h3-book-arithmetic-right-cancellation (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (first-product (proof-term-at (cadr parts) 1))
       (first-factors (h3-book-arithmetic-binary-arguments first-product))
       (second-product (proof-term-at (cadr parts) 2))
       (b (proof-term-at second-product 1))
       (q (proof-term-at (caddr parts) 3)))
    (let ((a (car first-factors)) (z (cadr first-factors)))
      (h3-book-arithmetic-with-scalar-cases
       lib z (h3-book-arithmetic-right-cancellation-branch lib formula (cadr parts) q a b z)))))

(defun h3-book-arithmetic-left-cancellation-products (lib goal products index)
  (declare (xargs :measure (acl2-count products)))
  (if (endp products)
      goal
    (proof-with-checked-results
        ((args (h3-book-arithmetic-tail (car products)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" args))
         (next (proof-proof-rewrite (library-library-proof lib) goal commute (list 1 2 1 index))))
      (h3-book-arithmetic-left-cancellation-products lib next (cdr products) (1+ index)))))

(defun h3-book-arithmetic-left-cancellation (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equality (proof-term-at formula 1))
         (products (h3-book-arithmetic-tail equality))
         (goal (proof-proof-reflexive proof formula))
         (goal (h3-book-arithmetic-left-cancellation-products lib goal products 1))
         (right (h3-book-arithmetic-step-at goal 2))
         (result (h3-book-arithmetic-right-cancellation lib right)))
      (proof-proof-transport proof result goal))))

(defun h3-book-arithmetic-symmetric-callback (step lib)
  (proof-proof-symmetric (library-library-proof lib) step))

(defun h3-book-arithmetic-reciprocal-equality-forward (step lib law)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((rewritten (proof-proof-rewrite proof law step '(1 1 2)))
         (reversed (proof-proof-symmetric proof rewritten)))
      (proof-proof-tidy proof reversed))))

(defun h3-book-arithmetic-reciprocal-equality-backward (step lib x y r law)
  (let* ((proof (library-library-proof lib))
         (ypred (list *library-numberp* y)))
    (proof-with-checked-results
        ((missing (proof-proof-assume proof ypred nil))
         (default (library-library-axiom lib "DEFAULT-*-2" (list x y)))
         (default (proof-proof-modus-ponens proof default missing))
         (bad (proof-proof-rewrite proof step default '(1 2)))
         (literal (proof-step-first bad))
         (computed (proof-proof-compute proof literal *proof-nil*))
         (bad (proof-proof-rewrite proof bad computed '(1)))
         (bad (proof-proof-tidy proof bad))
         (yn (proof-proof-front proof bad ypred))
         (commute-first (library-library-axiom lib "COMMUTATIVITY-OF-*" (list r x)))
         (commute-last (library-library-axiom lib "COMMUTATIVITY-OF-*" (list x y)))
         (first (proof-proof-chain proof commute-first (list law step commute-last)))
         (canceled (h3-book-arithmetic-cancel-product lib r y x law first))
         (r-type (h3-book-arithmetic-typed-number lib r))
         (r-fixed (h3-book-arithmetic-fix-value lib r r-type))
         (canceled (proof-proof-rewrite proof canceled r-fixed '(1 1)))
         (y-fixed (h3-book-arithmetic-fix-value lib y yn))
         (canceled (proof-proof-rewrite proof canceled y-fixed '(1 2))))
      (proof-proof-tidy proof canceled))))

(defun h3-book-arithmetic-reciprocal-equality-branch (numeric status nonzero lib formula p q r x y)
  (if (not nonzero)
      (proof-with-checked-results
          ((zero (h3-book-arithmetic-zero-test lib x status))
           (reverse (h3-book-arithmetic-with-equivalent-equalities
                     lib (proof-eq *proof-zero* y) (proof-eq y *proof-zero*)
                     (h3-book-arithmetic-symmetric-callback lib)
                     (h3-book-arithmetic-symmetric-callback lib))))
        (h3-book-arithmetic-search-prove
         (h3-rewrite-search-init lib (list *proof-not* *h3-book-arithmetic-fix*) nil nil 150 nil)
         formula (list numeric status zero reverse)))
    (proof-with-checked-results
        ((law (h3-book-arithmetic-inverse lib x numeric status))
         (comparison (h3-book-arithmetic-with-equivalent-equalities
                      lib p q (h3-book-arithmetic-reciprocal-equality-forward lib law)
                      (h3-book-arithmetic-reciprocal-equality-backward lib x y r law))))
      (h3-book-arithmetic-search-prove
       (h3-rewrite-search-init lib (list *proof-not* *h3-book-arithmetic-fix*) nil nil 150 nil)
       formula (list numeric status comparison)))))

(defun h3-book-arithmetic-reciprocal-equality (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (sides (h3-book-arithmetic-binary-arguments (cadr parts)))
       (x (proof-term-at (car sides) 1))
       (q (proof-term-at (caddr parts) 2)))
    (h3-book-arithmetic-with-scalar-cases
     lib x (h3-book-arithmetic-reciprocal-equality-branch
            lib formula (cadr parts) q (car sides) x (cadr sides)))))

(defun h3-book-arithmetic-reciprocal-fix (lib x)
  (let* ((proof (library-library-proof lib))
         (target (proof-eq (list *h3-book-arithmetic-divide* (list *h3-book-arithmetic-fix* x))
                           (list *h3-book-arithmetic-divide* x)))
         (test (list *library-numberp* x)))
    (proof-with-checked-results
        ((branch (proof-proof-assume proof test t))
         (start (proof-proof-reflexive proof (cadr target)))
         (fixed (h3-book-arithmetic-fix-value lib x branch))
         (yes (proof-proof-rewrite proof start fixed '(1 2 1)))
         (denied (proof-proof-assume proof test nil))
         (start (proof-proof-reflexive proof (cadr target)))
         (fixed (h3-book-arithmetic-fix-value lib x denied))
         (no (proof-proof-rewrite proof start fixed '(1 2 1)))
         (computed (proof-proof-compute proof (list *h3-book-arithmetic-divide* *proof-zero*) 0))
         (zero (h3-book-arithmetic-zero-test lib x denied))
         (reverse-zero (proof-proof-symmetric proof zero))
         (no (proof-proof-chain proof no (list computed reverse-zero)))
         (yes (proof-proof-tidy proof yes)))
      (proof-proof-cases proof test yes no))))

(defun h3-book-arithmetic-compare-reciprocals-forward (step lib p inversion-a inversion-b)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left (proof-term-at p 1))
         (start (proof-proof-reflexive proof (list *h3-book-arithmetic-divide* left)))
         (start (proof-proof-rewrite proof start step '(1 2 1)))
         (start (proof-proof-rewrite proof start inversion-a '(1 1)))
         (start (proof-proof-rewrite proof start inversion-b '(1 2))))
      (proof-proof-tidy proof start))))

(defun h3-book-arithmetic-compare-reciprocals-backward (step lib q a b)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((left (proof-term-at q 1))
         (start (proof-proof-reflexive proof (list *h3-book-arithmetic-divide* left)))
         (start (proof-proof-rewrite proof start step '(1 2 1)))
         (fixed (h3-book-arithmetic-reciprocal-fix lib a))
         (start (proof-proof-rewrite proof start fixed '(1 1)))
         (fixed (h3-book-arithmetic-reciprocal-fix lib b))
         (start (proof-proof-rewrite proof start fixed '(1 2))))
      (proof-proof-tidy proof start))))

(defun h3-book-arithmetic-unary-values (terms fixed-only)
  (if (endp terms)
      nil
    (proof-with-checked-results
        ((value (if (or (not fixed-only)
                        (proof-is-call (car terms) *h3-book-arithmetic-fix*))
                    (proof-term-at (car terms) 1)
                  (car terms)))
         (rest (h3-book-arithmetic-unary-values (cdr terms) fixed-only)))
      (cons value rest))))

(defun h3-book-arithmetic-unpack-unary-values (term fixed-only)
  (proof-with-checked-results
      ((args (h3-book-arithmetic-tail term))
       (values (h3-book-arithmetic-unary-values (seq-slice args 0 3) fixed-only)))
    (proof-list-of-length values 2)))

(defun h3-book-arithmetic-compare-reciprocals (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (factors (h3-book-arithmetic-unpack-unary-values (cadr parts) nil))
       (inversion-a (h3-book-arithmetic-reciprocal-involution lib (car factors)))
       (inversion-b (h3-book-arithmetic-reciprocal-involution lib (cadr factors))))
    (h3-book-arithmetic-with-equivalent-equalities
     lib (cadr parts) (caddr parts)
     (h3-book-arithmetic-compare-reciprocals-forward lib (cadr parts) inversion-a inversion-b)
     (h3-book-arithmetic-compare-reciprocals-backward lib (caddr parts) (car factors) (cadr factors)))))

(defun h3-book-arithmetic-negative-product (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (left (cadr parts))
         (prod (proof-term-at (caddr parts) 1))
         (factors (h3-book-arithmetic-binary-arguments prod))
         (a (car factors))
         (b (cadr factors))
         (opposite (list *proof-minus* b))
         (split (library-library-axiom lib "DISTRIBUTIVITY" (list a b opposite)))
         (reverse-split (proof-proof-symmetric proof split))
         (inverse (library-library-axiom lib "INVERSE-OF-+" (list b)))
         (zero (proof-proof-rewrite proof reverse-split inverse '(1 2 2)))
         (multiply-zero (h3-event-counts-multiply-zero lib a))
         (zero (proof-proof-chain proof zero (list multiply-zero)))
         (neg-prod (list *proof-minus* prod))
         (associate (library-library-axiom lib "ASSOCIATIVITY-OF-+" (list neg-prod prod left)))
         (cancel (proof-proof-symmetric proof associate))
         (cancel (proof-proof-rewrite proof cancel zero '(1 1 2)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-+" (list neg-prod prod)))
         (inverse (library-library-axiom lib "INVERSE-OF-+" (list prod)))
         (neg-sum (proof-proof-chain proof commute (list inverse)))
         (cancel (proof-proof-rewrite proof cancel neg-sum '(1 2 1)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-+" (list neg-prod *proof-zero*)))
         (unit (library-library-axiom lib "UNICITY-OF-0" (list neg-prod)))
         (leftzero (proof-proof-chain proof commute (list unit)))
         (closure (library-library-axiom lib "CLOSURE" (list prod *proof-zero*)))
         (parts (proof-proof-conjunct proof closure))
         (parts (proof-proof-conjunct proof (cadr parts)))
         (parts (proof-proof-conjunct proof (cadr parts)))
         (negate-number (car parts))
         (fixed (h3-book-arithmetic-fix-value lib neg-prod negate-number))
         (leftzero (proof-proof-chain proof leftzero (list fixed)))
         (unit (library-library-axiom lib "UNICITY-OF-0" (list left)))
         (left-type (h3-book-arithmetic-typed-number lib left))
         (fixed (h3-book-arithmetic-fix-value lib left left-type))
         (rightzero (proof-proof-chain proof unit (list fixed)))
         (cancel (proof-proof-rewrite proof cancel leftzero '(1 1)))
         (cancel (proof-proof-chain proof cancel (list rightzero)))
         (reversed (proof-proof-symmetric proof cancel)))
      (proof-proof-tidy proof reversed))))

(defun h3-book-arithmetic-multiply-out-rewrite (proof step part index)
  (proof-with-checked-results
      ((left (h3-book-arithmetic-step-at part 1))
       (right (h3-book-arithmetic-step-at part 2)))
    (if (equal left right)
        step
      (proof-proof-rewrite proof step part (list 1 2 index)))))

(mutual-recursion
 (defun h3-book-arithmetic-multiply-out (lib factor expression)
   (declare (xargs :measure (acl2-count expression)))
   (if (and (consp expression) (proof-is-call expression *proof-plus*))
       (proof-with-checked-results
           ((parts (h3-book-arithmetic-binary-arguments expression))
            (step (library-library-axiom lib "DISTRIBUTIVITY" (cons factor parts))))
         (h3-book-arithmetic-multiply-out-arguments lib factor (cdr expression) step 1))
     (proof-proof-reflexive (library-library-proof lib)
                            (list *proof-times* factor expression))))
 (defun h3-book-arithmetic-multiply-out-arguments (lib factor args step index)
   (declare (xargs :measure (acl2-count args)))
   (let ((proof (library-library-proof lib)))
     (if (endp args)
         (proof-proof-tidy proof step)
       (proof-with-checked-results
           ((part (h3-book-arithmetic-multiply-out lib factor (car args)))
            (next (h3-book-arithmetic-multiply-out-rewrite proof step part index)))
         (h3-book-arithmetic-multiply-out-arguments lib factor (cdr args) next (1+ index)))))))

(defun h3-book-arithmetic-factor-out (lib expression base factor)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((commute (library-library-axiom lib "COMMUTATIVITY-OF-*" (list base factor)))
         (multiply (h3-book-arithmetic-multiply-out lib factor base))
         (expanded (proof-proof-chain proof commute (list multiply)))
         (expanded-value (h3-book-arithmetic-step-at expanded 2))
         (aligned (h3-book-arithmetic-associative-equal lib expression expanded-value))
         (reversed (proof-proof-symmetric proof expanded)))
      (proof-proof-chain proof aligned (list reversed)))))

(defun h3-book-arithmetic-all-equalities-p (terms)
  (or (endp terms)
      (and (proof-is-call (car terms) *proof-equal*)
           (h3-book-arithmetic-all-equalities-p (cdr terms)))))

(defun h3-book-arithmetic-factor-cancellation-guard-p (guard)
  (and (proof-is-call guard *proof-not*)
       (proof-with-checked-results ((test (proof-term-at guard 1)))
         (and (proof-is-call test *proof-equal*)
              (proof-with-checked-results ((right (proof-term-at test 2)))
                (and (equal right *proof-zero*)
                     (proof-with-checked-results ((left (proof-term-at test 1)))
                       (proof-is-call left *h3-book-arithmetic-fix*))))))))

(defun h3-book-arithmetic-factor-cancellation-fixed (lib expected value)
  (if (proof-is-call expected *h3-book-arithmetic-fix*)
      nil
    (proof-with-checked-results ((numeric (h3-book-arithmetic-typed-number lib value)))
      (h3-book-arithmetic-fix-value lib value numeric))))

(defun h3-book-arithmetic-factor-cancellation-rewrite (proof step equation index reversed)
  (if (not equation)
      step
    (proof-with-checked-results
        ((equality (if reversed (proof-proof-symmetric proof equation) equation)))
      (proof-proof-rewrite proof step equality (list 1 index)))))

(defun h3-book-arithmetic-factor-cancellation-forward (step lib left right a b factor law fixed-a fixed-b)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((aligned (proof-proof-rewrite proof step left '(1 1)))
         (aligned (proof-proof-rewrite proof aligned right '(1 2)))
         (reduced (h3-book-arithmetic-cancel-product lib a b factor law aligned))
         (reduced (h3-book-arithmetic-factor-cancellation-rewrite proof reduced fixed-a 1 nil))
         (reduced (h3-book-arithmetic-factor-cancellation-rewrite proof reduced fixed-b 2 nil)))
      (proof-proof-tidy proof reduced))))

(defun h3-book-arithmetic-factor-cancellation-backward (step lib left right a b factor fixed-a fixed-b)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((step (h3-book-arithmetic-factor-cancellation-rewrite proof step fixed-a 1 t))
         (step (h3-book-arithmetic-factor-cancellation-rewrite proof step fixed-b 2 t))
         (before (proof-proof-reflexive
                  proof (list *proof-times* (list *h3-book-arithmetic-fix* a) factor)))
         (tidied (proof-proof-tidy proof step))
         (before (proof-proof-rewrite proof before tidied '(1 2 1)))
         (fixed (h3-book-arithmetic-multiply-fix lib a factor))
         (before (proof-proof-rewrite proof before fixed '(1 1)))
         (fixed (h3-book-arithmetic-multiply-fix lib b factor))
         (before (proof-proof-rewrite proof before fixed '(1 2)))
         (reverse-left (proof-proof-symmetric proof left))
         (before (proof-proof-rewrite proof before reverse-left '(1 1)))
         (reverse-right (proof-proof-symmetric proof right))
         (before (proof-proof-rewrite proof before reverse-right '(1 2))))
      (proof-proof-tidy proof before))))

(defun h3-book-arithmetic-factor-cancellation-equality (lib guard equality)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((factor (proof-term-at (cadr (cadr guard)) 1))
         (parts (h3-book-arithmetic-binary-arguments equality))
         (p (car parts))
         (q (cadr parts))
         (values (h3-book-arithmetic-unpack-unary-values q t))
         (a (car values))
         (b (cadr values))
         (p-left (proof-term-at p 1))
         (left (h3-book-arithmetic-factor-out lib p-left a factor))
         (p-right (proof-term-at p 2))
         (right (h3-book-arithmetic-factor-out lib p-right b factor))
         (numeric (list *library-numberp* factor))
         (denied (proof-proof-assume proof numeric nil))
         (given (proof-proof-assume proof guard t))
         (fixed (h3-book-arithmetic-fix-value lib factor denied))
         (cut (proof-proof-cut proof fixed given))
         (numeric-proof (proof-proof-front proof cut numeric))
         (fixed (h3-book-arithmetic-fix-value lib factor numeric-proof))
         (nonzero (proof-proof-rewrite proof given fixed '(1 1 1)))
         (nonzero (proof-proof-tidy proof nonzero))
         (law (h3-book-arithmetic-inverse lib factor numeric-proof nonzero))
         (fixed-a (h3-book-arithmetic-factor-cancellation-fixed lib (cadr q) a))
         (fixed-b (h3-book-arithmetic-factor-cancellation-fixed lib (caddr q) b))
         (result (h3-book-arithmetic-with-equivalent-equalities
                  lib p q
                  (h3-book-arithmetic-factor-cancellation-forward lib left right a b factor law fixed-a fixed-b)
                  (h3-book-arithmetic-factor-cancellation-backward lib left right a b factor fixed-a fixed-b))))
      (h3-rewrite-implication lib guard result))))

(defun h3-book-arithmetic-factor-cancellation (lib formula)
  (and (proof-is-call formula *library-implies*)
       (proof-with-checked-results
           ((parts (h3-book-arithmetic-binary-arguments formula))
            (guard (car parts))
            (equality (cadr parts))
            (guard-p (h3-book-arithmetic-factor-cancellation-guard-p guard)))
         (and guard-p
              (proof-is-call equality *proof-equal*)
              (h3-book-arithmetic-all-equalities-p (cdr equality))
              (h3-book-arithmetic-factor-cancellation-equality lib guard equality)))))

(defun h3-book-arithmetic-associative-argument-p (args)
  (and (consp args)
       (or (and (h3-rewrite-arguments (car args))
                (assoc-equal (caar args) *h3-book-arithmetic-associative*))
           (h3-book-arithmetic-associative-argument-p (cdr args)))))

(defun h3-book-arithmetic-associative-consequent (lib args)
  (let ((size (len args)))
    (cond ((equal size 2)
           (h3-book-arithmetic-associative-equal lib (car args) (cadr args)))
          ((equal size 1)
           '(:failure "failure" ""))
          (t '(:failure "failure" "")))))

(defun h3-book-arithmetic-arithmetic-theorem-fallback (lib formula)
  (proof-with-checked-results ((canceled (h3-book-arithmetic-factor-cancellation lib formula)))
    (or canceled
        (let ((implies (proof-is-call formula *library-implies*)))
          (proof-with-checked-results
              ((consequent (if implies (proof-term-at formula 2) formula)))
            (and (proof-is-call consequent *proof-equal*)
                 (h3-book-arithmetic-associative-argument-p (h3-rewrite-arguments consequent))
                 (proof-with-checked-results
                     ((step (h3-book-arithmetic-associative-consequent lib (cdr consequent))))
                   (if implies
                       (proof-with-checked-results ((guard (proof-term-at formula 1)))
                         (h3-rewrite-implication lib guard step))
                     step))))))))

(defun h3-book-arithmetic-arithmetic-theorem-times-zero (lib formula)
  (proof-with-checked-results ((product (proof-term-at formula 1)))
    (if (proof-is-call product *proof-times*)
        (proof-with-checked-results ((left (proof-term-at product 1)))
          (if (equal left *proof-zero*)
              (proof-with-checked-results ((right (proof-term-at product 2)))
                (h3-book-arithmetic-zero-left lib right))
            (h3-book-arithmetic-arithmetic-theorem-fallback lib formula)))
      (h3-book-arithmetic-arithmetic-theorem-fallback lib formula))))

(defun h3-book-arithmetic-arithmetic-theorem-minus-left (lib formula)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (h3-book-arithmetic-binary-arguments formula))
         (goal (proof-proof-reflexive proof formula))
         (args (h3-book-arithmetic-tail (car parts)))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" args))
         (goal (proof-proof-rewrite proof goal commute '(1 2 1)))
         (product (proof-term-at (cadr parts) 1))
         (args (h3-book-arithmetic-tail product))
         (commute (library-library-axiom lib "COMMUTATIVITY-OF-*" args))
         (goal (proof-proof-rewrite proof goal commute '(1 2 2 1)))
         (rewritten (h3-book-arithmetic-step-at goal 2))
         (result (h3-book-arithmetic-negative-product lib rewritten)))
      (proof-proof-transport proof result goal))))

(defun h3-book-arithmetic-arithmetic-theorem (lib name formula)
  (cond ((equal name "UNIQUENESS-OF-*-INVERSES")
         (h3-book-arithmetic-uniqueness-of-inverse lib formula))
        ((member-equal name '("PRODUCT-EQUAL-ZERO" "EQUAL-*-X-Y-0"))
         (h3-book-arithmetic-product-equal-zero lib formula))
        ((equal name "FUNCTIONAL-SELF-INVERSION-OF-/")
         (proof-with-checked-results
             ((rhs (proof-term-at formula 2))
              (term (proof-term-at rhs 1)))
           (h3-book-arithmetic-reciprocal-involution lib term)))
        ((equal name "DISTRIBUTIVITY-OF-/-OVER-*")
         (h3-book-arithmetic-reciprocal-product lib formula))
        ((member-equal name '("/-CANCELLATION-ON-RIGHT" "/-CANCELLATION-ON-LEFT"))
         (h3-book-arithmetic-cancel-reciprocal-product lib formula))
        ((equal name "EQUAL-/-0")
         (h3-book-arithmetic-reciprocal-zero-test lib formula))
        ((equal name "TIMES-ZERO")
         (h3-book-arithmetic-arithmetic-theorem-times-zero lib formula))
        ((equal name "RIGHT-CANCELLATION-FOR-*")
         (h3-book-arithmetic-right-cancellation lib formula))
        ((equal name "LEFT-CANCELLATION-FOR-*")
         (h3-book-arithmetic-left-cancellation lib formula))
        ((equal name "EQUAL-/")
         (h3-book-arithmetic-reciprocal-equality lib formula))
        ((equal name "EQUAL-/-/")
         (h3-book-arithmetic-compare-reciprocals lib formula))
        ((equal name "FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-RIGHT")
         (h3-book-arithmetic-negative-product lib formula))
        ((equal name "FUNCTIONAL-COMMUTATIVITY-OF-MINUS-*-LEFT")
         (h3-book-arithmetic-arithmetic-theorem-minus-left lib formula))
        (t (h3-book-arithmetic-arithmetic-theorem-fallback lib formula))))
