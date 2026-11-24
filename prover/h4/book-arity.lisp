(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-arity-take* (proof-sym "TAKE" "ACL2"))
(defconst *h4-book-arity-pairlis* (proof-sym "PAIRLIS$" "ACL2"))
(defconst *h4-book-arity-apply* (proof-sym "APPLY$" "ACL2"))
(defconst *h4-book-arity-apply-lambda* (proof-sym "APPLY$-LAMBDA" "ACL2"))
(defconst *h4-book-arity-formals* (proof-sym "LAMBDA-OBJECT-FORMALS" "ACL2"))
(defconst *h4-book-arity-body* (proof-sym "LAMBDA-OBJECT-BODY" "ACL2"))
(defconst *h4-book-arity-primitive* (proof-sym "APPLY$-PRIM" "ACL2"))
(defconst *h4-book-arity-primitivep* (proof-sym "APPLY$-PRIMP" "ACL2"))
(defconst *h4-book-arity-lamb* (proof-sym "LAMB" "ACL2"))
(defconst *h4-book-arity-checked-badge* (proof-sym "APPLY$-BADGEP" "ACL2"))
(defconst *h4-book-arity-tame-arguments* (proof-sym "SUITABLY-TAMEP-LISTP" "ACL2"))
(defconst *h4-book-arity-badge* (proof-sym "BADGE" "ACL2"))
(defconst *h4-book-arity-primitive-badge* (proof-sym "BADGE-PRIM" "ACL2"))
(defconst *h4-book-arity-user-badge* (proof-sym "BADGE-USERFN" "ACL2"))

(defun h4-book-arity-at (term indices)
  (declare (xargs :measure (acl2-count indices)))
  (if (endp indices)
      term
    (proof-with-checked-results ((child (proof-term-at term (car indices))))
      (h4-book-arity-at child (cdr indices)))))

(defun h4-book-arity-step-at (step indices)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (h4-book-arity-at literal indices)))

(defun h4-book-arity-length-shape (term size)
  (declare (xargs :measure (nfix size)))
  (cond ((equal size 0) (proof-neg (list *proof-consp* term)))
        ((not (posp size)) '(:failure "failure" ""))
        (t (proof-with-checked-results
               ((tail (h4-book-arity-length-shape (list *library-cdr* term) (1- size))))
             (proof-ite (list *proof-consp* term) tail *proof-false*)))))

(defun h4-book-arity-length-positive (p term shape)
  (let ((length (list *library-len* term))
        (tail (list *library-len* (list *library-cdr* term))))
    (proof-with-checked-results
        ((natural (library-library-natural p tail))
         (nonnegative (library-library-cite p "NATURAL-NONNEGATIVE" (list tail) (list natural)))
         (positive-one (h4-tactics-tactics-establish
                        p (library-lt *proof-zero* *proof-one*) nil nil nil nil))
         (integer-tail (library-library-type-of p tail nil))
         (integer-one (library-library-type-of p *proof-one* nil))
         (successor (library-library-cite p "POSITIVE-PLUS-NONNEGATIVE" (list tail *proof-one*)
                                          (list integer-tail integer-one positive-one nonnegative)))
         (view (h4-book-order-order-view p length (list shape) nil)))
      (library-library-transport-argument p successor view 2))))

(defun h4-book-arity-predecessor-length (p term shape)
  (let ((length (list *library-len* term))
        (proof (library-library-proof p)))
    (proof-with-checked-results
        ((view (h4-book-order-order-view p length (list shape) nil))
         (expanded (h4-tactics-tactics-normalize p (h4-book-arithmetic-predecessor length)
                                                nil nil (list view) nil))
         (value (h4-book-arity-step-at expanded '(2)))
         (linear (library-library-linear-equal p value (list *library-len* (list *library-cdr* term))
                                              nil)))
      (proof-proof-chain proof expanded (list linear)))))

(defun h4-book-arity-length-equals-atom (shape p goal)
  (proof-with-checked-results ((nil-shape (h4-tactics-tactics-nil-value p shape)))
    (h4-tactics-tactics-establish p goal nil (append *h4-book-flatten-logic* (list *library-len*))
                                (list nil-shape) nil)))

(defun h4-book-arity-length-equals-zero (p term shape right)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((strict (h4-book-arity-length-positive p term shape))
         (unequal (h4-book-order-order-unequal p strict :primitive))
         (nonzero (h4-book-order-reflected-test p unequal))
         (zero-test (h4-tactics-tactics-nil-value p nonzero))
         (shape-value (h4-tactics-tactics-normalize p right (list shape)
                                                   *h4-book-flatten-logic* nil nil))
         (reverse (proof-proof-symmetric proof shape-value)))
      (proof-proof-chain proof zero-test (list reverse)))))

(defun h4-book-arity-length-equals-pair-prepare (shape p term size right length number)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((length-type (library-library-type-of p length nil))
         (number-type (library-library-type-of p number nil))
         (congruence (proof-proof-use
                      proof *h4-book-updates-equal-predecessors*
                      (list (list *library-x* length) (list *library-y* number))
                      (list length-type number-type)))
         (shorter (h4-book-arity-predecessor-length p term shape))
         (congruence (proof-proof-rewrite proof congruence shorter '(1 1 1)))
         (previous (proof-proof-compute proof (h4-book-arithmetic-predecessor number) (1- size)))
         (congruence (proof-proof-rewrite proof congruence previous '(1 1 2)))
         (right-value (proof-proof-select proof right shape))
         (start (proof-proof-symmetric proof congruence)))
      (list start right-value))))

(defun h4-book-arity-length-equals-prepare (p term size)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((right (h4-book-arity-length-shape term size))
         (shape (proof-proof-assume proof (list *proof-consp* term) t))
         (start (if (zp size)
                    (h4-book-arity-length-equals-zero p term shape right)
                  (h4-book-arity-length-equals-pair-prepare
                   shape p term size right (list *library-len* term) (proof-quote size)))))
      (list right start))))

(defun h4-book-arity-length-equals-pair (p start child)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((end (proof-proof-symmetric proof (cadr start))))
      (proof-proof-chain proof (car start) (list child end)))))

(defun h4-book-arity-length-equals-finish (p term size right yes)
  (let ((goal (proof-eq (proof-eq (list *library-len* term) (proof-quote size)) right))
        (test (list *proof-consp* term)))
    (proof-with-checked-results
        ((shape (proof-proof-assume (library-library-proof p) test nil))
         (no (h4-book-arity-length-equals-atom shape p goal)))
      (h4-tactics-tactics-case-of p goal test yes no))))

(defun h4-book-arity-length-equals-visit (p term size prepared)
  (declare (xargs :measure (nfix size)))
  (cond ((failure-p prepared) prepared)
        ((zp size) (h4-book-arity-length-equals-finish p term size (car prepared) (cadr prepared)))
        (t (let ((tail (list *library-cdr* term)))
             (proof-with-checked-results
                 ((child (h4-book-arity-length-equals-visit
                          p tail (1- size) (h4-book-arity-length-equals-prepare p tail (1- size))))
                  (yes (h4-book-arity-length-equals-pair p (cadr prepared) child)))
               (h4-book-arity-length-equals-finish p term size (car prepared) yes))))))

(defun h4-book-arity-length-equals (p term size)
  (h4-book-arity-length-equals-visit p term size (h4-book-arity-length-equals-prepare p term size)))

(defun h4-book-arity-length-test-width (predicate cursor width term number)
  (declare (xargs :measure (acl2-count predicate)))
  (let ((consp-test (list *proof-consp* cursor)))
    (proof-with-checked-results
        ((advance (and (proof-is-call predicate *proof-if*)
                       (proof-with-checked-results ((test (proof-term-at predicate 1)))
                         (and (equal test consp-test)
                              (proof-with-checked-results ((no (proof-term-at predicate 3)))
                                (equal no *proof-false*)))))))
      (if (and (consp predicate) advance)
          (h4-book-arity-length-test-width (caddr predicate) (list *library-cdr* cursor)
                                            (1+ width) term number)
        (and (equal width number) (equal predicate (proof-neg consp-test)) (list term width))))))

(defun h4-book-arity-length-test (formula)
  (and (proof-is-call formula *proof-equal*)
       (proof-with-checked-results ((equality (proof-term-at formula 1)))
         (and (proof-is-call equality *proof-equal*)
              (proof-with-checked-results ((length (proof-term-at equality 1)))
                (and (proof-is-call length *library-len*)
                     (proof-with-checked-results
                         ((outer (proof-list-of-length formula 3))
                          (inner (proof-list-of-length equality 3))
                          (length (proof-list-of-length length 2)))
                       (let ((number (caddr inner))
                             (term (cadr length)))
                         (and (proof-is-call number *proof-quote*)
                              (proof-with-checked-results ((size (proof-term-at number 1)))
                                (and (integerp size)
                                     (h4-book-arity-length-test-width
                                      (caddr outer) term 0 term size))))))))))))

(defun h4-book-arity-prefix-shape (formula)
  (and (proof-is-call formula *proof-equal*)
       (proof-with-checked-results ((left (proof-term-at formula 1)))
         (and (proof-is-call left *h4-book-arity-pairlis*)
              (proof-with-checked-results ((right (proof-term-at formula 2)))
                (and (proof-is-call right *h4-book-arity-pairlis*)
                     (proof-with-checked-results
                         ((outer (proof-list-of-length formula 3))
                          (pair (proof-list-of-length (caddr outer) 3)))
                       (let ((sequence (cadr pair))
                             (values (caddr pair)))
                         (and (not (proof-compound sequence))
                              (not (proof-compound values))
                              (not (equal sequence values))
                              (equal left (list *h4-book-arity-pairlis* sequence
                                                (list *h4-book-arity-take*
                                                      (list *library-len* sequence) values)))
                              (list sequence values))))))))))

(defun h4-book-arity-fixed-prefix-opened (term shape rewrites p provide)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((projected (h4-book-order-order-view p term (list shape) *h4-book-flatten-logic*)))
      (if (endp rewrites)
          projected
        (proof-with-checked-results
            ((value (h4-book-arity-step-at projected '(2)))
             (reduced (h4-tactics-tactics-normalize p value nil nil rewrites provide)))
          (proof-proof-chain proof projected (list reduced)))))))

(defun h4-book-arity-fixed-prefix-empty (shape p left right provide)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((first (h4-book-arity-fixed-prefix-opened left shape nil p provide))
         (last (h4-book-arity-fixed-prefix-opened right shape nil p provide))
         (reverse (proof-proof-symmetric proof last)))
      (proof-proof-chain proof first (list reverse)))))

(defun h4-book-arity-fixed-prefix-step (shape hypothesis p sequence length taken left right provide)
  (let ((proof (library-library-proof p))
        (test (list *h4-book-arithmetic-zp* length)))
    (proof-with-checked-results
        ((positive (h4-book-arity-length-positive p sequence shape))
         (integer (library-library-type-of p length nil))
         (stopping (h4-tactics-tactics-normalize
                    p test (list positive integer)
                    (append *h4-book-flatten-logic* (list *h4-book-arithmetic-zp*)) nil nil))
         (continuing (h4-book-order-false-value p stopping))
         (taken-once (h4-book-order-order-view p taken (list continuing) nil))
         (shorter (h4-book-arity-predecessor-length p sequence shape))
         (taken-once (proof-proof-rewrite proof taken-once shorter '(1 2 2 1)))
         (first (h4-book-arity-fixed-prefix-opened left shape (list taken-once) p provide))
         (remaining (proof-proof-rewrite proof first hypothesis '(1 2 2)))
         (last (h4-book-arity-fixed-prefix-opened right shape nil p provide))
         (reverse (proof-proof-symmetric proof last)))
      (proof-proof-chain proof remaining (list reverse)))))

(defun h4-book-arity-fixed-prefix (p formula sequence values)
  (let ((proof (library-library-proof p))
        (length (list *library-len* sequence))
        (test (list *proof-consp* sequence))
        (changes (list (list values (list *library-cdr* values)))))
    (proof-with-checked-results
        ((sides (proof-list-of-length (cdr formula) 2))
         (taken (proof-term-at (car sides) 2))
         (provide (h4-book-finite-reduction-provider p))
         (yes-shape (proof-proof-assume proof test t))
         (hypothesis (h4-book-flatten-cdr-induction-recurse yes-shape p formula sequence changes))
         (step (h4-book-arity-fixed-prefix-step yes-shape hypothesis p sequence length taken
                                                (car sides) (cadr sides) provide))
         (no-shape (proof-proof-assume proof test nil))
         (base (h4-book-arity-fixed-prefix-empty no-shape p (car sides) (cadr sides) provide)))
      (h4-book-flatten-cdr-induction p formula sequence base step changes))))

(defun h4-book-arity-checked-length-call (guard goal natural test)
  (proof-with-checked-results
      ((count (proof-term-at natural 1))
       (sequence (proof-term-at test 1))
       (call (proof-term-at guard 1)))
    (and (proof-compound call)
         (proof-with-checked-results ((head (proof-term-at call 0)))
           (and (not (proof-compound head))
                (equal (len call) 4)
                (equal (cadr call) count)
                (equal (cadddr call) sequence)
                (not (proof-compound count))
                (not (proof-compound (caddr call)))
                (not (proof-compound sequence))
                (not (equal count (caddr call)))
                (not (equal count sequence))
                (not (equal (caddr call) sequence))
                (equal goal (proof-ite (list *h4-book-updates-true-list* sequence)
                                       (proof-eq (list *library-len* sequence) count) *proof-false*))
                call)))))

(defun h4-book-arity-checked-length-shape (formula)
  (and (proof-is-call formula *library-implies*)
       (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
         (let ((guard (cadr parts)) (goal (caddr parts)))
           (and (proof-is-call guard *proof-if*)
                (proof-with-checked-results ((no (proof-term-at guard 3)))
                  (and (equal no *proof-false*)
                       (proof-with-checked-results ((natural (proof-term-at guard 2)))
                         (and (proof-is-call natural *library-natp*)
                              (proof-is-call goal *proof-if*)
                              (proof-with-checked-results ((test (proof-term-at goal 1)))
                                (and (proof-is-call test *h4-book-updates-true-list*)
                                     (h4-book-arity-checked-length-call guard goal natural test))))))))))))

(defun h4-book-arity-binding-map (bindings result)
  (if (endp bindings)
      result
    (h4-book-arity-binding-map (cdr bindings)
                               (table-put result (caar bindings) (cadar bindings)))))

(defun h4-book-arity-checked-length-stopped (test-proof p count natural given opened sequence goal)
  (let ((proof (library-library-proof p))
        (null-symbol (proof-cl "NULL"))
        (eq-symbol (proof-cl "EQ")))
    (proof-with-checked-results
        ((zero (proof-proof-use proof *h4-book-arithmetic-natural-countdown-zero*
                               (list (list *library-x* count)) (list natural test-proof)))
         (value (h4-book-arity-step-at opened '(2)))
         (selected (proof-proof-select proof value test-proof))
         (chain (proof-proof-chain proof opened (list selected)))
         (empty (proof-proof-rewrite proof given chain '(1)))
         (literal (proof-step-first empty)))
      (if (not (equal literal (list null-symbol sequence)))
          '(:failure "InapplicableStep" "")
        (proof-with-checked-results
            ((normalized (h4-tactics-tactics-normalize p literal nil (list null-symbol eq-symbol)
                                                       nil nil))
             (empty (proof-proof-rewrite proof empty normalized '(1))))
          (h4-tactics-tactics-establish
           p goal nil (append *h4-book-flatten-logic* (list *library-len* *h4-book-updates-true-list*))
           (list empty zero) nil))))))

(defun h4-book-arity-checked-length-child
    (p certified test-proof formula bindings count natural sequence shape goal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((pair (h4-tactics-tactics-conjunct p certified))
         (builtin (library-library-builtin p 9 count))
         (decreases (proof-proof-discharge proof builtin test-proof))
         (instance (proof-subst formula (h4-book-arity-binding-map bindings nil)))
         (condition (proof-step-first decreases))
         (assumed (proof-proof-assume proof (proof-ite condition instance *proof-true*) t))
         (induction (proof-proof-prove-if proof assumed decreases))
         (next-type (proof-proof-use proof *h4-book-updates-predecessor-natural*
                                    (list (list *library-x* count)) (list test-proof)))
         (next (h4-book-division-conjunction p (list (cadr pair) next-type)))
         (proved (h4-tactics-tactics-modus-ponens p induction next))
         (tail (h4-tactics-tactics-conjunct p proved))
         (type-view (h4-book-order-order-view
                     p (list *h4-book-updates-true-list* sequence) (list shape) nil))
         (proper (proof-proof-transport proof (car tail) type-view))
         (length (h4-book-order-order-view p (list *library-len* sequence) (list shape) nil))
         (length (proof-proof-rewrite proof length (cadr tail) '(1 2 2)))
         (integral (library-library-cite p "NATURAL-INTEGER" (list count) (list natural)))
         (value (h4-book-arity-step-at length '(2)))
         (linear (library-library-linear-equal p value count (list integral)))
         (exact (proof-proof-chain proof length (list linear))))
      (h4-tactics-tactics-conjunction p goal proper exact))))

(defun h4-book-arity-checked-length-active-body
    (shape p running given goal count test-proof formula bindings natural sequence)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((value (h4-book-arity-step-at running '(2)))
         (observed (h4-tactics-tactics-normalize p value (list shape) *h4-book-flatten-logic* nil nil))
         (chain (proof-proof-chain proof running (list observed)))
         (certified (proof-proof-rewrite proof given chain '(1)))
         (literal (proof-step-first shape)))
      (if (proof-is-call literal *proof-consp*)
          (h4-book-arity-checked-length-child
           p certified test-proof formula bindings count natural sequence shape goal)
        (proof-with-checked-results ((literal (proof-step-first certified)))
          (if (equal literal *proof-false*)
              (proof-proof-subsume proof certified (cons goal (cdr (proof-step-clause certified))))
            '(:failure "InapplicableStep" "")))))))

(defun h4-book-arity-checked-length-active
    (test-proof p opened given goal count formula bindings natural sequence)
  (let ((proof (library-library-proof p))
        (test (list *proof-consp* sequence)))
    (proof-with-checked-results
        ((value (h4-book-arity-step-at opened '(2)))
         (selected (proof-proof-select proof value test-proof))
         (running (proof-proof-chain proof opened (list selected)))
         (yes-shape (proof-proof-assume proof test t))
         (yes (h4-book-arity-checked-length-active-body
               yes-shape p running given goal count test-proof formula bindings natural sequence))
         (no-shape (proof-proof-assume proof test nil))
         (no (h4-book-arity-checked-length-active-body
              no-shape p running given goal count test-proof formula bindings natural sequence)))
      (h4-tactics-tactics-case-of p goal test yes no))))

(defun h4-book-arity-checked-length (p formula call)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((call (proof-list-of-length call 4))
         (guard (proof-term-at formula 1))
         (assumed (proof-proof-assume proof guard t))
         (conditions (h4-tactics-tactics-conjunct p assumed))
         (goal (proof-term-at formula 2)))
      (let* ((count (cadr call))
             (flags (caddr call))
             (sequence (cadddr call))
             (test (list *h4-book-arithmetic-zp* count))
             (bindings (list (list count (h4-book-arithmetic-predecessor count))
                             (list flags (list *library-cdr* flags))
                             (list sequence (list *library-cdr* sequence)))))
        (proof-with-checked-results
            ((opened (proof-proof-unfold proof call))
             (stopped (proof-proof-assume proof test t))
             (yes (h4-book-arity-checked-length-stopped
                   stopped p count (cadr conditions) (car conditions) opened sequence goal))
             (active (proof-proof-assume proof test nil))
             (no (h4-book-arity-checked-length-active
                  active p opened (car conditions) goal count formula bindings (cadr conditions) sequence))
             (step (h4-tactics-tactics-case-of p goal test yes no))
             (ordinal (library-library-builtin p 1 count))
             (case-proof (h4-tactics-tactics-imply p formula step)))
          (proof-proof-induct proof ordinal case-proof formula
                              (list *library-count* count) (list bindings)))))))

(defun h4-book-arity-lambda-formals-finish (tail-shape p term shape tail)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((value (h4-book-order-order-view p term (list shape tail-shape) nil))
         (literal (proof-step-first tail-shape)))
      (if (proof-is-call literal *proof-consp*)
          value
        (proof-with-checked-results
            ((completion (library-library-axiom p "COMPLETION-OF-CAR" (list tail)))
             (body (h4-book-arity-step-at completion '(2)))
             (selected (proof-proof-select proof body tail-shape))
             (missing (proof-proof-chain proof completion (list selected)))
             (reverse (proof-proof-symmetric proof missing)))
          (proof-proof-chain proof value (list reverse)))))))

(defun h4-book-arity-lambda-formals (p function shape)
  (let* ((term (list *h4-book-arity-formals* function))
         (tail (list *library-cdr* function))
         (goal (proof-eq term (list *library-car* tail)))
         (test (list *proof-consp* tail))
         (proof (library-library-proof p)))
    (proof-with-checked-results
        ((yes-shape (proof-proof-assume proof test t))
         (yes (h4-book-arity-lambda-formals-finish yes-shape p term shape tail))
         (no-shape (proof-proof-assume proof test nil))
         (no (h4-book-arity-lambda-formals-finish no-shape p term shape tail)))
      (h4-tactics-tactics-case-of p goal test yes no))))

(defun h4-book-arity-application-not-consp (p function symbol)
  (let ((proof (library-library-proof p))
        (pair (list *proof-consp* function)))
    (proof-with-checked-results
        ((fact (proof-proof-fact proof "consp-not-symbolp" (list (list *library-x* function))))
         (assuming-pair (proof-proof-assume proof pair t))
         (no-symbol (h4-tactics-tactics-modus-ponens p fact assuming-pair))
         (conflict (proof-proof-cut proof symbol no-symbol)))
      (proof-proof-front proof conflict (proof-neg pair)))))

(defun h4-book-arity-lambda-application-arity (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((application (h4-book-arity-at formula '(2 1)))
         (arguments (proof-list-of-length (cdr application) 2))
         (guard (proof-term-at formula 1))
         (shape (proof-proof-assume proof guard t))
         (formals (h4-book-arity-lambda-formals p (car arguments) shape))
         (formals-term (h4-book-arity-step-at formals '(2)))
         (take-law (proof-proof-fact
                    proof (proof-sym "PAIRLIS$-TAKES-ARITY-ARGS" "ACL2")
                    (list (list *library-x* formals-term) (list *library-y* (cadr arguments)))))
         (goal (proof-term-at formula 2))
         (result (h4-tactics-tactics-establish p goal nil (list *h4-book-arity-apply-lambda*)
                                              (list formals take-law) nil)))
      (h4-tactics-tactics-imply p formula result))))

(defun h4-book-arity-lambda-application-one (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((guard (proof-term-at formula 1))
         (assuming (proof-proof-assume proof guard t))
         (parts (h4-tactics-tactics-conjunct p assuming))
         (application (h4-book-arity-at formula '(2 2)))
         (arguments (proof-list-of-length (cdr application) 2))
         (formals (h4-book-arity-lambda-formals p (car arguments) (car parts)))
         (length (proof-proof-rewrite proof (cadr parts) formals '(1 1 1)))
         (rule (proof-proof-fact proof (proof-sym "APPLY$-LAMBDA-ARITY-1" "ACL2")
                                (list (list (proof-sym "FN" "ACL2") (car arguments))
                                      (list (proof-sym "ARGS" "ACL2") (cadr arguments)))))
         (evidence (h4-book-division-conjunction p (list (car parts) length)))
         (instance (h4-tactics-tactics-modus-ponens p rule evidence))
         (goal (proof-term-at formula 2))
         (reduced (h4-tactics-tactics-normalize p goal (list (car parts))
                                                (list *h4-book-arity-apply*) nil nil))
         (result (proof-proof-transport proof instance reduced)))
      (h4-tactics-tactics-imply p formula result))))

(defun h4-book-arity-lambda-application-primitive (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((guard (proof-term-at formula 1))
         (primitive (proof-proof-assume proof guard t))
         (function (h4-book-arity-step-at primitive '(1)))
         (rule (proof-proof-fact proof (proof-sym "APPLY$-PRIMP-IMPLIES-SYMBOLP" "ACL2")
                                (list (list (proof-sym "FN" "ACL2") function))))
         (symbol (h4-tactics-tactics-modus-ponens p rule primitive))
         (no-pair (h4-book-arity-application-not-consp p function symbol))
         (goal (proof-term-at formula 2))
         (result (h4-tactics-tactics-establish p goal (list primitive no-pair)
                                              (list *h4-book-arity-apply*) nil nil)))
      (h4-tactics-tactics-imply p formula result))))

(defun h4-book-arity-lambda-application (p mode formula)
  (cond
   ((equal mode "beta")
    (proof-with-checked-results ((provider (h4-book-finite-reduction-provider p)))
      (h4-tactics-tactics-establish
       p formula nil
       (append *h4-book-flatten-logic*
               (list *h4-book-arity-apply* *h4-book-arity-apply-lambda* *h4-book-arity-formals*
                     *h4-book-arity-body* (proof-cl "NULL"))) nil provider)))
   ((equal mode "lambda constructor")
    (proof-with-checked-results ((provider (h4-book-finite-reduction-provider p)))
      (h4-tactics-tactics-establish
       p formula nil (append *h4-book-flatten-logic*
                             (list *h4-book-arity-lamb* *h4-book-updates-true-list*)) nil provider)))
   ((equal mode "lambda arity") (h4-book-arity-lambda-application-arity p formula))
   ((equal mode "one lambda argument") (h4-book-arity-lambda-application-one p formula))
   ((equal mode "primitive application") (h4-book-arity-lambda-application-primitive p formula))))

(defun h4-book-arity-badge-properties-universal (sign p goal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((selected (proof-proof-select proof goal sign)))
      (proof-proof-transport proof sign selected))))

(defun h4-book-arity-badge-properties-list-flags (sign p flags goal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((fields (proof-proof-prove-if proof flags sign))
         (typed (h4-tactics-tactics-conjunct p fields))
         (length (h4-tactics-tactics-conjunct p (cadr typed)))
         (both (h4-book-division-conjunction p (list (car typed) (car length))))
         (selected (proof-proof-select proof goal sign)))
      (proof-proof-transport proof both selected))))

(defun h4-book-arity-badge-properties (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((guard (proof-term-at formula 1))
         (given (proof-proof-assume proof guard t))
         (literal (proof-step-first given))
         (opened (proof-proof-unfold proof literal))
         (definition (proof-proof-rewrite proof given opened '(1)))
         (outer (h4-tactics-tactics-conjunct p definition))
         (weak (proof-step-first (car outer)))
         (weak-opened (proof-proof-unfold proof weak))
         (weak-fields (proof-proof-rewrite proof (car outer) weak-opened '(1)))
         (exists (h4-tactics-tactics-conjunct p weak-fields))
         (fields (h4-tactics-tactics-conjunct p (cadr outer)))
         (rest (h4-tactics-tactics-conjunct p (cadr fields)))
         (goal (h4-book-arity-at formula '(2 2 2 2)))
         (test (h4-book-arity-step-at (cadr rest) '(1)))
         (yes-sign (proof-proof-assume proof test t))
         (yes (h4-book-arity-badge-properties-universal yes-sign p goal))
         (no-sign (proof-proof-assume proof test nil))
         (no (h4-book-arity-badge-properties-list-flags no-sign p (cadr rest) goal))
         (enough (h4-tactics-tactics-case-of p goal test yes no))
         (result (h4-book-division-conjunction
                  p (list (car exists) (car fields) (car rest) enough))))
      (h4-tactics-tactics-imply p formula result))))

(defun h4-book-arity-length-type-branch (shape p term)
  (proof-with-checked-results
      ((opened (h4-book-order-order-view p term (list shape) nil))
       (value (h4-book-arity-step-at opened '(2)))
       (natural (library-library-natural p value)))
    (library-library-transport-argument p natural opened 1)))

(defun h4-book-arity-length-type (p term)
  (let ((proof (library-library-proof p))
        (goal (list *library-natp* term)))
    (proof-with-checked-results ((argument (proof-term-at term 1)))
      (let ((test (list (proof-cl "STRINGP") argument)))
        (proof-with-checked-results
            ((yes-shape (proof-proof-assume proof test t))
             (yes (h4-book-arity-length-type-branch yes-shape p term))
             (no-shape (proof-proof-assume proof test nil))
             (no (h4-book-arity-length-type-branch no-shape p term)))
          (h4-tactics-tactics-case-of p goal test yes no))))))

(defun h4-book-arity-signed-assumptions (proof tests)
  (if (endp tests)
      nil
    (proof-with-checked-results
        ((step (proof-proof-assume proof (caar tests) (cadar tests)))
         (remaining (h4-book-arity-signed-assumptions proof (cdr tests))))
      (cons step remaining))))

(defun h4-book-arity-available (proof tests evidence)
  (if (endp tests)
      evidence
    (let* ((test (caar tests))
           (holds (cadar tests))
           (literal (if holds test (proof-neg test))))
      (proof-with-checked-results ((step (proof-proof-assume proof test holds)))
        (h4-book-arity-available proof (cdr tests) (table-put evidence literal step))))))

(defun h4-book-arity-available-step (evidence literal)
  (let ((entry (assoc-equal literal evidence)))
    (if entry
        (cdr entry)
      '(:failure "failure" ""))))

(defun h4-book-arity-tame-list-argument-natural (p count term badge available)
  (let ((proof (library-library-proof p))
        (null-symbol (proof-cl "NULL")))
    (if (proof-is-call count (proof-cl "LENGTH"))
        (h4-book-arity-length-type p count)
      (proof-with-checked-results
          ((checked (proof-proof-fact proof (proof-sym "BADGE-TYPE" "ACL2")
                                     (list (list (proof-sym "FN" "ACL2") (list *library-car* term)))))
           (exists (h4-book-arity-available-step available (proof-neg (list null-symbol badge))))
           (present (proof-proof-prove-if proof checked exists))
           (properties (proof-proof-fact proof (proof-sym "APPLY$-BADGEP-PROPERTIES" "ACL2")
                                        (list (list *library-x* badge))))
           (instance (h4-tactics-tactics-modus-ponens p properties present))
           (types (h4-book-list-types-conjunct-proofs p instance))
           (typed (proof-term-at types 1)))
        (h4-tactics-tactics-establish p (list *library-natp* count) (list typed) nil nil nil)))))

(defun h4-book-arity-tame-list-step (p value tail target pair term badge given available)
  (let ((proof (library-library-proof p))
        (null-symbol (proof-cl "NULL"))
        (eq-symbol (proof-cl "EQ")))
    (cond
     ((equal value (list null-symbol (list *library-cdr* tail)))
      (proof-with-checked-results
          ((normalized (h4-tactics-tactics-normalize p value nil (list null-symbol eq-symbol) nil nil))
           (end (proof-proof-rewrite proof given normalized '(1)))
           (shape (h4-book-arity-available-step available (list *proof-consp* tail))))
        (h4-tactics-tactics-establish p target (list pair shape)
                                    (list *h4-book-updates-true-list* eq-symbol) (list end) nil)))
     ((not (proof-is-call value *h4-book-arity-tame-arguments*)) '(:failure "failure" ""))
     (t (proof-with-checked-results ((arguments (proof-term-at value 3)))
          (if (not (equal arguments tail))
              '(:failure "failure" "")
            (proof-with-checked-results
                ((parts (proof-list-of-length (cdr value) 3))
                 (natural (h4-book-arity-tame-list-argument-natural
                           p (car parts) term badge available))
                 (rule (proof-proof-fact
                        proof (proof-sym "SUITABLY-TAMEP-LISTP-IMPLICANT-1" "ACL2")
                        (seq-zip (list (proof-sym "N" "ACL2") (proof-sym "FLAGS" "ACL2")
                                      (proof-sym "ARGS" "ACL2")) parts)))
                 (evidence (h4-book-division-conjunction p (list given natural)))
                 (child (h4-tactics-tactics-modus-ponens p rule evidence))
                 (tail-type (h4-tactics-tactics-conjunct p child))
                 (opened (h4-book-order-order-view p target (list pair) nil)))
              (proof-proof-transport proof (car tail-type) opened))))))))

(defun h4-book-arity-tame-list-type-leaf (value tests p target pair term tail badge)
  (let ((implication (list *library-implies* value target))
        (proof (library-library-proof p)))
    (if (equal value *proof-false*)
        (h4-tactics-tactics-establish p implication nil (list *library-implies*) nil nil)
      (proof-with-checked-results
          ((given (proof-proof-assume proof value t))
           (available (h4-book-arity-available proof tests nil))
           (proper (h4-book-arity-tame-list-step p value tail target pair term badge given available)))
        (h4-tactics-tactics-imply p implication proper)))))

(defun h4-book-arity-badge-type-leaf-missing (sign p goal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((selected (proof-proof-select proof goal sign)))
      (proof-proof-transport proof sign selected))))

(defun h4-book-arity-primitive-badge-type (p function)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((primitive (proof-proof-assume proof (list *h4-book-arity-primitivep* function) t))
         (rule (proof-proof-fact proof (proof-sym "BADGE-PRIM-TYPE" "ACL2")
                                (list (list (proof-sym "FN" "ACL2") function))))
         (proved (h4-tactics-tactics-modus-ponens p rule primitive))
         (typed (h4-tactics-tactics-conjunct p proved)))
      (car typed))))

(defun h4-book-arity-user-badge-type (p function value absent sign)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((absent-spec (h4-tactics-tactics-normalize p absent nil
                                                   (list (proof-cl "NULL") (proof-cl "EQ")) nil nil))
         (nil-or-true (proof-proof-nil-or-true proof value))
         (condition (proof-proof-rewrite proof sign absent-spec '(1 1)))
         (nonempty (proof-proof-cut proof nil-or-true condition))
         (rule (proof-proof-fact proof (proof-sym "BADGE-USERFN-TYPE" "ACL2")
                                (list (list (proof-sym "FN" "ACL2") function)))))
      (h4-tactics-tactics-modus-ponens p rule nonempty))))

(defun h4-book-arity-badge-type-leaf-present (sign p value function absent goal)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((typed (cond ((proof-is-call value *h4-book-arity-primitive-badge*)
                       (h4-book-arity-primitive-badge-type p function))
                      ((proof-is-call value *h4-book-arity-user-badge*)
                       (h4-book-arity-user-badge-type p function value absent sign))
                      (t '(:failure "failure" ""))))
         (selected (proof-proof-select proof goal sign)))
      (proof-proof-transport proof typed selected))))

(defun h4-book-arity-badge-type-leaf (value unused-tests p template definitions function)
  (declare (ignore unused-tests))
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((goal (proof-subst template (list (cons *proof-result* value)))))
      (if (proof-is-call value *proof-quote*)
          (h4-tactics-tactics-establish
           p goal nil
           (append *h4-book-flatten-logic* definitions
                   (list (proof-cl "NULL") *h4-book-arity-checked-badge*
                         *h4-book-updates-true-list* *library-natp* *library-len*)) nil nil)
        (proof-with-checked-results
            ((absent (proof-term-at goal 1))
             (yes-sign (proof-proof-assume proof absent t))
             (yes (h4-book-arity-badge-type-leaf-missing yes-sign p goal))
             (no-sign (proof-proof-assume proof absent nil))
             (no (h4-book-arity-badge-type-leaf-present no-sign p value function absent goal)))
          (h4-tactics-tactics-case-of p goal absent yes no))))))

(defun h4-book-arity-symbol-arity-quoted (p requested goal no-pair signs)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((literal (proof-step-first requested))
         (arithmetic (h4-tactics-tactics-normalize p literal nil nil nil nil))
         (value (h4-book-arity-step-at arithmetic '(2))))
      (if (equal value *proof-false*)
          (proof-with-checked-results ((contradiction (proof-proof-rewrite proof requested arithmetic '(1))))
            (proof-proof-subsume proof contradiction
                                 (cons goal (cdr (proof-step-clause contradiction)))))
        (proof-with-checked-results ((provide (h4-book-finite-reduction-provider p)))
          (h4-tactics-tactics-establish p goal (cons no-pair signs)
                                       (list *h4-book-arity-apply*) nil provide))))))

(defun h4-book-arity-symbol-arity-leaf (value tests p badge length goal no-pair function args)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((signs (h4-book-arity-signed-assumptions proof tests))
         (literal (proof-step-first badge))
         (badge-value (h4-tactics-tactics-normalize p literal signs (list *h4-book-arity-badge*) nil nil))
         (requested (proof-proof-rewrite proof length badge-value '(1 1 1 1))))
      (if (proof-is-call value *proof-quote*)
          (h4-book-arity-symbol-arity-quoted p requested goal no-pair signs)
        (proof-with-checked-results
            ((choice (cond ((proof-is-call value *h4-book-arity-primitive-badge*)
                            (proof-with-checked-results
                                ((test (proof-proof-assume proof (list *h4-book-arity-primitivep* function) t)))
                              (cons "APPLY$-PRIM-ARITY-1" test)))
                           ((proof-is-call value *h4-book-arity-user-badge*)
                            (proof-with-checked-results ((test (proof-proof-rewrite proof badge badge-value '(1))))
                              (cons "APPLY$-USERFN-ARITY-1" test)))
                           (t '(:failure "failure" ""))))
             (rule (proof-proof-fact proof (proof-sym (car choice) "ACL2")
                                    (list (list (proof-sym "FN" "ACL2") function)
                                          (list (proof-sym "ARGS" "ACL2") args))))
             (evidence (h4-book-division-conjunction p (list (cdr choice) requested)))
             (applied (h4-tactics-tactics-modus-ponens p rule evidence))
             (normalized (h4-tactics-tactics-normalize p goal (cons no-pair signs)
                                                       (list *h4-book-arity-apply*) nil nil)))
          (proof-proof-transport proof applied normalized))))))

(defun h4-book-arity-value-leaf (p value template tests method context)
  (case method
    (:tame-list
     (h4-book-arity-tame-list-type-leaf value tests p (car context) (cadr context) (caddr context)
                                       (cadddr context) (nth 4 context)))
    (:badge-type
     (h4-book-arity-badge-type-leaf value tests p template (car context) (cadr context)))
    (:symbol-arity
     (h4-book-arity-symbol-arity-leaf value tests p (car context) (cadr context) template
                                    (caddr context) (cadddr context) (nth 4 context)))))

(defun h4-book-arity-by-value-form (p value)
  (cond
   ((proof-is-call value *proof-if*)
    (proof-with-checked-results ((branches (proof-list-of-length (cdr value) 3)))
      (cons :if branches)))
   ((null value) '(:failure "failure" ""))
   ((and (proof-compound value) (proof-compound (car value)))
    (proof-with-checked-results
        ((equality (proof-proof-beta (library-library-proof p) value))
         (body (h4-book-arity-step-at equality '(2))))
      (list :lambda equality body)))
   (t '(:leaf))))

(defun h4-book-arity-by-value-visit (n p value template tests method context form)
  (declare (xargs :measure (nfix n)))
  (let ((proof (library-library-proof p)))
    (cond
     ((zp n) '(:failure "Fuel" "h4-book-arity-by-value-visit"))
     ((failure-p form) form)
     ((eq (car form) :if)
      (let ((test (cadr form)) (yes-value (caddr form)) (no-value (cadddr form)))
        (proof-with-checked-results
            ((yes (h4-book-arity-by-value-visit
                   (1- n) p yes-value template (append tests (list (list test t))) method context
                   (and (< 1 n) (h4-book-arity-by-value-form p yes-value))))
             (no (h4-book-arity-by-value-visit
                  (1- n) p no-value template (append tests (list (list test nil))) method context
                  (and (< 1 n) (h4-book-arity-by-value-form p no-value))))
             (true-selection (proof-proof-if-true proof value))
             (true-reverse (proof-proof-symmetric proof true-selection))
             (yes (proof-proof-rewrite-result proof yes true-reverse template *proof-result*))
             (false-selection (proof-proof-if-false proof value))
             (false-reverse (proof-proof-symmetric proof false-selection))
             (no (proof-proof-rewrite-result proof no false-reverse template *proof-result*)))
          (proof-proof-cases proof test yes no))))
     ((eq (car form) :lambda)
      (let ((body (caddr form)))
        (proof-with-checked-results
            ((opened (h4-book-arity-by-value-visit
                      (1- n) p body template tests method context
                      (and (< 1 n) (h4-book-arity-by-value-form p body))))
             (reverse (proof-proof-symmetric proof (cadr form))))
          (proof-proof-rewrite-result proof opened reverse template *proof-result*))))
     (t (proof-with-checked-results
            ((step (h4-book-arity-value-leaf p value template tests method context))
             (literal (proof-step-first step))
             (goal (proof-subst template (list (cons *proof-result* value)))))
          (if (equal literal goal) step '(:failure "failure" "")))))))

(defun h4-book-arity-by-value (p value template tests method context)
  (h4-book-arity-by-value-visit 1000000 p value template tests method context
                                (h4-book-arity-by-value-form p value)))

(defun h4-book-arity-tame-list-type (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((guard (proof-term-at formula 1))
         (given (proof-proof-assume proof guard t))
         (parts (h4-tactics-tactics-conjunct p given))
         (tame (proof-step-first (car parts)))
         (term (proof-term-at tame 1))
         (target (proof-term-at formula 2)))
      (let ((tail (list *library-cdr* term))
            (badge (list *h4-book-arity-badge* (list *library-car* term)))
            (result-form (list *library-implies* *proof-result* target)))
        (proof-with-checked-results
            ((non-atom (h4-tactics-tactics-establish p (proof-neg (list (proof-cl "ATOM") term))
                                                     (list (cadr parts)) *h4-book-flatten-logic* nil nil))
             (opened (proof-proof-unfold proof tame))
             (body (h4-book-arity-step-at opened '(2)))
             (selected (proof-proof-select proof body non-atom))
             (opened (proof-proof-chain proof opened (list selected)))
             (value (h4-book-arity-step-at opened '(2)))
             (conditional (h4-book-arity-by-value p value result-form nil :tame-list
                                                   (list target (cadr parts) term tail badge)))
             (reverse (proof-proof-symmetric proof opened))
             (original (proof-proof-rewrite proof conditional reverse '(1 1)))
             (result (h4-tactics-tactics-modus-ponens p original (car parts))))
          (h4-tactics-tactics-imply p formula result))))))

(defun h4-book-arity-badge-type (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 4))
         (badge (proof-term-at (cadr parts) 1))
         (function (proof-term-at badge 1))
         (opened (proof-proof-unfold proof badge)))
      (let* ((absent (list (proof-cl "NULL") *proof-result*))
             (template (proof-ite absent absent (list *h4-book-arity-checked-badge* *proof-result*)))
             (definitions (list (proof-sym "WEAK-APPLY$-BADGE-P" "ACL2")
                                (proof-sym "ALL-NILS" "ACL2")
                                (proof-sym "SUBSETP-EQUAL" "ACL2")
                                (proof-sym "MEMBER-EQUAL" "ACL2"))))
        (proof-with-checked-results
            ((body (h4-book-arity-step-at opened '(2)))
             (result (h4-book-arity-by-value p body template nil :badge-type
                                              (list definitions function)))
             (reverse (proof-proof-symmetric proof opened)))
          (proof-proof-rewrite-result proof result reverse template *proof-result*))))))

(defun h4-book-arity-symbol-arity (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((guard (proof-term-at formula 1))
         (given (proof-proof-assume proof guard t))
         (parts (h4-book-list-types-conjunct-proofs p given))
         (parts (proof-list-of-length parts 3))
         (function (h4-book-arity-step-at (car parts) '(1)))
         (args (h4-book-arity-at formula '(2 2 2)))
         (goal (proof-term-at formula 2))
         (no-pair (h4-book-arity-application-not-consp p function (car parts)))
         (badge (proof-step-first (cadr parts)))
         (opened (proof-proof-unfold proof badge))
         (value (h4-book-arity-step-at opened '(2)))
         (cases (h4-book-arity-by-value p value goal nil :symbol-arity
                                         (list (cadr parts) (caddr parts) no-pair function args))))
      (h4-tactics-tactics-imply p formula cases))))

(defun h4-book-arity-beta-part-p (part)
  (and (proof-is-call part *proof-equal*)
       (proof-with-checked-results ((left (proof-term-at part 1)))
         (and (proof-is-call left *h4-book-arity-apply*)
              (proof-with-checked-results ((function (proof-term-at left 1)))
                (and (proof-is-call function *proof-cons*)
                     (proof-with-checked-results ((head (proof-term-at function 1)))
                       (and (equal head (proof-quote (proof-cl "LAMBDA")))
                            (proof-with-checked-results ((right (proof-term-at part 2)))
                              (proof-is-call right (proof-sym "EV$" "ACL2")))))))))))

(defun h4-book-arity-false-branch-mode (test yes)
  (proof-with-checked-results
      ((constructor (and (proof-is-call test *proof-consp*)
                         (proof-with-checked-results ((argument (proof-term-at test 1)))
                           (and (proof-is-call argument *h4-book-arity-lamb*)
                                (equal yes (list *h4-book-updates-true-list* argument)))))))
    (if constructor
        "lambda constructor"
      (proof-with-checked-results ((first (h4-book-arity-beta-part-p test)))
        (and first
             (proof-with-checked-results ((second (h4-book-arity-beta-part-p yes)))
               (and second "beta")))))))

(defun h4-book-arity-if-mode (formula)
  (proof-with-checked-results ((no (proof-term-at formula 3)))
    (let ((test (cadr formula)) (yes (caddr formula)))
      (proof-with-checked-results
          ((mode (and (equal no *proof-false*) (h4-book-arity-false-branch-mode test yes))))
        (or mode
            (and (proof-is-call test (proof-cl "NULL"))
                 (proof-with-checked-results ((argument (proof-term-at test 1)))
                   (and (proof-is-call argument *h4-book-arity-badge*)
                        (equal yes test)
                        (equal no (list *h4-book-arity-checked-badge* argument))
                        "badge type"))))))))

(defun h4-book-arity-apply-mode (guard left right)
  (proof-with-checked-results ((arguments (proof-list-of-length (cdr left) 2)))
    (let ((function (car arguments)) (actuals (cadr arguments)))
      (cond
       ((and (equal right (list *h4-book-arity-primitive* function actuals))
             (equal guard (list *h4-book-arity-primitivep* function)))
        "primitive application")
       ((proof-is-call right *h4-book-arity-apply*)
        (proof-with-checked-results ((other (proof-term-at right 1)))
          (and (equal other function)
               (proof-with-checked-results ((args (proof-term-at right 2)))
                 (and (equal actuals (list *proof-cons* (list *library-car* args) *proof-false*))
                      (let ((formals (list *library-len* (list *h4-book-arity-formals* function)))
                            (badge (list *h4-book-arity-badge* function)))
                        (cond
                         ((equal guard (proof-ite (list *proof-consp* function)
                                                  (proof-eq formals *proof-one*) *proof-false*))
                          "one lambda argument")
                         ((equal guard
                                 (proof-ite
                                  (list (proof-cl "SYMBOLP") function)
                                  (proof-ite badge
                                             (proof-eq (list *library-car* (list *library-cdr* badge))
                                                       *proof-one*) *proof-false*) *proof-false*))
                          "one symbol argument"))))))))))))

(defun h4-book-arity-equality-mode (guard goal)
  (and (proof-is-call goal *proof-equal*)
       (proof-with-checked-results ((sides (proof-list-of-length (cdr goal) 2)))
         (let ((left (car sides)) (right (cadr sides)))
           (cond
            ((proof-is-call left *h4-book-arity-apply-lambda*)
             (proof-with-checked-results ((arguments (proof-list-of-length (cdr left) 2)))
               (let* ((function (car arguments))
                      (length (list *library-len* (list *library-car* (list *library-cdr* function))))
                      (expected (list *h4-book-arity-take* length (cadr arguments))))
                 (and (equal right (list *h4-book-arity-apply-lambda* function expected))
                      (equal guard (list *proof-consp* function))
                      "lambda arity"))))
            ((proof-is-call left *h4-book-arity-apply*)
             (h4-book-arity-apply-mode guard left right)))))))

(defun h4-book-arity-badge-fields-mode (guard goal)
  (and (proof-is-call guard *h4-book-arity-checked-badge*)
       (proof-is-call goal *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at goal 1))
            (badge (proof-term-at guard 1)))
         (and (equal test (list *proof-consp* badge)) "badge fields"))))

(defun h4-book-arity-tame-mode (guard goal)
  (and (proof-is-call guard *proof-if*)
       (proof-with-checked-results ((test (proof-term-at guard 1)))
         (and (proof-is-call test (proof-sym "TAMEP" "ACL2"))
              (proof-with-checked-results ((argument (proof-term-at test 1)))
                (and (equal (cddr guard) (list (list *proof-consp* argument) *proof-false*))
                     (equal goal (list *h4-book-updates-true-list* argument))
                     "tame list"))))))

(defun h4-book-arity-implication-mode (formula)
  (proof-with-checked-results ((parts (proof-list-of-length (cdr formula) 2)))
    (let ((guard (car parts)) (goal (cadr parts)))
      (proof-with-checked-results ((badge (h4-book-arity-badge-fields-mode guard goal)))
        (or badge
            (proof-with-checked-results ((tame (h4-book-arity-tame-mode guard goal)))
              (or tame (h4-book-arity-equality-mode guard goal))))))))

(defun h4-book-arity-arity-mode (formula)
  (cond ((proof-is-call formula *proof-if*) (h4-book-arity-if-mode formula))
        ((proof-is-call formula *library-implies*) (h4-book-arity-implication-mode formula))))

(defun h4-book-arity-prove-mode (p formula)
  (proof-with-checked-results ((mode (h4-book-arity-arity-mode formula)))
    (cond ((equal mode "badge fields") (h4-book-arity-badge-properties p formula))
          ((equal mode "tame list") (h4-book-arity-tame-list-type p formula))
          ((equal mode "badge type") (h4-book-arity-badge-type p formula))
          ((equal mode "one symbol argument") (h4-book-arity-symbol-arity p formula))
          (t (h4-book-arity-lambda-application p mode formula)))))

(defun h4-book-arity-arity-proof (p formula)
  (proof-with-checked-results ((length (h4-book-arity-length-test formula)))
    (if length
        (h4-book-arity-length-equals p (car length) (cadr length))
      (proof-with-checked-results ((prefix (h4-book-arity-prefix-shape formula)))
        (if prefix
            (h4-book-arity-fixed-prefix p formula (car prefix) (cadr prefix))
          (proof-with-checked-results ((match (h4-book-arity-checked-length-shape formula)))
            (if match
                (let ((result (h4-book-arity-checked-length p formula match)))
                  (if (and (failure-p result)
                           (member-equal (cadr result)
                                         '("InapplicableStep" "InapplicableTerm" "MissingProofInput"
                                           "assertion" "key" "value" "Unproved")))
                      (h4-book-arity-prove-mode p formula)
                    result))
              (h4-book-arity-prove-mode p formula))))))))
