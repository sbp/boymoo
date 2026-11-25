(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *t2-evaluator-eval* (proof-sym "SELF-INTP-EVALUATE" "ACL2"))
(defconst *t2-evaluator-eval-list* (proof-sym "SELF-INTP-EVALUATE-LIST" "ACL2"))
(defconst *t2-evaluator-apply* (proof-sym "SELF-INTP-APPLY" "ACL2"))
(defconst *t2-evaluator-operator-constraints* 8)
(defconst *t2-evaluator-symbolp* (proof-cl "SYMBOLP"))
(defconst *t2-evaluator-endp* (proof-cl "ENDP"))
(defconst *t2-evaluator-atom* (proof-cl "ATOM"))
(defconst *t2-evaluator-kwote* (proof-sym "KWOTE" "ACL2"))
(defconst *t2-evaluator-kwote-list* (proof-sym "KWOTE-LST" "ACL2"))
(defconst *t2-evaluator-assoc* (proof-sym "ASSOC-EQUAL" "ACL2"))
(defconst *t2-evaluator-pairlis* (proof-sym "PAIRLIS$" "ACL2"))

(defun t2-evaluator-car (term)
  (list *library-car* term))

(defun t2-evaluator-cdr (term)
  (list *library-cdr* term))

(defun t2-evaluator-range-length (index)
  (cond ((integerp index) (nfix index))
        ((eq index t) 1)
        ((null index) 0)
        (t '(:failure "failure" ""))))

(defun t2-evaluator-nth-steps (index term)
  (declare (xargs :measure (nfix index)))
  (if (zp index)
      (t2-evaluator-car term)
    (t2-evaluator-nth-steps (1- index) (t2-evaluator-cdr term))))

(defun t2-evaluator-nth (index term)
  (proof-with-checked-results ((count (t2-evaluator-range-length index)))
    (t2-evaluator-nth-steps count term)))

(mutual-recursion
 (defun t2-evaluator-rename (term witnesses)
   (declare (xargs :measure (acl2-count term)))
   (cond
    ((or (not (proof-compound term)) (proof-is-call term *proof-quote*)) term)
    ((endp term) '(:failure "recipe-mismatch" ""))
    (t (let* ((operator (car term))
              (renamed (table-get witnesses operator operator)))
         (proof-with-checked-results
             ((renamed (if (proof-compound operator)
                           (proof-with-checked-results
                               ((parts (proof-list-of-length operator 3))
                                (body (t2-evaluator-rename (caddr operator) witnesses)))
                             (list (car parts) (cadr parts) body))
                         renamed))
              (args (t2-evaluator-rename-arguments (cdr term) witnesses)))
           (cons renamed args))))))

 (defun t2-evaluator-rename-arguments (args witnesses)
   (declare (xargs :measure (acl2-count args)))
   (if (endp args)
       nil
     (proof-with-checked-results
         ((arg (t2-evaluator-rename (car args) witnesses))
          (rest (t2-evaluator-rename-arguments (cdr args) witnesses)))
       (cons arg rest)))))

(defun t2-evaluator-operator-arguments (arguments index term environment)
  (if (endp arguments)
      nil
    (cons (list *t2-evaluator-eval* (t2-evaluator-nth-steps index term) environment)
          (t2-evaluator-operator-arguments (cdr arguments) (1+ index) term environment))))

(defun t2-evaluator-operator (formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length (cdr formula) 2))
       (equation (proof-list-of-length (cadr parts) 3)))
    (let ((expression (caddr equation)))
      (cond
       ((integerp expression) '(:failure "failure" ""))
       ((endp expression) '(:failure "recipe-mismatch" ""))
       (t (proof-with-checked-results ((lhs (proof-list-of-length (cadr equation) 3)))
            (let ((test (car parts)) (term (cadr lhs)) (environment (caddr lhs))
                  (operator (car expression)) (arguments (cdr expression)))
              (if (and (equal test (proof-ite (list *proof-consp* term)
                                               (proof-eq (t2-evaluator-car term) (proof-quote operator))
                                               *proof-false*))
                       (equal arguments (t2-evaluator-operator-arguments arguments 1 term environment)))
                  (list operator (len arguments))
                '(:failure "recipe-mismatch" "")))))))))

(defun t2-evaluator-operators (formulas)
  (if (endp formulas)
      nil
    (proof-with-checked-results
        ((operator (t2-evaluator-operator (car formulas)))
         (rest (t2-evaluator-operators (cdr formulas))))
      (cons operator rest))))

(defun t2-evaluator-install-lookup (term environment)
  (proof-ite (list *t2-evaluator-symbolp* term)
             (proof-ite term (t2-evaluator-cdr (list *t2-evaluator-assoc* term environment))
                        *proof-false*)
             *proof-false*))

(defun t2-evaluator-install-args (arity index)
  (declare (xargs :measure (nfix arity)))
  (if (zp arity)
      nil
    (cons (t2-evaluator-nth-steps index *library-y*)
          (t2-evaluator-install-args (1- arity) (1+ index)))))

(defun t2-evaluator-install-dispatch (dispatch)
  (if (endp dispatch)
      *proof-false*
    (proof-with-checked-results
        ((rest (t2-evaluator-install-dispatch (cdr dispatch)))
         (entry (proof-list-of-length (car dispatch) 2))
         (arity (t2-evaluator-range-length (cadr entry))))
      (let ((op (car entry)))
        (proof-ite (proof-eq *library-x* (proof-quote op))
                   (cons op (t2-evaluator-install-args arity 0)) rest)))))

(defun t2-evaluator-install-definitions (dispatch)
  (proof-with-checked-results ((apply (t2-evaluator-install-dispatch dispatch)))
    (let* ((x *library-x*) (y *library-y*)
           (formals (list x y))
           (lambda-body (list *t2-evaluator-eval* (t2-evaluator-nth 2 x)
                              (list *t2-evaluator-pairlis* (t2-evaluator-nth 1 x) y)))
           (apply (proof-ite (list *proof-consp* x) lambda-body
                             (proof-ite (list *t2-evaluator-symbolp* x) apply *proof-false*)))
           (on-call (proof-ite (proof-eq (t2-evaluator-car x) (proof-quote *proof-quote*))
                               (t2-evaluator-nth 1 x)
                               (list *t2-evaluator-apply* (t2-evaluator-car x)
                                     (list *t2-evaluator-eval-list* (t2-evaluator-cdr x) y))))
           (evaluate (proof-ite (list *proof-consp* x) on-call (t2-evaluator-install-lookup x y)))
           (evaluate-list (proof-ite (list *proof-consp* x)
                                     (list *proof-cons* (list *t2-evaluator-eval* (t2-evaluator-car x) y)
                                           (list *t2-evaluator-eval-list* (t2-evaluator-cdr x) y))
                                     *proof-false*)))
      (list (list *t2-evaluator-eval* formals evaluate)
            (list *t2-evaluator-eval-list* formals evaluate-list)
            (list *t2-evaluator-apply* formals apply)))))

(defun t2-evaluator-install-measures (definitions)
  (if (endp definitions)
      nil
    (acons (caar definitions) (list *library-count* *library-x*)
           (t2-evaluator-install-measures (cdr definitions)))))

(defun t2-evaluator-install (generator dispatch)
  (let ((rulers (list *proof-if*)))
    (proof-with-checked-results
        ((definitions (t2-evaluator-install-definitions dispatch))
         (measures (t2-evaluator-install-measures definitions))
         (result (t2-tactics-generator-prove-definition generator rulers definitions measures))
         (entry (car result))
         (data (cons rulers definitions))
         (generator (t2-tactics-generator-admit-given (cdr result) "define" data))
         (lib (t2-tactics-generator-lib generator))
         (source (proof-line "define" data)))
      (t2-tactics-generator-with-lib
       generator
       (library-library-with-entries
        lib (append (library-library-entries lib)
                    (list (list "define" *t2-evaluator-eval* (caddr entry)
                                (concatenate 'string source (cadddr entry))))))))))

(defun t2-evaluator-select-step (lib equation evidence)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first equation))
         (rhs (proof-term-at literal 2))
         (selected (proof-proof-select proof rhs evidence)))
      (proof-proof-chain proof equation (list selected)))))

(defun t2-evaluator-select (lib equation evidence)
  (declare (xargs :measure (acl2-count evidence)))
  (if (or (endp evidence) (failure-p equation))
      equation
    (t2-evaluator-select lib (t2-evaluator-select-step lib equation (car evidence))
                         (cdr evidence))))

(defun t2-evaluator-cons-truth (lib first rest)
  (proof-proof-fact (library-library-proof lib) "consp-cons"
                    (list (list *library-x* first) (list *library-y* rest))))

(defun t2-evaluator-cons-selectors (lib first rest)
  (proof-with-checked-results
      ((car-step (library-library-axiom lib "CAR-CONS" (list first rest)))
       (cdr-step (library-library-axiom lib "CDR-CONS" (list first rest))))
    (list car-step cdr-step)))

(defun t2-evaluator-false-test (lib equation)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first equation))
         (rhs (proof-term-at literal 2)))
      (if (not (equal rhs *proof-false*))
          '(:failure "recipe-mismatch" "")
        (proof-with-checked-results
            ((not-nil (proof-proof-not-nil proof))
             (reverse (proof-proof-symmetric proof equation))
             (step (proof-proof-rewrite proof not-nil reverse '(1 1))))
          (proof-proof-tidy proof step))))))

(defun t2-evaluator-end-test (lib term)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof (list *t2-evaluator-endp* term)))
         (literal (proof-step-first opened))
         (rhs (proof-term-at literal 2))
         (inner (proof-proof-unfold proof rhs)))
      (proof-proof-chain proof opened (list inner)))))

(defun t2-evaluator-open-cons-premise (lib value concrete)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((end (t2-evaluator-end-test lib value))
         (literal (proof-step-first end))
         (opened (proof-proof-unfold proof (caddr literal)))
         (nonempty (t2-evaluator-select lib opened (list concrete)))
         (chain (proof-proof-chain proof end (list nonempty))))
      (t2-evaluator-false-test lib chain))))

(defun t2-evaluator-open-cons-rewrite (proof equation accessor)
  (proof-with-checked-results
      ((literal (proof-step-first equation))
       (rhs (proof-term-at literal 2))
       (accessor-literal (proof-step-first accessor))
       (slot (proof-term-at accessor-literal 1)))
    (proof-proof-rewrite-result proof equation accessor (proof-eq *proof-false* rhs) slot)))

(defun t2-evaluator-open-cons (lib function first rest environment)
  (let* ((proof (library-library-proof lib))
         (value (list *proof-cons* first rest))
         (term (if (eq environment :none) (list function value) (list function value environment))))
    (proof-with-checked-results
        ((concrete (t2-evaluator-cons-truth lib first rest))
         (equation (proof-proof-unfold proof term))
         (concrete (if (equal function *t2-evaluator-kwote-list*)
                       (t2-evaluator-open-cons-premise lib value concrete)
                     concrete))
         (equation (t2-evaluator-select lib equation (list concrete)))
         (accessors (t2-evaluator-cons-selectors lib first rest))
         (equation (t2-evaluator-open-cons-rewrite proof equation (car accessors))))
      (t2-evaluator-open-cons-rewrite proof equation (cadr accessors)))))

(defun t2-evaluator-eval-nil (lib environment)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((computed (t2-book-logic-constant lib (list *t2-evaluator-symbolp* *proof-false*)))
         (symbolic (proof-proof-true-from-eq proof computed))
         (computed (t2-book-logic-constant lib (list *proof-consp* *proof-false*)))
         (no-cons (t2-evaluator-false-test lib computed))
         (opened (proof-proof-unfold proof (list *t2-evaluator-eval* *proof-false* environment)))
         (not-nil (proof-proof-not-nil proof)))
      (t2-evaluator-select lib opened (list no-cons symbolic not-nil)))))

(defun t2-evaluator-project-atom (lib operator)
  (if (equal operator *library-car*)
      (t2-evaluator-eval-nil lib *library-y*)
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((opened (proof-proof-unfold proof (list *t2-evaluator-eval-list* *proof-false* *library-y*)))
           (computed (t2-book-logic-constant lib (list *proof-consp* *proof-false*)))
           (empty (t2-evaluator-false-test lib computed)))
        (t2-evaluator-select lib opened (list empty))))))

(defun t2-evaluator-projection (lib operator name term branch cons-equation atom-equation)
  (let* ((proof (library-library-proof lib))
         (selector (list operator term))
         (east (list operator *library-x*))
         (operator-name (caddr operator)))
    (proof-with-checked-results
        ((literal (proof-step-first cons-equation))
         (known (library-library-axiom lib (concatenate 'string operator-name "-CONS")
                                      (cdr (caddr literal))))
         (reverse (proof-proof-symmetric proof cons-equation))
         (on-cons (proof-proof-rewrite proof known reverse '(1 1 1)))
         (computed (t2-book-logic-constant lib (list operator *proof-false*)))
         (reverse (proof-proof-symmetric proof atom-equation))
         (on-atom (proof-proof-rewrite proof computed reverse '(1 1 1)))
         (completion (library-library-axiom lib (concatenate 'string "COMPLETION-OF-" operator-name)
                                           (list *library-x*)))
         (absence (proof-proof-assume proof branch nil))
         (empty (t2-evaluator-select lib completion (list absence)))
         (evaluation (t2-evaluator-project-atom lib operator))
         (reverse (proof-proof-symmetric proof empty))
         (evaluation (proof-proof-rewrite proof evaluation reverse '(1 1 1)))
         (reverse (proof-proof-symmetric proof evaluation))
         (on-atom (proof-proof-chain proof on-atom (list reverse)))
         (literal (proof-step-first on-cons))
         (lhs (proof-term-at literal 1)))
      (if (not (equal lhs selector))
          '(:failure "recipe-mismatch" "")
        (proof-with-checked-results
            ((rhs (proof-term-at literal 2))
             (argument (proof-term-at rhs 1)))
          (if (not (equal argument east))
              '(:failure "recipe-mismatch" "")
            (proof-with-checked-results
                ((step (proof-proof-cases proof branch on-cons on-atom))
                 (claim (proof-step-first step)))
              (library-library-lemma lib name claim step nil))))))))

(defun t2-evaluator-list-projections (lib)
  (let ((proof (library-library-proof lib))
        (term (list *t2-evaluator-eval-list* *library-x* *library-y*))
        (branch (list *proof-consp* *library-x*)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof term))
         (present (proof-proof-assume proof branch t))
         (cons-equation (t2-evaluator-select lib opened (list present)))
         (opened (proof-proof-unfold proof term))
         (absent (proof-proof-assume proof branch nil))
         (atom-equation (t2-evaluator-select lib opened (list absent)))
         (lib (t2-evaluator-projection lib *library-car* "EVAL-LIST-CAR" term branch
                                      cons-equation atom-equation)))
      (t2-evaluator-projection lib *library-cdr* "EVAL-LIST-CDR" term branch
                               cons-equation atom-equation))))

(defun t2-evaluator-open-cons-with-tail (lib function tail)
  (case (len tail)
    (0 '(:failure "failure" ""))
    (1 (t2-evaluator-open-cons lib function (car tail) *proof-false* :none))
    (2 (t2-evaluator-open-cons lib function (car tail) (cadr tail) *proof-false*))
    (otherwise
     '(:failure "failure" ""))))

(defun t2-evaluator-quoted-value (lib value)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof (list *t2-evaluator-kwote* value)))
         (literal (proof-step-first opened))
         (rhs (proof-term-at literal 2)))
      (if (not (proof-is-call rhs *termination-return-last*))
          '(:failure "recipe-mismatch" "")
        (proof-with-checked-results
            ((unwrapped (proof-proof-unfold proof rhs))
             (quoted (proof-proof-chain proof opened (list unwrapped)))
             (literal (proof-step-first quoted))
             (form (proof-term-at literal 2))
             (selected (t2-evaluator-open-cons-with-tail lib *t2-evaluator-eval* (cdr form)))
             (is-quote (proof-proof-reflexive proof (proof-quote *proof-quote*)))
             (selected (t2-evaluator-select lib selected (list is-quote)))
             (car-step (library-library-axiom lib "CAR-CONS" (list value *proof-false*)))
             (selected (proof-proof-chain proof selected (list car-step)))
             (reverse (proof-proof-symmetric proof quoted)))
          (proof-proof-rewrite proof selected reverse '(1 1 1)))))))

(defun t2-evaluator-quoted-cons (lib claim branch on-cons)
  (let ((proof (library-library-proof lib)) (x *library-x*))
    (proof-with-checked-results
        ((literal (proof-step-first on-cons))
         (parts (proof-list-of-length (cdr (caddr literal)) 2))
         (first (car parts))
         (rest (cadr parts))
         (quoted (t2-evaluator-open-cons lib *t2-evaluator-kwote-list* first rest :none))
         (reflexive (proof-proof-reflexive proof (cadr claim)))
         (cons-step (proof-proof-rewrite proof reflexive on-cons '(1 2 1 1)))
         (cons-step (proof-proof-rewrite proof cons-step quoted '(1 2 1)))
         (literal (proof-step-first quoted))
         (rhs (proof-term-at literal 2))
         (evaluated (t2-evaluator-open-cons-with-tail lib *t2-evaluator-eval-list* (cdr rhs)))
         (cons-step (proof-proof-chain proof cons-step (list evaluated)))
         (value (t2-evaluator-quoted-value lib first))
         (cons-step (proof-proof-rewrite proof cons-step value '(1 2 1)))
         (builtin (library-library-builtin lib 3 x))
         (assumed (proof-proof-assume proof branch t))
         (smaller (proof-proof-discharge proof builtin assumed))
         (literal (proof-step-first smaller))
         (hypothesis (proof-ite literal
                                (proof-eq (list *t2-evaluator-eval-list*
                                                (list *t2-evaluator-kwote-list* rest) *proof-false*) rest)
                                *proof-true*))
         (assumed (proof-proof-assume proof hypothesis t))
         (reduced (proof-proof-prove-if proof assumed smaller))
         (cons-step (proof-proof-rewrite proof cons-step reduced '(1 2 2)))
         (reverse (proof-proof-symmetric proof on-cons)))
      (proof-proof-chain proof cons-step (list reverse)))))

(defun t2-evaluator-quoted-atom (lib claim on-atom)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((reflexive (proof-proof-reflexive proof (cadr claim)))
         (atom-step (proof-proof-rewrite proof reflexive on-atom '(1 2 1 1)))
         (computed (t2-book-logic-constant lib (list *proof-consp* *proof-false*)))
         (empty (t2-evaluator-false-test lib computed))
         (opened (proof-proof-unfold proof (list *t2-evaluator-kwote-list* *proof-false*)))
         (end (t2-evaluator-end-test lib *proof-false*))
         (absence (proof-proof-transport proof empty end))
         (quote-nil (t2-evaluator-select lib opened (list absence)))
         (atom-step (proof-proof-rewrite proof atom-step quote-nil '(1 2 1)))
         (opened (proof-proof-unfold proof (list *t2-evaluator-eval-list* *proof-false* *proof-false*)))
         (evaluation (t2-evaluator-select lib opened (list empty)))
         (reverse (proof-proof-symmetric proof on-atom)))
      (proof-proof-chain proof atom-step (list evaluation reverse)))))

(defun t2-evaluator-quoted-arguments (lib)
  (let* ((proof (library-library-proof lib)) (x *library-x*)
         (values (list *t2-evaluator-eval-list* x *library-y*))
         (claim (proof-eq (list *t2-evaluator-eval-list* (list *t2-evaluator-kwote-list* values)
                                *proof-false*) values))
         (branch (list *proof-consp* x)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof values))
         (assumed (proof-proof-assume proof branch t))
         (on-cons (t2-evaluator-select lib opened (list assumed)))
         (opened (proof-proof-unfold proof values))
         (assumed (proof-proof-assume proof branch nil))
         (on-atom (t2-evaluator-select lib opened (list assumed)))
         (cons-step (t2-evaluator-quoted-cons lib claim branch on-cons))
         (atom-step (t2-evaluator-quoted-atom lib claim on-atom))
         (ordinal (library-library-builtin lib 1 x))
         (cases (proof-proof-cases proof branch cons-step atom-step))
         (pairs (list (list x (t2-evaluator-cdr x))))
         (step (proof-proof-induct proof ordinal cases claim (list *library-count* x) (list pairs))))
      (library-library-lemma lib "EVAL-QUOTED-ARGUMENTS" claim step nil))))

(defun t2-evaluator-symbolic-premise (lib context test)
  (if (not (proof-is-call test *proof-consp*))
      (cons nil context)
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((term (proof-term-at test 1))
           (symbolic (t2-tactics-ruler-facts-find context (list *t2-evaluator-symbolp* term))))
        (if (not (car symbolic))
            symbolic
          (proof-with-checked-results
              ((incompatible (proof-proof-fact proof "consp-not-symbolp" (list (list *library-x* term))))
               (assumed (proof-proof-assume proof test t))
               (incompatible (t2-arithmetic-arithmetic-modus-ponens lib incompatible assumed))
               (cut (proof-proof-cut proof (car symbolic) incompatible))
               (premise (proof-proof-front proof cut (proof-neg test))))
            (cons premise (cdr symbolic))))))))

(defun t2-evaluator-computed-premise (lib test)
  (proof-with-checked-results ((computed (t2-book-logic-constant lib test)))
    (and computed
         (proof-with-checked-results
             ((literal (proof-step-first computed))
              (value (proof-term-at literal 2)))
           (cond ((equal value *proof-true*)
                  (proof-proof-true-from-eq (library-library-proof lib) computed))
                 ((equal value *proof-false*) (t2-evaluator-false-test lib computed))
                 (t nil))))))

(defun t2-evaluator-path-premise (lib context test)
  (proof-with-checked-results
      ((direct (t2-tactics-ruler-facts-find context test))
       (direct (if (car direct) direct
                 (t2-tactics-ruler-facts-find (cdr direct) (proof-neg test))))
       (direct (if (car direct) direct
                 (t2-evaluator-symbolic-premise lib (cdr direct) test))))
    (if (car direct)
        direct
      (proof-with-checked-results ((computed (t2-evaluator-computed-premise lib test)))
        (cons computed (cdr direct))))))

(defun t2-evaluator-known-path-step (lib equation context)
  (proof-with-checked-results
      ((literal (proof-step-first equation))
       (rhs (proof-term-at literal 2)))
    (if (not (proof-is-call rhs *proof-if*))
        (list* :done equation context)
      (proof-with-checked-results
          ((test (proof-term-at rhs 1))
           (premise (t2-evaluator-path-premise lib context test)))
        (if (not (car premise))
            (list* :done equation (cdr premise))
          (proof-with-checked-results
              ((selected (t2-evaluator-select lib equation (list (car premise)))))
            (list* :visit selected (cdr premise))))))))

(defun t2-evaluator-known-path-loop (n lib path)
  (declare (xargs :measure (nfix n)))
  (cond ((failure-p path) path)
        ((eq (car path) :done) (cdr path))
        ((zp n) '(:failure "fuel" "t2-evaluator-known-path"))
        (t (t2-evaluator-known-path-loop
            (1- n) lib (t2-evaluator-known-path-step lib (cadr path) (cddr path))))))

(defun t2-evaluator-known-path (n lib equation context)
  (t2-evaluator-known-path-loop n lib (list* :visit equation context)))

(defun t2-evaluator-argument-places (distance)
  (declare (xargs :measure (nfix distance)))
  (if (zp distance)
      nil
    (cons 1 (t2-evaluator-argument-places (1- distance)))))

(defun t2-evaluator-argument-tail-step (lib dispatch cursor environment location distance)
  (proof-with-checked-results
      ((tail (library-library-cite lib "EVAL-LIST-CDR" (list cursor environment) nil)))
    (proof-proof-rewrite (library-library-proof lib) dispatch tail
                         (append location (t2-evaluator-argument-places distance)))))

(defun t2-evaluator-argument-tail (lib dispatch cursor environment location distance)
  (declare (xargs :measure (nfix distance)))
  (cond ((failure-p dispatch) dispatch)
        ((zp distance) (cons dispatch cursor))
        (t (t2-evaluator-argument-tail
            lib (t2-evaluator-argument-tail-step lib dispatch cursor environment location distance)
            (t2-evaluator-cdr cursor) environment location (1- distance)))))

(defun t2-evaluator-argument-step (lib dispatch base environment index)
  (let ((location (list 1 2 (1+ index))))
    (proof-with-checked-results
        ((tail (t2-evaluator-argument-tail lib dispatch base environment location index))
         (first (library-library-cite lib "EVAL-LIST-CAR" (list (cdr tail) environment) nil)))
      (proof-proof-rewrite (library-library-proof lib) (car tail) first location))))

(defun t2-evaluator-arguments-loop (lib dispatch base environment index remaining)
  (declare (xargs :measure (nfix remaining)))
  (cond ((failure-p dispatch) dispatch)
        ((zp remaining) (proof-proof-tidy (library-library-proof lib) dispatch))
        (t (t2-evaluator-arguments-loop
            lib (t2-evaluator-argument-step lib dispatch base environment index)
            base environment (1+ index) (1- remaining)))))

(defun t2-evaluator-arguments (lib dispatch base environment arity)
  (proof-with-checked-results ((count (t2-evaluator-range-length arity)))
    (t2-evaluator-arguments-loop lib dispatch base environment 0 count)))

(defun t2-evaluator-nonsymbol (lib context index term)
  (let ((head (t2-evaluator-car term)) (proof (library-library-proof lib)))
    (if (equal index 3)
        (proof-with-checked-results
            ((incompatible (proof-proof-fact proof "consp-not-symbolp" (list (list *library-x* head))))
             (query (t2-tactics-ruler-facts-require context (list *proof-consp* head)))
             (nonsymbol (t2-arithmetic-arithmetic-modus-ponens lib incompatible (car query))))
          (cons nonsymbol (cdr query)))
      (t2-tactics-ruler-facts-require context (proof-neg (list *t2-evaluator-symbolp* head))))))

(defun t2-evaluator-constraint-head (lib context index term rhs quote-test)
  (let ((proof (library-library-proof lib)))
    (cond
     ((or (equal index 3) (equal index 7))
      (proof-with-checked-results
          ((constant (t2-book-logic-constant lib (list *t2-evaluator-symbolp* (proof-quote *proof-quote*))))
           (symbol (proof-proof-true-from-eq proof constant))
           (assumed (proof-proof-assume proof quote-test t))
           (reverse (proof-proof-symmetric proof assumed))
           (bad (proof-proof-rewrite proof symbol reverse '(1 1)))
           (nonsymbol (t2-evaluator-nonsymbol lib context index term))
           (cut (proof-proof-cut proof bad (car nonsymbol)))
           (step (proof-proof-front proof cut (proof-neg quote-test)))
           (context (t2-tactics-ruler-facts-learn (cdr nonsymbol) step)))
        (cons nil context)))
     ((<= *t2-evaluator-operator-constraints* index)
      (proof-with-checked-results
          ((op (proof-term-at rhs 0))
           (head-value (t2-tactics-ruler-facts-require context (proof-eq (t2-evaluator-car term) (proof-quote op))))
           (different (proof-proof-compute proof (proof-eq (proof-quote op) (proof-quote *proof-quote*)) *proof-nil*))
           (not-quote (t2-evaluator-false-test lib different))
           (reverse (proof-proof-symmetric proof (car head-value)))
           (step (proof-proof-rewrite proof not-quote reverse '(1 1 1)))
           (step (proof-proof-tidy proof step))
           (context (t2-tactics-ruler-facts-learn (cdr head-value) step)))
        (cons (car head-value) context)))
     (t (cons nil context)))))

(defun t2-evaluator-constraint-normalize (lib equation context term environment rhs quote-test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((parts (proof-list-of-length rhs 3))
         (other (t2-evaluator-open-cons-with-tail lib *t2-evaluator-eval* (cdr (cadr parts))))
         (premise (t2-tactics-ruler-facts-require context (proof-neg quote-test)))
         (other (t2-evaluator-select lib other (list (car premise))))
         (restored (library-library-cite lib "EVAL-QUOTED-ARGUMENTS"
                                         (list (t2-evaluator-cdr term) environment) nil))
         (other (proof-proof-rewrite proof other restored '(1 2 2)))
         (reverse (proof-proof-symmetric proof other)))
      (proof-proof-chain proof equation (list reverse)))))

(defun t2-evaluator-constraint-apply (lib equation context)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((literal (proof-step-first equation))
         (rhs (proof-term-at literal 2))
         (opened (proof-proof-unfold proof rhs))
         (result (t2-evaluator-known-path 1000000 lib opened context)))
      (proof-proof-chain proof equation (list (car result))))))

(defun t2-evaluator-constraint-operator (lib equation head-value term environment rhs)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((equation (proof-proof-rewrite proof equation head-value '(1 2 1)))
         (op (proof-term-at rhs 0))
         (opened (proof-proof-unfold proof (list *t2-evaluator-apply* (proof-quote op) *library-y*)))
         (context (t2-tactics-ruler-facts-init lib nil nil))
         (dispatch (t2-evaluator-known-path 1000000 lib opened context))
         (literal (proof-step-first equation))
         (right (proof-term-at literal 2))
         (arguments (proof-term-at right 2))
         (dispatch (proof-proof-instantiate proof (car dispatch) (list (list *library-y* arguments))))
         (equation (proof-proof-chain proof equation (list dispatch))))
      (t2-evaluator-arguments lib equation (t2-evaluator-cdr term) environment (1- (len rhs))))))

(defun t2-evaluator-constraint-equation (lib context index term environment lhs rhs quote-test)
  (let ((proof (library-library-proof lib)))
    (proof-with-checked-results
        ((head-result (t2-evaluator-constraint-head lib context index term rhs quote-test))
         (opened (proof-proof-unfold proof lhs))
         (path (t2-evaluator-known-path 1000000 lib opened (cdr head-result))))
      (cond
       ((equal index 0)
        (t2-evaluator-constraint-normalize lib (car path) (cdr path) term environment rhs quote-test))
       ((or (equal index 3) (equal index 7))
        (t2-evaluator-constraint-apply lib (car path) (cdr path)))
       ((<= *t2-evaluator-operator-constraints* index)
        (t2-evaluator-constraint-operator lib (car path) (car head-result) term environment rhs))
       (t (car path))))))

(defun t2-evaluator-constraint (lib formula index)
  (if (not (proof-is-call formula *library-implies*))
      '(:failure "recipe-mismatch" "")
    (proof-with-checked-results
        ((parts (proof-list-of-length (cdr formula) 2))
         (test (car parts))
         (goal (cadr parts))
         (context (t2-tactics-ruler-facts-init lib (list (list test t)) nil))
         (sides (proof-list-of-length (cdr goal) 2))
         (lhs (car sides))
         (lhs-parts (proof-list-of-length lhs 3))
         (term (cadr lhs-parts))
         (environment (caddr lhs-parts))
         (quote-test (proof-eq (t2-evaluator-car term) (proof-quote *proof-quote*)))
         (equation (t2-evaluator-constraint-equation lib context index term environment lhs (cadr sides) quote-test))
         (literal (proof-step-first equation)))
      (if (equal literal goal)
          (t2-power-implication lib test equation)
        '(:failure "recipe-mismatch" "")))))

(defun t2-evaluator-witness-arities (declarations)
  (if (endp declarations)
      t
    (proof-with-checked-results ((declaration (proof-list-of-length (car declarations) 2)))
      (and (equal (cadr declaration) 2)
           (t2-evaluator-witness-arities (cdr declarations))))))

(defun t2-evaluator-witness-formulas (constraints)
  (if (endp constraints)
      nil
    (proof-with-checked-results
        ((constraint (proof-list-of-length (car constraints) 2))
         (rest (t2-evaluator-witness-formulas (cdr constraints))))
      (cons (cadr constraint) rest))))

(defun t2-evaluator-witness-implications (formulas)
  (if (endp formulas)
      t
    (and (proof-is-call (car formulas) *library-implies*)
         (proof-with-checked-results ((claim (proof-term-at (car formulas) 2)))
           (and (proof-is-call claim *proof-equal*)
                (t2-evaluator-witness-implications (cdr formulas)))))))

(defun t2-evaluator-witness-map (names evaluator witnesses)
  (if (endp names)
      witnesses
    (let ((name (car names)))
      (t2-evaluator-witness-map
       (cdr names) evaluator
       (table-put witnesses name (if (equal name evaluator) *t2-evaluator-eval* *t2-evaluator-eval-list*))))))

(defun t2-evaluator-witness-proof (lib formula index)
  (proof-with-checked-results ((step (t2-evaluator-constraint lib formula index)))
    (proof-proof-subsume (library-library-proof lib) step (list formula))))

(defun t2-evaluator-witness-proofs (lib formulas index proofs)
  (declare (xargs :measure (acl2-count formulas)))
  (cond ((failure-p (car proofs)) (car proofs))
        ((endp formulas) (reverse proofs))
        (t (t2-evaluator-witness-proofs
            lib (cdr formulas) (1+ index)
            (cons (t2-evaluator-witness-proof lib (car formulas) index) proofs)))))

(defun t2-evaluator-witness-names (names witnesses)
  (if (endp names)
      nil
    (cons (table-get witnesses (car names) nil)
          (t2-evaluator-witness-names (cdr names) witnesses))))

(defun t2-evaluator-witness-install (generator names formulas witnesses)
  (proof-with-checked-results
      ((formulas (t2-evaluator-rename-arguments formulas witnesses))
       (dispatch (t2-evaluator-operators (nthcdr *t2-evaluator-operator-constraints* formulas)))
       (generator (t2-evaluator-install generator dispatch))
       (lib (t2-tactics-generator-lib generator))
       (lib (t2-evaluator-list-projections lib))
       (lib (t2-evaluator-quoted-arguments lib))
       (proofs (t2-evaluator-witness-proofs lib formulas 0 nil))
       (name (car names))
       (entry (proof-proof-entry "witness" name (cons name (t2-evaluator-witness-names names witnesses)) proofs)))
    (cons entry (t2-tactics-generator-with-lib generator lib))))

(defun t2-evaluator-witness-constraints (generator declarations constraints)
  (if (or (not (proof-compound constraints)) (< (len constraints) *t2-evaluator-operator-constraints*))
      '(:failure "unproved" "")
    (proof-with-checked-results
        ((names (strip-cars declarations))
         (formulas (t2-evaluator-witness-formulas constraints))
         (implications (t2-evaluator-witness-implications formulas)))
      (if (not implications)
          '(:failure "unproved" "")
        (proof-with-checked-results
            ((claim (proof-term-at (car formulas) 2))
             (lhs (proof-term-at claim 1))
             (evaluator (t2-book-logic-head lhs)))
          (if (not (member-equal evaluator names))
              '(:failure "unproved" "")
            (t2-evaluator-witness-install generator names formulas
                                         (t2-evaluator-witness-map names evaluator nil))))))))

(defun t2-evaluator-witness (generator data)
  (proof-with-checked-results ((declarations (proof-term-at data 0)))
    (cond ((integerp declarations) '(:failure "failure" ""))
          ((not (equal (len declarations) 2)) '(:failure "unproved" ""))
          (t (proof-with-checked-results ((arities (t2-evaluator-witness-arities declarations)))
               (if (not arities)
                   '(:failure "unproved" "")
                 (proof-with-checked-results ((constraints (proof-term-at data 1)))
                   (t2-evaluator-witness-constraints generator declarations constraints))))))))
