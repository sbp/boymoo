(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-book-updates-true-list* (proof-sym "TRUE-LISTP" "ACL2"))
(defconst *h4-book-updates-predecessor-natural* (proof-sym "H4-COUNTDOWN-PREDECESSOR" "ACL2"))
(defconst *h4-book-updates-tail-bound* (proof-sym "H4-INDEX-BOUND-ON-CDR" "ACL2"))
(defconst *h4-book-updates-equal-predecessors* (proof-sym "H4-EQUAL-PREDECESSORS-LEFT" "ACL2"))
(defconst *h4-book-updates-logic*
  (list *proof-not* (proof-cl "ATOM") (proof-cl "ENDP") (proof-cl "EQ")))

(defun h4-book-updates-index-guard (index sequence)
  (proof-ite (list *library-natp* index)
             (library-lt index (list *library-len* sequence))
             *proof-false*))

(defun h4-book-updates-update-shape-getter (guard required update)
  (let ((value (cadr update))
        (index (caddr update))
        (sequence (cadddr update)))
    (and (proof-is-call guard *proof-if*)
         (equal (cddr guard) (list required *proof-false*))
         (let ((readback (cadr guard)))
           (and (proof-is-call readback *proof-equal*)
                (proof-with-checked-results ((written (proof-term-at readback 1)))
                  (and (equal written value)
                       (proof-with-checked-results ((getter (proof-term-at readback 2)))
                         (and (proof-compound getter)
                              (proof-with-checked-results ((head (proof-term-at getter 0)))
                                (and (not (proof-compound head))
                                     (equal (cdr getter) (list index sequence))
                                     (list update nil getter))))))))))))

(defun h4-book-updates-update-shape-arguments (guard right update observe)
  (and (proof-compound update)
       (proof-with-checked-results ((head (proof-term-at update 0)))
         (and (not (proof-compound head))
              (equal (len update) 4)
              (let ((index (caddr update))
                    (sequence (cadddr update)))
                (and (not (proof-compound index))
                     (not (proof-compound sequence))
                     (let ((required (h4-book-updates-index-guard index sequence)))
                       (if observe
                           (and (equal right (list observe sequence))
                                (equal guard required)
                                (list update observe nil))
                         (and (equal right sequence)
                              (h4-book-updates-update-shape-getter
                               guard required update))))))))))

(defun h4-book-updates-update-shape (formula)
  (and (proof-is-call formula *library-implies*)
       (proof-with-checked-results ((claim (proof-term-at formula 2)))
         (and (proof-is-call claim *proof-equal*)
              (proof-with-checked-results
                  ((formula (proof-list-of-length formula 3))
                   (claim (proof-list-of-length claim 3)))
                (let ((guard (cadr formula))
                      (left (cadr claim))
                      (right (caddr claim)))
                  (and (proof-compound left)
                       (proof-with-checked-results ((left-head (proof-term-at left 0)))
                         (and (not (proof-compound left-head))
                              (proof-with-checked-results
                                  ((observe
                                    (and (member-equal left-head
                                                      (list *h4-book-updates-true-list* *library-len*))
                                         (proof-with-checked-results
                                             ((right-head (proof-term-at right 0)))
                                           (and (equal left-head right-head) left-head))))
                                   (update (if observe (proof-term-at left 1) left)))
                                (h4-book-updates-update-shape-arguments
                                 guard right update observe)))))))))))

(defun h4-book-updates-select-result (p call test)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof call))
         (literal (proof-step-first opened))
         (conditional (proof-term-at literal 2))
         (selected (proof-proof-select proof conditional test)))
      (proof-proof-chain proof opened (list selected)))))

(defun h4-book-updates-observe-list (p name sequence shape)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((details
          (if (proof-is-call sequence *proof-cons*)
              (let ((parts (cdr sequence)))
                (proof-with-checked-results
                    ((shape (proof-proof-fact
                             proof "consp-cons" (seq-zip (list *library-x* *library-y*) parts)))
                     (car-step (library-library-axiom p "CAR-CONS" parts))
                     (cdr-step (library-library-axiom p "CDR-CONS" parts)))
                  (cons shape (list car-step cdr-step))))
            (cons shape nil))))
      (if (not (car details))
          '(:failure "InapplicableStep" "")
        (proof-with-checked-results
            ((opened (proof-proof-unfold proof (list name sequence)))
             (literal (proof-step-first opened))
             (body (proof-term-at literal 2))
             (reduced (h4-tactics-tactics-normalize p body (list (car details))
                                                    *h4-book-updates-logic* (cdr details) nil)))
          (proof-proof-chain proof opened (list reduced)))))))

(defun h4-book-updates-prove-bounded-update-reconstruct
  (changed learned recursive p observer update sequence pair)
  (let ((proof (library-library-proof p)))
    (if observer
        (proof-with-checked-results
            ((identity (proof-proof-reflexive proof (list observer update)))
             (lifting (proof-proof-rewrite proof identity changed '(1 2 1)))
             (literal (proof-step-first changed))
             (output (proof-term-at literal 2))
             (observation (h4-book-updates-observe-list p observer output nil))
             (observed (proof-proof-chain proof lifting (list observation)))
             (observed
              (if recursive
                  (proof-with-checked-results
                      ((literal (proof-step-first observed))
                       (output (proof-term-at literal 2))
                       (rewritten (h4-tactics-tactics-normalize p output nil nil
                                                               (list learned) nil)))
                    (proof-proof-chain proof observed (list rewritten)))
                observed))
             (observation (h4-book-updates-observe-list p observer sequence pair))
             (reversed (proof-proof-symmetric proof observation)))
          (proof-proof-chain proof observed (list reversed)))
      (proof-with-checked-results
          ((restored (proof-proof-rewrite proof changed learned
                                          (if recursive '(1 2 2) '(1 2 1))))
           (elimination (library-library-axiom p "CAR-CDR-ELIM" (list sequence)))
           (joined (h4-tactics-tactics-modus-ponens p elimination pair)))
        (proof-proof-chain proof restored (list joined))))))

(defun h4-book-updates-prove-bounded-update-stop
  (test p getter readback observer update sequence pair)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((learned (if getter
                      (proof-with-checked-results
                          ((selected (h4-book-updates-select-result p getter test)))
                        (proof-proof-rewrite proof readback selected '(1 2)))
                    nil))
         (changed (h4-book-updates-select-result p update test)))
      (h4-book-updates-prove-bounded-update-reconstruct
       changed learned nil p observer update sequence pair))))

(defun h4-book-updates-prove-bounded-update-continue-
  (test p index formula bindings natural upper pair getter readback observer update sequence)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((builtin (library-library-builtin p 9 index))
         (descent (proof-proof-discharge proof builtin test))
         (condition (proof-step-first descent))
         (substituted (proof-subst formula (proof-bindings-table bindings nil)))
         (assumed (proof-proof-assume proof (proof-ite condition substituted *proof-true*) t))
         (hypothesis (proof-proof-prove-if proof assumed descent))
         (child-natural (proof-proof-use proof *h4-book-updates-predecessor-natural*
                                         (list (list *library-x* index)) (list test)))
         (child-upper (proof-proof-use proof *h4-book-updates-tail-bound*
                                       (list (list *library-x* index) (list *library-y* sequence))
                                       (list natural upper pair)))
         (child-guard (h4-book-division-conjunction p (list child-natural child-upper)))
         (child-guard
          (if getter
              (proof-with-checked-results
                  ((selected (h4-book-updates-select-result p getter test))
                   (child-readback (proof-proof-rewrite proof readback selected '(1 2))))
                (h4-book-division-conjunction p (list child-readback child-guard)))
            child-guard))
         (learned (h4-tactics-tactics-modus-ponens p hypothesis child-guard))
         (changed (h4-book-updates-select-result p update test)))
      (h4-book-updates-prove-bounded-update-reconstruct
       changed learned t p observer update sequence pair))))

(defun h4-book-updates-prove-bounded-update (p formula shape)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((shape (proof-list-of-length shape 3))
         (update (proof-list-of-length (car shape) 4)))
      (let* ((observer (cadr shape))
             (getter (caddr shape))
             (index (caddr update))
             (sequence (cadddr update))
             (tail (list *library-cdr* sequence))
             (child (h4-book-arithmetic-predecessor index))
             (bindings (list (list index child) (list sequence tail)))
             (test (list *h4-book-arithmetic-zp* index)))
        (proof-with-checked-results
            ((claim (proof-term-at formula 2))
             (formula-guard (proof-term-at formula 1))
             (guard (proof-proof-assume proof formula-guard t))
             (guard-parts (if getter (h4-tactics-tactics-conjunct p guard) (list nil guard)))
             (bound-parts (h4-tactics-tactics-conjunct p (cadr guard-parts)))
             (pair (proof-proof-use proof *h4-book-arithmetic-index-in-bounds*
                                    (list (list *library-x* index) (list *library-y* sequence))
                                    bound-parts))
             (yes-test (proof-proof-assume proof test t))
             (yes (h4-book-updates-prove-bounded-update-stop
                   yes-test p getter (car guard-parts) observer update sequence pair))
             (no-test (proof-proof-assume proof test nil))
             (no (h4-book-updates-prove-bounded-update-continue-
                  no-test p index formula bindings (car bound-parts) (cadr bound-parts)
                  pair getter (car guard-parts) observer update sequence))
             (cases (h4-tactics-tactics-case-of p claim test yes no))
             (ordinal (library-library-builtin p 1 index))
             (implication (h4-tactics-tactics-imply p formula cases)))
          (proof-proof-induct proof ordinal implication formula (list *library-count* index)
                              (list bindings)))))))

(defun h4-book-updates-applicable-step (result)
  (if (and (failure-p result)
           (member-equal (cadr result) '("InapplicableStep" "assertion")))
      nil
    result))

(defun h4-book-updates-list-update-proof (p formula)
  (proof-with-checked-results ((shape (h4-book-updates-update-shape formula)))
    (let ((definitions (proof-proof-definitions (library-library-proof p))))
      (and shape
           (assoc-equal (caar shape) definitions)
           (or (not (caddr shape)) (assoc-equal (car (caddr shape)) definitions))
           (h4-book-updates-applicable-step
            (h4-book-updates-prove-bounded-update p formula shape))))))

(defun h4-book-updates-swap-shape-updates (guard left right)
  (and (proof-compound left)
       (proof-with-checked-results ((update (proof-term-at left 0)))
         (and (not (proof-compound update))
              (equal (len left) 4)
              (proof-is-call (cadddr left) update)
              (equal (len (cadddr left)) 4)
              (let* ((value (cadr left))
                     (first (caddr left))
                     (inner (cadddr left))
                     (other (cadr inner))
                     (second (caddr inner))
                     (sequence (cadddr inner)))
                (and (not (proof-compound first))
                     (not (proof-compound second))
                     (not (proof-compound sequence))
                     (not (or (equal first second)
                              (equal first sequence)
                              (equal second sequence)))
                     (equal right (list update other second (list update value first sequence)))
                     (let ((required
                            (proof-ite (list *library-natp* first)
                                       (proof-ite (list *library-natp* second)
                                                  (proof-neg (proof-eq first second)) *proof-false*)
                                       *proof-false*)))
                       (and (equal guard required) (list first second sequence)))))))))

(defun h4-book-updates-swap-shape (formula)
  (and (proof-is-call formula *library-implies*)
       (proof-with-checked-results ((claim (proof-term-at formula 2)))
         (and (proof-is-call claim *proof-equal*)
              (proof-with-checked-results
                  ((formula (proof-list-of-length formula 3))
                   (claim (proof-list-of-length claim 3)))
                (h4-book-updates-swap-shape-updates (cadr formula) (cadr claim) (caddr claim)))))))

(defun h4-book-updates-swap-updates-unroll (call outer-test inner-test p provider)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((outer (h4-book-updates-select-result p call outer-test))
         (nested (proof-term-at call 3))
         (inner (h4-book-updates-select-result p nested inner-test))
         (literal (proof-step-first outer))
         (value (proof-term-at literal 2))
         (reduced (h4-tactics-tactics-normalize p value nil nil (list inner) provider)))
      (proof-proof-chain proof outer (list reduced)))))

(defun h4-book-updates-swap-updates-zero-index (term natural test p)
  (proof-proof-use (library-library-proof p) *h4-book-arithmetic-natural-countdown-zero*
                   (list (list *library-x* term)) (list natural test)))

(defun h4-book-updates-swap-updates-inductive-order
  (p first-order formula substitutions first second i-test j-test nat-first nat-second different)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((builtin (library-library-builtin p 9 first))
         (descent (proof-proof-discharge proof builtin i-test))
         (child-formula (proof-subst formula (proof-bindings-table substitutions nil)))
         (condition (proof-step-first descent))
         (assumed (proof-proof-assume proof (proof-ite condition child-formula *proof-true*) t))
         (induction (proof-proof-prove-if proof assumed descent))
         (i-type (library-library-cite p "NATURAL-INTEGER" (list first) (list nat-first)))
         (j-type (library-library-cite p "NATURAL-INTEGER" (list second) (list nat-second)))
         (indices (proof-proof-use proof *h4-book-updates-equal-predecessors*
                                    (list (list *library-x* first) (list *library-y* second))
                                    (list i-type j-type)))
         (reversed (proof-proof-symmetric proof indices))
         (child-different (proof-proof-rewrite proof different reversed '(1 1)))
         (child-first (proof-proof-use proof *h4-book-updates-predecessor-natural*
                                       (list (list *library-x* first)) (list i-test)))
         (child-second (proof-proof-use proof *h4-book-updates-predecessor-natural*
                                        (list (list *library-x* second)) (list j-test)))
         (guards (h4-book-division-conjunction p (list child-first child-second child-different)))
         (tails-equal (h4-tactics-tactics-modus-ponens p induction guards)))
      (proof-proof-rewrite proof first-order tails-equal '(1 2 2)))))

(defun h4-book-updates-swap-updates-compare
  (i-test j-test p formula goal left right first second provider
          nat-first nat-second different tests substitutions)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((i-literal (proof-step-first i-test))
         (j-literal (proof-step-first j-test)))
      (let ((i-zero (equal i-literal (car tests)))
            (j-zero (equal j-literal (cadr tests))))
        (if (and i-zero j-zero)
            (proof-with-checked-results
                ((i-equality (h4-book-updates-swap-updates-zero-index first nat-first i-test p))
                 (j-equality (h4-book-updates-swap-updates-zero-index second nat-second j-test p))
                 (reversed (proof-proof-symmetric proof j-equality))
                 (equal-indices (proof-proof-chain proof i-equality (list reversed)))
                 (contradiction (proof-proof-cut proof equal-indices different)))
              (proof-proof-subsume proof contradiction (cons goal (proof-step-clause contradiction))))
          (proof-with-checked-results
              ((first-order (h4-book-updates-swap-updates-unroll left i-test j-test p provider))
               (second-order (h4-book-updates-swap-updates-unroll right j-test i-test p provider))
               (first-order
                (if (or i-zero j-zero)
                    first-order
                  (h4-book-updates-swap-updates-inductive-order
                   p first-order formula substitutions first second i-test j-test
                   nat-first nat-second different)))
               (reversed (proof-proof-symmetric proof second-order)))
            (proof-proof-chain proof first-order (list reversed))))))))

(defun h4-book-updates-swap-updates-second-case
  (i-test p formula goal left right first second provider nat-first nat-second different
          tests substitutions)
  (let ((proof (library-library-proof p))
        (test (cadr tests)))
    (proof-with-checked-results
        ((yes-test (proof-proof-assume proof test t))
         (yes (h4-book-updates-swap-updates-compare
               i-test yes-test p formula goal left right first second provider
               nat-first nat-second different tests substitutions))
         (no-test (proof-proof-assume proof test nil))
         (no (h4-book-updates-swap-updates-compare
              i-test no-test p formula goal left right first second provider
              nat-first nat-second different tests substitutions)))
      (h4-tactics-tactics-case-of p goal test yes no))))

(defun h4-book-updates-swap-updates (p formula first second sequence)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((goal (proof-term-at formula 2))
         (sides (if (integerp goal)
                    '(:failure "failure" "")
                  (proof-list-of-length (cdr goal) 2)))
         (provider (h4-book-finite-reduction-provider p))
         (condition (proof-term-at formula 1))
         (guard (proof-proof-assume proof condition t))
         (parts (h4-tactics-tactics-conjunct p guard))
         (further (h4-tactics-tactics-conjunct p (cadr parts))))
      (let* ((left (car sides))
             (right (cadr sides))
             (nat-first (car parts))
             (nat-second (car further))
             (different (cadr further))
             (tests (list (list *h4-book-arithmetic-zp* first) (list *h4-book-arithmetic-zp* second)))
             (substitutions (list (list first (h4-book-arithmetic-predecessor first))
                                  (list second (h4-book-arithmetic-predecessor second))
                                  (list sequence (list *library-cdr* sequence))))
             (test (car tests)))
        (proof-with-checked-results
            ((yes-test (proof-proof-assume proof test t))
             (yes (h4-book-updates-swap-updates-second-case
                   yes-test p formula goal left right first second provider nat-first nat-second
                   different tests substitutions))
             (no-test (proof-proof-assume proof test nil))
             (no (h4-book-updates-swap-updates-second-case
                  no-test p formula goal left right first second provider nat-first nat-second
                  different tests substitutions))
             (cases (h4-tactics-tactics-case-of p goal test yes no))
             (ordinal (library-library-builtin p 1 first))
             (implication (h4-tactics-tactics-imply p formula cases)))
          (proof-proof-induct proof ordinal implication formula (list *library-count* first)
                              (list substitutions)))))))

(defun h4-book-updates-swap-proof (p formula)
  (proof-with-checked-results ((plan (h4-book-updates-swap-shape formula)))
    (let ((definitions (proof-proof-definitions (library-library-proof p))))
      (and plan
           (assoc-equal (car (cadr (caddr formula))) definitions)
           (h4-book-updates-applicable-step
            (h4-book-updates-swap-updates p formula (car plan) (cadr plan) (caddr plan)))))))

(defun h4-book-updates-append-suffix-type-open-append (shape p call)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (proof-proof-unfold proof call))
         (literal (proof-step-first opened))
         (value (proof-term-at literal 2))
         (reduced (h4-tactics-tactics-normalize p value (list shape)
                                                *h4-book-updates-logic* nil nil)))
      (proof-proof-chain proof opened (list reduced)))))

(defun h4-book-updates-append-suffix-type-lift (equality p call)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((identity (proof-proof-reflexive proof (list *h4-book-updates-true-list* call))))
      (proof-proof-rewrite proof identity equality '(1 2 1)))))

(defun h4-book-updates-append-suffix-type-stop (shape p call)
  (proof-with-checked-results ((opened (h4-book-updates-append-suffix-type-open-append shape p call)))
    (h4-book-updates-append-suffix-type-lift opened p call)))

(defun h4-book-updates-append-suffix-type-join (shape p call formula tail)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((opened (h4-book-updates-append-suffix-type-open-append shape p call))
         (lifted (h4-book-updates-append-suffix-type-lift opened p call))
         (literal (proof-step-first opened))
         (output (proof-term-at literal 2))
         (observed (h4-book-updates-observe-list p *h4-book-updates-true-list* output nil))
         (inspected (proof-proof-chain proof lifted (list observed)))
         (builtin (library-library-builtin p 3 *library-x*))
         (descent (proof-proof-discharge proof builtin shape))
         (condition (proof-step-first descent))
         (child (proof-subst formula (list (cons *library-x* tail))))
         (assumed (proof-proof-assume proof (proof-ite condition child *proof-true*) t))
         (induction (proof-proof-prove-if proof assumed descent)))
      (proof-proof-chain proof inspected (list induction)))))

(defun h4-book-updates-append-suffix-type (p append-name)
  (let* ((proof (library-library-proof p))
         (call (list append-name *library-x* *library-y*))
         (formula (proof-eq (list *h4-book-updates-true-list* call)
                            (list *h4-book-updates-true-list* *library-y*)))
         (pair (list *proof-consp* *library-x*))
         (tail (list *library-cdr* *library-x*))
         (substitutions (list (list *library-x* tail))))
    (proof-with-checked-results
        ((yes-test (proof-proof-assume proof pair t))
         (yes (h4-book-updates-append-suffix-type-join yes-test p call formula tail))
         (no-test (proof-proof-assume proof pair nil))
         (no (h4-book-updates-append-suffix-type-stop no-test p call))
         (cases (h4-tactics-tactics-case-of p formula pair yes no))
         (ordinal (library-library-builtin p 1 *library-x*)))
      (proof-proof-induct proof ordinal cases formula (list *library-count* *library-x*)
                          (list substitutions)))))

(defun h4-book-updates-append-suffix-shape-body (call body formals definitions)
  (and (proof-is-call body *proof-if*)
       (proof-with-checked-results
           ((test (proof-term-at body 1))
            (formal (proof-term-at formals 0)))
         (and (equal test (list *h4-book-arithmetic-zp* formal))
              (proof-with-checked-results ((base (proof-term-at body 2)))
                (and (equal base *proof-false*)
                     (proof-with-checked-results ((value (proof-term-at body 3)))
                       (and (proof-compound value)
                            (proof-with-checked-results ((head (proof-term-at value 0)))
                              (and (not (proof-compound head))
                                   (equal (len value) 3)
                                   (assoc-equal head definitions)
                                   (equal (cadr value)
                                          (list (car call) (h4-book-arithmetic-predecessor formal)))
                                   (equal (caddr value) (list *proof-cons* formal *proof-false*))
                                   (list call head)))))))))))

(defun h4-book-updates-append-suffix-shape (p formula)
  (and (proof-is-call formula *h4-book-updates-true-list*)
       (proof-with-checked-results ((call (proof-term-at formula 1)))
         (and (proof-compound call)
              (proof-with-checked-results ((head (proof-term-at call 0)))
                (and (not (proof-compound head))
                     (equal (len call) 2)
                     (let* ((definitions (proof-proof-definitions (library-library-proof p)))
                            (definition (assoc-equal head definitions)))
                       (and definition
                            (proof-with-checked-results
                                ((parts (proof-list-of-length (cdr definition) 2)))
                              (h4-book-updates-append-suffix-shape-body
                               call (cadr parts) (car parts) definitions))))))))))

(defun h4-book-updates-append-suffix-proof-stop (test p call)
  (proof-with-checked-results
      ((empty (h4-tactics-tactics-establish
               p (list *h4-book-updates-true-list* *proof-false*) nil
               (append *h4-book-updates-logic* (list *h4-book-updates-true-list*)) nil nil))
       (selected (h4-book-updates-select-result p call test)))
    (library-library-transport-argument p empty selected 1)))

(defun h4-book-updates-append-suffix-proof-join (test p call lemma)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((expanded (h4-book-updates-select-result p call test))
         (literal (proof-step-first expanded))
         (output (proof-term-at literal 2))
         (arguments (proof-list-of-length output 3))
         (empty (h4-tactics-tactics-establish
                 p (list *h4-book-updates-true-list* *proof-false*) nil
                 (append *h4-book-updates-logic* (list *h4-book-updates-true-list*)) nil nil))
         (observed (h4-book-updates-observe-list p *h4-book-updates-true-list* (caddr arguments) nil))
         (suffix (proof-proof-transport proof empty observed))
         (instance (proof-proof-instantiate
                    proof lemma (list (list *library-x* (cadr arguments))
                                      (list *library-y* (caddr arguments)))))
         (combined (proof-proof-transport proof suffix instance)))
      (library-library-transport-argument p combined expanded 1))))

(defun h4-book-updates-append-suffix-proof (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results ((shape (h4-book-updates-append-suffix-shape p formula)))
      (and shape
           (h4-book-updates-applicable-step
            (proof-with-checked-results
                ((lemma (h4-book-updates-append-suffix-type p (cadr shape)))
                 (argument (proof-term-at (car shape) 1))
                 (test (list *h4-book-arithmetic-zp* argument))
                 (yes-test (proof-proof-assume proof test t))
                 (yes (h4-book-updates-append-suffix-proof-stop yes-test p (car shape)))
                 (no-test (proof-proof-assume proof test nil))
                 (no (h4-book-updates-append-suffix-proof-join no-test p (car shape) lemma)))
              (h4-tactics-tactics-case-of p formula test yes no)))))))
