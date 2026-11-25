(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h4-recipes-from-df* (proof-sym "FROM-DF" "ACL2"))
(defconst *h4-recipes-recognizers*
  (list (proof-sym "DFP" "ACL2") (proof-cl "RATIONALP") (proof-cl "STRINGP")))

(defun h4-recipes-recognized-result (p formula)
  (proof-with-checked-results
      ((direct (h4-tactics-tactics-fact-instance p formula nil :none nil)))
    (if direct
        direct
      (proof-with-checked-results
          ((parts (proof-list-of-length formula 2))
           (recognizer (car parts))
           (call (cadr parts))
           (head (proof-term-at call 0))
           (reduced (h4-tactics-tactics-normalize
                     p call nil (list head *h4-recipes-from-df*) nil nil))
           (literal (proof-step-first reduced))
           (value (proof-term-at literal 2))
           (step (h4-tactics-tactics-fact-instance
                  p (list recognizer value) nil :none nil)))
        (if step
            (library-library-transport-argument p step reduced 1)
          '(:failure "failure" ""))))))

(defun h4-recipes-rationalize-round-trip-normalize
    (n p term known definitions equations replies result)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "h4-recipes-rationalize-round-trip-normalize"))
        ((not (h4-tactics-request-p result)) result)
        (t (let* ((request (h4-tactics-request-term result))
                  (reply (h4-tactics-tactics-fact-instance p request known equations t))
                  (replies (table-put replies request reply))
                  (next (if (failure-p reply)
                            reply
                          (h4-tactics-tactics-normalize
                           p term known definitions nil (cons :h4-tactics-provider replies)))))
             (h4-recipes-rationalize-round-trip-normalize
              (1- n) p term known definitions equations replies next)))))

(defun h4-recipes-rationalize-round-trip-attempt (p formula known equations definitions)
  (let ((goal (caddr formula)))
    (proof-with-checked-results
        ((term (proof-term-at goal 1))
         (first (h4-tactics-tactics-normalize
                 p term known definitions nil (list :h4-tactics-provider)))
         (step (h4-recipes-rationalize-round-trip-normalize
                1000000 p term known definitions equations nil first))
         (literal (proof-step-first step)))
      (and (equal literal goal) (h4-tactics-tactics-imply p formula step)))))

(defun h4-recipes-rationalize-round-trip (p formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (premise (proof-proof-assume (library-library-proof p) (cadr parts) t)))
    (let ((known (list premise))
          (wrappers (list *h4-recipes-from-df*
                          (proof-sym "TO-DFP" "ACL2")
                          (proof-sym "RIZE" "ACL2")))
          (equations (list (proof-sym "TO-DF-OF-DF-RATIONALIZE" "ACL2")
                           (proof-sym "TO-DF-OF-CONSTRAINED-DF-RATIONALIZE" "ACL2")
                           (proof-sym "DFP-IMPLIES-TO-DF-IS-IDENTITY" "ACL2"))))
      (or (h4-recipes-rationalize-round-trip-attempt p formula known equations wrappers)
          (h4-recipes-rationalize-round-trip-attempt
           p formula known equations (append wrappers (list (proof-sym "DF-RATIONALIZE" "ACL2"))))
          '(:failure "failure" "")))))

(defun h4-recipes-legal-name (p formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (premise (proof-proof-assume (library-library-proof p) (cadr parts) t))
       (conclusion (caddr parts))
       (argument (proof-term-at conclusion 1))
       (head (proof-term-at argument 0))
       (step (h4-tactics-tactics-establish
              p conclusion (list premise) (list head *proof-not*) nil nil)))
    (h4-tactics-tactics-imply p formula step)))

(defun h4-recipes-natural-measure-bounds (p opened body test total distance integers nonnegative)
  (proof-with-checked-results
      ((distance-is-int (library-library-type-of p distance integers))
       (pos (library-library-cite p "POSITIVE-ONE-PLUS" (list distance)
                                  (list distance-is-int nonnegative)))
       (total-is-int (library-library-type-of p total integers))
       (bound (library-library-cite p "POSITIVE-NONNEGATIVE" (list total)
                                    (list total-is-int pos)))
       (result (library-library-cite p "NATURAL-FROM-BOUNDS" (list total)
                                     (list total-is-int bound)))
       (proof (library-library-proof p))
       (if-true-step (proof-proof-if-true proof body))
       (yes (library-library-transport-argument p result if-true-step 1))
       (zero-natural (library-library-natural p *proof-zero*))
       (if-false-step (proof-proof-if-false proof body))
       (no (library-library-transport-argument p zero-natural if-false-step 1))
       (cases (proof-proof-cases proof test yes no))
       (step (library-library-transport-argument p cases opened 1)))
    (cons step p)))

(defun h4-recipes-natural-measure (p formula)
  (let ((proof (library-library-proof p)))
    (proof-with-checked-results
        ((call (proof-term-at formula 1))
         (opened (proof-proof-unfold proof call))
         (literal (proof-step-first opened))
         (body (proof-term-at literal 2))
         (branches (proof-list-of-length (cdr body) 3)))
      (if (not (equal (caddr branches) *proof-zero*))
          '(:failure "failure" "")
        (proof-with-checked-results
            ((arguments (proof-list-of-length (cdr call) 2))
             (i (car arguments))
             (j (cadr arguments))
             (test (car branches))
             (total (cadr branches))
             (assumed (proof-proof-assume proof test t))
             (first (h4-tactics-tactics-conjunct p assumed))
             (ix (car first))
             (second (h4-tactics-tactics-conjunct p (cadr first)))
             (jx (car second))
             (latest (cadr second))
             (distance (library-diff j i))
             (compare (library-library-axiom p "<-ON-OTHERS" (list j i)))
             (nonnegative (proof-proof-rewrite proof latest compare '(1 1)))
             (nonnegative-literal (proof-step-first nonnegative)))
          (if (not (equal nonnegative-literal (proof-neg (library-lt distance *proof-zero*))))
              '(:failure "failure" "")
            (proof-with-checked-results
                ((p (h4-terms-tactics-logic-and-types p))
                 (p (h4-terms-tactics-additive-identities p))
                 (p (h4-terms-tactics-ordered-arithmetic p)))
              (h4-recipes-natural-measure-bounds
               p opened body test total distance (list ix jx) nonnegative))))))))

(defun h4-recipes-recipe-recognizer (formula)
  (proof-with-checked-results ((head (proof-term-at formula 0)))
    (and (member-equal head *h4-recipes-recognizers*)
         (proof-with-checked-results ((call (proof-term-at formula 1)))
           (and (proof-compound call)
                (proof-with-checked-results ((operator (proof-term-at call 0)))
                  (and (not (proof-compound operator)) :recognized-result)))))))

(defun h4-recipes-recipe-natural-measure (formula)
  (and (proof-is-call formula *library-natp*)
       (proof-with-checked-results ((call (proof-term-at formula 1)))
         (and (proof-compound call) (equal (len call) 3) :natural-measure))))

(defun h4-recipes-recipe-equivalence (formula)
  (and (proof-is-call formula *proof-if*)
       (proof-with-checked-results ((test (proof-term-at formula 1)))
         (and (proof-is-call test (proof-sym "BOOLEANP" "ACL2"))
              (proof-with-checked-results ((relation (proof-term-at test 1)))
                (and (proof-is-call relation *h4-function-equality-fn-equal*)
                     :fn-equal-is-equivalence))))))

(defun h4-recipes-recipe-implication (formula)
  (and (proof-is-call formula *library-implies*)
       (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
         (let ((guard (cadr parts)) (goal (caddr parts)))
           (cond
            ((and (proof-is-call guard *h4-function-equality-fn-equal*)
                  (proof-is-call goal *proof-equal*))
             (proof-with-checked-results ((call (proof-term-at goal 1)))
               (if (proof-is-call call (proof-sym "DO$" "ACL2"))
                   :do-congruence
                 :loop-congruence)))
            ((and (proof-is-call guard (proof-sym "DFP" "ACL2"))
                  (proof-is-call goal *proof-equal*))
             (proof-with-checked-results
                 ((right (proof-term-at goal 2)) (value (proof-term-at guard 1)))
               (and (equal right value)
                    (let ((left (cadr goal)))
                      (or (equal left (list (proof-sym "TO-DF" "ACL2")
                                            (list (proof-sym "DF-RATIONALIZE" "ACL2") value)))
                          (equal left (list (proof-sym "TO-DFP" "ACL2")
                                            (list (proof-sym "RIZE" "ACL2") value)))))
                    :rationalize-round-trip)))
            ((proof-is-call guard *proof-not*)
             (proof-with-checked-results ((test (proof-term-at guard 1)))
               (and (proof-is-call test (proof-cl "SYMBOLP"))
                    (proof-with-checked-results ((value (proof-term-at test 1)))
                      (and (equal goal (proof-neg
                                        (list (proof-sym "LEGAL-VARIABLE-OR-CONSTANT-NAMEP" "ACL2") value)))
                           :legal-name)))))
            ((proof-is-call guard (proof-sym "TERMP" "ACL2"))
             (proof-with-checked-results ((value (proof-term-at guard 1)))
               (and (equal goal (list (proof-sym "PSEUDO-TERMP" "ACL2") value))
                    :term-implies-pseudo)))
            ((proof-is-call guard (proof-sym "TERM-LISTP" "ACL2"))
             (proof-with-checked-results ((value (proof-term-at guard 1)))
               (and (equal goal (list (proof-sym "PSEUDO-TERM-LISTP" "ACL2") value))
                    :term-list-implies-pseudo)))
            ((proof-is-call guard *proof-if*)
             (proof-with-checked-results ((test (proof-term-at guard 1)))
               (and (proof-is-call test (proof-sym "ARITIES-OKP" "ACL2"))
                    (proof-with-checked-results ((no (proof-term-at guard 3)))
                      (and (equal no *proof-false*)
                           (cond ((proof-is-call goal (proof-sym "LOGICP" "ACL2"))
                                  :arity-or-logic)
                                 ((proof-is-call goal *proof-equal*)
                                  (proof-with-checked-results ((left (proof-term-at goal 1)))
                                    (and (proof-is-call left (proof-sym "ARITY" "ACL2"))
                                         :arity-or-logic))))))))))))))

(defun h4-recipes-recipe (formula)
  (and (proof-compound formula)
       (proof-with-checked-results ((recognizer (h4-recipes-recipe-recognizer formula)))
         (or recognizer
             (proof-with-checked-results ((warrant (h4-warrants-warrant-parts formula)))
               (or (and warrant :warrant-recipe)
                   (h4-recipes-recipe-natural-measure formula)
                   (h4-recipes-recipe-equivalence formula)
                   (h4-recipes-recipe-implication formula)))))))

(defun h4-recipes-apply (tactic p formula warrant-filters)
  (case tactic
    (:warrant-recipe (h4-warrants-warrant-recipe p formula warrant-filters))
    (:natural-measure (h4-recipes-natural-measure p formula))
    (:do-congruence (h4-do-loop-do-congruence p formula))
    (:loop-congruence (h4-function-equality-loop-congruence p formula))
    (:term-implies-pseudo (h4-terms-term-implies-pseudo p formula))
    (otherwise
     (proof-with-checked-results
         ((step (case tactic
                  (:recognized-result (h4-recipes-recognized-result p formula))
                  (:fn-equal-is-equivalence
                   (h4-function-equality-fn-equal-is-equivalence p formula))
                  (:rationalize-round-trip (h4-recipes-rationalize-round-trip p formula))
                  (:legal-name (h4-recipes-legal-name p formula))
                  (:term-list-implies-pseudo (h4-terms-term-list-implies-pseudo p formula))
                  (:arity-or-logic (h4-association-arity-or-logic p formula))
                  (otherwise '(:failure "failure" "")))))
       (cons step p)))))
