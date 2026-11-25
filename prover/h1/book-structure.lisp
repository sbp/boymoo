(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *h1-book-structure-atom* (proof-cl "ATOM"))
(defconst *h1-book-structure-endp* (proof-cl "ENDP"))
(defconst *h1-book-structure-strip*
  (list (cons *library-car* (proof-sym "STRIP-CARS" "ACL2"))
        (cons *library-cdr* (proof-sym "STRIP-CDRS" "ACL2"))))
(defconst *h1-book-structure-lookup*
  (list (proof-sym "ASSOC-EQUAL" "ACL2")
        (proof-sym "HONS-ASSOC-EQUAL" "ACL2")))

(defun h1-book-structure-unproved-p (result)
  (and (failure-p result) (equal (cadr result) "unproved")))

(defun h1-book-structure-container-case (proof application known)
  (let ((core (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((equation (proof-proof-unfold core application))
         (branch (proof-rewritten-term equation)))
      (if (not (proof-is-call branch *proof-if*))
          '(:failure "unproved" "")
        (proof-with-checked-results
            ((test (proof-term-at branch 1))
             (known-literal (proof-step-first known)))
          (if (or (equal known-literal test)
                  (equal known-literal (proof-neg test)))
              (h1-propositions-select-value lib equation known)
            (proof-with-checked-results
                ((reduced
                  (h1-propositions-proof-simplify
                   core test (list known)
                   (list *h1-book-structure-atom* *h1-book-structure-endp*
                         *proof-not*))))
              (if (not reduced)
                  '(:failure "unproved" "")
                (proof-with-checked-results
                    ((value (proof-rewritten-term reduced)))
                  (if (member-equal value (list *proof-true* *proof-false*))
                      (proof-with-checked-results
                          ((tested (h1-propositions-computed-test lib reduced)))
                        (h1-propositions-select-value lib equation tested))
                    '(:failure "unproved" "")))))))))))

(defun h1-book-structure-projected-members (proof premise goal selector strip alist cons-evidence)
  (let* ((core (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (head-value (list selector (list *library-car* alist)))
         (tail-values (list strip (list *library-cdr* alist))))
    (proof-with-checked-results
        ((projected (h1-book-structure-container-case proof (cadr premise) cons-evidence))
         (projection (proof-rewritten-term projected)))
      (if (not (equal projection (list *proof-cons* head-value tail-values)))
          '(:failure "unproved" "")
        (proof-with-checked-results
            ((assumed (h1-arithmetic-proof-assume core premise t))
             (members (proof-proof-rewrite core assumed projected '(1 1)))
             (literal (proof-step-first members))
             (cons-fact (proof-proof-fact core "consp-cons"
                                        (list (list *library-x* head-value)
                                              (list *library-y* tail-values))))
             (typed (h1-book-structure-container-case proof literal cons-fact))
             (car-cons (library-library-axiom lib "CAR-CONS" (list head-value tail-values)))
             (with-head (h1-propositions-rewrite-value lib typed car-cons))
             (cdr-cons (library-library-axiom lib "CDR-CONS" (list head-value tail-values)))
             (typed (h1-propositions-rewrite-value lib with-head cdr-cons))
             (value (proof-rewritten-term typed)))
          (if (not (equal value (proof-ite (list (car goal) head-value)
                                           (list (car premise) tail-values)
                                           *proof-false*)))
              '(:failure "unproved" "")
            (proof-with-checked-results
                ((opened (proof-proof-rewrite core members typed '(1))))
              (h1-propositions-propositional-proof-conjunct lib opened))))))))

(defun h1-book-structure-projected-branch (proof equation test holds projection evidence)
  (let ((core (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof)))
    (proof-with-checked-results
        ((assumed (h1-arithmetic-proof-assume core test holds))
         (opened (h1-propositions-select-value lib equation assumed))
         (refl (h1-propositions-propositional-proof-reflexive lib projection))
         (value (proof-proof-rewrite core refl opened '(1 2 1))))
      (h1-propositions-library-transport-argument lib evidence value 1))))

(defun h1-book-structure-projected-cons (proof formula application goal alist cons-evidence members)
  (let* ((core (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (tail (list *library-cdr* alist))
         (tail-call (list (car application) (cadr application) tail)))
    (proof-with-checked-results
        ((decrease (library-library-builtin lib 3 alist))
         (decrease-literal (proof-step-first decrease))
         (child (proof-subst formula (list (cons alist tail))))
         (hypothesis (h1-arithmetic-proof-assume core (proof-ite decrease-literal child *proof-true*) t))
         (proved (h1-propositions-proof-prove-if core hypothesis decrease))
         (recursive (h1-propositions-propositional-proof-modus-ponens lib proved (cadr members)))
         (equation (h1-book-structure-container-case proof application cons-evidence))
         (branch (proof-rewritten-term equation)))
      (if (not (and (proof-is-call branch *proof-if*)
                    (equal (cddr branch) (list (list *library-car* alist) tail-call))))
          '(:failure "unproved" "")
        (proof-with-checked-results
            ((yes (h1-book-structure-projected-branch proof equation (cadr branch) t
                                                     (cadr goal) (car members)))
             (no (h1-book-structure-projected-branch proof equation (cadr branch) nil
                                                    (cadr goal) recursive))
             (on-cons (proof-proof-cases core (cadr branch) yes no)))
          (h1-propositions-propositional-proof-implies-from lib formula on-cons))))))

(defun h1-book-structure-projected-atom (proof formula application goal selector atom-evidence)
  (let ((core (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof))
        (recognizer (car goal)))
    (proof-with-checked-results
        ((empty (h1-tactics-prover-solve
                 proof (list recognizer *proof-false*)
                 (and (assoc-equal recognizer (proof-proof-definitions core))
                      (list recognizer))
                 160))
         (absent (h1-book-structure-container-case proof application atom-evidence))
         (right (proof-rewritten-term absent)))
      (if (not (equal right *proof-false*))
          '(:failure "unproved" "")
        (proof-with-checked-results
            ((refl (h1-propositions-propositional-proof-reflexive lib (cadr goal)))
             (rewritten (proof-proof-rewrite core refl absent '(1 2 1)))
             (constant (h1-tactics-prover-constant proof (list selector *proof-false*)))
             (value (proof-proof-chain core rewritten (list constant)))
             (result (h1-propositions-library-transport-argument lib empty value 1)))
          (h1-propositions-propositional-proof-implies-from lib formula result))))))

(defun h1-book-structure-projected-application (proof formula premise goal selector application)
  (let ((core (h1-tactics-prover-proof proof))
        (lib (h1-tactics-prover-library proof))
        (strip (cdr (assoc-equal selector *h1-book-structure-strip*))))
    (proof-with-checked-results ((parts (proof-list-of-length application 3)))
      (let ((key (cadr parts))
            (alist (caddr parts)))
        (if (or (not (equal (cadr premise) (list strip alist)))
                (proof-compound alist)
                (member-equal alist (h1-tactics-subterms key)))
            '(:failure "unproved" "")
          (let* ((test (list *proof-consp* alist))
                 (measure (list *library-count* alist))
                 (pairs (list (list alist (list *library-cdr* alist)))))
            (proof-with-checked-results
                ((cons-evidence (h1-arithmetic-proof-assume core test t))
                 (atom-evidence (h1-arithmetic-proof-assume core test nil))
                 (members (h1-book-structure-projected-members
                           proof premise goal selector strip alist cons-evidence))
                 (on-cons (h1-book-structure-projected-cons
                           proof formula application goal alist cons-evidence members))
                 (on-atom (h1-book-structure-projected-atom
                           proof formula application goal selector atom-evidence))
                 (step (proof-proof-cases core test on-cons on-atom))
                 (ordinal (descent-measure-ordinal lib measure)))
              (proof-proof-induct core ordinal step formula measure (list pairs)))))))))

(defun h1-book-structure-projected-association (proof formula)
  (if (not (proof-is-call formula *library-implies*))
      '(:failure "unproved" "")
    (proof-with-checked-results ((parts (proof-list-of-length formula 3)))
      (let* ((premise (cadr parts))
             (goal (caddr parts))
             (core (h1-tactics-prover-proof proof))
             (definitions (proof-proof-definitions core)))
        (cond
         ((or (not (assoc-equal (h1-tactics-call-head premise) definitions))
              (not (equal (len premise) 2)))
          '(:failure "unproved" ""))
         ((integerp goal) '(:failure "failure" ""))
         ((not (equal (len goal) 2))
          '(:failure "unproved" ""))
         (t
          (let* ((projection (cadr goal))
                 (selector (h1-tactics-call-head projection)))
            (if (not (assoc-equal selector *h1-book-structure-strip*))
                '(:failure "unproved" "")
              (proof-with-checked-results ((application (proof-term-at projection 1)))
                (if (member-equal (h1-tactics-call-head application) *h1-book-structure-lookup*)
                    (h1-book-structure-projected-application proof formula premise goal
                                                            selector application)
                  '(:failure "unproved" "")))))))))))

(defun h1-book-structure-nonempty-first-row-witness (proof test row equation)
  (proof-with-checked-results ((branch (proof-rewritten-term equation)))
    (if (not (proof-is-call branch *proof-if*))
        nil
      (proof-with-checked-results ((yes (proof-term-at branch 2)))
        (let ((empty (cadr branch)))
          (if (not (and (equal yes *proof-true*)
                        (member-equal empty (list (list *h1-book-structure-endp* row)
                                                  (list *h1-book-structure-atom* row)))))
              nil
            (let ((core (h1-tactics-prover-proof proof))
                  (lib (h1-tactics-prover-library proof))
                  (helper (concatenate 'string "H1-" (caddar empty) "-FALSE-CONSP")))
              (proof-with-checked-results
                  ((assumed (h1-arithmetic-proof-assume core empty t))
                   (result (h1-propositions-select-value lib equation assumed))
                   (truth (h1-tactics-prover-quoted-truth proof *proof-true*))
                   (positive (h1-propositions-proof-transport core truth result))
                   (denied (h1-arithmetic-proof-assume core test nil))
                   (contradiction (proof-proof-cut core positive denied))
                   (not-empty (proof-proof-front core contradiction (proof-neg empty)))
                   (axiom (library-library-axiom lib helper (list row))))
                (h1-propositions-propositional-proof-modus-ponens lib axiom not-empty)))))))))

(defun h1-book-structure-nonempty-first-row (proof root tests cons-evidence)
  (if (endp tests)
      '(:failure "unproved" "")
    (proof-with-checked-results ((signed (proof-list-of-length (car tests) 2)))
      (let* ((test (car signed))
             (core (h1-tactics-prover-proof proof)))
        (if (or (cadr signed)
                (not (assoc-equal (h1-tactics-call-head test) (proof-proof-definitions core)))
                (not (equal (cdr test) (list root))))
            (h1-book-structure-nonempty-first-row proof root (cdr tests) cons-evidence)
          (let ((equation (h1-book-structure-container-case proof test cons-evidence)))
            (if (h1-book-structure-unproved-p equation)
                (h1-book-structure-nonempty-first-row proof root (cdr tests) cons-evidence)
              (proof-with-checked-results
                  ((equation equation)
                   (witness (h1-book-structure-nonempty-first-row-witness
                             proof test (list *library-car* root) equation)))
                (if witness
                    witness
                  (h1-book-structure-nonempty-first-row proof root (cdr tests) cons-evidence))))))))))

(defun h1-book-structure-first-row-descent (proof variable actual tests)
  (let* ((core (h1-tactics-prover-proof proof))
         (lib (h1-tactics-prover-library proof))
         (row (list *library-car* variable)))
    (if (not (and (assoc-equal (h1-tactics-call-head actual) (proof-proof-definitions core))
                  (equal (cdr actual) (list variable))))
        '(:failure "unproved" "")
      (proof-with-checked-results
          ((cons-evidence (h1-arithmetic-proof-assume core (list *proof-consp* variable) t))
           (advancement (h1-book-structure-container-case proof actual cons-evidence))
           (result (proof-rewritten-term advancement)))
        (if (not (proof-is-call result *proof-cons*))
            '(:failure "unproved" "")
          (proof-with-checked-results ((head (proof-term-at result 1)))
            (if (not (equal head (list *library-cdr* row)))
                '(:failure "unproved" "")
              (proof-with-checked-results
                  ((refl (h1-propositions-propositional-proof-reflexive lib (list *library-car* actual)))
                   (first (h1-propositions-rewrite-value lib refl advancement))
                   (car-cons (library-library-axiom lib "CAR-CONS" (cdr result)))
                   (first (proof-proof-chain core first (list car-cons)))
                   (decrease (library-library-builtin lib 3 row))
                   (nonempty (h1-book-structure-nonempty-first-row proof variable tests cons-evidence))
                   (bound (proof-proof-discharge core decrease nonempty))
                   (symmetric (h1-propositions-proof-symmetric core first))
                   (step (proof-proof-rewrite core bound symmetric '(1 1 1))))
                (proof-proof-tidy core step)))))))))

(defun h1-book-structure-tuple-induction-cases (proof variable instances)
  (if (endp instances)
      nil
    (let* ((instance (car instances))
           (pairs (car instance))
           (actual (cadr (assoc-equal variable pairs))))
      (proof-with-checked-results
          ((descent (h1-book-structure-first-row-descent proof variable actual (cdr instance)))
           (rest (h1-book-structure-tuple-induction-cases proof variable (cdr instances))))
        (cons (list pairs descent) rest)))))

(defun h1-book-structure-tuple-induction-variables (proof formula variables instances openings)
  (cond
   ((endp variables) nil)
   ((proof-compound (car variables))
    (h1-book-structure-tuple-induction-variables proof formula (cdr variables) instances openings))
   (t
    (let* ((variable (car variables))
           (result
            (proof-with-checked-results
                ((cases (h1-book-structure-tuple-induction-cases proof variable instances)))
              (h1-tactics-prover-by-induction
               proof formula (list *library-count* (list *library-car* variable))
               cases openings nil 160 nil nil :none))))
      (if (h1-book-structure-unproved-p result)
          (h1-book-structure-tuple-induction-variables proof formula (cdr variables) instances openings)
        result)))))

(defun h1-book-structure-tuple-induction-terms (proof formula terms openings)
  (cond
   ((endp terms) '(:failure "unproved" ""))
   ((not (member-equal (h1-tactics-call-head (car terms)) openings))
    (h1-book-structure-tuple-induction-terms proof formula (cdr terms) openings))
   (t
    (proof-with-checked-results
        ((instances (h1-recursion-recursive-instances proof (car terms)))
         (result (and instances (h1-book-structure-tuple-induction-variables
                                 proof formula (cdar terms) instances openings))))
      (or result (h1-book-structure-tuple-induction-terms proof formula (cdr terms) openings))))))

(defun h1-book-structure-tuple-induction (proof formula)
  (let ((openings (h1-tactics-prover-functions-in proof formula)))
    (h1-book-structure-tuple-induction-terms proof formula
                                            (proof-unique (h1-tactics-subterms formula)) openings)))
