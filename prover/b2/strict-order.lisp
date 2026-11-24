(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defmacro b2-strict-order-declare-events ()
  '(progn

(defconst *b2-strict-order-strict* (proof-sym "<<" "ACL2"))
(defconst *b2-strict-order-lex* (proof-sym "LEXORDER" "ACL2"))
(defconst *b2-strict-order-total* (proof-sym "LEXORDER-TOTAL" "ACL2"))
(defconst *b2-strict-order-anti* (proof-sym "LEXORDER-ANTI-SYMMETRIC" "ACL2"))
(defconst *b2-strict-order-trans* (proof-sym "LEXORDER-TRANSITIVE" "ACL2"))

(defconst *b2-strict-order-order-theorems*
  (list (proof-sym "<<-ASYMMETRIC" "ACL2")
        (proof-sym "<<-IMPLIES-LEXORDER" "ACL2")
        (proof-sym "<<-IRREFLEXIVE" "ACL2")
        (proof-sym "<<-TRANSITIVE" "ACL2")
        (proof-sym "<<-TRICHOTOMY" "ACL2")))

(defun b2-strict-order-flipped-distinct (library a b evidence)
  (let ((proof (library-library-proof library))
        (target (proof-eq b a)))
    (proof-with-checked-results
        ((assumption (proof-proof-assume proof target t))
         (to-cut (proof-proof-symmetric proof assumption))
         (cut (proof-proof-cut proof to-cut evidence)))
      (proof-proof-front proof cut (proof-neg target)))))

(defun b2-strict-order-step-argument (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun b2-strict-order-pieces (library evidence)
  (let ((proof (library-library-proof library)))
    (proof-with-checked-results
        ((term (if evidence (proof-step-first evidence)
                 '(:failure "failure" "")))
         (equation (b2-tactics-tactics-normalize
                    library term nil (list term) nil 1500 nil))
         (equation (or equation
                       '(:failure "failure" "")))
         (opened (proof-proof-rewrite proof evidence equation '(1)))
         (opened (proof-proof-tidy proof opened)))
      (proof-proof-conjunct proof opened))))

(defun b2-strict-order-strict-order-consequent (premise library name target)
  (let ((proof (library-library-proof library)))
    (cond
     ((equal name (proof-sym "<<-IMPLIES-LEXORDER" "ACL2"))
      (proof-with-checked-results ((parts (b2-strict-order-pieces library premise)))
        (car parts)))
     ((equal name (proof-sym "<<-ASYMMETRIC" "ACL2"))
      (proof-with-checked-results
          ((parts (b2-strict-order-pieces library premise))
           (first (car parts))
           (distinct (cadr parts))
           (reverse-term (proof-term-at target 1))
           (reverse-step (proof-proof-assume proof reverse-term t))
           (other (b2-strict-order-pieces library reverse-step))
           (same-term (b2-strict-order-step-argument distinct 1))
           (same (b2-tactics-tactics-use-fact
                  library *b2-strict-order-anti* same-term (list first (car other))
                  nil nil 0 nil))
           (cut (proof-proof-cut proof same distinct)))
        (proof-proof-front proof cut target)))
     ((equal name (proof-sym "<<-TRANSITIVE" "ACL2"))
      (proof-with-checked-results
          ((conjuncts (proof-proof-conjunct proof premise))
           (left (b2-strict-order-pieces library (car conjuncts)))
           (xy (car left))
           (distinct (cadr left))
           (right (b2-strict-order-pieces library (cadr conjuncts)))
           (yz (car right))
           (xy-term (proof-step-first xy))
           (xy-parts (proof-list-of-length xy-term 3))
           (x (cadr xy-parts))
           (y (caddr xy-parts))
           (z (b2-strict-order-step-argument yz 2))
           (xz (proof-proof-fact proof *b2-strict-order-trans*
                                 (list (list *library-x* x)
                                       (list *library-y* y)
                                       (list *library-z* z))))
           (condition (b2-strict-order-step-argument xz 1))
           (evidence (b2-tactics-tactics-solve library condition (list xy yz)
                                             nil nil 0 nil))
           (xz (proof-proof-modus-ponens proof xz evidence))
           (same (proof-eq x z))
           (assumption (proof-proof-assume proof same t))
           (symmetric (proof-proof-symmetric proof assumption))
           (back (proof-proof-rewrite proof yz symmetric '(1 2)))
           (back (proof-proof-tidy proof back))
           (distinct-term (b2-strict-order-step-argument distinct 1))
           (equality (b2-tactics-tactics-use-fact
                      library *b2-strict-order-anti* distinct-term (list xy back)
                      nil nil 0 nil))
           (cut (proof-proof-cut proof equality distinct))
           (different (proof-proof-front proof cut (proof-neg same))))
        (b2-tactics-tactics-solve library target (list xz different)
                                 (list target) nil 0 nil)))
     (t
      (proof-with-checked-results
          ((conjuncts (proof-proof-conjunct proof premise))
           (not-reverse (car conjuncts))
           (distinct (cadr conjuncts))
           (parts (proof-list-of-length target 3))
           (x (cadr parts))
           (y (caddr parts))
           (nonstrict (list *b2-strict-order-lex* x y))
           (yes (proof-proof-assume proof nonstrict t))
           (no (proof-proof-assume proof nonstrict nil))
           (direct (b2-tactics-tactics-solve library target (list yes distinct)
                                           (list target) nil 0 nil))
           (total (proof-proof-fact proof *b2-strict-order-total*
                                    (list (list *library-x* x) (list *library-y* y))))
           (opposite (proof-proof-prove-if proof total no))
           (reverse-term (b2-strict-order-step-argument not-reverse 1))
           (different (b2-strict-order-flipped-distinct library x y distinct))
           (strict-reverse (b2-tactics-tactics-solve
                            library reverse-term (list opposite different)
                            (list reverse-term) nil 0 nil))
           (contra (proof-proof-cut proof strict-reverse not-reverse))
           (impossible (proof-proof-subsume proof contra
                                           (cons target (proof-step-clause contra)))))
        (proof-proof-cases proof nonstrict direct impossible))))))

(defun b2-strict-order-strict-order (library name formula)
  (if (equal name (proof-sym "<<-IRREFLEXIVE" "ACL2"))
      (proof-with-checked-results
          ((term (proof-term-at formula 1))
           (argument (proof-term-at term 1))
           (reflexive (proof-proof-fact (library-library-proof library)
                                       (proof-sym "LEXORDER-REFLEXIVE" "ACL2")
                                       (list (list *library-x* argument)))))
        (b2-tactics-tactics-solve library formula (list reflexive)
                                 (list term) nil 0 nil))
    (proof-with-checked-results
        ((parts (proof-list-of-length formula 3))
         (condition (cadr parts))
         (target (caddr parts))
         (request (b2-tactics-tactics-implication library condition target nil))
         (reply (b2-strict-order-strict-order-consequent
                 (cadddr (car request)) (cdr request) name target))
         (result (b2-tactics-tactics-implication library condition target
                                                (cons reply (cdr request)))))
      (car result))))
))
