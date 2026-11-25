(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *b2-lexicographic-alpha* (proof-sym "ALPHORDER" "ACL2"))
(defconst *b2-lexicographic-symbol-less* (proof-sym "SYMBOL<" "ACL2"))
(defconst *b2-lexicographic-complex* (proof-sym "COMPLEX-RATIONALP" "ACL2"))
(defconst *b2-lexicographic-string* (proof-cl "STRINGP"))

(defconst *b2-lexicographic-atom-types*
  (list *library-rationalp* *b2-lexicographic-complex* *b2-tactics-characterp*
        *b2-lexicographic-string* *b2-tactics-symbolp*))

(defconst *b2-lexicographic-disjoint*
  (list (list *b2-lexicographic-complex* *library-rationalp*)
        (list *library-numberp* *b2-tactics-characterp*)
        (list *library-numberp* *b2-lexicographic-string*)
        (list *library-numberp* *b2-tactics-symbolp*)
        (list *b2-tactics-characterp* *b2-lexicographic-string*)
        (list *b2-tactics-characterp* *b2-tactics-symbolp*)
        (list *b2-lexicographic-string* *b2-tactics-symbolp*)))

(defun b2-lexicographic-type-name (symbol)
  (proof-with-checked-results ((name (proof-term-at symbol 2)))
    (if (stringp name)
        (text-lower name)
      '(:failure "failure" ""))))

(defun b2-lexicographic-type-fact (lib a b value disjoint)
  (proof-with-checked-results ((first (b2-lexicographic-type-name a))
                               (second (b2-lexicographic-type-name b)))
    (proof-proof-fact (library-library-proof lib)
                      (text-join (if disjoint "-not-" "-") (list first second))
                      (list (list *library-x* value)))))

(defun b2-lexicographic-exclude-number (lib value kind typed)
  (let ((proof (library-library-proof lib))
        (number (list *library-numberp* value)))
    (proof-with-checked-results
        ((implication (b2-lexicographic-type-fact lib *library-numberp* kind value t))
         (assumption (proof-proof-assume proof number t))
         (impossible (proof-proof-modus-ponens proof implication assumption))
         (cut (proof-proof-cut proof typed impossible)))
      (proof-proof-front proof cut (proof-neg number)))))

(defun b2-lexicographic-exclude-disjoint (lib value kinds known)
  (if (endp kinds)
      nil
    (let* ((proof (library-library-proof lib))
           (a (caar kinds))
           (b (cadar kinds))
           (typed-a (assoc-equal a known))
           (typed-b (assoc-equal b known)))
      (proof-with-checked-results
          ((step (cond
                  (typed-a
                   (proof-with-checked-results
                       ((fact (b2-lexicographic-type-fact lib a b value t)))
                     (proof-proof-modus-ponens proof fact (cdr typed-a))))
                  (typed-b
                   (let ((opposite (list a value)))
                     (proof-with-checked-results
                         ((fact (b2-lexicographic-type-fact lib a b value t))
                          (assumption (proof-proof-assume proof opposite t))
                          (clash (proof-proof-modus-ponens proof fact assumption))
                          (cut (proof-proof-cut proof (cdr typed-b) clash)))
                       (proof-proof-front proof cut (proof-neg opposite)))))
                  (t nil)))
           (rest (b2-lexicographic-exclude-disjoint lib value (cdr kinds) known)))
        (if step (cons step rest) rest)))))

(defun b2-lexicographic-exclude-numeric-type (lib value numeric denied)
  (let ((proof (library-library-proof lib)) (test (list numeric value)))
    (proof-with-checked-results
        ((fact (b2-lexicographic-type-fact lib numeric *library-numberp* value nil))
         (assumption (proof-proof-assume proof test t))
         (advertised (proof-proof-modus-ponens proof fact assumption))
         (cut (proof-proof-cut proof advertised denied)))
      (proof-proof-front proof cut (proof-neg test)))))

(defun b2-lexicographic-exclude-types (lib value kind assumed)
  (let ((numericp (or (equal kind *library-rationalp*) (equal kind *b2-lexicographic-complex*)))
        (proof (library-library-proof lib)))
    (proof-with-checked-results
        ((known (if numericp
                    (proof-with-checked-results
                        ((fact (b2-lexicographic-type-fact lib kind *library-numberp* value nil))
                         (step (proof-proof-modus-ponens proof fact assumed)))
                      (list (cons kind assumed) (cons *library-numberp* step)))
                  (list (cons kind assumed))))
         (disjoint (b2-lexicographic-exclude-disjoint lib value *b2-lexicographic-disjoint* known)))
      (if numericp
          disjoint
        (proof-with-checked-results
            ((denied (b2-lexicographic-exclude-number lib value kind assumed))
             (nonrational (b2-lexicographic-exclude-numeric-type lib value *library-rationalp* denied))
             (noncomplex (b2-lexicographic-exclude-numeric-type lib value *b2-lexicographic-complex* denied)))
          (append disjoint (list nonrational noncomplex)))))))

(defun b2-lexicographic-type-reply (kind evidence replies)
  (let ((entry (assoc-equal (list kind evidence) replies)))
    (if entry
        (cdr entry)
      (list :b2-lexicographic-atom-types kind evidence))))

(defun b2-lexicographic-type-request-p (result)
  (eq (car result) :b2-lexicographic-atom-types))

(defun b2-lexicographic-evidence-at (evidence literal)
  (let ((entry (assoc-equal literal evidence)))
    (if entry
        (cdr entry)
      '(:failure "tactic-rejected" ""))))

(defun b2-lexicographic-atom-types-noninteger (evidence kind lib value replies)
  (let* ((proof (library-library-proof lib))
         (integer (list *proof-integerp* value))
         (rational (list *library-rationalp* value)))
    (proof-with-checked-results
        ((known (b2-tactics-tactics-evidence lib evidence))
         (negative (b2-lexicographic-evidence-at known (proof-neg rational)))
         (implication (library-library-axiom lib "INTEGER-IMPLIES-RATIONAL" (list value)))
         (assumed (proof-proof-assume proof integer t))
         (yields-rational (proof-proof-modus-ponens proof implication assumed))
         (cut (proof-proof-cut proof yields-rational negative))
         (not-integer (proof-proof-front proof cut (proof-neg integer))))
      (b2-lexicographic-type-reply kind (append evidence (list not-integer)) replies))))

(defun b2-lexicographic-atom-types-rational (lib value kind evidence replies)
  (let ((proof (library-library-proof lib)) (integer (list *proof-integerp* value)))
    (proof-with-checked-results
        ((yes (proof-proof-assume proof integer t))
         (positive (b2-lexicographic-type-reply kind (append evidence (list yes)) replies)))
      (if (b2-lexicographic-type-request-p positive)
          positive
        (proof-with-checked-results
            ((no (proof-proof-assume proof integer nil))
             (negative (b2-lexicographic-type-reply kind (append evidence (list no)) replies)))
          (if (b2-lexicographic-type-request-p negative)
              negative
            (proof-proof-cases proof integer positive negative)))))))

(defun b2-lexicographic-atom-types-classify (kinds previous lib value replies)
  (if (endp kinds)
      (b2-lexicographic-atom-types-noninteger previous nil lib value replies)
    (let* ((kind (car kinds)) (test (list kind value)) (proof (library-library-proof lib)))
      (proof-with-checked-results
          ((yes (proof-proof-assume proof test t))
           (no (proof-proof-assume proof test nil))
           (excluded (b2-lexicographic-exclude-types lib value kind yes))
           (evidence (append previous (cons yes excluded)))
           (positive (if (equal kind *library-rationalp*)
                         (b2-lexicographic-atom-types-rational lib value kind evidence replies)
                       (b2-lexicographic-atom-types-noninteger evidence kind lib value replies))))
        (if (b2-lexicographic-type-request-p positive)
            positive
          (proof-with-checked-results
              ((negative (b2-lexicographic-atom-types-classify
                          (cdr kinds) (append previous (list no)) lib value replies)))
            (if (b2-lexicographic-type-request-p negative)
                negative
              (proof-proof-cases proof test positive negative))))))))

(defun b2-lexicographic-atom-types (lib value replies)
  (b2-lexicographic-atom-types-classify *b2-lexicographic-atom-types* nil lib value replies))

(defun b2-lexicographic-atom-comparison-first-kind-compare
    (kind-b typed-b lib kind-a typed-a base a b formula unfold)
  (let ((evidence (append base typed-a typed-b)) (proof (library-library-proof lib)))
    (if (and (equal kind-a *b2-tactics-symbolp*) (equal kind-b *b2-tactics-symbolp*))
        (let ((same (proof-eq a b)))
          (proof-with-checked-results
              ((yes (proof-proof-assume proof same t))
               (no (proof-proof-assume proof same nil))
               (reflexive (proof-proof-fact proof (proof-sym "SYMBOL<-IRREFLEXIVE" "ACL2")
                                            (list (list *library-x* b))))
               (known (b2-tactics-tactics-evidence lib evidence))
               (typed (b2-lexicographic-evidence-at known (list *b2-tactics-symbolp* b)))
               (reflexive (proof-proof-modus-ponens proof reflexive typed))
               (symmetric (proof-proof-symmetric proof yes))
               (reflexive (proof-proof-rewrite proof reflexive symmetric '(1 1 2)))
               (reflexive (proof-proof-tidy proof reflexive))
               (left (b2-tactics-tactics-solve lib formula (append evidence (list yes reflexive))
                                              unfold nil 0 nil))
               (right (b2-tactics-tactics-solve lib formula (append evidence (list no))
                                               unfold nil 0 nil)))
            (proof-proof-cases proof same left right)))
      (b2-tactics-tactics-solve lib formula evidence unfold nil 0 nil))))

(defun b2-lexicographic-compare-second-type-reply (lib kind-a typed-a base a b formula unfold replies)
  (proof-with-checked-results ((step (b2-lexicographic-atom-types lib b replies)))
    (if (b2-lexicographic-type-request-p step)
        (proof-with-checked-results
            ((reply (b2-lexicographic-atom-comparison-first-kind-compare
                     (cadr step) (caddr step) lib kind-a typed-a base a b formula unfold)))
          (list :b2-lexicographic-replies (table-put replies (cdr step) reply)))
      step)))

(defun b2-lexicographic-compare-second-types (n lib kind-a typed-a base a b formula unfold pending)
  (declare (xargs :measure (nfix n)))
  (cond ((not (eq (car pending) :b2-lexicographic-replies)) pending)
        ((zp n) '(:failure "fuel" "b2-lexicographic-compare-second-types"))
        (t (b2-lexicographic-compare-second-types
            (1- n) lib kind-a typed-a base a b formula unfold
            (b2-lexicographic-compare-second-type-reply
             lib kind-a typed-a base a b formula unfold (cadr pending))))))

(defun b2-lexicographic-atom-comparison-first-kind
    (kind-a typed-a lib base a b formula unfold)
  (b2-lexicographic-compare-second-types
   1000000 lib kind-a typed-a base a b formula unfold '(:b2-lexicographic-replies nil)))

(defun b2-lexicographic-compare-first-type-reply (lib base a b formula unfold replies)
  (proof-with-checked-results ((step (b2-lexicographic-atom-types lib a replies)))
    (if (b2-lexicographic-type-request-p step)
        (proof-with-checked-results
            ((reply (b2-lexicographic-atom-comparison-first-kind
                     (cadr step) (caddr step) lib base a b formula unfold)))
          (list :b2-lexicographic-replies (table-put replies (cdr step) reply)))
      step)))

(defun b2-lexicographic-compare-first-types (n lib base a b formula unfold pending)
  (declare (xargs :measure (nfix n)))
  (cond ((not (eq (car pending) :b2-lexicographic-replies)) pending)
        ((zp n) '(:failure "fuel" "b2-lexicographic-compare-first-types"))
        (t (b2-lexicographic-compare-first-types
            (1- n) lib base a b formula unfold
            (b2-lexicographic-compare-first-type-reply lib base a b formula unfold (cadr pending))))))

(defun b2-lexicographic-atom-comparison (lib formula base)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (first (cadr parts))
       (args (proof-list-of-length first 3)))
    (b2-lexicographic-compare-first-types
     1000000 lib base (cadr args) (caddr args) formula
     (list first (caddr parts) *b2-lexicographic-alpha*) '(:b2-lexicographic-replies nil))))

(defun b2-lexicographic-tree-branches
    (lib formula measure x yes-x yes-y same-head unfold substitutions index)
  (if (endp substitutions)
      nil
    (let ((proof (library-library-proof lib)))
      (proof-with-checked-results
          ((builtin (library-library-builtin lib (- 3 index) x))
           (decrease (proof-proof-discharge proof builtin yes-x))
           (hypothesis (b2-tactics-tactics-induction-hypothesis
                        lib formula measure (car substitutions) decrease))
           (same (proof-proof-assume proof same-head (equal index 0)))
           (branch (b2-tactics-tactics-solve lib formula (list yes-x yes-y same)
                                            unfold (list hypothesis) 0 nil))
           (rest (b2-lexicographic-tree-branches
                  lib formula measure x yes-x yes-y same-head unfold (cdr substitutions) (1+ index))))
        (cons branch rest)))))

(defun b2-lexicographic-lexorder-equivalence (lib formula)
  (proof-with-checked-results
      ((parts (proof-list-of-length formula 3))
       (fast (cadr parts))
       (args (proof-list-of-length fast 3)))
    (let* ((proof (library-library-proof lib))
           (x (cadr args)) (y (caddr args))
           (left (list *proof-consp* x)) (right (list *proof-consp* y))
           (measure (list *library-count* x))
           (substitutions (list (list (list x (list *library-cdr* x))
                                      (list y (list *library-cdr* y)))
                                (list (list x (list *library-car* x))
                                      (list y (list *library-car* y))))))
      (proof-with-checked-results
          ((yes-x (proof-proof-assume proof left t))
           (no-x (proof-proof-assume proof left nil))
           (yes-y (proof-proof-assume proof right t))
           (no-y (proof-proof-assume proof right nil))
           (same-head (proof-eq (list *library-car* x) (list *library-car* y)))
           (unfold (list fast (caddr parts)))
           (branches (b2-lexicographic-tree-branches
                      lib formula measure x yes-x yes-y same-head unfold substitutions 0))
           (both-cons (proof-proof-cases proof same-head (car branches) (cadr branches)))
           (mixed (b2-tactics-tactics-solve lib formula (list yes-x no-y) unfold nil 0 nil))
           (cons-x (proof-proof-cases proof right both-cons mixed))
           (mixed (b2-tactics-tactics-solve lib formula (list no-x yes-y) unfold nil 0 nil))
           (atoms (b2-lexicographic-atom-comparison lib formula (list no-x no-y)))
           (atom-x (proof-proof-cases proof right mixed atoms))
           (ordinal (library-library-builtin lib 1 x))
           (cases (proof-proof-cases proof left cons-x atom-x)))
        (proof-proof-induct proof ordinal cases formula measure substitutions)))))
