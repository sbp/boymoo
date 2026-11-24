(in-package "BOYMOO-PROVER")

(set-verify-guards-eagerness 0)

(defconst *h2-ranges-book-nfix* (proof-sym "NFIX" "ACL2"))

(defun h2-ranges-first-at (step index)
  (proof-with-checked-results ((literal (proof-step-first step)))
    (proof-term-at literal index)))

(defun h2-ranges-inapplicable-p (value)
  (and (failure-p value) (equal (cadr value) "value")))

(defun h2-ranges-conjuncts-walk (n base evidence)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      '(:failure "Fuel" "h2-ranges-conjuncts-walk")
    (proof-with-checked-results ((literal (proof-step-first evidence)))
      (if (proof-is-call literal *proof-if*)
          (proof-with-checked-results ((otherwise (proof-term-at literal 3)))
            (if (equal otherwise *proof-false*)
                (proof-with-checked-results
                    ((parts (proof-proof-conjunct base evidence))
                     (rest (h2-ranges-conjuncts-walk (1- n) base (cadr parts))))
                  (cons (car parts) rest))
              (list evidence)))
        (list evidence)))))

(defun h2-ranges-conjuncts (proof evidence)
  (h2-ranges-conjuncts-walk 1000000 (h2-book-logic-proof proof) evidence))

(defun h2-ranges-difference-positive (proof lower upper comparison evidence)
  (let* ((lib (h2-search-search-library proof))
         (base (library-library-proof lib)))
    (proof-with-checked-results
        ((equation (library-library-comparison lib lower upper evidence)))
      (proof-proof-rewrite base comparison equation '(1)))))

(defun h2-ranges-positive-span-finish
    (proof span step facts lower upper distance gap strict lower-type upper-type)
  (let* ((lib (h2-search-search-library proof))
         (base (library-library-proof lib))
         (alignment (library-library-linear-equal lib gap span facts))
         (extended (and strict (h2-ranges-inapplicable-p alignment)))
         (alignment (if extended
                        (library-library-linear-equal
                         lib (library-plus *proof-one* distance) span facts)
                      alignment)))
    (cond
     ((h2-ranges-inapplicable-p alignment) nil)
     ((failure-p alignment) alignment)
     (strict
      (proof-with-checked-results
          ((positive (h2-ranges-difference-positive proof lower upper step facts))
           (positive
            (if extended
                (proof-with-checked-results
                    ((one (proof-proof-prove base (library-positive *proof-one*) nil nil)))
                  (library-library-cite lib "POSITIVE-SUM" (list *proof-one* distance)
                                        (list one positive)))
              positive)))
        (proof-proof-rewrite base positive alignment '(1 2))))
     (t
      (proof-with-checked-results
          ((successor (library-library-cite lib "SUCCESSOR-LARGER" (list upper)
                                            (list upper-type)))
           (next-upper (h2-ranges-first-at successor 2))
           (next-type (library-library-type-of lib next-upper facts))
           (comparison (library-library-cite lib "WEAK-THEN-LESS"
                                             (list lower upper next-upper)
                                             (list lower-type upper-type next-type
                                                   step successor)))
           (positive-gap (h2-ranges-difference-positive proof lower next-upper comparison facts))
           (value (h2-ranges-first-at positive-gap 2))
           (delta (library-library-linear-equal lib value gap facts))
           (positive (proof-proof-rewrite base positive-gap delta '(1 2))))
        (proof-proof-rewrite base positive alignment '(1 2)))))))

(defun h2-ranges-positive-span-match (proof span step facts comparison strict)
  (proof-with-checked-results
      ((endpoints (proof-list-of-length (cdr comparison) 2)))
    (let* ((lower (if strict (car endpoints) (cadr endpoints)))
           (upper (if strict (cadr endpoints) (car endpoints)))
           (distance (library-diff upper lower))
           (gap (if strict distance (library-plus *proof-one* distance)))
           (lib (h2-search-search-library proof))
           (lower-type (library-library-type-of lib lower facts)))
      (cond
       ((h2-ranges-inapplicable-p lower-type) nil)
       ((failure-p lower-type) lower-type)
       (t (let ((upper-type (library-library-type-of lib upper facts)))
            (cond ((h2-ranges-inapplicable-p upper-type) nil)
                  ((failure-p upper-type) upper-type)
                  (t (h2-ranges-positive-span-finish
                      proof span step facts lower upper distance gap strict
                      lower-type upper-type)))))))))

(defun h2-ranges-positive-span-scan (proof span remaining facts)
  (if (endp remaining)
      nil
    (let ((step (car remaining)))
      (proof-with-checked-results
          ((literal (proof-step-first step))
           (match (cond
                   ((proof-is-call literal *proof-less*)
                    (h2-ranges-positive-span-match proof span step facts literal t))
                   ((proof-is-call literal *proof-not*)
                    (proof-with-checked-results ((inner (proof-term-at literal 1)))
                      (if (proof-is-call inner *proof-less*)
                          (h2-ranges-positive-span-match proof span step facts inner nil)
                        nil)))
                   (t nil))))
        (or match (h2-ranges-positive-span-scan proof span (cdr remaining) facts))))))

(defun h2-ranges-positive-span (proof span facts)
  (h2-ranges-positive-span-scan proof span facts facts))

(defun h2-ranges-numeric-fixer (proof term)
  (let ((base (h2-book-logic-proof proof)))
    (proof-with-checked-results
        ((raw (proof-proof-unfold base term))
         (argument (proof-term-at term 1))
         (fixed (proof-proof-unfold base (list *library-nfix* argument)))
         (natural (proof-proof-unfold base (list *library-natp* argument)))
         (fixed (proof-proof-rewrite base fixed natural '(1 2 1)))
         (inverse (proof-proof-symmetric base fixed)))
      (proof-proof-chain base raw (list inverse)))))

(defun h2-ranges-assumption-facts (proof assumptions)
  (if (endp assumptions)
      nil
    (proof-with-checked-results
        ((pieces (h2-ranges-conjuncts proof (car assumptions)))
         (rest (h2-ranges-assumption-facts proof (cdr assumptions))))
      (append pieces rest))))

(defun h2-ranges-affine-decrease-nfix (proof smaller measure child parent facts active parent-type kind)
  (let* ((lib (h2-search-search-library proof))
         (base (library-library-proof lib)))
    (proof-with-checked-results
        ((adjacent (proof-proof-prove base (library-positive *proof-one*) nil nil))
         (strict (library-library-less-from-difference lib child parent adjacent facts))
         (child-type (library-library-type-of lib child facts))
         (descent (library-library-cite lib "NFIX-DECREASE" (list child parent)
                                        (list child-type parent-type active strict))))
      (if (equal kind *h2-ranges-book-nfix*)
          (proof-with-checked-results
              ((equation (h2-ranges-numeric-fixer proof smaller))
               (descent (library-library-transport-argument lib descent equation 1))
               (equation (h2-ranges-numeric-fixer proof measure)))
            (library-library-transport-argument lib descent equation 2))
        descent))))

(defun h2-ranges-affine-decrease-count (proof parent parent-type active step)
  (let* ((lib (h2-search-search-library proof))
         (base (library-library-proof lib))
         (stopped (list (proof-sym "ZP" "ACL2") parent)))
    (proof-with-checked-results
        ((opening (proof-proof-unfold base stopped))
         (view (h2-book-logic-select-body proof opening parent-type))
         (literal (proof-step-first active))
         (opening (proof-proof-unfold base (proof-neg literal)))
         (false-test (h2-book-logic-select-body proof opening active))
         (not-nil (proof-proof-not-nil base))
         (equation (proof-proof-chain base view (list false-test)))
         (running (library-library-transport-argument lib not-nil equation 1))
         (builtin (library-library-builtin lib 9 parent))
         (decrease (proof-proof-discharge base builtin running)))
      (proof-proof-rewrite base decrease step '(1 1 1)))))

(defun h2-ranges-affine-decrease-span (proof smaller measure child parent facts kind)
  (let* ((lib (h2-search-search-library proof))
         (predecessor (library-plus *proof-neg-one* parent))
         (step (library-library-linear-equal lib predecessor child facts)))
    (cond
     ((h2-ranges-inapplicable-p step) nil)
     ((failure-p step) step)
     (t (proof-with-checked-results ((active (h2-ranges-positive-span proof parent facts)))
          (if active
              (proof-with-checked-results ((parent-type (library-library-type-of lib parent facts)))
                (if (equal kind *library-count*)
                    (h2-ranges-affine-decrease-count proof parent parent-type active step)
                  (h2-ranges-affine-decrease-nfix proof smaller measure child parent
                                                  facts active parent-type kind)))
            nil))))))

(defun h2-ranges-affine-decrease (proof goal assumptions)
  (if (integerp goal)
      '(:failure "failure" "")
    (proof-with-checked-results ((parts (proof-list-of-length (cdr goal) 2)))
      (let ((smaller (car parts))
            (measure (cadr parts)))
        (proof-with-checked-results
            ((kind (if (or (consp measure) (null measure))
                       (proof-term-at measure 0)
                     nil)))
          (if (and (member-equal kind (list *h2-ranges-book-nfix* *library-nfix* *library-count*))
                   (proof-is-call smaller kind))
              (proof-with-checked-results
                  ((parent (proof-term-at measure 1))
                   (child (proof-term-at smaller 1)))
                (if (proof-is-call parent *proof-plus*)
                    (proof-with-checked-results ((facts (h2-ranges-assumption-facts proof assumptions)))
                      (h2-ranges-affine-decrease-span proof smaller measure child parent facts kind))
                  nil))
            nil))))))
