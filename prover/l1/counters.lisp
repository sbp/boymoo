(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defconst *l1-counters-nfix* (proof-sym "NFIX" "ACL2"))
(defconst *l1-counters-ten* (proof-quote 10))

(defun l1-counters-strip-nfix (term)
  (declare (xargs :measure (acl2-count term)))
  (cond
   ((proof-is-call term *l1-counters-nfix*)
    (if (consp (cdr term))
        (l1-counters-strip-nfix (cadr term))
      '(:failure "failure" "")))
   ((proof-is-call term *proof-plus*)
    (if (not (consp (cdr term)))
        '(:failure "failure" "")
      (proof-with-checked-results ((left (l1-counters-strip-nfix (cadr term))))
        (if (not (consp (cddr term)))
            '(:failure "failure" "")
          (proof-with-checked-results ((right (l1-counters-strip-nfix (caddr term))))
            (list *proof-plus* left right))))))
   (t term)))

(defun l1-counters-counter-measure-bound (bound negative formals)
  (and (proof-is-call negative *proof-minus*)
       (proof-with-checked-results
           ((operand (proof-term-at negative 1))
            (counter (l1-counters-strip-nfix operand)))
         (and (member-equal counter formals) (list *library-gap* bound counter)))))

(defun l1-counters-counter-measure (stored formals)
  (proof-with-checked-results ((difference (l1-counters-strip-nfix stored)))
    (and (proof-is-call difference *proof-plus*)
         (let ((left (cadr difference))
               (right (caddr difference)))
           (proof-with-checked-results
               ((measure (l1-counters-counter-measure-bound left right formals)))
             (or measure (l1-counters-counter-measure-bound right left formals)))))))

(defund l1-counters-integer-evidence (library term hypotheses)
  (proof-with-checked-results ((found (descent-hypotheses-find hypotheses (library-integer term))))
    (if (car found)
        found
      (proof-with-checked-results
          ((natural (descent-hypotheses-find (cdr found) (list *library-natp* term))))
        (if (not (car natural))
            natural
          (proof-with-checked-results
              ((step (library-library-cite library "NATURAL-INTEGER"
                                           (list term) (list (car natural)))))
            (cons step (cdr natural))))))))

(mutual-recursion
 (defun l1-counters-integer-in-scope (library term hypotheses)
   (declare (xargs :measure (acl2-count term)))
   (proof-with-checked-results ((found (l1-counters-integer-evidence library term hypotheses)))
     (cond
      ((car found) found)
      ((and (consp term)
            (or (proof-is-call term *proof-plus*)
                (proof-is-call term *proof-minus*)
                (proof-is-call term *proof-times*)))
       (proof-with-checked-results
           ((integers (l1-counters-integer-in-scope-arguments library (cdr term) (cdr found)))
            (step (library-library-type-of library term (car integers))))
         (cons step (cdr integers))))
      (t (proof-with-checked-results ((step (library-library-type-of library term nil)))
           (cons step (cdr found)))))))
 (defun l1-counters-integer-in-scope-arguments (library terms hypotheses)
   (declare (xargs :measure (acl2-count terms)))
   (if (endp terms)
       (cons nil hypotheses)
     (proof-with-checked-results
         ((first (l1-counters-integer-in-scope library (car terms) hypotheses))
          (rest (l1-counters-integer-in-scope-arguments library (cdr terms) (cdr first))))
       (cons (cons (car first) (car rest)) (cdr rest))))))

(defun l1-counters-multiply-advances (library factor old old-integer old-positive)
  (let ((proof (library-library-proof library)))
    (if (equal factor *l1-counters-ten*)
        (library-library-cite library "TENFOLD-LARGER" (list old)
                              (list old-integer old-positive))
      (proof-with-checked-results
          ((factor-value (proof-term-at factor 1))
           (rest (proof-quote (- factor-value 1)))
           (difference (list *proof-times* rest old))
           (rest-rational (library-library-rational library rest nil))
           (old-rational (library-library-rational library old (list old-integer)))
           (rest-positive (proof-proof-prove proof (library-positive rest) nil nil))
           (positive-difference (library-library-cite library "POSITIVE-PRODUCT" (list rest old)
                                                       (list rest-rational old-rational
                                                             rest-positive old-positive)))
           (step (library-library-less-from-difference library old (library-plus old difference)
                                                        positive-difference (list old-integer)))
           (expansion (library-library-axiom library "COMMUTATIVITY-OF-*" (list factor old)))
           (factor-sum (proof-proof-compute proof (library-plus *proof-one* rest) factor-value))
           (factor-sum (proof-proof-symmetric proof factor-sum))
           (expansion (proof-proof-rewrite proof expansion factor-sum '(1 2 2)))
           (distributed (library-library-axiom library "DISTRIBUTIVITY" (list old *proof-one* rest)))
           (expansion (proof-proof-chain proof expansion (list distributed)))
           (fix (proof-sym "FIX" "ACL2"))
           (number (library-library-number library old (list old-integer)))
           (commuted (library-library-axiom library "COMMUTATIVITY-OF-*" (list old *proof-one*)))
           (identity (library-library-axiom library "UNICITY-OF-1" (list old)))
           (fixed (proof-proof-simplify proof (list fix old) (list number) (list fix)))
           (one (proof-proof-chain proof commuted (list identity fixed)))
           (expansion (proof-proof-rewrite proof expansion one '(1 2 1)))
           (commuted-rest (library-library-axiom library "COMMUTATIVITY-OF-*" (list old rest)))
           (expansion (proof-proof-rewrite proof expansion commuted-rest '(1 2 2))))
        (library-library-transport-argument library step expansion 2)))))

(defun l1-counters-advance-sum (library old new increment base old-integer)
  (and (equal base old)
       (proof-is-call increment *proof-quote*)
       (proof-with-checked-results ((value (proof-term-at increment 1)))
         (and (or (eq value t) (and (integerp value) (< 0 value)))
              (proof-with-checked-results
                  ((positive (proof-proof-prove (library-library-proof library)
                                               (library-positive increment) nil nil)))
                (library-library-less-from-difference library old new
                                                      positive (list old-integer)))))))

(defun l1-counters-advance-product (library old new factor base old-integer old-positive)
  (and (equal base old)
       (proof-is-call factor *proof-quote*)
       (proof-with-checked-results ((value (proof-term-at factor 1)))
         (and (integerp value) (< 1 value)
              (proof-with-checked-results
                  ((step (l1-counters-multiply-advances library factor old old-integer old-positive))
                   (result (proof-rewritten-term step)))
                (if (equal result new)
                    step
                  (proof-with-checked-results
                      ((commuted (library-library-axiom library "COMMUTATIVITY-OF-*"
                                                        (list factor old))))
                    (proof-proof-rewrite (library-library-proof library) step commuted '(1 2)))))))))

(defun l1-counters-advance (library old new old-integer hypotheses)
  (cond
   ((proof-is-call new *proof-plus*)
    (proof-with-checked-results
        ((parts (proof-list-of-length new 3))
         (left (cadr parts))
         (right (caddr parts))
         (first (l1-counters-advance-sum library old new left right old-integer))
         (step (or first (l1-counters-advance-sum library old new right left old-integer))))
      (cons step hypotheses)))
   ((proof-is-call new *proof-times*)
    (proof-with-checked-results
        ((old-positive (descent-hypotheses-find hypotheses (library-positive old))))
      (if (not (car old-positive))
          old-positive
        (proof-with-checked-results
            ((parts (proof-list-of-length new 3))
             (left (cadr parts))
             (right (caddr parts))
             (first (l1-counters-advance-product library old new left right old-integer
                                                 (car old-positive)))
             (step (or first (l1-counters-advance-product library old new right left old-integer
                                                         (car old-positive)))))
          (cons step (cdr old-positive))))))
   (t (cons nil hypotheses))))

(defun l1-counters-below-bound (library old bound old-integer hypotheses)
  (proof-with-checked-results ((below (descent-hypotheses-find hypotheses (library-lt old bound))))
    (if (or (car below) (not (proof-is-call bound *proof-plus*)))
        below
      (proof-with-checked-results ((addend (proof-term-at bound 1)))
        (if (not (equal addend *proof-one*))
            below
          (proof-with-checked-results
              ((upper (proof-term-at bound 2))
               (at-most (descent-hypotheses-find (cdr below) (proof-neg (library-lt upper old)))))
            (if (not (car at-most))
                at-most
              (proof-with-checked-results
                  ((upper-integer (l1-counters-integer-in-scope library upper (cdr at-most)))
                   (step (library-library-cite library "LESS-THAN-NEXT" (list upper old)
                                               (list (car upper-integer) old-integer (car at-most)))))
                (cons step (cdr upper-integer))))))))))

(defun l1-counters-counter-decrease-gap (library child parent hypotheses)
  (proof-with-checked-results
      ((parts (proof-list-of-length parent 3))
       (bound (cadr parts))
       (old (caddr parts))
       (new (proof-term-at child 2))
       (old-integer (l1-counters-integer-in-scope library old hypotheses))
       (advances (l1-counters-advance library old new (car old-integer) (cdr old-integer))))
    (if (not (car advances))
        advances
      (proof-with-checked-results
          ((below (l1-counters-below-bound library old bound (car old-integer) (cdr advances))))
        (if (not (car below))
            below
          (proof-with-checked-results
              ((bound-integer (l1-counters-integer-in-scope library bound (cdr below)))
               (new-integer (l1-counters-integer-in-scope library new (cdr bound-integer)))
               (step (library-library-cite library "GAP-DECREASE" (list bound old new)
                                           (list (car bound-integer) (car old-integer)
                                                 (car new-integer) (car below) (car advances)))))
            (cons step (cdr new-integer))))))))

(defun l1-counters-counter-decrease (library goal hypotheses)
  (if (not (and hypotheses (proof-is-call goal *proof-ordinal-less*)))
      (cons nil hypotheses)
    (proof-with-checked-results
        ((parts (proof-list-of-length goal 3))
         (child (cadr parts))
         (parent (caddr parts)))
      (if (not (and (proof-is-call child *library-gap*) (proof-is-call parent *library-gap*)))
          (cons nil hypotheses)
        (proof-with-checked-results
            ((child-bound (proof-term-at child 1))
             (parent-bound (proof-term-at parent 1)))
          (if (equal child-bound parent-bound)
              (l1-counters-counter-decrease-gap library child parent hypotheses)
            (cons nil hypotheses)))))))
