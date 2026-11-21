; Cases of the comparison of review/termination/README.md: definitions
; whose class is known before the comparison runs.  review/termination/
; run.sh certifies this book into build/termination/, exports it with
; export/book.sh and compares it as it compares every book; cases.txt
; gives the class that each definition must have.

(in-package "ACL2")

; A clause that repeats an earlier one.  With the ruler-extenders :all,
; the walk records the call (bm-repeat (cdr x)) twice under the same
; rulers, with the call (bm-repeat (cddr x)) between them.  The
; specification leaves out the second copy and ACL2 the first, so both
; have the same clauses in another order.

(defun bm-repeat (x)
  (declare (xargs :ruler-extenders :all))
  (if (consp x)
      (cons (bm-repeat (cdr x))
            (cons (if (car x) (bm-repeat (cddr x)) 0)
                  (bm-repeat (cdr x))))
    nil))

; A test that a later one implies.  The second call is ruled by
; (not (eq (car x) 'a)) and (eq (car x) 'b); ACL2 drops the first.

(defun bm-implied (x)
  (cond ((atom x) 0)
        ((eq (car x) 'a) (bm-implied (cdr x)))
        ((eq (car x) 'b) (+ 1 (bm-implied (cdr x))))
        (t 2)))

; Two functions with the same measure.  ACL2 puts the clause (o-p M) of
; each function before the clauses of the calls in its body, and keeps the
; second copy, so that its clauses are those of the call in BM-EVEN, then
; (o-p M), then that of the call in BM-ODD; the specification puts the
; clauses (o-p M) first and keeps the first copy.

(mutual-recursion
 (defun bm-even (x) (if (consp x) (not (bm-odd (cddr x))) t))
 (defun bm-odd (x) (if (consp x) (bm-even (cdr x)) nil)))

; A relation other than o< (EDGE-CASES.md, entry 6.4), as in
; checks/facts.lsp.

(defun bm-mp (x) (true-listp x))
(defun bm-fn (x) (len x))
(defun bm-rel (x y) (< (len x) (len y)))

(defthm bm-rel-well-founded
  (and (implies (bm-mp x) (o-p (bm-fn x)))
       (implies (and (bm-mp x) (bm-mp y) (bm-rel x y))
                (o< (bm-fn x) (bm-fn y))))
  :rule-classes :well-founded-relation)

(defun bm-w (x)
  (declare (xargs :well-founded-relation bm-rel
                  :measure (true-list-fix x)))
  (if (consp x) (cons (car x) (bm-w (cdr x))) nil))

; Recursion inside the quoted lambda of a loop$ (EDGE-CASES.md, entry
; 6.14), as in checks/facts.lsp.  ACL2 Core finds no call of BM-L1 in
; its body.

(defun bm-l1 (x)
  (declare (xargs :loop$-recursion t :measure (acl2-count x)))
  (if (consp x) (loop$ for e in x sum (bm-l1 e)) 1))

; A measure that calls a constrained function, inside the encapsulate
; and after it.  ACL2 holds neither recursion as subversive, since no test
; and no argument of a call mentions BM-SIZE (ACL2's function SUBVERSIVEP
; does not look at the measure), so the equation of each is a definition
; of its own.  The body of BM-INSIDE calls no function of the constraint,
; so its define line stands before the constrain line of BM-SIZE (export/
; README.md, section 5 of core.lisp), and the checker refuses the measure
; entry that names BM-SIZE: a measure may call only functions in use.

(encapsulate
  (((bm-size *) => *))
  (local (defun bm-size (x) (acl2-count x)))
  (defthm bm-size-natp (natp (bm-size x)) :rule-classes :type-prescription)
  (defthm bm-size-cdr (implies (consp x) (< (bm-size (cdr x)) (bm-size x))))
  (defun bm-inside (x)
    (declare (xargs :measure (bm-size x)))
    (if (consp x) (bm-inside (cdr x)) x)))

(defun bm-outside (x)
  (declare (xargs :measure (bm-size x)))
  (if (consp x) (bm-outside (cdr x)) x))

; A recursion that ACL2 holds as subversive: the argument of its call
; mentions the constrained function BM-STEP, so its termination rests on
; the constraint, and its equation joins the constraint of the
; encapsulate (EDGE-CASES.md, entry 6.6).  There is no define line for it.

(encapsulate
  (((bm-step *) => *))
  (local (defun bm-step (x) (cdr x)))
  (defthm bm-step-smaller
    (implies (consp x) (< (bm-size (bm-step x)) (bm-size x))))
  (defun bm-sub (x)
    (declare (xargs :measure (bm-size x)))
    (if (consp x) (bm-sub (bm-step x)) x)))
