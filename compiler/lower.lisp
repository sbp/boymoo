(in-package "BOYMOO-COMPILER")

(include-book "qir")

(set-verify-guards-eagerness 0)

; P3, lowering: each definition of L1 becomes a function of QIR-A
; (compiler/DESIGN.md, sections 2 and 3).
;
; A term in a value position gives an operand: a variable gives the
; operand bound to it, a constant gives (:k . W), and a call of a
; primitive or of a function gives a new temporary. A :let binds each of
; its variables to the operand of its value, with no copy. An :if in a
; value position ends its block with (:if C L1 L0) and makes a join
; block, whose phi takes the value of each branch. A term in the tail
; position ends its block: a value with (:ret A), a call with (:tail F
; A ...), and a call of the definition by itself with a jump to the loop
; header, a block whose phis take the parameters. An :undef evaluates
; its arguments and ends its block with (:undef W); the term then has no
; value, which the lowering gives as :DEAD, and nothing after it on the
; same path is lowered. Arguments are lowered from left to right, so the
; instructions keep the order of evaluation of L1.
;
; The entry block is labelled 0. A definition that calls itself in the
; tail position has its loop header at 1: the entry block jumps to it,
; and its phis take the parameters, temporaries 0 to N - 1, from the
; entry, and the arguments of each such call from the block that makes
; it. The body refers to the phis, temporaries N to 2N - 1.

; ------------------------------------------------------------------
; The state of the lowering of one definition: the blocks finished, the
; last first; the label, phis and instructions, the last first, of the
; block being built, or NIL for the label when no block is open; the
; next temporary; the next label; and the jumps to the loop header,
; each (LABEL . ARGUMENTS).

(defun low-state (blocks label phis insts temp next backs)
  (list blocks label phis insts temp next backs))

(defun low-blocks (st) (nth 0 st))
(defun low-label (st) (nth 1 st))
(defun low-phis (st) (nth 2 st))
(defun low-insts (st) (nth 3 st))
(defun low-temp (st) (nth 4 st))
(defun low-next (st) (nth 5 st))
(defun low-backs (st) (nth 6 st))

(defun low-emit (inst st)
  (low-state (low-blocks st) (low-label st) (low-phis st)
             (cons inst (low-insts st)) (low-temp st) (low-next st) (low-backs st)))

(defun low-new-temp (st)
  (mv (cons :d (low-temp st))
      (low-state (low-blocks st) (low-label st) (low-phis st) (low-insts st)
                 (+ 1 (low-temp st)) (low-next st) (low-backs st))))

(defun low-new-label (st)
  (mv (low-next st)
      (low-state (low-blocks st) (low-label st) (low-phis st) (low-insts st)
                 (low-temp st) (+ 1 (low-next st)) (low-backs st))))

; Ends the open block with JUMP.
(defun low-end (jump st)
  (low-state (cons (list (low-label st) (low-phis st) (reverse (low-insts st)) jump)
                   (low-blocks st))
             nil nil nil (low-temp st) (low-next st) (low-backs st)))

; Opens the block LABEL with PHIS.
(defun low-start (label phis st)
  (low-state (low-blocks st) label phis nil (low-temp st) (low-next st) (low-backs st)))

(defun low-add-back (label args st)
  (low-state (low-blocks st) (low-label st) (low-phis st) (low-insts st)
             (low-temp st) (low-next st) (cons (cons label args) (low-backs st))))

; Gives the operand A of a term: in the tail position, ends the block
; with (:ret A).
(defun low-return (a tail st)
  (if tail
      (mv :dead (low-end (list :ret a) st))
    (mv a st)))

; Binds each variable of VARS to the operand in the same place of VALS.
(defun low-bind (vars vals env)
  (if (or (atom vars) (atom vals))
      env
    (low-bind (cdr vars) (cdr vals) (qir-put (car vars) (car vals) env))))

; Whether the word W is NIL.
(defun low-nil-p (w)
  (equal (low-bits w 64) 34))

; The label to which a test goes for the arm E of an :if in a test: LT
; or LF when E is a constant, which needs no block, else a new label.
(defun low-test-label (e lt lf st)
  (if (equal (car e) :const)
      (mv (if (low-nil-p (cadr e)) lf lt) st)
    (low-new-label st)))

; ------------------------------------------------------------------
; Terms. NAME is the name of the definition, for its calls of itself in
; the tail position; LOOP is T when it has a loop header. ENV maps each
; variable in scope to its operand. LOW-TERM gives the operand of the
; term, or :DEAD where it has none: always in the tail position, where
; it has ended its block. LOW-TERMS gives the list of operands, or :DEAD.

(mutual-recursion
 (defun low-term (e env tail name loop st)
   (declare (xargs :measure (* 2 (acl2-count e))
                   :hints (("Goal" :in-theory (disable low-nil-p)))))
   (let ((head (car e)))
     (cond
      ((equal head :var)
       (low-return (qir-get (cadr e) env) tail st))
      ((equal head :const)
       (low-return (cons :k (cadr e)) tail st))
      ((and (equal head :if) (equal (car (cadr e)) :const))
       (if (low-nil-p (cadr (cadr e)))
           (low-term (cadddr e) env tail name loop st)
         (low-term (caddr e) env tail name loop st)))
      ((equal head :if)
       (mv-let (l1 st)
         (low-new-label st)
         (mv-let (l0 st)
           (low-new-label st)
           (mv-let (u1 u0 st)
             (low-test (cadr e) l1 l0 env name loop st)
             (if tail
                 (mv-let (a st)
                   (if u1
                       (low-term (caddr e) env t name loop (low-start l1 nil st))
                     (mv :dead st))
                   (declare (ignore a))
                   (if u0
                       (low-term (cadddr e) env t name loop (low-start l0 nil st))
                     (mv :dead st)))
               (mv-let (join st)
                 (low-new-label st)
                 (mv-let (a st)
                   (if u1
                       (low-term (caddr e) env nil name loop (low-start l1 nil st))
                     (mv :dead st))
                   (let* ((a-label (low-label st))
                          (st (if (equal a :dead) st (low-end (list :jmp join) st))))
                     (mv-let (b st)
                       (if u0
                           (low-term (cadddr e) env nil name loop (low-start l0 nil st))
                         (mv :dead st))
                       (let* ((b-label (low-label st))
                              (st (if (equal b :dead) st (low-end (list :jmp join) st))))
                         (cond ((and (equal a :dead) (equal b :dead)) (mv :dead st))
                               ((equal a :dead) (mv b (low-start join nil st)))
                               ((or (equal b :dead) (equal a b))
                                (mv a (low-start join nil st)))
                               (t (mv-let (r st)
                                    (low-new-temp st)
                                    (mv r (low-start join
                                                     (list (list r (list (cons a-label a)
                                                                         (cons b-label b))))
                                                     st)))))))))))))))
      ((equal head :let)
       (mv-let (vals st)
         (low-terms (caddr e) env name loop st)
         (if (equal vals :dead)
             (mv :dead st)
           (low-term (cadddr e) (low-bind (cadr e) vals env) tail name loop st))))
      ((equal head :call)
       (mv-let (args st)
         (low-terms (caddr e) env name loop st)
         (cond ((equal args :dead) (mv :dead st))
               ((and tail loop (equal (cadr e) name))
                (mv :dead (low-end (list :jmp 1) (low-add-back (low-label st) args st))))
               (tail (mv :dead (low-end (list* :tail (cadr e) args) st)))
               (t (mv-let (r st)
                    (low-new-temp st)
                    (mv r (low-emit (list* r :call (cadr e) args) st)))))))
      ((equal head :prim)
       (mv-let (args st)
         (low-terms (caddr e) env name loop st)
         (if (equal args :dead)
             (mv :dead st)
           (mv-let (r st)
             (low-new-temp st)
             (low-return r tail (low-emit (list* r :prim (cadr e) args) st))))))
      ((equal head :undef)
       (mv-let (args st)
         (low-terms (caddr e) env name loop st)
         (if (equal args :dead)
             (mv :dead st)
           (mv :dead (low-end (list :undef (cadr e)) st)))))
      (t (mv :dead (low-end (list :undef 34) st))))))
 (defun low-terms (es env name loop st)
   (declare (xargs :measure (* 2 (acl2-count es))))
   (if (atom es)
       (mv nil st)
     (mv-let (a st)
       (low-term (car es) env nil name loop st)
       (if (equal a :dead)
           (mv :dead st)
         (mv-let (rest st)
           (low-terms (cdr es) env name loop st)
           (if (equal rest :dead)
               (mv :dead st)
             (mv (cons a rest) st)))))))
 (defun low-test (e lt lf env name loop st)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count e)))))
   (let ((head (car e)))
     (cond
      ((equal head :const)
       (if (low-nil-p (cadr e))
           (mv nil t (low-end (list :jmp lf) st))
         (mv t nil (low-end (list :jmp lt) st))))
      ((equal head :if)
       (let ((b (caddr e))
             (c (cadddr e)))
         (mv-let (lb st)
           (low-test-label b lt lf st)
           (mv-let (lc st)
             (low-test-label c lt lf st)
             (if (equal lb lc)
                 (mv-let (v st)
                   (low-term (cadr e) env nil name loop st)
                   (if (equal v :dead)
                       (mv nil nil st)
                     (mv (equal lb lt) (equal lb lf) (low-end (list :jmp lb) st))))
               (mv-let (ub uc st)
                 (low-test (cadr e) lb lc env name loop st)
                 (mv-let (t1 f1 st)
                   (cond ((not ub) (mv nil nil st))
                         ((equal (car b) :const) (mv (equal lb lt) (equal lb lf) st))
                         (t (low-test b lt lf env name loop (low-start lb nil st))))
                   (mv-let (t2 f2 st)
                     (cond ((not uc) (mv nil nil st))
                           ((equal (car c) :const) (mv (equal lc lt) (equal lc lf) st))
                           (t (low-test c lt lf env name loop (low-start lc nil st))))
                     (mv (or t1 t2) (or f1 f2) st)))))))))
      ((equal head :let)
       (mv-let (vals st)
         (low-terms (caddr e) env name loop st)
         (if (equal vals :dead)
             (mv nil nil st)
           (low-test (cadddr e) lt lf (low-bind (cadr e) vals env) name loop st))))
      (t (mv-let (v st)
           (low-term e env nil name loop st)
           (cond ((equal v :dead) (mv nil nil st))
                 ((qir-const-p v)
                  (if (low-nil-p (cdr v))
                      (mv nil t (low-end (list :jmp lf) st))
                    (mv t nil (low-end (list :jmp lt) st))))
                 (t (mv t t (low-end (list :if v lt lf) st)))))))))
)

; ------------------------------------------------------------------
; Definitions

; Whether the term E, in the tail position, calls NAME there.
(defun low-self-tail-p (e name)
  (declare (xargs :measure (acl2-count e)))
  (cond ((atom e) nil)
        ((equal (car e) :if)
         (or (low-self-tail-p (caddr e) name) (low-self-tail-p (cadddr e) name)))
        ((equal (car e) :let) (low-self-tail-p (cadddr e) name))
        ((equal (car e) :call) (equal (cadr e) name))
        (t nil)))

; The data temporaries numbered from I, N of them.
(defun low-temps (i n)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons (cons :d i) (low-temps (+ i 1) (- n 1)))))

; The arguments of a phi of the loop header for the parameter in place I:
; from each jump to the header, the argument in that place.
(defun low-back-args (backs i)
  (if (atom backs)
      nil
    (cons (cons (caar backs) (nth i (cdar backs)))
          (low-back-args (cdr backs) i))))

(defun low-header-phis (heads params backs i)
  (if (or (atom heads) (atom params))
      nil
    (cons (list (car heads) (cons (cons 0 (car params)) (low-back-args backs i)))
          (low-header-phis (cdr heads) (cdr params) backs (+ i 1)))))

; The function of QIR-A for the definition DEF of L1.
(defun lower-def (def)
  (let* ((name (car def))
         (formals (cadr def))
         (body (caddr def))
         (n (len formals))
         (params (low-temps 0 n)))
    (if (low-self-tail-p body name)
        (let ((heads (low-temps n n)))
          (mv-let (r st)
            (low-term body (low-bind formals heads nil) t name t
                      (low-state nil 1 nil nil (* 2 n) 2 nil))
            (declare (ignore r))
            (let* ((blocks (reverse (low-blocks st)))
                   (header (car blocks)))
              (list :fn name params
                    (list* (list 0 nil nil (list :jmp 1))
                           (list 1 (low-header-phis heads params (reverse (low-backs st)) 0)
                                 (qir-block-insts header) (qir-block-jump header))
                           (cdr blocks))))))
      (mv-let (r st)
        (low-term body (low-bind formals params nil) t name nil
                  (low-state nil 0 nil nil n 1 nil))
        (declare (ignore r))
        (list :fn name params (reverse (low-blocks st)))))))

; P3: the program of QIR-A for the definitions DEFS of L1.
(defun lower-definitions (defs)
  (if (atom defs)
      nil
    (cons (lower-def (car defs)) (lower-definitions (cdr defs)))))
