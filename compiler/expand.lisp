(in-package "BOYMOO-COMPILER")

(include-book "qir")

(set-verify-guards-eagerness 0)

; P4, expansion of primitives: QIR-A to QIR-M (compiler/DESIGN.md,
; sections 2 and 3), after Chez Scheme's np-expand-primitives. Each (T
; :prim P A ...) becomes operations on words, following the data
; representation of compiler/README.md, "The data", with a call of the
; runtime's routine for P, (T :rt R A ...), where the case is not computed
; inline.
; runtime.lisp defines what each routine computes, and each expansion
; below computes the same.
;
; The words of the data: an immediate integer n is 2n + 1; a cons is the
; offset of its two words, with the low three bits 000; an object with a
; header is its offset plus 2, so its low three bits are 010, and the low
; byte of its header, at the datum less 2, is its type (1 string, 2
; symbol, 3 integer, 4 fraction, 5 complex rational, 6 vector); a
; character of code c is 8c + 4. NIL is 34 and T is 58; both are symbols
; of the static block, which never moves.
;
; Where an expansion must read a field of an object that its argument
; may not be, it reads instead from a place in the static block that can
; always be read, and then discards what it read: the base of the load is
; (:sel C X 34), 34 being the symbol NIL, which has a header. The
; collector leaves that word as it is, as it leaves every reference into
; the static block, so it may be held in a data temporary. A field of a
; cons that X may not be is loaded only on the arm of a test of its tag.
;
; A test gives (T :sel C 58 34) from a word C that is 1 or 0. A jump
; (:if A L1 L0) becomes (:jnz C L1 L0) when A is such a test, and
; otherwise (:jnz W L1 L0) with W the comparison of A with 34.
;
; The blocks are expanded in a walk of the dominator tree, which carries
; what is known at each block: FACTS, what is known of each data
; temporary (:CONS when it is a cons, :ATOM when it is not, :FIXNUM when
; it is an immediate integer, or (:PAIR A . B) when it is the cons of the
; operands A and B); and AVAIL, the primitives and calls already computed
; on every path to the block, each from its name and operands to the
; operand of its result (a call is replaced only when EX-CSE-CALLS-P
; says so). A test of CONSP that a jump takes makes its
; argument known in the target, when the target has no other
; predecessor; CONS, CHAR-CODE and LENGTH make their results known. CAR,
; CDR and CONSP of an argument that is known need no test, and the
; arithmetic of an immediate integer that is known needs no test of its
; tag. A primitive or a call already in AVAIL is not computed again: its
; temporary is replaced by the earlier result everywhere. This is sound
; because every function of ACL2 Core gives the same value for the same
; arguments, whatever the definition, and the earlier computation
; dominates the later.
;
; Two patterns of the program are taken together when the first result
; has no other use: (BINARY-+ A (UNARY-- X)) in one block is a
; subtraction, and an :if whose test is the result of < or EQUAL, the
; last instruction of its block, branches on the comparison itself, when
; neither target has phis.
;
; An expansion with a slow case ends its block with (:jnz OK J S): the
; block S calls the routine, and the block J, where the rest of the
; original block goes, takes the result by a phi from the two. The phis
; that named the original block as a predecessor then name the last
; block made from it.

; ------------------------------------------------------------------
; The state of the expansion of one function: the blocks finished, the
; last first; the label, phis and instructions, the last first, of the
; block being built; the next temporary and the next label; CONDS, the
; map from the number of each data temporary that is a test to its word;
; TESTS, the map from the number of each data temporary that is a test of
; CONSP to (:CONSP . X), X its argument; RENAMES, the map from the label
; of each block that the expansion split to the label of the last block
; made from it; and SUBST, the map from the number of each temporary
; that is replaced to the operand that replaces it.

(defun ex-state (blocks label phis insts temp next conds tests renames subst)
  (list blocks label phis insts temp next conds tests renames subst))

(defun ex-blocks (st) (nth 0 st))
(defun ex-label (st) (nth 1 st))
(defun ex-phis (st) (nth 2 st))
(defun ex-insts (st) (nth 3 st))
(defun ex-temp (st) (nth 4 st))
(defun ex-next (st) (nth 5 st))
(defun ex-conds (st) (nth 6 st))
(defun ex-tests (st) (nth 7 st))
(defun ex-renames (st) (nth 8 st))
(defun ex-subst (st) (nth 9 st))

(defun ex-emit (inst st)
  (update-nth 3 (cons inst (ex-insts st)) st))

(defun ex-new-temp (class st)
  (mv (cons class (ex-temp st)) (update-nth 4 (+ 1 (ex-temp st)) st)))

(defun ex-new-label (st)
  (mv (ex-next st) (update-nth 5 (+ 1 (ex-next st)) st)))

(defun ex-end (jump st)
  (ex-state (cons (list (ex-label st) (ex-phis st) (reverse (ex-insts st)) jump)
                  (ex-blocks st))
            nil nil nil (ex-temp st) (ex-next st) (ex-conds st) (ex-tests st)
            (ex-renames st) (ex-subst st)))

(defun ex-start (label phis st)
  (update-nth 3 nil (update-nth 2 phis (update-nth 1 label st))))

(defun ex-note-cond (dest c st)
  (update-nth 6 (qir-put (cdr dest) c (ex-conds st)) st))

(defun ex-note-test (dest test st)
  (update-nth 7 (qir-put (cdr dest) test (ex-tests st)) st))

(defun ex-note-rename (old new st)
  (update-nth 8 (qir-put old new (ex-renames st)) st))

(defun ex-note-subst (dest x st)
  (update-nth 9 (qir-put (cdr dest) x (ex-subst st)) st))

; The operand that stands for X.
(defun ex-sub (x st)
  (or (and (qir-temp-p x) (qir-get (cdr x) (ex-subst st))) x))

(defun ex-subs (xs st)
  (if (atom xs)
      nil
    (cons (ex-sub (car xs) st) (ex-subs (cdr xs) st))))

; Emits (W OP . ARGS) for a new word temporary W, and gives W.
(defun ex-w (op args st)
  (mv-let (w st)
    (ex-new-temp :w st)
    (mv w (ex-emit (list* w op args) st))))

; The same for a new data temporary.
(defun ex-d (op args st)
  (mv-let (d st)
    (ex-new-temp :d st)
    (mv d (ex-emit (list* d op args) st))))

(defun ex-k (n) (cons :k n))

(defconst *ex-nil* '(:k . 34))
(defconst *ex-t* '(:k . 58))
(defconst *ex-one* '(:k . 1))

; The word A and B of two words that are each 1 or 0.
(defun ex-and (a b st)
  (cond ((equal a *ex-one*) (mv b st))
        ((equal b *ex-one*) (mv a st))
        (t (ex-w :and (list a b) st))))

; The integer of the 64 bits of W, in two's complement.
(defun ex-signed (w)
  (let ((w (low-bits w 64)))
    (if (< w 9223372036854775808) w (- w 18446744073709551616))))

(defun ex-fixnum-const-p (x)
  (and (qir-const-p x) (equal (low-bits (cdr x) 1) 1)))

; ------------------------------------------------------------------
; What is known: K is (FACTS . AVAIL).

(defun ex-fact (x facts)
  (and (qir-dtemp-p x) (qir-get (cdr x) facts)))

(defun ex-known-fixnum-p (x facts)
  (or (ex-fixnum-const-p x) (equal (ex-fact x facts) :fixnum)))

(defun ex-add-fact (dest fact k)
  (cons (qir-put (cdr dest) fact (car k)) (cdr k)))

; A constant or a temporary known to be equal to a datum exactly when it
; is the same word: an immediate integer, a character, NIL, T or another
; symbol, SYMBOLS being the map from the words of the symbols among the
; program's constants.
(defun ex-eq-operand-p (x facts symbols)
  (or (ex-known-fixnum-p x facts)
      (and (qir-const-p x)
           (or (equal (low-bits (cdr x) 3) 4)
               (equal (low-bits (cdr x) 64) 34)
               (equal (low-bits (cdr x) 64) 58)
               (and (qir-get (low-bits (cdr x) 64) symbols) t)))))

; ------------------------------------------------------------------
; Tests

; DEST is T when the word C is 1, and NIL when it is 0.
(defun ex-bool (dest c st)
  (ex-note-cond dest c (ex-emit (list dest :sel c *ex-t* *ex-nil*) st)))

(defun ex-const-bool (dest truth st)
  (ex-note-subst dest (if truth *ex-t* *ex-nil*) st))

; The word that is 1 when the low three bits of X are TAG, else 0.
(defun ex-tag-is (x tag st)
  (mv-let (w st)
    (ex-w :and (list x (ex-k 7)) st)
    (ex-w :ceq (list w (ex-k tag)) st)))

; For a datum X: H, 1 when X has a header, else 0; and B, the type in
; its header, or 2, the type of NIL, when it has none.
(defun ex-header-type (x st)
  (mv-let (h st)
    (ex-tag-is x 2 st)
    (mv-let (a st)
      (ex-d :sel (list h x *ex-nil*) st)
      (mv-let (b st)
        (ex-w :ldb (list a (ex-k -2)) st)
        (mv h b st)))))

; The word that is 1 when X is a fixnum or has a header whose type is
; from 3 to 3 + SPAN, else 0: INTEGERP for 0, RATIONALP for 1 and
; ACL2-NUMBERP for 2.
(defun ex-number-test (x span st)
  (mv-let (f st)
    (ex-w :and (list x (ex-k 1)) st)
    (mv-let (h b st)
      (ex-header-type x st)
      (declare (ignore h))
      (mv-let (e st)
        (if (equal span 0)
            (ex-w :ceq (list b (ex-k 3)) st)
          (mv-let (d st)
            (ex-w :sub (list b (ex-k 3)) st)
            (ex-w :cule (list d (ex-k span)) st)))
        (ex-w :or (list f e) st)))))

; The word that is 1 when X has a header of type TYPE, else 0. When X
; has none, B is 2, so only a test for symbols needs H.
(defun ex-header-test (x type st)
  (mv-let (h b st)
    (ex-header-type x st)
    (mv-let (e st)
      (ex-w :ceq (list b (ex-k type)) st)
      (if (equal type 2)
          (ex-w :and (list h e) st)
        (mv e st)))))

; A test of INTEGERP (SPAN 0), RATIONALP (1) or ACL2-NUMBERP (2) whose
; datum only an :if reads, as a branch: a fixnum goes to L1 at once, and
; the header is read only on the other arm.
(defun ex-number-branch (x span l1 l0 st)
  (mv-let (f st)
    (ex-w :and (list x (ex-k 1)) st)
    (mv-let (h st)
      (ex-new-label st)
      (let ((st (ex-start h nil (ex-end (list :jnz f l1 h) st))))
        (mv-let (hh b st)
          (ex-header-type x st)
          (declare (ignore hh))
          (mv-let (e st)
            (if (equal span 0)
                (ex-w :ceq (list b (ex-k 3)) st)
              (mv-let (d st)
                (ex-w :sub (list b (ex-k 3)) st)
                (ex-w :cule (list d (ex-k span)) st)))
            (ex-end (list :jnz e l1 l0) st)))))))

; ------------------------------------------------------------------
; The cases with a slow path. The open block computes OK, a word that is
; 1 when FAST is the result, else 0. Otherwise the instructions SLOW give
; the result R. DEST is defined in the join block, which is left open.
; When OK is the constant 1, FAST is the result and there is no slow
; path.

; The instruction that gives R from ROUTINE applied to ARGS. A routine
; whose label begins "rt-qir:" is a function of QIR-M (rt-qir.lisp) that
; the back end compiles with the contract of a routine (qir.lisp).
(defun ex-call-inst (r routine args)
  (list* r :rt routine args))

(defun ex-emit-all (insts st)
  (if (atom insts)
      st
    (ex-emit-all (cdr insts) (ex-emit (car insts) st))))

(defun ex-fast-slow-insts (ok fast dest slow r st)
  (if (equal ok *ex-one*)
      (ex-note-subst dest fast st)
    (let ((b (ex-label st)))
      (mv-let (s st)
        (ex-new-label st)
        (mv-let (join st)
          (ex-new-label st)
          (ex-start join (list (list dest (list (cons b fast) (cons s r))))
                    (ex-end (list :jmp join)
                            (ex-emit-all slow
                                         (ex-start s nil
                                                   (ex-end (list :jnz ok join s) st))))))))))

(defun ex-fast-slow (ok fast dest routine args st)
  (mv-let (r st)
    (ex-new-temp :d st)
    (ex-fast-slow-insts ok fast dest (list (ex-call-inst r routine args)) r st)))

; The same for a test whose datum only an :if reads: the open block ends
; with (:jnz OK F S); F branches on the word C, which is 1 when the test
; holds, to L1 or L0, and S on the datum that the routine gives.
(defun ex-fast-slow-branch (ok c routine args l1 l0 st)
  (mv-let (f st)
    (ex-new-label st)
    (mv-let (s st)
      (ex-new-label st)
      (mv-let (r st)
        (ex-new-temp :d st)
        (mv-let (w st)
          (ex-new-temp :w st)
          (ex-end (list :jnz w l1 l0)
                  (ex-emit (list w :cne r *ex-nil*)
                           (ex-emit (ex-call-inst r routine args)
                                    (ex-start s nil
                                              (ex-end (list :jnz c l1 l0)
                                                      (ex-start f nil
                                                                (ex-end (list :jnz ok f s)
                                                                        st))))))))))))

; ------------------------------------------------------------------
; The primitives

; CAR for OFF 0 and CDR for OFF 8. Of an X of which nothing is known, a
; test of its tag branches to a block that loads the field and to one
; that gives NIL, and a phi takes the result.
(defun ex-car-cdr (dest x off facts st)
  (let ((fact (ex-fact x facts)))
    (cond ((consp fact)
           (ex-note-subst dest (if (equal off 0) (cadr fact) (cddr fact)) st))
          ((equal fact :cons) (ex-emit (list dest :ld x (ex-k off)) st))
          (fact (ex-note-subst dest *ex-nil* st))
          (t (mv-let (w st)
               (ex-w :and (list x (ex-k 7)) st)
               (mv-let (lc st)
                 (ex-new-label st)
                 (mv-let (la st)
                   (ex-new-label st)
                   (mv-let (j st)
                     (ex-new-label st)
                     (mv-let (v st)
                       (ex-new-temp :d st)
                       (let* ((st (ex-start lc nil (ex-end (list :jnz w la lc) st)))
                              (st (ex-emit (list v :ld x (ex-k off)) st))
                              (st (ex-start la nil (ex-end (list :jmp j) st)))
                              (st (ex-end (list :jmp j) st)))
                         (ex-start j (list (list dest (list (cons lc v) (cons la *ex-nil*))))
                                   st)))))))))))

; CAR and CDR of the same X, when both occur in the function and nothing
; is known of X: one test of X branches to a block that loads both fields
; and to one that has neither, and the join takes both results by phis.
; OFF is 0 when DEST is the CAR, 8 when it is the CDR; gives the
; temporary of the other.
(defun ex-car-cdr-both (dest x off st)
  (mv-let (w st)
    (ex-w :and (list x (ex-k 7)) st)
    (mv-let (lc st)
      (ex-new-label st)
      (mv-let (la st)
        (ex-new-label st)
        (mv-let (j st)
          (ex-new-label st)
          (mv-let (other st)
            (ex-new-temp :d st)
            (mv-let (a st)
              (ex-new-temp :d st)
              (mv-let (d st)
                (ex-new-temp :d st)
                (let* ((st (ex-start lc nil (ex-end (list :jnz w la lc) st)))
                       (st (ex-emit (list d :ld x (ex-k 8)) (ex-emit (list a :ld x (ex-k 0)) st)))
                       (st (ex-start la nil (ex-end (list :jmp j) st)))
                       (st (ex-end (list :jmp j) st))
                       (car-dest (if (equal off 0) dest other))
                       (cdr-dest (if (equal off 0) other dest)))
                  (mv other
                      (ex-start j (list (list car-dest (list (cons lc a) (cons la *ex-nil*)))
                                        (list cdr-dest (list (cons lc d) (cons la *ex-nil*))))
                                st)))))))))))

(defun ex-consp (dest x facts st)
  (let ((fact (ex-fact x facts)))
    (cond ((or (consp fact) (equal fact :cons)) (ex-const-bool dest t st))
          (fact (ex-const-bool dest nil st))
          (t (mv-let (c st)
               (ex-tag-is x 0 st)
               (ex-note-test dest (cons :consp x) (ex-bool dest c st)))))))

; Ends the open block with (:jnz W TARGET NEXT), NEXT a new block that is
; then open; gives the label of the block ended.
(defun ex-chain-step (w target st)
  (let ((from (ex-label st)))
    (mv-let (next st)
      (ex-new-label st)
      (mv from (ex-start next nil (ex-end (list :jnz w target next) st))))))

; EQUAL: T when the words are the same. When they differ, NIL when
; their low three bits differ; when X is an immediate integer or a
; character (bit 0 or bit 2 set), as Y then is one too; or when one of
; them is a symbol, as symbols are equal only when they are the same word
; (runtime.lisp, rt:equal-distinct, compares two symbols no further): a
; constant with a header is tested for a symbol by the type in its
; header, in the static block. Otherwise both are conses or both have
; headers, and the routine compares them. X is the operand that is not a
; constant, when there is one. The tests are a chain of branches, each
; to T, to NIL or to the next: with BRANCH (L1 . L0), to the targets of
; the :if that reads the result; otherwise to a join block whose phi
; takes 58, 34 or the routine's result.
(defun ex-equal (dest x y facts symbols routine branch st)
  (let ((x (if (qir-const-p x) y x))
        (y (if (qir-const-p x) x y)))
    (cond
     ((equal x y) (mv (ex-const-bool dest t st) nil))
     ((or (ex-eq-operand-p x facts symbols) (ex-eq-operand-p y facts symbols))
      (mv-let (c st)
        (ex-w :ceq (list x y) st)
        (mv (ex-bool dest c st) nil)))
     (t (mv-let (join st)
          (if branch (mv nil st) (ex-new-label st))
          (let ((yes (if branch (car branch) join))
                (no (if branch (cdr branch) join)))
            (mv-let (same st)
              (ex-w :ceq (list x y) st)
              (mv-let (b0 st)
                (ex-chain-step same yes st)
                (mv-let (z st)
                  (ex-w :xor (list x y) st)
                  (mv-let (d st)
                    (ex-w :and (list z (ex-k 7)) st)
                    (mv-let (b1 st)
                      (ex-chain-step d no st)
                      (mv-let (imm st)
                        (ex-w :and (list x (ex-k 5)) st)
                        (mv-let (b2 st)
                          (ex-chain-step imm no st)
                          (mv-let (b3 st)
                            (if (and (qir-const-p y) (equal (low-bits (cdr y) 3) 2))
                                (mv-let (ty st)
                                  (ex-w :ldb (list y (ex-k -2)) st)
                                  (mv-let (sy st)
                                    (ex-w :ceq (list ty (ex-k 2)) st)
                                    (ex-chain-step sy no st)))
                              (mv nil st))
                            (mv-let (r st)
                              (ex-new-temp :d st)
                              (let ((st (ex-emit (ex-call-inst r routine (list x y)) st))
                                    (s (ex-label st)))
                                (if branch
                                    (mv-let (w st)
                                      (ex-w :cne (list r *ex-nil*) st)
                                      (mv (ex-end (list :jnz w yes no) st) t))
                                  (mv (ex-start join
                                                (list (list dest
                                                            (append (list (cons b0 *ex-t*)
                                                                          (cons b1 *ex-nil*)
                                                                          (cons b2 *ex-nil*))
                                                                    (if b3 (list (cons b3 *ex-nil*)) nil)
                                                                    (list (cons s r)))))
                                                (ex-end (list :jmp join) st))
                                      nil))))))))))))))))))

; The word that is 1 when X and Y are both fixnums: the constant 1 when
; both are known to be.
(defun ex-both-fixnums (x y facts st)
  (let ((kx (ex-known-fixnum-p x facts))
        (ky (ex-known-fixnum-p y facts)))
    (cond ((and kx ky) (mv *ex-one* st))
          (ky (ex-w :and (list x (ex-k 1)) st))
          (kx (ex-w :and (list y (ex-k 1)) st))
          (t (mv-let (a st)
               (ex-w :and (list x y) st)
               (ex-w :and (list a (ex-k 1)) st))))))

; The fixnum X less 1, which is even.
(defun ex-less-one (x st)
  (if (qir-const-p x)
      (mv (ex-k (- (cdr x) 1)) st)
    (ex-w :sub (list x (ex-k 1)) st)))

; The arithmetic with a slow path: the open block branches on F, 1 when
; the operands are fixnums, to a new block, left open, where the caller
; computes the result and O, 1 when it overflows; otherwise to the slow
; block S, whose label it gives. When F is the constant 1 there is no
; branch.
(defun ex-arith-split (f st)
  (mv-let (s st)
    (ex-new-label st)
    (if (equal f *ex-one*)
        (mv s st)
      (mv-let (c st)
        (ex-new-label st)
        (mv s (ex-start c nil (ex-end (list :jnz f c s) st)))))))

; Ends the open block with (:jnz O S J); the slow block S runs SLOW, which
; gives R; the join block J, left open, takes DEST from FAST or R.
(defun ex-arith-join (o fast dest slow r s st)
  (let ((b (ex-label st)))
    (mv-let (join st)
      (ex-new-label st)
      (ex-start join (list (list dest (list (cons b fast) (cons s r))))
                (ex-end (list :jmp join)
                        (ex-emit-all slow
                                     (ex-start s nil
                                               (ex-end (list :jnz o s join) st))))))))

; BINARY-+ of two fixnums 2a + 1 and 2b + 1 is 2(a + b) + 1, which is
; X + (Y - 1); it is a fixnum when that addition does not overflow.
(defun ex-plus (dest x y facts st)
  (let ((x (if (ex-fixnum-const-p x) y x))
        (y (if (ex-fixnum-const-p x) x y)))
    (mv-let (f st)
      (ex-both-fixnums x y facts st)
      (mv-let (s st)
        (ex-arith-split f st)
        (mv-let (y1 st)
          (ex-less-one y st)
          (mv-let (o st)
            (ex-w :ovadd (list x y1) st)
            (mv-let (sum st)
              (ex-w :add (list x y1) st)
              (mv-let (d1 st)
                (ex-d :copy (list sum) st)
                (mv-let (r st)
                  (ex-new-temp :d st)
                  (ex-arith-join o d1 dest
                                 (list (list r :rt "prim:ACL2::BINARY-+" x y))
                                 r s st))))))))))

; (BINARY-+ A (UNARY-- X)) of two fixnums 2a + 1 and 2x + 1 is
; 2(a - x) + 1, which is A - (X - 1); the slow path computes the two
; primitives in order.
(defun ex-subtract (dest a x facts st)
  (mv-let (f st)
    (ex-both-fixnums a x facts st)
    (mv-let (s st)
      (ex-arith-split f st)
      (mv-let (x1 st)
        (ex-less-one x st)
        (mv-let (o st)
          (ex-w :ovsub (list a x1) st)
          (mv-let (dif st)
            (ex-w :sub (list a x1) st)
            (mv-let (d1 st)
              (ex-d :copy (list dif) st)
              (mv-let (n st)
                (ex-new-temp :d st)
                (mv-let (r st)
                  (ex-new-temp :d st)
                  (ex-arith-join o d1 dest
                                 (list (list n :rt "prim:ACL2::UNARY--" x)
                                       (list r :rt "prim:ACL2::BINARY-+" a n))
                                 r s st))))))))))

; UNARY-- of the fixnum 2a + 1 is 2(-a) + 1, which is 2 - X.
(defun ex-minus (dest x facts st)
  (mv-let (f st)
    (if (ex-known-fixnum-p x facts) (mv *ex-one* st) (ex-w :and (list x (ex-k 1)) st))
    (mv-let (s st)
      (ex-arith-split f st)
      (mv-let (o st)
        (ex-w :ovsub (list (ex-k 2) x) st)
        (mv-let (dif st)
          (ex-w :sub (list (ex-k 2) x) st)
          (mv-let (d1 st)
            (ex-d :copy (list dif) st)
            (mv-let (r st)
              (ex-new-temp :d st)
              (ex-arith-join o d1 dest
                             (list (list r :rt "prim:ACL2::UNARY--" x))
                             r s st))))))))

; < of two fixnums is the signed comparison of their words.
(defun ex-less (dest x y facts branch st)
  (mv-let (f st)
    (ex-both-fixnums x y facts st)
    (mv-let (c st)
      (ex-w :cslt (list x y) st)
      (cond ((equal f *ex-one*) (mv (ex-bool dest c st) nil))
            (branch (mv (ex-fast-slow-branch f c "prim:COMMON-LISP::<" (list x y)
                                             (car branch) (cdr branch) st)
                        t))
            (t (mv-let (v st)
                 (ex-d :sel (list c *ex-t* *ex-nil*) st)
                 (mv (ex-fast-slow f v dest "prim:COMMON-LISP::<" (list x y) st) nil)))))))

; BINARY-LOGXOR of two fixnums: (2a + 1) xor (2b + 1) is 2(a xor b), so
; the result is that with its low bit set.
(defun ex-logxor (dest x y facts st)
  (mv-let (f st)
    (ex-both-fixnums x y facts st)
    (mv-let (z st)
      (ex-w :xor (list x y) st)
      (mv-let (s st)
        (ex-w :or (list z (ex-k 1)) st)
        (mv-let (d1 st)
          (ex-d :copy (list s) st)
          (ex-fast-slow f d1 dest "jet:ACL2::BINARY-LOGXOR" (list x y) st))))))

; ASH of a fixnum X = 2a + 1 by a fixnum K = 2k + 1. For k = -m below 0,
; (X >> m) arithmetic, with its low bit set, is 2 floor(a / 2^m) + 1, and
; m beyond 63 shifts as 63 does. For k from 0 to 62, (X - 1) << k is
; 2a 2^k, and the result is a fixnum when shifting it back by k gives
; X - 1. Every other case goes to the routine.
(defun ex-ash-right (dest x k m facts st)
  (mv-let (f st)
    (if (ex-known-fixnum-p x facts) (mv *ex-one* st) (ex-w :and (list x (ex-k 1)) st))
    (mv-let (r1 st)
      (ex-w :sar (list x (ex-k (if (< 63 m) 63 m))) st)
      (mv-let (r st)
        (ex-w :or (list r1 (ex-k 1)) st)
        (mv-let (d1 st)
          (ex-d :copy (list r) st)
          (ex-fast-slow f d1 dest "jet:COMMON-LISP::ASH" (list x k) st))))))

(defun ex-ash-left (dest x k n facts st)
  (mv-let (f st)
    (if (ex-known-fixnum-p x facts) (mv *ex-one* st) (ex-w :and (list x (ex-k 1)) st))
    (mv-let (x1 st)
      (ex-less-one x st)
      (mv-let (s st)
        (ex-w :shl (list x1 (ex-k n)) st)
        (mv-let (b st)
          (ex-w :sar (list s (ex-k n)) st)
          (mv-let (e st)
            (ex-w :ceq (list b x1) st)
            (mv-let (ok st)
              (ex-and f e st)
              (mv-let (l st)
                (ex-w :or (list s (ex-k 1)) st)
                (mv-let (d1 st)
                  (ex-d :copy (list l) st)
                  (ex-fast-slow ok d1 dest "jet:COMMON-LISP::ASH" (list x k) st))))))))))

(defun ex-ash-any (dest x k facts st)
  (mv-let (f st)
    (ex-both-fixnums x k facts st)
    (mv-let (kk st)
      (ex-w :sar (list k (ex-k 1)) st)
      (mv-let (neg st)
        (ex-w :cslt (list kk (ex-k 0)) st)
        (mv-let (m st)
          (ex-w :sub (list (ex-k 0) kk) st)
          (mv-let (big st)
            (ex-w :cugt (list m (ex-k 63)) st)
            (mv-let (mc st)
              (ex-w :sel (list big (ex-k 63) m) st)
              (mv-let (r1 st)
                (ex-w :sar (list x mc) st)
                (mv-let (r st)
                  (ex-w :or (list r1 (ex-k 1)) st)
                  (mv-let (x1 st)
                    (ex-less-one x st)
                    (mv-let (s st)
                      (ex-w :shl (list x1 kk) st)
                      (mv-let (b st)
                        (ex-w :sar (list s kk) st)
                        (mv-let (e st)
                          (ex-w :ceq (list b x1) st)
                          (mv-let (small st)
                            (ex-w :cult (list kk (ex-k 63)) st)
                            (mv-let (okl st)
                              (ex-w :and (list e small) st)
                              (mv-let (l st)
                                (ex-w :or (list s (ex-k 1)) st)
                                (mv-let (res st)
                                  (ex-w :sel (list neg r l) st)
                                  (mv-let (okk st)
                                    (ex-w :or (list neg okl) st)
                                    (mv-let (ok st)
                                      (ex-and f okk st)
                                      (mv-let (d1 st)
                                        (ex-d :copy (list res) st)
                                        (ex-fast-slow ok d1 dest "jet:COMMON-LISP::ASH"
                                                      (list x k) st)))))))))))))))))))))

(defun ex-ash (dest x k facts st)
  (if (ex-fixnum-const-p k)
      (let ((n (ash (ex-signed (cdr k)) -1)))
        (cond ((< n 0) (ex-ash-right dest x k (- n) facts st))
              ((< n 63) (ex-ash-left dest x k n facts st))
              (t (ex-emit (list dest :rt "jet:COMMON-LISP::ASH" x k) st))))
    (ex-ash-any dest x k facts st)))

; CHAR-CODE: the character 8c + 4 gives 2c + 1, its word shifted right
; by 2; anything else gives 0, the word 1.
(defun ex-char-code (dest x st)
  (mv-let (c st)
    (ex-tag-is x 4 st)
    (mv-let (s st)
      (ex-w :shr (list x (ex-k 2)) st)
      (ex-emit (list dest :sel c s (ex-k 1)) st))))

; CODE-CHAR: the fixnum 2n + 1 with n from 0 to 255, which is a word
; from 1 to 511, gives 8n + 4, its word shifted left by 2; anything else
; gives the character of code 0, the word 4.
(defun ex-code-char (dest x st)
  (mv-let (f st)
    (ex-w :and (list x (ex-k 1)) st)
    (mv-let (u st)
      (ex-w :cule (list x (ex-k 511)) st)
      (mv-let (c st)
        (ex-w :and (list f u) st)
        (mv-let (s st)
          (ex-w :shl (list x (ex-k 2)) st)
          (ex-emit (list dest :sel c s (ex-k 4)) st))))))

; For a datum X: OK, 1 when X is a string, else 0; and HD, the header of
; X, or that of NIL when X has none.
(defun ex-string-header (x st)
  (mv-let (h st)
    (ex-tag-is x 2 st)
    (mv-let (a st)
      (ex-d :sel (list h x *ex-nil*) st)
      (mv-let (hd st)
        (ex-w :ld (list a (ex-k -2)) st)
        (mv-let (ty st)
          (ex-w :and (list hd (ex-k 255)) st)
          (mv-let (ok st)
            (ex-w :ceq (list ty (ex-k 1)) st)
            (mv ok hd st)))))))

; LENGTH of a string: the header of a string is (size << 8) | 1, so the
; header shifted right by 7 is 2 size, and with its low bit set it is
; the fixnum of the size. A list goes to the routine, which gives a
; fixnum too.
(defun ex-length (dest x routine st)
  (mv-let (ok hd st)
    (ex-string-header x st)
    (mv-let (n st)
      (ex-w :shr (list hd (ex-k 7)) st)
      (mv-let (s st)
        (ex-w :or (list n (ex-k 1)) st)
        (mv-let (d1 st)
          (ex-d :copy (list s) st)
          (ex-fast-slow ok d1 dest routine (list x) st))))))

; CHAR of a string S and a fixnum index 2k + 1 with k below the size:
; the byte at k + 8 bytes after the header, which is at the datum less
; 2, gives the character 8b + 4. Every other case goes to the routine.
(defun ex-char (dest s i facts routine st)
  (mv-let (str hd st)
    (ex-string-header s st)
    (mv-let (fi st)
      (if (ex-known-fixnum-p i facts) (mv *ex-one* st) (ex-w :and (list i (ex-k 1)) st))
      (mv-let (k st)
        (ex-w :sar (list i (ex-k 1)) st)
        (mv-let (len st)
          (ex-w :shr (list hd (ex-k 8)) st)
          (mv-let (inr st)
            (ex-w :cult (list k len) st)
            (mv-let (ok1 st)
              (ex-and str fi st)
              (mv-let (ok st)
                (ex-w :and (list ok1 inr) st)
                (mv-let (base st)
                  (ex-d :sel (list ok s *ex-nil*) st)
                  (mv-let (off0 st)
                    (ex-w :add (list k (ex-k 6)) st)
                    (mv-let (off st)
                      (ex-w :sel (list ok off0 (ex-k 0)) st)
                      (mv-let (b st)
                        (ex-w :ldb (list base off) st)
                        (mv-let (c1 st)
                          (ex-w :shl (list b (ex-k 3)) st)
                          (mv-let (c2 st)
                            (ex-w :or (list c1 (ex-k 4)) st)
                            (mv-let (d1 st)
                              (ex-d :copy (list c2) st)
                              (ex-fast-slow ok d1 dest routine
                                            (list s i) st))))))))))))))))

; The expansion of (DEST :prim NAME . ARGS), with ARGS already replaced.
; NEGS maps the temporaries of the UNARY-- that a BINARY-+ takes as a
; subtraction to their arguments. BRANCH is (L1 . L0) when the result is
; the test of the :if that ends the block and nothing else reads it.
; SYMBOLS is as for EX-EQ-OPERAND-P. RTQ is T when the slow paths of
; EQUAL, LENGTH and CHAR call the functions of rt-qir.lisp. Gives what is
; known after it, the state, and whether the expansion ended the block.
(defun ex-prim (dest name args k negs symbols rtq branch st)
  (let ((x (car args))
        (y (cadr args))
        (facts (car k)))
    (cond
     ((equal name "COMMON-LISP::CAR") (mv k (ex-car-cdr dest x 0 facts st) nil))
     ((equal name "COMMON-LISP::CDR") (mv k (ex-car-cdr dest x 8 facts st) nil))
     ((equal name "COMMON-LISP::CONSP") (mv k (ex-consp dest x facts st) nil))
     ((equal name "COMMON-LISP::CONS")
      (mv (ex-add-fact dest (cons :pair (cons x y)) k)
          (ex-emit (list dest :cons x y) st) nil))
     ((equal name "COMMON-LISP::EQUAL")
      (mv-let (st done)
        (ex-equal dest x y facts symbols
                  (if rtq "rt-qir:EQUAL" "prim:COMMON-LISP::EQUAL") branch st)
        (mv k st done)))
     ((equal name "COMMON-LISP::<")
      (mv-let (st done)
        (ex-less dest x y facts branch st)
        (mv k st done)))
     ((equal name "ACL2::BINARY-+")
      (let ((nx (and (qir-dtemp-p x) (qir-get (cdr x) negs)))
            (ny (and (qir-dtemp-p y) (qir-get (cdr y) negs))))
        (mv k
            (cond (ny (ex-subtract dest x (ex-sub ny st) facts st))
                  (nx (ex-subtract dest y (ex-sub nx st) facts st))
                  (t (ex-plus dest x y facts st)))
            nil)))
     ((equal name "ACL2::UNARY--") (mv k (ex-minus dest x facts st) nil))
     ((equal name "ACL2::BINARY-LOGXOR")
      (mv (if (and (ex-known-fixnum-p x facts) (ex-known-fixnum-p y facts))
              (ex-add-fact dest :fixnum k)
            k)
          (ex-logxor dest x y facts st) nil))
     ((equal name "COMMON-LISP::ASH")
      (mv (if (and (ex-known-fixnum-p x facts) (ex-fixnum-const-p y)
                   (< (ex-signed (cdr y)) 0))
              (ex-add-fact dest :fixnum k)
            k)
          (ex-ash dest x y facts st) nil))
     ((equal name "COMMON-LISP::CHAR-CODE")
      (mv (ex-add-fact dest :fixnum k) (ex-char-code dest x st) nil))
     ((equal name "COMMON-LISP::CODE-CHAR") (mv k (ex-code-char dest x st) nil))
     ((equal name "COMMON-LISP::LENGTH")
      (mv (ex-add-fact dest :fixnum k)
          (ex-length dest x (if rtq "rt-qir:LENGTH" "jet:COMMON-LISP::LENGTH") st) nil))
     ((equal name "COMMON-LISP::CHAR")
      (mv k (ex-char dest x y facts (if rtq "rt-qir:CHAR" "jet:COMMON-LISP::CHAR") st) nil))
     ((equal name "ACL2::BAD-ATOM<=") (mv k (ex-note-subst dest *ex-nil* st) nil))
     ((equal name "COMMON-LISP::CHARACTERP")
      (mv k (mv-let (c st) (ex-tag-is x 4 st) (ex-bool dest c st)) nil))
     ((equal name "COMMON-LISP::STRINGP")
      (mv k (mv-let (c st) (ex-header-test x 1 st) (ex-bool dest c st)) nil))
     ((equal name "COMMON-LISP::SYMBOLP")
      (mv k (mv-let (c st) (ex-header-test x 2 st) (ex-bool dest c st)) nil))
     ((equal name "ACL2::COMPLEX-RATIONALP")
      (mv k (mv-let (c st) (ex-header-test x 5 st) (ex-bool dest c st)) nil))
     ((or (equal name "COMMON-LISP::INTEGERP") (equal name "COMMON-LISP::RATIONALP")
          (equal name "ACL2::ACL2-NUMBERP"))
      (let ((span (cond ((equal name "COMMON-LISP::INTEGERP") 0)
                        ((equal name "COMMON-LISP::RATIONALP") 1)
                        (t 2))))
        (cond ((ex-known-fixnum-p x facts) (mv k (ex-const-bool dest t st) nil))
              (branch (mv k (ex-number-branch x span (car branch) (cdr branch) st) t))
              (t (mv k (mv-let (c st) (ex-number-test x span st) (ex-bool dest c st))
                     nil)))))
     (t (mv k (ex-emit (list* dest :rt (qir-prim-routine name) args) st) nil)))))

; ------------------------------------------------------------------
; Instructions, jumps and blocks. CTX is (USES NEGS BMAP PREDS CHILDREN
; SYMBOLS FIELDS RTQ) for the function: the number of uses of each temporary,
; NEGS as for EX-PRIM, the map from labels to blocks, the predecessors of
; each block, the children of each block in the dominator tree, SYMBOLS
; as for EX-EQ-OPERAND-P, FIELDS, the set of (NAME . X) for each CAR and
; CDR of an operand X in the function, and RTQ as for EX-PRIM.

(defun ex-ctx-uses (ctx) (nth 0 ctx))
(defun ex-ctx-negs (ctx) (nth 1 ctx))
(defun ex-ctx-bmap (ctx) (nth 2 ctx))
(defun ex-ctx-preds (ctx) (nth 3 ctx))
(defun ex-ctx-children (ctx) (nth 4 ctx))
(defun ex-ctx-symbols (ctx) (nth 5 ctx))
(defun ex-ctx-fields (ctx) (nth 6 ctx))
(defun ex-ctx-rtq (ctx) (nth 7 ctx))

; Whether what is known of the argument of CAR, CDR or CONSP decides it
; with no instruction, so that it is not looked up in AVAIL: a CONSP
; whose argument is known, or a CAR or CDR of the cons of two operands or
; of an atom. A CAR or CDR of a known cons is a load, which an earlier
; one in AVAIL makes needless.
(defun ex-decided-p (name args facts)
  (let ((fact (ex-fact (car args) facts)))
    (and fact
         (or (equal name "COMMON-LISP::CONSP")
             (and (or (equal name "COMMON-LISP::CAR") (equal name "COMMON-LISP::CDR"))
                  (not (equal fact :cons)))))))

; Whether a CAR or CDR of RAW, which is X once replaced, nothing being
; known of X, has its other field taken in the function too.
(defun ex-both-fields-p (name raw args facts ctx)
  (and (or (equal name "COMMON-LISP::CAR") (equal name "COMMON-LISP::CDR"))
       (not (ex-fact (car args) facts))
       (qir-get (cons (if (equal name "COMMON-LISP::CAR") "COMMON-LISP::CDR" "COMMON-LISP::CAR")
                      raw)
                (ex-ctx-fields ctx))
       t))

(defun ex-avail-add (key dest k)
  (cons (car k) (qir-put key dest (cdr k))))

; Whether a call already in AVAIL is replaced by its earlier result.
; Measured on 2026-11-27 on the executable that the compiler writes from
; build/compiler/single/compiler.input, run on that input (/usr/bin/time
; -l, the median of 9 runs), replacing calls saved 5% of its processor
; time but raised its peak of resident memory by 2.4 MB, as results lived
; longer; so it is off.
(defun ex-cse-calls-p () nil)

; Gives what is known after INST, the state, and whether the expansion
; ended the block.
(defun ex-inst (inst k ctx branch st)
  (let ((op (qir-inst-op inst))
        (dest (qir-inst-dest inst)))
    (cond
     ((equal op :prim)
      (let* ((name (caddr inst))
             (args (ex-subs (cdddr inst) st))
             (key (cons name args))
             (prev (qir-get key (cdr k))))
        (mv-let (dest st)
          (if dest (mv dest st) (ex-new-temp :d st))
          (cond ((qir-get (cdr dest) (ex-ctx-negs ctx)) (mv k st nil))
                ((and prev (not (ex-decided-p name args (car k))))
                 (mv k (ex-note-subst dest prev st) nil))
                ((ex-both-fields-p name (cadddr inst) args (car k) ctx)
                 (let ((car-p (equal name "COMMON-LISP::CAR")))
                   (mv-let (other st)
                     (ex-car-cdr-both dest (car args) (if car-p 0 8) st)
                     (mv (ex-avail-add (list (if car-p "COMMON-LISP::CDR" "COMMON-LISP::CAR")
                                             (car args))
                                       other (ex-avail-add key dest k))
                         st nil))))
                (t (mv-let (k st done)
                     (ex-prim dest name args k (ex-ctx-negs ctx) (ex-ctx-symbols ctx)
                              (ex-ctx-rtq ctx) branch st)
                     (mv (if done k (ex-avail-add key (ex-sub dest st) k))
                         st done)))))))
     ((equal op :call)
      (let* ((args (ex-subs (cdddr inst) st))
             (key (list* :call (caddr inst) args))
             (prev (qir-get key (cdr k))))
        (cond ((and prev dest (ex-cse-calls-p))
               (mv k (ex-note-subst dest prev st) nil))
              (t (mv (if dest (ex-avail-add key dest k) k)
                     (ex-emit (list* dest :call (caddr inst) args) st)
                     nil)))))
     (t (mv k (ex-emit (list* dest op (ex-subs (cddr inst) st)) st) nil)))))

(defun ex-insts-of (insts k ctx branch st)
  (if (atom insts)
      (mv k st nil)
    (mv-let (k st done)
      (ex-inst (car insts) k ctx (and (atom (cdr insts)) branch) st)
      (if (atom (cdr insts))
          (mv k st done)
        (ex-insts-of (cdr insts) k ctx branch st)))))

; A word that is not 0 exactly when the datum A is not NIL.
(defun ex-truth (a facts st)
  (let ((c (and (qir-dtemp-p a) (qir-get (cdr a) (ex-conds st))))
        (fact (ex-fact a facts)))
    (cond (c (mv c st))
          ((qir-const-p a) (mv (ex-k (if (equal (low-bits (cdr a) 64) 34) 0 1)) st))
          ((or (consp fact) (equal fact :cons) (equal fact :fixnum)) (mv *ex-one* st))
          (t (ex-w :cne (list a *ex-nil*) st)))))

(defun ex-jump (jump facts st)
  (let ((op (car jump)))
    (cond ((equal op :if)
           (mv-let (c st)
             (ex-truth (ex-sub (cadr jump) st) facts st)
             (ex-end (list :jnz c (caddr jump) (cadddr jump)) st)))
          ((equal op :ret) (ex-end (list :ret (ex-sub (cadr jump) st)) st))
          ((equal op :tail) (ex-end (list* :tail (cadr jump) (ex-subs (cddr jump) st)) st))
          (t (ex-end jump st)))))

; (L1 . L0) when the block ends with an :if whose test is the result of
; <, EQUAL, INTEGERP, RATIONALP or ACL2-NUMBERP, the last instruction,
; read nowhere else, and neither target has phis; else NIL.
(defun ex-branch (block ctx)
  (let* ((insts (qir-block-insts block))
         (jump (qir-block-jump block))
         (last (car (last insts)))
         (bmap (ex-ctx-bmap ctx)))
    (and (consp insts)
         (equal (car jump) :if)
         (equal (qir-inst-op last) :prim)
         (member-equal (caddr last) '("COMMON-LISP::<" "COMMON-LISP::EQUAL"
                                      "COMMON-LISP::INTEGERP" "COMMON-LISP::RATIONALP"
                                      "ACL2::ACL2-NUMBERP"))
         (qir-dtemp-p (cadr jump))
         (equal (cadr jump) (qir-inst-dest last))
         (equal (qir-get (cdr (cadr jump)) (ex-ctx-uses ctx)) 1)
         (null (qir-block-phis (qir-get (caddr jump) bmap)))
         (null (qir-block-phis (qir-get (cadddr jump) bmap)))
         (cons (caddr jump) (cadddr jump)))))

(defun ex-block (block k ctx st)
  (let ((label (qir-block-label block)))
    (mv-let (k st done)
      (ex-insts-of (qir-block-insts block) k ctx (ex-branch block ctx)
                   (ex-start label (qir-block-phis block) st))
      (if done
          (mv k st)
        (let ((last (ex-label st)))
          (mv k
              (ex-jump (qir-block-jump block) (car k)
                       (if (equal last label) st (ex-note-rename label last st)))))))))

; What is known at the start of CHILD, a child of the block LABEL in the
; dominator tree, given K at the end of LABEL: when CHILD is a target of
; the jump of LABEL, a test of CONSP, and LABEL is its only predecessor,
; the argument of the test is known.
(defun ex-child-k (child label jump preds k st)
  (let* ((a (and (equal (car jump) :if) (ex-sub (cadr jump) st)))
         (test (and (qir-dtemp-p a)
                    (equal (qir-get child preds) (list label))
                    (qir-get (cdr a) (ex-tests st))))
         (x (cdr test)))
    (if (and (qir-dtemp-p x) (not (qir-get (cdr x) (car k))))
        (ex-add-fact x (if (equal child (caddr jump)) :cons :atom) k)
      k)))

(defun ex-push-children (children label jump preds k st work)
  (if (atom children)
      work
    (cons (cons (car children) (ex-child-k (car children) label jump preds k st))
          (ex-push-children (cdr children) label jump preds k st work))))

; WORK holds pairs (LABEL . K) of the blocks still to expand.
(defun ex-walk (work ctx st fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (atom work))
      st
    (let* ((label (caar work))
           (block (qir-get label (ex-ctx-bmap ctx))))
      (mv-let (k st)
        (ex-block block (cdar work) ctx st)
        (ex-walk (ex-push-children (qir-get label (ex-ctx-children ctx)) label
                                   (qir-block-jump block) (ex-ctx-preds ctx) k st
                                   (cdr work))
                 ctx st (- fuel 1))))))

; ------------------------------------------------------------------
; The uses of each temporary, and the subtractions.

(defun ex-count-uses (xs uses)
  (cond ((atom xs) uses)
        ((qir-temp-p (car xs))
         (ex-count-uses (cdr xs)
                        (qir-put (cdar xs) (+ 1 (nfix (qir-get (cdar xs) uses))) uses)))
        (t (ex-count-uses (cdr xs) uses))))

(defun ex-insts-uses (insts uses)
  (if (atom insts)
      uses
    (ex-insts-uses (cdr insts) (ex-count-uses (qir-inst-uses (car insts)) uses))))

(defun ex-phis-uses (phis uses)
  (if (atom phis)
      uses
    (ex-phis-uses (cdr phis)
                  (ex-count-uses (qir-phi-arg-operands (qir-phi-args (car phis))) uses))))

(defun ex-blocks-uses (blocks uses)
  (if (atom blocks)
      uses
    (ex-blocks-uses (cdr blocks)
                    (ex-count-uses (qir-jump-uses (qir-block-jump (car blocks)))
                                   (ex-insts-uses (qir-block-insts (car blocks))
                                                  (ex-phis-uses (qir-block-phis (car blocks))
                                                                uses))))))

; A temporary of UNARY-- that only a later BINARY-+ of the same block
; reads; UNARIES maps those of the block seen so far to their arguments.
(defun ex-unary-of (x unaries uses)
  (and (qir-dtemp-p x)
       (equal (qir-get (cdr x) uses) 1)
       (qir-get (cdr x) unaries)))

(defun ex-block-negs (insts unaries uses negs)
  (if (atom insts)
      negs
    (let* ((inst (car insts))
           (dest (qir-inst-dest inst))
           (name (and (equal (qir-inst-op inst) :prim) (caddr inst))))
      (cond ((and (equal name "ACL2::UNARY--") (qir-dtemp-p dest))
             (ex-block-negs (cdr insts) (qir-put (cdr dest) (cadddr inst) unaries)
                            uses negs))
            ((equal name "ACL2::BINARY-+")
             (let* ((a (cadddr inst))
                    (b (car (cddddr inst)))
                    (nb (ex-unary-of b unaries uses))
                    (na (and (not nb) (ex-unary-of a unaries uses))))
               (ex-block-negs (cdr insts) unaries uses
                              (cond (nb (qir-put (cdr b) nb negs))
                                    (na (qir-put (cdr a) na negs))
                                    (t negs)))))
            (t (ex-block-negs (cdr insts) unaries uses negs))))))

(defun ex-blocks-negs (blocks uses negs)
  (if (atom blocks)
      negs
    (ex-blocks-negs (cdr blocks) uses
                    (ex-block-negs (qir-block-insts (car blocks)) nil uses negs))))

(defun ex-insts-fields (insts fields)
  (if (atom insts)
      fields
    (let ((inst (car insts)))
      (ex-insts-fields (cdr insts)
                       (if (and (equal (qir-inst-op inst) :prim)
                                (or (equal (caddr inst) "COMMON-LISP::CAR")
                                    (equal (caddr inst) "COMMON-LISP::CDR")))
                           (qir-put (cons (caddr inst) (cadddr inst)) t fields)
                         fields)))))

(defun ex-blocks-fields (blocks fields)
  (if (atom blocks)
      fields
    (ex-blocks-fields (cdr blocks) (ex-insts-fields (qir-block-insts (car blocks)) fields))))

; ------------------------------------------------------------------
; The phis: their operands are replaced, and in the blocks that keep a
; label of the original function, BMAP, their predecessors renamed; the
; phis of the join blocks that the expansion made already name the
; blocks it made.

(defun ex-fix-args (args renames rename st)
  (if (atom args)
      nil
    (cons (cons (if rename (or (qir-get (caar args) renames) (caar args)) (caar args))
                (ex-sub (cdar args) st))
          (ex-fix-args (cdr args) renames rename st))))

(defun ex-fix-phis (phis renames rename st)
  (if (atom phis)
      nil
    (cons (list (qir-phi-dest (car phis))
                (ex-fix-args (qir-phi-args (car phis)) renames rename st))
          (ex-fix-phis (cdr phis) renames rename st))))

(defun ex-fix-blocks (blocks bmap st)
  (if (atom blocks)
      nil
    (let ((block (car blocks)))
      (cons (list (qir-block-label block)
                  (ex-fix-phis (qir-block-phis block) (ex-renames st)
                               (qir-get (qir-block-label block) bmap) st)
                  (qir-block-insts block)
                  (qir-block-jump block))
            (ex-fix-blocks (cdr blocks) bmap st)))))

; The function of QIR-M for the function FN of QIR-A. Its jumps on
; constants are folded, and each critical edge, from a block with two
; successors to a block with several predecessors, gets a block of its
; own, where the back end can place what the edge needs.
(defun expand-fn (fn symbols rtq)
  (let* ((blocks (qir-fn-blocks fn))
         (bmap (qir-block-map blocks nil))
         (rpo (qir-rpo blocks))
         (preds (qir-preds blocks))
         (uses (ex-blocks-uses blocks nil))
         (ctx (list uses (ex-blocks-negs blocks uses nil) bmap preds
                    (qir-dom-children rpo (qir-idoms-of rpo preds)) symbols
                    (ex-blocks-fields blocks nil) rtq))
         (st (ex-walk (list (cons (car rpo) (cons nil nil))) ctx
                      (ex-state nil nil nil nil (qir-next-temp fn) (qir-next-label fn)
                                nil nil nil nil)
                      (+ 1 (len blocks)))))
    (list :fn (qir-fn-name fn) (qir-fn-params fn)
          (qir-split-critical-edges
           (qir-fold-branches (ex-fix-blocks (reverse (ex-blocks st)) bmap st))
           (ex-next st)))))

(defun ex-fns (fns symbols rtq)
  (if (atom fns)
      nil
    (cons (expand-fn (car fns) symbols rtq) (ex-fns (cdr fns) symbols rtq))))

; The words of the symbols among the program's constants, from
; CONSTANTS, the index from the text of each constant to its datum that
; DATA-BUILD gives (index.lisp: a tree branching on 12 bits of the hash
; of the text, whose leaves are AVL trees). The text of a symbol begins
; with its package's name, in capitals; that of a string, a number, a
; character or a list begins otherwise.
(defun ex-symbol-text-p (text)
  (and (stringp text)
       (< 0 (length text))
       (let ((c (char-code (char text 0))))
         (and (<= 65 c) (<= c 90)))))

(defun ex-avl-symbols (tree acc)
  (if (atom tree)
      acc
    (let ((key (car (cdar tree)))
          (datum (cdr (cdar tree))))
      (ex-avl-symbols (cadr tree)
                      (ex-avl-symbols (cddr tree)
                                      (if (and (ex-symbol-text-p key) (natp datum)
                                               (equal (low-bits datum 3) 2))
                                          (qir-put datum t acc)
                                        acc))))))

(defun ex-index-symbols (tree bits acc)
  (declare (xargs :measure (nfix bits)))
  (cond ((atom tree) acc)
        ((zp bits) (ex-avl-symbols tree acc))
        (t (ex-index-symbols (car tree) (- bits 1)
                             (ex-index-symbols (cdr tree) (- bits 1) acc)))))

; P4: the program of QIR-M for the program FNS of QIR-A, with CONSTANTS
; as DATA-BUILD gives them.
(defun expand-with-constants (fns constants)
  (ex-fns fns (ex-index-symbols constants 12 nil) nil))

; P4 without the constants: no symbol but NIL and T is known.
(defun expand-functions (fns)
  (ex-fns fns nil nil))

; P4 as EXPAND-WITH-CONSTANTS, but with the slow paths of EQUAL, LENGTH
; and CHAR calling the functions of rt-qir.lisp, which the driver must
; add to the program: (APPEND (EXPAND-PROGRAM FNS CONSTANTS)
; (RT-QIR-FUNCTIONS)).
(defun expand-program (fns constants)
  (ex-fns fns (ex-index-symbols constants 12 nil) t))
