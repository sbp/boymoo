(in-package "BOYMOO-COMPILER")

(include-book "abi")

(set-verify-guards-eagerness 0)

; P7: QIR-L to MIR, A64 instructions over virtual registers
; (compiler/README.md, "MIR"). A virtual register is a temporary of QIR, (:d . N) or (:w . N);
; the pass makes new word temporaries for constants that an instruction
; needs in a register. It chooses the immediate forms of A64, fuses a
; comparison with the conditional jump or selection that is its only use,
; and tests overflow by the flags of a comparison.

(defconst *isel-2^64* 18446744073709551616)

(defun isel-word (w)
  (low-bits (ifix w) 64))

; The signed value of a word.
(defun isel-signed (w)
  (let ((u (isel-word w)))
    (if (< u 9223372036854775808) u (- u *isel-2^64*))))

(defun isel-imm12-p (u)
  (and (natp u) (< u 4096)))

; K when the word U is 2^K - 1 with K from 1 to 63, else NIL.
(defun isel-ones (u k fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((zp fuel) nil)
        ((equal u 0) (if (and (< 0 k) (< k 64)) k nil))
        ((equal (low-bits u 1) 1) (isel-ones (ash u -1) (+ k 1) (- fuel 1)))
        (t nil)))

(defun isel-mask-width (u)
  (isel-ones u 0 65))

; Use counts of the temporaries of a function, by number.

(defun isel-count-operands (xs tree)
  (cond ((atom xs) tree)
        ((qtemp-p (car xs))
         (isel-count-operands (cdr xs)
                              (ntab-put (cdar xs) (+ 1 (nfix (ntab-get (cdar xs) tree))) tree)))
        (t (isel-count-operands (cdr xs) tree))))

(defun isel-count-insts (insts tree)
  (if (atom insts)
      tree
    (isel-count-insts (cdr insts) (isel-count-operands (qinst-operands (car insts)) tree))))

(defun isel-count-blocks (blocks tree)
  (if (atom blocks)
      tree
    (isel-count-blocks (cdr blocks)
                       (isel-count-operands (qjump-operands (qblock-jump (car blocks)))
                                            (isel-count-insts (qblock-insts (car blocks)) tree)))))

; An operand in a register: a temporary as it is, or a constant loaded
; into a new word temporary. OUT holds MIR instructions in reverse order.
(defun isel-reg (x fresh out)
  (if (qconst-p x)
      (let ((r (cons :w fresh)))
        (mv r (+ fresh 1) (cons (list :li r (isel-word (cdr x))) out)))
    (mv x fresh out)))

(defun isel-commutative-p (op)
  (member op '(:add :mul :and :or :xor)))

(defun isel-reg-op (op)
  (case op
    (:add :add-reg) (:sub :sub-reg) (:mul :mul) (:and :and-reg) (:or :orr-reg)
    (:xor :eor-reg) (:shl :lslv) (:shr :lsrv) (otherwise :asrv)))

(defun isel-shift-op (op)
  (case op (:shl :lsl) (:shr :lsr) (otherwise :asr)))

; A word operation of two operands into DEST.
(defun isel-binop-ordered (dest op a b fresh out)
  (mv-let (ra fresh out)
      (isel-reg a fresh out)
      (let ((u (and (qconst-p b) (isel-word (cdr b)))))
        (cond
         ((and u (member op '(:add :sub)) (isel-imm12-p u))
          (mv fresh (cons (list :rri op dest ra u) out)))
         ((and u (member op '(:add :sub)) (isel-imm12-p (- *isel-2^64* u)))
          (mv fresh (cons (list :rri (if (eq op :add) :sub :add) dest ra (- *isel-2^64* u)) out)))
         ((and u (eq op :and) (isel-mask-width u))
          (mv fresh (cons (list :rri :and-mask dest ra (isel-mask-width u)) out)))
         ((and u (member op '(:shl :shr :sar)))
          (mv fresh (cons (list :rri (isel-shift-op op) dest ra (low-bits u 6)) out)))
         (t
          (mv-let (rb fresh out)
            (isel-reg b fresh out)
            (mv fresh (cons (list :rrr (isel-reg-op op) dest ra rb) out))))))))

(defun isel-binop (dest op a b fresh out)
  (if (and (qconst-p a) (not (qconst-p b)) (isel-commutative-p op))
      (isel-binop-ordered dest op b a fresh out)
    (isel-binop-ordered dest op a b fresh out)))

(defun isel-condition (op)
  (case op
    (:ceq :eq) (:cne :ne) (:cslt :lt) (:csle :le) (:csgt :gt) (:csge :ge)
    (:cult :lo) (:cule :ls) (:cugt :hi) (:cuge :hs) (otherwise :vs)))

(defun isel-swap-condition (c)
  (case c
    (:lt :gt) (:le :ge) (:gt :lt) (:ge :le) (:lo :hi) (:ls :hs) (:hi :lo) (:hs :ls)
    (otherwise c)))

(defun isel-compare-op-p (op)
  (member op '(:ceq :cne :cslt :csle :csgt :csge :cult :cule :cugt :cuge :ovadd :ovsub)))

; The flags of A compared with B (or added to B, for :ovadd). Gives the
; condition under which the comparison OP holds.
(defun isel-compare-ordered (op a b fresh out)
  (let ((c (isel-condition op)))
      (mv-let (ra fresh out)
        (isel-reg a fresh out)
        (let ((u (and (qconst-p b) (isel-word (cdr b))))
              (add (eq op :ovadd)))
          (cond
           ((and u (isel-imm12-p u))
            (mv c fresh (cons (list (if add :cmni :cmpi) ra u) out)))
           ((and u (isel-imm12-p (- *isel-2^64* u)))
            (mv c fresh (cons (list (if add :cmpi :cmni) ra (- *isel-2^64* u)) out)))
           (t
            (mv-let (rb fresh out)
              (isel-reg b fresh out)
              (mv c fresh (cons (list (if add :cmn :cmp) ra rb) out)))))))))

(defun isel-compare (op a b fresh out)
  (if (and (qconst-p a) (not (qconst-p b)) (not (eq op :ovsub)))
      (mv-let (c fresh out)
        (isel-compare-ordered op b a fresh out)
        (mv (isel-swap-condition c) fresh out))
    (isel-compare-ordered op a b fresh out)))

; A copy of the operand A into DEST.
(defun isel-copy (dest a out)
  (cond ((null dest) out)
        ((qconst-p a) (cons (list :li dest (isel-word (cdr a))) out))
        ((equal dest a) out)
        (t (cons (list :mov dest a) out))))

; A load of a word or a byte at the heap base plus A plus OFF.
(defun isel-load (kind dest a off fresh out)
  (mv-let (ra fresh out)
    (isel-reg a fresh out)
    (if (qconst-p off)
        (mv fresh (cons (list kind dest ra (isel-signed (cdr off))) out))
      (let ((sum (cons :w fresh)))
        (mv (+ fresh 1)
            (list* (list kind dest sum 0) (list :rrr :add-reg sum ra off) out))))))

; An operand of a selection: the constant 0 stays a constant, which P9
; writes as the zero register.
(defun isel-sel-reg (x fresh out)
  (if (and (qconst-p x) (equal (isel-word (cdr x)) 0))
      (mv (cons :k 0) fresh out)
    (isel-reg x fresh out)))

; The flags. FLAGS is NIL or (C . CONDITION): the flags hold the
; comparison that defines the word temporary C, which holds 1 exactly
; when CONDITION holds. A comparison sets them; a selection whose
; condition is not C compares its condition with 0, and so sets them to
; (C' . :NE); a call clobbers them. A first pass over a block counts the
; uses of each comparison that read the flags; a comparison all of whose
; uses do so gets no :cset.

(defun isel-tally (c tree)
  (ntab-put (cdr c) (+ 1 (nfix (ntab-get (cdr c) tree))) tree))

(defun isel-flags-after (inst flags)
  (let ((op (qinst-op inst)) (dest (qinst-dest inst)))
    (cond ((isel-compare-op-p op) (if dest (cons dest :eq) nil))
          ((eq op :sel)
           (if (and flags (equal (car flags) (car (qinst-args inst))))
               flags
             (if (qtemp-p (car (qinst-args inst))) (cons (car (qinst-args inst)) :ne) nil)))
          ((member op '(:call :rt :cons)) nil)
          (t flags))))

(defun isel-flag-uses (insts flags tree)
  (if (atom insts)
      (mv flags tree)
    (let* ((inst (car insts))
           (tree (if (and (eq (qinst-op inst) :sel) flags
                          (equal (car flags) (car (qinst-args inst))))
                     (isel-tally (car flags) tree)
                   tree)))
      (isel-flag-uses (cdr insts) (isel-flags-after inst flags) tree))))

(defun isel-block-flag-uses (b)
  (mv-let (flags tree)
    (isel-flag-uses (qblock-insts b) nil nil)
    (let ((jump (qblock-jump b)))
      (if (and flags (eq (car jump) :jnz) (equal (cadr jump) (car flags)))
          (isel-tally (car flags) tree)
        tree))))

; A conjunction with a mask of low bits whose only use is a comparison
; with 0 later in the same block, with its operand not defined again in
; between, becomes a test in that comparison. MASKED maps such a word
; temporary to (X . K), X the operand and K the width of the mask.

(defun isel-defines-p (x insts stop)
  (cond ((atom insts) nil)
        ((equal (qinst-dest (car insts)) stop) nil)
        ((equal (qinst-dest (car insts)) x) t)
        (t (isel-defines-p x (cdr insts) stop))))

(defun isel-zero-test-of (w insts)
  (cond ((atom insts) nil)
        ((and (member (qinst-op (car insts)) '(:ceq :cne))
              (equal (car (qinst-args (car insts))) w)
              (equal (cadr (qinst-args (car insts))) (cons :k 0)))
         (qinst-dest (car insts)))
        (t (isel-zero-test-of w (cdr insts)))))

(defun isel-masked (insts counts tree)
  (if (atom insts)
      tree
    (let* ((inst (car insts))
           (dest (qinst-dest inst))
           (args (qinst-args inst)))
      (isel-masked
       (cdr insts) counts
       (if (and (eq (qinst-op inst) :and) dest (qtemp-p (car args)) (qconst-p (cadr args))
                (isel-mask-width (isel-word (cdadr args)))
                (equal (ntab-get (cdr dest) counts) 1))
           (let ((test (isel-zero-test-of dest (cdr insts))))
             (if (and test (not (isel-defines-p (car args) (cdr insts) test)))
                 (ntab-put (cdr dest) (cons (car args) (isel-mask-width (isel-word (cdadr args))))
                           tree)
               tree))
         tree)))))

; One instruction. Gives FRESH, OUT and FLAGS. FUSED counts the uses of
; each comparison that read the flags.
(defun isel-inst (inst counts fused masked flags fresh out)
  (let ((dest (qinst-dest inst))
        (op (qinst-op inst))
        (args (qinst-args inst)))
    (cond
     ((eq op :copy)
      (mv fresh (isel-copy dest (car args) out) flags))
     ((isel-compare-op-p op)
      (if (null dest)
          (mv fresh out flags)
        (let ((m (and (member op '(:ceq :cne)) (qtemp-p (car args))
                      (equal (cadr args) (cons :k 0))
                      (ntab-get (cdar args) masked))))
          (mv-let (c fresh out)
            (if m
                (mv (if (eq op :ceq) :eq :ne) fresh (cons (list :tst (car m) (cdr m)) out))
              (isel-compare op (car args) (cadr args) fresh out))
            (mv fresh
                (if (equal (ntab-get (cdr dest) fused) (ntab-get (cdr dest) counts))
                    out
                  (cons (list :cset dest c) out))
                (cons dest c))))))
     ((and (eq op :and) dest (ntab-get (cdr dest) masked))
      (mv fresh out flags))
     ((member op '(:add :sub :mul :and :or :xor :shl :shr :sar))
      (if (null dest)
          (mv fresh out flags)
        (mv-let (fresh out)
          (isel-binop dest op (car args) (cadr args) fresh out)
          (mv fresh out flags))))
     ((eq op :sel)
      (cond ((null dest) (mv fresh out flags))
            ((qconst-p (car args))
             (mv fresh
                 (isel-copy dest (if (equal (isel-word (cdar args)) 0) (caddr args) (cadr args))
                            out)
                 flags))
            (t
             (mv-let (ra fresh out)
               (isel-sel-reg (cadr args) fresh out)
               (mv-let (rb fresh out)
                 (isel-sel-reg (caddr args) fresh out)
                 (if (and flags (equal (car flags) (car args)))
                     (mv fresh (cons (list :csel dest ra rb (cdr flags)) out) flags)
                   (mv fresh
                       (list* (list :csel dest ra rb :ne) (list :cmpi (car args) 0) out)
                       (cons (car args) :ne))))))))
     ((member op '(:ld :ldb))
      (if (null dest)
          (mv fresh out flags)
        (mv-let (fresh out)
          (isel-load op dest (car args) (cadr args) fresh out)
          (mv fresh out flags))))
     ((eq op :cons)
      (mv fresh (cons (list :rt "prim:COMMON-LISP::CONS" args dest) out) nil))
     ((eq op :rt)
      (mv fresh (cons (list :rt (car args) (cdr args) dest) out) nil))
     ((eq op :call)
      (mv fresh (cons (list :call (car args) (cdr args) dest) out) nil))
     ((eq op :spill)
      (mv-let (ra fresh out)
        (isel-reg (cadr args) fresh out)
        (mv fresh (cons (list :vst ra (car args)) out) flags)))
     ((eq op :reload)
      (mv fresh (cons (list :vld dest (car args)) out) flags))
     (t (mv (compiler-error "Unknown QIR-L instruction: ~x0." inst) out nil)))))

(defun isel-insts (insts counts fused masked flags fresh out)
  (if (atom insts)
      (mv fresh out flags)
    (mv-let (fresh out flags)
      (isel-inst (car insts) counts fused masked flags fresh out)
      (isel-insts (cdr insts) counts fused masked flags fresh out))))

; The jump of a block. Gives FRESH, OUT and the terminator. When the
; flags hold the test of bit 0 that the jump reads, and the test is the
; last instruction, the test and the branch become one :tbnz, if TBNZ.
(defun isel-jump (jump flags tbnz fresh out)
  (let ((op (car jump)))
    (cond
     ((and flags (eq op :jnz) (equal (cadr jump) (car flags)))
      (let ((last (car out)))
        (if (and tbnz (eq (car last) :tst) (equal (caddr last) 1)
                 (member (cdr flags) '(:eq :ne)))
            (mv fresh (cdr out)
                (if (eq (cdr flags) :ne)
                    (list :tbnz (cadr last) 0 (caddr jump) (cadddr jump))
                  (list :tbnz (cadr last) 0 (cadddr jump) (caddr jump))))
          (mv fresh out (list :bc (cdr flags) (caddr jump) (cadddr jump))))))
     (t
      (case op
        (:jmp (mv fresh out (list :b (cadr jump))))
        (:jnz (if (qconst-p (cadr jump))
                  (mv fresh out (list :b (if (equal (isel-word (cdadr jump)) 0)
                                             (cadddr jump)
                                           (caddr jump))))
                (mv fresh out (list :cbnz (cadr jump) (caddr jump) (cadddr jump)))))
        (:if (if (qconst-p (cadr jump))
                 (mv fresh out (list :b (if (equal (isel-word (cdadr jump)) 34)
                                            (cadddr jump)
                                          (caddr jump))))
               (mv fresh (cons (list :cmpi (cadr jump) 34) out)
                   (list :bc :ne (caddr jump) (cadddr jump)))))
        (:ret (mv fresh out jump))
        (:tail (mv fresh out (list :tail (cadr jump) (cddr jump))))
        (:undef (mv fresh out (list :undef (isel-word (cadr jump)))))
        (otherwise (mv (compiler-error "Unknown QIR-L jump: ~x0." jump) out nil)))))))

; A call of prim:COMMON-LISP::CONS lists, as a fifth field, the
; registers that the loads right after it load: P9 makes those loads only
; on the slow path, so the registers must hold their values at the call,
; which counts as a use of them.
(defun isel-loads-after (insts acc)
  (if (and (consp insts) (eq (car (car insts)) :vld))
      (isel-loads-after (cdr insts) (cons (cadr (car insts)) acc))
    (reverse-onto acc nil)))

(defun isel-mark-conses (insts)
  (if (atom insts)
      nil
    (let ((inst (car insts)))
      (cons (if (and (eq (car inst) :rt) (equal (cadr inst) "prim:COMMON-LISP::CONS"))
                (list :rt (cadr inst) (caddr inst) (cadddr inst) (isel-loads-after (cdr insts) nil))
              inst)
            (isel-mark-conses (cdr insts))))))

(defun isel-blocks (blocks counts tbnz fresh)
  (if (atom blocks)
      (mv nil fresh)
    (let* ((b (car blocks))
           (fused (isel-block-flag-uses b))
           (masked (isel-masked (qblock-insts b) counts nil)))
      (mv-let (fresh out flags)
        (isel-insts (qblock-insts b) counts fused masked nil fresh nil)
        (mv-let (fresh out term)
          (isel-jump (qblock-jump b) flags tbnz fresh out)
          (mv-let (rest fresh)
            (isel-blocks (cdr blocks) counts tbnz fresh)
            (mv (cons (list (qblock-label b) (isel-mark-conses (reverse-onto out nil)) term) rest)
                fresh)))))))

(defun isel-count-all (blocks n)
  (if (atom blocks)
      n
    (isel-count-all (cdr blocks) (+ n 1 (len (qblock-insts (car blocks)))))))

; A MIR function: (:MFN NAME PARAMS NSLOTS BLOCKS NEXT), where NEXT is
; above the number of every virtual register.
(defun isel-function (fn)
  (let* ((name (cadr fn))
         (params (caddr fn))
         (blocks (cadddr fn))
         (nslots (car (cddddr fn)))
         (fresh (+ 1 (abi-max-temp blocks (abi-max-operands params 0)))))
    (mv-let (mblocks fresh)
      (isel-blocks blocks (isel-count-blocks blocks nil) (< (isel-count-all blocks 0) 1000) fresh)
      (list :mfn name params nslots mblocks fresh))))

(defun isel-program (fns)
  (if (atom fns)
      nil
    (cons (isel-function (car fns)) (isel-program (cdr fns)))))
