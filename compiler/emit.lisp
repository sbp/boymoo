(in-package "BOYMOO-COMPILER")

(include-book "rega")

(set-verify-guards-eagerness 0)

; P9: MIR with homes to assembly items (compiler/README.md, "The assembly
; language"). It writes the prologue and the epilogues, the moves of the
; arguments of calls, the parameters and the results, and lays out the
; blocks in their order, with a jump left out where the next block is its
; target. x16 and x17 are its scratch registers. Items are consed in
; reverse order onto CODE.

(defun emit-items (items code)
  (reverse-onto items code))

; A 64-bit word into the register RD.

(defun emit-half (u i)
  (low-bits (ash u (* -16 i)) 16))

(defun emit-count-halves (u value i n)
  (declare (xargs :measure (nfix (- 4 i))))
  (if (or (not (natp i)) (<= 4 i))
      n
    (emit-count-halves u value (+ i 1) (if (equal (emit-half u i) value) (+ n 1) n))))

; The halves of U other than the half FIRST and those equal to SKIP, as
; movk items.
(defun emit-movks (rd u first skip i code)
  (declare (xargs :measure (nfix (- 4 i))))
  (if (or (not (natp i)) (<= 4 i))
      code
    (emit-movks rd u first skip (+ i 1)
                (if (or (equal i first) (equal (emit-half u i) skip))
                    code
                  (cons (list :movk rd (emit-half u i) (* 16 i)) code)))))

(defun emit-first-half (u skip i)
  (declare (xargs :measure (nfix (- 4 i))))
  (cond ((or (not (natp i)) (<= 4 i)) 0)
        ((equal (emit-half u i) skip) (emit-first-half u skip (+ i 1)))
        (t i)))

(defun emit-load-word (rd w code)
  (let* ((u (isel-word w))
         (ones (emit-count-halves u 65535 0 0))
         (zeros (emit-count-halves u 0 0 0)))
    (if (< zeros ones)
        (let ((first (emit-first-half u 65535 0)))
          (emit-movks rd u first 65535 0
                      (cons (list :movn rd (- 65535 (emit-half u first)) (* 16 first)) code)))
      (let ((first (emit-first-half u 0 0)))
        (emit-movks rd u first 0 0
                    (cons (list :movz rd (emit-half u first) (* 16 first)) code))))))

; RD := RN + N for any integer N; RD and RN are not sp. Uses x17 for a
; large N.
(defun emit-add-imm (rd rn n code)
  (cond ((and (equal n 0) (equal rd rn)) code)
        ((and (<= 0 n) (< n 4096)) (cons (list :add rd rn n) code))
        ((and (< n 0) (< (- n) 4096)) (cons (list :sub rd rn (- n)) code))
        ((< n 0) (cons (list :sub-reg rd rn 17 0) (emit-load-word 17 (- n) code)))
        (t (cons (list :add-reg rd rn 17 0) (emit-load-word 17 n code)))))

; The function's frame, as the emitter needs it.
(defun emit-ctx (name nslots nparams frame calls wrap check)
  (list name nslots nparams frame calls wrap check))

(defun ectx-name (ctx) (car ctx))
(defun ectx-nslots (ctx) (cadr ctx))
(defun ectx-nparams (ctx) (caddr ctx))
(defun ectx-frame (ctx) (cadddr ctx))
(defun ectx-calls (ctx) (car (cddddr ctx)))
(defun ectx-wrap (ctx) (cadr (cddddr ctx)))
(defun ectx-check (ctx) (caddr (cddddr ctx)))

; A call of a routine of the runtime. A function with no frame keeps its
; link on the machine stack around each such call.
(defun emit-rt-call (ctx label code)
  (if (ectx-wrap ctx)
      (emit-items (list '(:stp-pre 29 30 31 -16) (list :bl label) '(:ldp-post 29 30 31 16)) code)
    (cons (list :bl label) code)))

(defun emit-stack-params (ctx)
  (let ((n (ectx-nparams ctx)))
    (if (< 8 n) (- n 8) 0)))

(defun emit-block-label (ctx label)
  (list :blk (ectx-name ctx) label))

(defun emit-slot-offset (k)
  (+ 8 (* 8 k)))

; A source operand in a register: its own, or SCRATCH loaded from its
; slot or with its constant.
(defun emit-src (h scratch code)
  (case (car h)
    (:x (mv (cdr h) code))
    (:m (mv scratch (cons (list :ldr scratch 31 (emit-slot-offset (cdr h))) code)))
    (otherwise (mv scratch (emit-load-word scratch (cdr h) code)))))

; An operand of :csel, where the constant 0 is the zero register.
(defun emit-src-z (h scratch code)
  (if (and (eq (car h) :k) (equal (cdr h) 0))
      (mv 31 code)
    (emit-src h scratch code)))

(defun emit-dst (h)
  (if (eq (car h) :x) (cdr h) 16))

(defun emit-store-dst (h code)
  (if (eq (car h) :m)
      (cons (list :str 16 31 (emit-slot-offset (cdr h))) code)
    code))

; The home H into the register R.
(defun emit-into (r h code)
  (case (car h)
    (:x (if (equal (cdr h) r) code (cons (list :mov r (cdr h)) code)))
    (:m (cons (list :ldr r 31 (emit-slot-offset (cdr h))) code))
    (otherwise (emit-load-word r (cdr h) code))))

; The register R into the home H.
(defun emit-from (h r code)
  (case (car h)
    (:x (if (equal (cdr h) r) code (cons (list :mov (cdr h) r) code)))
    (:m (cons (list :str r 31 (emit-slot-offset (cdr h))) code))
    (otherwise code)))

; Parallel moves between registers, a list of (DEST . SOURCE), with x16
; to break a cycle.

(defun emit-drop-self (moves)
  (cond ((atom moves) nil)
        ((equal (caar moves) (cdar moves)) (emit-drop-self (cdr moves)))
        (t (cons (car moves) (emit-drop-self (cdr moves))))))

(defun emit-reg-moves (moves code fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((moves (emit-drop-self moves)))
    (cond ((atom moves) code)
          ((zp fuel) (compiler-error "Parallel move did not finish: ~x0." moves))
          (t
           (let ((free (abi-free-copy moves moves)))
             (if free
                 (emit-reg-moves (abi-remove-copy free moves)
                                 (cons (list :mov (car free) (cdr free)) code) (- fuel 1))
               (let ((d (caar moves)))
                 (emit-reg-moves (abi-replace-source d 16 moves)
                                 (cons (list :mov 16 d) code) (- fuel 1)))))))))

; The fast path of CONS, with its two data in x0 and x1, as the runtime's
; prim:COMMON-LISP::CONS has it: when x26 - x27 leaves 16 bytes, the
; next cons address, kept at x28 - 112, and x26 go down by 16, and the
; cons is written there; otherwise the routine is called, at SLOW. The
; datum is left in x0.
(defun emit-cons-fast (slow done)
  (list '(:sub-reg 16 26 27 0) '(:cmp 16 16) (list :b-cond :lo slow)
        '(:ldur 17 28 -112) '(:sub 17 17 16) '(:stur 17 28 -112) '(:sub 26 26 16)
        '(:stp 0 1 17 0) '(:sub-reg 0 17 28 0) (list :label done)))

; A cons whose two arguments are in registers writes them from there,
; and its result straight into its home; its slow path moves them into
; x0 and x1 and moves the result from x0.
(defun emit-cons-direct-p (inst)
  (let ((args (caddr inst)))
    (and (eq (car (car args)) :x) (eq (car (cadr args)) :x))))

(defun emit-cons-direct (inst slow done code)
  (let* ((args (caddr inst))
         (d (cadddr inst))
         (code (emit-items (list '(:sub-reg 16 26 27 0) '(:cmp 16 16) (list :b-cond :lo slow)
                                 '(:ldur 17 28 -112) '(:sub 17 17 16) '(:stur 17 28 -112)
                                 '(:sub 26 26 16)
                                 (list :stp (cdr (car args)) (cdr (cadr args)) 17 0))
                           code))
         (code (if d
                   (emit-store-dst d (cons (list :sub-reg (emit-dst d) 17 28 0) code))
                 code)))
    (cons (list :label done) code)))

(defun emit-cons-p (inst)
  (and (eq (car inst) :rt) (equal (cadr inst) "prim:COMMON-LISP::CONS")))

(defun emit-cons-label (ctx where kind)
  (list :blk (ectx-name ctx) kind (car where) (cdr where)))

; The moves of operands ARGS into x0 onwards, at most eight.
(defun emit-arg-reg-moves (args r acc)
  (cond ((or (atom args) (< 7 r)) acc)
        ((and (eq (car (car args)) :x) (not (equal (cdr (car args)) r)))
         (emit-arg-reg-moves (cdr args) (+ r 1) (cons (cons r (cdr (car args))) acc)))
        (t (emit-arg-reg-moves (cdr args) (+ r 1) acc))))

(defun emit-arg-other-moves (args r code)
  (cond ((or (atom args) (< 7 r)) code)
        ((eq (car (car args)) :x) (emit-arg-other-moves (cdr args) (+ r 1) code))
        (t (emit-arg-other-moves (cdr args) (+ r 1) (emit-into r (car args) code)))))

(defun emit-arg-moves (args code)
  (let ((moves (emit-arg-reg-moves args 0 nil)))
    (emit-arg-other-moves args 0 (emit-reg-moves moves code (+ 2 (* 2 (len moves)))))))

; The arguments after the eighth, stored from x25 upward.
(defun emit-stack-args (args j code)
  (if (atom args)
      code
    (mv-let (r code)
      (emit-src (car args) 16 code)
      (emit-stack-args (cdr args) (+ j 1) (cons (list :str r 25 (* 8 j)) code)))))

(defun emit-nthcdr8 (args)
  (nthcdr 8 args))

; A word at the address x25 + OFF, OFF negative, into or from R.
(defun emit-vstack (load r off code)
  (if (<= -256 off)
      (cons (list (if load :ldur :stur) r 25 off) code)
    (cons (list (if load :ldr :str) r 17 0) (emit-add-imm 17 25 off code))))

(defun emit-slot-address (ctx i)
  (* -8 (- (ectx-nslots ctx) i)))

; A load of the word or byte at x28 + RA + OFF into RD.
(defun emit-load (byte rd ra off code)
  (if (equal off 0)
      (cons (list (if byte :ldrb-reg :ldr-reg) rd 28 ra) code)
    (let ((code (cons (list :add-reg 17 28 ra 0) code)))
      (cond ((and byte (<= 0 off) (< off 4096)) (cons (list :ldrb rd 17 off) code))
            ((and (not byte) (<= 0 off) (<= off 32760) (equal (low-bits off 3) 0))
             (cons (list :ldr rd 17 off) code))
            ((and (<= -256 off) (< off 256)) (cons (list (if byte :ldurb :ldur) rd 17 off) code))
            (t (cons (list (if byte :ldrb :ldr) rd 17 0) (emit-add-imm 17 17 off code)))))))

(defun emit-inst (inst ctx where code)
  (case (car inst)
    (:mov
     (let ((d (cadr inst)) (s (caddr inst)))
       (if (eq (car d) :x)
           (emit-into (cdr d) s code)
         (mv-let (r code)
           (emit-src s 16 code)
           (emit-from d r code)))))
    (:li
     (let ((d (cadr inst)))
       (emit-store-dst d (emit-load-word (emit-dst d) (caddr inst) code))))
    (:rrr
     (let ((op (cadr inst)) (d (caddr inst)))
       (mv-let (ra code)
         (emit-src (cadddr inst) 16 code)
         (mv-let (rb code)
           (emit-src (car (cddddr inst)) 17 code)
           (emit-store-dst d (cons (if (member op '(:add-reg :sub-reg))
                                       (list op (emit-dst d) ra rb 0)
                                     (list op (emit-dst d) ra rb))
                                   code))))))
    (:rri
     (let ((d (caddr inst)))
       (mv-let (ra code)
         (emit-src (cadddr inst) 16 code)
         (emit-store-dst d (cons (list (cadr inst) (emit-dst d) ra (car (cddddr inst))) code)))))
    ((:cmp :cmn)
     (mv-let (ra code)
       (emit-src (cadr inst) 16 code)
       (mv-let (rb code)
         (emit-src (caddr inst) 17 code)
         (cons (if (eq (car inst) :cmp) (list :cmp-reg ra rb) (list :adds-reg 31 ra rb 0)) code))))
    (:tst
     (mv-let (ra code)
       (emit-src (cadr inst) 16 code)
       (cons (list :tst-mask ra (caddr inst)) code)))
    ((:cmpi :cmni)
     (mv-let (ra code)
       (emit-src (cadr inst) 16 code)
       (cons (list (if (eq (car inst) :cmpi) :cmp :cmn) ra (caddr inst)) code)))
    (:cset
     (let ((d (cadr inst)))
       (emit-store-dst d (cons (list :cset (emit-dst d) (caddr inst)) code))))
    (:csel
     (let ((d (cadr inst)))
       (mv-let (ra code)
         (emit-src-z (caddr inst) 16 code)
         (mv-let (rb code)
           (emit-src-z (cadddr inst) 17 code)
           (emit-store-dst d (cons (list :csel (emit-dst d) ra rb (car (cddddr inst))) code))))))
    ((:ld :ldb)
     (let ((d (cadr inst)))
       (mv-let (ra code)
         (emit-src (caddr inst) 16 code)
         (emit-store-dst d (emit-load (eq (car inst) :ldb) (emit-dst d) ra (cadddr inst) code)))))
    (:vld
     (let ((d (cadr inst)))
       (emit-store-dst d (emit-vstack t (emit-dst d) (emit-slot-address ctx (caddr inst)) code))))
    (:vst
     (mv-let (r code)
       (emit-src (cadr inst) 16 code)
       (emit-vstack nil r (emit-slot-address ctx (caddr inst)) code)))
    (:call
     (let* ((args (caddr inst))
            (more (emit-nthcdr8 args))
            (code (emit-stack-args more 0 code))
            (code (if (consp more) (emit-add-imm 25 25 (* 8 (len more)) code) code))
            (code (emit-arg-moves args code))
            (code (cons (list :bl (list :fn (cadr inst))) code)))
       (if (cadddr inst) (emit-from (cadddr inst) 0 code) code)))
    (:rt
     (if (and (emit-cons-p inst) (emit-cons-direct-p inst))
         (emit-cons-direct inst (emit-cons-label ctx where :slow) (emit-cons-label ctx where :done)
                           code)
       (let* ((code (emit-arg-moves (caddr inst) code))
              (code (if (emit-cons-p inst)
                        (emit-items (emit-cons-fast (emit-cons-label ctx where :slow)
                                                    (emit-cons-label ctx where :done))
                                    code)
                      (emit-rt-call ctx (cadr inst) code))))
         (if (cadddr inst) (emit-from (cadddr inst) 0 code) code))))
    (otherwise (compiler-error "Unknown MIR instruction: ~x0." inst))))

; A cons group: stores to the value stack, then a cons, then loads from
; it. When no stored or loaded home is x0 or x1, which the cons's
; arguments and result use, and no loaded home is that of the cons's
; result, the fast path leaves every loaded home as it was, so the stores
; and loads are needed only on the slow path, which may collect.

(defun emit-leading (insts op acc)
  (if (and (consp insts) (eq (car (car insts)) op))
      (emit-leading (cdr insts) op (cons (car insts) acc))
    (mv (reverse-onto acc nil) insts)))

(defun emit-homes-clear-p (homes avoid)
  (cond ((atom homes) t)
        ((member-equal (car homes) avoid) nil)
        (t (emit-homes-clear-p (cdr homes) avoid))))

(defun emit-seconds (insts)
  (if (atom insts) nil (cons (cadr (car insts)) (emit-seconds (cdr insts)))))

; Gives the stores, the cons and the loads of a cons group at the head of
; INSTS whose stores and loads can be moved to the slow path, or NIL.
(defun emit-cons-group (insts)
  (mv-let (stores rest)
    (emit-leading insts :vst nil)
    (if (and (consp rest) (emit-cons-p (car rest)))
        (mv-let (loads after)
          (emit-leading (cdr rest) :vld nil)
          (declare (ignore after))
          (let ((avoid (list (cons :x 0) (cons :x 1) (cadddr (car rest)))))
            (if (and (emit-homes-clear-p (emit-seconds stores) (list (cons :x 0) (cons :x 1)))
                     (emit-homes-clear-p (emit-seconds loads) avoid))
                (list stores (car rest) loads)
              nil)))
      nil)))

; FUEL bounds the number of steps, each of which takes at least one
; instruction; the callers give the number of instructions.
(defun emit-insts-fuel (insts ctx label i code fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (atom insts) (zp fuel))
      code
    (let ((group (emit-cons-group insts)))
      (if group
          (let ((n (+ (len (car group)) 1 (len (caddr group)))))
            (emit-insts-fuel (nthcdr n insts) ctx label (+ i n)
                             (emit-inst (cadr group) ctx (cons label i) code) (- fuel 1)))
        (emit-insts-fuel (cdr insts) ctx label (+ i 1)
                         (emit-inst (car insts) ctx (cons label i) code) (- fuel 1))))))

(defun emit-insts (insts ctx label i code)
  (emit-insts-fuel insts ctx label i code (len insts)))

; The slow paths of the conses of a block, after the code of the
; function: each makes the stores of its group, calls the routine, makes
; the loads and goes back.
; The call of the routine on the slow path of a cons, with the moves of
; its arguments when the fast path wrote them from their own registers,
; and then the move of its result.
(defun emit-cons-slow-call (inst ctx code)
  (emit-rt-call ctx "prim:COMMON-LISP::CONS"
                (if (emit-cons-direct-p inst) (emit-arg-moves (caddr inst) code) code)))

(defun emit-cons-slow-result (inst code)
  (if (and (emit-cons-direct-p inst) (cadddr inst))
      (emit-from (cadddr inst) 0 code)
    code))

(defun emit-cons-stubs-fuel (insts ctx label i code fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (atom insts) (zp fuel))
      code
    (let ((group (emit-cons-group insts)))
      (if group
          (let ((n (+ (len (car group)) 1 (len (caddr group))))
                (where (cons label i)))
            (emit-cons-stubs-fuel
             (nthcdr n insts) ctx label (+ i n)
             (cons (list :b (emit-cons-label ctx where :done))
                   (emit-cons-slow-result
                    (cadr group)
                    (emit-insts (caddr group) ctx label (+ i n)
                                (emit-cons-slow-call
                                 (cadr group) ctx
                                 (emit-insts (car group) ctx label i
                                             (cons (list :label (emit-cons-label ctx where :slow))
                                                   code))))))
             (- fuel 1)))
        (emit-cons-stubs-fuel
         (cdr insts) ctx label (+ i 1)
         (if (emit-cons-p (car insts))
             (cons (list :b (emit-cons-label ctx (cons label i) :done))
                   (emit-cons-slow-result
                    (car insts)
                    (emit-cons-slow-call
                     (car insts) ctx
                     (cons (list :label (emit-cons-label ctx (cons label i) :slow)) code))))
           code)
         (- fuel 1))))))

(defun emit-cons-stubs (insts ctx label i code)
  (emit-cons-stubs-fuel insts ctx label i code (len insts)))

(defun emit-blocks-stubs (blocks ctx code)
  (if (atom blocks)
      code
    (emit-blocks-stubs (cdr blocks) ctx
                       (emit-cons-stubs (cadr (car blocks)) ctx (car (car blocks)) 0 code))))

(defun emit-negate (c)
  (case c
    (:eq :ne) (:ne :eq) (:hs :lo) (:lo :hs) (:mi :pl) (:pl :mi) (:vs :vc) (:vc :vs)
    (:hi :ls) (:ls :hi) (:ge :lt) (:lt :ge) (:gt :le) (:le :gt) (otherwise c)))

; The machine frame and the value-stack frame are removed.
; sp := sp + N, N from -32768 to 32768, through x16 when N is large.
(defun emit-sp-add (n code)
  (cond ((and (<= 0 n) (< n 4096)) (cons (list :add 31 31 n) code))
        ((and (< n 0) (< (- n) 4096)) (cons (list :sub 31 31 (- n)) code))
        (t (cons '(:mov-sp 31 16) (emit-add-imm 16 16 n (cons '(:mov-sp 16 31) code))))))

(defun emit-leave (ctx x25 code)
  (let* ((code (emit-add-imm 25 25 x25 code))
         (frame (ectx-frame ctx)))
    (if (zp frame)
        code
      (emit-sp-add frame (if (ectx-calls ctx) (cons '(:ldr 30 31 0) code) code)))))

(defun emit-down-args (m j base code)
  (declare (xargs :measure (nfix (- m j))))
  (if (or (not (natp j)) (not (natp m)) (<= m j))
      code
    (emit-down-args m (+ j 1) base
                    (emit-items (list (list :ldr 16 25 (* 8 j)) (list :str 16 17 (+ base (* 8 j))))
                                code))))

(defun emit-term (term ctx next code)
  (let ((own (* -8 (+ (ectx-nslots ctx) (emit-stack-params ctx)))))
    (case (car term)
      (:b (if (equal (cadr term) next)
              code
            (cons (list :b (emit-block-label ctx (cadr term))) code)))
      (:bc
       (let ((c (cadr term)) (l1 (caddr term)) (l0 (cadddr term)))
         (cond ((equal l0 next) (cons (list :b-cond c (emit-block-label ctx l1)) code))
               ((equal l1 next) (cons (list :b-cond (emit-negate c) (emit-block-label ctx l0)) code))
               (t (emit-items (list (list :b-cond c (emit-block-label ctx l1))
                                    (list :b (emit-block-label ctx l0)))
                              code)))))
      (:cbnz
       (mv-let (r code)
         (emit-src (cadr term) 16 code)
         (let ((l1 (caddr term)) (l0 (cadddr term)))
           (cond ((equal l0 next) (cons (list :cbnz r (emit-block-label ctx l1)) code))
                 ((equal l1 next) (cons (list :cbz r (emit-block-label ctx l0)) code))
                 (t (emit-items (list (list :cbnz r (emit-block-label ctx l1))
                                      (list :b (emit-block-label ctx l0)))
                                code))))))
      (:tbnz
       (mv-let (r code)
         (emit-src (cadr term) 16 code)
         (let ((bit (caddr term)) (l1 (cadddr term)) (l0 (car (cddddr term))))
           (cond ((equal l0 next) (cons (list :tbnz r bit (emit-block-label ctx l1)) code))
                 ((equal l1 next) (cons (list :tbz r bit (emit-block-label ctx l0)) code))
                 (t (emit-items (list (list :tbnz r bit (emit-block-label ctx l1))
                                      (list :b (emit-block-label ctx l0)))
                                code))))))
      (:ret
       (cons '(:ret) (emit-leave ctx own (emit-into 0 (cadr term) code))))
      (:tail
       (let* ((args (caddr term))
              (more (emit-nthcdr8 args))
              (m (len more))
              (code (emit-stack-args more 0 code))
              (code (emit-arg-moves args code))
              (code (if (consp more)
                        (emit-down-args m 0 0 (emit-add-imm 17 25 own code))
                      code)))
         (cons (list :b (list :fn (cadr term)))
               (emit-leave ctx (+ own (* 8 m)) code))))
      (:undef
       (cons '(:bl "rt:undefined") (emit-load-word 0 (cadr term) code)))
      (otherwise (compiler-error "Unknown MIR terminator: ~x0." term)))))

(defun emit-blocks (blocks ctx code)
  (if (atom blocks)
      code
    (let ((b (car blocks)))
      (emit-blocks (cdr blocks) ctx
                   (emit-term (caddr b) ctx (if (consp (cdr blocks)) (car (cadr blocks)) nil)
                              (emit-insts (cadr b) ctx (car b) 0
                                          (cons (list :label (emit-block-label ctx (car b)))
                                                code)))))))

; The facts about a function's calls: whether it calls (and so must keep
; its link), and the most arguments it passes on the value stack.
(defun emit-calls-insts (insts calls most)
  (if (atom insts)
      (mv calls most)
    (let ((inst (car insts)))
      (case (car inst)
        (:call (emit-calls-insts (cdr insts) t
                                 (let ((m (len (emit-nthcdr8 (caddr inst))))) (if (< most m) m most))))
        (:rt (emit-calls-insts (cdr insts) t most))
        (otherwise (emit-calls-insts (cdr insts) calls most))))))

(defun emit-calls (blocks calls most)
  (if (atom blocks)
      (mv calls most)
    (mv-let (calls most)
      (emit-calls-insts (cadr (car blocks)) calls most)
      (let* ((term (caddr (car blocks)))
             (m (if (eq (car term) :tail) (len (emit-nthcdr8 (caddr term))) 0)))
        (emit-calls (cdr blocks) (or calls (< 0 m)) (if (< most m) m most))))))

(defun emit-compiled-calls-insts-p (insts)
  (cond ((atom insts) nil)
        ((eq (car (car insts)) :call) t)
        (t (emit-compiled-calls-insts-p (cdr insts)))))

(defun emit-compiled-calls-p (blocks)
  (cond ((atom blocks) nil)
        ((emit-compiled-calls-insts-p (cadr (car blocks))) t)
        (t (emit-compiled-calls-p (cdr blocks)))))

; Slots of the value stack cleared from x25 upward, in runs of at most 62
; words, x25 rising after each run. (P6 clears or stores each slot before
; anything can collect, so the prologue does not clear them.)
(defun emit-clear-run (i n code)
  (declare (xargs :measure (nfix (- n i))))
  (cond ((or (not (natp i)) (not (natp n)) (<= n i)) code)
        ((< (+ i 1) n)
         (emit-clear-run (+ i 2) n (cons (list :stp 16 16 25 (* 8 i)) code)))
        (t (cons (list :str 16 25 (* 8 i)) code))))

(defun emit-clear-slots (n code)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) code)
        ((< 62 n)
         (emit-clear-slots (- n 62) (emit-add-imm 25 25 (* 8 62) (emit-clear-run 0 62 code))))
        (t (emit-add-imm 25 25 (* 8 n) (emit-clear-run 0 n code)))))

; The parameters move from x0 to x7 and from the value stack to their
; homes: first those whose home is a slot, then the parallel moves
; between registers, then those on the value stack.
(defun emit-param-stores (homes r code)
  (cond ((or (atom homes) (< 7 r)) code)
        ((eq (car (car homes)) :m)
         (emit-param-stores (cdr homes) (+ r 1)
                            (cons (list :str r 31 (emit-slot-offset (cdr (car homes)))) code)))
        (t (emit-param-stores (cdr homes) (+ r 1) code))))

(defun emit-param-reg-moves (homes r acc)
  (cond ((or (atom homes) (< 7 r)) acc)
        ((and (eq (car (car homes)) :x) (not (equal (cdr (car homes)) r)))
         (emit-param-reg-moves (cdr homes) (+ r 1) (cons (cons (cdr (car homes)) r) acc)))
        (t (emit-param-reg-moves (cdr homes) (+ r 1) acc))))

(defun emit-param-loads (homes off code)
  (if (atom homes)
      code
    (let ((h (car homes)))
      (emit-param-loads (cdr homes) (+ off 8)
                        (emit-store-dst h (emit-vstack t (emit-dst h) off code))))))

(defun emit-params (homes ctx code)
  (let* ((code (emit-param-stores homes 0 code))
         (moves (emit-param-reg-moves homes 0 nil))
         (code (emit-reg-moves moves code (+ 2 (* 2 (len moves))))))
    (emit-param-loads (emit-nthcdr8 homes)
                      (* -8 (+ (ectx-nslots ctx) (emit-stack-params ctx)))
                      code)))

; The slow paths of the prologue, after the function's code: the call of
; rt:deep, which does not return, and that of rt:ensure-stack.
(defun emit-prologue-stubs (ctx most code)
  (let* ((name (ectx-name ctx))
         (code (if (or (zp (ectx-frame ctx)) (not (ectx-check ctx)))
                   code
                 (emit-items (list (list :label (list :blk name :deep)) '(:bl "rt:deep")) code))))
    (if (zp (+ (ectx-nslots ctx) most))
        code
      (emit-items (list (list :label (list :blk name :grow)) '(:bl "rt:ensure-stack")
                        (list :b (list :blk name :grown)))
                  code))))

(defun emit-prologue (ctx most code)
  (let* ((name (ectx-name ctx))
         (frame (ectx-frame ctx))
         (nslots (ectx-nslots ctx))
         (code (cond ((zp frame) code)
                     ((not (ectx-check ctx)) (emit-sp-add (- frame) code))
                     (t (let ((deep (list :blk name :deep)))
                          (emit-items (list '(:cmp-reg 16 23) (list :b-cond :lo deep)
                                            '(:mov-sp 31 16))
                                      (if (< frame 4096)
                                          (cons (list :sub 16 31 frame) code)
                                        (emit-add-imm 16 16 (- frame)
                                                      (cons '(:mov-sp 16 31) code))))))))
         (code (if (ectx-calls ctx) (cons '(:str 30 31 0) code) code))
         (code (if (zp (+ nslots most))
                   code
                 (emit-items (list '(:cmp-reg 8 24) (list :b-cond :hi (list :blk name :grow))
                                   (list :label (list :blk name :grown)))
                             (emit-add-imm 8 25 (* 8 (+ nslots most)) code)))))
    (emit-add-imm 25 25 (* 8 nslots) code)))

; Jumps to jumps. A block other than the first that has no instruction
; and only jumps is left out, and every jump to it goes to its target.

(defun emit-thread-map (blocks first tree)
  (if (atom blocks)
      tree
    (let ((b (car blocks)))
      (emit-thread-map (cdr blocks) first
                       (if (and (not (equal (car b) first)) (atom (cadr b))
                                (eq (car (caddr b)) :b) (not (equal (cadr (caddr b)) (car b))))
                           (ntab-put (car b) (cadr (caddr b)) tree)
                         tree)))))

(defun emit-thread (label map fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((next (ntab-get label map)))
    (if (or (zp fuel) (not next))
        label
      (emit-thread next map (- fuel 1)))))

(defun emit-thread-term (term map fuel)
  (case (car term)
    (:b (list :b (emit-thread (cadr term) map fuel)))
    ((:bc :cbnz)
     (let ((l1 (emit-thread (caddr term) map fuel))
           (l0 (emit-thread (cadddr term) map fuel)))
       (if (and (equal l1 l0) (eq (car term) :cbnz))
           (list :b l1)
         (list (car term) (cadr term) l1 l0))))
    (:tbnz
     (list :tbnz (cadr term) (caddr term)
           (emit-thread (cadddr term) map fuel) (emit-thread (car (cddddr term)) map fuel)))
    (otherwise term)))

(defun emit-thread-blocks (blocks map fuel)
  (cond ((atom blocks) nil)
        ((ntab-get (car (car blocks)) map) (emit-thread-blocks (cdr blocks) map fuel))
        (t (cons (list (car (car blocks)) (cadr (car blocks))
                       (emit-thread-term (caddr (car blocks)) map fuel))
                 (emit-thread-blocks (cdr blocks) map fuel)))))

; The frame of a function: (MV CALLS MOST WRAP FRAME). CALLS when it
; keeps its link in its frame, MOST the most arguments it passes on the
; value stack, WRAP when it has no frame and keeps its link around each
; call of a routine, FRAME the bytes of its machine frame.
(defun emit-frame-of (blocks nslots nspill)
  (mv-let (calls most)
    (emit-calls blocks nil 0)
    (let* ((wrap (and calls (not (emit-compiled-calls-p blocks)) (zp nslots) (zp nspill) (zp most)))
           (calls (and calls (not wrap)))
           (frame (if (or calls (< 0 nspill))
                      (* 16 (ash (+ 8 (* 8 nspill) 15) -4))
                    0)))
      (mv calls most wrap frame))))

(defun emit-mfn-blocks (mfn)
  (let ((blocks (car (cddddr mfn))))
    (emit-thread-blocks blocks (emit-thread-map blocks (car (car blocks)) nil) (len blocks))))

; UNCHECKED is the table of the functions whose prologue need not check
; sp against x23 (EMIT-UNCHECKED, below).
(defun emit-function (mfn unchecked code)
  (let* ((name (cadr mfn))
         (homes (caddr mfn))
         (nslots (cadddr mfn))
         (blocks (emit-mfn-blocks mfn))
         (nspill (cadr (cddddr mfn))))
    (mv-let (calls most wrap frame)
      (emit-frame-of blocks nslots nspill)
      (let ((ctx (emit-ctx name nslots (len homes) frame calls wrap
                           (not (index-get name unchecked)))))
        (if (< 32768 frame)
            (compiler-error "A machine frame is too large: ~x0." name)
          (emit-prologue-stubs
           ctx most
           (emit-blocks-stubs
           blocks ctx
           (emit-blocks blocks ctx
                        (emit-params homes ctx
                                     (emit-prologue ctx most
                                                    (cons (list :label (list :fn name))
                                                          (if (rega-rt-qir-p name)
                                                              (cons (list :label name) code)
                                                            code))))))))))))

; The checks of the machine stack. A compiled function checks, in its
; prologue, that its frame leaves sp above x23; the runtime keeps 16 KiB
; below x23 for the routines' own use. Every function on a cycle of the
; call graph checks, so that a recursion cannot pass x23 unseen; one that
; is on no cycle need not check when the frames of every chain of calls
; of such functions from it come to at most *EMIT-UNCHECKED-BYTES*, half
; of that margin. A cycle is found as an edge, in a search of the call
; graph from every function, to a function on the search's path; the
; target of each such edge is marked to check, so that every cycle holds
; a function that checks.

(defconst *emit-unchecked-bytes* 8192)

(defun emit-callees-insts (insts acc)
  (cond ((atom insts) acc)
        ((eq (car (car insts)) :call) (emit-callees-insts (cdr insts) (cons (cadr (car insts)) acc)))
        (t (emit-callees-insts (cdr insts) acc))))

(defun emit-callees (blocks acc)
  (if (atom blocks)
      acc
    (emit-callees (cdr blocks)
                  (let ((term (caddr (car blocks))))
                    (emit-callees-insts (cadr (car blocks))
                                        (if (eq (car term) :tail) (cons (cadr term) acc) acc))))))

; GRAPH maps each name to (BYTES . CALLEES): the bytes the function takes
; on the machine stack, the link it keeps around a routine included.
(defun emit-edge-count (mfns n)
  (if (atom mfns)
      n
    (emit-edge-count (cdr mfns) (+ n (len (emit-callees (car (cddddr (car mfns))) nil))))))

(defun emit-graph (mfns graph)
  (if (atom mfns)
      graph
    (let* ((mfn (car mfns))
           (blocks (emit-mfn-blocks mfn)))
      (mv-let (calls most wrap frame)
        (emit-frame-of blocks (cadddr mfn) (cadr (cddddr mfn)))
        (declare (ignore calls most))
        (emit-graph (cdr mfns)
                    (index-set (cadr mfn) (cons (if wrap 16 frame) (emit-callees blocks nil))
                               graph))))))

; The search for cycles. SEEN maps a name to :OPEN while it is on the
; path and :DONE after; MARKS holds the names that must check.
(mutual-recursion
 (defun emit-cycles-node (name graph seen marks fuel)
   (declare (xargs :measure (nfix fuel)))
   (cond ((zp fuel) (mv seen (index-set name t marks)))
         ((eq (index-get name seen) :open) (mv seen (index-set name t marks)))
         ((index-get name seen) (mv seen marks))
         ((not (index-get name graph)) (mv seen marks))
         (t (mv-let (seen marks)
              (emit-cycles-list (cdr (index-get name graph)) graph
                                (index-set name :open seen) marks (- fuel 1))
              (mv (index-set name :done seen) marks)))))
 (defun emit-cycles-list (names graph seen marks fuel)
   (declare (xargs :measure (nfix fuel)))
   (if (or (atom names) (zp fuel))
       (mv seen marks)
     (mv-let (seen marks)
       (emit-cycles-node (car names) graph seen marks (- fuel 1))
       (emit-cycles-list (cdr names) graph seen marks (- fuel 1))))))

; The bytes of the longest chain of unchecked frames from each function,
; or NIL for one that checks. DEPTHS maps a name to (D) once known.
(mutual-recursion
 (defun emit-depth-node (name graph marks depths fuel)
   (declare (xargs :measure (nfix fuel)))
   (let ((known (index-get name depths)))
     (cond (known (mv (car known) depths))
           ((or (zp fuel) (index-get name marks) (not (index-get name graph))) (mv nil depths))
           (t (mv-let (deepest depths)
                (emit-depth-list (cdr (index-get name graph)) graph marks depths 0 (- fuel 1))
                (let* ((d (+ (car (index-get name graph)) deepest))
                       (d (if (< *emit-unchecked-bytes* d) nil d)))
                  (mv d (index-set name (list d) depths))))))))
 (defun emit-depth-list (names graph marks depths deepest fuel)
   (declare (xargs :measure (nfix fuel)))
   (if (or (atom names) (zp fuel))
       (mv deepest depths)
     (mv-let (d depths)
       (emit-depth-node (car names) graph marks depths (- fuel 1))
       (emit-depth-list (cdr names) graph marks depths
                        (if (and d (< deepest d)) d deepest) (- fuel 1))))))

(defun emit-unchecked-names (mfns graph marks depths fuel unchecked)
  (if (atom mfns)
      unchecked
    (mv-let (d depths)
      (emit-depth-node (cadr (car mfns)) graph marks depths fuel)
      (emit-unchecked-names (cdr mfns) graph marks depths fuel
                            (if d (index-set (cadr (car mfns)) t unchecked) unchecked)))))

(defun emit-cycles-all (mfns graph seen marks fuel)
  (if (atom mfns)
      marks
    (mv-let (seen marks)
      (emit-cycles-node (cadr (car mfns)) graph seen marks fuel)
      (emit-cycles-all (cdr mfns) graph seen marks fuel))))

(defun emit-unchecked (mfns)
  (let* ((graph (emit-graph mfns nil))
         (fuel (* 4 (+ 1 (len mfns) (emit-edge-count mfns 0))))
         (marks (emit-cycles-all mfns graph nil nil fuel)))
    (emit-unchecked-names mfns graph marks nil fuel nil)))

(defun emit-functions (mfns unchecked code)
  (if (atom mfns)
      code
    (emit-functions (cdr mfns) unchecked (emit-function (car mfns) unchecked code))))

(defun emit-program (mfns code)
  (emit-functions mfns (emit-unchecked mfns) code))

; The adapter by which rt:start calls the entry function, whose argument
; it pushed on the value stack.
(defun emit-entry-adapter (entry code)
  (emit-items (list '(:label "rt:entry") '(:sub 25 25 8) '(:ldr 0 25 0)
                    '(:stp-pre 29 30 31 -16) (list :bl (list :fn entry))
                    '(:ldp-post 29 30 31 16) '(:ret))
              code))
