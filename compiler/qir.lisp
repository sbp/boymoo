(in-package "BOYMOO-COMPILER")

(include-book "index")

(set-verify-guards-eagerness 0)

; QIR, the intermediate language of the passes P3 to P6
; (compiler/DESIGN.md, section 3), and what those passes share: the parts
; of functions, blocks and instructions; maps from labels and temporaries;
; the predecessors of each block; the blocks in reverse post-order;
; immediate dominators; recognisers of well-formed QIR-A, QIR-M and
; QIR-L; liveness; a printer; and the table of the runtime's routines.

; ------------------------------------------------------------------
; Operands

(defun qir-dtemp-p (x)
  (and (consp x) (equal (car x) :d) (natp (cdr x))))

(defun qir-wtemp-p (x)
  (and (consp x) (equal (car x) :w) (natp (cdr x))))

(defun qir-temp-p (x)
  (or (qir-dtemp-p x) (qir-wtemp-p x)))

(defun qir-const-p (x)
  (and (consp x) (equal (car x) :k) (integerp (cdr x))))

(defun qir-operand-p (x)
  (or (qir-temp-p x) (qir-const-p x)))

; An operand that may stand where a datum is required: a data temporary,
; or a constant, which the pass that writes it makes a datum word.
(defun qir-data-operand-p (x)
  (or (qir-dtemp-p x) (qir-const-p x)))

(defun qir-operands-p (xs)
  (if (atom xs)
      (null xs)
    (and (qir-operand-p (car xs)) (qir-operands-p (cdr xs)))))

(defun qir-data-operands-p (xs)
  (if (atom xs)
      (null xs)
    (and (qir-data-operand-p (car xs)) (qir-data-operands-p (cdr xs)))))

; ------------------------------------------------------------------
; Maps from labels and from the numbers of temporaries. A map is an AVL
; tree of a64.lisp; a value of NIL cannot be told from a missing key.

(defun qir-get (key map)
  (table-tree-get key map))

(defun qir-put (key value map)
  (table-tree-put key value map))

; ------------------------------------------------------------------
; The parts of functions, blocks, phis, instructions and jumps.

(defun qir-fn-name (fn) (cadr fn))
(defun qir-fn-params (fn) (caddr fn))
(defun qir-fn-blocks (fn) (cadddr fn))
(defun qir-fn-nslots (fn) (car (cddddr fn)))

(defun qir-block-label (block) (car block))
(defun qir-block-phis (block) (cadr block))
(defun qir-block-insts (block) (caddr block))
(defun qir-block-jump (block) (cadddr block))

(defun qir-phi-dest (phi) (car phi))
(defun qir-phi-args (phi) (cadr phi))

(defun qir-inst-dest (inst) (car inst))
(defun qir-inst-op (inst) (cadr inst))

; The operands that an instruction reads. Every field after the
; operation is an operand, except the name of :prim, :call and :rt and
; the slot of :spill and :reload.
(defun qir-inst-uses (inst)
  (let ((op (qir-inst-op inst)))
    (cond ((or (equal op :prim) (equal op :call) (equal op :rt)
               (equal op :spill))
           (cdddr inst))
          ((equal op :reload) nil)
          (t (cddr inst)))))

(defun qir-jump-uses (jump)
  (let ((op (car jump)))
    (cond ((or (equal op :if) (equal op :jnz) (equal op :ret))
           (list (cadr jump)))
          ((equal op :tail) (cddr jump))
          (t nil))))

(defun qir-jump-succs (jump)
  (let ((op (car jump)))
    (cond ((equal op :jmp) (list (cadr jump)))
          ((or (equal op :if) (equal op :jnz))
           (list (caddr jump) (cadddr jump)))
          (t nil))))

(defun qir-block-succs (block)
  (qir-jump-succs (qir-block-jump block)))

; The operand that a phi takes from the predecessor PRED.
(defun qir-phi-arg (phi pred)
  (cdr (assoc-equal pred (qir-phi-args phi))))

; ------------------------------------------------------------------
; The table of the runtime's routines that compiled code may call
; (compiler/README.md, "The runtime"; runtime.lisp gives each contract).
; An entry is (LABEL ARITY ALLOCATES CHANGES): the routine takes ARITY
; data in x0 onwards and gives its result in x0; ALLOCATES is T when it
; may allocate, and so collect; CHANGES lists the registers other than
; x0 and the flags that it may change, or is :VOLATILE for x0 to x17,
; x24, x26 and x27. Every routine that returns keeps x19 to x23, x25,
; x28, x29 and sp. The routines whose labels begin "rt-qir:" are
; functions of QIR-M (rt-qir.lisp), which the driver adds to the program
; and the back end compiles, with the registers of this contract.

(defconst *qir-routines*
  '(("prim:ACL2::ACL2-NUMBERP" 1 nil (1 2))
    ("prim:ACL2::BAD-ATOM<=" 2 nil nil)
    ("prim:ACL2::BINARY-*" 2 t :volatile)
    ("prim:ACL2::BINARY-+" 2 t :volatile)
    ("prim:ACL2::UNARY--" 1 t :volatile)
    ("prim:ACL2::UNARY-/" 1 t :volatile)
    ("prim:COMMON-LISP::<" 2 t :volatile)
    ("prim:COMMON-LISP::CAR" 1 nil nil)
    ("prim:COMMON-LISP::CDR" 1 nil nil)
    ("prim:COMMON-LISP::CHAR-CODE" 1 nil (1))
    ("prim:COMMON-LISP::CHARACTERP" 1 nil (1 2))
    ("prim:COMMON-LISP::CODE-CHAR" 1 nil nil)
    ("prim:COMMON-LISP::COMPLEX" 2 t :volatile)
    ("prim:ACL2::COMPLEX-RATIONALP" 1 nil (1 2))
    ("prim:COMMON-LISP::COERCE" 2 t :volatile)
    ("prim:COMMON-LISP::CONS" 2 t :volatile)
    ("prim:COMMON-LISP::CONSP" 1 nil (1 2))
    ("prim:COMMON-LISP::DENOMINATOR" 1 nil (3 4 5))
    ("prim:COMMON-LISP::EQUAL" 2 nil (1 2 3 4 5 6 7 8 9 10 11 12 24))
    ("prim:COMMON-LISP::IMAGPART" 1 nil (3 4 5))
    ("prim:COMMON-LISP::INTEGERP" 1 nil (1 2))
    ("prim:ACL2::INTERN-IN-PACKAGE-OF-SYMBOL" 2 t :volatile)
    ("prim:COMMON-LISP::NUMERATOR" 1 nil (3 4 5))
    ("prim:ACL2::PKG-IMPORTS" 1 nil (1 2 3 4 5 6 7 8 9))
    ("prim:ACL2::PKG-WITNESS" 1 nil (1 2 3 4 5 6 7 8 9))
    ("prim:COMMON-LISP::RATIONALP" 1 nil (1 2))
    ("prim:COMMON-LISP::REALPART" 1 nil (3 4 5))
    ("prim:COMMON-LISP::STRINGP" 1 nil (1 2))
    ("prim:COMMON-LISP::SYMBOL-NAME" 1 t :volatile)
    ("prim:ACL2::SYMBOL-PACKAGE-NAME" 1 t :volatile)
    ("prim:COMMON-LISP::SYMBOLP" 1 nil (1 2))
    ("jet:COMMON-LISP::ASH" 2 t :volatile)
    ("jet:ACL2::BINARY-LOGXOR" 2 t :volatile)
    ("jet:COMMON-LISP::LENGTH" 1 nil (1 2 3))
    ("jet:COMMON-LISP::CHAR" 2 nil (1 2 3 4 5))
    ("jet:COMMON-LISP::SUBSEQ" 3 t :volatile)
    ("rt-qir:LENGTH" 1 nil (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 24))
    ("rt-qir:CHAR" 2 nil (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 24))
    ("rt-qir:EQUAL" 2 nil (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 24))
    ("rt-qir:EQUAL-ATOM" 2 nil (1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 24))))

(defun qir-routine (label)
  (assoc-equal label *qir-routines*))

(defun qir-routine-arity (label)
  (cadr (qir-routine label)))

(defun qir-routine-allocates-p (label)
  (caddr (qir-routine label)))

(defun qir-routine-changes (label)
  (cadddr (qir-routine label)))

; The primitive or prelude function NAME (index.lisp): its arity, and
; the label of its routine.
(defun qir-prim-entry (name)
  (or (assoc-equal name *primitives*) (assoc-equal name *jets*)))

(defun qir-prim-arity (name)
  (cadr (qir-prim-entry name)))

(defun qir-prim-routine (name)
  (cddr (qir-prim-entry name)))

; An instruction that may collect: a call, a cons, or a routine that
; allocates. A :tail leaves the frame before the callee starts.
(defun qir-inst-may-collect-p (inst)
  (let ((op (qir-inst-op inst)))
    (or (equal op :call) (equal op :cons)
        (and (equal op :rt) (qir-routine-allocates-p (caddr inst)) t))))

; ------------------------------------------------------------------
; Labels, successors and predecessors

; The map from each label to its block.
(defun qir-block-map (blocks map)
  (if (atom blocks)
      map
    (qir-block-map (cdr blocks)
                   (qir-put (qir-block-label (car blocks)) (car blocks) map))))

(defun qir-add-preds (succs label preds)
  (if (atom succs)
      preds
    (qir-add-preds (cdr succs) label
                   (qir-put (car succs) (cons label (qir-get (car succs) preds))
                            preds))))

(defun qir-preds-of-blocks (blocks preds)
  (if (atom blocks)
      preds
    (qir-preds-of-blocks (cdr blocks)
                         (qir-add-preds (qir-block-succs (car blocks))
                                        (qir-block-label (car blocks)) preds))))

; The map from each label to the list of its predecessors' labels, each
; once when the two targets of every branch differ.
(defun qir-preds (blocks)
  (qir-preds-of-blocks blocks nil))

(defun qir-count-succs (blocks n)
  (if (atom blocks)
      n
    (qir-count-succs (cdr blocks) (+ n (len (qir-block-succs (car blocks)))))))

; ------------------------------------------------------------------
; Reverse post-order, by a depth-first search with an explicit stack.
; A frame is (LABEL . SUCCS), SUCCS the successors not yet visited. Each
; step drops one successor or one frame, so the number of blocks and
; edges bounds the steps. POST receives each label as its frame is
; finished, so it ends in reverse post-order. The successors are visited
; last first, so that the first target of a branch comes first.

(defun qir-dfs (stack seen post bmap fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((or (zp fuel) (atom stack)) post)
        ((atom (cdar stack))
         (qir-dfs (cdr stack) seen (cons (caar stack) post) bmap (- fuel 1)))
        (t (let* ((frame (car stack))
                  (s (cadr frame))
                  (stack (cons (cons (car frame) (cddr frame)) (cdr stack)))
                  (block (qir-get s bmap)))
             (if (or (qir-get s seen) (not block))
                 (qir-dfs stack seen post bmap (- fuel 1))
               (qir-dfs (cons (cons s (reverse (qir-block-succs block))) stack)
                        (qir-put s t seen) post bmap (- fuel 1)))))))

; The labels of the blocks reachable from the entry, in reverse
; post-order; the entry is first.
(defun qir-rpo (blocks)
  (if (atom blocks)
      nil
    (let ((entry (qir-block-label (car blocks))))
      (qir-dfs (list (cons entry (reverse (qir-block-succs (car blocks)))))
               (qir-put entry t nil) nil (qir-block-map blocks nil)
               (+ 1 (len blocks) (qir-count-succs blocks 0))))))

(defun qir-labels-blocks (labels bmap)
  (if (atom labels)
      nil
    (cons (qir-get (car labels) bmap) (qir-labels-blocks (cdr labels) bmap))))

; The reachable blocks in reverse post-order.
(defun qir-rpo-blocks (blocks)
  (qir-labels-blocks (qir-rpo blocks) (qir-block-map blocks nil)))

(defun qir-keep-blocks (blocks keep)
  (cond ((atom blocks) nil)
        ((qir-get (qir-block-label (car blocks)) keep)
         (cons (car blocks) (qir-keep-blocks (cdr blocks) keep)))
        (t (qir-keep-blocks (cdr blocks) keep))))

(defun qir-label-set (labels set)
  (if (atom labels)
      set
    (qir-label-set (cdr labels) (qir-put (car labels) t set))))

; The reachable blocks in their order. A pass that removes edges calls
; this, and then drops the phi arguments of the removed predecessors.
(defun qir-reachable-blocks (blocks)
  (qir-keep-blocks blocks (qir-label-set (qir-rpo blocks) nil)))

; A :jnz on a constant becomes a :jmp to the target it takes.
(defun qir-fold-jump (jump)
  (if (and (equal (car jump) :jnz) (qir-const-p (cadr jump)))
      (list :jmp (if (equal (low-bits (cdr (cadr jump)) 64) 0) (cadddr jump) (caddr jump)))
    jump))

(defun qir-fold-jumps (blocks)
  (if (atom blocks)
      nil
    (let ((block (car blocks)))
      (cons (list (qir-block-label block) (qir-block-phis block)
                  (qir-block-insts block) (qir-fold-jump (qir-block-jump block)))
            (qir-fold-jumps (cdr blocks))))))

(defun qir-keep-phi-args (args preds)
  (cond ((atom args) nil)
        ((member-equal (caar args) preds)
         (cons (car args) (qir-keep-phi-args (cdr args) preds)))
        (t (qir-keep-phi-args (cdr args) preds))))

(defun qir-prune-phis (phis preds)
  (if (atom phis)
      nil
    (cons (list (qir-phi-dest (car phis)) (qir-keep-phi-args (qir-phi-args (car phis)) preds))
          (qir-prune-phis (cdr phis) preds))))

(defun qir-prune-blocks (blocks preds)
  (if (atom blocks)
      nil
    (let ((block (car blocks)))
      (cons (list (qir-block-label block)
                  (qir-prune-phis (qir-block-phis block)
                                  (qir-get (qir-block-label block) preds))
                  (qir-block-insts block) (qir-block-jump block))
            (qir-prune-blocks (cdr blocks) preds)))))

; Each :jnz on a constant of BLOCKS becomes a :jmp; then the blocks that
; are no longer reachable are dropped, and the phi arguments of the
; predecessors that are gone.
(defun qir-fold-branches (blocks)
  (let ((blocks (qir-reachable-blocks (qir-fold-jumps blocks))))
    (qir-prune-blocks blocks (qir-preds blocks))))

; Splitting the critical edges: an edge from a block with two successors
; to a block with two or more predecessors gets a block of its own, which
; only jumps to the target. NEXT is the first label not yet used.

(defun qir-retarget (jump old new)
  (if (or (equal (car jump) :jnz) (equal (car jump) :if))
      (list (car jump) (cadr jump)
            (if (equal (caddr jump) old) new (caddr jump))
            (if (equal (cadddr jump) old) new (cadddr jump)))
    jump))

(defun qir-rename-args (args old new)
  (if (atom args)
      nil
    (cons (if (equal (caar args) old) (cons new (cdar args)) (car args))
          (qir-rename-args (cdr args) old new))))

(defun qir-rename-phi-pred (phis old new)
  (if (atom phis)
      nil
    (cons (list (qir-phi-dest (car phis))
                (qir-rename-args (qir-phi-args (car phis)) old new))
          (qir-rename-phi-pred (cdr phis) old new))))

; The edges to split: (FROM TO NEW) for each critical edge, NEW its block.
(defun qir-critical-of (label succs preds next acc)
  (cond ((atom succs) (mv next acc))
        ((consp (cdr (qir-get (car succs) preds)))
         (qir-critical-of label (cdr succs) preds (+ next 1)
                          (cons (list label (car succs) next) acc)))
        (t (qir-critical-of label (cdr succs) preds next acc))))

(defun qir-criticals (blocks preds next acc)
  (if (atom blocks)
      acc
    (let ((succs (qir-block-succs (car blocks))))
      (if (consp (cdr succs))
          (mv-let (next acc)
            (qir-critical-of (qir-block-label (car blocks)) succs preds next acc)
            (qir-criticals (cdr blocks) preds next acc))
        (qir-criticals (cdr blocks) preds next acc)))))

; Applies the splits EDGES to BLOCK: its jump goes to the new blocks of
; the edges from it, and its phis take from the new blocks of the edges
; to it.
(defun qir-apply-splits (block edges)
  (if (atom edges)
      block
    (let* ((e (car edges))
           (label (qir-block-label block))
           (block (if (equal (car e) label)
                      (list label (qir-block-phis block) (qir-block-insts block)
                            (qir-retarget (qir-block-jump block) (cadr e) (caddr e)))
                    block))
           (block (if (equal (cadr e) label)
                      (list label (qir-rename-phi-pred (qir-block-phis block) (car e) (caddr e))
                            (qir-block-insts block) (qir-block-jump block))
                    block)))
      (qir-apply-splits block (cdr edges)))))

(defun qir-split-blocks (blocks edges)
  (if (atom blocks)
      nil
    (cons (qir-apply-splits (car blocks) edges)
          (qir-split-blocks (cdr blocks) edges))))

(defun qir-edge-blocks (edges)
  (if (atom edges)
      nil
    (cons (list (caddr (car edges)) nil nil (list :jmp (cadr (car edges))))
          (qir-edge-blocks (cdr edges)))))

(defun qir-split-critical-edges (blocks next)
  (let ((edges (qir-criticals blocks (qir-preds blocks) next nil)))
    (append (qir-split-blocks blocks edges) (qir-edge-blocks (reverse edges)))))

; The map from each label to its position in LABELS.
(defun qir-number (labels i map)
  (if (atom labels)
      map
    (qir-number (cdr labels) (+ i 1) (qir-put (car labels) i map))))

; ------------------------------------------------------------------
; Immediate dominators, by the iterative algorithm of Cooper, Harvey and
; Kennedy, "A Simple, Fast Dominance Algorithm" (2001). NUM gives the
; position of each label in reverse post-order; IDOM maps each block
; processed so far to its immediate dominator, and the entry to itself.

(defun qir-intersect (a b idom num fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (equal a b))
      a
    (if (< (nfix (qir-get b num)) (nfix (qir-get a num)))
        (qir-intersect (qir-get a idom) b idom num (- fuel 1))
      (qir-intersect a (qir-get b idom) idom num (- fuel 1)))))

(defun qir-new-idom (preds current idom num fuel)
  (if (atom preds)
      current
    (let ((p (car preds)))
      (qir-new-idom (cdr preds)
                    (cond ((not (qir-get p idom)) current)
                          ((not current) p)
                          (t (qir-intersect p current idom num fuel)))
                    idom num fuel))))

(defun qir-idom-pass (labels preds idom num changed fuel)
  (if (atom labels)
      (mv idom changed)
    (let* ((b (car labels))
           (new (qir-new-idom (qir-get b preds) nil idom num fuel)))
      (if (or (not new) (equal new (qir-get b idom)))
          (qir-idom-pass (cdr labels) preds idom num changed fuel)
        (qir-idom-pass (cdr labels) preds (qir-put b new idom) num t fuel)))))

(defun qir-idom-loop (labels preds idom num rounds fuel)
  (declare (xargs :measure (nfix rounds)))
  (if (zp rounds)
      idom
    (mv-let (idom changed)
      (qir-idom-pass labels preds idom num nil fuel)
      (if changed
          (qir-idom-loop labels preds idom num (- rounds 1) fuel)
        idom))))

; The map from the label of each reachable block to that of its
; immediate dominator; the entry maps to itself.
(defun qir-idoms-of (rpo preds)
  (let ((n (len rpo)))
    (qir-idom-loop (cdr rpo) preds (qir-put (car rpo) (car rpo) nil)
                   (qir-number rpo 0 nil) (+ n 2) (+ 2 (* 2 n)))))

(defun qir-idoms (blocks)
  (qir-idoms-of (qir-rpo blocks) (qir-preds blocks)))

(defun qir-add-children (labels idom children)
  (if (atom labels)
      children
    (let ((parent (qir-get (car labels) idom)))
      (qir-add-children (cdr labels) idom
                        (qir-put parent (cons (car labels) (qir-get parent children))
                                 children)))))

; The map from each label to its children in the dominator tree, in
; reverse post-order. RPO is the reverse post-order, entry first.
(defun qir-dom-children (rpo idom)
  (qir-add-children (reverse (cdr rpo)) idom nil))

; Whether block A dominates block B: whether A is on the path from B to
; the entry in the dominator tree.
(defun qir-dominates-p (a b idom fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((equal a b) t)
        ((zp fuel) nil)
        (t (let ((up (qir-get b idom)))
             (and up (not (equal up b))
                  (qir-dominates-p a up idom (- fuel 1)))))))

; ------------------------------------------------------------------
; Well-formed instructions, jumps and blocks. LEVEL is :A for QIR-A, :M
; for QIR-M and :L for QIR-L. CLASS is :D, :W or :ANY; in QIR-A every
; temporary is a data temporary.

(defun qir-dest-ok (dest class level)
  (or (null dest)
      (if (or (equal class :d) (equal level :a))
          (qir-dtemp-p dest)
        (if (equal class :w)
            (qir-wtemp-p dest)
          (qir-temp-p dest)))))

(defun qir-level-operand-p (x level)
  (if (equal level :a) (qir-data-operand-p x) (qir-operand-p x)))

(defconst *qir-word-ops*
  '(:add :sub :mul :and :or :xor :shl :shr :sar
    :ceq :cne :cslt :csle :csgt :csge :cult :cule :cugt :cuge
    :ovadd :ovsub))

(defun qir-word-op-p (op)
  (and (member-equal op *qir-word-ops*) t))

(defun qir-inst-ok (inst level)
  (and (true-listp inst)
       (consp (cdr inst))
       (let ((dest (car inst))
             (op (cadr inst))
             (args (cddr inst)))
         (cond
          ((equal op :copy)
           (and (equal (len args) 1)
                (qir-dest-ok dest :any level)
                (qir-level-operand-p (car args) level)))
          ((equal op :call)
           (and (consp args) (stringp (car args))
                (qir-dest-ok dest :d level)
                (qir-data-operands-p (cdr args))))
          ((equal level :a)
           (and (equal op :prim) (consp args)
                (equal (qir-prim-arity (car args)) (len (cdr args)))
                (qir-dest-ok dest :d level)
                (qir-data-operands-p (cdr args))))
          ((qir-word-op-p op)
           (and (equal (len args) 2)
                (qir-dest-ok dest :w level)
                (qir-operands-p args)))
          ((equal op :sel)
           (and (equal (len args) 3)
                (qir-dest-ok dest :any level)
                (qir-operands-p args)))
          ((or (equal op :ld) (equal op :ldb))
           (and (equal (len args) 2)
                (qir-dest-ok dest (if (equal op :ld) :any :w) level)
                (qir-data-operand-p (car args))
                (qir-operand-p (cadr args))))
          ((equal op :cons)
           (and (equal (len args) 2)
                (qir-dest-ok dest :d level)
                (qir-data-operands-p args)))
          ((equal op :rt)
           (and (consp args)
                (equal (qir-routine-arity (car args)) (len (cdr args)))
                (qir-dest-ok dest :d level)
                (qir-data-operands-p (cdr args))))
          ((equal level :l)
           (cond ((equal op :spill)
                  (and (null dest) (equal (len args) 2)
                       (natp (car args)) (qir-dtemp-p (cadr args))))
                 ((equal op :reload)
                  (and (qir-dtemp-p dest) (equal (len args) 1) (natp (car args))))
                 (t nil)))
          (t nil)))))

(defun qir-insts-ok (insts level)
  (if (atom insts)
      (null insts)
    (and (qir-inst-ok (car insts) level)
         (qir-insts-ok (cdr insts) level))))

(defun qir-jump-ok (jump level)
  (and (consp jump)
       (true-listp jump)
       (let ((op (car jump)))
         (cond ((equal op :jmp)
                (and (equal (len jump) 2) (natp (cadr jump))))
               ((equal op (if (equal level :a) :if :jnz))
                (and (equal (len jump) 4)
                     (qir-level-operand-p (cadr jump) level)
                     (natp (caddr jump)) (natp (cadddr jump))
                     (not (equal (caddr jump) (cadddr jump)))))
               ((equal op :ret)
                (and (equal (len jump) 2) (qir-data-operand-p (cadr jump))))
               ((equal op :tail)
                (and (consp (cdr jump)) (stringp (cadr jump))
                     (qir-data-operands-p (cddr jump))))
               ((equal op :undef)
                (and (equal (len jump) 2) (integerp (cadr jump))))
               (t nil)))))

(defun qir-phi-args-ok (args data)
  (if (atom args)
      (null args)
    (and (consp (car args))
         (natp (caar args))
         (if data
             (qir-data-operand-p (cdar args))
           (qir-operand-p (cdar args)))
         (qir-phi-args-ok (cdr args) data))))

(defun qir-phi-ok (phi level)
  (and (true-listp phi)
       (equal (len phi) 2)
       (qir-dest-ok (car phi) :any level)
       (car phi)
       (qir-phi-args-ok (cadr phi) (qir-dtemp-p (car phi)))))

(defun qir-phis-ok (phis level)
  (if (atom phis)
      (null phis)
    (and (qir-phi-ok (car phis) level)
         (qir-phis-ok (cdr phis) level))))

(defun qir-block-ok (block level)
  (and (true-listp block)
       (equal (len block) 4)
       (natp (qir-block-label block))
       (if (equal level :l)
           (null (qir-block-phis block))
         (qir-phis-ok (qir-block-phis block) level))
       (qir-insts-ok (qir-block-insts block) level)
       (qir-jump-ok (qir-block-jump block) level)))

(defun qir-blocks-ok (blocks level)
  (if (atom blocks)
      (null blocks)
    (and (qir-block-ok (car blocks) level)
         (qir-blocks-ok (cdr blocks) level))))

(defun qir-dtemps-p (xs)
  (if (atom xs)
      (null xs)
    (and (qir-dtemp-p (car xs)) (qir-dtemps-p (cdr xs)))))

; ------------------------------------------------------------------
; The graph: labels distinct, every target defined, every block
; reachable, the entry without predecessors or phis, and in each phi
; one argument for each predecessor.

(defun qir-labels-distinct-p (blocks seen)
  (cond ((atom blocks) t)
        ((qir-get (qir-block-label (car blocks)) seen) nil)
        (t (qir-labels-distinct-p (cdr blocks)
                                  (qir-put (qir-block-label (car blocks)) t seen)))))

(defun qir-labels-defined-p (labels bmap)
  (if (atom labels)
      t
    (and (qir-get (car labels) bmap) t
         (qir-labels-defined-p (cdr labels) bmap))))

(defun qir-targets-defined-p (blocks bmap)
  (if (atom blocks)
      t
    (and (qir-labels-defined-p (qir-block-succs (car blocks)) bmap)
         (qir-targets-defined-p (cdr blocks) bmap))))

(defun qir-phi-covers-p (preds args)
  (if (atom preds)
      t
    (and (assoc-equal (car preds) args)
         (qir-phi-covers-p (cdr preds) args))))

(defun qir-phis-match-p (phis preds)
  (if (atom phis)
      t
    (and (equal (len (qir-phi-args (car phis))) (len preds))
         (qir-phi-covers-p preds (qir-phi-args (car phis)))
         (qir-phis-match-p (cdr phis) preds))))

(defun qir-blocks-phis-match-p (blocks preds)
  (if (atom blocks)
      t
    (and (qir-phis-match-p (qir-block-phis (car blocks))
                           (qir-get (qir-block-label (car blocks)) preds))
         (qir-blocks-phis-match-p (cdr blocks) preds))))

(defun qir-graph-ok (blocks)
  (let ((bmap (qir-block-map blocks nil))
        (preds (qir-preds blocks)))
    (and (consp blocks)
         (qir-labels-distinct-p blocks nil)
         (qir-targets-defined-p blocks bmap)
         (equal (len (qir-rpo blocks)) (len blocks))
         (null (qir-get (qir-block-label (car blocks)) preds))
         (null (qir-block-phis (car blocks)))
         (qir-blocks-phis-match-p blocks preds))))

; ------------------------------------------------------------------
; Temporaries: every temporary of the function, the uses and
; definitions of each block, classes, and single assignment.

(defun qir-temps-of (xs acc)
  (cond ((atom xs) acc)
        ((qir-temp-p (car xs)) (qir-temps-of (cdr xs) (cons (car xs) acc)))
        (t (qir-temps-of (cdr xs) acc))))

(defun qir-phi-arg-operands (args)
  (if (atom args)
      nil
    (cons (cdar args) (qir-phi-arg-operands (cdr args)))))

(defun qir-phis-temps (phis acc)
  (if (atom phis)
      acc
    (qir-phis-temps (cdr phis)
                    (qir-temps-of (cons (qir-phi-dest (car phis))
                                        (qir-phi-arg-operands (qir-phi-args (car phis))))
                                  acc))))

(defun qir-insts-temps (insts acc)
  (if (atom insts)
      acc
    (qir-insts-temps (cdr insts)
                     (qir-temps-of (cons (qir-inst-dest (car insts))
                                         (qir-inst-uses (car insts)))
                                   acc))))

(defun qir-blocks-temps (blocks acc)
  (if (atom blocks)
      acc
    (qir-blocks-temps (cdr blocks)
                      (qir-temps-of (qir-jump-uses (qir-block-jump (car blocks)))
                                    (qir-insts-temps (qir-block-insts (car blocks))
                                                     (qir-phis-temps (qir-block-phis (car blocks))
                                                                     acc))))))

; Every temporary that occurs in FN, with repetitions.
(defun qir-fn-temps (fn)
  (qir-blocks-temps (qir-fn-blocks fn) (qir-temps-of (qir-fn-params fn) nil)))

; Whether no number is both a data and a word temporary.
(defun qir-classes-consistent-p (temps classes)
  (if (atom temps)
      t
    (let* ((x (car temps))
           (seen (qir-get (cdr x) classes)))
      (if seen
          (and (equal seen (car x))
               (qir-classes-consistent-p (cdr temps) classes))
        (qir-classes-consistent-p (cdr temps) (qir-put (cdr x) (car x) classes))))))

(defun qir-max-temp-of (temps n)
  (if (atom temps)
      n
    (qir-max-temp-of (cdr temps) (if (< n (cdar temps)) (cdar temps) n))))

; One more than the largest number of a temporary in FN: the first
; number that a pass may take for a new temporary.
(defun qir-next-temp (fn)
  (+ 1 (qir-max-temp-of (qir-fn-temps fn) -1)))

(defun qir-max-label-of (blocks n)
  (if (atom blocks)
      n
    (qir-max-label-of (cdr blocks)
                      (if (< n (qir-block-label (car blocks)))
                          (qir-block-label (car blocks))
                        n))))

; The first label that a pass may take for a new block.
(defun qir-next-label (fn)
  (+ 1 (qir-max-label-of (qir-fn-blocks fn) -1)))

(defun qir-phi-dests (phis)
  (if (atom phis)
      nil
    (cons (qir-phi-dest (car phis)) (qir-phi-dests (cdr phis)))))

(defun qir-inst-dests (insts)
  (cond ((atom insts) nil)
        ((qir-inst-dest (car insts))
         (cons (qir-inst-dest (car insts)) (qir-inst-dests (cdr insts))))
        (t (qir-inst-dests (cdr insts)))))

(defun qir-blocks-defs (blocks acc)
  (if (atom blocks)
      acc
    (qir-blocks-defs (cdr blocks)
                     (append (qir-phi-dests (qir-block-phis (car blocks)))
                             (qir-inst-dests (qir-block-insts (car blocks)))
                             acc))))

; Every definition of a temporary in FN: parameters, phis and
; instructions.
(defun qir-fn-defs (fn)
  (qir-blocks-defs (qir-fn-blocks fn) (qir-fn-params fn)))

(defun qir-distinct-temps-p (temps seen)
  (cond ((atom temps) t)
        ((qir-get (cdar temps) seen) nil)
        (t (qir-distinct-temps-p (cdr temps) (qir-put (cdar temps) t seen)))))

; ------------------------------------------------------------------
; Dominance of uses by definitions, checked by a walk of the dominator
; tree. DEFINED holds the temporaries defined on the path from the entry
; to the block, as a map from their numbers. A use in a phi is checked
; at the end of the predecessor. WORK holds pairs (LABEL . DEFINED).

(defun qir-defined-p (x defined)
  (or (qir-const-p x)
      (and (qir-temp-p x) (qir-get (cdr x) defined) t)))

(defun qir-all-defined-p (xs defined)
  (if (atom xs)
      t
    (and (qir-defined-p (car xs) defined)
         (qir-all-defined-p (cdr xs) defined))))

(defun qir-define (x defined)
  (if (qir-temp-p x) (qir-put (cdr x) t defined) defined))

(defun qir-define-all (xs defined)
  (if (atom xs)
      defined
    (qir-define-all (cdr xs) (qir-define (car xs) defined))))

(defun qir-insts-defined (insts defined)
  (cond ((atom insts) (mv t defined))
        ((qir-all-defined-p (qir-inst-uses (car insts)) defined)
         (qir-insts-defined (cdr insts)
                            (qir-define (qir-inst-dest (car insts)) defined)))
        (t (mv nil defined))))

(defun qir-phi-args-defined-p (phis pred defined)
  (if (atom phis)
      t
    (and (qir-defined-p (qir-phi-arg (car phis) pred) defined)
         (qir-phi-args-defined-p (cdr phis) pred defined))))

(defun qir-succ-phis-defined-p (succs pred bmap defined)
  (if (atom succs)
      t
    (and (qir-phi-args-defined-p (qir-block-phis (qir-get (car succs) bmap))
                                 pred defined)
         (qir-succ-phis-defined-p (cdr succs) pred bmap defined))))

(defun qir-push-work (labels defined work)
  (if (atom labels)
      work
    (cons (cons (car labels) defined)
          (qir-push-work (cdr labels) defined work))))

(defun qir-ssa-walk (work bmap children fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((atom work) t)
        ((zp fuel) nil)
        (t (let* ((label (caar work))
                  (block (qir-get label bmap))
                  (jump (qir-block-jump block))
                  (defined (qir-define-all (qir-phi-dests (qir-block-phis block))
                                           (cdar work))))
             (mv-let (ok defined)
               (qir-insts-defined (qir-block-insts block) defined)
               (and ok
                    (qir-all-defined-p (qir-jump-uses jump) defined)
                    (qir-succ-phis-defined-p (qir-jump-succs jump) label bmap defined)
                    (qir-ssa-walk (qir-push-work (qir-get label children) defined
                                                 (cdr work))
                                  bmap children (- fuel 1))))))))

; Whether every temporary of FN is assigned once and its definition
; dominates each of its uses. FN must satisfy QIR-GRAPH-OK.
(defun qir-ssa-ok (fn)
  (let* ((blocks (qir-fn-blocks fn))
         (rpo (qir-rpo blocks))
         (children (qir-dom-children rpo (qir-idoms-of rpo (qir-preds blocks)))))
    (and (qir-distinct-temps-p (qir-fn-defs fn) nil)
         (qir-ssa-walk (list (cons (car rpo) (qir-define-all (qir-fn-params fn) nil)))
                       (qir-block-map blocks nil) children (+ 1 (len blocks))))))

; ------------------------------------------------------------------
; Liveness, for any of the three languages. A set of temporaries is a
; list of operands in increasing order of their numbers, without
; repetitions. A phi's argument is live at the end of its predecessor,
; and a phi's temporary is defined at the start of its block.

(defun qir-set-insert (x set)
  (cond ((atom set) (list x))
        ((equal (cdr x) (cdar set)) set)
        ((< (cdr x) (cdar set)) (cons x set))
        (t (cons (car set) (qir-set-insert x (cdr set))))))

(defun qir-set-union (a b)
  (declare (xargs :measure (+ (len a) (len b))))
  (cond ((atom a) b)
        ((atom b) a)
        ((equal (cdar a) (cdar b)) (cons (car a) (qir-set-union (cdr a) (cdr b))))
        ((< (cdar a) (cdar b)) (cons (car a) (qir-set-union (cdr a) b)))
        (t (cons (car b) (qir-set-union a (cdr b))))))

(defun qir-set-remove (x set)
  (cond ((atom set) nil)
        ((equal (cdr x) (cdar set)) (cdr set))
        (t (cons (car set) (qir-set-remove x (cdr set))))))

(defun qir-set-member-p (x set)
  (cond ((atom set) nil)
        ((equal (cdr x) (cdar set)) t)
        ((< (cdr x) (cdar set)) nil)
        (t (qir-set-member-p x (cdr set)))))

; The set of the temporaries among XS.
(defun qir-set-of (xs set)
  (cond ((atom xs) set)
        ((qir-temp-p (car xs)) (qir-set-of (cdr xs) (qir-set-insert (car xs) set)))
        (t (qir-set-of (cdr xs) set))))

; The live set before an instruction, from the live set after it.
(defun qir-inst-live-before (inst live)
  (qir-set-of (qir-inst-uses inst)
              (if (qir-inst-dest inst)
                  (qir-set-remove (qir-inst-dest inst) live)
                live)))

; The live set at the start of INSTS, from that at their end.
(defun qir-insts-live-before (insts live)
  (if (atom insts)
      live
    (qir-inst-live-before (car insts) (qir-insts-live-before (cdr insts) live))))

(defun qir-remove-all (xs set)
  (if (atom xs)
      set
    (qir-remove-all (cdr xs) (qir-set-remove (car xs) set))))

(defun qir-phi-uses (phis pred)
  (if (atom phis)
      nil
    (cons (qir-phi-arg (car phis) pred) (qir-phi-uses (cdr phis) pred))))

; LIVE-IN maps each label to its set, or to :NONE while it is empty, as
; a map cannot hold NIL.
(defun qir-live-get (label live-in)
  (let ((set (qir-get label live-in)))
    (if (equal set :none) nil set)))

; The live set at the end of the block LABEL with successors SUCCS:
; what is live into each successor, with the arguments of its phis for
; this predecessor. LIVE-IN maps labels to the sets live into them:
; what is live after their phis, less what the phis define.
(defun qir-live-out (succs label bmap live-in)
  (if (atom succs)
      nil
    (qir-set-union (qir-set-of (qir-phi-uses (qir-block-phis (qir-get (car succs) bmap))
                                             label)
                               (qir-live-get (car succs) live-in))
                   (qir-live-out (cdr succs) label bmap live-in))))

; The live set on entry to BLOCK, from LIVE-IN: what is live after its
; phis, less what they define.
(defun qir-block-live-in (block bmap live-in)
  (let ((label (qir-block-label block)))
    (qir-remove-all (qir-phi-dests (qir-block-phis block))
                    (qir-insts-live-before
                     (qir-block-insts block)
                     (qir-set-of (qir-jump-uses (qir-block-jump block))
                                 (qir-live-out (qir-block-succs block) label bmap
                                               live-in))))))

(defun qir-live-pass (blocks bmap live-in changed)
  (if (atom blocks)
      (mv live-in changed)
    (let* ((label (qir-block-label (car blocks)))
           (old (qir-get label live-in))
           (new (qir-block-live-in (car blocks) bmap live-in))
           (new (or new :none)))
      (if (equal new old)
          (qir-live-pass (cdr blocks) bmap live-in changed)
        (qir-live-pass (cdr blocks) bmap (qir-put label new live-in) t)))))

(defun qir-live-loop (blocks bmap live-in rounds)
  (declare (xargs :measure (nfix rounds)))
  (if (zp rounds)
      live-in
    (mv-let (live-in changed)
      (qir-live-pass blocks bmap live-in nil)
      (if changed
          (qir-live-loop blocks bmap live-in (- rounds 1))
        live-in))))

; The map from each label of FN to the set live on entry to its block,
; less what its phis define, or :NONE for the empty set (QIR-LIVE-GET
; reads it). Blocks are
; visited in post-order; the number of rounds is bounded by the number
; of temporaries times the number of blocks, as each round that changes
; something adds a temporary to a set.
(defun qir-live-in-map (fn)
  (let* ((blocks (qir-fn-blocks fn))
         (post (reverse (qir-rpo-blocks blocks))))
    (qir-live-loop post (qir-block-map blocks nil) nil
                   (+ 2 (* (len blocks) (+ 1 (qir-next-temp fn)))))))

; The set live at the end of the block BLOCK of FN, given LIVE-IN from
; QIR-LIVE-IN-MAP.
(defun qir-block-live-out (block bmap live-in)
  (qir-live-out (qir-block-succs block) (qir-block-label block) bmap live-in))

; ------------------------------------------------------------------
; QIR-L: no data temporary is live across an instruction that may
; collect, other than the one it defines; every use of a temporary has a
; definition somewhere; every slot is below NSLOTS.

(defun qir-data-temps-p (set)
  (cond ((atom set) nil)
        ((qir-dtemp-p (car set)) t)
        (t (qir-data-temps-p (cdr set)))))

; Walks INSTS backwards from LIVE, the set live after them; gives
; whether each instruction that may collect has no data temporary live
; after it other than its own.
(defun qir-insts-collect-ok (insts live)
  (if (atom insts)
      (mv t live)
    (mv-let (ok after)
      (qir-insts-collect-ok (cdr insts) live)
      (let ((inst (car insts)))
        (mv (and ok
                 (or (not (qir-inst-may-collect-p inst))
                     (not (qir-data-temps-p
                           (if (qir-inst-dest inst)
                               (qir-set-remove (qir-inst-dest inst) after)
                             after)))))
            (qir-inst-live-before inst after))))))

(defun qir-blocks-collect-ok (blocks bmap live-in)
  (if (atom blocks)
      t
    (let ((block (car blocks)))
      (mv-let (ok live)
        (qir-insts-collect-ok
         (qir-block-insts block)
         (qir-set-of (qir-jump-uses (qir-block-jump block))
                     (qir-block-live-out block bmap live-in)))
        (declare (ignore live))
        (and ok (qir-blocks-collect-ok (cdr blocks) bmap live-in))))))

(defun qir-slots-ok (insts nslots)
  (if (atom insts)
      t
    (let ((op (qir-inst-op (car insts))))
      (and (or (not (or (equal op :spill) (equal op :reload)))
               (< (caddr (car insts)) nslots))
           (qir-slots-ok (cdr insts) nslots)))))

(defun qir-blocks-slots-ok (blocks nslots)
  (if (atom blocks)
      t
    (and (qir-slots-ok (qir-block-insts (car blocks)) nslots)
         (qir-blocks-slots-ok (cdr blocks) nslots))))

(defun qir-uses-defined-p (temps defined)
  (if (atom temps)
      t
    (and (qir-get (cdar temps) defined) t
         (qir-uses-defined-p (cdr temps) defined))))

; Whether nothing is live into the entry but the parameters.
(defun qir-entry-live-ok (fn live-in)
  (let ((live (qir-live-get (qir-block-label (car (qir-fn-blocks fn))) live-in)))
    (equal (qir-remove-all (qir-fn-params fn) live) nil)))

; ------------------------------------------------------------------
; Well-formed functions and programs

(defun qir-fn-shape-ok (fn level)
  (and (true-listp fn)
       (equal (car fn) :fn)
       (equal (len fn) (if (equal level :l) 5 4))
       (stringp (qir-fn-name fn))
       (qir-dtemps-p (qir-fn-params fn))
       (or (not (equal level :l)) (natp (qir-fn-nslots fn)))
       (true-listp (qir-fn-blocks fn))
       (qir-blocks-ok (qir-fn-blocks fn) level)))

(defun qir-fn-ok (fn level)
  (and (qir-fn-shape-ok fn level)
       (qir-graph-ok (qir-fn-blocks fn))
       (qir-classes-consistent-p (qir-fn-temps fn) nil)
       (if (equal level :l)
           (let ((live-in (qir-live-in-map fn))
                 (blocks (qir-fn-blocks fn)))
             (and (qir-distinct-temps-p (qir-fn-params fn) nil)
                  (qir-blocks-slots-ok blocks (qir-fn-nslots fn))
                  (qir-uses-defined-p (qir-fn-temps fn)
                                      (qir-define-all (qir-fn-defs fn) nil))
                  (qir-entry-live-ok fn live-in)
                  (qir-blocks-collect-ok blocks (qir-block-map blocks nil) live-in)))
         (qir-ssa-ok fn))))

; The map from the name of each function of a program to its number of
; parameters, and whether the names are distinct.
(defun qir-arities (fns map)
  (if (atom fns)
      (mv t map)
    (if (index-get (qir-fn-name (car fns)) map)
        (mv nil map)
      (qir-arities (cdr fns)
                   (index-set (qir-fn-name (car fns)) (len (qir-fn-params (car fns))) map)))))

(defun qir-insts-calls-ok (insts arities)
  (if (atom insts)
      t
    (and (or (not (equal (qir-inst-op (car insts)) :call))
             (equal (index-get (caddr (car insts)) arities)
                    (len (cdddr (car insts)))))
         (qir-insts-calls-ok (cdr insts) arities))))

(defun qir-blocks-calls-ok (blocks arities)
  (if (atom blocks)
      t
    (let ((jump (qir-block-jump (car blocks))))
      (and (qir-insts-calls-ok (qir-block-insts (car blocks)) arities)
           (or (not (equal (car jump) :tail))
               (equal (index-get (cadr jump) arities) (len (cddr jump))))
           (qir-blocks-calls-ok (cdr blocks) arities)))))

(defun qir-fns-ok (fns level arities)
  (if (atom fns)
      (null fns)
    (and (qir-fn-ok (car fns) level)
         (qir-blocks-calls-ok (qir-fn-blocks (car fns)) arities)
         (qir-fns-ok (cdr fns) level arities))))

; Whether FNS is a well-formed program of QIR at LEVEL: :A for QIR-A, :M
; for QIR-M, :L for QIR-L. Every function called is in the program with
; as many parameters as the call has arguments.
(defun qir-program-ok (fns level)
  (mv-let (distinct arities)
    (qir-arities fns nil)
    (and distinct
         (qir-fns-ok fns level arities))))

(defun qir-a-p (fns) (qir-program-ok fns :a))
(defun qir-m-p (fns) (qir-program-ok fns :m))
(defun qir-l-p (fns) (qir-program-ok fns :l))

; The first function of FNS that is not well formed at LEVEL, or NIL.
(defun qir-first-bad-fn (fns level)
  (cond ((atom fns) nil)
        ((qir-fn-ok (car fns) level) (qir-first-bad-fn (cdr fns) level))
        (t (car fns))))

; ------------------------------------------------------------------
; The printer: QIR as text, in the manner of QBE's. A temporary is
; written %dN or %wN, a constant as its integer, a label @N; each
; function begins with a line "function NAME (PARAMS)".

(defun qir-out-chars (s i left acc)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      acc
    (qir-out-chars s (+ i 1) (- left 1) (cons (char s i) acc))))

(defun qir-out-string (s acc)
  (qir-out-chars s 0 (length s) acc))

(defun qir-digits (n acc fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (not (natp n)) (< n 10))
      (cons (code-char (+ 48 (nfix n))) acc)
    (qir-digits (floor n 10) (cons (code-char (+ 48 (mod n 10))) acc)
                (- fuel 1))))

(defun qir-out-int (n acc)
  (let ((n (ifix n)))
    (if (< n 0)
        (reverse-onto (qir-digits (- n) nil 400) (cons #\- acc))
      (reverse-onto (qir-digits n nil 400) acc))))

; Writes the letters of S in lower case.
(defun qir-out-lower (s i left acc)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      acc
    (let* ((c (char s i))
           (n (char-code c)))
      (qir-out-lower s (+ i 1) (- left 1)
                     (cons (if (and (<= 65 n) (<= n 90)) (code-char (+ n 32)) c) acc)))))

(defun qir-out-operand (x acc)
  (cond ((qir-dtemp-p x) (qir-out-int (cdr x) (qir-out-string "%d" acc)))
        ((qir-wtemp-p x) (qir-out-int (cdr x) (qir-out-string "%w" acc)))
        ((qir-const-p x) (qir-out-int (cdr x) acc))
        ((stringp x) (qir-out-string x acc))
        ((integerp x) (qir-out-int x acc))
        ((symbolp x) (qir-out-lower (symbol-name x) 0 (length (symbol-name x)) acc))
        (t (qir-out-string "?" acc))))

(defun qir-out-label (label acc)
  (qir-out-int label (cons #\@ acc)))

; Writes each field after a space.
(defun qir-out-fields (xs acc)
  (if (atom xs)
      acc
    (qir-out-fields (cdr xs) (qir-out-operand (car xs) (cons #\Space acc)))))

(defun qir-out-phi-args (args acc)
  (if (atom args)
      acc
    (qir-out-phi-args (cdr args)
                      (qir-out-operand (cdar args)
                                       (cons #\Space (qir-out-label (caar args)
                                                                    (cons #\Space acc)))))))

(defun qir-out-dest (dest acc)
  (if dest
      (qir-out-string " = " (qir-out-operand dest acc))
    acc))

(defun qir-out-phis (phis acc)
  (if (atom phis)
      acc
    (qir-out-phis (cdr phis)
                  (cons #\Newline
                        (qir-out-phi-args (qir-phi-args (car phis))
                                          (qir-out-string "phi"
                                                          (qir-out-dest (qir-phi-dest (car phis))
                                                                        (cons #\Tab acc))))))))

(defun qir-out-insts (insts acc)
  (if (atom insts)
      acc
    (let ((inst (car insts)))
      (qir-out-insts (cdr insts)
                     (cons #\Newline
                           (qir-out-fields (cddr inst)
                                           (qir-out-operand (qir-inst-op inst)
                                                            (qir-out-dest (qir-inst-dest inst)
                                                                          (cons #\Tab acc)))))))))

(defun qir-out-labels (labels acc)
  (if (atom labels)
      acc
    (qir-out-labels (cdr labels) (qir-out-label (car labels) (cons #\Space acc)))))

(defun qir-out-jump (jump acc)
  (let* ((op (car jump))
         (acc (qir-out-operand op (cons #\Tab acc)))
         (acc (cond ((equal op :jmp) (qir-out-labels (cdr jump) acc))
                    ((or (equal op :if) (equal op :jnz))
                     (qir-out-labels (cddr jump) (qir-out-fields (list (cadr jump)) acc)))
                    (t (qir-out-fields (cdr jump) acc)))))
    (cons #\Newline acc)))

(defun qir-out-blocks (blocks acc)
  (if (atom blocks)
      acc
    (let ((block (car blocks)))
      (qir-out-blocks (cdr blocks)
                      (qir-out-jump (qir-block-jump block)
                                    (qir-out-insts (qir-block-insts block)
                                                   (qir-out-phis (qir-block-phis block)
                                                                 (cons #\Newline
                                                                       (qir-out-label (qir-block-label block)
                                                                                      acc)))))))))

(defun qir-out-fn (fn acc)
  (let* ((acc (qir-out-string (qir-fn-name fn) (qir-out-string "function " acc)))
         (acc (qir-out-string " (" acc))
         (acc (if (consp (qir-fn-params fn))
                  (qir-out-fields (cdr (qir-fn-params fn))
                                  (qir-out-operand (car (qir-fn-params fn)) acc))
                acc))
         (acc (cons #\) acc))
         (acc (if (equal (len fn) 5)
                  (qir-out-int (qir-fn-nslots fn) (qir-out-string " slots " acc))
                acc)))
    (qir-out-string (coerce '(#\} #\Newline) 'string)
                    (qir-out-blocks (qir-fn-blocks fn)
                                    (qir-out-string (coerce '(#\Space #\{ #\Newline) 'string) acc)))))

(defun qir-out-fns (fns acc)
  (if (atom fns)
      acc
    (qir-out-fns (cdr fns) (qir-out-fn (car fns) acc))))

; The text of a program of QIR.
(defun qir-print (fns)
  (coerce (reverse (qir-out-fns fns nil)) 'string))

; The text of one function.
(defun qir-print-fn (fn)
  (coerce (reverse (qir-out-fn fn nil)) 'string))
