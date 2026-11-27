(in-package "BOYMOO-COMPILER")

(include-book "qir")

(set-verify-guards-eagerness 0)

; P6: QIR-M to QIR-L (DESIGN.md, sections 3 and 4). The pass takes each
; function out of SSA form, then makes the collector's frame explicit:
; every data temporary that is live across an instruction that may
; collect gets a slot of the value-stack frame, is stored there before
; such an instruction (unless the slot holds its value already) and is
; loaded again after it. Blocks keep the shape (LABEL PHIS INSTS JUMP),
; with PHIS empty.

; Sets of natural numbers are lists in increasing order.

(defun nset-add (n s)
  (cond ((atom s) (list n))
        ((equal n (car s)) s)
        ((< n (car s)) (cons n s))
        (t (cons (car s) (nset-add n (cdr s))))))

(defun nset-del (n s)
  (cond ((atom s) nil)
        ((equal n (car s)) (cdr s))
        ((< n (car s)) s)
        (t (cons (car s) (nset-del n (cdr s))))))

(defun nset-member (n s)
  (cond ((atom s) nil)
        ((equal n (car s)) t)
        ((< n (car s)) nil)
        (t (nset-member n (cdr s)))))

(defun nset-union (a b)
  (declare (xargs :measure (+ (acl2-count a) (acl2-count b))))
  (cond ((atom a) b)
        ((atom b) a)
        ((equal (car a) (car b)) (cons (car a) (nset-union (cdr a) (cdr b))))
        ((< (car a) (car b)) (cons (car a) (nset-union (cdr a) b)))
        (t (cons (car b) (nset-union a (cdr b))))))

(defun nset-intersect (a b)
  (declare (xargs :measure (+ (acl2-count a) (acl2-count b))))
  (cond ((atom a) nil)
        ((atom b) nil)
        ((equal (car a) (car b)) (cons (car a) (nset-intersect (cdr a) (cdr b))))
        ((< (car a) (car b)) (nset-intersect (cdr a) b))
        (t (nset-intersect a (cdr b)))))

(defun nset-minus (a b)
  (declare (xargs :measure (+ (acl2-count a) (acl2-count b))))
  (cond ((atom a) nil)
        ((atom b) a)
        ((equal (car a) (car b)) (nset-minus (cdr a) (cdr b)))
        ((< (car a) (car b)) (cons (car a) (nset-minus (cdr a) b)))
        (t (nset-minus a (cdr b)))))

(defun nset-from-list (xs acc)
  (if (atom xs)
      acc
    (nset-from-list (cdr xs) (nset-add (car xs) acc))))

; Tables keyed by natural numbers, the trees of a64.lisp.

; The keys are natural numbers, compared with <; the trees are the same
; as table-tree-put builds.
(defun ntab-get (key tree)
  (if (atom tree)
      nil
    (let* ((entry (cdar tree))
           (other (car entry)))
      (cond ((equal key other) (cdr entry))
            ((< key other) (ntab-get key (cadr tree)))
            (t (ntab-get key (cddr tree)))))))

(defun ntab-put (key value tree)
  (if (atom tree)
      (table-node (cons key value) nil nil)
    (let* ((entry (cdar tree))
           (other (car entry))
           (left (cadr tree))
           (right (cddr tree)))
      (cond ((equal key other) (table-node (cons key value) left right))
            ((< key other) (table-balance entry (ntab-put key value left) right))
            (t (table-balance entry left (ntab-put key value right)))))))

; Operands, instructions and blocks.

(defun qtemp-p (x)
  (and (consp x) (or (eq (car x) :d) (eq (car x) :w))))

(defun qdata-p (x)
  (and (consp x) (eq (car x) :d)))

(defun qconst-p (x)
  (and (consp x) (eq (car x) :k)))

; The numbers of the data temporaries among XS, added to the set S.
(defun qdata-numbers (xs s)
  (cond ((atom xs) s)
        ((qdata-p (car xs)) (qdata-numbers (cdr xs) (nset-add (cdar xs) s)))
        (t (qdata-numbers (cdr xs) s))))

(defun qblock-label (b) (car b))
(defun qblock-phis (b) (cadr b))
(defun qblock-insts (b) (caddr b))
(defun qblock-jump (b) (cadddr b))

(defun qblock (label phis insts jump)
  (list label phis insts jump))

(defun qinst-dest (inst) (car inst))
(defun qinst-op (inst) (cadr inst))
(defun qinst-args (inst) (cddr inst))

(defun qjump-successors (jump)
  (case (car jump)
    (:jmp (list (cadr jump)))
    ((:if :jnz) (if (equal (caddr jump) (cadddr jump))
                    (list (caddr jump))
                  (list (caddr jump) (cadddr jump))))
    (otherwise nil)))

; The operands that a jump or an instruction reads, and whether an
; instruction may collect, as qir.lisp gives them.
(defun qjump-operands (jump)
  (qir-jump-uses jump))

(defun qinst-operands (inst)
  (qir-inst-uses inst))

(defun qinst-collects-p (inst)
  (qir-inst-may-collect-p inst))

; The largest temporary number and label of a function.

(defun abi-max-operands (xs m)
  (cond ((atom xs) m)
        ((and (qtemp-p (car xs)) (natp (cdar xs)) (< m (cdar xs)))
         (abi-max-operands (cdr xs) (cdar xs)))
        (t (abi-max-operands (cdr xs) m))))

(defun abi-max-phis (phis m)
  (if (atom phis)
      m
    (abi-max-phis (cdr phis) (abi-max-operands (list (caar phis)) m))))

(defun abi-max-insts (insts m)
  (if (atom insts)
      m
    (abi-max-insts (cdr insts)
                   (abi-max-operands (cons (qinst-dest (car insts))
                                           (qinst-operands (car insts)))
                                     m))))

(defun abi-max-temp (blocks m)
  (if (atom blocks)
      m
    (abi-max-temp (cdr blocks)
                  (abi-max-insts (qblock-insts (car blocks))
                                 (abi-max-phis (qblock-phis (car blocks)) m)))))

(defun abi-max-label (blocks m)
  (cond ((atom blocks) m)
        ((< m (qblock-label (car blocks))) (abi-max-label (cdr blocks) (qblock-label (car blocks))))
        (t (abi-max-label (cdr blocks) m))))

(defun abi-block-table (blocks tree)
  (if (atom blocks)
      tree
    (abi-block-table (cdr blocks) (ntab-put (qblock-label (car blocks)) (car blocks) tree))))

; 1. A conditional jump with two equal targets becomes a jump.

(defun abi-normal-jump (jump)
  (if (and (member (car jump) '(:if :jnz)) (equal (caddr jump) (cadddr jump)))
      (list :jmp (caddr jump))
    jump))

(defun abi-normalize (blocks)
  (if (atom blocks)
      nil
    (let ((b (car blocks)))
      (cons (qblock (qblock-label b) (qblock-phis b) (qblock-insts b)
                    (abi-normal-jump (qblock-jump b)))
            (abi-normalize (cdr blocks))))))

; 2. Splitting edges. An edge from a block with two successors to a
; block with phis passes through a new block, so that the copies of the
; phis are made on that edge only.

(defun abi-retarget (jump old new)
  (case (car jump)
    (:jmp (if (equal (cadr jump) old) (list :jmp new) jump))
    ((:if :jnz) (list (car jump) (cadr jump)
                      (if (equal (caddr jump) old) new (caddr jump))
                      (if (equal (cadddr jump) old) new (cadddr jump))))
    (otherwise jump)))

; Splits the edges of one block. Gives the new jump, the new blocks,
; the renamings (TARGET PRED . NEW) of phi arguments, and the next label.
(defun abi-split-successors (succs label jump table next added renames)
  (if (atom succs)
      (mv jump added renames next)
    (let* ((s (car succs))
           (target (ntab-get s table)))
      (if (and target (consp (qblock-phis target)))
          (abi-split-successors (cdr succs) label (abi-retarget jump s next) table (+ next 1)
                                (cons (qblock next nil nil (list :jmp s)) added)
                                (cons (list* s label next) renames))
        (abi-split-successors (cdr succs) label jump table next added renames)))))

(defun abi-split-blocks (blocks table next out added renames)
  (if (atom blocks)
      (mv (reverse-onto out nil) added renames)
    (let* ((b (car blocks))
           (succs (qjump-successors (qblock-jump b))))
      (if (consp (cdr succs))
          (mv-let (jump added renames next)
            (abi-split-successors succs (qblock-label b) (qblock-jump b) table next added renames)
            (abi-split-blocks (cdr blocks) table next
                              (cons (qblock (qblock-label b) (qblock-phis b) (qblock-insts b) jump) out)
                              added renames))
        (abi-split-blocks (cdr blocks) table next (cons b out) added renames)))))

(defun abi-rename-arg (arg target renames)
  (cond ((atom renames) arg)
        ((and (equal (car (car renames)) target)
              (equal (cadr (car renames)) (car arg)))
         (cons (cddr (car renames)) (cdr arg)))
        (t (abi-rename-arg arg target (cdr renames)))))

(defun abi-rename-args (args target renames)
  (if (atom args)
      nil
    (cons (abi-rename-arg (car args) target renames)
          (abi-rename-args (cdr args) target renames))))

(defun abi-rename-phis (phis target renames)
  (if (atom phis)
      nil
    (cons (list (car (car phis)) (abi-rename-args (cadr (car phis)) target renames))
          (abi-rename-phis (cdr phis) target renames))))

(defun abi-rename-blocks (blocks renames)
  (if (atom blocks)
      nil
    (let ((b (car blocks)))
      (cons (if (consp (qblock-phis b))
                (qblock (qblock-label b)
                        (abi-rename-phis (qblock-phis b) (qblock-label b) renames)
                        (qblock-insts b) (qblock-jump b))
              b)
            (abi-rename-blocks (cdr blocks) renames)))))

(defun abi-split-edges (blocks)
  (mv-let (blocks added renames)
    (abi-split-blocks blocks (abi-block-table blocks nil)
                      (+ 1 (abi-max-label blocks 0)) nil nil nil)
    (if (atom added)
        blocks
      (append (abi-rename-blocks blocks renames) (reverse-onto added nil)))))

; 3. Phis become copies at the end of each predecessor. A parallel copy
; is a list of (DEST . SOURCE); it is made a sequence of copies, with a
; fresh temporary to break each cycle.

(defun abi-source-p (x copies)
  (cond ((atom copies) nil)
        ((equal x (cdar copies)) t)
        (t (abi-source-p x (cdr copies)))))

(defun abi-drop-self (copies)
  (cond ((atom copies) nil)
        ((equal (caar copies) (cdar copies)) (abi-drop-self (cdr copies)))
        (t (cons (car copies) (abi-drop-self (cdr copies))))))

; A copy whose destination no other copy reads, or NIL.
(defun abi-free-copy (rest copies)
  (cond ((atom rest) nil)
        ((not (abi-source-p (caar rest) copies)) (car rest))
        (t (abi-free-copy (cdr rest) copies))))

(defun abi-remove-copy (copy copies)
  (cond ((atom copies) nil)
        ((equal copy (car copies)) (cdr copies))
        (t (cons (car copies) (abi-remove-copy copy (cdr copies))))))

(defun abi-replace-source (old new copies)
  (cond ((atom copies) nil)
        ((equal (cdar copies) old) (cons (cons (caar copies) new)
                                         (abi-replace-source old new (cdr copies))))
        (t (cons (car copies) (abi-replace-source old new (cdr copies))))))

; Gives the copies as instructions, in reverse order onto OUT, and the
; next fresh temporary number.
(defun abi-sequence (copies fresh out fuel)
  (declare (xargs :measure (nfix fuel)))
  (let ((copies (abi-drop-self copies)))
    (cond ((atom copies) (mv out fresh))
          ((zp fuel) (mv (compiler-error "Parallel copy did not finish: ~x0." copies) fresh))
          (t
           (let ((free (abi-free-copy copies copies)))
             (if free
                 (abi-sequence (abi-remove-copy free copies) fresh
                               (cons (list (car free) :copy (cdr free)) out) (- fuel 1))
               (let* ((d (caar copies))
                      (temp (cons (car d) fresh)))
                 (abi-sequence (abi-replace-source d temp copies) (+ fresh 1)
                               (cons (list temp :copy d) out) (- fuel 1)))))))))

(defun abi-sequence-copies (copies fresh)
  (mv-let (out fresh)
    (abi-sequence copies fresh nil (+ 2 (* 2 (len copies))))
    (mv (reverse-onto out nil) fresh)))

; The copies of the phis PHIS for the predecessor PRED.
(defun abi-phi-copies (phis pred)
  (if (atom phis)
      nil
    (let ((arg (assoc-equal pred (cadr (car phis)))))
      (if arg
          (cons (cons (car (car phis)) (cdr arg)) (abi-phi-copies (cdr phis) pred))
        (abi-phi-copies (cdr phis) pred)))))

; A table from each predecessor to the parallel copy at its end.
(defun abi-phi-preds (args phis tree)
  (if (atom args)
      tree
    (abi-phi-preds (cdr args) phis
                   (ntab-put (caar args) (abi-phi-copies phis (caar args)) tree))))

(defun abi-copy-table (blocks tree)
  (if (atom blocks)
      tree
    (let ((phis (qblock-phis (car blocks))))
      (abi-copy-table (cdr blocks)
                      (if (consp phis)
                          (abi-phi-preds (cadr (car phis)) phis tree)
                        tree)))))

(defun abi-remove-phis (blocks table fresh)
  (if (atom blocks)
      (mv nil fresh)
    (let* ((b (car blocks))
           (copies (ntab-get (qblock-label b) table)))
      (mv-let (seq fresh)
        (abi-sequence-copies copies fresh)
        (mv-let (rest fresh)
          (abi-remove-phis (cdr blocks) table fresh)
          (mv (cons (qblock (qblock-label b) nil
                            (if (consp seq) (append (qblock-insts b) seq) (qblock-insts b))
                            (qblock-jump b))
                    rest)
              fresh))))))

; 4. Liveness of the data temporaries.

(defun abi-inst-live (inst live)
  (qdata-numbers (qinst-operands inst)
                 (if (qdata-p (qinst-dest inst))
                     (nset-del (cdr (qinst-dest inst)) live)
                   live)))

(defun abi-insts-live (rinsts live)
  (if (atom rinsts)
      live
    (abi-insts-live (cdr rinsts) (abi-inst-live (car rinsts) live))))

(defun abi-live-out (succs table acc)
  (if (atom succs)
      acc
    (abi-live-out (cdr succs) table (nset-union (ntab-get (car succs) table) acc))))

(defun abi-block-live-in (b table)
  (abi-insts-live (reverse-onto (qblock-insts b) nil)
                  (qdata-numbers (qjump-operands (qblock-jump b))
                                 (abi-live-out (qjump-successors (qblock-jump b)) table nil))))

(defun abi-live-pass (rblocks table changed)
  (if (atom rblocks)
      (mv table changed)
    (let* ((b (car rblocks))
           (old (ntab-get (qblock-label b) table))
           (new (abi-block-live-in b table)))
      (if (equal old new)
          (abi-live-pass (cdr rblocks) table changed)
        (abi-live-pass (cdr rblocks) (ntab-put (qblock-label b) new table) t)))))

(defun abi-live-fix (rblocks table fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      table
    (mv-let (table changed)
      (abi-live-pass rblocks table nil)
      (if changed (abi-live-fix rblocks table (- fuel 1)) table))))

; The table from each label to the data temporaries live on entry.
(defun abi-liveness (blocks)
  (abi-live-fix (reverse-onto blocks nil) nil (+ 2 (* (len blocks) (len blocks)))))

; 5. The data temporaries live across an instruction that may collect.

(defun abi-across-insts (rinsts live acc)
  (if (atom rinsts)
      acc
    (let* ((inst (car rinsts))
           (acc (if (qinst-collects-p inst)
                    (nset-union (if (qdata-p (qinst-dest inst))
                                    (nset-del (cdr (qinst-dest inst)) live)
                                  live)
                                acc)
                  acc)))
      (abi-across-insts (cdr rinsts) (abi-inst-live inst live) acc))))

(defun abi-across (blocks table acc)
  (if (atom blocks)
      acc
    (let ((b (car blocks)))
      (abi-across (cdr blocks) table
                  (abi-across-insts (reverse-onto (qblock-insts b) nil)
                                    (qdata-numbers (qjump-operands (qblock-jump b))
                                                   (abi-live-out (qjump-successors (qblock-jump b))
                                                                 table nil))
                                    acc)))))

; 6. Slots. Two spilled temporaries interfere when one is live just after
; a definition of the other, or both are parameters live on entry; those
; that do not interfere may share a slot. Each spilled temporary takes
; the lowest slot that no temporary it interferes with has taken.

(defun abi-graph-add (a b graph)
  (ntab-put a (nset-add b (ntab-get a graph)) graph))

(defun abi-graph-edges (n others graph)
  (cond ((atom others) graph)
        ((equal n (car others)) (abi-graph-edges n (cdr others) graph))
        (t (abi-graph-edges n (cdr others)
                            (abi-graph-add (car others) n (abi-graph-add n (car others) graph))))))

(defun abi-graph-insts (rinsts live spilled graph)
  (if (atom rinsts)
      graph
    (let* ((inst (car rinsts))
           (dest (qinst-dest inst))
           (graph (if (and (qdata-p dest) (nset-member (cdr dest) spilled))
                      (abi-graph-edges (cdr dest) (nset-intersect live spilled) graph)
                    graph)))
      (abi-graph-insts (cdr rinsts) (abi-inst-live inst live) spilled graph))))

(defun abi-block-end-live (b table)
  (qdata-numbers (qjump-operands (qblock-jump b))
                 (abi-live-out (qjump-successors (qblock-jump b)) table nil)))

(defun abi-graph-blocks (blocks table spilled graph)
  (if (atom blocks)
      graph
    (abi-graph-blocks (cdr blocks) table spilled
                      (abi-graph-insts (reverse-onto (qblock-insts (car blocks)) nil)
                                       (abi-block-end-live (car blocks) table)
                                       spilled graph))))

(defun abi-graph-params (params entry-live graph)
  (if (atom params)
      graph
    (abi-graph-params (cdr params) entry-live
                      (abi-graph-edges (car params) entry-live graph))))

(defun abi-used-slots (neighbours slots acc)
  (if (atom neighbours)
      acc
    (abi-used-slots (cdr neighbours) slots
                    (let ((slot (ntab-get (car neighbours) slots)))
                      (if slot (nset-add slot acc) acc)))))

(defun abi-lowest-free (i used)
  (cond ((atom used) i)
        ((equal i (car used)) (abi-lowest-free (+ i 1) (cdr used)))
        ((< i (car used)) i)
        (t (abi-lowest-free i (cdr used)))))

(defun abi-slots (spilled graph slots nslots)
  (if (atom spilled)
      (mv slots nslots)
    (let ((slot (abi-lowest-free 0 (abi-used-slots (ntab-get (car spilled) graph) slots nil))))
      (abi-slots (cdr spilled) graph (ntab-put (car spilled) slot slots)
                 (if (< slot nslots) nslots (+ slot 1))))))

; The spilled temporaries live across each instruction that may collect.
; For each block, a list with one entry for each instruction: the set
; for one that may collect, NIL for one that cannot.

(defun abi-needs-insts (rinsts live spilled acc)
  (if (atom rinsts)
      acc
    (let ((inst (car rinsts)))
      (abi-needs-insts (cdr rinsts) (abi-inst-live inst live) spilled
                       (cons (if (qinst-collects-p inst)
                                 (nset-intersect (if (qdata-p (qinst-dest inst))
                                                     (nset-del (cdr (qinst-dest inst)) live)
                                                   live)
                                                 spilled)
                               nil)
                             acc)))))

(defun abi-needs (blocks table spilled tree)
  (if (atom blocks)
      tree
    (let ((b (car blocks)))
      (abi-needs (cdr blocks) table spilled
                 (ntab-put (qblock-label b)
                           (abi-needs-insts (reverse-onto (qblock-insts b) nil)
                                            (abi-block-end-live b table) spilled nil)
                           tree)))))

; 7. Stores and loads. Before an instruction that may collect, each
; temporary live across it is stored in its slot unless the slot holds
; its value already on every path; after the instruction each is loaded
; again, and a load whose value is not used is then dropped. (P9 may
; make the stores, clearing stores and loads around a :cons only on its
; slow path, so a :cons adds nothing to CURRENT and takes nothing from
; DIRTY.) So the
; temporaries are kept in the frame only on the paths that call, and
; every live data temporary is in a temporary everywhere else. CURRENT
; is the set of spilled temporaries whose slot holds their value: a
; store adds to it, a definition removes from it, and the meet of two
; paths intersects. DIRTY is the set of slots that may hold a datum
; written since the function began: before an instruction that may
; collect, each dirty slot that is not needed across it is set to the
; datum 1, the immediate integer 0, so that the collector does not keep
; what it referred to alive.

(defun abi-slot-set (ns slots acc)
  (if (atom ns)
      acc
    (abi-slot-set (cdr ns) slots (nset-add (ntab-get (car ns) slots) acc))))

(defun abi-spills (ns slots out)
  (if (atom ns)
      out
    (abi-spills (cdr ns) slots
                (cons (list nil :spill (ntab-get (car ns) slots) (cons :d (car ns))) out))))

(defun abi-loads (ns slots out)
  (if (atom ns)
      out
    (abi-loads (cdr ns) slots
               (cons (list (cons :d (car ns)) :reload (ntab-get (car ns) slots)) out))))

(defun abi-clear-spills (stale temp out)
  (if (atom stale)
      out
    (abi-clear-spills (cdr stale) temp (cons (list nil :spill (car stale) temp) out))))

; The stores that clear the slots STALE, in reverse order onto OUT, with
; TEMP, a data temporary that holds the datum 1.
(defun abi-clears (stale temp out)
  (if (atom stale)
      out
    (abi-clear-spills stale temp (cons (list temp :copy (cons :k 1)) out))))

(defun abi-undef (dest current)
  (if (qdata-p dest) (nset-del (cdr dest) current) current))

; Rewrites the instructions of a block, with NEEDS the temporaries live
; across each; gives them in reverse order onto OUT, with CURRENT and
; DIRTY at their end.
(defun abi-rewrite-insts (insts needs slots temp current dirty out)
  (if (atom insts)
      (mv out current dirty)
    (let ((inst (car insts)))
      (if (qinst-collects-p inst)
          (let* ((live (car needs))
                 (stores (nset-minus live current))
                 (needed (abi-slot-set live slots nil))
                 (out (abi-clears (nset-minus dirty needed) temp out))
                 (out (abi-spills stores slots out))
                 (dirty (nset-union (abi-slot-set stores slots nil) dirty))
                 (dirty (if (equal (qinst-op inst) :cons) dirty (nset-intersect dirty needed)))
                 (out (abi-loads live slots (cons inst out))))
            (abi-rewrite-insts (cdr insts) (cdr needs) slots temp
                               (abi-undef (qinst-dest inst)
                                          (if (equal (qinst-op inst) :cons)
                                              current
                                            (nset-union live current)))
                               dirty out))
        (abi-rewrite-insts (cdr insts) (cdr needs) slots temp
                           (abi-undef (qinst-dest inst) current) dirty (cons inst out))))))

; The same states as ABI-REWRITE-INSTS gives, without the instructions,
; for the analysis over the blocks.
(defun abi-state-insts (insts needs slots current dirty)
  (if (atom insts)
      (mv current dirty)
    (let ((inst (car insts)))
      (if (qinst-collects-p inst)
          (let* ((live (car needs))
                 (stores (nset-minus live current))
                 (needed (abi-slot-set live slots nil))
                 (dirty (nset-union (abi-slot-set stores slots nil) dirty))
                 (dirty (if (equal (qinst-op inst) :cons) dirty (nset-intersect dirty needed))))
            (abi-state-insts (cdr insts) (cdr needs) slots
                             (abi-undef (qinst-dest inst)
                                        (if (equal (qinst-op inst) :cons)
                                            current
                                          (nset-union live current)))
                             dirty))
        (abi-state-insts (cdr insts) (cdr needs) slots
                         (abi-undef (qinst-dest inst) current) dirty)))))

; CURRENT on entry to a block: the intersection over its predecessors;
; DIRTY: the union. :ALL stands for every temporary, before a
; predecessor is known.
(defun abi-meet (a b)
  (cond ((eq a :all) b)
        ((eq b :all) a)
        (t (nset-intersect a b))))

(defun abi-current-in (preds outs)
  (if (atom preds)
      :all
    (abi-meet (let ((v (ntab-get (car preds) outs))) (if v (car v) :all))
              (abi-current-in (cdr preds) outs))))

(defun abi-dirty-in (preds outs)
  (if (atom preds)
      nil
    (nset-union (cdr (ntab-get (car preds) outs)) (abi-dirty-in (cdr preds) outs))))

(defun abi-preds-add (succs label tree)
  (if (atom succs)
      tree
    (abi-preds-add (cdr succs) label
                   (ntab-put (car succs) (cons label (ntab-get (car succs) tree)) tree))))

(defun abi-preds (blocks tree)
  (if (atom blocks)
      tree
    (abi-preds (cdr blocks)
               (abi-preds-add (qjump-successors (qblock-jump (car blocks)))
                              (qblock-label (car blocks)) tree))))

; The state on entry to block B: (CURRENT . DIRTY). On entry to the
; function every slot is DIRTY, since the prologue leaves the frame's
; words as they were: each slot is cleared or stored before the first
; instruction that may collect.
(defun abi-state-in (b entry-label preds outs)
  (if (equal (car entry-label) (qblock-label b))
      (cons nil (cdr entry-label))
    (let ((ps (ntab-get (qblock-label b) preds)))
      (cons (abi-current-in ps outs) (abi-dirty-in ps outs)))))

; OUTS maps a label to (CURRENT . DIRTY) at the end of its block; a
; missing entry is (:ALL . NIL). ENTRY-LABEL is the label of the entry
; block with the set of every slot.
(defun abi-state-pass (blocks entry-label preds needs slots outs changed)
  (if (atom blocks)
      (mv outs changed)
    (let* ((b (car blocks))
           (in (abi-state-in b entry-label preds outs)))
      (if (eq (car in) :all)
          (abi-state-pass (cdr blocks) entry-label preds needs slots outs changed)
        (mv-let (current dirty)
          (abi-state-insts (qblock-insts b) (ntab-get (qblock-label b) needs) slots
                           (car in) (cdr in))
          (let ((old (ntab-get (qblock-label b) outs)))
            (if (equal old (cons current dirty))
                (abi-state-pass (cdr blocks) entry-label preds needs slots outs changed)
              (abi-state-pass (cdr blocks) entry-label preds needs slots
                              (ntab-put (qblock-label b) (cons current dirty) outs) t))))))))

(defun abi-state-fix (blocks entry-label preds needs slots outs fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      outs
    (mv-let (outs changed)
      (abi-state-pass blocks entry-label preds needs slots outs nil)
      (if changed
          (abi-state-fix blocks entry-label preds needs slots outs (- fuel 1))
        outs))))

(defun abi-rewrite-blocks (blocks entry-label preds needs slots temp outs)
  (if (atom blocks)
      nil
    (let* ((b (car blocks))
           (in (abi-state-in b entry-label preds outs))
           (current (if (eq (car in) :all) nil (car in))))
      (mv-let (out current dirty)
        (abi-rewrite-insts (qblock-insts b) (ntab-get (qblock-label b) needs) slots temp
                           current (cdr in) nil)
        (declare (ignore current dirty))
        (cons (qblock (qblock-label b) nil (reverse-onto out nil) (qblock-jump b))
              (abi-rewrite-blocks (cdr blocks) entry-label preds needs slots temp outs))))))

; A load whose temporary is not live after it is dropped.

; The loads right after a :cons are made only on its slow path (P9), so
; the temporaries they load must be in their registers at the :cons: it
; counts as a use of them. PENDING holds the temporaries loaded after the
; instruction being looked at, up to the first instruction that is not a
; load.
(defun abi-drop-dead-insts (rinsts live pending acc)
  (if (atom rinsts)
      acc
    (let ((inst (car rinsts)))
      (cond ((equal (qinst-op inst) :reload)
             (if (nset-member (cdr (qinst-dest inst)) live)
                 (abi-drop-dead-insts (cdr rinsts) (abi-inst-live inst live)
                                      (nset-add (cdr (qinst-dest inst)) pending) (cons inst acc))
               (abi-drop-dead-insts (cdr rinsts) live pending acc)))
            ((equal (qinst-op inst) :cons)
             (abi-drop-dead-insts (cdr rinsts) (abi-inst-live inst (nset-union pending live))
                                  nil (cons inst acc)))
            (t (abi-drop-dead-insts (cdr rinsts) (abi-inst-live inst live) nil (cons inst acc)))))))

; Liveness with that rule, for the dropping of dead loads.
(defun abi-cons-insts-live (rinsts live pending)
  (if (atom rinsts)
      live
    (let ((inst (car rinsts)))
      (cond ((equal (qinst-op inst) :reload)
             (abi-cons-insts-live (cdr rinsts) (abi-inst-live inst live)
                                  (nset-add (cdr (qinst-dest inst)) pending)))
            ((equal (qinst-op inst) :cons)
             (abi-cons-insts-live (cdr rinsts) (abi-inst-live inst (nset-union pending live)) nil))
            (t (abi-cons-insts-live (cdr rinsts) (abi-inst-live inst live) nil))))))

(defun abi-cons-live-pass (rblocks table changed)
  (if (atom rblocks)
      (mv table changed)
    (let* ((b (car rblocks))
           (old (ntab-get (qblock-label b) table))
           (new (abi-cons-insts-live (reverse-onto (qblock-insts b) nil)
                                     (abi-block-end-live b table) nil)))
      (if (equal old new)
          (abi-cons-live-pass (cdr rblocks) table changed)
        (abi-cons-live-pass (cdr rblocks) (ntab-put (qblock-label b) new table) t)))))

(defun abi-cons-live-fix (rblocks table fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      table
    (mv-let (table changed)
      (abi-cons-live-pass rblocks table nil)
      (if changed (abi-cons-live-fix rblocks table (- fuel 1)) table))))

(defun abi-cons-liveness (blocks)
  (abi-cons-live-fix (reverse-onto blocks nil) nil (+ 2 (* (len blocks) (len blocks)))))

(defun abi-drop-dead (blocks table)
  (if (atom blocks)
      nil
    (let ((b (car blocks)))
      (cons (qblock (qblock-label b) nil
                    (abi-drop-dead-insts (reverse-onto (qblock-insts b) nil)
                                         (abi-block-end-live b table) nil nil)
                    (qblock-jump b))
            (abi-drop-dead (cdr blocks) table)))))

(defun abi-all-slots (n acc)
  (if (zp n) acc (abi-all-slots (- n 1) (cons (- n 1) acc))))

; The whole pass for one function.
(defun abi-function (fn)
  (let* ((name (cadr fn))
         (params (caddr fn))
         (blocks (abi-split-edges (abi-normalize (cadddr fn))))
         (fresh (+ 1 (abi-max-temp blocks (abi-max-operands params 0)))))
    (mv-let (blocks fresh)
      (abi-remove-phis blocks (abi-copy-table blocks nil) fresh)
      (let* ((live (abi-liveness blocks))
             (spilled (abi-across blocks live nil)))
        (if (atom spilled)
            (list :fn name params blocks 0)
          (let* ((entry-label (qblock-label (car blocks)))
                 (graph (abi-graph-params (nset-intersect (qdata-numbers params nil) spilled)
                                          (nset-intersect (ntab-get entry-label live) spilled)
                                          (abi-graph-blocks blocks live spilled nil))))
            (mv-let (slots nslots)
              (abi-slots spilled graph nil 0)
              (let* ((needs (abi-needs blocks live spilled nil))
                     (temp (cons :d fresh))
                     (preds (abi-preds blocks nil))
                     (entry (cons entry-label (abi-all-slots nslots nil)))
                     (outs (abi-state-fix blocks entry preds needs slots nil
                                          (+ 2 (* (len blocks) (len blocks)))))
                     (blocks (abi-rewrite-blocks blocks entry preds needs slots temp outs)))
                (list :fn name params (abi-drop-dead blocks (abi-cons-liveness blocks)) nslots)))))))))

(defun abi-program (fns)
  (if (atom fns)
      nil
    (cons (abi-function (car fns)) (abi-program (cdr fns)))))
