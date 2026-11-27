(in-package "BOYMOO-COMPILER")

(include-book "isel")

(set-verify-guards-eagerness 0)

; P8: register assignment on MIR by linear scan (compiler/README.md,
; "MIR"). Liveness is computed on the blocks; each virtual register gets one
; interval, the span of the places where it is live, in the order of the
; blocks. A register that is live across a call of a compiled function
; lives in a slot of the machine stack, since such a call may change
; every register; one that is live across a call of a routine of the
; runtime may live only in x19 to x22 or x29, which the routines keep.
; Other registers get x0 to x15, x19 to x22 or x29, or a slot of the
; machine stack when all are taken. x16 and x17 are kept for P9.

; The registers that MIR instructions define and use, by number.

(defun mir-numbers (xs acc)
  (cond ((atom xs) acc)
        ((qtemp-p (car xs)) (mir-numbers (cdr xs) (cons (cdar xs) acc)))
        (t (mir-numbers (cdr xs) acc))))

(defun mir-dest (inst)
  (case (car inst)
    ((:mov :li :cset :csel :ld :ldb :vld) (cadr inst))
    ((:rrr :rri) (caddr inst))
    ((:call :rt) (cadddr inst))
    (otherwise nil)))

(defun mir-sources (inst)
  (case (car inst)
    (:mov (list (caddr inst)))
    ((:rrr :csel) (if (eq (car inst) :rrr)
                      (list (cadddr inst) (car (cddddr inst)))
                    (list (caddr inst) (cadddr inst))))
    (:rri (list (cadddr inst)))
    ((:cmp :cmn) (list (cadr inst) (caddr inst)))
    ((:cmpi :cmni :vst :tst) (list (cadr inst)))
    ((:ld :ldb) (list (caddr inst)))
    (:call (caddr inst))
    (:rt (append (caddr inst) (car (cddddr inst))))
    (otherwise nil)))

(defun mir-term-sources (term)
  (case (car term)
    ((:cbnz :ret :tbnz) (list (cadr term)))
    (:tail (caddr term))
    (otherwise nil)))

(defun mir-term-successors (term)
  (case (car term)
    (:b (list (cadr term)))
    ((:bc :cbnz) (if (equal (caddr term) (cadddr term))
                     (list (caddr term))
                   (list (caddr term) (cadddr term))))
    (:tbnz (if (equal (cadddr term) (car (cddddr term)))
               (list (cadddr term))
             (list (cadddr term) (car (cddddr term)))))
    (otherwise nil)))

(defun mir-inst-live (inst live)
  (let ((d (mir-dest inst)))
    (nset-from-list (mir-numbers (mir-sources inst) nil)
                    (if (qtemp-p d) (nset-del (cdr d) live) live))))

(defun mir-insts-live (rinsts live)
  (if (atom rinsts)
      live
    (mir-insts-live (cdr rinsts) (mir-inst-live (car rinsts) live))))

(defun mir-live-out (succs table acc)
  (if (atom succs)
      acc
    (mir-live-out (cdr succs) table (nset-union (ntab-get (car succs) table) acc))))

(defun mir-block-end-live (b table)
  (let ((term (caddr b)))
    (nset-from-list (mir-numbers (mir-term-sources term) nil)
                    (mir-live-out (mir-term-successors term) table nil))))

(defun mir-block-live-in (b table)
  (mir-insts-live (reverse-onto (cadr b) nil) (mir-block-end-live b table)))

(defun mir-live-pass (rblocks table changed)
  (if (atom rblocks)
      (mv table changed)
    (let* ((b (car rblocks))
           (old (ntab-get (car b) table))
           (new (mir-block-live-in b table)))
      (if (equal old new)
          (mir-live-pass (cdr rblocks) table changed)
        (mir-live-pass (cdr rblocks) (ntab-put (car b) new table) t)))))

(defun mir-live-fix (rblocks table fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (zp fuel)
      table
    (mv-let (table changed)
      (mir-live-pass rblocks table nil)
      (if changed (mir-live-fix rblocks table (- fuel 1)) table))))

(defun mir-liveness (blocks)
  (mir-live-fix (reverse-onto blocks nil) nil (+ 2 (* (len blocks) (len blocks)))))

; Intervals: a table from each register number to (FROM . TO). The
; instruction of index I reads its sources at 2I and writes its
; destination at 2I + 1; the parameters are written at 1.

(defun rega-mark (n p tree)
  (let ((old (ntab-get n tree)))
    (ntab-put n (if old
                    (cons (if (< p (car old)) p (car old))
                          (if (< (cdr old) p) p (cdr old)))
                  (cons p p))
              tree)))

(defun rega-mark-all (ns p tree)
  (if (atom ns)
      tree
    (rega-mark-all (cdr ns) p (rega-mark (car ns) p tree))))

; Crossing: a table from each register number to :CALL when it is live
; across a call of a compiled function, or :RT when only across calls
; of routines.
(defun rega-cross (ns kind tree)
  (if (atom ns)
      tree
    (rega-cross (cdr ns) kind
                (if (eq (ntab-get (car ns) tree) :call)
                    tree
                  (ntab-put (car ns) kind tree)))))

; The registers live on entry to a block that have no interval yet. Only
; these need the mark of the block's start: a register with an interval
; began in an earlier block, and a register live on entry is used in the
; block or live at its end, which the block's other marks record.
(defun rega-absent (ns tree acc)
  (cond ((atom ns) (reverse-onto acc nil))
        ((ntab-get (car ns) tree) (rega-absent (cdr ns) tree acc))
        (t (rega-absent (cdr ns) tree (cons (car ns) acc)))))

; Walks the instructions of a block backward, from the index I of its
; last instruction, marking uses, definitions and calls.
(defun rega-walk (rinsts i live ivals cross)
  (if (atom rinsts)
      (mv ivals cross)
    (let* ((inst (car rinsts))
           (d (mir-dest inst))
           (after (if (qtemp-p d) (nset-del (cdr d) live) live))
           (cross (if (member (car inst) '(:call :rt))
                      (rega-cross after (car inst) cross)
                    cross))
           (ivals (if (qtemp-p d) (rega-mark (cdr d) (+ 1 (* 2 i)) ivals) ivals))
           (srcs (mir-numbers (mir-sources inst) nil))
           (ivals (rega-mark-all srcs (* 2 i) ivals)))
      (rega-walk (cdr rinsts) (- i 1) (nset-from-list srcs after) ivals cross))))

; Marks every block; I is the index of the first instruction of the
; first block. Gives the intervals and the crossing table.
(defun rega-blocks (blocks i live-table ivals cross)
  (if (atom blocks)
      (mv ivals cross)
    (let* ((b (car blocks))
           (n (len (cadr b)))
           (last (+ i n))
           (out (mir-live-out (mir-term-successors (caddr b)) live-table nil))
           (end-live (mir-block-end-live b live-table))
           (fresh (rega-absent (ntab-get (car b) live-table) ivals nil))
           (ivals (rega-mark-all out (+ 1 (* 2 last)) ivals))
           (ivals (rega-mark-all (mir-numbers (mir-term-sources (caddr b)) nil) (* 2 last) ivals))
           (ivals (rega-mark-all fresh (* 2 i) ivals)))
      (mv-let (ivals cross)
        (rega-walk (reverse-onto (cadr b) nil) (- last 1) end-live ivals cross)
        (rega-blocks (cdr blocks) (+ last 1) live-table ivals cross)))))

; Hints: for each virtual register, a list of registers it would best
; be in, first those of the virtual registers it is copied to or from,
; written (:V . M), then the argument registers of the calls it is
; passed to, x0 for a result, and xI for the I-th parameter.
(defun rega-hint (x h tree)
  (if (qtemp-p x)
      (ntab-put (cdr x) (append (ntab-get (cdr x) tree) (list h)) tree)
    tree))

(defun rega-hint-args (args r tree)
  (if (or (atom args) (< 7 r))
      tree
    (rega-hint-args (cdr args) (+ r 1) (rega-hint (car args) r tree))))

(defun rega-hint-copies (insts tree)
  (if (atom insts)
      tree
    (let ((inst (car insts)))
      (rega-hint-copies
       (cdr insts)
       (if (and (eq (car inst) :mov) (qtemp-p (cadr inst)) (qtemp-p (caddr inst)))
           (rega-hint (caddr inst) (cons :v (cdadr inst))
                      (rega-hint (cadr inst) (cons :v (cdaddr inst)) tree))
         tree)))))

(defun rega-hint-insts (insts tree)
  (if (atom insts)
      tree
    (let ((inst (car insts)))
      (rega-hint-insts
       (cdr insts)
       (if (member (car inst) '(:call :rt))
           (rega-hint (cadddr inst) 0 (rega-hint-args (caddr inst) 0 tree))
         tree)))))

(defun rega-hints-copies (blocks tree)
  (if (atom blocks)
      tree
    (rega-hints-copies (cdr blocks) (rega-hint-copies (cadr (car blocks)) tree))))

(defun rega-hints (blocks tree)
  (if (atom blocks)
      tree
    (let* ((b (car blocks))
           (term (caddr b))
           (tree (rega-hint-insts (cadr b) tree))
           (tree (case (car term)
                   (:ret (rega-hint (cadr term) 0 tree))
                   (:tail (rega-hint-args (caddr term) 0 tree))
                   (otherwise tree))))
      (rega-hints (cdr blocks) tree))))

; The intervals as a list of (FROM TO N), in order of FROM.

(defun rega-interval-list (ns ivals acc)
  (if (atom ns)
      acc
    (let ((iv (ntab-get (car ns) ivals)))
      (rega-interval-list (cdr ns) ivals
                          (if iv (cons (list (car iv) (cdr iv) (car ns)) acc) acc)))))

(defun rega-merge (a b)
  (declare (xargs :measure (+ (acl2-count a) (acl2-count b))))
  (cond ((atom a) b)
        ((atom b) a)
        ((< (caar b) (caar a)) (cons (car b) (rega-merge a (cdr b))))
        (t (cons (car a) (rega-merge (cdr a) b)))))

(defun rega-split (xs a b)
  (if (atom xs)
      (mv a b)
    (rega-split (cdr xs) (cons (car xs) b) a)))

(defun rega-sort (xs fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (atom xs) (atom (cdr xs)))
      xs
    (mv-let (a b)
      (rega-split xs nil nil)
      (rega-merge (rega-sort a (- fuel 1)) (rega-sort b (- fuel 1))))))

(defun rega-tree-keys (tree acc)
  (declare (xargs :measure (acl2-count tree)))
  (if (atom tree)
      acc
    (rega-tree-keys (cadr tree) (rega-tree-keys (cddr tree) (cons (car (cdar tree)) acc)))))

; The registers in order of preference, and those that routines keep.
(defconst *rega-registers*
  '(9 10 11 12 13 14 15 8 7 6 5 4 3 2 1 0 19 20 21 22 29))

(defconst *rega-kept-registers* '(19 20 21 22 29))

; The registers other than x0 and x1, which an inline cons takes its
; arguments in and gives its result in: a register stored before or
; loaded after such a cons is kept out of them, so that P9 can make the
; stores and loads only on the cons's slow path.
(defconst *rega-cons-registers*
  '(9 10 11 12 13 14 15 8 7 6 5 4 3 2 19 20 21 22 29))

; The registers around each cons get the kind :CONS, unless they cross a
; call already.
(defun rega-cons-mark (ns cross)
  (if (atom ns)
      cross
    (rega-cons-mark (cdr ns) (if (ntab-get (car ns) cross) cross (ntab-put (car ns) :cons cross)))))

(defun rega-vst-sources (rinsts acc)
  (if (and (consp rinsts) (eq (car (car rinsts)) :vst))
      (rega-vst-sources (cdr rinsts) (mir-numbers (list (cadr (car rinsts))) acc))
    acc))

; RBEFORE holds the instructions before the current one, the nearest
; first.
(defun rega-cons-insts (insts rbefore cross)
  (if (atom insts)
      cross
    (let ((inst (car insts)))
      (rega-cons-insts
       (cdr insts) (cons inst rbefore)
       (if (and (eq (car inst) :rt) (equal (cadr inst) "prim:COMMON-LISP::CONS"))
           (rega-cons-mark (mir-numbers (car (cddddr inst)) (rega-vst-sources rbefore nil)) cross)
         cross)))))

(defun rega-cons-blocks (blocks cross)
  (if (atom blocks)
      cross
    (rega-cons-blocks (cdr blocks) (rega-cons-insts (cadr (car blocks)) nil cross))))

; The join of two kinds: NIL below :CONS below :RT below :CALL.
(defun rega-kind-rank (k)
  (case k (:call 3) (:rt 2) (:cons 1) (otherwise 0)))

(defun rega-kind-join (a b)
  (if (< (rega-kind-rank a) (rega-kind-rank b)) b a))

; The active intervals: a list of (TO N R), in order of TO.
(defun rega-insert-active (entry active)
  (cond ((atom active) (list entry))
        ((< (car entry) (caar active)) (cons entry active))
        (t (cons (car active) (rega-insert-active entry (cdr active))))))

(defun rega-expire (active from free)
  (cond ((atom active) (mv active free))
        ((< (caar active) from) (rega-expire (cdr active) from (cons (caddr (car active)) free)))
        (t (mv active free))))

(defun rega-first-free (prefs free)
  (cond ((atom prefs) nil)
        ((member (car prefs) free) (car prefs))
        (t (rega-first-free (cdr prefs) free))))

; The active entry with the furthest end whose register is in POOL.
(defun rega-victim (active pool best)
  (cond ((atom active) best)
        ((member (caddr (car active)) pool)
         (rega-victim (cdr active) pool (car active)))
        (t (rega-victim (cdr active) pool best))))

(defun rega-remove-active (entry active)
  (cond ((atom active) nil)
        ((equal entry (car active)) (cdr active))
        (t (cons (car active) (rega-remove-active entry (cdr active))))))

(defun rega-remove (x xs)
  (cond ((atom xs) nil)
        ((equal x (car xs)) (cdr xs))
        (t (cons (car xs) (rega-remove x (cdr xs))))))

; Slots of the machine stack are reused: MACTIVE lists (TO N K) for the
; registers in slot K, in order of TO, and MFREE the slots free again.

(defun rega-mexpire (mactive from mfree)
  (cond ((atom mactive) (mv mactive mfree))
        ((< (caar mactive) from)
         (rega-mexpire (cdr mactive) from (cons (caddr (car mactive)) mfree)))
        (t (mv mactive mfree))))

; The register that the first usable hint of HINTS names: a register
; number, or (:V . M) for the register of the virtual register M.
(defun rega-pick (hints pool free homes)
  (if (atom hints)
      nil
    (let* ((h (car hints))
           (r (if (consp h)
                  (let ((home (ntab-get (cdr h) homes)))
                    (and home (eq (car home) :x) (cdr home)))
                h)))
      (if (and r (member r pool) (member r free))
          r
        (rega-pick (cdr hints) pool free homes)))))

; Assigns homes: a table from each register number to (:X . R) or
; (:M . K), K a slot of the machine stack. NEXT is the next new slot.
(defun rega-scan (ivals cross hints active free mactive mfree homes next)
  (if (atom ivals)
      (mv homes next)
    (let* ((iv (car ivals))
           (from (car iv))
           (to (cadr iv))
           (n (caddr iv))
           (kind (ntab-get n cross)))
      (mv-let (active free)
        (rega-expire active from free)
        (mv-let (mactive mfree)
          (rega-mexpire mactive from mfree)
          (let* ((pool (case kind
                         (:rt *rega-kept-registers*)
                         (:cons *rega-cons-registers*)
                         (otherwise *rega-registers*)))
                 (r (and (not (eq kind :call))
                         (or (rega-pick (ntab-get n hints) pool free homes)
                             (rega-first-free pool free)))))
            (if r
                (rega-scan (cdr ivals) cross hints
                           (rega-insert-active (list to n r) active)
                           (rega-remove r free)
                           mactive mfree
                           (ntab-put n (cons :x r) homes) next)
              (let* ((victim (and (not (eq kind :call)) (rega-victim active pool nil)))
                     (slot (if (consp mfree) (car mfree) next))
                     (rest (if (consp mfree) (cdr mfree) mfree))
                     (after (if (consp mfree) next (+ next 1))))
                ; A register put out of its register takes a new slot: one
                ; free again now may have been in use since it began.
                (if (and victim (< to (car victim)))
                    (rega-scan (cdr ivals) cross hints
                               (rega-insert-active (list to n (caddr victim))
                                                   (rega-remove-active victim active))
                               free
                               (rega-insert-active (list (car victim) (cadr victim) next) mactive)
                               mfree
                               (ntab-put n (cons :x (caddr victim))
                                         (ntab-put (cadr victim) (cons :m next) homes))
                               (+ next 1))
                  (rega-scan (cdr ivals) cross hints active free
                             (rega-insert-active (list to n slot) mactive) rest
                             (ntab-put n (cons :m slot) homes) after))))))))))

; Rewriting: each virtual register becomes its home.

(defun rega-operand (x homes)
  (if (qtemp-p x)
      (or (ntab-get (cdr x) homes) (cons :x 16))
    x))

(defun rega-operands (xs homes)
  (if (atom xs)
      xs
    (cons (rega-operand (car xs) homes) (rega-operands (cdr xs) homes))))

; An instruction or terminator: every field that is a register becomes
; its home, and so does each register in a field that lists operands.
(defun rega-fields (xs homes)
  (cond ((atom xs) xs)
        ((qtemp-p (car xs)) (cons (rega-operand (car xs) homes) (rega-fields (cdr xs) homes)))
        ((and (consp (car xs)) (not (qconst-p (car xs))))
         (cons (rega-operands (car xs) homes) (rega-fields (cdr xs) homes)))
        (t (cons (car xs) (rega-fields (cdr xs) homes)))))

; A move from a register to itself is dropped.
(defun rega-insts (insts homes)
  (if (atom insts)
      nil
    (let ((inst (rega-fields (car insts) homes)))
      (if (and (eq (car inst) :mov) (equal (cadr inst) (caddr inst)))
          (rega-insts (cdr insts) homes)
        (cons inst (rega-insts (cdr insts) homes))))))

(defun rega-rewrite (blocks homes)
  (if (atom blocks)
      nil
    (let ((b (car blocks)))
      (cons (list (car b) (rega-insts (cadr b) homes) (rega-fields (caddr b) homes))
            (rega-rewrite (cdr blocks) homes)))))

(defun rega-param-hints (params r tree)
  (if (or (atom params) (< 7 r))
      tree
    (rega-param-hints (cdr params) (+ r 1) (rega-hint (car params) r tree))))

; The assignment for one function: (HOMES NSPILL LIVE), where HOMES is
; the table from each register number to its home, NSPILL the number of
; slots of the machine stack, and LIVE the table from each label to the
; registers live on entry to its block.
; Coalescing. The two sides of a copy between virtual registers share a
; home when neither is live just after a definition of the other (the
; copy itself included) and they cross calls of the same kind; the copy
; then moves a register to itself, and is dropped. AFTER maps each
; register number to the sets live just after its definitions; ALIAS maps
; a number to the representative of its group, MEMBERS a representative
; to the numbers of its group.

(defun rega-after-insts (rinsts live tree)
  (if (atom rinsts)
      tree
    (let* ((inst (car rinsts))
           (d (mir-dest inst))
           (tree (if (qtemp-p d)
                     (ntab-put (cdr d) (cons live (ntab-get (cdr d) tree)) tree)
                   tree)))
      (rega-after-insts (cdr rinsts) (mir-inst-live inst live) tree))))

(defun rega-after-blocks (blocks live-table tree)
  (if (atom blocks)
      tree
    (rega-after-blocks (cdr blocks) live-table
                       (rega-after-insts (reverse-onto (cadr (car blocks)) nil)
                                         (mir-block-end-live (car blocks) live-table) tree))))

(defun rega-after-params (ns all tree)
  (if (atom ns)
      tree
    (rega-after-params (cdr ns) all
                       (ntab-put (car ns) (cons (nset-del (car ns) all) (ntab-get (car ns) tree))
                                 tree))))

(defun rega-find (n alias)
  (or (ntab-get n alias) n))

(defun rega-set-hits-p (set rep self alias)
  (cond ((atom set) nil)
        ((and (not (equal (car set) self)) (equal (rega-find (car set) alias) rep)) t)
        (t (rega-set-hits-p (cdr set) rep self alias))))

(defun rega-sets-hit-p (sets rep self alias)
  (cond ((atom sets) nil)
        ((rega-set-hits-p (car sets) rep self alias) t)
        (t (rega-sets-hit-p (cdr sets) rep self alias))))

(defun rega-members-hit-p (members rep after alias)
  (cond ((atom members) nil)
        ((rega-sets-hit-p (ntab-get (car members) after) rep (car members) alias) t)
        (t (rega-members-hit-p (cdr members) rep after alias))))

(defun rega-members (rep members)
  (or (ntab-get rep members) (list rep)))

(defun rega-interfere-p (a b after alias members)
  (or (rega-members-hit-p (rega-members a members) b after alias)
      (rega-members-hit-p (rega-members b members) a after alias)))

(defun rega-alias-all (ns rep alias)
  (if (atom ns)
      alias
    (rega-alias-all (cdr ns) rep (ntab-put (car ns) rep alias))))

(defun rega-coalesce-insts (insts after cross alias members budget)
  (if (or (atom insts) (zp budget))
      (mv alias members cross budget)
    (let ((inst (car insts)))
      (if (and (eq (car inst) :mov) (qtemp-p (cadr inst)) (qtemp-p (caddr inst)))
          (let ((a (rega-find (cdadr inst) alias))
                (b (rega-find (cdaddr inst) alias)))
            (if (and (not (equal a b))
                     (< (rega-kind-rank (rega-kind-join (ntab-get a cross) (ntab-get b cross))) 2)
                     (not (rega-interfere-p a b after alias members)))
                (rega-coalesce-insts (cdr insts) after
                                     (ntab-put a (rega-kind-join (ntab-get a cross) (ntab-get b cross))
                                               cross)
                                     (rega-alias-all (rega-members b members) a alias)
                                     (ntab-put a (append (rega-members a members)
                                                         (rega-members b members))
                                               members)
                                     (- budget 1))
              (rega-coalesce-insts (cdr insts) after cross alias members (- budget 1))))
        (rega-coalesce-insts (cdr insts) after cross alias members budget)))))

(defun rega-coalesce-blocks (blocks after cross alias members budget)
  (if (atom blocks)
      (mv alias members cross)
    (mv-let (alias members cross budget)
      (rega-coalesce-insts (cadr (car blocks)) after cross alias members budget)
      (rega-coalesce-blocks (cdr blocks) after cross alias members budget))))

; Whether a function has a copy between virtual registers, the only case
; in which the sets live after each definition are needed.
(defun rega-copies-insts-p (insts)
  (cond ((atom insts) nil)
        ((and (eq (car (car insts)) :mov) (qtemp-p (cadr (car insts))) (qtemp-p (caddr (car insts))))
         t)
        (t (rega-copies-insts-p (cdr insts)))))

(defun rega-copies-p (blocks)
  (cond ((atom blocks) nil)
        ((rega-copies-insts-p (cadr (car blocks))) t)
        (t (rega-copies-p (cdr blocks)))))

; The intervals, crossings and hints of the groups: those of their
; representatives, joined with those of the other members.
(defun rega-join-ivals (ns ivals alias acc)
  (if (atom ns)
      acc
    (let ((iv (ntab-get (car ns) ivals))
          (r (rega-find (car ns) alias)))
      (rega-join-ivals (cdr ns) ivals alias
                       (if iv (rega-mark r (cdr iv) (rega-mark r (car iv) acc)) acc)))))

(defun rega-join-hints (ns hints alias acc)
  (if (atom ns)
      acc
    (let ((r (rega-find (car ns) alias)))
      (rega-join-hints (cdr ns) hints alias
                       (ntab-put r (append (ntab-get r acc) (ntab-get (car ns) hints)) acc)))))

(defun rega-member-homes (ns homes alias acc)
  (if (atom ns)
      acc
    (rega-member-homes (cdr ns) homes alias
                       (let ((h (ntab-get (rega-find (car ns) alias) homes)))
                         (if h (ntab-put (car ns) h acc) acc)))))

; Hints that name a virtual register are read through ALIAS by
; REGA-PICK: a group's home is in HOMES under its representative.
(defun rega-alias-hints (hs alias)
  (cond ((atom hs) nil)
        ((consp (car hs)) (cons (cons :v (rega-find (cdar hs) alias)) (rega-alias-hints (cdr hs) alias)))
        (t (cons (car hs) (rega-alias-hints (cdr hs) alias)))))

(defun rega-alias-hint-table (ns hints alias acc)
  (if (atom ns)
      acc
    (rega-alias-hint-table (cdr ns) hints alias
                           (ntab-put (car ns) (rega-alias-hints (ntab-get (car ns) hints) alias) acc))))

; The assignment for one function: (HOMES NSPILL LIVE), where HOMES is
; the table from each register number to its home, NSPILL the number of
; slots of the machine stack, and LIVE the table from each label to the
; registers live on entry to its block.
; A runtime function written in QIR (qir.lisp, *qir-routines*), whose
; name begins "rt-qir:", keeps the registers that routines keep, as the
; code that calls it with :rt relies on: it is allocated without them.
(defun rega-remove-all (xs pool)
  (cond ((atom pool) nil)
        ((member (car pool) xs) (rega-remove-all xs (cdr pool)))
        (t (cons (car pool) (rega-remove-all xs (cdr pool))))))

(defun rega-rt-qir-p (name)
  (and (stringp name) (< 7 (length name))
       (equal (subseq name 0 7) "rt-qir:")
       (qir-routine name)
       t))

(defun rega-pool (name)
  (if (rega-rt-qir-p name)
      (rega-remove-all *rega-kept-registers* *rega-registers*)
    *rega-registers*))

(defun rega-allocation (mfn)
  (let* ((params (caddr mfn))
         (blocks (car (cddddr mfn)))
         (live (mir-liveness blocks))
         (pnums (mir-numbers params nil))
         (ivals (rega-mark-all pnums 1 nil)))
    (mv-let (ivals cross)
      (rega-blocks blocks 1 live ivals nil)
      (let* ((after (if (rega-copies-p blocks)
                        (rega-after-params pnums (nset-from-list pnums nil)
                                           (rega-after-blocks blocks live nil))
                      nil))
             (keys (rega-tree-keys ivals nil)))
        (mv-let (alias members cross)
          (rega-coalesce-blocks blocks after (rega-cons-blocks blocks cross) nil nil 256)
          (declare (ignore members))
          ; With no group of more than one register, the groups' hints and
          ; homes are those of the registers. (Their intervals are rebuilt
          ; all the same: the order of the keys of the rebuilt tree decides
          ; between intervals that begin together.)
          (let* ((hints (rega-hints blocks (rega-hints-copies blocks (rega-param-hints params 0 nil))))
                 (givals (rega-join-ivals keys ivals alias nil))
                 (ghints (if alias (rega-join-hints keys hints alias nil) hints))
                 (ghints (if alias
                             (rega-alias-hint-table (rega-tree-keys ghints nil) ghints alias nil)
                           ghints))
                 (list (rega-sort (rega-interval-list (rega-tree-keys givals nil) givals nil) 64)))
            (mv-let (homes nspill)
              (rega-scan list cross ghints nil (rega-pool (cadr mfn)) nil nil nil 0)
              (list (if alias (rega-member-homes keys homes alias nil) homes) nspill live))))))))

; The pass for one function: (:MFN NAME HOMES NSLOTS BLOCKS NSPILL),
; where HOMES are the homes of the parameters, in order, and every
; register in BLOCKS is replaced by its home.
(defun rega-apply (mfn allocation)
  (let ((homes (car allocation)))
    (list :mfn (cadr mfn) (rega-operands (caddr mfn) homes) (cadddr mfn)
          (rega-rewrite (car (cddddr mfn)) homes) (cadr allocation))))

(defun rega-function (mfn)
  (rega-apply mfn (rega-allocation mfn)))

(defun rega-program (mfns)
  (if (atom mfns)
      nil
    (cons (rega-function (car mfns)) (rega-program (cdr mfns)))))
