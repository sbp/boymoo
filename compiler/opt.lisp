(in-package "BOYMOO-COMPILER")

(include-book "qir")

(set-verify-guards-eagerness 0)

(defun opt-word (n)
  (low-bits n 64))

(defun opt-constant (n)
  (cons :k (opt-word n)))

(defun opt-constant-word (operand)
  (if (qir-const-p operand) (opt-word (cdr operand)) nil))

(defun opt-signed (word)
  (if (< word #x8000000000000000) word (- word #x10000000000000000)))

(defun opt-bit (truth)
  (if truth 1 0))

(defun opt-signed-overflow-p (n)
  (or (< n (- #x8000000000000000)) (<= #x8000000000000000 n)))

; A and B are unsigned words. The result, if defined, is a word.
(defun opt-binary-word (op a b)
  (case op
    (:add (opt-word (+ a b)))
    (:sub (opt-word (- a b)))
    (:mul (opt-word (* a b)))
    (:and (ash (- (+ a b) (acl2::binary-logxor a b)) -1))
    (:or (ash (+ a b (acl2::binary-logxor a b)) -1))
    (:xor (acl2::binary-logxor a b))
    (:shl (opt-word (ash a (low-bits b 6))))
    (:shr (ash a (- (low-bits b 6))))
    (:sar (opt-word (ash (opt-signed a) (- (low-bits b 6)))))
    (:ceq (opt-bit (equal a b)))
    (:cne (opt-bit (not (equal a b))))
    (:cslt (opt-bit (< (opt-signed a) (opt-signed b))))
    (:csle (opt-bit (<= (opt-signed a) (opt-signed b))))
    (:csgt (opt-bit (< (opt-signed b) (opt-signed a))))
    (:csge (opt-bit (<= (opt-signed b) (opt-signed a))))
    (:cult (opt-bit (< a b)))
    (:cule (opt-bit (<= a b)))
    (:cugt (opt-bit (< b a)))
    (:cuge (opt-bit (<= b a)))
    (:ovadd (opt-bit (opt-signed-overflow-p (+ (opt-signed a) (opt-signed b)))))
    (:ovsub (opt-bit (opt-signed-overflow-p (- (opt-signed a) (opt-signed b)))))
    (otherwise nil)))

(defun opt-binary-identity (op a b a-word b-word)
  (let ((zero '(:k . 0))
        (same (equal a b)))
    (case op
      (:add (cond ((equal a-word 0) b) ((equal b-word 0) a) (t nil)))
      (:sub (cond (same zero) ((equal b-word 0) a) (t nil)))
      (:mul (cond ((or (equal a-word 0) (equal b-word 0)) zero)
                  ((equal a-word 1) b)
                  ((equal b-word 1) a)
                  (t nil)))
      (:and (cond ((or (equal a-word 0) (equal b-word 0)) zero)
                  ((equal a-word #xFFFFFFFFFFFFFFFF) b)
                  ((or same (equal b-word #xFFFFFFFFFFFFFFFF)) a)
                  (t nil)))
      (:or (cond ((or (equal a-word #xFFFFFFFFFFFFFFFF) (equal b-word #xFFFFFFFFFFFFFFFF))
                  '(:k . #xFFFFFFFFFFFFFFFF))
                 ((equal a-word 0) b)
                 ((or same (equal b-word 0)) a)
                 (t nil)))
      (:xor (cond (same zero) ((equal a-word 0) b) ((equal b-word 0) a) (t nil)))
      ((:shl :shr :sar) (if (and b-word (equal (low-bits b-word 6) 0)) a nil))
      ((:ceq :csle :csge :cule :cuge) (if same '(:k . 1) nil))
      ((:cne :cslt :csgt :cult :cugt) (if same zero nil))
      (:ovadd (if (or (equal a-word 0) (equal b-word 0)) zero nil))
      (:ovsub (if (or same (equal b-word 0)) zero nil))
      (otherwise nil))))

; A replacement is a constant or an operand already defined in the function.
(defun opt-inst-replacement (inst)
  (let* ((op (qir-inst-op inst))
         (a (caddr inst))
         (b (cadddr inst)))
    (cond ((eq op :copy) a)
          ((eq op :sel)
           (let ((c (opt-constant-word a))
                 (f (car (cddddr inst))))
             (cond ((equal b f) b)
                   (c (if (equal c 0) f b))
                   (t nil))))
          ((qir-word-op-p op)
           (let ((a-word (opt-constant-word a))
                 (b-word (opt-constant-word b)))
             (if (and a-word b-word)
                 (opt-constant (opt-binary-word op a-word b-word))
               (opt-binary-identity op a b a-word b-word))))
          (t nil))))

(defun opt-compatible-p (dest operand)
  (or (qir-const-p operand)
      (and (qir-temp-p operand) (eq (car dest) (car operand)))))

(defun opt-follow (operand aliases fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (not (qir-temp-p operand)))
      operand
    (let ((other (qir-get (cdr operand) aliases)))
      (if other (opt-follow other aliases (- fuel 1)) operand))))

(defun opt-rewrite-operands (operands aliases fuel)
  (if (atom operands)
      nil
    (cons (opt-follow (car operands) aliases fuel)
          (opt-rewrite-operands (cdr operands) aliases fuel))))

(defun opt-rewrite-inst (inst aliases fuel)
  (let* ((op (qir-inst-op inst))
         (args (opt-rewrite-operands (qir-inst-uses inst) aliases fuel)))
    (if (member-eq op '(:call :rt))
        (list* (qir-inst-dest inst) op (caddr inst) args)
      (list* (qir-inst-dest inst) op args))))

(defun opt-rewrite-jump (jump aliases fuel)
  (case (car jump)
    (:jnz (list* :jnz (opt-follow (cadr jump) aliases fuel) (cddr jump)))
    (:ret (list :ret (opt-follow (cadr jump) aliases fuel)))
    (:tail (list* :tail (cadr jump) (opt-rewrite-operands (cddr jump) aliases fuel)))
    (otherwise jump)))

; Heap reads in QIR-M refer to fields of existing objects.
(defun opt-pure-op-p (op)
  (or (qir-word-op-p op) (member-eq op '(:copy :sel :ld :ldb))))

(defun opt-raw-operands-p (operands)
  (or (atom operands)
      (and (not (qir-dtemp-p (car operands))) (opt-raw-operands-p (cdr operands)))))

(defun opt-small-mask-p (operand)
  (let ((word (opt-constant-word operand)))
    (and word (<= word 7))))

(defun opt-fixed-datum-p (operand)
  (let ((word (opt-constant-word operand)))
    (and word (or (equal (low-bits word 1) 1) (equal (low-bits word 3) 4)
                  (equal word 34) (equal word 58)))))

; Raw operations on data sometimes observe the placement of heap objects.
; Tag bits and equality of data words survive relocation by the collector.
(defun opt-stable-inst-p (inst)
  (let ((op (qir-inst-op inst))
        (a (caddr inst))
        (b (cadddr inst)))
    (and (qir-wtemp-p (qir-inst-dest inst))
         (not (member-eq op '(:ld :ldb)))
         (or (opt-raw-operands-p (qir-inst-uses inst))
             (and (eq op :and) (or (opt-small-mask-p a) (opt-small-mask-p b)))
             (and (member-eq op '(:ceq :cne))
                  (or (qir-dtemp-p a) (opt-fixed-datum-p a))
                  (or (qir-dtemp-p b) (opt-fixed-datum-p b)))))))

(defun opt-value-key (inst)
  (let ((class (car (qir-inst-dest inst)))
        (op (qir-inst-op inst))
        (a (caddr inst))
        (b (cadddr inst)))
    (if (and (member-eq op '(:add :mul :and :or :xor :ceq :cne :ovadd))
             (table-key-less b a))
        (list class op b a)
      (cons class (cdr inst)))))

; GLOBAL holds values that survive collection. LOCAL holds other values
; available in the current heap epoch. Both contain dominating definitions.
(defun opt-number-insts (insts label aliases definitions global local epoch reversed)
  (if (atom insts)
      (mv (reverse-onto reversed nil) aliases definitions global local epoch)
    (let* ((inst (opt-rewrite-inst (car insts) aliases 1))
           (dest (qir-inst-dest inst))
           (pure (opt-pure-op-p (qir-inst-op inst)))
           (replacement (and dest pure (opt-inst-replacement inst))))
      (cond ((and pure (not dest))
             (opt-number-insts (cdr insts) label aliases definitions global local epoch reversed))
            ((and replacement (opt-compatible-p dest replacement))
             (opt-number-insts (cdr insts) label (qir-put (cdr dest) replacement aliases)
                                  definitions global local epoch reversed))
            (t
             (let* ((inst (if replacement (list dest :copy replacement) inst))
                    (stable (and pure (opt-stable-inst-p inst)))
                    (key (and pure (opt-value-key inst)))
                    (prior (and key (qir-get key (if stable global local)))))
               (if prior
                   (opt-number-insts (cdr insts) label (qir-put (cdr dest) prior aliases)
                                        definitions global local epoch reversed)
                 (let* ((collect (qir-inst-may-collect-p inst))
                        (global (if (and key stable) (qir-put key dest global) global))
                        (local (cond (collect nil)
                                     ((and key (not stable)) (qir-put key dest local))
                                     (t local)))
                        (epoch (if collect (cons :after label) epoch))
                        (definitions (if (and pure dest) (qir-put (cdr dest) inst definitions)
                                       definitions)))
                   (opt-number-insts (cdr insts) label aliases definitions global local epoch
                                        (cons inst reversed))))))))))

(defun opt-constant-select-p (inst)
  (and (eq (qir-inst-op inst) :sel)
       (not (qir-dtemp-p (caddr inst)))
       (qir-const-p (cadddr inst)) (qir-const-p (car (cddddr inst)))))

; In a branch, a comparison with the result of a conditional select can
; test the select's condition directly when its arms are constant.
(defun opt-binary-test (op a b definitions)
  (let* ((left (opt-constant-word a))
         (right (opt-constant-word b))
         (word (or left right))
         (operand (if left b a))
         (select (and (qir-temp-p operand) (qir-get (cdr operand) definitions))))
    (cond ((and (equal word 0) (qir-wtemp-p operand) (member-eq op '(:ceq :cne)))
           (mv operand (eq op :cne) (eq op :ceq)))
          ((and word (opt-constant-select-p select))
           (let* ((yes (opt-constant-word (cadddr select)))
                  (no (opt-constant-word (car (cddddr select))))
                  (yes (if left (opt-binary-word op word yes) (opt-binary-word op yes word)))
                  (no (if left (opt-binary-word op word no) (opt-binary-word op no word))))
             (mv (caddr select) (not (equal yes 0)) (not (equal no 0)))))
          (t (mv nil nil nil)))))

(defun opt-test-source (operand definitions)
  (let* ((inst (and (qir-temp-p operand) (qir-get (cdr operand) definitions)))
         (op (qir-inst-op inst)))
    (cond ((opt-constant-select-p inst)
           (mv (caddr inst) (not (equal (opt-constant-word (cadddr inst)) 0))
               (not (equal (opt-constant-word (car (cddddr inst))) 0))))
          ((qir-word-op-p op) (opt-binary-test op (caddr inst) (cadddr inst) definitions))
          (t (mv nil nil nil)))))

(defun opt-jnz (test yes no facts definitions fuel)
  (declare (xargs :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable opt-constant-word opt-test-source
                                                       qir-wtemp-p qir-get)))))
  (let ((word (opt-constant-word test))
        (fact (and (qir-wtemp-p test) (qir-get (cdr test) facts))))
    (cond ((equal yes no) (list :jmp yes))
          (word (list :jmp (if (equal word 0) no yes)))
          (fact (list :jmp (if (eq fact :nonzero) yes no)))
          ((zp fuel) (list :jnz test yes no))
          (t (mv-let (source positive negative)
               (opt-test-source test definitions)
               (cond ((not source) (list :jnz test yes no))
                     ((eq positive negative) (list :jmp (if positive yes no)))
                     (t (opt-jnz source (if positive yes no) (if positive no yes)
                                    facts definitions (- fuel 1)))))))))

(defun opt-simplify-jump (jump facts definitions)
  (if (eq (car jump) :jnz)
      (opt-jnz (cadr jump) (caddr jump) (cadddr jump) facts definitions 16)
    jump))

; A block's state records its new block, global and local value maps,
; heap epoch, and facts established on entry to it.
(defun opt-same-epoch-p (preds states epoch)
  (or (atom preds)
      (let ((state (qir-get (car preds) states)))
        (and state (equal (cadddr state) epoch)
             (opt-same-epoch-p (cdr preds) states epoch)))))

(defun opt-edge-facts (label preds states facts)
  (if (and (consp preds) (atom (cdr preds)))
      (let* ((jump (qir-block-jump (car (qir-get (car preds) states))))
             (test (cadr jump)))
        (if (and (eq (car jump) :jnz) (qir-wtemp-p test))
            (qir-put (cdr test) (if (equal label (caddr jump)) :nonzero :zero) facts)
          facts))
    facts))

(defun opt-number-blocks (labels bmap preds idoms states aliases definitions)
  (if (atom labels)
      (mv states aliases)
    (let* ((label (car labels))
           (block (qir-get label bmap))
           (dominant (qir-get (qir-get label idoms) states))
           (incoming (qir-get label preds))
           (old-epoch (cadddr dominant))
           (inherit (and dominant (opt-same-epoch-p incoming states old-epoch)))
           (epoch (if inherit old-epoch (cons :entry label)))
           (facts (opt-edge-facts label incoming states (car (cddddr dominant)))))
      (mv-let (insts aliases definitions global local epoch)
        (opt-number-insts (qir-block-insts block) label aliases definitions (cadr dominant)
                             (if inherit (caddr dominant) nil) epoch nil)
        (let* ((jump (opt-simplify-jump (opt-rewrite-jump (qir-block-jump block) aliases 1)
                                          facts definitions))
               (block (list label (qir-block-phis block) insts jump))
               (state (list block global local epoch facts)))
          (opt-number-blocks (cdr labels) bmap preds idoms (qir-put label state states)
                                aliases definitions))))))

(defun opt-rewrite-phi-args (args aliases fuel)
  (if (atom args)
      nil
    (cons (cons (caar args) (opt-follow (cdar args) aliases fuel))
          (opt-rewrite-phi-args (cdr args) aliases fuel))))

(defun opt-rewrite-phis (phis aliases fuel)
  (if (atom phis)
      nil
    (cons (list (qir-phi-dest (car phis)) (opt-rewrite-phi-args (qir-phi-args (car phis)) aliases fuel))
          (opt-rewrite-phis (cdr phis) aliases fuel))))

(defun opt-numbered-blocks (blocks states aliases)
  (if (atom blocks)
      nil
    (let* ((label (qir-block-label (car blocks)))
           (block (car (qir-get label states)))
           (rest (opt-numbered-blocks (cdr blocks) states aliases)))
      (if block
          (cons (list label (opt-rewrite-phis (qir-block-phis block) aliases 1)
                      (qir-block-insts block) (qir-block-jump block))
                rest)
        rest))))

; Numbering with the maps of the blocks given: their reverse post-order,
; predecessors, block map and immediate dominators.
(defun opt-number-cfg (blocks rpo preds bmap idoms)
  (mv-let (states aliases)
    (opt-number-blocks rpo bmap preds idoms nil nil nil)
    (opt-numbered-blocks blocks states aliases)))

(defun opt-number (blocks)
  (let ((rpo (qir-rpo blocks))
        (preds (qir-preds blocks)))
    (opt-number-cfg blocks rpo preds (qir-block-map blocks nil) (qir-idoms-of rpo preds))))

(defun opt-prune (blocks)
  (let ((blocks (qir-reachable-blocks blocks)))
    (qir-prune-blocks blocks (qir-preds blocks))))

; Self operands carry the previous value and do not prevent the other
; incoming operands from determining a loop phi.
(defun opt-phi-source (args dest aliases fuel source)
  (if (atom args)
      source
    (let ((operand (opt-follow (cdar args) aliases fuel)))
      (cond ((equal operand dest) (opt-phi-source (cdr args) dest aliases fuel source))
            ((and (opt-compatible-p dest operand) (or (not source) (equal source operand)))
             (opt-phi-source (cdr args) dest aliases fuel operand))
            (t nil)))))

(defun opt-phi-aliases (phis aliases fuel)
  (if (atom phis)
      aliases
    (let* ((phi (car phis))
           (dest (qir-phi-dest phi))
           (source (opt-phi-source (qir-phi-args phi) dest aliases fuel nil)))
      (opt-phi-aliases (cdr phis) (if source (qir-put (cdr dest) source aliases) aliases) fuel))))

(defun opt-block-phi-aliases (blocks aliases fuel)
  (if (atom blocks)
      aliases
    (opt-block-phi-aliases (cdr blocks)
                              (opt-phi-aliases (qir-block-phis (car blocks)) aliases fuel) fuel)))

(defun opt-keep-phis (phis aliases)
  (cond ((atom phis) nil)
        ((qir-get (cdr (qir-phi-dest (car phis))) aliases) (opt-keep-phis (cdr phis) aliases))
        (t (cons (car phis) (opt-keep-phis (cdr phis) aliases)))))

(defun opt-rewrite-insts (insts aliases fuel)
  (if (atom insts)
      nil
    (cons (opt-rewrite-inst (car insts) aliases fuel)
          (opt-rewrite-insts (cdr insts) aliases fuel))))

(defun opt-apply-phi-aliases (blocks aliases fuel)
  (if (atom blocks)
      nil
    (let ((block (car blocks)))
      (cons (list (qir-block-label block)
                  (opt-rewrite-phis (opt-keep-phis (qir-block-phis block) aliases) aliases fuel)
                  (opt-rewrite-insts (qir-block-insts block) aliases fuel)
                  (opt-rewrite-jump (qir-block-jump block) aliases fuel))
            (opt-apply-phi-aliases (cdr blocks) aliases fuel)))))

(defun opt-trivial-phis (blocks fuel)
  (let ((aliases (opt-block-phi-aliases blocks nil fuel)))
    (if aliases
        (mv (opt-apply-phi-aliases blocks aliases fuel) t)
      (mv blocks nil))))

; Dead-code elimination starts from terminators and effectful instructions.
; Operands of a phi or pure instruction are needed when its result is used.
(defun opt-phi-operands (args)
  (if (atom args)
      nil
    (cons (cdar args) (opt-phi-operands (cdr args)))))

(defun opt-dce-phis (phis definitions edges)
  (if (atom phis)
      (mv definitions edges)
    (let* ((phi (car phis))
           (uses (opt-phi-operands (qir-phi-args phi))))
      (opt-dce-phis (cdr phis) (qir-put (cdr (qir-phi-dest phi)) uses definitions)
                       (+ edges (len uses))))))

(defun opt-dce-insts (insts definitions roots edges)
  (if (atom insts)
      (mv definitions roots edges)
    (let* ((inst (car insts))
           (dest (qir-inst-dest inst))
           (uses (qir-inst-uses inst)))
      (if (opt-pure-op-p (qir-inst-op inst))
          (opt-dce-insts (cdr insts)
                            (if dest (qir-put (cdr dest) uses definitions) definitions)
                            roots (+ edges (len uses)))
        (opt-dce-insts (cdr insts) definitions (append uses roots) edges)))))

(defun opt-dce-blocks (blocks definitions roots edges)
  (if (atom blocks)
      (mv definitions roots edges)
    (let ((block (car blocks)))
      (mv-let (definitions edges)
        (opt-dce-phis (qir-block-phis block) definitions edges)
        (mv-let (definitions roots edges)
          (opt-dce-insts (qir-block-insts block) definitions
                            (append (qir-jump-uses (qir-block-jump block)) roots) edges)
          (opt-dce-blocks (cdr blocks) definitions roots edges))))))

(defun opt-mark-live (pending definitions marked fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((atom pending) (mv t marked))
        ((zp fuel) (mv nil marked))
        ((or (not (qir-temp-p (car pending))) (qir-get (cdar pending) marked))
         (opt-mark-live (cdr pending) definitions marked (- fuel 1)))
        (t (let ((number (cdar pending)))
             (opt-mark-live (append (qir-get number definitions) (cdr pending)) definitions
                               (qir-put number t marked) (- fuel 1))))))

(defun opt-live-phis (phis marked)
  (cond ((atom phis) nil)
        ((qir-get (cdr (qir-phi-dest (car phis))) marked)
         (cons (car phis) (opt-live-phis (cdr phis) marked)))
        (t (opt-live-phis (cdr phis) marked))))

(defun opt-live-insts (insts marked)
  (if (atom insts)
      nil
    (let* ((inst (car insts))
           (dest (qir-inst-dest inst))
           (kept (and dest (qir-get (cdr dest) marked)))
           (rest (opt-live-insts (cdr insts) marked)))
      (cond (kept (cons inst rest))
            ((opt-pure-op-p (qir-inst-op inst)) rest)
            (t (cons (cons nil (cdr inst)) rest))))))

(defun opt-live-blocks (blocks marked)
  (if (atom blocks)
      nil
    (let ((block (car blocks)))
      (cons (list (qir-block-label block) (opt-live-phis (qir-block-phis block) marked)
                  (opt-live-insts (qir-block-insts block) marked) (qir-block-jump block))
            (opt-live-blocks (cdr blocks) marked)))))

(defun opt-dce (blocks)
  (mv-let (definitions roots edges)
    (opt-dce-blocks blocks nil nil 0)
    (mv-let (complete marked)
      (opt-mark-live roots definitions nil (+ 1 (len roots) edges))
      (if complete (opt-live-blocks blocks marked) blocks))))

; Redirecting an edge updates both the terminator and the successor's phis.
(defun opt-new-edge-args (labels operand args)
  (cond ((atom labels) args)
        ((assoc-equal (car labels) args) (opt-new-edge-args (cdr labels) operand args))
        (t (opt-new-edge-args (cdr labels) operand (cons (cons (car labels) operand) args)))))

(defun opt-relabel-phis (phis from labels)
  (if (atom phis)
      nil
    (let* ((phi (car phis))
           (args (qir-phi-args phi))
           (operand (qir-phi-arg phi from)))
      (cons (list (qir-phi-dest phi)
                  (opt-new-edge-args labels operand (remove-assoc-equal from args)))
            (opt-relabel-phis (cdr phis) from labels)))))

(defun opt-set-phis (label from labels bmap)
  (let ((block (qir-get label bmap)))
    (qir-put label
             (list label (opt-relabel-phis (qir-block-phis block) from labels)
                   (qir-block-insts block) (qir-block-jump block))
             bmap)))

(defun opt-pred-union (labels preds)
  (cond ((atom labels) preds)
        ((member-equal (car labels) preds) (opt-pred-union (cdr labels) preds))
        (t (opt-pred-union (cdr labels) (cons (car labels) preds)))))

(defun opt-relabel-preds (succs from labels bmap preds)
  (if (atom succs)
      (mv bmap preds)
    (let* ((label (car succs))
           (bmap (opt-set-phis label from labels bmap))
           (incoming (opt-pred-union labels (remove-equal from (qir-get label preds)))))
      (opt-relabel-preds (cdr succs) from labels bmap (qir-put label incoming preds)))))

(defun opt-phi-copies (phis pred)
  (if (atom phis)
      nil
    (cons (list (qir-phi-dest (car phis)) :copy (qir-phi-arg (car phis) pred))
          (opt-phi-copies (cdr phis) pred))))

(defun opt-merge-chain (label bmap preds fuel)
  (declare (xargs :measure (nfix fuel)
                  :hints (("Goal" :in-theory (disable qir-get opt-relabel-preds)))))
  (let* ((block (qir-get label bmap))
         (jump (qir-block-jump block))
         (target (cadr jump)))
    (if (and (not (zp fuel)) (eq (car jump) :jmp) (not (equal label target))
             (equal (qir-get target preds) (list label)))
        (let* ((next (qir-get target bmap))
               (insts (append (qir-block-insts block) (opt-phi-copies (qir-block-phis next) label)
                               (qir-block-insts next)))
               (merged (list label (qir-block-phis block) insts (qir-block-jump next)))
               (bmap (qir-put target nil (qir-put label merged bmap)))
               (preds (qir-put target nil preds)))
          (mv-let (bmap preds)
            (opt-relabel-preds (qir-block-succs next) target (list label) bmap preds)
            (opt-merge-chain label bmap preds (- fuel 1))))
      (mv bmap preds))))

(defun opt-merge-blocks (labels bmap preds fuel)
  (if (atom labels)
      (mv bmap preds)
    (mv-let (bmap preds)
      (opt-merge-chain (car labels) bmap preds fuel)
      (opt-merge-blocks (cdr labels) bmap preds fuel))))

(defun opt-empty-arm-target (arm pred bmap preds)
  (let* ((block (qir-get arm bmap))
         (jump (qir-block-jump block)))
    (and (eq (car jump) :jmp) (equal (qir-get arm preds) (list pred))
         (not (qir-block-phis block)) (not (qir-block-insts block))
         (cadr jump))))

(defun opt-select-paths (label jump bmap preds)
  (let* ((yes (caddr jump))
         (no (cadddr jump))
         (yes-join (opt-empty-arm-target yes label bmap preds))
         (no-join (opt-empty-arm-target no label bmap preds)))
    (cond ((equal yes-join no) (mv no yes label (list yes)))
          ((equal no-join yes) (mv yes label no (list no)))
          ((and yes-join (equal yes-join no-join)) (mv yes-join yes no (list yes no)))
          (t (mv nil nil nil nil)))))

(defun opt-drop-labels (labels map)
  (if (atom labels)
      map
    (opt-drop-labels (cdr labels) (qir-put (car labels) nil map))))

; A single phi reached through empty branches can be computed by a select.
(defun opt-convert-diamond (label bmap preds)
  (let* ((block (qir-get label bmap))
         (jump (qir-block-jump block)))
    (if (not (eq (car jump) :jnz))
        (mv bmap preds)
      (mv-let (join yes no arms)
        (opt-select-paths label jump bmap preds)
        (if (or (not join) (equal label join))
            (mv bmap preds)
          (let* ((next (qir-get join bmap))
                 (phis (qir-block-phis next))
                 (incoming (qir-get join preds)))
            (if (and (consp phis) (not (cdr phis)) (equal (len incoming) 2)
                     (member-equal yes incoming) (member-equal no incoming))
                (let* ((phi (car phis))
                       (inst (list (qir-phi-dest phi) :sel (cadr jump)
                                   (qir-phi-arg phi yes) (qir-phi-arg phi no)))
                       (first (list label (qir-block-phis block)
                                    (append (qir-block-insts block) (list inst)) (list :jmp join)))
                       (next (list join nil (qir-block-insts next) (qir-block-jump next))))
                  (mv (qir-put join next (qir-put label first (opt-drop-labels arms bmap)))
                      (qir-put join (list label) (opt-drop-labels arms preds))))
              (mv bmap preds))))))))

(defun opt-convert-diamonds (labels bmap preds)
  (if (atom labels)
      (mv bmap preds)
    (mv-let (bmap preds)
      (opt-convert-diamond (car labels) bmap preds)
      (opt-convert-diamonds (cdr labels) bmap preds))))

(defun opt-edge-args-equal-p (phis left right)
  (or (atom phis)
      (and (equal (qir-phi-arg (car phis) left) (qir-phi-arg (car phis) right))
           (opt-edge-args-equal-p (cdr phis) left right))))

(defun opt-redirectable-p (labels from target-preds phis)
  (or (atom labels)
      (and (or (not (member-equal (car labels) target-preds))
               (opt-edge-args-equal-p phis from (car labels)))
           (opt-redirectable-p (cdr labels) from target-preds phis))))

(defun opt-redirect-jump (jump from target)
  (case (car jump)
    (:jmp (if (equal (cadr jump) from) (list :jmp target) jump))
    (:jnz (let ((yes (if (equal (caddr jump) from) target (caddr jump)))
                (no (if (equal (cadddr jump) from) target (cadddr jump))))
            (if (equal yes no) (list :jmp yes) (list :jnz (cadr jump) yes no))))
    (otherwise jump)))

(defun opt-redirect (labels from target bmap)
  (if (atom labels)
      bmap
    (let* ((label (car labels))
           (block (qir-get label bmap))
           (jump (opt-redirect-jump (qir-block-jump block) from target)))
      (opt-redirect (cdr labels) from target
                       (qir-put label (list label (qir-block-phis block) (qir-block-insts block) jump)
                                bmap)))))

(defun opt-empty-blocks (labels bmap preds)
  (if (atom labels)
      bmap
    (let* ((label (car labels))
           (block (qir-get label bmap))
           (jump (qir-block-jump block))
           (target (cadr jump))
           (incoming (qir-get label preds)))
      (if (and (eq (car jump) :jmp) (not (equal label target))
               (not (qir-block-phis block)) (not (qir-block-insts block))
               (opt-redirectable-p incoming label (qir-get target preds)
                                     (qir-block-phis (qir-get target bmap))))
          (mv-let (bmap preds)
            (opt-relabel-preds (list target) label incoming
                                   (qir-put label nil (opt-redirect incoming label target bmap))
                                   (qir-put label nil preds))
            (opt-empty-blocks (cdr labels) bmap preds))
        (opt-empty-blocks (cdr labels) bmap preds)))))

(defun opt-block-labels (blocks)
  (if (atom blocks)
      nil
    (cons (qir-block-label (car blocks)) (opt-block-labels (cdr blocks)))))

(defun opt-ordered-blocks (labels bmap)
  (if (atom labels)
      nil
    (let ((block (qir-get (car labels) bmap)))
      (if block (cons block (opt-ordered-blocks (cdr labels) bmap))
        (opt-ordered-blocks (cdr labels) bmap)))))

(defun opt-compact (blocks)
  (let ((labels (opt-block-labels blocks)))
    (mv-let (bmap preds)
      (opt-merge-blocks labels (qir-block-map blocks nil) (qir-preds blocks) (len labels))
      (mv-let (bmap preds)
        (opt-convert-diamonds labels bmap preds)
        (opt-ordered-blocks labels (opt-empty-blocks (cdr labels) bmap preds))))))

(defun opt-one-block-p (blocks)
  (and (consp blocks) (not (cdr blocks))
       (not (qir-block-phis (car blocks))) (not (qir-block-succs (car blocks)))))

(defun opt-one-block (block)
  (let ((label (qir-block-label block)))
    (mv-let (insts aliases definitions global local epoch)
      (opt-number-insts (qir-block-insts block) label nil nil nil nil nil nil)
      (declare (ignore definitions global local epoch))
      (opt-dce (list (list label nil insts (opt-rewrite-jump (qir-block-jump block) aliases 1)))))))

(defun opt-flow-changed-p (before after)
  (if (or (atom before) (atom after))
      (not (equal before after))
    (or (not (equal (qir-block-label (car before)) (qir-block-label (car after))))
        (not (equal (qir-block-succs (car before)) (qir-block-succs (car after))))
        (opt-flow-changed-p (cdr before) (cdr after)))))

; ------------------------------------------------------------------
; Sinking and jump threading. A pure instruction whose result is read
; only in one successor S of its block B, of which B is S's only
; predecessor, moves to the start of S: it is then not computed on the
; paths that do not need it. A block B with no phis whose jump is
; (:jnz W X Y), and whose instructions are pure and read only in B, is
; threaded: for each predecessor P on whose edge to B the word W is
; known, either by P's own jump on W or by what P knows on entry, P goes
; instead to a copy of B, with new temporaries, that jumps straight to X
; or Y. What a block knows on entry is what its immediate dominator
; knows, with the test of its only predecessor's jump when that is a
; :jnz.

(defun thr-note (xs label kind uses)
  (cond ((atom xs) uses)
        ((qir-temp-p (car xs))
         (thr-note (cdr xs) label kind
                   (qir-put (cdar xs) (cons (cons label kind) (qir-get (cdar xs) uses)) uses)))
        (t (thr-note (cdr xs) label kind uses))))

(defun thr-insts-uses (insts label uses)
  (if (atom insts)
      uses
    (thr-insts-uses (cdr insts) label (thr-note (qir-inst-uses (car insts)) label :inst uses))))

(defun thr-phi-args-uses (args uses)
  (if (atom args)
      uses
    (thr-phi-args-uses (cdr args) (thr-note (list (cdar args)) (caar args) :phi uses))))

(defun thr-phis-uses (phis uses)
  (if (atom phis)
      uses
    (thr-phis-uses (cdr phis) (thr-phi-args-uses (qir-phi-args (car phis)) uses))))

; The map from each temporary to its uses, each (LABEL . KIND): KIND is
; :INST or :JUMP for a use in the block LABEL, :PHI for a use by a phi on
; the edge from the block LABEL.
(defun thr-uses (blocks uses)
  (if (atom blocks)
      uses
    (let ((block (car blocks)))
      (thr-uses (cdr blocks)
                (thr-note (qir-jump-uses (qir-block-jump block)) (qir-block-label block) :jump
                          (thr-insts-uses (qir-block-insts block) (qir-block-label block)
                                          (thr-phis-uses (qir-block-phis block) uses)))))))

; The one block in which every use in USES lies, when none is by a phi.
(defun thr-only-block (uses label)
  (cond ((atom uses) label)
        ((eq (cdar uses) :phi) nil)
        ((and label (not (equal (caar uses) label))) nil)
        (t (thr-only-block (cdr uses) (caar uses)))))

; Splits the instructions of the block LABEL into those kept and those
; that sink, each with its target, the last first.
(defun thr-sink-insts (insts label succs preds uses kept sunk)
  (if (atom insts)
      (mv kept sunk)
    (let* ((inst (car insts))
           (dest (qir-inst-dest inst))
           (target (and dest (opt-pure-op-p (qir-inst-op inst))
                        (thr-only-block (qir-get (cdr dest) uses) nil))))
      (if (and target (not (equal target label)) (member-equal target succs)
               (equal (qir-get target preds) (list label)))
          (thr-sink-insts (cdr insts) label succs preds uses kept (cons (cons target inst) sunk))
        (thr-sink-insts (cdr insts) label succs preds uses (cons inst kept) sunk)))))

(defun thr-sunk-for (sunk target)
  (cond ((atom sunk) nil)
        ((equal (caar sunk) target) (cons (cdar sunk) (thr-sunk-for (cdr sunk) target)))
        (t (thr-sunk-for (cdr sunk) target))))

(defun thr-prepend-sunk (succs sunk bmap)
  (if (atom succs)
      bmap
    (let* ((s (car succs))
           (moved (reverse (thr-sunk-for sunk s)))
           (block (qir-get s bmap)))
      (thr-prepend-sunk (cdr succs) sunk
                        (if (consp moved)
                            (qir-put s (list s (qir-block-phis block)
                                             (append moved (qir-block-insts block))
                                             (qir-block-jump block))
                                     bmap)
                          bmap)))))

(defun thr-sink-blocks (labels bmap preds uses changed)
  (if (atom labels)
      (mv bmap changed)
    (let* ((label (car labels))
           (block (qir-get label bmap))
           (succs (qir-block-succs block)))
      (mv-let (kept sunk)
        (thr-sink-insts (qir-block-insts block) label succs preds uses nil nil)
        (if (consp sunk)
            (thr-sink-blocks (cdr labels)
                             (thr-prepend-sunk succs sunk
                                               (qir-put label (list label (qir-block-phis block)
                                                                    (reverse kept)
                                                                    (qir-block-jump block))
                                                        bmap))
                             preds uses t)
          (thr-sink-blocks (cdr labels) bmap preds uses changed))))))

; Sinks until nothing moves, at most ROUNDS times. Gives the blocks with
; their predecessors, their map and their uses, which the last round has
; computed.
(defun thr-sink (blocks rounds)
  (declare (xargs :measure (nfix rounds)))
  (if (zp rounds)
      (mv blocks (qir-preds blocks) (qir-block-map blocks nil) (thr-uses blocks nil))
    (let ((labels (opt-block-labels blocks))
          (bmap0 (qir-block-map blocks nil))
          (preds0 (qir-preds blocks))
          (uses0 (thr-uses blocks nil)))
      (mv-let (bmap changed)
        (thr-sink-blocks labels bmap0 preds0 uses0 nil)
        (if changed
            (thr-sink (opt-ordered-blocks labels bmap) (- rounds 1))
          (mv blocks preds0 bmap0 uses0))))))

; What each block knows on entry: a map from the number of a word
; temporary to :NONZERO or :ZERO.
(defun thr-facts (labels bmap preds idom facts)
  (if (atom labels)
      facts
    (let* ((label (car labels))
           (up (qir-get label idom))
           (inherited (if (equal up label) nil (qir-get up facts)))
           (incoming (qir-get label preds))
           (jump (and (consp incoming) (atom (cdr incoming))
                      (qir-block-jump (qir-get (car incoming) bmap))))
           (known (if (and (eq (car jump) :jnz) (qir-temp-p (cadr jump)))
                      (qir-put (cdr (cadr jump))
                               (if (equal label (caddr jump)) :nonzero :zero) inherited)
                    inherited)))
      (thr-facts (cdr labels) bmap preds idom (qir-put label (or known :none) facts)))))

(defun thr-known (pred label w bmap facts)
  (let ((jump (qir-block-jump (qir-get pred bmap)))
        (known (qir-get pred facts)))
    (cond ((and (eq (car jump) :jnz) (equal (cadr jump) w))
           (if (equal label (caddr jump)) :nonzero :zero))
          ((and (consp known) (qir-temp-p w)) (qir-get (cdr w) known))
          (t nil))))

; Whether every instruction of INSTS is pure and read only in LABEL.
(defun thr-local-p (insts label uses)
  (or (atom insts)
      (let ((dest (qir-inst-dest (car insts))))
        (and dest (opt-pure-op-p (qir-inst-op (car insts)))
             (equal (thr-only-block (qir-get (cdr dest) uses) label) label)
             (thr-local-p (cdr insts) label uses)))))

; Copies INSTS with a new temporary for each definition.
(defun thr-copy-insts (insts renames temp acc)
  (if (atom insts)
      (mv (reverse acc) temp)
    (let* ((inst (car insts))
           (dest (qir-inst-dest inst))
           (new (cons (car dest) temp))
           (inst (opt-rewrite-inst inst renames 1)))
      (thr-copy-insts (cdr insts) (qir-put (cdr dest) new renames) (+ temp 1)
                      (cons (cons new (cdr inst)) acc)))))

(defun thr-retarget (jump from to)
  (case (car jump)
    (:jmp (if (equal (cadr jump) from) (list :jmp to) jump))
    (:jnz (list :jnz (cadr jump)
                (if (equal (caddr jump) from) to (caddr jump))
                (if (equal (cadddr jump) from) to (cadddr jump))))
    (otherwise jump)))

(defun thr-add-pred-args (phis from new)
  (if (atom phis)
      nil
    (cons (list (qir-phi-dest (car phis))
                (append (qir-phi-args (car phis))
                        (list (cons new (qir-phi-arg (car phis) from)))))
          (thr-add-pred-args (cdr phis) from new))))

; Threads the edges into the block LABEL from PREDS.
(defun thr-edges (preds label block bmap facts temp next added)
  (if (atom preds)
      (mv bmap temp next added)
    (let* ((pred (car preds))
           (jump (qir-block-jump block))
           (known (and (not (equal pred label))
                       (thr-known pred label (cadr jump) bmap facts))))
      (if known
          (mv-let (insts temp)
            (thr-copy-insts (qir-block-insts block) nil temp nil)
            (let* ((target (if (eq known :nonzero) (caddr jump) (cadddr jump)))
                   (target-block (qir-get target bmap))
                   (pred-block (qir-get pred bmap))
                   (bmap (qir-put pred (list pred (qir-block-phis pred-block)
                                             (qir-block-insts pred-block)
                                             (thr-retarget (qir-block-jump pred-block) label next))
                                  bmap))
                   (bmap (qir-put target (list target
                                               (thr-add-pred-args (qir-block-phis target-block)
                                                                  label next)
                                               (qir-block-insts target-block)
                                               (qir-block-jump target-block))
                                  bmap)))
              (thr-edges (cdr preds) label block
                         (qir-put next (list next nil insts (list :jmp target)) bmap)
                         facts temp (+ next 1) (cons next added))))
        (thr-edges (cdr preds) label block bmap facts temp next added)))))

(defun thr-blocks (labels bmap preds uses facts temp next added)
  (if (atom labels)
      (mv bmap added)
    (let* ((label (car labels))
           (block (qir-get label bmap))
           (jump (qir-block-jump block)))
      (if (and (eq (car jump) :jnz)
               (qir-temp-p (cadr jump))
               (null (qir-block-phis block))
               (< (len (qir-block-insts block)) 8)
               (thr-local-p (qir-block-insts block) label uses))
          (mv-let (bmap temp next added)
            (thr-edges (qir-get label preds) label block bmap facts temp next added)
            (thr-blocks (cdr labels) bmap preds uses facts temp next added))
        (thr-blocks (cdr labels) bmap preds uses facts temp next added)))))

; Threading. Gives the blocks and, when threading left the blocks as
; sinking gave them, the maps it computed of them: (RPO PREDS BMAP IDOMS),
; else NIL.
(defun opt-thread-cfg (blocks)
  (mv-let (blocks preds bmap uses)
    (thr-sink blocks 4)
    (let* ((labels (opt-block-labels blocks))
           (rpo (qir-rpo blocks))
           (idoms (qir-idoms-of rpo preds))
           (facts (thr-facts rpo bmap preds idoms nil))
           (fn (list :fn "" nil blocks)))
      (mv-let (threaded added)
        (thr-blocks (cdr labels) bmap preds uses facts
                    (qir-next-temp fn) (qir-next-label fn) nil)
        (if (consp added)
            (mv (opt-prune (opt-ordered-blocks (append labels (reverse added)) threaded)) nil)
          (mv blocks (list rpo preds bmap idoms)))))))

(defun opt-thread (blocks)
  (mv-let (result cfg)
    (opt-thread-cfg blocks)
    (declare (ignore cfg))
    result))

; A change to edges or phi operands can reveal values in another round.
; A round that only combines computations has already visited their uses.
; CFG is NIL or the maps of BLOCKS that the last threading computed;
; gives the blocks with such maps of them, or NIL.
(defun opt-rounds-cfg (blocks aliases-fuel rounds cfg)
  (declare (xargs :measure (nfix rounds)
                  :hints (("Goal" :in-theory (disable opt-number opt-number-cfg opt-prune
                                                       opt-trivial-phis
                                                       opt-dce opt-compact opt-flow-changed-p
                                                       opt-one-block-p opt-thread-cfg)))))
  (cond ((zp rounds) (mv blocks cfg))
        ((opt-one-block-p blocks) (mv (opt-one-block (car blocks)) nil))
        (t (let ((reachable (opt-prune
                             (if cfg
                                 (opt-number-cfg blocks (car cfg) (cadr cfg) (caddr cfg)
                                                    (cadddr cfg))
                               (opt-number blocks)))))
             (mv-let (simple phis-removed)
               (opt-trivial-phis reachable aliases-fuel)
               (mv-let (compact ccfg)
                 (opt-thread-cfg (opt-compact (opt-dce simple)))
                 (if (or phis-removed (opt-flow-changed-p blocks compact))
                     (opt-rounds-cfg compact aliases-fuel (- rounds 1) ccfg)
                   (mv compact ccfg))))))))

(defun opt-rounds (blocks aliases-fuel rounds)
  (mv-let (result cfg)
    (opt-rounds-cfg blocks aliases-fuel rounds nil)
    (declare (ignore cfg))
    result))

(defun opt-phi-count (blocks count)
  (if (atom blocks)
      count
    (opt-phi-count (cdr blocks) (+ count (len (qir-block-phis (car blocks)))))))

; ------------------------------------------------------------------
; Loop-invariant code motion. A natural loop is the header H of a back
; edge, an edge to H from a block that H dominates, and every block that
; reaches such a block without passing H. When H has one predecessor P
; outside its loop, and P ends with (:jmp H), P is the preheader, and a
; pure instruction of the loop whose operands are all defined outside it
; (or by instructions already moved) moves to the end of P, in order.
; Its definition then still dominates every use, and it is computed
; once in place of once each time round. Loops are taken innermost
; first, so that what leaves an inner loop can leave an outer one too.
;
; A load moves only when computing it in the preheader cannot fault
; where the loop would not have: either it is in the header, which runs
; whenever the preheader does, after nothing in the header that could
; stop, call or fault; or it reads the header of an object, at the
; offset -2 from a base (:sel C X 34) whose C is (:ceq (:and X 7) 2), so
; that the base is X when X has a header and NIL otherwise (expand.lisp
; builds such bases). When
; the loop contains an instruction that may collect, a moved value must
; mean the same after a collection: a data temporary, which P6 keeps; a
; load of a word, as the fields that P4 and rt-qir.lisp load into word
; temporaries (headers, bytes of strings, digits) hold no references and
; never change; or a word operation that OPT-STABLE-INST-P accepts.

(defun licm-set-all (xs set)
  (if (atom xs)
      set
    (licm-set-all (cdr xs) (if (qir-temp-p (car xs)) (qir-put (cdar xs) t set) set))))

(defun licm-inst-dests (insts acc)
  (cond ((atom insts) acc)
        ((qir-inst-dest (car insts))
         (licm-inst-dests (cdr insts) (cons (qir-inst-dest (car insts)) acc)))
        (t (licm-inst-dests (cdr insts) acc))))

; The temporaries defined in the blocks LABELS.
(defun licm-defs (labels bmap set)
  (if (atom labels)
      set
    (let ((block (qir-get (car labels) bmap)))
      (licm-defs (cdr labels) bmap
                 (licm-set-all (qir-phi-dests (qir-block-phis block))
                               (licm-set-all (licm-inst-dests (qir-block-insts block) nil)
                                             set))))))

(defun licm-insts-collect-p (insts)
  (and (consp insts)
       (or (qir-inst-may-collect-p (car insts))
           (licm-insts-collect-p (cdr insts)))))

(defun licm-collects-p (labels bmap)
  (and (consp labels)
       (or (licm-insts-collect-p (qir-block-insts (qir-get (car labels) bmap)))
           (licm-collects-p (cdr labels) bmap))))

(defun licm-outside-p (xs defs)
  (or (atom xs)
      (and (not (and (qir-temp-p (car xs)) (qir-get (cdar xs) defs)))
           (licm-outside-p (cdr xs) defs))))

(defun licm-def (x definitions)
  (and (qir-temp-p x) (qir-get (cdr x) definitions)))

; Whether INST is (OP A B) or (OP B A) for the operation OP, the operand
; A and the constant word B.
(defun licm-op-with-p (inst op a b)
  (and (eq (qir-inst-op inst) op)
       (or (and (equal (caddr inst) a) (equal (opt-constant-word (cadddr inst)) b))
           (and (equal (cadddr inst) a) (equal (opt-constant-word (caddr inst)) b)))))

; Whether the load INST reads the header of a base (:sel C X 34) whose C
; is (:ceq (:and X 7) 2).
(defun licm-header-load-p (inst definitions)
  (let* ((base (licm-def (caddr inst) definitions))
         (x (caddr (cdr base)))
         (c (licm-def (caddr base) definitions))
         (c-and (and c (licm-def (if (qir-const-p (caddr c)) (cadddr c) (caddr c))
                                 definitions))))
    (and (equal (opt-constant-word (cadddr inst)) #xFFFFFFFFFFFFFFFE)
         base (eq (qir-inst-op base) :sel)
         (equal (car (cddddr base)) '(:k . 34))
         (qir-dtemp-p x)
         c (licm-op-with-p c :ceq (if (qir-const-p (caddr c)) (cadddr c) (caddr c)) 2)
         c-and (licm-op-with-p c-and :and x 7))))

; CLEAN is T while INST is in the header after only instructions that
; moved or cannot stop, call or fault.
(defun licm-movable-p (inst defs collects definitions clean)
  (let ((op (qir-inst-op inst))
        (dest (qir-inst-dest inst)))
    (and dest
         (opt-pure-op-p op)
         (licm-outside-p (qir-inst-uses inst) defs)
         (if (member-eq op '(:ld :ldb))
             (and (or clean (licm-header-load-p inst definitions))
                  (or (not collects) (qir-wtemp-p dest)))
           (or (not collects) (qir-dtemp-p dest) (opt-stable-inst-p inst))))))

; Splits INSTS into those kept and those moved, both the last first, and
; takes the moved ones' temporaries out of DEFS. CLEAN is as for
; LICM-MOVABLE-P: an instruction that stays and is not a pure operation
; on words, a selection or a copy ends it.
(defun licm-insts (insts defs collects definitions clean kept moved)
  (if (atom insts)
      (mv kept moved defs)
    (let ((inst (car insts)))
      (if (licm-movable-p inst defs collects definitions clean)
          (licm-insts (cdr insts) (qir-put (cdr (qir-inst-dest inst)) nil defs)
                      collects definitions clean kept (cons inst moved))
        (licm-insts (cdr insts) defs collects definitions
                    (and clean (or (qir-word-op-p (qir-inst-op inst))
                                   (member-eq (qir-inst-op inst) '(:sel :copy))))
                    (cons inst kept) moved)))))

; LABELS are the blocks of the loop in reverse post-order, the header
; first; CLEAN is T for the header only.
(defun licm-blocks (labels bmap defs collects definitions clean moved)
  (if (atom labels)
      (mv bmap moved)
    (let ((block (qir-get (car labels) bmap)))
      (mv-let (kept moved defs)
        (licm-insts (qir-block-insts block) defs collects definitions clean nil moved)
        (licm-blocks (cdr labels)
                     (qir-put (car labels)
                              (list (car labels) (qir-block-phis block) (reverse kept)
                                    (qir-block-jump block))
                              bmap)
                     defs collects definitions nil moved)))))

; The blocks of the loop of header H: H and every block that reaches one
; of WORK without passing H.
(defun licm-body (work body preds fuel)
  (declare (xargs :measure (nfix fuel)))
  (cond ((or (zp fuel) (atom work)) body)
        ((qir-get (car work) body) (licm-body (cdr work) body preds (- fuel 1)))
        (t (licm-body (append (qir-get (car work) preds) (cdr work))
                      (qir-put (car work) t body) preds (- fuel 1)))))

(defun licm-in (labels set)
  (cond ((atom labels) nil)
        ((qir-get (car labels) set) (cons (car labels) (licm-in (cdr labels) set)))
        (t (licm-in (cdr labels) set))))

(defun licm-out (labels set)
  (cond ((atom labels) nil)
        ((qir-get (car labels) set) (licm-out (cdr labels) set))
        (t (cons (car labels) (licm-out (cdr labels) set)))))

; The predecessors of H that H dominates: the sources of its back edges.
(defun licm-latches (preds h idom fuel)
  (cond ((atom preds) nil)
        ((qir-dominates-p h (car preds) idom fuel)
         (cons (car preds) (licm-latches (cdr preds) h idom fuel)))
        (t (licm-latches (cdr preds) h idom fuel))))

; Moves what it can out of the loop of each header of HEADERS.
(defun licm-loops (headers rpo bmap preds idom definitions fuel)
  (if (atom headers)
      bmap
    (let* ((h (car headers))
           (latches (licm-latches (qir-get h preds) h idom fuel))
           (body (licm-body latches (qir-put h t nil) preds fuel))
           (outside (licm-out (qir-get h preds) body))
           (pre (car outside))
           (pre-block (qir-get pre bmap))
           (labels (licm-in rpo body)))
      (if (and (consp latches) (consp outside) (atom (cdr outside))
               (equal (qir-block-jump pre-block) (list :jmp h)))
          (mv-let (bmap moved)
            (licm-blocks labels bmap (licm-defs labels bmap nil)
                         (licm-collects-p labels bmap) definitions t nil)
            (licm-loops (cdr headers) rpo
                        (if (consp moved)
                            (qir-put pre (list pre (qir-block-phis pre-block)
                                               (append (qir-block-insts pre-block) (reverse moved))
                                               (qir-block-jump pre-block))
                                     bmap)
                          bmap)
                        preds idom definitions fuel))
        (licm-loops (cdr headers) rpo bmap preds idom definitions fuel)))))

(defun licm-insts-defs (insts map)
  (cond ((atom insts) map)
        ((qir-inst-dest (car insts))
         (licm-insts-defs (cdr insts) (qir-put (cdr (qir-inst-dest (car insts))) (car insts) map)))
        (t (licm-insts-defs (cdr insts) map))))

(defun licm-definitions (blocks map)
  (if (atom blocks)
      map
    (licm-definitions (cdr blocks) (licm-insts-defs (qir-block-insts (car blocks)) map))))

(defun licm-headers (labels preds idom fuel)
  (cond ((atom labels) nil)
        ((consp (licm-latches (qir-get (car labels) preds) (car labels) idom fuel))
         (cons (car labels) (licm-headers (cdr labels) preds idom fuel)))
        (t (licm-headers (cdr labels) preds idom fuel))))

; CFG is NIL or the maps of BLOCKS, (RPO PREDS BMAP IDOMS).
(defun opt-licm-cfg (blocks cfg)
  (let* ((rpo (if cfg (car cfg) (qir-rpo blocks)))
         (preds (if cfg (cadr cfg) (qir-preds blocks)))
         (idom (if cfg (cadddr cfg) (qir-idoms-of rpo preds)))
         (fuel (* 4 (+ 1 (len blocks) (qir-count-succs blocks 0))))
         (headers (reverse (licm-headers rpo preds idom fuel))))
    (if (atom headers)
        blocks
      (opt-ordered-blocks (opt-block-labels blocks)
                             (licm-loops headers rpo
                                         (if cfg (caddr cfg) (qir-block-map blocks nil))
                                         preds idom
                                         (licm-definitions blocks nil) fuel)))))

(defun opt-licm (blocks)
  (opt-licm-cfg blocks nil))

(defun opt-function (fn)
  (let ((blocks (qir-fn-blocks fn)))
    (if (atom blocks)
        fn
      (mv-let (result cfg)
        (opt-rounds-cfg blocks (opt-phi-count blocks 1) 3 nil)
        (list :fn (qir-fn-name fn) (qir-fn-params fn) (opt-licm-cfg result cfg))))))

(defun opt-program (fns)
  (if (atom fns)
      nil
    (cons (opt-function (car fns)) (opt-program (cdr fns)))))
