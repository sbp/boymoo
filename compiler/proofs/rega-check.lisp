(in-package "BOYMOO-COMPILER")

(include-book "../rega")

(logic)
(set-verify-guards-eagerness 0)

(defun rega-home-p (home nspill)
  (and (consp home)
       (case (car home)
         (:x (and (member-equal (cdr home) *rega-registers*) t))
         (:m (and (natp (cdr home)) (< (cdr home) nspill)))
         (otherwise nil))))

(defun rega-surviving-home-p (kind home)
  (case kind
    (:call (eq (car home) :m))
    (:rt (or (eq (car home) :m)
             (and (eq (car home) :x) (member-equal (cdr home) *rega-kept-registers*) t)))
    (otherwise t)))

; A definition can overwrite its own home. The other live values must
; survive both that write and any clobber of the instruction.
(defun rega-live-safe-p (live dest home kind homes nspill)
  (if (endp live)
      t
    (let ((place (ntab-get (car live) homes)))
      (and (or (equal (car live) dest)
               (and (rega-home-p place nspill) (not (equal home place))
                    (rega-surviving-home-p kind place)))
           (rega-live-safe-p (cdr live) dest home kind homes nspill)))))

(defun rega-operands-have-homes-p (operands homes nspill)
  (if (endp operands)
      t
    (let ((operand (car operands)))
      (and (or (qir-const-p operand)
               (and (qir-temp-p operand) (rega-home-p (ntab-get (cdr operand) homes) nspill)))
           (rega-operands-have-homes-p (cdr operands) homes nspill)))))

(defun rega-parameters-have-distinct-homes-p (params homes nspill used)
  (if (endp params)
      t
    (let ((place (ntab-get (cdar params) homes)))
      (and (qir-dtemp-p (car params)) (rega-home-p place nspill) (not (member-equal place used))
           (rega-parameters-have-distinct-homes-p (cdr params) homes nspill (cons place used))))))

(defun rega-instruction-safe-p (inst after homes nspill)
  (let* ((dest (mir-dest inst))
         (number (and dest (cdr dest)))
         (home (and dest (ntab-get number homes))))
    (and (or (not dest) (and (qir-temp-p dest) (rega-home-p home nspill)))
         (rega-operands-have-homes-p (mir-sources inst) homes nspill)
         (rega-live-safe-p after number home (car inst) homes nspill))))

(defun rega-check-instructions (reversed live homes nspill)
  (if (endp reversed)
      (mv t live)
    (let ((inst (car reversed)))
      (if (rega-instruction-safe-p inst live homes nspill)
          (rega-check-instructions (cdr reversed) (mir-inst-live inst live) homes nspill)
        (mv nil live)))))

(defun rega-successors-known-p (labels blocks)
  (if (endp labels)
      t
    (and (qir-get (car labels) blocks)
         (rega-successors-known-p (cdr labels) blocks))))

(defun rega-blocks-safe-p (blocks block-map live homes nspill)
  (if (endp blocks)
      t
    (let* ((block (car blocks))
           (term (caddr block)))
      (mv-let (safe entry-live)
        (rega-check-instructions (reverse-onto (cadr block) nil)
                                    (mir-block-end-live block live) homes nspill)
        (and safe (equal (ntab-get (car block) live) entry-live)
             (rega-successors-known-p (mir-term-successors term) block-map)
             (rega-operands-have-homes-p (mir-term-sources term) homes nspill)
             (rega-blocks-safe-p (cdr blocks) block-map live homes nspill))))))

; The supplied live-in sets must be a fixed point of the MIR transfer
; functions. Each live-in parameter is initialized by the caller.
(defun rega-validate (function homes nspill live)
  (let ((params (caddr function))
        (blocks (car (cddddr function))))
    (and (consp blocks) (natp nspill)
         (qir-labels-distinct-p blocks nil)
         (subsetp-equal (ntab-get (caar blocks) live) (mir-numbers params nil))
         (rega-parameters-have-distinct-homes-p params homes nspill nil)
         (rega-blocks-safe-p blocks (qir-block-map blocks nil) live homes nspill))))

(defun rega-allocation-valid-p (function allocation)
  (rega-validate function (car allocation) (cadr allocation) (caddr allocation)))

(defun rega-validated-program (functions)
  (if (endp functions)
      nil
    (let* ((function (car functions))
           (allocation (rega-allocation function)))
      (if (rega-allocation-valid-p function allocation)
          (cons (rega-apply function allocation) (rega-validated-program (cdr functions)))
        (compiler-error "Register assignment failed validation: ~x0." (cadr function))))))
