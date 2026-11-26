(in-package "BOYMOO-PROOFS")

(include-book "../foundations/interfaces")

(logic)
(set-verify-guards-eagerness 0)

; The Linux wrappers precede the runtime. The generated functions follow
; the runtime and do not enter the layout of these instruction ranges.
(defconst *allocation-runtime-items*
  (append (boymoo-compiler::linux-system-code)
          (boymoo-compiler::runtime-code)))

(defconst *allocation-runtime-labels*
  (mv-let (size labels reversed)
    (boymoo-compiler::a64-layout *allocation-runtime-items* 0 nil nil)
    (declare (ignore size reversed))
    labels))

(defun allocation-label-offset (label)
  (boymoo-compiler::a64-offset label *allocation-runtime-labels*))

(defconst *allocation-runtime-code-size*
  (mv-let (size labels reversed)
    (boymoo-compiler::a64-layout *allocation-runtime-items* 0 nil nil)
    (declare (ignore labels reversed))
    size))

(defun allocation-code-address (label origin)
  (+ origin (allocation-label-offset label)))

(defun allocation-code-origin-p (origin)
  (and (natp origin)
       (<= (+ origin *allocation-runtime-code-size*) (expt 2 64))))

(defun allocation-extract-instructions (items pc start end labels)
  (if (or (atom items) (<= end pc))
      nil
    (let* ((item (car items))
           (size (boymoo-compiler::a64-image-item-size item))
           (rest (allocation-extract-instructions
                  (cdr items) (+ pc size) start end labels)))
      (if (and (<= start pc) (equal size 4))
          (cons (proof-decode (boymoo-compiler::a64-word item pc labels)) rest)
        rest))))

(defun allocation-instructions (label count)
  (let ((start (allocation-label-offset label)))
    (allocation-extract-instructions
     *allocation-runtime-items* 0 start (+ start (* 4 count))
     *allocation-runtime-labels*)))

(defconst *allocation-grow-code* (allocation-instructions "rt:grow" 14))
(defconst *allocation-header-code* (allocation-instructions "rt:alloc" 9))
(defconst *allocation-cells-code* (allocation-instructions "rt:alloc-cells" 10))
(defconst *allocation-cons-code* (allocation-instructions "prim:COMMON-LISP::CONS" 24))
(defconst *allocation-large-string-code* (allocation-instructions "rt:new-large-string" 38))
(defconst *allocation-map-code* (allocation-instructions "sys:map" 11))

(assert-event
 (and (equal (len *allocation-grow-code*) 14)
      (equal (len *allocation-header-code*) 9)
      (equal (len *allocation-cells-code*) 10)
      (equal (len *allocation-cons-code*) 24)
      (equal (len *allocation-large-string-code*) 38)
      (equal (len *allocation-map-code*) 11)
      (not (member-equal :undefined *allocation-grow-code*))
      (not (member-equal :undefined *allocation-header-code*))
      (not (member-equal :undefined *allocation-cells-code*))
      (not (member-equal :undefined *allocation-cons-code*))
      (not (member-equal :undefined *allocation-large-string-code*))
      (not (member-equal :undefined *allocation-map-code*))))
