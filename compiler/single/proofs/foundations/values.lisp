(in-package "BOYMOO-PROOFS")

(include-book "machine")

(logic)
(set-verify-guards-eagerness 0)

(defconst *proof-nil* 34)
(defconst *proof-t* 58)

(defun proof-immediate-integer-p (value)
  (and (integerp value)
       (<= (- (expt 2 62)) value)
       (< value (expt 2 62))))

(defun proof-integer-word (value)
  (boymoo-model::a64-unsigned 64 (+ 1 (* 2 (ifix value)))))

(defun proof-character-word (value)
  (+ 4 (* 8 (char-code value))))

(defun proof-word-tag (word)
  (boymoo-model::a64-unsigned 3 word))

(defun proof-pointer-address (word base)
  (boymoo-model::a64-unsigned 64 (+ base (- word (proof-word-tag word)))))

; The object map lists (address zone kind rank) records. The address is
; also the key. Static, active and external objects have separate zones.
(defun proof-object (address zone kind rank) (list address zone kind rank))
(defun proof-object-address (object) (car object))
(defun proof-object-zone (object) (cadr object))
(defun proof-object-kind (object) (caddr object))
(defun proof-object-rank (object) (cadddr object))

(defun proof-object-word (object base)
  (boymoo-model::a64-unsigned
   64 (+ (- (proof-object-address object) base)
         (if (eq (proof-object-kind object) :header) 2 0))))

(defun proof-header-type (header)
  (boymoo-model::a64-unsigned 8 header))

(defun proof-header-size (header)
  (ash header -8))

(defun proof-value-view (value) (cons :value value))
(defun proof-value-view-p (view) (eq (car view) :value))
(defun proof-view-value (view) (cdr view))

(defun proof-limb-magnitude (count address machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      0
    (+ (proof-load-word address machine)
       (* (expt 2 32) (proof-limb-magnitude (1- count) (+ 8 address) machine)))))

(defun proof-limbs-p (count address machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      t
    (let ((limb (proof-load-word address machine)))
      (and (unsigned-byte-p 32 limb)
           (or (< 1 count) (posp limb))
           (proof-limbs-p (1- count) (+ 8 address) machine)))))

; A normalized integer view may be in scratch storage. A published
; type 3 object additionally requires a non-immediate value.
(defun proof-integer-view (address machine)
  (let* ((header (proof-load-word address machine))
         (size (proof-header-size header))
         (sign (proof-load-word (+ 8 address) machine))
         (count (1- (ash size -3))))
    (if (and (equal (proof-header-type header) 3)
             (<= 8 size)
             (equal (mod size 8) 0)
             (proof-span-p address (+ 8 size))
             (or (equal sign 0) (and (equal sign 1) (posp count)))
             (proof-limbs-p count (+ 16 address) machine))
        (let ((magnitude (proof-limb-magnitude count (+ 16 address) machine)))
          (proof-value-view (if (equal sign 0) magnitude (- magnitude))))
      nil)))

; The package list is ordered by package number. Each record has its
; name, an ACL2 witness in its home package, visibility and imports.
(defun proof-package (name witness visible imports)
  (list name witness visible imports))

(defun proof-package-name (package) (car package))
(defun proof-package-witness (package) (cadr package))
(defun proof-package-visible (package) (caddr package))
(defun proof-package-imports (package) (cadddr package))

(defun proof-symbol-value (name-view number-view packages)
  (let ((name (proof-view-value name-view))
        (number (proof-view-value number-view)))
    (if (and (proof-value-view-p name-view)
             (proof-value-view-p number-view)
             (stringp name) (natp number) (proof-immediate-integer-p number)
             (< number (len packages)))
        (let* ((package (nth number packages))
               (witness (proof-package-witness package)))
          (and (symbolp witness)
               (let ((symbol (acl2::intern-in-package-of-symbol name witness)))
                 (and (symbolp symbol)
                      (equal (symbol-name symbol) name)
                      (equal (acl2::symbol-package-name symbol)
                             (proof-package-name package))
                      (proof-value-view symbol)))))
      nil)))

(defun proof-cons-value (first second)
  (and first second
       (if (and (proof-value-view-p first) (proof-value-view-p second))
           (proof-value-view (cons (proof-view-value first)
                                   (proof-view-value second)))
         (list :pair first second))))

(defun proof-rational-value (first second)
  (let ((numerator (proof-view-value first))
        (denominator (proof-view-value second)))
    (and (proof-value-view-p first)
         (proof-value-view-p second)
         (integerp numerator) (integerp denominator)
         (< 1 denominator)
         (let ((value (/ numerator denominator)))
           (and (equal (acl2::numerator value) numerator)
                (equal (acl2::denominator value) denominator)
                (proof-value-view value))))))

(defun proof-complex-value (first second)
  (let ((real (proof-view-value first))
        (imaginary (proof-view-value second)))
    (and (proof-value-view-p first)
         (proof-value-view-p second)
         (rationalp real) (rationalp imaginary)
         (not (equal imaginary 0))
         (proof-value-view (complex real imaginary)))))

; Word cases descend in rank. Slot cases also descend in the number
; of sibling entries, without charging them against the rank.
(defun proof-view-step (kind input count depth base objects packages machine)
  (declare (xargs :measure
                  (make-ord 1 (1+ (nfix depth))
                            (if (eq kind :slots) (1+ (nfix count)) 0))))
  (if (eq kind :slots)
      (if (zp count)
          (list :slots)
        (let ((first (proof-view-step :word (proof-load-word input machine)
                                      0 depth base objects packages machine))
              (rest (proof-view-step :slots (+ 8 input) (1- count) depth
                                     base objects packages machine)))
          (and first rest (list* :slots first (cdr rest)))))
    (let ((tag (proof-word-tag input)))
      (cond
       ((not (unsigned-byte-p 64 input)) nil)
       ((oddp input)
        (proof-value-view (ash (boymoo-model::a64-signed 64 input) -1)))
       ((equal tag 4)
        (and (unsigned-byte-p 8 (ash input -3))
             (proof-value-view (code-char (ash input -3)))))
       ((and (member-equal tag '(0 2)) (posp depth))
        (let* ((address (proof-pointer-address input base))
               (object (assoc-equal address objects))
               (rank (proof-object-rank object)))
          (and object
               (natp rank)
               (< rank depth)
               (if (equal tag 0)
                   (and (eq (proof-object-kind object) :cons)
                        (proof-span-p address 16)
                        (proof-cons-value
                         (proof-view-step :word (proof-load-word address machine)
                                          0 rank base objects packages machine)
                         (proof-view-step :word (proof-load-word (+ 8 address) machine)
                                          0 rank base objects packages machine)))
                 (and (eq (proof-object-kind object) :header)
                      (let* ((header (proof-load-word address machine))
                             (size (proof-header-size header))
                             (type (proof-header-type header))
                             (payload (+ address 8)))
                        (and (proof-span-p address (+ 8 size))
                             (case type
                               (1 (proof-value-view (proof-load-string size payload machine)))
                               (3 (let ((view (proof-integer-view address machine)))
                                    (and view
                                         (not (proof-immediate-integer-p
                                               (proof-view-value view)))
                                         view)))
                               ((2 4 5)
                                (and (equal size 16)
                                     (let ((first (proof-view-step
                                                   :word (proof-load-word payload machine)
                                                   0 rank base objects packages machine))
                                           (second (proof-view-step
                                                    :word (proof-load-word (+ payload 8) machine)
                                                    0 rank base objects packages machine)))
                                       (case type
                                         (2 (proof-symbol-value first second packages))
                                         (4 (proof-rational-value first second))
                                         (otherwise (proof-complex-value first second))))))
                               (6 (and (equal (mod size 8) 0)
                                       (let ((fields (proof-view-step
                                                      :slots payload (ash size -3) rank
                                                      base objects packages machine)))
                                         (and fields (cons :vector (cdr fields))))))
                               (otherwise nil)))))))))
       (t nil)))))

(defun proof-view (word base objects packages machine)
  (let* ((address (proof-pointer-address word base))
         (object (assoc-equal address objects)))
    (proof-view-step :word word 0 (1+ (nfix (proof-object-rank object)))
                     base objects packages machine)))

(defun proof-value-p (word value base objects packages machine)
  (equal (proof-view word base objects packages machine)
         (proof-value-view value)))

(defun proof-stack-views (count address base objects packages machine)
  (declare (xargs :measure (nfix count)))
  (if (zp count)
      (list :slots)
    (let ((first (proof-view (proof-load-word address machine)
                             base objects packages machine))
          (rest (proof-stack-views (1- count) (+ 8 address)
                                   base objects packages machine)))
      (and first rest (list* :slots first (cdr rest))))))
