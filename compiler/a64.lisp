(in-package "BOYMOO-COMPILER")

(set-verify-guards-eagerness 0)

(defun low-bits (x width)
  (- x (ash (ash x (- width)) width)))

(defun reverse-onto (xs acc)
  (if (consp xs)
      (reverse-onto (cdr xs) (cons (car xs) acc))
    acc))

(defun compiler-error (message value)
  (hard-error 'compile-text message (list (cons #\0 value))))

(defun a64-unsigned (x width)
  (if (and (integerp x) (<= 0 x) (equal (ash x (- width)) 0))
      x
    (compiler-error "Unsigned assembly field out of range: ~x0." x)))

(defun a64-signed-scaled (x scale width)
  (let* ((n (ash x (- scale)))
         (sign (ash n (- 1 width))))
    (if (and (integerp x) (equal (ash n scale) x)
             (or (equal sign 0) (equal sign -1)))
        (low-bits n width)
      (compiler-error "Signed assembly field out of range: ~x0." x))))

(defun a64-reg (x shift)
  (ash (a64-unsigned x 5) shift))

(defun a64-rn-rd (rn rd)
  (+ (a64-reg rn 5) (a64-reg rd 0)))

(defun a64-rrr (base rd rn rm)
  (+ base (a64-reg rm 16) (a64-rn-rd rn rd)))

(defun a64-uimm (base rd rn imm scale)
  (let ((n (ash imm (- scale))))
    (+ base (a64-rn-rd rn rd)
       (ash (a64-unsigned
             (if (equal (ash n scale) imm) n
               (compiler-error "Unaligned assembly offset: ~x0." imm))
             12)
            10))))

(defun a64-wide (base rd imm shift)
  (+ base (a64-reg rd 0) (ash (a64-unsigned imm 16) 5)
     (case shift
       (0 0) (16 #x200000) (32 #x400000) (48 #x600000)
       (otherwise (compiler-error "Invalid move-wide shift: ~x0." shift)))))

(defun a64-pair (base rt rt2 rn off)
  (+ base (a64-rn-rd rn rt) (a64-reg rt2 10)
     (ash (a64-signed-scaled off 3 7) 15)))

(defun a64-condition (condition)
  (case condition
    (:eq 0) (:ne 1) (:hs 2) (:lo 3) (:mi 4) (:pl 5) (:vs 6) (:vc 7)
    (:hi 8) (:ls 9) (:ge 10) (:lt 11) (:gt 12) (:le 13) (:al 14)
    (otherwise (compiler-error "Unknown assembly condition: ~x0." condition))))

(defun a64-mask (base rd rn k)
  (if (and (integerp k) (< 0 k) (< k 64))
      (if (and (equal base #x92400000) (equal rd 31))
          (a64-rrr #x8a000000 31 rn 31)
        (+ base (a64-rn-rd rn rd) (ash (- k 1) 10)))
    (compiler-error "Invalid low-bit mask width: ~x0." k)))

(defun a64-shift (op rd rn n)
  (let* ((n (a64-unsigned n 6))
         (r (if (eq op :lsl) (low-bits (- n) 6) n))
         (s (if (eq op :lsl) (- 63 n) 63)))
    (+ (if (eq op :asr) #x93400000 #xd3400000)
       (ash r 16) (ash s 10) (a64-rn-rd rn rd))))

(defun a64-adr (base rd delta)
  (let ((bits (a64-signed-scaled delta 0 21)))
    (+ base (a64-reg rd 0) (ash (low-bits bits 2) 29)
       (ash (ash bits -2) 5))))

(defun table-string-less (a b i left)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      nil
    (let ((x (char a i))
          (y (char b i)))
      (if (equal x y)
          (table-string-less a b (+ i 1) (- left 1))
        (< (char-code x) (char-code y))))))

(defun table-text-less (a b)
  (let ((x (length a))
        (y (length b)))
    (if (equal x y)
        (table-string-less a b 0 x)
      (< x y))))

(defun table-key-kind (key)
  (cond ((stringp key) 0)
        ((consp key) 1)
        ((rationalp key) 2)
        ((characterp key) 3)
        ((symbolp key) 4)
        (t 5)))

(defun table-key-less (a b)
  (declare (xargs :measure (acl2-count a)))
  (let ((x (table-key-kind a))
        (y (table-key-kind b)))
    (cond ((not (equal x y)) (< x y))
          ((stringp a) (table-text-less a b))
          ((consp a) (if (equal (car a) (car b))
                        (table-key-less (cdr a) (cdr b))
                      (table-key-less (car a) (car b))))
          ((rationalp a) (< a b))
          ((characterp a) (< (char-code a) (char-code b)))
          ((symbolp a)
           (if (equal (symbol-name a) (symbol-name b))
               (table-text-less (symbol-package-name a) (symbol-package-name b))
             (table-text-less (symbol-name a) (symbol-name b))))
          ((equal (realpart a) (realpart b)) (< (imagpart a) (imagpart b)))
          (t (< (realpart a) (realpart b))))))

; Each bucket holds an AVL tree. A node stores its height and entry,
; followed by its left and right children.
(defun table-height (tree)
  (if tree (caar tree) 0))

(defun table-node (entry left right)
  (let ((a (table-height left))
        (b (table-height right)))
    (list* (cons (+ 1 (if (< a b) b a)) entry) left right)))

(defun table-rotate-left (entry left right)
  (table-node (cdar right) (table-node entry left (cadr right)) (cddr right)))

(defun table-rotate-right (entry left right)
  (table-node (cdar left) (cadr left) (table-node entry (cddr left) right)))

(defun table-balance (entry left right)
  (let ((a (table-height left))
        (b (table-height right)))
    (cond ((< (+ b 1) a)
           (table-rotate-right
            entry
            (if (< (table-height (cadr left)) (table-height (cddr left)))
                (table-rotate-left (cdar left) (cadr left) (cddr left))
              left)
            right))
          ((< (+ a 1) b)
           (table-rotate-left
            entry left
            (if (< (table-height (cddr right)) (table-height (cadr right)))
                (table-rotate-right (cdar right) (cadr right) (cddr right))
              right)))
          (t (table-node entry left right)))))

(defun table-tree-get (key tree)
  (if (atom tree)
      nil
    (let* ((entry (cdar tree))
           (other (car entry)))
      (cond ((equal key other) (cdr entry))
            ((table-key-less key other) (table-tree-get key (cadr tree)))
            (t (table-tree-get key (cddr tree)))))))

(defun table-tree-put (key value tree)
  (if (atom tree)
      (table-node (cons key value) nil nil)
    (let* ((entry (cdar tree))
           (other (car entry))
           (left (cadr tree))
           (right (cddr tree)))
      (cond ((equal key other) (table-node (cons key value) left right))
            ((table-key-less key other)
             (table-balance entry (table-tree-put key value left) right))
            (t (table-balance entry left (table-tree-put key value right)))))))

(defun table-get (key hash bits tree)
  (declare (xargs :measure (nfix bits)))
  (cond ((atom tree) nil)
        ((zp bits) (table-tree-get key tree))
        (t (table-get key (ash hash -1) (- bits 1)
                      (if (equal (low-bits hash 1) 0)
                          (car tree)
                        (cdr tree))))))

(defun table-put (key value hash bits tree)
  (declare (xargs :measure (nfix bits)))
  (cond ((zp bits) (table-tree-put key value tree))
        ((equal (low-bits hash 1) 0)
         (cons (table-put key value (ash hash -1) (- bits 1) (car tree))
               (cdr tree)))
        (t (cons (car tree)
                 (table-put key value (ash hash -1) (- bits 1) (cdr tree))))))

(defun hash-string (s i left hash)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      hash
    (hash-string s (+ 1 i) (- left 1)
                 (low-bits (+ (* 33 hash) (char-code (char s i))) 24))))

(defun label-hash (key)
  (cond ((stringp key) (hash-string key 0 (length key) 0))
        ((integerp key) (low-bits key 24))
        ((characterp key) (char-code key))
        ((symbolp key)
         (let ((name (symbol-name key)))
           (hash-string name 0 (length name) 13)))
        ((consp key)
         (low-bits (+ (* 65599 (label-hash (car key)))
                      (label-hash (cdr key))) 24))
        (t 0)))

(defun a64-offset (label labels)
  (or (table-get label (label-hash label) 16 labels)
      (compiler-error "Undefined assembly label: ~x0." label)))

(defun a64-word (item pc labels)
  (let ((a (cadr item)) (b (caddr item)) (c (cadddr item))
        (d (car (cddddr item))))
    (case (car item)
      (:movz (a64-wide #xd2800000 a b c))
      (:movk (a64-wide #xf2800000 a b c))
      (:movn (a64-wide #x92800000 a b c))
      (:mov (a64-rrr #xaa000000 a 31 b))
      (:mov-sp (+ #x91000000 (a64-rn-rd b a)))
      (:add (a64-uimm #x91000000 a b c 0))
      (:sub (a64-uimm #xd1000000 a b c 0))
      (:adds (a64-uimm #xb1000000 a b c 0))
      (:subs (a64-uimm #xf1000000 a b c 0))
      (:cmp (a64-uimm #xf1000000 31 a b 0))
      (:cmn (a64-uimm #xb1000000 31 a b 0))
      (:add-reg (a64-rrr (+ #x8b000000 (ash (a64-unsigned d 6) 10)) a b c))
      (:sub-reg (a64-rrr (+ #xcb000000 (ash (a64-unsigned d 6) 10)) a b c))
      (:adds-reg (a64-rrr (+ #xab000000 (ash (a64-unsigned d 6) 10)) a b c))
      (:subs-reg (a64-rrr (+ #xeb000000 (ash (a64-unsigned d 6) 10)) a b c))
      (:cmp-reg (a64-rrr #xeb000000 31 a b))
      (:neg (a64-rrr #xcb000000 a 31 b))
      (:and-reg (a64-rrr #x8a000000 a b c))
      (:orr-reg (a64-rrr #xaa000000 a b c))
      (:eor-reg (a64-rrr #xca000000 a b c))
      (:ands-reg (a64-rrr #xea000000 a b c))
      (:tst-reg (a64-rrr #xea000000 31 a b))
      (:mvn (a64-rrr #xaa200000 a 31 b))
      (:and-mask (a64-mask #x92400000 a b c))
      (:tst-mask (a64-mask #xf2400000 31 a b))
      ((:lsl :lsr :asr) (a64-shift (car item) a b c))
      (:lslv (a64-rrr #x9ac02000 a b c))
      (:lsrv (a64-rrr #x9ac02400 a b c))
      (:asrv (a64-rrr #x9ac02800 a b c))
      (:clz (+ #xdac01000 (a64-rn-rd b a)))
      (:mul (a64-rrr #x9b007c00 a b c))
      (:smulh (a64-rrr #x9b407c00 a b c))
      (:sdiv (a64-rrr #x9ac00c00 a b c))
      (:udiv (a64-rrr #x9ac00800 a b c))
      (:msub (a64-rrr (+ #x9b008000 (a64-reg d 10)) a b c))
      (:csel (a64-rrr (+ #x9a800000 (ash (a64-condition d) 12)) a b c))
      (:cset (if (eq b :al)
                 (a64-wide #xd2800000 a 1 0)
               (a64-rrr (+ #x9a800400 (ash (acl2::binary-logxor (a64-condition b) 1) 12))
                        a 31 31)))
      (:ldr (a64-uimm #xf9400000 a b c 3))
      (:str (a64-uimm #xf9000000 a b c 3))
      (:ldr-reg (a64-rrr #xf8606800 a b c))
      (:str-reg (a64-rrr #xf8206800 a b c))
      (:ldur (+ #xf8400000 (ash (a64-signed-scaled c 0 9) 12) (a64-rn-rd b a)))
      (:stur (+ #xf8000000 (ash (a64-signed-scaled c 0 9) 12) (a64-rn-rd b a)))
      (:ldurb (+ #x38400000 (ash (a64-signed-scaled c 0 9) 12) (a64-rn-rd b a)))
      (:ldrb (a64-uimm #x39400000 a b c 0))
      (:strb (a64-uimm #x39000000 a b c 0))
      (:ldrb-reg (a64-rrr #x38606800 a b c))
      (:strb-reg (a64-rrr #x38206800 a b c))
      (:ldp (a64-pair #xa9400000 a b c d))
      (:stp (a64-pair #xa9000000 a b c d))
      (:ldp-post (a64-pair #xa8c00000 a b c d))
      (:stp-pre (a64-pair #xa9800000 a b c d))
      (:b (+ #x14000000 (a64-signed-scaled (- (a64-offset a labels) pc) 2 26)))
      (:bl (+ #x94000000 (a64-signed-scaled (- (a64-offset a labels) pc) 2 26)))
      (:b-cond
       (+ #x54000000 (a64-condition a)
          (ash (a64-signed-scaled (- (a64-offset b labels) pc) 2 19) 5)))
      ((:cbz :cbnz)
       (+ (if (eq (car item) :cbz) #xb4000000 #xb5000000) (a64-reg a 0)
          (ash (a64-signed-scaled (- (a64-offset b labels) pc) 2 19) 5)))
      ((:tbz :tbnz)
       (let ((bit (a64-unsigned b 6)))
         (+ (if (eq (car item) :tbz) #x36000000 #x37000000)
            (ash (ash bit -5) 31) (ash (low-bits bit 5) 19) (a64-reg a 0)
            (ash (a64-signed-scaled (- (a64-offset c labels) pc) 2 14) 5))))
      (:adr (a64-adr #x10000000 a (- (a64-offset b labels) pc)))
      (:br (+ #xd61f0000 (a64-reg a 5)))
      (:blr (+ #xd63f0000 (a64-reg a 5)))
      (:ret #xd65f03c0)
      (:svc (+ #xd4000001 (ash (a64-unsigned a 16) 5)))
      (otherwise (compiler-error "Unknown assembly item: ~x0." item)))))

(defun prepend-word (word left acc)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      acc
    (prepend-word word (- left 1)
                  (cons (code-char (low-bits (ash word (* -8 (- left 1))) 8))
                        acc))))

(defun prepend-string (s left acc)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      acc
    (prepend-string s (- left 1) (cons (char s (- left 1)) acc))))

; An image is a byte count paired with strings in file order. Only
; bounded runs of individual bytes are turned into fragments.
(defun image-flush (chars chunks)
  (if (consp chars)
      (cons (coerce chars 'string) chunks)
    chunks))

(defun image-zeroes (left chars)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      (coerce chars 'string)
    (image-zeroes (- left 1) (cons (code-char 0) chars))))

(defun image-padding (left chunks)
  (if (zp left)
      chunks
    (cons (image-zeroes left nil) chunks)))

(defun image-onto (chunks rest)
  (if (atom rest)
      chunks
    (reverse-onto (reverse-onto chunks nil) rest)))

; Conses the first I characters of the string S onto CHARS, reading S by
; position from its end, so that each byte of the image costs one cons.
(defun image-prepend-chars (s i chars)
  (declare (xargs :measure (nfix i)))
  (if (zp i)
      chars
    (image-prepend-chars s (- i 1) (cons (char s (- i 1)) chars))))

; REVERSED holds the fragments of an image, the last first.
(defun image-characters (reversed chars)
  (if (consp reversed)
      (image-characters (cdr reversed)
                        (image-prepend-chars (car reversed) (length (car reversed)) chars))
    chars))

; The string of the fragments CHUNKS, in order: their characters are listed
; once, from the last fragment back to the first, and made a string once.
(defun image-string (chunks)
  (coerce (image-characters (reverse-onto chunks nil) nil) 'string))

(defun aligned-size (size bits)
  (ash (ash (+ size (- (ash 1 bits) 1)) (- bits)) bits))

(defun a64-zero-source-p (item)
  (equal 31 (if (or (eq (car item) :cmp) (eq (car item) :cmn))
                (cadr item)
              (caddr item))))

; Flag-setting instructions with an immediate encode SP as source 31.
; Use two words to compute the result and flags for a zero source.
(defun a64-zero-source-words (item)
  (let* ((op (car item))
         (compare (or (eq op :cmp) (eq op :cmn)))
         (subtract (or (eq op :cmp) (eq op :subs)))
         (rd (if compare 31 (cadr item)))
         (imm (a64-unsigned (if compare (caddr item) (cadddr item)) 12)))
    (if (equal rd 31)
        (let ((flags (if subtract
                         (if (equal imm 0) 6 8)
                       (if (equal imm 0) 4 0))))
          (mv #xea1f03ff (+ #xfa5f13e0 flags)))
      (mv (a64-wide #xd2800000 rd imm 0)
          (if subtract
              (a64-rrr #xeb000000 rd 31 rd)
            (a64-rrr #xea000000 31 rd rd))))))

(defun a64-size (item)
  (case (car item)
    ((:quad :adr-far) 8)
    ((:adds :subs :cmp :cmn) (if (a64-zero-source-p item) 8 4))
    (:bytes (aligned-size (length (cadr item)) 2))
    (:label 0)
    (otherwise 4)))

(defun a64-image-item-size (item)
  (if (eq (car item) :image)
      (cadr item)
    (a64-size item)))

(defun a64-layout (items pc labels reversed)
  (if (atom items)
      (mv pc labels reversed)
    (let* ((item (car items))
           (key (cadr item)))
      (if (eq (car item) :label)
          (let ((hash (label-hash key)))
            (if (table-get key hash 16 labels)
                (mv (compiler-error "Duplicate assembly label: ~x0." key) nil nil)
              (a64-layout (cdr items) pc (table-put key pc hash 16 labels) reversed)))
        (a64-layout (cdr items) (+ pc (a64-image-item-size item)) labels
                    (cons item reversed))))))

(defun a64-emit (item pc labels acc)
  (let ((value (cadr item)))
    (case (car item)
      (:quad (if (and (integerp value)
                      (or (and (<= 0 value) (equal (ash value -64) 0))
                          (equal (ash value -63) -1)))
                 (prepend-word value 8 acc)
               (compiler-error "Invalid quad: ~x0." value)))
      ((:adds :subs :cmp :cmn)
       (if (a64-zero-source-p item)
           (mv-let (first second)
             (a64-zero-source-words item)
             (prepend-word first 4 (prepend-word second 4 acc)))
         (prepend-word (a64-word item pc labels) 4 acc)))
      (:adr-far
       (let* ((target (a64-offset (caddr item) labels))
              (pages (- (ash target -12) (ash pc -12))))
         (prepend-word (a64-adr #x90000000 value pages) 4
                       (prepend-word (if (equal value 31)
                                         #xaa1f03ff
                                       (a64-uimm #x91000000 value value
                                                 (low-bits target 12) 0))
                                     4 acc))))
      (otherwise (prepend-word (a64-word item pc labels) 4 acc)))))

(defun a64-write-chunks (reversed end labels chars buffered chunks)
  (if (atom reversed)
      (image-flush chars chunks)
    (let* ((item (car reversed))
           (bytes (a64-image-item-size item))
           (pc (- end bytes)))
      (case (car item)
        (:image
         (a64-write-chunks (cdr reversed) pc labels nil 0
                           (image-onto (caddr item) (image-flush chars chunks))))
        (:bytes
         (let* ((text (cadr item))
                (size (length text))
                (chunks (image-padding (- bytes size) (image-flush chars chunks))))
           (a64-write-chunks (cdr reversed) pc labels nil 0
                             (if (zp size) chunks (cons text chunks)))))
        (otherwise
         (let ((chars (a64-emit item pc labels chars))
               (buffered (+ bytes buffered)))
           (if (<= 512 buffered)
               (a64-write-chunks (cdr reversed) pc labels nil 0
                                 (image-flush chars chunks))
             (a64-write-chunks (cdr reversed) pc labels chars buffered chunks))))))))

(defun a64-write (reversed end labels acc)
  (a64-write-chunks reversed end labels nil 0 acc))

(defun a64-assemble-image (items entry)
  (mv-let (end labels reversed)
    (a64-layout items 0 nil nil)
    (mv (cons end (a64-write reversed end labels nil)) (a64-offset entry labels))))

(defun a64-assemble (items entry)
  (mv-let (image location)
    (a64-assemble-image items entry)
    (mv (image-string (cdr image)) location)))

(defun a64-bytes (items)
  (mv-let (end labels reversed)
    (a64-layout items 0 nil nil)
    (image-string (a64-write reversed end labels nil))))
