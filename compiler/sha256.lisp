(in-package "BOYMOO-COMPILER")

(include-book "a64")

(set-verify-guards-eagerness 0)

(defconst *sha256-initial*
  '(#x6a09e667 #xbb67ae85 #x3c6ef372 #xa54ff53a
    #x510e527f #x9b05688c #x1f83d9ab #x5be0cd19))

(defconst *sha256-constants*
  '(#x428a2f98 #x71374491 #xb5c0fbcf #xe9b5dba5
    #x3956c25b #x59f111f1 #x923f82a4 #xab1c5ed5
    #xd807aa98 #x12835b01 #x243185be #x550c7dc3
    #x72be5d74 #x80deb1fe #x9bdc06a7 #xc19bf174
    #xe49b69c1 #xefbe4786 #x0fc19dc6 #x240ca1cc
    #x2de92c6f #x4a7484aa #x5cb0a9dc #x76f988da
    #x983e5152 #xa831c66d #xb00327c8 #xbf597fc7
    #xc6e00bf3 #xd5a79147 #x06ca6351 #x14292967
    #x27b70a85 #x2e1b2138 #x4d2c6dfc #x53380d13
    #x650a7354 #x766a0abb #x81c2c92e #x92722c85
    #xa2bfe8a1 #xa81a664b #xc24b8b70 #xc76c51a3
    #xd192e819 #xd6990624 #xf40e3585 #x106aa070
    #x19a4c116 #x1e376c08 #x2748774c #x34b0bcb5
    #x391c0cb3 #x4ed8aa4a #x5b9cca4f #x682e6ff3
    #x748f82ee #x78a5636f #x84c87814 #x8cc70208
    #x90befffa #xa4506ceb #xbef9a3f7 #xc67178f2))

(defun sha256-low32 (x)
  (- x (ash (ash x -32) 32)))

; A sum of at most seven words has at most three bits above bit 31.
(defun sha256-reduce-sum (sum)
  (let* ((sum (if (< sum #x400000000) sum (- sum #x400000000)))
         (sum (if (< sum #x200000000) sum (- sum #x200000000))))
    (if (< sum #x100000000) sum (- sum #x100000000))))

(defun sha256-rotr (x n)
  (let ((high (ash x (- n))))
    (+ high (ash (- x (ash high n)) (- 32 n)))))

(defun sha256-xor3 (x y z)
  (acl2::binary-logxor (acl2::binary-logxor x y) z))

(defun sha256-cap-sigma0 (x)
  (sha256-xor3 (sha256-rotr x 2) (sha256-rotr x 13) (sha256-rotr x 22)))

(defun sha256-cap-sigma1 (x)
  (sha256-xor3 (sha256-rotr x 6) (sha256-rotr x 11) (sha256-rotr x 25)))

(defun sha256-sigma0 (x)
  (sha256-xor3 (sha256-rotr x 7) (sha256-rotr x 18) (ash x -3)))

(defun sha256-sigma1 (x)
  (sha256-xor3 (sha256-rotr x 17) (sha256-rotr x 19) (ash x -10)))

(defun sha256-choose (x y z)
  (let* ((different (acl2::binary-logxor y z))
         (both (ash (- (+ x different) (acl2::binary-logxor x different)) -1)))
    (acl2::binary-logxor z both)))

; At each bit, the sum less the parity is two if the majority bit is one.
(defun sha256-majority (x y z)
  (ash (- (+ x y z) (sha256-xor3 x y z)) -1))

(defun sha256-next-word (history)
  (let ((oldest (cddddr (cddddr (cddddr history)))))
    (sha256-reduce-sum (+ (sha256-sigma1 (cadr history))
                          (caddr (cddddr history))
                          (sha256-sigma0 (caddr oldest))
                          (cadddr oldest)))))

; The initial words are in message order. The history holds the words
; used in this block, latest first.
(defun sha256-rounds (constants pending history a b c d e f g h)
  (if (atom constants)
      (list a b c d e f g h)
    (let* ((w (if (consp pending) (car pending) (sha256-next-word history)))
           (first (+ h (sha256-cap-sigma1 e) (sha256-choose e f g)
                     (car constants) w))
           (second (+ (sha256-cap-sigma0 a) (sha256-majority a b c))))
      (sha256-rounds (cdr constants) (cdr pending) (cons w history)
                     (sha256-reduce-sum (+ first second)) a b c
                     (sha256-reduce-sum (+ d first)) e f g))))

(defun sha256-add-states (x y)
  (if (atom x)
      nil
    (cons (sha256-reduce-sum (+ (car x) (car y)))
          (sha256-add-states (cdr x) (cdr y)))))

(defun sha256-compress (words state-words)
  (let* ((last-four (cddddr state-words))
         (rounds (sha256-rounds *sha256-constants* words nil
                                (car state-words) (cadr state-words)
                                (caddr state-words) (cadddr state-words)
                                (car last-four) (cadr last-four)
                                (caddr last-four) (cadddr last-four))))
    (sha256-add-states state-words rounds)))

(defun sha256-message-word (text at)
  (+ (ash (char-code (char text at)) 24)
     (ash (char-code (char text (+ at 1))) 16)
     (ash (char-code (char text (+ at 2))) 8)
     (char-code (char text (+ at 3)))))

; The message range may include virtual zero bytes after the end of TEXT.
; The SHA-256 padding follows the full message range.
(defun sha256-padded-byte (text at data-end message-end)
  (cond ((< at data-end) (char-code (char text at)))
        ((equal at message-end) 128)
        (t 0)))

(defun sha256-last-word (text at data-end message-end padded-end bits)
  (cond ((equal (+ at 4) padded-end) (sha256-low32 bits))
        ((equal (+ at 8) padded-end) (ash bits -32))
        (t (+ (ash (sha256-padded-byte text at data-end message-end) 24)
              (ash (sha256-padded-byte text (+ at 1) data-end message-end) 16)
              (ash (sha256-padded-byte text (+ at 2) data-end message-end) 8)
              (sha256-padded-byte text (+ at 3) data-end message-end)))))

(defun sha256-block-words (text at left data-end message-end padded-end bits acc)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      acc
    (let ((word (if (<= (+ at 4) data-end)
                    (sha256-message-word text at)
                  (sha256-last-word text at data-end message-end padded-end bits))))
      (sha256-block-words text (- at 4) (- left 1) data-end message-end padded-end
                          bits (cons word acc)))))

(defun sha256-blocks (text at left data-end message-end padded-end bits digest)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      digest
    (let ((words (sha256-block-words text (+ at 60) 16 data-end message-end
                                    padded-end bits nil)))
      (sha256-blocks text (+ at 64) (- left 1) data-end message-end padded-end
                     bits (sha256-compress words digest)))))

(defun sha256-range-words (text start data-end message-end)
  (let* ((bytes (- message-end start))
         (blocks (ash (+ bytes 72) -6)))
    (sha256-blocks text start blocks data-end message-end
                   (+ start (ash blocks 6)) (ash bytes 3) *sha256-initial*)))

; A page that spans fragments needs at most one page of temporary
; string data. Full pages within one fragment are hashed in place.
(defun sha256-page-pieces (chunks at left pieces)
  (if (atom chunks)
      (mv (reverse-onto pieces nil) nil 0)
    (let* ((text (car chunks))
           (size (length text))
           (available (- size at)))
      (if (< left available)
          (mv (reverse-onto (cons (subseq text at (+ at left)) pieces) nil)
              chunks (+ at left))
        (let ((pieces (if (zp available)
                          pieces
                        (cons (if (zp at) text (subseq text at size)) pieces))))
          (if (equal left available)
              (mv (reverse-onto pieces nil) (cdr chunks) 0)
            (sha256-page-pieces (cdr chunks) 0 (- left available) pieces)))))))

(defun sha256-page (chunks at size)
  (let* ((text (car chunks))
         (end (+ at size))
         (length (length text)))
    (if (and (consp chunks) (<= end length))
        (mv (sha256-range-words text at end end)
            (if (equal end length) (cdr chunks) chunks)
            (if (equal end length) 0 end))
      (mv-let (pieces rest next)
        (sha256-page-pieces chunks at size nil)
        (let ((page (image-string pieces)))
          (mv (sha256-range-words page 0 (length page) size) rest next))))))

(defun sha256-prepend-be (word left acc)
  (declare (xargs :measure (nfix left)))
  (if (zp left)
      acc
    (let ((high (ash word -8)))
      (sha256-prepend-be high (- left 1)
                         (cons (code-char (- word (ash high 8))) acc)))))

(defun sha256-prepend-digest (words acc)
  (if (atom words)
      acc
    (sha256-prepend-be (car words) 4
                       (sha256-prepend-digest (cdr words) acc))))

(defun sha256 (text)
  (let ((end (length text)))
    (coerce (sha256-prepend-digest (sha256-range-words text 0 end end) nil)
            'string)))
