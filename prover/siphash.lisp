(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

; SipHash-2-4 of the character codes of a string, with the key of the
; sixteen bytes 0 to 15.  The value is a natural number below 2^64, and
; siphash-hexdigest writes it as sixteen hexadecimal digits in lower case.
; It gives a helper of a proof a name that depends only on its text.  Of
; ACL2's functions on bits it uses logxor and ash alone.

(defconst *siphash-word* 18446744073709551616)

(defconst *siphash-hex* "0123456789abcdef")

; The sum of two words, modulo 2^64.
(defun siphash-add (x y)
  (let ((sum (+ x y)))
    (if (< sum *siphash-word*)
        sum
      (- sum *siphash-word*))))

; A word turned left by a number of bits between 1 and 63: its upper bits
; become the lower bits.
(defun siphash-rotate (x bits)
  (let* ((high (ash x (- bits 64)))
         (low (- x (ash high (- 64 bits)))))
    (+ (ash low bits) high)))

(defun siphash-rounds (n v0 v1 v2 v3)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list v0 v1 v2 v3)
    (let* ((v0 (siphash-add v0 v1))
           (v1 (logxor (siphash-rotate v1 13) v0))
           (v0 (siphash-rotate v0 32))
           (v2 (siphash-add v2 v3))
           (v3 (logxor (siphash-rotate v3 16) v2))
           (v0 (siphash-add v0 v3))
           (v3 (logxor (siphash-rotate v3 21) v0))
           (v2 (siphash-add v2 v1))
           (v1 (logxor (siphash-rotate v1 17) v2))
           (v2 (siphash-rotate v2 32)))
      (siphash-rounds (1- n) v0 v1 v2 v3))))

; The word of the first n characters, the first in the lowest byte.
(defun siphash-load (n chars shift word)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (endp chars))
      word
    (siphash-load (1- n) (cdr chars) (+ shift 8)
                  (+ word (ash (char-code (car chars)) shift)))))

; Takes in n whole words, and returns the characters left and the state.
(defun siphash-words (n chars v0 v1 v2 v3)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      (list chars v0 v1 v2 v3)
    (let* ((word (siphash-load 8 chars 0 0))
           (v (siphash-rounds 2 v0 v1 v2 (logxor v3 word))))
      (siphash-words (1- n) (nthcdr 8 chars)
                     (logxor (car v) word) (cadr v) (caddr v) (cadddr v)))))

(defun siphash (string)
  (let* ((size (length string))
         (whole (ash size -3))
         (state (siphash-words whole (coerce string 'list)
                               #x7469686173716475 #x6b617f6d656e6665
                               #x6b7f62616d677361 #x7b6b696e727e6c7b))
         (last (+ (siphash-load 7 (car state) 0 0)
                  (ash (- size (ash (ash size -8) 8)) 56)))
         (v (siphash-rounds 2 (cadr state) (caddr state) (cadddr state)
                            (logxor (car (cddddr state)) last)))
         (v (siphash-rounds 4 (logxor (car v) last) (cadr v)
                            (logxor (caddr v) 255) (cadddr v))))
    (logxor (logxor (car v) (cadr v)) (logxor (caddr v) (cadddr v)))))

(defun siphash-hex (n value chars)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      chars
    (let ((high (ash value -4)))
      (siphash-hex (1- n) high
                   (cons (char *siphash-hex* (- value (ash high 4))) chars)))))

(defun siphash-hexdigest (string)
  (coerce (siphash-hex 16 (siphash string) nil) 'string))
