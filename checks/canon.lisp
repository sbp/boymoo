; The canonical text of a datum, as spec/formats.md defines it, written
; by ACL2.  It is the one printer of the formats in this repository: the
; checks, the exporter, its read-back check and the tests of the runner
; all print with it, the scripts through checks/canon.lsp.  It is a book
; with no state: (bm-line WORD ARGS) is the text of the line whose word is
; WORD and whose data are ARGS, and (bm-obj X ACC) puts the text of the
; datum X, in reverse, before the characters ACC.  Its functions are in
; logic mode with verified guards.

(in-package "ACL2")

(logic)

; Every function below adds characters to ACC, a list of characters in
; reverse order.

(defun bm-hex2 (n)
  (declare (xargs :guard (and (natp n) (< n 256)) :verify-guards nil))
  (list (char "0123456789ABCDEF" (floor n 16))
        (char "0123456789ABCDEF" (mod n 16))))

(defun bm-plain-charp (c)
  (declare (xargs :guard (characterp c) :verify-guards t))
  (or (and (char<= #\A c) (char<= c #\Z))
      (and (char<= #\0 c) (char<= c #\9))
      (member c '(#\- #\+ #\* #\/ #\< #\= #\> #\! #\? #\$ #\% #\& #\_
                  #\^ #\~ #\. #\@))))

(defun bm-all-plain (chars)
  (declare (xargs :guard (character-listp chars) :verify-guards t))
  (or (endp chars)
      (and (bm-plain-charp (car chars))
           (bm-all-plain (cdr chars)))))

; The characters of a string or of a name between bars.  DELIM is the
; closing character, which is escaped, as is the backslash and every
; character whose code is not from 32 to 126.

(defun bm-escaped (chars delim acc)
  (declare (xargs :guard (and (character-listp chars) (characterp delim)
                             (character-listp acc))
                  :verify-guards nil))
  (cond ((endp chars) acc)
        (t (let* ((c (car chars))
                  (n (char-code c)))
             (bm-escaped
              (cdr chars) delim
              (if (and (<= 32 n) (<= n 126)
                       (not (eql c delim))
                       (not (eql c #\\)))
                  (cons c acc)
                (revappend (cons #\\ (bm-hex2 n)) acc)))))))

; One part of a symbol: the name of its package, or its own name.

(defun bm-part (s acc)
  (declare (xargs :guard (and (stringp s) (character-listp acc))
                  :verify-guards nil))
  (let ((chars (coerce s 'list)))
    (if (and (consp chars) (bm-all-plain chars))
        (revappend chars acc)
      (cons #\| (bm-escaped chars #\| (cons #\| acc))))))

(defun bm-nat (n acc)
  (declare (xargs :guard (and (natp n) (character-listp acc))
                  :verify-guards nil))
  (revappend (explode-nonnegative-integer n 10 nil) acc))

(defun bm-int (i acc)
  (declare (xargs :guard (and (integerp i) (character-listp acc))
                  :verify-guards nil))
  (if (< i 0)
      (bm-nat (- i) (cons #\- acc))
    (bm-nat i acc)))

(defun bm-rat (r acc)
  (declare (xargs :guard (and (rationalp r) (character-listp acc))
                  :verify-guards nil))
  (if (integerp r)
      (bm-int r acc)
    (bm-nat (denominator r) (cons #\/ (bm-int (numerator r) acc)))))

(mutual-recursion

 (defun bm-obj (x acc)
   (declare (xargs :measure (* 2 (acl2-count x))
                   :guard (character-listp acc) :verify-guards nil))
   (cond ((consp x)
          (bm-tail (cdr x) (bm-obj (car x) (cons #\( acc))))
         ((rationalp x) (bm-rat x acc))
         ((complex-rationalp x)
          (cons #\) (bm-rat (imagpart x)
                            (cons #\Space
                                  (bm-rat (realpart x)
                                          (revappend '(#\# #\C #\()
                                                     acc))))))
         ((characterp x)
          (revappend (list* #\# #\\ (bm-hex2 (char-code x))) acc))
         ((stringp x)
          (cons #\" (bm-escaped (coerce x 'list) #\" (cons #\" acc))))
         ((symbolp x)
          (bm-part (symbol-name x)
                   (cons #\: (cons #\: (bm-part (symbol-package-name x)
                                                acc)))))
         ; The executable hard error has a guard. ILLEGAL calls it.
         (t (mbe :logic (er hard 'bm-obj "Not a datum of ACL2 Core: ~x0" x)
                 :exec (er hard? 'bm-obj "Not a datum of ACL2 Core: ~x0" x)))))

 (defun bm-tail (x acc)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count x)))
                   :guard (character-listp acc)))
   (cond ((consp x)
          (bm-tail (cdr x) (bm-obj (car x) (cons #\Space acc))))
         ((null x) (cons #\) acc))
         (t (cons #\) (bm-obj x (revappend '(#\Space #\. #\Space)
                                           acc)))))))

(defun bm-args (args acc)
  (declare (xargs :guard (and (true-listp args) (character-listp acc))
                  :verify-guards nil))
  (cond ((endp args) acc)
        (t (bm-args (cdr args) (bm-obj (car args) (cons #\Space acc))))))

; A line: a word, which is a string of lower case letters and hyphens,
; and the data after it.

(defun bm-line (word args)
  (declare (xargs :guard (and (stringp word) (true-listp args))
                  :verify-guards nil))
  (coerce (reverse (cons #\) (bm-args args
                                      (revappend (coerce word 'list)
                                                 (list #\()))))
          'string))

(encapsulate
 ()

 ; Each byte indexes two characters in the hexadecimal alphabet.
 (local (defun bm-hex-indices-p (n)
          (and (natp (floor n 16)) (< (floor n 16) 16)
               (natp (mod n 16)) (< (mod n 16) 16))))
 (local (defun bm-check-hex-indices (n)
          (and (bm-hex-indices-p n)
               (or (zp n) (bm-check-hex-indices (1- n))))))
 (local (defthm bm-check-hex-indices-below
          (implies (and (natp n) (bm-check-hex-indices n)
                        (natp i) (<= i n))
                   (bm-hex-indices-p i))
          :hints (("Goal" :in-theory (disable bm-hex-indices-p)))))
 (local (defthm bm-hex-indices-in-bounds
          (implies (and (natp n) (< n 256))
                   (and (integerp (floor n 16)) (<= 0 (floor n 16))
                        (< (floor n 16) 16)
                        (integerp (mod n 16)) (<= 0 (mod n 16))
                        (< (mod n 16) 16)))
          :hints (("Goal" :use ((:instance bm-check-hex-indices-below (n 255) (i n)))
                   :in-theory (disable floor mod bm-check-hex-indices-below)))))

 (verify-guards bm-hex2 :hints (("Goal" :in-theory (disable floor mod))))

 ; Each printing step preserves a character-list accumulator.
 (local (defthm bm-characterp-nth
          (implies (and (character-listp chars) (< (nfix i) (len chars)))
                   (characterp (nth i chars)))))
 (local (defthm bm-character-listp-hex2
          (implies (and (natp n) (< n 256))
                   (character-listp (bm-hex2 n)))
          :hints (("Goal" :in-theory (disable floor mod)))))

 (verify-guards bm-escaped :hints (("Goal" :in-theory (disable bm-hex2))))
 (local (defthm bm-character-listp-escaped
          (implies (and (character-listp chars) (character-listp acc))
                   (character-listp (bm-escaped chars delim acc)))
          :hints (("Goal" :in-theory (disable bm-hex2)))))

 (verify-guards bm-part)
 (local (defthm bm-character-listp-part
          (implies (character-listp acc)
                   (character-listp (bm-part s acc)))))
 (local (defthm bm-characterp-digit-to-char
          (characterp (digit-to-char n))))
 (local (defthm bm-character-listp-explode
          (implies (character-listp acc)
                   (character-listp (explode-nonnegative-integer n base acc)))
          :hints (("Goal" :in-theory (disable floor mod digit-to-char)))))
 (local (in-theory (disable explode-nonnegative-integer)))
 (verify-guards bm-nat)
 (verify-guards bm-int)
 (verify-guards bm-rat)
 (local (defthm bm-character-listp-rat
          (implies (character-listp acc)
                   (character-listp (bm-rat r acc)))))

 (local (defun bm-character-list-induction (tailp x acc)
          (declare (xargs :measure (+ (* 2 (acl2-count x)) (if tailp 1 0))))
          (cond ((consp x)
                 (let ((start (cons (if tailp #\Space #\() acc)))
                   (list (bm-character-list-induction nil (car x) start)
                         (bm-character-list-induction t (cdr x)
                                                      (bm-obj (car x) start)))))
                ((and tailp x)
                 (bm-character-list-induction nil x
                                              (revappend '(#\Space #\. #\Space) acc)))
                (t (list tailp acc)))))
 (local (defthm bm-object-and-tail-preserve-characters
          (implies (character-listp acc)
                   (if tailp
                       (character-listp (bm-tail x acc))
                     (character-listp (bm-obj x acc))))
          :rule-classes nil
          :hints (("Goal" :induct (bm-character-list-induction tailp x acc)
                   :in-theory (e/d (illegal) (bm-hex2 bm-escaped bm-part bm-rat))
                   :expand ((bm-obj x acc) (bm-tail x acc))))))
 (local (defthm bm-character-listp-obj
          (implies (character-listp acc) (character-listp (bm-obj x acc)))
          :hints (("Goal" :use ((:instance bm-object-and-tail-preserve-characters
                                           (tailp nil)))))))
 (local (defthm bm-bad-datum-error-equals-illegal
          (equal (er hard 'bm-obj "Not a datum of ACL2 Core: ~x0" x)
                 (er hard? 'bm-obj "Not a datum of ACL2 Core: ~x0" x))
          :hints (("Goal" :in-theory (enable illegal)))))
 (verify-guards bm-obj
   :hints (("Goal" :in-theory (disable bm-hex2 bm-escaped bm-part bm-rat))))

 (verify-guards bm-args)
 (local (defthm bm-character-listp-args
          (implies (character-listp acc)
                   (character-listp (bm-args args acc)))))
 (verify-guards bm-line
   :hints (("Goal" :use ((:instance bm-character-listp-args
                                    (acc (revappend (coerce word 'list)
                                                    (list #\()))))
                   :in-theory (disable bm-args bm-character-listp-args)))))
