; The canonical text of a datum, as spec/formats.md defines it, written
; by ACL2.  It is the one printer of the formats in this repository: the
; checks, the exporter, its read-back check and the tests of the runner
; all print with it, the scripts through checks/canon.lsp.  It is a book
; with no state: (bm-line WORD ARGS) is the text of the line whose word is
; WORD and whose data are ARGS, and (bm-obj X ACC) puts the text of the
; datum X, in reverse, before the characters ACC.  Its functions are in
; logic mode; they declare no guard, so ACL2 verifies none.  The book
; changes no default of ACL2, since the scripts load it with LD, which
; keeps such a change for the rest of the session.

(in-package "ACL2")

(logic)

; Every function below adds characters to ACC, a list of characters in
; reverse order.

(defun bm-hex2 (n)
  (list (char "0123456789ABCDEF" (floor n 16))
        (char "0123456789ABCDEF" (mod n 16))))

(defun bm-plain-charp (c)
  (or (and (char<= #\A c) (char<= c #\Z))
      (and (char<= #\0 c) (char<= c #\9))
      (member c '(#\- #\+ #\* #\/ #\< #\= #\> #\! #\? #\$ #\% #\& #\_
                  #\^ #\~ #\. #\@))))

(defun bm-all-plain (chars)
  (or (endp chars)
      (and (bm-plain-charp (car chars))
           (bm-all-plain (cdr chars)))))

; The characters of a string or of a name between bars.  DELIM is the
; closing character, which is escaped, as is the backslash and every
; character whose code is not from 32 to 126.

(defun bm-escaped (chars delim acc)
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
  (let ((chars (coerce s 'list)))
    (if (and (consp chars) (bm-all-plain chars))
        (revappend chars acc)
      (cons #\| (bm-escaped chars #\| (cons #\| acc))))))

(defun bm-nat (n acc)
  (revappend (explode-nonnegative-integer n 10 nil) acc))

(defun bm-int (i acc)
  (if (< i 0)
      (bm-nat (- i) (cons #\- acc))
    (bm-nat i acc)))

(defun bm-rat (r acc)
  (if (integerp r)
      (bm-int r acc)
    (bm-nat (denominator r) (cons #\/ (bm-int (numerator r) acc)))))

(mutual-recursion

 (defun bm-obj (x acc)
   (declare (xargs :measure (* 2 (acl2-count x))))
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
         (t (er hard 'bm-obj "Not a datum of ACL2 Core: ~x0" x))))

 (defun bm-tail (x acc)
   (declare (xargs :measure (+ 1 (* 2 (acl2-count x)))))
   (cond ((consp x)
          (bm-tail (cdr x) (bm-obj (car x) (cons #\Space acc))))
         ((null x) (cons #\) acc))
         (t (cons #\) (bm-obj x (revappend '(#\Space #\. #\Space)
                                           acc)))))))

(defun bm-args (args acc)
  (cond ((endp args) acc)
        (t (bm-args (cdr args) (bm-obj (car args) (cons #\Space acc))))))

; A line: a word, which is a string of lower case letters and hyphens,
; and the data after it.

(defun bm-line (word args)
  (coerce (reverse (cons #\) (bm-args args
                                      (revappend (coerce word 'list)
                                                 (list #\()))))
          'string))
