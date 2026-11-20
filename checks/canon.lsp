; The canonical text of a datum, as spec/formats.md defines it, written
; by ACL2.  The checks load this file and use it to print what ACL2
; holds, so that it can be compared, byte for byte, with the files of
; this repository.

(in-package "ACL2")

(program)

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

(defun bm-write-lines (lines chan state)
  (declare (xargs :stobjs state))
  (cond ((endp lines) state)
        (t (pprogn (princ$ (car lines) chan state)
                   (newline chan state)
                   (bm-write-lines (cdr lines) chan state)))))

(defun bm-write-file (lines file state)
  (declare (xargs :stobjs state))
  (mv-let (chan state)
    (open-output-channel file :character state)
    (cond ((null chan)
           (prog2$ (er hard 'bm-write-file "Cannot write ~x0" file) state))
          (t (pprogn (bm-write-lines lines chan state)
                     (close-output-channel chan state))))))

(logic)
