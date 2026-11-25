(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun reader-byte-codes (chars)
  (if (endp chars)
      nil
    (cons (char-code (car chars)) (reader-byte-codes (cdr chars)))))

(defconst *reader-plain*
  (reader-byte-codes (coerce "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789-+*/<=>!?$%&_^~.@" 'list)))

(defconst *reader-hex* "0123456789ABCDEF")

(defconst *reader-word-chars*
  (reader-byte-codes (coerce "abcdefghijklmnopqrstuvwxyz-" 'list)))

(defconst *reader-value-error* '(:failure "value" ""))

(defconst *reader-decimal-limit* 4300)

(defun reader-reader-init (source)
  (list :reader source 0))

(defun reader-reader (source)
  (reader-reader-init source))

(defun reader-reader-s (r)
  (cadr r))

(defun reader-reader-i (r)
  (caddr r))

; A cursor used within a call pairs the offset with the unread characters.
(defun reader-cursor (r)
  (let ((index (reader-reader-i r)))
    (cons index (nthcdr index (coerce (reader-reader-s r) 'list)))))

(defun reader-at-cursor (r cursor)
  (list :reader (reader-reader-s r) (car cursor)))

(defun reader-at-result (r result)
  (if (failure-p result)
      result
    (cons (car result) (reader-at-cursor r (cdr result)))))

(defun reader-cursor-peek (cursor)
  (if (endp (cdr cursor)) -1 (char-code (cadr cursor))))

(defun reader-cursor-advance (cursor count)
  (cons (+ (car cursor) count) (nthcdr count (cdr cursor))))

(defun reader-prefix-p (prefix chars)
  (cond ((endp prefix) t)
        ((endp chars) nil)
        ((eql (car prefix) (car chars))
         (reader-prefix-p (cdr prefix) (cdr chars)))
        (t nil)))

(defun reader-cursor-take (cursor text)
  (if (reader-prefix-p (coerce text 'list) (cdr cursor))
      (reader-cursor-advance cursor (length text))
    *reader-value-error*))

(defun reader-reader-take (r text)
  (if (text-starts-at (reader-reader-s r) text (reader-reader-i r))
      (list :reader (reader-reader-s r) (+ (reader-reader-i r) (length text)))
    *reader-value-error*))

(defun reader-hex-digit (c)
  (let ((byte (char-code c)))
    (cond ((and (<= 48 byte) (<= byte 57)) (- byte 48))
          ((and (<= 65 byte) (<= byte 70)) (- byte 55))
          (t -1))))

(defun reader-hex-byte (chars)
  (if (and (consp chars) (consp (cdr chars)))
      (let ((high (reader-hex-digit (car chars)))
            (low (reader-hex-digit (cadr chars))))
        (if (or (< high 0) (< low 0)) -1 (+ (* 16 high) low)))
    -1))

(defun reader-printable-p (byte)
  (and (<= 32 byte) (<= byte 126)))

(defun reader-escaped-chars (chars index close reversed)
  (declare (xargs :measure (acl2-count chars)))
  (let ((byte (if (endp chars) -1 (char-code (car chars)))))
    (cond
     ((= byte close)
      (cons (coerce (reverse reversed) 'string) (cons (1+ index) (cdr chars))))
     ((endp chars) *reader-value-error*)
     ((= byte 92)
      (let ((escaped (reader-hex-byte (cdr chars))))
        (if (or (< escaped 0)
                (and (reader-printable-p escaped) (/= escaped close) (/= escaped 92)))
            *reader-value-error*
          (reader-escaped-chars (cdddr chars) (+ index 3) close
                                (cons (code-char escaped) reversed)))))
     ((reader-printable-p byte)
      (reader-escaped-chars (cdr chars) (1+ index) close (cons (car chars) reversed)))
     (t *reader-value-error*))))

(defun reader-cursor-escaped (cursor close)
  (reader-escaped-chars (cdr cursor) (car cursor) close nil))

(defun reader-scan (chars index alphabet reversed)
  (if (and (consp chars) (member-equal (char-code (car chars)) alphabet))
      (reader-scan (cdr chars) (1+ index) alphabet (cons (car chars) reversed))
    (cons (coerce (reverse reversed) 'string) (cons index chars))))

; Whether CODE is a member of *reader-plain*, found by comparing: the letters
; A to Z, the digits, and - + * / < = > ! ? $ % & _ ^ ~ . @
(defun reader-plain-code-p (code)
  (or (and (<= 65 code) (<= code 90))
      (and (<= 42 code) (<= code 57) (not (= code 44)))
      (and (<= 60 code) (<= code 64))
      (= code 33)
      (and (<= 36 code) (<= code 38))
      (= code 94)
      (= code 95)
      (= code 126)))

; reader-scan with the alphabet *reader-plain*.
(defun reader-scan-plain (chars index reversed)
  (if (and (consp chars) (reader-plain-code-p (char-code (car chars))))
      (reader-scan-plain (cdr chars) (1+ index) (cons (car chars) reversed))
    (cons (coerce (reverse reversed) 'string) (cons index chars))))

(defun reader-cursor-plain (cursor)
  (reader-scan-plain (cdr cursor) (car cursor) nil))

(defun reader-all-plain-p (chars)
  (if (endp chars)
      t
    (and (reader-plain-code-p (char-code (car chars)))
         (reader-all-plain-p (cdr chars)))))

(defun reader-cursor-part (cursor)
  (if (= (reader-cursor-peek cursor) 124)
      (let ((result (reader-cursor-escaped (reader-cursor-advance cursor 1) 124)))
        (if (failure-p result)
            result
          (let ((p (car result)))
            (if (and (not (equal p "")) (reader-all-plain-p (coerce p 'list)))
                *reader-value-error*
              result))))
    (reader-cursor-plain cursor)))

(defun reader-partition-slash (chars reversed)
  (if (or (endp chars) (eql (car chars) #\/))
      (cons (reverse reversed) chars)
    (reader-partition-slash (cdr chars) (cons (car chars) reversed))))

(defun reader-digit-p (c)
  (let ((byte (char-code c)))
    (and (<= 48 byte) (<= byte 57))))

(defun reader-all-digits-p (chars)
  (if (endp chars)
      t
    (and (reader-digit-p (car chars)) (reader-all-digits-p (cdr chars)))))

(defun reader-canonical-digits-p (chars)
  (and (consp chars)
       (reader-all-digits-p chars)
       (not (and (eql (car chars) #\0) (consp (cdr chars))))))

(defun reader-decimal (digits value)
  (if (endp digits)
      value
    (reader-decimal (cdr digits) (+ (* 10 value) (- (char-code (car digits)) 48)))))

(defun reader-decimal-value (digits)
  (let ((count (len digits)))
    (if (> count *reader-decimal-limit*)
        (quote (:failure "value" ""))
      (reader-decimal digits 0))))

(defun reader-gcd (n a b)
  (declare (xargs :measure (nfix n)))
  (cond ((zp n) '(:failure "fuel" "reader-gcd"))
        ((zp b) a)
        (t (reader-gcd (1- n) b (mod a b)))))

(defun reader-reduced-ratio (n magnitude denominator)
  (let ((d (reader-decimal-value denominator)))
    (if (failure-p d)
        d
      (let ((gcd (reader-gcd 1000000 magnitude d)))
        (cond ((failure-p gcd) gcd)
              ((or (< d 2) (/= gcd 1)) *reader-value-error*)
              (t (list "ratio" n d)))))))

(defun reader-rational-text (text)
  (let* ((parts (reader-partition-slash (coerce text 'list) nil))
         (num (car parts))
         (fractionp (consp (cdr parts)))
         (den (cddr parts))
         (negativep (eql (car num) #\-))
         (digits (if negativep (cdr num) num)))
    (cond
     ((not (reader-canonical-digits-p digits)) *reader-value-error*)
     ((and fractionp (not (reader-canonical-digits-p den))) *reader-value-error*)
     ((equal num '(#\- #\0)) *reader-value-error*)
     (t (let ((magnitude (reader-decimal-value digits)))
          (if (failure-p magnitude)
              magnitude
            (let ((n (if negativep (- magnitude) magnitude)))
              (if fractionp (reader-reduced-ratio n magnitude den) n))))))))

(defun reader-complex-imaginary (re cursor)
  (let* ((field (reader-cursor-plain cursor))
         (im (reader-rational-text (car field))))
    (if (failure-p im)
        im
      (let ((closed (reader-cursor-take (cdr field) ")")))
        (cond ((failure-p closed) closed)
              ((equal im 0) *reader-value-error*)
              (t (cons (list "complex" re im) closed)))))))

(defun reader-cursor-complex (cursor)
  (let ((opened (reader-cursor-take cursor "#C(")))
    (if (failure-p opened)
        opened
      (let* ((field (reader-cursor-plain opened))
             (re (reader-rational-text (car field))))
        (if (failure-p re)
            re
          (let ((space (reader-cursor-take (cdr field) " ")))
            (if (failure-p space) space (reader-complex-imaginary re space))))))))

(defun reader-cursor-sharp (cursor)
  (if (reader-prefix-p '(#\# #\\) (cdr cursor))
      (let ((byte (reader-hex-byte (cdddr cursor))))
        (if (< byte 0)
            *reader-value-error*
          (cons (list "char" byte) (reader-cursor-advance cursor 4))))
    (reader-cursor-complex cursor)))

(defun reader-cursor-string (cursor)
  (let ((result (reader-cursor-escaped (reader-cursor-advance cursor 1) 34)))
    (if (failure-p result)
        result
      (cons (list "str" (car result)) (cdr result)))))

(defun reader-cursor-symbol-or-rational (cursor byte)
  (let ((first (reader-cursor-part cursor)))
    (if (failure-p first)
        first
      (let ((next (cdr first)))
        (cond
         ((reader-prefix-p '(#\: #\:) (cdr next))
          (let ((second (reader-cursor-part (reader-cursor-advance next 2))))
            (if (failure-p second)
                second
              (cons (list "sym" (car first) (car second)) (cdr second)))))
         ((or (= byte 124) (= (car cursor) (car next))) *reader-value-error*)
         (t (let ((rational (reader-rational-text (car first))))
              (if (failure-p rational) rational (cons rational next)))))))))

(defun reader-datum-list-p (x)
  (and (consp x) (not (stringp (car x)))))

(defun reader-close-list (cursor reversed)
  (let ((closed (reader-cursor-take cursor ")")))
    (if (failure-p closed) closed (cons (reverse reversed) closed))))

(mutual-recursion
 (defun reader-cursor-datum (n cursor)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       '(:failure "fuel" "reader-reader-datum")
     (let ((byte (reader-cursor-peek cursor)))
       (cond
        ((= byte 40)
         (let ((first (reader-cursor-datum (1- n) (reader-cursor-advance cursor 1))))
           (if (failure-p first)
               first
             (reader-cursor-list-items (1- n) (cdr first) (list (car first))))))
        ((= byte 34) (reader-cursor-string cursor))
        ((= byte 35) (reader-cursor-sharp cursor))
        (t (reader-cursor-symbol-or-rational cursor byte))))))
 (defun reader-cursor-list-items (n cursor reversed)
   (declare (xargs :measure (nfix n)))
   (cond
    ((zp n) '(:failure "fuel" "reader-cursor-list-items"))
    ((/= (reader-cursor-peek cursor) 32) (reader-close-list cursor reversed))
    (t (let ((next (reader-cursor-advance cursor 1)))
         (if (reader-prefix-p '(#\. #\Space) (cdr next))
             (let ((tail (reader-cursor-datum (1- n) (reader-cursor-advance next 2))))
               (cond ((failure-p tail) tail)
                     ((or (reader-datum-list-p (car tail))
                          (equal (car tail) '("sym" "COMMON-LISP" "NIL")))
                      *reader-value-error*)
                     (t (reader-close-list (cdr tail) (cons (list "dot" (car tail)) reversed)))))
           (let ((item (reader-cursor-datum (1- n) next)))
             (if (failure-p item)
                 item
               (reader-cursor-list-items (1- n) (cdr item) (cons (car item) reversed))))))))))

(defun reader-reader-datum (r)
  (reader-at-result r (reader-cursor-datum 1000000 (reader-cursor r))))

(defun reader-cursor-line-args (n cursor word reversed size)
  (declare (xargs :measure (nfix n)))
  (cond
   ((zp n) '(:failure "fuel" "reader-cursor-line-args"))
   ((= (reader-cursor-peek cursor) 32)
    (let ((arg (reader-cursor-datum 1000000 (reader-cursor-advance cursor 1))))
      (if (failure-p arg)
          arg
        (reader-cursor-line-args (1- n) (cdr arg) word (cons (car arg) reversed) size))))
   (t (let ((end (reader-cursor-take cursor ")")))
        (cond ((failure-p end) end)
              ((/= (car end) size) *reader-value-error*)
              (t (cons (list word (reverse reversed)) end)))))))

(defun reader-reader-line (r)
  (let ((opened (reader-cursor-take (reader-cursor r) "(")))
    (if (failure-p opened)
        opened
      (let* ((field (reader-scan (cdr opened) (car opened) *reader-word-chars* nil))
             (word (car field)))
        (cond ((endp (cddr field)) '(:failure "value" ""))
              ((equal word "") *reader-value-error*)
              (t (reader-at-result r (reader-cursor-line-args 1000000 (cdr field) word nil
                                                             (length (reader-reader-s r))))))))))

(defun reader-escape-chars (chars close)
  (if (endp chars)
      nil
    (let* ((byte (char-code (car chars)))
           (rest (reader-escape-chars (cdr chars) close)))
      (if (and (reader-printable-p byte) (/= byte close) (/= byte 92))
          (cons (car chars) rest)
        (list* #\\ (char *reader-hex* (floor byte 16)) (char *reader-hex* (mod byte 16))
               rest)))))

(defun reader-escape (bytes close)
  (coerce (reader-escape-chars (coerce bytes 'list) close) 'string))

(defun reader-part (p)
  (if (and (not (equal p "")) (reader-all-plain-p (coerce p 'list)))
      p
    (text-join "" (list "|" (reader-escape p 124) "|"))))

(defun reader-rat (x)
  (cond ((integerp x) (decimal-text x))
        ((eq x t) "1")
        (t (text-join "/" (list (decimal-text (cadr x)) (decimal-text (caddr x)))))))

(defun reader-format-hex (n)
  (let* ((magnitude (abs n))
         (digits (explode-nonnegative-integer magnitude 16 nil)))
    (coerce (cond ((< n 0) (cons #\- digits))
                  ((< magnitude 16) (cons #\0 digits))
                  (t digits))
            'string)))

(defun reader-write-atom (x)
  (cond
   ((or (integerp x) (eq x t) (equal (car x) "ratio")) (reader-rat x))
   ((equal (car x) "str") (text-join "" (list "\"" (reader-escape (cadr x) 34) "\"")))
   ((equal (car x) "char") (string-append "#\\" (reader-format-hex (cadr x))))
   ((equal (car x) "complex")
    (text-join "" (list "#C(" (reader-rat (cadr x)) " " (reader-rat (caddr x)) ")")))
   (t (text-join "::" (list (reader-part (cadr x)) (reader-part (caddr x)))))))

(mutual-recursion
 (defun reader-write-into (x reversed)
   (declare (xargs :measure (1+ (* 2 (acl2-count x)))))
   (cond ((null x) '(:failure "index" ""))
         ((reader-datum-list-p x) (reader-write-list-into x t (cons #\( reversed)))
         (t (revappend (coerce (reader-write-atom x) 'list) reversed))))
 (defun reader-write-list-into (xs firstp reversed)
   (declare (xargs :measure (* 2 (acl2-count xs))))
   (cond
    ((endp xs) (cons #\) reversed))
    ((and (endp (cdr xs)) (consp (car xs)) (equal (caar xs) "dot"))
     (let ((written (reader-write-into (cadar xs)
                                      (list* #\Space #\. #\Space reversed))))
       (if (failure-p written) written (cons #\) written))))
    (t (let ((written (reader-write-into (car xs)
                                        (if firstp reversed (cons #\Space reversed)))))
         (if (failure-p written) written (reader-write-list-into (cdr xs) nil written)))))))

(defun reader-write (x)
  (let ((written (reader-write-into x nil)))
    (if (failure-p written) written (coerce (reverse written) 'string))))
