(in-package "BOYMOO-PROVER")
(set-verify-guards-eagerness 0)

(defun failure-p (x)
  (and (consp x)
       (eq (car x) :failure)
       (consp (cdr x))
       (stringp (cadr x))
       (consp (cddr x))
       (stringp (caddr x))
       (null (cdddr x))))

(defun text-starts-at (s prefix start)
  (cond
   ((stringp prefix)
    (let* ((size (length s))
           (first (if (< start 0) (max 0 (+ size start)) start))
           (last (+ first (length prefix))))
      (and (<= last size)
           (equal (subseq s first last) prefix))))
   ((consp prefix)
    (or (text-starts-at s (car prefix) start)
        (text-starts-at s (cdr prefix) start)))
   (t nil)))

(defun text-starts-with (s prefix)
  (text-starts-at s prefix 0))

(defun text-ends-with (s suffix)
  (cond
   ((stringp suffix)
    (let* ((size (length s))
           (first (- size (length suffix))))
      (and (<= 0 first)
           (equal (subseq s first size) suffix))))
   ((consp suffix)
    (or (text-ends-with s (car suffix)) (text-ends-with s (cdr suffix))))
   (t nil)))

(defun text-join-reversed (separator strings reversed)
  (if (endp strings)
      reversed
    (text-join-reversed separator (cdr strings)
                      (revappend (coerce (car strings) 'list)
                                 (revappend separator reversed)))))

(defun text-join (sep strings)
  (if (endp strings)
      ""
    (coerce (reverse (text-join-reversed (coerce sep 'list) (cdr strings)
                                      (reverse (coerce (car strings) 'list))))
            'string)))

(defun text-case-chars (chars lower upper offset)
  (if (endp chars)
      nil
    (let ((code (char-code (car chars))))
      (cons (if (and (<= lower code) (<= code upper))
                (code-char (+ code offset))
              (car chars))
            (text-case-chars (cdr chars) lower upper offset)))))

(defun text-upper (s)
  (coerce (text-case-chars (coerce s 'list) 97 122 -32) 'string))

(defun text-lower (s)
  (coerce (text-case-chars (coerce s 'list) 65 90 32) 'string))

(defun decimal-places (value place places)
  (declare (xargs :measure (nfix (- value place))))
  (let ((next (* 10 place))
        (ordered (cons place places)))
    (if (and (natp value) (posp place) (<= next value))
        (decimal-places value next ordered)
      ordered)))

; The remainder entering a decimal place is less than ten times that place.
(defun decimal-digit (n value place)
  (declare (xargs :measure (nfix n)))
  (if (or (zp n) (< value place))
      (cons (- 9 n) value)
    (decimal-digit (1- n) (- value place) place)))

(defun decimal-chars (places value)
  (if (endp places)
      nil
    (let ((digit (decimal-digit 9 value (car places))))
      (cons (code-char (+ 48 (car digit)))
            (decimal-chars (cdr places) (cdr digit))))))

(defun decimal-text (n)
  (let* ((value (abs n))
         (chars (decimal-chars (decimal-places value 1 nil) value)))
    (coerce (if (< n 0) (cons #\- chars) chars) 'string)))

(defun seq-slice-bound (bound default size)
  (cond ((not (integerp bound)) default)
        ((< bound 0) (max 0 (+ size bound)))
        (t (min size bound))))

(defun seq-slice (xs start stop)
  (let* ((size (length xs))
         (first (seq-slice-bound start 0 size))
         (last (seq-slice-bound stop size size)))
    (subseq xs first (max first last))))

(defun text-take-equal (width input substring)
  (cond ((zp width) (equal substring nil))
        ((atom substring) nil)
        ((equal (car input) (car substring))
         (text-take-equal (1- width) (cdr input) (cdr substring)))
        (t nil)))

(defun text-find-chars (input substring width index)
  (cond ((text-take-equal width input substring) index)
        ((endp input) -1)
        (t (text-find-chars (cdr input) substring width (1+ index)))))

(defun text-find (s substring)
  (let ((width (length substring)))
    (if (> width (length s))
        -1
      (text-find-chars (coerce s 'list) (coerce substring 'list) width 0))))

(defun text-space-p (c)
  (let ((code (char-code c)))
    (or (= code 32) (and (<= 9 code) (<= code 13))
        (and (<= 28 code) (<= code 31)))))

(defun text-strip-char-p (c chars)
  (if (eq chars :none)
      (text-space-p c)
    (if (member-equal c chars) t nil)))

(defun text-drop-chars (input chars)
  (if (and (consp input) (text-strip-char-p (car input) chars))
      (text-drop-chars (cdr input) chars)
    input))

(defun text-strip-left (s chars)
  (coerce (text-drop-chars (coerce s 'list)
                         (if (eq chars :none) :none (coerce chars 'list)))
          'string))

(defun text-strip-right (s chars)
  (coerce (reverse (text-drop-chars (reverse (coerce s 'list))
                                  (if (eq chars :none) :none (coerce chars 'list))))
          'string))

(defun text-strip (s chars)
  (text-strip-right (text-strip-left s chars) chars))

(defun text-split-separator (n input sep width maxsplit reversed)
  (declare (xargs :measure (nfix n)))
  (cond ((or (endp input) (= maxsplit 0) (zp n))
         (list (coerce (revappend reversed input) 'string)))
        ((text-take-equal width input sep)
         (cons (coerce (reverse reversed) 'string)
               (text-split-separator (1- n) (nthcdr width input) sep width (1- maxsplit) nil)))
        (t (text-split-separator (1- n) (cdr input) sep width maxsplit
                               (cons (car input) reversed)))))

(defun text-split-space-word (input maxsplit reversed)
  (declare (xargs :measure (acl2-count input)))
  (cond
   ((endp input)
    (if (endp reversed) nil (list (coerce (reverse reversed) 'string))))
   ((and (endp reversed) (= maxsplit 0))
    (let ((rest (text-drop-chars input :none)))
      (if (endp rest) nil (list (coerce rest 'string)))))
   ((text-space-p (car input))
    (if (endp reversed)
        (text-split-space-word (cdr input) maxsplit nil)
      (cons (coerce (reverse reversed) 'string)
            (text-split-space-word (cdr input) (1- maxsplit) nil))))
   (t (text-split-space-word (cdr input) maxsplit (cons (car input) reversed)))))

(defun text-split-max (s sep maxsplit)
  (cond ((eq sep :none) (text-split-space-word (coerce s 'list) maxsplit nil))
        ((equal sep "") '(:failure "value" ""))
        ((> (length sep) (length s)) (list s))
        (t (text-split-separator (length s) (coerce s 'list) (coerce sep 'list)
                               (length sep) maxsplit nil))))

(defun text-split (s sep)
  (text-split-max s sep -1))

(defun text-line-break-p (c)
  (let ((code (char-code c)))
    (or (and (<= 10 code) (<= code 13))
        (and (<= 28 code) (<= code 30)))))

(defun text-lines-chars (input reversed)
  (cond ((endp input)
         (if (consp reversed)
             (list (coerce (reverse reversed) 'string))
           nil))
        ((text-line-break-p (car input))
         (cons (coerce (reverse reversed) 'string)
               (text-lines-chars
                (if (and (eql (char-code (car input)) 13)
                         (consp (cdr input))
                         (eql (char-code (cadr input)) 10))
                    (cddr input)
                  (cdr input))
                nil)))
        (t (text-lines-chars (cdr input) (cons (car input) reversed)))))

(defun text-lines (s)
  (text-lines-chars (coerce s 'list) nil))

(defun text-replace-empty (input new)
  (if (endp input)
      (list new)
    (cons new
          (cons (coerce (list (car input)) 'string)
                (text-replace-empty (cdr input) new)))))

(defun text-replace (s old new)
  (if (equal old "")
      (text-join "" (text-replace-empty (coerce s 'list) new))
    (text-join new (text-split s old))))

(defun value-less (x y)
  (declare (xargs :measure (+ (acl2-count x) (acl2-count y))))
  (cond ((and (rationalp x) (rationalp y)) (< x y))
        ((and (stringp x) (stringp y)) (if (string< x y) t nil))
        ((and (consp x) (consp y))
         (if (equal (car x) (car y))
             (value-less (cdr x) (cdr y))
           (value-less (car x) (car y))))
        (t (and (null x) (consp y)))))

(defun seq-insert-sorted (x xs)
  (if (and (consp xs) (value-less (car xs) x))
      (cons (car xs) (seq-insert-sorted x (cdr xs)))
    (cons x xs)))

(defun seq-sorted (xs)
  (if (endp xs)
      nil
    (seq-insert-sorted (car xs) (seq-sorted (cdr xs)))))

(defun seq-zip (xs ys)
  (if (or (endp xs) (endp ys))
      nil
    (cons (list (car xs) (car ys)) (seq-zip (cdr xs) (cdr ys)))))

(defun seq-numbered (xs start)
  (if (endp xs)
      nil
    (cons (list start (car xs)) (seq-numbered (cdr xs) (1+ start)))))

(defun seq-range-count (n start step)
  (declare (xargs :measure (nfix n)))
  (if (zp n)
      nil
    (cons start (seq-range-count (1- n) (+ start step) step))))

(defun seq-range (start stop step)
  (if (= step 0)
      '(:failure "value" "")
    (seq-range-count (ceiling (- stop start) step) start step)))

(defun text-quoted-chars (chars quote-char)
  (if (endp chars)
      nil
    (let* ((c (car chars))
           (code (char-code c))
           (rest (text-quoted-chars (cdr chars) quote-char)))
      (cond ((or (eql c quote-char) (eql c #\\)) (list* #\\ c rest))
            ((= code 9) (list* #\\ #\t rest))
            ((= code 10) (list* #\\ #\n rest))
            ((= code 13) (list* #\\ #\r rest))
            ((and (<= 32 code) (<= code 126)) (cons c rest))
            (t (list* #\\ #\x
                      (char "0123456789abcdef" (floor code 16))
                      (char "0123456789abcdef" (mod code 16))
                      rest))))))

(defun text-quoted (s)
  (let* ((chars (coerce s 'list))
         (quote-char (if (and (member-equal #\' chars)
                              (not (member-equal #\" chars)))
                         #\"
                       #\')))
    (coerce (cons quote-char
                  (append (text-quoted-chars chars quote-char)
                          (list quote-char)))
            'string)))

(defun seq-index-from (xs x index)
  (cond ((endp xs) -1)
        ((equal (car xs) x) index)
        (t (seq-index-from (cdr xs) x (1+ index)))))

(defun seq-index (xs x)
  (let ((index (seq-index-from xs x 0)))
    (if (< index 0)
        (list :failure "value" "")
      index)))

(defun table-get (d key default)
  (let ((entry (assoc-equal key d)))
    (if entry (cdr entry) default)))

(defun table-put (d key value)
  (cond ((endp d) (list (cons key value)))
        ((equal key (caar d)) (cons (cons key value) (cdr d)))
        (t (cons (car d) (table-put (cdr d) key value)))))

(defun table-without (d key)
  (cond ((endp d) nil)
        ((equal key (caar d)) (cdr d))
        (t (cons (car d) (table-without (cdr d) key)))))

(defun table-delete (d key)
  (if (assoc-equal key d)
      (table-without d key)
    (list :failure "key" "")))

(defun table-keys (d)
  (if (endp d) nil (cons (caar d) (table-keys (cdr d)))))

(defun table-values (d)
  (if (endp d) nil (cons (cdar d) (table-values (cdr d)))))

(defun table-items (d)
  (if (endp d)
      nil
    (cons (list (caar d) (cdar d)) (table-items (cdr d)))))

(defun table-update (d other)
  (if (endp other)
      d
    (table-update (table-put d (caar other) (cdar other)) (cdr other))))
