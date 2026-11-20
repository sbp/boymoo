; Benchmark: symbols.  1,500 symbols are made from their names with
; intern-in-package-of-symbol, and sorted by name by insertion, comparing
; the characters of their names.

(in-package "ACL2")

; A name is counted up as a list of digits from 0 to 25, the least
; significant first, and written as letters in that order.
(defun bench-next (l)
  (declare (xargs :guard (nat-listp l)))
  (cond ((endp l) (list 0))
        ((< (car l) 25) (cons (+ 1 (car l)) (cdr l)))
        (t (cons 0 (bench-next (cdr l))))))

(defun bench-letters-of (l)
  (declare (xargs :guard (nat-listp l)))
  (if (endp l) nil (cons (code-char (min 255 (+ 65 (car l)))) (bench-letters-of (cdr l)))))

(defun bench-chars< (a b)
  (declare (xargs :guard (and (character-listp a) (character-listp b))))
  (cond ((endp b) nil)
        ((endp a) t)
        ((char< (car a) (car b)) t)
        ((char< (car b) (car a)) nil)
        (t (bench-chars< (cdr a) (cdr b)))))

(defun bench-sym< (a b)
  (declare (xargs :guard (and (symbolp a) (symbolp b))))
  (bench-chars< (coerce (symbol-name a) 'list) (coerce (symbol-name b) 'list)))

(defun bench-insert (s l)
  (declare (xargs :guard (and (symbolp s) (symbol-listp l))))
  (cond ((endp l) (list s))
        ((bench-sym< s (car l)) (cons s l))
        (t (cons (car l) (bench-insert s (cdr l))))))

(defthm bench-nat-listp-next
  (implies (nat-listp l) (nat-listp (bench-next l))))

(defthm bench-character-listp-letters-of
  (character-listp (bench-letters-of l)))

(defthm bench-symbol-listp-insert
  (implies (and (symbolp s) (symbol-listp l)) (symbol-listp (bench-insert s l))))

(defun bench-make (n name acc)
  (declare (xargs :guard (and (natp n) (nat-listp name) (symbol-listp acc))))
  (if (zp n)
      acc
    (bench-make (- n 1) (bench-next name)
                (bench-insert (intern-in-package-of-symbol
                               (coerce (bench-letters-of name) 'string) 'bench-make)
                              acc))))

(defun bench-symbols ()
  (declare (xargs :guard t))
  (let ((l (bench-make 1500 nil nil)))
    (list (len l) (car l) (nth 750 l) (nth 1499 l))))
