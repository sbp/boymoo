; Benchmark: characters and strings.  A string of 200,000 letters is made
; from a list of characters, taken apart again, put in upper case by
; arithmetic on the codes, and the letters E are counted; ten times.

(in-package "ACL2")

(defun bench-letters (n c acc)
  (declare (xargs :guard (and (natp n) (natp c) (< c 26))))
  (if (zp n)
      acc
    (bench-letters (- n 1) (if (< c 25) (+ c 1) 0) (cons (code-char (+ 97 c)) acc))))

(defun bench-upcase (l)
  (declare (xargs :guard (character-listp l)))
  (if (endp l)
      nil
    (cons (let ((k (char-code (car l))))
            (if (and (<= 97 k) (<= k 122)) (code-char (- k 32)) (car l)))
          (bench-upcase (cdr l)))))

(defun bench-count (c l acc)
  (declare (xargs :guard (and (characterp c) (character-listp l) (natp acc))))
  (if (endp l) acc (bench-count c (cdr l) (if (eql c (car l)) (+ 1 acc) acc))))

(defthm bench-natp-count
  (implies (natp acc) (natp (bench-count c l acc)))
  :rule-classes :type-prescription)

(defthm bench-character-listp-letters
  (implies (character-listp acc) (character-listp (bench-letters n c acc))))

(defthm bench-character-listp-upcase
  (implies (character-listp l) (character-listp (bench-upcase l))))

(defun bench-chars-of (k s acc)
  (declare (xargs :guard (and (natp k) (stringp s) (natp acc))))
  (if (zp k)
      acc
    (bench-chars-of (- k 1) s
                    (bench-count #\E (coerce (coerce (bench-upcase (coerce s 'list)) 'string) 'list)
                                 acc))))

(defun bench-chars ()
  (declare (xargs :guard t))
  (bench-chars-of 10 (coerce (bench-letters 200000 0 nil) 'string) 0))
