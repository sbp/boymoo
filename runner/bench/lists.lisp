; Benchmark: building and walking lists: two hundred times, the list of
; the integers from 1 to 10,000 is built, reversed, doubled by a
; recursion that is not in the last position, and summed.

(in-package "ACL2")

(defun bench-iota (n acc)
  (declare (xargs :guard (natp n)))
  (if (zp n) acc (bench-iota (- n 1) (cons n acc))))

(defun bench-rev (l acc)
  (declare (xargs :guard (true-listp l)))
  (if (endp l) acc (bench-rev (cdr l) (cons (car l) acc))))

(defun bench-double (l)
  (declare (xargs :guard (integer-listp l)))
  (if (endp l) nil (cons (* 2 (car l)) (bench-double (cdr l)))))

(defun bench-sum (l acc)
  (declare (xargs :guard (and (integer-listp l) (integerp acc))))
  (if (endp l) acc (bench-sum (cdr l) (+ acc (car l)))))

(defthm bench-integer-listp-iota
  (implies (integer-listp acc) (integer-listp (bench-iota n acc))))

(defthm bench-integer-listp-rev
  (implies (and (integer-listp l) (integer-listp acc))
           (integer-listp (bench-rev l acc))))

(defthm bench-integer-listp-double
  (implies (integer-listp l) (integer-listp (bench-double l))))

(defthm bench-integerp-sum
  (implies (and (integer-listp l) (integerp acc)) (integerp (bench-sum l acc))))

(defun bench-lists-of (k n acc)
  (declare (xargs :guard (and (natp k) (natp n) (integerp acc))))
  (if (zp k)
      acc
    (bench-lists-of (- k 1) n
                    (bench-sum (bench-double (bench-rev (bench-iota n nil) nil)) acc))))

(defun bench-lists () (declare (xargs :guard t)) (bench-lists-of 200 10000 0))
