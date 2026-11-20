; Benchmark: sorting.  A merge sort of a permutation of the integers
; below 20,000, ten times.

(in-package "ACL2")

(defun bench-perm (i x n acc)
  (declare (xargs :guard (and (natp i) (natp x) (natp n))))
  (if (zp i)
      acc
    (bench-perm (- i 1) (if (< (+ x 7919) n) (+ x 7919) (- (+ x 7919) n)) n
                (cons x acc))))

(defun bench-evens (l)
  (declare (xargs :guard (true-listp l)))
  (if (endp l) nil (cons (car l) (bench-evens (cddr l)))))

(defun bench-merge (a b)
  (declare (xargs :guard (and (integer-listp a) (integer-listp b))
                  :measure (+ (len a) (len b))))
  (cond ((endp a) b)
        ((endp b) a)
        ((< (car b) (car a)) (cons (car b) (bench-merge a (cdr b))))
        (t (cons (car a) (bench-merge (cdr a) b)))))

(defthm bench-integer-listp-evens
  (implies (integer-listp l) (integer-listp (bench-evens l)))
  :hints (("Goal" :induct (bench-evens l))))

(defthm bench-integer-listp-merge
  (implies (and (integer-listp a) (integer-listp b))
           (integer-listp (bench-merge a b))))

; DEPTH bounds the depth of the recursion, which halves the list each
; time; 64 levels are enough for any list that fits in memory.
(defun bench-msort (l depth)
  (declare (xargs :guard (and (integer-listp l) (natp depth)) :measure (nfix depth)
                  :verify-guards nil))
  (if (or (zp depth) (endp l) (endp (cdr l)))
      l
    (bench-merge (bench-msort (bench-evens l) (- depth 1))
                 (bench-msort (bench-evens (cdr l)) (- depth 1)))))

(defthm bench-integer-listp-msort
  (implies (integer-listp l) (integer-listp (bench-msort l depth))))

(verify-guards bench-msort)

(defthm bench-integer-listp-perm
  (implies (and (integer-listp acc) (integerp x) (integerp n))
           (integer-listp (bench-perm i x n acc))))

(defun bench-sort-of (k l acc)
  (declare (xargs :guard (and (natp k) (integer-listp l))))
  (if (zp k) acc (bench-sort-of (- k 1) l (bench-msort l 64))))

(defun bench-sort ()
  (declare (xargs :guard t))
  (let ((s (bench-sort-of 10 (bench-perm 20000 0 20000 nil) nil)))
    (list (car s) (cadr s) (nth 19999 s))))
