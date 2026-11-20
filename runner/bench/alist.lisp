; Benchmark: association lists.  An alist of 3,000 keys, each key looked
; up in turn.

(in-package "ACL2")

(defun bench-squares (n acc)
  (declare (xargs :guard (and (natp n) (alistp acc))))
  (if (zp n) acc (bench-squares (- n 1) (cons (cons n (* n n)) acc))))

(defun bench-lookup (k al)
  (declare (xargs :guard (alistp al)))
  (cond ((endp al) nil)
        ((equal k (car (car al))) (car al))
        (t (bench-lookup k (cdr al)))))

(defun bench-sum-lookups (n al acc)
  (declare (xargs :guard (and (natp n) (alistp al) (acl2-numberp acc))))
  (if (zp n)
      acc
    (bench-sum-lookups (- n 1) al (+ acc (fix (cdr (bench-lookup n al)))))))

(defthm bench-alistp-squares
  (implies (alistp acc) (alistp (bench-squares n acc))))

(defun bench-alist ()
  (declare (xargs :guard t))
  (bench-sum-lookups 3000 (bench-squares 3000 nil) 0))
