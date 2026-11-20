; Benchmark: large integers.  7 to the power 40,000, by 40,000
; multiplications; it has 33,804 digits.

(in-package "ACL2")

(defun bench-pow (b e)
  (declare (xargs :guard (and (integerp b) (natp e))))
  (if (zp e) 1 (* b (bench-pow b (- e 1)))))

(defun bench-power () (declare (xargs :guard t)) (bench-pow 7 40000))
