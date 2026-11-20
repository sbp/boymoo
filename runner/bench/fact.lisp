; Benchmark: large integers.  The factorial of 6,000, which has 20,066
; digits.

(in-package "ACL2")

(defun bench-fact-of (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) 1 (* n (bench-fact-of (- n 1)))))

(defun bench-fact () (declare (xargs :guard t)) (bench-fact-of 6000))
