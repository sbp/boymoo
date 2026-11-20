; Benchmark: recursion on integers, the doubly recursive Fibonacci function.

(in-package "ACL2")

(defun bench-fib-of (n)
  (declare (xargs :guard (natp n)))
  (if (zp n) 0 (if (= n 1) 1 (+ (bench-fib-of (- n 1)) (bench-fib-of (- n 2))))))

(defun bench-fib () (declare (xargs :guard t)) (bench-fib-of 30))
