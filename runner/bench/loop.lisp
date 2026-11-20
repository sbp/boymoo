; Benchmark: a loop in the last position, ten million steps of a sequence
; of Fibonacci numbers kept below a million by subtraction.

(in-package "ACL2")

(defun bench-loop-of (n a b)
  (declare (xargs :guard (and (natp n) (natp a) (natp b))))
  (if (zp n)
      a
    (bench-loop-of (- n 1) b (if (< 1000000 (+ a b)) (- (+ a b) 1000000) (+ a b)))))

(defun bench-loop () (declare (xargs :guard t)) (bench-loop-of 10000000 0 1))
