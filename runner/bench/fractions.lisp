; Benchmark: fractions.  The sum of 1/i for i from 1 to 1,500, a
; fraction whose numerator and denominator have about 650 digits each.

(in-package "ACL2")

(defun bench-harmonic (n acc)
  (declare (xargs :guard (and (natp n) (rationalp acc))))
  (if (zp n) acc (bench-harmonic (- n 1) (+ acc (/ n)))))

(defun bench-fractions () (declare (xargs :guard t)) (bench-harmonic 1500 0))
