; A book of the cases at which a runner must stop, and of a few it must
; run, for the tests of the reference runner (runner/test.sh).  The test
; certifies it into build/runner/test/ and exports it with
; export/book.sh; ACL2 computes the value of each call that
; runner/test/gen.py lists for it.

(in-package "ACL2")

; A constrained function with no attachment, and a function that calls it.
(encapsulate (((rt-three *) => *))
  (local (defun rt-three (x) (declare (ignore x)) 3))
  (defthm rt-three-is-3 (equal (rt-three x) 3)))
(defun rt-three-user (x) (cons (rt-three x) x))

; An attachment in force, and a function that calls the constrained
; function.
(defstub rt-s (x) t)
(defun rt-s-impl (x) (declare (xargs :guard t)) (cons x x))
(defattach rt-s rt-s-impl)
(defun rt-s-user (x) (list (rt-s x)))

; hard-error and illegal, reached and not reached; a function that is
; not executable; a function introduced by choice.
(defun rt-he (x) (if (consp x) (hard-error 'rt "RT" nil) x))
(defun rt-il (x) (if (consp x) (illegal 'rt "RT" nil) x))
(defun-nx rt-nx (x) (cons x x))
(defchoose rt-ch (y) (x) (equal y x))

; An mbe whose halves agree, with its guards verified.
(defun rt-mbe (x)
  (declare (xargs :guard t))
  (mbe :logic (if (consp x) (car x) nil) :exec (and (consp x) (car x))))

; Recursion that is not in the last position, a loop that is, mutual
; recursion, and a function in program mode with an mbe.
(defun rt-deep (n) (if (zp n) 0 (+ 1 (rt-deep (- n 1)))))
(defun rt-loop (n acc) (if (zp n) acc (rt-loop (- n 1) (+ acc 1))))
(mutual-recursion
 (defun rt-ev (n) (if (zp n) t (rt-od (- n 1))))
 (defun rt-od (n) (if (zp n) nil (rt-ev (- n 1)))))
(defun rt-pm (x)
  (declare (xargs :mode :program))
  (mbe :logic (list 'logic x) :exec (list 'exec x)))
