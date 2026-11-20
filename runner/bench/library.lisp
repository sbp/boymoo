; Benchmark: functions of ACL2's own library.  Three hundred times, a
; list of 350 numbers is built with make-list-ac and append, its
; duplicates removed, paired with its reverse by pairlis$, looked up with
; assoc-equal, and forty of its members written as strings with
; explode-nonnegative-integer and string-append.

(in-package "ACL2")

(defun bench-numbers (n acc)
  (declare (xargs :guard (natp n)))
  (if (zp n) acc (bench-numbers (- n 1) (cons n acc))))

(defthm bench-true-listp-numbers
  (implies (true-listp acc) (true-listp (bench-numbers n acc))))

(defthm bench-characterp-digit-to-char
  (characterp (digit-to-char n)))

(defthm bench-character-listp-explode
  (implies (character-listp ans)
           (character-listp (explode-nonnegative-integer n base ans)))
  :hints (("Goal" :induct (explode-nonnegative-integer n base ans))))

(defun bench-strings (l acc)
  (declare (xargs :guard (and (true-listp l) (stringp acc))))
  (if (endp l)
      acc
    (bench-strings (cdr l)
                   (string-append acc (coerce (explode-nonnegative-integer (nfix (car l)) 10 nil)
                                              'string)))))

(defthm bench-stringp-strings
  (implies (stringp acc) (stringp (bench-strings l acc))))

(defthm bench-true-listp-make-list-ac
  (implies (true-listp ac) (true-listp (make-list-ac n val ac))))

(defthm bench-alistp-pairlis$
  (alistp (pairlis$ x y)))

(defun bench-library-of (k acc)
  (declare (xargs :guard (and (natp k) (natp acc))))
  (if (zp k)
      acc
    (let* ((l (append (make-list-ac 50 k nil) (bench-numbers 300 nil)))
           (u (remove-duplicates-equal l))
           (al (pairlis$ u (reverse u)))
           (s (bench-strings (take 40 u) ""))
           (p (assoc-equal 150 al)))
      (bench-library-of (- k 1)
                        (+ acc (len u) (if (consp p) (nfix (cdr p)) 0) (length s))))))

(defun bench-library () (declare (xargs :guard t)) (bench-library-of 300 0))
