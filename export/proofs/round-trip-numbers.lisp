; Inversion of the decimal runs that stand for rational numbers.

(in-package "ACL2")

(include-book "round-trip-text")
(local (include-book "ihs/quotient-remainder-lemmas" :dir :system))
(local (include-book "arithmetic-5/lib/basic-ops/numerator-and-denominator"
                     :dir :system))

(local (in-theory (disable floor mod rt-plain-char-p)))

; The positive part of a decimal numeral, followed by a given suffix.
; At zero it returns the suffix. The numeral for zero is handled separately.
(local
 (defun rt-decimal-prefix (n suffix)
   (declare (xargs :measure (nfix n)))
   (if (zp n)
       suffix
     (rt-decimal-prefix (floor n 10)
                        (cons (digit-to-char (mod n 10)) suffix)))))

(local
 (defthm rt-explode-to-decimal-prefix
   (equal (explode-nonnegative-integer n 10 suffix)
          (if (and (zp n) (not suffix))
              '(#\0)
            (rt-decimal-prefix n suffix)))))

(local
 (defthm rt-decimal-digit
   (implies (and (natp d) (< d 10))
            (and (characterp (digit-to-char d))
                 (equal (char-code (digit-to-char d)) (+ 48 d))
                 (equal (equal (digit-to-char d) #\0) (equal d 0))
                 (not (equal (digit-to-char d) #\-))
                 (not (equal (digit-to-char d) #\/))
                 (rt-plain-char-p (digit-to-char d))))
   :hints (("Goal" :in-theory (enable digit-to-char rt-plain-char-p)))))

(local (in-theory (disable digit-to-char explode-nonnegative-integer)))

; The recurrence for scanning a digit undoes the quotient and remainder
; step that produced it. The decimal numeral of a positive number is
; nonempty and has a nonzero first digit.
(local
 (defthm rt-digits-value-of-decimal-prefix
   (implies (natp n)
            (equal (boymoo::digits-value (rt-decimal-prefix n suffix) 0)
                   (boymoo::digits-value suffix n)))
   :hints (("Goal" :induct (rt-decimal-prefix n suffix)))))

(local
 (defthm rt-decimal-prefix-leading-digit
   (implies (posp n)
            (and (consp (rt-decimal-prefix n suffix))
                 (not (equal (car (rt-decimal-prefix n suffix)) #\0))
                 (not (equal (car (rt-decimal-prefix n suffix)) #\-))))
   :hints (("Goal" :induct (rt-decimal-prefix n suffix)))))

(local
 (defthm rt-positive-value-of-decimal
   (implies (posp n)
            (equal (boymoo::positive-value
                    (explode-nonnegative-integer n 10 nil))
                   n))
   :hints (("Goal" :in-theory (disable rt-decimal-prefix)))))

(local
 (defthm rt-decimal-is-not-a-single-zero
   (implies (posp n)
            (not (equal (explode-nonnegative-integer n 10 nil) '(#\0))))
   :hints (("Goal"
            :use ((:instance rt-decimal-prefix-leading-digit (suffix nil)))
            :in-theory (disable rt-decimal-prefix
                                rt-decimal-prefix-leading-digit)))))

(local
 (defthm rt-decimal-first-not-minus
   (not (equal (car (explode-nonnegative-integer n 10 nil)) #\-))
   :hints (("Goal" :in-theory (disable rt-decimal-prefix)))))

; A decimal numeral is a plain run, has no slash, and is a true list.
(local
 (defun rt-no-slash-p (cs)
   (if (consp cs)
       (and (not (equal (car cs) #\/))
            (rt-no-slash-p (cdr cs)))
     (equal cs nil))))

(local
 (defthm rt-decimal-prefix-is-plain
   (implies (rt-all-plain-p suffix)
            (rt-all-plain-p (rt-decimal-prefix n suffix)))))

(local
 (defthm rt-decimal-prefix-has-no-slash
   (implies (rt-no-slash-p suffix)
            (rt-no-slash-p (rt-decimal-prefix n suffix)))))

(local
 (defthm rt-decimal-is-plain
   (rt-all-plain-p (explode-nonnegative-integer n 10 nil))
   :hints (("Goal" :in-theory (disable rt-decimal-prefix)))))

(local
 (defthm rt-decimal-has-no-slash
   (rt-no-slash-p (explode-nonnegative-integer n 10 nil))
   :hints (("Goal" :in-theory (disable rt-decimal-prefix)))))

(local
 (defthm rt-decimal-consp
   (consp (explode-nonnegative-integer n 10 nil))
   :hints (("Goal" :in-theory (disable rt-decimal-prefix)))))

(local
 (defthm rt-decimal-prefix-characters
   (implies (character-listp suffix)
            (character-listp (rt-decimal-prefix n suffix)))))

(local
 (defthm rt-decimal-characters
   (character-listp (explode-nonnegative-integer n 10 nil))
   :hints (("Goal" :in-theory (disable rt-decimal-prefix)))))

(local (in-theory (disable rt-explode-to-decimal-prefix)))

(defund rt-integer-text (i)
  (if (< i 0)
      (cons #\- (explode-nonnegative-integer (- i) 10 nil))
    (explode-nonnegative-integer i 10 nil)))

(defund rt-rational-text (r)
  (if (integerp r)
      (rt-integer-text r)
    (append (rt-integer-text (numerator r))
            (cons #\/ (explode-nonnegative-integer (denominator r) 10 nil)))))

; The reverse accumulators of the three number printers.
(local
 (defthm rt-print-integer
   (equal (bm-int i acc) (revappend (rt-integer-text i) acc))
   :hints (("Goal" :in-theory (enable rt-integer-text)))))

(defthm rt-print-rational
  (implies (rationalp r)
           (equal (bm-rat r acc) (revappend (rt-rational-text r) acc)))
  :hints (("Goal" :in-theory (e/d (rt-rational-text) (bm-int)))))

; The integer scanner is used on both sides of the optional slash.
(local
 (defthm rt-integer-value-of-text
   (implies (integerp i)
            (equal (boymoo::integer-value (rt-integer-text i)) i))
   :hints (("Goal" :cases ((equal i 0))
            :in-theory (e/d (rt-integer-text)
                                    (rt-explode-to-decimal-prefix
                                     boymoo::positive-value))))))

(local
 (defthm rt-integer-has-no-slash
   (rt-no-slash-p (rt-integer-text i))
   :hints (("Goal" :in-theory (enable rt-integer-text)))))

(local
 (defthm rt-integer-text-true-listp
   (true-listp (rt-integer-text i))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (enable rt-integer-text)))))

(local
 (defthm rt-split-slash-of-prefix
   (implies (rt-no-slash-p cs)
            (equal (boymoo::split-slash (append cs tail) acc)
                   (boymoo::split-slash tail (revappend cs acc))))
   :hints (("Goal" :induct (revappend cs acc)))))

(local
 (defthm rt-split-slash-of-integer-text
   (equal (boymoo::split-slash (rt-integer-text i) nil)
          (cons (rt-integer-text i) :none))
   :hints (("Goal" :use ((:instance rt-split-slash-of-prefix
                                     (cs (rt-integer-text i)) (tail nil)
                                     (acc nil)))
            :in-theory (disable rt-split-slash-of-prefix)))))

(local
 (defthm rt-split-slash-of-fraction-text
   (equal (boymoo::split-slash
           (append (rt-integer-text i) (cons #\/ tail)) nil)
          (cons (rt-integer-text i) tail))
   :hints (("Goal" :use ((:instance rt-split-slash-of-prefix
                                     (cs (rt-integer-text i))
                                     (tail (cons #\/ tail)) (acc nil)))
            :in-theory (disable rt-split-slash-of-prefix)))))

; ACL2's numerator and denominator give the number in lowest terms.
(defthm rt-number-value-of-rational-text
  (implies (rationalp r)
           (equal (boymoo::number-value (rt-rational-text r)) (list r)))
  :hints (("Goal" :use ((:instance rational-implies2 (x r)))
           :in-theory (e/d (rt-rational-text)
                            (boymoo::split-slash boymoo::positive-value
                             boymoo::integer-value rt-explode-to-decimal-prefix
                             rational-implies2)))))

(local
 (defthm rt-all-plain-of-append
   (equal (rt-all-plain-p (append x y))
          (and (rt-all-plain-p x) (rt-all-plain-p y)))))

(defthm rt-rational-text-is-plain
  (rt-all-plain-p (rt-rational-text r))
  :hints (("Goal" :in-theory (enable rt-rational-text rt-integer-text
                                    rt-plain-char-p)
           :do-not-induct t)))

(defthm rt-rational-text-consp
  (consp (rt-rational-text r))
  :hints (("Goal" :in-theory (enable rt-rational-text rt-integer-text)
           :do-not-induct t)))

(defthm rt-rational-text-characters
  (character-listp (rt-rational-text r))
  :hints (("Goal" :in-theory (enable rt-rational-text rt-integer-text))))

(defthm rt-rational-text-first-plain
  (rt-plain-char-p (car (rt-rational-text r)))
  :hints (("Goal" :use ((:instance rt-all-plain-first (cs (rt-rational-text r)))))))

; For the converse, extending a positive decimal accumulation by a
; digit puts that same digit at the end of the numeral.
(local
 (defthm rt-decimal-prefix-inserts-digit
   (implies (and (natp n) (natp d) (< d 10) (< 0 (+ (* 10 n) d)))
            (equal (rt-decimal-prefix (+ (* 10 n) d) suffix)
                   (rt-decimal-prefix n (cons (digit-to-char d) suffix))))
   :hints (("Goal" :expand ((rt-decimal-prefix (+ d (* 10 n)) suffix)
                             (mod (+ d (* 10 n)) 10))
            :use ((:instance cancel-floor-+-basic (i n) (x (* 10 n)) (y d) (z 10)))
            :in-theory (disable rt-decimal-prefix cancel-floor-+-basic)))))

(local
 (defthm rt-digit-to-char-recovers-digit
   (implies (and (characterp c) (<= 48 (char-code c)) (< (char-code c) 58))
            (equal (digit-to-char (- (char-code c) 48)) c))
   :hints (("Goal" :use ((:instance rt-equal-char-codes
                                     (x (digit-to-char (- (char-code c) 48)))
                                     (y c)))
            :in-theory (disable rt-equal-char-codes)))))

(local
 (defthm rt-decimal-prefix-inserts-character
   (implies (and (natp n) (characterp c) (<= 48 (char-code c)) (< (char-code c) 58)
                 (< 0 (+ -48 (* 10 n) (char-code c))))
            (equal (rt-decimal-prefix (+ -48 (* 10 n) (char-code c)) suffix)
                   (rt-decimal-prefix n (cons c suffix))))
   :hints (("Goal" :use ((:instance rt-decimal-prefix-inserts-digit
                                     (d (- (char-code c) 48))))
            :in-theory (disable rt-decimal-prefix rt-decimal-prefix-inserts-digit)))))

(local
 (defthm rt-decimal-prefix-of-scanned-digits
   (implies (and (posp n) (boymoo::digits-value cs n))
            (and (posp (boymoo::digits-value cs n))
                 (equal (rt-decimal-prefix (boymoo::digits-value cs n) suffix)
                        (rt-decimal-prefix n (append cs suffix)))))
   :hints (("Goal" :induct (boymoo::digits-value cs n)
            :in-theory (disable rt-decimal-prefix)
            :do-not '(generalize fertilize)))))

(local
 (defthm rt-code-of-zero-digit
   (implies (characterp c)
            (equal (equal (char-code c) 48) (equal c #\0)))
   :hints (("Goal" :use ((:instance rt-equal-char-codes (x c) (y #\0)))
            :in-theory (disable rt-equal-char-codes)))))

(local
 (defthm rt-positive-value-of-run
   (implies (and (true-listp cs) (boymoo::positive-value cs))
            (let ((v (boymoo::positive-value cs)))
              (and (integerp v) (< 0 v)
                   (equal (explode-nonnegative-integer v 10 nil) cs))))
   :hints (("Goal" :in-theory (e/d (rt-explode-to-decimal-prefix)
                                    (rt-decimal-prefix-inserts-character
                                     rt-decimal-prefix-of-scanned-digits))
            :use ((:instance rt-decimal-prefix-inserts-character
                             (n 0) (c (car cs)) (suffix (cdr cs)))
                  (:instance rt-decimal-prefix-of-scanned-digits
                             (n (- (char-code (car cs)) 48))
                             (cs (cdr cs)) (suffix nil)))
            :expand ((boymoo::digits-value cs 0))
            :do-not-induct t))))

(local
 (defthm rt-double-negation-of-an-integer
   (implies (integerp i) (equal (- (- i)) i))))

(local
 (defthm rt-integer-value-of-run
   (implies (and (true-listp cs) (boymoo::integer-value cs))
            (let ((v (boymoo::integer-value cs)))
              (and (integerp v) (equal (rt-integer-text v) cs))))
   :hints (("Goal" :use (rt-positive-value-of-run
                        (:instance rt-positive-value-of-run (cs (cdr cs))))
            :in-theory (e/d (rt-integer-text)
                             (boymoo::positive-value rt-positive-value-of-run))
            :do-not-induct t))))

; Splitting a run records the original text on both sides of the slash.
(local
 (defthm rt-split-slash-keeps-text
   (implies (true-listp cs)
            (let ((split (boymoo::split-slash cs acc)))
              (and (true-listp (car split))
                   (if (equal (cdr split) :none)
                       (equal (car split) (revappend acc cs))
                     (and (true-listp (cdr split))
                          (equal (revappend acc cs)
                                 (append (car split) (cons #\/ (cdr split)))))))))
   :hints (("Goal" :induct (boymoo::split-slash cs acc)))))

(local
 (defthm rt-fraction-has-its-written-numerator
   (implies (and (integerp num) (posp den)
                 (equal (denominator (* num (/ den))) den))
            (equal (numerator (* num (/ den))) num))
   :hints (("Goal" :use ((:instance |(* r (denominator r))| (r (* num (/ den)))))
            :in-theory (disable |(* r (denominator r))|)))))

(defthm rt-read-rational-is-canonical
  (implies (and (true-listp run) (boymoo::number-value run))
           (let* ((result (boymoo::number-value run))
                  (value (car result)))
             (and (rationalp value)
                  (equal result (list value))
                  (equal (rt-rational-text value) run))))
  :rule-classes nil
  :hints (("Goal" :use ((:instance rt-split-slash-keeps-text (cs run) (acc nil))
                        (:instance rt-integer-value-of-run (cs run))
                        (:instance rt-integer-value-of-run
                                   (cs (car (boymoo::split-slash run nil))))
                        (:instance rt-positive-value-of-run
                                   (cs (cdr (boymoo::split-slash run nil)))))
           :in-theory (e/d (rt-rational-text)
                            (rt-split-slash-keeps-text boymoo::split-slash
                             boymoo::integer-value boymoo::positive-value
                             rt-integer-value-of-run rt-positive-value-of-run))
           :do-not-induct t)))

(in-theory (disable bm-rat boymoo::number-value))
