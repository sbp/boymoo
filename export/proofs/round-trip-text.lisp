; Character lists and the two ways of writing a symbol part.

(in-package "ACL2")

(include-book "canon")
(include-book "read")

; The reader and the printer use the same list operations.
(defthm rt-app-is-append
  (equal (boymoo::app x y) (append x y)))

(defthm rt-rev-onto-is-revappend
  (equal (boymoo::rev-onto x acc) (revappend x acc)))

(defthm rt-rev-is-revappend
  (equal (boymoo::rev x) (revappend x nil)))

(defthm rt-append-associative
  (equal (append (append x y) z) (append x (append y z))))

(defthm rt-append-nil
  (implies (true-listp x) (equal (append x nil) x)))

(defthm rt-append-characters
  (implies (and (character-listp x) (character-listp y))
           (character-listp (append x y))))

(defthm rt-revappend-of-append
  (equal (revappend (append x y) z)
         (revappend y (revappend x z))))

(defthm rt-append-of-revappend
  (equal (append (revappend x y) z)
         (revappend x (append y z))))

(defthm rt-revappend-of-revappend
  (equal (revappend (revappend x y) z)
         (revappend y (append x z))))

(defthm rt-consp-of-append
  (equal (consp (append x y)) (or (consp x) (consp y))))

(defthm rt-car-of-append
  (equal (car (append x y)) (if (consp x) (car x) (car y))))

(defthm rt-consp-of-revappend
  (equal (consp (revappend x y)) (or (consp x) (consp y))))

(defthm rt-len-of-append
  (equal (len (append x y)) (+ (len x) (len y))))

(in-theory (disable boymoo::app boymoo::rev-onto boymoo::rev))

; The alphabet and the hexadecimal notation of spec/formats.md, section 2.
(defun rt-plain-char-p (c)
  (and (characterp c)
       (let ((n (char-code c)))
         (or (and (<= 65 n) (<= n 90))
             (and (<= 48 n) (<= n 57))
             (if (member-equal c '(#\- #\+ #\* #\/ #\< #\= #\> #\! #\?
                                   #\$ #\% #\& #\_ #\^ #\~ #\. #\@))
                 t nil)))))

(defun rt-all-plain-p (cs)
  (if (consp cs)
      (and (rt-plain-char-p (car cs)) (rt-all-plain-p (cdr cs)))
    t))

(defthm rt-all-plain-first
  (implies (and (consp cs) (rt-all-plain-p cs))
           (rt-plain-char-p (car cs)))
  :rule-classes ((:forward-chaining :trigger-terms ((rt-all-plain-p cs)))))

(defun rt-hex-digit (n)
  (code-char (+ n (if (< n 10) 48 55))))

(defund rt-hex-high (n)
  (rt-hex-digit (floor n 16)))

(defund rt-hex-low (n)
  (rt-hex-digit (mod n 16)))

; Exhaust the 256 character codes to compare the two alphabets and the
; hexadecimal conversions with the specification.
(local
 (defun rt-byte-check (n)
   (let ((c (code-char n))
         (hi (rt-hex-high n))
         (lo (rt-hex-low n)))
     (and (iff (bm-plain-charp c) (rt-plain-char-p c))
          (equal (boymoo::plain-char-p c) (rt-plain-char-p c))
          (equal (bm-hex2 n) (list hi lo))
          (natp (boymoo::hex-value hi))
          (natp (boymoo::hex-value lo))
          (equal (+ (* 16 (boymoo::hex-value hi))
                    (boymoo::hex-value lo))
                 n)))))

(local
 (defun rt-byte-check-through (n)
   (and (rt-byte-check n)
        (or (zp n) (rt-byte-check-through (1- n))))))

(local
 (defthm rt-byte-check-of-lesser-code
   (implies (and (natp n) (rt-byte-check-through n) (natp i) (<= i n))
            (rt-byte-check i))
   :hints (("Goal" :in-theory (disable rt-byte-check)))))

(local
 (defthm rt-byte-check-of-code
   (implies (and (natp n) (< n 256)) (rt-byte-check n))
   :rule-classes nil
   :hints (("Goal" :use ((:instance rt-byte-check-of-lesser-code
                                     (n 255) (i n)))
            :in-theory (disable rt-byte-check)))))

(defthm rt-bm-plain-char
  (implies (characterp c)
           (iff (bm-plain-charp c) (rt-plain-char-p c)))
  :hints (("Goal" :use ((:instance rt-byte-check-of-code (n (char-code c))))
           :in-theory (disable rt-plain-char-p bm-plain-charp
                               boymoo::plain-char-p boymoo::hex-value
                               bm-hex2))))

(defthm rt-reader-plain-char
  (equal (boymoo::plain-char-p c) (rt-plain-char-p c))
  :hints (("Goal" :use ((:instance rt-byte-check-of-code (n (char-code c))))
           :cases ((characterp c))
           :in-theory (disable bm-plain-charp boymoo::hex-value bm-hex2))
          ("Subgoal 1" :in-theory (disable bm-plain-charp boymoo::hex-value
                                          bm-hex2 rt-plain-char-p
                                          boymoo::plain-char-p))))

(defthm rt-print-hex
  (implies (and (natp n) (< n 256))
           (equal (bm-hex2 n) (list (rt-hex-high n) (rt-hex-low n))))
  :hints (("Goal" :use rt-byte-check-of-code
           :in-theory (disable bm-plain-charp rt-plain-char-p
                               boymoo::plain-char-p boymoo::hex-value bm-hex2))))

(defthm rt-read-hex
  (implies (and (natp n) (< n 256))
           (and (boymoo::hex-value (rt-hex-high n))
                (boymoo::hex-value (rt-hex-low n))
                (equal (+ (* 16 (boymoo::hex-value (rt-hex-high n)))
                          (boymoo::hex-value (rt-hex-low n)))
                       n)))
  :hints (("Goal" :use rt-byte-check-of-code
           :in-theory (disable bm-plain-charp rt-plain-char-p
                               boymoo::plain-char-p boymoo::hex-value bm-hex2))))

(defthm rt-equal-char-codes
  (implies (and (characterp x) (characterp y))
           (equal (equal (char-code x) (char-code y)) (equal x y)))
  :hints (("Goal" :use ((:instance code-char-char-code-is-identity (c x))
                         (:instance code-char-char-code-is-identity (c y)))
           :in-theory (disable code-char-char-code-is-identity))))

(local
 (defthm rt-code-92
   (implies (characterp c)
            (equal (equal (char-code c) 92) (equal c #\\)))
   :hints (("Goal" :use ((:instance rt-equal-char-codes (x c) (y #\\)))
            :in-theory (disable rt-equal-char-codes)))))

(defthm rt-bm-all-plain
  (implies (character-listp cs)
           (equal (bm-all-plain cs) (rt-all-plain-p cs)))
  :hints (("Goal" :in-theory (disable bm-plain-charp rt-plain-char-p))))

(defthm rt-reader-all-plain
  (equal (boymoo::all-plain-p cs) (rt-all-plain-p cs))
  :hints (("Goal" :in-theory (disable boymoo::plain-char-p rt-plain-char-p))))

(in-theory (disable bm-hex2 bm-plain-charp bm-all-plain
                    boymoo::hex-value boymoo::plain-char-p boymoo::all-plain-p))

; A quoted character is literal exactly when it can stand for itself.
(defun rt-literal-char-p (c close)
  (and (<= 32 (char-code c)) (<= (char-code c) 126)
       (not (equal c close))
       (not (equal c #\\))))

(defun rt-escaped-char (c close)
  (if (rt-literal-char-p c close)
      (list c)
    (list #\\ (rt-hex-high (char-code c)) (rt-hex-low (char-code c)))))

(defun rt-escaped-text (cs close)
  (if (consp cs)
      (append (rt-escaped-char (car cs) close)
              (rt-escaped-text (cdr cs) close))
    nil))

(defthm rt-escaped-text-characters
  (implies (character-listp cs)
           (character-listp (rt-escaped-text cs close)))
  :hints (("Goal" :in-theory (enable rt-hex-high rt-hex-low))))

(defund rt-part-text (cs)
  (if (and (consp cs) (rt-all-plain-p cs))
      cs
    (cons #\| (append (rt-escaped-text cs #\|) '(#\|)))))

; Reversing the printer's accumulator gives the escaped text in order.
(defthm rt-print-escaped
  (implies (character-listp cs)
           (equal (bm-escaped cs close acc)
                  (revappend (rt-escaped-text cs close) acc)))
  :hints (("Goal" :induct (bm-escaped cs close acc))))

(defthm rt-print-part
  (implies (stringp s)
           (equal (bm-part s acc)
                  (revappend (rt-part-text (coerce s 'list)) acc)))
  :hints (("Goal" :in-theory (enable rt-part-text))))

; The scans stop at the end of a plain run or at the closing quote.
(defthm rt-lex-plain-of-run
  (implies (and (rt-all-plain-p cs) (not (rt-plain-char-p (car rest))))
           (equal (boymoo::lex-plain (append cs rest) acc)
                  (cons (revappend cs acc) rest)))
  :hints (("Goal" :induct (revappend cs acc)
           :in-theory (disable rt-plain-char-p))))

(local
 (defun rt-quoted-scan-induction (cs close dec raw)
   (if (consp cs)
       (rt-quoted-scan-induction (cdr cs) close (cons (car cs) dec)
                                 (revappend (rt-escaped-char (car cs) close) raw))
     (cons dec raw))))

(defthm rt-lex-quoted-of-escaped-text
  (implies (and (character-listp cs) (characterp close) (not (equal close #\\)))
           (equal (boymoo::lex-quoted
                   (append (rt-escaped-text cs close) (cons close rest))
                   close dec raw)
                  (list* (revappend cs dec)
                         (revappend (rt-escaped-text cs close) raw)
                         rest)))
  :hints (("Goal" :induct (rt-quoted-scan-induction cs close dec raw))))

(local
 (defthm rt-lex-quoted-at-close
   (equal (boymoo::lex-quoted (cons close rest) close dec raw)
          (list* dec raw rest))))

(defthm rt-lex-part-of-text
  (implies (and (character-listp cs) (not (rt-plain-char-p (car rest))))
           (equal (boymoo::lex-part (append (rt-part-text cs) rest))
                  (list* cs (rt-part-text cs) rest)))
  :hints (("Goal" :in-theory (e/d (rt-part-text)
                                   (boymoo::lex-quoted boymoo::lex-plain
                                    rt-plain-char-p rt-escaped-text
                                    rt-all-plain-p))
           :do-not-induct t)))

(in-theory (disable bm-escaped bm-part
                    boymoo::lex-quoted boymoo::lex-plain boymoo::lex-part))
