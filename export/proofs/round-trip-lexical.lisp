; Every successful atom scan consumes the text of the atom it returns.

(in-package "ACL2")

(include-book "round-trip-atoms")

; Represented symbols carry their canonical text as their name, with
; the two special symbols of the format interpreted directly.
(defund rt-reader-atom-text (x)
  (cond ((equal x nil) (coerce "COMMON-LISP::NIL" 'list))
        ((equal x t) (coerce "COMMON-LISP::T" 'list))
        ((symbolp x) (coerce (symbol-name x) 'list))
        (t (rt-atom-text x))))

(local
 (defthm rt-interned-text-is-not-a-special-symbol
   (implies (and (character-listp text) (< 3 (len text)))
            (let ((s (intern-in-package-of-symbol (coerce text 'string)
                                                   'boymoo::boymoo)))
              (and (not (equal s nil)) (not (equal s t)))))
   :hints (("Goal"
            :use ((:instance symbol-name-intern-in-package-of-symbol
                             (s (coerce text 'string)) (any-symbol 'boymoo::boymoo))
                  (:instance coerce-inverse-1 (x text)))
            :in-theory (disable symbol-name-intern-in-package-of-symbol
                                coerce-inverse-1)))))

(local
 (defthm rt-text-symbol-keeps-text
   (implies (and (character-listp text) (< 3 (len text)))
            (equal (rt-reader-atom-text (boymoo::text-symbol text)) text))
   :hints (("Goal" :use rt-interned-text-is-not-a-special-symbol
            :in-theory (e/d (rt-reader-atom-text)
                             (rt-interned-text-is-not-a-special-symbol))))))

(defthm rt-read-atom-text-of-datum-form
  (implies (not (consp x))
           (equal (rt-reader-atom-text (rt-datum-form x)) (rt-atom-text x)))
  :hints (("Goal"
           :use ((:instance rt-text-symbol-keeps-text
                            (text (rt-symbol-text (symbol-package-name x) (symbol-name x)))))
           :in-theory (e/d (rt-reader-symbol rt-reader-atom-text rt-atom-text)
                            (rt-text-symbol-keeps-text rt-rational-text
                             rt-symbol-text rt-escaped-text))
           :expand ((rt-datum-form x)))))

; A represented symbol can be separated into its two decoded names.
(defund rt-reader-symbol-parts (symbol)
  (rt-symbol-text-components (rt-reader-atom-text symbol)))

(defthm rt-reader-symbol-parts-are-strings
  (and (stringp (car (rt-reader-symbol-parts symbol)))
       (stringp (cadr (rt-reader-symbol-parts symbol))))
  :hints (("Goal" :in-theory (enable rt-reader-symbol-parts rt-symbol-text-components))))

(local
 (defthm rt-text-symbol-of-symbol-text
   (equal (boymoo::text-symbol (rt-symbol-text package name))
          (rt-reader-symbol package name))
   :hints (("Goal" :in-theory (enable rt-reader-symbol)))))

(defthm rt-reader-symbol-parts-of-reader-symbol
  (implies (and (stringp package) (stringp name))
           (equal (rt-reader-symbol-parts (rt-reader-symbol package name))
                  (list package name)))
  :hints (("Goal" :use ((:instance rt-text-symbol-keeps-text
                                   (text (rt-symbol-text package name))))
           :in-theory (e/d (rt-reader-symbol-parts) (rt-text-symbol-keeps-text)))))

(defund rt-reader-atom-in-table-p (x pkgs)
  (if (symbolp x)
      (let* ((parts (rt-reader-symbol-parts x))
             (package (car parts))
             (name (cadr parts)))
        (and (equal x (rt-reader-symbol package name))
             (rt-symbol-passes-index-p package name pkgs)))
    (or (rationalp x) (complex-rationalp x) (characterp x) (stringp x))))

(local
 (defthm rt-represented-name-in-table
   (implies (and (stringp package) (stringp name)
                 (rt-symbol-passes-index-p package name pkgs))
            (rt-reader-atom-in-table-p (rt-reader-symbol package name) pkgs))
   :hints (("Goal" :in-theory (enable rt-reader-atom-in-table-p)))))

; A plain scan records the consumed prefix, in reverse.
(local
 (defthm rt-lex-plain-keeps-text
   (let ((r (boymoo::lex-plain cs acc)))
     (equal (revappend (car r) (cdr r)) (revappend acc cs)))
   :hints (("Goal" :induct (boymoo::lex-plain cs acc)
            :in-theory (enable boymoo::lex-plain)))))

(local
 (defthm rt-plain-char-is-a-character
   (implies (rt-plain-char-p c) (characterp c))
   :rule-classes :forward-chaining))

(local
 (defthm rt-lex-plain-characters
   (implies (character-listp acc)
            (character-listp (car (boymoo::lex-plain cs acc))))
   :hints (("Goal" :induct (boymoo::lex-plain cs acc)
            :in-theory (e/d (boymoo::lex-plain) (rt-plain-char-p))))))

(local
 (defthm rt-all-plain-of-reverse
   (equal (rt-all-plain-p (revappend cs acc))
          (and (rt-all-plain-p cs) (rt-all-plain-p acc)))
   :hints (("Goal" :induct (revappend cs acc)
            :in-theory (disable rt-plain-char-p)))))

(local
 (defthm rt-lex-plain-records-plain-chars
   (implies (rt-all-plain-p acc)
            (rt-all-plain-p (car (boymoo::lex-plain cs acc))))
   :hints (("Goal" :induct (boymoo::lex-plain cs acc)
            :in-theory (e/d (boymoo::lex-plain) (rt-plain-char-p))))))

(local
 (defthm rt-lex-plain-records-a-nonempty-run
   (equal (consp (car (boymoo::lex-plain cs acc)))
          (or (consp acc) (and (consp cs) (rt-plain-char-p (car cs)))))
   :hints (("Goal" :induct (boymoo::lex-plain cs acc)
            :in-theory (e/d (boymoo::lex-plain) (rt-plain-char-p))))))

; Hexadecimal digits determine a unique byte, and reading that byte
; as two digits recovers the same pair.
(local
 (defthm rt-hex-value-bounds
   (implies (boymoo::hex-value c)
            (and (characterp c) (integerp (boymoo::hex-value c))
                 (<= 0 (boymoo::hex-value c)) (< (boymoo::hex-value c) 16)))
   :rule-classes ((:forward-chaining :trigger-terms ((boymoo::hex-value c))))
   :hints (("Goal" :in-theory (enable boymoo::hex-value)))))

(local
 (defthm rt-hex-value-injective
   (implies (and (boymoo::hex-value a) (boymoo::hex-value b))
            (equal (equal (boymoo::hex-value a) (boymoo::hex-value b))
                   (equal a b)))
   :rule-classes nil
   :hints (("Goal" :use ((:instance rt-equal-char-codes (x a) (y b)))
            :in-theory (e/d (boymoo::hex-value) (rt-equal-char-codes))))))

(local
 (defthm rt-base-16-components-are-unique
   (implies (and (integerp h1) (integerp h2)
                 (natp l1) (< l1 16) (natp l2) (< l2 16)
                 (equal (+ (* 16 h1) l1) (+ (* 16 h2) l2)))
            (and (equal h1 h2) (equal l1 l2)))
   :rule-classes nil
   :hints (("Goal" :cases ((< h1 h2) (< h2 h1))))))

(local
 (defthm rt-hex-digit-values-from-byte
   (implies (and (boymoo::hex-value hi) (boymoo::hex-value lo))
            (let* ((code (+ (* 16 (boymoo::hex-value hi)) (boymoo::hex-value lo)))
                   (read-hi (boymoo::hex-value (rt-hex-high code)))
                   (read-lo (boymoo::hex-value (rt-hex-low code))))
              (and (equal read-hi (boymoo::hex-value hi))
                   (equal read-lo (boymoo::hex-value lo)))))
   :hints (("Goal" :use ((:instance rt-read-hex
                            (n (+ (* 16 (boymoo::hex-value hi)) (boymoo::hex-value lo))))
                        (:instance rt-base-16-components-are-unique
                         (h1 (boymoo::hex-value hi)) (l1 (boymoo::hex-value lo))
                         (h2 (boymoo::hex-value (rt-hex-high
                               (+ (* 16 (boymoo::hex-value hi)) (boymoo::hex-value lo)))))
                         (l2 (boymoo::hex-value (rt-hex-low
                               (+ (* 16 (boymoo::hex-value hi)) (boymoo::hex-value lo)))))))
            :in-theory (disable rt-read-hex)))))

(local
 (defthm rt-hex-digits-from-byte
   (implies (and (boymoo::hex-value hi) (boymoo::hex-value lo))
            (let ((code (+ (boymoo::hex-value lo) (* 16 (boymoo::hex-value hi)))))
              (and (equal (rt-hex-high code) hi)
                   (equal (rt-hex-low code) lo))))
   :hints (("Goal" :use
            ((:instance rt-hex-digit-values-from-byte)
             (:instance rt-hex-value-injective
              (a (rt-hex-high (+ (* 16 (boymoo::hex-value hi)) (boymoo::hex-value lo))))
              (b hi))
             (:instance rt-hex-value-injective
              (a (rt-hex-low (+ (* 16 (boymoo::hex-value hi)) (boymoo::hex-value lo))))
              (b lo)))
            :in-theory (disable rt-hex-digit-values-from-byte)))))

; A quoted scan preserves the relation between the characters it has
; decoded and the characters of their escaped spelling.
(local
 (defthm rt-escaped-text-of-append
   (equal (rt-escaped-text (append x y) close)
          (append (rt-escaped-text x close) (rt-escaped-text y close)))
   :hints (("Goal" :induct (append x y)
            :in-theory (disable rt-escaped-char)))))

(local
 (defthm rt-escaped-text-of-reverse-with-final-character
   (equal (rt-escaped-text (revappend dec (list c)) close)
          (append (rt-escaped-text (revappend dec nil) close)
                  (rt-escaped-char c close)))
   :hints (("Goal" :use ((:instance rt-escaped-text-of-append
                                     (x (revappend dec nil)) (y (list c))))
            :in-theory (disable rt-escaped-text-of-append rt-escaped-char)))))

(local
 (defthm rt-backslash-code
   (implies (characterp c)
            (equal (equal (char-code c) 92) (equal c #\\)))
   :hints (("Goal" :use ((:instance rt-equal-char-codes (x c) (y #\\)))
            :in-theory (disable rt-equal-char-codes)))))

(local
 (defthm rt-read-escape-is-required
   (implies (and (boymoo::hex-value hi) (boymoo::hex-value lo) (characterp close))
            (let ((code (+ (boymoo::hex-value lo) (* 16 (boymoo::hex-value hi)))))
              (implies (or (< code 32) (< 126 code) (equal code 92)
                           (equal code (char-code close)))
                       (equal (rt-escaped-char (code-char code) close)
                              (list #\\ hi lo)))))
   :hints (("Goal"
            :use (rt-hex-digits-from-byte
                  (:instance rt-equal-char-codes
                             (x (code-char (+ (* 16 (boymoo::hex-value hi))
                                              (boymoo::hex-value lo))))
                             (y close)))
            :in-theory (disable rt-equal-char-codes rt-hex-digits-from-byte)))))

(local
 (defthm rt-read-literal-is-allowed
   (implies (and (characterp c) (< 31 (char-code c)) (< (char-code c) 127)
                 (not (equal (char-code c) 92)) (not (equal c close)))
            (equal (rt-escaped-char c close) (list c)))))

(local
 (defthm rt-character-listp-of-reverse
   (implies (and (character-listp cs) (character-listp acc))
            (character-listp (revappend cs acc)))))

(local
 (defthm rt-lex-quoted-keeps-text-and-escapes
   (let ((r (boymoo::lex-quoted cs close dec raw)))
     (implies (and r (characterp close) (not (equal close #\\))
                   (character-listp dec) (character-listp raw)
                   (equal (revappend raw nil)
                          (rt-escaped-text (revappend dec nil) close)))
              (and (character-listp (car r))
                   (character-listp (cadr r))
                   (equal (revappend (cadr r) nil)
                          (rt-escaped-text (revappend (car r) nil) close))
                   (equal (revappend raw cs)
                          (revappend (cadr r) (cons close (cddr r)))))))
   :hints (("Goal" :induct (boymoo::lex-quoted cs close dec raw)
            :in-theory (e/d (boymoo::lex-quoted) (rt-escaped-text rt-escaped-char))
            :do-not '(generalize fertilize) :do-not-induct t)
           ("Subgoal *1/2" :use ((:instance rt-read-escape-is-required
                                            (hi (cadr cs)) (lo (caddr cs))))
            :in-theory (e/d (boymoo::lex-quoted)
                             (rt-escaped-text rt-escaped-char rt-read-escape-is-required))))))

(local
 (defthm rt-read-quoted-text
   (let ((r (boymoo::lex-quoted cs close nil nil)))
     (implies (and r (characterp close) (not (equal close #\\)))
              (and (character-listp (cadr r))
                   (character-listp (revappend (car r) nil))
                   (character-listp (revappend (cadr r) nil))
                   (equal (revappend (cadr r) nil)
                          (rt-escaped-text (revappend (car r) nil) close))
                   (equal cs (revappend (cadr r) (cons close (cddr r)))))))
   :rule-classes nil
   :hints (("Goal" :use ((:instance rt-lex-quoted-keeps-text-and-escapes
                                    (dec nil) (raw nil)))
            :in-theory (disable rt-lex-quoted-keeps-text-and-escapes)))))

; A symbol part returns both its contents and the text that was consumed.
(local
 (defthm rt-reverse-is-empty-exactly-when-input-has-no-cons
   (iff (revappend x nil) (consp x))
   :hints (("Goal" :use ((:instance rt-consp-of-revappend (y nil)))))))

(local
 (defthm rt-read-symbol-part
   (let ((r (boymoo::lex-part cs)))
     (implies r
              (and (character-listp (car r))
                   (character-listp (cadr r))
                   (consp (cadr r))
                   (equal (cadr r) (rt-part-text (car r)))
                   (equal (append (cadr r) (cddr r)) cs))))
   :rule-classes nil
   :hints (("Goal"
            :use ((:instance rt-read-quoted-text (cs (cdr cs)) (close #\|)))
            :in-theory (e/d (boymoo::lex-part rt-part-text)
                             (rt-escaped-text rt-all-plain-p rt-plain-char-p
                              rt-lex-quoted-keeps-text-and-escapes))
            :do-not-induct t))))

(local
 (defthm rt-length-of-nonempty-list
   (implies (consp x) (< 0 (len x)))
   :rule-classes :linear))

(local
 (defthm rt-read-symbol-after-package
   (let ((r (boymoo::lex-symbol-rest part pkgs)))
     (implies (and r (consp (cadr part)) (character-listp (cadr part)))
              (and (not (consp (car r)))
                   (equal (append (rt-reader-atom-text (car r)) (cdr r))
                          (append (cadr part) (cddr part))))))
   :hints (("Goal" :use ((:instance rt-read-symbol-part (cs (cddddr part))))
            :in-theory (disable boymoo::text-symbol)
            :do-not-induct t))))

(local
 (defthm rt-text-symbol-of-character-parts
   (implies (and (character-listp package) (character-listp name))
            (equal (boymoo::text-symbol
                    (append (rt-part-text package) (list* #\: #\: (rt-part-text name))))
                   (rt-reader-symbol (coerce package 'string) (coerce name 'string))))
   :hints (("Goal" :in-theory (enable rt-reader-symbol rt-symbol-text)))))

(local
 (defthm rt-read-symbol-is-in-table
   (let ((r (boymoo::lex-symbol-rest part pkgs)))
     (implies (and r (character-listp (car part))
                   (equal (cadr part) (rt-part-text (car part))))
              (rt-reader-atom-in-table-p (car r) pkgs)))
   :hints (("Goal" :use ((:instance rt-read-symbol-part (cs (cddddr part))))
            :in-theory (e/d (rt-symbol-passes-index-p)
                             (boymoo::text-symbol boymoo::trie-get))
            :do-not-induct t))))

(local
 (defthm rt-read-string-after-quote
   (let* ((r (boymoo::lex-quoted cs #\" nil nil))
          (val (coerce (revappend (car r) nil) 'string)))
     (implies r
              (equal (append (rt-reader-atom-text val) (cddr r))
                     (cons #\" cs))))
   :hints (("Goal" :use ((:instance rt-read-quoted-text (close #\")))
            :in-theory (e/d (rt-reader-atom-text rt-atom-text) (rt-escaped-text))))))

(local
 (defthm rt-read-plain-number
   (let* ((r (boymoo::lex-plain cs nil))
          (run (revappend (car r) nil))
          (num (boymoo::number-value run)))
     (implies num
              (and (rationalp (car num))
                   (equal (append (rt-rational-text (car num)) (cdr r)) cs))))
   :hints (("Goal"
            :use ((:instance rt-read-rational-is-canonical
                             (run (revappend (car (boymoo::lex-plain cs nil)) nil)))
                  (:instance rt-lex-plain-keeps-text (acc nil)))
            :in-theory (disable rt-lex-plain-keeps-text)))))

; The sharp scan writes the two digits of a character, or the text
; of each rational part with the punctuation of a complex rational.
(defthm rt-cons-of-front-and-tail
  (implies (and (consp x) (equal c (car x)))
           (equal (cons c (cdr x)) x)))

(local
 (defthm rt-read-sharp-atom
   (let ((r (boymoo::lex-sharp cs)))
     (implies r
              (and (not (consp (car r)))
                   (rt-reader-atom-in-table-p (car r) pkgs)
                   (equal (append (rt-reader-atom-text (car r)) (cdr r))
                          (cons #\# cs)))))
   :hints (("Goal"
            :use ((:instance rt-read-plain-number (cs (cddr cs)))
                  (:instance rt-read-plain-number
                             (cs (cddr (boymoo::lex-plain (cddr cs) nil)))))
            :in-theory (e/d (boymoo::lex-sharp rt-reader-atom-in-table-p
                                              rt-reader-atom-text rt-atom-text)
                             (rt-read-plain-number rt-escaped-text))
            :do-not-induct t))))

(local
 (defthm rt-rational-text-of-reader-atom
   (implies (rationalp x)
            (equal (rt-reader-atom-text x) (rt-rational-text x)))
   :hints (("Goal" :in-theory (enable rt-reader-atom-text rt-atom-text)))))

(local
 (defthm rt-plain-part-is-its-text
   (implies (and (consp cs) (rt-all-plain-p cs))
            (equal (rt-part-text cs) cs))
   :hints (("Goal" :in-theory (enable rt-part-text)))))

(local
 (defthm rt-string-or-rational-is-a-reader-atom
   (implies (or (rationalp x) (stringp x))
            (rt-reader-atom-in-table-p x pkgs))
   :hints (("Goal" :in-theory (enable rt-reader-atom-in-table-p)))))

(defthm rt-read-atom-is-canonical
  (let ((r (boymoo::lex-atom cs pkgs)))
    (implies r
             (and (not (consp (car r)))
                  (rt-reader-atom-in-table-p (car r) pkgs)
                  (equal (append (rt-reader-atom-text (car r)) (cdr r)) cs))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (boymoo::lex-atom)
                                   (boymoo::lex-symbol-rest rt-plain-char-p
                                    rt-read-plain-number rt-lex-plain-keeps-text))
           :use ((:instance rt-read-plain-number)
                 (:instance rt-lex-plain-keeps-text (acc nil))
                 rt-read-symbol-part)
           :do-not-induct t)))
