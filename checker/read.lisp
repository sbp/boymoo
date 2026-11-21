; Boymoo, the checker: the reader of spec/formats.md, sections 1 and 2.
;
; An input is a string.  It is split into lines, each the list of its
; characters with its line feed; a last line without one stays as it is
; and is refused.  A line is read in one pass, with an explicit stack for
; the lists it holds, against the packages declared before it, and is
; refused unless it is the one text of its word and data and every symbol
; on it exists (spec/language.md, section 2).
;
; How a symbol is held.  The packages of an input are not packages of the
; runner, nor of ACL2 when the checker runs inside it.  So the symbol whose
; text is P::N is held as the symbol of the package BOYMOO whose name is
; that text, which is unique (spec/formats.md, section 2); and the symbols
; COMMON-LISP::NIL and COMMON-LISP::T are held as NIL and T themselves, so
; that lists end with NIL and the primitives that give T or NIL give the
; checker's own.  Two symbols of an input are the same exactly when the
; symbols that hold them are.

(in-package "BOYMOO")

(include-book "base")

; ---------------------------------------------------------------------------
; Packages, as the reader needs them
;
; The table of packages is a trie from the characters of a package's name to
; its record: its imports, a trie from the characters of each import's name
; to the list of that import, whether it is hidden, and the lines that
; declared it.  The value in the trie of imports is a list, never NIL, so
; that an import held as NIL, COMMON-LISP::NIL, is found as present: a
; package that imports it has no symbol named NIL of its own.

(defmacro prec-imports (r) `(car ,r))
(defmacro prec-trie (r) `(car (cdr ,r)))
(defmacro prec-hidden (r) `(car (cdr (cdr ,r))))
(defmacro prec-lines (r) `(car (cdr (cdr (cdr ,r)))))

(defun guard-sized-clause-p (c)
  (declare (xargs :guard t))
  (and (consp c)
       (true-listp (car c))
       (guard-natural-list-p (cdr c))
       (equal (len (car c)) (len (cdr c)))))

(defun guard-name-record-p (entry)
  (declare (xargs :guard t))
  (and (true-listp entry)
       (equal (len entry) 3)
       (or (not (car entry)) (natp (car entry)))
       (or (not (cadr entry)) (guard-sized-clause-p (cadr entry)))
       (true-listp (caddr entry))))

(mutual-recursion
 (defun guard-trie-p (node kind)
   (declare (xargs :guard t :measure (acl2-count node)))
   (if (consp node)
       (and (guard-trie-value-p (car node) kind)
            (guard-trie-kids-p (cdr node) kind))
     (equal node nil)))

 (defun guard-trie-kids-p (kids kind)
   (declare (xargs :guard t :measure (acl2-count kids)))
   (if (consp kids)
       (and (consp (car kids))
            (characterp (car (car kids)))
            (guard-trie-p (cdr (car kids)) kind)
            (guard-trie-kids-p (cdr kids) kind))
     (equal kids nil)))

 (defun guard-trie-value-p (value kind)
   (declare (xargs :guard t :measure (acl2-count value)))
   (or (equal value nil)
       (case kind
         (:import
          (and (consp value) (symbolp (car value)) (equal (cdr value) nil)))
         (:package
          (and (consp value)
               (consp (cdr value))
               (true-listp value)
               (equal (len value) 4)
               (symbol-listp (prec-imports value))
               (guard-trie-p (prec-trie value) :import)
               (booleanp (prec-hidden value))
               (true-listp (prec-lines value))))
         (:name (guard-name-record-p value))
         (:special (equal value t))
         (otherwise nil)))))

(defconst *nil-text* (coerce "COMMON-LISP::NIL" 'list))
(defconst *t-text* (coerce "COMMON-LISP::T" 'list))

; The symbol that holds the symbol whose text is TEXT.
(defun text-symbol (text)
  (declare (xargs :guard (character-listp text)))
  (if (equal text *nil-text*)
      nil
    (if (equal text *t-text*)
        t
      (intern-in-package-of-symbol (coerce text 'string) 'boymoo))))

; The text of the symbol that S holds.
(defun sym-text (s)
  (declare (xargs :guard (symbolp s)))
  (if (equal s nil)
      *nil-text*
    (if (equal s t)
        *t-text*
      (coerce (symbol-name s) 'list))))

; ---------------------------------------------------------------------------
; Characters

; A plain character: A to Z, a digit, or one of -+*/<=>!?$%&_^~.@
(defun plain-char-p (c)
  (declare (xargs :guard t))
  (if (characterp c)
      (let ((n (char-code c)))
        (if (< n 65)
            (if (< n 48)
                (member-p n '(33 36 37 38 42 43 45 46 47))
              (if (< n 58) t (member-p n '(60 61 62 63 64))))
          (if (< n 91) t (member-p n '(94 95 126)))))
    nil))

(defun all-plain-p (cs)
  (declare (xargs :guard t))
  (if (consp cs)
      (if (plain-char-p (car cs)) (all-plain-p (cdr cs)) nil)
    t))

; The value of a hexadecimal digit, 0 to 9 or A to F, or NIL.
(defun hex-value (c)
  (declare (xargs :guard t))
  (if (characterp c)
      (let ((n (char-code c)))
        (if (and (< 47 n) (< n 58))
            (- n 48)
          (if (and (< 64 n) (< n 71)) (- n 55) nil)))
    nil))

; ---------------------------------------------------------------------------
; Runs, quoted text and the parts of symbols
;
; Each function below returns NIL if the text is refused, and otherwise a
; cons whose last cdr is the rest of the line.

; The longest run of plain characters at the start of CS: (RUN . REST),
; RUN reversed onto ACC.
(defun lex-plain (cs acc)
  (declare (xargs :guard t))
  (if (and (consp cs) (plain-char-p (car cs)))
      (lex-plain (cdr cs) (cons (car cs) acc))
    (cons acc cs)))

; The text after an opening quote CLOSE, a double quote or a bar, up to and
; with the closing one: (DEC RAW . REST), where DEC is the characters
; written and RAW their text, both reversed onto what was given.  A
; character from 32 to 126 other than CLOSE and the backslash stands for
; itself; any other is written as a backslash and two hexadecimal digits,
; and one that can stand for itself never is.
(defun lex-quoted (cs close dec raw)
  (declare (xargs :guard (characterp close)))
  (if (consp cs)
      (let ((c (car cs)))
        (if (equal c close)
            (cons dec (cons raw (cdr cs)))
          (if (characterp c)
              (let ((n (char-code c)))
                (if (equal n 92)
                    (if (and (consp (cdr cs)) (consp (cdr (cdr cs))))
                        (let ((h1 (hex-value (car (cdr cs))))
                              (h2 (hex-value (car (cdr (cdr cs))))))
                          (if (and h1 h2)
                              (let ((code (+ (* 16 h1) h2)))
                                (if (if (< code 32)
                                        t
                                      (if (< 126 code)
                                          t
                                        (if (equal code 92)
                                            t
                                          (equal code (char-code close)))))
                                    (lex-quoted (cdr (cdr (cdr cs))) close
                                                (cons (code-char code) dec)
                                                (cons (car (cdr (cdr cs)))
                                                      (cons (car (cdr cs))
                                                            (cons c raw))))
                                  nil))
                            nil))
                      nil)
                  (if (and (< 31 n) (< n 127))
                      (lex-quoted (cdr cs) close (cons c dec) (cons c raw))
                    nil)))
            nil)))
    nil))

; A part of a symbol, its package name or its name: a run of plain
; characters that is not empty, or a text between bars that could not be
; written plain.  The result is (DEC RAW . REST), with DEC the characters
; of the part and RAW its text.
(defun lex-part (cs)
  (declare (xargs :guard t
                  :verify-guards nil))
  (if (consp cs)
      (if (equal (car cs) #\|)
          (let ((r (lex-quoted (cdr cs) #\| nil nil)))
            (if r
                (let ((dec (rev (car r))))
                  (if (and (consp dec) (all-plain-p dec))
                      nil
                    (cons dec
                          (cons (cons #\| (rev-onto (car (cdr r)) (list #\|)))
                                (cdr (cdr r))))))
              nil))
        (let ((r (lex-plain cs nil)))
          (if (consp (car r))
              (let ((run (rev (car r))))
                (cons run (cons run (cdr r))))
            nil)))
    nil))

; After the package part P, a result of LEX-PART: the two colons, the name,
; and the symbol, which must exist.  The result is (SYMBOL . REST).
(defun lex-symbol-rest (p pkgs)
  (declare (xargs :guard (and (consp p)
                             (consp (cdr p))
                             (character-listp (car (cdr p)))
                             (true-listp (trie-get (car p) pkgs)))
                  :verify-guards nil))
  (let ((rest (cdr (cdr p))))
    (if (and (consp rest) (equal (car rest) #\:)
             (consp (cdr rest)) (equal (car (cdr rest)) #\:))
        (let ((n (lex-part (cdr (cdr rest)))))
          (if n
              (let ((rec (trie-get (car p) pkgs)))
                (if (and rec (not (trie-get (car n) (prec-trie rec))))
                    (cons (text-symbol
                           (app (car (cdr p))
                                (cons #\: (cons #\: (car (cdr n))))))
                          (cdr (cdr n)))
                  nil))
            nil))
      nil)))

; ---------------------------------------------------------------------------
; Numbers

; The value of a run of digits after N, or NIL if a character is no digit.
(defun digits-value (cs n)
  (declare (xargs :guard (integerp n)))
  (if (consp cs)
      (if (characterp (car cs))
          (let ((c (char-code (car cs))))
            (if (and (< 47 c) (< c 58))
                (digits-value (cdr cs) (+ (* 10 n) (- c 48)))
              nil))
        nil)
    n))

; A positive number: a digit from 1 to 9, then digits.
(defun positive-value (cs)
  (declare (xargs :guard t))
  (if (and (consp cs) (not (equal (car cs) #\0)))
      (digits-value cs 0)
    nil))

; An integer: 0, a positive number, or - and a positive number.
(defun integer-value (cs)
  (declare (xargs :guard t))
  (if (equal cs '(#\0))
      0
    (if (and (consp cs) (equal (car cs) #\-))
        (let ((v (positive-value (cdr cs))))
          (if v (- v) nil))
      (positive-value cs))))

; (BEFORE . AFTER) at the first slash of CS, or (CS . :NONE).
(defun split-slash (cs acc)
  (declare (xargs :guard t))
  (if (consp cs)
      (if (equal (car cs) #\/)
          (cons (rev acc) (cdr cs))
        (split-slash (cdr cs) (cons (car cs) acc)))
    (cons (rev acc) :none)))

; The rational that a run of plain characters writes, in a list, or NIL.
; A fraction is an integer other than 0, a slash, and a positive number
; above 1, with no common factor: so its denominator in lowest terms is the
; one written, which the primitives compute without a division here.
(defun number-value (run)
  (declare (xargs :guard t
                  :verify-guards nil))
  (let ((s (split-slash run nil)))
    (if (equal (cdr s) :none)
        (let ((v (integer-value run)))
          (if v (list v) nil))
      (let ((num (integer-value (car s)))
            (den (positive-value (cdr s))))
        (if (and num den (not (equal num 0)) (< 1 den))
            (let ((q (* num (/ den))))
              (if (equal (denominator q) den) (list q) nil))
          nil)))))

; After #: a character, #\ and two hexadecimal digits, or a complex
; rational, #C( a rational, a space, a rational other than 0, and ).
(defun lex-sharp (cs)
  (declare (xargs :guard t
                  :verify-guards nil))
  (if (and (consp cs) (equal (car cs) #\\)
           (consp (cdr cs)) (consp (cdr (cdr cs))))
      (let ((h1 (hex-value (car (cdr cs))))
            (h2 (hex-value (car (cdr (cdr cs))))))
        (if (and h1 h2)
            (cons (code-char (+ (* 16 h1) h2)) (cdr (cdr (cdr cs))))
          nil))
    (if (and (consp cs) (equal (car cs) #\C)
             (consp (cdr cs)) (equal (car (cdr cs)) #\())
        (let* ((r1 (lex-plain (cdr (cdr cs)) nil))
               (re (number-value (rev (car r1))))
               (rest1 (cdr r1)))
          (if (and re (consp rest1) (equal (car rest1) #\Space))
              (let* ((r2 (lex-plain (cdr rest1) nil))
                     (im (number-value (rev (car r2))))
                     (rest2 (cdr r2)))
                (if (and im (not (equal (car im) 0))
                         (consp rest2) (equal (car rest2) #\)))
                    (cons (complex (car re) (car im)) (cdr rest2))
                  nil))
            nil))
      nil)))

; ---------------------------------------------------------------------------
; Atoms
;
; The first character decides the kind: a double quote begins a string, #
; a character or a complex rational, a bar a symbol; a run of plain
; characters is a package name if two colons follow it, and otherwise an
; integer or a fraction.  The result is (ATOM . REST).
(defun lex-atom (cs pkgs)
  (declare (xargs :guard (let ((p (lex-part cs)))
                          (or (not p) (true-listp (trie-get (car p) pkgs))))
                  :verify-guards nil))
  (if (consp cs)
      (let ((c (car cs)))
        (if (equal c #\")
            (let ((r (lex-quoted (cdr cs) #\" nil nil)))
              (if r (cons (coerce (rev (car r)) 'string) (cdr (cdr r))) nil))
          (if (equal c #\#)
              (lex-sharp (cdr cs))
            (if (equal c #\|)
                (let ((p (lex-part cs)))
                  (if p (lex-symbol-rest p pkgs) nil))
              (if (plain-char-p c)
                  (let ((r (lex-plain cs nil)))
                    (if (and (consp (cdr r)) (equal (car (cdr r)) #\:))
                        (let ((run (rev (car r))))
                          (lex-symbol-rest (cons run (cons run (cdr r))) pkgs))
                      (let ((v (number-value (rev (car r)))))
                        (if v (cons (car v) (cdr r)) nil))))
                nil)))))
    nil))

; ---------------------------------------------------------------------------
; That each step of the reader consumes characters, for the termination of
; the loop below.

(local
 (defthm len-cdr-shorter
   (implies (consp x) (< (len (cdr x)) (len x)))
   :rule-classes :linear))

(local
 (defthm lex-plain-shorter
   (<= (len (cdr (lex-plain cs acc))) (len cs))
   :rule-classes :linear))

(local
 (defthm lex-plain-shorter-strict
   (implies (and (consp cs) (plain-char-p (car cs)))
            (< (len (cdr (lex-plain cs acc))) (len cs)))
   :rule-classes :linear))

(local
 (defthm lex-quoted-shorter
   (implies (lex-quoted cs close dec raw)
            (< (len (cdr (cdr (lex-quoted cs close dec raw)))) (len cs)))
   :rule-classes :linear))

(local
 (defthm lex-part-shorter
   (implies (lex-part cs)
            (< (len (cdr (cdr (lex-part cs)))) (len cs)))
   :rule-classes :linear))

(local
 (defthm lex-symbol-rest-shorter
   (implies (lex-symbol-rest p pkgs)
            (< (len (cdr (lex-symbol-rest p pkgs))) (len (cdr (cdr p)))))
   :rule-classes :linear))

(local
 (defthm lex-sharp-shorter
   (implies (lex-sharp cs)
            (< (len (cdr (lex-sharp cs))) (len cs)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable number-value lex-plain rev)))))

(local
 (defthm lex-atom-shorter
   (implies (lex-atom cs pkgs)
            (< (len (cdr (lex-atom cs pkgs))) (len cs)))
   :rule-classes :linear
   :hints (("Goal" :in-theory (disable number-value lex-plain rev lex-quoted
                                       lex-part lex-symbol-rest lex-sharp)))))

(local (in-theory (disable lex-atom)))

; ---------------------------------------------------------------------------
; Lines

(defun guard-reader-frames-p (stack)
  (declare (xargs :guard t))
  (if (consp stack)
      (and (true-listp (car stack))
           (guard-reader-frames-p (cdr stack)))
    (equal stack nil)))

(defun guard-reader-stack-p (stack)
  (declare (xargs :guard t))
  (and (consp stack) (guard-reader-frames-p stack)))

; The data of a line after its word.  STACK holds a frame for each list
; still open, the elements read so far in reverse, and last the frame of the
; line itself, which holds the word.  ELEM says that an element must come
; next; otherwise one has just been read.  The result is (ELEMENTS . REST)
; when the line closes, where REST must be what follows its line feed.
(defun parse-loop (cs stack elem pkgs)
  (declare (xargs :guard (and (guard-reader-stack-p stack) (guard-trie-p pkgs :package))
                  :verify-guards nil
                  :measure (len cs)))
  (if (consp cs)
      (if elem
          (if (equal (car cs) #\()
              (parse-loop (cdr cs) (cons nil stack) t pkgs)
            (let ((r (lex-atom cs pkgs)))
              (if r
                  (parse-loop (cdr r) (cons (cons (car r) (car stack)) (cdr stack))
                              nil pkgs)
                nil)))
        (if (equal (car cs) #\))
            (if (consp (cdr stack))
                (parse-loop (cdr cs)
                            (cons (cons (rev (car stack)) (car (cdr stack)))
                                  (cdr (cdr stack)))
                            nil pkgs)
              (if (and (consp (cdr cs)) (equal (car (cdr cs)) #\Newline))
                  (cons (rev (car stack)) (cdr (cdr cs)))
                nil))
          (if (equal (car cs) #\Space)
              (if (and (consp (cdr stack))
                       (consp (cdr cs)) (equal (car (cdr cs)) #\.)
                       (consp (cdr (cdr cs))) (equal (car (cdr (cdr cs))) #\Space))
                  ; A list whose last cdr is not NIL: " . ", an atom other
                  ; than NIL, and the closing parenthesis.
                  (let ((r (lex-atom (cdr (cdr (cdr cs))) pkgs)))
                    (if (and r (car r)
                             (consp (cdr r)) (equal (car (cdr r)) #\)))
                        (parse-loop (cdr (cdr r))
                                    (cons (cons (rev-onto (car stack) (car r))
                                                (car (cdr stack)))
                                          (cdr (cdr stack)))
                                    nil pkgs)
                      nil))
                (parse-loop (cdr cs) stack t pkgs))
            nil)))
    nil))

; A word: one or more of the letters a to z and the hyphen.  The result is
; (WORD . REST), the word reversed onto ACC.
(defun lex-word (cs acc)
  (declare (xargs :guard t))
  (if (and (consp cs) (characterp (car cs))
           (let ((n (char-code (car cs))))
             (if (equal n 45) t (and (< 96 n) (< n 123)))))
      (lex-word (cdr cs) (cons (car cs) acc))
    (cons acc cs)))

; The line CS, the characters of one line with its line feed, as the list
; of its word and its data; or NIL if it is refused.  WORDS is an
; association list from the characters of each word that may stand here to
; the keyword that names it.
(defun parse-line (cs words pkgs)
  (declare (xargs :guard (guard-trie-p pkgs :package)
                  :verify-guards nil))
  (if (and (consp cs) (equal (car cs) #\())
      (let* ((r (lex-word (cdr cs) nil))
             (w (pair-of (rev (car r)) words)))
        (if w
            (let ((p (parse-loop (cdr r) (list (list (cdr w))) nil pkgs)))
              (if (and p (equal (cdr p) nil)) (car p) nil))
          nil))
    nil))

; The lines of the characters CS, each with its line feed, and last, if CS
; does not end with a line feed, what follows the last one.
(defun split-lines (cs cur acc)
  (declare (xargs :guard t))
  (if (consp cs)
      (if (equal (car cs) #\Newline)
          (split-lines (cdr cs) nil (cons (rev-onto cur (list #\Newline)) acc))
        (split-lines (cdr cs) (cons (car cs) cur) acc))
    (rev (if (consp cur) (cons (rev cur) acc) acc))))
