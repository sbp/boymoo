; A single atom, with the rest of the line left for the caller.

(in-package "ACL2")

(include-book "round-trip-numbers")
(include-book "round-trip-symbols")

; The text of each kind of atom, in the order in which it is read.
(defund rt-atom-text (x)
  (cond ((rationalp x) (rt-rational-text x))
        ((complex-rationalp x)
         (list* #\# #\C #\(
                (append (rt-rational-text (realpart x))
                        (cons #\Space (append (rt-rational-text (imagpart x))
                                               '(#\)))))))
        ((characterp x)
         (let ((n (char-code x)))
           (list #\# #\\ (rt-hex-high n) (rt-hex-low n))))
        ((stringp x)
         (cons #\" (append (rt-escaped-text (coerce x 'list) #\") '(#\"))))
        (t (rt-symbol-text (symbol-package-name x) (symbol-name x)))))

(defthm rt-print-atom
  (implies (and (rt-format-datum-p x) (not (consp x)))
           (equal (bm-obj x acc) (revappend (rt-atom-text x) acc)))
  :hints (("Goal" :in-theory (e/d (rt-atom-text) (rt-escaped-text))
           :expand ((bm-obj x acc)))))

(defthm rt-atom-text-characters
  (character-listp (rt-atom-text x))
  :hints (("Goal" :in-theory (e/d (rt-atom-text rt-hex-high rt-hex-low)
                                   (rt-escaped-text)))))

; A rational run ends at the first character that is neither plain
; nor a colon. The two runs in a complex rational end at its space
; and its closing parenthesis.
(defund rt-atom-boundary-p (rest)
  (and (not (rt-plain-char-p (car rest)))
       (not (equal (car rest) #\:))))

(local
 (defthm rt-lex-atom-of-rational-text
   (implies (and (rationalp x) (rt-atom-boundary-p rest))
            (equal (boymoo::lex-atom (append (rt-atom-text x) rest) pkgs)
                   (cons x rest)))
   :hints (("Goal"
            :use ((:instance rt-rational-text-first-plain (r x)))
            :in-theory (e/d (rt-atom-boundary-p rt-atom-text)
                             (rt-rational-text-first-plain rt-plain-char-p))))))

(local
 (defthm rt-lex-atom-of-complex-text
   (implies (complex-rationalp x)
            (equal (boymoo::lex-atom (append (rt-atom-text x) rest) pkgs)
                   (cons x rest)))
   :hints (("Goal" :in-theory (e/d (rt-atom-text)
                                    (rt-plain-char-p))))))

; The opening character fixes the scan for quoted strings and characters.
(local
 (defthm rt-lex-atom-of-character-text
   (implies (characterp x)
            (equal (boymoo::lex-atom (append (rt-atom-text x) rest) pkgs)
                   (cons x rest)))
   :hints (("Goal" :in-theory (enable rt-atom-text)))))

(local
 (defthm rt-lex-atom-of-string-text
   (implies (stringp x)
            (equal (boymoo::lex-atom (append (rt-atom-text x) rest) pkgs)
                   (cons x rest)))
   :hints (("Goal" :in-theory (e/d (rt-atom-text) (rt-escaped-text))))))

(local (in-theory (disable boymoo::lex-atom boymoo::lex-sharp)))

(local
 (defthm rt-lex-atom-of-native-symbol-text
   (implies (and (symbolp x) (rt-atom-boundary-p rest)
                 (rt-written-symbols-pass-index-p x pkgs))
            (equal (boymoo::lex-atom (append (rt-atom-text x) rest) pkgs)
                   (cons (rt-reader-symbol (symbol-package-name x) (symbol-name x))
                         rest)))
   :hints (("Goal" :in-theory (e/d (rt-atom-text rt-atom-boundary-p)
                                    (rt-plain-char-p))))))

(defthm rt-lex-atom-of-text
  (implies (and (rt-format-datum-p x) (not (consp x))
                (rt-written-symbols-pass-index-p x pkgs)
                (rt-atom-boundary-p rest))
           (equal (boymoo::lex-atom (append (rt-atom-text x) rest) pkgs)
                  (cons (rt-datum-form x) rest)))
  :hints (("Goal" :in-theory (disable rt-written-symbols-pass-index-p)
           :expand ((rt-datum-form x) (rt-format-datum-p x)))))

; A dot followed by a space cannot begin any atom. It is the punctuation
; for the final cdr of a list.
(defthm rt-dotted-tail-marker-is-not-an-atom
  (implies (and (equal (car cs) #\.) (equal (cadr cs) #\Space))
           (equal (boymoo::lex-atom cs pkgs) nil))
  :hints (("Goal" :in-theory (enable boymoo::lex-atom boymoo::lex-plain
                                     boymoo::number-value boymoo::split-slash
                                     rt-plain-char-p))))

(defthm rt-lex-atom-refuses-open-parenthesis
  (implies (or (not (consp cs)) (equal (car cs) #\())
           (equal (boymoo::lex-atom cs pkgs) nil))
  :hints (("Goal" :in-theory (enable boymoo::lex-atom rt-plain-char-p))))

(in-theory (disable boymoo::lex-atom boymoo::lex-sharp))
