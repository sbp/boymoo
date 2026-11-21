(in-package "BOYMOO")

(include-book "read")
(include-book "guards-base")

(defthm cg-sym-text-chars
  (character-listp (sym-text s)))

(local
 (defthm cg-plain-char-is-character
   (implies (plain-char-p c) (characterp c))
   :rule-classes ((:forward-chaining) (:rewrite))))

(local
 (defthm cg-hex-value-is-character
   (implies (hex-value c) (characterp c))
   :hints (("Goal" :in-theory (enable hex-value)))
   :rule-classes ((:forward-chaining) (:rewrite))))

(local
 (defthm cg-hex-value-range
   (implies (hex-value c)
            (and (natp (hex-value c)) (<= (hex-value c) 15)))
   :rule-classes
   ((:rewrite)
    (:linear :corollary (implies (hex-value c) (<= (hex-value c) 15)))
    (:linear :corollary (implies (hex-value c) (<= 0 (hex-value c)))))))

(local (in-theory (disable hex-value plain-char-p)))

(local
 (defthm cg-lex-quoted-shape
   (implies (lex-quoted cs close dec raw)
            (and (consp (lex-quoted cs close dec raw))
                 (consp (cdr (lex-quoted cs close dec raw)))))
   :hints (("Goal" :induct (lex-quoted cs close dec raw)))))

(local
 (defthm cg-lex-quoted-characters
   (implies (and (character-listp dec) (character-listp raw))
            (and (character-listp (car (lex-quoted cs close dec raw)))
                 (character-listp (car (cdr (lex-quoted cs close dec raw))))))
   :hints (("Goal" :induct (lex-quoted cs close dec raw)))))

(local
 (defthm cg-lex-quoted-rest
   (implies (character-listp cs)
            (character-listp (cdr (cdr (lex-quoted cs close dec raw)))))
   :hints (("Goal" :induct (lex-quoted cs close dec raw)))))

(local
 (defthm cg-lex-plain-characters
   (implies (character-listp acc)
            (character-listp (car (lex-plain cs acc))))))

(local
 (defthm cg-lex-plain-rest
   (implies (character-listp cs)
            (character-listp (cdr (lex-plain cs acc))))))

(local
 (defthm cg-lex-plain-nonempty-run
   (implies (or (consp acc) (and (consp cs) (plain-char-p (car cs))))
            (consp (car (lex-plain cs acc))))))

(verify-guards lex-part
  :hints (("Goal" :in-theory (disable lex-quoted lex-plain rev all-plain-p))))

(defthm cg-lex-part-shape
  (implies (lex-part cs)
           (and (consp (lex-part cs))
                (consp (cdr (lex-part cs)))))
  :hints (("Goal" :in-theory (disable lex-quoted lex-plain rev all-plain-p))))

(defthm cg-lex-part-characters
  (let ((p (lex-part cs)))
    (and (character-listp (car p))
         (character-listp (car (cdr p)))))
  :hints (("Goal" :in-theory (disable lex-quoted lex-plain rev all-plain-p))))

(defthm cg-lex-part-rest
  (implies (character-listp cs)
           (character-listp (cdr (cdr (lex-part cs)))))
  :hints (("Goal" :in-theory (disable lex-quoted lex-plain rev all-plain-p))))

(verify-guards lex-symbol-rest
  :hints (("Goal" :in-theory (disable lex-part trie-get app text-symbol))))

(local
 (defthm cg-digits-value-integer-or-nil
   (implies (integerp n)
            (or (integerp (digits-value cs n))
                (equal (digits-value cs n) nil)))
   :rule-classes :type-prescription
   :hints (("Goal" :induct (digits-value cs n)))))

(local
 (defthm cg-positive-value-integer-or-nil
   (or (integerp (positive-value cs))
       (equal (positive-value cs) nil))
   :rule-classes :type-prescription))

(local
 (defthm cg-integer-value-integer-or-nil
   (or (integerp (integer-value cs))
       (equal (integer-value cs) nil))
   :rule-classes :type-prescription
   :hints (("Goal" :in-theory (disable positive-value)))))

(verify-guards number-value
  :hints (("Goal"
           :in-theory (disable integer-value positive-value split-slash))))

(local
 (defthm cg-number-value-shape
   (implies (number-value run)
            (and (consp (number-value run))
                 (rationalp (car (number-value run)))))
   :hints (("Goal"
            :in-theory (disable integer-value positive-value split-slash)))))

(verify-guards lex-sharp
  :hints (("Goal" :in-theory (disable number-value lex-plain rev))))

(local
 (defthm cg-lex-part-of-plain-run
   (implies (and (consp cs) (not (equal (car cs) #\|))
                 (plain-char-p (car cs)))
            (let* ((r (lex-plain cs nil))
                   (run (rev (car r))))
              (equal (lex-part cs)
                     (cons run (cons run (cdr r))))))
   :hints (("Goal" :in-theory (disable lex-plain rev)))))

(verify-guards lex-atom
  :hints (("Goal" :in-theory (disable lex-part lex-plain lex-sharp lex-quoted
                                     lex-symbol-rest number-value trie-get rev))))

