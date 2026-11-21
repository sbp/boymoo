(in-package "BOYMOO")

(include-book "terms")
(include-book "guards-read")

(verify-guards fn-arity
  :hints (("Goal" :in-theory (disable name-entry pair-of))))

(local
 (defthm cg-sym-parts-rest-is-list
   (let ((rest (cdr (cdr (lex-part (sym-text s))))))
     (and (true-listp rest) (true-listp (cdr rest))))
   :hints (("Goal" :use ((:instance cg-lex-part-rest (cs (sym-text s))))
            :in-theory (disable lex-part sym-text)))
   :rule-classes nil))

(verify-guards sym-parts
  :hints (("Goal" :use cg-sym-parts-rest-is-list
           :in-theory (disable lex-part sym-text))))
(verify-guards sym-name)

(defthm cg-sym-parts-characters
  (and (character-listp (car (sym-parts s)))
       (character-listp (cdr (sym-parts s))))
  :hints (("Goal" :in-theory (disable lex-part sym-text))))

(defthm cg-sym-name-characters
  (character-listp (sym-name s))
  :hints (("Goal" :in-theory (disable sym-parts))))

(local
 (defthm cg-sixteens-range
   (implies (and (natp n) (natp h) (<= (+ n (* 16 h)) 255))
            (let ((q (sixteens n h)))
              (and (natp q)
                   (< q 16)
                   (<= 0 (+ n (* 16 h) (- (* 16 q))))
                   (< (+ n (* 16 h) (- (* 16 q))) 16))))
   :rule-classes nil
   :hints (("Goal" :induct (sixteens n h)))))

(verify-guards escape-part
  :hints (("Goal" :use ((:instance cg-sixteens-range
                                  (n (char-code (car cs))) (h 0)))
           :in-theory (disable sixteens hex-char))))

(local
 (defthm cg-escape-part-characters
   (implies (and (character-listp cs) (character-listp acc))
            (character-listp (escape-part cs acc)))
   :hints (("Goal" :induct (escape-part cs acc)
            :in-theory (disable sixteens hex-char)))))

(local
 (defthm cg-hex-char-is-character
   (characterp (hex-char d))))

(verify-guards part-text)

(defthm cg-part-text-characters
  (implies (character-listp cs)
           (character-listp (part-text cs)))
  :hints (("Goal" :in-theory (disable all-plain-p escape-part))))

(verify-guards make-sym
  :hints (("Goal" :in-theory (disable part-text text-symbol app))))

(defthm cg-make-sym-is-symbol
  (symbolp (make-sym pkg name))
  :hints (("Goal" :in-theory (disable part-text))))

(verify-guards intern-sym
  :hints (("Goal" :in-theory (disable trie-get make-sym))))

(defthm cg-intern-sym-is-symbol
  (implies (and (true-listp w)
                (true-listp (trie-get pkg (w-pkgs w)))
                (let ((found (trie-get name (prec-trie (trie-get pkg (w-pkgs w))))))
                  (or (not found)
                      (and (consp found) (symbolp (car found))))))
           (symbolp (intern-sym name pkg w)))
  :hints (("Goal" :in-theory (disable trie-get make-sym))))

(verify-guards variable-p
  :hints (("Goal" :in-theory (disable sym-parts sym-text trie-get))))

(defthm cg-size-acc-is-natural
  (implies (natp acc)
           (natp (size-acc x acc)))
  :hints (("Goal" :induct (size-acc x acc))))

(defthm cg-size-is-natural
  (natp (size x)))
