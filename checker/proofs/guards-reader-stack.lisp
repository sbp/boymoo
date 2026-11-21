(in-package "BOYMOO")

(include-book "guards-invariants")

; Each frame is a list of data in reverse order. The bottom frame holds
; the word and the data of the line read so far.
(defthm cg-reader-stack-is-list
  (implies (guard-reader-stack-p stack)
           (true-listp stack))
  :hints (("Goal" :induct (guard-reader-frames-p stack))))

(local
 (defthm cg-reader-stack-shape
   (implies (guard-reader-stack-p stack)
            (and (true-listp stack) (consp stack)))
   :rule-classes :forward-chaining))

(defthm cg-reader-stack-start
  (guard-reader-stack-p (list (list word))))

(defthm cg-reader-stack-after-open
  (implies (guard-reader-stack-p stack)
           (guard-reader-stack-p (cons nil stack))))

(defthm cg-reader-stack-after-element
  (implies (guard-reader-stack-p stack)
           (guard-reader-stack-p (cons (cons datum (car stack)) (cdr stack)))))

(defthm cg-reader-stack-after-close
  (implies (and (guard-reader-stack-p stack)
                (consp (cdr stack)))
           (guard-reader-stack-p
            (cons (cons datum (cadr stack)) (cddr stack)))))

(defthm cg-reader-package-lookup
  (implies (guard-trie-p pkgs :package)
           (let ((p (lex-part cs)))
             (or (not p) (true-listp (trie-get (car p) pkgs)))))
  :hints (("Goal" :use ((:instance cg-package-record-of-lookup
                                   (key (car (lex-part cs))) (node pkgs)))
           :in-theory (disable lex-part trie-get))))

(verify-guards parse-loop
  :hints (("Goal" :in-theory (disable lex-atom lex-part trie-get guard-reader-stack-p))))

(verify-guards parse-line
  :hints (("Goal" :in-theory (disable parse-loop pair-of lex-word))))

(local
 (defthm cg-rev-onto-is-list
   (implies (true-listp acc)
            (true-listp (rev-onto xs acc)))))

(defthm cg-parse-loop-result-is-list
  (true-listp (car (parse-loop cs stack elem pkgs)))
  :hints (("Goal" :induct (parse-loop cs stack elem pkgs)
           :in-theory (disable lex-atom))))

(defthm cg-parse-line-result-is-list
  (true-listp (parse-line cs words pkgs))
  :hints (("Goal" :in-theory (disable parse-loop lex-word pair-of))))

(local
 (defthm cg-rev-onto-keeps-character-lists
   (implies (and (guard-character-lists-p xs) (guard-character-lists-p acc))
            (guard-character-lists-p (rev-onto xs acc)))))

(defthm cg-split-lines-character-lists
  (implies (and (character-listp cs)
                (character-listp cur)
                (guard-character-lists-p acc))
           (guard-character-lists-p (split-lines cs cur acc)))
  :hints (("Goal" :induct (split-lines cs cur acc)
           :in-theory (disable rev-onto))))

(defthm cg-lines-of-character-lists
  (guard-character-lists-p (lines-of string))
  :hints (("Goal" :in-theory (disable split-lines))))
